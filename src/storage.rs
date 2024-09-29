// © 2022 Vlad-Stefan Harbuz <vlad@vladh.net>
// SPDX-License-Identifier: AGPL-3.0-only
// “Cellsum” is a registered trademark and no rights to it are ceded.

//! Provides storage for a document's sheets, cells, properties and so on.

use std::collections::VecDeque;

use nohash_hasher::{IntMap, IntSet};
#[allow(unused_imports)]
use tracing::{debug, error, info, instrument, warn};

use crate::formulas;
use crate::sheet::{CellAbsPos, SheetSize};

#[derive(Debug, PartialEq)]
/// A storage error.
pub enum Error {
    EvalError(formulas::eval::Error),
    CouldNotGetCell(CellAbsPos),
}

#[derive(Debug, Clone)]
/// The storage for the data of one cell.
pub struct Cell {
    /// A string containing the formula last set for this cell.
    formula: String,
    /// The result of evaluating this cell's formula.
    value: formulas::eval::Value,
    /// A list of cells this cell depends on. Every time a cell's value is evaluated, that cell's
    /// `dependencies` must also be updated.
    dependencies: VecDeque<CellAbsPos>,
    /// A list of the cells that depend on this cell.
    ///
    /// Here is how this list is updated. Say cell A previously depended on cell B, but cell A's
    /// value has been changed and it now depends on cell C. When A is changed, we have to look up
    /// B's `dependants` and remove A from this list, because A does not depend on B anymore. Note
    /// that this means that, when updating A, we need to keep track of its _previous_ list of
    /// dependencies too, so that we know we have to update B. Next, A now depends on C, so we need
    /// to look up C's `dependants`, then record A in its list of dependants, because A now depends
    /// on C.
    ///
    /// And yes, “dependant” is correct in British/Canadian English, don't @ me.
    dependants: VecDeque<CellAbsPos>,
}

impl Cell {
    /// Creates a new [`Cell`].
    pub fn new(formula: String, value: formulas::eval::Value) -> Self {
        Self {
            formula,
            value,
            dependencies: VecDeque::default(),
            dependants: VecDeque::default(),
        }
    }
}

#[derive(Debug, Default, Clone)]
/// The storage for all of the cells in one sheet (worksheet).
pub struct Sheet {
    /// The main store for cell data, as an [`IntMap`] mapping [`CellAbsPos`] hashes to respective
    /// [`Cell`]s.
    cells: IntMap<usize, Cell>,
}

impl Sheet {
    /// Clears all storage in this sheet.
    pub fn clear(&mut self) {
        self.cells.clear();
    }

    /// Returns the number of _used_ rows and columns in a sheet.
    pub fn get_sheet_size(&self) -> SheetSize {
        // #slow
        match self.get_positions().last() {
            None => SheetSize { cols: 0, rows: 0 },
            Some(last_pos) => SheetSize {
                cols: last_pos.col + 1,
                rows: last_pos.row + 1,
            },
        }
    }

    /// Returns all [`CellAbsPos`]es in the current [`Sheet`], sorted.
    pub fn get_positions(&self) -> Vec<CellAbsPos> {
        let mut ints: Vec<&usize> = self.cells.keys().collect();
        ints.sort();
        ints.into_iter()
            .map(|&h| CellAbsPos::from_hash(h))
            .collect()
    }

    /// Given a [`Cell`]'s [`CellAbsPos`], return a string containing its formula, if there is one.
    pub fn get_formula(&self, abs_pos: CellAbsPos) -> Option<String> {
        self.cells
            .get(&abs_pos.to_hash())
            .map(|cell| cell.formula.clone())
    }

    /// Given a [`Cell`]'s [`CellAbsPos`], return the value obtained from the last evaluation of
    /// its formula.
    pub fn get_value(&self, abs_pos: CellAbsPos) -> Option<formulas::eval::Value> {
        self.cells
            .get(&abs_pos.to_hash())
            .map(|cell| cell.value.clone())
    }

    /// Update the values in all of `origin`'s dependants, their dependants and so on. If we end up
    /// finding `origin` in a list of dependants, fail and return `None`, because this means we
    /// have a cycle.
    fn update_dependant_values(
        &mut self,
        origin_abs_pos: CellAbsPos,
        did_error: bool,
    ) -> Result<(), Error> {
        let mut seen_cells: IntSet<usize> = IntSet::default();
        let mut to_visit: VecDeque<CellAbsPos> = self
            .cells
            .get(&origin_abs_pos.to_hash())
            .ok_or(Error::CouldNotGetCell(origin_abs_pos))?
            .dependants
            .clone();

        while !to_visit.is_empty() {
            let Some(curr_abs_pos) = to_visit.pop_front() else {
                break;
            };
            if curr_abs_pos == origin_abs_pos {
                let origin_cell = self
                    .cells
                    .get_mut(&origin_abs_pos.to_hash())
                    .ok_or(Error::CouldNotGetCell(origin_abs_pos))?;
                let make_err = || formulas::eval::Error::FoundCircularReference {
                    abs_pos: origin_abs_pos,
                };
                origin_cell.value = formulas::eval::Value::Error(make_err());
                return Err(Error::EvalError(make_err()));
            }
            let curr_hash = curr_abs_pos.to_hash();
            if seen_cells.contains(&curr_hash) {
                break;
            }
            seen_cells.insert(curr_hash);

            let new_value = if did_error {
                formulas::eval::Value::Error(formulas::eval::Error::DependencyErrored)
            } else {
                let curr_formula = self
                    .cells
                    .get(&curr_hash)
                    .ok_or(Error::CouldNotGetCell(curr_abs_pos))?
                    .formula
                    .clone();
                let ctx = formulas::eval::Context::new(self);
                let (new_value, _) = formulas::eval::evaluate(&ctx, &curr_formula);
                new_value
            };

            let curr_cell = self
                .cells
                .get_mut(&curr_hash)
                .ok_or(Error::CouldNotGetCell(curr_abs_pos))?;
            curr_cell.value = new_value;
            to_visit.append(&mut curr_cell.dependants.clone());
        }

        Ok(())
    }

    /// Given a cell and its new list of dependencies, update this cell's dependencies, and those
    /// dependencies' dependants. See the documentation of [`Cell`] for more information.
    fn update_cell_dependencies(
        &mut self,
        cell_abs_pos: CellAbsPos,
        new_dependencies: VecDeque<CellAbsPos>,
    ) -> Result<(), Error> {
        let cell_hash = cell_abs_pos.to_hash();
        let cell = self
            .cells
            .get_mut(&cell_hash)
            .ok_or(Error::CouldNotGetCell(cell_abs_pos))?;
        let old_dependencies = cell.dependencies.clone();

        // Remove our cell from the old dependant lists.
        // TODO: Do disjunction here. Without it, this is a bit #slow, but it's no big deal.
        for dep_abs_pos in &old_dependencies {
            let dep_hash = dep_abs_pos.to_hash();
            let dep_cell = self
                .cells
                .get_mut(&dep_hash)
                .ok_or(Error::CouldNotGetCell(*dep_abs_pos))?;
            dep_cell
                .dependants
                .retain(|&dependant| dependant != cell_abs_pos);
        }

        // Add our cell to the new dependant lists.
        for dep_abs_pos in &new_dependencies {
            let dep_hash = dep_abs_pos.to_hash();
            let dep_cell = self
                .cells
                .get_mut(&dep_hash)
                .ok_or(Error::CouldNotGetCell(*dep_abs_pos))?;
            dep_cell.dependants.push_back(cell_abs_pos);
        }

        let cell = self
            .cells
            .get_mut(&cell_hash)
            .ok_or(Error::CouldNotGetCell(cell_abs_pos))?;
        cell.dependencies = new_dependencies;

        Ok(())
    }

    /// Removes the [`Cell`] at a [`CellAbsPos`].
    pub fn remove_cell(&mut self, abs_pos: CellAbsPos) {
        self.cells.remove(&abs_pos.to_hash());
    }

    /// Set a [`Cell`]'s formula, evaluate it, and store both the formula and the evaluated result
    /// in the [`Cell`].
    pub fn set_formula(&mut self, abs_pos: CellAbsPos, formula: &str) -> Result<(), Error> {
        let (new_value, new_dependencies) =
            formulas::eval::evaluate(&formulas::eval::Context::new(self), formula);

        let res = match new_value {
            formulas::eval::Value::Error(ref err) => Err(Error::EvalError(err.clone())),
            _ => Ok(()),
        };

        let hash = abs_pos.to_hash();
        if let Some(cell) = self.cells.get_mut(&hash) {
            cell.value = new_value;
            cell.formula = formula.to_string();
        } else {
            let cell = Cell::new(formula.to_string(), new_value);
            self.cells.insert(hash, cell);
        };

        self.update_cell_dependencies(abs_pos, new_dependencies)?;
        self.update_dependant_values(abs_pos, res != Ok(()))?;

        res
    }
}
