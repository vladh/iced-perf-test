// © 2022 Vlad-Stefan Harbuz <vlad@vladh.net>
// SPDX-License-Identifier: AGPL-3.0-only
// “Cellsum” is a registered trademark and no rights to it are ceded.

//! Handles the dimensions of a sheet of cells and trusses. A truss is a row or a column.

use std::hash::{Hash, Hasher};
use std::{cmp, fmt};

use iced::widget::scrollable;
use iced::{Pixels, Point, Rectangle, Size};
#[allow(unused_imports)]
use tracing::{debug, error, info, instrument, warn};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error {
    CellrefParseError,
}

const LETTERS: &[char] = &[
    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S',
    'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
];

#[allow(dead_code)]
/// The maximum number of cells in a sheet.
///
/// Calculated as:
/// ```
/// AbsNotch::MAX
/// ```
pub const MAX_N_CELLS: AbsNotch = 18446744073709551615;

#[allow(dead_code)]
/// The maximum is to have [`MAX_ROW_MAX_COL_RATIO`] times more rows than columns.
pub const MAX_ROW_MAX_COL_RATIO: AbsNotch = 4;

#[allow(dead_code)]
/// The maximum number of columns in a sheet.
///
/// Calculated as:
/// ```
/// (((MAX_N_CELLS / MAX_ROW_MAX_COL_RATIO) as f64).sqrt()) as AbsNotch
/// ```
pub const MAX_N_COLS: AbsNotch = 2147483648;

#[allow(dead_code)]
/// The maximum number of rows in a sheet.
///
/// Calculated as:
/// ```
/// MAX_N_COLS * MAX_ROW_MAX_COL_RATIO
/// ```
pub const MAX_N_ROWS: AbsNotch = 8589934592;

/// The scroll information from the surrounding Scrollable.
#[derive(Debug, Clone, Copy)]
pub struct ScrollInfo {
    pub relative_offset: scrollable::RelativeOffset,
    pub absolute_offset: scrollable::AbsoluteOffset,
    pub bounds: Rectangle,
}

impl Default for ScrollInfo {
    fn default() -> Self {
        Self::new()
    }
}

impl ScrollInfo {
    fn new() -> Self {
        Self {
            relative_offset: scrollable::RelativeOffset::default(),
            absolute_offset: scrollable::AbsoluteOffset::default(),
            bounds: Rectangle::with_size(Size::new(0.0, 0.0)),
        }
    }
}

/// A truss is a row or a column.
#[derive(Debug, Clone, Copy)]
pub enum Truss {
    Column,
    Row,
}

/// The absolute index of a cell along a truss, 0-indexed. For example, a cell on the second row
/// has notch 1 along the row truss.
pub type AbsNotch = usize;

/// The index of a cell along a truss, 0-indexed, relative to a certain other [`AbsNotch`], usually
/// that of the current first cell. For example, if the current first cell is at (2, 2), a cell on
/// the second row has relative position (3, 3). Negative values are also allowed to eg indicate
/// the relative position of off-screen cells.
pub type RelNotch = isize;

/// The size of a sheet, in `cols` and `rows`.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct SheetSize {
    pub cols: AbsNotch,
    pub rows: AbsNotch,
}

/// A cell's absolute position.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct CellAbsPos {
    pub col: AbsNotch,
    pub row: AbsNotch,
}

/// Converts a column's [`AbsNotch`] to the column fragment of a cellref, i.e. gives “A” for
/// [`AbsNotch`] “0”.
pub fn col_notch_to_col_ref(mut col: AbsNotch) -> String {
    let mut res = String::new();
    let n_letters = LETTERS.len() as AbsNotch;
    loop {
        res.insert(0, LETTERS[col % n_letters]);
        if col < n_letters {
            break;
        }
        col = (col / n_letters) - 1;
    }
    res
}

/// Converts a row's [`AbsNotch`] to the row fragment of a cellref, i.e. gives “1” for
/// [`AbsNotch`] “0”.
pub fn row_notch_to_row_ref(row: AbsNotch) -> String {
    (row + 1).to_string()
}

impl CellAbsPos {
    /// Converts a cell ref to a relative position.
    pub fn from_cellref(r: &str) -> Result<Self, Error> {
        if r.find(char::is_alphabetic) != Some(0) {
            return Err(Error::CellrefParseError);
        }
        let idx_num = r.find(char::is_numeric).ok_or(Error::CellrefParseError)?;
        let r_up = r.to_uppercase();
        let (col_ref, row_ref) = r_up.split_at(idx_num);

        let row: AbsNotch = row_ref.parse().map_err(|_| Error::CellrefParseError)?;

        let mut col: AbsNotch = 0;

        for (idx, c) in col_ref.chars().rev().enumerate() {
            let digit = LETTERS
                .iter()
                .position(|&l| l == c)
                .ok_or(Error::CellrefParseError)?;
            col += ((digit + 1) * LETTERS.len().pow(idx as u32)) as AbsNotch;
        }

        Ok(Self {
            col: col - 1,
            row: row - 1,
        })
    }

    /// Converts a cell's relative position to a cell ref.
    pub fn to_cellref(self) -> String {
        col_notch_to_col_ref(self.col) + &row_notch_to_row_ref(self.row)
    }

    /// Converts an absolute position into a position relative to a `base`.
    pub fn to_rel(self, base: CellAbsPos) -> CellRelPos {
        CellRelPos {
            col: (self.col as RelNotch) - (base.col as RelNotch),
            row: (self.row as RelNotch) - (base.row as RelNotch),
        }
    }

    /// Converts an absolute position to a numeric value between 0 and [`MAX_N_CELLS`] that can be
    /// used as an integer hash for e.g. [`nohash_hasher::IntMap`].
    pub fn to_hash(self) -> usize {
        ((self.row as u128 * MAX_N_COLS as u128) + self.col as u128) as usize
    }

    /// Converts a hash back into an absolute position.
    pub fn from_hash(hash: usize) -> Self {
        CellAbsPos {
            col: (hash as u128 % MAX_N_COLS as u128) as usize,
            row: (hash as u128 / MAX_N_COLS as u128) as usize,
        }
    }
}

impl Hash for CellAbsPos {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_hash().hash(state);
    }
}

impl fmt::Display for CellAbsPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CellAbsPos({}, {})", self.col, self.row)
    }
}

#[cfg(test)]
mod test_cell_abs_pos {
    use super::*;

    #[test]
    fn test_from_cellref() {
        let tests = [
            (String::from("A1"), CellAbsPos { row: 0, col: 0 }),
            (String::from("C2"), CellAbsPos { row: 1, col: 2 }),
            (String::from("AC99"), CellAbsPos { row: 98, col: 28 }),
            (String::from("AHV1"), CellAbsPos { row: 0, col: 905 }),
        ];
        for (case, expected) in tests {
            assert_eq!(CellAbsPos::from_cellref(&case), Ok(expected));
        }
    }

    #[test]
    fn test_col_notch_to_col_ref() {
        let tests = [(0, "A"), (2, "C"), (28, "AC"), (905, "AHV")];
        for (case, expected) in tests {
            assert_eq!(col_notch_to_col_ref(case), expected);
        }
    }

    #[test]
    fn test_to_cellref() {
        let tests = [
            (CellAbsPos { row: 0, col: 0 }, "A1"),
            (CellAbsPos { row: 1, col: 2 }, "C2"),
            (CellAbsPos { row: 98, col: 28 }, "AC99"),
            (CellAbsPos { row: 0, col: 905 }, "AHV1"),
        ];
        for (case, expected) in tests {
            assert_eq!(case.to_cellref(), expected);
        }
    }

    #[test]
    fn test_to_hash() {
        let abs_pos = CellAbsPos { row: 1, col: 0 };
        assert_eq!(abs_pos.to_hash(), MAX_N_COLS);
    }

    #[test]
    fn test_from_hash() {
        let expected = CellAbsPos { row: 1, col: 0 };
        assert_eq!(CellAbsPos::from_hash(MAX_N_COLS), expected);
    }
}

/// A cell's position relative to a certain cell, usually the current first cell.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct CellRelPos {
    pub col: RelNotch,
    pub row: RelNotch,
}

impl CellRelPos {
    /// Converts a position relative to a `base` into an absolute position.
    pub fn to_abs(self, base: CellAbsPos) -> Option<CellAbsPos> {
        let col = base.col as RelNotch + self.col;
        let row = base.row as RelNotch + self.row;
        if col < 0 || row < 0 {
            None
        } else {
            Some(CellAbsPos {
                col: col as AbsNotch,
                row: row as AbsNotch,
            })
        }
    }

    /// Converts a [`Point`], for example a cursor position, into a relative cell position.
    pub fn from_point(p: Point, viewport: &Rectangle, sheet_view: &SheetView) -> CellRelPos {
        let sv = sheet_view;
        // `p` translated from viewport space into grid widget space.
        let p_trans = Point {
            x: p.x - sv.left_header_width - viewport.x,
            y: p.y - sv.top_header_height - viewport.y,
        };
        CellRelPos {
            col: (p_trans.x / sv.cell_base_width).floor() as RelNotch,
            row: (p_trans.y / sv.cell_base_height).floor() as RelNotch,
        }
    }
}

impl fmt::Display for CellRelPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CellRelPos({}, {})", self.col, self.row)
    }
}

#[cfg(test)]
mod test_cell_rel_pos {
    use super::*;

    #[test]
    fn test_to_abs() {
        let rel_pos = CellRelPos { row: 2, col: 2 };
        let base = CellAbsPos { row: 2, col: 2 };
        let abs_pos = rel_pos.to_abs(base);
        assert_eq!(abs_pos, Some(CellAbsPos { row: 4, col: 4 }));
    }
}

/// A range of absolute cell positions, with a `start` and an `end`.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct CellRelRange {
    pub start: CellRelPos,
    pub end: CellRelPos,
}

impl CellRelRange {
    /// Returns this range but sorted such that earlier rows and columns are in the `start` field.
    pub fn sorted(&self) -> CellRelRange {
        let mut res = *self;
        if res.start.col > res.end.col {
            (res.start.col, res.end.col) = (res.end.col, res.start.col);
        }
        if res.start.row > res.end.row {
            (res.start.row, res.end.row) = (res.end.row, res.start.row);
        }
        res
    }

    /// Converts a cell range relative to a base into an absolute cell range.
    pub fn to_abs(self, base: CellAbsPos) -> Option<CellAbsRange> {
        Some(CellAbsRange {
            start: self.start.to_abs(base)?,
            end: self.end.to_abs(base)?,
        })
    }

    /// Returns whether this range contains a certain [`CellRelPos`].
    pub fn contains(&self, t: CellRelPos) -> bool {
        let sorted = self.sorted();
        t.row >= sorted.start.row
            && t.row <= sorted.end.row
            && t.col >= sorted.start.col
            && t.col <= sorted.end.col
    }
}

/// A range of relative cell positions, with a `start` and an `end`.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct CellAbsRange {
    pub start: CellAbsPos,
    pub end: CellAbsPos,
}

impl CellAbsRange {
    /// Creates a range based on two cellref strings such as `A1`, `C3`.
    pub fn from_cellref_explicit_range(cellref1: &str, cellref2: &str) -> Result<Self, Error> {
        Ok(CellAbsRange {
            start: CellAbsPos::from_cellref(cellref1)?,
            end: CellAbsPos::from_cellref(cellref2)?,
        })
    }

    /// Creates a range based on a cellref range expression such as `A1:C3`.
    pub fn from_cellref_range(s: &str) -> Result<Self, Error> {
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() != 2 {
            return Err(Error::CellrefParseError);
        }
        Self::from_cellref_explicit_range(parts[0], parts[1])
    }

    /// Returns this range but sorted such that earlier rows and columns are in the `start` field.
    pub fn sorted(&self) -> Self {
        let mut res = *self;
        if res.start.col > res.end.col {
            (res.start.col, res.end.col) = (res.end.col, res.start.col);
        }
        if res.start.row > res.end.row {
            (res.start.row, res.end.row) = (res.end.row, res.start.row);
        }
        res
    }

    /// Converts an absolute cell range to a cell range relative to a base.
    pub fn to_rel(self, base: CellAbsPos) -> CellRelRange {
        CellRelRange {
            start: self.start.to_rel(base),
            end: self.end.to_rel(base),
        }
    }

    /// Returns whether this range contains a certain [`CellAbsPos`].
    pub fn contains(&self, t: CellAbsPos) -> bool {
        let sorted = self.sorted();
        t.row >= sorted.start.row
            && t.row <= sorted.end.row
            && t.col >= sorted.start.col
            && t.col <= sorted.end.col
    }

    /// Converts an absolute cell range to a [`Vec`] of all cells inside it.
    pub fn expand(self) -> Vec<CellAbsPos> {
        let mut expanded = Vec::default();
        let sorted = self.sorted();
        for col in sorted.start.col..=sorted.end.col {
            for row in sorted.start.row..=sorted.end.row {
                expanded.push(CellAbsPos { col, row });
            }
        }
        expanded
    }
}

#[cfg(test)]
mod test_abs_cell_range {
    use super::*;

    #[test]
    fn test_from_cellref_explicit_range() {
        let range = CellAbsRange::from_cellref_explicit_range("A1", "C3");
        let expected = CellAbsRange {
            start: CellAbsPos { col: 0, row: 0 },
            end: CellAbsPos { col: 2, row: 2 },
        };
        assert_eq!(range, Ok(expected));
    }

    #[test]
    fn test_from_cellref_range() {
        let range = CellAbsRange::from_cellref_range("A1:C3".to_string());
        let expected = CellAbsRange {
            start: CellAbsPos { col: 0, row: 0 },
            end: CellAbsPos { col: 2, row: 2 },
        };
        assert_eq!(range, Ok(expected));
    }

    #[test]
    fn test_expand() {
        let range = CellAbsRange {
            start: CellAbsPos { col: 0, row: 0 },
            end: CellAbsPos { col: 2, row: 2 },
        };
        let expanded = range.expand();
        let expected = vec![
            CellAbsPos { col: 0, row: 0 },
            CellAbsPos { col: 0, row: 1 },
            CellAbsPos { col: 0, row: 2 },
            CellAbsPos { col: 1, row: 0 },
            CellAbsPos { col: 1, row: 1 },
            CellAbsPos { col: 1, row: 2 },
            CellAbsPos { col: 2, row: 0 },
            CellAbsPos { col: 2, row: 1 },
            CellAbsPos { col: 2, row: 2 },
        ];
        assert_eq!(expanded, expected);
    }
}

/// A truss that the user has resized. The user will only resize some trusses. The rest will remain
/// at their default size.
#[derive(Debug, Clone, Copy)]
pub struct ResizedTruss {
    notch: AbsNotch,
    #[allow(dead_code)]
    size: Pixels,
}

/// A list of all of the trusses (rows or columns) that the user has resized.
#[derive(Debug, Clone)]
pub struct ResizedTrussVec {
    vec: Vec<ResizedTruss>,
}

impl ResizedTrussVec {
    fn new() -> Self {
        Self {
            vec: Vec::default(),
        }
    }

    /// Get all of the resized trusses up to a certain [`AbsNotch`].
    pub fn get_up_to(&self, max_notch: AbsNotch) -> &[ResizedTruss] {
        for (idx, resized_truss) in self.vec.iter().enumerate() {
            if resized_truss.notch >= max_notch {
                return &self.vec[0..idx];
            }
        }
        &self.vec[..]
    }

    /// Add a resized truss.
    pub fn add(&mut self, new_resized_truss: ResizedTruss) {
        let mut predecessor_idx = None;
        for (idx, resized_truss) in self.vec.iter().enumerate() {
            if resized_truss.notch >= new_resized_truss.notch {
                break;
            }
            predecessor_idx = Some(idx);
        }
        let new_idx = match predecessor_idx {
            Some(x) => x + 1,
            None => 0,
        };
        self.vec.insert(new_idx, new_resized_truss);
    }
}

#[cfg(test)]
mod test_resized_truss_vec {
    use super::*;

    #[test]
    fn test() {
        let mut rtv = ResizedTrussVec::new();
        rtv.add(ResizedTruss {
            notch: 7,
            size: iced::Pixels(100.0),
        });
        rtv.add(ResizedTruss {
            notch: 3,
            size: iced::Pixels(100.0),
        });
        rtv.add(ResizedTruss {
            notch: 9,
            size: iced::Pixels(100.0),
        });
        let res = rtv.get_up_to(8);
        assert_eq!(res.len(), 2);
        assert_eq!(res[0].notch, 3);
        assert_eq!(res[1].notch, 7);
    }
}

/// Contains the raw dimension data for a sheet, which is then processed into a more detailed
/// [`SheetView`].
#[derive(Debug, Clone)]
pub struct SheetMetrics {
    n_cols: AbsNotch,
    n_rows: AbsNotch,
    cell_base_width: f32,
    cell_base_height: f32,
    left_header_width: f32,
    top_header_height: f32,
    cell_x_padding: f32,
    cell_y_padding: f32,
    cell_border_width: f32,
    resized_cols: ResizedTrussVec,
    resized_rows: ResizedTrussVec,
}

impl Default for SheetMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl SheetMetrics {
    fn new() -> Self {
        let mut ret = Self {
            n_rows: 500,
            n_cols: 500,
            cell_base_height: 30.0,
            cell_base_width: 180.0,
            left_header_width: 50.0,
            top_header_height: 30.0,
            cell_x_padding: 10.0,
            cell_y_padding: 5.0,
            cell_border_width: 2.0,
            resized_cols: ResizedTrussVec::new(),
            resized_rows: ResizedTrussVec::new(),
        };
        ret.resized_cols.add(ResizedTruss {
            notch: 7,
            size: Pixels(100.0),
        });
        ret.resized_cols.add(ResizedTruss {
            notch: 3,
            size: Pixels(100.0),
        });
        ret.resized_rows.add(ResizedTruss {
            notch: 7,
            size: Pixels(100.0),
        });
        ret.resized_rows.add(ResizedTruss {
            notch: 3,
            size: Pixels(100.0),
        });
        ret
    }
}

/// Takes the raw dimension data from [`SheetMetrics`] and processes it into all of the metrics
/// needed to display the visible part of a sheet.
#[derive(Debug, Clone)]
pub struct SheetView {
    pub n_cols: AbsNotch,
    pub n_rows: AbsNotch,
    pub cell_base_width: f32,
    pub cell_base_height: f32,
    pub left_header_width: f32,
    pub top_header_height: f32,
    pub cell_x_padding: f32,
    pub cell_y_padding: f32,
    pub cell_border_width: f32,
    pub resized_cols: ResizedTrussVec,
    pub resized_rows: ResizedTrussVec,
    pub sheet_width: f32,
    pub sheet_height: f32,
    pub x_scroll_end: f32,
    pub y_scroll_end: f32,
    pub first_visible_col: AbsNotch,
    pub first_visible_row: AbsNotch,
    pub last_visible_col: AbsNotch,
    pub last_visible_row: AbsNotch,
}

impl SheetView {
    /// Creates a [`SheetView`] from [`SheetMetrics`] and [`ScrollInfo`].
    pub fn new(metrics: &SheetMetrics, scroll_info: &ScrollInfo) -> Self {
        // TODO: Scaling

        let sheet_width = metrics.cell_base_width * metrics.n_cols as f32;
        let sheet_height = metrics.cell_base_height * metrics.n_rows as f32;

        let bottom_safety_margin = 75.0;

        let x_scroll_end = sheet_width + metrics.cell_base_width;
        let y_scroll_end = sheet_height + metrics.cell_base_height + bottom_safety_margin;

        let first_visible_col =
            (scroll_info.absolute_offset.x / metrics.cell_base_width).floor() as AbsNotch;
        let first_visible_row =
            (scroll_info.absolute_offset.y / metrics.cell_base_height).floor() as AbsNotch;
        let last_visible_col = cmp::min(
            ((scroll_info.absolute_offset.x + scroll_info.bounds.width) / metrics.cell_base_width)
                .floor() as AbsNotch,
            metrics.n_cols - 1,
        );
        let last_visible_row = cmp::min(
            ((scroll_info.absolute_offset.y + scroll_info.bounds.height) / metrics.cell_base_height)
                .floor() as AbsNotch,
            metrics.n_rows - 1,
        );

        Self {
            n_cols: metrics.n_cols,
            n_rows: metrics.n_rows,
            cell_base_width: metrics.cell_base_width,
            cell_base_height: metrics.cell_base_height,
            left_header_width: metrics.left_header_width,
            top_header_height: metrics.top_header_height,
            cell_x_padding: metrics.cell_x_padding,
            cell_y_padding: metrics.cell_y_padding,
            cell_border_width: metrics.cell_border_width,
            resized_cols: metrics.resized_cols.clone(),
            resized_rows: metrics.resized_rows.clone(),

            sheet_width,
            sheet_height,
            x_scroll_end,
            y_scroll_end,
            first_visible_col,
            first_visible_row,
            last_visible_col,
            last_visible_row,
        }
    }
}
