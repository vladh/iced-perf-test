// © 2022 Vlad-Stefan Harbuz <vlad@vladh.net>
// SPDX-License-Identifier: AGPL-3.0-only
// “Cellsum” is a registered trademark and no rights to it are ceded.

//! Provides CSV file reading/writing.

use crate::sheet::CellAbsPos;
use crate::storage::Sheet;

#[derive(Debug)]
#[allow(dead_code)]
pub enum Error {
    CsvError(csv::Error),
    IoError(std::io::Error),
    StorageError(crate::storage::Error),
}

pub fn write(sheet: &Sheet, filepath: &str) -> Result<(), Error> {
    let sheet_size = sheet.get_sheet_size();
    let mut writer = csv::Writer::from_path(filepath).map_err(Error::CsvError)?;
    for row in 0..sheet_size.rows {
        let mut row_vals = vec!["".to_string(); sheet_size.cols];
        for (col, row_val) in row_vals.iter_mut().enumerate().take(sheet_size.cols) {
            let val = sheet.get_value(CellAbsPos { col, row });
            if let Some(val) = val {
                *row_val = val.to_string();
            }
        }
        writer.write_record(row_vals).map_err(Error::CsvError)?;
    }
    writer.flush().map_err(Error::IoError)?;
    Ok(())
}

pub fn read(sheet: &mut Sheet, filepath: &str) -> Result<(), Error> {
    let mut reader = csv::ReaderBuilder::new()
        .has_headers(false)
        .from_path(filepath)
        .map_err(Error::CsvError)?;
    let mut row = 0;
    for result in reader.records() {
        let record = result.map_err(Error::CsvError)?;
        let mut col = 0;
        for field in record.iter() {
            sheet
                .set_formula(CellAbsPos { col, row }, field)
                .map_err(Error::StorageError)?;
            col += 1;
        }
        row += 1;
    }
    Ok(())
}
