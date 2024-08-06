// Copyright (C) 2024 一梦全能 team
//
// This file is part of ThunderMonkey.
//
// ThunderMonkey is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ThunderMonkey is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ThunderMonkey.  If not, see <http://www.gnu.org/licenses/>.

mod arg_parse;
mod frontend;
mod preprocessor;

use arg_parse::{Mode, ParsedArgs};
use preprocessor::preprocess;
use std::fs::{read_to_string, File};
use std::io::Write;

/// 每个人承担自己的风险！
#[macro_export]
macro_rules! risk {
    ($expression:expr, $pattern:pat => $extracted_expression:expr) => {
        match $expression {
            $pattern => $extracted_expression,
            _ => unreachable!(),
        }
    };
}

fn compile() -> Result<(), Box<dyn std::error::Error>> {
    let ParsedArgs { mode, input, output } = arg_parse::parse(std::env::args())?;
    let code = preprocess(read_to_string(input)?);
    // let code = read_to_string(input)?;
    let ast = frontend::parser::parse(&code)?;
    let mut f = File::create(output)?;
    match mode {
        Mode::Debug => {
            println!("使用调试模式");
            write!(f, "{ast:#?}")?;
        }
        Mode::Optimization => {
            println!("使用优化模式");
            write!(f, "{ast:#?}")?;
        }
    }
    Ok(())
}

fn main() {
    if let Err(s) = compile() {
        println!("{s}");
        std::process::exit(1);
    }
}
