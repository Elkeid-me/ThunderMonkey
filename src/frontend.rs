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

pub mod ast;
mod error;
mod ir_generator;
pub mod parser;
pub mod ty;

use crate::backend::chollima::IR;


pub fn generator_ir(src: &str) -> Result<IR, Box<dyn std::error::Error>> {
    let translation_unit = parser::parse(src)?;
    Ok(ir_generator::generator_ir(translation_unit))
}
