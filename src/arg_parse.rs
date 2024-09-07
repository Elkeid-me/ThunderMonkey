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

use std::env::Args;

pub enum Mode {
    Debug,
    Optimization,
}

pub struct ParsedArgs {
    pub mode: Mode,
    pub input: String,
    pub output: String,
}

pub fn parse(args: Args) -> Result<ParsedArgs, String> {
    let mut args = args.skip(1);
    let mut mode = Mode::Debug;
    let mut output_flag = false;
    let mut assem_output_flag = false;
    let mut output = String::new();
    let mut input = String::new();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-o" => output_flag = true,
            "-O1" => mode = Mode::Optimization,
            "-S" => assem_output_flag = true,
            _ => {
                if output_flag {
                    output = arg;
                    output_flag = false;
                } else {
                    input = arg;
                }
            }
        }
    }
    if !assem_output_flag {
        return Err("需要输入 `-S` 参数，指定汇编输出".to_string());
    }
    if output.is_empty() {
        return Err("没有指定输出文件".to_string());
    }
    if input.is_empty() {
        return Err("没有指定输入文件".to_string());
    }
    Ok(ParsedArgs { mode, input, output })
}
