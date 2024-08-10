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
mod backend;
mod frontend;
mod preprocessor;

use arg_parse::{Mode, ParsedArgs};
use backend::chollima::IR;
use preprocessor::preprocess;
use std::fs::{read_to_string, File};
use std::io::Write;

type Handler = u32;
type HashMap<K, V> = rustc_hash::FxHashMap<K, V>;
type HashSet<V> = rustc_hash::FxHashSet<V>;

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
    let ir = frontend::generator_ir(&code)?;

    if cfg!(feature = "debug_output") {
        let IR { symbol_table, ir: i } = &ir;
        println!("{:#?}", symbol_table);

        for (handler, def) in i {
            match def {
                backend::chollima::GlobalItem::Variable { words, init } => (),
                backend::chollima::GlobalItem::Function { code, context, arg_handlers } => {
                    println!("{handler}");
                    for i in code {
                        println!("    {i}");
                    }
                }
            }
        }
    }

    let asm = backend::hyoksin::asm_generate(ir);
    let mut f = File::create(output)?;
    match mode {
        Mode::Debug => println!("使用调试模式"),
        Mode::Optimization => println!("使用优化模式"),
    }

    write!(f, ".macro mov32, reg, val\n    movw \\reg, #:lower16:\\val\n    movt \\reg, #:upper16:\\val\n.endm\n")?;

    for i in asm {
        write!(f, "{i}")?;
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn set_stack() {
    unsafe {
        use libc::{rlim_t, rlimit, setrlimit, RLIMIT_STACK};
        let mut limit = rlimit { rlim_cur: (256 * 1024 * 1024) as rlim_t, rlim_max: (256 * 1024 * 1024) as rlim_t };
        setrlimit(RLIMIT_STACK, &mut limit as *mut rlimit);
    }
}

#[cfg(not(target_os = "linux"))]
fn set_stack() {}

fn main() {
    set_stack();
    if let Err(s) = compile() {
        println!("{s}");
        std::process::exit(1);
    }
}
