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

use super::armv7::{Inst::*, Reg::*, *};
use super::chollima::*;
use crate::frontend::ast::Definition;
use crate::{Handler, HashMap};
use std::collections::VecDeque;

///  .......
/// |-------|
/// | arg 2 |
/// |-------|
/// | arg 1 |
/// |-------|
/// |old bp |
/// |-------|
/// |   ra  |
/// |-------| <- bp
/// |
/// |

fn function(
    handler: Handler,
    code: &VecDeque<IRItem>,
    context: &HashMap<Handler, usize>,
    arg_handlers: &Vec<Handler>,
    symbol_table: &HashMap<Handler, Definition>,
) -> ARM {
    let mut c = HashMap::default();

    for (i, &handler) in arg_handlers.iter().enumerate() {
        c.insert(handler, (i as i32 + 2) * 4);
    }

    let mut stack_size = 0;
    for (&handler, &size) in context.iter() {
        stack_size -= size as i32 * 4;
        c.insert(handler, stack_size);
    }

    let mut asm = ARM::new();
    asm.add_directive(Directive::Text);

    let is_entry = symbol_table.get(&handler).unwrap().id.as_str() == "main";

    if is_entry {
        asm.add_directive(Directive::Global("main".to_string()));
        asm.add_label("main".to_string());
    } else {
        asm.add_directive(Directive::Global(format!("__zvezda_label_{handler}")));
        asm.add_label(format!("__zvezda_label_{handler}"));
    }

    asm.add_inst(Push(R11));
    asm.add_inst(Push(R14));
    asm.add_inst(Mov(R11, R13));
    asm.add_inst(Mov32(R0, stack_size));
    asm.add_inst(Add(R13, R0, R13));
    for ir in code {
        match ir {
            IRItem::AddInt => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Add(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::SubInt => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Sub(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::MulInt => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Mul(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::DivInt => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Mov32Label(R2, "__aeabi_idiv".to_string()));
                asm.add_inst(Blx(R2));
                asm.add_inst(Push(R0));
            }

            IRItem::AddFloat => {
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VAddF32(S0, S0, S1));
                asm.add_inst(VPush(S0));
            }
            IRItem::SubFloat => {
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VSubF32(S0, S0, S1));
                asm.add_inst(VPush(S0));
            }
            IRItem::MulFloat => {
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VMulF32(S0, S0, S1));
                asm.add_inst(VPush(S0));
            }
            IRItem::DivFloat => {
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VDivF32(S0, S0, S1));
                asm.add_inst(VPush(S0));
            }

            IRItem::Mod => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Mov32Label(R2, "__aeabi_idivmod".to_string()));
                asm.add_inst(Blx(R2));
                asm.add_inst(Push(R1));
            }

            IRItem::Sll => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Lsl(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::Slr => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Lsr(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::Sar => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Asr(R0, R0, R1));
                asm.add_inst(Push(R0));
            }

            IRItem::And => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(And(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::Or => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Orr(R0, R0, R1));
                asm.add_inst(Push(R0));
            }
            IRItem::Xor => {
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Eor(R0, R0, R1));
                asm.add_inst(Push(R0));
            }

            IRItem::EqInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Eq(R2));
                asm.add_inst(Push(R2));
            }
            IRItem::NeInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Ne(R2));
                asm.add_inst(Push(R2));
            }
            IRItem::LeInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Le(R2));
                asm.add_inst(Push(R2));
            }
            IRItem::LtInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Lt(R2));
                asm.add_inst(Push(R2));
            }
            IRItem::GeInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Ge(R2));
                asm.add_inst(Push(R2));
            }
            IRItem::GtInt => {
                asm.add_inst(Eor(R2, R2, R2));
                asm.add_inst(Pop(R1));
                asm.add_inst(Pop(R0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(Load1Gt(R2));
                asm.add_inst(Push(R2));
            }

            IRItem::EqFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Eq(S2));
                asm.add_inst(VPush(S2));
            }
            IRItem::NeFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Ne(S2));
                asm.add_inst(VPush(S2));
            }
            IRItem::LeFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Le(S2));
                asm.add_inst(VPush(S2));
            }
            IRItem::LtFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Lt(S2));
                asm.add_inst(VPush(S2));
            }
            IRItem::GeFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Ge(S2));
                asm.add_inst(VPush(S2));
            }
            IRItem::GtFloat => {
                asm.add_inst(VEor(S2, S2, S2));
                asm.add_inst(VPop(S1));
                asm.add_inst(VPop(S0));
                asm.add_inst(VCmpF32(S0, S1));
                asm.add_inst(VLdr1Gt(S2));
                asm.add_inst(VPush(S2));
            }

            IRItem::PushFloat(f) => {
                asm.add_inst(Mov32(R0, f.to_bits() as i32));
                asm.add_inst(Push(R0));
            }
            IRItem::PushInt(i) => {
                asm.add_inst(Mov32(R0, *i));
                asm.add_inst(Push(R0));
            }

            IRItem::PopWords(words) => {
                for _i in 0..*words {
                    asm.add_inst(Pop(R0));
                }
            }
            IRItem::Double => {
                asm.add_inst(Pop(R0));
                asm.add_inst(Push(R0));
                asm.add_inst(Push(R0));
            }
            IRItem::CvtIF => {
                asm.add_inst(Pop(R0));
                asm.add_inst(Mov32Label(R1, "__aeabi_i2f".to_string()));
                asm.add_inst(Blx(R1));
                asm.add_inst(VPush(S0));
            }
            IRItem::CvtFI => {
                asm.add_inst(VPop(S0));
                asm.add_inst(Mov32Label(R1, "__aeabi_f2iz".to_string()));
                asm.add_inst(Blx(R1));
                asm.add_inst(Push(R0));
            }
            IRItem::Br { then, or_else } => {
                asm.add_inst(Mov32Label(R2, format!("__zvezda_label_{then}")));
                asm.add_inst(Mov32Label(R3, format!("__zvezda_label_{or_else}")));
                asm.add_inst(Pop(R0));
                asm.add_inst(Mov32(R1, 0));
                asm.add_inst(Cmp(R0, R1));
                asm.add_inst(BxNe(R2));
                asm.add_inst(Bx(R3));
            }
            IRItem::Jmp { label } => {
                asm.add_inst(Mov32Label(R0, format!("__zvezda_label_{label}")));
                asm.add_inst(Bx(R0));
            }
            IRItem::CallFloat { function, num_args } => {
                let mut num_args = *num_args;
                let id = symbol_table.get(function).unwrap().id.as_str();
                match id {
                    "getint" => asm.add_inst(Mov32Label(R8, format!("getint"))),
                    "getch" => asm.add_inst(Mov32Label(R8, format!("getch"))),
                    "getfloat" => asm.add_inst(Mov32Label(R8, format!("getfloat"))),
                    "getarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getarray")));
                    }
                    "getfarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getfarray")));
                    }
                    "putint" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putint")));
                    }
                    "putch" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putch")));
                    }
                    "putfloat" => {
                        asm.add_inst(VPop(S0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putfloat")));
                    }
                    "putarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putarray")));
                    }
                    "putfarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putfarray")));
                    }
                    "putf" => asm.add_inst(Mov32Label(R8, format!("putf"))),
                    "starttime" => asm.add_inst(Mov32Label(R8, format!("starttime"))),
                    "stoptime" => asm.add_inst(Mov32Label(R8, format!("stoptime"))),
                    _ => asm.add_inst(Mov32Label(R8, format!("__zvezda_label_{function}"))),
                }
                asm.add_inst(Blx(R8));
                asm.add_inst(Mov32(R0, num_args as i32 * 4));
                asm.add_inst(Add(R13, R0, R13));
                asm.add_inst(VPush(S0));
            }
            IRItem::CallInt { function, num_args } => {
                let mut num_args = *num_args;
                let id = symbol_table.get(function).unwrap().id.as_str();
                match id {
                    "getint" => asm.add_inst(Mov32Label(R8, format!("getint"))),
                    "getch" => asm.add_inst(Mov32Label(R8, format!("getch"))),
                    "getfloat" => asm.add_inst(Mov32Label(R8, format!("getfloat"))),
                    "getarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getarray")));
                    }
                    "getfarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getfarray")));
                    }
                    "putint" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putint")));
                    }
                    "putch" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putch")));
                    }
                    "putfloat" => {
                        asm.add_inst(VPop(S0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putfloat")));
                    }
                    "putarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putarray")));
                    }
                    "putfarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putfarray")));
                    }
                    "putf" => asm.add_inst(Mov32Label(R8, format!("putf"))),
                    "starttime" => asm.add_inst(Mov32Label(R8, format!("starttime"))),
                    "stoptime" => asm.add_inst(Mov32Label(R8, format!("stoptime"))),
                    _ => asm.add_inst(Mov32Label(R8, format!("__zvezda_label_{function}"))),
                }
                asm.add_inst(Blx(R8));
                asm.add_inst(Mov32(R0, num_args as i32 * 4));
                asm.add_inst(Add(R13, R0, R13));
                asm.add_inst(Push(R0));
            }
            IRItem::CallVoid { function, num_args } => {
                let mut num_args = *num_args;
                let id = symbol_table.get(function).unwrap().id.as_str();
                match id {
                    "getint" => asm.add_inst(Mov32Label(R8, format!("getint"))),
                    "getch" => asm.add_inst(Mov32Label(R8, format!("getch"))),
                    "getfloat" => asm.add_inst(Mov32Label(R8, format!("getfloat"))),
                    "getarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getarray")));
                    }
                    "getfarray" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("getfarray")));
                    }
                    "putint" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putint")));
                    }
                    "putch" => {
                        asm.add_inst(Pop(R0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putch")));
                    }
                    "putfloat" => {
                        asm.add_inst(VPop(S0));
                        num_args -= 1;
                        asm.add_inst(Mov32Label(R8, format!("putfloat")));
                    }
                    "putarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putarray")));
                    }
                    "putfarray" => {
                        asm.add_inst(Pop(R0));
                        asm.add_inst(Pop(R1));
                        num_args -= 2;
                        asm.add_inst(Mov32Label(R8, format!("putfarray")));
                    }
                    "putf" => asm.add_inst(Mov32Label(R8, format!("putf"))),
                    "starttime" => asm.add_inst(Mov32Label(R8, format!("starttime"))),
                    "stoptime" => asm.add_inst(Mov32Label(R8, format!("stoptime"))),
                    _ => asm.add_inst(Mov32Label(R8, format!("__zvezda_label_{function}"))),
                }
                asm.add_inst(Blx(R8));
                asm.add_inst(Mov32(R0, num_args as i32 * 4));
                asm.add_inst(Add(R13, R0, R13));
            }
            IRItem::Load => {
                asm.add_inst(Pop(R0));
                asm.add_inst(Ldr(R0, R0));
                asm.add_inst(Push(R0));
            }
            IRItem::Store => {
                asm.add_inst(Pop(R0));
                asm.add_inst(Pop(R1));
                asm.add_inst(Sdr(R0, R1));
            }
            IRItem::LoadAddr { var } => {
                if c.contains_key(var) {
                    let offset = c.get(var).unwrap();
                    asm.add_inst(Mov32(R0, *offset));
                    asm.add_inst(Add(R0, R0, R11));
                    asm.add_inst(Push(R0));
                } else {
                    asm.add_inst(Mov32Label(R0, format!("__zvezda_label_{var}")));
                    asm.add_inst(Push(R0));
                }
            }
            IRItem::RetFloat => {
                asm.add_inst(VPop(S0));
                asm.add_inst(Mov(R13, R11));
                asm.add_inst(Pop(R14));
                asm.add_inst(Pop(R11));
                asm.add_inst(Bx(R14));
            }
            IRItem::RetInt => {
                asm.add_inst(Pop(R0));
                asm.add_inst(Mov(R13, R11));
                asm.add_inst(Pop(R14));
                asm.add_inst(Pop(R11));
                asm.add_inst(Bx(R14));
            }
            IRItem::Label { addr } => asm.add_label(format!("__zvezda_label_{addr}")),
        }
    }
    asm
}

fn global_variable(handler: Handler, words: usize, init: &Option<Vec<u32>>) -> ARM {
    let mut asm = ARM::new();

    asm.add_directive(Directive::Data);
    asm.add_directive(Directive::Global(format!("__zvezda_label_{handler}")));
    asm.add_label(format!("__zvezda_label_{handler}"));

    match init {
        Some(list) => asm.add_directive(Directive::Word(list.clone())),
        None => asm.add_directive(Directive::Zero(words)),
    }
    asm
}

pub fn asm_generate(ir: IR) -> ARM {
    let IR { symbol_table, ir } = &ir;

    let mut asm = ARM::new();
    for (&handler, item) in ir {
        match item {
            GlobalItem::Variable { words, init } => asm.extend(global_variable(handler, *words, init)),
            GlobalItem::Function { code, context, arg_handlers } => {
                asm.extend(function(handler, code, context, arg_handlers, symbol_table));
            }
        }
    }

    asm
}
