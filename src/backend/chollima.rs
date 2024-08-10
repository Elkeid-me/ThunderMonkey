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

use crate::{frontend::ast::Definition, Handler, HashMap};
use std::collections::VecDeque;

pub enum GlobalItem {
    Variable { words: usize, init: Option<Vec<u32>> },
    Function { code: VecDeque<IRItem>, context: HashMap<Handler, usize>, arg_handlers: Vec<Handler> },
}

pub struct IR {
    pub symbol_table: HashMap<Handler, Definition>,
    pub ir: HashMap<Handler, GlobalItem>,
}

#[derive(Clone, Copy)]
pub enum OpType {
    Int,
    Float,
    Void,
}

pub enum IRItem {
    AddInt,
    SubInt,
    MulInt,
    DivInt,

    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,

    Mod,

    Sll,
    Slr,
    Sar,

    And,
    Or,
    Xor,

    EqInt,
    NeInt,
    LeInt,
    LtInt,
    GeInt,
    GtInt,

    EqFloat,
    NeFloat,
    LeFloat,
    LtFloat,
    GeFloat,
    GtFloat,

    PushFloat(f32),
    PushInt(i32),
    PopWords(usize),

    Double,

    CvtIF,
    CvtFI,

    Br {
        then: Handler,
        or_else: Handler,
    },

    Jmp {
        label: Handler,
    },

    CallFloat {
        function: Handler,
        num_args: usize,
    },

    CallInt {
        function: Handler,
        num_args: usize,
    },

    CallVoid {
        function: Handler,
        num_args: usize,
    },

    Load,

    Store,

    /// 将某个变量的 **地址** 加载到栈顶
    LoadAddr {
        var: Handler,
    },

    RetFloat,
    RetInt,

    Label {
        addr: Handler,
    },

    StartTime {
        lineno: i32,
    },
    StopTime {
        lineno: i32,
    },
}

impl std::fmt::Display for IRItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRItem::AddInt => write!(f, "add_int"),
            IRItem::SubInt => write!(f, "sub_int"),
            IRItem::MulInt => write!(f, "mul_int"),
            IRItem::DivInt => write!(f, "div_int"),

            IRItem::AddFloat => write!(f, "add_float"),
            IRItem::SubFloat => write!(f, "sub_float"),
            IRItem::MulFloat => write!(f, "mul_float"),
            IRItem::DivFloat => write!(f, "div_float"),

            IRItem::Mod => write!(f, "mod_int"),
            IRItem::Sll => write!(f, "sll"),
            IRItem::Slr => write!(f, "slr"),
            IRItem::Sar => write!(f, "sar"),
            IRItem::And => write!(f, "and"),
            IRItem::Or => write!(f, "or"),
            IRItem::Xor => write!(f, "xor"),

            IRItem::EqInt => write!(f, "eq_int"),
            IRItem::NeInt => write!(f, "ne_int"),
            IRItem::LeInt => write!(f, "le_int"),
            IRItem::LtInt => write!(f, "lt_int"),
            IRItem::GeInt => write!(f, "ge_int"),
            IRItem::GtInt => write!(f, "gt_int"),

            IRItem::EqFloat => write!(f, "eq_float"),
            IRItem::NeFloat => write!(f, "ne_float"),
            IRItem::LeFloat => write!(f, "le_float"),
            IRItem::LtFloat => write!(f, "lt_float"),
            IRItem::GeFloat => write!(f, "ge_float"),
            IRItem::GtFloat => write!(f, "gt_float"),

            IRItem::PushFloat(f_) => write!(f, "push_float {f_}"),
            IRItem::PushInt(i) => write!(f, "push_int {i}"),
            IRItem::PopWords(size) => write!(f, "pop_words {size}"),
            IRItem::Double => write!(f, "double"),

            IRItem::CvtIF => write!(f, "cvt_i_f"),
            IRItem::CvtFI => write!(f, "cvt_f_i"),

            IRItem::Br { then, or_else } => write!(f, "br label_{then}, label_{or_else}"),
            IRItem::Jmp { label } => write!(f, "jmp label_{label}"),
            IRItem::CallFloat { function, num_args } => write!(f, "call_float .F{function}, {num_args}"),
            IRItem::CallInt { function, num_args } => write!(f, "call_int .F{function}, {num_args}"),
            IRItem::CallVoid { function, num_args } => write!(f, "call_void .F{function}, {num_args}"),

            IRItem::RetFloat => write!(f, "ret_float"),
            IRItem::RetInt => write!(f, "ret_int"),

            IRItem::Load => write!(f, "load"),
            IRItem::Store => write!(f, "store"),
            IRItem::LoadAddr { var } => write!(f, "load_addr .V{var}"),

            IRItem::Label { addr } => write!(f, "label_{addr}"),

            IRItem::StartTime { lineno } => write!(f, "start_time {lineno}"),
            IRItem::StopTime { lineno } => write!(f, "stop_time {lineno}"),
        }
    }
}
