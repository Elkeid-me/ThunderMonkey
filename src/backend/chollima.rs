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

use crate::{Handler, HashMap};
use std::collections::VecDeque;
use crate::frontend::ast::Definition;

pub struct IR {
    pub ast: Vec<Handler>,
    pub defs: HashMap<Handler, VecDeque<IRItem>>,
    pub symbol_table: HashMap<Handler, Definition>,
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

    DefWords {
        var: Handler,
        size: usize,
    },
}

impl std::fmt::Display for IRItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRItem::AddInt => writeln!(f, "add_int"),
            IRItem::SubInt => writeln!(f, "sub_int"),
            IRItem::MulInt => writeln!(f, "mul_int"),
            IRItem::DivInt => writeln!(f, "div_int"),

            IRItem::AddFloat => writeln!(f, "add_float"),
            IRItem::SubFloat => writeln!(f, "sub——float"),
            IRItem::MulFloat => writeln!(f, "mul_float"),
            IRItem::DivFloat => writeln!(f, "div_float"),

            IRItem::Mod => writeln!(f, "mod_int"),
            IRItem::Sll => writeln!(f, "sll"),
            IRItem::Slr => writeln!(f, "slr"),
            IRItem::Sar => writeln!(f, "sar"),
            IRItem::And => writeln!(f, "and"),
            IRItem::Or => writeln!(f, "or"),
            IRItem::Xor => writeln!(f, "xor"),

            IRItem::EqInt => writeln!(f, "eq_int"),
            IRItem::NeInt => writeln!(f, "ne_int"),
            IRItem::LeInt => writeln!(f, "le_int"),
            IRItem::LtInt => writeln!(f, "lt_int"),
            IRItem::GeInt => writeln!(f, "ge_int"),
            IRItem::GtInt => writeln!(f, "gt_int"),

            IRItem::EqFloat => writeln!(f, "eq_float"),
            IRItem::NeFloat => writeln!(f, "ne_float"),
            IRItem::LeFloat => writeln!(f, "le_float"),
            IRItem::LtFloat => writeln!(f, "lt_float"),
            IRItem::GeFloat => writeln!(f, "ge_float"),
            IRItem::GtFloat => writeln!(f, "gt_float"),

            IRItem::PushFloat(f_) => writeln!(f, "push_float {f_}"),
            IRItem::PushInt(i) => writeln!(f, "push_int {i}"),
            IRItem::PopWords(size) => writeln!(f, "pop_words {size}"),
            IRItem::Double => writeln!(f, "double"),

            IRItem::CvtIF => writeln!(f, "cvt_i_f"),
            IRItem::CvtFI => writeln!(f, "cvt_f_i"),

            IRItem::Br { then, or_else } => writeln!(f, "br .L{then}, .L{or_else}"),
            IRItem::Jmp { label } => writeln!(f, "jmp .L{label}"),
            IRItem::CallFloat { function, num_args } => writeln!(f, "call_float .F{function}, {num_args}"),
            IRItem::CallInt { function, num_args } => writeln!(f, "call_int .F{function}, {num_args}"),
            IRItem::RetFloat => writeln!(f, "ret_float"),
            IRItem::RetInt => writeln!(f, "ret_int"),

            IRItem::CallVoid { function, num_args } => writeln!(f, "call_void .F{function}, {num_args}"),
            IRItem::Load => writeln!(f, "load"),
            IRItem::Store => writeln!(f, "store"),
            IRItem::LoadAddr { var } => writeln!(f, "load_addr .V{var}"),

            IRItem::Label { addr } => writeln!(f, ".L{addr}"),

            IRItem::DefWords { var: handler, size } => writeln!(f, "def_words .V{handler}, {size}"),
        }
    }
}
