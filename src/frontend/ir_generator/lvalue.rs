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

use super::Generator;
use crate::backend::chollima::*;
use crate::frontend::{ast::Expr, ast::ExprInner::*, ty::Type};
use std::collections::VecDeque;

macro_rules! assign_helper {
    ($generator: expr, $l: expr, $r: expr, $op: path) => {{
        let mut ir = $generator.expr_lvalue($l);
        ir.extend([IRItem::Double, IRItem::Double, IRItem::Load]);
        let ty = match $l.ty {
            Type::Int => OpType::Int,
            Type::Float => OpType::Float,
            _ => unreachable!(),
        };
        ir.extend($generator.expr_rvalue($r, ty));
        ir.extend([$op, IRItem::Store]);
        ir
    }};
    ($generator: expr, $l: expr, $r: expr, $op_1: path, $op_2: path) => {{
        let mut ir = $generator.expr_lvalue($l);
        ir.extend([IRItem::Double, IRItem::Double, IRItem::Load]);
        let ty = match $l.ty {
            Type::Int => OpType::Int,
            Type::Float => OpType::Float,
            _ => unreachable!(),
        };
        ir.extend($generator.expr_rvalue($r, ty));
        match ty {
            OpType::Int => ir.push_back($op_1),
            OpType::Float => ir.push_back($op_2),
            _ => unreachable!(),
        }
        ir.push_back(IRItem::Store);
        ir
    }};
}

macro_rules! pre_inc_dec_helper {
    ($ir_generator: expr, $expr: expr, $op_1: path, $op_2:path) => {{
        let mut ir = $ir_generator.expr_lvalue($expr);
        ir.extend([IRItem::Double, IRItem::Load]);
        match &$expr.ty {
            Type::Int => ir.extend([IRItem::PushInt(1), $op_1, IRItem::Store]),
            Type::Float => ir.extend([IRItem::PushFloat(1.0), $op_2, IRItem::Store]),
            _ => unreachable!(),
        }
        ir
    }};
}

impl Generator {
    pub fn expr_lvalue(&self, expr: &Expr) -> VecDeque<IRItem> {
        let Expr { inner, ty: _, category: _, is_const: _ } = expr;
        match inner {
            PreInc(expr) => pre_inc_dec_helper!(self, expr, IRItem::AddInt, IRItem::AddFloat),
            PreDec(expr) => pre_inc_dec_helper!(self, expr, IRItem::SubInt, IRItem::SubFloat),
            Assignment(l, r) => {
                let mut ir = self.expr_lvalue(l);
                ir.push_back(IRItem::Double);
                let ty = match l.ty {
                    Type::Int => OpType::Int,
                    Type::Float => OpType::Float,
                    _ => unreachable!(),
                };
                ir.extend(self.expr_rvalue(r, ty));
                ir.push_back(IRItem::Store);
                ir
            }
            AddAssign(l, r) => assign_helper!(self, l, r, IRItem::AddInt, IRItem::AddFloat),
            SubAssign(l, r) => assign_helper!(self, l, r, IRItem::SubInt, IRItem::SubFloat),
            MulAssign(l, r) => assign_helper!(self, l, r, IRItem::MulInt, IRItem::MulFloat),
            DivAssign(l, r) => assign_helper!(self, l, r, IRItem::DivInt, IRItem::DivFloat),
            ModAssign(l, r) => assign_helper!(self, l, r, IRItem::Mod),
            AndAssign(l, r) => assign_helper!(self, l, r, IRItem::And),
            OrAssign(l, r) => assign_helper!(self, l, r, IRItem::Or),
            XorAssign(l, r) => assign_helper!(self, l, r, IRItem::Xor),
            ShLAssign(l, r) => assign_helper!(self, l, r, IRItem::Sll),
            SaRAssign(l, r) => assign_helper!(self, l, r, IRItem::Sar),
            Var(handler) => VecDeque::from([IRItem::LoadAddr { var: *handler }]),
            ArrayElem(handler, subscripts) => self.array_elem_helper(*handler, subscripts),
            _ => unreachable!(),
        }
    }
}
