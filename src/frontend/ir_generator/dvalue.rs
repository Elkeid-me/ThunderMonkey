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
use crate::backend::chollima::{IRItem, OpType};
use crate::frontend::{ast::Expr, ast::ExprInner::*, ty::Type};
use std::collections::VecDeque;

macro_rules! assign_helper {
    ($generator: expr, $l: expr, $r: expr, $op: path) => {{
        let mut ir = $generator.expr_lvalue($l);
        ir.extend([IRItem::Double, IRItem::Load]);
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
        ir.extend([IRItem::Double, IRItem::Load]);
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

macro_rules! inc_dec_helper {
    ($ir_generator: expr, $expr: expr, $op_1: path, $op_2:path) => {{
        let mut ir = $ir_generator.expr_lvalue($expr);
        ir.extend([IRItem::Load]);
        match &$expr.ty {
            Type::Int => ir.extend([IRItem::PushInt(1), $op_1, IRItem::Store]),
            Type::Float => ir.extend([IRItem::PushFloat(1.0), $op_2, IRItem::Store]),
            _ => unreachable!(),
        }
        ir
    }};
}

impl Generator {
    pub fn expr_dvalue(&self, expr: &Expr) -> VecDeque<IRItem> {
        let Expr { inner, ty: _, category: _, is_const: _ } = expr;
        match inner {
            Mul(l, r)
            | Div(l, r)
            | Mod(l, r)
            | Add(l, r)
            | Sub(l, r)
            | ShL(l, r)
            | SaR(l, r)
            | Xor(l, r)
            | And(l, r)
            | Or(l, r)
            | Eq(l, r)
            | Neq(l, r)
            | Grt(l, r)
            | Geq(l, r)
            | Les(l, r)
            | Leq(l, r) => {
                let mut l_ir = self.expr_dvalue(l);
                l_ir.extend(self.expr_dvalue(r));
                l_ir
            }
            LogicNot(expr) | Nega(expr) | Not(expr) => self.expr_dvalue(expr),
            PostInc(expr) | PreInc(expr) => inc_dec_helper!(self, expr, IRItem::AddInt, IRItem::AddFloat),
            PostDec(expr) | PreDec(expr) => inc_dec_helper!(self, expr, IRItem::AddInt, IRItem::AddFloat),
            Assignment(l, r) => {
                let mut ir = self.expr_lvalue(l);
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
            Integer(_) | Floating(_) | Var(_) => VecDeque::new(),
            Func(_, _) => self.expr_rvalue(expr, OpType::Void),
            ArrayElem(_, subscripts) => subscripts.iter().flat_map(|expr| self.expr_dvalue(expr)).collect(),
            LogicAnd(_, _) | LogicOr(_, _) => {
                let mut ir = self.expr_rvalue(expr, OpType::Int);
                ir.push_back(IRItem::PopWords(1));
                ir
            }
        }
    }
}
