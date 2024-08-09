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
            PostInc(_) => todo!(),
            PostDec(_) => todo!(),
            PreInc(_) => todo!(),
            PreDec(_) => todo!(),
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
            AddAssign(_, _) => todo!(),
            SubAssign(_, _) => todo!(),
            MulAssign(_, _) => todo!(),
            DivAssign(_, _) => todo!(),
            ModAssign(_, _) => todo!(),
            AndAssign(_, _) => todo!(),
            OrAssign(_, _) => todo!(),
            XorAssign(_, _) => todo!(),
            ShLAssign(_, _) => todo!(),
            SaRAssign(_, _) => todo!(),
            Integer(_) | Floating(_) | Var(_) => VecDeque::new(),
            Func(_, _) => self.expr_rvalue(expr, OpType::Void),
            ArrayElem(_, subscripts) => subscripts.into_iter().flat_map(|expr| self.expr_dvalue(expr)).collect(),
            LogicAnd(_, _) => todo!(),
            LogicOr(_, _) => todo!(),
        }
    }
}
