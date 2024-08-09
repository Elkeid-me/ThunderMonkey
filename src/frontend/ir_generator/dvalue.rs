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
use crate::backend::chollima::{OpType, IRItem};
use crate::frontend::{ast::Expr, ast::ExprInner::*, ty::Type};
use std::collections::VecDeque;

impl Generator {
    pub fn expr_dvalue(&self, expr: Expr) -> VecDeque<IRItem> {
        let Expr { inner, ty, category, is_const } = expr;
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
                let mut l_ir = self.expr_dvalue(*l);
                l_ir.extend(self.expr_dvalue(*r));
                l_ir
            }
            LogicNot(expr) | Nega(expr) | Not(expr) => self.expr_dvalue(*expr),
            PostInc(_) => todo!(),
            PostDec(_) => todo!(),
            PreInc(_) => todo!(),
            PreDec(_) => todo!(),
            Assignment(l, r) => todo!(),
            AddAssign(l, r) => todo!(),
            SubAssign(l, r) => todo!(),
            MulAssign(l, r) => todo!(),
            DivAssign(l, r) => todo!(),
            ModAssign(l, r) => todo!(),
            AndAssign(l, r) => todo!(),
            OrAssign(l, r) => todo!(),
            XorAssign(l, r) => todo!(),
            ShLAssign(l, r) => todo!(),
            SaRAssign(l, r) => todo!(),
            Integer(_) | Floating(_) | Var(_) => VecDeque::new(),
            Func(_, _) => self.expr_rvalue(Expr { inner, ty, category, is_const }, OpType::Void),
            ArrayElem(_, subscripts) => subscripts.into_iter().flat_map(|expr| self.expr_dvalue(expr)).collect(),
            LogicAnd(_, _) => todo!(),
            LogicOr(_, _) => todo!(),
        }
    }
}
