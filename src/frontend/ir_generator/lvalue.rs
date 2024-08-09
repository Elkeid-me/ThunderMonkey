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

impl Generator {
    pub fn expr_lvalue(&self, expr: &Expr) -> VecDeque<IRItem> {
        let Expr { inner, ty: _, category: _, is_const: _ } = expr;
        match inner {
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
                ir.push_back(IRItem::Double);
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
            Var(handler) => VecDeque::from([IRItem::LoadAddr { var: *handler }]),
            ArrayElem(handler, subscripts) => self.array_elem_helper(*handler, subscripts),
            _ => unreachable!(),
        }
    }
}
