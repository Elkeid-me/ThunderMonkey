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

use super::{Generator, IRItem, OpType};
use crate::frontend::{ast::*, ty::Type};
use crate::{risk, Handler};
use std::collections::VecDeque;

impl Generator {
    fn fun_def(&mut self, handler: Handler) -> VecDeque<IRItem> {}

    pub fn global_def(&mut self, handler: Handler) -> (handler, VecDeque<IRItem>) {}

    pub fn def(&mut self, handler: Handler) -> VecDeque<IRItem> {
        let Definition { init, ty, id, is_global, is_arg } = self.symbol_table.get(&handler).unwrap();

        match (ty, init) {
            (Type::Int, None) | (Type::Float, None) => VecDeque::from([IRItem::DefWords { var: handler, size: 1 }]),
            (Type::Int, Some(Init::ConstInt(_)))
            | (Type::Int, Some(Init::ConstFloat(_)))
            | (Type::Float, Some(Init::ConstInt(_)))
            | (Type::Float, Some(Init::ConstFloat(_))) => VecDeque::new(),
            (Type::Int, Some(Init::Expr(expr))) => {
                let mut ir = VecDeque::from([IRItem::DefWords { var: handler, size: 1 }, IRItem::LoadAddr { var: handler }]);
                ir.extend(self.expr_rvalue(expr.clone(), OpType::Int));
                ir.push_back(IRItem::Store);
                ir
            }
            (Type::Float, Some(Init::Expr(expr))) => {
                let mut ir = VecDeque::from([IRItem::DefWords { var: handler, size: 1 }, IRItem::LoadAddr { var: handler }]);
                ir.extend(self.expr_rvalue(expr.clone(), OpType::Float));
                ir.push_back(IRItem::Store);
                ir
            }
            (Type::Array(_, lens), None) => {
                let size = lens.iter().fold(4usize, |i, e| i * e);
                VecDeque::from([IRItem::DefWords { var: handler, size }])
            }
            (Type::Array(_, _), Some(_)) => todo!(),
            _ => unreachable!(),
        }
    }
}
