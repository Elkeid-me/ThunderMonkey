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

use super::{Generator, GlobalItem, IRItem, OpType};
use crate::frontend::{ast::*, ty::Type};
use crate::Handler;
use std::collections::VecDeque;
use std::vec;

impl Generator {
    fn fun_def(&mut self, handler: Handler, block: &Block, arg_handlers: &[Handler], ret_ty: &Type) {
        self.context.clear();

        let ir = self.block(block, 0, 0, ret_ty).0;

        let v =
            GlobalItem::Function { code: ir, context: std::mem::take(&mut self.context), arg_handlers: arg_handlers.to_vec() };
        self.global_items.insert(handler, v);
    }

    pub fn global_def(&mut self, handler: Handler) {
        let Definition { init, ty, id: _, is_global: _, is_arg: _ } = self.symbol_table.get(&handler).unwrap();
        match (ty, init) {
            (Type::Int | Type::Float, None) => {
                self.global_items.insert(handler, GlobalItem::Variable { words: 1, init: None });
            }
            (Type::Int, Some(Init::Expr(expr))) => {
                let bits = match &expr.inner {
                    ExprInner::Integer(i) => vec![*i as u32],
                    ExprInner::Floating(f) => vec![(*f as i32) as u32],
                    _ => unreachable!(),
                };
                self.global_items.insert(handler, GlobalItem::Variable { words: 1, init: Some(bits) });
            }
            (Type::Float, Some(Init::Expr(expr))) => {
                let bits = match &expr.inner {
                    ExprInner::Integer(i) => vec![(*i as f32).to_bits()],
                    ExprInner::Floating(f) => vec![f.to_bits()],
                    _ => unreachable!(),
                };
                self.global_items.insert(handler, GlobalItem::Variable { words: 1, init: Some(bits) });
            }
            (Type::Float, Some(Init::ConstFloat(_)))
            | (Type::Int, Some(Init::ConstInt(_)))
            | (Type::Int, Some(Init::ConstFloat(_)))
            | (Type::Float, Some(Init::ConstInt(_)))
            | (Type::Function(_, _), None) => (),
            (Type::Array(_, lens), None) => {
                let size = lens.iter().fold(1usize, |i, e| i * e);
                self.global_items.insert(handler, GlobalItem::Variable { words: size, init: None });
            }
            (Type::Array(_, _), Some(Init::ConstList(_))) => self.global_array(handler),
            (Type::Array(_, _), Some(Init::List(_))) => self.global_array(handler),
            (Type::Function(ret_type, _), Some(Init::Function { block, is_entry: _, arg_handlers })) => unsafe {
                let p = self as *const Generator;
                let p = p as *mut Generator;
                let s = &mut *p;
                s.fun_def(handler, block, arg_handlers, ret_type);
            },
            _ => unreachable!(),
        }
    }

    fn flat_const_list(list: &ConstInitList, expected_ty: &Type) -> Vec<u32> {
        match expected_ty {
            Type::Int => list
                .iter()
                .flat_map(|item| match item {
                    ConstInitListItem::ConstInitList(list) => Self::flat_const_list(list, expected_ty),
                    ConstInitListItem::Int(i) => vec![*i as u32],
                    ConstInitListItem::Float(f) => vec![(*f as i32) as u32],
                })
                .collect(),
            Type::Float => list
                .iter()
                .flat_map(|item| match item {
                    ConstInitListItem::ConstInitList(list) => Self::flat_const_list(list, expected_ty),
                    ConstInitListItem::Int(i) => vec![(*i as f32).to_bits()],
                    ConstInitListItem::Float(f) => vec![f.to_bits()],
                })
                .collect(),
            _ => unreachable!(),
        }
    }

    fn flat_list(list: &InitList, expected_ty: &Type) -> Vec<u32> {
        match expected_ty {
            Type::Int => list
                .iter()
                .flat_map(|item| match item {
                    InitListItem::InitList(list) => Self::flat_list(list, expected_ty),
                    InitListItem::Expr(expr) => match &expr.inner {
                        ExprInner::Integer(i) => vec![*i as u32],
                        ExprInner::Floating(f) => vec![(*f as i32) as u32],
                        _ => unreachable!(),
                    },
                })
                .collect(),
            Type::Float => list
                .iter()
                .flat_map(|item| match item {
                    InitListItem::InitList(list) => Self::flat_list(list, expected_ty),
                    InitListItem::Expr(expr) => match &expr.inner {
                        ExprInner::Integer(i) => vec![(*i as f32).to_bits()],
                        ExprInner::Floating(f) => vec![f.to_bits()],
                        _ => unreachable!(),
                    },
                })
                .collect(),
            _ => unreachable!(),
        }
    }

    fn global_array(&mut self, handler: Handler) {
        let Definition { init, ty, id: _, is_global: _, is_arg: _ } = self.symbol_table.get(&handler).unwrap();
        match (ty, init) {
            (Type::Array(base, lens), Some(Init::ConstList(list))) => {
                let size = lens.iter().fold(1usize, |i, e| i * e);
                self.global_items
                    .insert(handler, GlobalItem::Variable { words: size, init: Some(Self::flat_const_list(list, base)) });
            }
            (Type::Array(base, lens), Some(Init::List(list))) => {
                let size = lens.iter().fold(1usize, |i, e| i * e);
                self.global_items
                    .insert(handler, GlobalItem::Variable { words: size, init: Some(Self::flat_list(list, base)) });
            }
            _ => unreachable!(),
        }
    }

    fn flat_expr_list(list: &InitList) -> Vec<Expr> {
        list.iter()
            .flat_map(|item| match item {
                InitListItem::InitList(list) => Self::flat_expr_list(list),
                InitListItem::Expr(expr) => vec![expr.clone()],
            })
            .collect()
    }

    pub fn def(&mut self, handler: Handler) -> VecDeque<IRItem> {
        let Definition { init, ty, id: _, is_global: _, is_arg: _ } = self.symbol_table.get(&handler).unwrap();
        match (ty, init) {
            (Type::Int, Some(Init::ConstInt(_)))
            | (Type::Int, Some(Init::ConstFloat(_)))
            | (Type::Float, Some(Init::ConstInt(_)))
            | (Type::Float, Some(Init::ConstFloat(_))) => VecDeque::new(),
            (Type::Int, None) | (Type::Float, None) => {
                self.context.insert(handler, 1);
                VecDeque::new()
            }
            (Type::Int, Some(Init::Expr(expr))) => {
                self.context.insert(handler, 1);
                let mut ir = VecDeque::from([IRItem::LoadAddr { var: handler }]);
                ir.extend(self.expr_rvalue(expr, OpType::Int));
                ir.push_back(IRItem::Store);
                ir
            }
            (Type::Float, Some(Init::Expr(expr))) => {
                self.context.insert(handler, 1);
                let mut ir = VecDeque::from([IRItem::LoadAddr { var: handler }]);
                ir.extend(self.expr_rvalue(expr, OpType::Float));
                ir.push_back(IRItem::Store);
                ir
            }
            (Type::Array(_, lens), None) => {
                let size = lens.iter().fold(1usize, |i, e| i * e);
                self.context.insert(handler, size);
                VecDeque::new()
            }
            (Type::Array(_, _), Some(Init::ConstList(_))) => {
                self.global_array(handler);
                VecDeque::new()
            }
            (Type::Array(ty, lens), Some(Init::List(list))) => {
                let size = lens.iter().fold(1usize, |i, e| i * e);
                self.context.insert(handler, size);
                let exprs = Self::flat_expr_list(list);
                let expected_ty = match ty.as_ref() {
                    Type::Int => OpType::Int,
                    Type::Float => OpType::Float,
                    _ => unreachable!(),
                };
                exprs
                    .iter()
                    .enumerate()
                    .flat_map(|(i, expr)| {
                        let mut ir =
                            VecDeque::from([IRItem::LoadAddr { var: handler }, IRItem::PushInt(i as i32 * 4), IRItem::AddInt]);
                        ir.extend(self.expr_rvalue(expr, expected_ty));
                        ir.push_back(IRItem::Store);
                        ir
                    })
                    .collect()
            }
            _ => unreachable!(),
        }
    }
}
