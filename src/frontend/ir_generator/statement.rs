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
use crate::Handler;
use std::collections::VecDeque;

impl Generator {
    fn while_statement(&mut self, cond: &Expr, block: &Block, ret_ty: &Type) -> VecDeque<IRItem> {
        let while_label = self.counter.borrow_mut().get();
        let while_next_label = self.counter.borrow_mut().get();
        let (block_ir, block_label) = self.block(block, while_label, while_next_label, ret_ty);
        let mut ir = VecDeque::from([IRItem::Jmp { label: while_label }, IRItem::Label { addr: while_label }]);
        ir.extend(self.expr_rvalue(cond, OpType::Int));
        ir.extend([IRItem::Br { then: block_label, or_else: while_next_label }]);
        ir.extend(block_ir);
        ir.extend([IRItem::Jmp { label: while_label }, IRItem::Label { addr: while_next_label }]);
        ir
    }
    fn if_statement(
        &mut self,
        cond: &Expr,
        then_block: &Block,
        else_block: &Block,
        while_label: Handler,
        while_next_label: Handler,
        ret_ty: &Type,
    ) -> VecDeque<IRItem> {
        match (then_block.is_empty(), else_block.is_empty()) {
            (true, true) => self.expr_dvalue(cond),
            (false, true) => {
                let next_label = self.counter.borrow_mut().get();
                let (then_block_ir, then_block_label) = self.block(then_block, while_label, while_next_label, ret_ty);
                let mut ir = self.expr_rvalue(cond, OpType::Int);
                ir.extend([
                    IRItem::Br { then: then_block_label, or_else: next_label },
                    IRItem::Label { addr: then_block_label },
                ]);
                ir.extend(then_block_ir);
                ir.extend([IRItem::Jmp { label: next_label }, IRItem::Label { addr: next_label }]);
                ir
            }
            (true, false) => {
                let next_label = self.counter.borrow_mut().get();
                let (else_block_ir, else_block_label) = self.block(else_block, while_label, while_next_label, ret_ty);
                let mut ir = self.expr_rvalue(cond, OpType::Int);
                ir.extend([
                    IRItem::Br { then: next_label, or_else: else_block_label },
                    IRItem::Label { addr: else_block_label },
                ]);
                ir.extend(else_block_ir);
                ir.extend([IRItem::Jmp { label: next_label }, IRItem::Label { addr: next_label }]);
                ir
            }
            (false, false) => {
                let next_label = self.counter.borrow_mut().get();
                let (then_block_ir, then_block_label) = self.block(then_block, while_label, while_next_label, ret_ty);
                let (else_block_ir, else_block_label) = self.block(else_block, while_label, while_next_label, ret_ty);
                let mut ir = self.expr_rvalue(cond, OpType::Int);
                ir.extend([
                    IRItem::Br { then: then_block_label, or_else: else_block_label },
                    IRItem::Label { addr: then_block_label },
                ]);
                ir.extend(then_block_ir);
                ir.extend([IRItem::Jmp { label: next_label }, IRItem::Label { addr: else_block_label }]);
                ir.extend(else_block_ir);
                ir.extend([IRItem::Jmp { label: next_label }, IRItem::Label { addr: next_label }]);
                ir
            }
        }
    }

    pub fn statement(
        &mut self,
        statement: &Statement,
        while_label: Handler,
        while_next_label: Handler,
        ret_ty: &Type,
    ) -> VecDeque<IRItem> {
        match statement {
            Statement::Expr(expr) => self.expr_dvalue(expr),
            Statement::If(cond, then_block, else_block) => {
                self.if_statement(cond, then_block, else_block, while_label, while_next_label, ret_ty)
            }
            Statement::While(cond, block) => self.while_statement(cond, block, ret_ty),
            Statement::Return(expr) => {
                if let Some(expr) = expr {
                    match ret_ty {
                        Type::Int => {
                            let mut ir = self.expr_rvalue(expr, OpType::Int);
                            ir.push_back(IRItem::RetInt);
                            ir
                        }
                        Type::Float => {
                            let mut ir = self.expr_rvalue(expr, OpType::Float);
                            ir.push_back(IRItem::RetFloat);
                            ir
                        }
                        _ => unreachable!(),
                    }
                } else {
                    VecDeque::from([IRItem::RetInt])
                }
            }
            Statement::Break => VecDeque::from([IRItem::Jmp { label: while_next_label }]),
            Statement::Continue => VecDeque::from([IRItem::Jmp { label: while_label }]),
        }
    }

    pub fn block(
        &mut self,
        block: &Block,
        while_label: Handler,
        while_next_label: Handler,
        ret_ty: &Type,
    ) -> (VecDeque<IRItem>, Handler) {
        let label = self.counter.borrow_mut().get();
        let body = block
            .into_iter()
            .flat_map(|item| match item {
                BlockItem::Def(handlers) => handlers.into_iter().flat_map(|handler| self.def(*handler)).collect(),
                BlockItem::Block(block) => self.block(block, while_label, while_next_label, ret_ty).0,
                BlockItem::Statement(stmt) => self.statement(stmt, while_label, while_next_label, ret_ty),
            })
            .collect();
        (body, label)
    }
}
