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

mod def;
mod dvalue;
mod lvalue;
mod rvalue;
mod statement;

use super::{ast::*, ty::Type};
use crate::{backend::chollima::*, Handler, HashMap};
use std::{cell::RefCell, collections::VecDeque};

struct Counter {
    value: i32,
}

impl Counter {
    fn get(&mut self) -> u32 {
        self.value -= 1;
        self.value as u32
    }
}

struct Generator {
    counter: RefCell<Counter>,
    ast: Vec<Handler>,
    symbol_table: HashMap<Handler, Definition>,
    context: RefCell<HashMap<Handler, usize>>,
    global_items: RefCell<HashMap<Handler, GlobalItem>>,
}

impl Generator {
    fn new(translation_unit: TranslationUnit) -> Self {
        let TranslationUnit { ast, symbol_table } = translation_unit;
        Self {
            counter: RefCell::new(Counter { value: -1 }),
            ast,
            symbol_table,
            context: RefCell::new(HashMap::default()),
            global_items: RefCell::new(HashMap::default()),
        }
    }

    fn generator(mut self) -> IR {
        for &handler in std::mem::take(&mut self.ast).iter() {
            self.global_def(handler);
        }
        IR { symbol_table: self.symbol_table, ir: self.global_items.take() }
    }

    pub(self) fn array_elem_helper(&self, array: Handler, subscripts: &[Expr]) -> VecDeque<IRItem> {
        let symbol_ty = &self.symbol_table.get(&array).unwrap().ty;
        let (mut ir, len_prod) = match symbol_ty {
            Type::Pointer(_, lens) => {
                let v: Vec<_> = [4]
                    .into_iter()
                    .chain(lens.iter().rev().scan(4usize, |i, &elem| {
                        *i *= elem;
                        Some(*i)
                    }))
                    .collect();
                (VecDeque::from([IRItem::LoadAddr { var: array }, IRItem::Load]), v)
            }
            Type::Array(_, lens) => {
                let mut v: Vec<_> = [4]
                    .into_iter()
                    .chain(lens.iter().rev().scan(4usize, |i, &elem| {
                        *i *= elem;
                        Some(*i)
                    }))
                    .collect();
                v.pop();
                (VecDeque::from([IRItem::LoadAddr { var: array }]), v)
            }
            _ => unreachable!(),
        };

        ir.extend(subscripts.iter().zip(len_prod.into_iter().rev()).flat_map(|(expr, len)| {
            let mut ir = VecDeque::from([IRItem::PushInt(len as i32)]);
            ir.extend(self.expr_rvalue(expr, OpType::Int));
            ir.extend([IRItem::MulInt, IRItem::AddInt]);
            ir
        }));

        ir
    }
}

pub fn generator_ir(translation_unit: TranslationUnit) -> IR {
    Generator::new(translation_unit).generator()
}
