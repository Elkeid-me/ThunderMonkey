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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Void,
    Pointer(Box<Type>, Vec<usize>),
    Array(Box<Type>, Vec<usize>),
    Function(Box<Type>, Vec<Type>),
    // 变参函数
    VAList,
}

impl Type {
    pub fn convertible(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Int, Self::Int) | (Self::Int, Self::Float) | (Self::Float, Self::Int) | (Self::Float, Self::Float) => true,
            (Self::Array(base_1, len_1), Self::Pointer(base_2, len_2)) => base_1 == base_2 && &len_1[1..] == len_2,
            (Self::Pointer(base_1, len_1), Self::Array(base_2, len_2)) => base_1 == base_2 && len_1 == &len_2[1..],
            (Self::Array(base_1, len_1), Self::Array(base_2, len_2))
            | (Self::Pointer(base_1, len_1), Self::Pointer(base_2, len_2)) => base_1 == base_2 && len_1 == len_2,
            _ => false,
        }
    }
}
