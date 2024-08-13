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

use std::collections::VecDeque;
use std::fmt::{Display, Formatter, Result};

#[derive(Clone)]
pub enum Inst {
    Push(Vec<GPR>),
    Pop(Vec<GPR>),
    VPush(Vec<FPR>),
    VPop(Vec<FPR>),

    B(String),
    BEq(String),
    BNe(String),

    Blx(GPR),
    Bx(GPR),
    BxEq(GPR),
    BxNe(GPR),

    Cmp(GPR, GPR),

    Ldr(GPR, GPR),
    Sdr(GPR, GPR),
    Mov32(GPR, i32),
    Mov32Label(GPR, String),
    Mov(GPR, GPR),

    MovImmEq(GPR, i32),
    MovImmNe(GPR, i32),
    MovImmGe(GPR, i32),
    MovImmGt(GPR, i32),
    MovImmLe(GPR, i32),
    MovImmLt(GPR, i32),

    Add(GPR, GPR, GPR),
    Sub(GPR, GPR, GPR),
    Mul(GPR, GPR, GPR),

    Eor(GPR, GPR, GPR),
    EorImm(GPR, GPR, i32),
    Orr(GPR, GPR, GPR),
    And(GPR, GPR, GPR),
    AndS(GPR, GPR, GPR),
    Lsl(GPR, GPR, GPR),
    Lsr(GPR, GPR, GPR),
    Asr(GPR, GPR, GPR),

    VAddF32(FPR, FPR, FPR),
    VSubF32(FPR, FPR, FPR),
    VMulF32(FPR, FPR, FPR),
    VDivF32(FPR, FPR, FPR),
}

#[allow(unused)]
#[derive(Clone, Copy, PartialEq)]
pub enum GPR {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7, // BP
    R8,
    R9,
    R10,
    R11,
    R12,
    SP,
    LR,
    PC,
}

#[allow(unused)]
#[derive(Clone, Copy, PartialEq)]
pub enum FPR {
    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    S12,
    S13,
    S14,
    S15,
    S16,
    S17,
    S18,
    S19,
    S20,
    S21,
    S22,
    S23,
    S24,
    S25,
    S26,
    S27,
    S28,
    S29,
    S30,
    S31,
}

#[derive(Clone)]
pub enum Directive {
    Text,
    Global(String),
    Data,
    Zero(usize),
    Word(Vec<u32>),
}

#[derive(Clone)]
pub enum ARMItem {
    Label(String),
    Inst(Inst),
    Directive(Directive),
}

pub type ARM = VecDeque<ARMItem>;

impl Display for GPR {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::R0 => write!(f, "r0"),
            Self::R1 => write!(f, "r1"),
            Self::R2 => write!(f, "r2"),
            Self::R3 => write!(f, "r3"),
            Self::R4 => write!(f, "r4"),
            Self::R5 => write!(f, "r5"),
            Self::R6 => write!(f, "r6"),
            Self::R7 => write!(f, "r7"),
            Self::R8 => write!(f, "r8"),
            Self::R9 => write!(f, "r9"),
            Self::R10 => write!(f, "r10"),
            Self::R11 => write!(f, "r11"),
            Self::R12 => write!(f, "r12"),
            Self::SP => write!(f, "r13"),
            Self::LR => write!(f, "r14"),
            Self::PC => write!(f, "r15"),
        }
    }
}

impl Display for FPR {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::S0 => write!(f, "s0"),
            Self::S1 => write!(f, "s1"),
            Self::S2 => write!(f, "s2"),
            Self::S3 => write!(f, "s3"),
            Self::S4 => write!(f, "s4"),
            Self::S5 => write!(f, "s5"),
            Self::S6 => write!(f, "s6"),
            Self::S7 => write!(f, "s7"),
            Self::S8 => write!(f, "s8"),
            Self::S9 => write!(f, "s9"),
            Self::S10 => write!(f, "s10"),
            Self::S11 => write!(f, "s11"),
            Self::S12 => write!(f, "s12"),
            Self::S13 => write!(f, "s13"),
            Self::S14 => write!(f, "s14"),
            Self::S15 => write!(f, "s15"),

            Self::S16 => write!(f, "s16"),
            Self::S17 => write!(f, "s17"),
            Self::S18 => write!(f, "s18"),
            Self::S19 => write!(f, "s19"),
            Self::S20 => write!(f, "s20"),
            Self::S21 => write!(f, "s21"),
            Self::S22 => write!(f, "s22"),
            Self::S23 => write!(f, "s23"),
            Self::S24 => write!(f, "s24"),
            Self::S25 => write!(f, "s25"),
            Self::S26 => write!(f, "s26"),
            Self::S27 => write!(f, "s27"),
            Self::S28 => write!(f, "s28"),
            Self::S29 => write!(f, "s29"),
            Self::S30 => write!(f, "s30"),
            Self::S31 => write!(f, "s31"),
        }
    }
}

pub trait ARMTrait {
    fn add_label(&mut self, label: String);
    fn add_inst(&mut self, inst: Inst);
    fn add_directive(&mut self, directive: Directive);
}

impl ARMTrait for ARM {
    fn add_label(&mut self, label: String) {
        self.push_back(ARMItem::Label(label));
    }
    fn add_inst(&mut self, inst: Inst) {
        self.push_back(ARMItem::Inst(inst));
    }
    fn add_directive(&mut self, directive: Directive) {
        self.push_back(ARMItem::Directive(directive));
    }
}

impl Display for Inst {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Ldr(rd, rs) => write!(f, "ldr {rd}, [{rs}]"),
            Self::Sdr(rs_1, rs_2) => write!(f, "str {rs_1}, [{rs_2}]"),

            Self::Add(rd, rs_1, rs_2) => write!(f, "add {rd}, {rs_1}, {rs_2}"),
            Self::Sub(rd, rs_1, rs_2) => write!(f, "sub {rd}, {rs_1}, {rs_2}"),
            Self::Mul(rd, rs_1, rs_2) => write!(f, "mul {rd}, {rs_1}, {rs_2}"),

            Self::Push(reg_list) => {
                let list: Vec<_> = reg_list.iter().map(|reg| format!("{reg}")).collect();
                write!(f, "push {{{}}}", list.as_slice().join(", "))
            }
            Self::Pop(reg_list) => {
                let list: Vec<_> = reg_list.iter().map(|reg| format!("{reg}")).collect();
                write!(f, "pop {{{}}}", list.as_slice().join(", "))
            }
            Self::VPush(reg_list) => {
                let list: Vec<_> = reg_list.iter().map(|reg| format!("{reg}")).collect();
                write!(f, "vpush {{{}}}", list.as_slice().join(", "))
            }
            Self::VPop(reg_list) => {
                let list: Vec<_> = reg_list.iter().map(|reg| format!("{reg}")).collect();
                write!(f, "vpop {{{}}}", list.as_slice().join(", "))
            }

            Self::B(label) => write!(f, "b {label}"),
            Self::BEq(label) => write!(f, "beq {label}"),
            Self::BNe(label) => write!(f, "bne {label}"),

            Self::Blx(reg) => write!(f, "blx {reg}"),
            Self::Bx(reg) => write!(f, "bx {reg}"),
            Self::BxEq(reg) => write!(f, "bxeq {reg}"),
            Self::BxNe(reg) => write!(f, "bxne {reg}"),

            Self::Mov32(reg, imm) => write!(f, "mov32 {reg}, {imm}"),
            Self::Mov32Label(reg, label) => write!(f, "mov32 {reg}, {label}"),
            Self::Mov(rd, rs) => write!(f, "mov {rd}, {rs}"),
            Self::MovImmEq(reg, imm) => write!(f, "moveq {reg}, #{imm}"),
            Self::MovImmNe(reg, imm) => write!(f, "movne {reg}, #{imm}"),
            Self::MovImmGe(reg, imm) => write!(f, "movge {reg}, #{imm}"),
            Self::MovImmGt(reg, imm) => write!(f, "movgt {reg}, #{imm}"),
            Self::MovImmLe(reg, imm) => write!(f, "movle {reg}, #{imm}"),
            Self::MovImmLt(reg, imm) => write!(f, "movlt {reg}, #{imm}"),

            Self::Eor(rd, rs_1, rs_2) => write!(f, "eor {rd}, {rs_1}, {rs_2}"),
            Self::EorImm(rd, rs, imm) => write!(f, "eor {rd}, {rs}, #{imm}"),
            Self::Orr(rd, rs_1, rs_2) => write!(f, "orr {rd}, {rs_1}, {rs_2}"),
            Self::And(rd, rs_1, rs_2) => write!(f, "and {rd}, {rs_1}, {rs_2}"),
            Self::AndS(rd, rs_1, rs_2) => write!(f, "ands {rd}, {rs_1}, {rs_2}"),
            Self::Lsl(rd, rs_1, rs_2) => write!(f, "lsl {rd}, {rs_1}, {rs_2}"),
            Self::Lsr(rd, rs_1, rs_2) => write!(f, "lsr {rd}, {rs_1}, {rs_2}"),
            Self::Asr(rd, rs_1, rs_2) => write!(f, "asr {rd}, {rs_1}, {rs_2}"),

            Self::Cmp(rd, rs) => write!(f, "cmp {rd}, {rs}"),

            Self::VAddF32(rd, rs_1, rs_2) => write!(f, "vadd.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VSubF32(rd, rs_1, rs_2) => write!(f, "vsub.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VMulF32(rd, rs_1, rs_2) => write!(f, "vmul.f32 {rd}, {rs_1}, {rs_2}"),
            Self::VDivF32(rd, rs_1, rs_2) => write!(f, "vdiv.f32 {rd}, {rs_1}, {rs_2}"),
        }
    }
}

impl Display for Directive {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Text => write!(f, ".text"),
            Self::Global(label) => write!(f, ".global {label}"),
            Self::Data => write!(f, ".data"),
            Self::Zero(len) => write!(f, ".zero {}", len * 4),
            Self::Word(nums) => {
                let data: Vec<_> = nums.iter().map(u32::to_string).collect();
                write!(f, ".word {}", data.as_slice().join(", "))
            }
        }
    }
}

impl Display for ARMItem {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            Self::Label(label) => writeln!(f, "{label}:"),
            Self::Inst(inst) => writeln!(f, "    {inst}"),
            Self::Directive(directive) => writeln!(f, "{directive}"),
        }
    }
}
