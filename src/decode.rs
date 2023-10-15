use mycelium_bitfield::bitfield;

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
  // * RV64I_Zifencei *
  // <insn> rd, rs1, rs2
  add(Reg, Reg, Reg),
  sub(Reg, Reg, Reg),
  xor(Reg, Reg, Reg),
  or(Reg, Reg, Reg),
  and(Reg, Reg, Reg),
  sll(Reg, Reg, Reg),
  srl(Reg, Reg, Reg),
  sra(Reg, Reg, Reg),
  slt(Reg, Reg, Reg),
  sltu(Reg, Reg, Reg),
  addw(Reg, Reg, Reg),
  subw(Reg, Reg, Reg),
  sllw(Reg, Reg, Reg),
  srlw(Reg, Reg, Reg),
  sraw(Reg, Reg, Reg),
  // <insn> rd, rs1, imm
  addi(Reg, Reg, i16),
  xori(Reg, Reg, i16),
  ori(Reg, Reg, i16),
  andi(Reg, Reg, i16),
  slli(Reg, Reg, u8),
  srli(Reg, Reg, u8),
  srai(Reg, Reg, u8),
  slti(Reg, Reg, i16),
  sltiu(Reg, Reg, i16),
  addiw(Reg, Reg, i16),
  slliw(Reg, Reg, u8),
  srliw(Reg, Reg, u8),
  sraiw(Reg, Reg, u8),
  // l<size> rd, imm(rs1)
  lb(Reg, i16, Reg),
  lh(Reg, i16, Reg),
  lw(Reg, i16, Reg),
  ld(Reg, i16, Reg),
  lbu(Reg, i16, Reg),
  lhu(Reg, i16, Reg),
  lwu(Reg, i16, Reg),
  // s<size> rs2, imm(rs1)
  sb(Reg, i16, Reg),
  sh(Reg, i16, Reg),
  sw(Reg, i16, Reg),
  sd(Reg, i16, Reg),
  // <insn> rd, imm
  lui(Reg, i32),
  auipc(Reg, i32),
  // b<cond> rs1, rs2, label
  beq(Reg, Reg, i16),
  bne(Reg, Reg, i16),
  blt(Reg, Reg, i16),
  bge(Reg, Reg, i16),
  bltu(Reg, Reg, i16),
  bgeu(Reg, Reg, i16),
  // jal rd, label
  jal(Reg, i32),
  // jalr rd, imm(rs1)
  jalr(Reg, i16, Reg),
  // e<action>
  ecall,
  ebreak,
  // fence pred, succ
  fence(u8),
  fence_tso,
  fence_i,
}

bitfield! {
  struct Encoding32<u32> {
    const OPCODE = 7;
    const RD = 5;
    const FUNCT3 = 3;
    const RS1 = 5;
    const RS2 = 5;
    const FUNCT7 = 7;
  }
}

macro_rules! bitfield_getter {
  ($($($fname:ident)|*, $type:ty, $cname:ident),*$(,)?) => {
    $($(pub fn $fname(&self) -> $type { self.get(Self::$cname) as $type })*)*
  };
}

impl Encoding32 {
  bitfield_getter! {
    opcode, u8, OPCODE,
    rd, u8, RD,
    funct3, u8, FUNCT3,
    rs1, u8, RS1,
    rs2 | shamt, u8, RS2,
    funct7, u8, FUNCT7,
  }

  pub fn i_imm(&self) -> i16 {
    sext16(u16::from(self.funct7() << 5) + u16::from(self.rs2()), 12)
  }

  pub fn s_imm(&self) -> i16 {
    sext16(u16::from(self.funct7() << 5) + u16::from(self.rd()), 12)
  }

  pub fn b_imm(&self) -> i16 {
    bitfield! {
      struct BType<u32> {
        const _OPCODE = 7;
        const IMM_11 = 1;
        const IMM_4_1 = 4;
        const _FUNCT3 = 3;
        const _RS1 = 5;
        const _RS2 = 5;
        const IMM_10_5 = 6;
        const IMM_12 = 1;
      }
    }
    let b = BType::from_bits(self.bits());
    let imm = (b.get(BType::IMM_12) << 12)
      + (b.get(BType::IMM_11) << 11)
      + (b.get(BType::IMM_10_5) << 5)
      + (b.get(BType::IMM_4_1) << 1);
    sext16(imm as u16, 13)
  }

  pub fn u_imm(&self) -> i32 {
    self.bits() as i32 & !0xfff
  }

  pub fn j_imm(&self) -> i32 {
    bitfield! {
      struct JType<u32> {
        const _OPCODE = 7;
        const _RD = 5;
        const IMM_19_12 = 8;
        const IMM_11 = 1;
        const IMM_10_1 = 10;
        const IMM_20 = 1;
      }
    }
    let j = JType::from_bits(self.bits());
    let imm = (j.get(JType::IMM_20) << 20)
      + (j.get(JType::IMM_19_12) << 12)
      + (j.get(JType::IMM_11) << 11)
      + (j.get(JType::IMM_10_1) << 1);
    sext32(imm, 21)
  }
}

pub fn decode_word(word: u32) -> (Instruction, bool) {
  use Instruction::*;
  if let Some(insn) = decode_compressed(word as u16) {
    (insn, true)
  } else {
    // 32-bit
    let r = Encoding32::from_bits(word);
    let (rdr, rs1r, rs2r) = (Reg::x(r.rd()), Reg::x(r.rs1()), Reg::x(r.rs2()));
    let insn = match r.opcode() >> 2 {
      0b01100 => (match (r.funct3(), r.funct7()) {
        (0, 0) => add,
        (0, 32) => sub,
        (4, 0) => xor,
        (6, 0) => or,
        (7, 0) => and,
        (1, 0) => sll,
        (5, 0) => srl,
        (5, 32) => sra,
        (2, 0) => slt,
        (3, 0) => sltu,
        _ => unimplemented!(),
      })(rdr, rs1r, rs2r),
      0b01110 => (match (r.funct3(), r.funct7()) {
        (0, 0) => addw,
        (0, 32) => subw,
        (1, 0) => sllw,
        (5, 0) => srlw,
        (5, 32) => sraw,
        _ => unimplemented!(),
      })(rdr, rs1r, rs2r),
      0b00100 => match r.funct3() {
        0 => addi(rdr, rs1r, r.i_imm()),
        4 => xori(rdr, rs1r, r.i_imm()),
        6 => ori(rdr, rs1r, r.i_imm()),
        7 => andi(rdr, rs1r, r.i_imm()),
        1 if r.funct7() == 0 => slli(rdr, rs1r, r.shamt()),
        5 if r.funct7() == 0 => srli(rdr, rs1r, r.shamt()),
        5 if r.funct7() == 32 => srai(rdr, rs1r, r.shamt()),
        2 => slti(rdr, rs1r, r.i_imm()),
        3 => sltiu(rdr, rs1r, r.i_imm()),
        _ => unimplemented!(),
      },
      0b00110 => match (r.funct3(), r.funct7()) {
        (0, _) => addiw(rdr, rs1r, r.i_imm()),
        (1, 0) => slliw(rdr, rs1r, r.shamt()),
        (5, 0) => srliw(rdr, rs1r, r.shamt()),
        (5, 32) => sraiw(rdr, rs1r, r.shamt()),
        _ => unimplemented!(),
      },
      0b00000 => (match r.funct3() {
        0b000 => lb,
        0b001 => lh,
        0b010 => lw,
        0b011 => ld,
        0b100 => lbu,
        0b101 => lhu,
        0b110 => lwu,
        _ => unimplemented!(),
      })(rdr, r.i_imm(), rs1r),
      0b01000 => (match r.funct3() {
        0b000 => sb,
        0b001 => sh,
        0b010 => sw,
        0b011 => sd,
        _ => unimplemented!(),
      })(rs2r, r.s_imm(), rs1r),
      0b11100 => match (r.i_imm(), r.rs1(), r.funct3(), r.rd()) {
        (0, 0, 0, 0) => ecall,
        (1, 0, 0, 0) => ebreak,
        _ => unimplemented!(),
      },
      0b11000 => (match r.funct3() {
        0b000 => beq,
        0b001 => bne,
        0b100 => blt,
        0b101 => bge,
        0b110 => bltu,
        0b111 => bgeu,
        _ => unimplemented!(),
      })(rs1r, rs2r, r.b_imm()),
      0b01101 => lui(rdr, r.u_imm()),
      0b00101 => auipc(rdr, r.u_imm()),
      0b11011 => jal(rdr, r.j_imm()),
      0b11001 if r.funct3() == 0 => jalr(rdr, r.i_imm(), rs1r),
      0b00011 => {
        use fence_op::*;
        let fm = word >> 28;
        let io = (word >> 20) as u8;
        match (fm, io, r.rs1(), r.funct3(), r.rd()) {
          (0b0000, 0, 0, 1, 0) => fence_i,
          (0b0000, io, _, 0, _) => fence(io),
          (0b1000, PR | PW | SR | SW, 0, 0, 0) => fence_tso,
          _ => unimplemented!(),
        }
      }
      _ => unimplemented!(),
    };
    (insn, false)
  }
}

pub fn decode_compressed(half: u16) -> Option<Instruction> {
  use Instruction::*;
  use Reg::*;

  if half & 0b11 == 0b11 && half & 0b11100 != 0b11100 {
    return None;
  }
  let op = (half & 0b11) as u8;
  let funct3 = (half >> 13 & 0b111) as u8;
  let insn = match op {
    0 => {
      let rs1i = (half >> 7 & 0b111) as u8;
      let rdi_rs2i = (half >> 2 & 0b111) as u8;
      let (rdr_rs2r, rs1r) = (Reg::c(rdi_rs2i), Reg::c(rs1i));
      let (rdr, rs2r) = (rdr_rs2r, rdr_rs2r);
      match funct3 & 0b11 {
        // c.fld/c.ld | c.fsd/c.sd
        0b01 | 0b11 => {
          let uimm_5_3 = half >> 10 & 0b111;
          let uimm_7_6 = half >> 5 & 0b11;
          let uimm = ((uimm_7_6 << 6) + (uimm_5_3 << 3)) as u8;
          match funct3 {
            // 0b001 => c_fld(FloatReg::compress(rdi_rs2i), uimm, Reg::compress(rs1i)),
            0b011 => ld(rdr, uimm as i16, rs1r),
            // 0b101 => c_fsd(FloatReg::compress(rs1i), uimm, Reg::compress(rdi_rs2i)),
            0b111 => sd(rs2r, uimm as i16, rs1r),
            0b001 | 0b101 => unimplemented!("floating point"),
            _ => unreachable!(),
          }
        }
        // c.lw/c.sw
        0b10 => {
          let uimm_5_3 = half >> 10 & 0b111;
          let uimm_2 = half >> 6 & 1;
          let uimm_6 = half >> 5 & 1;
          let uimm = ((uimm_6 << 6) + (uimm_5_3 << 3) + (uimm_2 << 2)) as i16;
          (if funct3 & 0b100 == 0 { lw } else { sw })(rdr_rs2r, uimm, rs1r)
        }
        // c.addi4spn
        _ if funct3 == 0b000 => {
          let uimm_5_4 = half >> 11 & 0b11;
          let uimm_9_6 = half >> 7 & 0b1111;
          let uimm_2 = half >> 6 & 1;
          let uimm_3 = half >> 5 & 1;
          let uimm = (uimm_9_6 << 6) + (uimm_5_4 << 4) + (uimm_3 << 3) + (uimm_2 << 2);
          if uimm == 0 {
            unimplemented!("reserved");
          }
          addi(rdr, Reg::sp, uimm as i16)
        }
        _ => unimplemented!(),
      }
    }
    1 => {
      let hi_imm = half >> 12 & 1;
      let rd = (half >> 7 & 0b11111) as u8;
      let lo_imm = half >> 2 & 0b11111;
      let rdr = Reg::x(rd);
      match funct3 {
        0b000 | 0b001 | 0b010 => {
          let imm = sext16(((hi_imm << 5) + lo_imm) as u16, 6);
          match (funct3, rd, imm) {
            (0b001, 0, _) => unimplemented!("reserved"),
            (0b000, 0, _) => addi(zero, zero, 0),  // c.nop
            (0b000, _, _) => addi(rdr, rdr, imm),  // c.addi
            (0b001, _, _) => addiw(rdr, rdr, imm), // c.addiw
            (0b010, _, _) => addi(rdr, zero, imm), // cli
            _ => unreachable!(),
          }
        }
        0b011 => match rd {
          0 => unimplemented!("reserved"),
          2 => {
            let imm = (hi_imm << 9)
              + ((lo_imm >> 1 & 0b11) << 7)
              + ((lo_imm >> 3 & 1) << 6)
              + ((lo_imm & 1) << 5)
              + ((lo_imm >> 4) << 4);
            addi(Reg::sp, Reg::sp, sext16(imm as u16, 10)) // c.addi16sp
          }
          _ => {
            let imm = ((hi_imm as u32) << 17) + (lo_imm << 12) as u32;
            lui(rdr, sext32(imm, 18)) // c.lui
          }
        },
        0b100 => {
          let hi_funct2 = rd >> 3 & 0b11;
          let rdr = Reg::c(rd & 0b111);
          match hi_funct2 {
            0b11 => {
              let funct2 = lo_imm >> 3;
              let rs2i = (lo_imm & 0b111) as u8;
              (match (hi_imm, funct2) {
                (0, 0b00) => sub,
                (0, 0b01) => xor,
                (0, 0b10) => or,
                (0, 0b11) => and,
                (1, 0b00) => subw,
                (1, 0b01) => addw,
                (1, 0b10) => or,
                (1, 0b11) => and,
                _ => unimplemented!("reserved"),
              })(rdr, rdr, Reg::c(rs2i))
            }
            _ => {
              let imm = (hi_imm << 5 + lo_imm) as u8;
              match hi_funct2 {
                0b00 => srli(rdr, rdr, imm),                   // c.srli
                0b01 => srai(rdr, rdr, imm),                   // c.srai
                0b10 => andi(rdr, rdr, sext16(imm as u16, 6)), // c.andi
                _ => unimplemented!(),
              }
            }
          }
        }
        0b101 => {
          // inst[12:2] = imm[11|4|9:8|10|6|7|3:1|5]
          let (hi_imm, rd_rs1, lo_imm) = (hi_imm as u32, rd as u32, lo_imm as u32);
          let imm = (hi_imm << 11)
            + ((rd_rs1 >> 1 & 1) << 10)
            + ((rd_rs1 >> 2 & 0b11) << 8)
            + ((lo_imm >> 4) << 7)
            + ((rd_rs1 & 1) << 6)
            + ((lo_imm & 1) << 5)
            + ((rd_rs1 >> 4) << 4)
            + ((lo_imm >> 1 & 0b111) << 1);
          jal(zero, sext32(imm, 12)) // c.j
        }
        // c.beqz/c.bnez
        _ => {
          let rs1r = Reg::c(rd & 0b111);
          let imm = ((half >> 12 & 1) << 8)
            + ((lo_imm >> 3 & 0b11) << 6)
            + ((lo_imm & 1) << 5)
            + ((rd >> 3 & 0b11) << 3) as u16
            + ((lo_imm >> 1 & 0b11) << 1);
          (match funct3 {
            0b110 => beq,
            0b111 => bne,
            _ => unimplemented!(),
          })(rs1r, zero, sext16(imm as u16, 9))
        }
      }
    }
    2 => {
      let hi_imm = (half >> 12 & 1) as u16;
      let rd_rs1 = (half >> 7 & 0b11111) as u8;
      let rs2 = (half >> 2 & 0b11111) as u8;
      let (rdr_rs1r, rs2r) = (Reg::x(rd_rs1), Reg::x(rs2));
      let (rdr, rs1r) = (rdr_rs1r, rdr_rs1r);
      match funct3 {
        0b000 => {
          let uimm = (hi_imm << 5) as u8 + rs2;
          slli(rdr, rdr, uimm) // c.slli
        }
        0b010 | 0b011 if rd_rs1 == 0 => unimplemented!("reserved"),
        0b001 | 0b011 => {
          let rs2 = rs2 as u16;
          let uimm_8_6 = rs2 & 0b111;
          let uimm_4_3 = rs2 >> 3;
          let uimm = (uimm_8_6 << 6) + (hi_imm << 5) + (uimm_4_3 << 3);
          if funct3 & 0b10 == 0 {
            // c_fldsp(FloatReg::f(rd_rs1), uimm)
            todo!("floating point")
          } else {
            ld(rdr, uimm as i16, sp) // c.ldsp
          }
        }
        0b010 => {
          let uimm_7_6 = rs2 & 0b11;
          let uimm_4_2 = rs2 >> 2;
          let uimm = (uimm_7_6 << 6) + (hi_imm << 5) as u8 + (uimm_4_2 << 2);
          lw(rdr, uimm as i16, sp) // c.lwsp
        }
        0b100 => match (hi_imm, rd_rs1, rs2) {
          (0, 0, 0) => unimplemented!("reserved"),
          (0, _, 0) => jalr(zero, 0, rs1r),  // c.jr
          (0, _, _) => add(rdr, zero, rs2r), // c.mv
          (1, 0, 0) => ebreak,               // c.ebreak
          (1, _, 0) => jalr(ra, 0, rs1r),    // c.jalr
          (1, _, _) => add(rdr, rdr, rs2r),  // c.add
          _ => unimplemented!(),
        },
        0b101 | 0b111 => {
          let rd_rs1 = rd_rs1 as u16;
          let uimm_4_3 = rd_rs1 >> 3;
          let uimm_8_6 = rd_rs1 & 0b111;
          let uimm = (uimm_8_6 << 6) + (hi_imm << 5) + (uimm_4_3 << 3);
          if funct3 & 0b10 == 0 {
            // c_fsdsp(FloatReg::f(rs2), uimm)
            todo!("floating point")
          } else {
            sd(rs2r, uimm as i16, sp) // c.sdsp
          }
        }
        0b110 => {
          let uimm_4_2 = rd_rs1 >> 2;
          let uimm_7_6 = rd_rs1 & 0b111;
          let uimm = (uimm_7_6 << 6) + (hi_imm << 5) as u8 + (uimm_4_2 << 2);
          sw(rs2r, uimm as i16, sp) // c.swsp
        }
        _ => unimplemented!(),
      }
    }
    _ => unimplemented!(),
  };
  Some(insn)
}

macro_rules! impl_sign_extend {
  ($name:ident,$unsigned:ty,$signed:ty,$size:expr) => {
    fn $name(uimm: $unsigned, width: u8) -> $signed {
      debug_assert!(width <= $size);
      (((0 as $unsigned).wrapping_sub(uimm >> width - 1) << width) + uimm) as $signed
    }
  };
}

impl_sign_extend!(sext16, u16, i16, 16);
impl_sign_extend!(sext32, u32, i32, 32);

#[allow(non_camel_case_types)]
#[rustfmt::skip]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reg {
  zero = 0,
  ra,
  sp,
  gp,
  tp,
  t0, t1, t2,
  s0, s1,
  a0, a1,
  a2, a3, a4, a5, a6, a7,
  s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
  t3, t4, t5, t6,
}

impl Reg {
  #[allow(non_upper_case_globals)]
  pub const fp: Self = Reg::s0;

  pub fn x(n: u8) -> Self {
    assert!(n < 32);
    // SAFETY: See assert above
    unsafe { std::mem::transmute(n) }
  }

  pub fn c(n: u8) -> Self {
    assert!(n < 8);
    Self::x(n + 8)
  }
}

#[allow(non_camel_case_types)]
#[rustfmt::skip]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatRegister {
  ft0 = 0, ft1, ft2, ft3, ft4, ft5, ft6, ft7,
  fs0, fs1,
  fa0, fa1,
  fa2, fa3, fa4, fa5, fa6, fa7,
  fs2, fs3, fs4, fs5, fs6, fs7, fs8, fs9, fs10, fs11,
  ft8, ft9, ft10, ft11
}

impl FloatRegister {
  pub fn f(n: u8) -> Self {
    assert!(n < 32);
    // SAFETY: See assert above
    unsafe { std::mem::transmute(n) }
  }

  pub fn compress(n: u8) -> Self {
    assert!(n < 8);
    Self::f(n + 8)
  }
}

pub mod fence_op {
  pub const PI: u8 = 1 << 7;
  pub const PO: u8 = 1 << 6;
  pub const PR: u8 = 1 << 5;
  pub const PW: u8 = 1 << 4;
  pub const SI: u8 = 1 << 3;
  pub const SO: u8 = 1 << 2;
  pub const SR: u8 = 1 << 1;
  pub const SW: u8 = 1;
}
