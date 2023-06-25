#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
  // * RV64I *
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

  lb(Reg, i16, Reg),
  lh(Reg, i16, Reg),
  lw(Reg, i16, Reg),
  /// ld rd, imm(rs1)
  ld(Reg, i16, Reg),
  lbu(Reg, i16, Reg),
  lhu(Reg, i16, Reg),
  lwu(Reg, i16, Reg),
  /// sb rs1, imm(rs2)
  sb(Reg, i16, Reg),
  sh(Reg, i16, Reg),
  sw(Reg, i16, Reg),
  sd(Reg, i16, Reg),
  /// lui rd, imm
  lui(Reg, i32),

  /// auipc rd, imm
  auipc(Reg, i32),
  /// beq rs1, rs2, label
  beq(Reg, Reg, i16),
  bne(Reg, Reg, i16),
  blt(Reg, Reg, i16),
  bge(Reg, Reg, i16),
  bltu(Reg, Reg, i16),
  bgeu(Reg, Reg, i16),
  /// jal rd, label
  jal(Reg, i32),
  /// jalr rd, imm(rs1)
  jalr(Reg, i16, Reg),
  ecall,
  ebreak,
  /// fence pred, succ
  fence(u8),
  fence_tso,

  // * Zifencei *
  fence_i,

  // * RV64M *
  mul(Reg, Reg, Reg),
  mulh(Reg, Reg, Reg),
  mulhu(Reg, Reg, Reg),
  mulhsu(Reg, Reg, Reg),
  mulw(Reg, Reg, Reg),
  div(Reg, Reg, Reg),
  divu(Reg, Reg, Reg),
  rem(Reg, Reg, Reg),
  remu(Reg, Reg, Reg),
  divw(Reg, Reg, Reg),
  divuw(Reg, Reg, Reg),
  remw(Reg, Reg, Reg),
  remuw(Reg, Reg, Reg),

  // * RV64C *
  /// c.fld rd', uimm(rs1')
  c_fld(FloatReg, u8, Reg),
  /// c.ld rd', uimm(rs1')
  c_ld(Reg, u8, Reg),
  /// c.fsd rs1', uimm(rs2')
  c_fsd(FloatReg, u8, Reg),
  /// c.sd rs1', uimm(rs2')
  c_sd(Reg, u8, Reg),
  /// c.lw rd', uimm(rs1')
  c_lw(Reg, u8, Reg),
  /// c.sw rs1', uimm(rs2')
  c_sw(Reg, u8, Reg),
  /// c.addi4spn rd', uimm
  c_addi4spn(Reg, u16),
  /// c.nop
  c_nop,
  /// c.addi rd, imm
  c_addi(Reg, i8),
  c_addiw(Reg, i8),
  c_li(Reg, i8),
  c_addi16sp(i16),
  /// c.lui rd, imm
  c_lui(Reg, i32),
  /// c.srli rd', uimm
  c_srli(Reg, u8),
  /// c.srai rd', uimm
  c_srai(Reg, u8),
  /// c.andi rd', imm
  c_andi(Reg, i8),
  /// c.sub rd', rs2'
  c_sub(Reg, Reg),
  /// c.xor rd', rs2'
  c_xor(Reg, Reg),
  /// c.or rd', rs2'
  c_or(Reg, Reg),
  /// c.and rd', rs2'
  c_and(Reg, Reg),
  /// c.subw rd', rs2'
  c_subw(Reg, Reg),
  /// c.addw rd', rs2'
  c_addw(Reg, Reg),
  /// c.j offset
  c_j(i16),
  /// c.beqz rs1', imm
  c_beqz(Reg, i16),
  /// c.bnez rs1', imm
  c_bnez(Reg, i16),
  /// c.slli rd, uimm
  c_slli(Reg, u8),
  c_fldsp(FloatReg, u16),
  c_lwsp(Reg, u8),
  c_ldsp(Reg, u16),
  /// c.jr rs1
  c_jr(Reg),
  /// c.mv rd, rs2
  c_mv(Reg, Reg),
  /// c.ebreak
  c_ebreak,
  /// c.jalr rs1
  c_jalr(Reg),
  /// c_add rd, rs2
  c_add(Reg, Reg),
  /// c.fsdsp rs2, uimm(sp)
  c_fsdsp(FloatReg, u16),
  c_swsp(Reg, u8),
  c_sdsp(Reg, u16),
}

pub fn parse_word(word: u32) -> Instruction {
  use Instruction::*;
  if word & 0b11 == 0b11 && word & 0b11100 != 0b11100 {
    // 32-bit
    let funct7 = (word >> 25) as u8;
    let rs2 = (word >> 20 & 0b11111) as u8;
    let rs1 = (word >> 15 & 0b11111) as u8;
    let funct3 = (word >> 12 & 0b111) as u8;
    let rd = (word >> 7 & 0b11111) as u8;
    let opcode = (word & 0b1111111) as u8;
    match opcode >> 2 {
      // R-type, OP
      0b01100 => (match (funct3, funct7) {
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
      })(Reg::x(rd), Reg::x(rs1), Reg::x(rs2)),
      // R-type, OP-32
      0b01110 => (match (funct3, funct7) {
        (0, 0) => addw,
        (0, 32) => subw,
        (1, 0) => sllw,
        (5, 0) => srlw,
        (5, 32) => sraw,
        _ => unimplemented!(),
      })(Reg::x(rd), Reg::x(rs1), Reg::x(rs2)),
      // I-type, OP-IMM | OP-IMM32 | LOAD
      op @ (0b00100 | 0b00110 | 0b00000) => {
        let imm_11_5 = funct7 as u16;
        let imm = imm_11_5 << 5 + rs2;
        match op {
          // OP-IMM
          0b00100 => (match funct3 {
            0 => addi,
            4 => xori,
            6 => ori,
            7 => andi,
            1 if imm_11_5 == 0 => return slli(Reg::x(rd), Reg::x(rs1), rs2),
            5 if imm_11_5 == 0 => return srli(Reg::x(rd), Reg::x(rs1), rs2),
            5 if imm_11_5 == 32 => return srai(Reg::x(rd), Reg::x(rs1), rs2),
            2 => slti,
            3 => sltiu,
            _ => unimplemented!(),
          })(Reg::x(rd), Reg::x(rs1), sext16(imm, 12)),
          // OP-IMM32
          0b00110 => (match (funct3, imm_11_5) {
            (0, _) => return addiw(Reg::x(rd), Reg::x(rs1), sext16(imm, 12)),
            (1, 0) => slliw,
            (5, 0) => srliw,
            (5, 32) => sraiw,
            _ => unimplemented!(),
          })(Reg::x(rd), Reg::x(rs1), rs2),
          // LOAD
          0b00000 => (match funct3 {
            0b000 => lb,
            0b001 => lh,
            0b010 => lw,
            0b011 => ld,
            0b100 => lbu,
            0b101 => lhu,
            0b110 => lwu,
            _ => unimplemented!(),
          })(Reg::x(rd), sext16(imm, 12), Reg::x(rs1)),
          _ => unreachable!(),
        }
      }
      // S-type, STORE
      0b01000 => {
        let imm_11_5 = funct7 as u16;
        let imm = imm_11_5 << 5 + rd;
        (match funct3 {
          0b000 => sb,
          0b001 => sh,
          0b010 => sw,
          0b011 => sd,
          _ => unimplemented!(),
        })(Reg::x(rs1), sext16(imm, 12), Reg::x(rs2))
      }
      // I-type(?), SYSTEM
      0b11100 => match (funct7, rs2, rs1, funct3, rd) {
        (0, 0, 0, 0, 0) => ecall,
        (1, 0, 0, 0, 0) => ebreak,
        _ => unimplemented!(),
      },
      // B-type, BRANCH
      0b11000 => {
        let funct7 = funct7 as u16;
        let (imm_12, imm_10_5) = (funct7 >> 6, funct7 & 0b111111);
        let (imm_4_1, imm_11) = (rd >> 1 & 0b1111, rd & 1);
        let imm = imm_12 << 12 + imm_11 << 11 + imm_10_5 << 5 + imm_4_1 << 1;
        (match funct3 {
          0b000 => beq,
          0b001 => bne,
          0b100 => blt,
          0b101 => bge,
          0b110 => bltu,
          0b111 => bgeu,
          _ => unimplemented!(),
        })(Reg::x(rs1), Reg::x(rs2), sext16(imm, 13))
      }
      // lui | auipc
      op @ (0b01101 | 0b00101) => {
        let (imm_31_25, imm_24_20, imm_19_15, imm_14_12) =
          (funct7 as u32, rs2 as u32, rs1 as u32, funct3 as u32);
        let imm = imm_31_25 << 25 + imm_24_20 << 20 + imm_19_15 << 15 + imm_14_12 << 12;
        (match op {
          0b01101 => lui,
          0b00101 => auipc,
          _ => unimplemented!(),
        })(Reg::x(rd), imm as i32) // Already 32-bit, no need to sign extend
      }
      // J-type, jal
      0b11011 => {
        let (funct7, rs2, imm_19_15, imm_14_12) =
          (funct7 as u32, rs2 as u32, rs1 as u32, funct3 as u32);
        let imm = ((funct7 >> 6) << 20)
          + (imm_19_15 << 15)
          + (imm_14_12 << 12)
          + ((rs2 & 1) << 11)
          + ((funct7 & 0b111111) << 5)
          + ((rs2 >> 1) << 1);
        jal(Reg::x(rd), sext32(imm, 21))
      }
      // R-type, jalr
      0b11001 => {
        let imm_11_5 = funct7 as u16;
        let imm = imm_11_5 << 5 + rs2;
        jalr(Reg::x(rd), sext16(imm, 20), Reg::x(rs1))
      }
      0b00011 => {
        use fence_op::*;
        let fm = word >> 28;
        let io = (word >> 20) as u8;
        match (fm, io, rs1, funct3, rd) {
          (0b0000, 0, 0, 1, 0) => fence_i,
          (0b0000, io, _, 0, _) => fence(io),
          (0b1000, PR | PW | SR | SW, 0, 0, 0) => fence_tso,
          _ => unimplemented!(),
        }
      }
      _ => unimplemented!(),
    }
  } else {
    // 16-bit
    // Although no F/D implementation now, c.f* is still parsed
    let word = word & (u16::MAX as u32);
    let op = (word & 0b11) as u8;

    let funct3 = (word >> 13 & 0b111) as u8;
    match op {
      0 => {
        let rs1i = (word >> 7 & 0b111) as u8;
        let rdi_rs2i = (word >> 2 & 0b111) as u8;
        match funct3 & 0b11 {
          // c.fld/c.ld | c.fsd/c.sd
          0b01 | 0b11 => {
            let uimm_5_3 = word >> 10 & 0b111;
            let uimm_7_6 = word >> 5 & 0b11;
            let uimm = (uimm_7_6 << 6 + uimm_5_3 << 3) as u8;
            match funct3 {
              0b001 => c_fld(FloatReg::compress(rdi_rs2i), uimm, Reg::compress(rs1i)),
              0b011 => c_ld(Reg::compress(rdi_rs2i), uimm, Reg::compress(rs1i)),
              0b101 => c_fsd(FloatReg::compress(rs1i), uimm, Reg::compress(rdi_rs2i)),
              0b111 => c_sd(Reg::compress(rs1i), uimm, Reg::compress(rdi_rs2i)),
              _ => unreachable!(),
            }
          }
          // c.lw/c.sw
          0b10 => {
            let uimm_5_3 = word >> 10 & 0b111;
            let uimm_2 = word >> 6 & 1;
            let uimm_6 = word >> 5 & 1;
            let uimm = (uimm_6 << 6 + uimm_5_3 << 3 + uimm_2 << 2) as u8;
            if funct3 & 0b100 == 0 {
              c_lw(Reg::compress(rdi_rs2i), uimm, Reg::compress(rs1i))
            } else {
              c_sw(Reg::compress(rs1i), uimm, Reg::compress(rdi_rs2i))
            }
          }
          // c.addi4spn
          _ if funct3 == 0b000 => {
            let uimm_5_4 = word >> 11 & 0b11;
            let uimm_9_6 = word >> 7 & 0b1111;
            let uimm_2 = word >> 6 & 1;
            let uimm_3 = word >> 5 & 1;
            let uimm = uimm_9_6 << 6 + uimm_5_4 << 4 + uimm_3 << 3 + uimm_2 << 2;
            c_addi4spn(Reg::compress(rdi_rs2i), uimm as u16)
          }
          _ => unimplemented!(),
        }
      }
      1 => {
        let hi_imm = word >> 12 & 1;
        let rd = (word >> 7 & 0b11111) as u8;
        let lo_imm = word >> 2 & 0b11111;
        match funct3 {
          0b000 | 0b001 | 0b010 => {
            let imm = sext8((hi_imm << 5 + lo_imm) as u8, 6);
            match (funct3, rd, imm) {
              (0b000, 0, _) => c_nop,
              (0b000, rd, imm) => c_addi(Reg::x(rd), imm),
              (0b001, 0, _) => unimplemented!("reserved"),
              (0b001, rd, imm) => c_addiw(Reg::x(rd), imm),
              (0b010, rd, imm) => c_li(Reg::x(rd), imm),
              _ => unreachable!(),
            }
          }
          0b011 => match rd {
            0 => unimplemented!("reserved"),
            2 => {
              let imm_4 = lo_imm >> 4;
              let imm_6 = lo_imm >> 3 & 1;
              let imm_8_7 = lo_imm >> 1 & 0b11;
              let imm_5 = lo_imm & 1;
              let imm = hi_imm << 9 + imm_8_7 << 7 + imm_6 << 6 + imm_5 << 5 + imm_4 << 4;
              c_addi16sp(sext16(imm as u16, 10))
            }
            _ => {
              let imm = hi_imm << 17 + lo_imm << 12;
              c_lui(Reg::x(rd), sext32(imm, 18))
            }
          },
          0b100 => {
            let hi_funct2 = rd >> 3 & 0b11;
            let rdi = rd & 0b111;
            match hi_funct2 {
              0b11 => {
                let funct2 = lo_imm >> 3;
                let rs2i = (lo_imm & 0b111) as u8;
                (match (hi_imm, funct2) {
                  (0, 0b00) => c_sub,
                  (0, 0b01) => c_xor,
                  (0, 0b10) => c_or,
                  (0, 0b11) => c_and,
                  (1, 0b00) => c_subw,
                  (1, 0b01) => c_addw,
                  (1, 0b10) => c_or,
                  (1, 0b11) => c_and,
                  _ => unimplemented!("reserved"),
                })(Reg::compress(rdi), Reg::compress(rs2i))
              }
              _ => {
                let imm = (hi_imm << 5 + lo_imm) as u8;
                match hi_funct2 {
                  0b00 => c_srli(Reg::compress(rdi), imm),
                  0b01 => c_srai(Reg::compress(rdi), imm),
                  0b10 => c_andi(Reg::compress(rdi), sext8(imm, 6)),
                  _ => unimplemented!(),
                }
              }
            }
          }
          0b101 => {
            // inst[12:2] = imm[11|4|9:8|10|6|7|3:1|5]
            let (hi_imm, rd_rs1, lo_imm) = (hi_imm as u16, rd as u16, lo_imm as u16);
            let imm = (hi_imm << 11)
              + ((rd_rs1 >> 1 & 1) << 10)
              + ((rd_rs1 >> 2 & 0b11) << 8)
              + ((lo_imm >> 4) << 7)
              + ((rd_rs1 & 1) << 6)
              + ((lo_imm & 1) << 5)
              + ((rd_rs1 >> 4) << 4)
              + ((lo_imm >> 1 & 0b111) << 1);
            c_j(sext16(imm, 12))
          }
          _ => {
            let imm_4_3 = rd >> 3 & 0b11;
            let rs1i = rd & 0b111;
            let imm_7_6 = lo_imm >> 3 & 0b11;
            let imm_2_1 = lo_imm >> 1 & 0b11;
            let imm_5 = lo_imm & 1;
            let imm = hi_imm << 8 + imm_7_6 << 6 + imm_5 << 5 + imm_4_3 << 3 + imm_2_1 << 1;
            (match funct3 {
              0b110 => c_beqz,
              0b111 => c_bnez,
              _ => unimplemented!(),
            })(Reg::compress(rs1i), sext16(imm as u16, 9))
          }
        }
      }
      2 => {
        let hi_imm = word >> 12 & 1;
        let rd_rs1 = (word >> 7 & 0b11111) as u8;
        let rs2 = (word >> 2 & 0b11111) as u8;
        match funct3 {
          0b000 => {
            let uimm = hi_imm << 5 + rs2;
            c_slli(Reg::x(rd_rs1), uimm as u8)
          }
          0b001 | 0b011 => {
            let uimm_8_6 = rs2 as u16 & 0b111;
            let uimm_4_3 = rs2 >> 3;
            let uimm = uimm_8_6 << 6 + hi_imm << 5 + uimm_4_3 << 3;
            if funct3 & 0b10 == 0 {
              c_fldsp(FloatReg::f(rd_rs1), uimm)
            } else {
              c_ldsp(Reg::x(rd_rs1), uimm)
            }
          }
          0b010 => {
            let uimm_7_6 = rs2 & 0b11;
            let uimm_4_2 = rs2 >> 2;
            let uimm = uimm_7_6 << 6 + hi_imm << 5 + uimm_4_2 << 2;
            c_lwsp(Reg::x(rd_rs1), uimm)
          }
          0b100 => match (hi_imm, rd_rs1, rs2) {
            (0, 0, 0) => unimplemented!("reserved"),
            (0, rs1, 0) => c_jr(Reg::x(rs1)),
            (0, rd, rs2) => c_mv(Reg::x(rd), Reg::x(rs2)),
            (1, 0, 0) => c_ebreak,
            (1, rs1, 0) => c_jalr(Reg::x(rs1)),
            (1, rd, rs2) => c_add(Reg::x(rd), Reg::x(rs2)),
            _ => unimplemented!(),
          },
          0b101 | 0b111 => {
            let uimm_4_3 = rd_rs1 >> 3;
            let uimm_8_6 = rd_rs1 as u16 & 0b111;
            let uimm = uimm_8_6 << 6 + hi_imm << 5 + uimm_4_3 << 3;
            if funct3 & 0b10 == 0 {
              c_fsdsp(FloatReg::f(rs2), uimm)
            } else {
              c_sdsp(Reg::x(rs2), uimm)
            }
          }
          0b110 => {
            let uimm_4_2 = rd_rs1 >> 2;
            let uimm_7_6 = rd_rs1 & 0b111;
            let uimm = uimm_7_6 << 6 + hi_imm << 5 + uimm_4_2 << 2;
            c_swsp(Reg::x(rs2), uimm)
          }
          _ => unimplemented!(),
        }
      }
      _ => unimplemented!(),
    }
  }
}

macro_rules! impl_sign_extend {
  ($name:ident,$unsigned:ty,$signed:ty,$size:expr) => {
    fn $name(uimm: $unsigned, width: u8) -> $signed {
      debug_assert!(width <= $size);
      (((0 as $unsigned).wrapping_sub(uimm >> width - 1) << width) + uimm) as $signed
    }
  };
}

impl_sign_extend!(sext8, u8, i8, 8);
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

  pub fn compress(n: u8) -> Self {
    assert!(n < 8);
    Self::x(n + 8)
  }
}

#[allow(non_camel_case_types)]
#[rustfmt::skip]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatReg {
  ft0 = 0, ft1, ft2, ft3, ft4, ft5, ft6, ft7,
  fs0, fs1,
  fa0, fa1,
  fa2, fa3, fa4, fa5, fa6, fa7,
  fs2, fs3, fs4, fs5, fs6, fs7, fs8, fs9, fs10, fs11,
  ft8, ft9, ft10, ft11
}

impl FloatReg {
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
