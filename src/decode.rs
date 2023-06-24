#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
  // * RV64I *
  /// - I:   opcode, funct3, rs1, rd,  imm
  /// - S/B: opcode, funct3, rs1, rs2, imm
  ISB(u8, u8, u8, u8, u32),
  /// opcode, rd, imm
  UJ(u8, u8, u32),

  add(u8, u8, u8),
  sub(u8, u8, u8),
  xor(u8, u8, u8),
  or(u8, u8, u8),
  and(u8, u8, u8),
  sll(u8, u8, u8),
  srl(u8, u8, u8),
  sra(u8, u8, u8),
  slt(u8, u8, u8),
  sltu(u8, u8, u8),

  addw(u8, u8, u8),
  subw(u8, u8, u8),
  sllw(u8, u8, u8),
  srlw(u8, u8, u8),
  sraw(u8, u8, u8),

  addi(u8, u8, i16),
  xori(u8, u8, i16),
  ori(u8, u8, i16),
  andi(u8, u8, i16),
  slli(u8, u8, u8),
  srli(u8, u8, u8),
  srai(u8, u8, u8),
  slti(u8, u8, i16),
  sltiu(u8, u8, i16),

  addiw(u8, u8, i16),
  slliw(u8, u8, u8),
  srliw(u8, u8, u8),
  sraiw(u8, u8, u8),

  // * RV64C *
  /// c.fld rd', uimm(rs1')
  c_fld(u8, u8, u8),
  /// c.ld rd', uimm(rs1')
  c_ld(u8, u8, u8),
  /// c.fsd rs1', uimm(rs2')
  c_fsd(u8, u8, u8),
  /// c.sd rs1', uimm(rs2')
  c_sd(u8, u8, u8),
  /// c.lw rd', uimm(rs1')
  c_lw(u8, u8, u8),
  /// c.sw rs1', uimm(rs2')
  c_sw(u8, u8, u8),
  /// c.addi4spn rd', uimm
  c_addi4spn(u8, u16),
  /// c.nop
  c_nop,
  /// c.addi rd, imm
  c_addi(u8, i8),
  c_addiw(u8, i8),
  c_li(u8, i8),
  c_addi16sp(i16),
  /// c.lui rd, imm
  c_lui(u8, i32),
  /// c.srli rd', uimm
  c_srli(u8, u8),
  /// c.srai rd', uimm
  c_srai(u8, u8),
  /// c.andi rd', imm
  c_andi(u8, i8),
  /// c.sub rd', rs2'
  c_sub(u8, u8),
  /// c.xor rd', rs2'
  c_xor(u8, u8),
  /// c.or rd', rs2'
  c_or(u8, u8),
  /// c.and rd', rs2'
  c_and(u8, u8),
  /// c.subw rd', rs2'
  c_subw(u8, u8),
  /// c.addw rd', rs2'
  c_addw(u8, u8),
  /// c.j offset
  c_j(i16),
  /// c.beqz rs1', imm
  c_beqz(u8, i16),
  /// c.bnez rs1', imm
  c_bnez(u8, i16),
  /// c.slli rd, uimm
  c_slli(u8, u8),
  c_fldsp(u8, u16),
  c_lwsp(u8, u8),
  c_ldsp(u8, u16),
  /// c.jr rs1
  c_jr(u8),
  /// c.mv rd, rs2
  c_mv(u8, u8),
  /// c.ebreak
  c_ebreak,
  /// c.jalr rs1
  c_jalr(u8),
  /// c_add rd, rs2
  c_add(u8, u8),
  /// c.fsdsp rs2, uimm(sp)
  c_fsdsp(u8, u16),
  c_swsp(u8, u8),
  c_sdsp(u8, u16),
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
      })(rd, rs1, rs2),
      // R-type, OP-32
      0b01110 => (match (funct3, funct7) {
        (0, 0) => addw,
        (0, 32) => subw,
        (1, 0) => sllw,
        (5, 0) => srlw,
        (5, 32) => sraw,
        _ => unimplemented!(),
      })(rd, rs1, rs2),
      // I-type, OP-IMM | OP-IMM32 | LOAD | SYSTEM | STORE
      op @ (0b00100 | 0b00110 | 0b00000 | 0b11100) => {
        let imm_11_5 = funct7 as u16;
        let imm = imm_11_5 << 5 + rs2;
        (match op {
          // OP-IMM
          0b00100 => match funct3 {
            0 => addi,
            4 => xori,
            6 => ori,
            7 => andi,
            1 if imm_11_5 == 0 => return slli(rd, rs1, rs2),
            5 if imm_11_5 == 0 => return srli(rd, rs1, rs2),
            5 if imm_11_5 == 32 => return srai(rd, rs1, rs2),
            2 => slti,
            3 => sltiu,
            _ => unimplemented!(),
          },
          // OP-IMM32
          0b00110 => match (funct3, imm_11_5) {
            (0, _) => addiw,
            (1, 0) => return slliw(rd, rs1, rs2),
            (5, 0) => return srliw(rd, rs1, rs2),
            (5, 32) => return sraiw(rd, rs1, rs2),
            _ => unimplemented!(),
          },
          _ => unreachable!(),
        })(rd, rs1, sx16(imm, 12))
      }
      // TODO: finish off
      // BRANCH
      0b11000 => {
        let (funct7, rd) = (funct7 as u32, rd as u32);
        let (imm_12, imm_10_5) = (funct7 >> 6, funct7 & 0b111111);
        let (imm_4_1, imm_11) = (rd >> 1 & 0b1111, rd & 1);
        let imm = imm_12 << 12 + imm_11 << 11 + imm_10_5 << 5 + imm_4_1 << 1;
        ISB(opcode, funct3, rs1, rs2, sign_extend_u32(imm, 13))
      }
      // LUI | AUIPC
      0b01101 | 0b00101 => {
        let (imm_31_25, imm_24_20, imm_19_15, imm_14_12) =
          (funct7 as u32, rs2 as u32, rs1 as u32, funct3 as u32);
        // Already 32-bit, no need to sign extend
        let imm = imm_31_25 << 25 + imm_24_20 << 20 + imm_19_15 << 15 + imm_14_12 << 12;
        UJ(opcode, rd, imm)
      }
      _ => unimplemented!(),
    }
  } else {
    // 16-bit
    // Although no F/D implementation now, C.F* is still parsed
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
              0b001 => c_fld(rdi_rs2i, uimm, rs1i),
              0b011 => c_ld(rdi_rs2i, uimm, rs1i),
              0b101 => c_fsd(rs1i, uimm, rdi_rs2i),
              0b111 => c_sd(rs1i, uimm, rdi_rs2i),
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
              c_lw(rdi_rs2i, uimm, rs1i)
            } else {
              c_sw(rs1i, uimm, rdi_rs2i)
            }
          }
          // c.addi4spn
          _ if funct3 == 0b000 => {
            let uimm_5_4 = word >> 11 & 0b11;
            let uimm_9_6 = word >> 7 & 0b1111;
            let uimm_2 = word >> 6 & 1;
            let uimm_3 = word >> 5 & 1;
            let uimm = uimm_9_6 << 6 + uimm_5_4 << 4 + uimm_3 << 3 + uimm_2 << 2;
            c_addi4spn(rdi_rs2i, uimm as u16)
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
            let imm = sx8((hi_imm << 5 + lo_imm) as u8, 6);
            match (funct3, rd, imm) {
              (0b000, 0, _) => c_nop,
              (0b000, rd, imm) => c_addi(rd, imm),
              (0b001, 0, _) => unimplemented!("reserved"),
              (0b001, rd, imm) => c_addiw(rd, imm),
              (0b010, rd, imm) => c_li(rd, imm),
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
              c_addi16sp(sx16(imm as u16, 10))
            }
            _ => {
              let imm = hi_imm << 17 + lo_imm << 12;
              c_lui(rd, sx32(imm, 18))
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
                })(rdi, rs2i)
              }
              _ => {
                let imm = (hi_imm << 5 + lo_imm) as u8;
                match hi_funct2 {
                  0b00 => c_srli(rdi, imm),
                  0b01 => c_srai(rdi, imm),
                  0b10 => c_andi(rdi, sx8(imm, 6)),
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
            c_j(sx16(imm, 12))
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
            })(rs1i, sx16(imm as u16, 9))
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
            c_slli(rd_rs1, uimm as u8)
          }
          0b001 | 0b011 => {
            let uimm_8_6 = rs2 as u16 & 0b111;
            let uimm_4_3 = rs2 >> 3;
            let uimm = uimm_8_6 << 6 + hi_imm << 5 + uimm_4_3 << 3;
            (if funct3 & 0b10 == 0 { c_fldsp } else { c_ldsp })(rd_rs1, uimm)
          }
          0b010 => {
            let uimm_7_6 = rs2 & 0b11;
            let uimm_4_2 = rs2 >> 2;
            let uimm = uimm_7_6 << 6 + hi_imm << 5 + uimm_4_2 << 2;
            c_lwsp(rd_rs1, uimm)
          }
          0b100 => match (hi_imm, rd_rs1, rs2) {
            (0, 0, 0) => unimplemented!("reserved"),
            (0, rs1, 0) => c_jr(rs1),
            (0, rd, rs2) => c_mv(rd, rs2),
            (1, 0, 0) => c_ebreak,
            (1, rs1, 0) => c_jalr(rs1),
            (1, rd, rs2) => c_add(rd, rs2),
            _ => unimplemented!(),
          },
          0b101 | 0b111 => {
            let uimm_4_3 = rd_rs1 >> 3;
            let uimm_8_6 = rd_rs1 as u16 & 0b111;
            let uimm = uimm_8_6 << 6 + hi_imm << 5 + uimm_4_3 << 3;
            (if funct3 & 0b10 == 0 { c_fsdsp } else { c_sdsp })(rs2, uimm)
          }
          0b110 => {
            let uimm_4_2 = rd_rs1 >> 2;
            let uimm_7_6 = rd_rs1 & 0b111;
            let uimm = uimm_7_6 << 6 + hi_imm << 5 + uimm_4_2 << 2;
            c_swsp(rs2, uimm)
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

impl_sign_extend!(sx8, u8, i8, 8);
impl_sign_extend!(sx16, u16, i16, 16);
impl_sign_extend!(sx32, u32, i32, 32);

fn sign_extend_u32(uimm: u32, width: u8) -> u32 {
  assert!(width <= 32);
  (0u32.wrapping_sub(uimm >> width - 1) << width) + uimm
}

#[allow(non_camel_case_types)]
#[rustfmt::skip]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
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

impl Register {
  #[allow(non_upper_case_globals)]
  pub const fp: Self = Register::s0;

  pub fn x(n: u8) -> Self {
    assert!(n < 32);
    // SAFETY: See assert above
    unsafe { std::mem::transmute(n) }
  }

  pub fn from_compressed(n: u8) -> Self {
    assert!(n < 8);
    Self::x(n + 8)
  }
}