use crate::decode::{decode_compressed, decode_word, Instruction};
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionBytes {
  Full(u32),
  Compressed(u16),
}

impl Display for InstructionBytes {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Full(i) => write!(f, "{i:0>8x}"),
      Self::Compressed(i) => write!(f, "{i:0>4x}"),
    }
  }
}

pub fn disasm(asm: &[u8]) -> (Vec<(InstructionBytes, Instruction)>, u8) {
  let len = asm.len();
  let mut cursor = 0;
  let mut result = Vec::new();
  let mut unexpected = 0;
  while cursor < len {
    match len - cursor {
      1 => {
        println!("unexpected 1 byte remaining");
        unexpected = 1;
        break;
      }
      x @ (2 | 3) => {
        let half = u16::from_le_bytes(asm[cursor..cursor + 2].try_into().unwrap());
        if let Some(insn) = decode_compressed(half) {
          result.push((InstructionBytes::Compressed(half), insn));
          cursor += 2;
        } else {
          unexpected = x as u8;
          break;
        }
      }
      _ => {
        let word = u32::from_le_bytes(asm[cursor..cursor + 4].try_into().unwrap());
        let (insn, compressed) = decode_word(word);
        let bytes = if compressed {
          cursor += 2;
          InstructionBytes::Compressed(word as u16)
        } else {
          cursor += 4;
          InstructionBytes::Full(word)
        };
        result.push((bytes, insn))
      }
    }
  }
  (result, unexpected)
}
