use crate::decode::Reg;
use crate::decode::FloatReg;

/// State of a hart.
#[derive(Debug, Clone)]
pub struct State {
  pc: i64,
  regs: [i64; 31],
  float_regs: [f64; 32],
}

impl State {
  fn pc(&self) -> i64 {
    self.pc
  }

  fn jump(&mut self, offset: i64) {
    self.pc += offset;
  }

  fn reg(&self, index: Reg) -> i64 {
    if index == Reg::zero {
      0
    } else {
      self.regs[index as u8 as usize - 1]
    }
  }

  fn set_reg(&mut self, index: Reg, value: i64) {
    if index != Reg::zero {
      self.regs[index as u8 as usize - 1] = value;
    }
  }

  fn float_reg(&self, index: FloatReg) -> f64 {
    self.float_regs[index as u8 as usize]
  }

  fn set_float_reg(&mut self, index: FloatReg, value: f64) {
    self.float_regs[index as u8 as usize] = value;
  }
}
