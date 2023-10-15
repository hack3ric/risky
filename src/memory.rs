use std::collections::BTreeMap;
use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::Path;
use std::sync::Arc;

pub const PAGE_SIZE: u16 = 4096;

#[derive(Debug, Clone, Default)]
pub struct Memory {
  pages: BTreeMap<u32, Page>,
}

impl Memory {
  pub fn new() -> Self {
    Default::default()
  }

  fn page(&self, page_id: u32) -> Result<&Page, SegFault> {
    self.pages.get(&page_id).ok_or(SegFault(()))
  }

  pub fn read_u8(&self, addr: u64) -> Result<u8, SegFault> {
    let (page_id, offset) = parse_addr(addr)?;
    self.page(page_id).and_then(|p| p.read_u8(offset))
  }

  pub fn read_u16(&self, addr: u64) -> Result<u16, SegFault> {
    let (page_id, offset) = parse_addr(addr)?;
    let cur_page = self.page(page_id)?;
    let bytes = if offset == 0xfff {
      let next_page = self.page(page_id + 1)?;
      [cur_page.read_u8(0xfff)?, next_page.read_u8(0)?]
    } else {
      cur_page.read_bytes::<2>(offset)?
    };
    Ok(u16::from_le_bytes(bytes))
  }

  // TODO: optimize
  pub fn read_u32(&self, addr: u64) -> Result<u32, SegFault> {
    let mut bytes = [0; 4];
    bytes[0..2].copy_from_slice(&self.read_u16(addr)?.to_le_bytes());
    bytes[2..4].copy_from_slice(&self.read_u16(addr + 2)?.to_le_bytes());
    Ok(u32::from_le_bytes(bytes))
  }

  // TODO: optimize
  pub fn read_u64(&self, addr: u64) -> Result<u64, SegFault> {
    let mut bytes = [0; 8];
    bytes[0..4].copy_from_slice(&self.read_u16(addr)?.to_le_bytes());
    bytes[4..8].copy_from_slice(&self.read_u16(addr + 4)?.to_le_bytes());
    Ok(u64::from_le_bytes(bytes))
  }

  pub fn mmap_file(
    &mut self,
    page_id: u32,
    file: impl AsRef<Path>,
    len: u64,
    file_perm: [bool; 3],
    // mem_perm: [bool; 3],
  ) -> Result<(), SegFault> {
    let file = File::options()
      .read(file_perm[0])
      .write(file_perm[1])
      .open(file.as_ref())?;
    let file = Arc::new(file);

    // We currently don't care about the actual file's length though.
    //
    // This errors when the file length is greater than the entire 44-bit usable
    // memory space, or the pages are already allocated.
    let full_page_count = u32::try_from(len / u64::from(PAGE_SIZE)).map_err(|_| SegFault(()))?;
    let last_page_len = u16::try_from(len % u64::from(PAGE_SIZE)).unwrap();
    let total_page_count = full_page_count + u32::from(last_page_len > 0);
    for pid in page_id..(page_id + total_page_count) {
      if self.pages.contains_key(&pid) {
        return Err(SegFault(()));
      }
    }

    // The following steps of adding pages shall not cause segfault, otherwise it
    // will lose its atomicity.

    for p in 0..(total_page_count - 1) {
      let page = Page {
        block: MemBlock::File {
          inner: file.clone(),
          offset: u64::from(p) * u64::from(PAGE_SIZE),
          len: PAGE_SIZE,
          perm: file_perm,
        },
        perm: file_perm,
      };
      assert!(self.pages.insert(page_id + p, page).is_none());
    }
    let last_page = Page {
      block: MemBlock::File {
        inner: file,
        offset: u64::from(total_page_count - 1) * u64::from(PAGE_SIZE),
        len: if last_page_len == 0 {
          PAGE_SIZE
        } else {
          last_page_len
        },
        perm: file_perm,
      },
      perm: file_perm,
    };
    assert!(self
      .pages
      .insert(page_id + total_page_count - 1, last_page)
      .is_none());
    Ok(())
  }
}

fn parse_addr(addr: u64) -> Result<(u32, u16), SegFault> {
  // valid 44-bit address: 32-bit page ID + 12-bit page offset
  // high memory is not handled right now
  if addr >> 44 > 0 {
    return Err(SegFault(()));
  }
  let page_id = u32::try_from(addr >> 12).unwrap();
  let offset = u16::try_from(addr & 0xfff).unwrap();
  Ok((page_id, offset))
}

#[derive(Debug, Clone)]
pub struct Page {
  block: MemBlock,
  perm: [bool; 3],
}

impl Page {
  pub fn read_bytes<const N: usize>(&self, pos: u16) -> Result<[u8; N], SegFault> {
    if self.perm[0] {
      self.block.read_bytes(pos)
    } else {
      Err(SegFault(()))
    }
  }

  pub fn read_u8(&self, pos: u16) -> Result<u8, SegFault> {
    Ok(self.read_bytes::<1>(pos)?[0])
  }

  pub fn write_bytes<const N: usize>(&mut self, pos: u16, value: [u8; N]) -> Result<(), SegFault> {
    if self.perm[1] {
      self.block.write_bytes(pos, value)
    } else {
      Err(SegFault(()))
    }
  }

  fn set_perm(&mut self, idx: usize, value: bool) -> bool {
    // For anonymous pages, there's no restriction; for file-backed pages, the
    // maximum permission is the underlying files' opening permissions.
    if let MemBlock::File { perm, .. } = self.block {
      if !perm[idx] && value {
        return false;
      }
    }
    self.perm[idx] = value;
    true
  }

  pub fn set_read(&mut self, value: bool) -> bool {
    self.set_perm(0, value)
  }

  pub fn set_write(&mut self, value: bool) -> bool {
    self.set_perm(1, value)
  }

  pub fn set_exec(&mut self, value: bool) -> bool {
    self.set_perm(2, value)
  }
}

#[derive(Debug, Clone)]
enum MemBlock {
  Anonymous(Box<[u8; 4096]>),
  File {
    inner: Arc<File>,
    offset: u64,
    len: u16,
    perm: [bool; 3],
  },
}

impl MemBlock {
  fn read_bytes<const N: usize>(&self, pos: u16) -> Result<[u8; N], SegFault> {
    assert!(N <= 4);
    assert!(pos < 4096);
    match self {
      MemBlock::Anonymous(buf) => {
        let pos = usize::from(pos);
        buf
          .get(pos..pos + N)
          .ok_or(SegFault(()))?
          .try_into()
          .map_err(|_| SegFault(()))
      }
      MemBlock::File {
        inner, offset, len, ..
      } if pos < *len - (N as u16) + 1 => {
        let mut buf = [0; N];
        (inner.read_at(&mut buf, offset + u64::from(pos))? == N)
          .then_some(buf)
          .ok_or(SegFault(()))
      }
      MemBlock::File { .. } => Err(SegFault(())),
    }
  }

  fn write_bytes<const N: usize>(&mut self, pos: u16, value: [u8; N]) -> Result<(), SegFault> {
    assert!(N <= 4);
    assert!(pos < 4096);
    match self {
      MemBlock::Anonymous(buf) => {
        let pos = usize::from(pos);
        buf
          .get_mut(pos..pos + N)
          .ok_or(SegFault(()))?
          .copy_from_slice(&value);
      }
      MemBlock::File {
        inner, offset, len, ..
      } if pos < *len - (N as u16) + 1 => inner.write_all_at(&value, *offset + u64::from(pos))?,
      MemBlock::File { .. } => return Err(SegFault(())),
    }
    Ok(())
  }
}

// TODO: cause
#[derive(Debug, Clone)]
pub struct SegFault(());

impl From<std::io::Error> for SegFault {
  fn from(_value: std::io::Error) -> Self {
    Self(())
  }
}

#[test]
fn test() -> Result<(), SegFault> {
  let mut mem = Memory::new();
  mem.mmap_file(0x10000 / u32::from(PAGE_SIZE), "a.out", 1312, [
    true, false, true,
  ])?;
  let i = mem.read_u32(0x1010c)?.to_be();
  println!("{i:x}");
  Ok(())
}
