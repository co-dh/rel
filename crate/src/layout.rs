#![forbid(unsafe_code)]
//! `exc_layout` / `for_layout` / `alp_layout` (coc.h:199, 209, 1518) as one function, and own.c's `exc_ok`.
use crate::why::Why;
use crate::BLK;

/// `for_layout` frm=0, frm=1, `alp_layout`.
pub enum Tail { None, Frames, Exps }
pub struct ExcLayout { pub raw: usize, pub off: usize, pub pos: usize, pub tail: usize, pub size: usize }

const ALP_MAXE: i32 = 18; // coc.h ALP_MAXE

fn align8(x: usize) -> Option<usize> { Some(x.checked_add(7)? & !7) }

/// None = overflow.
pub fn exc_layout(nblk: usize, nexc: usize, esz: usize, tail: Tail) -> Option<ExcLayout> {
    let raw: usize = 16;
    let off = align8(raw.checked_add(nexc.checked_mul(esz)?)?)?;
    let pos = align8(off.checked_add(nblk.checked_add(1)?.checked_mul(4)?)?)?;
    let t = align8(pos.checked_add(nexc.checked_mul(2)?)?)?;
    let size = match tail {
        Tail::None => t,
        Tail::Frames => t.checked_add(nblk.checked_mul(8)?)?,
        Tail::Exps => align8(t.checked_add(nblk)?)?,
    };
    Some(ExcLayout { raw, off, pos, tail: t, size })
}

fn u32_at(t: &[u8], o: usize) -> u32 { u32::from_ne_bytes(t[o..o + 4].try_into().unwrap()) }
fn u16_at(t: &[u8], o: usize) -> u16 { u16::from_ne_bytes(t[o..o + 2].try_into().unwrap()) }

/// The exception ladder at `t` in part `part`: a FoR patch list fills its tail exactly, an ALP blob
/// (`Tail::Exps`) holds it with a decimal exponent a block after it.
pub fn exc_ok(t: &[u8], nblk: usize, nexc: u64, esz: usize, part: i32, tail: Tail, why: &mut Why) -> bool {
    let len = t.len();
    let alp = matches!(tail, Tail::Exps);
    let l = if nexc > len as u64 / (esz as u64 + 2) { None } else { exc_layout(nblk, nexc as usize, esz, tail) };
    // the usize::MAX of C is an overflow here: never fits
    if !l.as_ref().is_some_and(|l| if alp { l.size <= len } else { l.size == len }) {
        why.say(format_args!("part {part}: the exception sections of {nblk} blocks and {nexc} exceptions of {esz} bytes, found {len} bytes"));
        return false;
    }
    let l = l.unwrap();
    let eo = |b: usize| u32_at(t, l.off + 4 * b);
    let ep = |j: usize| u16_at(t, l.pos + 2 * j);
    let ex = |b: usize| t[l.tail + b] as i8;
    if eo(0) != 0 || eo(nblk) as u64 != nexc {
        why.say(format_args!("part {part}: exception offsets running from 0 to {nexc}, found {} to {}", eo(0), eo(nblk)));
        return false;
    }
    for b in 0..nblk {
        if eo(b) > eo(b + 1) {
            why.say(format_args!("part {part} block {b}: ascending exception offsets, found {} then {}", eo(b), eo(b + 1)));
            return false;
        }
        if alp && (ex(b) < 0 || ex(b) as i32 > ALP_MAXE) {
            why.say(format_args!("part {part} block {b}: a decimal exponent in 0..{ALP_MAXE}, found {}", ex(b)));
            return false;
        }
    }
    for j in 0..nexc as usize {
        if ep(j) as usize >= BLK {
            why.say(format_args!("part {part} exception {j}: a position inside its block of {BLK}, found {}", ep(j)));
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    fn say(f: impl FnOnce(&mut Why) -> bool) -> (bool, String) {
        let mut b = [0u8; 200];
        let r = f(&mut Why::new(&mut b));
        let n = b.iter().position(|&c| c == 0).unwrap();
        (r, String::from_utf8(b[..n].to_vec()).unwrap())
    }
    #[test] fn layout_c_arithmetic() {
        let l = exc_layout(1, 0, 8, Tail::None).unwrap();
        assert_eq!((l.raw, l.off, l.pos, l.tail, l.size), (16, 16, 24, 24, 24));
        let l = exc_layout(2, 3, 8, Tail::Frames).unwrap();
        assert_eq!((l.off, l.pos, l.tail, l.size), (40, 56, 64, 80));
        assert_eq!(exc_layout(2, 3, 8, Tail::Exps).unwrap().size, 72);
        assert!(exc_layout(1, usize::MAX, 8, Tail::None).is_none());
    }
    #[test] fn wrong_size_message() {
        let (ok, m) = say(|w| exc_ok(&[0; 10], 1, 0, 8, 1, Tail::None, w));
        assert!(!ok);
        assert_eq!(m, "part 1: the exception sections of 1 blocks and 0 exceptions of 8 bytes, found 10 bytes");
    }
    #[test] fn empty_ladder_ok_and_alp_slack() {
        let mut t = [0u8; 40]; // nblk 1, nexc 0: off 16, pos 24, exp at 24, size 32
        assert!(say(|w| exc_ok(&t[..24], 1, 0, 8, 1, Tail::None, w)).0);
        assert!(say(|w| exc_ok(&t, 1, 0, 8, 2, Tail::Exps, w)).0);
        assert!(!say(|w| exc_ok(&t, 1, 0, 8, 2, Tail::None, w)).0);
        t[24] = 19;
        assert_eq!(say(|w| exc_ok(&t, 1, 0, 8, 2, Tail::Exps, w)).1, "part 2 block 0: a decimal exponent in 0..18, found 19");
        t[24] = 0; t[20] = 1;
        assert_eq!(say(|w| exc_ok(&t, 1, 0, 8, 2, Tail::Exps, w)).1, "part 2: exception offsets running from 0 to 0, found 0 to 1");
    }
}
