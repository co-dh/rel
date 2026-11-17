//! interp.rs's two computations, free of Lean objects.
#![forbid(unsafe_code)]

/// The key a verb spelling reads its cell under: a spelling of 1 to 7 bytes packs whole into a `u64`, its length in the
/// low byte and the bytes above it, so the packing is injective and a slot whose stored key matches needs no string
/// compare. `0` is the "ask the string table" answer (empty or longer than 7 bytes); no packed key is `0`, the length
/// being nonzero in the low byte.
pub fn str_key7(s: &[u8]) -> u64 {
    if s.is_empty() || s.len() > 7 { return 0 }
    s.iter().enumerate().fold(s.len() as u64, |k, (i, &b)| k | (b as u64) << (8 * (i + 1)))
}

fn xorshift32(mut s: u32) -> u32 { s ^= s << 13; s ^= s >> 17; s ^ (s << 5) }

/// `drawGuids`: fills `out` (a multiple of 8 bytes) with words of `xorshift` (low half drawn first, the high half from
/// it), each written most significant byte first, and answers the seed after them. One dependence chain, so serial.
pub fn draw_guids(mut seed: u32, out: &mut [u8]) -> u32 {
    for w in out.chunks_exact_mut(8) {
        let lo = xorshift32(seed);
        let hi = xorshift32(lo);
        seed = hi;
        w.copy_from_slice(&(((hi as u64) << 32) | lo as u64).to_be_bytes());
    }
    seed
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn key7_packs() {
        assert_eq!(str_key7(b""), 0);
        assert_eq!(str_key7(b"12345678"), 0);
        assert_eq!(str_key7(b"+:"), 2 | (b'+' as u64) << 8 | (b':' as u64) << 16);
        assert_ne!(str_key7(b"a"), str_key7(b"a\0"));
    }
    #[test] fn guids_chain() {
        let mut o = [0u8; 16];
        let s = draw_guids(1, &mut o);
        let lo = xorshift32(1);
        let hi = xorshift32(lo);
        assert_eq!(&o[..8], &(((hi as u64) << 32) | lo as u64).to_be_bytes());
        let mut o2 = [0u8; 8];
        assert_eq!(draw_guids(1, &mut o2), hi);
        assert_eq!(o2, o[..8]);
        assert_ne!(s, 1);
    }
}
