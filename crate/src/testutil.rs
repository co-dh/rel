//! Test-only builders shared by the unit tests of more than one module (one copy each): the per-id writers the tests use
//! to make `ids` input, which the kernels themselves never need (they read ids and write through `ids::pack`'s peers).
use crate::by_width;

/// `v` stored as element `i` of `p` at the lane width `W`: `ids::lane`'s inverse; a narrow field is a read-modify-write of
/// its shared byte.
pub fn lane_put<const W: u32>(p: &mut [u8], i: usize, v: u64) {
    match W {
        0 => {}
        1 | 2 | 4 => {
            let (b, s, m) = (i * W as usize >> 3, (i * W as usize & 7) as u32, ((1u16 << W) - 1) as u8);
            p[b] = p[b] & !(m << s) | ((v as u8 & m) << s);
        }
        _ => { let k = W as usize / 8; p[i * k..i * k + k].copy_from_slice(&v.to_le_bytes()[..k]) }
    }
}

/// id `v` at index `i`, `w` bits each.
pub fn id_put(p: &mut [u8], w: u32, i: usize, v: u64) { by_width!(w, lane_put(p, i, v)) }
