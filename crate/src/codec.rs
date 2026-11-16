#![forbid(unsafe_code)]
#![allow(unused_variables)] // scaffold: the task that fills this module removes it
//! Column (a), coc.c: the threaded passes behind the `qlean_coc_*` entries (A15) and the `qlean_alp_*` ones (A18).
//! The entries themselves unbox and allocate, and stay C (§1); each calls the pass here through its `qrs_*` shim.
use crate::alp::{dec, Cocf};
use crate::c::{run_map, Runner};
use crate::coc::Coc;
use crate::pod::{self, Lane};
use crate::{BLK, QLEAN_COST_ARITH, QLEAN_COST_GATHER};

// ---- A15: coc.c:592-837 ----
/// coc.c:592-594 `qlean_coc_decode_{i16,i32,i64}` past the unboxing: the whole column into `out`, by blocks.
pub fn decode<T: Lane + Send>(run: Runner, c: &Coc, out: &mut [T]) { unimplemented!("A15: coc_decode_run") }
/// coc.c:616 `qlean_coc_block_start`: each block's first element into `out` (`nblk` long).
pub fn block_start(c: &Coc, out: &mut [i64]) { unimplemented!("A15: qlean_coc_block_start") }
/// coc.c:761 `coc_mask_cmp_run` and its entry: `x op v` as a bitmap into `out` (`(n + 7) / 8` bytes).
pub fn mask_cmp(run: Runner, op: u8, v: i64, c: &Coc, out: &mut [u8]) { unimplemented!("A15: coc_mask_cmp_run") }
/// coc.c:766 `coc_cmp2_run`: `a op b` as a bitmap, blocks threaded over `coc_cmp2_res`.
pub fn cmp2(run: Runner, op: i32, a: &Coc, b: &Coc, deep: &[u32], out: &mut [u64]) { unimplemented!("A15: coc_cmp2_run") }
/// coc.c:810 `shift_fill`: the encoder's source for `qlean_coc_shift` when the metadata cannot absorb `k`:
/// elements `i0 .. i0 + buf.len()` of `x + k` (`neg`: `k - x`), nulls `fill`.
pub fn shift_fill(c: &Coc, k: i64, neg: bool, fill: i64, buf: &mut [i64], i0: usize) { unimplemented!("A15: shift_fill") }

// ---- A18: coc.c:1015-1149 ----
/// Blocks `b0 .. b1` into `o`, block `b` at `o[(b - b0) * BLK * esz ..]` (`o` may end inside the last block).
fn load_blocks(f: &Cocf, b0: usize, b1: usize, o: &mut [u8]) {
    let (n, esz) = (f.c.meta.n, if f.f32 { 4 } else { 8 });
    for b in b0..b1 {
        let nb = (n - b * BLK).min(BLK);
        f.load_blk(b, nb, &mut o[(b - b0) * BLK * esz..][..nb * esz])
    }
}
/// coc.c:1015 `alp_decode_run` and its entries: the whole ALP column into `out` (`f32`/`f64` bytes), by blocks.
pub fn alp_decode(run: Runner, f: &Cocf, out: &mut [u8]) {
    let unit = BLK * if f.f32 { 4 } else { 8 };
    run_map(run, out, f.c.meta.nblk, unit, QLEAN_COST_ARITH, unit, &|lo, hi, o: &mut [u8]| load_blocks(f, lo, hi, o));
}
/// coc.c:1051 `alp_chunk_run`: blocks `b0 .. b1` of an `f64` column into `buf` (`(b1 - b0) * BLK` doubles), the
/// chunk `qlean_alp_sum_f64` hands its serial lane chain. The chain itself is reduce.c's, which `at` feeds.
pub fn alp_chunk(run: Runner, f: &Cocf, b0: usize, b1: usize, buf: &mut [u8]) {
    let unit = BLK * 8;
    run_map(run, buf, b1 - b0, unit, QLEAN_COST_ARITH, unit, &|lo, hi, o: &mut [u8]| load_blocks(f, b0 + lo, b0 + hi, o));
}
/// coc.c:1103 `alp_gather_run` and its entry: `f[idx[i]]` into `out`, `fill`'s bits where `idx[i]` is out of range.
pub fn alp_gather(run: Runner, fill: u64, f: &Cocf, idx: &[i64], out: &mut [u8]) {
    let (sn, esz, shape) = (f.c.meta.n, if f.f32 { 4 } else { 8 }, f.c.one_width());
    run_map(run, out, idx.len(), esz, QLEAN_COST_GATHER, esz + 8, &|lo, hi, o: &mut [u8]| {
        let mut buf = [0u64; BLK];
        let bb = pod::bytes_mut(&mut buf);
        // `c/structural.c`'s GATHER_RUNS rule: a run of BLK / 8 indices in one block restores the block once,
        // fewer are read one at a time
        let (mut rb, mut re) = (usize::MAX, 0);
        for j in lo..hi {
            let (u, at) = (idx[j] as u64, (j - lo) * esz);
            if u >= sn as u64 { o[at..at + esz].copy_from_slice(&fill.to_ne_bytes()[..esz]); continue }
            let (u, b) = (u as usize, u as usize / BLK);
            if j >= re {
                re = j + 1;
                while re < hi && idx[re] as u64 / BLK as u64 == b as u64 { re += 1 }
                if re - j >= BLK / 8 { rb = b; f.load_blk(b, (sn - b * BLK).min(BLK), bb) } else { rb = usize::MAX }
            }
            if rb == b { o[at..at + esz].copy_from_slice(&bb[(u - b * BLK) * esz..][..esz]); continue }
            if j + 16 < hi { f.c.prefetch(idx[j + 16] as usize) }
            let k = (u % BLK) as u16;
            let (l, h) = (f.exc_off[b] as usize, f.exc_off[b + 1] as usize);
            let l = l + f.exc_pos[l..h].partition_point(|&p| p < k);
            if l < h && f.exc_pos[l] == k { o[at..at + esz].copy_from_slice(&f.exc_raw[l * esz..(l + 1) * esz]); continue }
            let v = dec(f.c.get_w(shape, u), f.exp[b] as i32);
            if f.f32 { o[at..at + 4].copy_from_slice(&(v as f32).to_ne_bytes()) } else { o[at..at + 8].copy_from_slice(&v.to_ne_bytes()) }
        }
    });
}
