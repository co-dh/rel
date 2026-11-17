//! scan.rs's twelve Lean exports: the running scans, `avg`, `ema` and the moving-window family over a payload or an encoded
//! column, each an answer sized by `crate::scan` and filled by it.
#![deny(unsafe_code)]
use crate::key::SK_KINDS_N;
use crate::lean::{B, O, SArr, export};
use crate::{os, scan};

/// The text of a refused argument on stderr, then exit 1, as C's `fprintf(stderr, …); exit(1)` did.
fn die(args: core::fmt::Arguments) -> ! {
    os::eprint(args).expect("qlean: stderr");
    os::exit(1)
}
/// A fresh answer of `n` bytes, filled by `fill`.
fn answer(n: usize, fill: impl FnOnce(&mut [u8])) -> O {
    let mut o = SArr::new(1, n);
    fill(o.bytes_mut());
    o.into()
}

export! {
    /// `Scan.anyNull kind n a`: whether one of the payload's first `n` elements is the kind's null. `Kernel.scanColumn` asks
    /// it before `fills`, so that the identity is seen as the argument and not handed to `Column.answer` as a written payload.
    fn qlean_scan_any_null(kind: u8, n: usize, a: B) -> u8 { scan::col_any_null(kind, n, a.bytes()) as u8 }

    /// The ByteArray of `n` elements at `sc_out_width` whose ith element is the accumulator after element i of the fold of
    /// `Verb` (QLean/Kernel/Scan.lean). Where that fold is the identity the answer is the argument object, refcounted.
    fn qlean_scan(op: u8, kind: u8, n: usize, a: B) -> O {
        let p = a.bytes();
        if scan::col_same(op, kind, n, p) { return a.to_owned() }
        answer(scan::col_len(op, kind, n, p.len()), |o| scan::col(op, kind, n, p, o))
    }

    /// `scanBits op n a` is `Column.packBits (scan op SK_BIT n a)`: the fold at the bit layout, packed one bit an element.
    fn qlean_scan_bits(op: u8, n: usize, a: B) -> O {
        let p = a.bytes();
        let Some(nb) = scan::bits_len(op, n, p.len()) else {
            die(format_args!("qlean_scan_bits: verb {op} does not answer at the bit layout; only the three `outKind` leaves there do -- see QLean/Kernel/Scan.lean\n"))
        };
        answer(nb, |o| scan::col_bits(op, n, p, o))
    }

    /// `scanFoR op kind n metadata pack` is `scan op kind n (Coc.decode 8 metadata pack n)`, read a block at a time.
    fn qlean_scan_foR(op: u8, kind: u8, n: usize, mv: B, pv: B) -> O {
        let (m, p) = (mv.bytes(), pv.bytes());
        answer(scan::for_len(op, kind, m, n), |o| scan::col_for(op, kind, n, m, p, o))
    }

    /// `scanAlp op kind n metadata pack alp` is `scan op kind n (Coc.alpDecode metadata pack alp n)`, read a block at a time.
    fn qlean_scan_alp(op: u8, kind: u8, n: usize, mv: B, pv: B, av: B) -> O {
        let (m, p, x) = (mv.bytes(), pv.bytes(), av.bytes());
        answer(scan::alp_len(op, kind, m, n), |o| scan::col_alp(op, kind, n, m, p, x, o))
    }

    /// q's `avg` as the bits of the `Float` it answers: `0n` for no live element, else the total over the count.
    fn qlean_scan_avg(kind: u8, n: usize, a: B) -> u64 {
        match scan::col_avg(kind, n, a.bytes()) {
            Some(bits) => bits,
            None => die(format_args!("qlean_scan_avg: element kind {kind} is not one of the {SK_KINDS_N} in QLean/Kernel/Scan.lean\n")),
        }
    }

    /// `emaBits a b`: `out[0] = b[0]`, `out[i] = (1-a)*out[i-1] + a*b[i]`, read and written as little-endian doubles.
    fn qlean_scan_ema(abits: u64, bv: B) -> O {
        let y = bv.bytes();
        let n = scan::ema_n(y.len());
        answer(8 * n, |o| scan::ema(abits, &y[..8 * n], o))
    }

    /// `emaVecBits xy co seed`: `out[i] = co[i]*out[i-1] + xy[i]`, seeded at `out[-1] = seed`.
    fn qlean_scan_ema_v(xyv: B, cov: B, seedbits: u64) -> O {
        let (xy, co) = (xyv.bytes(), cov.bytes());
        let n = scan::ema_n(xy.len());
        answer(8 * n, |o| scan::ema_v(&xy[..8 * n], &co[..8 * n], seedbits, o))
    }

    /// `mwinBits`: the moving-window verb of window `w` over `n` elements of a dense payload.
    fn qlean_mwin(op: u8, kind: u8, w: usize, n: usize, a: B) -> O {
        let p = a.bytes();
        answer(scan::mwin_len(op, kind, n, p.len()), |o| scan::mwin(op, kind, w, n, p, o))
    }

    /// `mwinBitmap op w n a` is `qlean_mwin op SK_BIT w n a` packed one bit an element; only the two extremes arrive.
    fn qlean_mwin_bits(op: u8, w: usize, n: usize, a: B) -> O {
        let p = a.bytes();
        let Some(nb) = scan::mwin_bits_len(op, n, p.len()) else {
            die(format_args!("qlean_mwin_bits: verb {op} does not answer a boolean; only mmin and mmax do -- see QLean/Kernel/Scan.lean\n"))
        };
        answer(nb, |o| scan::mwin_bits(op, w, n, p, o))
    }

    /// `mwinFoR op kind w n metadata pack` is `mwin op kind w n (Coc.decode 8 metadata pack n)`, read a block at a time.
    fn qlean_mwin_foR(op: u8, kind: u8, w: usize, n: usize, mv: B, pv: B) -> O {
        let (m, p) = (mv.bytes(), pv.bytes());
        answer(scan::mwin_for_len(op, kind, m, n), |o| scan::mwin_for(op, kind, w, n, m, p, o))
    }

    /// `mwin op kind w n (Coc.alpDecode metadata pack alp n)`, read a block at a time.
    fn qlean_mwin_alp(op: u8, kind: u8, w: usize, n: usize, mv: B, pv: B, av: B) -> O {
        let (m, p, x) = (mv.bytes(), pv.bytes(), av.bytes());
        answer(scan::mwin_alp_len(op, kind, m, n), |o| scan::mwin_alp(op, kind, w, n, m, p, x, o))
    }
}
