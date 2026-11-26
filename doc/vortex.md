# Vortex as relk's kernels: not adopted

Decision (owner, 2026-11-18): relk keeps its own kernels and file format; PLAN 6 continues. Vortex 0.93.0
(c1de7e80d7df) was read, not linked.

| Question                         | Finding                                                                                         |
|----------------------------------|-------------------------------------------------------------------------------------------------|
| PLAN 6 primitives                | only `gather` has a counterpart (`take`, lazy, no bounds check); no scan, scatter, sort, distinct |
| relk's 77 exports                | direct 0, adapter 27, keep ours 50                                                              |
| `foR`                            | no byte-exact counterpart; FoR+BitPacked fix 1024-element blocks and fall back to canonical      |
| Load = mmap                      | data buffers mmap zero-copy, but every array is decoded into an `ArrayRef` tree from a flatbuffer |
| Toolchain, deps                  | MSRV 1.95 (relk 1.93.1), no `no_std`, arrow and async in the workspace                           |
| FastLanes layout (spike, below)  | take 0.8–1.5×, compare 1.4–4.6× (median ≈ 2.4×) of relk's AVX-512 coc kernels on the same payload |
| Code size                        | `fastlanes` adds 682 KB `.text`; relk is 115 KB                                                  |

The spike (`/data/tmp/vortex-spike.md`, bench in `/data/tmp/fl-spike/`) compared `fastlanes` 0.8.1 with relk on
u64 columns of 1M and 64M rows at widths 1–32. `pack.rs`'s scalar per-element `res_at` is 40–100× slower than
either; that gap is the scalar loop, not the layout, and relk's existing AVX-512 codec closes most of it.

Follow-up (done): `pack.rs` no longer exists; `foR` is read through the AVX-512 coc/codec kernels instead of `res_at`; compare-to-constant is
the one op where FastLanes' lane order may pay, so it is re-measured after that change before any layout is copied.

## Re-measure on 0164b91

relk 的 5 个 kernel（`qlean_k_scan/gather/scatter/asc/distinct`）在 master 0164b91 上对照 q 4.1 和 FastLanes 0.8.1
重测。`crate/` 在 0164b91 之后没有改动。原始数据在 `/data/tmp/relk-remeasure/`。

Setup:
- 代码：`/data/tmp/relk-remeasure/src/main.rs`（bench crate `rb`）、`qb.q`、`run.sh`、`join.awk`、`table.awk`。relk 用 path dep，
  `default-features = false, features = ["std"]`，作为 rlib 链接，未修改；Lean runtime 的 `lean_alloc_object` 等函数按
  `crate/rt/src/lib.rs` 的 malloc/free 定义在 bench 里。rustc 1.93.1，`-C target-cpu=native`，fat LTO，cgu 1。
- 入口：`qlean_k_*` 只有 Lean-object 签名，所以直接调用它们包装的 Rust 函数：`scan::kscan_rows`（+`kscan_pack`）、
  `gather::words`、`scatter::words`、`asc::order`/`ord_key`/`grade`、`distinct::words`。foR 的读写路径
  `exports::scan::for_words`、`exports::scatter::for_words_of`、`raw` 在 `std` build 里被 cfg 掉，所以把它们逐行抄进 bench：
  `ffi::Sink::new(n, 8, Form::For).enc().answer(&Blocks::dense(..))` 写，`coc::view` + `Coc::std` + `Blocks::load_w` +
  逐字节 `rd` 读。每个 kernel 的计时 = 读所有 foR 输入 + kernel + 用 `Sink` 写 foR 输出（与 Lean 调用的路径相同）。
- take / eq / lt 的 coc 路径：`structural::gather_enc`（`qlean_structural_gather_foR` 的内部函数）和 `codec::mask_cmp`。
  rel 现在的 `gather` 走 `qlean_k_gather`（先把整列 decode 再取下标），表里 "gather 1%" 就是这条路径；`Coc::get` 已不存在。
- CPU AMD Ryzen 9 9900X，`taskset -c 3`，`QLEAN_THREADS=1`，q 不带 `-s`：全部单线程。每个 cell 一个进程，套在
  `CAP_MEM_MB=20000 cap` 里（它以 99 Hz 采样 perf，开销 <1%）。并发 session 让 load 在 5–10 之间；
  `run.sh` 在 1 分钟 load ≥ 6 时等待，但 1M 的 asc 仍有噪声（两次运行 px asc 21.7 / 58.1 ms）。
- 计时：relk/FastLanes 先 warm-up 一次，再跑 3 次取 median。q 先用 `\ts:k` 把 k 加倍到一个 batch ≥ 50 ms，再跑 3 个
  batch，取 median 除以 k（note.md §1 用的是 minimum；这里用 median，和 relk 一致）。
- 数据（同一份文件给 relk 和 q，q 用 `(1#"j";1#8)1:` 读入）：`ts` = `x-min x` of `sums 1+n?2000`；`px` = `x-min x` of
  `sums -5+n?11`；`sz` = `1+n?100`；`xl` = `(xl*xl) mod p`，其中 `xl = (2654435761*til N) mod p`，`p = 1000000007`
  （bench-roofline.txt 的 setup）；`xn` = `xl%1000000007`，即 q 的 float 除法，按 f64 的 bit pattern 存成 u64（`%` 在 q
  里是除法，不是 mod；PLAN §6.0 的 incompressible control 就是这个）；`so` = `sz`，但 `i mod 1024 = 517` 的元素换成 `2^62`。
  行数 1M = 1048576，100M = 100000768（= 97657 × 1024，FastLanes 需要整块）。gather 1% = n/100 个均匀随机下标；
  perm = Fisher–Yates 全排列；c = `x[n div 2]`；seg sums 的段在 `i mod 1000 = 0` 处开始；`asc (x,sz)` 按 (x, sz) 字典序。
- encoded/dense（relk foR，meta+pack）：ts 0.318，px 0.125，sz 0.113，so 0.973，xl 0.473，xn 0.879。FastLanes payload +
  9 B/块，小 0.3%。
- RSS：每个 cell 写 `/proc/self/clear_refs` = 5 后，取 `VmHWM` 减去开始时的 `VmRSS`（warm-up + 3 次运行中多出的峰值），
  单位 MiB，只给 100M。q 的 `\ts` 空间在 `q*.tsv` 第 6 列。
- bytes r/w：由编码大小算出，没有用 perf 计数器：r = foR 输入的 meta+pack（下标列也是 foR），w = `Sink` 写出的 foR
  （x<c 是 bitmap）。每个 kernel 中间还会 decode 成 8n 字节的 `Vec<u64>` 再编码，这部分没有计入。
- 正确性：每个 relk 和 FastLanes 结果都等于 dense Rust 参考实现（全部相等）；每个可比较的 cell 都和 q 的 checksum 相等
  （按 mod 2^64 比较：1M 78/78，100M 65/65）。
- 100M 的 xn 没有跑完：Claude Code 在系统内存不足时（另一个 session 占用内存，可用约 6 GB）杀掉了 background run，
  所以没有重跑。xl asc 在 100M 的 read 是 4.6 s，其他列约 0.2 s，这是内存压力造成的。

Table（ms，median of 3；relk/q > 1 表示 relk 慢；RSS 和 r/w 是 100M 的值；1M 的 take 是 n/100 次取值的总时间）：

| col | op               | relk 1M | q 1M   | fl 1M  | r/q 1M | relk 100M | q 100M | fl 100M | r/q 100M | r/fl 100M | RSS MiB | r/w MB |
|-----|------------------|---------|--------|--------|--------|-----------|--------|---------|----------|-----------|---------|--------|
| ts  | sums (kscan add) |   3.872 |  0.312 |      - |  12.41 |      397 |    45.0 |      - |   8.81 |      - |   3599 | 270/574   |
| ts  | maxs (kscan max) |   3.903 |  0.844 |      - |   4.62 |      405 |    75.0 |      - |   5.40 |      - |   3294 | 270/254   |
| ts  | x<c (kscan map)  |   3.763 |  0.006 |      - | 627.17 |      338 |   2.375 |      - | 142.30 |      - |   3063 | 270/13    |
| ts  | seg sums /1000   |   3.885 |  1.625 |      - |   2.39 |      579 |     168 |      - |   3.45 |      - |   3598 | 270/573   |
| ts  | gather 1%        |   0.409 |  0.004 |      - | 102.25 |      110 |   3.562 |      - |  30.75 |      - |    791 | 258/5     |
| ts  | gather perm      |   5.269 |  0.562 |      - |   9.38 |     2581 |     399 |      - |   6.47 |      - |   3496 | 595/466   |
| ts  | scatter perm     |   3.210 |  1.281 |      - |   2.51 |     1213 |     389 |      - |   3.12 |      - |   3496 | 595/466   |
| ts  | asc (x, perm)    |    25.8 |  0.562 |      - |  45.95 |    17778 |     106 |      - | 167.71 |      - |   4820 | 254/383   |
| ts  | asc (x,sz)       |    44.4 |   32.2 |      - |   1.38 |    24373 |    2691 |      - |   9.06 |      - |   7109 | 345/473   |
| ts  | distinct(asc x)  |   1.257 |  0.727 |      - |   1.73 |      261 |     120 |      - |   2.17 |      - |   1649 | 254/128   |
| ts  | take 1% (coc)    |   0.045 |  0.007 |  0.034 |   6.43 |     12.9 |   3.688 |   15.9 |   3.49 |   0.81 |      8 | 262/8     |
| ts  | x=c (coc)        |   0.002 |  0.119 |  0.001 |   0.02 |    0.259 |    20.5 |  0.182 |   0.01 |   1.42 |     12 | 254/13    |
| ts  | x<c (coc)        |   0.003 |  0.008 |  0.001 |   0.38 |    0.335 |   2.406 |  0.189 |   0.14 |   1.77 |     12 | 254/13    |
| px  | sums (kscan add) |   5.591 |  0.602 |      - |   9.29 |      386 |    59.0 |      - |   6.54 |      - |   3361 | 116/324   |
| px  | maxs (kscan max) |   5.047 |  0.953 |      - |   5.30 |      369 |    90.0 |      - |   4.10 |      - |   3056 | 116/4     |
| px  | x<c (kscan map)  |   4.240 |  0.104 |      - |  40.77 |      326 |    19.5 |      - |  16.70 |      - |   3063 | 116/13    |
| px  | seg sums /1000   |   5.248 |  1.438 |      - |   3.65 |      413 |     145 |      - |   2.85 |      - |   3361 | 116/324   |
| px  | gather 1%        |   0.473 |  0.004 |      - | 118.25 |     82.5 |   3.188 |      - |  25.89 |      - |    788 | 104/2     |
| px  | gather perm      |   9.079 |  0.703 |      - |  12.91 |     1872 |     328 |      - |   5.71 |      - |   3258 | 441/216   |
| px  | scatter perm     |   6.922 |  1.422 |      - |   4.87 |      749 |     380 |      - |   1.97 |      - |   3258 | 441/216   |
| px  | asc (x, perm)    |    58.1 |  6.312 |      - |   9.21 |     7658 |     454 |      - |  16.87 |      - |   4874 | 100/313   |
| px  | asc (x,sz)       |    62.3 |   24.2 |      - |   2.57 |    18823 |    1379 |      - |  13.65 |      - |   7174 | 191/407   |
| px  | distinct(asc x)  |   0.780 |  0.332 |      - |   2.35 |     90.3 |    79.0 |      - |   1.14 |      - |    764 | 11/0      |
| px  | take 1% (coc)    |   0.074 |  0.004 |  0.056 |  18.50 |     12.3 |   3.188 |   14.0 |   3.85 |   0.88 |      8 | 108/8     |
| px  | x=c (coc)        |   0.005 |  0.104 |  0.003 |   0.05 |    0.391 |    19.5 |  0.245 |   0.02 |   1.60 |     12 | 100/13    |
| px  | x<c (coc)        |   0.006 |  0.102 |  0.003 |   0.06 |    0.517 |    19.5 |  0.244 |   0.03 |   2.12 |     12 | 100/13    |
| sz  | sums (kscan add) |   3.411 |  0.387 |      - |   8.81 |      368 |    68.0 |      - |   5.41 |      - |   3246 | 106/203   |
| sz  | maxs (kscan max) |   3.431 |  0.859 |      - |   3.99 |      361 |    96.0 |      - |   3.76 |      - |   3055 | 106/3     |
| sz  | x<c (kscan map)  |   3.871 |  0.098 |      - |  39.50 |      329 |    21.2 |      - |  15.47 |      - |   3062 | 106/13    |
| sz  | seg sums /1000   |   3.358 |  0.984 |      - |   3.41 |      374 |     159 |      - |   2.35 |      - |   3246 | 106/203   |
| sz  | gather 1%        |   0.417 |  0.004 |      - | 104.25 |     79.9 |   3.562 |      - |  22.42 |      - |    787 | 94/1      |
| sz  | gather perm      |   6.204 |  0.672 |      - |   9.23 |     1421 |     408 |      - |   3.48 |      - |   3140 | 431/91    |
| sz  | scatter perm     |   4.670 |  1.422 |      - |   3.28 |      837 |     578 |      - |   1.45 |      - |   3138 | 431/91    |
| sz  | asc (x, perm)    |    14.7 |  2.594 |      - |   5.68 |     4113 |     670 |      - |   6.14 |      - |   4784 | 91/219    |
| sz  | asc (x,sz)       |    33.9 |  9.375 |      - |   3.62 |    15025 |    1376 |      - |  10.92 |      - |   5546 | 181/222   |
| sz  | distinct(asc x)  |   0.538 |  0.355 |      - |   1.52 |     88.5 |    86.0 |      - |   1.03 |      - |    763 | 3/0       |
| sz  | take 1% (coc)    |   0.020 |  0.004 |  0.021 |   5.00 |     10.6 |   6.000 |   17.2 |   1.77 |   0.61 |      8 | 99/8      |
| sz  | x=c (coc)        |   0.115 |  0.158 |  0.048 |   0.73 |     12.6 |    20.8 |  5.654 |   0.61 |   2.23 |     12 | 91/13     |
| sz  | x<c (coc)        |   0.119 |  0.168 |  0.049 |   0.71 |     15.0 |    22.2 |  6.096 |   0.67 |   2.45 |     12 | 91/13     |
| so  | sums (kscan add) |   7.267 |  0.703 |      - |  10.34 |      431 |    60.0 |      - |   7.18 |      - |   3809 | 794/794   |
| so  | maxs (kscan max) |   6.265 |  1.016 |      - |   6.17 |      493 |    90.0 |      - |   5.47 |      - |   3055 | 794/3     |
| so  | x<c (kscan map)  |   7.036 |  0.164 |      - |  42.90 |      424 |    21.2 |      - |  19.95 |      - |   3062 | 794/13    |
| so  | seg sums /1000   |   8.028 |  2.656 |      - |   3.02 |      614 |     164 |      - |   3.74 |      - |   3806 | 794/791   |
| so  | gather 1%        |   1.094 |  0.008 |      - | 136.75 |      146 |   3.625 |      - |  40.28 |      - |    791 | 782/5     |
| so  | gather perm      |    12.4 |  1.359 |      - |   9.13 |     2092 |     385 |      - |   5.43 |      - |   3552 | 1119/524  |
| so  | scatter perm     |   8.765 |  1.625 |      - |   5.39 |     1134 |     494 |      - |   2.29 |      - |   3553 | 1119/526  |
| so  | asc (x, perm)    |    34.0 |   88.0 |      - |   0.39 |    11846 |    9814 |      - |   1.21 |      - |   4784 | 778/219   |
| so  | asc (x,sz)       |    68.8 |   51.0 |      - |   1.35 |    17345 |    4173 |      - |   4.16 |      - |   7073 | 869/222   |
| so  | distinct(asc x)  |   0.818 |  0.516 |      - |   1.59 |      103 |    92.0 |      - |   1.12 |      - |    763 | 3/0       |
| so  | take 1% (coc)    |   0.079 |  0.008 |  0.048 |   9.88 |     14.1 |   3.938 |   23.0 |   3.58 |   0.61 |      8 | 786/8     |
| so  | x=c (coc)        |   0.602 |  0.162 |  0.122 |   3.72 |     67.7 |    23.5 |   41.0 |   2.88 |   1.65 |     12 | 778/13    |
| so  | x<c (coc)        |   1.257 |  0.168 |  0.121 |   7.48 |     73.3 |    23.8 |   40.8 |   3.09 |   1.80 |     12 | 778/13    |
| xl  | sums (kscan add) |   3.867 |  0.391 |      - |   9.89 |      450 |    57.0 |      - |   7.89 |      - |   3520 | 394/491   |
| xl  | maxs (kscan max) |   3.632 |  0.859 |      - |   4.23 |      432 |    89.0 |      - |   4.85 |      - |   3055 | 394/3     |
| xl  | x<c (kscan map)  |   3.779 |  0.098 |      - |  38.56 |      396 |    19.5 |      - |  20.29 |      - |   3063 | 394/13    |
| xl  | seg sums /1000   |   3.877 |  1.000 |      - |   3.88 |      468 |     149 |      - |   3.14 |      - |   3520 | 394/491   |
| xl  | gather 1%        |   0.409 |  0.007 |      - |  58.43 |      101 |   3.312 |      - |  30.57 |      - |    790 | 382/4     |
| xl  | gather perm      |   5.703 |  0.750 |      - |   7.60 |     1845 |     332 |      - |   5.56 |      - |   3414 | 719/378   |
| xl  | scatter perm     |   4.197 |  0.969 |      - |   4.33 |     1061 |     379 |      - |   2.80 |      - |   3412 | 719/378   |
| xl  | asc (x, perm)    |    31.8 |   21.0 |      - |   1.52 |    36027 |    3437 |      - |  10.48 |      - |   4083 | 378/519   |
| xl  | asc (x,sz)       |    51.8 |   26.5 |      - |   1.95 |    29143 |    4527 |      - |   6.44 |      - |   7191 | 469/610   |
| xl  | distinct(asc x)  |   1.282 |  0.539 |      - |   2.38 |      263 |     112 |      - |   2.35 |      - |   1650 | 178/128   |
| xl  | take 1% (coc)    |   0.020 |  0.004 |  0.029 |   5.00 |    8.303 |   3.250 |   16.3 |   2.55 |   0.51 |      8 | 386/8     |
| xl  | x=c (coc)        |   0.257 |  0.098 |  0.052 |   2.62 |     28.5 |    19.5 |  8.676 |   1.46 |   3.28 |     12 | 378/13    |
| xl  | x<c (coc)        |   0.261 |  0.098 |  0.052 |   2.66 |     28.8 |    19.5 |   11.1 |   1.48 |   2.60 |     12 | 378/13    |
| xn  | sums (kscan add) |   3.270 |  0.387 |      - |   8.45 |      405 |       - |      - |      - |      - |   3818 | 719/803   |
| xn  | maxs (kscan max) |   3.805 |  0.859 |      - |   4.43 |      381 |       - |      - |      - |      - |   3055 | 719/3     |
| xn  | x<c (kscan map)  |   3.837 |  0.098 |      - |  39.15 |      343 |       - |      - |      - |      - |   3063 | 719/13    |
| xn  | seg sums /1000   |   4.068 |  0.969 |      - |   4.20 |      414 |       - |      - |      - |      - |   3818 | 719/803   |
| xn  | gather 1%        |   0.441 |  0.004 |      - | 110.25 |     96.1 |       - |      - |      - |      - |    793 | 707/7     |
| xn  | gather perm      |   5.952 |  0.523 |      - |  11.38 |     1363 |       - |      - |      - |      - |   3723 | 1044/703  |
| xn  | scatter perm     |   4.204 |  0.969 |      - |   4.34 |      773 |       - |      - |      - |      - |   3722 | 1044/703  |
| xn  | asc (x, perm)    |    55.0 |   67.0 |      - |   0.82 |    40190 |       - |      - |      - |      - |   5034 | 703/819   |
| xn  | asc (x,sz)       |    75.6 |   73.0 |      - |   1.04 |        - |       - |      - |      - |      - |      - | -         |
| xn  | distinct(asc x)  |   1.294 |  0.539 |      - |   2.40 |        - |       - |      - |      - |      - |      - | -         |
| xn  | take 1% (coc)    |   0.044 |  0.004 |  0.027 |  11.00 |        - |       - |      - |      - |      - |      - | -         |
| xn  | x=c (coc)        |   0.551 |  0.098 |  0.072 |   5.62 |        - |       - |      - |      - |      - |      - | -         |
| xn  | x<c (coc)        |   0.559 |  0.098 |  0.076 |   5.70 |        - |       - |      - |      - |      - |      - | -         |

Where we win:
- coc `x=c` / `x<c` 在 ts、px 上：100M ts 0.26 ms 对 q 20.5（79×），px 0.39 对 19.5（50×）——`codec::cmp_meta` 用块的
  base/max 就能定下几乎所有块。sz 也赢（0.61–0.67×）。
- coc take 1% 在 100M 上比 FastLanes 快（0.51–0.88×）；1M 时 0.69–1.65×，有输有赢。
- q 的 `iasc` 在宽值域上慢：1M so asc 0.39×，xn asc 0.82×。distinct 在 100M 的 px/sz/so 上与 q 持平（1.03–1.14×）。

Where we lose, and why（`perf record -g -e cycles:u` 单独跑该 cell，`RB_REPS` 次重复，数据在 `perf/*.data`）：
- kscan（sums/maxs/seg sums 2.4–12×，map `x<c` 16–630×）：三段各占约 1/3（100M ts sums：read 173、kern 101、
  write 121 ms，q 总共 45）。`rb::for_words_of` 19%（抄自 `raw`：每个 u64 由 8 次字节 `fold` 拼出）、`res_unpack_add`
  12%、`main::{{closure}}` 40%（内联的 `kscan_rows`：每行一次 `op_eval` 的 `match` 加 `Result`）、`simd::v::pack64` 7%。
  map 是用 kscan 写的（每行都是段起点），所以整列要 decode 两遍（x 和常数 seed）；q 的 `x<c` 是一次 SIMD 扫描。
- gather 1%（100M 22–40×，1M 58–137×）：`qlean_k_gather` 先把整列 decode，再取 1% 的下标。`for_words_of` 62%，
  `res_unpack_add` 30%。
- gather perm（3.5–6.5×）：`GenericShunt::next` 62%，即 `gather::words` 里 `collect::<Result<Vec<_>>>` 的随机读
  加逐行的越界判断。scatter perm（1.5–3.1×）：内联的 `scatter::words` 54%（随机写），其余是 decode/encode。
- asc（100M 4–168×，只有 so 是 1.21×；ts 168× 是因为 q 对已排好序的 ts 做 `iasc` 很快）：内联的 `asc::grade` 93%，热点指令是 `movzbl`，
  即每一趟里 `d(i)` 通过排列 `p` 随机读 `k[i]` 后取一个字节。8 趟 LSD 每趟都随机访问整列，两个 key 列是 16 趟。
- coc `x=c`/`x<c` 对 FastLanes（1.4–10×，xl/so/xn 对 q 也输 1.5–7.5×）：`relk::c::slice` 87%（内联的
  `codec::mask_res`）。热点是 `kmovb %k0` 和 `or %rsi,(%rbp,%rax,8)`：每个 AVX-512 compare 只得到 8 位 mask，再逐 8 个
  元素 OR 进 bitmap 字；FastLanes 的 `unpack_cmp` 一次比较 1024 个转置 lane，写 16 个字。
- coc take 1% 对 q（100M 1.8–3.9×）：`structural::enc` 24%、`res::res_get_in` 15%、`Coc::get` 12%，每个元素都要做块查找
  和位提取；q 是直接按下标读 dense 列。

Outlier row（so）：在 master 上，每块一个 `2^62` 会让整块按 63 位打包（`Coc.encode` 没有 patch/frame），所以 encoded/dense
是 0.973，而 sz 是 0.113，so 的 coc 比较也比 sz 慢 5×。restore patches/frames 的分支（`Coc.planOf = enc::for_blk`）合并后，
so 这一行会改变：异常值会进 patch list，块宽回到 sz 的 7 位。
