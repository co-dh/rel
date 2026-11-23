// palette: one colour per layer, as doc/rel-architecture.zh.typ
#let c-syn = rgb("#2f5d9e")
#let c-sem = rgb("#7a3e9d")
#let c-run = rgb("#2e7d4f")
#let c-rs  = rgb("#b5541c")
#let ink   = rgb("#222831")

#set document(title: "null = 残差 0")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); null = 残差 0 #h(1fr) master 199e935 · 2026-11-23 ],
  footer: context align(center, text(8pt, fill: gray)[#counter(page).display()]))
#set text(font: ("Libertinus Serif", "Noto Serif CJK SC", "Noto Sans CJK SC"), size: 10pt, fill: ink, lang: "zh", region: "cn")
#set par(justify: false, leading: 0.75em)
#show raw: set text(font: ("JuliaMono", "Noto Sans CJK SC"), size: 8.6pt)
#show raw.where(block: false): it => box(fill: luma(240), inset: (x: 2.5pt), outset: (y: 2.5pt), radius: 2pt, it)
#show raw.where(block: true): it => block(width: 100%, fill: rgb("#f3f1ea"), inset: 9pt, radius: 4pt,
  stroke: (left: 2.5pt + c-run), it)
#set heading(numbering: "1.1")
#show heading: set text(font: ("Noto Sans CJK SC"), weight: "bold")
#show heading.where(level: 1): it => block(above: 1.4em, below: 0.8em)[
  #text(15pt, fill: c-syn, it) #v(-0.5em) #line(length: 100%, stroke: 0.8pt + c-syn.lighten(50%))]
#show heading.where(level: 2): set text(12pt, fill: c-sem)
#set list(marker: text(fill: c-syn)[▸])

#import "tbl.typ": tbl, soft
#let card(color, title, body) = block(width: 100%, fill: soft(color), stroke: (left: 3pt + color),
  inset: 9pt, radius: (right: 4pt))[#text(weight: "bold", fill: color, font: "Noto Sans CJK SC", title) \ #body]

#align(center)[
  #text(24pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[null = 残差 0] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[`1+atom` 带内 null 的重新设计：判 null 只与 0 比较，与宽度无关] \
  #v(2pt) #text(9pt, fill: gray)[master 199e935 · 2026-11-23 · 取代 `rel-architecture` §4.2 卡片"null 在带内"中的"顶残差"]
]
#v(6pt)

全文用同一块作例子，记号：块的 frame `f`、宽度 `w`、残差 `r`、值 `v = f + r`、行掩码 `m = [r ≠ 0]`（0 或 1）。

```
三行：100, null, 105
现状（顶残差）  base = 100, w = 6, 带标志   r = 000000  111111  000101      null = 2^6 − 1
新（残差 0）    base =  99, w = 6, 带标志   r = 000001  000000  000110      null = 0
```

= 现状（nullband-int a4843b7、nullband3h3 8b84e97）

- `1+t` 是一列 `Opt t n`。宽度字节第 7 位是块的 null 标志（`Column.nulAt`、Rust `NUL_FLAG`）。
- 带标志的块里残差 `2^w − 1` 是 null（`Column.foRNul`：标志 ∧ 无 patch ∧ 残差 `= ones w`）；写出端是 `Coc.nulBlock`。
- `kscan` 的 `Op.null` 读 `foRNuls`；逐行对齐的 scan 拒绝含 null 的输入（`noNul "kscan"`）；gather、scatter 把标志当第二列带着走。
- 缺点：null 码随 `w` 变。判 null 要先算每块的 `2^w − 1`（`w = 64` 另走一支）；加宽一块时 null 码要改写。

= 编码：null = 残差 0

#tbl(c-run, (auto, 1fr, 1fr), ([问题], [决定], [理由 / 例]),
  [null 码], [带标志的块里残差 `0` 是 null], [判 null 是 `r == 0`，不含 `w`],
  [frame], [`base` 字段存 `f = min − 1`（`min` 是非 null 值的最小者）；值的残差 `r = v − f ≥ 1`],
    [解码 `foRBits = base + frame + r` 一字不改，所有读值的地方（Lean 引理、Rust 的每个 `base + res`）不动。例：`min = 100` → `f = 99`，`105` 存 `000110`],
  [`min` 已是该类型最小 key], [`f = min`（不回绕）；该值残差为 0，与 null 撞码，进 patch 列表],
    [保持"`base ≤` 每个值"，按块跳过的谓词仍成立。就是现有的 `Coc.patched`（"值在 null 码上则 patch"）。例：`i8` 列含 `−128` 与 null：`f = −128`，`−128` 进 patch],
  [宽度], [`w = widthFor(max − f) = widthFor(range + 1)`],
    [与现状逐块相等：现状是 `widthFor(range)`，`range = 2^d − 1` 时加 1，正是 `widthFor(range + 1)`。例：值 `100..163`（range 63）现状 `6 → 7`；新 `r = 1..64`，也是 7。没有空间代价],
  [null 标志], [保留，仍是每块一位],
    [去掉标志则每块都要让出残差 0：无 null 的常量块不能再是 `w = 0`，同一段字节按 `Arr` 读和按 `Opt` 读得到不同的值。保留则字节自己说明含义],
  [无 null 的块], [不变：`f = min`、无标志、残差 0 是值 `min`], [现有列零代价；`Arr t n` 仍是"没有带标志的块"],
  [patch], [带标志的块只 patch 撞 null 码的值（同现状）；patch 的行不是 null], [判 null 仍是：标志 ∧ 无 patch ∧ `r == 0`。无 patch 的块（常态）只剩 `r == 0`],
  [`w = 0` 的块], [带标志：全 null（没有值）；不带标志：常量 `min`（不变）],
    [只有一个不同值加 null 的块是 `w = 1`：`1` 是值、`0` 是 null，就是一张"非 null"位图],
  [缓存], [`maxv` 是非 null 最大值，`bsum` 不计 null（不变）；`base` 现在是下界，带标志时比 `min` 小 1], [要精确 `min` 的读者没有；谓词跳块只用界],
)

- 附带得到的性质（顶残差没有）：
  - 清零的内存就是全 null 列（`tot(R)` 的 scatter 目标）。
  - 块内残差的无符号序就是和的次序 `inl < inr`（null 最前）。
  - 同 frame 加宽 `w → w'` 是零扩展，null 仍是 0。现状 `111111` 加宽到 8 位读成 `00111111` = 值 163，必须改写。

= 判 null

- 规则：行 `i` 是 null ⇔ 块带标志 ∧ 行不在 patch 列表 ∧ `r == 0`。例：`r = 000001 000000 000110` → `0 1 0`。
- Lean：只改 `Column.foRNul` 的最后一个合取项，`== ones (widthAt metadata b)` 变成 `== 0`。`foRNuls`、`foROpt`、`hasNul`、`Op.null`、
  `kscan` 的 seed 都经它读，文本不变。`foROpt_top` 改名 `foROpt_zero`。
- Rust：`Coc::is_nul` 是 `nul(b) && patch(b, j).is_none() && res(b, j) == 0`；`scan.rs` 的 `Col::nuls` 与"第一个 null 行"对带标志的块逐残差与 0 比，
  不再算 `top`，没有 `w ≥ 64` 分支；`Coc::nuls` 随 `is_nul`。

= 编码上的运算

== 语义（先定，再谈 kernel）

- 二元算术 `plus minus times div mod` 在 `1+V` 上是 `V` 上动词的 `1+(−)` 提升：任一操作数是 null，结果是 null。现在的 `noNul "kscan"` 对这些 `Op` 取消。
- 比较与二元 `max` `min` 不传播，按和的次序 `inl < inr`（架构已定：null 小于每个值）。`max(null, 5) = 5`，`min(null, 5) = null`。见文末待选 A–C。
- fold（分段 `scan` 的 `sums prds mins maxs fills`）跳过 null（现状 `scanOf … isNull`，q 的 `sum`），不传播。

== "0 × x = 0" 在哪里成立

#card(c-sem, [结论])[
  值是 `v = f + r`，不是 `r`。残差 0 的吸收性只在*不动 frame 的线性运算*里直接可用；两列相乘时 frame 不为 0，不成立。\
  - 成立：列乘正常数。`3 × (99 + r) = 297 + 3r`：新 `f' = 297`，`r' = 3r = 3, 0, 18` → 300, null, 315。null 自动保持。
  - 不成立一：两列相乘。另一列 `f₂ = 9`、`r₂ = 1, 3, 0`（10, 12, null）。`v₁v₂ = f₁f₂ + f₁r₂ + f₂r₁ + r₁r₂`；第 2 行 `r₁ = 0`，
    余下 `f₁r₂ = 297 ≠ 0`，不加掩码就读成一个值。只有 `f₁ = f₂ = 0` 时 `r' = r₁r₂`，才是"0 乘任何数得 0"。
  - 不成立二：乘常数 0。`0 × 105` 是*值* 0，不是 null；残差全乘成 0 会把三行都读成 null。正确结果是 `f' = −1`、`r' = m = 1, 0, 1`。
  - 加法：0 对加法是单位元，不是吸收元。`r₁ + r₂ = 2, 3, 6` 配 `f' = 108` 读成 110, 111, 114；后两行应为 null。必须乘掩码：`2, 0, 0`。
  真正的收益是掩码本身便宜：`m = [r ≠ 0]`，每块同一条比较，不含 `w`，无标志的块整条掩码路径不走。]

== 每个运算的块内规则

两列时下标 1、2；无标志的块 `m` 恒为 1（它的残差 0 是值）。写出端按结果的 `min` 重新收紧 frame，下表的 `f'` 只需是下界。
没有残差闭式的运算（`×`、`div`、`mod`）在寄存器里按行算 `f + r`，再乘掩码，不物化解码列。

#tbl(c-sem, (auto, auto, 1fr), ([运算], [null 是否自动], [块内规则 / 例]),
  [`x + c`、`x − c`（标量）], [自动], [`f' = f ± c`，残差不读不写。`+ 5`：`f' = 104`，`r` 不变],
  [`c · x`，`c > 0`], [自动], [`f' = c·f`，`r' = c·r`，`w' = w + bitwidth(c)`。溢出规则同现状（`stepCols`）],
  [`c · x`，`c ≤ 0`；取负], [掩码], [`c = 0`：`f' = −1`，`r' = m`。`c < 0`：`f' = c·(f + R) − 1`，`r' = m·(c·(r − R) + 1)`，`R = maxv − f`],
  [`x + y`], [掩码], [`f' = f₁ + f₂`，`r' = m₁m₂·(r₁ + r₂)`。例：`f' = 108`，`r' = 2, 0, 0` → 110, null, null],
  [`x − y`], [掩码], [`f' = f₁ − f₂ − R₂`，`r' = m₁m₂·(r₁ − r₂ + R₂)`，`R₂ = maxv₂ − f₂`（保证 `r' ≥ 1`）],
  [`x · y`], [掩码], [`r' = m₁m₂·((f₁ + r₁)(f₂ + r₂) − f')`。第 1 行：`100·10 − 891 = 109`],
  [`div`、`mod`], [掩码], [同上，掩码再乘 `[v₂ ≠ 0]`（除以 0 得 null，q 的规则）],
  [`x < c`、`x ≤ c`（标量）], [自动], [每块阈值 `t = max(c − f, 1)`，无符号比 `r < t`；null 是 0 所以总成立。`x < 103`：`t = 4` → 是, 是, 否；`x < 50`：`t = 1` → 只有 null],
  [`x = c`（标量）], [自动], [`r == c − f`；`c ≤ base` 的块按 `base` 整块跳过，所以 `c − f ≥ 1`，不会配到 null],
  [`x < y`、`=`（两列）], [掩码], [比 `(m₁, v₁)` 与 `(m₂, v₂)` 的字典序；同 frame 的两块直接比残差],
  [fold `sum`], [自动], [`Σv = f·k + Σr`，`k = popcount(m)`；null 行给 `Σr` 加 0。例：`Σr = 7`，`k = 2` → `2·99 + 7 = 205`。现状要减 `63 × null 行数`],
  [fold `max`], [自动], [`f + max r`；`max r = 0` ⇔ 全 null ⇔ 结果 null。例：`max r = 6` → 105],
  [fold `min`], [一次减法], [对 `r − 1`（无符号回绕，null 变成最大）取 `min` 再加 1。例：`0, 2^64−1, 5` → `0` → `r = 1` → 100],
  [fold `prd`、`fills`], [掩码], [`m = 0` 的行跳过（现状的 `isNull` 分支）],
  [二元 `max` `min`], [掩码], [`max`：`(m, v)` 字典序取大；`min` 取小（待选 A）],
  [stream `first`、concat 重定基], [同 frame 自动；换 frame 掩码], [同 `f`：残差零扩展到 `w'`。换成 `f'`：`r' = m·(r + f − f')`。无标志块并入带标志块：`f' ≤ min − 1`，`r' = r + f − f'`],
  [`gather`、`scatter` 的 `last`], [掩码], [按源块 `r' = m·(r + f_src − f_out)`，一遍完成；null 随残差走，Rust 不需要第二遍取标志。`fill` 的格是值],
  [`inl°`、`inr°`、`null`], [—], [带标志的块按 `r ≠ 0` / `r == 0` 取行；无标志的块整块留下 / 整块丢掉],
  [`asc`、`seen`], [不变], [仍是 `nulCodes` 的两列（跨块 frame 不同，不能只比残差）],
)

= 迁移

#tbl(c-rs, (auto, 1fr), ([处], [改动]),
  [`Column.foRNul`（`Rel/Kernel/Value.lean`）], [最后一个合取项改 `== 0`。这是读端唯一的定义],
  [`Coc.nulBlock`、`planBlock`、`patched`、`encodeAt`（`Rel/Kernel/Coc.lean`）],
    [`base = frame = min − 1`（在类型最小 key 处不减）；宽度 `widthFor(mx − f)`；null 行写残差 0；`patched` 的"null 码"是残差 0。这是写端唯一的定义],
  [`Enc.Valid` 的残差界（`Value.lean`）], [带标志的块：非 null、非 patch 的残差 `≥ 1`（现状是 `≤ ones w − 1`）],
  [Rust], [`enc.rs` 的 `nul_meta`、`nul_pack`；`cocops.rs` 的 `is_nul`；`scan.rs` 的 `Col::nuls` 与首个 null；`coc.rs` 的注释；测试 `in_band_null_is_the_flagged_top_residual` 改名并换期望],
  [`Gather`、`Scatter`、`Asc`、`Scan`、`Csv` 的 Lean 模型], [不改：只经 `hasNul`、`foRNuls`、`nulMap`、`wordsFoR … nul` 读写 null],
  [定理], [`foRNuls_wordsFoR`、`Opt.get_eq_of_raw`、`nulAt_encodeAt`、`KernelSpec/Asc` 的陈述都写在 `foRNuls` / `foROpt` 上，陈述不变。
    展开 `foRNul` 或 `nulBlock` 的证明（`KernelSpec/Closure` 的回读、`Coc` 的引理、`foROpt_top`）重证],
  [`CocTest` 的逐字节 `#guard`、Rust `cargo test` 的期望字节], [含 null 的块重新 pin],
  [磁盘], [宽度字节的格式不变，带标志块的含义变了：已写出的含 null 的 own-file 要重写（没有版本号可区分新旧）],
)

- 在途分支：nullband3g3（concat = 一条 `kscan .first` stream）与 nullband3h4（`inr°`）照常做完，不等本设计。它们只经
  `foRNuls` / `Op.null` / `wordsFoR … nul` 碰 null，null 码藏在 `foRNul` + `nulBlock`（Rust `is_nul` + `nul_meta` / `nul_pack`）这一对定义后面。
- 条件：这两个分支自己不写 `ones (widthAt …)` 或 Rust 的 `top`。合并后用索引查 `Column.ones` 的引用、Rust 里查 `top`，除上表外应为空。
- 顺序：g3、h4 合并 → 一个提交 `nullzero` 改上表的读写两端并重 pin → 之后再按 §4.2 逐个放开算术 `Op` 的 `noNul`（每个 `Op` 一条 `decide` + `#guard`）。
- 与架构文档：`rel-architecture` §4.2 卡片里"（已撤）null 码移到残差 0"一条恢复为现行决定，"顶残差"各处随 `nullzero` 提交改写。

= 待主人选

二元 `max` `min` 遇到 null 操作数：
- *A*（本文采用）按和的次序，同 q 的 `|` `&`：`max(null, 5) = 5`，`min(null, 5) = null`。理由：架构已定 null 小于每个值，`max` `min` 由次序定义。
- *B* 与算术一样传播：任一为 null 则 null。理由："其它运算同理"。
- *C* 仍拒绝（`noNul`），等有程序用到再定。
