// palette: one colour per layer, as doc/rel-architecture.zh.typ
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let c-rs  = rgb("#b5541c")   // Rust
#let ink   = rgb("#222831")
#let soft(c) = c.lighten(88%)

#set document(title: "Tm 最小化设计")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); Tm 最小化设计 #h(1fr) base b2e5fcd · 2026-11-22 ],
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

// striped table with a coloured header; an `auto` column is its widest cell, capped at 28% of the width
#let tbl(color, cols, head, ..cells) = layout(size => table(
  columns: cols.enumerate().map(((i, c)) => if c != auto { c } else {
    let w = calc.max(..(head.at(i), ..cells.pos().enumerate().filter(((k, _)) => calc.rem(k, cols.len()) == i)
      .map(((_, x)) => x)).map(x => measure(x).width)) + 12pt
    calc.min(w, 0.28 * size.width) }),
  stroke: none, inset: (x: 6pt, y: 4.5pt),
  fill: (_, y) => if y == 0 { color } else if calc.even(y) { soft(color) } else { white },
  table.header(..head.map(h => text(fill: white, weight: "bold", font: "Noto Sans CJK SC", h))),
  ..cells, table.hline(stroke: 0.8pt + color)))
#let card(color, title, body) = block(width: 100%, fill: soft(color), stroke: (left: 3pt + color),
  inset: 9pt, radius: (right: 4pt))[#text(weight: "bold", fill: color, font: "Noto Sans CJK SC", title) \ #body]

#align(center)[
  #text(20pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[Tm 最小化设计]
  #v(-0.3em)
  #text(10pt, fill: gray.darken(30%))[`Tm` 只留原语 · 可定义的运算进 prelude · 速度由 fused 行保证，每行由一条定理绑定]
]

#card(c-syn, [已定的方向（用户决定，本文不再讨论）])[
  - `Tm`（`Rel/Run/Lang/Tm.lean:16`）只留原语。
  - 每个可定义的运算是 prelude（`Rel/Programs/Prelude.lean`）里的一条 point-free 定义。
  - `prims`（`Rel/Run/Lang/Syntax.lean:240`）的一行是某条定义的快速实现，由定理绑定，elaborator 用它替换定义。
  本文给出：判定规则、逐个运算的结论、构造子前后对照、迁移批次、待决问题。只改文档，不改 `.lean` / `.rs`。
]

= 一个例子，然后是规则

== 例子：`E(succ)` 与 `length`

```
[1 3] {∋} 3 {succ} 4            所以   [1 3] {Λ(∋ succ)} [2 4]        // E(succ) 就是 Λ(∋ succ)
[5 7] {⦇[0, π₁ succ]⦈} 2        而行 length 读 hi − lo = 2            // 同一个关系，两种算法
```

- `E(R)`：今天是构造子 `Tm.E`，其 `den` 子句 `EDen`（`Rel/Lang/Den.lean:280`）字面上就是 `lamDen (∋ ≫ T)`，其代码 `GenK.E`（`Rel/Run/Lang/GenK.lean:311`）字面上就是 `lam (comp (ofVals Tab.mem) R)`。构造子没有带来任何东西：它是 #text(fill: c-sem)[定义]。
- `length`：定义是 fold，行 `length`（`Tab.length`，`Rel/Run/Power.lean:26`）一次读出每个 cell 的宽度。两者相等是定理 `Tm.dfnCut_den`（`Rel/Lang/DfnLaw.lean:258`）。它是 #text(fill: c-run)[fused 行]。
- `∋`：没有任何项与它同义，它是 #text(fill: c-rs)[native 行]。`Λ`、`≫` 有子项，各种遍历要看它们的结构，它们是 #text(fill: c-syn)[构造子]。

== 规则（全文只在此处陈述一次）

#tbl(c-syn, (auto, 1fr, 1fr), ([层], [判定条件], [存放处]),
  [构造子], [(1) 没有其余构造子与行组成的项与它同 `den`；并且 (2) 它带关系子项、或绑定 / 引用变量、或是 elaborator 的规则（`Tm.dem`、`convTm`、`pairTest`、`uniPart`）自己要构造和匹配的叶子], [`inductive Tm`],
  [定义], [存在 point-free 项 `d`，`d.den` 等于该运算的关系；`d` 按 `Tm.gen` 直接运行的代价可接受], [prelude 的一条 `≜`],
  [native 行], [满足 (1)，但不满足 (2)：一个不带结构的叶子，只在某个数据类型（atom、数组的位置）上有意义], [`prims` 的一行，无定义],
  [fused 行], [有定义 `d`，但 `d` 直接运行比专用算法慢，或 `d` 在该 object 上不能运行（缺 universe、缺逆）], [`prims` 的一行，带定义，带定理 `行.den = d.den`],
)

- 「同 `den`」之外还要「同 demand」：定义 `d` 的 `Tm.dem`（`Tm.lean:122`）须与被替换的构造子相同，否则调用处的 `closeRes` / `closed?` 结果会变。下文每个运算都核对了这一点。
- 一个运算进不了定义层的唯一理由是条件 (1)。「elaborator 内部到处用它」不是理由：内部使用改为构造那一行（`dom` 即如此，见 §3.2）。

= 构造子前后对照

今天 44 个构造子（`Tm.lean:16-92`）。目标 22 个。

#tbl(c-syn, (auto, 1fr, 1fr), ([组], [今天], [目标]),
  [allegory], [`id comp conv meet join zero top dom ran`], [`id comp conv meet join zero top`；`dom` `ran` → 定义 + fused 行],
  [除法], [`ldiv rdiv`], [`ldiv rdiv`（`symDiv` 已是定义：`Pre.symDiv`，`Elab.lean:424`，`Tm.symDiv_den`，`Den.lean:497`）],
  [Boolean], [`diff`], [`diff`],
  [积 / 和], [`outl outr pair prod`；`inl inr inl° inr°` 是行；`[R,S]` 已是定义 `Pre.junc`（`Elab.lean:429`）], [`outl outr pair`；`prod` → 定义；`inl inr` 仍是 native 行（问题 A–C）],
  [power], [`lam E est thin nil atPos`；`∋` 是行 `memRow`], [`lam`；`E` → 定义；`nil` `est` `thin` → 定义 + fused 行；`at` → native 行；`∋` 仍是 native 行],
  [数据], [`val uni succ arith leq lt`], [`val uni`；atom 运算全部是行（§3.5）],
  [递归], [`mu nu fold foldr foldI hylo`], [`mu nu fold`；`foldr` `foldI` → 定义 + fused 行；`hylo` 并入 `mu`（§4）],
  [绑定], [`var share own call callCv arg`], [`var arg const`（§5）：`prim` `call` `callCv` `share` 合为 `const`；`own` 删除],
  [库原语], [`prim`], [并入 `const`],
)

目标的 22 个：`id comp conv meet join zero top` · `ldiv rdiv` · `diff` · `outl outr pair` · `lam` · `mu nu fold` · `val uni` · `var arg const`。

= 逐个运算

记号：复合按图序，`R S` 即 `R ≫ S`；`∈ = ∋°`，`> = <°`，`≥ = ≤°`（prelude 已有）。「dem」列写定义的 `Tm.dem` 是否等于今天的构造子。

== 纯定义（不需要行）

#tbl(c-sem, (auto, 1fr, 1fr, 1fr), ([运算], [定义], [`den` 定理], [运行与性能]),
  [`E(R)`], [`E(R) ≜ Λ(∋ R)`], [新增 `Tm.E_den`：展开 `EDen`（`Den.lean:280`）与 `rowDens` 的 `∋` 项即得，`rfl` 级], [`GenK.E` 已是这个复合（§4.6：`∋` 行 → `≫` → `Λ`），代价不变。lifted 路径 `appliedL`（`Elab.lean:1239`）已经按定义构造。dem 相同（`lam` 恒为 true）],
  [`R × S`], [`R × S ≜ ⟨π₁ R, π₂ S⟩`], [新增 `Tm.prod_den`：`rprodMap = rpair (fst ≫ R) (snd ≫ S)`。相邻引理 `Rep.rpair_eq_meet_proj`（`Rel/Rep.lean:84`），freyd 侧 `RelSet.prodMap_eq_rprodMap`], [`build` 在任一操作数 on demand 时已经这样构造（`Elab.lean:2308-2318`）。两侧都 closed 时今天走 `Tab.prod`（CROSS）；改后 dem 由 false 变 true，closed 使用由 `closeRes` 读源 universe，该 universe 见下条],
  [积 object 的 universe], [`ran(⟨⊤(u), ⊤(v)⟩)`，`⊤(u) : 1 ⟶ A`], [`uniPart`（`Elab.lean:2130`）今天写 `.prod u v`；改为左式，`den` 相同（在 key `∗` 上的 pair 即 CROSS）], [代价相同：单 key 上的 `Tab.pair` 就是一次 CROSS。`Tm.code` 里「`prod` 不 memo」的特例（`TmGen.lean:136`）随之删除],
  [`succ`], [`succ ≜ ⟨𝟙, ⊤ 1⟩ plus`], [新增 `Tm.succ_den`：对 `succDen`（`Den.lean:72`）与 `arithDen` 展开], [`Tab.succ`（`Rel/Run/Arith.lean:120`）是一次 `scan`；定义多一次 pair。`succ` 出现在 fold 的 step 里（`DfnCut.length`），所以保留 fused 行 `succ`],
  [`max` `min`], [`max ≜ τ(≤) π₂ ∪ τ(>) π₁`], [在非值 atom 上 `build` 已这样构造（`Elab.lean:2373-2380`）], [值 atom 上 kernel 有 `max` `min` 的 `Op`：fused 行],
  [`hylo(c, S)`], [`μX : c G(X) S` 的 surface 写法，`G` 由 `S` 的源 object 读出（`hyloG`，`Elab.lean:1324`）], [`Tm.den` 的 `hylo` 子句与 `mu` 子句相同（`Den.lean:428-469`），无需定理], [见 §4],
)

== 定义 + fused 行

#tbl(c-run, (auto, 1fr, 1fr, 1fr), ([运算], [定义], [绑定定理], [行与 elaborator]),
  [`dom(R)`], [`dom(R) ≜ ⟨𝟙, R⟩ π₁`。不用 `𝟙 ∩ R R°`：`R°` 在 on-demand 的 `R` 上经常不能运行（`convTm` 对 `lam` `fold` 等报错，`Elab.lean:1928-2001`）], [新增 `Tm.dom_den`：`⟨𝟙,R⟩π₁ = 𝟙 ∩ R ≫ R°`（今天的 `den` 子句），逐点三行。行的正确性已有 `GenK.dom_sound`（`GenKSpec.lean:173`）], [行 `dom` → `Tab.dom`（`Rel/Run/Canon.lean:71`，§4.5：取一列 → `asc` → `seen`）。定义多一次 pair 与一次 gather。dem：定义为 `R.dem`，与今天相同；行要有同样的 dem，见问题 Q–R],
  [`ran(R)`], [`ran(R) ≜ dom(R°)`], [新增 `Tm.ran_den`，由 `Tm.dom_den` 得。行：`GenK.ran_sound`（`GenKSpec.lean:180`）], [行 `ran` → `Tab.ran`（`Canon.lean:67`）。定义要先 `Tab.conv`（两列重排序），行只排一列],
  [`nil`], [`nil ≜ Λ(𝟘)`], [新增 `Tm.nil_den`：`lamDen 𝟘 a ys ↔ ys = []`（`lamDen`，`Den.lean:244`；`nilDen`，`Den.lean:66`）。行：`Tab.nil_holds`（`RepTabDiv.lean:23`）], [行 `nil` → `Tab.nil`（`Rel/Run/Div.lean:64`），常数列。`nil` 是每个 fold 的初值，所以保留行],
  [`est(Q)`], [`est(Q) ≜ ∋ ∩ (∈ \ (Q ∪ 𝟙)°)`。`∈ \ S°` 是最大的 `Y` 使 `∈ Y ⊑ S°`：`xs Y b` 则 `xs` 的每个 `c` 满足 `b S c`], [新增 `Tm.est_den`：等于 `estDen`（`Den.lean:239`）。`∪ 𝟙` 正是 `estDen` 里的 `c ≠ b`，所以不需要 `Q` 自反的假设。行：`Tab.est_holds`（`RepTabDiv.lean:2651`）、`GenK.est_sound`（`GenKEst.lean:14`）], [行 `est`，参数是 pair test `τ(Q)`，与 `thinL` `merge` 同形（`Prim.sig` 的 `some true`，`GenK.testVals`，`GenK.lean:369`）→ `Tab.est`（`Power.lean:49`）。数组 object 没有 universe，定义里的 `\` 不能运行，所以该处永远选行（`DfnCut.fused` 的既有规则）。lifted 路径已按定义构造（`Elab.lean:1439-1446`）],
  [`thin(Q)`], [`thin(Q) ≜ Λ(∋ − ∋ (Q − Q°))`：去掉被别的元素严格压过的元素], [新增 `Tm.thin_den`：等于 `thinDen`（`Den.lean:284`）。行：`Tab.thin_den`（`RepTabDiv.lean:2705`）、`GenK.thin_sound`（`GenKEst.lean:20`）], [行 `thin` → `Tab.thin`（`Power.lean:63`）。`Q` closed 时定义可直接运行，但要把整张 `Q` 与成员表连接；行只在同一数组内的元素对上读 `Q`。与 freyd 的差别见问题 O–P],
  [`⦇e,S⦈ʳ`（`foldr`）], [`⦇e,S⦈ʳ ≜ reverse ⦇e, ⟨π₂,π₁⟩ S⦈`，`reverse ≜ ⦇[nil, ⟨π₂,π₁⟩ cons]⦈`（q 的 `reverse`，prelude 新增）], [新增 `Tm.foldr_den`，由已有的 `foldDen_rev`（`Den.lean:149`）得。行：`GenK.foldr_sound`（`GenKFold.lean:321`）], [行 `foldr`（两个关系参数 `e` `S`）→ `Tab.foldRounds Tab.peelR`（`Rel/Run/Fix.lean:44,58`）：`snoc°` 从尾部读，不生成反转的副本。定义要先建 `reverse` 的整个数组],
  [`foldI(e,S)`], [`foldI(e,S) ≜ ⟨π₂ ⦇e,S⦈, π₁⟩ dom(π₁π₁ ∩ π₂) π₁π₂`：carrier 为 `I×V` 的一个 `fold`，再按 key 取出], [已有 `foldIDen_eq`（`Den.lean:188`）。行：`GenK.foldI_sound`（`GenKFold.lean:348`）], [行 `foldI` → `GenK.foldI`（`GenK.lean:353`）。定义在每个数组上为 `e` 的所有 key 设初值；行只为与该数组配对的 key 设初值。这回答了架构 §7 的「先验证两者确实可写出」：可写出，但须留行],
  [`length` `sum` `flat`], [已有：`DfnCut`（`Elab.lean:2056-2063`）], [已有：`Tm.dfnCut_den`], [不变；定义的文本移入 prelude（§6）],
  [`asc(P)`], [`asc(P) ≜ (dom(P) Λ(> P) length)°`，其中 `>` 是任意 object 上的序], [无：没有定理把 `ascDen`（`Rel/AscOrder.lean:34`）与它等同（`Syntax.lean:292-294`）], [行 `asc` → `Tab.asc`（`Rel/Run/Asc.lean:20`）。先决问题是「任意 object 上的序」：问题 F–H],
  [`star(R)`], [`star(R) ≜ μX : 𝟙 ∪ R X`], [新增 `Tab.star_holds`], [见 §4],
)

== `dom` 行需要的 dem

- 今天：`Tm.dem (.dom R) = R.dem`（`Tm.lean:124`）；`arg (prim r) x` 的 dem 在 `r.whole` 时是 `x.dem`，否则恒为 true（`Tm.lean:123`）。
- `dom` 行既不是 `whole`（它要在 demand 的 key 上运行 `R`），也不是恒 true（closed 的 `R` 给出 closed 的 `dom(R)`）。
- 改动：`Prim.whole : Bool` 推广为三值 `Prim.dem`：`keys`（恒 on demand）、`whole`（读整表）、`arg`（dem 取自参数，参数在 demand 的 key 上运行）。`dom` `ran` `est` `thin` `foldr` `foldI` 都用 `arg` 或 `keys`，不新增机制。

== native 行

#tbl(c-rs, (auto, 1fr, 1fr), ([运算], [为什么不能定义], [改动]),
  [`∋` `inl` `inr` `cons` `snoc` `cat` `zip`、`cons°` 等], [数据类型的构造与读取；今天已是行（`Syntax.lean:240-317`），`rowDens`（`Den.lean:371`）给出 `den`], [不变],
  [`at`], [`∋` 丢掉位置，`Λ` 的结果按 `Obj.lt` 排序，所以位置只能由数组自身读出], [今天是带数字的构造子 `Tm.atPos k`。改为二元行 `at : [β]×ν ⟶ β`（q 的索引），`at(k) ≜ ⟨𝟙, ⊤ k⟩ at`。`Tab.atPos`（`Power.lean:36`）把 `colConst n k` 换成索引列，其余 kernel 调用不变。问题 L–N],
  [`plus minus times div mod divide`、`$`、`sqrt` 等浮点运算], [atom 上的算术], [§3.5],
)

== atom 运算：一种统一的处理

今天有两种：`succ arith leq lt` 是带 universe `U` 的构造子（`Tm.lean:55-58`）；`sqrt`、`$`、浮点运算是不带 universe 的行（`floatOps`，`Rel/Run/Cast.lean:31`）。

```
(2,3) {plus} 5                  // 行 plus : t×t ⟶ t，在整个 atom 上
(2,3) {(U×U) plus U} 5          // 有界 object 上的 plus：elaborator 在两侧复合 U
```

统一为第二种：每个 atom 运算是一行，签名只含 atom object，行里没有 universe；有界 object 上的运算由 elaborator 写成 `⟨π₁U, π₂U⟩ 行 U`。这正是 `DfnCut.cut`（`Elab.lean:2066-2082`）对 `length` `sum` 已经做的事。

#tbl(c-rs, (auto, 1fr, 1fr), ([运算], [归属], [说明]),
  [`plus minus times div mod divide`], [native 行，各 atom `t` 一个实例], [→ `Tab.arith`（`Arith.lean:104`），§4.5 的 `scan` 链不变。`den`：`arithDen`（`Den.lean:127`）去掉 `U`],
  [`lt`（pair 上的 test）], [native 行 `lt : t×t ⟶ t×t`，`a < b` 的 pair 上的 coreflexive], [→ `Tab.cmpPairs`（`Div.lean:114`）],
  [`<`（关系）], [定义 `< ≜ U ⟨𝟙, ⊤(U)⟩ lt π₂`], [即 `GenK.cmp`（`GenK.lean:295-305`）的两条分支：已知 `K.pairs` 时只运行 `lt`；否则是 `dom U` 的 CROSS 再 `lt`。`pairTest` 对它化简为 `(U×U) lt`，定理 `τ(<) = (U×U) lt` 新增],
  [`≤`], [定义 `≤ ≜ < ∪ 𝟙`，前提是对每个 atom 有 `leAt t a b ↔ ltAt t a b ∨ a = b`（`Den.lean:90-97`）], [待验证：浮点 atom 上 `fordAt` 对 null 的处理。若不成立，`le` 与 `lt` 同为 native 行。无论哪种都保留 fused 行（一次 `scan`，`Tab.ordOp`，`Div.lean:106`）],
  [`succ` `max` `min`], [定义 + fused 行（§3.1）], [],
  [`$`、浮点运算], [native 行，不变], [`Tab.cast`、`Tab.floatOp`（`Cast.lean:15,43`）],
)

- 删除的构造子：`succ arith leq lt`。`convTm` 里它们的四条规则（`Elab.lean:1976-1985`，其中 `arith` 那条用到 `Tm.prod`）改为查逆表（§5.2）。
- 定理：`GenK.succ` / `arith` / `leq` / `lt` 的 soundness 改述为行的 `RowOK`（`rowsProved`，`GenSound.lean:100`）。

= 递归：`mu`、`nu`、`star`、`hylo`

`mu` 与 `nu` 保持为原语。非线性的 `μ`（`X` 出现在函子内，如 `hylo`）与 `ν` 不能写成闭包。

== `star`

```
a {R} b {R} c，c {S} d          所以   a {R* S} d
μX : S ∪ R X  =  R* S           // 线性递归就是闭包后复合
```

- prelude 新增 `star(R : α ⟶ α) : α ⟶ α ≜ μX : 𝟙 ∪ R X`，与定理 `starLinear : μX : S ∪ R X = star(R) S`（由 `rel_aop prelude` 证）。
- surface 已有后缀 `R*`，在 parser 里展开为 `μX : 𝟙 ∪ e X` 并为 `X` 造新名（`Rel/Run/Lang/Grammar.lean:397-403`）。改为：`R*` 是 prelude 常量 `star(R)` 的记号，parser 不再造名。
- fused 行 `star` → 新的 `Tab.star`：semi-naive，`Δ₀ = K`，`Δᵢ₊₁ = Δᵢ R − X`，`X := X ∪ Δ`。`≫` 对 `∪` 分配，所以对线性递归 semi-naive 是精确的；一般的 `μ` 体没有这个性质，继续用整体迭代。
- 行 `star` on demand：`K star(R)` 从 key `K` 出发只走可达的点，所以在没有 universe 的 object（数组）上也能运行；closed 的 `μ` 每轮整体读体，做不到（`Elab.lean:2459-2463`）。

== 程序与 prelude 里的每个 `μ` / `ν`

范围：`Rel/Programs/*.lean` 全部 20 个文件。未列出的文件（`Circuit` `Detab` `Edit` `JobShop` `Knapsack` `Mss` `Selsort` `Wumpus` `Frame` `FrameGroup` `FrameJoin`）没有 `μ` `ν` `hylo` `*`。`Rel/Lang/Test/Fixpoints.lean` 的测试程序不在此表内，决定问题 S–T 之前须补查。「组合子」列是 §5.3 无变量方案的输入。

#tbl(c-sem, (auto, 1fr, auto, 1fr, 1fr, auto), ([位置], [项], [线性], [用 `star` 改写], [fused 行 `star` 的收益], [组合子]),
  [`Party.lean:21`], [`under ≜ boss°*`], [是], [已是 `star(boss°)`], [12 个点、深度 3：无可测收益；作为 `star` 的回归用例], [`star`],
  [`Party.lean:52`], [`guests ≜ μX : win (𝟙 ∪ (boss° boss° X)) ∪ ((𝟙 − win) boss° X)`], [是：`X` 出现两次，但每次都是 `Rᵢ X`，在 `∪` 下], [`guests ≜ star(T) win`，`T ≜ win boss° boss° ∪ ((𝟙 − win) boss°)`], [同上，规模太小。改写后去掉一个 `μ`], [`star`],
  [`Party.lean:33,43,50`], [`hylo(⟨𝟙, kids⟩, S)` 三处：`μX : c G(X) S`], [否：`X` 在 `F(·)` 与 `×` 下], [不能], [不适用], [`hylo`],
  [`Quicksort.lean:31`], [`sort' ≜ hylo(c, [nil, join])`], [否：`X × 𝟙 × X`], [不能], [不适用], [`hylo`],
  [`CSP.lean:14`（被 `SudokuAC:60`、`SudokuPC:49`、`SudokuPC9:23` 调用）], [`AC3 ≜ νX : s ∩ (A\(X C))`], [`ν`，`X` 一次], [不能], [不适用], [`sim(A,C,s)`：`s` 之下最大的 `X` 使 `A X ⊑ X C`（最大模拟）],
  [`SudokuPC.lean:54`、`SudokuPC9.lean:28`], [`K ≜ νX : K₀ ∩ pc(X)`，`pc(X) = π₁\(sup(X) X)`，`sup(X) = π₁X ∩ (π₂π₁°)`], [`ν`，`X` 两次，且相互复合], [不能], [不适用], [无：`X` 与自身复合，不是模拟的形状；只能为这一个程序造组合子],
  [`Prelude.lean`], [没有 `μ` `ν`，只有 fold], [—], [—], [—], [`fold`],
  [`Blocks.lean:25-26`], [`Q ≜ ran(L(s₀,t)π₁)`：用一个 fold 在数组 `0…27` 上数轮次来迭代 `t`，没有写 `μ`], [是（未写成 `μ`）], [`Q ≜ ran(s₀ star(t))`；`L` 另外记录步数，`C` `Z` 仍需要它], [有：`t : [X×X] ⟶ [X×X]` 在数组 object 上，closed 的 `μ` 不能运行，所以今天只能写有界的 fold；on-demand 的行 `star` 从 `s₀` 出发直接算可达状态，无需上界 `N`], [`star`],
  [`Chess.lean:30`], [`L(R) ≜ 𝟙 ∪ R ∪ (RR) ∪ … ∪ (RRRRRRR)`], [是（未写成 `μ`）], [`L(R) ≜ star(R)`（8×8 棋盘上 `R⁸ = 𝟘`）], [今天 28 次 `≫`；`star` 至多 8 轮，每轮一次 `≫`], [`star`],
)

#card(c-rs, [与 §4.5 的出入])[
  §4.5 的 `μ` 行写「semi-naive 只多一个 `−`」。代码没有 semi-naive：`Tab.mu`（`Rel/Run/Fix.lean:35`）每轮算 `X ∪ f(X)`，`f` 读整个 `X`。所以 `d` 轮的闭包做了约 `d` 倍的连接；fused 行 `star` 把它降到一倍。对比对象是这个整体迭代，不是 semi-naive。
]

== 局部完备的视角：为什么 `mu` `nu` 是原语而 `star` 不是

```
A = {1,2,3}，R = {1→2, 2→3}，φX = 𝟙 ∪ R X
定义  μφ = ⋂{X : φX ⊑ X}        // X 取遍 A ⟶ A 的全部 2⁹ = 512 个关系
迭代  𝟘 → 𝟙 → 𝟙∪R → 𝟙∪R∪R²      // 再一轮不加行，停
```

- Freyd 没有不动点算子。局部完备的分配 allegory（§2.22，`Freyd.Alg.LocallyCompleteDistributiveAllegory`，`/home/dh/repo/freyd/Freyd/S2_20.lean:391`）的每个 hom-set 是完备格；`μ`、`ν`、`R* = ⋃ₙ Rⁿ` 都由任意交与并 #text(fill: c-sem)[定义]。§2.315(b)：每个分配 allegory 嵌入它的局部完备的 downdeal 完备化；同文件 `:489-561` 有 `IsDowndeal`、`principalDowndeal`、`principalDowndeal_injective`、`downClosure_of_isDowndeal`（索引里只见到嵌入是单射这一条，没有见到完备化作为 allegory 的实例）。
- AOP 侧：`Freyd.Alg.mu φ = Inf (fun X => φ X ⊑ X)`，`nu φ = Sup (fun X => X ⊑ φ X)`（`AOP/A6_2.lean:53,56`），在 `LocallyCompleteDistributiveAllegory` 上。`Rel.Core.Rel.mu` `nu`（`Rel/Core/Fix.lean:17,20`）是同一定义的逐点写法。
- 这个定义不能执行：`⋂{X : φX ⊑ X}` 量化 `A ⟶ B` 的每个关系，共 `2^(|A|·|B|)` 个；object 无限时有无限多个。
- Rel 执行的是 Kleene 迭代 `⋃ₙ φⁿ(𝟘)`，某轮不加行即停（`Tab.fixOn`，`Rel/Run/Fix.lean:20`）。

#tbl(c-sem, (auto, 1fr, 1fr), ([问题], [已有], [缺]),
  [迭代等于 `Inf` 定义], [freyd：`Continuous`（`AOP/A6_2.lean:286`）、`kleene : mu φ = Sup (fun T => ∃ n, T = iterZ φ n)`（`:299`，假设 `Monotonic` 与 `Continuous`）、`mu_le_of_closed`（`:337`）。\ Rel：`GenK.mu_sound`（`Rel/Lang/GenKFix.lean:91`）只假设 `Monotonic Φ`], [Rel 侧没有 `Continuous` 与 `kleene`，也不需要：见下条],
  [Rel 的 soundness 靠什么], [不靠连续性。每轮 `X ⊑ μ`（`mu_prefixed`）；停下时行数不变，所以 `Φ(X) ⊑ X`，于是 `μ ⊑ X`（`mu_le`）。稳定了的迭代就是一个 prefixed point，Knaster–Tarski 的两半足够（`Rel/Core/Fix.lean:22,26`）], [连续性只在迭代不稳定时才需要（无限 object）；Rel 此时到 `cap` 报错，不返回表],
  [`ν`], [对偶：`Tab.nu`（`Fix.lean:26`）从起点 `S` 的表向下，`X ↦ X ∩ φ(X)`；`GenK.nu_sound`（`GenKFix.lean:46`）：每轮 `ν ⊑ X ⊑ S`，停下时 `X ⊑ S ∩ Φ(X)`，由 `le_nu` 得 `X ⊑ ν`。`Tm.nu k S body` 的 `S` 就是这个起点], [—],
  [轮数上界], [代码里的 `cap`：`μ` 为 `max muCap (n·m+2)`，`n` `m` 是两端 universe 的大小（`Elab.lean:2470-2474`）；`ν` 为起点行数加 2（`Fix.lean:28`）。理由写在注释里：严格的一轮至少增（减）一行，所以至多 `|A|·|B|` 轮], [没有定理说单调的体不会撞上 `cap`。撞上是报错，不影响 soundness；缺的是「不误报」],
  [体单调], [`Tm.pol`（`Tm.lean:315`）在 elaboration 时检查，`Tm.monoOK`（`GenSound.lean:125`）是 `Tm.gen_sound` 的假设], [—],
)

结论：Freyd 意义下的原语是无限的交与并。带约束变量的 `mu` `nu` 是它可执行的片段，对有限 object 上单调的体成立（稳定即不动点）。所以它们留作 `Tm` 的原语；`star` 是其中一个体 `𝟙 ∪ R X`，是 prelude 定义。freyd 已有 `Freyd.Alg.star`、`starBody`、`star_unfold`、`star_eq_mu'`、`star_trans`、`star_UP`（`AOP/A6_7.lean:43-172`），prelude 的 `starLinear` 由它们证。

== `hylo` 并入 `mu`

- 事实：`Tm.den` 对 `hylo` 与 `mu` 是同一子句；差别只在运行。`GenK.mu` closed，每轮整体读体，有 `cap`；`GenK.hylo`（`GenK.lean:391`）on demand：先算子节点可达的点 `N`，检查无环，再只在 `N` 上迭代 `|N|+3` 轮。
- 提议：删构造子 `hylo`；`hylo(c,S)` 是 `μX : c G(X) S` 的 surface 写法（如 `R*`）。`Tm.gen` 对 `mu`：体有子节点（`Tm.kids k A = some c`，`Tm.lean:346`）时走今天 `GenK.hylo` 的路径，否则走 `GenK.mu`。把迭代限制在 `N` 上的依据是已有的 `Tm.den_local`（`Den.lean:972`）。
- 环：今天 `hylo` 遇环报错，因为数组值会无限增长。并入后：有环时 `|N|+3` 轮不够，改用 `mu` 的 `cap`，到 `cap` 仍未停才报错，报错文本沿用 `cycleMsg`。无环时行为与今天完全相同。
- dem：`mu` 的 dem 由恒 false 变为「体有子节点」。问题 D–E。

= 绑定组：语法还是实现

`var share call callCv arg own` 都不是 allegory 运算。逐个判定：

#tbl(c-syn, (auto, auto, 1fr, 1fr), ([构造子], [判定], [依据（代码）], [去处]),
  [`var d k`], [`k` 是语法，`d` 是实现], [`k`：`μX`/`νX` 绑定的变量，`den` 为 `ρ k`；不动点演算本身有约束变量。`d`：「use site 定的 demand 位」（`Tm.lean:70-73`），`Tm.dem` 只是读回它（`Tm.lean:131`）], [留 `var k`。`d` 移入环境：`Tm.dem (δ : Nat → Bool)`，由绑定者写入（`mu`/`nu` 的变量是每轮的表，false；参数取实参的 dem）。于是 `den` 有 `ρ`、`gen` 有 `η`、`dem` 有 `δ`：同一语法的三个解释各带一个环境],
  [`share k R`], [实现], [`den` 即 `R.den`（`Den.lean:428-469`）；只由 `Tm.number`（`TmGen.lean:379`）在 elaboration 之后插入，为的是 `Code.shares`（`TmGen.lean:390`）把每个 closed 部分只算一次], [不再是构造子：编号后的 closed 部分是程序表里一个生成的零元常量，使用处是 `const`（§5.1）。表由 `Tm.number` 从 `Tm` 生成，不手写],
  [`call ks c os b`], [实现（定义机制）], [`den` 是体 `b` 在实参下的 `den`（`Val.args`，`Den.lean:298`）；`gen` 是体的代码绑定实参（`TmGen.lean:191`）。它是 `let`，不是运算。体 `b` 内联在节点里，只为 `Tm.den` 能结构递归], [并入 `const`：节点只留名字 `c` 与 `os`，体在程序表里],
  [`callCv ks c c' os b u`], [实现], [`call` 加上逆常量 `c'` 与逆体 `u`，仅为 `convTm`；单列构造子是因为 `Option (Tm B A)` 字段会成为 kernel 拒绝的嵌套族（`Tm.lean:78-80`）], [删除：逆在逆表里（§5.2）],
  [`arg f x`], [语法], [算子作用于关系：`F(R)`、`thinL(Q)`、`est(Q)`、`c(R,S)`。`den` 由 `Tm.argDen`（`Den.lean:474`）沿 spine 收集], [保留],
  [`own R`], [实现], [`den` 与 `gen` 都是 `R` 的（`TmGen.lean:169`）；只为 `convTm` 知道 `perm° = perm`（`Tm.lean:49-51`；`Expand.useDef` 把 `prelude.perm` 换成 `.own`，`Expand.lean:41-58`）], [删除：`perm ↦ perm` 是逆表的一项],
  [`close`（`Pre.close`）与 `closeRes`], [elaborator 内部，已在 `Tm` 之前], [`Pre.close` 不进入 `Tm`；`closeRes`（`Elab.lean:2183`）在需要 closed 项处复合源 universe], [不动；它读 `Tm.dem`，随 `δ` 改签名],
  [`Tm.dem`], [实现，但由 `Tm` 计算], [构造子与其部分的函数（`Tm.lean:122-137`），`var` 除外], [保留为函数，加 `δ`；每删一个构造子少一条子句],
)

== `const`：行、定义、共享部分是同一个东西

```
est(≤)      今天：arg (prim estRow) τ(≤)        // 行
sort(≤)     今天：arg (call … prelude.sort …)   // 定义，体内联
            今天：share 7 R                     // 编号的 closed 部分
三者都是：一个有名字的常量，用 arg 给它关系参数
```

- 一个构造子 `const (c : Lean.Name) (os : List Obj)`，取代 `prim`、`call`、`callCv`、`share`。
- 一张表 `Consts`，每项：签名；`body?`（定义的项）；`row?`（native 实现，即今天 `Prim` 的字段与 `rowGens` 的项）；`conv?`（逆常量）；`dem`。
- 三层由表项的形状决定，不另设机制：

#tbl(c-run, (auto, auto, auto, 1fr), ([层], [`body?`], [`row?`], [义务]),
  [定义], [有], [无], [无],
  [native 行], [无], [有], [`RowOK`（`rowsProved_ok`，`GenSound.lean:747`）],
  [fused 行], [有], [有], [定理 `row.den = body.den`；缺定理的项由一个 `#guard` 列表拒绝，如今天的 `Prim.dfn_read`（`DfnLaw.lean:299`）],
  [共享部分], [有，由 `Tm.number` 生成], [无], [`Code.shares_sound`（`GenSound.lean:1150`）],
)

- `den`：`Val` 增加常量环境，按依赖顺序对表折叠得到（定义不递归；`Code.shares` 今天就是这样折叠 slot 的）。`Tm.den` 仍是结构递归，因为体不再内联。
- DRY：表是唯一来源。`rowDens`、`kernRows`、`rowGens`、`Elab.dfns`、`Prim.prelude`、`Shares` 今天是六张按名字对齐的表（`#guard rowGens.length = kernRows.length`，`TmGen.lean:129`）；改后前五张是同一张表的字段。
- 这是 IR 吗：不是第二种项。程序 = `Consts` 表 + 若干 `Tm`；表里共享部分的项由 `Tm.number` 生成。

== 逆表

- 今天逆的来源有三处：行的 `Prim.conv`（`Syntax.lean:184-202`）；`callCv` 的 `c'`；`own`。
- 改为 `Consts` 项的 `conv?` 一个字段。行的逆照旧填写（`cons ↦ uncons`）。定义的逆来自 prelude 里形如 `c° = c'` 的定理：新增 `theorem permConv : perm° = perm`（由 `rel_aop prelude` 证，如 `absorption`），elaborator 读到这种形状的定理就填 `conv?`。
- `convTm`（`Elab.lean:1928-2001`）对 `const` 只有一条规则：查 `conv?`，没有则报今天的错。`succ arith own callCv prim` 的专门规则全部消失。`convTm_den`（`ConvSpec.lean:128`）的相应情形改为引用该定理。

== 去掉 `var` 的方案（供决定，问题 S–T）

`var` 今天有两个用途：`μX`/`νX` 的约束变量；定义的参数（`filter(p)` 的 `p`，由 `call` 的 `ks` 与 `arg` 绑定）。

直接的编码为什么不行：

- HOAS `mu (body : Tm A B → Tm A B)`：`Tm` 出现在箭头左侧，不是严格正的，Lean 拒绝这个 inductive。
- PHOAS `mu (body : V A B → Tm V A B)` 加 `var (x : V A B)`：去掉了编号 `k`，但变量构造子还在。

方案 (a)：无变量，递归只经由组合子（AOP 的写法）。

#tbl(c-syn, (auto, 1fr, 1fr), ([组合子], [含义], [覆盖 §4.2 表里的哪些]),
  [`fold` `⦇e,S⦈`], [已无变量], [prelude 的全部 fold],
  [`hylo(c, S)`], [`μX : c G(X) S`，取 `c` 与 `S`，没有 `k` 与体；函子 `G` 由 `S` 的源 object 决定（`hyloG`，`Elab.lean:1324`）], [`Party` 三处、`Quicksort` 一处],
  [`star(R)`], [`μX : 𝟙 ∪ R X`；线性的 `μX : S ∪ R X` 写 `star(R) S`], [`Party.under`、`Party.guests`、`Blocks.Q`、`Chess.L`],
  [`sim(A, C, S)`], [`νX : S ∩ (A\(X C))`：`S` 之下最大的模拟], [`csp.AC3`（三个程序调用）],
  [无], [`νX : K₀ ∩ (π₁\((π₁X ∩ π₂π₁°) X))`], [`SudokuPC`、`SudokuPC9` 的 `K`：没有组合子],
)

- 得到：`mu` `nu` `var` 三个构造子换成 `hylo` `star` `sim`；`Tm.fv` `Tm.subst` `Tm.pol`、`Val.bind`、`Val.Grow`、`Tm.den_local` 以及 `Tm.monoOK` 这个假设全部消失，因为每个组合子的单调性各证一次。surface 的 `μX : …` `νX : …` 语法删除。
- 代价：`SudokuPC` 的 `K` 写不出来，除非为它加第五个组合子；以后每个新形状的不动点都要加一个构造子、一条 `den`、一个 `GenK` 函数、一条 soundness。这与 §4.3 的结论相反：那里的原语是「任意单调体的不动点」。
- 定义参数：方案 (a) 在 elaboration 时代入实参（`Tm.subst`，`Tm.lean:264`，已有），`Tm` 里没有参数变量，`call` `arg` 对定义不再需要（`arg` 只剩给行传参数）。
  - `call` 今天给出的代码共享：closed 部分照旧由 `Tm.number` 编号、只算一次（`TmGen.lean:379`），运行时不变。带参数的体今天每个 `(c, os)` 生成一份 Lean 常量；代入后每个调用处各生成一份。若要保留共享，它存在于从 `Tm` 生成的 IR 里（对展开后的项做 hash-consing，把只差实参的子项抽成函数），不手写。
  - 构建代价：项的大小由「各定义体之和」变为「每个调用处一份体」。例：`chess` 的 `ρ` 调用 `r` 八次，`r` 调用 `L`（28 次 `≫`）；`W` `M` `Pin` 又各调用 `ρ` 或 `q` 八次。`Expand.tmE` 生成的 `Expr`、kernel 的类型检查、`relc` 输出的 C 都随之线性增长。未测量；决定前应在 `chess` 与 `frameStat` 上量 `lake build` 的时间与 `.olean` 大小。

方案 (b)：留 `var`。

- 变量用 PHOAS（`Tm V A B`，`var (x : V A B)`，`mu (body : V A B → Tm V A B)`）取代编号 `k`：变量带类型，`η k A B` 的按 object 查找与转型消失。代价：每个 `Tm` 上的函数多一个参数 `V`；`Expand.tmE` 与 `Tm.numberKey` 需要一阶的键，仍要在 `V := fun _ _ => Nat` 处实例化，所以编号在这两处回来。
- demand 位 `d` 移出 `Tm`，进环境 `δ`（§5 的表）。
- 定义参数：仍是变量，由 `const` 的表项绑定（§5.1）。

= fused 行的选择：一个机制

今天有两个机制，都做「用行替换定义」：

#tbl(c-run, (auto, 1fr, 1fr), ([], [`Prim.prelude` + `useDef`], [`Elab.dfns` + `DfnCut`]),
  [谁写定义], [prelude 文本（`filter` `takewhile` `tails` `prefix` `suffix` `concat`）], [Lean 里构造的 `Tm`（`length` `sum` `flat`），prelude 里没有],
  [用户写什么], [定义名], [行名],
  [替换], [`Expand.useDef`（`Expand.lean:41-58`）按常量名换成 `.prim`], [`build` 按 universe 选 `fused` / `cut` / 定义（`Elab.lean:2330-2363`）],
  [定理], [无：「named unchecked」，由 `Test` 与 `Calc` 检查], [`Tm.dfnCut_den`，并由 `Prim.dfn_read` 锁定行的名单],
)

合并为一个（即 §5.1 的表）：

- 定义的文本一律在 prelude。`length ≜ ⦇[0, π₁ succ]⦈`、`sum`、`flat` 从 `DfnCut` 的 Lean 构造移为 prelude 文本；`DfnCut` 只保留「按 universe 选 fused / cut / 定义」的规则，其定义项读自 prelude 常量的 `body?`。
- 用户写的永远是定义名；行没有独立的 surface 名字。`Op.table`（`Syntax.lean:323-336`）里 `dom ran E est thin nil` 等项改为 prelude 常量。
- 选择规则不变（`Elab.lean:2330-2363`）：不需要 universe 或 universe 无界 → 行；universe 是初始段 → `cut`；否则 → 定义。
- 每个 fused 项必须有定理。今天「unchecked」的六行（`filter` 等）成为待证义务，列在批次 B9；证出之前留在一个显式的 `unproved` 名单里，名单只能变短。

= 对各部分的改动汇总

#tbl(c-sem, (auto, 1fr), ([部分], [改动]),
  [`Tm` 的遍历], [`size mapMSz fv subst pol kids`（`Tm.lean:141-346`）、`Expand.tmE`（`TmGen.lean:283`）、`Tm.number`：每删一个构造子各少一条子句。`Tm.pol` 里 `lam E thin` 的「部分须不含变量」只剩 `lam`],
  [`Tm.dem`], [加环境 `δ`；`dom own share call callCv` 的透传子句消失；`arg` 子句读 `Prim.dem` 三值],
  [pair test `τ(Q)`], [`pairTest`（`Elab.lean:1901`）与 `test`（`Elab.lean:2501-2545`）构造 `dom` 之处改为构造行 `dom`；`τ(<)` 化简为 `lt` 行],
  [`convTm`], [§5.2：`const` 一条规则；`dom ran` 的自逆规则改为逆表项 `dom ↦ dom`、`ran ↦ ran`],
  [`GenK`], [删 `E prod own`；`dom ran nil est thin atPos succ arith leq lt foldr foldI` 的函数体不动，改由行的表项引用；`hylo` 成为 `mu` 的一条路径；新增 `star`],
  [`Tm.gen` / `Tm.gen_sound`], [`Tm.gen`（`TmGen.lean:143-193`）从 44 条减到 22 条。`Tm.gen_sound`（`GenSound.lean:1005`）相应情形移到 `rowsProved_ok`；已有的 `GenK.*_sound` 引理原样复用],
  [`Tm.den`], [从 44 条减到 22 条；被删构造子的命名语义（`estDen` `thinDen` `EDen` `nilDen` `foldIDen` 等）留作行的 `den` 或定理的右端],
  [kernel（`crate/`）], [不动。`Tab.star` 与索引列的 `Tab.atPos` 都只用现有 kernel],
)

性能（对照架构 §4.5 / §4.6）：每个运算运行的仍是今天的 `Tab.*`，因为凡定义比专用算法慢之处都留了 fused 行。变化只有三处：`E`、`×` 无变化（今天的代码已是定义）；`star` 更快（§4.2）；closed × closed 的 `×` 由 `Tab.prod` 换成单 key 的 `Tab.pair`，同为一次 CROSS。

= 迁移批次

每批独立可构建。每批的 gate：`lake build RelCore RelKernel RelRun Rel` 全绿（含每个程序的 `#guard x.ok` 与 `Rel/Lang/Test/*` 的期望文本）；`sh crate/build.sh syms`；`rel-native` 的 `out/key` `out/val` 与 `lake exe relc plan` 一致。

#tbl(c-run, (auto, 1fr, 1fr, auto), ([批次], [内容], [文件], [风险]),
  [B0], [架构文档按 §9 改；不改代码], [`doc/rel-architecture.zh.typ`], [无],
  [B1], [`E` → prelude 定义；删 `Tm.E` `GenK.E`；`Tm.E_den`], [`Tm.lean` `Den.lean` `GenK.lean` `TmGen.lean` `GenSound.lean` `Elab.lean` `Prelude.lean`], [低：代码已是定义],
  [B2], [`×` → `⟨π₁R, π₂S⟩`；`uniPart` 的积 universe；删 `Tm.prod` `GenK.prod` 与 `Tm.code` 的特例；`Tm.prod_den`], [同上，加 `ConvSpec.lean`], [中：closed 积由 false 变 on demand，`crossMax` 的检查要跟到 `Tab.pair`],
  [B3], [`Prim.dem` 三值；行 `dom` `ran` `nil`；删三个构造子；`pairTest` `test` `uniPart` `DfnCut.flat` 改为构造行], [`Syntax.lean` `Tm.lean` `Elab.lean` `Den.lean` `GenSound.lean`], [高：`dom` 在 elaborator 里用得最多；须先合],
  [B4], [行 `est` `thin`（照 `thinL`）；prelude 定义；`Tm.est_den` `Tm.thin_den`], [`Syntax.lean` `Prelude.lean` `Den.lean` `GenSound.lean` `relaop/RelAop/Prelude.lean`], [中：`Mss` 的 `calc` 用到 `est` 的 prelude 定理],
  [B5], [atom 运算全部成行；删 `succ arith leq lt`；二元行 `at`，删 `atPos`], [`Syntax.lean` `Tm.lean` `Elab.lean` `Den.lean` `GenSound.lean` `Power.lean`], [中：`leAt` 的验证；`Frame*` 大量使用算术],
  [B6], [`foldr` `foldI` → fused 行；prelude `reverse`], [`Syntax.lean` `Tm.lean` `Elab.lean`（`lFold`，`:982`）`Den.lean`], [低],
  [B7], [prelude `star`，`R*` 改为它的记号；`Tab.star` 与 `Tab.star_holds`；`Party.guests`、`Chess.L` 改写], [`Grammar.lean` `Prelude.lean` `Fix.lean` `Party.lean` `Chess.lean`], [中：新的证明],
  [B8], [`hylo` 并入 `mu`], [`Tm.lean` `GenK.lean` `TmGen.lean` `GenKHylo.lean` `Elab.lean`], [中：`mu` 的 dem 改变；取决于问题 D–E],
  [B9], [逆表；删 `own` `callCv`；`Tm.dem` 加 `δ`，`var` 去掉 `d`；`permConv`], [`Tm.lean` `Elab.lean` `Expand.lean` `ConvSpec.lean` `Prelude.lean`], [中：`Tm.dem` 有 92 处使用],
  [B10], [`const` 与 `Consts` 表：并 `prim call share`；并 `dfns` 与 `Prim.prelude`；六条 unchecked 行的定理], [`Syntax.lean` `Tm.lean` `TmGen.lean` `Den.lean` `GenSound.lean` `Expand.lean` `DfnLaw.lean`], [高：`Code.program_sound`（`GenSound.lean:1318`）重述；最后做],
)

- 顺序：B0 → {B1, B2, B6, B7} → B3 → {B4, B5} → B8 → B9 → B10。master 在每批之后都是绿的，因为每批删构造子与加定义 / 行在同一次提交里。
- 可在并行 worktree 里做：{B1, B2, B6, B7}，以及 {B4, B5}。它们改同一批文件的不同构造子子句；`Tm.dem` 列叶子的那几行（`Tm.lean:133-137`）会按 hunk 冲突，合并时手工取并集。
- 不可并行：B3 之前不做 B4（`est` 行依赖 `Prim.dem`）；B9、B10 改所有遍历的签名，各自独占。

= 对架构文档 §1 与 §7 的修改建议

构造子分组表（`doc/rel-architecture.zh.typ:185-196`）换为 §2 的「目标」列，并加一行说明三层（§1.2 的表）。该表今天的出入：

- 漏列已存在的构造子 `foldr`（只在正文提到）、`foldI`、`callCv`。
- 列了 `junc`；代码里 `[R,S]` 已是定义 `Pre.junc`（`Elab.lean:429`），不存在构造子 `junc`，也不存在 `juncD`。
- 写「目标：加 `inl` `inr`」为构造子；代码里它们是行（`inlRow` `inrRow`，`Syntax.lean:212-214`）。按 §1.2 的规则它们留作行（问题 A–C）。

TODO（`:487-494`）的修改：

#tbl(c-syn, (auto, 1fr), ([行], [改为]),
  [`:479`], [删去「删 `Tm.gap`」与 `compile` / `compile_sound`：索引里没有这三个声明；现有的是 `Tm.gen` 与 `Tm.gen_sound`，假设为 `Tm.GenHyp`（`GenSound.lean:108`）],
  [`:492`], [「`junc` 改为定义」已完成，删去；「`Tm` 加 `inl` `inr`」改为「`inl` `inr` 是 native 行」],
  [`:493`], [换为本文 §3 的结论表],
  [`:494`], [`flat` 已不是构造子（`flatRow`，`Tm.flat_den`）；`foldI` 改为「定义 + fused 行」（§3.2）；「`hylo` 改名 `hylo`」是空操作，换为「`hylo` 并入 `mu`」],
  [`:497`], [`Tm` 去掉 `d`：做法是 §5 的 `δ`；`Fn d A B` 仍在 `GenK` 里使用，本文不处理],
)

§4.5 的 `μ` 行：把「semi-naive 只多一个 `−`」改为「整体迭代（`Tab.fixOn`）；线性递归走行 `star`（semi-naive）」。§4.6 的 `length` 项：「定理未证」与 `Prim.dfn` 改为「`Tm.dfnCut_den` 已证」与 `Elab.dfns`。

= 待决问题

每个选项一个字母，全文不重复。推荐项标 ★。

#tbl(c-sem, (auto, 1fr, 1fr), ([问题], [选项], [理由]),
  [`∋` `inl` `inr` 放在哪], [★ A：留作 native 行。\ B：升为构造子（用户最初的目标列表）。\ C：连 `outl` `outr` 也降为行], [A：它们是没有子项的叶子，行的 `conv?` 已统一给出 `inl°` `inr°`；升为构造子要在约 14 个遍历各加三条子句，`convTm` 还得为它们写专门规则。B 的好处只是与 `outl` `outr` 对称。C 不行：`pairTest` `convProj` `uniPart` 自己构造并匹配 `outl` `outr`（规则的条件 2）],
  [`hylo`], [★ D：并入 `mu`，体有子节点时 on demand。\ E：保留构造子 `hylo`], [D：`den` 已相同；差别是运行策略，由项本身（`Tm.kids`）决定。代价：有环时由「立即报错」变为「跑到 `cap` 再报错」],
  [任意 object 上的序（`asc` 的定义需要它）], [★ F：序是定义，`lt ≜ dom(Λ(π₁ ∪ π₂) at(0) ∩ π₁) − dom(π₁ ∩ π₂)`，加 fused 行。\ G：native 行 `lt`，在所有 object 上。\ H：只在 atom 上；`asc` 保持无定义的 native 行], [F：`Λ` 的结果已按 `Obj.lt` 排序（`lamDen`，`Den.lean:244`），`at(0)` 读出最小者，所以序在语言里已经可定义，不需要新原语。待验证：atom 上 `Obj.lt`（`Rel/ObjOrder.lean:44`）与 `ltAt` 是否一致（浮点）；不一致则浮点 atom 的 `<` 是另一个 native 行。之后 `asc` 的定理 `ascDen = ⟦(dom(P) Λ(> P) length)°⟧` 仍是一条新证明],
  [常量的表示], [★ I：一个 `const` 与一张表（§5.1）。\ J：保留 `prim` 与 `call` 两个构造子，只删 `callCv` `own` `share`。\ K：绑定组不动], [I：行、定义、共享部分是同一概念，fused 行就是「两个字段都有」。J 是 I 的前九成工作（批次 B9），可以先停在 J],
  [`at`], [★ L：二元 native 行 `at : [β]×ν ⟶ β`。\ M：保留按数字 `k` 索引的一族（行表之外的特例）。\ N：定义 `at(k) ≜ (cons° π₂)ᵏ cons° π₁`，无行], [L：是关系，不带数字参数，也给出 q 的 `x i`。N 每个 `k` 要 `k+1` 次 kernel 调用，而 `Tab.atPos` 是一次],
  [`thin` 的含义], [★ O：保留名字，写明它是 map，并补定理 `thin(Q) ⊑ setify thinRel(Q)`（`Q` 传递时）。\ P：改名], [freyd 的 `thinRel`（`AOP/A8_1.lean:70`，`thinRel_pt`）是关系：任何压得住全体的子集都算。Rel 的 `thinDen` 取其中确定的一个。两者今天没有定理相连],
  [`var`（§5.3）], [S：去掉 `var`，递归只用组合子 `fold hylo star sim`，定义参数在 elaboration 时代入。\ ★ T：留 `var`；`d` 移出 `Tm`；是否改 PHOAS 另议], [§4.2 的表：10 处递归里 `SudokuPC` 的 `K`（两个文件）没有组合子可用，S 要么删掉该程序、要么为它加专用构造子。T 保持「任意单调体」这一个原语，`star` `hylo` 仍可作为定义与写法。PHOAS 不减少构造子，收益只是变量带类型，建议不做。此项由用户决定],
  [`dom` 行的 dem], [★ Q：`Prim.dem` 三值，`dom` 为 fused 行。\ R：`dom` 作为例外留作构造子], [Q 让规则没有例外；R 省掉批次 B3 的大部分，但 `dom` 明明有定义 `⟨𝟙,R⟩π₁`],
)

= 代码与架构文档不一致之处（汇总）

- `Tm.gap`、`compile`、`compile_sound`（§7 `:479`）不存在；现为 `Tm.gen` / `Tm.gen_sound` / `Tm.GenHyp`。
- §1 表漏 `foldr` `foldI` `callCv`；列了不存在的 `junc` `juncD`；`inl` `inr` 是行不是构造子。
- §7 `:494` 称 `flat` 是构造子；它已是行加定义。
- §4.6 称 `length` 的定理未证并提到 `Prim.dfn`；`Tm.dfnCut_den` 已证，字段叫 `Elab.dfns`。
- §4.5 称 `μ` 是 semi-naive；`Tab.mu` 是整体迭代。
- §7 `:497` 称 `Tm` 去掉 `d`、删 `Fn`；`Tm.var` 仍存 `d`，`GenK` 仍用 `Fn d A B`。
- `Tm.fv` 的注释写「40-constructor family」（`Tm.lean:209`）；实际 44 个。
- `Prim` 的文档注释称 fused 行「keyed in `Elab.dfns`」；六条带 `prelude :=` 的行不在 `dfns` 里，走的是 `useDef`，没有定理。
