#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// palette: one colour per layer, reused in diagrams, tables and headings
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let c-rs  = rgb("#b5541c")   // Rust
#let ink   = rgb("#222831")
#let soft(c) = c.lighten(88%)

#set document(title: "Rel dataframe 设计")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); Rel dataframe 设计 #h(1fr) master 69d5638 · 2026-11-18 ],
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

// striped table with a coloured header
#let tbl(color, cols, head, ..cells) = table(
  columns: cols, stroke: none, inset: (x: 6pt, y: 4.5pt),
  fill: (_, y) => if y == 0 { color } else if calc.even(y) { soft(color) } else { white },
  table.header(..head.map(h => text(fill: white, weight: "bold", font: "Noto Sans CJK SC", h))),
  ..cells, table.hline(stroke: 0.8pt + color))
#let card(color, title, body) = block(width: 100%, fill: soft(color), stroke: (left: 3pt + color),
  inset: 9pt, radius: (right: 4pt))[#text(weight: "bold", fill: color, font: "Noto Sans CJK SC", title) \ #body]

// ───────────────────────────── title
#align(center)[
  #text(24pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[Rel dataframe 设计] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[DataHaskell `dataframe` 与 polars 的运算，写成五个 kernel 上的关系代数程序] \
  #v(2pt) #text(9pt, fill: gray)[master 69d5638 · 2026-11-18]
]
#v(6pt)

#let bx(c, body) = (fill: soft(c), stroke: 1pt + c, corner-radius: 4pt, inset: 8pt)
#figure(
  diagram(spacing: (16mm, 12mm), node-stroke: 1pt, edge-stroke: 0.9pt, label-size: 8.5pt,
    node((0, 0), [dataframe 运算 \ #text(8pt)[`.rel` 定义]], ..bx(c-syn, none)),
    edge("-|>", [Elab]),
    node((1, 0), [*`Tm [C] [C']`* \ #text(8pt)[logical plan]], ..bx(c-syn, none)),
    edge("-|>", [改写定律]),
    node((2, 0), [*recipe* \ #text(8pt)[CODE、WHERE、…]], ..bx(c-sem, none)),
    edge("-|>", [`Plan`]),
    node((3, 0), [*5 个 kernel* \ #text(8pt)[`scan` `scatter` ┃ `gather` `asc` `distinct`]], ..bx(c-rs, none)),
  ),
  caption: [一个 frame 是位置对象 `I` 上的 tabulation，记作 `[C]`；`I` 只有长度 `n`，不存储。],
)

#tbl(c-syn, (auto, auto, 1fr), ([记号], [类型], [含义]),
  [`x`], [`[C]`], [一个 frame：tabulation `c : I ⟶ C`，`I` 是行位置 `0…n−1`（第 2 节）。`[C]` 是这个 map 的记号],
  [`S`], [`Schema`], [行的类型：带列名的列类型表；`S.obj` 是其积],
  [`a` `v`], [`col S "…"`], [一列：一个投影（`π₁` `π₂` 的复合）],
  [`k`], [`col S "…"`], [key 列（一个投影，或若干投影的 pair）],
  [`p`], [`C ⟶ C`], [谓词，写成 coreflexive],
  [`e`], [`C ⟶ V`], [一行之内的表达式],
  [`!`], [`A ⟶ 1`], [到 prelude 的终对象 `1` 的 `⊤`],
  [`F(R)`], [`[A] ⟶ [B]`], [后接 `R`：`c ↦ c ≫ R`，`I` 不变],
)

// ───────────────────────────── 0
// ───────────────────────────── 1
= 数据模型

== frame 的值

- frame 是 `Vals C n`（`Rel/Run/Core.lean:456`）：struct of arrays，`C = A₁×A₂` 时每个 atom 一个 `Arr t n`（`Core.lean:25`）。
  不新增类型。它表示的关系、行的编号与落盘方式在第 2 节。
- 一个运算是 `[C] ⟶ [C']`，与 Haskell 的 `DataFrame -> DataFrame` 一一对应。
- 值为关系（集合）的结果按既有约定存成 canonical 形式：`asc` 之后 `distinct`（`doc/rel-architecture.zh.typ` §4
  「allegory 运算 → kernel」与 §7 的 D2 canonical table；`doc/rel-kernels.md` §3 的 DICT、CODE）。本文引用，不另述。
- `take` `drop` `range` 只改 `lo`、`hi`，不复制任何列。

== schema 与列名

- 今天：`Obj.prod` 没有字段名，列名是程序里的定义（`price ≜ π₁ ≫ π₂`）；形状相同、列名不同的两个 frame 类型相同，`select "price"` 与按名 join 无法检查。
- 设计（与 DataHaskell `TypedDataFrame '[Column "price" Double, …]` 相同的做法）：`Schema := List (String × Obj)`；`Schema.obj : Schema → Obj` 是一个定义，
  按 `.d` 的列顺序给出嵌套 `prod`。frame 的项以 schema 为下标，`Tm S.obj B`。
- 列名访问：`col S "price" : S.obj ⟶ T` 当且仅当 `("price", T) ∈ S`，在 elaboration 时判定，否则报错并指出缺的列名。
  `select` `exclude` `rename` `derive` `join` 是 `Schema` 上的函数，给出两个 `S.obj` 之间的项。
- 为什么不加 `Obj` 构造子：`Schema.obj` 让表示等式按定义成立，kernel、存储、`rep`、canonical、`lam_sound` 都看不到新东西；
  新构造子要给每个对 `Obj` 的 match 加分支，而 P3/P4 正在重写这些 match。代价：字段类型相同、名字不同的两个 schema 有同一个 `Obj`，只有 schema 这一层区分它们。
- 对 F4 的影响：读文件要声明 schema，或在 elaboration 时读 `.d`；`.d` 就是 `Schema` 的落盘形式（D.7），同一个来源。
  wide pivot、`get_dummies` 只有在输出列被声明时才有类型。
- PLAN：D.11。`Schema` 层与其函数现在就在 master 上写，不等 P3；`.rel` 里的 `col "…"` 语法与带 schema 的 `input` / `output` 在 D.9。
#tbl(c-syn, (auto, auto, 1fr), ([dataframe / polars 类型], [Rel 一侧], [说明]),
  [`Bool`], [`u1`], [也是 `filter` 的 mask],
  [`Int8` … `Int64`], [`i8` `i16` `i32` `i64`], [],
  [`Word8`], [`u8`], [],
  [`Word16` … `Word64`], [无], [finding F9],
  [`Float` `Double`], [`f32` `f64`], [保序 code，NaN 也有位置],
  [`Char`], [`char`], [],
  [`Text`、Categorical], [`sym`], [排好序的字典（`arr char`），保序 id],
  [装箱的值], [`general`], [每个元素装箱],
  [`Day`], [`date`（`i32`）], [epoch 以来的天数；foR code 按整数有序（PLAN 6.9 第 1 步，`69d5638`）],
  [`UTCTime`], [`datetime`（`i64`）], [epoch 以来的纳秒，无时区；同上],
  [list 列（`collect`）], [`Obj.arr T`], [平铺 payload 加 `lo` `hi`],
  [`Maybe a`], [`A+1`], [见 1.4],
)

== 编码：只有 `foR`

唯一的编码是现有的 `Ext.Enc.foR`（`doc/rel-architecture.zh.typ`「剩下的唯一编码：foR」）。`coc` 不是第二种编码，
是写出和读入 `foR` 的 codec。

#tbl(c-run, (auto, 1fr), ([名字], [是什么]),
  [`foR`], [`Ext.Enc.foR md pk`（`Rel/Kernel/Value.lean`）：每 $2^"lg"$ 个元素一块，值是 base 加回绕的残差，残差按该块的宽度
    （0 到 64 位）LSB 优先打包；`lg` 每列一个。`enum` / ids 是 $b = 0$ 的 `foR`，`bits` 是 base 0 宽度 1，常量是宽度 0],
  [缓存], [`maxv`（谓词跳过整块）、`bsum` / `sumnul` / `sumn`（O(nblk) 求和）、`off`（块起点）。只服务速度，语义从不读，
    所以证明零成本],
  [codec `coc`], [Lean：`Coc.encode` / `Coc.encodeAt`（`Rel/Kernel/Coc.lean`）写 `foR`，kernel 经 `Rel.Kernel.foRWords` 读。
    Rust：`coc::Coc`（`crate/src/coc.rs`）是同一批字节的视图，kernel 经 `blocks.rs` 的 `Blocks::walk` / `load` 一块一块地读，
    compute-on-compression 在这一层发生],
)

- 对 dataframe 有用的三点，都来自缓存：`maxv` 与 base 就是 zone map，`filter` 可以整块跳过；`sum` 可以只读 `bsum`；
  排好序的列每块宽度很小。
- `Ext.Enc` 今天有 `bytes` `bits` `syms` `foR` `alp` `enum` `gen`。PLAN 6.11 之后只剩 `foR`，`alp` 作为 float 的 fast path
  挂在 `foR` 的元数据上，其余五个删除。
- `packed`（去掉缓存的 `foR`）已弃用。
- Lean `Coc.encode` 与 Rust 的宽度选择相同（并列取较窄），逐字节相等（`f0f9171`），gate 3 直接比较字节。

== null

#tbl(c-sem, (auto, auto, 1fr), ([读法], [第 3 行为 null], [结论]),
  [q 的哨兵值], [第 3 个元素是 `0N`], [带内表示；随 q 语义移出（PLAN R5、6.9）],
  [和类型 `v : C ⟶ V+1`], [第 3 个元素是 `inr(∗)`], [*采用*：每列都是全函数，`F(⟨a, v⟩)` 不丢行],
  [部分列 `v ≫ inl°`], [第 3 行没有像], [派生的读法：表达式里与 null 比较的行被 `filter` 去掉，和 polars 一致],
)

- `tot(R) = R ≫ inl ∪ (𝟙 − dom(R)) ≫ ! ≫ inr`：把部分的 `R : A ⟶ B` 变回全的 `A ⟶ B+1`（`R` 有值取值，否则 null）。
- 布局问题：今天 `Vals (.sum V 1) n` 是 tag 列、*每行一个位置*、以及压紧的非 null payload。那个位置列违反「位置不存储」；
  `V+1` 需要就地布局（tag 列加等长的值列）。这是 `Vals` 在 `.sum A 1` 处的改动，不是新类型（finding F5）。

// ───────────────────────────── 2
= 存储与顺序

一个实例：frame `[(A,1),(B,2),(A,1)]` 是 `a : I ⟶ K`、`b : I ⟶ N`，`I = {0,1,2}`：`0 {a} A`，`0 {b} 1`，`2 {a} A`，`2 {b} 1`。
第 0 行与第 2 行是 `I` 的不同元素，所以是两行；`a° ≫ b` 只有 `A ↦ 1`、`B ↦ 2` 两对。

- *语义是集合。* 没有 bag，也没有 list 对象。frame 是一个 tabulation：每列是 `I` 出发的 map。以 `I` 为 key 它已经是
  `asc`、`distinct` 的，不需要排序。`a° ≫ b : A ⟶ B`（排序并去重）只在运算的规格需要它时才形成：join、`distinct`、成员判断。
- *顺序是位置的顺序。* 用户的排序是一个置换 `I ⟶ I`，由 `gather` 施加。规则：结果是新 frame 的运算必须说明它怎样给新的 `I` 编号。

#tbl(c-sem, (auto, 1fr), ([运算的类别], [新的 I]),
  [`F(R)`：`select` `derive` `apply` `impute`], [不变],
  [`filter`、`distinct`、semi / anti join、`sample`], [保留位置的集合的 `enum`：按原位置顺序重新编号],
  [`sortBy`、`shuffle`], [同一个 `I`，经置换],
  [`take` `drop` `range`], [`I` 的一个区间，平移到 0],
  [`cat`、`union`], [`I + J`：左边的位置在前],
  [join、`over`、`melt`], [匹配对 `(i, j)` 的集合的 `enum`，按 `(i, j)` 的字典序],
  [`groupBy`、`aggregate`、pivot], [出现的 key 的集合的 `enum`，按 key 的顺序；每组内部是原位置的 `enum`],
)

- `enum`（位置的集合 ↦ 按位置顺序的 list）是顺序进入的唯一位置（`CLAUDE.md`）。它今天没有声明。它不作为位置数组算出来，
  只作用到列上：mask 的 `scan(add)` 给出目标位置，每列一次 `scatter`（recipe WHERE）。
- *`I` 是虚的。* 它只有 `n`：不落盘，在内存里也不物化（存成 `foR` 每个 1024 块约 10 bit / 行）。
  key 是一个种类「位置 `0…n−1`」，kernel 把它当恒等处理：`gather`、`scatter` 的下标或 payload 是这个 key 时，kernel 读自己的循环变量。
  它不是新的存储，也不是 `Enc.gen`（6.11 删除）。实现是 `Enc.pos`（PLAN 6.13a / D.4），进行中；验收：`til n` 读成 `pos`，不出现 `gather(invert(p), p)`。
  会用到 `til n` 数组的运算列在 F1。
- *落盘（q / kdb 的方式）。* 目录 = 表；文件 = 列，是一个 mmap 的 `foR` `Enc`，没有序列化（`CLAUDE.md` 的 Goal）；
  `.d` 文件 = `Schema` 的列顺序；`sym` 列共用一个字典文件。`.d`、共用字典、符号 key 三项是新的，不在 PLAN 里。

// ───────────────────────────── 3
= 运算

== 辅助定义

```
len(n)      = dom(length ≫ n°)                                    长度为 n 的 list（coreflexive），n : 1 ⟶ N
take(n)     = prefix ≫ len(n)          takeLast(n) = suffix ≫ len(n)
drop(n)     = cat° ≫ dom(π₁ ≫ len(n)) ≫ π₂                        x = y ⧺ z 且 |y| = n，取 z
strₗ        : A×[B] ⟶ [A×B]                                       把 a 配给每个元素；一个 foldI，carrier 带着 a
strᵣ        : [A]×B ⟶ [A×B]                                       对称
selᴷ(k)     : K×[C] ⟶ [C]    = strₗ ≫ filter(cor(k°)) ≫ F(π₂)     key 等于 κ 的行，顺序不变
groups(k)   : [C] ⟶ K×[C]    = ⟨∋ ≫ k, 𝟙⟩ ≫ ⟨π₁, selᴷ(k)⟩         每个出现的 key 与它的子 list
M           : C×E ⟶ C×E      = cor(k ≫ h°)                        key 相等的行对；k : C ⟶ K，h : E ⟶ K
cand        : C×[E] ⟶ [C×E]  = strₗ ≫ filter(M)                   左表一行在右表中的全部匹配
hit         : C×[E] ⟶ C×[E]  = dom(cand ≫ ∋)                      至少有一个匹配
lastw(w)    : [A] ⟶ [A]      = Λ(suffix ≫ dom(length ≫ ≤ ≫ w°)) ≫ est(length ≫ ≥ ≫ length°)   最长的、不超过 w 的后缀
```

- 一个实例：`groups(k)` 在 `x = [(A,1),(B,2),(A,3)]` 上：`x {⟨∋ ≫ k, 𝟙⟩} (A, x) {⟨π₁, selᴷ(k)⟩} (A, [(A,1),(A,3)])`；
  另一个像是 `(B, [(B,2)])`。每个 key 一个像；子 list 是 `x` 的一段（`filter` 保持顺序与重复）。

== DataHaskell `dataframe` 的导出函数

函数表取自 `DataFrame.hs` 的导出与 `DataFrame.Operations.*`、`DataFrame.Functions`（github.com/DataHaskell/dataframe，`main`）。
kernel 一栏：S = `scan`，T = `scatter`，G = `gather`，A = `asc`，D = `distinct`；"无" = 只改投影或 `lo`/`hi`。

#tbl(c-syn, (auto, 1.55fr, auto, 1fr), ([Haskell 函数], [Rel 复合], [kernel], [说明 / finding]),
  [`select` `exclude` `selectBy`], [`F(⟨col S "a", col S "b"⟩)`], [无], [列名在 elaboration 时检查；选 `Vals` 的子树],
  [`rename` `renameMany`], [`F(col S "c")`，换名字], [无], [列名在 elaboration 时检查],
  [`derive` `deriveMany` `deriveWithExpr` `insert*` `cloneColumn`], [`F(⟨𝟙, e(col S "c")⟩)`], [S], [列名在 elaboration 时检查；map：每行一个 segment 的 `scan`],
  [`apply` `applyMany` `applyInt` `applyDouble` `safeApply` `applyAtIndex`], [`F(⟨a ≫ g, b⟩)`], [S],
    [`g` 必须是 `Op` 的复合；任意 Haskell 函数没有对应的项（F12）],
  [`applyWhere`], [`F(p ≫ ⟨a ≫ g, b⟩ ∪ (𝟙 − p))`], [S], [两个 mask 分支的并],
  [`filter` `filterWhere` `filterBy`], [`filter(p)`，如 `p = dom(a ≫ < ∩ b)`], [S T],
    [mask 的前缀计数是 `scatter` 的目标位置：瞬时位置向量（F1）],
  [`filterJust` `filterAllJust`], [`filter(dom(v ≫ inl°))`], [S T], [],
  [`filterNothing` `filterAllNothing`], [`filter(dom(v ≫ inr°))`], [S T], [],
  [`take` `drop` `takeLast` `dropLast` `range` `byIndexRange` `cube`], [`take(n)`、`drop(n)`、`takeLast(n)`], [无], [只改 `lo`、`hi`],
  [`selectRows`], [`F(at)`，下标来自数据], [G], [`at(i)` 只接受常量 `i`；显式位置是 API 的输入（F1）],
  [`sortBy`], [`sort(Q)`，`Q = a ≫ ≤ ≫ a°`], [A G],
    [prelude 的 `sort(Q) = perm ≫ ordered(Q)`；稳定排序是它的一个 refinement（F16）；带着其它列走要 `asc` 的置换（F1）],
  [`topBy`], [`sort(Q) ≫ take(n)`], [A G], [定律：等于 `est` 的 n 次迭代；待证],
  [`distinct`], [`distinct`], [A D G], [`prims` 的行：保留第一次出现],
  [`groupBy`], [`Λ(groups(k)) : [C] ⟶ [K×[C]]`], [A D S T], [recipe CODE；每组是 `lo`/`hi` 段],
  [`aggregate`], [`F(𝟙 × (F(v) ≫ f))`], [S G], [recipe SEGFOLD：分段 `scan`，取每段最后一行],
  [`sum` `mean` `count` `countAll` `minimum` `maximum` `reduce`], [`f = sum`、`length`、`est(≥)`、`⦇e, ⊕⦈`；`mean = ⟨sum, length⟩ ≫ fdiv`], [S], [`Op` 的 fold],
  [`variance` `stddev` `skewness` `correlation` `zScore`], [若干 fold 的 pair 再做算术], [S], [],
  [`median` `percentile` `genericPercentile` `interQuartileRange`], [`asc ≫ cat° ≫ dom(⟨π₁ ≫ length, π₂ ≫ length⟩ ≫ r) ≫ π₂ ≫ head`], [A],
    [`r` 是两段长度之比；位置由 `cat°` 给出，不是下标],
  [`countDistinct` `mode`], [`F(v) ≫ distinct ≫ length`；`mode` 再接 `est`], [A D S], [],
  [`collect`], [`F(v)`（每组的 list 本身）], [无], [结果列的类型是 `Obj.arr V`],
  [`firstOrNothing` `lastOrNothing`], [`tot(head)`、`tot(last)`], [G], [每段的第一 / 最后一个位置],
  [`topK` `bottomK` `kExtremes`], [`asc ≫ takeLast(n)`], [A], [],
  [`valueCounts` `valueProportions` `frequencies`], [`groupBy` + `aggregate`，`f = length`], [A D S T], [],
  [`summarize` `describeColumns` `nulls`], [固定的一组聚合的 pair], [S A], [输出的列由 schema 决定，静态可知],
  [`innerJoin` `join` `joinOn`], [`strᵣ ≫ F(cand(col S "k")) ≫ concat`], [全部], [列名在 elaboration 时检查；recipe CODE + EXPAND；匹配的位置对必须物化（F1）；字面读是二次的（F3）],
  [`leftJoin`], [`strᵣ ≫ F(hit ≫ cand ≫ F(𝟙×inl) ∪ (𝟙 − hit) ≫ π₁ ≫ ⟨𝟙, ! ≫ inr⟩ ≫ τ) ≫ concat`], [全部], [右侧整行为 null（`E+1`）；F5],
  [`rightJoin`], [`leftJoin` 交换两侧], [全部], [],
  [`fullOuterJoin`], [`leftJoin` 之后 `cat` 上右表未匹配的行], [全部], [两侧都是和类型],
  [`union`], [`cat ≫ distinct`], [S T A D], [],
  [`intersect`], [`strᵣ ≫ filter(hit) ≫ F(π₁) ≫ distinct`，`k = h = 𝟙`], [A S T D], [recipe LOOKUP],
  [`difference` `symmetricDifference`], [`strᵣ ≫ filter(𝟙 − hit) ≫ F(π₁) ≫ distinct`], [A S T D], [],
  [`<>`（行拼接）], [`cat`], [S T], [recipe CONCAT；`sym` 列字典不同时再做 DICT + CODE],
  [`|||`（列拼接）], [`zip`], [无], [两个 `Vals` 并排；长度不等时无像],
  [`impute` `imputeWith` `fromMaybe` `castWithDefault`], [`F(v ≫ [𝟙, ! ≫ c])`], [S], [`c : 1 ⟶ V`；`imputeWith` 的 `c` 是一个聚合],
  [`toMaybe` `isJust` `isNothing` `isNull` `fromJust` `whenPresent`], [`inl`、`dom(inl°)`、`dom(inr°)`、`inl°`、`[g ≫ inl, inr]`], [S], [],
  [`recode` `recodeWithDefault`], [`F(v ≫ T)`，`T` 是字面量表；带缺省用 `tot`], [A S T G], [recipe LOOKUP],
  [`lift` `lift2` `nullLift` `bind`], [无], [—], [宿主语言的任意函数没有项（F12）],
  [`cast` `toDouble` `div` `mod` `pow` `relu` `eq` `lt` `and` `or` `not` …], [`Op` 的 constructor], [S], [整数 / 浮点转换的 `Op` 待加；`arith` 今天只在 `i64`（F9）],
  [`over`], [`⟨𝟙, 𝟙⟩ ≫ strᵣ ≫ F(⟨π₁, (k × 𝟙) ≫ selᴷ(k) ≫ F(v) ≫ f⟩)`], [全部], [每行带上它那一组的聚合；CODE + SEGFOLD + 按组号 `gather`],
  [`contains` `length` `splitOn` `match` `matchAll`], [`contains(s) = dom(suffix ≫ prefix ≫ s)`], [—], [字符串：F8],
  [`parseDate` `daysBetween`], [`date` 上的整数减法；`parseDate` 是字符串解析], [S], [F8、F10],
  [`sample` `shuffle` `randomSplit` `kFolds` `stratifiedSample` `mkRandom`], [`subseq ≫ len(n)`；`perm`], [S G], [规格有多个像，PRNG 选一个；下标向量是显式位置（F13）],
  [`fromList` `fromRows` `fromColumns` `fromUnboxedVector` `empty`], [字面量 `Tm.val`，或 `zip`], [无], [],
  [`columnAsVector` `columnAsList` `toList` `toRowList` `to*Matrix`], [`F(col S "c")`，在输出边界读出], [无], [列名在 elaboration 时检查],
  [`dimensions` `nRows` `nColumns` `columnNames`], [`length`；其余读 `Obj`], [无], [],
  [`readCsv` `readTsv` `readParquet` `readJSON` `writeCsv` `writeParquet`], [无], [—], [IO 在代数之外；schema 推断见 F4、F11],
  [`scanCsv` `scanParquet` `fromDataFrame` `run`（Lazy）], [`input` 声明、`rel_program`、`output`], [—], [第 5 节],
  [`fold`、`display`、Plot、`DecisionTree`、`KMeans` 等], [不在本设计范围], [—], [宿主层的工具与模型库],
)

== polars 多出来的运算

#tbl(c-sem, (auto, 1.55fr, auto, 1fr), ([polars], [Rel 复合], [kernel], [说明 / finding]),
  [semi / anti join], [`strᵣ ≫ filter(hit) ≫ F(π₁)`；anti 用 `𝟙 − hit`], [A S T G], [LOOKUP、map、WHERE],
  [cross join], [`strᵣ ≫ F(strₗ) ≫ concat`], [S T G], [EXPAND],
  [asof join], [`strᵣ ≫ F(⟨π₁, tot(strₗ ≫ filter(M≤) ≫ last ≫ π₂)⟩)`], [A S T G],
    [`M≤ = cor(⟨k,t⟩ ≫ (𝟙 × ≥) ≫ ⟨h,u⟩°)`，右表按时间有序；LOOKUP 带 `≤`，结果写回左表原位要位置（F1）],
  [`cum_sum` 等], [`inits ≫ tail ≫ F(F(v) ≫ ⦇e, ⊕⦈)`], [S], [由 scan lemma 等于 `⊕` 的前缀 `scan`],
  [`shift(1)`], [`⟨! ≫ inr ≫ τ, init ≫ F(inl)⟩ ≫ cat`], [S T], [前面接一个 null，去掉最后一个],
  [`diff`], [`⟨tail, init⟩ ≫ zip ≫ F(minus)`], [S], [两个切片的 map，不复制],
  [`rolling(w)`], [`inits ≫ tail ≫ F(lastw(w) ≫ F(v) ≫ f)`], [S G], [recipe WINDOW（F1）],
  [`forward_fill`], [`⦇nil, step⦈`，carrier 带着最后一个有效值], [S], [`scan(last)`，在有效行开新段],
  [`melt`], [`⟨F(⟨! ≫ x, a⟩), F(⟨! ≫ y, b⟩)⟩ ≫ cat : [C] ⟶ [P×V]`], [S T], [CONCAT；各列要同类型],
  [pivot（long）], [`groupBy(⟨k, q⟩)` + `aggregate`], [A D S T], [long 形式就是 key 为 `K×P` 的 frame],
  [pivot（wide）], [`groupBy(k) ≫ F(𝟙 × ⟨tot(∋ ≫ dom(q ≫ x°) ≫ v), …⟩)`], [A D S T G], [只对声明的 `obj P = {x, y}` 可写（F4）],
)

== recipe

沿用 `doc/rel-kernels.md` §3 的八个（CODE、DICT、RANK、CONCAT、LOOKUP、EXPAND、WHERE、SEGFOLD），这里新增两个，都是五个 kernel 的复合：

- WINDOW：`f` 可逆（`sum`、`count`）时，前缀 `scan(f)` 得 `s`，再 `⟨drop(w), take(n−w)⟩ ≫ zip ≫ F(minus)`：
  位置 `i − w` 处的值是同一列的一个切片，不用 `gather`。
  `min` / `max`：每 `w` 行一段做两次分段 `scan`，其中一次从后往前，再 map `scan(min)`（van Herk）。
- WHERE 的无下标形式：mask 的 `scan(add)` 给出每个保留行的目标位置，每列一次 `scatter` 写过去，不经过 `gather`。

// ───────────────────────────── 3
= kernel 集合

目标是 `doc/rel-architecture.zh.typ` §4 的五个 kernel。dataframe 库不新增 kernel。

#tbl(c-rs, (auto, auto, 1.3fr, 1fr), ([kernel], [层], [形状（读 foR，写 foR）], [状态（master 69d5638）]),
  [`scan`], [原语], [`Op` 的分段前缀折叠；含 map 与 fold], [有：`Kernel.kscan`，`qlean_k_scan`（6.4）。答 `.foR (Coc.encode 8 …)`；
    布尔结果答 `.bits`（F17）],
  [`scatter`], [原语], [`out[ix[i]] = e[i]`；`ix[i] ≥ n` 是错误], [`qlean_k_scatter`（6.5）],
  [`gather`], [优化], [`out[i] = e[ix[i]]`，带 fill], [`qlean_k_gather`（6.6，`23b65e0`，定理 `raw_kgather`）],
  [`asc`], [优化], [按若干列稳定排序：排好的值 + 置换], [`qlean_k_asc`（`178da18`）],
  [`distinct`], [优化], [有序输入上每段相等行的第一个位置], [`qlean_k_distinct`（`d1e6ff6`）],
)

五个 kernel 都在 master 上，直接在 foR 块上计算（6.10，`2b042fd`）。

- 计数：*5 个 kernel*（2 个原语，3 个由定理等于原语复合的优化）。另有 4 个 R4 runtime export
  （`stop`、`coc_encode`、`coc_decode`、`own_write`），不是 kernel。
- `crate/RELK.txt` 其余的旧导出怎样归到这五个，见 `doc/rel-kernels.md` §3，这里不重列。
- *融合准入规则。* 融合 kernel 只在四条都成立时加入：Lean body 就是那个复合项；证明了「融合 = 复合」；有第二个真实程序
  需要它并有测量；它由 plan 改写引入，程序与库定义不写它的名字。预计最先来的：hash 求组号（CODE）、等值 join（CODE + EXPAND）、
  map 链（`F(R) ≫ F(S) = F(R ≫ S)`）。
- 第 3 节没有哪个运算需要第六个 kernel。需要补的都不是 kernel：`Op` 的 constructor（整数 / 浮点互转、`fround`、
  `sample` 用的 PRNG 步）；一个映射 column 目录的 runtime export（`own_write` 的逆，决定 G）；recipe WINDOW。

// ───────────────────────────── 4
= Lazy plan

#tbl(c-syn, (auto, 1fr), ([polars 与 DataFrame.Lazy], [Rel]),
  [`LazyFrame` 的方法链], [`rel_program` 中的一个定义],
  [logical plan], [`Tm A B d`（`Rel/Run/Lang/Tm.lean:15`）],
  [schema 解析、类型提升], [`Elab`：`Tm` 的 `Obj` 下标；没有隐式提升],
  [optimiser], [一个 `Tm → Tm` 的 pass，配 `(opt t).den ρ = t.den ρ`；没有实现],
  [运行时的 predicate pushdown], [demand 位 `d` 与 `Known.dom`；块一级还有 `foR` 的 base / max],
  [公共子 plan], [`Tm.share`（`Expand.share`）],
  [physical plan], [`Plan`（`Rel/Run/Lang/Plan.lean:170`）：`funs`、`globals`、`main`],
  [executor], [Lean 中的 `Plan.run`；`relc` 把它印成 C（`Rel/Lang/EmitC.lean`），`rel-native` 链接 `librelk.a`],
  [`scanCsv` `scanParquet`], [`input` 声明：已决定（G），没有实现],
  [`run` / `collect`], [`output x to dir`（`Plan.output`、`planOf`）：语言里还没有这个声明],
)

- 现状：`compile`、`Tm.plan`（`Rel/Run/Lang/Compile.lean:236`、`:239`）在 Lean 里经 `Gen` / `Alg` 运行每个 `Tm` 节点；
  `compile_sound`（`Rel/Lang/CompileSpec.lean:238`）覆盖 `Tm.gap = none` 的节点（`Rel/Lang/Rows.lean:111`）。
  `Λ`、`asc`、`foldI`、`hylo` 今天都是 gap，而 `groupBy`、`strₗ` 正好用到它们。
- native 路径更窄：`Plan.ofTm`（`Plan.lean:333`）只构造 `val`、`conv`、`share`；`arithB`（`:397`）、`groupIdsF`（`:362`）
  是仅有的 builder；`Plan.abi`（`EmitC.lean:16`）列的 12 个符号都是旧导出。

== 定律充当 optimiser

一个实例，projection pushdown：`derive e` 之后 `select a`：`F(⟨𝟙, e⟩) ≫ F(π₁ ≫ a) = F(⟨𝟙, e⟩ ≫ π₁ ≫ a) = F(dom(e) ≫ a) = F(a)`。
第一步是 functor 律，第二步是 `⟨R, S⟩ ≫ π₁ = dom(S) ≫ R`，第三步要求 `e` 是全的（1.4 保证）。列 `e` 不被计算。

#tbl(c-sem, (auto, 1.6fr, auto), ([优化], [定律], [状态]),
  [projection pushdown], [`⟨R, S⟩ ≫ π₁ = dom(S) ≫ R`；`S` 全时 `dom(S) = 𝟙`], [待陈述],
  [表达式融合], [`F(R) ≫ F(S) = F(R ≫ S)`], [待陈述（`E` 的版本是 prelude 的 `Ecomp`）],
  [predicate pushdown], [`F(R) ≫ filter(p) = filter(dom(R ≫ p)) ≫ F(R)`；`cand` 中 `p` 移到一侧], [待证],
  [group 走排序], [`Λ(groups(k))` = 按 `k` 稳定排序后在 key 变化处切段], [待证；fold 融合],
  [join 走排序], [`strᵣ ≫ F(cand) ≫ concat` = 两侧按 key 排序后逐段展开], [待证],
  [cumulative 是一次 scan], [`inits ≫ F(⦇e, ⊕⦈)` = `⊕` 的前缀 scan], [B&dM scan lemma；`Programs/Mss` 是一例],
  [聚合不看顺序], [`perm ≫ ⦇e, ⊕⦈ = ⦇e, ⊕⦈`，`⊕` 结合且交换], [待证；`Op.assoc`],
  [融合 kernel], [准入规则的「pattern = 融合」], [每个 kernel 一条],
)

- 这里有两种定律，只有一种是现成的。`Rel/CRel*.lean`、`Rel/Rep*.lean`（约 270 与 260 条：`rep_pair`、`rep_filterC`、`rep_asc` …）
  是表示定律：可执行的算子算出了那个关系。它们为 physical plan 作证，和 `compile_sound` 一样。
- optimiser 要的是项与项之间的代数定律 `t₁.den ρ = t₂.den ρ`（`Tm.den`，`Rel/Lang/Den.lean:300`）。它们在 `Rel/Core`
  与 prelude 的 `theorem` 声明里（`absorption`、`Eunion`、`Ecomp`、`estMap`，经 `rel_aop` 对 freyd 证明）。
  index 里还没有 pair 投影律与 map 融合律；上表标「待证」的四条是真正的工作量，用 fold / hylo 的融合律来证。
- 没有的：pass 本身、代价模型、统计信息。定律说两个 plan 相等，不说哪个便宜（F7）。

// ───────────────────────────── 5
= Findings

写不出来、或只能别扭地写出来的运算。

- *F1 `I` 是虚的，所以下面这些原本要 `til n` 数组的地方都要改写。* 每一处都让 kernel 把位置读成循环变量：
  - `asc` 的置换（`sortBy`、`groupBy` 的 CODE、LOOKUP、asof）：置换是「按 key 排序的 `til n`」。`asc` kernel 以恒等 key 为 payload，
    直接产出置换，不接受一个 `til n` 输入。
  - RANK（置换的逆，`scatter(perm, til n)`）：`scatter` 的 payload 是恒等 key。
  - `cat` / `melt` 的 CONCAT（目标位置 `off + 0…n−1`）：按块追加，属于 codec，不调用 `scatter`。
  - `rolling`、`shift`、`diff`（位置 `i ± w`）：同一列的切片，只改 `lo`、`hi`（recipe WINDOW）。
  - van Herk 里反转的列（下标 `n−1−i`）：`scan` 要一个方向参数；今天的 `kscan` 没有，这是 `scan` 的一处扩展，不是新 kernel。
  - `enum` 本身作为位置的 list（q 的 `where`）：不形成；只有它作用到列上的结果（见第 2 节）。
  下标向量如果是由数据算出来的，就不是 `I`，而是普通的值列，照常存在：mask 的前缀计数、`asc` 产出的置换、join 的匹配位置对（EXPAND）、
  `selectRows` 的输入、PRNG 的输出。主表标 F1 的行指的是这一类；它们是 recipe 内部的瞬时值，不落盘。
- *F2 `Λ` 的 canonical 形式还没有实现。* `groupBy` 的 `Λ(groups(k))` 依赖「集合存成 `asc` 后 `distinct` 的数组」这个约定；
  `Tm.gap`（`Rel/Lang/Rows.lean:111`）今天对 `Λ` `E` `thin` 报的正是它（D2 canonical table，`doc/rel-denotation-design.md` §7.1），
  `asc`、`setify` 两行也缺定律（`rowGaps`）。
- *F3 规格按字面读是二次的。* `groups(k)` 对每个 key 做一次 `filter`，`strᵣ ≫ F(cand)` 对每个左行扫一遍右表，
  `over`、`rolling` 同理。它们靠第 5 节「待证」的四条定律才线性地运行；在定律证出之前，native builder 对这些 pattern 的
  翻译没有证明，要由 `Tm.gap` 报出来。另外 `strₗ`、`strᵣ`、带参数的 `filter` 不在 `prims` 里，要用 `foldI` 写，而 `foldI` 今天是 gap。
- *F4 依赖数据的 schema 无法给出类型。* wide pivot、`get_dummies`、读文件时推断 schema：结果的 `Obj` 要读了值才知道，
  而 `Tm A B` 在 elaboration 时固定 `B`。wide pivot 只对声明的有限 `obj P` 可写；long 形式是忠实的那个。
- *F5 null。* 布局问题见 1.4，outer join 的两支见主表 `leftJoin`。另外 null 上的布尔运算（Kleene `or`）要用 `[R, S]` 逐情况写。
- *F6 没有 hash。* `groupBy`、join、`distinct` 都基于排序。窄的 `foR` code 上 radix `asc` 是线性的；宽 key 或高基数时
  polars 的 hash 表应当更快。stage 1 测量；hash 形式是第一批融合候选，它们不保持稳定顺序，定理只能到「组内相差一个置换」。
- *F7 没有代价模型。* join 顺序、build 侧的选择需要统计信息。
- *F8 字符串别扭。* `contains` 的规格（主表）按字面运行对串长是二次的；线性搜索是一个融合 kernel。
  正则是「步骤为转移表」的 fold，把正则编译成表在语言之外。两者都只在 `sym` 字典上做一次。
- *F9 atom 覆盖。* 没有 `u8` 以上的无符号整数，没有 `i128`。`Tm.arith`、`leq`、`lt` 只在 `i64` 上并带一个数的 universe；
  dataframe 需要它们在每个有序 atom 上。
- *F10 时间类型。* `date`、`datetime` 是整数 code，没有时区。日历运算（取月份、截断到月）是整数算术加上与日历表的 join。
- *F11 IO 在代数之外。* CSV、Parquet、JSON 的解析不是列上的关系，留作 runtime export。
- *F12 宿主函数。* `lift`、`lift2`、`apply`、`bind` 接受任意 Haskell 函数；Rel 只有 `Op` 的有限集合及其复合。
  这也是 polars 表达式（不含 `map_elements`）同样的限制。
- *F13 抽样。* `sample(n)` 是有多个像的关系（任意 n 行），实现用 PRNG 选一个，是规格的 refinement，不是相等。
- *F14 整列执行。* kernel 读写整列。polars 的 streaming 引擎按 morsel 工作并可落盘；`lazy` / `Known` 传递的是 demand，不是批。
- *F15 浮点 `sum` 是顺序的。* `Op.assoc fadd = false`，一段之内按顺序折叠。组与组并行，一个大组不并行。
- *F16 稳定排序不是规格。* `sort(Q) = perm ≫ ordered(Q)` 在并列时有多个像；`asc` kernel 的稳定结果是其中之一。
  「保持原顺序」本身要位置才能陈述，所以只作为实现的性质记录。
- *F17 `foR` 的布尔列不统一。* `Enc.WF` 不接受布尔类型的 `foR`，所以 `scan` 的布尔结果答 `.bits`；`filter` 的 mask
  因此是第二种形式。进行中（D.5）：布尔列成为 `u1` foR，经 `Kernel.boolBits` 读，`Enc.bits` 将删除。
- *F-a `groups(k)` 今天写不出。* `strₗ` 不在 prims（报错 `unknown name 'str'`），带 key 的 `foldI` 是 gap。可运行的绕法：carrier 带 key 的左 fold，
  按 K 的整个 universe 各 seed 一次，要求 K 是声明过的有限对象，代价 |K|×n。→ D.8；rel-lazy `d72cf71` 已把 `groups(k)`、`filter(p)` 写成复合（不加 Tm 节点），
  并有 canonical 元素对象的 `lam_sound`。
- *F-b `filter(p)` 的形态。* 进入 Tm 时是 prelude 的 fold 展开式，recipe 要按 fold 结构匹配。→ D.8。
- *F-c 已修（`ee84ad8`）。* Elab 的 `Row` 改名 `LiftRow`，运行程序的模块可以 import `Rel.Lang.Rows`、调用 `Tm.gap`。
- *F-d 排序的 CODE 物化 `til n`。* 基于排序的 CODE 物化了 `til n`（`gather(invert(p), p)`）。→ D.4 的验收条件。
- *F-e 缺 export 指令。* 没有 plan 指令把算出的 buffer 交给 `qlean_own_write` 的 parts，也没有把 size 寄存器变成单元素 buffer。→ D.7。

// ───────────────────────────── 6
= 分阶段计划

每个阶段以 `CLAUDE.md` 的三个 gate 通过结束，并把新的 finding 追加到第 6 节。

#tbl(c-run, (auto, 1.2fr, 1fr, 1fr), ([阶段], [交付], [新代码], [PLAN / 状态]),
  [1], [两列上的 `filter` + `groupBy` + `sum`，经 `rel-native` 跑通], [`Plan.ofTm` 的分支；不加 kernel], [1a 绕法可运行，1b 完成，1c 等 D.7],
  [2], [从文件读 frame；每个 atom 上的算术], [`input` / `output` 声明、映射 column 目录的 export、`Op`], [D.7、D.9、D.3],
  [3], [`sortBy`、`distinct`、inner / semi / anti join，全部在五个 kernel 上], [RANK、LOOKUP、EXPAND 的 builder], [kernel 已齐],
  [4], [null 为 `V+1`（就地布局）；left / outer / asof join；`impute`], [`tot`、`Vals` 在 `.sum A 1` 处的布局], [—],
  [5], [cumulative、`shift`、`rolling`、`cat`、`melt`、long pivot], [WINDOW], [D.6],
  [6], [optimiser pass 与第 5 节「待证」的定律], [`opt : Tm → Tm` 及其 `den` 定理], [D.8],
  [7], [第一批融合 kernel，经融合准入规则], [按测量], [—],
  [8], [字符串、时间], [按 F8、F10], [D.3（date/datetime 已加）],
)

rel 的 D 块：D.1 asc/distinct 已完成；D.2 宽度并列已完成；D.3 atom 第 1 步已完成（`69d5638`）；D.4 虚拟 I；D.5 布尔 foR；D.6 scan 方向；D.7 mmap export + F-e；D.8 F2/foldI/hylo/F-a/F-b；D.9 input/output；D.10 已完成；D.11 Schema。

阶段 1（最小的端到端切片）：

- 程序：`out : [K×N] ⟶ [K×N] ≜ filter(dom(π₂ ≫ big)) ≫ Λ(groups(π₁)) ≫ F(𝟙 × (F(π₂) ≫ sum))`，输入是一个两列的字面量 frame。
- 1a：原写法被拒（`unknown name 'str'`），`frame` 绕法可运行，`#guard` 结果 `{(∗, (A, 13) (B, 10))}` 与手算一致。
- 1b：用现有 kernel 写出 `whereB`（WHERE）与 `groupSumB`（`grade` 稳定排序 + 相邻比较分段；一次前缀和 `scan`，段尾减段首），
  `Plan.run` 与 Lean 的指称逐字节相等，`Plan.ofTm` 未扩展（F-a、F-b）。
- 1c：卡在 F-e。
- 1d：同一个 plan 在从 column 目录读入的 10⁷ 行上对 polars 计时；这是 F6 要的测量，它决定阶段 7 是否从 hash 分组开始。
