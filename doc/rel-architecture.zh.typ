#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// palette: one colour per layer, reused in diagrams, tables and headings
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let c-rs  = rgb("#b5541c")   // Rust
#let ink   = rgb("#222831")
#let soft(c) = c.lighten(88%)

#set document(title: "Rel 架构")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); Rel 架构 #h(1fr) master 059f46c · 2026-11-18 ],
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
  #text(24pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[Rel 架构] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[从 allegory 语法，到语义映射，到最小 kernel] \
  #v(2pt) #text(9pt, fill: gray)[master 059f46c · 2026-11-18]
]
#v(6pt)

// ───────────────────────────── overview diagram
#let bx(c, body) = (fill: soft(c), stroke: 1pt + c, corner-radius: 4pt, inset: 8pt)
#figure(
  diagram(spacing: (18mm, 14mm), node-stroke: 1pt, edge-stroke: 0.9pt, label-size: 8.5pt,
    node((0, 0), [`.rel` 源码], fill: luma(235), stroke: gray, corner-radius: 4pt),
    edge("-|>", [Parse / Elab]),
    node((1, 0), [*`Tm A B`* \ #text(8pt)[程序（语法树）]], ..bx(c-syn, none)),
    edge("-|>", [`compile`], label-side: left),
    node((3, 0), [*`Rel A B`* \ #text(8pt)[`tab` 有限表 ┃ `lazy` 等边界]], ..bx(c-run, none)),
    edge((1, 0), (2, 1), "-|>", [`⟦−⟧ρ`], label-side: right),
    edge((3, 0), (2, 1), "-|>", [`rep`], label-side: left),
    node((2, 1), [*`Core.Rel A.El B.El`* \ #text(8pt)[语义：谓词]], ..bx(c-sem, none)),
    node((4, 0), [*Rust `relk`* \ #text(8pt)[5 个 kernel]], ..bx(c-rs, none)),
    edge((3, 0), (4, 0), "<|-|>", stroke: c-rs, [`@[extern]`], label-side: left),
  ),
  caption: [#text(fill: c-syn)[程序] 与 #text(fill: c-run)[值] 映到同一个 #text(fill: c-sem)[关系]，三角形交换：
    `rep ∘ compile = ⟦−⟧`，方案 A 中写在 `compile` 的类型里。],
)

// ───────────────────────────── glossary
#tbl(c-syn, (auto, auto, 1fr), ([名字], [全称], [是什么]),
  [`Tm A B`], [term], [程序本身：一个 allegory 表达式（语法树），类型是 arrow `A ⟶ B`],
  [`⟦t⟧ρ`], [`Tm.den`], [语义映射：把项 `t` 映到它的关系 `Core.Rel A.El B.El`（`A.El × B.El` 上的谓词）；`ρ` 给自由变量赋值],
  [`ρ`], [environment], [`Val := Nat → (A B : Obj) → Core.Rel A.El B.El`：给自由变量 `var k` 指定关系；编号不带类型，所以 `ρ k A B` 按 `var k : Tm A B` 自己的类型查。`μ` `ν` `hylo` 绑定变量时扩展它：`⟦μ k b⟧ρ = lfp (X ↦ ⟦b⟧(ρ[k ↦ X]))`；闭项从 `Val.empty` 开始],
  [`η`], [code environment], [代码侧的 `ρ`：给同一批变量可执行的值；`compile` 的前提 `η.Sound ρ` = 每个变量 `rep (η k) = ρ k`],
)

// ───────────────────────────── 3
= 类型与运行时关系：`Obj`、`Rel A B`、`compile`

```
inductive Obj                           -- 类型的代码；A B 都是 Obj
  | atom (t : Atom)                     -- u1 char i8 i16 i32 i64 f32 f64 sym（目标：从 QAtomicType 收窄，见 §4.3）
  | prod (a b : Obj)                    -- 积：多列
  | arr  (b : Obj)                      -- 每格一个数组：平铺 payload + lo/hi
  | sum  (a b : Obj)                    -- 和：tag 列 + 各分支位置

Obj.El : Obj → Type                     -- 解码：atom ↦ 原子的 Lean 类型，prod ↦ ×，arr ↦ List，sum ↦ ⊕

structure Known (A B : Obj) where
  dom : Option (Σ n, Vals A n)          -- 已知的定义域 K
  ran : Option (Σ n, Vals B n)          -- 已知的值域 L

inductive Rel (A B : Obj)
  | tab  (t : Except String (Tab A B))            -- 两列等长数组；error = 失败及其消息（原 CRel 的 ok = false），一路到 check、print
  | lazy (f : Known A B → Rel A B)                -- 边界够了返回 tab，不够返回 lazy 等更多边界

compile η t : {r : Rel A B // rep r = ⟦t⟧ρ}       -- 方案 A：规格在类型里
```

#grid(columns: (1fr, 1fr), gutter: 8pt,
  card(c-run, [为什么是 `lazy`])[`succ`、`arith`、`leq`、`⊤` 是无限关系，只能在边界已知后求值；
    它们和有限表一样是 `Rel` 的值，不是编译器的特例。复合时自动传播：`tab ≫ lazy` 把左表的值域作为 `dom` 交给右边。],
  card(c-run, [闭项只算一次（草稿，待审）])[闭项的值不随上下文变：由下面的 `rep (f ⟨K, L⟩) = K ≫ R ≫ L`，取空边界得 `rep (f {}) = R`。
    所以一个不需要边界的闭项（有限：旧记号 `Tm.dem = false`）在共享常量处求值一次，存成 `tab`（`GenK.memo`）；
    需要边界的闭项（`𝟙`、`≤`、`⊤` 等无限关系）仍是 `lazy`，在每个上下文里按边界求值。否则一个闭的 `lazy` 值在 `fold` 的每一轮重算。],
  card(c-run, [需要几侧边界])[`succ`（函数）：`dom` 已知即返回 `tab`。`leq`：`Λ(leq)(3) = {3,4,…}` 无限，
    `dom` 与 `ran` 都已知才返回 `tab (K ≫ leq ≫ L)`。`⊤`：`K × L`。],
)

- 删除的类型：`CRel`（`ok` 并入 `tab` 的 `Option`）、`Fn`、`Dem`（定义域就是 `Known.dom`）、`Den`（直接写 `Core.Rel`）。
- `Obj` 是可检查的数据，编译器按它分派（`Vals A n` 几列、哪个宽度的 kernel）；Lean 的 `Type` 不能模式匹配，所以程序用 `Obj`、数学用 `.El`。
- `Tab` 是三字段结构 `{n, key, val}`（原来的 `Rel k v`），内容和 `Σ n, Vals A n × Vals B n` 相同，留名字是因为字段名 `.n .key .val` 被两千多处使用。
- 新的组合子加 `Known` 的字段，不加 `Rel` 的构造子。

#card(c-sem, [`rep` 与 `compile`（规格写在类型里）])[
  `rep (tab (some t))` = 表读成的谓词；`rep (lazy f) = R` ⇔ 对任意 `K`、`L`，`rep (f ⟨K, L⟩) = K ≫ R ≫ L`（缺的一侧取 `𝟙`）。\
  `compile : (t : Tm A B) → η.Sound ρ → {r : Rel A B // rep r = ⟦t⟧ρ}` —— 返回值带着自己的证明，没有单独的
  `compile_sound`；每个节点的 `Gen.*_sound` 引理是 `compile` 定义的一部分，证明在编译时被擦掉。
  前提是 gap 全部清零（见 §7 TODO）；在此之前，现有的 `compile` + `compile_sound`（带 `t.gap = none`）保留。]

#card(c-rs, [Lean 证明不到的边界])[
  证明连到 Lean 定义为止。`@[extern]` kernel 的 Rust 实现只由 `decide`（kernel 中用 Lean body 算）与 `#guard`
  （运行编译后的 Rust）成对测试；Lean 编译器本身是信任基。kernel 越少，这条只有测试的边界越窄。]


// ───────────────────────────── 1
= 语法：allegory 的项 `Tm : Obj → Obj → Type`

- 前端：`Parse` → `Elab`（得到 `Tm`）→ `Expand`（`rel_program`，elaboration 时编号 `share`、产出代码）。

#tbl(c-syn, (auto, 1fr), ([组], [构造子]),
  [allegory], [`id` `comp` `conv` `meet` `dom` `ran`],
  [distributive allegory], [`zero` `join` `top`],
  [division allegory], [`ldiv` `rdiv`；symmetric division 只有运行时的 `Alg.symDiv`，`Tm` 中缺构造子],
  [Boolean（有补）], [`diff`：需要补，不属于一般 allegory],
  [product / sum], [`outl` `outr` `pair` `prod`；`junc` = `[R,S]`（目标：加 `inl` `inr`，`[R,S] = inl° ≫ R ∪ inr° ≫ S` 成为定义；`juncD` 随 lazy `Rel` 消失）],
  [power], [`lam`（Λ） `E` `est` `thin` `nil` `atPos`],
  [数据], [`val R` `uni U` `succ` `arith` `leq` `lt`],
  [递归], [`mu` `nu` `fold`（`⦇e,S⦈`，代数 `[nil, snoc]` 上的 catamorphism：左折叠，步骤读 `(acc, x)`，从下标 0 向上；尽量从左到右读，程序的含义需要时才用从右到左读的 `foldr`（`⦇e,S⦈ʳ`，步骤读 `(x, acc)`，如 `sum`、`thinL`）；输出数组只用 `snoc` 在末尾追加构造，从不在前面插入） `hylo`（`μX. c ≫ G(X) ≫ S`，原 `hylo`）],
  [绑定 / 复用], [`var` `share` `own` `call` `arg`],
  [库原语], [`prim r`：`prims` 表的一行（`inits` `tails` `prefix` `concat` `zip` …；`asc` `seen` 改为 kernel），在某个类型上实例化，参数由 `arg` 给出],
)

#card(c-syn, [改写引理（原 `Tm.Ax`）])[category 律、`°°`、`(RS)° = S°R°`、分配律、`𝟘`、`μ`/`ν` 展开（`ν = S ∩ b[ν]`）：每条写成 `⟦lhs⟧ρ = ⟦rhs⟧ρ`，由 `Rel/Core/` 中 `Core.Rel` 的定理证明；改写 `t₁` 为 `t₂` 只需 `⟦t₁⟧ρ = ⟦t₂⟧ρ`。Rel 只在 `Rel(Set)` 上运行，所以 `Tm.Le`、`Syn`、`Hom.den` 去掉。]

// ───────────────────────────── 2
= 语义映射 `⟦−⟧`：`Tm.den ρ : Core.Rel A.El B.El`

- 按结构递归、全函数、point-free：每个节点是若干关系的复合，与该节点的 `Gen.*_sound` 引理一致。
  例：`⟦nu k S b⟧ρ = Core.Rel.nu (X ↦ ⟦S⟧ρ ∩ ⟦b⟧(ρ[k ↦ X]))`（最大不动点）。
- 与 `Tm.argDen` 互递归：一行 `arg` 脊的含义（`rowDens`）。
- `Rel.Core` 只用 `{propext, Quot.sound}`（构造性），freyd bridge 把它按 `rfl` 映到 freyd 的 `RelSet`。

// ───────────────────────────── 4
= 最小 kernel（目标设计）

#card(c-rs, [现状 → 目标])[
  现状：99 个 `qlean_*` 导出，7 种编码，其中大半服务于 q 的语义。它们已冻结在 qlean 自己的副本里（rel tag
  `qlean-base` = `e024297`，`qlean/.lake/packages/rel`）。目标：rel 只保留 *一种编码* 和 *5 个 kernel*；
  allegory 的每个运算、每个不动点都是它们的复合。Rel 要支持 data frame，所以原子有 u1 char i8 i16 i32 i64 f32 f64 sym。]

== 移出 rel 的 q 语义

#tbl(c-rs, (auto, 1fr), ([移出], [原因]),
  [`gen`（boxed）], [不在 kernel 里处理 boxed 值；boxed 值先编成 code 再进 Rel],
  [`til` `cycle` `cast` `floor` `widen`], [q verb，不是 allegory 运算],
  [`find` `bin search` `member` `match`], [q 的查找 verb；Rel 中是 `≫`（join）的特例],
  [`own_write` `md5` 等], [q 运行时的需要],
)

== 剩下的唯一编码：foR（分块 frame of reference）

#figure(
  diagram(spacing: (2mm, 8mm), edge-stroke: 0.8pt, label-size: 8pt,
    node((0, 0), [列：$n$ 个 code], ..bx(c-run, none)),
    edge((0, 0), (0, 1), "-|>", [每 $2^"lg"$ 个一块，`lg` 每列自选], label-side: left),
    node((0, 1), grid(columns: 3, gutter: 0pt,
      box(fill: c-sem.lighten(70%), inset: 5pt, stroke: 0.6pt + c-sem)[base $b$],
      box(fill: c-syn.lighten(75%), inset: 5pt, stroke: 0.6pt + c-syn)[宽度 $w ∈ 0..64$],
      box(fill: c-run.lighten(80%), inset: 5pt, stroke: 0.6pt + c-run)[$2^"lg"$ 个 $w$ 位偏移，紧密打包])),
  ),
  caption: [第 $i$ 个元素 $= b + "offset"_w [i]$；`ofRaw` 对每块取 $w = "bitwidth"(max − min)$。
    `lg` 是列的参数（如 0..16）：值域变化快的列用小块（每块 $w$ 更窄），平稳的列用大块（base 和宽度的开销更少）。],
)

#tbl(c-run, (auto, auto, 1fr), ([旧形式], [在 foR 中], [说明]),
  [`bits`（bitmap）], [$b = 0$，$w = 1$], [布尔列、mask],
  [`enum` / ids], [$b = 0$，$w = ⌈log_2 "card"⌉$，同样的残差打包], [code 列的常态],
  [`foR`], [一般情形], [不变],
  [常量列], [$w = 0$], [只存 base],
  [`bytes`（dense）], [不再是一种形式], [只在某块值域确实需要 $w = 8k$ 时出现，是 foR 的退化块，不单独实现],
)

- 结论：*一种编码*，就是现有的 `Ext.Enc.foR`（曾设想的 `packed` 即去掉缓存的 `foR`，已弃用）。`Enc.raw` 只有一个解码，所有 kernel 的模型仍写在 `raw` 上。
- 缓存（只服务速度，语义从不读，证明零成本）：`maxv`（谓词跳过整块）、`bsum`/`sumnul`/`sumn`（O(nblk) 求和）、`off`（块起点）。
- 每个 kernel 读 foR、写 foR；写出由共享的 `Producer::block_into` 逐块完成，不经过稠密中间数组。

== 原子类型：都是 foR 的 code

#tbl(c-syn, (auto, 1.2fr, 1fr), ([原子], [存成什么 code], [比较 / 运算]),
  [`u1`], [宽度 1 的无符号 code（0 或 1），真假值就是 `u1`，不另设 `bool`；sum 的 tag 列也是 `u1` 列], [`asc`、`scan(and/or/not)` 直接在 code 上],
  [`char`], [8 位无符号 code（字节值，保序）；字符串 = `arr char`], [`asc` 按字节序；`arr char` 按字典序],
  [`i8` `i16` `i32` `i64`], [翻转符号位，得到同宽的无符号数（保序）；再按块 foR], [`asc`、`scan(lt)` 直接在 code 上；算术按声明宽度回绕],
  [`f32` `f64`], [保序位映射：正数翻转符号位，负数翻转全部位，得到 `UInt32` / `UInt64`], [code 的序 = 浮点的全序（NaN 也有位置）；`fadd` `fmul` `flt` 等先还原再算],
  [`sym`], [保序字典 id：字典 = 排好序、无重复的字符串表（`arr char`），列存 id], [id 的序 = 字符串的序，所以 `asc`、join、`∩` 都只看 id],
)

- 原子的宽度只决定 code 的值域上限（`i8` ≤ 8 位 …）；块的宽度 $w$ 仍按数据选，常常比声明宽度窄。

- data frame = `Rel A B` 的 `tab`，`B` 是若干原子列的 `prod`：struct of arrays，每列一个 foR `Enc`。
- `alp`（浮点小数压缩）不再是一种形式；需要时作为 float 列的 fast path，配一条定理说明 decode 后等于保序位映射。
- intern（建字典）= `asc ≫ seen`：字符串排序、去重得字典（`first` 经 `gather` 取回代表串）；每个字符串的 id = 它所在组的编号
  `g`（`asc` 的排列经 `scatter` 回原位）。两个 `sym` 列合并（`∪`、join 两侧字典不同）时对字典的并做一次 intern、重映射 id。不是 kernel。

== 5 个 kernel：2 个原语 + 3 个优化

#tbl(c-rs, (auto, 1.4fr, auto, 1fr), ([kernel], [形状（输入输出都是 foR）], [定律], [现有 driver]),
  [`scan`], [`(op : Op) (rev : Bool) (s t) (n) (seg : Enc) (es : List Enc) : Enc × Option UInt64`，分段前缀折叠；含 map 与 fold。第二个分量是折叠结果：最后访问的那一行（正向第 `n − 1` 行，`rev` 时第 0 行）按 `t` 的宽度截取的字，`n = 0` 时为 `none`；kernel 写输出时从累加器取得，无需解码输出（`kscan_last`）], [`raw_scan`], [`scan` `map` `fold`],
  [`gather`], [`(ix : Enc) (e : Enc) (fill) : Enc`，`out[i] = e[ix[i]]`], [`raw_permute`], [`permute`],
  [`scatter`], [`(ix : Enc) (e : Enc) (n) (fill) : Enc`，`out[ix[i]] = e[i]`], [`raw_scatter`（新）], [—],
  [`asc`（草稿，待审）], [`(m) (es : List (AscKey × Enc)) : List Enc × Enc`，`AscKey = atom t ┃ cells n c lo hi els`；
    按若干列字典序稳定排序：每列排好的值 + 排列], [`asc_sorted` + `asc_perm`（新）], [—],
  [`seen`（草稿，待审）], [`(n) (es : List (AscKey × Enc)) : (k, g, first)`，各列按 `asc` 的方式读；行须已按 `asc` 序，否则报错（先跑 `asc`）：`k` 为组数，`g` 为每行的组号（按首次出现编号），`first` 为每组第一行的位置；如键 `B A B`：`k = 2`，`g = 0 1 0`，`first = 0 1`], [—（`asc ≫ seen` 给出 `asc` 的并列组编号；定理待写）], [—],
  [`bitrows`（融合 kernel，草稿，待审）], [`(all : Bool) (w na ni g) (ends idx m : Enc) : Enc`，`m` 是 `na · w` 位的 `u1` 位矩阵（第 `i` 行占 `[i·w, (i+1)·w)` 位）；输出 `g · w` 位：第 `r` 行 = 第 `r` 段 `[ends[r-1], ends[r])` 中各 `idx[k]` 行的 `∨`（`all = false`，即 `≫`，空段为 0）或 `∧`（`all = true`，即 `\`，空段为 1）。只在位矩阵小时选用：`|A|·|B| ≤ 2²⁷`（`sudokupc9` 的 `π₁\(sup(X) X)`：作表 1.9e8 行，作矩阵 4.3e7 位）。选用规则（草稿，待审）：kernel 路径的 `≫`、`\`（`GenK` 经 `Tab.compSel`、`Tab.ldivSel`）先由 `compGroups` 的前缀和得展开行数 `T`，当输入矩阵 `na·w` 与输出矩阵 `g·w` 各 `≤ 2²⁷` 且 `< 2³²`、两者之和小于展开所写的 `64·T` 位（每行至少一个 64 位字）时（`Tab.bitsWin`）用位矩阵，否则用分块展开或计数],[`Tab.compBits_comp`：`compBits R S = .ok X`、`comp R S = .ok Y` ⟹ `X.Holds = Y.Holds`；`Tab.ldivBits_ldiv`：`ldivBits` 对 `ldiv` 同式（由 `raw_kbitrows`、`csr_spec`、`colCat_raw`、`Tab.compBits_holds`、`Tab.ldivBits_holds` 证，`Rel/RepBits.lean`）。只证所表的关系相同；输出为 `Canon`（与 `Tab.comp` 的行序相同）未证：仓库中尚无从 `kasc` 秩序到 `Obj.lt` 的桥，现由 `Rel/BitsTest.lean` 的 `#guard` 对照], [`Tab.compBits` `Tab.ldivBits`],
)
- `AscKey` 的 `cells`（草稿，待审）：一个 `arr` 侧作一个键，列的每个字是格号，格 = `[lo, hi)` 夹到共享 payload
  `[0, c)`；`els` 是 payload 的键列。两格按元素逐个比较序码（字典序），真前缀在前；格长相同且各元素序码相等才相等。
  `arr char` 是它在 `els = [atom char]` 时的特例。

- *map 与 fold 都是 scan*：map = 步骤不读累加值的 scan（`op` 只看当前元素）；fold = scan 的最后一个值
  （分段时取每段最后一个）。`Op` 标明自己是否读累加值、是否结合，Rust 据此并行：不读累加值或结合的 `op` 分块并行，其余顺序扫。
- `asc` 返回排列，因为排一列时要带着同一行的其它列走（`gather`）。
- `seen` 的相等就是 `asc` 的：键 = 每列保序 code 的元组；code 在每个有序类型上是存储位的单射，所以相等 = 存储位相等（`-0.0` 与 `0.0`、两个不同位的 NaN 是不同的键），NaN 与 `-0` 的规范化在产生浮点字的地方做；因此 `asc ≫ seen` 编号的恰是 `asc` 的并列组。
  两个引擎都直接读 foR 块、从不解码整列：直接寻址（每个混合进制 code 一个槽，值域来自块元数据）；输入已按 `asc` 序时用游程检测。
  键域过宽又无序时报错，错误说明需要 hash 而 hash 未实现；没有 hash 引擎，也没有 `part` 引擎（已决定，PLAN D.12）。
- `last` 不属于 `seen`：它是 `scatter`（位置 → `g`，后写覆盖），按组号顺序（计划中，未实现）。
#tbl(c-rs, (auto, auto, 1fr, auto), ([层], [kernel], [由原语写出（定理）], [单独实现的理由]),
  [原语], [`scan`], [—：唯一做计算的], [—],
  [原语], [`scatter`], [—：唯一把数据写到计算出的位置的], [—],
  [优化], [`seen`], [Lean body = `Order.idsBy` 的 foR 形式（`Order.firstsBy` 取每组第一行，行的组号 = 其键在其中的下标）；未写成 `scan` / `scatter` 的复合], [不排序：直接寻址一遍扫描，有序输入用游程检测；`∩ ∪ − ≫ dom ran` 都以它结尾],
  [优化], [`asc`], [radix sort：每一位 `scan`（直方图、前缀偏移）→ `scatter`；`arr char` 用 MSD], [比较排序常数小],
  [优化], [`gather`], [`(ix[i], i)` 与 `(j, e[j])` 拼接 → `asc` → `scan` 向后填 `e` → `scatter` 回 `i`], [O(n)，不必排序],
)
- Lean body 只需信任两个原语；每个优化 kernel 配一条定理 `k = 上表中的复合`，所以它的 Lean body 可以就是那个复合，
  Rust 实现仍由 `decide`/`#guard` 对它测试。
- `Op` 是有限枚举（`add` `sub` `mul` `min` `max` `eq` `lt` `and` `or` `not` `first`，及 float 的 `fadd` `fmul` `fdiv` `flt` …），而不是 Lean 闭包：Rust 只能执行固定的运算集，
  Lean body 用 `Op.eval` 解释它，所以 `decide`/`#guard` 的检查方式不变。

== allegory 运算 → kernel

#tbl(c-sem, (auto, 1fr), ([运算], [由哪些 kernel 复合]),
  [`°`], [交换 key / val 两列，无 kernel],
  [code（相等 ⇔ code 相等）], [`seen`（`g` 即 code，按首次出现编号，无需排序）],
  [`∪`], [两表拼接 → `asc`（key, val 两列）→ `seen`（`first` 取代表行）],
  [`∩` `−`], [两表拼接、带来源标记 → `asc` → 每组相等行数 `scan` → 保留出现在两侧（`∩`）或只在左侧（`−`）的组],
  [`≫`], [两侧按中间列 `asc`、取组（`seen`）、组内展开（`scan` 偏移、`scatter` 组头、`scan(max)` 填充）、`gather` 取行、`asc` + `seen`。（草稿，待审）展开总行数超过 `blockRows` 时分块：在组的边界切开，每块至多约 `blockRows` 行（单个大组自成一块），每块先 `asc` + `seen` 去重，再与前面的结果做 `∪`；块只切 `R` 的行，`S` 每块整体参与（`Tab.compWith`，`Rel/Run/Comp.lean`）],
  [`dom` `ran`], [取一列 → `asc` → `seen`（`first` 取代表行）],
  [`R\S` `R/S` 对称除], [不求补：按组比较「R 的 b 的个数」与「其中满足 S 的个数」，即分段 `scan`],
  [Λ（`arr` 侧）], [`asc ≫ seen` 的组号 `g` 与 `first` 给出 `lo`/`hi`],
  [`μ` `ν` `fold` `hylo`], [Lean 中的循环（`fixOn`），每轮调用上面的运算，行数不变即停；semi-naive 只多一个 `−`],
)

== allegory 运算 → kernel：power 与 list（草稿，待审）

以下各行照 `Rel/Run/Div.lean`（`∋` `E`）、`Rel/Run/Power.lean`、`Rel/Run/List.lean` 现有代码写出。行中的复用部分：
- `canon` = `asc → seen → gather`：去重、升序（`∪` 行的后半）；每行最后都接它，下面不再写。
- 格界 `[s, e)`：`scan`（逐行 `max`/`min`）把 `lo` `hi` 夹到 payload `[0, m)`，宽 `e − s` 不为负。
- EXPAND(`w`)：`scan`（前缀和定各组起点）→ `scatter(max)` 组号到起点 → `scan(max)` 向后填 → `gather`；
  得每个输出行的组 `G` 与组内偏移 `u`（`≫` 行的「组内展开」）。
- where(`b`)：`scan(add)` 得前缀和 `s`，其折叠结果即个数 `K`（`m = 0` 时为 `none`，空 where 的个数按定义为 0）→ `scan(sub)` 得 `d = s − b`（每行之前保留的行数）→ `scatter(last)` 把 `pos` 写到 `d`，共 `K + 1` 格（被丢弃的行写到下一保留行的格、由后者覆盖，或写到多出的第 `K` 格）→ `gather` 取前 `K` 格：`b = 1` 的位置，升序；O(m)，不排序。
- 「`2^63` 拒绝」：位置、宽度按有符号 `i64` 读，所以超过时报错，不截断。

#tbl(c-sem, (auto, 1fr), ([运算（草稿，待审）], [由哪些运算与 kernel 复合]),
  [`∋`（on `X`）], [格界 → EXPAND(`e − s`) → `gather`（key 取格 `X[G]`，val 取 payload 第 `s[G] + u` 个）；
    `n·m + n + m ≥ 2^63` 拒绝],
  [`E(R)`], [`Λ(∋ ≫ R)`：`∋` 行 → `≫` 行 → Λ 行],
  [`τ` = `Λ(𝟙)`], [`𝟙` on `X` = `dom ⟨X, X⟩`（`asc → seen → gather`）→ Λ 行；Λ 中 `X` 与表共 `N` 行，`N ≥ 2^63` 拒绝],
  [`setify` = `Λ(∋)`], [`∋` 行 → Λ 行],
  [`length`], [格界 → `scan(sub)` 得宽 `e − s`；payload `m ≥ 2^63` 拒绝。是 `fold` 定义（§1、§7「`prims` 行改为
    `fold`」）的融合形式，定理 `⟦length 行⟧ = ⟦fold 定义⟧` 未证],
  [`at(k)`], [格界 → `scan` 测 `k < e − s` → where → `gather`（格，及 payload 第 `s + k` 个）；`m + k ≥ 2^63` 拒绝],
  [`est(Q)`], [`G = ∋`、`D = ran ⟨G, G⟩`、`V = ran G`；`Y = (D − Q(D)) − ran ⟨V, V⟩`（失败的对，去掉对角）；
    结果 `G − ⟨G, G⟩ ≫ Y ≫ π₁`。只用 `∋` `⟨,⟩` `ran` `−` `≫` `π₁` 各行，`Q` 只在一个数组内的对 `D` 上跑],
  [`thin(Q)`], [`G` `D` 同上；`w = D ≫ ⟨π₂, π₁⟩`，`S = dom (w ≫ Q(ran w))`（交换后也通过的对），`Y = Q(D) − S`
    （严格胜出的对）；结果 `Λ(G − ⟨G, G⟩ ≫ Y ≫ π₂)` on `X`],
  [`cat`（`(xs, ys) ↦ xs ++ ys`）], [两 payload 拼接（`scatter` + `scan(add)`）→ 两侧格界 → `scan` 宽 `w₁ + w₂` →
    EXPAND → `gather` `s₁[G]` `s₂[G]` `w₁[G]` → `scan` 选下标（`u < w₁` 取第一段 `s₁[G] + u`，否则
    `m₁ + s₂[G] + u − w₁`）→ `gather` payload → `scan` 前缀和得新格 `lo` `hi`；
    `n(m₁ + m₂) + n + m₁ + m₂ ≥ 2^63` 拒绝。是 §7 中应成为定义的列表运算的融合形式，`⟦cat 行⟧ = ⟦定义⟧` 未证],
  [`snoc` `cons`], [`(𝟙 × τ) ≫ cat`、`(τ × 𝟙) ≫ cat`；这里的 `τ` 是逐行单元素格 `[i, i + 1)`（`scan`），
    不经 Λ 行、不 `canon`。同为融合形式，`⟦snoc 行⟧ = ⟦定义⟧`、`⟦cons 行⟧ = ⟦定义⟧` 未证],
  [`zip`], [两侧格界 → `scan(min)` 宽 → EXPAND → `gather` 两 payload 各在 `s₁[G] + u`、`s₂[G] + u` →
    `scan` 前缀和得新格；拒绝条件同 `cat`],
  [`sum`（`⦇0, +⦈ʳ`）], [格界 → EXPAND → `gather` 元素 `v` → `scan` 标每格末元素 → 反向分段 `scan(add)` 得后缀和
    `W` → `scan` 测溢出（`v` 与 `W − v` 同号、`W` 异号）或 null `−2^63` → `scatter(or)` 得坏格、`scatter(add)`
    得每格回绕总和 → where 留无坏元素的格（坏格不出现在结果中，不报错）；`n·m + n + m ≥ 2^63` 拒绝。
    `foldr` 的融合形式，`⟦sum 行⟧ = ⟦定义⟧` 未证],
  [`cons°`], [格界 → where(`s < e`) → `gather`：首元素 = payload 第 `s` 个，尾 = 格 `[s + 1, e)`（`scan`），
    共享原 payload，不建新 payload；`n + m + 1 ≥ 2^63` 拒绝],
  [`snoc°`], [同 `cons°`：格 `[s, e − 1)` 与 payload 第 `e − 1` 个],
  [`cat°`], [格界 → EXPAND(`e − s + 1`)（每格的每个切点）→ `gather` `s` `e` → `scan` 切点 `s[G] + u`；
    两段 `[s, s + u)`、`[s + u, e)` 共享原 payload；`n(m + 1) + n + m + 1 ≥ 2^63` 拒绝],
  [`inits`（草稿，待审）], [`Λ(prefix)`：`prefix` 行 → Λ 行；一个数组的前缀互为真前缀，Λ 的升序格即按长度递增，`[]` 在前],
  [`tails`（草稿，待审）], [`Λ(cat°) ≫ F(π₂)`：`cat°` 行 → Λ 行（格内按切点递增）→ 取格 payload 的第二列，格界不变（无 kernel）；
    后缀按长度递减，`[]` 在后],
  [`concat`（草稿，待审）], [`⦇nil, cat⦈`：`fold` 行（`Tab.foldRounds`，每轮 `cons°`），步骤为 `cat` 行],
  [`filter(p)`（草稿，待审）], [`⦇nil, dom(π₂p) snoc ∪ (𝟙 − dom(π₂p)) π₁⦈`：`fold` 行，每轮 `≫ dom p`、`⟨,⟩`、`snoc` 行、`−`、`∪`],
  [`takewhile(p)`（草稿，待审）], [`⦇nil, dom(π₁p) cons ∪ (𝟙 − dom(π₁p)) nil⦈ʳ`：`foldr` 行（每轮 `snoc°`），每轮 `≫ dom p`、`⟨,⟩`、`cons` 行、`−`、`nil`、`∪`],
  [`hylo(c, S)`（草稿，待审）], [`μX. c ≫ G(X) ≫ S` 在需求键 `D` 上：节点 `N = μN. D ∪ ran(N ≫ ch)`（`ch` = `c` 后接
    `G` 的成员关系），再 `D ≫ μX. N ≫ φ(X)`；两处都是 `Tab.mu`（`∪` 行的轮次），不建中间结构；无环时至多 `|N| + 2` 轮],
  [`loop(F)`（草稿，待审）], [`P ≫ loop(F)`：在 `ran P` 的每个 `(c, ys)` 上，以 `c` 起、沿 `ys` 的左折叠
    （`Tab.foldRounds` + `cons°`），每轮 `p ≫ F(ran p)`，`p` 为该轮的对 `(acc, y)`],
  [`merge(Q)`（草稿，待审）], [状态 `((x, y), acc)` 自 `((x, y), [])` 起，以 `cat(x, y)` 为时钟跑 `|x| + |y|` 轮
    `Tab.foldRounds`：`l = dom(⟨a, b⟩ ≫ Q)`（`a`、`b` 为两侧 `cons°` 的头），`l` 或 `y` 空时取 `a`，否则取 `b`，
    `snoc` 到 `acc`；结果 `π₂`],
  [`thinL(Q)`（草稿，待审）], [`⦇nil, bump(Q)⦈ʳ`（`Tab.foldRounds` + `snoc°`）；`bump` 在对 `(x, ys)` 上：
    `u = ys ≫ cons°` 得 `(b, bs)`，`x Q b` 时 `x :: bs`，`b Q x` 时 `ys`，`ys` 空或两者皆否时 `cons`（`x :: ys`）],
)

== Rust 侧

#grid(columns: (1fr, 1fr), gutter: 8pt,
  card(c-rs, [crate 结构])[`scan.rs` `gather.rs` `scatter.rs` `asc.rs` `seen.rs` 各一个导出；`pack.rs` 是分块编解码（不导出）；
    `pod::Elt`、`by_width!`（u1、char、i8–i64、f32、f64）、`pool` 保留。`RELK.txt` 从 99 行变为 5 行。],
  card(c-rs, [融合 kernel])[如 join、intern、group ids：只是优化，每个配一条定理说明它等于上表中的某个复合；
    在第二个真实需要出现前不加。],
)
// ───────────────────────────── 5
= 分层（目录 = Lake library）

#tbl(c-syn, (auto, auto, auto, 1fr, auto), ([层], [目录], [lib], [内容], [axiom]),
  text(fill: c-sem)[core], [`Rel/Core/`], [RelCore], [`Core.Rel α β`，`≫ ° ∩ ∪ 𝟙 𝟘`，`mu`，`nu`], [`propext` `Quot.sound`],
  text(fill: c-run)[kernel], [`Rel/Kernel/`], [RelKernel], [`Enc`（foR）、5 个 extern、driver], [Classical],
  text(fill: c-run)[kernel spec], [`Rel/KernelSpec/`], [RelKernel], [其余部分引用的 kernel 引理], [],
  text(fill: c-run)[run-time], [`Rel/Run/`], [RelRun], [`Obj` `Vals` `Rel` `Known` `Alg` `Tm` `Gen` `compile`], [precompiled],
  text(fill: c-syn)[证明 + 语言], [`Rel/`、`Rel/Lang/`], [Rel], [`Rep*` 律、`KernelWF`、`Lang.Den`（语义）、`CompileSpec`], [],
  text(fill: c-rs)[Rust], [`crate/`], [`relk`], [5 个 `qlean_*`], [—],
  text(fill: c-rs)[native rt], [`crate/rt/`], [独立 package], [替代 `libleanshared` 的 Lean runtime], [—],
)

= Gate

`make check` = #box[build] · compile-diff（`compile` 对 `rel_program` 差分）· crate-test · syms · native · ldd · index ·
index-complete · axioms · noreduce · panic · externs；另加 `lake -d freyd/relaop build RelAop -R -K rel=…`。

// ───────────────────────────── 7
= TODO：清零 gap，然后把 `compile` 改成带证明的类型

按依赖顺序；全部完成后删去 `Tm.gap` 与前提 `t.gap = none`（`Rel/Lang/Rows.lean:102-134`）。

#tbl(c-run, (auto, auto, 1fr, auto), ([序], [gap], [缺什么], [能否证明]),
  [1], [`foldI`], [改为由 `fold` 定义（见下）；其正确性由 `fold` 的引理得出，不再需要 `foldI_sound`], [能：随定义消失],
  [2], [`share` 含自由变量], [共享部分必须是闭项；开项在每次绑定下重算是代码的错], [能：改 `Expand` 不共享开项，无需新证明],
  [3], [`setify` / `asc` 行], [`asc`、`seen` 改为 kernel 后，缺的是它们的定律：float 不满足 `Obj.Ordered`（NaN）；缺「排序后的排列唯一」（`¬ lt` 反对称）], [能：float 用保序位映射后有全序；反对称是常规证明。与 float 编码同批做],
  [4], [`hylo`], [按轮迭代 = lfp，需要 `den_local`（body 在一组 key 上的输出只依赖这组 key）], [多半能（positive body）；可能要加 locality 前提],
  [5], [`lam` `E` `thin`], [同一集合有多种数组表示；需要 D2 canonical table（有序、无重复）], [能：先实现 canonical 形式（`doc/rel-denotation-design.md` §7.1）],
  [6], [`call`], [泛型定义还没有语义（stage 5）], [能：语义 = 展开成定义的项],
  [—], [body 非 positive 的 `μ` / `ν`], [非单调函数的不动点，Knaster–Tarski 不适用，迭代可能振荡], [不能；改为 elaboration 时报错，不再是 gap],
)

其它 TODO：
- `Tm` 加 `inl` `inr`；`junc` 改为定义 `inl° ≫ R ∪ inr° ≫ S`；删 `juncD`（demand 由 lazy `Rel` 在运行时处理）。
- 逐个检查 `prims` 的行能否写成 `fold`/`hylo`（如 `inits` `tails`），能写的改为定义，只留真正的 kernel 级原语。
- `foldI`、`flat` 不再是构造子：`flat R` 由 `pair` `outl` `outr` 加相等测试写出（`(i,a) ↦ b` ⇔ `i R (a,b)`），`foldI` 是 carrier 为 `I × V` 的 `fold`（初值依赖 key）；先验证两者确实可写出，再删构造子及其 `Gen`、`den` 分支。`hylo` 改名 `hylo`。
- 去掉 `Syn`、`Tm.Le`、`Tm.Eqv`、`Hom.den`（`Rel/Lang/Syn.lean`）与 #9；`Tm.Ax` 改为改写引理 `⟦lhs⟧ρ = ⟦rhs⟧ρ`；freyd 需要的范畴在 `relaop` 自建。
- `Tm` 加 symmetric division 构造子（运行时已有 `Alg.symDiv`）。
- 改名：去掉 `Den` `Dem` `Fn` `CRel`，`Rel k v` 改为 `Rel A B`（`tab` ┃ `lazy`），`Tm` 去掉 `d`。
- kernel 缩到 5 个：原语 `scan` `scatter`，优化 `gather` `asc` `seen`（各配「= 原语复合」的定理）、编码只留 foR（块长 `lg` 每列可选）、原子 u1 char i8–i64 f32 f64 sym；q 专用 kernel 留在 qlean 的副本（tag `qlean-base`）。
