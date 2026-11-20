// palette: one colour per layer, reused in tables and headings
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let ink   = rgb("#222831")
#let soft(c) = c.lighten(88%)

#set document(title: "DataFrame 到 Rel 的映射")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); DataFrame 到 Rel 的映射 ],
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

// ───────────────────────────── title
#align(center)[
  #text(24pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[DataFrame 到 Rel 的映射] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[DataHaskell `dataframe` 与 polars 的运算，写成 Rel 的关系代数项]
]
#v(6pt)

Rel 本身（`Obj`、`Tm`、kernel、编码、原子、`compile`）见 `rel-architecture`；本文只讲 dataframe 怎样写成 Rel。
一个 frame 是从位置对象 `N` 出发、定义域为 `(<m)` 的部分 map `x : N ⟶ C`；只存长度 `m`。
库是 `Rel/Programs/Frame.lean`、`FrameGroup.lean`、`FrameJoin.lean`（程序 `frame`、`frameGroup`、`frameJoin`）。

#tbl(c-syn, (auto, auto, 1fr), ([记号], [类型], [含义]),
  [`N`], [对象], [位置（自然数），所有 frame 共用；元素不存储。`N` 是无界的 `obj N`（没有右侧，`rel-architecture` §0），
    关系按需运行，所以 verb 读的位置都从 `dom(x)` 来：新位置的编号写成 `dom(x) ≫ asc(…)`],
  [`x` `y`], [`N ⟶ C`], [一个 frame：部分 map，`dom(x) = (<m)`（第 2 节）。第 `a` 列是 `x ≫ a`],
  [`m`], [`1 ⟶ N`], [frame 的长度 `count(x)`；两个 frame 时写 `m₁` `m₂`],
  [`n` `w`], [`1 ⟶ N`], [常量；`n̂ = ! ≫ n` 是取值 `n` 的常函数],
  [`(<n)`], [`N ⟶ N`], [coreflexive：只放过 `i < n`],
  [`(+n)`], [`N ⟶ N`], [函数 `i ↦ i+n`；`(+n)°` 是 `i ↦ i−n`，只在 `i ≥ n` 有像],
  [`≤ₙ` `<ₙ`], [`N ⟶ N`], [位置的序],
  [`ι`], [`N ⟶ N`], [新位置到旧位置的关系；结果的列是 `ι ≫ x`],
  [`S`], [`Schema`], [行的类型：带列名的列类型表；`S.obj` 是其积],
  [`a` `v`], [`col S "…"`], [一列：一个投影（`π₁` `π₂` 的复合）],
  [`k` `h`], [`col S "…"`], [key 列（一个投影，或若干投影的 pair）；`h` 是右侧 frame 的],
  [`c`], [`N ⟶ V`], [一个 frame 的一列 `x ≫ a`；编号的定义都只读一列],
  [`p`], [`C ⟶ C`], [谓词，写成 coreflexive],
  [`e`], [`C ⟶ V`], [一行之内的表达式],
  [`f`], [`[N] ⟶ D`], [聚合：读一组的位置数组（`Λ` 的升序）],
  [`!`], [`A ⟶ 1`], [到 prelude 的终对象 `1` 的 `⊤`],
)

// ───────────────────────────── 1
= 数据模型

== frame 的值

- frame 是 `Vals C n`（`Rel/Run/Core.lean:456`），不新增类型；列的布局见 `rel-architecture` §4.3『原子类型：都是 foR 的 code』。
  它表示的关系、行的编号与落盘方式在第 2 节。
- 一个运算是以 frame `x : N ⟶ C` 为参数、结果为 `N ⟶ C'` 的定义，与 Haskell 的 `DataFrame -> DataFrame` 一一对应。
  没有运算以单元格里的 list 代替一个关系。
- 值为集合的结果是 `Λ(R)`：`R` 的像按 `Obj.lt` 升序、无重复的数组（`Tm.den` 的 `lam`）；第 3 节的 `agg` 读这个升序。

== schema 与列名

- `Obj.prod` 没有字段名，列名是程序里的定义（`price ≜ π₁ ≫ π₂`）；形状相同、列名不同的两个 frame 类型相同，`select "price"` 与按名 join 无法检查。
- 设计（与 DataHaskell `TypedDataFrame '[Column "price" Double, …]` 相同的做法）：`Schema := List (String × Obj)`；`Schema.obj : Schema → Obj` 是一个定义，
  按 `.d` 的列顺序给出嵌套 `prod`。frame 的项以 schema 为下标，`Tm S.obj B`。
- 列名访问：`col S "price" : S.obj ⟶ T` 当且仅当 `("price", T) ∈ S`，在 elaboration 时判定，否则报错并指出缺的列名。
  `select` `exclude` `rename` `derive` `join` 是 `Schema` 上的函数，给出两个 `S.obj` 之间的项。
- 为什么不加 `Obj` 构造子：`Schema.obj` 让表示等式按定义成立，kernel、存储、`rep`、canonical、`lam_sound` 都看不到新东西；
  新构造子要给每个对 `Obj` 的 match 加分支。代价：字段类型相同、名字不同的两个 schema 有同一个 `Obj`，只有 schema 这一层区分它们。
- `.d` 就是 `Schema` 的落盘形式，同一个来源；依赖数据的 schema 见 F1。

各 atom 的编码与比较见 `rel-architecture` §4.3『原子类型：都是 foR 的 code』。

#tbl(c-syn, (auto, auto, 1fr), ([dataframe / polars 类型], [Rel 一侧], [说明]),
  [`Bool`], [`u1`], [也是 `filter` 的 mask],
  [`Int8` … `Int64`], [`i8` `i16` `i32` `i64`], [],
  [`Word8`], [`u8`], [],
  [`Word16` … `Word64`], [无], [不在本设计范围],
  [`Float` `Double`], [`f32` `f64`], [],
  [`Char`], [`char`], [],
  [`Text`、Categorical], [`sym`], [],
  [装箱的值], [`general`], [boxed 值先编成 code：`rel-architecture` §4.1],
  [`Day`], [`date`（`i32`）], [epoch 以来的天数],
  [`UTCTime`], [`datetime`（`i64`）], [epoch 以来的纳秒，无时区],
  [list 列（`collect`）], [`Obj.arr T`], [],
  [`Maybe a`], [`A+1`], [见 1.3],
)

== null

#tbl(c-sem, (auto, auto, 1fr), ([读法], [第 3 行为 null], [结论]),
  [q 的哨兵值], [第 3 个元素是 `0N`], [带内表示；q 语义不在 Rel 中（`rel-architecture` §4.1）],
  [和类型 `v : C ⟶ V+1`], [第 3 个元素是 `inr(∗)`], [*采用*：每列都是全函数，`x ≫ ⟨a, v⟩` 不丢行],
  [部分列 `v ≫ inl°`], [第 3 行没有像], [派生的读法：表达式里与 null 比较的行被 `filterBy` 去掉，和 polars 一致],
)

- `inl°`、`inr°` 是 `prims` 的行；`[R, S] = inl° ≫ R ∪ inr° ≫ S`：按 tag 分情况，null 一支读 `S : 1 ⟶ B`。
- `tot(R) = R ≫ inl ∪ (𝟙 − dom(R)) ≫ ! ≫ inr`：把部分的 `R : A ⟶ B` 变回全的 `A ⟶ B+1`（`R` 有值取值，否则 null）。
- 存储：`V+1` 是 tag 列加等长的值列（就地布局），没有位置列，因为位置不存储（第 2 节）。

// ───────────────────────────── 2
= 存储与顺序

一个实例：frame `[(A,1),(B,2),(A,1)]` 是 `a : N ⟶ K`、`b : N ⟶ V`，`m = 3`：`0 {a} A`，`0 {b} 1`，`2 {a} A`，`2 {b} 1`，`3` 没有像。
第 0 行与第 2 行是 `N` 的不同元素，所以是两行；`a° ≫ b` 只有 `A ↦ 1`、`B ↦ 2` 两对。

- *语义是集合。* 没有 bag，也没有 list 对象。frame 是一族从同一个 `N` 出发的部分 map，定义域都是 `(<m)`。以 `N` 为 key 它已经
  有序且无重复，不需要排序。`a° ≫ b : A ⟶ B`（排序并去重）只在运算的规格需要它时才形成：join、`distinct`、成员判断。
- *新 frame = 位置关系后接列。* 结果是新 frame 的运算给出 `ι : N ⟶ N`（新位置 ↦ 旧位置），结果是 `ι ≫ x`。
- *`(lo, hi)` 窗口在 frame 上，所有列共用。* 每个运算对所有列施加同一个 `ι : N ⟶ N`，所以窗口不属于某一列。
  key 仍是位置 `pos`，`m = hi − lo`；`take`、`drop` 只移动 `lo`、`hi`；其余的 `ι`（`sortBy`、`filterBy`、`groupBy`）
  得到 `lo = 0` 的新 frame。

#tbl(c-sem, (auto, 1fr), ([运算的类别], [`ι : N ⟶ N`]),
  [`x ≫ R`：`select` `derive` `apply` `impute` `over`], [`𝟙`],
  [`filterBy`、`distinct`、semi / anti join、`sample`], [`dom(x) ≫ asc(P)`，`P ⊑ dom(x)` 是保留的位置：按原位置顺序重新编号],
  [`sortBy`、`shuffle`], [`dom(x) ≫ iasc(x ≫ a)`：`dom(x)` 上的置换],
  [`take` `drop` `range`], [`(<n)`、`(+n)`、`(<b−a) ≫ (+a)`],
  [`<>`、`union`、`melt`], [第二个 frame 的位置经 `(dom(y) ≫ (+m₁))°`：`x ∪ (dom(y) ≫ (+m₁))° ≫ y`],
  [join], [`asc(ran(⟨𝟙, K⟩)) : N ⟶ N×N`，`K : N ⟶ N` 是匹配的位置对，按 `(i, j)` 的字典序；结果后接 `x × y`],
  [`groupBy`、`aggregate`、pivot], [`firstOcc(x ≫ k)`：每组一行，按 key 第一次出现的顺序；组是 `group(x ≫ k) : N ⟶ N`（3.1）],
)

- `asc(P) : N ⟶ B`（`prims` 的一行，`P : B ⟶ B`）：`j ↦ dom(P)` 中按 `Obj.lt` 第 `j` 小的元素，即 q 在集合上的 `asc`。
  每个新位置的编号都是一次 `asc`；定义见 3.1。
- *`N` 的元素是虚的。* frame 只有 `m`：位置不落盘。
- *落盘（q / kdb 的方式）。* 目录 = 表；文件 = 列，是一个 mmap 的 `foR` `Enc`，没有序列化（`CLAUDE.md` 的 Goal）；
  `.d` 文件 = `Schema` 的列顺序；`sym` 列共用一个字典文件。

// ───────────────────────────── 3
= 运算

== 辅助定义

左栏是库（与 prelude）的定义，省略 frame 参数 `x`（两个 frame 时为 `x`、`y`）；它们只用 `Tm` 构造子、`prims` 的行与
prelude（`Rel/Programs/Prelude.lean`）。

```
// 常量与位置
!              = top(1)                         A ⟶ 1；Tm.top，1 是 prelude 的 obj 1
n̂              = ! ≫ n                          A ⟶ N 的常函数
<ₙ  ≤ₙ         = <   ≤ 在 N 上
>ₙ  ≥ₙ         = <ₙ°   ≤ₙ°                      prelude 的 > ≥
(<n)           = dom(<ₙ ≫ n°)                   Tm.dom
(+n)           = ⟨𝟙, n̂⟩ ≫ plus                  Tm.arith add；(+1) = succ；(+n)° = ⟨𝟙, n̂⟩ ≫ minus 在 i ≥ n 上
// 编号：prims 的 asc 与 prelude 的 iasc
asc(P)         : N ⟶ B                          j ↦ dom(P) 第 j 小的元素；q：asc（集合上）
iasc(c)        = asc(ran(⟨c, dom(c)⟩)) ≫ π₂     j ↦ c 第 j 小的值所在位置，相等按位置；q：iasc（稳定）
idesc(c)       = r ≫ asc(ran(⟨c, r⟩)) ≫ π₂ ≫ r   从 asc 的末端读；q：idesc（稳定）
  r            = dom(c) ≫ ⟨! ≫ count(c), succ⟩ ≫ minus    i ↦ m−1−i
firstOcc(c)    = dom(c) ≫ asc(ran(agg(c°, head)))   组号 ↦ 该值第一次出现的位置；q：x?distinct x
group(c)       = firstOcc(c) ≫ c ≫ c°           组号 ↦ 持有该值的各位置；q：group
lastOcc(c)     = agg(group(c), last)            组号 ↦ 组内最后一个位置
J(k, h)        = x ≫ k ≫ (y ≫ h)°               key 相等的左右位置对；k : C ⟶ K，h : E ⟶ K
joinOn(K)      = asc(ran(⟨𝟙, K⟩)) ≫ (x × y)      K : N ⟶ N 的位置对按 (i, j) 字典序编号
// 聚合：f 读一组位置的升序数组
agg(R, f)      = dom(R) ≫ Λ(R) ≫ f              R : A ⟶ N；Λ(R) 是 R 的像，位置升序
summarize(f)   = agg((dom(x) ≫ ⊤)°, f)          1 ⟶ D：整个 frame 是一组
count          = summarize(length)              m : 1 ⟶ N；prim length（dfn ⦇[0, π₁ succ]⦈）
over(k, f)     = ⟨x, x ≫ k ≫ agg((x ≫ k)°, f)⟩  每行带上它那一组的聚合，位置不变
win(w)         = ≥ₙ ∩ (dom(x) ≫ (+w) ≫ >ₙ ≫ dom(x))°   i ↦ i−w < j ≤ i 的每个 j
rolling(w, f)  = agg(win(w), f)
// 行的窗口
take(n)        = (<n) ≫ x
drop(n)        = (dom(x) ≫ dom(≥ₙ ≫ n°) ≫ (+n)°)° ≫ x    = (+n) ≫ x
range(a, b)    = take(b − a, drop(a))           b − a = ⟨b, a⟩ ≫ minus
dropLast(n)    = take(m − n)                    m − n < 0 时为空
takeLast(n)    = dom(x) ≫ asc(dom(x) − dom(dropLast(n))) ≫ x
filterBy(p)    = dom(x) ≫ asc(dom(x ≫ p)) ≫ x
// null（1.3）
tot(R)         = R ≫ inl ∪ (𝟙 − dom(R)) ≫ ! ≫ inr
filterJust(v)  = filterBy(dom(v ≫ inl°))        filterNothing(v) = filterBy(dom(v ≫ inr°))
shift(n)       = dom(x) ≫ tot((+n)° ≫ x)        行 i 读行 i−n；q：xprev
diff(n)        = dom(x) ≫ tot(⟨x, (+n)° ≫ x⟩ ≫ minus)   x 是一列
```

- `f` 的取法：`sum` 是 `F(x ≫ v) ≫ sum`（prim `sum`，dfn `⦇[0, plus]⦈ʳ`），`count` 是 `length`，积是
  `F(x ≫ v) ≫ ⦇[1̂, times]⦈`，`reduce` 是给定 `arith` 的 `F(x ≫ v) ≫ ⦇e, ⊕⦈`，`mean` 是 `F(x ≫ v) ≫ ⟨sum, length⟩ ≫ div`。
  `min` `max` 只选不造：`F(x ≫ v) ≫ Λ(∋) ≫ head`、`last`（`Λ(∋)` 是数组的值的升序集合）。每组第一个、最后一个值：
  `F(x ≫ v) ≫ head`、`last`。`F` 是 prim：数组逐元素后接 `x ≫ v`。
- 一个实例：`c = x ≫ a = B A B`：`agg(c°, head)` 是 `A ↦ 1`、`B ↦ 0`，`asc` 把 `{0, 1}` 编号，`firstOcc = 0 1`；
  `group(c)` 是 `0 ↦ {0, 2}`、`1 ↦ {1}`；`iasc(c)`：`⟨c, dom(c)⟩` 的像 `(A,1) (B,0) (B,2)` 升序，`π₂` 得 `1 0 2`。
  规则：每个编号都是一次 `asc`：先形成要编号的集合（位置、`(值, 位置)` 对、位置对），`asc` 按 `Obj.lt` 编号。
- 一个实例：`take(3)` 在 `m = 4` 的 `x` 上：`2 {(<3)} 2 {x} (A,1)`；`3` 被 `(<3)` 挡住，没有像。
  规则：结果是 `ι ≫ x`；`(<n)` 收 `hi`，`(+n)` 移 `lo`，其余的 `ι` 得到 `lo = 0` 的新 frame（第 2 节）。

== DataHaskell `dataframe` 的导出函数

函数表取自 `DataFrame.hs` 的导出与 `DataFrame.Operations.*`、`DataFrame.Functions`（github.com/DataHaskell/dataframe，`main`）。

#tbl(c-syn, (auto, 1.55fr, 1fr), ([Haskell 函数], [Rel 复合], [说明 / finding]),
  [`select` `exclude` `selectBy`], [`x ≫ ⟨col S "a", col S "b"⟩`], [列名在 elaboration 时检查],
  [`rename` `renameMany`], [`x ≫ col S "c"`，换名字], [同上],
  [`derive` `deriveMany` `deriveWithExpr` `insert*` `cloneColumn`], [`x ≫ ⟨𝟙, e⟩`], [同上],
  [`apply` `applyMany` `applyInt` `applyDouble` `safeApply` `applyAtIndex`], [`x ≫ ⟨a ≫ e, b⟩`],
    [`e` 是构造子与 `arith` 的复合；任意 Haskell 函数：F7],
  [`applyWhere`], [`x ≫ applyWhere(p, e)`，`applyWhere(p, e) = p ≫ e ∪ (𝟙 − p)`], [],
  [`filter` `filterWhere` `filterBy`], [`filterBy(p)`，如 `p = dom(a ≫ < ∩ b)`], [],
  [`filterJust` `filterAllJust`], [`filterJust(v)`], [],
  [`filterNothing` `filterAllNothing`], [`filterNothing(v)`], [],
  [`take` `drop` `takeLast` `dropLast` `range` `byIndexRange` `cube`], [`take(n)` `drop(n)` `takeLast(n)` `dropLast(n)` `range(a, b)`], [],
  [`selectRows`], [`ix ≫ x`，`ix : N ⟶ N` 是输入的下标 frame], [],
  [`sortBy`], [`sortBy(a) = dom(x) ≫ iasc(x ≫ a) ≫ x`；降序用 `idesc`], [`iasc` 稳定：稳定排序就是规格，是相等而不是 refinement],
  [`topBy`], [`topBy(n, a) = take(n, sortBy(a))`], [],
  [`distinct`], [`distinct = firstOcc(x) ≫ x`], [按第一次出现的顺序：`B A B` → `B A`],
  [`groupBy`], [组 `group(x ≫ k)`；组的 key `firstOcc(x ≫ k) ≫ x ≫ k`], [],
  [`aggregate`], [`aggregate(k, f) = ⟨firstOcc(x ≫ k) ≫ x ≫ k, agg(group(x ≫ k), f)⟩`], [],
  [`sum` `mean` `count` `countAll` `minimum` `maximum` `reduce`], [`summarize(f)`，`f` 见 3.1；`count = m`],
    [`mean` 只有整数除法，浮点：F4],
  [`variance` `stddev` `skewness` `correlation` `zScore`], [无], [要浮点算术：F4],
  [`median` `percentile` `genericPercentile` `interQuartileRange`],
    [`median(a) = summarize(F(M ≫ a) ≫ ⟨sum, length⟩ ≫ div, M)`，`M = dom(d ≫ ≤ₙ ≫ m°) ≫ dom(d ≫ succ ≫ succ ≫ ≥ₙ ≫ m°) ≫ sortBy(a)`，`d = ⟨𝟙, 𝟙⟩ ≫ plus`；
    `percentile(r) = ⟨⟨m, r̂⟩ ≫ times, 100̂⟩ ≫ div ≫ sortBy(a) ≫ a`],
    [`M` 是排序后 `2i ≤ m ≤ 2i+2` 的一或两行，取整数均值；`percentile` 的 `r·m` 为浮点时 F4],
  [`countDistinct` `mode`], [`countDistinct = count(distinct(x ≫ a))`；`mode(a) = summarize(head, s) ≫ s`，`s = idesc(u ≫ π₂) ≫ u ≫ π₁`，`u = valueCounts(a)`],
    [`mode` 在并列中取先出现的（`idesc` 稳定）],
  [`collect`], [`collect(k, c) = aggregate(k, F(x ≫ c))`], [结果列的类型是 `Obj.arr V`],
  [`firstOrNothing` `lastOrNothing`], [`tot(summarize(head) ≫ x)`、`tot(summarize(last) ≫ x)`],
    [空 frame 得 null；每组一行：`firstOcc(x ≫ k) ≫ x`、`lastOcc(x ≫ k) ≫ x`],
  [`topK` `bottomK` `kExtremes`], [`take(n, dom(x) ≫ idesc(x ≫ a) ≫ x)`；`bottomK = topBy(n, a)`], [],
  [`valueCounts` `valueProportions` `frequencies`], [`valueCounts(v) = aggregate(v, length)`], [比例要浮点除法：F4],
  [`summarize` `describeColumns` `nulls`], [上面各聚合的 pair；`nulls = count(x ≫ v ≫ inr°)`], [浮点的 mean / std：F4],
  [`innerJoin` `join` `joinOn`], [`innerJoin(k, h) = joinOn(J(k, h))`], [],
  [`leftJoin`], [`leftJoin(k, h) = asc(ran(⟨𝟙, dom(x) ≫ tot(J(k, h))⟩)) ≫ (x × (y ⊕ 𝟙))`],
    [`y ⊕ 𝟙 = [y ≫ inl, inr]`（prelude）：没有匹配的行右侧为 null（`E+1`）],
  [`rightJoin`], [`leftJoin` 交换两侧], [],
  [`fullOuterJoin`], [`append(leftJoin(k, h) ≫ (inl × 𝟙), antiJoin(h, k, y, x) ≫ ⟨! ≫ inr, inl⟩)`], [两侧都是和类型],
  [`union`], [`union = distinct(append(x, y))`], [],
  [`intersect`], [`intersect = distinct(semiJoin(𝟙, 𝟙))`], [],
  [`difference` `symmetricDifference`], [`difference = distinct(antiJoin(𝟙, 𝟙))`；对称差是两个方向的 `difference` 的 `union`], [],
  [`<>`（行拼接）], [`append(x, y) = x ∪ (dom(y) ≫ (+m₁))° ≫ y`], [`sym` 列先合并字典（`rel-architecture` §4.3）],
  [`|||`（列拼接）], [`⟨x, y⟩`], [F9],
  [`impute` `imputeWith` `fromMaybe` `castWithDefault`], [`x ≫ v ≫ [𝟙, c]`], [`c : 1 ⟶ V`；`imputeWith` 的 `c` 是一个聚合],
  [`toMaybe` `isJust` `isNothing` `isNull` `fromJust` `whenPresent`], [`inl`、`dom(inl°)`、`dom(inr°)`、`inl°`、`[e ≫ inl, inr]`], [],
  [`recode` `recodeWithDefault`], [`x ≫ v ≫ T`；带缺省 `x ≫ v ≫ tot(T) ≫ [𝟙, c]`], [`T` 是 `Tm.val` 的字面量表],
  [`lift` `lift2` `nullLift` `bind`], [无], [F7],
  [`cast` `toDouble` `div` `mod` `pow` `relu` `eq` `lt` `and` `or` `not` …],
    [`div` `mod` 是 `arith`；`eq` 是 `𝟙`，`lt` 是 `<`；`and` `or` `not` 是 coreflexive 的 `∩` `∪` `−`；`relu = ⟨𝟙, 0̂⟩ ≫ max`],
    [整数 / 浮点转换、`pow`：F4],
  [`over`], [`over(k, f)`], [每行带上它那一组的聚合，位置不变],
  [`contains` `length` `splitOn` `match` `matchAll`], [`contains(s) = dom(suffix ≫ prefix ≫ s)`；`length` 是 prim], [`splitOn` `match`：F3],
  [`parseDate` `daysBetween`], [无], [`daysBetween` 是 `date` 上的 `minus`：F4、F5；`parseDate`：F3],
  [`sample` `shuffle` `randomSplit` `kFolds` `stratifiedSample` `mkRandom`], [无], [F8],
  [`fromList` `fromRows` `fromColumns` `fromUnboxedVector` `empty`], [字面量 `Tm.val`，或 `⟨x, y⟩`], [],
  [`columnAsVector` `columnAsList` `toList` `toRowList` `to*Matrix`], [`summarize(F(x ≫ c))`], [位置顺序的数组],
  [`dimensions` `nRows` `nColumns` `columnNames`], [`m`；其余读 `Schema`], [],
  [`readCsv` `readTsv` `readParquet` `readJSON` `writeCsv` `writeParquet`], [无], [F1、F6],
  [`scanCsv` `scanParquet` `fromDataFrame` `run`（Lazy）], [`main` 的关系参数（`input`）、`rel_program` 中的定义、`output`], [`rel_program` 本身就是 plan：`rel-architecture` §1],
  [`fold`、`display`、Plot、`DecisionTree`、`KMeans` 等], [不在本设计范围], [宿主层的工具与模型库],
)

== polars 多出来的运算

#tbl(c-sem, (auto, 1.55fr, 1fr), ([polars], [Rel 复合], [说明 / finding]),
  [semi / anti join], [`semiJoin(k, h) = dom(x) ≫ asc(dom(J(k, h))) ≫ x`；`antiJoin(k, h) = dom(x) ≫ asc(dom(x) − dom(J(k, h))) ≫ x`], [],
  [cross join], [`crossJoin = joinOn(dom(x) ≫ ⊤ ≫ dom(y))`], [],
  [asof join], [`⟨x, tot((J≤ − J≤ ≫ >ₜ) ≫ y)⟩`],
    [`J≤ = x ≫ ⟨k, t⟩ ≫ (𝟙 × ≥) ≫ ⟨h, u⟩° ≫ y°`，`>ₜ = y ≫ u ≫ > ≫ u° ≫ y°`：减去后留下时间最近的；`ι = 𝟙`],
  [`cum_sum` 等], [`agg(dom(x) ≫ ≥ₙ, f)`], [行 `i` 聚合 `j ≤ i` 的行],
  [`shift(k)`], [`shift(k)`], [前 `k` 个位置是 null],
  [`diff`], [`diff(1)` 作用在 `x ≫ v` 上], [`v(i) − v(i−1)`，第 0 行 null],
  [`rolling(w)`], [`rolling(w, f)`], [],
  [`forward_fill`], [`(M ∪ (dom(x) − dom(M))) ≫ x ≫ v`，`M = agg(dom(x) ≫ ≥ₙ ≫ dom(x ≫ v ≫ inl°), last)`],
    [每行取不晚于它的最近非 null 行；之前没有非 null 的行保留自己的 null],
  [`melt` / `unpivot`], [`pivotLong(i, s, a, t, b) = append(x ≫ ⟨i, ⟨! ≫ s, a⟩⟩, x ≫ ⟨i, ⟨! ≫ t, b⟩⟩)`；`melt(s, a, t, b) = pivotLong(𝟙, s, a, t, b) ≫ π₂`],
    [每行对每个值列一次，得 `(id, 列名, 值)`；各列要同类型],
  [pivot（long）], [`aggregate(⟨k, q⟩, f)`], [long 形式就是 key 为 `K×P` 的 frame],
  [pivot（wide）], [`firstOcc(x ≫ k) ≫ x ≫ k ≫ ⟨𝟙, tot(⟨𝟙, ! ≫ α⟩ ≫ G), …⟩`，`G = agg((x ≫ ⟨k, q⟩)°, f)`], [每个声明的 `α ∈ P` 一列：F1],
)

// ───────────────────────────── 4
= Findings

写不出来、或只能别扭地写出来的运算。

- *F1 依赖数据的 schema 无法给出类型。* wide pivot、`get_dummies`、读文件时推断 schema：结果的 `Obj` 要读了值才知道，
  而 `Tm A B` 在 elaboration 时固定 `B`。wide pivot 只对声明的有限 `obj P` 可写；long 形式是忠实的那个。
  读文件要声明 schema，或在 elaboration 时读 `.d`。
- *F3 字符串别扭。* 字符串是 `arr char`，单元格里的值，不是 frame（F9）；`contains` 的规格要形成全部子串。
  正则是「步骤为转移表」的 fold，把正则编译成表在语言之外。
- *F4 atom 覆盖。* `Tm.arith`、`leq`、`lt` 只在 `i64` 上；dataframe 需要它们在每个有序 atom 上（`date` 的 `minus` 即
  `daysBetween`）。已决定：`arith`、`lt` 以 atom 为下标；尚未实现。`arith` 只有 `plus` `minus` `times` `div` `mod` `max` `min`：
  没有浮点运算，所以 `mean` 只有整数除法，`variance` `stddev` `skewness` `correlation` `zScore` `valueProportions`、
  浮点的 `percentile` 写不出；没有 `pow`，整数 / 浮点互转、`fround` 也没有。
- *F5 时间类型。* `date`、`datetime` 是整数 code，没有时区。日历运算（取月份、截断到月）是整数算术加上与日历表的 join。
- *F6 IO 在代数之外。* 程序读的 frame 是 `main` 的关系参数（`input`）；CSV、Parquet、JSON 的解析不是列上的关系。
- *F7 宿主函数。* `lift`、`lift2`、`apply`、`bind` 接受任意 Haskell 函数；Rel 只有 `Op` 的有限集合及其复合。
  这也是 polars 表达式（不含 `map_elements`）同样的限制。
- *F8 抽样。* `sample(n)` 是有多个像的关系（任意 n 行），实现选其中一个，是规格的 refinement，不是相等。
- *F9 位置模型之外的两处。* 单元格里的 list（`Obj.arr`：字符串、`collect` 的结果）是一个值，`N` 只给 frame 的行编号。
  `⟨x, y⟩` 的定义域是 `dom(x) ∩ dom(y)`，长度不等时取较短的；要「不等长无像」须另加 `dom(x) = dom(y)` 的检查。
