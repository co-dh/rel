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
一个 frame 是从位置对象 `N` 出发、定义域为 `(<m)` 的部分 map，记作 `[C]`；只存长度 `m`。

#tbl(c-syn, (auto, auto, 1fr), ([记号], [类型], [含义]),
  [`N`], [对象], [位置（自然数），所有 frame 共用；元素不存储],
  [`x` `y`], [`[C]`], [一个 frame：部分 map `x : N ⟶ C`，`dom(x) = (<m)`（第 2 节）。第 `a` 列是 `x ≫ a`；`[C]` 是这类 map 的类型],
  [`m`], [自然数], [frame 的长度；两个 frame 时写 `m₁` `m₂`],
  [`(<n)`], [`N ⟶ N`], [coreflexive：只放过 `i < n`],
  [`(+n)`], [`N ⟶ N`], [函数 `i ↦ i+n`；`(+n)°` 是 `i ↦ i−n`，只在 `i ≥ n` 有像],
  [`≤ₙ` `<ₙ`], [`N ⟶ N`], [位置的序],
  [`ι` `σ`], [`N ⟶ N`], [新位置到旧位置的关系；`σ` 专指 `(<m)` 上的置换。结果的列是 `ι ≫ x`],
  [`S`], [`Schema`], [行的类型：带列名的列类型表；`S.obj` 是其积],
  [`a` `v`], [`col S "…"`], [一列：一个投影（`π₁` `π₂` 的复合）],
  [`k`], [`col S "…"`], [key 列（一个投影，或若干投影的 pair）],
  [`p`], [`C ⟶ C`], [谓词，写成 coreflexive],
  [`e`], [`C ⟶ V`], [一行之内的表达式],
  [`!`], [`A ⟶ 1`], [到 prelude 的终对象 `1` 的 `⊤`],
  [`F(R)`], [`[A] ⟶ [B]`], [后接 `R`：`x ↦ x ≫ R`，位置不变（`ι = 𝟙`）],
)

// ───────────────────────────── 1
= 数据模型

== frame 的值

- frame 是 `Vals C n`（`Rel/Run/Core.lean:456`），不新增类型；列的布局见 `rel-architecture` §4.3『原子类型：都是 foR 的 code』。
  它表示的关系、行的编号与落盘方式在第 2 节。
- 一个运算是 `[C] ⟶ [C']`，与 Haskell 的 `DataFrame -> DataFrame` 一一对应。
- 值为集合的结果（组的 key、`distinct`）按 Rel 的 canonical 约定存成 `asc` 之后 `distinct`：见 `rel-architecture` §4.5『allegory 运算 → kernel』。

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
  [`Word16` … `Word64`], [无], [F4],
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
  [和类型 `v : C ⟶ V+1`], [第 3 个元素是 `inr(∗)`], [*采用*：每列都是全函数，`F(⟨a, v⟩)` 不丢行],
  [部分列 `v ≫ inl°`], [第 3 行没有像], [派生的读法：表达式里与 null 比较的行被 `filter` 去掉，和 polars 一致],
)

- `tot(R) = R ≫ inl ∪ (𝟙 − dom(R)) ≫ ! ≫ inr`：把部分的 `R : A ⟶ B` 变回全的 `A ⟶ B+1`（`R` 有值取值，否则 null）。
- 存储：`V+1` 是 tag 列加等长的值列（就地布局），没有位置列，因为位置不存储（第 2 节）。

// ───────────────────────────── 2
= 存储与顺序

一个实例：frame `[(A,1),(B,2),(A,1)]` 是 `a : N ⟶ K`、`b : N ⟶ V`，`m = 3`：`0 {a} A`，`0 {b} 1`，`2 {a} A`，`2 {b} 1`，`3` 没有像。
第 0 行与第 2 行是 `N` 的不同元素，所以是两行；`a° ≫ b` 只有 `A ↦ 1`、`B ↦ 2` 两对。

- *语义是集合。* 没有 bag，也没有 list 对象。frame 是一族从同一个 `N` 出发的部分 map，定义域都是 `(<m)`。以 `N` 为 key 它已经是
  `asc`、`distinct` 的，不需要排序。`a° ≫ b : A ⟶ B`（排序并去重）只在运算的规格需要它时才形成：join、`distinct`、成员判断。
- *新 frame = 位置关系后接列。* 结果是新 frame 的运算给出 `ι : N ⟶ N`（新位置 ↦ 旧位置），结果是 `ι ≫ x`。
- *`(lo, hi)` 窗口在 frame 上，所有列共用。* 每个运算对所有列施加同一个 `ι : N ⟶ N`，所以窗口不属于某一列。
  key 仍是位置 `pos`，`m = hi − lo`；`take`、`drop` 只移动 `lo`、`hi`；构造新数组的运算（按 `σ` 的 `gather`、`filter` 的压紧、
  `groupBy`）得到 `lo = 0` 的 frame。

#tbl(c-sem, (auto, 1fr), ([运算的类别], [`ι : N ⟶ N`]),
  [`F(R)`：`select` `derive` `apply` `impute` `over`], [`𝟙`],
  [`filter`、`distinct`、semi / anti join、`sample`], [`where(P)`，`P ⊑ (<m)` 是保留的位置：按原位置顺序重新编号],
  [`sortBy`、`shuffle`], [`(<m)` 上的置换 `σ`],
  [`take` `drop` `range`], [`(<n)`、`(+n)`、`(<b−a) ≫ (+a)`],
  [`cat`、`union`、`melt`], [第二个 frame 的位置经 `(+m₁)°`：`x ∪ (+m₁)° ≫ y`],
  [join], [`where(J) : N ⟶ N×N`，`J` 是匹配的位置对，按 `(i, j)` 的字典序；结果 `where(J) ≫ (x × y)`],
  [`groupBy`、`aggregate`、pivot], [`first(k)`：每组一行，按 key 第一次出现的顺序；组是 `g(k)° : N ⟶ N`（3.1）],
)

- `where(P) : N ⟶ A`（有序对象 `A` 上的有限集合 ↦ 按顺序编号；即 q 的 `where`：`where 0 1 1 0 1` 是 `1 2 4`）是顺序进入的唯一位置（`CLAUDE.md`）。
  `A = N` 时 `where(P) = (P ≫ cnt(P))°`；`A = K` 时是 canonical 约定（1.1）。
- *`N` 的元素是虚的。* frame 只有 `m`：位置不落盘。
- *落盘（q / kdb 的方式）。* 目录 = 表；文件 = 列，是一个 mmap 的 `foR` `Enc`，没有序列化（`CLAUDE.md` 的 Goal）；
  `.d` 文件 = `Schema` 的列顺序；`sym` 列共用一个字典文件。

// ───────────────────────────── 3
= 运算

== 辅助定义

```
take(n)       = (<n) ≫ x                       hi := min(hi, lo+n)
drop(n)       = (+n) ≫ x                       lo += n；长度 m ∸ n，因为 x 在 ≥ m 处无像
range(a, b)   = (<b−a) ≫ (+a) ≫ x              takeLast(n) = drop(m ∸ n)    dropLast(n) = take(m ∸ n)
cnt(P)        : N ⟶ N  = Λ(>ₙ ≫ P) ≫ size      P ⊑ (<m)：i 之前 P 中的位置个数
where(P)       : N ⟶ N  = (P ≫ cnt(P))°         新位置 ↦ P 的第 i 个元素
filter(p)     = where(dom(x ≫ p)) ≫ x
σ = asc(x ≫ a)                                 (<m) 上的双射，按 ⟨x ≫ a, 𝟙⟩ 的字典序单调，所以唯一
new(a)        = (<m) − dom(x ≫ a ∩ >ₙ ≫ x ≫ a)   没有更早的 j < i 与 i 的 a 相同：scan，carrier 是已见集合
first(a)      : N ⟶ N = where(new(a))           每个 a 值第一次出现的位置，按第一次出现的顺序
g(a)          : N ⟶ N = x ≫ a ≫ (first(a) ≫ x ≫ a)°               组号：i 的 a 值在 first(a) 中的编号
last(a)       : N ⟶ N = agg(max, g(a)°, 𝟙)      每组最大的位置，按组号（第一次出现的顺序）：位置按 g 覆盖写入
J             = x ≫ k ≫ h° ≫ y°  : N ⟶ N        key 相等的左右位置对；k : C ⟶ K，h : E ⟶ K
fold(⊕, y)    : P(N) ⟶ V                       位置集合 P ↦ where(P) ≫ y 按位置顺序的 ⦇e, ⊕⦈
agg(⊕, R, y)  = Λ(R) ≫ fold(⊕, y)              R : A ⟶ N；每个 a 对它的位置做一次 fold
win(w)        = ≥ₙ ∩ <ₙ ≫ (+w)°                i ↦ i−w < j ≤ i 的每个 j
```

- 一个实例：`x ≫ a = B A B`：`0` 时已见 `∅`，留；`1` 时 `A ∉ {B}`，留；`2` 时 `B ∈ {B, A}`，丢。`first = 0 1`，`g = 0 1 0`。
  规则：`new`、`g` 是同一次 scan，已见集合在编码列（sym、字典 id，值是 `0..card−1`）上是 card 位的 bitmap，
  一般值上是 hash；扫描一遍，O(m)。列已有序时已见集合退化为「前一个值」。

- 一个实例：`take(3)` 在 `m = 4` 的 `x` 上：`2 {(<3)} 2 {x} (A,1)`；`3` 被 `(<3)` 挡住，没有像。
  规则：结果是 `ι ≫ x`；coreflexive `(<n)` 收 `hi`，`(+n)` 移 `lo`，其余的 `ι` 得到 `lo = 0` 的新 frame（第 2 节）。

== DataHaskell `dataframe` 的导出函数

函数表取自 `DataFrame.hs` 的导出与 `DataFrame.Operations.*`、`DataFrame.Functions`（github.com/DataHaskell/dataframe，`main`）。

#tbl(c-syn, (auto, 1.55fr, 1fr), ([Haskell 函数], [Rel 复合], [说明 / finding]),
  [`select` `exclude` `selectBy`], [`F(⟨col S "a", col S "b"⟩)`], [列名在 elaboration 时检查],
  [`rename` `renameMany`], [`F(col S "c")`，换名字], [列名在 elaboration 时检查],
  [`derive` `deriveMany` `deriveWithExpr` `insert*` `cloneColumn`], [`F(⟨𝟙, e(col S "c")⟩)`], [列名在 elaboration 时检查],
  [`apply` `applyMany` `applyInt` `applyDouble` `safeApply` `applyAtIndex`], [`F(⟨a ≫ g, b⟩)`],
    [`g` 必须是 `Op` 的复合；任意 Haskell 函数没有对应的项（F7）],
  [`applyWhere`], [`F(p ≫ ⟨a ≫ g, b⟩ ∪ (𝟙 − p))`], [两个 mask 分支的并],
  [`filter` `filterWhere` `filterBy`], [`where(dom(x ≫ p)) ≫ x`，如 `p = dom(a ≫ < ∩ b)`], [],
  [`filterJust` `filterAllJust`], [`filter(dom(v ≫ inl°))`], [],
  [`filterNothing` `filterAllNothing`], [`filter(dom(v ≫ inr°))`], [],
  [`take` `drop` `takeLast` `dropLast` `range` `byIndexRange` `cube`], [`(<n) ≫ x`、`(+n) ≫ x`、`(<b−a) ≫ (+a) ≫ x`], [只改 `lo`、`hi`],
  [`selectRows`], [`ix ≫ x`，`ix : N ⟶ N` 是输入的下标 frame], [下标来自数据],
  [`sortBy`], [`σ ≫ x`，`σ = asc(x ≫ a)`], [位置 `𝟙` 作次 key，`σ` 唯一：稳定排序就是规格，是相等而不是 refinement],
  [`topBy`], [`(<n) ≫ σ ≫ x`], [],
  [`distinct`], [`first(𝟙) ≫ x`], [按第一次出现的顺序；一次 scan 加 `where`。`B A B` → `B A`],
  [`groupBy`], [组号 `g(k)`；组是 `g(k)° : N ⟶ N`，组的 key 是 `first(k) ≫ x ≫ k`], [组按 key 第一次出现的顺序],
  [`aggregate`], [`⟨first(k) ≫ x ≫ k, agg(⊕, g(k)°, x ≫ v)⟩`], [`g` 一次 scan；按组号累加 `⊕` 也是一遍，但要求写入时带 `⊕` 的 scatter（今天的 `scatter` 只覆盖）],
  [`sum` `mean` `count` `countAll` `minimum` `maximum` `reduce`], [`fold(⊕, x ≫ v)(dom(x))`，`⊕ = add`、`min`、…；`count = m`；`mean = ⟨sum, count⟩ ≫ fdiv`], [`Op` 的 fold],
  [`variance` `stddev` `skewness` `correlation` `zScore`], [若干 fold 的 pair 再做算术], [],
  [`median` `percentile` `genericPercentile` `interQuartileRange`], [`i ≫ σ ≫ x ≫ v`，`σ = asc(x ≫ v)`，`i = ⌊r·m⌋ : 1 ⟶ N`],
    [一个位置，读一个元素],
  [`countDistinct` `mode`], [`size(ran(x ≫ v))`；`mode` 对 `agg(count, …)` 接 `est`], [],
  [`collect`], [每组 `where(P) ≫ x ≫ v`，`P` 是该组的位置], [结果列的类型是 `Obj.arr V`],
  [`firstOrNothing` `lastOrNothing`], [`first(k) ≫ x ≫ ⟨k, v⟩`、`last(k)` 同理], [每组一行，按 key 第一次出现的顺序],
  [`topK` `bottomK` `kExtremes`], [`(<n) ≫ σ ≫ x`，`σ` 降序或升序], [],
  [`valueCounts` `valueProportions` `frequencies`], [`groupBy` + `aggregate`，`⊕ = count`], [],
  [`summarize` `describeColumns` `nulls`], [固定的一组聚合的 pair], [输出的列由 schema 决定，静态可知],
  [`innerJoin` `join` `joinOn`], [`where(J) ≫ (x × y)`，`J = x ≫ k ≫ h° ≫ y°`], [列名在 elaboration 时检查],
  [`leftJoin`], [`where(dom(x) ≫ tot(J)) ≫ (x × [y ≫ inl, inr])`], [`tot(J) : N ⟶ N+1`，无匹配的左位置配 `inr`；右侧整行为 null（`E+1`）；F2],
  [`rightJoin`], [`leftJoin` 交换两侧], [],
  [`fullOuterJoin`], [`leftJoin` 之后 `cat` 上 `where(dom(y) − ran(J)) ≫ y`], [两侧都是和类型],
  [`union`], [`cat` 后 `distinct`；`cat = x ∪ (+m₁)° ≫ y`], [],
  [`intersect`], [`where(dom(J)) ≫ x` 后 `distinct`，`k = h = 𝟙`], [],
  [`difference` `symmetricDifference`], [`where(dom(x) − dom(J)) ≫ x` 后 `distinct`], [],
  [`<>`（行拼接）], [`x ∪ (+m₁)° ≫ y`], [`sym` 列字典不同时先合并字典（`rel-architecture` §4.3 的 intern）],
  [`|||`（列拼接）], [`⟨x, y⟩`], [定义域 `dom(x) ∩ dom(y)`，长度不等时取较短的（F9）],
  [`impute` `imputeWith` `fromMaybe` `castWithDefault`], [`F(v ≫ [𝟙, ! ≫ c])`], [`c : 1 ⟶ V`；`imputeWith` 的 `c` 是一个聚合],
  [`toMaybe` `isJust` `isNothing` `isNull` `fromJust` `whenPresent`], [`inl`、`dom(inl°)`、`dom(inr°)`、`inl°`、`[g ≫ inl, inr]`], [],
  [`recode` `recodeWithDefault`], [`F(v ≫ T)`，`T` 是字面量表；带缺省用 `tot`], [],
  [`lift` `lift2` `nullLift` `bind`], [无], [宿主语言的任意函数没有项（F7）],
  [`cast` `toDouble` `div` `mod` `pow` `relu` `eq` `lt` `and` `or` `not` …], [`Op` 的 constructor], [整数 / 浮点转换没有 `Op`（F4）],
  [`over`], [`⟨x, x ≫ k ≫ agg(⊕, (x ≫ k)°, x ≫ v)⟩`], [每行带上它那一组的聚合，位置不变],
  [`contains` `length` `splitOn` `match` `matchAll`], [`contains(s) = dom(suffix ≫ prefix ≫ s)`], [字符串：F3],
  [`parseDate` `daysBetween`], [`date` 上的整数减法；`parseDate` 是字符串解析], [F3、F5],
  [`sample` `shuffle` `randomSplit` `kFolds` `stratifiedSample` `mkRandom`], [`where(P) ≫ x`，`P ⊑ dom(x)`、`size(P) = n`；`σ ≫ x`，`σ` 是 `(<m)` 上任一置换], [规格有多个像（F8）],
  [`fromList` `fromRows` `fromColumns` `fromUnboxedVector` `empty`], [字面量 `Tm.val`，或 `⟨x, y⟩`], [],
  [`columnAsVector` `columnAsList` `toList` `toRowList` `to*Matrix`], [`F(col S "c")`，在输出边界读出], [列名在 elaboration 时检查],
  [`dimensions` `nRows` `nColumns` `columnNames`], [`m`；其余读 `Obj`], [],
  [`readCsv` `readTsv` `readParquet` `readJSON` `writeCsv` `writeParquet`], [无], [IO 在代数之外；schema 推断见 F1、F6],
  [`scanCsv` `scanParquet` `fromDataFrame` `run`（Lazy）], [`input` 声明、`rel_program` 中的定义、`output`], [`rel_program` 本身就是 plan：`rel-architecture` §1],
  [`fold`、`display`、Plot、`DecisionTree`、`KMeans` 等], [不在本设计范围], [宿主层的工具与模型库],
)

== polars 多出来的运算

#tbl(c-sem, (auto, 1.55fr, 1fr), ([polars], [Rel 复合], [说明 / finding]),
  [semi / anti join], [`where(dom(J)) ≫ x`；anti 用 `where(dom(x) − dom(J)) ≫ x`], [],
  [cross join], [`where(dom(x) ≫ ⊤ ≫ dom(y)) ≫ (x × y)`], [],
  [asof join], [`⟨x, tot(last(J≤) ≫ y)⟩`],
    [`J≤ = x ≫ ⟨k,t⟩ ≫ (𝟙 × ≥) ≫ ⟨h,u⟩° ≫ y°`，右表按时间有序时 `last` 是最近的；位置是左表的，`ι = 𝟙`],
  [`cum_sum` 等], [`c = μ c. (<1) ≫ x ≫ v ∪ ⟨(+1)° ≫ c, x ≫ v⟩ ≫ ⊕`], [`c(i) = c(i−1) ⊕ v(i)`],
  [`shift(k)`], [`(<m) ≫ tot((+k)° ≫ x)`], [值是同一列的切片；前 `k` 个位置是 null],
  [`diff`], [`⟨(+1) ≫ x ≫ v, x ≫ v⟩ ≫ minus`], [同一列的两个切片],
  [`rolling(w)`], [`dom(x) ≫ agg(f, win(w), x ≫ v)`], [],
  [`forward_fill`], [`c = μ c. W ≫ x ≫ v ∪ (dom(x) − W) ≫ (+1)° ≫ c`，`W = dom(x ≫ v ≫ inl°)`], [非 null 的行取自己的值，其余取前一行的结果],
  [`melt`], [`x ≫ ⟨! ≫ α, a⟩ ∪ (+m)° ≫ x ≫ ⟨! ≫ β, b⟩ : N ⟶ P×V`], [各列要同类型],
  [pivot（long）], [`groupBy(⟨k, q⟩)` + `aggregate`], [long 形式就是 key 为 `K×P` 的 frame],
  [pivot（wide）], [`first(k) ≫ x ≫ k ≫ ⟨𝟙, tot(⟨𝟙, ! ≫ α⟩ ≫ agg(f, (x ≫ ⟨k, q⟩)°, x ≫ v)), …⟩`], [每个声明的 `α ∈ P` 一列；只对声明的 `obj P = {α, β}` 可写（F1）],
)

// ───────────────────────────── 4
= Findings

写不出来、或只能别扭地写出来的运算。

- *F1 依赖数据的 schema 无法给出类型。* wide pivot、`get_dummies`、读文件时推断 schema：结果的 `Obj` 要读了值才知道，
  而 `Tm A B` 在 elaboration 时固定 `B`。wide pivot 只对声明的有限 `obj P` 可写；long 形式是忠实的那个。
  读文件要声明 schema，或在 elaboration 时读 `.d`。
- *F2 null。* outer join 的两支见主表 `leftJoin`。null 上的布尔运算（Kleene `or`）要用 `[R, S]` 逐情况写。
- *F3 字符串别扭。* 字符串是 `arr char`，单元格里的 list，不在位置模型里（F9）；`contains` 的规格要形成全部子串。
  正则是「步骤为转移表」的 fold，把正则编译成表在语言之外。
- *F4 atom 覆盖。* 没有 `u8` 以上的无符号整数，没有 `i128`。`Tm.arith`、`leq`、`lt` 只在 `i64` 上并带一个数的 universe；
  dataframe 需要它们在每个有序 atom 上。整数 / 浮点互转、`fround` 没有 `Op`。
- *F5 时间类型。* `date`、`datetime` 是整数 code，没有时区。日历运算（取月份、截断到月）是整数算术加上与日历表的 join。
- *F6 IO 在代数之外。* CSV、Parquet、JSON 的解析不是列上的关系。
- *F7 宿主函数。* `lift`、`lift2`、`apply`、`bind` 接受任意 Haskell 函数；Rel 只有 `Op` 的有限集合及其复合。
  这也是 polars 表达式（不含 `map_elements`）同样的限制。
- *F8 抽样。* `sample(n)` 是有多个像的关系（任意 n 行），实现选其中一个，是规格的 refinement，不是相等。
- *F9 位置模型之外的两处。* 单元格里的 list（`Obj.arr`：字符串、`collect` 的结果）仍是 list，`N` 只给 frame 的行编号。
  `⟨x, y⟩` 的定义域是 `dom(x) ∩ dom(y)`，长度不等时取较短的；要「不等长无像」须另加 `dom(x) = dom(y)` 的检查。
- *F10 `groups(k)` 在今天的语言里写不出。* `rel_program` 拒绝它（`unknown name 'str'`：`strₗ` 不在 prims，带 key 的
  `foldI` 是 gap）。能写的只有绕法：carrier 带 key 的左 fold，按 `K` 的整个 universe 各 seed 一次，要求 `K` 是声明过的
  有限对象，代价 |K|×m。rel-lazy 正在解决：`groups(k)` 与 `filter(p)` 已写成复合，不加 `Tm` 节点。
