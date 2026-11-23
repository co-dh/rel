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

// an API table: each row is (function, composition, note, status); the counts are read from the same rows
#let st = (full: "全", part: "部分", no: "无", out: "范围外")
#let apitbl(color, head, rows) = tbl(color, (auto, 1.55fr, 1fr, auto), head,
  ..rows.map(r => (r.at(0), r.at(1), r.at(2), text(font: "Noto Sans CJK SC", st.at(r.at(3))))).flatten())
#let tally(rows) = st.pairs().map(((k, v)) => v + " " + str(rows.filter(r => r.at(3) == k).len())).join("、")

// ───────────────────────────── title
#align(center)[
  #text(24pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[DataFrame 到 Rel 的映射] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[DataHaskell `dataframe` 与 polars 的运算，写成 Rel 的关系代数项]
]
#v(6pt)

Rel 本身（`Obj`、`Tm`、kernel、编码、原子、`compile`）见 `rel-architecture`；本文只讲 dataframe 怎样写成 Rel。
一个 frame 是从位置对象 `N` 出发、定义域为 `(<m)` 的部分 map `x : N ⟶ C`；只存长度 `m`。
库是 `Rel/Programs/Frame.lean`、`FrameGroup.lean`、`FrameJoin.lean`（程序 `frame`、`frameGroup`、`frameJoin`；实数统计在 `FrameGroup.lean` 的程序 `frameStat`）。
复合按图序写成并置：`R S` 先 `R` 后 `S`。

#tbl(c-syn, (auto, auto, 1fr), ([记号], [类型], [含义]),
  [`N`], [对象], [位置（自然数），所有 frame 共用；元素不存储。`N` 是无界的 `obj N`（没有右侧，`rel-architecture` §0），
    关系按需运行，所以 verb 读的位置都从 `dom(x)` 来：新位置的编号写成 `dom(x) asc(…)`],
  [`x` `y`], [`N ⟶ C`], [一个 frame：部分 map，`dom(x) = (<m)`（第 2 节）。第 `a` 列是 `x a`],
  [`m`], [`1 ⟶ N`], [frame 的长度 `count(x)`；两个 frame 时写 `m₁` `m₂`],
  [`n` `w`], [`1 ⟶ N`], [常量；`⊤ n` 是取值 `n` 的常函数],
  [`(<n)`], [`N ⟶ N`], [coreflexive `dom(< n°)`：只放过 `i < n`],
  [`(+n)`], [`N ⟶ N`], [函数 `⟨𝟙, ⊤ n⟩plus`：`i ↦ i+n`；`(+n)°` 是 `i ↦ i−n`，只在 `i ≥ n` 有像],
  [`≤` `<` `≥` `>`], [`A ⟶ A`], [序；`≥` `>` 是 prelude 给 `≤°` `<°` 的名字],
  [`ι`], [`N ⟶ N`], [新位置到旧位置的关系；结果的列是 `ι x`],
  [`S`], [`Schema`], [行的类型：带列名的列类型表；`S.obj` 是其积],
  [`a` `v`], [`col S "…"`], [一列：一个投影（`π₁` `π₂` 的复合）],
  [`k` `h`], [`col S "…"`], [key 列（一个投影，或若干投影的 pair）；`h` 是右侧 frame 的],
  [`c`], [`N ⟶ V`], [一个 frame 的一列 `x a`；编号的定义都只读一列],
  [`p`], [`C ⟶ C`], [谓词，写成 coreflexive],
  [`e`], [`C ⟶ V`], [一行之内的表达式],
  [`f`], [`[N] ⟶ D`], [聚合：读一组的位置数组（`Λ` 的升序）],
  [`⊤`], [`A ⟶ 1`], [到 prelude 的终对象 `1`（`obj 1`）的 `Tm.top`；目标是别的对象时是全关系],
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

- `Obj.prod` 没有字段名，列名是程序里的定义（`price ≜ π₁ π₂`）；frame 是位置的：形状相同、列名不同的两个 frame 类型相同，
  `select "price"` 与按名 join 无法检查。
- 设计（与 DataHaskell `TypedDataFrame '[Column "price" Double, …]` 相同的做法）：`Schema := List (String × Obj)`；`Schema.obj : Schema → Obj` 是一个定义，
  按 `.d` 的列顺序给出嵌套 `prod`。frame 的项以 schema 为下标，`Tm S.obj B`。
- 列名访问：`col S "price" : S.obj ⟶ T` 当且仅当 `("price", T) ∈ S`，在 elaboration 时判定，否则报错并指出缺的列名。
  `select` `exclude` `rename` `derive` `join` 是 `Schema` 上的函数，给出两个 `S.obj` 之间的项。
- 为什么不加 `Obj` 构造子：`Schema.obj` 让表示等式按定义成立，kernel、存储、`rep`、canonical、`lam_sound` 都看不到新东西；
  新构造子要给每个对 `Obj` 的 match 加分支。代价：字段类型相同、名字不同的两个 schema 有同一个 `Obj`，只有 schema 这一层区分它们。
- `.d` 就是 `Schema` 的落盘形式，同一个来源：`Table.write` 把列名按顺序写成 `.d`（文本列 `[C]`，与字典 `sym` 同一写法，
  文件 `.d.lo` `.d.hi` `.d.e`），`Table.readSchema` 读回 `Schema`（列名读 `.d`，每列的 `Obj` 读该列文件的头）；依赖数据的 schema 见 F1。

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
  [`Day`], [`date`（`i32`）], [1970-01-01 以来的天数],
  [`UTCTime`], [`datetime`（`i64`）], [1970-01-01 00:00:00 以来的纳秒，无时区],
  [list 列（`collect`）], [`Obj.arr T`], [],
  [`Maybe a`], [`A+1`], [见 1.3],
)

== null 的表示

例：一列 `[1, 2, null, 4]`，位置从 0 编号，null 在位置 2；表的第二列是这一列在各读法下的值。

#tbl(c-sem, (auto, auto, 1fr), ([读法], [例的值], [结论]),
  [q 的哨兵值], [`1 2 0N 4`：位置 2 存保留值 `0N`（i64 的最小值）], [带内表示；q 语义不在 Rel 中（`rel-architecture` §4.1）],
  [和类型 `v : C ⟶ V+1`], [`{(0,inl 1),(1,inl 2),(2,inr ∗),(3,inl 4)}`], [*采用*：每列都是全函数，`x ⟨a, v⟩` 不丢行],
  [部分列 `v inl°`], [`{(0,1),(1,2),(3,4)}`：位置 2 没有像], [派生的读法：表达式里与 null 比较的行被 `filterBy` 去掉，和 polars 一致],
)

- `inl°`、`inr°` 是 `prims` 的行；`[R, S] = inl° R ∪ inr° S`：按 tag 分情况，null 一支读 `S : 1 ⟶ B`。
- `tot(R)`（3.1）把部分的 `R : A ⟶ B` 变回全的 `A ⟶ B+1`：`R` 有值取值，否则 null。
- 存储：`V+1` 是 tag 列加各分支内的位置，每个分支的值各自成列（`rel-architecture` 第 0 节的 `sum`）。

// ───────────────────────────── 2
= 存储与顺序

一个实例：frame `[(A,1),(B,2),(A,1)]` 是 `a : N ⟶ K`、`b : N ⟶ V`，`m = 3`：`0 {a} A`，`0 {b} 1`，`2 {a} A`，`2 {b} 1`，`3` 没有像。
第 0 行与第 2 行是 `N` 的不同元素，所以是两行；`a° b` 只有 `A ↦ 1`、`B ↦ 2` 两对。

- *语义是集合。* 没有 bag，也没有 list 对象。frame 是一族从同一个 `N` 出发的部分 map，定义域都是 `(<m)`。以 `N` 为 key 它已经
  有序且无重复，不需要排序。`a° b : A ⟶ B`（排序并去重）只在运算的规格需要它时才形成：join、`distinct`、成员判断。
- *新 frame = 位置关系后接列。* 结果是新 frame 的运算给出 `ι : N ⟶ N`（新位置 ↦ 旧位置），结果是 `ι x`。
- *`(lo, hi)` 窗口在 frame 上，所有列共用。* 每个运算对所有列施加同一个 `ι : N ⟶ N`，所以窗口不属于某一列。
  key 仍是位置 `pos`，`m = hi − lo`；`take`、`drop` 只移动 `lo`、`hi`；其余的 `ι`（`sortBy`、`filterBy`、`groupBy`）
  得到 `lo = 0` 的新 frame。

#tbl(c-sem, (auto, 1fr), ([运算的类别], [ι : N ⟶ N]),
  [`x R`：`select` `derive` `apply` `impute` `over`], [`𝟙`],
  [`filterBy`、`distinct`、semi / anti join、`sample`], [`dom(x) asc(P)`，`P ⊑ dom(x)` 是保留的位置：按原位置顺序重新编号],
  [`sortBy`、`shuffle`], [`dom(x) iasc(x a)`：`dom(x)` 上的置换],
  [`take` `drop` `range`], [`(<n)`、`(+n)`、`(<b−a) (+a)`],
  [`<>`、`union`、`melt`], [第二个 frame 的位置经 `(dom(y) (+m₁))°`：`x ∪ ((dom(y) (+m₁))° y)`],
  [join], [`asc(ran(⟨𝟙, K⟩)) : N ⟶ N×N`，`K : N ⟶ N` 是匹配的位置对，按 `(i, j)` 的字典序；结果后接 `⟨π₁ x, π₂ y⟩`],
  [`groupBy`、`aggregate`、pivot], [`firstOcc(x k)`：每组一行，按 key 第一次出现的顺序；组是 `group(x k) : N ⟶ N`（3.1）],
)

- `asc(P) : N ⟶ B`（`prims` 的一行，`P : B ⟶ B`）：`j ↦ dom(P)` 中按 `Obj.lt` 第 `j` 小的元素，即 q 在集合上的 `asc`。
  每个新位置的编号都是一次 `asc`；定义见 3.1。
- *`N` 的元素是虚的。* frame 只有 `m`：位置不落盘。
- *落盘（q / kdb 的方式）。* 目录 = 表；文件 = 列，是一个 mmap 的 `foR` `Enc`，没有序列化（`CLAUDE.md` 的 Goal）；
  `.d` 文件 = `Schema` 的列顺序；整个数据库的 `sym` 列共用一个字典文件 `sym`（只追加：新串取下一个 id，旧 id 不变，数据列不重写），旁边是它的
  `sym.rank`。键为位置（存为 `.long` 的数对象，如 `N`）的输出写一张重编号的
  新表；其它键（任何 atom 的对象，如 `obj D : date`，或 schema）写成 key 表与 val 表，磁盘上 `key/`、`val/` 两个目录。
  CSV 是第二种格式：一个文件，key 列在前、val 列在后；列按对象的结构展开（`Expand.csvLeaves`）：schema 每个字段一列，
  积的每个因子各自展开、具名因子以其名为前缀（`Trade×(Quote+1)` 得 `Trade.sym` … `Quote.sym` …），`S+1` 是 `S` 的每列
  各一个可空列、全空即 `1`，部分为空的行读时报错并指出行与列；表头即这些列名。

// ───────────────────────────── 3
= 运算

== 辅助定义

左栏是库（与 prelude `Rel/Programs/Prelude.lean`）的定义，正文照抄库；`≜` 是库的定义，`:` 是 `prims` 的行。

```
// 编号
asc(P)            : N ⟶ B                        j ↦ dom(P) 第 j 小的元素；q：asc（集合上）
iasc(c)           ≜ asc(ran(⟨c,𝟙⟩))π₂            j ↦ c 第 j 小的值所在位置，相等按位置；q：iasc（稳定）
idesc(c)          ≜ r asc(ran(⟨c, r⟩)) π₂ r where r ≜ dom(c) ⟨⊤ count(c), succ⟩minus
                                                 r : i ↦ m−1−i，从 asc 的末端读；q：idesc（稳定）
firstOcc(c)       ≜ dom(c) asc(ran(agg(c°, head)))   组号 ↦ 该值第一次出现的位置；q：x?distinct x
group(c)          ≜ firstOcc(c) c c°             组号 ↦ 持有该值的各位置；q：group
lastOcc(c)        ≜ agg(group(c), last)          组号 ↦ 组内最后一个位置
J(a, b, x, y)     ≜ x a (y b)°                   key 相等的左右位置对
joinOn(K, x, y)   ≜ asc(ran(⟨𝟙, K⟩)) ⟨π₁ x, π₂ y⟩   K : N ⟶ N 的位置对按 (i, j) 字典序编号
// 聚合：f 读一组位置的升序数组
agg(R, f)         ≜ dom(R) Λ(R) f                R : A ⟶ N；Λ(R) 是 R 的像，位置升序
summarize(f, x)   ≜ agg((dom(x) ⊤)°, f)          1 ⟶ D：整个 frame 是一组
count(x)          ≜ summarize(length, x)         m : 1 ⟶ N；prim length
over(a, f, x)     ≜ ⟨x, x a agg((x a)°, f)⟩      每行带上它那一组的聚合，位置不变
win(w, x)         ≜ (dom(x) ⟨𝟙, ⊤ (dom(x) < w°)°⟩plus dom(x))°   对偏移 d < w 形成 i = j + d，所以建 (行数 × w) 个对
rolling(w, f, x)  ≜ agg(win(w, x), f)
// 行的窗口
take(n, x)        ≜ dom(< n°) x
drop(n, x)        ≜ (dom(x) dom(≥ n°) ⟨𝟙, ⊤ n⟩minus)° x
range(a, b, x)    ≜ take(⟨b, a⟩minus, drop(a, x))
dropLast(n, x)    ≜ take(⟨count(x), n⟩minus, x)  m − n < 0 时为空
takeLast(n, x)    ≜ dom(x) asc(dom(x) − dom(dropLast(n, x))) x
filterBy(p, x)    ≜ dom(x) asc(dom(x p)) x
// null（1.3）
tot(R)            ≜ R inl ∪ ((𝟙 − dom(R)) ⊤ inr)
filterJust(c, x)  ≜ filterBy(dom(c inl°), x)
filterNothing(c, x) ≜ filterBy(dom(c inr°), x)
shift(n, x)       ≜ dom(x) tot(⟨𝟙, ⊤ n⟩minus x)                行 i 读行 i−n；q：xprev
diff(n, x)        ≜ dom(x) tot(⟨x, ⟨𝟙, ⊤ n⟩minus x⟩minus)      x 是一列
next(n, x)        ≜ dom(x) tot(⟨𝟙, ⊤ n⟩plus x)                 行 i 读行 i+n；q：next
```

- `f` 的取法（`c = x v`）：`sum` 是 `F(c) sum`（prim `sum`，dfn `⦇[0, plus]⦈ʳ`），`count` 是 `length`，积是
  `F(c) ⦇[⊤ 1, times]⦈`，`reduce` 是 `F(c) ⦇[e, op]⦈`（`op` 是一个 `arith`）；`f64` 列的和也是 prim `sum`，按位置从左加（q 的顺序，`TestFrameTyped.sumFloatT`）。
  实数统计（q 的名字 `avg` `var` `svar` `dev` `sdev` `cov` `scov`，q 的 `cor` 写作 `corr`）与 `sum` 一样是数组上的关系
  `[γ] ⟶ φ`，接在 `F(c)` 之后：整列 `summarize(F(c) avg, c)`，每组 `aggregate(a, F(x c) avg, x)`，不另写每组的定义。
  结果在 float 对象变量 `φ` 中，由每个用处的期望类型确定（库不声明 float 对象），经 `$` 与真商 `%`，从不取整。
  数的运算不给操作数期望类型，故作操作数的统计写成 `avg 𝟙(φ)`。值在 `avg` 与 `cov` 的入口先经 `$ φ` 一次转到 `φ`，
  和、积都在 `φ` 中，不在列自己的对象 γ 中：在 `obj N = 0…40` 上 `7·7 = 49` 不是元素，在 γ 中相乘会让 `var` 无像；
  整数列与 `f64` 列都可用（`TestFrameStat.frameStatFloatT`）。
  `min` `max` 只选不造：`F(c) Λ(∋) head`、`last`（`Λ(∋)` 是数组的值的升序集合）。每组第一个、最后一个值：
  `F(c) head`、`last`。`F` 是 prim：数组逐元素后接 `c`。
- 一个实例：`c = x a = B A B`：`agg(c°, head)` 是 `A ↦ 1`、`B ↦ 0`，`asc` 把 `{0, 1}` 编号，`firstOcc = 0 1`；
  `group(c)` 是 `0 ↦ {0, 2}`、`1 ↦ {1}`；`iasc(c)`：`⟨c, 𝟙⟩` 的像 `(A,1) (B,0) (B,2)` 升序，`π₂` 得 `1 0 2`。
  规则：每个编号都是一次 `asc`：先形成要编号的集合（位置、`(值, 位置)` 对、位置对），`asc` 按 `Obj.lt` 编号。
- 一个实例：`take(3, x)` 在 `m = 4` 的 `x` 上：`2 {(<3)} 2 {x} (A,1)`；`3` 被 `(<3)` 挡住，没有像。
  规则：结果是 `ι x`；`(<n)` 收 `hi`，`(+n)` 移 `lo`，其余的 `ι` 得到 `lo = 0` 的新 frame（第 2 节）。

#let dh = (
  ([`select` `exclude` `selectBy`], [`x ⟨col S "a", col S "b"⟩`], [列名在 elaboration 时检查], "full"),
  ([`rename` `renameMany`], [只改 `Schema`，frame 不变], [列名只在 schema 里，frame 是位置的（1.2）], "full"),
  ([`derive` `deriveMany` `deriveWithExpr` `insert*` `cloneColumn`], [`x ⟨𝟙, e⟩`], [], "full"),
  ([`apply` `applyMany` `applyInt` `applyDouble` `safeApply` `applyAtIndex`], [`apply(f, a, b, x) ≜ x ⟨lift(f, a), b⟩`，即 `x ⟨a f, b⟩`],
    [`f` 是程序里的 Rel 定义（构造子、`Op` 行与关系的复合），作关系参数传入；任意 Haskell 函数不进入程序：F7], "full"),
  ([`applyWhere`], [`applyWhere(p, e) ≜ (p e) ∪ (𝟙 − p)`，后接于 `x`], [], "full"),
  ([`filter` `filterWhere` `filterBy`], [`filterBy(p, x)`，如 `p = dom(a < ∩ b)`], [], "full"),
  ([`filterJust` `filterAllJust`], [`filterJust(c, x)`], [], "full"),
  ([`filterNothing` `filterAllNothing`], [`filterNothing(c, x)`], [], "full"),
  ([`take` `drop` `takeLast` `dropLast` `range` `byIndexRange` `cube`],
    [`take(n, x)` `drop(n, x)` `takeLast(n, x)` `dropLast(n, x)` `range(a, b, x)`], [], "full"),
  ([`selectRows`], [`ix x`，`ix : N ⟶ N` 是输入的下标 frame], [], "full"),
  ([`sortBy`], [`sortBy(a, x) ≜ dom(x) iasc(x a) x`；`sortByDesc(a, x) ≜ dom(x) idesc(x a) x`],
    [`iasc` `idesc` 稳定：稳定排序就是规格，是相等而不是 refinement], "full"),
  ([`topBy`], [`topBy(n, a, x) ≜ take(n, sortBy(a, x))`], [], "full"),
  ([`distinct`], [`distinct(x) ≜ firstOcc(x) x`], [按第一次出现的顺序：`B A B` → `B A`], "full"),
  ([`groupBy`], [组 `group(x k)`；组的 key `firstOcc(x k) x k`], [], "full"),
  ([`aggregate`], [`aggregate(a, f, x) ≜ ⟨firstOcc(x a) x a, agg(group(x a), f)⟩`], [], "full"),
  ([`sum` `mean` `count` `countAll` `minimum` `maximum` `reduce`], [`summarize(f, x)`，`f` 见 3.1；`count(x)`；
    `mean` 是 `summarize(F(c) avg, c)`，`avg : [γ] ⟶ φ ≜ F(𝟙 $ φ) ⟨sum, length $ φ⟩%`],
    [`minimum` `maximum` 在 `f64`、`date` 列上按值的序；prim `sum` 在 `i64` `f64` 上，从左加；`avg` 在整数列与 `f64` 列上，和在 `φ` 中], "full"),
  ([`variance` `stddev` `skewness` `correlation` `zScore`],
    [`cov : [γ×γ] ⟶ φ ≜ F(⟨π₁ $ φ, π₂ $ φ⟩) ⟨F(times 𝟙(φ)) avg 𝟙(φ), ⟨F(π₁) avg 𝟙(φ), F(π₂) avg 𝟙(φ)⟩times⟩minus`；
    `scov : [γ×γ] ⟶ φ ≜ ⟨cov 𝟙(φ), ⟨length $ φ, tail length $ φ⟩%⟩times`；
    `var : [γ] ⟶ φ ≜ F(⟨𝟙, 𝟙⟩) cov`；`svar : [γ] ⟶ φ ≜ F(⟨𝟙, 𝟙⟩) scov`；`dev : [γ] ⟶ φ ≜ var 𝟙(φ) sqrt`；`sdev : [γ] ⟶ φ ≜ svar 𝟙(φ) sqrt`；
    `corr : [γ×γ] ⟶ φ ≜ ⟨cov 𝟙(φ), ⟨F(π₁) dev 𝟙(φ), F(π₂) dev 𝟙(φ)⟩times⟩%`；
    `skewness : [γ] ⟶ φ ≜ ⟨⟨F(𝟙 $ φ ⟨⟨𝟙, 𝟙⟩times, 𝟙⟩times 𝟙(φ)) avg 𝟙(φ), ⟨avg 𝟙(φ), ⟨⟨var 𝟙(φ), ⟨var 𝟙(φ), var 𝟙(φ)⟩plus⟩plus, ⟨avg 𝟙(φ), avg 𝟙(φ)⟩times⟩plus⟩times⟩minus, ⟨var 𝟙(φ), dev 𝟙(φ)⟩times⟩%`；
    `zScore(c) ≜ ⟨⟨c $ φ, ⊤ m⟩minus, ⊤ s⟩% where m ≜ summarize(F(c) avg 𝟙(φ), c), s ≜ summarize(F(c) sdev 𝟙(φ), c)`],
    [q 的 `var` `svar` `dev` `sdev` `cov` `scov` `cor`（prelude 的 `cor` 是 coreflexive，故名 `corr`）；`scov` 乘 n/(n−1)，一行时 `0·∞` 为 NaN，无像；
    `skewness` 是总体的 g1 = m3/m2^1.5（DataHaskell 的 `skewness'`），m3 = E[x³] − 3μσ² − μ³，每个值先 `$ φ` 再立方，
    可接在 `aggregate` 里每组用；`zScore` 每行 (x − 均值)/样本标准差（DataHaskell 的 `variance'` 是 n − 1），一行时无像；
    整数列与 `f64` 列上都可用], "full"),
  ([`median` `percentile` `genericPercentile` `interQuartileRange`],
    [`quantilePos(p, c) ≜ dom(⟨lo, p⟩ cor(≤)) dom(⟨p, hi⟩ cor(≤)) ⟨p, ⟨count(c) $ φ, hi⟩minus⟩times where hi ≜ {(∗,1.0)}, lo ≜ {(∗,0.0)}`；
    `quantile(p, c) ≜ summarize(F(q) sum, q) where hi ≜ {(∗,1.0)}, lo ≜ {(∗,0.0)}, d ≜ ⟨dom(c) $ φ, ⊤ quantilePos(p, c)⟩minus, w ≜ ⟨⊤ hi, ⟨d, ⟨⊤ lo, d⟩minus⟩max⟩minus, q ≜ dom(⟨⊤ lo, w⟩ cor(<)) ⟨w, sortBy(𝟙, c) $ φ⟩times`；
    `genericPercentile(p, c) ≜ quantilePos(p, c) floor 𝟙(Z) (dom(c) $ Z)° sortBy(𝟙, c)`；
    `median` 是 `quantile({(∗,0.5)}, c)`，`percentile` 是 `quantile` 在 k/100，`interQuartileRange` 是 `⟨quantile({(∗,0.75)}, c), quantile({(∗,0.25)}, c)⟩minus`],
    [`quantilePos` 是排序后的位置 h = p·(n−1)，p 不在 [0, 1] 时无像。`quantile` 线性插值（DataHaskell 的 `quantiles'`、polars 的 `linear`）：
    值 = lower + frac·(upper − lower)，即 |i − h| < 1 的行以权 1 − |i − h| 求和；q 的 `med` 是 p = 0.5，不另写；整数列与 `f64` 列上都可用。
    `genericPercentile` 不插值（DataHaskell 的 `quantilesOrd'`）：排序后位置 ⌊h⌋ 的值本身，`floor` 把 h 变为 `i64` 的 `Z`，
    故任何有序的列都可用（整数、`f64`、`date`、枚举对象，`TestFrameStat`）；DataHaskell 的参数是整数 k、p = k/100。
    都是 `c` 上的关系，不是数组上的，故不接在 `aggregate` 里], "full"),
  ([`countDistinct` `mode`], [`countDistinct(x) ≜ count(distinct(x))`；`mode(a, x) ≜ summarize(head, s) s where s ≜ idesc(valueCounts(a, x) π₂) valueCounts(a, x) π₁`],
    [`mode` 在并列中取先出现的（`idesc` 稳定）], "full"),
  ([`collect`], [`collect(a, c, x) ≜ aggregate(a, F(x c), x)`], [结果列的类型是 `Obj.arr V`], "full"),
  ([`firstOrNothing` `lastOrNothing`], [`firstOrNothing(x) ≜ tot(summarize(head, x) x)`；`lastOrNothing(x) ≜ tot(summarize(last, x) x)`],
    [空 frame 得 null；每组一行：`firstOcc(x k) x`、`lastOcc(x k) x`], "full"),
  ([`topK` `bottomK` `kExtremes`], [`topK(n, a, x) ≜ take(n, sortByDesc(a, x))`；`bottomK` 是 `topBy`], [并列按位置顺序], "full"),
  ([`valueCounts` `valueProportions` `frequencies`], [`valueCounts(a, x) ≜ aggregate(a, length, x)`；
    `valueProportions(a, x) ≜ valueCounts(a, x) ⟨π₁, ⟨π₂ $ φ, ⊤ count(x) $ φ⟩%⟩`], [比例是计数经 `$ φ` 后的真商 `%`], "full"),
  ([`summarize` `describeColumns`],
    [`describe(c) ≜ ⟨count(c), ⟨summarize(F(c) avg, c), ⟨tot(summarize(F(c) sdev, c)), ⟨summarize(F(c) Λ(∋) head, c), summarize(F(c) Λ(∋) last, c)⟩⟩⟩⟩`],
    [count、mean、std（样本的，一行时为 null）、min、max；读 `avg`，整数列与 `f64` 列上都可用；四分位数是 `quantile` 在 0.25、0.75，不在 `describe` 的结果中], "full"),
  ([`nulls`], [`nulls(c, x) ≜ count(filterNothing(c, x))`], [], "full"),
  ([`innerJoin` `join` `joinOn`], [`innerJoin(a, b, x, y) ≜ joinOn(J(a, b, x, y), x, y)`], [], "full"),
  ([`leftJoin`], [`leftJoin(a, b, x, y) ≜ asc(ran(⟨𝟙, dom(x) tot(J(a, b, x, y))⟩)) ⟨π₁ x, π₂ (y ⊕ 𝟙)⟩`],
    [`y ⊕ 𝟙 = [y inl, 𝟙 inr]`（prelude 的 `⊕`）：没有匹配的行右侧为 null（`E+1`）], "full"),
  ([`rightJoin`], [`rightJoin(a, b, x, y) ≜ leftJoin(b, a, y, x) ⟨π₂, π₁⟩`], [], "full"),
  ([`fullOuterJoin`], [`fullOuterJoin(a, b, x, y) ≜ append(leftJoin(a, b, x, y) ⟨π₁ inl, π₂⟩, antiJoin(b, a, y, x) ⟨⊤ inr, inl⟩)`],
    [left join 之后接 `y` 中无匹配的行，左侧为 null；两侧都是和类型], "full"),
  ([`union`], [`union(x, y) ≜ distinct(append(x, y))`], [], "full"),
  ([`intersect`], [`intersect(x, y) ≜ distinct(semiJoin(𝟙, 𝟙, x, y))`], [], "full"),
  ([`difference` `symmetricDifference`], [`difference(x, y) ≜ distinct(antiJoin(𝟙, 𝟙, x, y))`；`symmetricDifference(x, y) ≜ append(difference(x, y), difference(y, x))`], [], "full"),
  ([`<>`（行拼接）], [`append(x, y) ≜ x ∪ ((dom(y) ⟨𝟙, ⊤ count(x)⟩plus)° y)`], [`sym` 列同一个数据库字典，id 原样拼接（`rel-architecture` §4.3）], "full"),
  ([`|||`（列拼接）], [`hstack(x, y) ≜ dom(⟨x, y⟩ ⊤ count(x) count(y)°) ⟨x, y⟩`], [两个 frame 行数不同时结果是 `𝟘`：F9], "full"),
  ([`impute` `imputeWith` `fromMaybe` `castWithDefault`], [`x v [𝟙, c]`；`imputeWith` 是 `x v [𝟙, summarize(f, x)]`], [`c : 1 ⟶ V`], "full"),
  ([`toMaybe` `isJust` `isNothing` `isNull` `fromJust` `whenPresent`], [`inl`、`dom(inl°)`、`dom(inr°)`、`dom(inr°)`、`inl°`、`e ⊕ 𝟙`], [复合，库中没有定义], "full"),
  ([`recode` `recodeWithDefault`], [`x v T`；带缺省 `x v tot(T) [𝟙, c]`], [`T` 是 `Tm.val` 的字面量表], "full"),
  ([`lift` `lift2` `nullLift` `nullLift2` `bind`],
    [`lift(f, c) ≜ c f`；`lift2(f, a, b) ≜ ⟨a, b⟩ f`；`bind(f, c) ≜ c [f, inr]`；`nullLift(f, c) ≜ bind(f inl, c)`；
    `nullLift2(f, a, b)`：两列都有值时 `⟨a inl°, b inl°⟩ f inl`，否则 null],
    [`f` 是 Rel 定义，作关系参数（`TestFrameLift`）；部分的 `f` 在无像的行上没有结果，不变成 null：F7], "full"),
  ([`cast` `toDouble` `div` `mod` `pow` `fround` `relu` `eq` `lt` `and` `or` `not` …],
    [`pow x i` 是 `⟨x $ F, i $ F⟩xexp`（`i` 是字面量或列）；`div` `mod` 是 `arith`；`eq` 是 `𝟙`，`lt` 是 `<`；`and` `or` `not` 是 coreflexive 的 `∩` `∪` `−`；`relu = ⟨𝟙, ⊤ 0⟩max`；`toDouble` 是 `x v $ F`（`obj F : f64`）；`fround` 是 row `x v round`],
    [`$` 只保值（整数 → 浮点、窄 → 宽）；`arith` 与 `<` 在 `f64` `f32` 上（`TestFloatArith`），`div` 是取整的商，`%` 是真商；浮点 → 整数是 `floor`（`f32` `f64` 到 `i64`，NaN 与越界无像，`TestFloatArith.unaryT`）；
    `xexp` 是 libm `pow`，负底数的整数次幂有值（`TestFrameCols.framePow`）；`round` 半数取偶（`f32` `f64` 到 `i64`，NaN 与越界无像，`TestFrameCols.frameRound`）], "full"),
  ([`over`], [`over(a, f, x)`], [], "full"),
  ([`contains` `length` `splitOn` `match` `matchAll`],
    [`contains(s) ≜ dom(suffix prefix s)`；`length` 是 prim；`splitOn(s) ≜ ⦇[nil τ, a (e ∪ ((𝟙 − dom(e)) snoc))]⦈`，
    `a ≜ ⟨π₁ init, ⟨π₁ last, π₂⟩snoc⟩`，`e ≜ (𝟙 × (cat° (𝟙 × s))) ⟨⟨π₁, π₂ π₁⟩snoc, nil⟩snoc`；`match(T, q, A) ≜ dom(⦇[q, T]⦈ A)`],
    [`splitOn` 是 q 的 `vs`：左 fold 把每个元素接到最后一段，该段以 `s` 结尾时切开；多字符分隔符同一条定义，取最左、
    不重叠的匹配（`"ababa"` 按 `"aba"` 切成 `"" "ba"`），这只有从左到右的扫描能选，所以不是匹配位置的 `where`。
    `match` 的 `T : σ×α ⟶ σ` 是转移关系（关系，所以也可以是 NFA），`q` 起始态，`A` 接受态的 coreflexive；把正则编成 `T`
    在语言之外（`TestFrameText`，`[0-9]+` 的手写表）。`matchAll`：未做], "part"),
  ([`parseDate` `daysBetween`], [`daysBetween(a, b) ≜ ⟨a $ Z, b $ Z⟩minus`],
    [日期读作其天数（`a`、`b` 在任一 `date` 对象上，`Z : i64` 是库声明的对象）；`date` 上的 `minus` 仍被拒：差不是日期；`parseDate`：F3，停在「日数」一步], "part"),
  ([`sample` `shuffle` `randomSplit` `kFolds` `stratifiedSample` `mkRandom`], [无], [F8], "no"),
  ([`fromList` `fromRows` `fromColumns` `fromUnboxedVector` `empty`], [字面量 `Tm.val`，或 `⟨x, y⟩`], [], "full"),
  ([`columnAsVector` `columnAsList` `toList` `toRowList` `to*Matrix`], [`summarize(F(x c), x)`], [位置顺序的数组], "full"),
  ([`dimensions` `nRows` `nColumns` `columnNames`], [`count(x)`；`nColumns` `columnNames` 读 `Schema`], [列名只在 schema 里，frame 是位置的], "full"),
  ([`readTsv` `readParquet` `readJSON` `writeParquet`], [无], [F6], "no"),
  ([`readCsv` `writeCsv` `scanCsv`], [`input x : N ⟶ S from csv "f"` / `output x to csv "f"`],
    [schema 在语句里声明，或 `schema S from "dir"` 在 elaboration 时读表目录的 `.d`（F1）；CSV 文件没有 `.d`，要声明；CSV 解析是 crate 的 IO 导出（F6）], "full"),
  ([`scanParquet` `fromDataFrame` `run`（Lazy）], [`rel_program` 中的定义],
    [`rel_program` 本身就是 plan：`rel-architecture` §1], "full"),
  ([`fold`、`display`、Plot、`DecisionTree`、`KMeans` 等], [不在本设计范围], [宿主层的工具与模型库], "out"),
)

#let pl = (
  ([semi / anti join], [`semiJoin(a, b, x, y) ≜ dom(x) asc(dom(J(a, b, x, y))) x`；`antiJoin(a, b, x, y) ≜ dom(x) asc(dom(x) − dom(J(a, b, x, y))) x`], [], "full"),
  ([cross join], [`crossJoin(x, y) ≜ innerJoin(⊤ 𝟙(1), ⊤ 𝟙(1), x, y)`], [], "full"),
  ([asof join], [`aj(k, t, h, u, x, y) ≜ ⟨x, dom(x) tot(agg(m, last) y)⟩ where r ≜ ⟨π₁, sums(counts(ran(x ⟨k, t⟩), (y ⟨h, u⟩)°))⟩, m ≜ x ⟨k, t⟩ r (y ⟨h, u⟩ r)°`；
    `counts(D, R) ≜ agg(R, length) ∪ ((D − dom(R)) ⊤ {(∗,0)})`],
    [`counts(D, R)` 在 `D` 的每个点上给 `R` 的像的长度，没有像的点为 0；q 的 `aj`：`r` 数同 key 的 `y` 行中时间不晚于该时间的个数，`m` 接上最新的 `u ≤ t`；`agg(m, last)` 是并列时取最后一行；
    计数在 `y` 的位置对象 `μ` 里；`ι = 𝟙`；`sums` 沿时间扫描，`date` `datetime` 的时间列照常运行（`TestFrameTyped.ajDateT`）；`f64` 的时间列被拒：F4], "full"),
  ([`cum_sum` 等], [`cumAgg(f, x) ≜ agg(dom(x) ≥ dom(x), f)`；`cumSum(c) ≜ sumsBy(dom(c) ⊤ 𝟙(1), c)`；
    `sumsBy(g, c) ≜ ⟨g, 𝟙⟩ sums(⟨g, 𝟙⟩° c)`],
    [行 `i` 聚合 `j ≤ i` 的行；q：`sums`（`f` 为 `sum`）。`cumSum` 是 `cumAgg(F(c) sum, c)`，一组；`sumsBy` 是每组内的 `cum_sum().over(g)`；
    `f64` 列上每行一次 IEEE 加法，沿位置从左到右（`TestFrameStat`）；`f32` 列先 `$` 到 `f64`], "full"),
  ([`shift(k)`], [`shift(k, x)`；`shift(−k)` 是 `next(k, x)`], [前（`next`：后）`k` 个位置是 null], "full"),
  ([`diff`], [`diff(1, c)`], [`c(i) − c(i−1)`，第 0 行 null], "full"),
  ([`rolling(w)`], [`rolling(w, f, x)`], [], "full"),
  ([`forward_fill`], [`fills(c) ≜ (p ∪ (dom(c) − dom(p))) c where r ≜ cumSum(counts(dom(c), dom(c inl°))), p ≜ r (dom(c inl°) r)°`],
    [q 的 `fills`：`r(i)` 数不晚于 `i` 的有值行，`p` 把 `i` 送到计数相同的有值行，即不晚于 `i` 的最后一个；计数为 0 时没有，null 保留],
    "full"),
  ([`melt` / `unpivot`], [`pivotLong(i, s, a, t, b, x) ≜ append(x ⟨i, ⟨⊤ s, a⟩⟩, x ⟨i, ⟨⊤ t, b⟩⟩)`；`melt(s, a, t, b, x) ≜ pivotLong(𝟙, s, a, t, b, x) π₂`],
    [每行对每个值列一次，得 `(id, 列名, 值)`；各列要同类型], "full"),
  ([pivot（long）], [`aggregate(⟨k, q⟩, f, x)`], [long 形式就是 key 为 `K×P` 的 frame], "full"),
  ([pivot（wide）], [`pivotOn(k, ⟨v ∈ V ↦ pivotCol(k, q, v, f, x)⟩, x)`；`pivotOn(k, w, x) ≜ firstOcc(x k) x k ⟨𝟙, w⟩`，
    `pivotCol(k, q, s, f, x) ≜ ran(x k) tot(⟨𝟙, ⊤ s⟩ agg((x ⟨k, q⟩)°, f))`],
    [有限对象 `V` 的每个元素一列，没有的为 null；`V` 是声明的 `obj S = {…}`，或 `obj V from "dir" c` 读磁盘上列的不同值（F1）], "full"),
  ([`get_dummies`], [`⟨v ∈ V ↦ dummy(c, v, x)⟩ : P ⟶ D`，`schema D = {c ∈ V : 1+1}`；`dummy(c, s, x) ≜ dom(x) tot(x c s°)`],
    [每个元素 `v` 一列 `c_v`，`inl` 当行的 `c` 是 `v`（`c s° s` 即余自反 `c ≫ (= s)`），否则 `inr`（F1）], "full"),
)

== DataHaskell `dataframe` 的导出函数

函数表取自 `DataFrame.hs` 的导出与 `DataFrame.Operations.*`、`DataFrame.Functions`（github.com/DataHaskell/dataframe，`main`）。
状态：全 = 一个库定义或复合给出它；部分 = 只写出一部分，见说明栏；无 = 写不出，见说明栏的 finding；范围外 = 不在本设计范围。
`≜` 的行是库的定义，正文照抄库。计数：#tally(dh)。

#apitbl(c-syn, ([Haskell 函数], [Rel 复合], [说明 / finding], [状态]), dh)

== polars 多出来的运算

计数：#tally(pl)。

#apitbl(c-sem, ([polars], [Rel 复合], [说明 / finding], [状态]), pl)

// ───────────────────────────── 4
= Findings

写不出来、或只能别扭地写出来的运算。

- *F1 依赖数据的 schema：在 elaboration 时读数据定下。* wide pivot、`get_dummies`、读文件时推断 schema：结果的 `Obj`
  要读了值才知道，而 `Tm A B` 在 elaboration 时固定 `B`。做法：依赖数据的对象在 elaboration 时读数据的 `.d` 定下，
  `B` 仍是固定的；数据变了，程序要重新 elaborate（`rel_program` 重新编译），旧的 elaboration 不会察觉。
  - 读文件（已做）：`schema S from "dir"` 在 elaboration 时读 `dir` 的 `.d`（`Embed.diskOf` → `Table.readSchema`），
    得到与 `schema S = {…}` 相同的 `ObjDef.schema`，没有第二种 schema 类型。磁盘只记 atom，不记程序的对象名，所以每列
    在它的 atom 的无界对象上，以 atom 命名（`qty : i32` 即 `obj i32 : i32`），语句替程序声明它；程序已把这个名字声明成
    别的对象时报错。`sym` 列被拒（没有 `sym` 的字面量对象）。测试 `Rel/Lang/TestSchemaDisk.lean`。
  - wide pivot、`get_dummies`（已做）：例 `get_dummies(c)`，磁盘上 `c` 的不同值是 `3` `7` `9`，结果 schema 是
    `{c_3 : 1+1, c_7 : 1+1, c_9 : 1+1}`，列名来自数据的值。两样机制，都在 elaboration 时，没有新的 `Tm` 构造子：
    (a) `obj V from "dir" c` 读列 `c` 的不同值（升序，`asc distinct`），元素保持存储的值（`ObjDef.coded`：元素 `w` 的
    code 是磁盘上的值本身，不是 `0…n−1`；`ObjInfo.codes` 是两种声明共用的 code 表）；
    (b) 在有限对象上生成积：`⟨v ∈ V ↦ e⟩` 把 `e` 在每个元素 `w` 处（`v` 换成字面量 `{(∗,w)} : 1 ⟶ V`）的项左嵌套成对，
    与 `Schema.obj` 同形；`schema D = {c ∈ V : A}` 每个元素一列 `c_w : A`。`V` 可以是任何有限对象（声明的 `{…}`、
    范围、磁盘的）。`dummy`、`pivotCol` 是逐元素的库定义，积在使用处由 (b) 生成。测试 `Rel/Lang/TestPivotDisk.lean`。
  - 未做：对象变量上的生成（库定义 `getDummies(c, x)` 本身对 `V` 泛型）要求定义在每个使用处展开，现在定义只 elaborate
    一次、对象变量是刚性的；`obj V from` 只读 `i64` 列（`sym` 列要 `sym` 的字面量对象）；导入的有限对象不能生成。
- *F3 字符串别扭。* 字符串是 `arr char`，单元格里的值，不是 frame（F9）；`contains` 的规格要形成全部子串。
  `splitOn`、`match` 是库定义（上表），无新行、无新 kernel；正则是「步骤为转移表」的 fold，把正则编译成表在语言之外。
  仍缺：(1) `parseDate`：数字是 `$` 与 `minus` 的算术、`⦇[0, ⟨π₁ ×10, π₂⟩plus]⦈`，但 `(2024, 1, 15) ↦ 19737` 这条规则只在
  Lean 的 `Db.Csv.daysFrom`（CSV 读法与日期字面量共用），没有行；在 Rel 里写一遍 Hinnant 公式是同一知识的第二份，
  所以待定：加行 `ymd : [C] ⟶ D`（含义 `Db.Csv.ymd`，非 kernel），或写一份公式并由测试钉住；
  (2) 字面量里只有一个字符的 `"0"` 在 `Q×C` 上读作文本 `[C]`，不读作 `char`（`TestFrameText` 用码 48…57 写数字）。
- *F4 atom 覆盖。* 列可以在声明的 atom 对象上（`obj F : f64`、`obj D : date`）：只比较、排序、匹配值的运算
  （`sortBy` `topK` `distinct` `aggregate` 的组与 `min` `max`、join）照常运行（`TestFrameTyped`）。`arith` 与 `<` `≤`
  在 `f64` `f32` 上（`TestFloatArith`）；prim `sum` 在 `i64` `f64` 上，按位置从左加（`TestFrameTyped.sumFloatT`）。
  真商 `%` 与 `sqrt` 给出 `avg` `var` `cov` `corr` `quantile` `skewness` `zScore` `valueProportions` 与 `describe` 的
  均值、标准差；值先 `$ φ`，和在 `φ` 中，所以整数列与 `f64` 列都可用（`TestFrameStat.frameStatFloatT`）。仍缺：
  (1) `sums` 在 `i64` `f64` 上，`cumSum` `sumsBy` 在 `f64` 列上运行（`TestFrameStat`），`f32` 列被拒、先 `$` 到 `f64`；
  (2) 已解决（请求 10/11）：统计对结果的 float 对象 `φ` 泛型，由用处的期望类型确定（`TestGenericNum.avgGT`），库不再声明
  `F`；数的运算（`sqrt` `times` …）不把结果对象连到操作数，作操作数的统计写 `𝟙(φ)`。`f32` 的结果被 prim `sum` 拒
  （`TestFrameStat.frameStatF32T`）；泛型定义中的数字字面量在每处使用的对象上构造（请求 12、13），故 `quantile` 直接写 `0.0`、`1.0`；(3) 浮点 → 整数是一元的 `floor`（`f32` `f64` 到 `i64`），`genericPercentile` 用它取 ⌊h⌋；`pow x i` 是 prim `xexp` 的
  `⟨x $ F, i $ F⟩xexp`（`TestFrameCols.framePow`）；`fround` 是一元的 `round`，半数取偶（`TestFrameCols.frameRound`）；
  (4) `aj` 的时间沿 `sums` 扫描：`date` `datetime` 的时间列运行（`TestFrameTyped.ajDateT` `sumsTimeT`），`f64` 的
  时间列被拒，`f64` 的 canon 序在 S5 之前是位的序（`TestFrameTyped.sumsFloatPosT`）。
- *F5 时间类型。* `date`、`datetime` 是整数 code，没有时区。日历运算（取月份、截断到月）是整数算术加上与日历表的 join。
- *F6 IO 在代数之外。* 程序读的 frame 是 `input` 语句声明的名字，路径与格式写在语句里；CSV 的解析是 crate 的 IO 导出，不是列上的关系。
- *F7 宿主函数。* 覆盖的：`lift`、`lift2`、`apply`、`bind`、`nullLift`、`nullLift2` 是 `frame` 的库定义，元素函数
  `f` 是程序里的 Rel 定义（构造子、`Op` 行与关系的复合，可带参数，如 `atLeast(m) ≜ ⟨𝟙, ⊤ m⟩max`），作为关系参数
  传入，与 `applyWhere(p, e)` 同一机制；如 `x lift(dbl, π₂)`、`dbl ≜ ⟨𝟙, 𝟙⟩plus`，在 `v = 5 3 …` 上得 `10 6 …`
  （`TestFrameLift`）。不覆盖的：任意 Haskell（或 Lean）函数。它在程序里是一个不透明的 kernel，违反「只有原语是
  kernel」，没有 Rel 的律可用于它，也不能在编码列上计算；polars 表达式（不含 `map_elements`）是同样的限制。
- *F8 抽样。* `sample(n)` 是有多个像的关系（任意 n 行），实现选其中一个，是规格的 refinement，不是相等。
- *F9 位置模型之外的两处。* 单元格里的 list（`Obj.arr`：字符串、`collect` 的结果）是一个值，`N` 只给 frame 的行编号。
  `⟨x, y⟩` 的定义域是 `dom(x) ∩ dom(y)`，长度不等时取较短的；`hstack` 另加行数相等的检查，不等长时是 `𝟘`。
