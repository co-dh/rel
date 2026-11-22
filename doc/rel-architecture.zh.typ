#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// palette: one colour per layer, reused in diagrams, tables and headings
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let c-rs  = rgb("#b5541c")   // Rust
#let ink   = rgb("#222831")

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

#import "tbl.typ": tbl, soft
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
  | sum  (a b : Obj)                    -- 和：tag 列 + 各分支位置；atom+1 是一列，null 在带内（§4 foR）
  | one                                 -- 终对象 1（决定 M）：只有一个值，不存任何列；`obj 1 = {∗}` 这类单元素对象都是它

Obj.El : Obj → Type                     -- 解码：atom ↦ 原子的 Lean 类型，prod ↦ ×，arr ↦ List，sum ↦ ⊕，one ↦ Unit

structure Known (A B : Obj) where
  dom : Option (Σ n, Vals A n)          -- 已知的定义域 K
  ran : Option (Σ n, Vals B n)          -- 已知的值域 L
  pairs : Option (Tab A B) := none      -- 上下文要与结果求交的表 P：结果只需在 P 的对上正确

inductive Rel (A B : Obj)
  | tab  (t : Except String (Tab A B))            -- 两列等长数组；error = 失败及其消息（原 CRel 的 ok = false），一路到 check、print
  | lazy (f : Known A B → Rel A B)                -- 边界够了返回 tab，不够返回 lazy 等更多边界
  | bits (g w o x ra y rc)                        -- （草稿，待审）g·w 位的 u1 位矩阵 o，行值 x[ra[a]]、列值 y[rc[c]]；读成行即 Tab.ofBits

compile η t : {r : Rel A B // rep r = ⟦t⟧ρ}       -- 方案 A：规格在类型里
```

#grid(columns: (1fr, 1fr), gutter: 8pt,
  card(c-run, [为什么是 `lazy`])[`succ`、`arith`、`leq`、`⊤` 是无限关系，只能在边界已知后求值；
    它们和有限表一样是 `Rel` 的值，不是编译器的特例。复合时自动传播：`tab ≫ lazy` 把左表的值域作为 `dom` 交给右边。],
  card(c-run, [闭项只算一次（草稿，待审）])[闭项的值不随上下文变：由下面的 `rep (f ⟨K, L⟩) = K ≫ R ≫ L`，取空边界得 `rep (f {}) = R`。
    所以一个不需要边界的闭项（有限：旧记号 `Tm.dem = false`）在共享常量处求值一次，存成 `tab`（`GenK.memo`）；
    需要边界的闭项（`𝟙`、`≤`、`⊤` 等无限关系）仍是 `lazy`，在每个上下文里按边界求值。否则一个闭的 `lazy` 值在 `fold` 的每一轮重算。
    开项（读变量的部分）不共享，但每次绑定只算一次：定义的实参与 `where` 项经 `call`/`arg` 绑定，体读多少次都不重算。],
  card(c-run, [需要几侧边界])[`succ`（函数）：`dom` 已知即返回 `tab`。`leq`：`Λ(leq)(3) = {3,4,…}` 无限，
    `dom` 与 `ran` 都已知才返回 `tab (K ≫ leq ≫ L)`。`⊤`：`K × L`。],
  card(c-run, [对的需求 `pairs`])[`T ∩ R`、`T − R` 把 `T` 自己作为 `pairs` 交给 `R`：`rep (f ⟨K, L, P⟩) ∩ P = (K ≫ R ≫ L) ∩ P`。
    `≤ <`（经 `°` 得 `≥ >`，经 `∪` 往下传）用它：只在 `P` 的 n 对上逐对比较再选行，不做 `K × L` 的 cross。
    `𝟙`、`succ`、`arith`、`π₁ π₂`、`Λ` 是函数或 coreflexive，结果行数已是 `|K|`，不看 `pairs`；`⊤` 可以用（`P` 切到 `V`），尚未用。
    没有表可求交的比较（`P ≤ P`）仍做 cross，超过 `crossMax` 对时 `Vals.cross` 返回 error 而不是 abort。],
)

- 删除的类型：`CRel`（`ok` 并入 `tab` 的 `Option`）、`Fn`、`Dem`（定义域就是 `Known.dom`）、`Den`（直接写 `Core.Rel`）。
- `Obj` 是可检查的数据，编译器按它分派（`Vals A n` 几列、哪个宽度的 kernel）；Lean 的 `Type` 不能模式匹配，所以程序用 `Obj`、数学用 `.El`。
- `Tab` 是三字段结构 `{n, key, val}`（原来的 `Rel k v`），内容和 `Σ n, Vals A n × Vals B n` 相同，留名字是因为字段名 `.n .key .val` 被两千多处使用。
- 新的组合子加 `Known` 的字段，不加 `Rel` 的构造子。
- 「表已是 canonical」（按 `(key, val)` 升序、无重复）不放进 `Known`（它向下传边界，而这个事实从产生表的一步向上传），
  也不加成 `Tab` 的第四个字段（`⟨n, key, val⟩` 处处要改）：它是证明 `Tab.Canonical r := ∃ U, U.canon = .ok r`，
  在调用处静态决定。一个先 `canon` 输入的运算有 `…Of` 形式，直接取已 canonical 的表。例：`E(R)` 的 `mem X ≫ R`
  是 `≫` 的结果，最后一步已是 `canon`（`comp_canon`），所以 `E` 调 `lamOf` 而不是 `lam`，少一次 `asc → seen → gather`；
  `setify` 的 `mem X` 同理（`mem_canonical`）。
- 例外 `bits`（草稿，待审）：中间结果留作位矩阵，交给下一个选位矩阵的运算，不展开成行。`Known` 只向下传边界，
  不能把矩阵交回上层；`tab` 存的是行；`lazy` 是不透明的函数，所以加一个构造子。`rep (bits ..) = rep (tab (Tab.ofBits ..))`；
  任何不认识它的运算先 `runE` 读成 `tab`。

#card(c-sem, [`rep` 与 `compile`（规格写在类型里）])[
  `rep (tab (some t))` = 表读成的谓词；`rep (lazy f) = R` ⇔ 对任意 `K`、`L`，`rep (f ⟨K, L⟩) = K ≫ R ≫ L`（缺的一侧取 `𝟙`）。\
  `compile : (t : Tm A B) → η.Sound ρ → {r : Rel A B // rep r = ⟦t⟧ρ}` —— 返回值带着自己的证明，没有单独的
  `compile_sound`；每个节点的 `Gen.*_sound` 引理是 `compile` 定义的一部分，证明在编译时被擦掉。
  前提是 gap 全部清零（见 §7 TODO）；在此之前，现有的 `compile` + `compile_sound`（带 `t.gap = none`）保留。]

#card(c-rs, [Lean 证明不到的边界])[
  证明连到 Lean 定义为止。`@[extern]` kernel 的 Rust 实现只由 `decide`（kernel 中用 Lean body 算）与 `#guard`
  （运行编译后的 Rust）成对测试；Lean 编译器本身是信任基。kernel 越少，这条只有测试的边界越窄。
  读入侧也在这条边界内：文件字节读成表（`own_map` 的 `own::check`、`csv_read`）没有 Lean 模型能证明「读到的表就是文件的含义」，
  写出的文件能读回（往返律）同样只有测试。]


// ───────────────────────────── 1
= 语法：allegory 的项 `Tm : Obj → Obj → Type`

- 前端：`Parse` → `Elab`（得到 `Tm`）→ `Expand`（`rel_program`，elaboration 时编号 `share`、产出代码）。
- 语句 `input x : A ⟶ B from "路径"` / `output x to "路径"`（后接 `csv` 为 CSV，否则为 mmap 表目录；路径就是语句里的字面量）
  不是 `Tm` 的构造子：`input` 声明一个只有类型的名字，是后续语句里程序层的 `var`；`output` 指名一个定义或 `input`。下表「绑定 / 复用」一行不变。
  key 是位置（不落盘）当且仅当 key 对象是存为 `.long` 的数对象；其它 key 对象都是 key 列。CSV 的列按对象结构展开，
  `S+1` 是 `S` 每列一个可空列（`dataframe-design` F6 的落盘一条）；内存里 `atom+1` 是一列，null 是块内保留的顶残差（§4 foR）。
- 字面量 `{(a,b),…}` 里的一个词按它所在对象的 atom 读成存储字（`Elab.wordAt`）：整数 `3` `-3`；浮点 `2.5` `1e-3`
  （按 Lean 的浮点字面量读）；`date` 上也可写 q 的日期 `2024.01.15`，`datetime` 上写 q 的时间
  `2024.01.15D12:30:00.5`（小数 1–9 位）。日期、时间是一个词（中间无空格），值是 1970-01-01 起的天数、纳秒数（公历外推，
  年份 0001–9999），由 CSV 的读法 `Db.Csv.ymd`、`Db.Csv.stamp` 以 `.` 为日期分隔符读出（`Elab.qForm`）。词不在该 atom
  里（不存在的日子如 `2024.02.30`、超出 atom 范围、写在别的 atom 的对象上）时 elaboration 报错，写出这个词、对象和 atom。
- 文本 `"TK, main"` 是 Lean 的字符串字面量（转义按 Lean：`\"` `\\` `\n` `\t` `\xHH` 等），即它的 UTF-8 字节组成的数组：
  每个字节是 `char` 上的一个词（q 的写法 `"a"`、`"\ooo"`，`Tup.ofText`、`Elab.qForm`），所以只在元素对象是 `char` 的
  `[C]` 上成立，不是另一种机制。
- 字面量的对象：唯一持有它的词的已声明对象；多个对象都持有时，取其中每个作用在该位置上的数值运算（行的 `num`、`succ`、
  算术、`≤`、`<`）都接受的那一个（`Elab.settleLit`，`Pre.nums`），检查的两边一起定。`where` 里输入的表按该输入声明的类型读。
- 泛型定义（类型里有对象变量 `φ`）的体里可以写它的对象变量（`x $ φ`）。数动词（`succ` `arith` `≤` `<`、带 `num`
  约束的 row 如 `sqrt`）与 `$` 的合法性（`numObj`、`castOK`，合起来是 `Elab.numCheck`；它读的数对象表 `Pre.numsAt` 与 `settleLit` 是同一份）在对象变量上不在定义处判定，
  而是记下、在每次使用时判定：
  - 定义处先把每个变量当 `.long` 建一次常量（`Expand.once`）；建不成时，把变量上的这些检查留给使用
    （`ObjInfo.deferred`）再建一次，只作判定、不产出代码：建得成则定义合法、没有常量，否则报原错误。
  - 没有常量的定义、或常量对某变量不泛型（在 `.long` 上建）而调用给了别的对象时，调用就是定义在调用处对象上的展开
    （单态化，`Pre.call` 的 `alt`），`numCheck` 在具体对象上运行；所以 `GenSound` 的 `rowOK` 只面对具体 atom，不变。
  - 使用解出变量的对象后，`mkDef` 在展开上先跑 `numCheck`，报错写出调用、变量和它得到的对象：
    `` `avg` at this call, where φ is N: divide on N: … ``（`Rel/Lang/TestGenericNum.lean`）。
- 定义的体留下的、类型与参数都够不到的开放对象（`length $ F` 里 `length` 的 ℕ），按 let 泛化成该定义的隐式对象变量
  `n#i`（`Elab.generalise`，`mkDef` 的每次使用与无参定义都经过它）：没有使用能确定它，所以每次使用都取常量建变量时的
  对象 `.long`（未声明名字的 `objOf`），数检查照常在它上面跑（`numObj`、`numCheck`）。字面量与 `nil` 的开放对象仍归
  `settleOpen`；`check` 不是定义，其中仍开放的对象照旧报错。
- 泛型定义体里的数字面量（整数与浮点，`Elab.numParts` 读得出的词）先是开放对象（`Elab.litTy`），上下文可把它定在对象
  变量上（`⟨a, {(∗,0.5)}⟩plus` 里的 φ）；`numCheck` 在每次使用解出的对象上按该对象的 atom 读它的词（`litCol`），读不出
  就在该使用处报错：`` `inc` at this call, where φ is N: '0.5' is not an element of N, an object of i64 ``。
  体里写的字面量、其开放对象没有使用够得到的，在定义可见的已声明对象里定（`mkDef` 调 `settleLit`），不看调用方的对象。
  调用的实参里仍有 `settleOpen` 才定的对象（字面量的、`nil` 的源）时，不在此时选形式（closed、on demand、tested），
  调用的含义就是展开（`Expand.callDef`），但代码不复制实参：定义体在调用处只 elaborate 一次，每个参数是它自己的变量，
  得到 `call`，实参经 `arg` 各算一次、由 `Code.args` 绑定（`Elab.callOf`、`Pre.callE`）；`where x ≜ e` 同样是一个参数的
  `call`，`e` 为其实参（体里其它在作用域内的名字也作为参数传入，因为 `call` 的体只读自己的参数）。`build` 先建这个
  `call`，建不成（体要整读某参数、实参只能按对测试）时退回展开；分析（`numCheck`、`settleOpen`、极性）读展开。

#tbl(c-syn, (auto, 1fr), ([组], [构造子]),
  [allegory], [`id` `comp` `conv` `meet` `dom` `ran`],
  [distributive allegory], [`zero` `join` `top`],
  [division allegory], [`ldiv` `rdiv`；symmetric division 不是构造子，是定义 `R/S ∩ (S/R)°`（`Pre.symDiv`，含义 `Tm.symDiv_den`），表层写作中缀 `R ÷ S`（`Bin.table`，与 `/` 同一优先级、左结合）],
  [Boolean（有补）], [`diff`：需要补，不属于一般 allegory],
  [product / sum], [`outl` `outr` `pair` `prod`；`junc` = `[R,S]`（目标：加 `inl` `inr`，`[R,S] = inl° ≫ R ∪ inr° ≫ S` 成为定义；`juncD` 随 lazy `Rel` 消失）],
  [power], [`lam`（Λ） `E` `est` `thin` `nil` `atPos`],
  [数据], [`val R` `uni U` `succ` `arith` `leq` `lt`],
  [递归], [`mu` `nu` `fold`（`⦇e,S⦈`，代数 `[nil, snoc]` 上的 catamorphism：左折叠，步骤读 `(acc, x)`，从下标 0 向上；尽量从左到右读，程序的含义需要时才用从右到左读的 `foldr`（`⦇e,S⦈ʳ`，步骤读 `(x, acc)`，如 `thinL`）；输出数组只用 `snoc` 在末尾追加构造，从不在前面插入） `hylo`（`μX. c ≫ G(X) ≫ S`，原 `hylo`）],
  [绑定 / 复用], [`var` `share` `own` `call` `arg`],
  [库原语], [`prim r`：`prims` 表的一行（`inits` `tails` `prefix` `concat` `zip` …；`asc` `seen` 改为 kernel），在某个类型上实例化，参数由 `arg` 给出],
)

#card(c-syn, [改写引理（原 `Tm.Ax`）])[category 律、`°°`、`(RS)° = S°R°`、分配律、`𝟘`、`μ`/`ν` 展开（`ν = S ∩ b[ν]`）：每条写成 `⟦lhs⟧ρ = ⟦rhs⟧ρ`，由 `Rel/Core/` 中 `Core.Rel` 的定理证明；改写 `t₁` 为 `t₂` 只需 `⟦t₁⟧ρ = ⟦t₂⟧ρ`。Rel 只在 `Rel(Set)` 上运行，所以 `Tm.Le`、`Syn`、`Hom.den` 去掉。]

// ───────────────────────────── 2
= 语义映射 `⟦−⟧`：`Tm.den ρ : Core.Rel A.El B.El`

- 按结构递归、全函数、point-free：每个节点是若干关系的复合，与该节点的 `Gen.*_sound` 引理一致。
  例：`⟦nu k S b⟧ρ = Core.Rel.nu (X ↦ ⟦S⟧ρ ∩ ⟦b⟧(ρ[k ↦ X]))`（最大不动点）。
- 有 `input` 时，`⟦d⟧ρ` 在 `ρ` 把每个输入名绑到它的表上读（`Tm.gen_sound` 本来就对环境 `η` `ρ` 量化）；没有 `input` 的闭程序仍从 `Val.empty` 开始。
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
  [`til` `cycle` `floor` `widen`], [q verb，不是 allegory 运算],
  [`find` `bin search` `member` `match`], [q 的查找 verb；Rel 中是 `≫`（join）的特例],
  [`md5` 等], [q 运行时的需要],
)

q 的 `cast` 不移出，而是行 `$`（typed base S6）：`x $ F` 把 `x : A ⟶ N` 的每个值换成 `F` 的 atom 上同一个数，即与
`QAtomicType.embed s t` 的图复合。只允许保值方向：`s → t` 当且仅当 `s` 的每个值在 `t` 上都能精确表示（`castOK`，由两个
atom 的位宽、符号、指数和尾数位读出，不逐对列出），另加整数 → 浮点；后者在不能精确表示处没有像（部分映射，从不舍入，
`i64 → f64` 在 `2^53 + 1` 处无像）。有损方向（浮点 → 整数、宽 → 窄）在 elaboration 时报错并写出两个 atom。

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

#card(c-run, [`atom+1`：null 在带内（决定 K）])[
  可空原子 `V+1` 存成*一列*，含义仍是 `V+1`（null = `inr ∗`）。宽度字节只用到 64，第 7 位空出来作 null 标志：
  `widthAt` 读低 7 位，`nulAt` 读第 7 位（Rust `NUL_FLAG`、`Meta::w`、`Meta::nul`）。带标志的块里残差 $2^w − 1$ 是 null；
  不带标志的块没有任何代价，现有列的含义不变。\
  例：一块 $w = 6$、base $= 100$、带标志：残差 `000101` 是 $105$，`111111` 是 null（不是 $163$）。
  若该块非 null 值的跨度 $max − min$ 恰为 $2^6 − 1 = 63$，编码器把 $w$ 加宽到 7；全 null 的块是 $w = 0$ 加标志。
  base、`maxv` 是非 null 值的极值，`bsum` 不计 null；null 排在列的最后（与 tag 在前的现有次序一致）。
  - 没有 null 字：规格把可空列的元素读成 `Option`（`foROpt`；`foROpt_top`：带标志块的顶残差读成 `none`；
    `foROpt_plain`：不带标志的块读成原值）。普通的 `Arr t n` 只在没有带标志的块时成立。
  - kernel 不解码，只在编码上判 null（`foRNul`：标志 ∧ 无 patch ∧ 残差 $= 2^w − 1$）：`inl` 不动存储；`inl°` 留非 null 行
    （不带标志的块整块留下）；`inr°` 留 null 行；`tot(R)` 是 scatter 到全 null 列；`sum` 经 `bsum` 跳过 null。
    gather、scatter、seen 带着标志走（gather 出的块可能变成带标志）。
  - 浮点：ALP 的每块整数也是 foR（`alpBits` 读 `foRBits`），同一标志适用。
  - 范围：只有 `atom+1` 在带内；`(V+1)+1` 与一般 `A+B` 仍是 tag/idx，内层的 `V+1` 作为 payload 存在带内。
  - `1` 是单元对象 `Obj.one`（决定 M）：elaborator 把单元素对象存成它，不再是 `.long` 的 code 0；规则由类型给出。]

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

#tbl(c-rs, (auto, 2.2fr, 1.8fr, 1fr), ([kernel], [形状（输入输出都是 foR）], [定律], [现有 driver]),
  [`scan`], [`(op : @& Op) (rev : Bool) (s t) (n) (seg : Option Enc) (es : List Enc) (pre post : List (Op × UInt64)) : Enc × Option UInt64`，分段前缀折叠；含 map（`seg = none`：每行一段）与 fold。每个输入字先过 `pre` 链、每个输出字再过 `post` 链（每步 `op.eval x c`），一趟完成 element-wise 的复合（批准 A）。第二个分量是折叠结果：最后访问的那一行（正向第 `n − 1` 行，`rev` 时第 0 行）按 `t` 的宽度截取的字，`n = 0` 时为 `none`；kernel 写输出时从累加器取得，无需解码输出（`kscan_last`）], [`raw_scan`], [`scan` `map` `fold`],
  [`gather`], [`(ix : Enc) (e : Enc) (fill) : Enc`，`out[i] = e[ix[i]]`], [`raw_permute`], [`permute`],
  [`scatter`], [`(ix : Enc) (e : Enc) (n) (fill) : Enc`，`out[ix[i]] = e[i]`], [`raw_scatter`（新）], [—],
  [`asc`（草稿，待审）], [`(m) (es : List (AscKey × Enc)) : List Enc × Enc`，`AscKey = atom t ┃ cells n c lo hi els`；
    按若干列字典序稳定排序：每列排好的值 + 排列], [`asc_sorted` + `asc_perm`（新）], [—],
  [`seen`（草稿，待审）], [`(n) (es : List (AscKey × Enc)) : (k, g, first)`，各列按 `asc` 的方式读；行须已按 `asc` 序，否则报错（先跑 `asc`）：`k` 为组数，`g` 为每行的组号（按首次出现编号），`first` 为每组第一行的位置；如键 `A B B`：`k = 2`，`g = 0 1 1`，`first = 0 1`], [—（`asc ≫ seen` 给出 `asc` 的并列组编号；定理待写）], [—],
  [`bitrows`（融合 kernel，草稿，待审）], [`(all : Bool) (w na ni g) (ends idx m : Enc) : Enc`，`m` 是 `na · w` 位的 `u1` 位矩阵（第 `i` 行占 `[i·w, (i+1)·w)` 位）；输出 `g · w` 位：第 `r` 行 = 第 `r` 段 `[ends[r-1], ends[r])` 中各 `idx[k]` 行的 `∨`（`all = false`，即 `≫`，空段为 0）或 `∧`（`all = true`，即 `\`，空段为 1）。只在位矩阵小时选用：`|A|·|B| ≤ 2²⁷`（`sudokupc9` 的 `π₁\(sup(X) X)`：作表 1.9e8 行，作矩阵 4.3e7 位）。选用规则（草稿，待审）：kernel 路径的 `≫`、`\`（`GenK` 经 `Tab.compSel`、`Tab.ldivSel`）先由 `compGroups` 的前缀和得展开行数 `T`，当输入矩阵 `na·w` 与输出矩阵 `g·w` 各 `≤ 2²⁷` 且 `< 2³²`、两者之和小于展开所写的 `64·T` 位（每行至少一个 64 位字）时（`Tab.bitsWin`）用位矩阵，否则用分块展开或计数。
    结果不展开（草稿，待审）：`≫` 选了位矩阵就返回 `Rel.bits`（`Tab.compSelM`），下一个运算若也读位矩阵则直接接上——
    `tab ≫ bits` 以左表值在 `bits` 行值中的序号选行，再 `bitrows`（`Tab.compTabMat`，输出 `≤ 2²⁷` 位时）；
    `bits ∩ tab` 以两侧在行值、列值中的序号取位 `o[a·w+c]` 过滤表（`Tab.keepBits`）；`R \ bits`、`bits ≫ S`、`∪`、`−` 先读成行。
    `rdiv` 经 `Tab.ldivSel`（`R/S = (S° \ R°)°`）同样可选位矩阵],[`Tab.compBits_comp`：`compBits R S = .ok X`、`comp R S = .ok Y` ⟹ `X.Holds = Y.Holds`；`Tab.ldivBits_ldiv`：`ldivBits` 对 `ldiv` 同式（由 `raw_kbitrows`、`csr_spec`、`colCat_raw`、`Tab.compBits_holds`、`Tab.ldivBits_holds` 证，`Rel/RepBits.lean`）。只证所表的关系相同；输出为 `Canon`（与 `Tab.comp` 的行序相同）未证：仓库中尚无从 `kasc` 秩序到 `Obj.lt` 的桥，现由 `Rel/BitsTest.lean` 的 `#guard` 对照], [`Tab.compBits` `Tab.ldivBits`],
)
- `AscKey` 的 `cells`（草稿，待审）：一个 `arr` 侧作一个键，列的每个字是格号，格 = `[lo, hi)` 夹到共享 payload
  `[0, c)`；`els` 是 payload 的键列。两格按元素逐个比较序码（字典序），真前缀在前；格长相同且各元素序码相等才相等。
  `arr char` 是它在 `els = [atom char]` 时的特例。
- 为什么 `arr` 侧是 `els` + `lo` + `hi`，不是 q 的 `els` + `starts`（owner 2026-11-20 定：保持 `lo`/`hi`）：
  #table(columns: 4,
    [布局], [数组], [格 `i`], [对 payload 的要求],
    [q], [`els` `starts`], [`els[starts[i], starts[i+1])`], [各格按序铺满 payload，不能重叠],
    [Rel], [`els` `lo` `hi`], [`els[lo[i], hi[i])`], [无：任意区间，可共享、可重叠],
  )
  - `cons°` 的尾是 `[s + 1, e)`，`snoc°` 的头是 `[s, e − 1)`，`cat°` 的两段是 `[s, s + u)`、`[s + u, e)`：都只写新的
    `lo` `hi`，共享原 payload。`fold` 和 `hylo` 每一步都做 `cons°`，所以这是递归程序的主路径。
  - `inits` `tails`：长 `n` 的数组有 `n` 个前缀（后缀），共享时是 `n` 个区间；按 q 的布局要把 payload 复制成
    `n²/2` 个元素。
  - `starts` 是 `hi[i] = lo[i+1]` 的特例；没有为它另设规范形式或快路径。
  - `ix`（每行一个格号）只属于排序键 `AscKey.cells`：多行指向同一格而不复制 payload；它不是 `arr` 侧存储的一部分。

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
  [优化], [`seen`], [Lean body = `Order.idsBy` 的 foR 形式（`Order.firstsBy` 取每组第一行，行的组号 = 其键在其中的下标）；未写成 `scan` / `scatter` 的复合], [行须已按 `asc` 序：一遍扫描做游程检测；`∩ ∪ − ≫ dom ran` 都以它结尾],
  [优化], [`asc`], [radix sort：每一位 `scan`（直方图、前缀偏移）→ `scatter`；`arr char` 用 MSD], [比较排序常数小],
  [优化], [`gather`], [`(ix[i], i)` 与 `(j, e[j])` 拼接 → `asc` → `scan` 向后填 `e` → `scatter` 回 `i`], [O(n)，不必排序],
)
- Lean body 只需信任两个原语；每个优化 kernel 配一条定理 `k = 上表中的复合`，所以它的 Lean body 可以就是那个复合，
  Rust 实现仍由 `decide`/`#guard` 对它测试。
- `Op` 是有限的运算集（`add` `sub` `mul` `min` `max` `eq` `lt` `and` `or` `not` `first`，及 float 的 `fadd` `fmul` `fdiv` `flt` …），而不是 Lean 闭包：Rust 只能执行固定的运算集，
  Lean body 用 `Op.eval` 解释它，所以 `decide`/`#guard` 的检查方式不变。
- `Op` 不再是枚举：`cast (s t : QAtomicType)` 带两个字段（S6），所以 `kscan`/`kscatter` 以借用对象 `@& Op` 传它，
  不再是一个字节。无字段的 `Op` 是 `lean_box(序号)`，`cast s t` 是 tag 46 的构造子对象，两个 `u8` 标量字段；
  Rust 用 `op_code` 读它。plan 寄存器（`Reg Op`）与 C 发射器同样按对象传。

== allegory 运算 → kernel

#tbl(c-sem, (auto, 1fr), ([运算], [由哪些 kernel 复合]),
  [`°`], [交换 key / val 两列，无 kernel],
  [code（相等 ⇔ code 相等）], [`seen`（`g` 即 code，按首次出现编号；行须已按 `asc` 序）],
  [`∪`], [两表拼接 → `asc`（key, val 两列）→ `seen`（`first` 取代表行）],
  [`∩` `−`], [两表拼接、带来源标记 → `asc` → 每组相等行数 `scan` → 保留出现在两侧（`∩`）或只在左侧（`−`）的组],
  [`≫`], [两侧按中间列 `asc`、取组（`seen`）、组内展开（`scan` 偏移、`scatter` 组头、`scan(max)` 填充）、`gather` 取行、`asc` + `seen`。（草稿，待审）展开总行数超过 `blockRows` 时分块：在组的边界切开，每块至多约 `blockRows` 行（单个大组自成一块），每块先 `asc` + `seen` 去重，再与前面的结果做 `∪`；块只切 `R` 的行，`S` 每块整体参与（`Tab.compWith`，`Rel/Run/Comp.lean`）],
  [`dom` `ran`], [取一列 → `asc` → `seen`（`first` 取代表行）],
  [`R\S` `R/S` 对称除 `R ÷ S`], [不求补：按组比较「R 的 b 的个数」与「其中满足 S 的个数」，即分段 `scan`],
  [值动词 `plus` `minus` `times` `divide`（`%`，只在浮点 atom 上）`div` `mod` `max` `min`（`Tm.arith t`）], [两个操作数各与 `dom U` 复合（`≫`）→ 一次 `scan` 链：`i64` 上是整数 `Op` 加回绕/null 标记（`stepCols`）；浮点 atom 上先 `f32to64` 宽化，再 `fadd` `fsub` `fmul` `fdiv` `fmax` `fmin`，`div` 为 `ffloor(fdiv)`、`mod` 为 `x − y·ffloor(x/y)`（q 的定义），最后 `fto t` 写回 `t` 的规范字（`f32` 舍入、`−0` 写成 `+0`、NaN 写成 null）→ 非 null 的行 `keep` → `≫ U`；无新 kernel],
  [`<` `≤`（`Tm.lt t`、`Tm.leq t`）], [两侧（`K` 的 `pairs`，或 `dom U` 的 CROSS）→ `scan` 一次比较：`i64` 用有符号 `lt` `le`，浮点 atom 宽化到 `f64` 后用 IEEE 的 `flt` `fle`（`Tab.ordOp`）→ `keep`],
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
    结果 `G − ⟨G, G⟩ ≫ Y ≫ π₁`。只用 `∋` `⟨,⟩` `ran` `−` `≫` `π₁` 各行，`Q` 只在一个数组内的对 `D` 上跑；
    `D` 是 coreflexive，`D − Q(D)` 只看 `Q p p`，即 `Q` 按对角读（`D − Q(D) = D − (Q(D) ∩ D)`）],
  [`thin(Q)`], [`G` `D` 同上；`Q` 按对角读（同 `est`）：`Δ = Q(D) ∩ D`（`D` 中 `Q p p` 的对 `p`）；
    `w = D ≫ ⟨π₂, π₁⟩`，`S = dom (w ≫ Δ)`（交换后也在 `Δ` 中的对；`D` 含每对的交换），`Y = Δ − S`
    （严格胜出的对）；结果 `Λ(G − ⟨G, G⟩ ≫ Y ≫ π₂)` on `X`。`Q` 只跑一次],
  [`cat`（`(xs, ys) ↦ xs ++ ys`）], [两 payload 拼接（`scatter` + `scan(add)`）→ 两侧格界 → `scan` 宽 `w₁ + w₂` →
    EXPAND → `gather` `s₁[G]` `s₂[G]` `w₁[G]` → `scan` 选下标（`u < w₁` 取第一段 `s₁[G] + u`，否则
    `m₁ + s₂[G] + u − w₁`）→ `gather` payload → `scan` 前缀和得新格 `lo` `hi`；
    `n(m₁ + m₂) + n + m₁ + m₂ ≥ 2^63` 拒绝。是 §7 中应成为定义的列表运算的融合形式，`⟦cat 行⟧ = ⟦定义⟧` 未证],
  [`snoc` `cons`], [`(𝟙 × τ) ≫ cat`、`(τ × 𝟙) ≫ cat`；这里的 `τ` 是逐行单元素格 `[i, i + 1)`（`scan`），
    不经 Λ 行、不 `canon`。同为融合形式，`⟦snoc 行⟧ = ⟦定义⟧`、`⟦cons 行⟧ = ⟦定义⟧` 未证],
  [`zip`], [两侧格界 → `scan(min)` 宽 → EXPAND → `gather` 两 payload 各在 `s₁[G] + u`、`s₂[G] + u` →
    `scan` 前缀和得新格；拒绝条件同 `cat`],
  [`sum`（`⦇0, +⦈`）], [格界 → EXPAND → `gather` 元素 `v` → 每格首元素（偏移 0）标段 → 自左向右分段
    `scan(add)`（i64）或 `scan(fadd)`（f64）从 0 得前缀和 `W`，测坏步（i64：溢出或 null `−2^63`；f64：`fto` 后
    `W' ≠ W` 或 NaN）（`sumTail`，与 `sums` 共用）→ `scatter(or)` 得坏格、`scatter(last)` 取每格末行的和（空格为 0）
    → where 留无坏元素的格（坏格不出现在结果中，不报错）；`n·m + n + m ≥ 2^63` 拒绝。值对象为 i64 或 f64
    （`sumAtoms`），含义是左折叠 `sumAt`（`Tab.sum_holds`）。融合行只用在没有 universe 的对象上；target 有 universe
    （声明的有限对象，或泛型常量里的数变量）时 elaborator 构建定义本身（row 表的 `Prim.dfn`：`sum` 是 `⦇[0, plus]⦈`，
    `length` 是 `⦇[0, π₁ succ]⦈`），所以每一步都留在对象内：`−3…3` 上 `[3,3,−3] sum` 无结果（中间和 6），`1…5` 上
    `length` 为 `𝟘`（fold 从 0 起步）。造出新数的 row 必须带 `dfn`],
  [`sums`（q 的 `sums`，`x : κ×ν ⟶ γ` ↦ `κ×ν ⟶ γ`）], [`canon(x)` → 全 key 列 `seen`（组数少于行数即 `x` 不简单，
    报错并给出该位置）→ `κ` 列 `seen` 得每个 key 的首行 → `scatter(last)` 得段标 `seg` → 分段 `scan(add)`（种子 0）得
    前缀和 `W` → `scan` 测溢出（`v` 与 `W − v` 同号、`W` 异号）或 null `−2^63` → 分段 `scan(or)` 把坏步传到该 key
    之后各行 → where 留无坏步的行（同 `sum`，不报错）。值对象为 i64 或 f64（`sumAtoms`）：f64 上同一段标做分段
    `scan(fadd)`（种子 `+0`，自左向右，q 的顺序）得 `W`，`scan(fto)` 得 `W'`，`W' ≠ W` 或 `W' = 2^63`（NaN）为坏步，
    同样分段 `scan(or)` 传播；`W'` 既非 `W` 也非 `2^63`（`−0`）报错。f32 按名报错并提示先 `$` 到 f64
    （`stepAt .f32` 每步舍入到 f32，一次 `kscan` 不能算）。不排序 `canon` 之外的东西、不回置换。含义是组合
    `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)`（左折叠，`rowDens` 即此组合），本行是它的融合形式（定理
    `Tab.sums_holds`，无前提）。`Prim.dfn` 同 `asc`：待 `dfn` 能读行的关系参数],
  [`$`（`x $ F`，`x : A ⟶ N` ↦ `A ⟶ F`，只在 `castOK N F` 的原子对之间）], [`scan` map（`Op.cast s t`，在编码列上）：
    每个值换成 `t` 中表示同一个数的字（`QAtomicType.embed`，不舍入），无像时写 null 字 `2^63`（任何像都不是它：
    `word_ne_nul`）→ `scan` map（`Op.ne`，对常量列 `2^63`）得 0/1 标志 → where（`keep`）→ `canon`。无新 kernel、无新
    导出。`Tab.cast_holds`：结果是 `embed` 在需求值上的图，无前提；像是规范字（`embed_canonical`：无 NaN、无 `−0`）。
    不在 `castOK` 中的对（浮点 → 整数、宽 → 窄）在 elaboration 时报错],
  [一元浮点动词 `sqrt` `neg` `abs` `exp` `log` `sin` `cos` `tan` `asin` `acos` `atan` `floor` `round`（`x : A ⟶ F` ↦ `A ⟶ F`，
    `F` 为 f32/f64；`floatOps`）], [`f32` 先 `scan` map `f32to64` 宽化 → `scan` map（该行的 `Op`：`fsqrt` …）→ `scan` map
    `fto t` 写回规范字（NaN 写 null）→ `scan` map `Op.ne` 得标志 → where（`keep`）→ `canon`，与 `$` 同形
    （`keep_canon_holds`），末两步与值动词共用（`ftoCols`）。无新 kernel、无新导出。`Tab.floatOp_den`：结果是 `floatDen o`
    在需求值上的图，无前提；`√−1`、`log −1` 无行。`floor` 与 `round`（就近取整、平局取偶，IEEE roundTiesToEven，
    `Op.roundEven`；q 无 `round`）回 `i64`（末步 `Op.ofF64 .i64`），NaN 与 `i64` 外的值无行。整数对象上按名报错，提示先 `$`],
  [二元浮点动词 `xexp`（q 的 `x xexp y` = `x^y`；`⟨x, y⟩ : A ⟶ F×F` ↦ `A ⟶ D`，`F` 为 f32/f64，`D` 为 f64；
    `floatOps` 中 `Op` 读两个操作数（`Op.readsAcc`）的行）], [同一元浮点动词，一次 `scan` map 读两列：两操作数经
    `f32to64` 宽化 → `fpow`（libm `pow`）→ `Op.ofF64` → `Op.ne` 标志 → where（`keep`）。无新 kernel、无新导出。
    `Tab.floatOp_den`：结果是 `floatDen fpow` 在需求值上的图；负底数配整数指数有值（`(−2)^3 = −8`，
    `exp(y·log x)` 在此无值，这是本行存在的理由），NaN 无行],
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
    `G` 的成员关系），再 `D ≫ μX. N ≫ φ(X)`；两处都是 `Tab.mu`（`∪` 行的轮次），不建中间结构；无环时至多 `|N| + 2` 轮；
    有环则报错（草稿，待审）：`νP. dom(N ≫ ch ≫ P)`（`Tab.nu`）自 `N` 起，非空即有节点从自身可达，不给静默的 `𝟘`],
  [`loop(F)`（草稿，待审）], [`P ≫ loop(F)`：在 `ran P` 的每个 `(c, ys)` 上，以 `c` 起、沿 `ys` 的左折叠
    （`Tab.foldRounds` + `cons°`），每轮 `p ≫ F(ran p)`，`p` 为该轮的对 `(acc, y)`],
  [`merge(Q)`（草稿，待审）], [状态 `((x, y), acc)` 自 `((x, y), [])` 起，以 `cat(x, y)` 为时钟跑 `|x| + |y|` 轮
    `Tab.foldRounds`：`Q` 按对角读（同 `thin`）：`l = dom(⟨a, b⟩ ≫ (Q(D) ∩ D))`，`D = ran ⟨a, b⟩`
    （`a`、`b` 为两侧 `cons°` 的头；`(a, b) Q (a, b)` 的键），`l` 或 `y` 空时取 `a`，否则取 `b`，
    `snoc` 到 `acc`；结果 `π₂`],
  [`thinL(Q)`（草稿，待审）], [`⦇nil, bump(Q)⦈ʳ`（`Tab.foldRounds` + `snoc°`）；`bump` 在对 `(x, ys)` 上：
    `u = ys ≫ cons°` 得 `(b, bs)`，`Q` 按对角读（同 `thin`，`Q(D) ∩ D`）：`(x, b) Q (x, b)` 时 `x :: bs`，
    `(b, x) Q (b, x)` 时 `ys`，`ys` 空或两者皆否时 `cons`（`x :: ys`）],
  [`F(R)`（草稿，待审）], [格界 → EXPAND → `gather` 元素成平铺 payload `v`（`T` 行）→ `⟨pos, v⟩ ≫ R`（按位置作键）；
    每个位置恰一个像（`R` 在这些元素上是函数）时，像按位置序即新 payload，格宽不变（`Vals.cells`），一遍完成；
    否则（某元素 0 个或 ≥ 2 个像）为左折叠 `⦇nil, ⟨π₁, π₂R⟩ snoc⦈`（`Tab.foldRounds` + `cons°`，每元素一轮）；
    `n·m + n + m ≥ 2^63` 拒绝],
)

== Rust 侧

#tbl(c-rs, (auto, 2.5fr, 1fr, 1fr), ([IO 导出（不是 kernel）], [形状], [Lean 模型], [定律]),
  [`own_map`], [`(path) : IO OwnFile`：mmap 一个列文件，`own::check` 拒绝会读越界的块], [`ownParse`（不含 `own::check`）], [—],
  [`own_write`], [`(path code attr kind count domain parts) : IO Unit`：写临时文件再 rename], [`ownImage`], [`ownParse_ownImage`],
  [`csv_read`], [`(path cols) : IO (USize × List Enc)`：CSV 直接读成按声明的 schema 定型的 foR 列，不经解码的整列], [`csvWords`], [—],
  [`csv_write`], [`(path cols n es) : IO Unit`：每块取列的一段，格式化后按序写临时文件再 rename], [`csvText`], [`csvWords_csvText`],
)
- IO 导出读写文件，不做关系运算，所以不在上面「allegory 运算 → kernel」表里占行，也不计入 5 个 kernel。
  输出键是 `N` 时写一张重编号的新表；其它键写 key 表与 val 表（磁盘上 `key/`、`val/`）。mmap 读入的 float 列读时检查规范形。

#grid(columns: (1fr, 1fr), gutter: 8pt,
  card(c-rs, [crate 结构])[`scan.rs` `gather.rs` `scatter.rs` `asc.rs` `seen.rs` 各一个导出；`pack.rs` 是分块编解码（不导出）；
    `pod::Elt`、`by_width!`（u1、char、i8–i64、f32、f64）、`pool` 保留。`RELK.txt` = 5 个 kernel 加保留的 `stop`、
    `coc_encode`、`coc_decode`（`PLAN.md` 第 5 节 R4）；`RELIO.txt` = IO 导出（`own_map` `own_write` `csv_read` `csv_write`）。
    `syms` gate 读两个文件：二者不相交，并集 = crate 定义的 `qlean_*`。],
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
  text(fill: c-rs)[Rust], [`crate/`], [`relk`], [5 个 kernel 的 `qlean_*`（`RELK.txt`）与 IO 导出（`RELIO.txt`）], [—],
  text(fill: c-rs)[native rt], [`crate/rt/`], [独立 package], [替代 `libleanshared` 的 Lean runtime], [—],
)

= Gate

`make check` = #box[build] · compile-diff（`compile` 对 `rel_program` 差分）· crate-test · syms · native · ldd · index ·
index-complete · axioms · noreduce · panic · externs；`syms` 读 `RELK.txt` 与 `RELIO.txt` 两个列表；另加 `lake -d freyd/relaop build RelAop -R -K rel=…`。

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
- symmetric division 不加构造子：它是定义 `R/S ∩ (S/R)°`（`Pre.symDiv`），由 `rdiv` `meet` `conv` 组成，表层语法 `R ÷ S`（已完成）。
- 改名：去掉 `Den` `Dem` `Fn` `CRel`，`Rel k v` 改为 `Rel A B`（`tab` ┃ `lazy`），`Tm` 去掉 `d`。
- kernel 缩到 5 个：原语 `scan` `scatter`，优化 `gather` `asc` `seen`（各配「= 原语复合」的定理）、编码只留 foR（块长 `lg` 每列可选）、原子 u1 char i8–i64 f32 f64 sym；q 专用 kernel 留在 qlean 的副本（tag `qlean-base`）。
