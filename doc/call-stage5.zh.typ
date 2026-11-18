// palette and helpers copied from doc/rel-architecture.zh.typ
#let c-syn = rgb("#2f5d9e")   // syntax
#let c-sem = rgb("#7a3e9d")   // semantics
#let c-run = rgb("#2e7d4f")   // run-time / compiler
#let c-rs  = rgb("#b5541c")   // Rust
#let ink   = rgb("#222831")
#let soft(c) = c.lighten(88%)

#set document(title: "5.5 call（stage 5）提案")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.3cm), fill: rgb("#fcfbf8"),
  header: context if counter(page).get().first() > 1 [
    #set text(8pt, fill: gray.darken(20%)); 5.5 call（stage 5）提案 #h(1fr) base 0164b91 · 2026-11-18 ],
  footer: context align(center, text(8pt, fill: gray)[#counter(page).display()]))
#set text(font: ("Libertinus Serif", "Noto Serif CJK SC", "Noto Sans CJK SC"), size: 9.5pt, fill: ink, lang: "zh", region: "cn")
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

#let tbl(color, cols, head, ..cells) = table(
  columns: cols, stroke: none, inset: (x: 6pt, y: 3.8pt),
  fill: (_, y) => if y == 0 { color } else if calc.even(y) { soft(color) } else { white },
  table.header(..head.map(h => text(fill: white, weight: "bold", font: "Noto Sans CJK SC", h))),
  ..cells, table.hline(stroke: 0.8pt + color))
#let card(color, title, body) = block(width: 100%, fill: soft(color), stroke: (left: 3pt + color),
  inset: 9pt, radius: (right: 4pt))[#text(weight: "bold", fill: color, font: "Noto Sans CJK SC", title) \ #body]

#align(center)[
  #text(22pt, weight: "bold", font: "Noto Sans CJK SC", fill: c-syn)[5.5 `call`（stage 5）提案] \
  #v(2pt) #text(11pt, fill: gray.darken(30%))[Q11：调用 = 被调用者的 term，参数绑定为实参的语义 · base 0164b91 · 2026-11-18 · 不改 `.lean`]
]

= 现状（行号按 index，base 0164b91）

#tbl(c-syn, (auto, 1fr), ([位置], [`call` 今天的行为]),
  [`Tm.call` · `Run/Lang/Tm.lean:81`], [`call d c os cv`：只有常量名 `c`、对象 `os`、逆的常量 `cv`；没有 body。实参挂在 `arg` 链上。],
  [`Tm.den` · `Lang/Den.lean:339`], [`.call .. => 𝟘`；`Tm.argDen`（349）对 `call` 头也返回 `𝟘`。],
  [`Tm.gen` · `Run/Lang/Compile.lean:222`], [`leaf (none' A B d)`（`none'` 在 129）；`arg` 的头不是 row 时也是 `none'`（226）。],
  [`Tm.gap` · `Lang/Rows.lean:116`], [`"call: a generic definition's term waits for stage 5"`，所以 `compile_sound` 对 `call` 空真。],
  [Elab `convTm` 1335 · `build` 1656–1661 · `test` 1710–1713 · `callArgs` 1686], [生成 `Tm.call … c os cv`，再由 `callArgs` 加上对象变量的 universe 和实参。],
  [Expand `plan?` 637 · `spine` 666 · `node` 747 · `emit` 826–844], [代码是 Lean 常量 `c os pl₁ … plₙ`；每个 `Once` 由 `emit` 生成一个这样的常量。],
)

= 语义：`⟦call f args⟧ρ` 是什么

- 例子：`f(X₀, X₁) ≜ X₀ ≫ X₁°`，其 body 为 `b = var 0 ≫ (var 1)°`。调用 `f(R, S)` 的 term 是 `arg(arg(call 2 f b) R) S`。
```
⟦f(R,S)⟧ρ = ⟦b⟧[0 ↦ ⟦R⟧ρ, 1 ↦ ⟦S⟧ρ] = ⟦R⟧ρ ≫ (⟦S⟧ρ)°
```
- 一般式（`ss = [⟦x₀⟧ρ, …, ⟦xₙ₋₁⟧ρ]`，正是 `Tm.argDen` 沿 `arg` 链已经累积的列表）：
```
⟦arg(…arg(call n f b) x₀ …) xₙ₋₁⟧ρ = ⟦b⟧(Val.args ss)     // body 中第 i 个参数读作第 i 个实参的语义
Val.args ss = Val.empty.bind 0 ss₀ … .bind (n-1) ssₙ₋₁    // Val.bind 的实例，不是新概念
```
- 组合的关系：不引入新算子。`call` 组合的正是 body 的那些关系（`≫ ° ∩ ∪ …`），每个 `Xᵢ` 换成 `⟦xᵢ⟧ρ`；对象变量的 universe
  也是参数（`emit` 的 `rk` 变量，`callArgs` 的 `uni` 实参），同样处理。
- body 在 `Val.empty` 上读，不读 `ρ`：调用者的 `μ`/`ν` 变量不会漏进被调用者，和 `share` 一样。
- 与 inline 一致：实参都是 closed（`d = false`）时，`Tm.den_subst`（`Den.lean:478`）给出 `⟦call⟧ρ = ⟦b.subst σ⟧ρ`，
  `σ = [(i, xᵢ)]`。PLAN 的 Q11 "被调用者的 term 被 inline" 因此是一条定理，而不是 term 的复制。

= 机制：`call` 是 let 节点，body 是它的子项

#card(c-sem, [选择])[
  `Tm.call` 持有被调用者的 body（已在本次调用的对象上），实参留在 `arg` 链上，由 `argDen` 像 row 一样累积。\
  为什么：inline 展开（`Pre.call` 的 `alt`）使 term 随嵌套调用相乘增长，并丢掉"每个 form 一个 body"；按名字查定义的环境无法被结构递归的 `Tm.den` 跟随（设计 §1.2 "not a name-keyed environment"）。body 作为字段，`den`/`gen`/`compile_sound` 直接递归进去。
]

= 各模块的改动

#tbl(c-run, (auto, auto, 1fr), ([模块], [声明], [改动]),
  [Tm], [`Tm.call`], [`call (n : Nat) (c : Lean.Name) (b : Tm A B d) (cv : Option ((e : Bool) × Tm B A e))`：`n` 参数个数，`b` body，
    `cv` 逆的 body（取代逆的常量名）；去掉 `os`（body 已实例化）；`c` 只用于报错。`Tm.fv`/`subst`/`mapM` 待它如 `share`：
    `fv = []`，`subst` 保留，`mapM` 不进入。],
  [Den], [`Val.args`（新）`Tm.den` `Tm.argDen`], [§2 的两条子句；`den_congr` `den_subst` `den_pol` 的 `call` 分支：body 不读 `ρ`，`rfl`。],
  [Compile], [`Out.row` `Tm.gen` `CodeEnv.args`（新）], [`row : Option (Head × List Code)`，`Head := prim r | call n b`；`Tm.gen` 在
    `.call` 给出头；`arg` 凑满 `n` 个实参时代码为 `(b.gen (CodeEnv.args cs)).fn`，不满时仍是 `none'`。
    `CodeEnv.args` 是 `CodeEnv.bind` 在 plan 上的折叠。],
  [Rows], [`Tm.gap`], [`.call _ _ b _ => b.gap`，删去 stage 5 的字符串。],
  [CompileSpec], [`Out.Sound` `CodeEnv.Sound.args`（新）], [`Out.Sound` 的 row 子句改为对 `Head` 量化；见 §5。],
  [Elab], [`build` `test` `convTm` `Pre.call`], [`build`/`test` 用被调用者 `Once.res` 在 `os` 上的实例作 body（D/E）；
    `convTm`：`.call n c b (some ⟨e,u⟩) => .call n c u (some ⟨d,b⟩)`；`callArgs` 不变。`Pre.call` 带上 body。],
  [Expand], [`callDef` `plan?` `spine` `node` `emit` `RegEntry.call`], [`callDef` 把 `Once.res` 交给 `Pre.call`；
    `plan?`/`spine`/`node` 的 `call` 分支改成 body 在实参 plan 下的 `code`（A/B）；`RegEntry.call` 存 body（J/K）。],
)

= Soundness

- `compile_sound`（`CompileSpec.lean:238`）陈述不变：`t.gap = none → η.Sound ρ → (t.gen η).Sound (t.den ρ) (t.argDen ρ)`。
- 新增一个引理，`CodeEnv.Sound.bind`（`CompileSpec.lean:17`）的折叠：
```
theorem CodeEnv.Sound.args {cs : List Code} {ss : List Sem} (h : Code.Sounds cs ss) :
    (CodeEnv.args cs).Sound (Val.args ss)
```
- `call n c b cv` 分支：由 `b` 的归纳假设取 `η := CodeEnv.args (cs ++ cs')`、`ρ := Val.args ss`，`hη` 由上面的引理给出，
  正好是 `Out.Sound` 的 row 子句；实参个数不等于 `n` 时 `Head.run = none`，子句空真。

#tbl(c-sem, (auto, 1fr), ([条件], [为什么成立 / 谁负责]),
  [结构递归], [`b` 是 `call` 的字段：`Tm.den`、`Tm.gen`、`Tm.gap` 和 `induction t` 都直接进入 `b`，不需要 fuel 或 `termination_by`。],
  [term 有限（良基）], [定义之间的调用图无环：rel-lang-design 452 "A body names only earlier definitions: no recursion"；跨程序由
    Lean 的 import DAG 保证（module design 128）。递归只能写成 `μ`/`hylo`，其条件属于 5.2、5.3。Elab 的不变式：body 在调用之前已建好。],
  [对象不匹配], [`Val.args` 与 `CodeEnv.args` 都沿用 `bind` 的规则：在别的对象上读一个变量，得到 `𝟘` 和 ok 的 `zero`，两边一致。],
  [demand bit 不匹配], [参数以 bit `e` 绑定、以 `d` 使用：`false → true` 提升（`Tm.lift` 的对应），`true → false` 无 key，返回 `none'`（不 ok）；`PSound` 都成立。],
  [gap], [`(call n c b cv).gap = b.gap`：body 自己的缺口（`lam`、`hylo` …）照常传出。],
)

= 未决问题

#tbl(c-rs, (auto, 1fr, auto), ([问题], [选项], [建议]),
  [代码怎么出], [*A* 删掉按 form 生成的常量，调用的代码就是 body 在实参下 `compile` 展开（设计 §5.1 stage 5 "deletes `Tm.call`'s
    plan-passing constants"）· *B* 保留常量作共享代码，`emit` 把它定义成 `fun os pls => (b.gen (CodeEnv.args pls)).pl`，期望与调用点
    `rfl` 相等 · *C* 保留常量，`call` 留在 `gap`], [B：代码只出一次],
  [对象实例化], [*D* Run 中新增 `Tm.instObj os`，把占位 atom `varObj k` 换成 `os[k]`（表落在占位对象上时报错）· *E* 在调用的具体对象上重新跑 `once`，不加新函数，但每个对象实例一个 body], [D：`OExp.inst` 在 term 上的对应],
  [实参的 plan], [*F* `Code` 在 `Fn` 旁带上实参的 `Pl`，bit plan 穿过调用（设计 §5.2 "Env holds `Pl`"）· *G* 实参以其 `Fn` 的 `pleaf` 绑定，bit plan 在调用边界停止], [F],
  [逆], [*H* `cv` 存逆的 body（Elab 中 `convTm` 算出），如今天的逆常量 · *I* 去掉 `cv`，`convTm` 进入 body；参数的逆需要实参的逆，今天没有这个规则], [H],
  [别的程序的定义], [*J* `RegEntry.call`/`Sig` 存 body `Res` · *K* 导入方重新 elaborate 被调用者],
    [J],
)
