#let blue = rgb("#2f5d9e")
#let violet = rgb("#7a3e9d")
#let green = rgb("#2e7d4f")
#import "tbl.typ": tbl, soft

#set document(title: "Rel P9 · 程序与证明一体")
#set page(width: 25.2cm, height: 29.7cm, margin: (x: 1.8cm, y: 1.6cm),
  fill: rgb("#fcfbf8"),
  footer: context align(center, text(8pt, fill: gray)[#counter(page).display()]))
#set text(font: ("Libertinus Serif", "Noto Serif CJK SC", "Noto Sans CJK SC"),
  size: 10pt, lang: "zh", region: "cn")
#set par(leading: 0.75em)
#set heading(numbering: "1.1")
#show heading: set text(font: "Noto Sans CJK SC", weight: "bold", fill: blue)
#show raw: set text(font: ("JuliaMono", "Noto Sans CJK SC"), size: 8.6pt)
#show raw.where(block: true): it => block(width: 100%, fill: soft(green), inset: 9pt,
  stroke: (left: 2.5pt + green), it)

#align(center)[
  #text(24pt, weight: "bold", fill: blue)[程序与证明一体] \
  #text(10pt, fill: gray)[Rel P9 · 实现现状 · 基线 87f9a1e]
]

= 范围与现状

证明写在 `rel_program` 内部：`check … by lemma` 与 `theorem … by lemma` / `theorem … := calc`。
Lean kernel 检查的是两侧实际 elaboration 后的 `Tm.den` 的等式或包含。本节只记代码现在做什么，未做的单列。

#tbl(blue, (auto, 1fr, 1fr), ([评审项], [已实现], [未做]),
  [证明目标], [关系判断 `R = S` / `R ⊑ S`，对象与关系参数在 `∀ ρ` 之下量化，`if` 假设是目标的前提。证明常量为 `n.proof.<t>`，`check` 为 `n.proof.check<i>`。], [`derive p : {r // spec = r}`：推导的末式生成定义体，没有实现。定义体与 spec 仍是两个声明。],
  [证明来源], [`by lemma`：Lean 定理的类型与目标核对（`certify`）。calc 的一步引用已有证明常量的 theorem（`certifyCalc`）。], [`using`：前提只能取自 theorem 的 `if` 假设，没有 `using` 语法。],
  [缺证明时], [calc 中无法认证的步骤列入 `n.proof.unproved`，附原因，不报错。`by lemma` 的类型不符是 elaboration 错误，不发出可执行定义。], [`rel_program` 在缺证明时拒绝 elaborate：未实现，没有 `by` 也没有 calc 的 `theorem` 照常通过（见 9.10 表）。],
  [测试], [具体输入比较仍是 `check`（无 `by`）。], [独立的 `test` 声明：没有实现。],
)

9.8：用户可写 `Λ(R)`，定义为 `(𝟙÷∋)E(R)`；Mss 与 Prelude 的等式写显式复合。
集合由严格升序数组表示，有限像条件写在定理的陈述里。

= 9.2 编译证书

#tbl(violet, (auto, 1fr), ([证书], [内容]),
  [`n.proof.shares`], [`Tm.shareOK_iff` 把闭性与极性判定（`Tm.shareOK`）变成 `∀ d ∈ input, d.2.2.GenHyp (fun _ R => R.fv = [])`；`Expand.emit`（`Rel/Run/Lang/TmGen.lean`）发出。只在程序 import 了 `Rel.Lang.GenSound` 时发出（现为 Prelude、Prefix），共享子项含自由变量或不动点体非正时报错。],
  [`n.proof.sound`], [`Code.program_reps` 应用于 `n.proof.shares`：在共享表下，每个已编号项的生成码 `Reps` 其 denotation `d.2.2.den Val.empty`，对任意良构 store 成立。内部使用 `Code.program_sound` 与 `Tm.gen_sound`。],
)

- 范围：`n.proof.sound` 覆盖空 `Known` 下的项。IO 入口经 `Code.args` 绑定输入，其 `Sound` 保持未单独验证，仍为开放项。
- 证明项在编译时擦除；Rust extern 与文件 IO 沿用现有差分和往返测试。

= 9.3–9.6 语法与认证

下面是 `Rel/Programs/Mss.lean` 的 `toGreedy`，逐字：

```text
theorem toGreedy : fused = greedy := calc     -- note `mss-mono`, `mss-step`, the greedy row
  fused
    := ≜ fused
  (𝟙÷∋)E(suffix) E((𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥))est(≥)
    := greedyFold
  (𝟙÷∋)E(suffix) E(⦇[(𝟙÷∋)E(zero) est(≥), (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ)est(≥)
    := estMap(zero, ≥)
  (𝟙÷∋)E(suffix) E(⦇[  zero, (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ)est(≥)
    := ≜ oplus
  (𝟙÷∋)E(suffix) E(⦇[  zero, oplus]⦈ʳ)est(≥)
    := ≜ g
  (𝟙÷∋)E(suffix) E(g)est(≥)
    := ≜ greedy
  greedy
```

从 `Rel/Lang/PrefixCata.lean` 取一条带假设的 `theorem … if … by …`（`hypThm`）：

```text
private theorem hypId {A B : Obj} {R S : Tm A B} (ρ : Val) (h : R.den ρ = S.den ρ) : R.den ρ = S.den ρ := h

rel_program hypThm where
    obj N = 0…3
    theorem hy(R : N ⟶ N, S : N ⟶ N) if R = S : R = S by hypId
```

#tbl(green, (auto, 1fr), ([语法 / 机制], [现状]),
  [calc 的形状], [式子与理由行交替：第一个式子是陈述的左边，之后每个理由独占一行 `[⊑] := why`（缩进，无 cmpOp 时链接为 `=`），其后是新式子，最后一个式子是陈述的右边；每个式子只写一次，没有 `_`。局部 `where` 引理未做。],
  [`why`], [`≜ m`：展开定义 `m`，两侧 elaborate 成同一 `Tm`，证明为 `rfl`。其余：引用 theorem 名，取其 `….proof.m`（同 program 或 prelude 的常量），用 `Eq.trans` 串接。],
  [认证], [`certifyCalc`（`Rel/Run/Lang/Embed.lean`）逐步认证；`theoremChecks`（`Rel/Run/Lang/Expand.lean`）把陈述、前提和每个链接按同一签名 elaborate，`goalOf` 生成目标。引用的 theorem 若带前提，前提须在本 theorem 的 `if` 假设里找到。],
  [不能认证], [含 `⊑` 步，被引 theorem 无证明常量，前提找不到，或某步的类型不符：整条 theorem 进入 `n.proof.unproved`，附原因。],
  [对象变量], [theorem 未固定的对象变量被全称量化（`∀ σ`），`by` 与 calc 都按此认证（`genericTheorem`）。参数对象和 `𝟙` 的开放对象在读取 valuation 前实例化。],
  [`theorem` 的边类型], [两侧只按 Den 定型，`[N]` 作源不需要 universe（`convParam`）。`R°°` 读作 `R`。],
  [负例], [`badPrefix`：声称的关系改变后类型仍对，`by` 的证明类型不符，不发出任何可执行定义。],
  [`check … by lemma`], [Prefix 的第一条 check 由 `Rel.Lang.Tm.prefixFold_input` 证；`check e prefixC = e prefix` 与 `check {(∗,3 1)} ⊑ x prefixC` 仍无证明。通用 fold 证明在 `Rel/Lang/PrefixFold.lean`。],
)

开放：9.6f（calc 一步引用 `t(args)`，带实参）进行中；`derive`、`using`、`test` 声明、`where` 局部引理、`⊑` 链、Agda 风格 calc 未做。

= 9.10 / 9.9 义务表

状态按代码核对。"已证"指 theorem 带 `by lemma`，产生 `n.proof.<t>`。"引理在"指 Lean 引理已有（`Rel/Lang/Laws/*`），但 theorem 尚未接上 `by`。

#tbl(green, (auto, auto, 1fr), ([theorem], [状态], [证明 / 阻塞]),
  [Prelude `foldUP`、`foldrUP`], [已证], [`Rel.Lang.Tm.foldUP_den`、`Tm.foldrUP_den`（`Laws/FoldUP.lean`，来自 `foldUP`、`foldrUP`；`den` of `uncons`/`unsnoc`）。依赖 `#print axioms` 核对。],
  [Mss `zeroEntire`], [已证], [`Tm.dom_single`（`Laws/Map.lean`，经 `dom_of_entire`）。],
  [Mss `zeroSimple`], [已证], [`Tm.simple_single`（`simple_of_fun`）。],
  [Mss `geqRefl`], [已证], [`Tm.geq_refl`（`Laws/Order.lean`）。],
  [Prelude `absorption`], [引理在], [`EDen_absorb`、`lamDen_id_EDen`（`Laws/Absorb.lean`）；theorem 未接 `by`。],
  [Prelude `Eunion`], [引理在], [`EDen_union`（`Laws/Eunion.lean`）需每点有数组像（`∀ a, ∃ ys, lamDen T a ys`）；theorem 的陈述没有该前提，须补前提或限制对象，再接 `by`。],
  [Prelude `Ecomp`], [引理在], [`EDen_comp`（`Laws/Ecomp.lean`）；theorem 未接 `by`。],
  [Prelude `estMap`], [引理在], [`estMap_den`（`Laws/EstMap.lean`）只用 `simple(f)`；theorem 未接 `by`。],
  [Prelude `permConv`], [引理在], [`permDen_iff`（`perm` 的 denotation 是 `List.Perm`）与 `permDen_conv`（`Laws/PermConv.lean`）；未接 `by`。],
  [Prelude `starLinear`], [未证], [没有引理；`μX : S ∪ (R X) = star(R) S` 需不动点的唯一性。],
  [Mss `estUnion`], [未证], [没有引理；它的陈述依赖「no set empty」。],
  [Mss `greedyFold`], [未证], [没有引理；`(𝟙÷∋)E(⦇S⦈)est(≥) = ⦇(𝟙÷∋)E(S)est(≥)⦈` 须对 fold 归纳。],
  [Mss `toFused`], [未证], [没有引理，也没有 calc。],
  [Mss `toScan`], [引理在], [`toScan_den`（`Rel/Lang/MssScan.lean`）：对一般的种子 `Te` 与步 `TO`，按 elaborator 融合后的形状（`Λ(suffix g)`，左嵌套）证；未接 `by`。],
  [Mss `toShape`、`toGreedy`、`linear`], [认证受阻], [calc 引用的 theorem（`absorption`、`Eunion`、`estUnion`、`Ecomp`、`greedyFold`、`estMap`、`toFused`、`toScan`）还没有 `….proof.m`，所以列入 `n.proof.unproved`，原因是 `no proof constant for …`。上面的引理接上 `by` 后，`toShape` 剩 `estUnion`，`toGreedy` 剩 `greedyFold`。],
  [Prefix `prefixEq`], [不存在], [基线的 `prefixCata` 里只有一条 `check … by prefixFold_input`；`foldUP` 在 Prelude 已证，`prefixEq` 尚无陈述。],
)

- 其余程序：`Rel/Programs` 与 `Rel/Lang` 的 `check` 仍为具体输入测试，没有迁移，全仓严格模式未启用。
- 9.9：companion 引用的 law 尚无逐条记录（原文位置、量化、前提、Rel 声明、阻塞）；图导出暂缓。
- 完成判据不变：rel 内全部证明完毕且运行路径无 `relaop` / `rel_aop` 引用，再通知 freyd 会话清理。
  Mss 与 Prelude 里「owed to Lean: `rel_aop` …」的注释对应上表未证的行，随证明接上改写。

= 验收

- 已有：`n.proof.shares`、`n.proof.sound`、`n.proof.check<i>`、`n.proof.<t>`、`n.proof.unproved` 的 `#check` 在 `Rel/Lang/PrefixCata.lean`；负例 `badPrefix` 用 `#guard_msgs` 断言并检查没有导出可执行代码。
- 门：`lake build RelCore RelKernel RelRun Rel` 全绿；`foldUP`、`foldrUP`、`Tm.foldUP_den` 的 `#print axioms` 不含 `sorryAx`。
- 待做：去掉 `using prefixEq` 之类前提后错误落在该行；包含步用于等式、错误中间式、局部引理越界、variant 修改后复用旧证书；`make allcov`、`make compile-diff`、`make pc9-time` 与既有 pointfree、decode、listban、axioms 门，在同一 checkout 布局和资源限制下比较迁移前后的 `AllPrograms` 时间。
