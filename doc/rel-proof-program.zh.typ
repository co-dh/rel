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
  #text(10pt, fill: gray)[Rel P9 · 9.1 评审稿 · 基线 d19b9a5]
]

= 范围与评审决定

`rel_program` 在缺少必需证明时停止 elaboration。带证明的程序定义写在 `rel_program` 内部。
它同时给出一个关系 `A ⟶ B` 和一个同型关系等式。推导首式给规格，末式给定义体，证书记录两式相等。
具体输入的行比较由独立的测试声明执行。

#tbl(blue, (auto, 1fr), ([评审项], [建议]),
  [程序的证明类型], [在 `rel_program` 内声明关系 `p : A ⟶ B`，推导产生 `spec = p`。类型和证明目标只使用 Rel 的对象、关系与等式。],
  [证明来源], [calc 的理由引用 Rel 内具名的 Lean 定理。候选 `by lemmaName` 引用已检查的证明，elaborator 将其类型与声明目标核对。参数和实例由目标推断，law 的前提由 `using` 或当前已证假设提供。],
  [推导生成程序], [候选 `derive p : {r : A ⟶ B // spec = r} := calc`。最后一个完整表达式是定义体，证明随定义导出。局部引理由推导的 `where` 绑定。],
)

9.8 以已合并的 PR 为准。用户可写 `Λ(R)`，其定义为 `(𝟙÷∋)E(R)`。
Mss 与 Prelude 等式仍写显式复合。集合由严格升序数组表示，有限像条件由定理陈述与证明表达。

= 9.2 编译证书的接入点

`Expand.emit`（`Rel/Run/Lang/TmGen.lean`）把定义、打印、检查两侧及输出可达的 IO 定义
送入 `Code.program`，再生成共享槽、`Tm` 与 `Tm.gen` 调用。普通入口在空 `Known` 下调用
`runE`。IO 入口在输入读入后通过 `Code.args` 绑定，再调用 `Tm.gen`。首批接普通入口，IO
入口单独验证输入绑定保持 `Sound`。

源码中的证明目标是 `spec = p`，其中两边都是 `A ⟶ B` 的关系。
若后续法则需要在需求上下文内使用它，可对等式两边复合相同的关系。
例如当 `K : X ⟶ A`、`L : B ⟶ Y` 时，复合 congruence 给出 `K spec L = K p L`。
声明中的参数使用 Rel 的带类型关系参数。

编译器内部另外检查实际生成的代码符合该关系的语义。合法 demand、共享槽、成功结果的表示，
都由内部 soundness 验证处理。运行时 IO 与分配失败按现有执行语义报告。证明字段在编译时擦除。

+ 在编号前检查极性与候选共享子项的闭性，生成
  `∀ d ∈ ds, d.2.2.GenHyp (fun _ R => R.fv = [])`。用 `Tm.monoOK_iff` 分解极性义务，
  用结构证明补闭性。保留 `Tm.hasCode` 对缺少 kernel body 的拒绝。
+ 在编号后用 `Code.program_sound` 得到共享表的 `Sound` 与已编号项的完整 `GenHyp`。
  用 `Tm.gen_sound` 生成证书。证书直接引用 Lean 中发出的项和槽，`tmE` 的结构比对继续检查
  metaprogram 序列化。先验证证书字段与实际调用的代码定义等价，再接回现有 `Except String (Tab A B)` 接口。
+ `GenSound` 已 import `TmGen`。把需要证明的 elaboration 层放在两者之上，先用 Prefix 验证导入方向。
  保留 `RelRun` 的 precompile 边界。用构建图确认通用证明编辑不会把程序和测试拉进运行库。
+ 测试普通定义、共享槽和需要 `Code.args` 的 IO 定义。比较运行结果及错误路径。Lean 证明覆盖 Lean 定义，
  Rust extern 与文件 IO 仍沿用仓库现有差分和往返测试。

= 9.3–9.6 Prefix 验证切片

```text
derive prefixC : {p : [α] ⟶ [α] // prefix = p} := calc
  prefix
    := unfold prefix
  cat° π₁
    := foldUP([nil, nil ∪ cons], cat° π₁) using prefixEq
  ⦇[nil, nil ∪ cons]⦈ʳ

check x prefixC = x prefix by prefixOnInput
test  e prefixC = e prefix
test  {(∗,3 1)} ⊑ x prefixC
```

每个完整关系式只写一次。缩进的 `:=` 行证明它上方与下方的式子相等。

`prefixOnInput` 使用 `prefixC.spec` 的对称性和复合 congruence。证明目标是此条 `check` 实际
elaborate 的两项在同一环境下的等式。对带参数的定理，环境量化该声明的对象和关系参数，
`if` 假设写作 Rel 等式或包含关系。elaborator 在 Lean 内核中检查这些关系判断，等式链中的包含步拒绝 elaboration。

#tbl(violet, (auto, 1fr), ([代码位置], [第一批改动]),
  [`PrefixCata.lean`], [将 `Tm.prefixFold_prefixDef` 与通用 seed 引理移到 `Programs.Prefix` 可导入的证明模块。先用通用定理核验具体 check，再接入 `foldUP` 与 `prefixEq`。程序专属的 `c.t3/t4/t7` 留到 source-level check 接通后清理。],
  [`Syntax / Grammar`], [为推导保留首式，每步的关系符、理由、源码位置和完整后继式，以及局部引理。以 `Why` 表示 law 引用与定义展开。为 `check` 和具体输入测试分别建声明。],
  [`Embed / Parse`], [解析理由和局部作用域。先确立参数与对象 scope，再解析每步。用 elaborated term 检查首末项。程序 variant 若改变定义，重新验证依赖该定义的证书，或在没有替代证明时报错。],
  [`Expand / 编译证书层`], [根据同一次 typed elaboration 生成程序体和证明目标。为生成的 `prefixC.spec` 检查完整 proof term，再允许导出及复用。],
)

验收例删除 `using prefixEq` 后，`foldUP` 所需的 algebra-square 前提应出现在该行错误中。
还要检查同类型的错误中间式、包含步用于等式、局部引理越界、variant 修改后复用旧证书，以及
错误的 self-converse 声明。优化只读已在原始 denotation 上验过的 law，避免 `convs prog`
从声明本身读取尚未证明的优化事实。

= 9.10 迁移批次与 9.9 义务表

#tbl(green, (auto, 1fr, 1fr), ([批次], [已有锚点], [完成条件]),
  [Prefix], [基线有 3 条具体 `check`。通用 fold 语义已有证明，`foldUP` 和 `prefixEq` 的通用陈述见旧分支。], [末式运行同一 fold，source-level check 通过，原来的输入覆盖仍可执行。],
  [Prelude], [6 条待验证 law。先做 `absorption`、`Eunion`、`Ecomp`、`estMap`，再处理 `permConv` 与 `starLinear`。], [参数和前提与实际对象一致。为已声明有限 atom 对象建立可复用的有限像证据。],
  [Mss], [已有 `toShape`、`toGreedy`、`linear` 三条 calc。先接 `toShape`，再分开处理 `toFused`、`greedyFold`、`toScan`。], [末式生成可执行 scan。声明对象与运行时算术下的原有样例保留。遇到溢出或无限像，给出具体项和缺失前提供评审。],
  [其余程序], [文本初扫 `Rel/Programs` 有 64 条 `check` 和 16 条 theorem，`Rel/Lang` 的程序块约有 960 条 `check`。], [以 parser 和声明索引复核清单。迁移具体输入测试时同步更新 `TestCompile` 的 literal-row 覆盖统计。所有迁移完成后启用全仓严格模式。],
)

9.9 每条 companion 引用记录原文位置、关系与对象的量化、前提、Rel 声明、证明依赖和当前阻塞。
在被引用的 law 全部有记录后核对覆盖。图导出继续暂缓。Rel 内全部证明完毕且运行路径无
`relaop` 引用后，再通知 freyd 清理桥。

= 验收与基线

在同一 checkout 布局和资源限制下记录迁移前后的 `AllPrograms` 时间，运行 `make allcov`、
`make compile-diff`、`make pc9-time` 及现有 pointfree、decode、listban、axioms gates。
Prefix 首批还运行相关正、负例和 native 差分。保持现有覆盖和断言，证明项从可执行路径擦除。
运行完整基线需要可写的 `/data/tmp`，目前该目录在 Codex sandbox 中只读。
