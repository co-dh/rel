# Rel: 从 master 059f46c 迁移到 `rel-architecture.zh.typ` 的计划

目标的来源：`doc/rel-architecture.zh.typ`。现状的来源：`/home/dh/repo/rel` 在 059f46c 的 refactor index 及其指向的文件。
下文所有行号从 1 起计，只在 059f46c 有效；每一步开始时先用第 0 节的 index 查询重新读取它的 anchor。

第 5 节的 owner 决定（采用推荐的默认值；owner 可以推翻）：
- R1/Q4：`rep` 是谓词 `Reps`，`tab none` 表示每一个 relation（partial correctness）；诊断信息来自出错的节点，
  绝不来自被截断的 table。
- R4："kernel"（5）不同于 "runtime export"：`stop`、`Coc.encode`/`decode` 保留为 runtime export；
  `own_write` 和 group-id kernel 用 `EmitC` 重写。
- R5：atom 是 `u1 char i8 i16 i32 i64 f32 f64 sym`（九个）。真值是 `u1`（宽度 1），没有 `bool`；
  tag 是 `Arr .u1`
  （原为 `.boolean`）；`char` 是 8 位，字符串是 `arr char`；装箱的 `general` 和时间类 atom 删除。
- R7：浮点数先规范化（一个 NaN，`-0 ↦ +0`），再做保序的位映射；相等 = 规范化之后的位相等。
- R8：1.1 只写不是某条 `Core.Rel` 定律的复述的等式（`mu_unfold`、`nu_unfold`）；
  其余十条直接用作 `Core.Rel` 的定律。
- Q1 删除 `RelAop/Syn.lean`；Q2 表层的 `refold` 也变成 `hylo`；Q3 `tab` 持有 `Option (Tab A B)`，结构
  `{n, key, val}`（owner：M）；
  Q7 `Den` 手工 inline；Q9 `hylo` 保留 `k what ch body`；Q11 `call` 的意思是被调用者的 term 被 inline；
  Q12 `compile` 从 `RelRun` 移到持有证明的 library。
- 非 log 的输出（baseline、row 分析）写进本文件或 `doc/`，不写进 `/data/tmp`。

## 0. 每一步都遵守的约定

- Repo `/home/dh/repo/rel`。绝不 grep `*.lean`；定位一个 declaration 用

  ```
  sqlite3 -readonly /home/dh/repo/rel/.lake/build/refactor-index.db "select i.user_name, i.module, r.sl1+1, r.el1+1
    from decl_info i join decl_range r on r.name=i.name and r.module=i.module
    where i.internal=0 and i.user_name like '<PATTERN>'"
  ```

  查它的使用者用 `select use_module, group_concat(l1+1) from use_site where name='<FULL NAME>' group by 1`。
- `LR` = `/home/dh/repo/lean-refactor/scripts/lean-refactor`。先不带 `--apply` 运行（预览），再带上。
  每次 `LR` 运行之后：`LR index`，然后查询重复 namespace
  `select name from decl_info where name like 'Rel.Rel.Rel.%' or name like 'Rel.LeetQ.%' or name like 'Rel.QLean.%'`
  必须什么也不返回。
- `B <targets>` = `CAP_MEM_MB=20000 /home/dh/repo/freyd/scripts/cap lake build <targets>`，输出写到
  `/data/tmp/<step>.log`，读它的末尾。worktree 只 build 它编辑过的 module。
- Phase gate（phase 合并之前在 main 上运行一次）：`make check`（build、compile-diff、crate-test、syms、
  native、ldd、index-complete、axioms、noreduce、panic、externs），然后
  `lake -d /home/dh/repo/freyd/relaop build RelAop -R -K rel=/home/dh/repo/rel`。
- 每一步都禁止：`sorry`、`native_decide`、`!` 下标、提高 `maxHeartbeats`、新的 `panic!`、
  pointwise（`∃`）的 definition body、`Rel/Core/` 内的 `Classical`、`Rel`/`Column`/`FinRel` 的第二份拷贝。
- Model 标签：**opus** = 这一步含 Lean 证明或需要设计的算法；**sonnet** = 敲字、rename、删除、build。
  build 因为某个证明失败的 sonnet 步骤停下并报告；它不去证明。
- 生成的代码：`Rel/Programs/*` 和 `Rel/Lang/Test*` 中的每个 `rel_program` 常量都由
  `Expand.node`（`Rel/Run/Lang/Expand.lean` 676-746）经 `mkConst ``Gen.…` 发出。rename 或删除某个
  `Gen.*` 常量的步骤，在同一步里编辑 `Expand.node` 的对应行，并重新 build `Rel.Programs.Prelude`。

## 1. Diff table

Size：S = 一步，少于 20 次 tool call；M = 一到三步；L = 多于三步或一场证明战役。

| #  | 设计项                         | 现有代码（module : 行）               | 差距                                    | Size |
|----|--------------------------------|---------------------------------------|-----------------------------------------|------|
| 1  | `Rel` = `tab` 或 `lazy`        | `Rel.Rel`, `Run/Core.lean:485`        | 没有 `lazy`、`Known`；2420 个依赖者     | L    |
| 2  | `Known = {dom, ran}`           | `Gen.Dem`, `Gen.lean:25`, 只有 dom    | `ran` 一侧没有对应物                    | M    |
| 3  | CRel 删除，ok → Option         | `CRel`, `Run/CRelDef.lean:8`          | 2297 个 decl；`.rel` 在 ok=false 时被读 | L    |
| 4  | `Fn`、`Dem` 删除               | `Gen.lean:48`, `:25`; `Pl` `:51`      | 7 个 module 中 224 + 182 个 decl        | L    |
| 5  | `Den` 被 inline                | `abbrev Den`, `Lang/Den.lean:20`      | 274 个 decl；`LR` 没有 inline 命令      | M    |
| 6  | `Tm` 没有 `Bool` 下标          | `Tm`, `Run/Lang/Tm.lean:15`           | `Res`、Elab、Expand、Bits、Plan         | L    |
| 7  | `compile` 返回 subtype         | `compile`, `Compile.lean:235`         | 先关闭所有 gap；R2                      | L    |
| 8  | Syn、Le、Eqv、Hom.den 消失     | `Lang/Syn.lean`, 347 行               | 在 rel 中是叶子；freyd import 它        | S    |
| 9  | `Tm.Ax` 写成等式               | `Syn.lean:21-42`, `:131-148`          | 12 个 constructor，12 条等式            | S    |
| 10 | refold 改名 hylo               | `Tm.lean:91`, `Gen.lean:267`          | 120 个名字含 "refold"                   | S    |
| 11 | foldI 成为 definition          | `Tm.lean:68`, `Den.lean:98`           | 只有在第 6 项之后才通过 typecheck；R3   | M    |
| 12 | flat 成为 definition           | `Tm.lean:72`, `Den.lean:103`          | 同上；`flat_sound` 消失                 | M    |
| 13 | inl、inr constructor           | prim 第 3、4 行, `Syntax.lean:150`    | 行已存在，constructor 不存在；R9        | S    |
| 14 | junc 是 definition，没有 juncD | `Tm.lean:35`, `:38`; `Gen.lean:247`   | `Core.Rel.junc` 已经是并集              | M    |
| 15 | 对称除法 ctor                  | `Alg.symDiv`, `Run/Alg.lean:293`      | 没有 `Tm` ctor，没有 `Den`              | M    |
| 16 | 拒绝非正的 μ/ν                 | `Tm.pol`, `Tm.lean:254`               | Elab `.fix`（1655-1670）：没有检查      | S    |
| 17 | gap：open share                | `Rows.lean:125`, `Expand.lean:530`    | 没有找到 producer；R6                   | M    |
| 18 | gap：setify、asc               | `rowGaps`, `Rows.lean:107`            | row 的 soundness；浮点序；R7            | M    |
| 19 | gap：hylo                      | `rep_refold`, `RefoldSpec.lean:124`   | `den_local` 不存在                      | M    |
| 20 | gap：lam、E、thin              | `lamDen` `Den.lean:111`; `Canon`      | 缺三条 soundness 引理                   | L    |
| 21 | gap：call                      | `Tm.lean:79`; den `𝟘`, `none'`        | stage 5 在代码里没有说明                | L    |
| 22 | prim row 写成 fold/hylo        | 28 行, `Compile.lean:77-112`          | 没有逐行检查                            | M    |
| 23 | scan、scatter primitive        | driver, `Kernel/Driver.lean:25-38`    | `Op`、`Op.eval`、两条定律               | L    |
| 24 | gather、asc、distinct          | `gatherPacked`, `Order.grade`, `nubC` | extern、定律、"= 复合"                  | L    |
| 25 | 一种编码 `packed`              | `Ext.Enc`, 7 个 ctor, `Value.lean`    | 460 个 decl 依赖 `Enc`                  | L    |
| 26 | 九个 atom                      | `QAtomicType`, 18 个 ctor, `Value:13` | 1718 个 decl；boolean、general；R5      | L    |
| 27 | RELK.txt 99 → 5                | `crate/RELK.txt`, `crate/src/ffi/`    | native gate 需要更多；R4                | L    |
| 28 | q-only kernel 离开             | 99 个 extern（`extern.tsv`）          | qlean 固定在 e024297：无工作            | S    |

## 2. Phases

顺序：P0 → P1 → P2 → P3 → P4 → P5 → P7，P6（kernels）在 Lean 层面独立于 P2-P5，
只有浮点序例外（5.2 等待 6.9）。P1 和 P2 的各步可以与 P6 同时运行。

### P0 Baseline（1 步）

**0.1 sonnet.** `make -C /home/dh/repo/rel index`，然后 `make -C /home/dh/repo/rel check > /data/tmp/p0.log 2>&1`。
从 log 中取出 compile-diff 那一行（"compile agrees … on N definitions; not ok on …"），连同
`git -C /home/dh/repo/rel rev-parse HEAD` 记入本文件末尾的 "Baseline" 一节。
Done：exit 0 且文件存在。
之后每个 phase gate 都拿自己的 compile-diff 行与这一行比较。

### P1 Syn 移除（3 步；先 1.1 后 1.2；1.3 与 1.2 在同一次合并）

**1.1 sonnet — `Tm.Ax` 写成等式。** 文件 `Rel/Lang/Den.lean`，追加在 `den_anti`（585-592 行）之后。
对 `Tm.Ax` 的 12 个 constructor（`Rel/Lang/Syn.lean` 21-42：`id_comp comp_id assoc conv_conv conv_comp
meet_join comp_join join_comp comp_zero zero_comp mu_unfold nu_unfold`）各加一条 theorem

```
theorem Tm.den_<ctor> <the constructor's binders, copied> (ρ : Val) : (<lhs>).den ρ = (<rhs>).den ρ := <term>
```

其中 `<lhs>`、`<rhs>` 是 constructor 结果类型 `Tm.Ax lhs rhs` 的两个下标，constructor 的每个假设
成为 theorem 的假设，`<term>` 是 `Tm.Ax.sound`（`Syn.lean` 131-148）中对应 case 的右端（它们用
`Core.Rel.id_comp comp_id comp_assoc recip_recip recip_comp inter_union comp_union union_comp
comp_zero zero_comp mu_fix nu_fix`、`Tm.den_subst`、`Tm.den_mono`）。Build
`B Rel.Lang.Den`。Done：12 条新 theorem，build 通过。如果某个拷贝来的 term 不通过检查，停下并报告（opus）。

**1.2 sonnet — 删除 `Rel/Lang/Syn.lean`。** 删除之前，先 `LR uses Rel.Lang.foldDen_le` 和
`LR uses Rel.Lang.foldIDen_le`：预期使用者只在 `Rel.Lang.Syn` 中；如果别的 module 用了其中一个，
先 `LR move-decl Rel.Lang.Den <name> --apply`。`rfl` 引理 `Tm.den_comp … Tm.den_own`（315-328）、
`den_mu`、`den_nu`、`den_refold`（333-341）在 index 中没有使用者，随文件一起删除。然后
`git rm Rel/Lang/Syn.lean`；没有 rel module import 它。Build `B Rel`。Done：`LR index` 之后
`select count(*) from decl_info where
module='Rel.Lang.Syn'` 为 0。

**1.3 sonnet — freyd 一侧。** 只有 `/home/dh/repo/freyd/relaop/RelAop/Syn.lean`（39 行：`instance : Cat Syn`、
`def den : Functor Syn RelSet`、`den_outl`、`den_outr`）import `Rel.Lang.Syn`；没有 relaop 文件 import
`RelAop.Syn`。方案 A（默认）：`git -C /home/dh/repo/freyd rm relaop/RelAop/Syn.lean`。方案 B（如果
owner 对 Q1 回答 "保留 functor"）：在 1.2 之前，把 `Rel/Lang/Syn.lean` 的 44-303 行（`Tm.Le` … 
`Syn.assoc`）拷到 `RelAop/Syn.lean` 顶部，把其中的 `import Rel.Lang.Syn` 换成 `import Rel.Lang.Den`，
跳过 `Tm.Ax` 的各 case（把 `Tm.Le.ax` 的使用换成 1.1 的等式：opus）。Done：第 0 节的 relaop gate。

### P2 不依赖 `Rel` 类型的工作（6 步；除 2.2 先于 2.3 之外，全部在 worktree 中并行）

**2.1 sonnet — refold → hylo。** 名字列表：运行
`select name from decl_info where internal=0 and lower(name) like '%refold%' and module not like 'Rel.Programs.%'
and module not like 'Rel.Lang.Test%' and name not like 'Rel.Lang.Pre.%' and name not like 'Rel.Lang.Expr.%'`。
对每个名字 N 传入一对 `N N'`，N' 把 `refold` 换成 `hylo`、`Refold` 换成 `Hylo`（必须包含
`Rel.Lang.Tm.refold`、`Rel.Lang.Gen.refold`、`Rel.Lang.Gen.refoldRounds`、`Gen.rep_refold`、`refoldRounds_ok`、
`Rel/RefoldSpec.lean` 的 `Refold.*` 名字）：`LR rename N N' … --apply`；然后改 module：
`LR rename Rel.RefoldSpec Rel.HyloSpec --apply`。表层 constructor `Pre.refold`（Elab 160、304、915、1636）
保留原名（Q2）。手工检查 rename 工具可能漏掉的三处：`Expand.lean:735`
（`mkConst ``Gen.refold`）、`Rows.lean:114`（gap 字符串）、`Elab.lean:1640`。Build `B RelRun Rel`。Done：上面的
查询只返回生成 module 中的名字；build 通过。

**2.2 opus — `flatDen` 是一个复合。** 文件 `Rel/Lang/Den.lean`，在 `flatDen`（103 行）之后。加入

```
theorem flatDen_eq (T : Den I (.prod A B)) :
    flatDen T = ((graph Prod.fst ≫ T) ∩ (graph Prod.snd ≫ (graph Prod.fst)°)) ≫ graph Prod.snd
```

三个投影的写法要与 `Tm.den` 的 `.outl`、`.outr` 两个 case 的右端（`Den.lean` 191-234）完全一致，
这样 4.2 步用它改写之后可以由 `rfl` 关闭。按点读：`(i,a)` 到
`(a',b)`，条件是 `T i (a',b)` 且 `a' = a`，再到 `b`。Build `B Rel.Lang.Den`。

**2.3 opus — `foldIDen` 是一个 `foldDen`。** 同一文件，在 `foldIDen`（98 行）之后。加入

```
theorem foldIDen_eq (Te : Den I (.prod V V)) (TS : Den (.prod E (.prod I V)) (.prod I V)) :
    foldIDen Te TS =
      ((π₁ ≫ π₁°) ∩ (π₂ ≫ foldDen (ranD ⟨𝟙, Te ≫ π₂⟩) (TS ∩ (π₂ ≫ π₁ ≫ π₁°)))) ≫ π₂
```

其中 `π₁`、`π₂`、`ranD`、`⟨_,_⟩`、`𝟙` 是 `Tm.den` 分别赋给 `.outl`、`.outr`、`.ran`、
`.pair`、`.id` 的 Core 算子。carrier 是 `I × V`；meet `TS ∩ (π₂ ≫ π₁ ≫ π₁°)` 让下标保持不变，
`foldIDen` 的做法是在 `TS` 两侧都写 `p.1`。没有这个 meet，等式就是假的。沿用
`foldDen_le` 风格对 `foldDen`（`Den.lean:89`）展开。Build `B Rel.Lang.Den`。

**2.4 sonnet — elaboration 时的 positivity 错误。** 文件 `Rel/Run/Lang/Elab.lean`，`.fix` case，1655-1670 行。
在 `let body ← closed? …` 这一行之后插入一个检查：以 μ 和 ν 两个 case 在 `Tm.gap`（`Rel/Lang/Rows.lean` 116-119）
中传入的完全相同的参数调用 `Tm.pol`（`Rel/Run/Lang/Tm.lean:254`），失败时
`throw ⟨p, s!"{if least then "μ" else "ν"} at {p}: its body does not use {k} positively"⟩`。不要动
`Tm.gap`（见 R2）。Build `B RelRun Rel`。Done：build 通过（树里今天没有任何程序是非正的：
compile-diff 行等于 baseline）；在 `Rel/Lang/Test.lean` 中为这个新错误加一个 `#guard_msgs` 测试。

**2.5 opus — 对称除法的含义。** 文件 `Rel/Lang/Den.lean`，在 `rdivDen`（49-70 行）之后。加入
`def symDivDen (UA : Den A A) (UB : Den B B) (R : Den A C) (S : Den B C) : Den A B`，point-free，由
`ldivDen`/`rdivDen` 和 converse 构造，宇宙的取法与那两个相同；在 `Rel/CRelRel.lean` 中 `rep_symDiv`（306 行）
之后加一条 theorem：`rep_symDiv` 的右端
（`(∀ c, R x c ↔ S y c) ∧ ((∃ c, R x c) ∨ (x ∈ Ua ∧ y ∈ Ub))`）就是 `symDivDen (corefl Ua) (corefl Ub) R S x y`。
Build `B Rel.Lang.Den Rel.CRelRel`。

**2.6 opus（分析，不编辑）— prim row 写成 fold/hylo。** 对 `Compile.lean` 77-112 的 28 行中的每一行
（`tau cons mem inl inr map filter takewhile thinL merge loop uncons length sum inits tails prefix suffix concat
cat uncat zip snoc unsnoc setify distinct asc tic`），在 `doc/rel-rows.md` 中写一行：它等于的 `Tm`
（只使用目标 `Tm` 的 constructor），或者 "primitive" 加上理由。`Syntax.lean` 150-192 已经用 `prelude :=` 定义
标出了 `filter takewhile tails prefix suffix concat`。输出供 Q5 使用；不改代码。
Done（`doc/rel-rows.md`）。Owner 的决定：array 只由 `snoc` 构造，绝不由 `cons` 构造（追加使用
array 的剩余容量），所以默认的 `fold` 消去 `[nil, snoc]`（4.5 步），`cons`、`uncons` 是只用于读取的
definition（`cons° = uncons`）；在含义允许的地方 array 从左向右读，所以右 fold 只留给 `sum` 和 `thinL`，
它们的含义是从右到左（保留）；Q5 答 L（每个有 slice 代码的 row 仍是融合 kernel，它的 definition 是
规约，`⟦row⟧ = ⟦def⟧`）。

### P3 `Rel` 类型（13 步；在一个分支 `rel-lazy` 上串行，标注处除外）

分阶段规则：名字保留，先改类型，最后才去掉下标。phase gate 在分支上通过之前，不动 master。

**3.1 sonnet — 结构 `Rel.Rel` 变成 `Rel.Tab`。** 从 index 取配对：
`select name || ' Rel.Tab' || substr(name, 8) from decl_info where internal=0 and (name='Rel.Rel' or name like
'Rel.Rel.%')`（结构、字段 `n key val`、`mk`、`Holds`、`toList`、`Canon`、…）。`LR rename <pairs> --apply`。
Build `B RelCore RelKernel RelRun Rel`。Done：不再有名为 `Rel.Rel` 或 `Rel.Rel.*` 的 declaration。（Q3：设计也把
带三个字段的结构叫 `Tab`，因为 2128 个 declaration 投影 `.n .key .val`。）

**3.2 opus — `CRel` 是 `Option (Tab A B)`。** 文件 `Rel/Run/CRelDef.lean` 8-64 行。把结构替换为

```
abbrev CRel (k v : Obj) := Option (Tab k v)
def CRel.ok (c : CRel k v) : Bool := c.isSome            -- temporary, removed in 3.12
def CRel.rel (c : CRel k v) : Tab k v := c.getD default   -- temporary, removed in 3.12
def CRel.mk (r : Tab k v) (ok : Bool) : CRel k v := if ok then some r else none   -- temporary
```

删除 `instance : Inhabited (CRel A B)`（46 行；`Option` 已有一个，值为 `none`），经 `CRel.mk` 重述 `CRel.guard`（50）、
`comp`（53）、`inter`（57）、`union`（60）、`CRel.ofC`（43）。然后按 import 顺序逐个 module 修复使用 `CRel.mk` 的
16 个 module（92 个 declaration）以及每处 `{ c with … }`/匿名构造子的使用：
`select use_module, group_concat(l1+1) from use_site where name='Rel.CRel.mk' group by 1`。形如
`(X).ok = true → … (X).rel …` 的语句保持原文。超出预算时按 library 拆分：3.2a `RelRun`
（`Run/CRel*Def.lean`、`Gen.lean`、`Expand.lean`），3.2b `Rel/CRel*.lean`，3.2c `Rel/Lang/*`。Build
`B RelRun Rel`。Done：build 通过；compile-diff 行；列出每一个期望值改变了的 `#guard`（R1）。

**3.3 opus — `Known`、`Rel`、`Reps`。** 新文件 `Rel/Run/Lang/Lazy.lean`（import `Rel.Run.CRelDef`），把它加到
`Rel/Run/Lang/Gen.lean` 的 import：

```
structure Known (A B : Obj) where
  dom : Option ((n : USize) × Vals A n) := none
  ran : Option ((n : USize) × Vals B n) := none
inductive Rel (A B : Obj) where
  | tab (t : Option (Tab A B))
  | lazy (f : Known A B → Rel A B)
def Rel.run : Rel A B → Known A B → Option (Tab A B)      -- tab t ↦ t;  lazy f ↦ (f K).run K
```

并在 `Rel/Rep.lean` 中 `Rep.rep`（17 行）之后：

```
def Known.den (K : Known A B) : Core.Rel A.El A.El × Core.Rel B.El B.El     -- none ↦ 𝟙, some c ↦ corefl (∈ c)
def Rel.Reps : Rel A B → Core.Rel A.El B.El → Prop
  | .tab none, _ => True
  | .tab (some t), R => Rep.rep t = R
  | .lazy f, R => ∀ K, (f K).Reps (K.den.1 ≫ R ≫ K.den.2)
```

这是把设计中的 `rep (lazy f) = R ⇔ ∀ K L, rep (f ⟨K,L⟩) = K ≫ R ≫ L` 读成谓词；R1
说明了它为什么不是函数。只有当后面某一步引用时，才去证 `Reps.tab_some`、`Reps.lazy_iff`。Build
`B Rel.Run.Lang.Lazy Rel.Rep`。

**3.4 opus — 与旧函数类型之间的桥。** 文件 `Rel/Lang/GenSpec.lean`，在 `Gen.Sound`（37 行）之后：

```
def Gen.Fn.toRel : {d : Bool} → Gen.Fn d A B → Rel A B     -- false: tab (f ()); true: lazy fun K => dom-keyed call
theorem Gen.Sound.reps {f : Gen.Fn d A B} {T} (h : Gen.Sound f T) : (Gen.Fn.toRel f).Reps T
```

（`toRel` 本身放在 `Gen.lean` 的 48 行之后。）当 `d = true` 且 `K.dom = none` 时，结果是 `tab none`。
复用 `keys`、`Cor`（`GenSpec.lean` 26、31）、`Sound.eq`（41）。这一步证明 3.3 的谓词由今天的
soundness 蕴含；如果证不出来，就停下：3.3 的定义是错的，Q4 仍然悬而未决。
Build `B Rel.Lang.GenSpec`。

**3.5 opus — `Gen.Fn d A B := Rel A B`（phantom `d`），叶子。** `Rel/Run/Lang/Gen.lean`：把 48 行改为
`abbrev Gen.Fn (_d : Bool) (A B : Obj) := Rel A B`；重写叶子（66-89 行），让 `d = false` 的叶子
返回 `.tab …`，`d = true` 的叶子返回 `.lazy fun K => …`，在原来读 `Dem` 的地方读 `K.dom`（`leq`、`lt`、
`top` 还读 `K.ran`：`tab (K ≫ leq ≫ L)`、`K × L`）。`Dem`（25 行）保留到 3.12，供 plan 路径使用。
把 `Gen.Sound`（`GenSpec.lean:37`）重述为 `def Gen.Sound (f : Rel A B) (T) : Prop := f.Reps T`，并重证
叶子引理 `const_sound … mem_sound`（`GenSpec.lean` 89-145）。Build `B Rel.Run.Lang.Gen`；145 行以下的 `GenSpec`
在 3.7 之前可以是红的。

**3.6 opus — 二元和一元组合子。** `Gen.lean` 93-190（`comp conv meet join diff dom ran pair prod junc
ldiv rdiv` 以及 `…B` 位矩阵形式）：每个都变成按 `tab`/`lazy` 分 case 的 `Rel` 上的函数。规则：
旧代码在 `d = false` 时运行的 body 是 `tab, tab` 的 case；它在 `d = true` 时运行的 body 放在
`.lazy fun K =>` 之下，其中 `Dem.of`/`Dem.l`/`Dem.r`（29-40）换成 `K.dom`；`tab r ≫ lazy g`
调用 `g ⟨some r.val-column, K.ran⟩`。`comp` 不得读取 `none` 的 `r.n`（109 行今天就在读）。引理
`comp_sound`（348）… `rdiv_sound`（555）、`compB_sound … ldivB_sound`（649-661）。Build `B Rel.Run.Lang.Gen`。

**3.7 opus — fold 和不动点。** `Gen.lean` 191-270（`fold foldI flat nu nuAC mu onNodes juncD
refoldRounds refold`）以及 `GenSpec.lean` 495-548、`CompileSpec.lean` 29-125（`mu_sound nu_sound flat_sound
onNodes_sound juncD_sound`）、`Rel/HyloSpec.lean`。`mu` 在触到上限时返回 `tab none`（今天：带 `ok = false`
的被截断的链）。Build `B RelRun Rel.Lang.GenSpec Rel.Lang.CompileSpec`。

**3.8 opus — `Compile`、`Expand`、测试迁到新的 `Fn`。** `Rel/Run/Lang/Compile.lean`：`CodeEnv`（13）、`bind`
（17）、`Out`（155）、`Out.memo`（162）、`Tm.gen`（169-232）去掉 `()`/`Dem` 的应用。`Expand.lean`：
`printText`（100）和 `checkErr`（104）接受 `Rel A B` 并读取 `Rel.run r {}`；`share`（621）、`body`（670）、
`node`（676-746）在原来发出 `CRel A B` 的地方发出 `Rel A B`。`Rel/Lang/Test.lean` 的 `get`、`test/TestCompile.lean`
的 `differs` 比较 `Option (Tab A B)`。`Rel/Lang/CompileSpec.lean` 212-355 改为在 `Reps` 上重述；
`Rel/Lang/RelRep.lean` 的 `prf pprf prfNode`（31-67）随之改动。Build `B RelCore RelKernel RelRun Rel TestCompile`。
Done：phase 式检查 `make check`；compile-diff 行等于 baseline，R1 能解释的条目除外。

**3.9 sonnet — 从 `Tm` 去掉下标。** `Rel/Run/Lang/Tm.lean`：15 行变为
`inductive Tm : Obj → Obj → Type`；从每个 constructor（15-91）、`Res`（94：
`(A) × (B) × Tm A B`）、`Tm.mapM parts fv Sub lift Sub.get fresh subst pol`（100-278）中删去 `Bool` 下标；`Tm.call` 失去
第一个参数 `d`，`cv : Option (Lean.Name × Bool)` 变成 `Option Lean.Name`。然后 `Gen.Fn` 失去它的参数：
`LR remove-arg Rel.Lang.Gen.Fn 0 --apply`（在预览中核对参数下标）。按 constructor 列出的使用者在
第 4 节的 anchor 列表里。Build `B Rel.Run.Lang.Tm Rel.Run.Lang.Bits Rel.Run.Lang.Plan Rel.Run.Lang.Gen
Rel.Run.Lang.Compile`。

**3.10 opus — 没有 demand bit 的 Elab。** `Rel/Run/Lang/Elab.lean`：`swapTm pairTest Proj Proj.pre Proj.meet
convTm convProj onPairs divTest`（1247-1385）、`at?`（1401）、`closed?`（1405，变成 `at?`）、`uniPart uniTm numU`
（1412-1433）、`corAt`（1489）、`closeRes`（1493：今天它在 `d = true` 时给宇宙加前缀；没有 `d` 之后，
前缀加在 `Tm.fv`/形状要求的地方 — Q6）、`build`（1507-1670）、`callArgs`（1675）。Build `B RelRun`。

**3.11 opus — 没有 demand bit 的 Expand。** `Expand.lean`：`closed`（526，`!d && t.fv.isEmpty`）、`number`
（530-534）、`free`（538）、`varComp`（541）、`arcs`（548）、`code`（607-618）、`plan?`（629）、`planOr`（657）、`spine`
（663）、`node`。位矩阵路径（`Bits.runC`，`Bits.lean:249`）原来在 `d = false` 时被选中；改为在
`Gen.comp`/`meet`/`diff`/`ldiv` 内部当 "两个操作数都是 `tab`" 时选中（3.6 已经有这个 case 拆分），
并且如果 `compB meetB diffB ldivB` 已经没有调用者，就把它们作为独立名字删除。Build `B RelCore RelKernel RelRun Rel
TestCompile`。

**3.12 sonnet — 删除临时物。** `LR unused` 必须列出 `Gen.Dem`、`Dem.of`、`Dem.l`、`Dem.r`、
`Gen.Fn.toRel`、`Gen.Sound.reps`、`CRel.mk`；对每个 `LR remove <each> --apply`。对 `CRel.ok`、`CRel.rel`（454 + 479
个 declaration，大多是生成的）：逐个 module 把手写语句 `(X).ok = true → P (X).rel` 重写为
`∀ r, X = some r → P r`（如果某个证明破了，用 opus）；然后 `LR remove`。`LR fold-abbrev` 不是
`CRel` 所需要的逆操作：读完它的 `--help` 之后，用 `LR retype Rel.CRel …` 把 `CRel A B` 换成 `Option (Tab A B)`
（确切形式以手册为准）。Build 全部四个 library。

**3.13 sonnet — inline `Den`。** `Den A B`（`Den.lean:20`）被 `Den GenSpec Rows
ConvSpec CompileSpec BitsSpecRun BitsSpec` 中的 274 个 declaration 使用。`LR` 没有 "unfold abbrev" 命令（Q7）。
在它出现之前：这一步被阻塞；不要用 regex 去做。

### P4 `Tm` 的 constructor 变更（5 步；串行，它们共用同样的 match 分支）

对每个被移除的 constructor，在下列位置删除它的分支：`Tm.lean`（`mapM fv subst pol`）、`Den.lean`（`den`、`den_congr`、
`den_subst`、`den_pol`）、`Rows.lean`（`gap`）、`Compile.lean`（`gen`）、`CompileSpec.lean`、`ConvSpec.lean`、
`BitsSpec.lean`、`BitsSpecRun.lean`、`Elab.lean`（`convTm`、`build`）、`Expand.lean`（`node`）。Anchor：第 4 节。

**4.1 opus — `inl`、`inr` constructor；`junc` 成为 definition；`juncD` 删除。** `Tm.lean`：加入
`| inl : Tm A (.sum A B)` 和 `| inr : Tm B (.sum A B)`；把 constructor `junc`（35）替换为

```
def Tm.junc (R : Tm A C) (S : Tm B C) : Tm (.sum A B) C := .join (.comp (.conv .inl) R) (.comp (.conv .inr) S)
```

删除 `juncD`（38）。`.inl`/`.inr` 的 `den` 是 `Core.Rel.inl`/`Core.Rel.inr`，所以 `(Tm.junc R S).den ρ =
Core.Rel.junc (R.den ρ) (S.den ρ)` 由 `rfl`（`Core/Rel.lean:70`）成立。`.inl`/`.inr` 的 `gen` 是提升后的
`CRel.inl`/`CRel.inr`；soundness 来自 `inl_sound`（120）、`inr_sound`（125）。删除 prim 第 3、4 行（`inlRow`、`inrRow`，
`Syntax.lean` 150-151；`Compile.lean` 的行；`Rows.lean` 的行），使只剩一份 definition（R9）。删除 `Gen.junc`、
`Gen.juncD`（247）、`junc_sound`（438）、`juncD_sound`（`CompileSpec:125`）、`Expand.node` 的 701、737 行；Elab 1292、
1422、1578-1587 构造 `Tm.junc`。Build 全部四个 library + `TestCompile`。Done：`Quicksort`、`TestRefold`、`Test`
（`Gen.juncD` 的使用者）的 `#guard` 结果不变；报告 `Rel.Programs.Quicksort` 的计时（R3）。

**4.2 opus — `flat` 成为 definition。** 把 constructor `flat`（`Tm.lean:72`）替换为
`def Tm.flat (R : Tm I (.prod A B)) : Tm (.prod I A) B := .comp (.meet (.comp .outl R) (.comp .outr (.conv .outl)))
.outr`；由 2.2，`den` 等于 `flatDen`。删除 `Gen.flat`（209-212）、`flat_sound`（`CompileSpec:75`）、
`Expand.node:717`。生成代码中 `Gen.flat` 的使用者：`Test` 20、`Chess` 9、`TestWumpus` 7、`Blocks` 3、
`Edit` 2、`Wumpus`、`Knapsack`、`ModuleTest`。Done 同 4.1，报告 `Rel.Programs.Chess` 的计时。

**4.3 opus — `foldI` 成为 definition。** 把 constructor `foldI`（`Tm.lean:68`）替换为 `den` 等于
`foldIDen_eq`（2.3）右端的那个 `Tm`。删除 `Gen.foldI`（196-206）、`foldIDen_le`、`foldI` 的 gap 分支
（`Rows.lean:121`）、`Expand.node:715`。使用者：`Edit`、`Knapsack`、`Test`、`TestKnapsack`、`TestEdit`。gap
"foldI: no foldI_sound" 随分支一起消失。Done 同 4.1。

**4.4 opus — `symDiv` constructor。** `Tm.lean` 在 `rdiv` 之后：`| symDiv (UA : Tm A A) (UB : Tm B B) (R : Tm A C)
(S : Tm B C) : Tm A B`（仿照 `ldiv` 的宇宙参数；Q8）。`den := symDivDen`（2.5）；`gen` 经由
`CRel.symDiv`（`Run/CRelRelDef.lean:52`）；soundness 来自 `CRel.rep_symDiv`（`CRelRel.lean:306`）和 2.5。给
P4 开头列出的每个函数加上分支。`Grammar`/`Elab` 中的表层语法是另一个决定（Q8）。

**4.5 opus — 以 `[nil, snoc]` 上的左 fold 为默认；只用 `snoc` 构造。** 今天 `fold` 只是 `[nil, cons]` 上的
右 fold：`foldDen`（`Den.lean:107-113`）设 `ys[n]` 为种子，令 `ys[t] = S(xs[t], ys[t+1])` 并返回
`ys[0]`；kernel 的第 `k` 轮从末尾读第 `k` 个元素（`Alg.foldRound`，`Run/Alg.lean:686-700`）。规则
（`doc/rel-rows.md` 开头）：在含义允许的地方从左向右读，只有含义需要时才从右向左；
array 只通过追加来构造。没有 row 的含义改变，所以没有 `rowDens` 条目，也没有 `#guard` 结果改变。
- 加入左 fold，步 `S : V×E ⟶ V` 读 `(acc, x)`，先读下标 0（`scan` 运行的顺序），作为 `Tm.fold`；
  今天的 constructor 保留为 `Tm.foldr`，含义不变。含义：`foldDen` 变成 `foldrDen`，旁边加一个左
  `foldDen`（种子 `ys[0]`，`ys[t+1] = S(ys[t], xs[t])`，结果 `ys[n]`）；`foldIDen`、`foldIDen_eq`
  （115-157）移到左 fold（meet 变成 `π₁ ≫ π₁ ≫ π₁°`）；`fold_le`、`foldI_le`（550-558）两种都要；
  两个 constructor 的分支都加到 P4 开头列出的每个函数里。
- 代码：`foldRound` 接受读取顺序（第 `k` 个元素从开头数，或像今天那样从末尾数）；
  `demandStepC`（733-736）对左 fold 配对 `(pend, el)`，对右 fold 配对 `(el, pend)`；`foldOnC`（743-748）、
  `CRel.foldOn`（`Run/CRelFoldDef.lean:16`）、`Gen.fold`（`Gen.lean:191-192`）旁边加 `Gen.foldr`、
  `Gen.foldI`（如果 4.3 还没有移除它）、`Expand.node:713`。
- 右 fold 只保留在含义是从右到左的地方：`Arr.sumC`（`Alg.lean:1546`；`sum` 的附带条件
  约束后缀和）和 `thinLOnC` 的第一遍（1393；`thinLDen` 是从末尾开始的链）。其余每个
  `foldOnC` 调用者都移到左 fold。
- 前置 → 追加：每条由 `consC`（`Alg.lean:656`）构造的输出路径改为由 `snocC` 构造：`thinBodyC`（1377）
  变成 `doc/rel-rows.md` 的两遍 `thinA`/`thinK`（动作从右向左追加，然后保留的
  元素从左向右追加；`thinLDen`、`rep_thinLOnC`（`CRelFold.lean:469`）及它们的 `#guard` 保持原来的
  语句）、`mapFoldC`（771）、`alphaC`（896）、`permC`（1242）、`subseqC`（1347）、`ticC`（1531）。`consC` 和
  `CRel.cons`（`Run/CRelListDef.lean:44`）只作为 `cons` 行的代码保留，直到 2.6 删除该行；
  `mergeRound`（1408）已经是追加。
- 引理：`rep_foldOnC`（`CRelFold.lean:133-181`）、`CRel.rep_foldOn`（533-557）、`foldRows_iter`、
  `foldRows_rep_keep`（`RepFold.lean:328-347`、`575-669`）、`Gen.fold_sound`（`GenSpec.lean:493-518`），各对两种
  读取顺序都成立；以及上述 kernel 的 `rep_*C` 引理。
- 程序：每个左 fold 的步翻转它的 pair，原来 cons 的步改为 snoc，使输出保持
  原来的顺序；每个 prelude definition 取 `doc/rel-rows.md` §2 中的形式：`prefix`、`subseq`、`tails`、
  `filter`、`takewhile`、`perm`（它的 `add`）、`sort`（`Rel/Programs/Prelude.lean`）；生成代码
  调用 `Gen.fold` 的程序（`Selsort Mss Detab Blocks Edit Party Knapsack Quicksort`）以及测试（`Test TestHylo
  TestSelsort TestKnapsack TestEdit TestMss`）。含义为从右到左的 fold 变成 `foldr`。

Build 全部四个 library + `TestCompile`。Done：compile-diff 不变（241 / 25），每个 `#guard` 结果不变。

### P5 按既定顺序关闭 gap（8 步；5.4a-c 并行，其余串行）

**5.1 opus — share。** `Tm.gap` 分支 `Rows.lean:125`、`compile_sound` 分支 `CompileSpec.lean:305`、den
`Den.lean:225`（`R.den Val.empty`）、`Expand.number` 530-534（只包裹 `closed` 的子 term）、`convTm` 的 share 分支
`Elab.lean:1325`、`convProj` `:1361`。先通过对 `relRegistry` 做 `#eval`（如 `test/TestCompile.lean` 所做）
找出哪些已注册的 term 含有 `R.fv ≠ []` 的 `.share k R`；报告该列表。然后修 producer，使它不再
发出这种 term。gap 分支作为 well-formedness 条件保留（R2）。

**5.2 opus — setify、asc 行。** `Rows.lean`：在下标 24（`setify`）和 26（`asc`）加 `Row` 条目，分别来自
`CRel.rep_setify`（`CRelPower.lean:283`）和 `CRel.rep_asc`（`CRelArith.lean:221`，一个方向，假设
`B.Ordered`）；`rep_asc` 的逆方向需要 `Obj.KeyInj`（`CRel.lean:124`），它今天在浮点 atom 上为假
（R7）。从 `rowGaps`（107）中删去这两个名字，并从 `Tm.gap` 中删去 `prim` 分支。如果浮点
key 改变，则等待 6.9。

**5.3 opus — hylo。** 在 `Rel/Lang/Den.lean` 中新增：
`theorem Tm.den_local (b : Tm A B) (k) (ch : Core.Rel …) (h : <b has the shape c ≫ G(X) ≫ S>) : (∀ y, ch x y →
X y = X' y) → b.den (ρ.bind k X) x = b.den (ρ.bind k X') x`，写法见 `doc/rel-denotation-design.md` §7.2；
然后在 `CompileSpec.lean` 中由 `Gen.rep_hylo`（`HyloSpec.lean:124`，假设 `Monotonic Φ` 来自
`Tm.den_mono`，`Local` 来自 `den_local`）
得到 `hylo_sound`。删除 `Tm.gap` 的 hylo 分支（`Rows.lean:114`）。Q9：hylo 的 `Tm.den`
忽略 `ch`；把 `ch` 与 body 联系起来的前提在设计中没有。

**5.4a / 5.4b / 5.4c opus — `lam_sound`、`E_sound`、`thin_sound`。** `GenSpec.lean`，各一条 theorem，分别针对
`lamDen`（`Den.lean:111`）、`EDen`、`thinDen`；复用 `Rel.Tab.Canon`、`canon_ofC`（`CRel.lean:310`）、`canon_comp`
（330）、`canon_inter`（335）、`canon_union`（341）、`canon_diff`（`CRelFold:627`）、`canon_antiJoin`（`CRelRel:329`）、
`Obj.lt_*`（`ObjOrder.lean` 41-49、145）。每条都需要元素 object 的 `Ordered` 和 `KeyInj` 作为假设；
它们在 `compile_sound` 中从哪里来是 Q10。然后是 `compile_sound` 和 `Tm.gap` 的三个分支。

**5.5 opus — call（stage 5）。** `Tm.call`（`Tm.lean:79`）、den `𝟘`（`Den.lean:229`）、`none'`（`Compile.lean:221`）、
Elab 1335、1652、1702，Expand 637、666、746。设计只给出了 stage 的名字，没有给出机制（Q11）；这一步
以一份书面提案开始，而不是代码。

**5.6 sonnet — 删除 `Tm.gap`。** 当 `Tm.gap` 的每个分支（`Rows.lean` 111-134）除 R2 的
well-formedness 分支外都返回 `none` 时：rename 剩下的部分（`LR rename Rel.Lang.Tm.gap Rel.Lang.Tm.illFormed --apply`），
删除 `rowGaps`、`gap_or`（`CompileSpec:233`）、`compile_sound` 的最后一行（355）。Build 全部 + `TestCompile`。
Done：compile-diff 报告 0 个 "not ok"。

### P6 Kernel（调研 + 12 步；同一个 kernel 的 Rust 和 Lean 两半串行，不同 kernel 并行）

**6.0 opus（分析，不编辑）— 替换表。** 对 `/data/tmp/rel-gates/rel/extern.tsv` 的 99 行中的每一行
（namespace：`Rel.Kernel` 51、`Ew` 17、`Order` 18、`Coc` 10、`Scan` 1、
`Column` 1、`Db` 1）：
给出 Lean 使用者（`use_site`），并归入以下之一：{`scan op`、`scatter`、`gather`、`asc`、`distinct`、
"q-only: delete"、"no target: R4"}。输出 `/data/tmp/rel-kernels.md`。6.8-6.11 步由这张表切分而来；
在它存在之前无法切分。Done：`doc/rel-kernels.md`（由 owner 缩小范围：class R = 从
Rel 的 runtime 或程序可达，77 个；class Q = 不可达，22 个；五个 kernel 的表只覆盖 R）。

**6.0a sonnet — 删除 class Q。** 删除 `doc/rel-kernels.md` §2 的 22 个 class-Q extern 及其 cone
（47 个 declaration，那里按 module 列出）、它点名的 `#guard`/`decide` 命令位置、`crate/RELK.txt` 的 22 行，
以及没有调用者的 Rust export 和文件（`crate/src/ffi/*`）。Rel 只需要 Rel 用到的东西；
qlean 保留自己的拷贝（`qlean-base`）。build 之后重新检查 `Verify.overStep_fold`（`KernelSpec.Group`）。
Gate：`B RelCore RelKernel RelRun Rel`、`RELK.txt` 为 77 行时的 `sh crate/build.sh syms`、
`make externs`、`make panic`。在 6.1 之前；碰到证明的 sonnet 步骤停下并报告。

**6.1 sonnet — `Op`。** 在 `RelKernel` 中新增 `Rel/Kernel/Op.lean`：
`inductive Rel.Kernel.Op | add | sub | mul | min | max | eq | lt | and | or | not | first | fadd | fmul | fdiv |
flt`（按设计 §4 补全列表）、`def Op.readsAcc : Op → Bool`、`def Op.assoc : Op → Bool`、
`def Op.eval : Op → UInt64 → UInt64 → UInt64`，作用在原始 word 上。名字 `Rel.Lang.Op`（`Syntax.lean`）已经
存在：kernel 的那个放在 `Rel.Kernel`。要映射的现有 op code：`Ew.add … Ew.acos`（`Elementwise.lean`
22-65）、`Scan.Verb`（`Scan.lean:11`）。

**6.2 opus — `packed`。** `Rel/Kernel/Value.lean`：给 `Ext.Enc` 加 constructor
`| packed (lg : UInt8) (bases widths payload : ByteArray)`，以及它在 `Ext.Enc.raw`（705 行）中的 case；`bits` 是
base 0 宽度 1，`enum` 宽度 `⌈log2 card⌉`，`const` 宽度 0。复用 `Coc.encodeAt`（`Coc.lean:85`）。其他六个
constructor 保留到 6.11。

**6.3 opus — `crate/src/pack.rs`。** `packed` 的块 encode/decode，基于 `pod::Elt`（`pod.rs:22`）、`by_width!`
（`ids.rs:12`）、`Producer::block_into`（`enc.rs:284`）、`pool`。在 `crate/` 中 `cargo test`。

**6.4 / 6.5 opus — `scan`、`scatter`（并行）。** Lean（`Rel/Kernel/Scan.lean`，新增 `Rel/Kernel/Scatter.lean`）：

```
@[extern "qlean_k_scan"]    def Kernel.kscan (op : Op) (seg : @& Enc) (es : @& List Enc) : Enc := <model on raw>
@[extern "qlean_k_scatter"] def Kernel.kscatter (ix e : @& Enc) (n : USize) (fill : UInt64) : Enc := <model>
theorem raw_scan …    theorem raw_scatter …       -- Rel/KernelSpec/, statements from §4 of the design
```

各带一对 `decide`-beside-`#guard`；Rust `crate/src/scan.rs`（已存在，扩展）、`scatter.rs`（新增）、
`ffi/scan.rs`、`ffi/structural.rs`；把这两个符号加进 `crate/RELK.txt`。临时用 `k` 名字，因为
`qlean_scan`（`Scan.scan`，`Scan.lean:179`）和 `Kernel.scan`（`Driver.lean:33`）已经存在；在 6.11 改名。
模型用 `Op.eval` 陈述，绝不用 Lean 闭包。下标 ≥ `n` 是错误，绝不丢弃（owner，
2026-11-18：不得静默出错）：模型返回 `Except`，Rust 把错误返回给 Lean，需要丢弃某一行的
复合把它送到一个多余的 cell，之后再把该 cell 截掉（WHERE，`doc/rel-kernels.md`）。
Gate：`B RelKernel`、`sh crate/build.sh syms`、
`make externs`。

**6.6 / 6.7 / 6.8 opus — `gather`、`asc`、`distinct`（并行，在 6.4 和 6.5 之后）。**

```
@[extern "qlean_k_gather"]   def Kernel.kgather (ix e : @& Enc) (fill : UInt64) : Enc
@[extern "qlean_k_asc"]      def Kernel.kasc (es : @& List Enc) : Enc × Enc          -- values, permutation
@[extern "qlean_k_distinct"] def Kernel.kdistinct (es : @& List Enc) : Enc
```

定律 `raw_permute`、`asc_sorted` + `asc_perm`、`distinct_first` + `distinct_cover`，以及各一条 "= `kscan` 与
`kscatter` 的复合" 的 theorem，取自设计的复合表（distinct = scan → scatter；asc =
radix scan → scatter，`arr` 字节用 MSD；gather = concat → asc → scan fill → scatter）。Lean 的 body 就是
这个复合；Rust 是融合形式。现有材料：`gatherPacked`（`Structural.lean:34`）、`scatterPacked`
（240）、`Order.grade`（`Sort.lean:69`）、`gradeLane`（96）、`runStarts`（`Search.lean:233`）、`Alg.nubC`（`Alg:202`）。

**6.9 opus — atom 和保序编码。** `QAtomicType`（`Value.lean:13`）用 `LR rename` 改名：
`boolean→u1 long→i64 int→i32 short→i16 byte→i8 real→f32 float→f64 symbol→sym`（`char` 保留原名）；
然后浮点 atom 处的 `Obj.key`（`ObjOrder.lean:19`）变成保序的位映射。移除 `general` 和时间类 atom：按 R5，`.sum` 的 tag
变成 `Arr .u1`；`Obj.general` 消失，`Obj.Ordered` 失去它的 `t ≠ .general` 前提。

**6.10 opus，多步 — 迁移使用者。** 按 6.0 的表每组一步：每个调用旧 extern 的 `Alg`/`Code`/`CRel*Def` definition
在这五个 kernel 上重述，它的 `KernelSpec`/`KernelWF` 引理由新定律重证。
`Rel/KernelSpec/*`（约 5700 行）和 `Rel/KernelWF/*`（约 16000 行）
是针对今天的 kernel 陈述的；步数在 6.0 之后才知道。

**6.11 sonnet — 删除旧物。** 移除六个旧的 `Ext.Enc` constructor、旧 extern、driver
`Kernel.map fold scan permute`（`Driver.lean`；分别有 5、2、2、2 个使用者）、没有调用者的 Rust 文件；用 `LR rename`
把 `k` 名字改成 `Kernel.scan gather scatter asc distinct`，把符号改成 `qlean_scan …`；`crate/RELK.txt`；
`panic-allow.txt`。Gate：`syms`、`externs`、`panic`、`crate-test`。

**6.12 opus — native gate。** `Rel/Lang/EmitC.lean:16` 的 `abi` 列出 `Db.ownWrite`、`Order.groupIds`、`idGroups`、
`Ew.val cmp bit`、`whereBits`、`gatherBytes`；`relc`/`rel-native` 用 `qlean_own_write` 写 column。把
`abi` 重述到这五个 kernel 加上 R4 保留的东西；`lake build rel-native` 以及 `out/key`、`out/val` 的比较。

### P7 Plan A（4 步；串行）

**7.1 opus — library 边界。** `compile` 在 `RelRun`（precompiled）；`Tm.den`（`Rel/Lang/Den.lean`，
noncomputable，`Classical`）和每个 `*_sound` 在 `Rel`。要么 `Den.lean`、`GenSpec.lean`、
`CompileSpec.lean`、`Rows.lean` 及它们的 import（`CRel*`、`KernelWF`）移到 `Rel/Run/` 之下，要么 `compile` 移到
`Rel/Lang/`，且 `rel_program`（它在 elaboration 时运行它）import `Rel`。由 Q12 决定；这一步
被它阻塞。

**7.2 opus — subtype。**
`def compile (η : CodeEnv) (ρ : Val) (hη : η.Sound ρ) (t : Tm A B) (hw : t.illFormed = none) :
{r : Rel A B // r.Reps (t.den ρ)}`，由 `Tm.gen`（`Compile.lean` 169-232）的递归构造，每个分支的
证明就是 `compile_sound`（`CompileSpec.lean` 238-355）的对应分支。删除 `compile_sound`、`Out.Sound`、
`Code.Sound`。

**7.3 opus — `rel_program` 发出 `compile t`（设计文档 §5.1 stage 4）。** 从 `Expand.lean` 删除：`code node
plan? planOr spine body share primE fitConst primWrappers`；从 `Rel/Lang/RelRep.lean` 删除：`prf pprf prfNode lem
lemO rep`；`Rel/Lang/TestRep.lean`。`test/TestCompile.lean` 和 `compile-diff` gate 失去它们的对象
（没有第二个东西可比较）：用程序的 `#guard` 取代该 gate。

**7.4 sonnet — 清理。** 对 `Rel/Lang/*` 和 `Rel/Run/Lang/*` 运行 `LR unused`、`LR unused-simp`、`LR remove-import`；
更新 `CLAUDE.md` 的 Layout/Gates 文字和 `Makefile`（`compile-diff`）。

## 3. 各 phase 的并行与串行

| Phase | 步数 | 并行的 worktree（不共用 section）      | 串行                                        |
|-------|------|----------------------------------------|---------------------------------------------|
| P0    | 1    | —                                      | 0.1                                         |
| P1    | 3    | 1.3（freyd repo）与 1.1 并行           | 1.1 → 1.2；1.2 和 1.3 一起合并              |
| P2    | 6    | 2.1、2.2、2.4、2.5、2.6                | 2.2 → 2.3（`Den.lean` 的同一 section）      |
| P3    | 13   | 3.3 与 3.2 并行                        | 3.1 → 3.2 → 3.4 → 3.5 → … → 3.13，一个分支  |
| P4    | 5    | 无：每一步都编辑同样的 match 分支      | 4.1 → 4.2 → 4.3 → 4.4 → 4.5                 |
| P5    | 8    | 5.4a、5.4b、5.4c；5.2 与 5.3 并行      | 先 5.1；5.5 → 5.6 最后                      |
| P6    | 13+  | 6.1、6.3；6.4、6.5；6.6-6.8；6.10 各组 | 先 6.0；6.2 → 6.4；6.9 → 6.10 → 6.11 → 6.12 |
| P7    | 4    | —                                      | 7.1 → 7.2 → 7.3 → 7.4                       |

合计：8 个 phase，53 步（6.10 只计一次；它在 6.0 之后展开）。Opus 39，sonnet 14。

## 4. Anchor：会变化的 constructor 的使用位置（行号对应 059f46c）

| Ctor   | Tm.lean            | Den.lean        | Compile | CSpec  | Rows | Elab                | Expand      |
|--------|--------------------|-----------------|---------|--------|------|---------------------|-------------|
| foldI  | 68 126 166 230 275 | 226 255 395 577 | 217     | 355    | 121  | 1351 1623           | 715         |
| flat   | 72 127 167 231 276 | 227 269         | 219     | 260    | 128  | 1352 1627           | 717         |
| juncD  | 38 115 155 219 269 | 211 255 537     | 202     | 352    | 130  | 1348 1584           | 737         |
| junc   | 35 114 154 218 268 | 210             | 201     | 289    | 130  | 1292 1422 1578 1587 | 701         |
| refold | 91 131 171 237 273 | 234 285 380 565 | 228     | 355    | 114  | 1347 1640           | 521 735     |
| share  | 65 174 248 278     | 225 242 294     | 216     | 305    | 125  | 1325 1361           | 见下        |
| call   | 79                 | 229             | 221     | 355    | 115  | 1335 1652 1702      | 637 666 746 |
| mu, nu | 87, 84             | —               | —       | 29, 43 | 116  | 1283 1284 1664 1668 | 520 722 734 |

`CSpec` 是 `Rel/Lang/CompileSpec.lean`。另外：

- `Expand.lean` 中的 `share`：531 534 543 550 608 642 664 714；`Plan.lean:336`；`RelRep.lean` 39、57、106。
- `ConvSpec.lean`：foldI 48、134；flat 134；juncD 135；junc 132；refold 135；share 46、93、194。
- `BitsSpec.lean:76` 中的 `foldI`、`BitsSpecRun.lean:31, 480`；`RelRep.lean:95` 中的 `junc`。

## 5. 风险和未决问题（只陈述，不解决）

- **R1 在新的 `Rel` 上 `rep` 不是函数；失败的 table 不带任何行。** 设计给出
  `rep (lazy f) = R ⇔ ∀ K L, rep (f ⟨K,L⟩) = K ≫ R ≫ L`，这是谓词；决定 2 写 `rep r = ⟦t⟧ρ`。没有 `dom` 的 `succ`
  没有 table，而 `tab none` 没有 relation。3.3 步使用 `Reps`，其中 `tab none ↦ True`
  （partial correctness，如同今天的 `ok = true →`）— Q4。另外：今天代码在 `ok = false` 时读取 `.rel`
  （`Gen.comp` 109 行、`Expand.printText` 100、`checkErr` 104、`Gen.mu` 被截断的链、`failures` 112）；
  用 `Option` 之后这些行不复存在，诊断信息会改变。
- **R2 Plan A 需要 `compile` 在 `Tm` 上是全函数，而有三个条件在 `Tm` 中无法表达。** 正的 μ/ν
  body、closed 的 `share` 部分和已解析的 `call`，都是对 `Tm` 递归计算出的性质（`Tm.pol`、
  `Tm.fv`）；没有 induction-recursion，它们不能成为 constructor 的字段。"在 elaboration 时被拒绝" 并不
  把假设从 theorem 中去掉。5.6/7.2 步保留一个可判定的 `t.illFormed = none`；它是否
  算作 "所有 gap 都已关闭"，由 owner 决定。第二半：`compile` 在 precompiled 的 `RelRun` 中，`Tm.den` 和
  所有证明在 `Rel` 中（Q12）。
- **R3 foldI 和 flat 作为 definition 与 gap 的顺序矛盾，而且可能更慢。** 两个 definition 都需要在 on-demand 的
  term 上使用 `conv` 或 `ran`，而 `Bool` 下标禁止这样做，所以它们只有在 P3 之后才通过 typecheck，而决定 6
  把 foldI 列在最前。`foldI` 只有配上保持下标的 meet（2.3）才等于一个 `fold`。`Gen.foldI`、`Gen.flat`、
  `Gen.juncD` 今天是直接的 kernel；推导出的 term 每次调用要运行 `outl° `、一个 meet 和一个复合
  （Chess、Edit、Knapsack、Quicksort 用到它们）。没有任何测量。
- **R4 "RELK.txt 有 5 行" 与 gate 矛盾。** `rel-native` 和 `relc` 调用 `qlean_own_write` 和 group-id
  kernel（`EmitC.lean:16`）；`qlean_stop`（`Kernel.stop`）是容量中止；`Coc.encode`/`decode`、
  `Column.blockStart` 是 extern，在那五个之中没有位置。`externs`、`syms` 和 `panic` gate 读这份列表。
- **R5（上面已决定）九个 atom 移除了 core 在用的类型。** `Vals (.sum A B)` 把它的 tag 放在
  `Arr .boolean` 中；`Obj.general`
  和 `Obj.Ordered (t ≠ .general)` 点名了 `.general`；`Arr .long` 持有 `Obj.arr` 的 `lo`/`hi`。设计没有
  说 tag column 变成什么（i8，还是宽度 1 的 packed），也没有说装箱的 column 是否保留。1718 个 declaration
  依赖 `QAtomicType`；`KernelSpec` + `KernelWF`（约 21700 行）是针对今天的 kernel 和
  编码陈述的：P6 的证明代价在 6.0 之前未知。
- **R6 Open share：没有找到 producer。** `Expand.number` 只包裹 closed 的 term，而 `Tm.gap` 却有这个分支；
  `convTm`（1325）和 `convProj`（1361）重建 share。`closed` 是用 `!d` 定义的，所以它的含义在
  3.11 改变。
- **R7 浮点序。** `rank64` 把每个 NaN 送到同一个 key，所以 `¬ lt` 不是反对称的，`KeyInj` 失败；
  设计的保序位映射使不同的 NaN payload 互不相同，且 `-0 ≠ +0`。这会改变每个 relation 中浮点数的
  相等，不只是 `asc`。
- **R8 作为等式的 `Tm.Ax` 是 `Core.Rel` 定律的一行复述**（12 条中的 10 条），仓库的
  "no one-liner theorems" 规则见到就删，除非它们是交付物。决定 3 要求写它们；1.1 步
  写全部 12 条。
- **R9 `inl`/`inr` 已经作为 prim 第 3、4 行存在**，带有 `inl_sound`、`inr_sound`。加 constructor
  而不删这两行就是重复；4.1 删除这两行，这会改变 `prims` 的下标（`Rows.lean` 中 `rows` 按 0-27 编号），
  以及 freyd relaop 中 `Calc.toTerm` 的读法（`RelAop/Calc.lean`）。
- **R10 `nuAC`。** `Expand.node:732` 对 AC-3 形状的 body 发出 `Gen.nuAC`；`compile` 用 `Gen.nu`。它们只靠
  compile-diff 测试保证一致；`nuAC` 没有 soundness 引理（设计文档 §7.2 说它需要自己的）。7.3 之后，
  要么 `compile` 选择 `nuAC`（需要该引理），要么 AC-3 程序变慢。
- **R11 4.2/4.3 之后的 `Tm.pol`。** 它把 `foldI`、`flat` 当作 "不得提及 k"；作为 definition，它们的
  polarity 由 `comp`/`meet`/`conv` 推出，所以被接受的程序集合会改变。
- **R12 分阶段使用临时物**（`CRel.ok`、`CRel.rel`、`CRel.mk`、`Fn.toRel`、phantom `d`、`k` 命名的
  kernel、与六种编码并存的 `packed`）。每一个在一个 phase 的时间内都是同一事实的第二种形式，违反
  DRY 规则；每一个都有指名的删除步骤（3.12、3.9、6.11）。

给 owner 的问题：

| Q   | 问题                                                                                              |
|-----|---------------------------------------------------------------------------------------------------|
| Q1  | freyd：删除 `RelAop/Syn.lean`，还是把商移到 relaop 以保留 `Functor Syn RelSet`？                  |
| Q2  | 表层关键字 / `Pre.refold` 是否也变成 hylo？                                                       |
| Q3  | 答 M：`tab` 持有 `Option (Tab A B)`，`Tab` 是结构 `{n, key, val}`（3.1 的 rename）                |
| Q4  | `Reps`（谓词，`tab none ↦ True`）是不是想要的 `rep`？如果不是，`rep (tab none)` 是什么？          |
| Q5  | 答 L：`snoc`、`asc` 是 primitive；2.6 中每个 `+ slice` 行都是融合 kernel，由 `⟦row⟧ = ⟦def⟧` 联系 |
| Q6  | 没有 `d` 之后，Elab 在哪里插入今天由 `closeRes` 插入的宇宙前缀？                                  |
| Q7  | `Den` 的 inline：给 lean-refactor 加一个 unfold-abbrev 命令，还是把 `Den` 保留为 notation？       |
| Q8  | `Tm.symDiv` 的签名（宇宙参数同 `ldiv`？）及其表层语法。                                           |
| Q9  | `Tm.hylo` 的签名（保留 `k what ch body`？）以及把 `ch` 与 `body` 联系起来的前提。                 |
| Q10 | lam/E/thin 的 `Ordered`/`KeyInj` 假设在 `compile` 的类型中从哪里来？                              |
| Q11 | `Tm.den` 中 `call` 的含义（stage 5）：inline 被调用者的 term，还是一个 definition 的环境？        |
| Q12 | plan A 的 library 边界：证明移进 `RelRun`，还是把 `compile` 移出它？                              |

## Baseline

在 `e78e922`，`make check` exit 0。compile-diff："compile agrees with the generated code on 241 definitions; not ok
on 25"（`sudokuac.s`、`Test.given.q{R,M,F,h}`、`Test.orders.Of`、`Test.muGrow.g`、`TestWumpus.given.f0`-`f16`、
`TestRefold.refoldCycle.bad`）。每个 phase gate 都必须复现 241 / 25，或解释差异。
