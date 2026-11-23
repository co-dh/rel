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
  （由 G 细化：规范化只在产生 float 字的地方做；序码与 `Obj.key` 都是存储位上的单射 `ordCode`，代码已如此，见 G。）
- R8：1.1 只写不是某条 `Core.Rel` 定律的复述的等式（`mu_unfold`、`nu_unfold`）；
  其余十条直接用作 `Core.Rel` 的定律。
- Q1 删除 `RelAop/Syn.lean`；Q2 表层的 `refold` 也变成 `hylo`；Q3 `tab` 持有 `Option (Tab A B)`，结构
  `{n, key, val}`（owner：M）；
  Q7 `Den` 手工 inline；Q9 `hylo` 保留 `k what ch body`；Q11 `call` 的意思是被调用者的 term 被 inline；
  Q12 `compile` 从 `RelRun` 移到持有证明的 library。（2026-11-18 推翻：见 7.1、7.2）
- Rel 是自己的语言，不是 k/q 的实现（owner 更正，2026-11-18）：没有 Rel 程序用到的 kdb/q 语义一律删除，
  不保留、不搬走；此后的计划按此办理（见 6.14）。
- owner 决定（2026-11-18，迁移由 operator 重排为 W0–W6，见 6.14）：
  - "there should be no conversion"：kernel 调用之间、算子边界上没有 `Coc.encode`/`Coc.decode`/`Enc.bytesOf`/
    稠密 `ByteArray`；没有 adapter（`Enc.ofLongs`/`Enc.longs` 撤回）。
  - M：列编码集缩到 foR + `pos`；`sym` 是字典（6.11）之上的 id 列；字面量在进入处编码成 foR；`general` 列只作为
    `arr`（`lo`、`hi` 指向一个扁平 payload）存在。`.bytes`、`.syms`、`.gen`、enum 编码删除。
  - C：kernel 测试输入保持 1024 行一块。
  - I（6.9）：`QAtomicType` 的 13 个 constructor 全部保留（`u1 u8 i16 i32 i64 f32 f64 char i8 sym date datetime
    general`）；删除的是 q 的编号和 wire 语义：`code`（q 类型码）、`width` 的 IPC/splayed 含义、doc comment 里的 q null
    规则。未决：若没有 Rel 程序用 `date`/`datetime`，它们是否并入 `i32`/`i64`。
  - reader 是 mmap（`ownMap`）；`crate/RELK.txt` 的目标：五个 kernel + `stop`、`coc_encode`、`coc_decode`
    （owner 没有说 "5" 是否取字面）。IO export（`own_write`、`own_map`）已分到 `crate/RELIO.txt`（I4），不计入 RELK；
    现在 RELK.txt 9 行，RELIO.txt 2 行，`syms` gate 要求二者不相交且并集 = crate 定义的 `qlean_*`。
  - `pointfree` gate 的范围 = L（只管类型以关系类型开头的 def）；gate G = 三个 gate，allowlist 只减不增。
  - `CLAUDE.md` 已提交（a2104f5）：Goal 是 "Rel is its own language, not k/q"；规则 "a kernel computes on the encoded
    column"。
- owner 决定（2026-11-19）：
  - F（D.12）：`kseen` 只接受已按 `kasc` 序排好的行；引擎选择与直接寻址删除，调用者一律 `kasc ≫ kseen`。
  - owner 不在时，已写原则答不了的设计问题由 fable agent 分析并执行，问题、结论、理由记在本列表供复查；kernel 要
    解码、推翻 owner 已做的决定，仍留给 owner。
  - fable 决定（2026-11-19，owner 接受：G）：float atom 的相等 = 存储位相等。问题：W2 的定律带前提 `hK`（序码相等
    则行相等），而 `kasc`/`kseen` 的序码把 `±0` 合成一个、所有 NaN 合成一个，`hK` 在 f32/f64 上为假。结论：序码
    在每个有序原子类型上是存储字的单射保序位映射（float 用 IEEE totalOrder：非负置符号位，负数翻全部位，比较时
    不再 `normalise`）；R7 的规范化（一个 NaN、`-0 ↦ +0`）只在产生 float 字的地方做（随 6.9）。理由：值模型已经
    是位（`Carrier .f64 = UInt64`）；`doc/rel-architecture.zh.typ:197` 写的就是纯位映射；规范化过的列上新旧序码
    相同，所以 R7 与 D.12 不被推翻；没有 Rel 程序用 float。后果：未规范化的列上 `-0.0` 与 `0.0` 是不同的行；
    mmap 进来的 float 列是否检查规范化，留给 owner。实现在分支 `ordcode`。
    代码已按 G 办理（S5，分支 `tb-s5`）：`Obj.key` 在每个定宽 atom（f32/f64 在内）上是 `atomKey`，即 `ascOrd`
    （`kasc` 用的同一个 `ordCode`）作用于存储位 `Column.bitsOf`；合并 NaN 与 `±0` 的 `Order.rank`（及
    `rank32`/`rank64`、`foRKey`、`rank_ofNat_iff`）删除；`Obj.key_ordCode` 不再排除 float；`Obj.ascBad` 只拒绝
    `sym`、`general`，`asc` 接受 float。`LamLaw` 已是定理（S5，`Vals.lamLaw`）；`Obj.eq_of_not_lt` 的前提保留，
    原因只剩 `general`（key 为 `[]`）。
- 非 log 的输出（baseline、row 分析）写进本文件或 `doc/`，不写进 `/data/tmp`。
- owner 决定（2026-11-20，最终）：
  - date 字面量写作 q 的 `2024.01.15`，新 token（实现：分支 `datelit`，`Elab.qForm`；值为 1970-01-01 起的天数）。
  - `sum`/`sums` 在 i64 与 f64 上都按从左到右求和（q 的顺序，owner 裁定 C）：`sum` 的定义是左折叠 `⦇[0, plus]⦈`。
  - cast 逐值偏：没有像的值没有行，不报错。
- 文本字面量 `"…"`（分支 `txtlit`）：`[C]` 上字节的数组，`Tup.ofText`；未写类型的检查里字面量的对象由其上的数值运算定
  （`Elab.settleLit`），`where` 表按输入的声明类型读（`Expr.lit` 的 `ty`）。测试 `Rel/Lang/TestDateLit.lean`。

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

| #  | 设计项                         | 现有代码（module : 行）               | 差距                                    | Size | 状态       |
|----|--------------------------------|---------------------------------------|-----------------------------------------|------|------------|
| 1  | `Rel` = `tab` 或 `lazy`        | `Rel.Rel`, `Run/Core.lean:485`        | 没有 `lazy`、`Known`；2420 个依赖者     | L    | ✅ 3.8      |
| 2  | `Known = {dom, ran}`           | `Gen.Dem`, `Gen.lean:25`, 只有 dom    | `ran` 一侧没有对应物                    | M    | ✅ 3.3      |
| 3  | CRel 删除，ok → Option         | `CRel`, `Run/CRelDef.lean:8`          | 2297 个 decl；`.rel` 在 ok=false 时被读 | L    | 🔄 3.12     |
| 4  | `Fn`、`Dem` 删除               | `Gen.lean:48`, `:25`; `Pl` `:51`      | 7 个 module 中 224 + 182 个 decl        | L    | 🔄 3.12b    |
| 5  | `Den` 被 inline                | `abbrev Den`, `Lang/Den.lean:20`      | 206 处用在 12 个 module；`LR notate`     | M    | ✅ 3.13     |
| 6  | `Tm` 没有 `Bool` 下标          | `Tm`, `Run/Lang/Tm.lean:15`           | `Res`、Elab、Expand、Bits、Plan         | L    | ✅ 3.9      |
| 7  | `compile` 返回 subtype         | `compile`, `Compile.lean:235`         | 先关闭所有 gap；R2                      | L    | ✅ 7.2      |
| 8  | Syn、Le、Eqv、Hom.den 消失     | `Lang/Syn.lean`, 347 行               | 在 rel 中是叶子；freyd import 它        | S    | ✅ 1.2      |
| 9  | `Tm.Ax` 写成等式               | `Syn.lean:21-42`, `:131-148`          | 12 个 constructor，12 条等式            | S    | ✅ 1.1      |
| 10 | refold 改名 hylo               | `Tm.lean:91`, `Gen.lean:267`          | 120 个名字含 "refold"                   | S    | ✅ 2.1      |
| 11 | foldI 成为 definition          | `Tm.lean:68`, `Den.lean:98`           | owner 选 D：留 ctor，证 `foldI_sound`   | M    | ✅ 4.3      |
| 12 | flat 成为 definition           | `Pre.flat`, `Elab.lean:262`（p44）     | dfnR6：flat 融合，primFit 每实例拟合一次；绿，待合并 | M    | 🔄 4.2      |
| 13 | inl、inr 是叶子                | `inlRow`…`inrConvRow`, `Syntax:176`   | 无：prim 行带 code、den、RowOK；R9      | S    | ✅ 4.1      |
| 14 | junc 是 definition，没有 juncD | `Pre.junc`, `Elab.lean:256`           | 无：`inl°R ∪ inr°S`；不放 prelude       | M    | ✅ 4.1      |
| 15 | 对称除法是 definition          | `Pre.symDiv`, `Elab.lean:264`         | 无：`R/S ∩ (S/R)°`；表层语法 `R ÷ S`    | M    | ✅ 4.4      |
| 16 | 拒绝非正的 μ/ν                 | `Tm.pol`, `Tm.lean:254`               | Elab `.fix`（1655-1670）：没有检查      | S    | ✅ 2.4      |
| 17 | gap：open share                | `Rows.lean:125`, `Expand.lean:530`    | 无：share 读 `Val.empty`，情形已证      | M    | ✅ 5.1      |
| 18 | gap：setify、asc               | `rowGaps`, `Rows.lean:107`            | 无 gap；`LamLaw` 是定理（S5）          | M    | 🔄 5.2      |
| 19 | gap：hylo                      | `rep_refold`, `RefoldSpec.lean:124`   | `onNodes` 修复、`hylo_sound`；去 `ch`   | M    | ✅ 5.3      |
| 20 | gap：lam、E、thin              | `lamDen` `Den.lean:111`; `Canon`      | 三条已证；残留缺口：f32/f64 元素        | L    | ✅ 5.4c     |
| 21 | gap：call                      | `Tm.lean:79`; den 读 body             | 无：`Tm.den` 读 body，情形已证          | L    | ✅ 5.5      |
| 22 | prim row 写成 fold/hylo        | 28 行, `Compile.lean:77-112`          | 没有逐行检查                            | M    | ✅ 2.6      |
| 23 | scan、scatter primitive        | driver, `Kernel/Driver.lean:25-38`    | 有定律，无 caller（见 W2–W3）           | L    | 🔄 W2–W3    |
| 24 | gather、asc、distinct          | `gatherPacked`, `Order.grade`, `nubC` | 无 caller；无 "= 复合" 定理（见 W2）    | L    | 🔄 W2       |
| 25 | 一种编码 `foR`              | `Ext.Enc`, 7 个 ctor, `Value.lean`    | 460 个 decl 依赖 `Enc`                  | L    | 🔄 W1b      |
| 26 | 九个 atom                      | `QAtomicType`, 18 个 ctor, `Value:13` | 1718 个 decl；boolean、general；R5      | L    | 🔄 6.9      |
| 27 | RELK.txt 84 → 5 + 保留的（现 9；IO 2 个在 RELIO.txt） | `crate/RELK.txt`, `crate/RELIO.txt`, `crate/src/ffi/` | native gate 需要更多；R4                | L    | 🔄 W5       |
| 28 | q-only kernel 删除             | 84 个 extern（`RELK.txt`）            | q 专用 kernel 仍导出（W0）              | S    | 🔄 W0       |
| 29 | seen-set scan `kseen`          | `kdistinct`, `Order.groupIds`         | foR 上的 `g` 与 `first`；agent 在做     | L    | 🔄 D.12     |

## 2. Phases

顺序：P0 → P1 → P2 → P3 → P4 → P5 → P7；P6（kernels）在 Lean 层面独立于 P2-P5，只有浮点序例外（5.2 等待 6.9）。
状态：✅ 完成，🔄 进行中，⬜ 未开始，✖ 弃用。每步的旧文本（文件、行号、`LR` 命令、Done 条件）在 commit
178da18 的 `PLAN.md` §2：`git show 178da18:PLAN.md`。行号已过时，先用 index 重新定位。

进度（2026-11-18，master a2104f5）：45 / 67 步（67%）；另有 12 步进行中（5.3、7.5 已合并，各加一步）。只数 ✅：分支上 build 通过但还没合并的步骤算进行中。

| Phase                | 完成 / 步数 | %    | 进行中（分支）                                              |
|----------------------|-------------|------|-------------------------------------------------------------|
| dataframe D.1–D.12   | 7 / 12      | 58%  | D.3 D.7 D.8 D.12                                            |
| P0 baseline          | 1 / 1       | 100% |                                                             |
| P1 删除 `Syn`        | 3 / 3       | 100% |                                                             |
| P2 不依赖 `Rel` 类型 | 6 / 6       | 100% |                                                             |
| P3 `Rel` 类型        | 11 / 13     | 85%  | 3.12（3.12b 未开始）                                        |
| P4 `Tm` constructor  | 2 / 5       | 40%  |                                                             |
| P5 关闭 gap          | 7 / 8       | 88%  | 5.2（浮点 key 的 `LamLaw`）                                 |
| P6 kernels           | 9 / 15      | 60%  | 6.9、6.10、6.11（`d56c`）、6.13（`d4pos2`、`d4pos3`）、6.14 |
| P7 Plan A            | 2 / 4       | 50%  |                                                             |

Diff table 的「状态」列：✅ 后面是完成它的步骤；🔄 是部分完成，后面是还没完成的那一步；⬜ 后面是要做它的步骤。
29 项里 ✅ 12、🔄 11、⬜ 6（master a2104f5，2026-11-18；第 19 行随 5.3 合并改为 ✅）。

### 高优先级：dataframe（`doc/dataframe-design.zh.pdf` §2、§6、§7；stage 1 的 `Plan.ofTm` 由 dataframe 会话自己做）

按此顺序执行，排在其余未开始的步骤之前：
- ✅ D.1 `qlean_k_asc`（6.7，178da18）与 `qlean_k_distinct`（6.8，d1e6ff6）早已在 master。
- ✅ D.2 F17(2) Rust 与 Lean 的宽度平局：foR B（f0f9171）后 `Coc.encode` 就是 Rust 的代价选择，平局取较窄宽度，
  `CocTest` 的 `decide`/`#guard` 逐字节比较。gate 3 的文件字节两边相同。
  CocTest 与 StructuralTest 的实例缩到各 case 所需的最少元素（合并 479841c，峰值 13.7 GB → 1.65 GB）。
- ✅ df-F8 随机源：`Op.mix`（splitmix64 在计数 `u` 处，`Op.mixWord`，Rust `op_word` 分支 49，`cast`/`fto` 码后移一位，
  `RELK.txt` 不变），row `mix : R ⟶ R`（i64，`Tab.mixOp`，`mixOp_den`/`mixOp_wf`，`rowOK_mix`）；`frameRand` 库：
  `rand` `shuffle` `sample` `randomSplit` `randomRest` `kFolds`，`TestFrameRand` 钉住种子 0 与 42 的手算值。
  未做：`stratifiedSample`、`mkRandom`；`EmitC` 没有 `mix` 的 C 代码（`relc` 遇到该 row 报错）。
- 🔄 D.3 6.9 atom（含 `date`、`datetime`、`u8`）：Rust tag 表 WIP，Lean rename 排在 3.8 之后（见 6.9）。
  执行约束：机器 30 GB，`cap` 的 20000 MB 是每个进程的虚拟地址上限（`ulimit -v`），不是占用；限不住多个 build 的总 RSS，所以重的命令（全量 build、`lean-refactor`）前加 `cc-guard/bin/admit`：只在可用内存够时启动，不加锁，CPU 让调度器分。合并后把 sha 告诉 dataframe 会话，stage 1 rebase 到它上面。
- ✅ D.4 6.13a 虚拟行号 `Enc.pos`：已合并，以下为合并前的记录。`d4pos2` 32b83cf，`RelKernel`、`RelRun` 与所有用到 `Enc` 的 `Rel` module build
  通过，0 sorryAx，cargo test 154，syms 一致；定律 G1、G2、S1、D1 已证。未合并：`kasc` 的 `pos` 捷径在 m > 2^63 时与
  Lean 模型不一致（`ascOrd .i64` 翻符号位），`d4pos3` 给两边加 `m ≤ 2^63` 并带此前提证 A1、A2。
  原条目：6.9 合并后立即开始（两者都改 `Value.lean`，不能并行）。
  验收（dataframe F-d）：排序编码要的位置 `til n` 直接读 `pos`，不再用 `gather(invert(p), p)` 绕。
  owner 的细化（经 dataframe 会话）：位置是一个固定的对象 `N`，不是每个 frame 各自的 `I = {0..n-1}`。m 行的 frame 是一族
  恰在 `0..m-1` 上有定义的部分映射 `x : N ⟶ C`，加上 m；`N` 的元素从不存储。产生新 frame 的 op 是关系 `p : N ⟶ N`
  （新位置 → 旧位置），结果列是 `p ≫ x`：`take(n) = (<n) ≫ x`（实现 `hi := min(hi, lo+n)`）、`drop(n) = (+n) ≫ x`
  （实现 `lo += n`）、filter 是保留位置的 `where`、sort 是 `asc` 给出的置换经 `gather` 作用。所以 `pos` 这一侧的含义是
  「`N` 中小于 m 的位置」；`Enc.pos` 的定义（`get .i64 m .pos i = some i`，i < m）不变。
  进度：6.13a WIP 51aeacd（Lean 与 Rust 读取分支、测试；`RelKernel` 剩 `KGather` 两个证明），由分支 `d4pos2` 接着做。
  6.13b 的范围：`longsOf`/`tilLongs`/`tilCol` 还有约 35 个可执行调用者（`Rel.Run.Alg`、`Rel.Run.Code`、`Rel.Run.Lang.Bits` 等）。
  窗口在 frame 上（owner，经 dataframe 会话）：一个 frame 的所有列共用一对 `(lo, hi)`，因为每个 frame op 对每一列用同一个
  `p : N ⟶ N`。frame 的位置总是 `0..m-1`，key 始终恰为 `Enc.pos`，m = hi − lo；在新位置 i 读列 c 就是读 c 的 payload 的
  `lo + i`。`drop(n)` 是 frame 上的 `lo += n`，key 仍是 `pos`（m − n），所以 `Enc.pos` 不需要 offset（与 6.13 的「不做
  `a + s·i`」一致）。值恰好是行号的列（物化的下标）是普通 `i64` 列，不是 `pos`。构造新数组的 op（按置换 `gather`、
  filter 的压紧、groupBy）产生 `lo = 0` 的 frame。
- ✅ D.5 F17(1) 布尔 `foR`（已合并：boolean 是 `u1` 的 `foR`；
  `Ew.cmp`/`Ew.bit` 返回两个寄存器，bitmap 形式是 `Ew.cmpBits`；
  plan 侧 `call1`/`callK`/`maskB`；以下为合并前的记录。6.11c，`d56c` e0afbe1：每个使用者经 `boolBits` 读 writer 的 `u1` foR，唯一的读引理
  `boolBits_bools`；全量 build 0 error 0 sorryAx，cargo test 154；compile-diff、native、syms 待合并时的 `make check`；
  `Enc.bits` 尚未删除；`RazeRowRec.held_side` 的 `dsimp` 变慢的原因未查）：把 6.11 中「`bits` 是宽度 1 的 `foR`」这一项提前，`Enc.WF` 接受 `u1` 的 `foR`，`scan` 的布尔结果
  答 `foR`。在 6.10 的 `scan` agent 合并之后（同一个 kernel）。
- ✅ D.6（已合并）`scan` 的方向参数（反向扫描，van Herk）：`kscan` 的扩展，不是新 kernel。
  与 D.5 同一个 agent，在 `scan` 合并之后。
- 🔄 D.7 第一部分 F-e 已合并（ca8f45c，master 78b01ed）：`Rel.Db.pushPart`、`Rel.Kernel.enlistLong`，native gate 比较
  整个 `out` 目录。第二部分（列的 mmap reader）也已合并：`d7map` fbb31f7 与 `d7store` d3926fd 都经 75a2d45 进了
  master；reader 叫 `Rel.Db.ownMap`（`@[extern "qlean_own_map"]`，body `ownParse`，不是 `fileMap`），定律
  `ownParse_ownImage`（`Rel/KernelSpec/Own.lean`）。qlean HEAD 仍在 `rust/qrs/src/ffi/own.rs` 定义一份 `qlean_own_map`，
  但它的工作区把 rel 钉在 `qlean-base` = e024297（不含 75a2d45），所以现在没有重复定义；qlean 把钉子移过 75a2d45 时删
  自己那份（DRY），是 qlean 会话的事。表目录见 D.9。`.d` 是自有格式的 sym 列（no serialization）；共享字典用列头已有的
  `domain` 字段。未决：`own::check` 没有 Lean model。
  原条目：stage 2 存储的 runtime 部分：export 把 column 目录 mmap 成 `Tab`（目录 = 表，文件 = 一列的 foR `Enc`，`.d` 列序，
  共享 sym 字典文件；`pos` 一侧不落盘，按 6.13）。只动 `crate/rt` 与 `Rel.Kernel`，6.9 合并后与 D.4 并行。
  同一 agent 补 dataframe F-e：`relc`/`rel-native` 跑不了算出来的程序，缺两条 plan 指令：把算出的 buffer 交给
  `qlean_own_write` 的 `parts : Array ByteArray`；把一个 size 寄存器变成单元素 buffer（`.hi` 列）。D.9 依赖它。
- 🔄 D.8 F2 `Λ` 的 canonical 形式（5.2 setify/asc 行、5.4a `lam_sound`）、`foldI`（4.3）、`hylo`（5.3）：在 `rel-lazy` 上紧接
  3.8 做，排在 3.9-3.13 之前。不在 master 上先做：这些步骤改的 `Gen`/`Compile` 组合子正被 P3 重写，先做就要写两遍。
  dataframe 的输入：F-a `groups(k)` 写不出（`strₗ` 不在 `prims`，带键的 `foldI` 缺），只能按 K 的整个 universe 逐元素
  播种左 fold，代价 |K|×n；F-b `filter(p)` 进入 `Tm` 时是 prelude 的 fold 展开，recipe 只能匹配 fold 的结构。
  D.8 一并决定 `filter`/`groupBy` 是否各有自己的 `Tm` 节点。
  进度（`rel-lazy` e7c40ee，全量 build 0 error 0 sorryAx，compile-diff 241/25 = baseline，native 字节相等）：
  - 已完成：`lam_sound`（canonical 元素对象，d72cf71）；`groups(k) = ran(R k) ≫ Λ((R k)°)` 与 `filter(p) = R ≫ p` 是
    组合式，不加 `Tm` 节点；`E_sound`（0ac4f13，与 `lam_sound` 共用 `lamDen_of`）；`Obj.canonical` 对每个 rank 单射的
    atom 成立（e7c40ee，只有 `f32`/`f64` 不成立）。
  - 未完成：`foldI` 成为 definition（`rep_foldBy_keep` 要从 `pend₀ = top T.key e` 推广到任意逐行种子关系）；`thin_sound`
    （缺一条把 `swapInC` 的行读回 `TQ (c,b)` 的引理）；setify/asc 行（Row 引理对每个 σ 都要成立，而含义只在 canonical
    元素对象上成立，Row 接口要加对 σ 的前提）；`hylo`（`rep_hylo` 要 `Local chN Φ`，而 `Tm.den` 不看 `ch`，见 Q9）。
  - 性能发现：TestGroups 的耗时随最大组的大小增长（1 个 key 160 ms，1000 个 key 7 ms）。原因是 `Obj.sortByC` 的 `.arr`
    分支（`Rel/Run/Code.lean`）是 LSD radix sort，每个元素位置跑一遍 `arrPass`，一行里有 100000 个元素就是 100000 遍。
    ✅ perf13：已不成立。`Code.lean` 在 T10f（18224ec）删除，`.arr` 的序现在是 `kasc` 的 `cells` key，Rust 侧
    `Cells::codes`（R12）把 payload 排一次名、每个 cell 按 slice 比较，代价随元素总数。master d8030bc 上 1 个 key
    21 ms，1000 个 key 22 ms；`perf record -g` 中 `librelk.so` 合计 5%，其余是 elaboration。TestGroups 加了
    skewed 一例（501 组，其中一组 50000 行），守住"组数 × 最长"不再回来。
- ✅ D.10（ee84ad8，make check 绿）：两个 `Row` 是不同概念，`Elab` 的改名 `LiftRow`/`liftRows`；TestMss 覆盖。原条目 F-c：`Rel.Lang.Row` 在 `Rel.Lang.Rows` 与 `Rel.Run.Lang.Elab` 各定义一次，同时 import 就报
  `environment already contains 'Rel.Lang.Row.mk.injEq'`，`Tm.gap` 因此不能在运行程序的模块里调用。在 master 上修，立即派。
- ✅ D.9 语言里的 `input`/`output` 声明：改 `Elab`/`Expand`，在 3.10/3.11（去掉 demand bit 的 `Elab`、`Expand`）之后。
  D.11 的表层语法也在这里：`.rel` 里的 `col "…"`，以及带 schema 的 `input`/`output`。
  步骤 1（与语言表层无关，分支 `d9table`）：`Rel/Lang/Table.lean` 的 `readVals` 是 `cols` 的逆：从目录里每列一个自有格式文件
  （按 `cols` 的路径加列名前缀）mmap（`ownMap`）出值一侧，经 `Arr.of` 检查进入；位置 key 不落盘。唯一的 writer 是
  `writeVals`，`writeRel` 是它的实例（`key`、`val` 两个前缀）。`ownParts`/`ownFile` 对 `Enc.pos` 答 `none`（不写文件），
  不再报错。`f32`/`f64`、`sym` 与 enumeration 列被拒（float 规则未定；sym 等 sym writer）。往返测试
  `Rel/Lang/TestTable.lean`。
  owner 裁定（最终）：不定义新数据结构，不转换；目录 = 表，文件 = 列，内存结构即磁盘结构（mmap）。IO 写在 `.rel`
  程序里：语句 `input … from …` / `output … to …`（owner 2026-11-20 选 G，取代此前“输入绑定在 host 一侧”的做法；语法设计在
  `/data/tmp/io/design.md`）。Rel 读写 mmap 表与 CSV；CSV 解析器是 `crate/` 里的 Rust，读、写两个新 export（owner 同日选
  A），算 IO export，不计入“RELK 到 5”。输出按结果 key 的 OBJECT（类型，不是运行时看
  key 列）分两种：key 是行号（`N ⟶ S`）时写一张新表，列按 key 序、行重编号 `0…n−1`、无 key 文件（程序内部 filter 保留原
  key，只在写时重编号）；key 不是行号时是 q 的 keyed table：一个目录下 `key/`、`val/` 两个普通表目录（每列一个文件，按
  schema 字段命名）。不是 record 的一侧是一列，文件名就是该侧名 `key` / `val`（两侧同一规则）。mmap 读入的 float 列在读时
  检查规范形（NaN 无行、只有一个零），否则拒绝并报文件、行、位模式。
  owner 2026-11-20 的裁定（语句形式见 `/data/tmp/io/design.md`）：
  - F.1 J：语句里的字面量就是路径，运行时不替换；相对路径按运行的工作目录。
  - F.2 L：`check`/`print` 用到没有 `where` 绑定的 `input` 时，elaboration 报错并指名该 input。
  - F.3 N：`date`、`datetime` 的 epoch 是 1970-01-01。
  - CSV 解析器是 `crate/` 的 Rust，两个 IO export（`csv_read`、`csv_write`）与 `own_map`、`own_write` 一起记在
    `crate/RELIO.txt`，不计入“RELK 到 5”；CSV 直接读成编码列，类型取自声明的 schema，不推断。
  - key 是 `N` 的输出写一张重编号的新表；其它 key 写 key 表 → val 表，磁盘上 `key/`、`val/`。
  - 转换是 prim 行 `$`（`x $ F`），只做保值方向。
  步骤表（每步单独合并；I4 已完成，I0 由本次完成，I2 进行中）：
  - ✅ I0 文档：`rel-architecture`、`dataframe-design`、本条。
  - ✅ I1 表代码移到 `Rel/Run/Table.lean`（`lean-refactor move`），律留在 lib `Rel`；需要 `d9step2` 合并。
  - ✅ I2 语法与 AST：`sInput`、`sOutput`、`check`/`print` 的 `where`；`Decl.input`/`output`；elaboration 拒绝；run-time 名作参数。
  - ✅ I3 `n.io`、`n.inputs`、`n.outputs`，推论 `Sound.inputs`；需要 I1、I2。
  - ✅ I4 crate：导出分为 `RELK.txt`（kernel）与 `RELIO.txt`（IO），`syms` gate 读两个文件。
  - ✅ I5 Lean 里的 CSV 模型（`csvWords`、`csvText`、每个 atom 的读写、往返律），`Rel/Kernel/Db/Csv.lean`。
  - ✅ I6 `qlean_csv_read`：`Db.csvRead` 的 body 即 `csvWords`，Rust 在 `crate/src/csv.rs`（逐块直接写进编码列），
    `Rel.Kernel.Db.CsvTest` 逐例对照。 ✅ I7 `qlean_csv_write`：`Db.csvWrite`，body 即 `csvText`，同一测试对照。
  - ✅ I8 可空列 `V+1`、文本列 `[C]`；`sym` 仍在步骤 6 之后。
  - ✅ I9 `n.io` 中的 `from csv`/`to csv`，`relc run MOD NAME`；需要 I3、I7。
  - ✅ I10 native（分支 `i10native`）：`abi` 加 `ownMap`、`csvRead`、`csvWrite`（与 `UInt8.decEq`）。plan 加输入边
    `Plan.input`（只有 `lit` 与 IO 读），其寄存器是 `main` 的前几个；`Plan.exec` 先执行它，再把读到的值作为 `lit`
    接在 `main` 前，`Plan.run` 仍是纯的；C 把两者作为一个 block 打印。`kernel%` 接受有返回值的 IO kernel；新指令
    `sproj` 读构造子的非装箱标量（`ownMap` 答的 count、code、kind），布局与 `ctorC` 共用 `scalarLayout`。
    `Plan.ofTm σ` 读 `.var`（运行时定义的 `Once.binds` 绑到 input 的寄存器）。`ioOf` 按 `n.io` 的顺序：读
    `ioReach` 所及的 input，算所及的运行时定义，写每个 output（表目录或 CSV，位置 key 只写 val 一侧）。
    测试 `TestNative.nativeIO`：CSV input 与表目录 input（`test/native/in`），输出到表目录与 CSV；`make native`
    在第三个目录跑 `relc run`（`n.io`，Lean 语义），native 的 `out/io` 与之逐字节相等。
    ✅ native-io2（`565b382`）：新指令 `part x.i`（parts 数组的第 i 个 part；不是 `proj`：`Array` 无 tag、有 size），
    `ownSideB` 由 kind 与两个 part 重建 `Enc`（同 `Db.ownEnc`），故 map 来的列也有 `Enc` 寄存器：可写成 CSV
    （`output s to csv`、`g.csv`），也可进 recipe（`sk ≜ s ∪ s`）；float 列 `canonFloatB`（`fto t` 后 `ne` 求和，非零即
    `fail`，同 `Table.readArr`）；keyed input（目录 `key/` `val/`，或 CSV 的 key 列在前）读后 `canonT`。测试：
    `nativeIO` 加 `k` `kc` `f` `g` `sk`，`make native` 逐字节相等；`canonFloatB` 的 `#eval`（`-0`、NaN，两种 float）。
    尚未做（plan 拒绝并指名）：可空 CSV 列 `S+1`（`ofCsv` 重组与检查，等 rq17）。
  - ✅ I11 native 的 `Tm`（分支 `nativetm`）：`Plan.tabB` 按每个节点的 `GenK` 配方（§4 的 kernel 复合）建表：
    `val` `uni` `𝟘` `𝟙` `⊤` `π₁` `π₂` `≫`（`compOne`）`°` `∩` `−`（`select`）`∪` `dom` `ran` `⟨,⟩` `×`（CROSS）
    `own` `share` `var`；按需节点读上下文已知的值（`compT` 的 `ran`、`∩` `−` `⟨,⟩` 的 `bound`）。`abi` 加
    `USize.mul`。测试：`native1a` 14 个闭定义、`nativeIO` 的 `un` `cm`，`make native` 与 Lean 值逐字节相等。
    分支 `nativetm2b`：plan 加循环指令 `Instr.loop`（状态寄存器、一轮的 block、`done` 位、轮数上限用尽即 `fail`，
    即 `Tab.fixOn`/`foldRounds` 的轮次；C 是 `for (;;)`，状态经临时变量换代），`fixB` 是 `Tab.fixOn`，`nuB`/`muB`
    是 `Tab.nu`/`Tab.mu`；`tabB` 移植 `ν` `μ` `hylo`（`GenK.hylo`：节点 `μ`、`ν` 查环、`D ≫ μY`），变量环境 `TmEnv`
    读输入的 `Side` 或一轮的表。测试 `tc`（`μ`）`gf`（`ν`）逐字节相等；`hylo` 无测试：叶子要和或数组侧。
    分支 `nativetm2a` 加：上下文 `Dom` 改为 `Known` 的三项（`dom` `ran` `pairs`），`∩` `−` 交出 `bound`；
    `≤` `<`（`cmpB`：`Tab.ordOp`、`wideCol`，有 `pairs` 时切到两侧再逐对测，否则 CROSS）；`succ` `arith`
    （`succB` `arithT`：两次与 `dom U` 复合，`stepB` 即 `stepColsAt` 的 i64 比较与 float 的 `fverbOne`/`fverbBy`）；
    `prim` `arg` `call` `callCv`（`argB` 按 `Tm.argGen` 拆 spine：call 的实参闭合建表后绑定到 `ks`；行按其
    `kernRows` 算子的 wrapper：`floatOp` `$` 走 `ofVals`，`asc` 走 `ofRel`）。`crossB` 加 `Vals.cross` 的
    `crossMax` 与 `crossIx` 的 2^63 检查（`fail` 把计数附在消息后，文字同 Lean 但数值不内插）；`abi` 加
    `USize.sub` `USize.decLt`。测试：`native1a` 加 `le` `lt` `ml`（`∩ ≤` 的 pairs）`sc` `ps` `mn` `dv` `tm`
    `fc`（局部 call），共 23 个闭定义，`make native` 逐字节相等；CROSS 超界的 `#eval`。
    分支 `nativetm3b`（合并 2a、2b）：`Cols` 改为 `Col` 树（`atom` / `arr {m, lo, hi, payload}` / `sum`，积是列表拼接），
    `sum` 的所有情形只经 `sumB`（目前拒绝并指名配方）；`keyB` 给 `arr` 侧 `AscKey.cells`，`concatB` 拼 payload 并
    `clampShift` lo/hi，`gatherCols` 留 payload，`fixB` 每轮 `packT`（`Vals.pack`），`expandB` `spanB` 从 `compB` 抽出；
    节点 `nil`（`nilB`）`at`（`atB`）`Λ`（`lamB` = `lamOf ∘ canon`）`E`（`memB ≫ R` 再 `lamB`）与行 `∋`（`memB`）。
    测试 `nl` `hd` `ee` 逐字节相等；`lm`（`dom(x) Λ(bo°)`）`lu` 不等：Lean 写 2 行，plan 写 3 行（无值的键），未查明，
    暂不列入 `semOuts`。`hylo` 测试需行 `F`（`Tab.map`）。
    分支 `nativetm3a` 加：`\` `/`（`ldivSelB` 即 `Tab.ldivSel`：`groupsB`（`compGroups`）的展开数与组数在运行时
    `ite` 选择 `ldivBitsB`（`code2B` 编号、`csrB` 分组、`kbitrows true`、`ofBitsB` 读回）或计数的 `ldivOfB`，
    `bitsWinB` 用除法比较不溢出；`\` 的除法是 `ldivB`（先 `canonT`），`/` 的两个 converse 已是 `canonT` 答案，
    传 `ldivOfB`，即 canonfld2 的 `Tab.ldivOf`）；`abi` 加 `kbitrows`。call 实参按 `Code.args`：变量表 `Vars` 存
    每个变量的建表函数，按需（`dem`）或闭合建表失败（`GenK.memo` 留 lazy）的实参在每个使用处按其上下文建表，
    其余闭合建一次；body 只见实参（`Code.args` 的 `η.closed`）；对象不符读 `𝟘`（`Code.bind`）。测试：`native1a`
    加 `ld`（位矩阵）`l1`（计数）`rd`（`/`）`gc`（实参 `succ` 按需），共 27 个闭定义，`make native` 逐字节相等。
    分支 `nativetm4`（合并 3a、3b）：σ 是 3a 的 `Vars`（`ν` `μ` `hylo` 的一轮绑定为 `fun _ _ _ => pure X`），
    `ldivSelB` 的 `iteT` 按 `regsOf`/`withRegs` 读回 `Col` 树，`groupsB` 与 `expandB` 共用于 `compB`。
    仍拒绝并指名：`est` `thin` 与三种 fold（`foldRounds` 未接 `Instr.loop`）、行 `F` 及其余数组/求和行、
    求和侧（`sumB`）；从文件 map 的列（无 `Enc`）作运算数。
    分支 `nativetm5`：`funT` 把一个配方建成 plan 函数（`defFun`）并在每个使用处 `apply`，函数体相同即复用前一个
    （`Fun`、`Instr`、`Val` 派生 `BEq`），所以每种表形状一个 C 函数；`compSelB`、`compB`、`ldivSelB` 经它。
    `rel-native.c` 由 7.8 MB 降到 4.5 MB，`cc1 -O2` 峰值由超过 20 GB 降到 1.4 GB，`make native` 通过。
    行 `F`（`cellsMapB`）：`fm ≜ lm F(rt)` 逐字节相等，列入 `semOuts`（共 33 个闭定义）。`hy`（`hylo`）仍失败：
    `hylo` 的 `μY` 第一轮 `Y = 𝟘`，`F(Y)` 的元素没有像，`Tab.map` 此时走左 fold（`foldRounds peelL`），plan 尚无
    这条配方（需 `uncons` `snoc` 的 plan 配方与 `Instr.loop` 上的 `foldRounds`），故 `hy` 不列入 `semOuts`。
    仍拒绝并指名：`est` `thin` 与三种 fold、`Tab.map` 的 fold 分支。
    分支 `nativetm6`：`foldRoundsB` 是 `Instr.loop` 上的 `Tab.foldRounds`（同 `fixB`：状态为 `rest` `P` `out` 三表的
    行数与 `regsOf`，`withRegs` 读回；一轮先 `ite` 判 `P` 无行则原样交出状态并置 `done`，否则 `peel`、`step`、
    `out ∪ (P − dom(el) P)`，两者 `packT`）。新配方：`unconsB`（`uncons`/`unsnoc`，不建 payload）、`cellCatB`
    （`Vals.cat`）、`snocB`（`𝟙 × τ` 后 `cat`）、`peelB`（`peelL`/`peelR`）、`piB`/`projT`（`outl`/`outr` 及其复合）、
    `diffB`。`cellsMapB` 的 `guard` 换成 `iteT`：一遍映射或 `mapFoldB`（`Tab.map` 的左 fold，经 `funT` 成 plan
    函数），与 `Tab.map` 同一判据。`tabB` 接 `est` `thin`（`pairsB` 的 `G` `P` `D`，再按 `Tab.est`/`Tab.thin` 复合）、
    `fold` `foldr`（`foldB`）、`foldI`，全部经同一个 `foldRoundsB`。测试：`native1a` 加 `hy` `f1`（`⦇z0, plus⦈`）
    `f3`（`⦇…⦈ʳ`）`es`（`est(≤)`）`th`（`thin(≤)`），共 38 个闭定义，`make native` 三方逐字节相等；
    `rel-native.c` 4.7 MB → 7.5 MB（加 `hy`）→ 9.9 MB（再加 fold、`est`、`thin`），`cc1 -O2` 峰值 1.5 → 1.8 → 2.5 GB。
    `foldI` 的配方已接但无 semOut：提升 fold（`X⦇[e,S]⦈` 给一族）在 `native1a` 中写不出（`1 ⟶ …` 报
    “expected an object, found '1'”）。
    分支 `nativetm8`（20d7363 之后）：表配方一律是 plan 函数（`funT`；新 `funV` 值+表、`funW` 计数+字）：`nubB`
    （故 `canonT` `coreflB` `domOf` `piB`）`selectB`（`∩` `−`）`unionB` `packT` `unconsB` `nilB` `atB` `lamB` `memB`
    `snocB` `cellsMapB`，以及 `ascSeenB` `expandB` `groupFoldB`；同形同体者只发一次。`rowB` 接 `uncons` `unsnoc`
    `snoc`（`after`）`flat`（`onKeys`：`((outl X ≫ R) ∩ (outr X ≫ (outl R.val)°)) ≫ outr R.val`）。测试 `fi`
    （`foldI`，经行 `flat`）三方逐字节相等，`native1a` 自声明 `obj 1 = {∗}`（`relc` 在 Lean scope 外读程序，
    `⊤(1,L)` 找不到 prelude 的 `1`）。`rel-native.c` 9.94 MB → 5.74 MB（无 `fi`）/ 7.29 MB（加 `fi`），
    `cc1 -O2` 峰值 2059 MB → 低于 1224 MB（`cap` 峰值为 `relc c` 本身）。
    分支 `nativetm9`（7fe9c7c 之后）：`relc` 找不到 prelude 的 `1` 的真因是 `planIO` 的 `importModules` 未设
    `loadExts`：registry（各程序的 homes）是 env extension，未加载时程序不读任何 home；改为 `loadExts := true`
    （`runIO` 同），`native1a` 改用 `open Rel.Programs.prelude in`，删去自声明的 `obj 1`。表配方按列：新 `funC`
    （每列一个 plan 函数，`gatherCols`、`concatB` 逐列调用），`prefixB` `spanB` 走 `funW`，`groupsB` 的计数与
    `compFromB` 的行号只读字（`funW`，与表形无关），`compBitsB` 走 `funT`。`rel-native.c` 7.29 MB → 3.68 MB，
    212 个函数（最大 `main` 12040 行、其次 2448 行）；`cap` 峰值 1417 MB 为 `relc c` 本身；native 三方逐字节相等。
    分支 `nativetm10`（d8030bc 之后）：`main` 大的原因是 `tabB` 的节点配方本身（`crossB` `cmpB` `succB` `arithT`、
    字面量、`known` 的切片……）与每个 output 的 `sidesOf` 和写都内联在调用处，只有经 `funT` 的配方才成函数。改为：
    `tabB` = `funT [] (nodeB …)`，每个 `Tm` 节点一律一个 plan 函数；`mainStepB`（每个 output 的边与写，`outputOf`、
    `ioOf`、测试的 `arithOut` `gidOut`）一律一个 plan 函数；`iteT` 的两支各一个函数。通用核心 `funB`：闭包变换的寄存器
    类型依次取读者声明（`useTy`）、结果槽（`tysOf`）、所在 block 的定义（`defTy`，`resN` 数寄存器）；体只有一条无 block
    的指令时就地展开（不发 `apply`）。按 clang AST 的函数范围计：`rel-native.c` 3.66 MB → 2.92 MB，201 → 435 个函数，
    `main` 12371 → 250 行，最大函数 12371 → 1039 行（`\` 的 `ldivOfB`：其 `compB` `concatB` `crossB` 仍内联）；`cc -O2`
    28.2 s → 17.6 s，`cc1` 峰值 490 → 401 MB；`lake build rel-native`（改 TestNative 后）20.9 s；native 三方逐字节相等。
  步骤 2（分支 `d9step2`）：`Table.write S dir x`（一侧，按 schema 列名）、`Table.read S dir : IO (Tab .long S.obj)`
  （key 为位置）、`writeKeyed K S`/`readKeyed K S`（`key/`、`val/`）；缺文件、类型码不同、行数不同都报文件名与期望/实际；
  空 schema、重名列被拒。float 检查对唯一谓词 `Table.nonCanonical`（typed base S5 定义规范 float 后由它填）。定理：
  `Arr.pos_get`（`pos_clamp` 由它推出）、`Table.frame_holds`（重编号即 `ι ≫ t`，`ι = {(j, key j)}`，key 两两不同时）；
  文件上的 `read (write x) = frame x` 只 `#guard`（extern）。sym 列仍报“等 sym writer（步骤 6）”。
  步骤 3 由 IO I3 完成（`n.io` 在 `Expand.emit`，见下面 I3 行）。
  I1 ✅、I3 ✅（分支 `io-i3`，未合并）：表代码移到 `Rel/Run/Table.lean`（lib `RelRun`；`frame_holds` 留在
  `Rel/Lang/Table.lean`），加 `readCsv`（`Db.csvRead` 直接进编码列）、`ofRun`，keyed 读入经 `Tab.canon`。`Expand.emit`
  对每个程序加 `n.inputs`、`n.outputs : List (String × Bool × String)`（名、csv、路径）与 `n.io : IO Unit`：读 output
  所及的 input，按序用 kernel twin 算所及的运行时定义，key 为位置的 output 写 `write`（重编号），其余写 `key/`、`val/`；
  `to csv` 在任何读之前报"I7 未到"。import 的程序的 input 与运行时定义按常量名继承（`importT`、`pxIO`）。推论
  `Sound.inputs`（`GenSound.lean`）。`TestIO`：CSV input → 位置 output 与 keyed output，importer 的 output，拒绝都 pin；
  GenSoundTest 1341/1341（154 个程序）。与 design.md 不同：`from csv` 的读已在 I3（design.md 排在 I9）。
  I2 ✅（分支 `io-i2`，未合并；不做文件 IO）：语句 `input n : A ⟶ B from [csv] "path"`、`output n to [csv] "path"`，
  `check`/`print … where n ≜ {…}`（`Decl.input`/`Decl.output`，`Embed.stmt`，`Expand.walk` 的 `ioCols`/`bindIns`）。
  input 是没有 body 的运行时名；无参数且直接提到运行时名的定义按已有的参数化定义 elaboration（运行时名即其参数，
  无第二种绑定）；`check`/`print` 的 `where` 把 input 换成表、运行时定义换成对它的应用，未给表的 input 报错并指名。
  A.1 的拒绝都有报错，`Rel/Lang/TestIO.lean` 每条一个 `#guard_msgs`；GenSoundTest 1298/1298（145 个程序）。
  未做/与 design.md 不同：被 import 的程序带 input 被拒（等 I3）；带参数或 test 的定义提到 input 被拒（把 input 作参数
  传入）；运行时定义仍 emit 已有的参数化常量（只 emit `.kernel` 在 I3）；sym/general 的 CSV 拒绝无法测（不能声明这种
  object）；compile-diff 只在 main 跑（`main-only`）。
  I5 ✅（分支 `io-i5`）：CSV 的 Lean 模型，无 extern。`Rel/Kernel/Db/Csv.lean`：`csvWords cols b`、`csvText cols n ws`、
  逐 atom 的读写（`readAtom`/`fmtAtom`，float 精确舍入 + 最短文本，date/datetime 以 1970-01-01 为原点）、C.4 的拒绝；
  写出只在文本能读回同一 word 时写（`cell`），NaN、`-0`、越界 date 都由这一条拒绝。`Rel/KernelSpec/Csv.lean`：
  `csvWords_csvText`（写后读为恒等）已证，axioms `propext, Classical.choice, Quot.sound`。`Rel/Kernel/Db/CsvTest.lean`：
  case 表全部 `decide +kernel`，atom 用例按 `QAtomicType` 的 constructor 证（`atom_cases`）。C.5 的逐块解析编码是
  Rust（I6/I7）的要求；`.rel` 字面量的 `floatBits` 仍用 Lean `Float`，待改用 `readFloat`。选择记在 `/data/tmp/io/i5-notes.md`。
  I6 ✅（分支 `io-i6`）：`qlean_csv_read`（`crate/src/csv.rs`、`ffi/csv.rs`，列入 `RELIO.txt`），`@[extern]` 在 `Db.csvRead`
  上，body 即 `csvWords` + `wordsFoR`；一遍顺序扫描定记录与块起点，各列按块解析直接进 `Sink` 编码；`CsvTest` 读侧用例
  合为一张 `decide` 表，extern 与 body 在 88 个文件上一致。选择记在 `/data/tmp/io/i6-notes.md`。
  I9 ✅（分支 `io-i8`）：`output n to csv "p"` 由 `Table.writeCsv` 写（`Db.csvWrite`，各列编码直接交给 extern）：key 为位置的
  output 只写值列（按行序重编号，同 `write`），其余一个文件、一个表头，key 列在前、值列在后（同 `readCsv` 读的形式）；
  `Io.output` 带表头 `Option Db.CsvCols`（同 `Io.input`），"I7 未到"的拒绝及其 pin 删除。`relc run MOD NAME`：import
  模块 `MOD`、`evalConst` 程序 `NAME` 的 `io` 并运行（与 design.md 的 `relc run NAME` 不同：多一个模块参数；解释器要
  `supportInterpreter := true` 才找到 extern 与 `Init` 的编译代码）。`TestIO`：
  CSV 输入 → 位置与 keyed 的 CSV 输出 → 第二个程序 `from csv` 读回，文本与读回的行都按手算 pin。
  I8 ✅（分支 `io-i8b`）：`CsvCols` 每列加形状 `CsvShape`（`atom | null | text`），export 名不变，每个 part 带自己的行数
  （`List (USize × Enc)`）。可空列 `V+1` 存为 tag(`u1`) + idx + l + r，空字段即 null，写侧把 null 写成空字段；某个 atom
  能印成空文本时在 elaboration 拒绝该列。文本列 `[C]` 存为 lo/hi + 一个扁平字节 payload，引号规则同其余字段。读写都按块，
  不整列解码；往返定律改为按行（`fieldsOf`）成立，布局不唯一。`sym` 仍拒绝（等步骤 6）。见 `/data/tmp/io/i8b-notes.md`。
  IO-out ✅（分支 `io-out`，dataframe 请求 1121 第 1、3、6 条）：CSV 的列按对象结构展开（`Expand.csvLeaves`）：schema 每字段
  一列，积的因子各自展开、具名因子以其名为前缀（`Trade×(Quote+1)` → `Trade.sym` … `Quote.sym` …），`S+1` 是 `S` 每列一个
  可空列；extern 不变，`Table.toCsv`/`ofCsv` 把和的 tag/idx/null 部分按列复制、读回时核对各列 tag 相同（部分为空的行报错，
  指出行与两列）。key 为位置当且仅当 key 对象是存为 `.long` 的数对象，其它 key（`obj D : date`、`obj F : f64`）是 key 列；
  旧的“the key is positions … declare the key an object stored i64”拒绝不再可达，已删。对象在消息里按程序写法打印
  （`OTy.exp` 经 `nameShown`：`Rel.Programs.prelude.«1»` → `1`）。第 6 条不是缺陷：`relk.o` 已按 `pkg.dir / "crate"`，
  那行 “Compiling relk (/home/dh/repo/rel/crate)” 是 Lake 重放从 main 复制来的 `.lake` trace 里的日志。见
  `/data/tmp/typedbase/ioout-notes.md`。
  I7 ✅（分支 `io-i7`）：`qlean_csv_write`（列入 `RELIO.txt`），`@[extern]` 在 `Db.csvWrite` 上，body 即 `rawAll` + `csvText`；按 1024 行一块读编码列、逐行格式化、临时文件 rename；写侧 case 表 `decide +kernel`，extern 与 body 及读回在全部用例上一致。选择记在 `/data/tmp/io/i7-notes.md`。
- ✅ D.11 表层语法（`schema S = {k : K, v : N}`、`col S "v"`）已合并（da636a9）；`Schema` 层此前已合并（5ab6d2e，master 0fb9879，`Rel/Lang/Schema.lean`、`TestSchema.lean`）；TestFrame 的
  frame 按 `Schema` 索引（D.9 收尾：`frame` 的 `x` 是 `input x : P ⟶ S`，列经 `col S "…"`，`check … where x ≜ …`）。frame 的 schema 进入类型（owner 经 dataframe 会话决定，选 wrapper，不加 `Obj` constructor）：
  `Schema := List (String × Obj)`；`Schema.obj : Schema → Obj` 是 definition（按 `.d` 列序的嵌套 `prod`）；frame 的项按
  schema 索引；`col S "price"` 存在当且仅当 `("price", T) ∈ S`，在 elaboration 时判定，出错时报出列名；
  select/exclude/rename/derive/join 是 `Schema` 上的函数。kernel、存储、`rep`、`lam_sound` 不变。
  已知限制：字段类型相同、名字不同的两个 schema 是同一个 `Obj`，只有按 schema 索引的一层区分它们。
  顺序：`Schema` 层及其函数与 P3 无依赖，现在在 master 上做；D.7 的 `.d` 文件是同一个 `Schema` 的磁盘形式（一个来源）。
- 🔄 df-F1 依赖数据的 schema（`dataframe-design` F1）：第 1 部分已做——`schema S from "dir"` 在 elaboration 时读表目录的
  `.d`（`Embed.diskOf`、`Embed.schemaFrom`、`Table.readSchema`、`Table.objOf?`），`Table.write` 写 `.d`（`textCol`），
  每列在以其 atom 命名的无界对象上；测试 `Rel/Lang/TestSchemaDisk.lean`。未做：第 2 部分（以列的不同值为元素的对象、
  按它生成 `pivotWide`/`getDummies` 的 schema）要设计变更，例见 F1；EmitC/native 的输出路径不写 `.d`；`readSide` 不核对
  `.d` 与声明的 schema。
- 🔄 D.12 `kseen` 取代 `kdistinct`（owner 2026-11-18 批准；仍是五个 kernel，一个 declaration）：答 `(k, g, first)`，即
  组 id 与首次出现的位置；相等按 `kasc` 的序码（`-0.0 = 0.0`，所有 NaN 是同一个 key）。引擎：直接寻址（范围来自块元数据）
  与有序输入上的 run 检测；宽的无序 key 报可操作的错误（现在没有 hash，只做编码列；非编码 key 是向 owner 的新请求；
  `part` 引擎是解码，不批准）。
  ✅ 已落地：`kseen` kernel（212c171）；它的定律 `kseen_ok firsts_spec firsts_runs firsts_all kseen_pos`（e130504）；
  `kscatter` 接受 `Op`，覆盖是 `.last`，`last` 是位置的 scatter（23059eb）。
  ⬜ 未做：宽的无序 key 上 Lean body 有答案而 Rust 报错，且组 id 规则写了两次（`kseen` 的 body 与 `Order.idsBy`），
  修复 `seenfix` 已合并（0957f87：`kseen` 的 body 返回 Rust 的 hash 错误；`Order.groupIn` 是组 id 的唯一来源）；
  ✅ 余下各项（seen-rest）：composite 定理 `kasc_kseen`（`Rel/RepSeen.lean`：`kasc` 答出时，`kseen` 在其排好的列上
  不报错；所答由 `kseen_ok`、`kasc_grade` 给出）；runs 引理已有（`kseen_runs`，`RepSetOps`）；`Order.groupIds*` 已在
  92cbb31 等处删除，`kseen` 的调用者全走 kernel；doc §4 的 `seen` 行改写（`Order.idsBy` → `firstsBy`/`groupIn`，列出定律）。
  ✅ 已折叠（4e2420e；rq17f5 `Vals.sorted_key`）：`lexLe_congr_right`（`RepTabComp`）是 `lexLe_congr` 的特例，`nub_cover`/`nub_sel` 内联的
  `hkey` 即 `kasc_grade`。
  rq17f5（部分）：`nub_cover`/`nub_sel` 的 `hkey` 改为 `Vals.sorted_key`（`kasc_grade` + `asc_perm_grade`）；新引理
  `Vals.cols_wf`（`Vals.cols` 的每列 `Ext.Enc.WF`，由 `Arr.wf` 与 `.pos` 得）；`hN : n.toNat < 2 ^ 32` 加到
  `Vals.nub_*` 与 `Tab.canon_holds`/`ran_holds`/`dom_holds`；`kscatter_words` 加前提 `hasNul e = false`。
  ⬜ 阻塞（待决定）：`Vals.row` 在原子上读 `Arr.get`，null 行读到的是块的 top residual，`kgather` 之后是新块的，
  所以 `Arr.gather_row`、`Arr.eq_of_codes`、`Arr.codes_of_eq`、`Arr.get_raw_atom` 的 u1 界在有 null 的列上为假。
  ✅ `RepSeen` 引用 `kasc_grade`（rq17f7）、`lexLe_congr_right` 折叠（4e2420e）。
  rq17f6（部分）：阻塞按设计卡 "atom+1"（决定 K）解除：`Arr t n` 的类型带 `hasNul = false`（`Arr.plain`），`Arr.mk` 要它、
  `Arr.of` 判定它；`Arr.opt` 删除（无调用者）。新引理 `Verify.hasNul_of_nulAt`、`foRNul_of_plain`、`ofBytes_plain`、
  `bools_plain`、`Ext.Enc.blank_plain`、`colMap_plain`、`colPrefix_plain`；`kscan_closed` 多一项 `hasNul = false`。
  `Rel.Run.*` 与 `RepCanon` 全绿（`gather_row` 经 `kgather_plain`，u1 界经 `foRNul_of_plain`，`eq_of_codes`/`codes_of_eq`
  经 `nulCodes`/`nulWords` 在无 null 处化简）。⬜ 剩：`RepCols` 起的下游模块未建；`kscatter_words` 调用者传 `x.plain`；
  `hN` 调用者；✅ `RepSeen`/`lexLe_congr_right` 折叠（4e2420e）。in-band `V+1` 今天没有 `Obj` 情形，待设计。
  rq17f7（部分）：合并 9199fbf（`scatter.rs` 冲突：`ordered` 快路只在 `nul = None` 时走，因它不写 null 位）。绿：
  `RepCols`（`raw_scatter` 取 `x.plain`、`lastCount_eq` 取 `hN`、`wordsArr` 取 `hasNul_wordsFoR`）、`RepOrder`、
  `RepSeen`（`kasc_kseen` 引 `kasc_grade`，取 `hwf`/`hN`/列无 null；`ascCol_perm` 过 `noNul`）、`Gather`（`hnn` 删，
  用 `foRNul_of_plain`）、`RepCanon`（`Vals.cols_wf` 加"列无 null"合取）。✅ `lexLe_congr_right` 折叠（4e2420e：
  `RepTabComp` 引 `Rel.RepSeen`，:238 用 `lexLe_congr rfl e.symm`；dry-lex 查 index：`Rel/Rep*.lean` 无其他
  `_left`/`_right`/`'` 特例）。`RepSetOps` 未绿：缺 `kscatter_plain`（三种证法
  均在 `whnf` 超时，见 /data/tmp/rq17f7-handoff.md）；`union_holds`/`canon_sorted`/`canon_distinct` 已取 `hN`，其
  调用者（GenKFold、RepTabDiv、RepWFOps、GenKSpec、GenKHylo、RepAsc、RepSums、GenKFix）未改。
  rq17f8（部分）：合并 rq17f7（2c948e0），`kscatter` 保留 master 的 `readsDivisor` 拒绝在 null 搬运之前。
  `kscatter_plain`（每个 op：`e` 无 null 则答案无 null；先把 `hasNul e` 改写为 `false` 再 split，不再 whnf 超时）；
  `foRNuls_plain`（无 null 的 WF 列每行 flag 为 0）。`kasc_grade` 改取 `N < 2^32 ∨ 各列无 null`：`canon` 排序的列都来自
  `Vals.cols`，都无 null，所以 `hN` 从 `Vals.sorted_key`/`nub_*`/`canon_*`/`ran_holds`/`dom_holds`/`union_holds`/
  `kasc_kseen` 删去（`R.comp S` 内部的 union 无从给出行数界）；`select_ok` 直接引 `kasc_grade`。`scatter_add_count`、
  `scatter_last_at`、`kgather_word` 取 `hasNul e = false`。`lexLe_congr_right` 折叠完成。绿：Closure、RepCanon、
  RepSeen、RepSetOps、RepTabComp。⬜ 剩：`RepTabDiv`（`kgather_word`/`scatter_last_at` 的源列无 null 证明，见
  /data/tmp/rq17f8-handoff.md），其后 GenKBits、GenKFix、RepBits、RepSums、RepWhere、RepStruct、RepTabArith、DfnLaw、
  GenKFold、RepAsc、RepWFOps、GenKSpec、GenKHylo 未建；`colMap_plain`/`colPrefix_plain` 折入 `_closed` 未做。
  ✓ 其后各模块已绿（rq17f9–f12，6f58d7f）：RepTabDiv、GenKSpec（`BitsWf` 加 `hasNul o = false`）、GenKBits
  （`kbitrows_plain`，gather 链取无 null 的 index）、GenKFix、GenKFold、RepSums、RepWhere、RepStruct、RepTabArith、
  DfnLaw、RepAsc、RepWFOps、GenKHylo。`Arr.lexLe_i64` 不需要改述：决定 K 下 `Arr t n` 的类型自带
  `hasNul = false`（`Arr.plain`，rq17f6），null 只在 `t+1`，所以 `nulCodes` 在 `Arr` 列上就是码本身。新引理：
  `expand_plain`（RepTabComp，EXPAND 的偏移列无 null）、`Tab.sumTail_plain`（RepSums，bad 列无 null）。
  决定 F 已落地（5617318，2026-11-19）：上面的 "引擎" 一句作废。`kseen` 在乱序行上报固定错误（指出第一处乱序的行），
  `seenEngine`/`keySpan`/`foRBounds` 与 Rust 的 `seen::direct` 删除（`Seen.lean` 74 → 32 行）；新引理 `kseen_sorted`。
  未做：1024 行块边界只有 Rust 测试，Lean 例子因 `decide +kernel` 归约不动而缺（与决定 C 有出入）。
  已诊断（seen1024，2026-11-22）：不是 `Sum` 的可判定实例，是答案的编码器。每个 kernel 的答案经 `wordsFoR` →
  `Coc.encode`，kernel 归约的是 `encodeAt 10` 的 Lean 体：`planOf`/`frameAt` 对每个候选 frame 在整块上算 `npatch`
  （每个宽度块内平方），`keyAt` 读 `pushBits` 建的 `ByteArray`（kernel 里是 list）。实测 `wordsFoR` 往返全零列：
  10 行过（峰值 RSS 1986 MB，即 import 基线），20 行过（2370 MB），40/70/100 行在 4 GB 地址空间下 OOM；只编码
  40 行就超过 6 GB（RSS 4945 MB，24 s）。所以跨块边界（≥ 65 行，即使输入用 2^6 的块）的 `decide` 例子都放不下；
  要有，得先把 `encodeAt` 的 spec 改成 kernel 能便宜归约的形式（frame 搜索不做块内平方、读字节不走 list）。
  🔶 cocspec（2026-11-22）：frame 搜索已线性——`planOf` 每块用结构递归的 `sortBy` 排一次序（core 的 `mergeSort`
  是良基递归，kernel 归约不动），`frameOf` 一遍扫过、两个前缀指针数每个候选 frame 的 patch；输出与旧体逐位相同
  （600 个随机块、36189 个 key、w = 1/8 差分 0 处不同；全部 kernel 测试原样通过）。`planOf` 300 个不同 key：旧体
  4 GB 下 abort，新体 6.2 s / 2553 MB 过。但 1100 行例子仍放不下，剩三处与搜索无关的 kernel 代价（4 GB 地址空间）：
  (a) 按下标读 list 背的 `ByteArray` 每次 O(i)：`keyAt` 读 `pushBits` 建的 40 行 abort，读平铺 list 的 300 行
  abort；顺序解 1100 行只要 1.0 s——`encodeAt` 的 `keyAt`/`bitAt nul` 要改成按块顺序消费字节（连带重证
  `foRBits_encode`、`foRWF_encodeAt`、`nblk_encode`、`wordsFoR_closed`、`raw_encodeAt`、`lgAt_encodeAt`、`foRBytes_wf`）；
  (b) `(Array.range m).map f`（`blockOf`/`planBlock` 建 `ks` 的写法）300 个就 2260 MB；(c) 解码侧 `raw`/`foRBits`
  逐元素按下标读：用编码器给出的 1100 行全零元数据（平铺字面量、空 pack）单独解码，40 行 1.2 s，1100 行 OOM。
  另：一个 1024 key 的块单是 `planOf` 在 8 GB 下也 abort（33 s），kernel 每步留在 whnf 缓存里的内存是下限。
  ✅ 关闭（owner 2026-11-22，决定 S）：1024 行块边界由编译执行的 `#guard` 对 Rust 检查，`decide` 只覆盖小输入；
  不改 `encodeAt` 的读法，也不另写无 extern 的模型副本。
  ✅ 运行路径上的平方解码（nodecode 765527b）：`foRBits` 每个元素重算 trailer 偏移 O(nblk)，`Vals.cols` 为判形状解码整列；
  改为 `foROk` 判形状、`foRExc`/`foRFrame` 取 `blockStarts` 的 trailer；10⁵ 行 leftJoin 40.2s→0.96s、带 null 的 group-by
  187s→1.54s；`make decode` 列出仍可达 `foRBits`/`alpBits` 的编译定义（`decode-allow.txt`，150 个，余为单元素读与 u1 位图）。
  ✅ decode 门（决定 G）：`decode-allow.txt` 中的名字是 `irReach` 的叶子（到达但不展开），只有一条不经任何白名单名字的路径
  通向 `foRBits`/`alpBits` 才被标出；白名单里不再自己到达解码器的条目（或已不是 RelRun 编译定义）算 stale 并使门失败。179→9 个。
- 🔄 D.13 `sums`（dataframe 请求，q 的 `sums`，分支 `sums`）：prim 行 `sums : κ×ν ⟶ γ ↦ κ×ν ⟶ γ`，key 在源对象里，
  每个 key 内按位置升序的左 fold 前缀和，溢出或 null 之后该 key 余下的行无像。含义（`rowDens`）是
  `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)`（`Den.lean` 的 `sumsDen`）。
  ✅ 已落地：`Tab.sums`（`Rel/Run/SetOps.lean`）只用 `kseen`、`kscatter`、`kscan .add`、`colMap`，无新 kernel，不解码；
  非 simple 的 x 报错并指出位置；`TestSums`（含 10⁶ 行：10⁵ 约 10 ms，10⁶ 约 55 ms，线性）；doc §4 行；
  `segScan_ok`（`RepSetOps`）：分段 `kscan` 在每行给出本组到该行的 fold，`groupFold_ok` 改为引用它。
  ✅ `Tab.sums_holds`（`Rel/RepSums.lean`）：`Tab.sums x = .ok T → rep T = sumsDen (rep x)`，无前提；该行已进
  `kernRows` 与 `rowsProved`（`("sums", no)`，`rowOK_sums`），`gen_sound` 不加前提；程序里写 `sums(x)`
  （`x : N×N ⟶ N`）走 kernel，`TestSums.sumsP` 以 `check` 验分组、单 key、负数、溢出、null。
  ✅ 位置 ν 与值 γ 是两个对象（分支 `sumsG`）：原先签名里两者是同一个变量 `ℕ`，所以 `x : K×P ⟶ N` 报
  "found N, expected P"；运行、`sumsDen`、`Tab.sums_holds`、`rowOK_sums` 都在存储层（`.long`）上，本来就不限
  γ = ν，无需改。γ 是 `plus` 所接受的数对象（存为 i64，`Prim.num`、`Elab.numObj` 与 `plus` 同一检查）；
  i32、f64 等对象被拒："sums on I: I is an object of i32, and sums runs on objects of i64 only"
  （`TestSums.sumsPN`、`sumsI`、`sumsF`）。窄整数 γ 要等值算子支持窄整数。
  ⬜ 未做：`Prim.dfn` 条目（上面的组合式）等 dfn 能读行的关系参数（与 `asc` 相同）；`Plan.ofTm` 没有 prim 的
  recipe，不需要加。
- ✅ df-F7 宿主函数（`dataframe-design` F7）：任意 Haskell/Lean 函数不进入程序（那是原语之外的不透明 kernel）；
  元素函数是程序里的 Rel 定义，作为关系参数传给 `frame` 的库定义 `lift(f, c) ≜ c f`、`lift2(f, a, b) ≜ ⟨a, b⟩f`、
  `apply(f, a, b, x) ≜ x ⟨lift(f, a), b⟩`、`bind(f, c) ≜ c [f, inr]`、`nullLift(f, c) ≜ bind(f inl, c)`、`nullLift2`
  （任一列为 null 即 null）。测试 `Rel/Lang/TestFrameLift.lean`（无参、带参 `atLeast(m)`、部分的 `f`）。
  未覆盖：DataHaskell 用列名指定 `apply` 的目标列（这里 `a` 取列、`b` 是保留的列，替换的列放在最前）。

### typed base objects（`/data/tmp/typedbase/design.md` §7：float `arith`/`div`、`sqrt`、`date` 上的 `minus`）

- ✅ S0 fork A，每个 constant 自己的 placeholder（分支 `tb-s0`）：`Once.ph = placeholdersOf env.objs`，即 `varAtoms`
  中没有任何作用域内对象存储在其上的 atom；`Obj.inst ph σ`、`Tm.instObj ph σ`、`callTm … ph`、`Pre.call … ph`。
  `.long` 不在 `varAtoms` 中，所以任何 `ph` 都保持它（S3 起由 `fixed_ok` 读出，不加前提）。变量多于 `ph` 时 `once` 报错并给出定义名。
- ✅ S1（分支 `tb-s1b`）`obj F : t` 声明存储在 atom `t` 上的对象：`ObjDef.num (t := .i64)`，`objInfo` 给
  `obj := .atom t`。atom 名只有一张表 `atomNames`（`Syntax.lean`），由 `QAtomicType` 的构造子生成，名字即构造子名。
  能声明的 atom 是 `litLayout t`（`Kernel.ascLayout` 去掉 `u1`）有值者：`u8 i8 i16 i32 i64 f32 f64 char date
  datetime`；`sym`、`general`、`u1` 和未知名字在解析时报错并列出可用 atom。`obj N` 不变（i64）。`numU` 在非 i64 的
  声明对象上报错并给出 atom（`+`、`<` 等留给 S3）；`code` 不再把非 i64 对象当 i64。
- ✅ S2 float 字面量：整数，或 Lean 的 scientific 字面量（`2.5`、`1e-3`、`1.5E10`），可带紧贴的 `-`；没有 NaN 或
  无穷的写法，舍入为无穷的字面量报错。一个字是否属于某对象只有一条规则 `ObjInfo.member`：命名元素、range 内的数，
  或数对象（`obj N` 即 i64 在内）的 atom 上 `Elab.wordAt` 读得出；`holders` 由它决定字面量的对象，没有对象接受时
  `refusals` 给出每个对象拒绝的理由（i64 对象上的 `2.5`：`'2.5' is not an element of N, an object of i64`）。
  `code` 的数对象分支也经 `wordAt`（i64 查范围）。产生 float 字的地方规范化（决定 G）：`-0.0` 读成 `0.0`；判断谓词
  `Rel.QAtomicType.nonCanonical t b`（`Rel/Kernel/Value.lean`，f32/f64 上 NaN 或负零，其余 atom 为 false），合并时
  `Rel.Lang.Table.nonCanonical` 由它定义。打印 `Elab.floatText`：能读回同样位的最短十进制，首位数量级在 `[-7, 21)`
  时用带小数点的普通写法（`2.5`、`-0.00000015`、`15000000000.0`），否则 `1e-8`、`1e21`。object 变量多于 placeholder
  时调用处报错（`Expand.placeholdersFor`）。测试 `Rel/Lang/TestFloatObj.lean`；GenSoundTest 1235/1235。
- ✅ S3（分支 `tb-s3c`）`Tm.arith t k`、`leq t`、`lt t` 以 atom 为下标：`stepAt t k`、`ltAt t`/`leAt t`（i64 上为
  `Int64` 的，f32/f64 上为 IEEE 的，读 `fval` 给出的 f64 字），运行侧 `stepColsAt`、`cmpOn (ordOp s t)`，定律
  `Tab.arith_holds {t}`、`cmp_sound`/`arith_sound` 对任意 atom 一条，i64 是其实例。PLAN 未定的部分映射已决定：
  `0/0` 与 `1 mod 0` 无行（IEEE 答 NaN）；`x/0` 与溢出保留 ±∞；`−0` 写作 `+0`。float atom 上的 `div` 是 q 的向下取整
  除法。`convTm_instObj_den` 的 arith 情形用 `fixed_ok`/`back_ok`（任意 `X Y`：`σ` 保持对象时节点即 `t` 本身沿该等式
  移动），代替 `fixed_long`/`fixed_arith`/`back_long`，因为 f32/f64 在 `varAtoms` 中、`Obj.inst` 不归约。途中修正两个
  运行代码错误：`colMap` 不论列的 atom 都按 i64 读输入（现在带输入 atom `s`）；`wideCol .f32` 误读 f32 字节。
- 🟡 S4（分支 `tb-s4`）序不需要算术：`QAtomicType.ordNum` 给出有序 atom 的存储数类型（数 atom 自身，`char` 为 `u8`，
  `date` 为 `i32`，`datetime` 为 `i64`），`<`、`≤` 在每个有序 atom 上运行：i64/f32/f64 照旧，其余为 `iordAt`，即存储值
  经 `Op.cast r .i64` 加宽后的 `Int64` 序（`wideCol`、`ordOp`，定律 `iord_iff`、`castWord_ofBits`）；`max`/`min` 在没有
  值算子的有序 atom 上是组合 `τ(≤)π₂ ∪ τ(>)π₁`（`Elab.build`），在 i64/f32/f64 上仍是融合的 `arith`。以 `.long` 读对象
  变量的行在 `Prim.num` 中声明它（`length`、`sum`、`positions`、`asc` 的 `ℕ`，`sums` 的 `ℕ` 与 `V`），在其它 atom 上按名
  报错；常量不泛化的对象变量在 `callTm` 中先检查，`cumSum(f)`（f64）不再报 internal。未做：float 上的 `sum`/`sums`
  （右折叠与逐块扫描在 float 上结果不同，需裁定求和顺序）、`sums` 的位置对象为任意有序 atom、行 `sqrt`。
  S4c/S4d（分支 `tb-s4d`）：`sums` 的位置在每个以整数存储的有序 atom 上运行（`QAtomicType.intOrd`、`Prim.ord`、
  `leAt t`、`Tab.sums_den`），f32/f64/sym 位置按名报错；`aj` 在 `date` 时间列上运行（`TestFrameTyped.ajDateT`、
  `sumsTimeT` 钉住手算的行）。float 的 `sum`/`sums`（owner 裁定：自左向右）未做：f64 可由一次 `kscan .fadd` 精确算出，
  f32 不能——`stepAt .f32` 每步舍入到 f32，而 `kscan` 每行只折一个 `Op`，在 f64 上累加再舍入一次结果不同
  （2^24 + 1 + 1）；需 owner 裁定：加 `Op`、改 f32 的含义、或 f32 仍报错。库调用 `cumSum(f)`、`sumsBy(g, f)` 在 f64 上
  已是具名报错，不再是 internal。（f64 的 `sum`/`sums` 已由下面 S4e–S4g 做完；f32 见 fsum。）
  fsum（owner 裁定 2026-11-22，选项 B）：float atom 一条规则——每个元素加宽到 f64，在 f64 上左折叠 `⦇0, fadd⦈`，
  结果舍入一次到值 atom `V`，结果对象仍是 `V`（`Lang.fsumDen`/`sumDen`，`sumAt`、`sumsDen` 都读它）；`sums` 的每个
  前缀值同样是 f64 累加值舍入一次到 `V`。f64 上舍入是恒等，结果不变；i64 不变。运行：`sumTailF`，一次分段
  `kscan .fadd`，`pre (widen V)`、`post [fto V]`（进位是 `post` 之前的 f64 和），该行值为 `2^63`（NaN）即坏步；
  旧 f64 的 `−0` 报错去掉（`fto` 已把 `−0` 写成 `+0`，与 `froundDen` 一致）。`sumAtoms = [i64, f32, f64]`。
  universe 路径：定义 `⦇[0, plus]⦈` 每步舍入，与 `sumDen` 在 float atom 上不同，`DfnCut.sum` 要求 `t ∉ floatAtoms`
  （`DfnLaw.sumDen_fold`）。测试 `TestFrameTyped.sumF32T`（f32 `[2^24, 1, 1] → 2^24+2`）、`sumF32T2`
  （`0.1 + 0.2 → 0x3e99999a`）、`sumsF32T`（前缀 `2^24, 2^24, 2^24+2`）。
  S4e/S4f（分支 `tb-s4e`、`tb-s4f`，owner 裁定：float 求和自左向右，q 的顺序；f32 按名报错并给出 `$` 到 f64 的提示）：
  `sums` 的值对象为 i64 或 f64（`sumAtoms`）。`Tab.sumsOn` 对值 atom 泛型：f64 上一次分段 `kscan .fadd`（种子 `+0`），
  `W' = fto W`，`W' ≠ W` 或 NaN 为坏步，`−0` 报错，分段 `kscan .or` 传播后 `keep`。`sumsDen`/`sumsAt K P V` 泛型；
  定律 `stepF_word`、`sumsF_fold`、`sumsF_holds`、`sums_den`（无 sorry）。测试 `TestFrameTyped.sumsFloatT`（手算
  `(1, 1e16, −1e16) → (1, 1e16, 0)`）、`sumsF32T`，`TestFrameStat` 的 f64 `cumSum`/`sumsBy`。
  S4g（分支 `sumL`→`sumL2`，owner 裁定 C）：`sum` 的定义在每个 atom 上是左折叠 `⦇[0, plus]⦈`（i64 也改为左折叠）。
  `RowCode.sum` 为 `(.arr σ₁, σ₁)`，含义 `sumAt V`（`foldDen (· = ofBits 0) (stepAt t add)`）；`Tab.sumOn` 与
  `sumsOn` 共用 `sumTail`（`Rel/Run/SetOps.lean`：分段 `kscan .add`/`.fadd` 与坏步）；定理 `sumTail_fold`、
  `Tab.sum_holds`（任意 `V`：`T.Holds xs c ↔ (∃ i, X.row i = xs) ∧ sumAt V xs c`）、`runScan_ok`、`seenSeg_ok`；
  `rowOK_sum` 用 `Tab.sum_holds`。测试 `TestFrameTyped.sumFloatT`（`1, 1e16, −1e16 → 0`）、`Kern45.sumFold`
  （`3 3 −3` 的中间和 6 ∉ `−3…3`）。
  分支 `sumL3`（owner 裁定 B）：`DfnCut.sum`/`dfns`/`zeroTm` 在任意有序 atom `t` 上，`.arr (.atom t) ⟶ .atom t`，
  步 `.arith t add`；基 `0` 是 atom 的字面零字 `ofBits t 0`（`zeroCol`：一行 `wordsFoR #[0]` 的 `uni`，
  `ran(u {0})`），不再是 `⟨𝟙,𝟙⟩ minus ∩ 𝟙`，故无需浮点减法的事实。`Tm.dfnCut_den` 对任意 atom 成立：universe
  `P : B.El → Prop`，`Seg B P`（`i64` 上为 `InitSeg`，其余 atom 为 `False`）；`plus_iff`、`zeroTm_den`、`zeroCol_row`、
  `Prim.den_sumRow`、`Prim.den_mapRow_corefl` 泛化，无 sorry。`build`：没有 universe 的对象变量（非 `num`）上，
  定义需要 universe（`DfnCut.uni`）的行报错而不再跑未截断的融合行；占位 atom（无字面 `0`）上 `dfns` 无形式，
  所以含 `sum` 的泛型常量留在 `.long`（`Expand.once`），f64 上的 `sum` 只在单态处跑。
  分支 `sumgen`：这不是缺口。对象变量 φ 上的 `sum`（`sumT(x : ν ⟶ [φ]) ≜ x sum`、经另一泛型定义的 `sumN`、
  `avgS : [φ] ⟶ φ ≜ ⟨sum, length $ φ⟩%`）在 f64、i64、universe `0…5` 的对象上都得到手算的行
  （`TestGenericNum.sumGT`）：常量对 φ 不泛型时，调用在调用处对象上展开（`Pre.call` 的 `alt`），`build` 在已知
  atom 上选 row 与 universe 截断，对每个 `dfns` row 都如此，无需改代码。仍报错的是 `devG : [γ] ⟶ φ ≜ varG sqrt`
  （dataframe request 11）：`sqrt : F ⟶ D` 的 `F` 与 `D` 无关，`varG` 的 φ 是类型与参数都够不到的开放对象，
  按设计文档 §1（`Elab.generalise`）取 `.long`，`divide` 在 i64 上报错。改它要定一条开放对象取 atom 的规则
  （例如取每个作用在它上面的数值运算都接受的 atom），与设计文档现文冲突，待 owner 裁定；写 `varG 𝟙(φ) sqrt` 可用。
  分支 `rq1213`（dataframe request 12、13）：泛型体里的浮点字面量也先开放（`litTy` 用 `numParts`），`numCheck` 在每次
  使用的对象上读字面量的词（`litCol`，与 `code` 一起移到 section Num），`deferred` 变量上 `code` 不读码；体里写的、
  没有使用够得到的字面量对象在定义可见的对象里定（`mkDef`）；`callDef` 在实参里仍有字面量 / `nil` 开放对象时不选形式。
  13 的原因不是 φ：实参里 `{(∗,0)}` 的对象在选形式时仍开放，单态的 `{(∗,0)} $ F` 在有 ν、γ 的定义里同样失败。
  `quantile` 的 0、1 写成 `{(∗,0.0)}`、`{(∗,1.0)}`；测试 `TestGenericNum.litGT`、`litGN`、`sumLitT`。
- ✅ S5 float 上的 `Obj.key = ordCode`；`key_ordCode`、`ascBad`、float 上的 `LamLaw`（分支 `s5`）。代码部分已在
  `tb-s5`（见决定 G）。`LamLaw` 不再是前提而是定理：`Vals.lt_of_codes`（`Rel/RepOrder.lean`）——在 `kasc` 读得了
  每一列（`ascCol` 有答案）的任何 side 上，行的序码（`seenKey`）字典序在前，则元素 `Obj.lt` 在前：atom 由
  `Obj.key_ordCode`（float 在内），pair、sum、array 逐列对应 `Obj.key` 的各部分（`lt_prod`、`lt_inl`、
  `lt_inl_inr`、`Obj.lt_arr_of`，cell 的块由 `flatMap_range_lt` 取第一个不同块）；`Vals.lamLaw` 是 `Λ` 的序律。
  `kasc` 拒绝 `sym`、`general`，所以无需对象条件。`lam_den`、`E_den`、`setify_den`、`tau_den`、`thin_den`、
  `asc_holds`、`tails_den`、`inits_den`、`GenK.lam_sound`、`GenK.thin_sound` 去掉 `hB`；`def LamLaw` 删除，
  `Tm.LamLaws` 在 `Λ` 处什么也不问（只剩不动点体正，即 `Tm.monoOK`）。✅ 清理（分支 `s5clean`）：`Tm.LamLawsAt`
  的参数 `L`、`Tm.LamLaws`、`Tm.LamLawsAt.mono`、`rowsProved` 的 object 函数（现为行名 `List String`）、`RowOK`
  与 `rowOK_args`/`rowOK_of`/`primGen_ok` 里只带 `L` 的前提一并删去；`gen_sound` 的前提是 `Tm.GenHyp P`（不动点体正，
  `share` 处 `P`，即 7.3b 的 `η.sh.Shares`），`P` 取 `True` 时等于 `t.monoOK = true`（`Tm.monoOK_iff`）。
- 🟡 S6 行 `$`（分支 `tb-s6`，owner 裁定 J）：`x $ F` 与 `QAtomicType.embed s t` 的图复合（`castDen`），部分映射、不舍入；
  允许的对由 `castOK` 从两个 atom 的格式读出（加宽、整数 → 浮点）；有损方向在 elaboration 报错。`Tab.cast`（分支
  `tb-s6c`）是编码列上一次 `scan` map（`Op.cast s t`，无像写 null 字 `2^63`）+ `colMap .ne` 标志 + `keep` + `canon`，
  不在 `castOK` 中的对报错。定律 `Tab.cast_holds`（无前提，已证）、`rowOK_cast`、`embed_canonical`（全部输入）、
  `ofBits_word`；`Table.nonCanonical` 由 `QAtomicType.nonCanonical` 定义。测试 `Rel/Lang/TestCast.lean`。未完：
  `Rel/Lang/EmbedTest.lean:46` 的 `𝟙 $x` 现在被读成 cast 行，报 `expected a term` 而不是 antiquotation 错误（待裁定）。
  S4b（分支 `tb-s4b`）：没有数 atom 的有序 atom（`date`、`datetime`、`char`）持有其存储字所计的数，`storeFmt?`
  即其 `ordNum` 的格式（`date` 为 1970-01-01 起的 `i32` 天数）；`value`/`ofValue`/`castOK` 都读 `storeFmt?`，同一条
  规则给出 `date → i32/i64`、`datetime → i64`、`i32 → date`、`i64 → datetime`（`i64 → date` 是收窄，报错）；两个各有
  单位的 atom 之间不 cast（`date ↔ datetime`）。Rust `cast_word` 把 `char`/`date`/`datetime` 的码读作 `u8`/`i32`/`i64`，
  无新 op、无新导出。`Tab.cast_holds` 仍是一条（前提改读 `storeFmt?`）。`daysBetween` 是 `⟨a $ N, b $ N⟩minus`，按 S8
  留给 dataframe 库；`minus` 在 `date` 上仍报错（`TestFrameTyped.daysCastT` 钉住组合的行）。
- ✅ S7 `Op.cast s t`（`Op` 的最后一个构造子，带两个字段）：`kscan`/`kscatter` 以 `@& Op` 传对象，Rust `cast_word`
  （`CAST = 46`），无新导出；`Reg Op` 按对象传（`nullOps`）。所有数值对一个构造子，不只 `i64 → f64`。
- 🔄 df-F3 字符串（dataframe F3）：`Rel/Programs/Frame.lean` 加库定义 `splitOn(s)`（q 的 `vs`，左 fold，最后一段以 `s`
  结尾时切开，多字符分隔符同一条定义、取最左不重叠的匹配）与 `match(T, q, A) ≜ dom(⦇[q, T]⦈ A)`（`T` 是转移关系，
  DFA 或 NFA）；无新行、无新 kernel；测试 `TestFrameText`。⬜ `parseDate` 停：`(y, m, d) ↦ 天数` 只在 Lean 的
  `Db.Csv.daysFrom`，Rel 无此行，待 owner 选行 `ymd : [C] ⟶ D` 或 Rel 中的公式副本；⬜ `matchAll`；
  ⬜ 字面量中单字符 `"0"` 在 `char` 位置读成文本 `[C]`（Elab 的字面量读法）。
- ⬜ S8 库定义 `mean` `stddev` `correlation` `skewness` `zScore` `valueProportions` float `describe` `daysBetween`
  （dataframe 会话）。前提：
  - ✅ 真商 `%`（q 的 `divide`，分支 `fdiv`）：`arith` 族的又一个值动词 `Ew.divide = 3`（q 的动词号），`fverbBy` 中为
    `fdiv`，`stepAt`、`fstepCols`、`arith_sound` 不变即覆盖它（`fverbBy_map` 多一个情形）。名字 `divide` 与 `%` 都在
    `Op.table`，`%` 是一个字符的符号名，不改词法。只在 f32/f64 上；在整数对象上按名报错，提示先 `$` 转换
    （`numObj`：没有整数 step 的动词在整数 atom 上都如此；未声明 atom 的对象按 `i64` 一样检查）。`x % 0.0` 为 ±∞
    （值），`0.0 % 0.0` 无行（NaN）。测试 `TestFloatArith.divideT`、`divideIntT`。
  - ✅ `sqrt`（分支 `fsqrt`）：一元 float 动词是 `prims` 行 `F ⟶ F`，一族一个实现：`unaryOps`（`Rel/Run/Cast.lean`）
    列出 q 名与 `Op`：`sqrt neg abs exp log sin cos tan asin acos atan floor`，每个都是已有 Lean body 与 `#guard`
    的 `Op`，无新 Op、kernel、导出。`Tab.unary s`（`wideCol` → `colMap o` → `ftoCols`：`Op.fto t` + 非 null 标志，
    与 `fstepCols` 共用）+ `keep` + `canon`；语义 `unaryDen o`（`fval`、`o.eval 0`、`fto`、非 `2^63`）。定律
    `fmapCols_spec`、`Tab.unary_den`、`rowOK_unary`；`keep_canon_holds` 是 `$` 与本族共用的"列映射后滤去 null"，
    `cast_holds` 由它导出。`kernRows` 的项是常量加其前置参数（`Tab.unary` 带行名）。`Prim.num` 改为对象变量 →
    允许的 atom 表（`intAtoms`、`floatAtoms`），整数对象上按名报错并给出 `$` 提示（`numObj`）。`floor` 后改为
    `F ⟶ D`、`D` 为 `i64`（见下一项）。测试 `TestFloatArith.unaryT`、`sqrtIntT`。
  - ✅ 一趟 element-wise（分支 `kchain3`，批准 A）：`kscan` 带每行 Op 链 `pre`/`post`、`seg : Option Enc`（`none`
    即 map），只改签名、无新导出。`fverbOne k`（动词 = 一个二元 `Op` + 一元链；`mod` 无，仍多趟）定义 `fverbBy`；
    `widen t`（`wideCol` 的链）、`fstepArr`（`colArr o … (widen t) (c ++ [fto t])`，一趟）、`nanFlag`（`post` 链
    `ne nulWord`，一趟，无 `colConst`）；`fmapCols` 一趟。`Tab.unary`/`Tab.cast` 在 `keep` 后不再 `canon`
    （`keep_map_holds`）。native plan 的 `scanB` 读 `Option`，map 不再造常量 `1` 列。一元行改为 `F ⟶ D`：
    `unaryOps` 每行带答案 atom（`floor` 为 `i64`，同 q；其余 `f64`），`prims` 的 `num` 为 `F` float、`D` 该 atom；
    链尾 `Op.ofF64 u`（float atom 用 `fto`，保留 `±∞`；否则 `cast f64 u`，NaN、`±∞`、越界为 `2^63`，由
    `nanFlag` 滤去，`#guard` 钉住）。`unaryDen o A B`、`Tab.unary : Tab A B`、`nanFlag_spec` 在任何数 atom。
    sqrt 10^6 行（最好一次）：f64 4493 → 762 µs，f32 5322 → 1279 µs。
    ✅ perf11f（3da3cb3，合入 7543bb6）：常量除数的 `rdiv`/`rmod` 作 `kscan` 链的 `post` 步（`Op.rdiv/rmod`，`kscanRefuses`，
    `kscan_post_ok`）；`Bench.Blocks` 的 scan 90950 不变、scatter 87334 → 85987；`Bench.Edit` 的 scan 179437 → 179371、
    scatter 67148 → 66482；wall 1031 → 985 ms（Blocks）、1319 → 1199 ms（Edit）；`Bench.SudokuPC9` scan 3414、scatter 3970、wall 27.5 s。
  - 🟡 float `sum`/`sums`：`mean`、float `describe` 需要它。`sums` 取 i64 或 f64 值（S4e/S4f），f32 按名报错；
    f64 `sum`（格）已落地（分支 `sumL2`）。
  - ✅ 对象变量上的数动词与 `$`（分支 `objvar`，dataframe 请求，architecture §1）：泛型定义的体可写自己的对象变量
    （`x $ φ`，`Parse.S.ovars`、`Env.ovars`）；数动词与 `$` 在对象变量上的检查（`Elab.numCheck`）留到每次使用：
    `Expand.once` 在全 `.long` 建不成时以 `ObjInfo.deferred` 建一次只作判定，成则定义无常量；无常量的定义、以及给
    非泛型变量非 `.long` 对象的调用，都在调用处对象上建展开（单态化，代码生成前实例化，`rowOK` 只见具体 atom）。
    `mkDef` 在使用解出变量后先跑 `numCheck`，错误写出调用、变量与对象。库可以对数对象泛型，不必自己声明 `F`/`Z`/`D`。
    测试 `TestGenericNum`（`avg` 在 f64 上运行、在 i64 上于调用处报错；`daysBetween` 在用户的 `date` 对象上运行）。
  - ✅ 体里开放的对象（dataframe 请求 9，分支 `len9`）：定义的体留下的、类型与参数够不到的对象（`length $ F` 的 ℕ）
    是该定义的隐式对象变量 `n#i`（`Elab.generalise`，let 泛化），每次使用都在 `.long` 上，数检查照常；`check` 里
    仍报错。测试 `TestGenericNum.lenT`（`length $ F`）、`wsumT`（`positions(p) sum $ ψ` 的 ℕ）、
    `openCheckT`（`check` 里仍报错）。
  - ✅ 只在结果类型里的对象变量（dataframe 请求 10，分支 `rq10`）：类型含对象变量的定义无论有无参数都是泛型
    （`Expand.read` 不再把无参数的泛型定义当常量体），每次使用由期望类型实例化（`mkDef`、`callDef` 的合一）；使用
    返回时变量未解的，其数检查记入 `St.uses`，在项 elaborate 完（`settleOpen`、`generalise` 之后）由
    `Elab.settleUses` 在实例上跑；无物固定的变量报错，写出变量、定义与使用处。测试 `TestGenericNum.avgGT`
    （`avgG : [Z] ⟶ φ` 在两个 f64 对象上）、`avgGOpen`（`print x avgG` 报错）。
- ✅ df-F6b 输入格式（dataframe F6）：TSV 是 CSV 换分隔符，不是第二个读写器。`csvRead`/`csvWrite`（Lean 模型与 crate
  导出 `qlean_csv_read`/`qlean_csv_write`）多一个 `sep : UInt8` 参数，`Csv.dialect` 拒绝 `"` `\r` `\n`；读后写回的定理
  `csvWords_csvText` 对每个分隔符成立。程序里写在声明文件处：`input x : N ⟶ S from csv '\t' "f"`、
  `output x to csv '\t' "f"`，不写为 `,`（`Decl.input/output` 的 `csv : Option UInt8`，`Io` 的 `csv : Option (UInt8 ×
  CsvCols)`）。测试：`TestTable` TSV 往返（含 `,` 的字段不加引号、含 `\t` 的加引号），`TestFrameApp.tsvApp` 程序往返，
  crate `records_as_the_model` 的 `\t` 用例。parquet、JSON 不做（owner 决定）。`test/disabled/CsvTest.lean` 已停用，未改。
- ⬜ S9 文档：architecture §1、§4.3，dataframe F4，PLAN（随各步）。

### P0 baseline — 1/1

- ✅ 0.1 建 index，`make check` 定 baseline：compile-diff 241 个 definition，25 个 not ok。

### P1 删除 `Syn` — 3/3

- ✅ 1.1 `Tm.Ax` 写成等式 `⟦lhs⟧ = ⟦rhs⟧`。
- ✅ 1.2 删除 `Rel/Lang/Syn.lean`。
- ✅ 1.3 freyd 一侧删除 `relaop/RelAop/Syn.lean`。

### P2 不依赖 `Rel` 类型 — 6/6

- ✅ 2.1 `refold` → `hylo`。
- ✅ 2.2 `flatDen` 是一个复合。
- ✅ 2.3 `foldIDen` 是一个 `foldDen`。
- ✅ 2.4 elaboration 时的 positivity 错误，错误信息写出变量名和位置（9d9c061）。
- ✅ 2.5 对称除法的含义。
- ✅ 2.6 分析：28 个 prim row 能否写成 fold/hylo（不编辑）。

### P3 `Rel` 类型 — 11/13（在分支 `rel-lazy` 上串行；phase gate 通过之前不动 master）

- ✅ 3.1 结构 `Rel.Rel` → `Rel.Tab`。
- ✅ 3.2 `CRel` 是 `Option (Tab A B)`（90e753d）；与 3.3 合于 `rel-lazy` bee2ce2，`make check` 通过，241 / 25。
- ✅ 3.3 `Known`、`Rel`（`tab | lazy`）、`Reps`，新文件 `Rel/Run/Lang/Lazy.lean`（3a00d75，`rel-lazy`）。
- ✅ 3.4 新旧函数类型之间的桥（891dee8，`rel-lazy`）：`Gen.Fn.toRel`，`Gen.Sound.reps`。owner 选 Q4 = A：`Reps K` 只在 `K` 两侧之内比较
  （`K.dom ≫ rep t ≫ K.ran = K.dom ≫ T ≫ K.ran`），`Reps` 以 `K` 为参数，同 `Rel.run`。
- ✅ 3.5 `Gen.Fn d A B := Rel A B`（phantom `d`）：叶子（8ee7433，`rel-lazy`）。组合子暂由 `Fn.ofDem`/`Fn.at` 包旧体；
  `Sound f T := ∀ K, f.Reps K T`，旧谓词留作 `KSound`。
- ✅ 3.6 二元和一元组合子（3.6a 9fe7e30 组合子经 `compT`/`lift1`/`lift2`；3.6b 8c4fed0 行与叶子引理；合并 f4b0e42）。
  `comp` 不再对 `R` 的结果做 `ranC`，`S` 直接拿 `R` 的值列。
- ✅ 3.7 fold 和不动点（d1a45f0）：`foldr fold foldI flat hylo juncD` 是 `ofVals` 叶子，`nu nuAC mu` 是闭合体的 `.tab`；
  `onNodes` 分 tab/lazy 两种。`Fn.ofDem`、`Fn.at`、`KSound`、`Sound.at` 仍有调用者，3.12 删。
- ✅ 3.8 `Compile`、`Expand`、测试迁到新的 `Fn`（rel-lazy 867370d，全量 build、compile-diff 241/25、native 都绿）。Quicksort OOM：`compT` 把表的整列值（含重复）交给后面的 lazy 部分，改为 `ranC r`（faf139b）；`Expand.lem` 从项取每个部分的 `d`。
- ✅ 3.9 已合并（无下标的 `Tm A B`，结构函数 `Tm.dem`，3 分量 `Res`）；以下为合并前的记录。从 `Tm` 去掉下标：3.9–3.11 与 3.12 的一部分是一次编译原子的改动（13 个 module，分析
  `/data/tmp/rel-lazy-chain-analysis.md`），在集成分支 `noidx`（= `rel-lazy` e7c40ee + 下列提交）上分波移植，全绿后才并回。
  `Tm.lean` 完成（91b337e：`Tm A B`，结构函数 `Tm.dem`，`var (d) (k)`；移植说明 `/data/tmp/t0-porting-notes.md`）；
  `Bits`、`Plan` 完成（`w1a` 820bd67）。剩：`Elab`、`Gen`+`Compile`、`Expand`、`Den`、`*Spec`、`Rows`、`RelRep`、测试。
  类型不再检查的：闭合字段的 `dem = false`、`est`/`thin` 的 `Q`、`mapM` 与 `subst` 保持 `dem`。
- ✅ 3.10 没有 demand bit 的 `Elab`。
- ✅ 3.11 没有 demand bit 的 `Expand`。
- 🔄 3.12 删除临时物（`CRel.ok/rel/mk`、`Gen.Dem`、…）：
  3.12a ✅ 已合并（`Pl` 去掉 `Dem`）；
  3.12b ✅（`dem312b`，无代码改动）：`Out.Sound.memo`、`Dem`、`Dem.of` 在 000ce33 已不存在；`Cor` 保留，
  它是 `Elab.test` 的结果类型（用户 `corAt`、`paramOf`、`test`），与 prelude 的 `cor(S) = dom(π₁S ∩ π₂)` 是同一个
  relation `τ(S)`，但一个是 elaborator 中 term 的类型、一个是 `.rel` 库定义，互不替代，`prelude.cor` 保留；
  没有一个 `{d}` binder 是未被提及的：33 个带 `d : Bool` 的声明全部在结论里把 `d` 传给 `GenK.*`；
  3.12c ✅ 删去 `Gen.Fn`（phantom 索引连同别名本身，code 的类型就是 `Rel A B`）、15 个 `GenK.*` 的 21 个 `d`/`e`
  参数、`TmGen`/`Expand` 生成的 bit（`bE`），以及 33 个 `*_sound`/`*_wf` 的 `{d}`/`{d e}`/`{d d'}` binder。
- ✅ 3.13 inline `Den`：`lean-refactor notate Rel.Lang.Den --form 'Core.Rel (Obj.El $0) (Obj.El $1)'` 改写 12 个 module 中的 206 处应用，再删去 `abbrev Den`；没有已存在的别名可用（`Obj → Obj → Type` 的只有 `Tm`）。

### P4 `Tm` 的 constructor 变更 — 3/5（串行，共用同样的 match 分支）

- ✅ 4.1 `junc` 成为 definition，`juncD` 删除（junc41b，065b33f 合并，145e89c 进 master）：
  - `Tm.junc`、`Tm.juncD`、`GenK.junc`、`GenK.juncD`、`junc_sound`、`Tab.junc` 及其 law 删除；
    `Den`、`GenSound`、`ConvSpec` 中的 junc 分支随之删除。
  - `[R,S]` 由 `Pre.junc`（`Elab.lean:256`）展开为 `inl°R ∪ inr°S`；`α` 与 `hyloG` 的 `G(X)` 用同一个定义。
  - `inl`、`inr` 不加 constructor：prim 行 `inl`、`inr` 已是叶子；新增行 `inl°`、`inr°`（kernel
    `Tab.inlConv/inrConv`，`rowOK_inlC/inrC`，`Prim.den_conv`）。
  - 不放 prelude（与 P6 的 "prelude `.rel`" 不同）：`α`、`hyloG` 是 elaborator 自己的构造，prelude 可不加载；
    `Tm.kids` 按 `join`/`comp` 结构读 `[ , ]`，`call` 给 `none`；`call` 的 `Tm.den` 仍是 gap。
  - fold `⦇[e,S]⦈` 直接取两部分，不经过 junc。
  - 性能（`perf stat` 用户态指令数，626c084 → 1888ee2）：Quicksort 130.4G → 132.4G（+1.6%），
    Chess 483.8G → 483.7G，Edit 676.7G → 675.9G，Knapsack 15.72G → 15.74G。无回退，不需要融合 kernel。
- 🔄 4.2 `flat` 成为 definition：`flat` 留作融合行，由 `dfns` 与定义相连（分支 dfnR6，全量构建绿，待合并）。
  - `Rᴵ` 由 `Pre.flat`（`Elab.lean`，`Pre.junc` 之后）展开为 `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂`（pair、投影加相等测试，
    没有 converse）；`Tm.flat_den` 证明它的 `Den` 等于 `flatDen`。
  - `Tm.flat`、`GenK.flat`、`Pre.flat` 构造子、`flat_sound`、`flat_le` 及 `Den`、`GenSound`、`ConvSpec` 中的 flat
    分支删除；全量构建绿，GenSoundTest 1181 of 1181，没有 gap。
  - 性能（`perf stat` 用户态指令数，2281e0f → p44）：Knapsack 16.35G → 16.43G（+0.5%），
    Quicksort 79.77G → 79.96G（+0.2%），Edit 665.1G → 690.8G（+3.9%），Chess 314.0G → 379.8G（+21.0%）。
    改写为 `⟨π₁R,π₂⟩⟨π₁π₁ ∩ π₂, π₁π₂⟩π₂`（不用 `dom`）更慢：Chess 383.2G（+22.0%）。
  - Chess 超过 20%，所以 `flat` 留作融合行，用 `dfns`（`Elab.lean`）与定义相连（分支 dfnR2 → dfnR5）。
  - 读回（`Tm.dfnCut?` 把建好的定义认回融合行）从未匹配：trace 中带定义的 81 个 row（47 `length`、33 `sum`、1 个
    T49 的 `length`）0 个跑融合行，81 个跑定义；原因是定义的起点建成 `ran(U ⟨𝟙,𝟙⟩minus ∩ 𝟙)`，读回只认裸
    `⟨𝟙,𝟙⟩minus ∩ 𝟙`。dfnR4 删去读回：`build` 的 `.prim` 分支直接由 row 自己的关系和 target 的 universe
    选择：无界 → 融合行；`0…k` → 融合行后接 target 的 `𝟙`（`c.cut`）；其他 universe → 定义。
  - "融合行后接 `𝟙_B`" 不是所有 universe 上的含义（§4 `sum` 行：每一步都留在对象内）：`−3…3` 上
    `[−3,3,3] sum` 按定义为 `𝟘`（中间和 6），按 cut 为 3；`1…5` 上 `length` 按定义为 `𝟘`（从 0 起步）。
    `Tm.dfnCut_den` 证明二者只在 universe 为全体数或 `0…k` 时相等；`flat` 没有 universe，处处跑融合行。
  - dfnR5：定义的起点 `zeroTm u` 改为 `build` 实际建出的闭合形式 `ran(u (⟨𝟙,𝟙⟩minus ∩ 𝟙))`，于是其他 universe
    上跑的 `d` 就是旧路径跑的定义（dfnR4 的 4 个 guard 失败来自裸起点无 key 可读、结果为空）。
  - dfnR6：Chess 超 heartbeat 的原因是每个融合 `flat` 出现处（2507 个）都在 MetaM 里重新拟合 wrapper（`primE`，
    `primsFit` 一次、`node` 再一次）。`Expand.primFit` 按 (row, 对象, 关系类型) 只拟合一次，结果是对关系抽象的
    `fun xs => e`，`primsFit`、`node`、`GenSound` 的 `rowGens` 共用（`primMemo`）。全量构建绿，GenSoundTest
    1183 of 1183，0 error table，`gen_sound` 无新前提。
  - 性能（`perf stat -e instructions:u lake -R lean`，同一机器上 86fbf2a → dfnR6）：Knapsack 23.76G → 21.54G
    （−9.3%），Quicksort 87.23G → 87.11G，Chess 321.5G → 285.7G（−11.1%），Edit 665.1G（旧数）→ 204.3G。
    旧数（16.35G 等）比今天在 86fbf2a 上测得的少约 7.4G（`lake -R` 本身今天 8.62G），"Knapsack +34%" 来自与旧数
    比较；`0…k` 上改跑定义 `d` 为 23.62G，`c.cut` 比定义便宜。R49 / R499 的 `rel_program` 均低于 200 ms
    （原 6.29 s / 35.3 s），不随 |M| 增长。
- ✅ 4.3 `foldI`：owner 选 D，constructor 保留为融合形式，
  用 `foldIDen_eq` + `foldI_sound` 与定义相连
  （已证，e172821 合并，无额外前提；`Gen.foldI` 的 step 是交 `S ∩ π₁π₁π₁°`）。
- ✅ Tm28 B6（n 参数行 + foldI）：5d7704e 让一行可取任意个关系参数（`Tm.spinePol`、`Sems.le`、`Tm.den_pol_spine`，
  `primE` 直接拟合一个 `Fn` 组合子）；9030fca 把 `Tm.foldI` 换成两参数的融合行 `foldIRow`（`GenK.foldI`），定义
  `(π₁π₁° ∩ π₂⦇ran⟨𝟙,eπ₂⟩, S ∩ π₁π₁π₁°⦈)π₂` 是 `DfnCut.foldI`（`Tm.dfnCut_den` 用 `foldIDen_eq`），`rowOK_foldI`
  来自 `GenK.foldI_sound`；`Tm.foldI`、`Pre.foldI` 及其所有分支删除。GenSoundTest 1594 of 1594。
- ✅ 4.4 owner 决定：symmetric division 是定义，不是 `Tm` 构造子。`Pre.symDiv` = `R/S ∩ (S/R)°`（与 `/` 共用
  `Pre.rdivWhole`），`Tm.symDiv_den` 证其含义是 `symDivDen`，`TestSymDiv` 测行。表层语法是中缀 `R ÷ S`
  （owner 2026-11-20 决定；`Bin.table` 的一项，与 `/` 同一优先级），`TestSymDiv` 测它与手写定义行相同。
- ✅ 4.5 默认是 `[nil, snoc]` 上的左 fold；只用 `snoc` 构造。
- ✅ Tm28 B1（`doc/tm-minimal-design.zh.typ` §3，分支 `tm28b1`）：`E` 是定义 `E(R) ≜ Λ(∋ R)`，不是 `Tm` 构造子。删
  `Tm.E`、`Pre.E`、`GenK.E` 及其每个 match 分支；`applied` 构造 `Λ(∋ R)`（`appliedL` 本来如此），表层 `E( )` 不变。
  `Tm.E_den` 证 `⟦Λ(∋ R)⟧ = EDen ⟦R⟧`；`Prim.den_memRow` 加强为等式 `⟦∋⟧ = (x ∈ xs)`。
- ✅ Tm28 B2（§3）：`R × S` 是定义 `Tm.prod R S ≜ ⟨π₁R, π₂S⟩`（`Tm.prod_den`），删 `Tm.prod` 构造子、`GenK.prod`、
  `Tab.prod` 与 `Tm.code` 的「`prod` 不 memo」特例；积 universe 为 closed 的 `Tm.prodUni u v ≜ ran(⟨u, ⊤(v)⟩)`
  （`Tm.prodUni_den`，`uniPart` 与 `arith` 的 converse 共用）；`crossMax` 跟到 `Tab.pair`（`Tab.compPairs` 先数行）。

### P5 按既定顺序关闭 gap — 7/8（5.4a-c 并行，其余串行）

- ✅ 5.1 share：`Tm.den` 在 `Val.empty` 下读 share，`Tm.gen` 在 `Code.empty` 下建它，`gen_sound` 的 share 情形已证；
  没有 gap 留给它（p56）。
- 🔄 5.2 Λ/thin/setify/asc 的 soundness：`Gen.thin_sound`、`Gen.setify_sound`、`Gen.asc_sound` 已证并接入（3006856）；
  `thin` 仍有缺口：元素对象不 canonical 或 pair test 不是 `Tm.cor`；浮点 key 的缺口已由 S5 关闭。
- ✅ 5.3 hylo：owner 选 H（删 `ch` 字段，`Tm.kids` 是唯一来源）再选 A
  （`Tm.size`，`Tm.gen` 用 `termination_by t.size`，
  `compile_sound` 对 size 强归纳，不要 mutual `kidsGen`）。
  已完成：`Gen.onNodes` 的 lazy 分支裁到其 nodes，
  Gen 层 `hylo_sound`，`onKeys_round` 不带 coreflexive 前提（已合并，5b50784）。
  `d8hyloA`（d266a73：删 `ch`，`Tm.size`，`compile_sound` 按 size 归纳，`Tm.den_local`）经修复已合并为 296bab2
  （hylo 没有 `ch`：`Tm.kids` 是唯一来源，`Tm.size`，`compile_sound` 按 size 归纳）。
- ✅ 5.4a ✅ `lam_sound`（d72cf71）、5.4b ✅ `E_sound`（0ac4f13），都在 `rel-lazy`；5.4c ✅ `thin_sound`（3006856，见 D.8）。
- ✅ 5.5 call（stage 5）：代码已是这个形状：`Tm.call` 带 body，`Tm.den` 读 body（`Val.args ks`），`gen_sound` 的
  call 情形已证（p56 核对）。提案 `doc/call-stage5.zh.pdf`（69a8e5d）。owner 定 B D F H J：保留按 form 的常量作共享代码，
  与调用点 `rfl` 相等；`Tm.instObj` 实例化对象；`Code` 带实参的 `Pl`；`cv` 存逆的 body；registry 存 body `Res`。
  实现排在 P3、P4 之后（改 `Tm.call`）。
- ✅ 5.6 删除 `Tm.gap`（61c77cb）。`Tm.gap` 不是 constructor，是 `GenSound` 里的 Bool 谓词；所有 29 行都在
  `rowsProved`（`rowGens_proved`），剩下的 gap 情形是 error table，另有两个不是：row 给错关系个数、hylo 的
  `Tm.kids = none`（`Tm.gen` 和 `Expand.node` 都跑 `𝟘` 当 children）。现在 `primGen` 对个数报错，`Tm.gen` 给
  error table，`Expand.node` 在 `kids = none` 时报错。`Tm.gen_sound` 去掉 `t.gap = false` 前提；GenSoundTest 改数
  `Tm.hasCode`：133 个程序 1181 / 1181。compile-diff：723 ok，4 个 not ok（`muGrow.g`、`pairN.bad`、
  `hyloCycle.bad`、`unboundedT.bad`，是故意失败的测试，改动前同样 4 个）；pin 差 45 个，全是 "in the run, not in the
  baseline"（pin 落后于新加的测试），没有改变的定义。

### P6 kernels — 9/15

- ✅ 6.0 替换表：每个旧 extern 由哪些新 kernel 组成（分析）。
- ✅ 6.0a 删除 class Q 的 22 个 extern（其余 q 专用 kernel 仍在导出，见 6.14）。
- ✅ 6.1 `Op`。
- ✖ 6.2 / 6.3 `packed`：owner 选 `foR` 为唯一编码。
- ✅ 6.4 / 6.5 `scan`、`scatter`；唯一的 foR 读取是 `Rel.Kernel.foRWords`。
- ✅ 6.6 / 6.7 / 6.8 `gather`、`asc`、`distinct`；写入是 `wordsFoR`。6.7 剩余：`arr` key 的 MSD；浮点用 `ordKey`
  直到 6.9。
- ✅ 计划外：foR 含 patch 与 frame，Lean `Coc.encode` 为规格，Rust 逐字节相同（owner 选 B）；30f7b34，合并进 master f0f9171。`≥2^32` 个元素的列不写 patch list。
- 🔄 6.9 atom 和保序编码（Rust tag 表 WIP c4e3fb0，Lean 未改，不能单独合并；constructor 顺序
  `u1 u8 i16 i32 i64 f32 f64 char i8 sym date datetime general`，前 8 个 = 今天的 `SK_*`，G 时不改编号；
  q 类型码 `date` 14、`datetime` 12、`i8` 3（q 未用）。两次 LR rename 因内存被杀，排在 3.8 build 之后）：`QAtomicType` → `u1 char u8 i8 i16 i32 i64 f32 f64 sym date datetime`，用 `LR rename`，全仓串行。
  owner 定：`QAtom` 的 constructor 同名改（`.i64 x`、`.i32 x`，不再用 `long`、`int`）；`i8` 有符号（排序翻符号位 `0x80`，
  同 `i16`/`i32`/`i64`），另加无符号字节 `u8`（今天的 `byte`）；`Scan.Kind` 并入 `QAtomicType`，由它推出，不再单独定义
  （`orderKind`、`clsOf` 随之删除或变成恒等）。
  决定 I（owner，2026-11-18）：13 个 constructor 全部保留（`u1 u8 i16 i32 i64 f32 f64 char i8 sym date datetime general`）；
  删除的是 q 的编号和 wire 语义：`code`（q 类型码）、`width` 的 IPC/splayed 含义、doc comment 里的 q null 规则。
  未决：若没有 Rel 程序用 `date`/`datetime`，它们是否并入 `i32`/`i64`。（与上面的 q 类型码、`date`/`datetime`
  描述冲突之处，以本条为准。）
  `date`（自 1970-01-01 的天数，存为 i32）与 `datetime`（自 1970-01-01 的纳秒，存为 i64；q 的 epoch 是 2000-01-01，
  差 10957 天，不同；owner 2026-11-20 选 N），都不带时区；存为 foR
  码，按整数比较和排序（owner 经 dataframe 会话提出）。
- 🔄 6.10 已合并（master 2b042fd，make check 绿 241/25）：`gather` `scatter` `distinct` `asc` `scan` 直接在 foR 块上计算，
  共用一个 `for_view`（8196e68）；编码器选宽度提速，同一 plan（e340c19，`for_meta` 70% → 7–11%，`kgatherp` 4–8×）；
  Sink 每块只调一次 producer（2b042fd，约 2%）。之后合并、待 make check：`kgather` 在 #idx ≥ #src 且源列非 flat 时整列
  解码一次（860961e，ts −16–20%，xn −27–29%，sz 不变；owner 交我决定）；scan 浮点 NaN 规则（131f437，release 向量化交换
  操作数，取第一个 NaN 并置 quiet 位）。✅ scatter 一遍（scatter-once）：`encode_scatter` 已在 260e2d6
  作为死代码删除，答案经 `Sink` 每块写一次；剩下的两遍在输入：pass 1 解码整列 `ix` 只为查越界、数每块行数、判升序，
  写时再解码一次。现在 `ix` 的 metadata（`base`/`maxv`）若块间有序，`scatter::ordered` 按 metadata 二分找每个答案块的
  `ix` 块、块内二分切行，每个答案块自己验它切的块升序且首尾等于 metadata（c0554c0 只让含块最小下标的答案块验，并行时别的答案块在未验的乱序块上二分切行，
  BitsTest 越界 panic，已在 master 回退），op 错误与越界在同一遍里记下取最小行；验不过回到原路径（V 不变）。
  bench `scatter::tests::bench`（2^24 格、2^23 行、`last`）：升序 47–53 → 29–32 ms，乱序不变（72–92 ms，噪声）。
  scatter exactly-once 检查随 6.13。
  原条目：迁移使用者，按 6.0 的表每组一步；同时让 `scan`/`scatter`/`gather`/`asc`/`distinct` 直接在 foR 块上计算，
  去掉 `foRWords` 解码与 `wordsFoR` 重编码（CLAUDE.md 规则：解码需 owner 批准）。vortex 1M 复测：relk 多数格输给 q，
  主因就是这层解码/编码；`asc` 的 kern 本身也慢（38 ms 对 q 6 ms）。分析 `/data/tmp/p610-blocks.md`。
  owner 批准（每个 kernel 的 doc comment 记下）：一次只把一块解码进 L1 scratch（8 KiB）算是按块计算，处处允许（S）；
  `kscatter` 乱序下标先按输出块分组、扫两遍，不开整列数组（V）；`kasc` 一般 grade 用排列工作数组，宽 key 或多列 key
  另加整列序码数组（X）。默认：带 patch 的源按地址随机读，先测；不做输入块原样透传，重跑编码器块步骤，Lean 不改。
  顺序：`scan` → `gather` → `asc` → `scatter` → `distinct`；复用未 export 的旧 Rust（`codec::mask_cmp`、`cmp2`、
  `ffi/coc.rs` `val_vv`、`gather_enc`、`sort::order_enc`、`encode_scatter`），经 `Sink` 写出。foR B 已合并（f0f9171）；等它的 `make check` 通过，接着先做 6.9。
  vortex 100M 复测（564ffa1，`doc/vortex.md` "Re-measure on 0164b91"，perf 定位）给每个 kernel 的改法：
  - `scan`（慢 2.4-12×，当 map 用 `x<c` 慢 16-630×）：去掉 `rb::for_words_of` 整列解码和 `simd::v::pack64` 整列重编码，
    改为一次一块；`kscan_rows`/`op_eval` 的 `match` 与 `Result` 从每行提到每块，块内循环单态；比较走 `codec::mask_cmp`，
    平滑列先用块元数据（`codec::cmp_meta`，这条路径已经比 q 快 50-79×）。
  - `gather`（1% 慢 22-40×，全排列慢 3.5-6.5×）：只解码被读到的块（`gather_enc`、`res_get_in`）；结果经 `Sink` 写出，
    不再逐元素收集成 `Result`（`GenericShunt::next` 占 62%）。
  - `asc`（慢 4-168×）：LSD 的 8 趟不再经排列随机读 `k[i]`，key 随排列一起搬动（X 的序码数组）；先用块元数据查是否
    已有序，有序即返回（q 在已排序输入上快的原因）。
  - `scatter`（全排列慢 1.5-3.1×）：按 V 先按输出块分组，块内顺序写。
  - `distinct`（≈ q）：只换成按块读写，不另优化。
  - 6.10 之后另起一步：旧 coc 比较路径 `c::slice`（内联 `mask_res`，每 8 lane 一次 `kmovb` + `or`，占 87%）
    对 FastLanes 慢 1.4-10×，改为整字掩码写出；`take` 1% 的逐元素块查找改为按块分组。
  - 每个 kernel 合并后用 vortex 的 harness 在 100M 上复测一次，记进 `doc/vortex.md`；带 patch 的列（`sz` + outlier）
    在 foR B 合并（f0f9171）后重测。
- 🔄 6.11 删除旧 extern 与旧 constructor；保留 SIMD 编解码函数；删 `Enc.bits`：
  Rust 与 `RelKernel` 在分支 `nobits` 完成，Run/Rel 一侧在 `nobits2` 收尾。6.11c 见 D.5；之后删 `Enc.bits`，在分支 `nobits3`，已合并（a9812af：`Enc.bits` 删除）。
  决定 M（owner，2026-11-18）使本步成为 W2 的前提（即 W1b）：编码集缩到 foR + `pos`，`sym` 是字典之上的 id 列，
  字面量在进入处编码成 foR，`general` 列只作为 `arr` 存在；`.bytes`、`.syms`、`.gen`、enum 编码删除。
- ✅ 6.12 native gate：`make native`（`check` 的前提）跑 `TestNative.gatePlan`（`native1a`、`arithB`、`groupIdsB`），
  C 调到 scan/scatter/gather/asc/seen 五个 kernel；`relc plan` 与 `rel-native` 的 `out/` 逐项、逐文件 `cmp` 相等，3 s（7c98fda）。
- 🔄 6.13 虚拟行号（6.13a 见 D.4；6.13b、6.13c 未开始；owner 经 dataframe 会话决定）：frame 的行号对象 `I` 只存 `n`，磁盘与内存都不物化；每个 kernel 把它
  当恒等（位置即循环下标）。不是 `Enc.gen`，也不退回 `til n` 数组。设计 `/data/tmp/p613-design.md`，按规则定：
  - 放在列上：`Enc.pos`，无 payload 的 constructor，`Enc.get .long n .pos i = some (.long i)`（DRY：列已有编码的概念；
    放在 `Tab.key` 上则第一次取逆 `R°` 就要物化）。`Tab`、`rep`、`Reps` 不变，`Rel.Tab.key` 的 562 处使用不改。
  - 只给 `i64`；只表示 `0…n-1`，不做 `a + s·i`（没有第二个实例之前不加抽象）。
  - `WF` 在 6.10 去掉 `longsOf` 的可执行调用者之前为 `False`（不退回 `til n`）。
  - 数据算出的下标 `scatter`：`kscatter` 检查每格恰写一次，出错时报出格号（不吞错）。
  - 磁盘：`pos` 一侧没有文件，`n` 从另一侧读；两侧都是 `pos` 时 `output` 拒绝（内存即磁盘结构）。
  - 结果的编码只由参数的编码决定，kernel 不因检测到恰为行号就返回 `pos`。
  - 顺序：与 P3 无依赖。6.13a 在 6.10 开头（constructor、Lean 与 Rust 读取分支、定律、测试；改 `Value.lean`，全量重建，
    一次提交进 master 后并入 `rel-lazy`）；6.13b 在 6.10 末尾（`WF := True`，删 `tilCol`，gate：def 中 0 个 `tilLongs`）；
    6.13c `Plan` 与 C emitter，随 6.12。
- 🔄 6.14 调用者迁移与旧 kernel 删除（2026-11-18 由 operator 重排为 W0–W6）：
  - 发现（fable review，2026-11-18）：每个算子边界上的 relation 已经是编码列的 `Tab = {n, key : Vals A n,
    val : Vals B n}`（`Rel/Run/Core.lean:26`）。`structure Code` 与稠密 `ByteArray` 长列（`Rel/Run/Code.lean`）是从
    qlean 的 kernel pipeline 继承来的中间层，设计把它删掉。工作单位是 `Tab → Tab` 边界上的算子体（`Alg.*C`），
    不是旧 kernel 的 family，也不是 `Tm` constructor。
  - 为什么按 family 或 constructor 切分什么也退不掉：每个算子经六个共享函数到达 54–70 个旧 export：
    `Alg.canonC` → `Obj.sortByC`（每个 op 之后；`Rel/Run/CRelDef.lean:32`、`Code.lean:950`）58；
    `Lang.Bits.runC`（`Rel/Run/Lang/Bits.lean:249`）63；`Obj.codes`/`codesC`（`Code.lean:817`、`848`）49；
    `Tab.nub`/`nubC`（`Code.lean:985`、`Alg.lean:202`）49；`Obj.raze`/`razeC`（`Code.lean:665`、`712`）35；
    `Vals.pick`/`pickC`（`Code.lean:587`、`623`）22；`Alg.join`（`Code.lean:990`）17。
  - 证明代价：3069 条 theorem 里，1141 条只被下层引用，随下层删除；语言层依赖 85 条不变的算子命题；276 条上层证明直接
    引用下层，要从五个 kernel 的定律重证；另加一个新的支持层（估计 150–300 条，未核实）。
  - 包：
    - ✅ W0 删除没有 Rel 程序到达的每个旧 export（不替换，不重证）：已合并（de93da2），删 7 个；其余 70 多个都被
      六个共享函数连着，在算子改写之前删不掉。
    - ✅ W1 闭包定律（af61a75，`Rel/KernelSpec/Closure.lean`）：`Enc.Valid`、`foRWords_valid`、`wordsFoR_closed`、
      五条 `k*_closed`；桥 `Arr.get_raw_foR`。缺口：`pos` 不是 `Enc.WF`；`u1` 列带前提 `t ≠ u1`。
    - 🔄 W1a 每个原子列在产生处就是 foR 或 `pos`（ad5b0d7，`mig-for`）：`col longCol setIdCol colFn`、`Gen.atom`
      经 `longArr` 产生 foR（`longCol`、`setIdCol` 是旧 kernel 稠密输出在出口处编码一次，随 W5 删除）。仍稠密：
      `tilCol valCol`、`pick`/`gatherColumn`、`Enc.answer`、`sortByC`——卡在旧层只对 `.bytes` 陈述的 raze/pick
      定律上，不再逐点改，由 W3 把这些算子直接改写到五个 kernel 上。`Expand.atomE` 对 sym/general/ALP 列报错。
    - W1b 删除 foR + `pos` 之外的编码（决定 M）：在 W1a 之后（`.bytes` 没有构造点时删 constructor）。
    - 🔄 W2 第一个算子端到端（04acf52）：`Tab.canon`/`ran`/`dom` = `kasc` → `kseen` → `kgather`
      （`Rel/Run/Canon.lean`，定律 `Rel/RepCanon.lean`），kernel 之间无转换。未做：替换旧的 `canonC`/`nubC`/
      `CRel.ran`/`CRel.dom`（等 W3 的 `pick` 替换，以及 `sym`、`general`、`arr`、`sum` 列）。前提 `hK` 已去掉
      （2f86a15，`ordcode`，owner: G）：`ascOrd_atom`、`Vals.row_of_seenKey`；`Vals.nub_sorted`（按序码升序、无两行
      序码相等）；`Vals.seenKey_iff_row`（序码相等 ⇔ 行相等）、`Vals.nub_distinct`（005e20e）。缺：1024 行块边界的
      Lean 例子（`decide +kernel` 不归约；已诊断为 `encodeAt` 的 kernel 归约代价，见 D.12 的 seen1024 一条；
      cocspec 去掉了 frame 搜索的平方，剩下按下标读字节与解码侧，见同处）。
    - W3 策略（2026-11-19，owner 三条决定，取代同日早先的 "全部算子齐了再一次切换"）：
      - 工作清单是 `Rel.Lang.Tm` 的构造子（43 个；`call`/`arg`/`var`/`share`/`own` 是绑定），spec 是各自的
        denotation。不照旧层 `CRel.*`/`Alg.*` 的列表移植（owner："this is stupid"）；旧算子只在 `#guard` 里做对照，
        与 denotation 不一致时跟 denotation。清单 agent 按旧层数出的 "约 62 个未开始" 作废。
      - 设计就是 `doc/rel-architecture.zh.typ`（owner："You should follow the architect pdf"），不另写设计：
        - §1：`Tm` 的构造子组保持为构造子；§4 "allegory 运算 → kernel" 给出每个运算由哪些 kernel 复合（`R\S`、
          `R/S`、对称除不求补，按组比较个数；`Λ` 由 `asc ≫ seen` 给 `lo`/`hi`；`μ ν fold hylo` 是 Lean 里的循环
          `fixOn`）；§0：`Rel A B = tab | lazy`，`succ`、`arith`、`leq`、`⊤` 是 `lazy`。
        - 成为定义的是 §7 TODO 列的：`junc = inl° ≫ R ∪ inr° ≫ S`（已完成，4.1：elaborator 的 `Pre.junc`，
          不是 prelude `.rel`，原因见 4.1）、`flat`、`foldI`、`prims` 表里能写成 `fold`/`hylo` 的行（prelude
          `.rel`）；只留 kernel 级的原语。
        - 我提过的两个形式（列是 `pos ⟶ α` 的 map —— 那是 dataframe 的 frame；全部算子写进 prelude）都被 owner
          否决，已撤回。
        - owner 选 G（2026-11-19）：`\`、`/`、`Λ`、pair 等保持为 `Tm` 的节点，kernel 复合写在 compiler 发的 Lean
          代码里；不从 `Tm` 删掉改成 prelude 定义。规则："Not define new data structure"——算子与定律只用已有类型。
          owner 定（2026-11-19，改了先前的"删除"）：保留 `AscKey`。它只用于一侧类型是 `[β]` 的情况：把
          `lo`/`hi`/payload 作为一个 key 交给 `kasc`/`kseen`，比较时沿 payload 逐元素比。分支 `w3nokey`
          （展开成等宽列）已停，不合入。待办：architecture §4 的 `asc`/`seen` 签名按 `AscKey` 更新。
        - 切换（`/data/tmp/w3-switch-steps.md`，T0–T10）的三点，owner 交给我定（2026-11-19）：
          (1) `Rel.tab` 带 `Except String (Tab A B)` 而不是 `Option`，kernel 复合的错误消息一路到 `check`
          （规则：不吞错误）；architecture §0 的类型随之更新。(2) 切换期间新旧两条路径用第二个同签名的 `Gen`
          namespace，`Expand` 按程序选；不加算子结构体。(3) `length cat cons F sum` 等行先写成 `fold`/`hylo`
          上的定义，融合复合以后再加并配 `⟦row⟧ = ⟦def⟧`。
      - compiler（`Gen.*`）现在就发 kernel 复合，按程序切换：一个程序用到的构造子都有 kernel 版本，它就走新路径；
        "仍走旧路径的程序数" 是进度数字，到 0 时 W5 删除旧层。新旧算子不能在一个程序里混用（旧的写 `.bytes`，
        新 kernel 拒绝非 foR，转换被禁止）。切换步骤：`/data/tmp/w3-switch-steps.md`（在写）。
    - W3 已在 master（335b933）的 Lean `Tab` 算子与定律；尚无程序运行它们：
      - 共用构件 `Rel/Run/Cols.lean`（`colPrefix`、`shiftCol`、`Arr.concat`、`Vals.concat`、`catPlan`、`lastCount`；
        `colConst`、`colMap` 在 `Rel/Run/Canon.lean`）；`Rel/Run/Core.lean` 的 `Arr.ofBytes`、`Arr.ofFn`（每个定宽
        type 的 foR producer，`w1float` 2ed1c81）。
      - `Rel/Run/Canon.lean`：`Vals.cols`、`Vals.gather`、`Vals.nub`、`Tab.canon`、`dom`、`ran`，覆盖 atom、tuple、
        `sum`、`arr` 侧（`Tab.canon_holds`、`canon_sorted`）。
      - `Rel/Run/SetOps.lean`：`∪ ∩ − ⊑`（`Tab.union_holds`、`inter_holds`、`diff_holds`、`le_holds`、`inter_sorted`、
        `diff_sorted`、`whereCol_spec`；`whereCol` 拒绝 ≥ 2^63 行）。
      - `Rel/Run/Comp.lean`：`≫` 与 converse（`Tab.comp_holds`、`comp_canon`、`conv_holds`；`Tab.comp` 拒绝
        `2^63 ≤ n*m + n + m`）。
      - kernel 签名变更（`w3arrside2`）：`AscKey` = `atom t` | `cells n c lo hi els`，`kasc`/`kseen` 取
        `List (AscKey × Enc)`；cell 按元素序码的字典序比较，真前缀在前；没有新 export。
    - W3 状态（2026-11-19，master 41bf67b）：算子在 master、尚无程序运行它们。
      - 有算子且有定律：`∪ ∩ − ≫ ° dom ran`、`𝟘 𝟙 ⊤ outl outr pair prod inl inr junc flat`、
        `\ / Λ E ∋ nil lt leq`、`succ`。有算子无定律：`arith`（`Tab.arith_holds` 未证）。
      - 缺算子：`est thin atPos fold foldr foldI mu nu hylo`、对称除、`val` 的包装、`prim` 各行。
      - 与 architecture §4 不同、待改：`∩ − \` 的按组折叠用了 `kscatter` 而不是分段 `scan`；`\` 物化 join；
        `°` 之后多跑一次 `canon`。
      - `lt leq`（`GenK.cmp`，cmpmeet）：已是 `lazy`，`dom`、`ran` 都已知才算；与表求交时（`T ∩ ≥`、`T − <`）
        `Known.pairs` 带来 `T` 的对，只逐对比较 n 对再选行（`Tab.cmpPairs`），不做 `K × L` 的 cross。
        仍做 cross 的：没有表可求交的比较（`P ≤ P`）与 `top`（`top` 尚未用 `pairs`）；`Vals.cross` 超过
        `crossMax = 2^28` 对时返回 error，不再在 Rust 侧 abort。
      - ✅ `R × S` 与 `⟨π₁ R, π₂ S⟩` 同一 plan（分支 `prodplan`，dataframe 报告）：闭的 `x × y`（`dem = false`）原先被
        `Expand.code` 包进 `GenK.memo`，无上下文地算出整个 CROSS（`Tab.prod`），复合 `asc(ran⟨𝟙,K⟩) (x × y)` 来不及把
        `K` 的对交给它；pair 写法 `dem = true`，从不冻结。现在 product 节点不 memo（其两个操作数照旧 memo），已知定义域时
        `GenK.prod` 就是 pair 写法，没有边界时才 CROSS。`TestFrameBench.joinBig`（1500 × 55001 对，1500 个匹配）：
        3.84 s / 4.7 GB → 0.34 s，与 pair 写法相同；`TestFrameJoin` 比较两种写法的行。
      - 🔄 kernel 分配失败是 error 不是 abort（分支 `prodplan`）：`pod::vec_of` / `pod::try_uninit`（`try_reserve_exact`）
        给出 `"<kernel>: cannot allocate <bytes> bytes for <what> (<n> elements)"`，经 `except` 成为 `Except.error`；
        已接入：`gather` 的整列 `e`，`scatter` 的行偏移、行值、块计数，`seen` 的游程位、块计数，`bitrows` 的
        `ends`/`idx`/结果位。未接入：`asc` 的工作数组（`asc.rs` `dense` `work` `codes` `lsd` `rank` `mixed` `grade`，
        `sort.rs` 的 `cnt` `ba/bb` `ia/ib`：返回 `Option`/`()` 的函数链，要改成 `Result`）、`Sink` 的输出（经 Lean 的
        `lean_alloc_object`，失败在 Lean 运行时内）与 `coc_alloc`（`exit(1)`）、`Ext.Enc.encode`（签名无 `Except`，
        要改 extern 签名）。
      - 定律的缺口：`lam_den`/`E_den`（等于 `lamDen`/`EDen`）带前提 `hB`（序码的序与 `B.lt` 一致），未对任何
        `Obj` 证掉；float 上本来不成立（`±0.0`、NaN）。
      - 合并记录：w3arrcat fe67914，w3arith 0f77c2f，w3struct+w3sumcat 4b6f121，w3div+w3divlaw+w3lam 803cd89，
        w3ldiv 9d7704b，fixpanic 41bf67b（`RepTabArith` 的证明展开 `Ew.intStep` 把 `panic!` 分支带进证明项；
        改为引用每个 verb 一条的 `Ew.intStep_*`）。旧层里同因上 `panic-allow.txt` 的条目随 W5 消失。
    - W3 切换（`/data/tmp/w3-switch-steps.md`）：T0 去重（✅ `5e41591`）→ T1 compile-diff 按名字、按行集合
      对照生成的基线（✅）→ T2 管线 + `val uni zero id ° ≫ ∩ ∪ − dom ran`（✅ `43cfd2b`，`GenK`）→ T3 `top outl outr pair
      prod ldiv rdiv` 与 `nu`/`mu` 循环：第一批程序（`sudokuac csp sudokupc sudokupc9`）走新路径，16 → 12 →
      T4 `wumpus`（11）→ T5 `chess`（10）→ T7 `circuit`（9）→ T8（6）→ T9（0）→ T10 删旧层（W5）。
      状态（2026-11-19，master `95c082e`）：跑在新 kernel 上的程序 0 / 16；T3 在做（`t3b`）；T4、T5、T7 的 `GenK` 发射体和
      kernel 行表已合入（`95c082e`），`est`/`thin` 在程序里等 T3 的 `pair outl outr`；`Tab` 算子 `nu mu τ setify length atPos
      est thin` 与 list 行已在 master。owner 决定（2026-11-19）：`kscan` 多返回 fold 结果，`whereCol` = `scan → scatter →
      gather`，不排序（`b44915c`）；architecture §4 的 power/list 行是草稿，待 owner 审。
      状态（2026-11-19 12:00，master `1a31760`，`make check` 绿，compile-diff 427 / 33）：新 kernel 上 3 / 15（`sudokuac sudokupc
      circuit`）；T6、T8 在做（`t68b`）。owner 决定（2026-11-19）：`sudokupc9` 选 A —— §4 加两行：`≫` 与 `\` 按左侧 key 分块
      （峰值有界，块界取 `expand` 前的 `cR·cS` 前缀和），以及一个 bit matrix 融合 kernel `kbitrows`（现有 `bitRowsOver`，
      `|A|·|B| ≤ 2²⁷` 时选用，用定理连到 `Tab.comp` / `Tab.ldiv`）；RELK 目标 10 → 11。分析：`/data/tmp/pc9/analysis.md`。
      `rel-native` 程序自己创建输出目录（owner 选 E），CLAUDE.md 不改。`muGrow` 固定在旧层：新路径上无不动点的 `μ` 要跑
      1024 轮、每轮给变长的数组排序（`kasc` 的 `cmp_rows` 占 71%），待修。
      状态（2026-11-19 13:42，master `f90f42e`，`make check` 绿，compile-diff 427 / 33）：新 kernel 上仍 3 / 15；RELK 80。
      已合入：`kbitrows` + `Tab.compBits` / `Tab.ldivBits` + 定理 `Tab.compBits_comp` / `Tab.ldivBits_ldiv`（同样的行，`Canon` 未证）；
      `Tab.comp` 展开分块（`blockRows = 2^24`，`comp_holds` 不变）；`kasc` 的 `cmp_rows` 每元素读一次整列宽度的问题已修
      （基准 64 s → 0.39 s）；`own_write` 创建缺失的父目录。未做：编译器选用 `compBits`、去掉 `sudokupc9` 与 `muGrow` 的固定
      （✅ 2026-11-22 核对 `cd3523e`：`GenK.compR` / `ldiv` / `rdiv` / `ldivM` 经 `Tab.compSelM` / `Tab.ldivSel` 按 `Tab.bitsWin`
      选，`66384ef`；`sudokupc9` 的 `rel.kernel false` 随 `9907da6` 删去；`muGrow` 走 kernel 路径，`3d7d677`）、
      T6 / T8（`t68c`，闭项只算一次的规则见 architecture §0 草稿）。
      状态（2026-11-19 16:34，master `a362914`，`make check` 绿，compile-diff 598 / 34，旧条目无变化）：新 kernel 上 17 / 17
      （全部程序 `offKernel = []`）；RELK 80。T3–T9 完成。已合入：T6 / T8、`rows5`（`inits tails concat filter takewhile`）、
      `GenK.hylo`（有环的余代数报错，owner 选 C）、`loop merge thinL`、`F(R)` 行（`Tab.map`）、`≫` / `\` 按 `Tab.bitsWin` 选
      bit matrix、`Tab.pack`（`foldRounds` 每轮压缩数组 payload；knapsack OOM 的原因是 `∪` 拼接 payload 而 `canon` 保留）、
      `Tab.toList` 按列读（`implemented_by`，owner 选 E：证明待办）。
      T10 之前欠的：`relRegs` 读编码列（`frame` 因此固定在旧层）；去掉 `muGrow`、`hyloCycle`、`frame` 的固定和各 `Kern*`
      模块的旧路径对照；`Tab.fixOn` 也要 `pack`（`muGrow` 带 270 倍的无用 payload，分支 `onepack` 在做）；μ/ν 轮数用尽时
      kernel 路径的错误文本要带 μ 的位置和上限；`sudokupc9` 约 30 s（owner 选 B：中间结果保持 bit matrix，分支 `bitsmid`
      在做）；`GenK.rdiv` 的 bits 规则；`Tab.pack`、`Tab.map`、新行、`GenK.hylo` 没有连到 denotation 的定理。
      状态（2026-11-19 17:03，master `3d7d677`，完整构建绿 486 jobs，`make check` 在跑）：17 / 17；RELK 80。
      已合入：`onepack`（只有一个 `pack`，`Tab.fixOn` 与 `foldRounds` 的累积输出每轮都经过它；μ/ν 轮数用尽与有环的
      `hylo` 在 kernel 路径上报出项的位置和上限，文本只定义一次：`Tab.capMsg`、`GenK.cycleMsg`）；`bitsfin`（新构造子
      `Rel.bits` 承载 bit matrix，owner 选 B 批准的例外，§0 草稿行；`≫` 选中 matrix 时返回 `.bits`，`tab ≫ bits`、
      `bits ∩ tab` 在 matrix 上算，`rdiv` 走 `Tab.ldivSel`；`Rel/Run/Gather.lean` 从 `Canon`、`Cols` 拆出）。
      `sudokupc9` 28.7 s → 13.3 s（旧路径 1.2 s）；`muGrow` 去掉固定，118 s → 约 40 s，`#guard` 改为 kernel 路径的文本。
      测试代码的取舍由我定（owner，2026-11-19）。
      在做：分支 `frame1b` 删 `frame` 的 stage 1b（它只测 T10 要删的旧 kernel）与 `relRegs valsRegs arrRegs maskB
      whereB groupSumB`，去掉 `frame` 的固定；“Lean 之外的 plan 与 `frame.out` 逐字节相等”到 W6 重写。
      T10 之前还欠的：`hyloCycle` 的固定和各 `Kern*` 模块的旧路径对照（随旧层删）；第三个 gate 的 `arithOut` 一半与
      `TestNative` 的 `gplan` 全是旧 export，T10 会弄断，保留它需要 W6 先做（写出路径 `lit` + `own_write` 那一半不受影响）。
      pc9-regress（2026-11-22）：`sudokupc9` 3.1 s → 35 s 是真回退（程序逐字节相同，同为 `lake lean` 热构建：10342bc 3.3 s，
      5690422 35 s）。first-parent bisect：c164861 3.3 s、205f5bc 3.6 s、e76c990（只改 pin），首个坏提交 7f9e4d7（integ3）
      24.3 s；integ3 内 d3dc7f9 3.6 s，故为 paramL2（fde8044）。机制：`GenK.meetOn` 对 `.bits` 操作数也走 `T.runE {}`，
      即 `Tab.ofBits` 把 matrix 读回成行再 `bound`：`sup(X) = π₁X ∩ π₂π₁°` 里 `π₁X` 是 59049 × 729 的 matrix，读回 2.7e7 行，
      之后 `sup(X) X` 也只能按行算（perf 的 `Take::block`、`for_meta`）。paramL2 前 `.bits` 走 `meetV`（`keepBits`，不读回）。
      已修（93e2c1c）：`meetOn` 加一支 `.bits … x … y … => meetV T (S.force ⟨K.dom 或 x, K.ran 或 y, none⟩)`（matrix 的行、列
      值集合作 S 的界，不读回），`lake lean` 热构建 35 s → 10.4–11.1 s，`#guard` 通过；同时撤回 paramL2 的 `callDef` 按需
      形式再无收益（11.8 s）。`meetOn_sound`/`meetOn_wf` 多一个情形，新引理 `Known.WF.orElse`（`K` 未知的一边用 `Vals.WF`
      值集合补上仍 `WF`；matrix 的 `x`/`y` 的 `Vals.WF` 已在 `Rel.Wf (.bits …)` 里），行落在 `x × y` 内由 `Tab.ofBits_set`。
      第二处回退已修（026c1ce）：`GenK.memo` 的兜底分支 `| R => .tab (R.runE {})` 把 `.bits` 经 `Tab.ofBits` 读回成行，
      `K₀ ∩ π₁\(sup(X) X)` 每轮成了两张表的 `Tab.inter`，而不是 `meetV` 的 tab∩bits。规则：`memo` 只把 `lazy` 换成它在空
      上下文 `force` 出的值（`tab` 或 `bits`）；别的值已算过一次，原样返回，表示由读它的运算选。`lake lean` 热构建
      12.4 s → 3.1 s（两次 3.10 s、3.15 s）。`memo_sound`/`memo_wf` 用已有的 `force_runE`、`Rel.Wf.force`，无新引理；
      architecture §0 “存成 `tab`”改为“存成 `force` 后的值（`tab` 或 `bits`）”。
      ~~`ldiv(tab, bits)` 每轮把 matrix 读回~~：过时，I2 已做（`GenK.ldivM` → `Tab.ldivTabMat`，`kbitrows true`，不读回；
      `Tab.ldivTabMat_law` 已证）。2026-11-22 在 9aed3b4 上量（`lake lean`，含约 1 s 启动）：`sudokupc9` 41 s；只算 `sup(K₀)`
      6 s，`sup(K₀) K₀` 12 s，一轮 `K₀ ∩ π₁\(sup(K₀) K₀)` 11 s：`\` 与 `∩` 合计不到 1 s，每轮约 10 s 在 `sup(X)`
      （`π₁X` 2.7e7 行的表，约 5 s）和 `sup(X) X` 的 `compSel`（约 5 s）。perf（多线程）：relk 57%、libleanshared 23%，
      `for_meta` 7%、`Take::block` 4%、`k_scatter`/`k_seen`/`k_asc` 各约 1.5%，`k_bitrows` 0%；kernel 在 pool 线程上跑，
      `--call-graph dwarf` 加 `QLEAN_THREADS=1` 也连不到 Lean 调用者。下一步若做：`π₁X ∩ π₂π₁°` 不物化 `π₁X`。μ 的 semi-naive：不做（2026-11-19，
      owner 交我定）。试过 `Δ = f(X) − X` 再 `X ∪ Δ`：每轮排序两次，`muGrow` 66 s → 79 s，已撤回。要省需要循环体对
      `∪` 分配的判定（`X ≫ X`、带 `\` 的不满足）和已排序表的归并（新 kernel）；17 个程序里只有 `Party` 用 `μ`，
      运行时间可忽略。出现受益的程序时再议。
      ✅ 2026-11-22 owner 定 D：μ 体对 `X` 线性（`Tm.linIn`）时走 semi-naive `Tab.muLin`（`Δ' = F(Δ) − X`，只算新行），
      `Tm.den_linIn`（`⟦t⟧(X ∪ Y) ⊑ ⟦t⟧X ∪ ⟦t⟧Y`）+ `Tab.muLin_holds` 证与 `Tab.mu` 同解（`GenK.mu_sound`）。
      `muGrow` 32 s → 5.0 s（其中 import 0.7 s）→ 3.2 s（mugrow2，perf 采样时长 5.25 s → 3.20 s）：
      (1) `enc::move_blk` 的 null 测试只看 `nul` 有位的行——原先 `nul` 为空时也逐元素循环（perf 里的 `write_nul` 21%，
      不是清零缓冲区）；(2) `Cells::codes` 的 span 排序改稳定排序（合并已有序的段），排序 15% → 9%；(3) 每轮的 `∪`
      与 `−` 合为 `Tab.unionDiff`，共用 `T ++ X` 的一次 `asc` + `seen`（`unionDiff_ok`）。余下仍与 `|X|`（含 payload）
      成正比：concat 是两次全长 `kscatter` 加一次 `add`，每次重编码 `X` 的整个 payload（`for_meta` 11%、`write_nul`
      9%），`asc` 的 `Cells::codes` 读整个 payload。与 `|Δ|` 成正比需要：对已排序 `X` 的成员测试（无 search kernel，
      五个 kernel 组不出）与不重编码的追加。
      mugrow3（3.2 s → 2.4 s，perf cycles 24.3G → 16.6G）：`X` 放在 concat 前面（`X.unionDiff T` 答 `(X ∪ T, T − X)`，
      `−` 是 `Tab.rdiff`：不含 `X` 行的组，`rdiff_holds`），`X` 的块与输出块对齐；`Producer::take`（`enc::Moving`、
      `enc::movable`）由 `kscatter .last` 经 `pos`、`kscan` 的单位元 map（`+0`、`|0`、`-0`、`×1`、`first`、`last`）与
      `kgather` 的连续整块索引实现，对齐的块原样搬移（`write_nul` 9.5% → 1.8%，`for_meta` 10.8% → 5.4%）。余下：
      `pool::worker` 自旋 27% + `run_c` 5.5%（小任务的线程交接），`asc` 排序 8.7%（仍读整个 `X`），与 `|X|` 成正比。
      mugrow4：搬移块的测试（3 块以上，有补丁与无补丁；搬移输出与不搬移路径逐字节相等，无一错）：Rust `scatter`、
      `gather`、`kscan` 各一（`enc::MOVED` 计数断言确有搬移），Lean 每个 kernel 一条 3000 行 `#guard`（该规模 `decide`
      归约不了）。`SPIN` 1024 → 256：`muGrow` 墙钟 1.71 s → 1.91 s（cpu 2.99 s → 2.64 s）、`Pc9Time` 2.80 s，墙钟变慢，
      已撤回；`SPLIT` 未试。
      `muGrow` 32 s → 5.0 s（其中 import 0.7 s）。余下每轮仍与 `|X|` 成正比：`∪` 是 concat + `canon`（重排全部 `X`），
      `−` 是 `select`（`kasc` 全部 `X ++ F(Δ)`）；perf：`write_nul` 21%、pool 空转 17%、排序 15%、`for_meta` 10%。
      再省需要已排序表的归并 / 对已排序 `X` 的成员测试（新 kernel 组合），未做。
      perf10（2026-11-22）：`muGrow` 的“排序 15%”是 `kasc` 的 cells 键（`Cells::codes` 按 `[u64]` 逐字比较等长的秩串），
      改为 64 字一段 `memcmp` 跳过公共前缀：比较 + quicksort 23.6% → 6.1%，`muGrow` 6.9 s → 4.2–5.5 s；`res_get_in`
      强制内联（边缘读取放冷路径）+ `encode_meta_blk` 一遍算 min/max/sum：`sudokupc9` 3.08–3.20 s → 2.77–2.80 s。
      余下：`for_meta` 8–10% 是 `plan` 的直方图（标量计数），`write_nul` 闭包是各 producer 内联进来的块步，未动。
      未证：`Tab.keepBits_holds`、`Tab.compTabMat_holds`（命题已写在 `bitsfin` 的报告里，缺 `index` 与 `colMap` 的 spec）、
      `Tab.pack`、`Tab.map`、新行、`GenK.hylo`。
      状态（2026-11-19 17:58，master `a2f1f9b`；`make check` 绿到 `6a91b10`，其后的合并未构建）：已合入 `frame1b`（`frame`
      走 kernel 路径）、`w6`（W6 完成：plan 路径只调用五个 kernel 与 `own_write`；寄存器以 `Val.ctor` / `Val.nat`、
      `Instr.ctor` / `Instr.proj` 承载 Lean 构造子对象，owner 2026-11-19 批准；recipe `whereB` = scan → scan → scatter →
      gather，`groupIdsB` = `kasc` → `kseen` → `kscatter`，`arithB` 仅 `add sub mul`；旧 recipe 的 9 条定理删除，新 recipe
      未证）、`t10a`（编译器只发射 `GenK.*`；`rel.kernel` 开关、`*Old` 对照、全部固定、`RelRep.lean` 删除）。RELK 仍 80：
      旧层由 plan 路径四个文件的 import（`Rel.Run.Code`、`GenSpec`）保持存活。在做：分支 `t10b` 切断这些 import，删旧层
      与对应 Rust，RELK → 11；并删无 kernel 实现也无程序使用的 prim `asc distinct tic`。
      状态（2026-11-19 18:23，master `22c1940`，未变；`t10b` `ba2cedf` 未合入）：`t10b` 删 99 个模块、1519 条定理与 prim
      `asc distinct tic`，各 gate 在其 worktree 通过，但 RELK 仍 80：旧 export 在 `Rel/Kernel` 之外的直接调用者是保留的
      核心 `Rel.Run.Code`（37 个 export）、`Rel.Run.Core`（11）、`Rel.Run.Alg`（8），经它们 `Syntax.prims` 的行类型
      （`prim% CRel.*`）、`Elab` 的字面量（`Alg.prod idU col emptyArr`）、`Den`、`Rep.rep`、`Lazy` 也依赖旧层。
      审计（逐条按陈述引用的常量分类，`/data/tmp/t10b-audit/classes.tsv`）：564 条关于已删定义；352 条只关于现行路径
      不可达的旧 `Alg.*` / `CRel.*`；301 条覆盖的旧代码仍在编译期运行（`showRel` → `Tab.nub` → `Alg.Code`）；100 条关于
      现行定义，是误删（`convTm_den` 一组、`Hylo.rounds_lfp` 一组、`Tm.den_local` 等、`Enc.get` / `Enc.raw` 的读取
      引理）；202 条通用辅助引理。删除前后都没有任何定理的陈述提到 `GenK`：`compile_sound` 说的是旧编译器 `Tm.gen`，
      与生成代码的联系只由 compile-diff 测试。compile-diff 现在把生成代码的结果与冻结的 baseline 比，是回归固定，
      不再有独立对照。owner 2026-11-19 选 A：补回误删后合入，接受上述两点为中间状态。
      在做：分支 `t10c`（在 `t10b` 之上）恢复 `ConvSpec`、Hylo 理论、denotation 引理、读取引理，删无调用者的
      `bit_rows_over`、`structural_enlist`（RELK → 78），改正 compile-diff 的描述。
      之后 T10d：把 `Syntax.prims` 的行类型、`Elab` 字面量、`Den`、`Rep.rep`、`Lazy` 改到 `Tab` 上，重写 `Run.Core` 的
      11 处，删 `Code`、`Alg`、`CRel*Def`、旧 kernel 与其 Rust，RELK → 11；合入后在 main 重生成 compile-diff baseline
      与 `panic-allow.txt`，改 CLAUDE.md 的 Layout（`KernelWF`、`CRel*` law 已不存在）。
      欠的证明：`GenK.*` 组合子与 `Tm` denotation 之间没有定理；`Tab.arith bitsMax compTabMat keepBits foldRounds mu
      nu peelL peelR atPos est thin`、`kernRows` 的行、plan 的 `groupIdsB arithB whereB` 无定理；compile-diff 需要一个以
      denotation 为准的独立对照才重新成为检查。
      状态（2026-11-19 18:54，master `893fcd4`，`make check` 全绿，compile-diff 476 ok / 2 按预期报错）：`t10b` + `t10c`
      合入（a1f86e9，RELK 78；读取引理补回 55 / 62，在 `Rel/KernelWF/Read.lean`）；`t10d` 合入（b455892）：**RELK 11**
      （`k_scan k_scatter k_gather k_asc k_seen k_bitrows stop coc_encode coc_decode own_write own_map`），67 个旧
      kernel 去掉 `@[extern]` 与 Rust export、6 个 ffi 模块、5 个 kernel 测试模块；`showRel checkErr uniOf litCol` 改到
      `Tab` 上。未完成：旧 kernel 仍以普通 Lean 定义存在，`Code`、`Alg`、`CRel*Def`、`Run/KernelWF` 未删；ffi 背后的
      Rust 库模块未删。在做 T10e：`Syntax.prims` 的行类型直接写出、`CRel` 类型换成 `Tab` / `Rel`、`Den` / `Rep` 去掉
      `Alg.*`、`Rep*` 的对照 `#guard` 改成固定的期望行，然后删上述模块与无 export 可达的 Rust 模块。
      状态（2026-11-19 19:24，master `c96ebc8`，`make check` 全绿，RELK 11，compile-diff 476 ok / 2 按预期报错）：
      `t10e`（4c1ed12）、`pfree`（ffeec8d）、`t10f`（18224ec）、`t10g`（3088ee5）合入。`Rel/Run/{Code,Alg,Algebra}`、
      7 个 `CRel*Def`、`Rel/Run/KernelWF/*` 已删；`Prim.sig` 直接写出（`prim% CRel.*` 删）；`CRel` 类型换成
      `Except String (Tab A B)`（`Rel.runE` 的返回类型）；`Rep*` 的对照检查改成对 list 上的 denotation 比（19 组）或
      字面行（ν、μ），按集合比较，不再覆盖行序；`Known.den` / `Tm.den` 里 column 取值上的 coreflexive 写成
      `(graph row)° ≫ graph row`（pointfree gate）。删掉的定理：`Rep` 里 9 条关于 `Alg.idU zero outl outr conv` 的
      （`Tab.*_holds` 已有同样的定律）。
      旧 kernel 模块（`Db.Own Dep.* Driver Elementwise Eval.Val Reduce Search Sort Structural`）里 267 个声明的去向
      （`/data/tmp/t10g/holders.md`）：41 个无人使用，已删；164 个只被上面已删的模块持有，现在可删；36 个只在定理 /
      陈述里用，保留；26 个在运行路径上——动词编码常量（搬到 `Kernel/Op.lean`）、原子类型映射 `Dep.Carrier` 与空原子
      （数据定义，保留）、以及 `Column.intern`（`Db.ownParts` 写 `syms` 列时建字典，O(n²) 的 Lean list 代码，首次出现序，
      own 文件 kind 4 `enum`）。按 architecture §4（`sym` = 保序字典 id，intern = `asc ≫ seen`，字典排好序）与本文件
      "`.syms`、enum 编码删除"，`Column.intern` 与 own 的 `enum` 种类删除，不另问 owner。
      Rust：无整模块可删（`sort structural ew group ids` 各有部分被现行 kernel 使用）；模块设为私有后 894 个无用项，逐项清。
      状态（2026-11-19 19:46，master `91abf22`，`make check` 全绿，RELK 11，compile-diff 476 / 2）：`t10h`（40c1358）合入。
      旧 kernel 模块里 224 个无人使用的声明删除，`Kernel/Driver`、`Kernel/Reduce`、`KernelSpec/Dyad` 整个删除，连同约 90 条
      以它们为对象的引理。index 显示没有任何程序、测试或 native gate 把 `syms` 列送进 own 写入器，所以 `Column.intern`
      及其辅助删除；`Db.ownParts` / `Db.ownFile` 返回 `Except String`，对 `syms` / `enum` 列报错（symbol 列应是 foR id 加
      排好序的字典，该写入器尚不存在）。留下：Rust own 格式仍读 kind 4；`Rel/KernelWF/Read.lean` 约 60 条引理无使用者但
      对象还在；旧模块里剩运行路径与定理仍读的定义（`Carrier`、`rank`、`ordKey`、`binStep`、`tilLongs`、`Ew.intStep` 等）。
      T10i（`t10i` a837f6c，未合入）：`crate/src` 17 540 → 7 709 行，默认配置 0 警告；但把现行 kernel 的测试也删了
      （`cargo test` 169 → 53），并去掉了 `build.sh` 无 feature 那一步的 `-D warnings`。T10j 在其上补回被测对象仍在的测试。
      状态（2026-11-19 20:05，master `aa977bb`；`make check` 绿到 `91abf22`，其后两个合并只改 CLAUDE.md 与一个测试模块，
      该模块单独 build 通过）：CLAUDE.md 的 Layout 改到现状（aafc4ce）；prelude 的 `pm od st py pz` 重新对照 list 上的含义
      （`pregd` 55a6161：每个 key 配其数组的全部排列、按 `le` 有序的行、两者的交；用 `specOk` 按集合比）。
      **T10 剩余**（迁移收尾，按顺序）：
      - T10j（在跑，分支 `t10j`，基于 `t10i`）：补回 Rust 里被测对象仍在的测试，核实 `build.sh` 那一步原本检查什么。
        通过后把 `t10i` + `t10j` 合入，`make check`。
      - Rust own 格式的 kind 4（`enum`）读取：Lean 侧已不写；等 `sym` 的写入器（foR id + 排好序的字典，
        `kasc ≫ kseen` + `kgather`）存在时一并改格式。现在没有程序用 `sym`。
      - `Rel/KernelWF/Read.lean` 约 60 条、`KernelSpec` 里若干条引理无使用者但对象还在：留到 T11 的归纳定理写完，
        仍无使用者的再删。
      - 性能与 `Tab.toList` csimp 等见上面"未做"。
    - **T11 生成代码的正确性**（分析：`/data/tmp/oracle/design.md`；依据 architecture `:117-119` "`compile` 返回自己的证明，
      每个节点的 `Gen.*_sound` 是其定义的一部分"、`:352` "compile-diff = `compile` 对 `rel_program` 差分"、`:123-125`
      "证明止于 Lean 定义，Rust 由 `decide` / `#guard` 测"）。现状：`Expand.node` 每个 `Tm` 构造子对一个 `GenK.*`，
      55 个定义、0 条定理；陈述用的谓词 `Rel.Rel.Reps K r R`（`Rel/Rep.lean:28`）已存在而无定理使用；`Tm.gen` /
      `compile` 已不在；`Tm.den (.call ..) = 𝟘`。不另写 list 上的求值器（那是第二份 `Tm.den`）。
      - 状态（2026-11-19 20:50，master 83f98bb；`make check` 在 bf0a8c5 全绿）：T11a、T11b、T11c、T11e1–e3 已合入。
        `Tm.gen_sound (hb : GenK.ReadsBack) … : t.gap = false → t.LamLaws → Sound η ρ → ∀ K, (t.gen η).Reps K (t.den ρ)`
        （`Rel/Lang/GenSound.lean`）；覆盖 117 / 203 个定义；差分测试 `Tm.gen` 对生成常量 261 比较、0 不同，随
        `make check` 跑。`CompTabMatLaw`/`KeepBitsLaw` 原陈述为假，已换成 `BitsWf`/`Rel.Wf`（`Rel/Lang/GenKBits.lean`）。
        - 发现：`ReadsBack` 第一部分为假（反例 `/data/tmp/t11e4/Cex.lean`，已跑）：sum key 的 `idx` 列为 `bytes` 时
          `compSelM` 给出 bit matrix，`ofBits` 的 `kgather` 报 `gather: e: constructor 0 is not foR`。是报错不是错答案；
          修法二选一（`compSelM` 拒绝非 `foR`/`pos` 的列，或 `kgather` 读 `bytes`），随 bit matrix 路径的改动一起定。
        - 发现：`GenK.juncD` 不成立（tag false 而 `l = 0`，或 tag true 而 `r = 0` 时读 `dflt`）；无程序使用；未改。
        - T11d 只做了测试一侧：`GenSoundTest.reread` 在读入时展开每个带参数的定义，不留 `call` 节点；
          `Tm.den (.call ..) = 𝟘` 仍在。
        - owner 定的顺序（C）：先做 architecture §4 已定的实现改动（`∩ − \` 分段 `scan`、`\` 不物化 join、
          `ldiv(tab, bits)` 在 bit matrix 上算、`μ` semi-naive），差分测试与回归固定保护；`ldiv meet diff mu fold` 与
          bit matrix 路径的证明（T11e 余项、`ReadsBack`）等实现稳定后再做。T11e5 只做 `arith`。
        - 2026-11-20 07:03，master d42a7d5：**check-68 全绿**（481/2、483/483，235 / 235）。`elabE` / `elabArgs`
          恢复成全函数（owner 选 B；elabTotal 493222d）：row 的定义通过 `elabWith` 的参数 `dfn` elaborate，不是自调用；
          定义里出现带定义的 row 时在 elaboration 报错并指出两个 row（只在该 row 被程序用到时触发，不是对整张表预查）。
          dataframe 的 gap 清单（`/data/tmp/df-gaps.md`）：owner 选 gap 1（universe 来自数据，选项在
          `/data/tmp/uniA/`，待 owner 选）与 gap 0（row `where` / `asc` / `firstOcc`，分支 `dfrows`）并行。
        - 2026-11-20 06:21，master bfa135d + pin：**check-67 全绿**（481/2、483/483，235 / 235；定义数 478 → 483 是新测试
          `sumFold` 的 5 个）。owner 的两项决定已落地：
          - **E**（`sum`/`length` 在有 universe 的对象上等于 fold，逐步检查；sumE af94837）：`Prim.dfn : Option Expr` 是 row 表里
            每个 row 的定义（`length.dfn = ⦇[0, π₁ succ]⦈`，`sum.dfn = ⦇[0, plus]⦈ʳ`，S4g 起为左折叠 `⦇[0, plus]⦈`）；`Elab.build` 在 target 有 universe 时
            构建定义，否则用融合 row（`long` 上 `rowOK_sum`/`Tab.sum_holds` 不动）。a9998a7 的 `row ≫ U` 已删。附带改动：
            `elabE`/`elabArgs` 变 `partial`；`foldParts.base` 对 source = target 同一未解对象的 base 不再设成 `1`。
            新测试 `sumFold`（手算）：`M = -3…3` 的 `[-3,3,3] sum` 无结果，`P = 1…5` 的 `length = 𝟘`。已有固定值全部不变，
            `compile-diff.json` 只新增 5 条；compile-diff 一步 936 → 928 s，没有可见变慢。
          - **registry B**（regB 11f19aa；check-66 在 fac8d01 全绿）：同一 key 的第二次登记必须是同一定义（`Registry.again`、
            `Registry.call?`、`Tm.diffAt`/`Tm.fieldsEq`，嵌套调用按 key 比），否则报错；`lookup` 返回先登记的。A（常量名只由 key
            决定）不可行：互不 import 的两个模块声明同名常量，同时 import 时 Lean 拒绝。整棵树 113 个 key、4 个登记多次
            （`blocks` 的 `R.form.4`、`M.form.4`、`S'.form.4.4`、`L.form.0.1`），全部相同——这个计数未进 gate。
          - 04:52 一条里"待 owner 决定"的两项作废。
        - 2026-11-20 04:52，master 643bc17 + pin：**check-65 全绿**（476/2、478/478，235 / 235）。
          - T11f 合入（t11f b61c2d8）：六个 kern 测试程序 147 个定义中 146 个有手算的字面行 `check`；`TestCompile` 列出没有任何
            字面行 `check` 提到的定义：436 → 290（共 478）。
          - T11f 的发现：`kernT45.sm ≜ x sum`（`N = 0…5`）给出 `(1,6)`，`6 ∉ N`。原因：row（`.prim`）只通过 `toObj` 用
            source/target，声明对象的 universe 在那里丢失；`plus` 不是 row，`Tm.arith` 自带 `≫ U`。`length` 同样出界。
            `gen_sound` 看不到：`sum` 的 denotation 也写在 `long` 上。
          - 修法（sumN a9998a7，`Elab.build` 的 `.prim` 分支）：row 的实例化 target 有 universe 时合成 `row ≫ U`（`uniPart`）；
            无新 constructor/kernel/证明。`compile-diff.json` 只改 `kernT45.sm` 一条（去掉 `(1,6)`）。
          - **待 owner 决定**：(a) 有限对象上 `row ≫ U` 只查最终结果，与 §4 的 `sum = ⦇0,+⦈ʳ`、`length` = fold 不等
            （`N = -3…3`、`[-3,3,3]`；`N = 1…5` 的 `length`）——D 接受并在 §4 注明 / E 把 `U` 传进 `Tab.sum` 与 `length` 逐步查 /
            F 只在 `long` 上定义；现为 D。(b) registry 同 key 两个常量——A 常量名只由 key 决定 / B 检查两 body 相同 / C 留着。
          - 代价：`∋ loop inl inr` 在有限对象上多一次与 universe 的 join。
        - 2026-11-20 03:23，master 0229322：**check-62 全绿**（476/2、478/478，235 / 235）。check-61 在 cbfe5a4 失败：registry 的
          冲突检查（d2b163a）在真实程序上触发——`Rel.Lang.Test.given` 与 `Rel.Lang.Test.orders` 互不 import，各登记
          `Rel.Programs.blocks.R.form.4`，import 两者的测试模块全部报错；s5conv 报告的"58 个不同 key、0 重复"只查了它构建的
          模块。d2b163a 已 revert（`Registry.clashes` 随之去掉）；`callTm_convOK` 保留。未解决：同一 key 两个常量
          （`emitter ++ key`），`lookup` 静默取后登记的，"同 key 同 body"仍未检查；方向是让常量名不依赖登记它的模块（会改
          `compile-diff.json` 的常量名，先不动）。下面 03:01 一条里关于 `Registry.clashes`/`call?` 的内容作废。
        - 2026-11-20 03:01，master cbfe5a4（check-61 在跑；check-60 在 66bb2cc 全绿，476/2、478/478）：s5conv 合入，235 / 235。
          `callCv` 的 `ConvOK` 前提由构造推出（`callTm_convOK`、`convTm_instObj_den`；前提换成实例化后 body 的结构性 `ConvOK`；
          没有字面的"`instObj` 与 `den` 交换"引理——两边元素类型不同）。registry：key = `formKey c fs`；两个互不 import 的模块
          原来可以各建同一 key，`Registry.add` 静默取最新；现在保留第一条、记入新字段 `Registry.clashes`，`Registry.call?` 报错
          （key、两个常量名、修法），`Embed.define` 与 `reread` 都走它。今天的树里 58 条 call、58 个不同 key。
        - 2026-11-20 02:40，master 66bb2cc（check-60 在跑；check-59 在 6f29cc5 全绿）：**覆盖 235 / 235，`Tm.gap` 在 17 个程序的
          定义上不再命中**。已合入：p13F + p15F（行 `F`：`Obj.key_ordCode`——整数 atom 类型上 `kasc` 的 code 序即 `Obj.lt`，float
          不在其中；`Tab.mapFold_holds`、`Vals.cells_expand_row`、`Tab.comp_pos_rows`、`Tab.map_holds`、`GenK.map_sound`）、p14sum
          （行 `sum`：`Tab.sum_holds`，`raw_kscan_rev` 对每个 `Op`）、dry1（删 `cellBounds`，`Tab.length`/`Tab.atPos` 调 `cellSpan`；
          `Tab.mu_holds`、`GenK.mu_sound` 由 `Tab.fixOn_inv` 推出）。差分测试慢的 3 项已查：不是回归，这 3 个定义此前"无代码"不参加
          比较；`Tm.gen` 一侧每个调用点重算 body（`chess.mate` 260 次调用 / 13 个被调定义），时间全在 kernel；决定不改（带缓存的
          求值器要复制 `Tm.gen` 的分情形）。`gen_sound` 仍带的前提：`LamLaws`（`Λ`/`E`/`τ`/`setify`/`tails` 处的 `LamLaw`，加循环体
          单调——后者可判定且全部通过）。待做（gs-clean 核对于 cd3523e）：
          - ✅ `Tm.ConvOK` 的 `callCv` 前提不在 `gen_sound` 上：`gen_sound` 只带 `GenHyp`，`Tm.ConvOK` 只被 `convTm_den`
            读，`convTm_den` 无调用处；`callTm` 建的 `callCv` 由 `callTm_convOK`（s5conv）推出。
          - ✅ `reread` 读最终 registry：perf14c c6f97f8 / perf14d cd3523e 改为在程序自己 read 时的 registry 下重读。
          - ✅ 重复证明文本（gs-clean 1850c5a）：`GenKFold` 里 `Arr.pos_get` 的副本删去，用 `RepCols` 的；
            `expand_cells_le` 删去，`Tab.map_holds` 用 `cellSpan_width` + `expand_spec` 得 `T ≤ n·m`（同 `cells_expand_row`）。
          - ✅ `Tm.spineHead` 已随 `Tm.gap` 在 61c77cb 删去；`Expand.spineHead`（`noCode` 的报告）没有死分支。
        - 2026-11-20 01:59，master aa5060f：覆盖 218 / 235（新口径：17 个程序的定义加上每个注册的共享定义各算一次；旧口径 203 不再
          打印）。check-57（4e82176）、check-58（3bd6f13）全绿，差分 478 / 478、compile-diff 476 / 2。已合入：s5t23（stage 5 T2/T3：
          `den`/`gen` of `call` = body under `Val.args`/`Code.args`，`Sound.args`，`gen_sound_spine` 的 `call`/`callCv`/`share`
          情形，`reread` 读 registry；`arg call` 从 gap 表消失）、p12rows（行 `thinL`、`tails`；`rowsProved` 条目改为 Λ 定律所在的
          object 列表）。剩余 gap：`arg F` 17（6 单独）、`prim sum` 11（0 单独）。新增未证前提：`Tm.ConvOK` 在 `callCv` 处
          （`u.den = (b.den)°`，只进 `convTm_den`；要证需 `Tm.instObj` 与 `den`/`convTm` 交换的引理）。`Tm.argDen_false` 已删（call 头
          上为假）。回归：差分测试 3 项超过 60 s（`chess.mate` 246 s、`chess.m` 245 s、`chess.Pin₁` 91 s；此前 0 项），运行路径不受
          影响。未检查：`reread` 读最终 registry 而非 elaboration 时的。在跑：p13F（行 `F`）、p14sum（行 `sum`）、s5slow（profile
          差分测试）。
        - 2026-11-20 01:26，master 4e82176（check-57 在跑）：覆盖 166 / 203。已合入：p10wire（`est atPos mu nu hylo` 出 `Tm.gap`，
          `Sound.bind`，`Tm.LamLawsAt`/`Tm.monoOK`，`gen_sound_spine` 按 `Tm.size` 归纳）、s5t1（stage 5 T1：`Tm.call ks c os b`、
          `Tm.callCv … b u` 带实例化后的 body，`Tm.instObj`、`Once.binds`，registry 存整个 `Once`；差分 478 / 478、compile-diff 476 / 2
          不变；`Tm.size` 总和 4182 → 9550，olean +0.3%，elaboration 时间不变）、p11rows（行 `concat`、`merge`；
          `Tab.foldRounds_holds` 加 round invariant `I`，旧的 `hstep` 前提对 `merge` 为假）。剩余 gap（挡住 / 单独）：`arg call` 23 / 23、
          `arg F` 13 / 3、`prim tails` 1 / 1、`prim sum` 10 / 0、`arg thinL` 1 / 0。在跑：s5t23（`den`/`gen` of call = body，`Sound.args`，
          `reread` 读 registry）、p12rows（`F`：缺"kasc code 序 = 数值序"引理；`thinL`、`tails`、`sum`）。
        - 2026-11-20 01:04，master 2b74cb8，`make check` 全绿（check-56）：覆盖 145 / 203，差分 478 / 478。已合入：p7munu（`GenK.nu_sound`、
          `mu_sound`，`GenKFix.lean`）、p8est（`est_sound`、`atPos_sound`、`hylo_sound`，`GenKEst.lean`、`GenKHylo.lean`）、p9arg（`RowOK`
          带参数码，`Tm.argGap`，`gen_sound_spine`；行 `loop filter`）。在做：p10wire（把 est atPos mu nu hylo 接进 `gen_sound`，hylo 按
          `Tm.size` 递归；单调条件计入测试）、s5t1（stage 5 运行侧：`call ks c os b` / `callCv` 带 body，计划 `/data/tmp/s5plan/plan.md`；
          我定：两个平构造子、`ks : List Nat`、保留 `os`、只靠差分测试绑定、`reread` 先保持 `calls = none`）。
          缺口：共享常量路径没有和 `Tm.gen` 比过（闭定义里没有 call 节点）；stage 5 后让 `reread` 读 elaborate 时的 registry。
          待清：`Tab.fixOn_inv` 与 `Tab.mu_holds` 重复；行 `F sum merge thinL tails`（都不单独挡住定义）。
        - 2026-11-20 00:33，master 7de1951（未跑全 gate，三次合并后各自构建过）：覆盖 143 / 203。p4rows：`Tm.gapKinds` + `gap_eq`，
          `GenSoundTest` 按 gap 种类报"挡住 / 单独挡住"；行 `snoc cons cat` 已证。p5rows：行 `uncat zip length` 已证。p6arg：
          `Tab.loop_holds`、`GenK.loop_sound`。剩余（挡住/单独）：`arg call` 23/22、`nu` 8/8、`est` 10/6、`hylo` 6/5、`atPos` 7/4、
          `arg loop` 4/4、`mu` 2/2。`arg call` 证不了：`Tm.call` 只带 `Lean.Name`，`den = 𝟘`，`gen` 给 error 表；按
          `doc/rel-denotation-design.md` stage 5 做 `let` 节点（在 p9arg 合入后派）。在做：p7munu（`mu nu`）、p8est（`est atPos hylo`）、
          p9arg（`RowOK` 推广到带参数的行，`loop filter merge thinL F`，`tails` 的 `LamLaws` 对象）。
          待清：`cellBounds`（`Rel/Run/Power.lean`）是 `cellSpan` 的重复；`GenSoundTest.reread` 的 docstring 说"no call node is left"，对 Once 体不成立。
        - 2026-11-20 00:17，master edb7413，`make check` 全绿（check-55）：覆盖 127 / 203，差分 478 比较、0 不同。`gen_sound` 无未证前提
          （`ReadsBack` 三项已证并删除，p3reads）；`fold foldr foldI` 出 gap（p2fold + p2bfold：`uncons/unsnoc/pack_holds`，
          `foldRounds_holds` 的步骤可依赖 key；`Vals.pack` 补 2^63 检查）。check-54 红过一次：p2bfold 与 p3reads 合起来不编译，
          4 行修复。architecture 的 `seen` 三处已统一为"行须已按 `asc` 序"（91f583f）。
        - 23:44，master ad90237，`make check` 全绿（check-53）：覆盖 122 / 203，差分 478 比较、0 不同（compile-diff 一步 432 s）。
        - 关机前的状态（2026-11-19 21:50 左右）：master ad90237 = 10342bc + d1diff（差分测试按 `Tm.hasCode` 跳过，分支上 478 比较、
          0 不同）+ p1ldiv 6f2aa59（`Tab.ldivTabMat_law/_wf`、`GenK.ldiv_sound/_wf` 已证，`ldiv` 出 gap，分支上 122 / 203；
          `ReadsBack` 多了第三个合取项）。**master 上还没构建、没跑 `make check`**（下一个是 check-53）。I1 前后计时：316 个定义合计 120.9 s → 121.1–124.5 s，两次"之后"相差 3.4 s，差别在噪声内，没有可测的变慢。
          计时用的 worktree 已删除。每小时偏离检查已查到 8e26eb3。
        - 21:40，master 10342bc，`make check` 全绿（check-52）：覆盖 116 / 203，差分 302 比较、0 不同。
          - I1 ✅ `∩ − \ /` 的按组折叠走 `Tab.groupFold`（分段 `kscan`，`Rel/Run/SetOps.lean`；`Tab.groupFold_ok`），
            `inter_holds diff_holds ldiv_holds` 已对新实现重证。`\` 仍物化 join（`Σₐ |R a|·|S a|` 行）：不物化要换算法，待定。
          - I2 ✅ `R \ bits` 在 matrix 上算（`Tab.ldivTabMat`，`GenK.ldivM`；`sudokupc9` 13.5 s → 3.1 s）；`Vals.cols` 拒绝
            `kgather` 读不了的 sum `idx` 列（`bytes` 反例已修，`Rel/BitsTest.lean` 的 `bytesKey`）。待证：
            `Tab.ldivTabMat_law`（陈述在 `ldivTabMat` 的注释里）、`ldivTabMat_wf`；`GenK.ldiv_sound` 已删，`ldiv` 在
            `Tm.gap`。差分测试跳过带 gap 节点的定义，`ldiv` 的 14 个定义不再被比较：待改成对 `Tm.gen` 有真实代码的
            gap 定义也比较。
          - I3 ✗ `μ` semi-naive 按 `:477` 的写法更慢（每轮两次排序；`muGrow` 66 s → 79 s），已撤回。要省需要循环体对
            `∪` 分配的判定和已排序表的归并（新 kernel）；只有 `Party` 用 `μ`。等 owner 定做不做。
          - T11e5 ✅ `Tab.arith_holds`、`GenK.arith_sound`；`foldRounds_holds`（轮不变式）已证，`fold foldr foldI` 仍缺
            `Tab.pack_holds`、`Tab.uncons_holds`、`Tab.unsnoc_holds`。
          - T11d：读入时内联是 architecture §7 与 Q11 的做法；运行时的项仍含 `call`，`Tm.den (.call ..) = 𝟘` 一支不再被读到。
      - T11a ✅：新模块 `Rel/Lang/GenKSpec.lean`，为已有 `Tab.*_holds` 的运算（`id comp conv meet dom
        ran zero join top ldiv rdiv diff outl outr pair prod junc flat lam nil val uni succ leq lt`、行 `∋ τ setify inl
        inr`）各写一条 `GenK.*_sound`：前提 `∀ K, R.Reps K X`，结论右边与 `Tm.den` 对应分支相同；从 `Tab` 定律到
        `GenK` 引理的提升只证一次。需要附加条件的引理如实带上条件并列出。
      - T11b：`Tm.gen`（把 `Expand.node` 那张表写成 `Tm → Fn` 的函数）与 `gen_sound : Sound η ρ → ∀ K,
        (t.gen η).Reps K (t.den ρ)`，对 `Tm` 归纳；尚无引理的构造子进一个可判定的 gap 清单，定理先带清单落地再缩小。
        `Expand` 与 `gen` 是两个递归，由差分测试绑定（architecture `:352`）。
      - T11c：`test/TestCompile.lean` 改成 `(t.gen η).runE {}` 对生成的常量做差分；`compile-diff.json` 的固定只留给
        gap 清单里的定义。
      - T11d：`call` 的含义 = 内联被调用定义的项（Q11），`Tm.den (.call ..)` 不再是 `𝟘`，定理覆盖带调用的程序。
      - T11e：补缺的 `Tab` 定律，gap 清单随之缩小：`arith est thin atPos mu nu fixOn foldRounds peelL peelR compSelM
        compTabMat keepBits bitsMax pack`、25 个 `kernRows` 中的 20 个、plan 的 `groupIdsB arithB whereB`（可并行，
        每条一个 agent）。
      - T11f：六个只测"能跑且行数非零"的测试程序（`kernT2` 30、`kernT45` 34、`kernT68` 25、`kernT9` 31、`kernRows5` 18、
        `kernMap` 9，共 147 个定义）补字面行的 `check`；`TestCompile` 报出没有任何 `check` 触及的定义。只有字面行的
        `check` 能看到 `Elab` 给出的错 `Tm` 与固定时就错的结果。
      - 度量：有 `_sound` 引理的 `GenK` 运算数（现 0 / 55）；gap 清单长度；被字面行 `check` 覆盖的定义数
        （478 中约 35 + 测试程序里的若干，T11f 时用 `checkOf` 的 `Chk` 列表精确数）。
    - W3 留给后面的风险（清单 agent 提出，均未验证）：计数做 `\` 会物化 join（最多 `|R|·|S|` 行），SudokuPC9、
      blocks 可能超内存；规范序从 `Obj.lt` 变成 `kasc` 序码，打印的期望值与 `out/key`、`out/val` 可能变；
      `coc_block_start`、`coc_bools_of`、`structural_bits_of_for` 与 `Plan.abi` 点名的 12 个 export 在 W5 后仍有
      caller。
    - W4 `Gen.*B`（稠密 bit 矩阵，`Lang.Bits`）改走 table 路径；融合形式只在有定理时回来。
    - W5 删除 `Rel/Run/Code.lean`、`Rel/KernelWF/`、旧的 `KernelSpec` module、`Kernel/{Structural,Sort,Search,
      Elementwise}` 与它们的 Rust；`RELK.txt` = 5 + 保留的。
    - W6 native：`Plan` 得到一个 `Enc` 寄存器，`Plan.abi` 列出这五个。
  - 度量（每次合并）：调用旧 export 的可执行 def（149，W0 之后未重数）；`RELK.txt` 行数（master 335b933：79；
    主要在 W5 下降）；仍走旧路径的程序数（全部；新路径尚不存在）；compile-diff 241/25。`make check` 在 afd96d5
    全绿（2026-11-19）；335b933 的 `make check` 全绿（241/25）。
  - 2026-11-19 的修复：`Coc.packRes` 改为一次 `map`（77b475c；逐字节 `push` 在 Lean kernel 里是平方的，
    `SeenTest` 8.2 → 1.6 GB，全库 build 峰值 2.8 GB）；own 列文件没有 kind 1，part 数表是唯一判据，两条拒绝文本
    由表生成（679839b；`OWN_NPARTS` 变为 `[Option<usize>; 5]`，qlean 的比较要跟着改）。
  - 第一波撤回（2026-11-18）：按 export family 切分（分支 `mig-scan`、`mig-gather`、`mig-ew`、`mig-enc`、
    `mig-closure`、`mig-abi`、`mig-recipes`：未 build 的 WIP，未合并）；`Code` 的载体改写到 `Enc` 上；adapter
    `Enc.ofLongs`/`Enc.longs`；加强 `code_runs`；q 动词 recipe（find、member、bin、where、rank、dict）作为具名实体：
    只有 concat、expand、分段 fold 与 classes = `kasc` → `kseen` 留作构件。保留：`kasc`/`kseen` 在 `arr` key 上
    （分支 `mig-arrkey` 369f095，WIP）。
  - 风险：纯组合比融合 kernel 多遍（每个 op 之后的 canon 是一次排序；`kseen` 没有 hash，要先 `kasc`）；生成的测试在
    elaboration 时运行每个程序，慢的组合会拉长 build；qlean 钉在 e024297，import `Rel.Kernel.*`/`Rel.KernelSpec.*`，
    所以 W5 会弄坏它，除非 pin 不动。
  - 已合并（自 d4105f7）：`d7map`（75a2d45）、`mig-asc`（931a278）；296bab2 hylo 没有 `ch`（`Tm.kids` 是唯一来源，`Tm.size`，`compile_sound` 按 size）；
    0957f87 seenfix；a9812af `Enc.bits` 删除；dbdc72d 7.5 gate。
  - 操作：同一时刻最多一个 `lean-refactor index`：每次运行对每个 kernel `*Test.lean` 占 3–7 GB；2026-11-18 三个并行
    index 加九个 agent 填满 30 GB 内存和 57 GB swap，`make check` 在 index 一步停住。

### P7 Plan A — 2/4（7.2-7.4 串行；7.5 独立）

- ✖ 7.1 library 边界：不做。owner 2026-11-18 选 7.2 的 wrapper，`compile` 留在预编译的 `RelRun`，没有东西要移；
  这推翻 Q12（“`compile` 移到持有证明的 library”）。
- ✅ 7.2 `Rel/Lang/CompileSpec.lean` 与 `compileS` 已在 a8ca355 删除。compiler 是 `Tm.gen`
  （`Rel/Run/Lang/TmGen.lean`），定理是 `Tm.gen_sound`（`Rel/Lang/GenSound.lean`）。`gen_sound` 要求 `t.GenHyp`
  （不动点体正，每个 `share` 槽表示其部分），所以不是每个程序都能包成 subtype；按设计卡片“`rep` 与 `compile`”，保留普通 `Tm.gen`
  加单独的定理。
- ✅ 7.3 `rel_program` 发出 `compile t`，从 `Expand.lean` 删除旧路径。
  Q1 选 A（设计卡片“闭项只算一次”：在共享常量处只算一次）：闭部分是 η 旁边携带的 share 表；`rel_program` 在程序和
  call body 上给它们编号；`.share k R` 读槽 k；`Sound` 增加：每个槽计算 ⟦R⟧。三部分：
  - ✅ 7.3a `Tm.gen` 及其运行时部分移到 `RelRun`（`Rel/Run/Lang/TmGen.lean`）；`Tm.code` 不缓存 `.prod`
    （旧 `Expand.code` 的条件）；`Expand.tmE`：一个 `Tm` 作为构造它的 `Expr`，`GenSoundTest` 测 round-trip。
  - ✅ 7.3b share 表（分支 `s73b`）：`Code` 是结构 `{var, sh}`，`sh : Codes` 是 share 表，`Code.bind`、`Code.args`
    保留它（`Code.args η ks xs`）。`Tm.number`（`RelRun`，`TmGen`）给闭部分编号并进入 call body；相等的部分
    （`Expand.tmE`，其已编号的部分读作槽号）共用一个槽；spine 的头不编号。`Code.shares` 每个槽只算一次，
    `Code.program` 给一个程序的所有定义一张表。`.share k R` 读槽 k，表里没有时就地构建。`Sound` 增加：每个槽 `Wf`
    （`Code.Wf`）；`Tm.GenHyp`（原 `Tm.LamLawsAt`）增加参数 `P`，在 `share k R` 处要求 `Codes.Shares`（槽 k 表示 ⟦R⟧）。
    只改了 `gen_sound` 与 `gen_wf` 的 share、call 两个 case。`Tm.number`/`Code.shares` 满足 `Codes.Shares`：
    已证（分支 `shares`，见 7.3c 末）。
    测量（`test/TestCompile.lean`，`REL_COMPILE_TIMES`）：chess 整个程序的 share 表 31.1 s，之后每个定义 0 ms；
    旧的 `Tm.gen` 路径 `chess.mate` 246 s、`chess.m` 245 s。所有程序合计 90.5 s；963 个定义与生成的常量相等，pin 不变。
  - ✅ 7.3c（分支 `s73c`）`Expand.emit` 移到 `TmGen`：程序的全部项（定义、print、check、output 用到的 run-time
    定义的 body）一起 `Code.program` 编号；槽 k 的项是常量 `n.c.t<k>`（`tmE sh`：已编号的部分写成它们的常量），
    `n.shares : Code := Code.shares #[…]` 每个程序一个，只算一次；`n.x := runE (Tm.gen n.shares ⌜t⌝) {}`。
    `io` 的 run-time 定义：`Tm.gen (Code.args n.shares o.binds 表) ⌜body⌝`（`Sound.inputs` 的形状）。没有 code
    的节点用 `Tm.hasCode` 判断，报错列出 `noCode`（从 `test/TestCompile.lean` 移来），消息同旧。删除：`node`、
    `code`、`share`、`spine`、`body`、kernel twin（`kernelTwin`、`lams`、`RM`）、`Expand.number`（`Tm.number`
    取代）、`Tm.kernelNode`/`offKernel`/`onKernel`。保留 `primFit`：`once` 用它判断对象变量是不是数对象，
    `rowGens` 用它生成。
  - ✅ 7.3c 续（分支 `shares`）：`Code.program` 建的表满足 `Codes.Shares`，定理 `Code.program_sound`
    （`Rel/Lang/GenSound.lean` 末）：各定义的每个 `share` 部分闭（`GenHyp fun _ R => R.fv = []`）时，
    `Code.shares (Code.program ds).2` 对 `Val.empty` `Sound`，且每个编号后的项满足 `GenHyp …sh.Shares`，
    `Tm.gen_sound` 对它适用。为此 `Tm.number` 改为全函数（`termination_by t.size`，经 `Tm.mapMSz`：`Tm.mapM`
    带子项 size 证明，`Tm.mapM` 由它定义）：旧的 `partial` 版本在 HashMap 命中时返回 `.share k t`（`t` 是新部分，
    与槽 k 的项只有 opaque 的 `Expr` key 相等，不可证），现在返回槽 k 自己的项（`Tm.numberSlot`）；`emit` 只写
    槽号的常量，发出的程序不变。证明的各层：`Res.Slot`（项逐字读表）、`Code.shares_sound`、`numberSlot_spec`、
    `Tm.mapMSz_spec`、`Tm.number_spec`、`Code.program_go`。
    剩余缺口：发出的常量 `n.shares`/`n.c.t<k>` 等于 `Code.program` 的输出这一点没有证明（`emit` 经 `Expand.tmE`
    把项写成 `Expr`，`tmE` 的 round-trip 只由 `GenSoundTest` 测）。
  - ✅ 7.3c 续（分支 `tmeround`）：缺口由检查关闭，不是证明。`emit` 在写完所有槽常量和编号后的项之后，把它们
    一次 `evalExpr` 成 `List Res`，逐个与 `Code.program` 的输出比较（`Tm.diffAt`，槽常量逐个查，`share` 只比槽号，
    `Tm.numberKey`），不同就拒绝该程序；每个程序、每个写出的项都查，不再只抽样。`Tm.fieldsEq` 比较 row 的全部
    字段（原来只比 `sym`），`OExp` 加 `BEq`。不能证明的原因：`Lean.Expr` 在 Lean 的逻辑里没有语义，
    `eval (toExpr t) = t` 无法陈述；kernel `decide` 也不可行（`Code.program` 用 `Expr` 的 hash 作 HashMap key，
    `String.hash` 是 opaque extern；`Tm` 没有 `DecidableEq`，payload 按 `valEq` 比较）。信任的只剩 Lean 的
    求值器与 kernel 一致。发出的程序不变。
- ✅ 7.4 清理：`LR unused`、`unused-simp`、`remove-import`。声明 0 个删除（`unused` 只删未用 binder，且每个声明都有引用或属交付物）；
  未用 simp 参数/binder 共 41 条 simp 语句修改（15 个文件；RepWF 的 7 条在合并 master 时放弃）；未用 import 1 条（`Run.Table`→`Run.Cols`；`Lang.Table`→`RepCols` 被 `Arr.pos_get` 需要，保留）。
  避开 GenSound/Tm/Den/GenK*/Csv/Coc 文件；`lean-refactor` 自带的验证 build 因 OwnTest `#guard_msgs` 误报，改用完整 `lake build` 验证。
  7.4b ✅ 声明级清理：删除无引用声明 219 个（5 轮至不动点；排除 `Rel.Core`、PLAN/Makefile/允许表点名的、带
  extern/simp/instance 等属性的、GenK*/GenSound/List/RepTabDiv/Fix/Power/Where）。7.4c 合并 master：保留 master 仍引用的
  `ones_eq`（被 private `fieldByte_eq` 引用，index 看不到）与 6.13 已证定律 G1/G2/S1（`kgather_pos_ix`、`kgather_pos_e`、
  `kscatter_pos_ix`）；合并后新变为无引用的 4 个一并删除（`toUInt64_two_pow_sub_one`、`Tm.Sub.den`、`copySlice_end`、
  `elemsW_alpDecode`），合计仍为 219 个。
- ✅ 7.5 已合并（dbdc72d，`gates3`）：gate `bang`（allowlist 32）、`pointfree`（13）、`kernel-tested`（68 of 84）；`pointfree` 的范围 = L。原条目，规则 gate（owner 选）：三个 gate，allowlist 只减不增：`!` 下标（今天 32 个 def）；关系值 def 的 body 里的
  `∃`（`Rel/Lang/Den.lean` 11 个 + `thinLDen`）；测试 module 里用到的每个 extern（85 个里 69 个没有被用到）。
  分支 `gates3`。另：`CLAUDE.md` 的 14 条规则里 9 条没有 gate。

### P8 存储简化（存储审计，2026-11-21；owner 2026-11-22 列入）

- ✅ 8.1 `Tab` 的规范序由产生它的一步给出，已规范的表跳过 `canon`（分支 `canonfld`）。`canonfld2`：`ldivOf`（`ldiv`
  去掉两个输入 `canon`），`ldivSel` 的回退除法作参数；`Tab.rdiv`、`GenK.rdiv`（两个 `conv` 答案）走 `ldivOf`，
  `inits`（`prefix` 是 `comp` 答案）走 `lamOf`。每次 `rdiv` 走计数分支省 2 次 `canon` = atom×atom 时 10 次 kernel
  调用（每次 `kasc`、`kseen`、`kgather` 各 1，加每列 1 次 `kgather`），位矩阵分支不变；每次 `inits` 省 1 次 `canon`。
  `GenK.E` 一项取消：Tm28 B1 删去了 `GenK.E`，`E(R)` 现在就是 `GenK.lam` 套 `GenK.comp`，其 `lam` 输入仍是位矩阵
  读回（`Tab.ofBits`），不是 `canon` 答案，所以与 `lam` 的其余输入同样处理。`tau`/`thin` 的 `lam` 输入（`idU`、`diff`
  答案）不是 `canon` 答案。`canonfld3`：`tails` 的 `lam` 输入是 `uncat` 答案，`uncat` 最后一步就是 `canon`
  （`Tab.uncat_canonical`），所以走 `lamOf`；每次 `tails` 省 1 次 `canon` = 9 次 kernel 调用（`kasc`、`kseen`、
  `kgather` 各 1，三个 `arr` 列各 `lo`、`hi` 2 次 `kgather`）。
  余下的 `canon` 都必须留，按两类：
  - 产生新行的一步，答案的序与重复由这一步决定，`canon` 就是给出规范序的那一步：`conv`（两边对调，序变）、
    `compExpand`（展开有重复）、`union`（`concat`）、`mem`、`nil`、`lamOf` 末尾、`asc`、`cross`、`outl`、`outr`、
    `inl`、`inr`、`cat`、`snoc`、`cons`、`zip`、`uncons`、`unsnoc`、`uncat`、`sumOn`、`length`、`atPos`、
    `positions`、`map`、`GenK.val`（字面量）、`Table.canon`（文件读入）。
  - 规范化输入的一步，其调用方的输入都不是 `canon` 答案：`lam`（`GenK.lam` 任意 `R`；`tau` 的 `idU`；`thin` 的
    `diff`）、`ldiv`（`GenK.ldiv`、`GenK.ldivM` 任意 `r`；`ldivM` 回退的 `s` 是 `ofBits` 读回）、`keepBits`
    （`meetV` 任意表）、`nu`（`GenK.nu` 任意 `S`；`hylo` 的 `N` 是 `mu` 答案，即 `pack` 过的 `union` 答案，
    `pack` 重写列，所以不是 `canon` 答案）、`star`、`sumsOn`（行参数任意）、`showRel`（打印）。
- ⬜ 8.2 稠密 sum。例：`long+sym` 三行 `inl 7, inr x, inl 9`，现在存 `tag=[0,1,0] idx=[0,0,1] l=[7,9] r=[x]`，
  改为 `tag=[0,1,0] a=[7,0,9] b=[0,x,0]`：每边一列 n 行，不属于该边的位置填 0（全 0 的块宽度 0，只占块头）。
  去掉 `idx`、`Vals.cols` 里把两边 gather 回 n 行、concat 时平移 `idx`、`Obj.dflt`；`inl°` 是按 tag 选行再 gather，
  不排序（今天 5 次排序）。`(A+B)+C` 按层递归：每层一列 `u1` tag，k 元 sum 有 k−1 列 tag，不另定三元存法。
  涉及 `Vals`（Core.lean:652-693）、`Vals.gather`、`Vals.cols`、`Vals.concat`、`injCols`/`inl`/`inr`/`inlConv`/
  `inrConv`（Struct.lean:57-125）及 `RepStruct` 的 `*_holds`、CSV/own 的 sum 列、Rust 侧 sum 的读写。
  与 rq17 的关系：`atom+1` 走块内 null 码（决定 K，`nullband`），不经 8.2；其余 sum 用 8.2。
  在 `nullband` 的 unit 对象决定（M/N）之后做，因为两者都改 `Vals` 的 sum 分支。
- 🔄 8.3 一种编码（分支 `foronly`）：`Ext.Enc` 只留 `foR`、`pos` 与 `gen`。已做：删 `bytes`、`alp`（Lean 类型与
  `WF`/`raw`/`get`；`Enc.ofBytes` 是每个定宽列进入 foR 的唯一入口；`answer`/`encode`/`alpOf` 删除；own 格式 v5，
  拒读 v4 及 kind 0/3；Rust `blocks::tag` 重编号 `FOR=1 ENUM=2 POS=4`）。
  留下：Rust ALP 内部（`alp.rs`、`enc.rs`、kwin、ffi `CCocf`）删除，进行中。
  已做（分支 `symdict`）：删 `Enc.syms`/`Enc.enum`（Lean `WF`/`raw`/`get`、`SymsWF`、`symKey`/`symCmp`、`idWidth`、
  `symsOf`；Rust `tag::ENUM`、`Src::Ids`、own kind 4）。`Enc` 现在是 `foR`=0、`gen`=1、`pos`=2，Rust `FOR=0 POS=2`；
  `QAtom.sym : UInt64` 是编号，`width .sym = 8`，`orderKind .sym = i64`，所以 `asc`/比较/`seen` 在编号上原样跑；
  own 仍是 v5（kind 2 含义不变，Lean 写端从没写过 kind 4）。测试按 `ctorIdx` 读 tag；`crate/src/tag.rs` 由
  `gates tags Rel.Kernel.Value` 生成，`make tags` 检查它与 Lean 一致。
  已做（分支 `symdict3`）：字典 `Table.Dict = Tab .long (.arr (.atom .char))`（§0.2 的 `ℕ ⟶ [C]`）。
  `Table.intern`：`R` = 文本按行的 frame，`D` = `ran R` 的 frame（`Tab.ran` 排序、去重），id = `R ≫ D°`；所以 id 序 =
  文本序，没有新 kernel、没有 hash。`Table.decode`：`I ≫ D`，id 超出字典即报错。CSV：`symText` 把 sym 列当
  `.text char` 交给 `Db.csvRead`/`csvWrite`（Rust 不变），`internCsv`/`decodeCsv` 在三段文本与一段 id 之间换；
  `readCsvDicts` 返回表与各 sym 列的字典，`writeCsv ds` 经字典写回。own：`writeSym`/`readSym`，id 列 `p` 旁边是
  普通文本列 `p.dict`，没有新 kind；读时拒绝未排序或有重复的字典、拒绝无文本的 id；`readArr` 不再拒绝 sym。
  `TestTable` 的 `#guard_msgs`：CSV sym 列往返相等，任意两行 id 的序 = 文本的序，own 往返相等。
  已做（分支 `83s6`）：程序（`n.io`）带一个字典（§0.2 一库一字典）：`TmGen` 从 `Dict.empty` 起，按输入顺序把每个 CSV
  输入的 sym 列经 `readCsvDict` intern 进同一个 `D`，所有 `writeCsv` 经最后的 `D` 解码；两个输入的同一串是同一 id，
  `∪`/`∩`/join 直接在 id 上，无需重映射。展开时 `Db.Csv.symText` 后再查 `schema`；`Table.readCsv` 删除；EmitC 拒绝 sym CSV 列。
  已做（分支 `symlib`，`bc4836c`，主人决定 N/Q/O 2026-11-22）：一库一字典。库 = 表目录的父目录（`Table.lib`），表
  只靠所在位置记它的库，不另存字段；字典即 `writeDict` 的 `<库>/sym` 与 `<库>/sym.rank`（`libDict`：缺则空、缺一部分
  即报错）。更正上文：`intern` 的 id 序不是文本序——新串接在 `D` 之后、按首行序（代码已如此），序只经 `rank`。
  程序在展开时定它的库（`progLib`：读或写的 own 表中有 sym 列者，须同一库），字典 `d` 从该库的字典起（不再从
  `Dict.empty`），CSV 输入的新串接在其后；own 输入的 id 原样读、对 `d` 检查（`readOwn`/`checkSyms`）；own 输出先把
  `d` 追加进库的字典（`writeLib`：库的字典须是 `d` 的前若干行，否则报出第一个不同的 id），再原样写 id
  （`writeOwn`）。两库相遇：展开时报错 “the symbol columns of `a` are ids in the library L₁ and those of `b` in the
  library L₂, two dictionaries, so they cannot meet; convert one to its texts with `unenum` (`I ≫ D`)”——按程序判，
  不按 `∩`/join 的数据流判，因为一个程序只持一个字典。`Table.unenum (I : A ⟶ sym) = I ≫ D`（`Tab.comp`，无新
  kernel），`decode` 是它在 frame 上的特例。未做：语言里的 `unenum` 行——字典 `D` 还不是 `Tm` 的项，须先给 `Tm`
  一个字典项（请求）。测试：`TestTable`（两表同库共享 id、追加违例、`progLib` 报错、`unenum` 往返），`TestIO`
  （`libAIO`/`libBIO`/`libMeetIO` 端到端、`twoLibT` 报错）。
  `symdict3` 的 gate：full build 399 jobs 0 error 0 `sorryAx`，GenSound 1594/1594；`make tags`（`Gates.lean` 改用
  `.str _ s`，`Name.lastComponentAsString` 在 v4.28 不存在）、`decode-allow`、`panic-allow`、`bang-allow`、
  `pointfree`、`native`、`build.sh syms` 通过；`cargo test --features std` 82 passed。138→82 的落差在 master 的
  b59ffda..000ce33（a837f6c 删除死代码的测试，随后恢复主体仍活着的；ALP 删除）；symdict2 只删了 `ids.rs`
  `at_and_max`（`id_at`/`ids_max` 已删）与 `own.rs` `check_symbols`（kind 4 已删）。`compile-diff` 只在 main 跑。
  已做（分支 `symdict4`，基于 5120a48，决定 E 2026-11-22）：整个数据库一个字典，只追加（q 的 sym 文件）：新串取下一个
  id，旧 id 不变，数据列不重写；id 相等 = 串相等；序经 `rank = iasc(D)° = D ≫ asc(ran D)°`，字典增长只重算 `rank`。
  `Table.intern D x`：`N = ran R − ran D`，`F = Λ((R ≫ N)°) ≫ uncons ≫ π₁`（新串到首行），`D'` = `D` 接 `F°`；id =
  `R ≫ D'°`。own：`writeDict`/`readDict` 写库目录的 `sym` 与 `sym.rank`（拒绝重复的串、与字典不符的 rank），
  `writeSym`/`readSym D` 只写读 id（拒绝无文本的 id）。CSV：`readCsvDict D`、`writeCsv (Option Dict)` 共用一个字典。
  序：`Obj.ascBad` 拒绝 sym（`asc`/`iasc` 经 `rank`）；`<`/`≤` 本来就拒绝 sym（`ordNum .sym = none`）。未做：`<`/`asc`
  行要接 `rank`；程序读库目录（own 格式）的 sym 列时从 `readDict` 起字典。
  `symdict4` 的 gate：full build 399 jobs 0 error 0 `sorryAx`；`make decode-allow panic-allow bang-allow pointfree
  tags native`、`build.sh syms` 通过；`cargo test --features std` 82 passed；compile-diff 与 `test/compile-diff.json`
  无差异（`TestCompile` 要 `CAP_MEM_MB=20000`，默认 12288 MB 时 qlean kernel 分配失败）。
  `gen`（`general`）随 8.4 与 `QValue` 盒子一起删。未定：float 今天存原始 IEEE 位的 foR（无损、已 WF）；改成
  保序位映射会改变每个 float kernel（比较、`asc`、`min`/`max`）的语义，单独做。
  - 🔄 `nullband2`：`Obj.one`（`El = Unit`，不存列）已加，单元素对象 elaborate 成它；CSV 可空列 4 部分 → 3（去掉 null
    payload）。`1` 的一边与其他边一样有 own 文件（kind 5：头里的行数，0 个 part；`Plan.cols` 给出 `.inl n`），
    顶层 `.one` 或 `A×1` 从 own 文件读回时过 `same`。`nullband4`：生成代码里 `1` 的一边是 `Gen.oneV n`；
    `Vals.gather` 在 `.one` 上 gather 位置列 `.pos` 再丢掉，越界的下标照样报错；CSV 里 `1` 的一列是它唯一元素的名字
    （long 列，code 0），`S+1` 的右边 `1` 不占列、行数是 null 行数（`tagCount`）；`Arr.opt`：按 `foRNul` 把元素读成
    `Option`。剩：`Vals (.sum (.atom t) .one)` 改成一列带内 null（`Vals`、`row`、`rowsImpl`、`gather`、`concat`、
    `cols`、`pack`、`readVals`/`encVals`、CSV 各加一支，`RepCanon`/`RepCols`/`RepTabDiv`/`GenKBits` 里每个对
    `.sum a b` 的归纳都要先分出这一支）、可空 foR 写入器（新 extern，Lean 体 = Rust）、kernel 判 null、
    CSV 可空列 3 部分 → 1、decode-allow 收缩。
    已做（分支 rq17）：可空 foR 写入器 `Coc.encodeNul`（extern `qlean_coc_encode_nul`，Lean 体 `encodeNulAt` =
    Rust `enc::encode_nul`）：块的 base/max/sum 只取非 null 行；含 null 的块置 `nulAt` 位，null 行写顶端残差
    `2 ^ d - 1`，值已占顶端时宽一位；不打补丁；逐块写编码，不解码。`foRMeta` 的块偏移按宽度字节的低 7 位算（与
    `widthAt` 同读法）。`CocTest`：三对 `decide`/`#guard`（混合块、全 null 块、无 null = `encode`）与 `foROpt` 读回；
    Rust 测试 `encode_nul_puts_nulls_in_band`。剩：`Vals` 的 sum 分支及其后各项（见上）；待主人定：null 码是否
    每块都留（见交接报告的代价）。
    rq17b 第 1 步已做：写入器只有一个。`Coc.encodeAt lg w x patch nul`（`nul` 默认空位图）/ `Coc.encode w x nul`
    （extern `qlean_coc_encode`，`qlean_coc_encode_nul`、`encodeNul`、`encodeNulAt`、Rust `encode_nul` 删除）；
    块步 `Coc.planBlock … nul b`：块内有 null 走 `nulBlock`（置位、不打补丁），否则走原 `blockOf`+`planOf`。
    “每块都留 null 码”只改 `planBlock` 这一处。Rust：`Sink::write_nul`、`enc::move_blk` 按块分 `nul_meta`/`nul_pack`
    与 `for_meta`/`for_pack`。`Encoding.foRBits_encode`、`planBlock_bounds` 以空位图陈述（`bitAt_empty`）。
    剩：第 2–5 步（`Vals (.sum (.atom t) .one) := Arr t n` 及其各用处、kernel 在块上判 null、CSV 3 → 1、decode-allow）。
    🔄 nullband 第 2 步，列类型已做：`Opt t n`（`Run/Core.lean`，`Arr t n` 去掉无 null 条款）：`Opt.get` 经
    `isNul`（`foRNul`，不解码）读成 `Option`，`Opt.ofAtoms` 经 `Coc.encode … nul` 写，`Opt.gather` 经 `kgather`（null 随行
    搬运），`Opt.ofArr` 即 `inl`。`TestNullband`：i64、u1 列三块都有 null 往返；无 null 不置标志；gather 保 null。
    未做：`Vals (.sum (.atom t) .one) := Opt t n` 本身——`Vals` 的 `.sum` 分支与 `.sum (.atom t) .one` 重叠，`Vals`、
    `row`、`gather`、`concat`、`cols`、`pack`、`readVals`/`encVals`、CSV 与 `RepCanon`/`RepCols`/`RepStruct`/`RepWF`/
    `ObjOrder`/`GenKBits` 里约 90 处 `.sum a b` 匹配都要先分出这一支；`general` 无块，`general+1` 不能带内。
    ✅ nullband2：`Opt.kgather_wf`（`Gather.lean`，取代 `Arr.kgather_wf`，`Arr.gather` 经 `Opt.ofArr` 用它）证明带 null 的源
    gather 后仍 `Enc.WF`（非 null 的行读源的非 null 行，`raw_kgather` 的 null 位），`Opt.gather` 的运行时判定删除。
    `TestNullband` 加 `#guard`：`kasc` 把 `3 0N 1` 排成 `iasc = 1 2 0`、gather 出 `0N 1 3`；可空键 join（`kasc ≫ kseen`
    分组）`0N 2 5` × `5 0N 7` 得 `(0,1) (2,0)`——null 配 null。两者只经 `Opt.get`/`isNul`，不依赖 null 的残差。
    主人定（null 次序，随 q）：null 小于每个值，`atom+1` 上 `inr ∗ < inl a`（q 的 `asc 3 0N 1` 是 `0N 1 3`），doc §4
    "atom+1" 卡片已改。主人定 O：null 码从块的顶残差移到残差 0（带标志块里值存成残差 + 1），块内比码即 null 在前；
    `nullbot` 改 `foRNul` 与 Rust，其他证明与 `#guard` 只经 `foRNul`/`Opt.isNul`。
    ✅ nullorder（随 q 次序，一般的，不特判 `.one`）：每个 sum `inr` 在前。`Obj.key` 是 `inl ↦ 1 ::`、`inr ↦ 0 ::`
    （`Obj.lt_inr_inl` 取代 `lt_inl_inr`）；`Vals.cols` 的 sum 键列是 `colMap .not … .u1` 的 `¬tag`，`tag` 本身由
    `foROk` 查（`kasc` 不再读它）；新引理 `colMap_not_u1`（`RepCanon`：结果是 `Arr .u1 n`、元素 = `!tag.get`）；
    `Vals.cols_sum` 给出 `nt` 与 `Valid tag`，`lt_of_codes`/`row_of_codes`/`codes_of_row`/`cols_wf`/
    `gather_ok_of_cols` 随之改。`ObjOrder` 加 `#guard`：`i64+1` 上 `inr ∗` 的键小于 `inl 3`。所建测试模块无钉住的
    sum 次序要改。`Vals` 换 `Opt` 之后 `atom+1` 的键是 `nulCodes`，已是 null 在前，与之一致。
    ⬜ nullband3（下一步，不再被挡）：`Vals (.sum (.atom t) .one) := Opt t n`。`.sum a b` 对变量 `a b` 不再归约，约 90
    处匹配各加一支。分部分做，每部分一个 agent、各自建绿：
    - nullband3a：`Run/Core`（`Vals`、`row`、`gather`、`concat`、`cols`、`pack`、`readVals`/`encVals`）+ `Gather` +
      `TestNullband`。
    - 之后按 import 次序每个 Rep 模块一部分：nullband3b `ObjOrder`、3c `RepCanon`、3d `RepCols`、3e `RepOrder`、
      3f `RepStruct`、3g `RepWF`、3h `GenKBits`（及建时报错的其余模块，各按 import 次序接在后面）。
    主人定（F）：null 码只在含 null 的块里留（宽度字节 bit 7），无 null 的块照旧走普通 foR 计划——无 null 的块不付任何
    代价，读者仍只有一条路径（每块判一次标志位）。`planBlock` 现状即此，不改。
    rq17c 发现：第 3 步必须先于第 2 步。`kgather` 今天是 `wordsFoR (gatherWords (foRWords ix) (foRWords e))`，`wordsFoR`
    以空位图编码，所以 null 行被读成它的残差字、写回时成了一个值。例：块宽 3、frame 0，第 2 行 null 存 `7`；gather
    `[2]` 得到一列 `[7]`、无标志——`Vals.gather` 在 `atom+1` 上 = `Arr.gather` = `kgather`，`gather_row` 不再成立。
    同理 `kscatter`（`foRWords`/`wordsFoR`）、`kasc`/`kseen`（比的是原始字：块 A 的 null `7` 与块 B 的值 `7` 相等）。
    顺序：先让 `foRWords`/`wordsFoR` 成对携带 null 位（`(words, nuls)`，kernel 体把 null 位当作值的一部分 gather /
    scatter / 比较），Rust 生产者经 `Sink::write_nul` 写出；再改 `Vals`。
    null 语义（按原则定：Rel 的名字与语义随 q）：`asc`/`iasc` 中 null 排最前；`seen`/distinct 中所有 null 相等、与任何值
    不等。`gather`/`scatter` 的下标为 null 是错误（null 不指任何行）；`scatter` 只有 `.last` 搬运 null，其他 op 遇 null
    是错误（不给出无定义的值）。
    rq17d（第 3 步，WIP）：kernel 体已改。`Scatter.lean`：`hasNul`（只读宽度字节）、`foRNuls`（每行 null 位作字，
    `foRNul` 判块）、`noNul`、`nulMap`、`wordsFoR ws (nul := .empty)`；`kgather`/`kscatter` 用同一下标搬运 null 位；
    `Asc.nulCodes`：含 null 的原子列编码成两列（null 0 / 值 1；值码在 null 处取 0），`kasc` 搬运 null 位，`kseen` 经
    `ascCol` 自动得到 null 相等。无 null 的列走原路径，字节不变。Rust：`Coc::is_nul`/`nuls`（只读带标志的块）、
    `exports::scatter::no_nul`、`gather::enc`/`scatter::blocks`/`ffi::asc::kasc` 经 `Sink::write_nul` 写出，`asc::Col::Nul`
    与 `asc::work` 返回多列。`cargo test --features std` 通过。剩：`KernelSpec` 的定理对含 null 的输入不再成立（例：
    `raw_scatter` 的结论 `o = wordsFoR ws`；`ascKeys_row` 说行码只依赖原始字），已给 `raw_scatter`/`kscatter_pos_ix`
    加 `hasNul e = false`；其余（`KernelSpec.Asc`、`KGather`、`KSeen`、`Closure` 及 Rel 下约 50 处用法）待做，见
    `tmp/handoff.md`。
    ✅ rq17h 主人定 B（29e12ef）：补丁表 `exc_off` 改 u64，`2^32` 行以上的列照常打补丁；`encodeAt` 的门槛成 `n < 2^64`
    （u64 计数自身的上限），`excBlob_*` 前提 `< 2^32` → `< 2^64`；own 格式版本 5 → 6，旧文件按名拒读。每块 +4 字节。
    rq17merge：rq17f12 的 null 位图与 u64 补丁表合并后，`USize` 行数 `< 2^64`，`wordsFoR_nul`/`foRNuls_wordsFoR`
    不再带 `hbig`，`asc_col_row`/`kasc_grade` 不再要 `< 2^32` 行。
- 🔄 8.3 `Enc` 只留 foR（分支 `foronly`）。今天 7 种：`bytes`（字面量、`ofAtoms`、`blank` 仍产生，进 kernel 前再转
  foR）、`alp`（`alpOf` 仍产生）、`syms`/`enum`/`gen`（运行路径上没有产生者）、`foR`、`pos`。float 存保序位映射的
  foR 字，`sym` = foR 编号 + 排好序的字典（§4.2），own 文件升版本。`pos` 去留待 owner（O/P）。
- 🔄 8.4 `Arr t n := {e : Enc // Enc.WF t n e}`。原来 `{v : QValue // v.WFAt t n}`：每列一个 `.vector t n enc attr`
  盒子，`t`、`n` 在类型参数里已有又存一遍；`attr` 只有 2 处读；`QValue` 的 `dict table keyed slices func err enum`
  只在 `Kernel.Value`、`Run.ValEq` 用；own 文件头的 `attr`、`domain` 写了没人读。去掉 `QValue` 盒子与 `general`
  （`Carrier .general = QValue`），文件格式升版本。在 8.3 合并之后做（同改 `Enc`/`QValue`/`general`）。
  ✅ 盒子已去（分支 arr84）：`Arr t n := {e : Enc // Enc.WF t n e ∧ Kernel.hasNul e = false}`；`Arr.mk` 无 attribute
  参数，`Arr.of t n (e : Enc)`；`Plan.cols` 给 `SideCol = USize ⊕ Σ t k, Arr t k`（`checkSyms` 直接拿到
  `Arr .sym k`，不再经 `Arr.of` 重查）；`Db.ownFile t n e`（enum 分支删，头里 `attr`/`domain` 写空）；
  `Expand.valsEq` 比 `t`、`n` 与 `encEq`；`Table.encOf` 删；`QValue.marking` 删（无使用者，8.4b）。`general` 不需要盒子：它的列是 `Enc.gen xs`，
  仍是 `Arr .general n`。
  ✅ own 文件头 v7（8.4b/8.4c）：字节 8 版本 7、9 类型码、10 kind、11 part 数（u8）、12..16 零、16..24 count，
  `attr` 与 domain 名去掉（`OwnFile {code kind count parts}`，Rust `own.rs` 同改，`test/native/in` 重写）；
  `ownParse_ownImage` 在 `ByteArray` 形式上重证；plan 的列寄存器按名读（`Side.regs`/`Side.count`/`Side.enc`）。
  剩：删 `general`/`Enc.gen` 与 `QValue`（`Carrier .general`、`ValEq`）。
- ✅ 8.5 `Obj.arr` 的 `0 ≤ lo ≤ hi ≤ m` 作为不变式，只在 `readVals` 查一次（分支 `lohi`）。例：payload `m = 5`，
  一格 `lo=2 hi=7`，今天每个读者都算 `min(hi,m)=5`：一次 `∋` 3 次 `colMap` + 2 次 `colConst`（Div.lean:20-30），
  一次 concat 4 次 `clampShift`。改后 `readVals` 拒收 `hi>m`，产生者（`cons°/snoc°/cat°` 等）给出证明，不再 clamp。
  - ✅ 入口检查（分支 `lohi`）：`readVals` 的 `arr` 分支拒收 `lo<0`、`lo>hi`、`hi>m`，报 `.lo` 文件、行号、`[lo, hi)`
    与 `m`；`TestTable` 三个拒收例。
  - ✅ 不变式作为谓词，不加字段（分支 `lohi2`）：`Vals.WF`/`Tab.WF`（`RepCols`，`arr` 处 `0 ≤ lo ≤ hi ≤ m`，
    递归经 `prod`/`sum`）；`readVals` 的检查抽成 `cellBad`（`Run/Cols`），`cellBad_none` 即 `WF` 的格子条款；保持引理
    `Vals.gather_wf`、`nub_wf`、`Tab.canon_wf`、`catSide_wf`、`catSummand_wf`、`concat_wf`（`RepCols`），
    `Vals.cells_wf`、`tau_wf`（`RepTabDiv`，由拆出的 `cells_spec`、`tau_spec` 给出，`cells_row`/`tau_row` 也改读它们）。
  - ⬜ 删 clamp（未做，阻塞）：删任一 clamp，其定律（`concat_row`、`mem_holds`、`pack_row`、`cellSpan_spec`）要输入
    的 `WF`，传递依赖 183 个定理（GenSound 41、RepTabDiv 35、GenKFold 26、GenKBits 22、GenKSpec 18 …）。输入来自程序
    算出的任一 `Tab`：`rowOK_mem` 的 `X` 取自任意 `Known` 的 `K.dom`，`Rel.Reps` 对一切 `K` 量化。已有的槽是
    `Rel.Wf`（`GenKBits`，`.tab _ => True`，经 `Code.Wf`/`Sound` 进 `gen_sound`，91 个 `_wf` 引理）：改成
    `.tab (.ok t) => Tab.WF t`，加 `Known.WF`，`Reps` 只在 `Known.WF` 的 `K` 上要求；然后 91 个 `_wf` 各证其 op 保持
    `Tab.WF`（上面的保持引理是底），`Tab.lam` 要 `kseen`/`kscatter .add` 计数规格，`Vals.cells` 的调用处要 `expand`
    的前缀和 `≤ T`。
  - 🔄 各 op 的保持引理（分支 `lohi3a`，`Rel/RepWF.lean`）：结构、集合、`comp`、bits、除法、比较、`inl°/inr°`、
    `length`/`atPos`/`asc`/`est`、`nil`/`lamOf`/`lam`/`E`/`tau`/`setify` 已证；`fixOn`/`mu`/`nu` 以 `Tab.pack` 保持
    为前提（`Vals.pack` 经 `Vals.cells`）。修了 `lamOf` 的错：`r` 无行时格子 `[f+c, f+c)` 指向 `m = 0` 的 payload 之外
    （例：`D` 3 行、`r` 空，组 0 是 `[1,1)`，`hi = 1 > 0`），改为 `nil D`；`lamOf_canon` 多给 `U.WF`。未做：`List`
    （`cells` 调用处，用 lohi3b 的 `expand_spec`）、`thin`/`thinL`/`merge`/`loop`/`foldRounds`、`Arith`、`Cast`、
    `Where`，以及 `Rel.Wf` 的切换本身。
  - ✅ `List` 与 `pack` 的保持引理（分支 `lohi4a`）：`Vals.pack_wf`/`Tab.pack_wf` 已证，`fixOn`/`mu`/`nu` 去掉
    `hpack` 前提；`cat`/`snoc`/`cons`/`zip`/`uncons`/`unsnoc`/`uncat`/`prefix`/`suffix`/`inits`/`tails`/`sum`
    已证（`Rel/RepWF.lean`），`positions` 并入 `positions_spec`（`Rel/RepWhere.lean`）。共用引理在
    `Rel/RepTabDiv.lean`：`Vals.cells_expand_wf`（`Vals.cells` 铺在自身宽度的 EXPAND 上，每宽 `≤ c`、`n·c < 2^63`）、
    `cellSpan_width`、`cell_wf_nat`、`cellSpan_start_le`（例：`uncat` 空格 `[SN, SN)` 要 `SN ≤ m`，由输入 WF 给出）。
  - ✅ 轮次、`thin`、值动词、`$`（分支 `lohi4b`，`Rel/RepWFOps.lean`）：`foldRounds_wf`（所有折叠共用）、
    `peelL`/`peelR`、`loop`、`merge`、`thinL`、`thin`、`arith`、`succ`、`cast`、`floatOp` 已证。合入 lohi4a 后
    `hpack` 换成 `Tab.pack_wf`，`ListWF` 删去、直接用 `cat_wf` 等；lohi4b 的 `positions_wf` 与 `positions_spec`
    重复，删去（连同只为它写的 `expand_span_lt`、`sum_countP_group`、`eval_ne`）。`map`/`flatten`/`filter`/
    `takewhile` 在 `foldRounds_wf` 上证完（`map` 的单趟分支用 `Vals.cells_expand_wf`）。不再有 WF 前提。
  - ✅ 合入 canonfld2（分支 `lohi5`）：`map_wf` 单趟分支由 `if` 条件取 `C.n = T`（例：`C` 的 payload 长 `C.n`，
    `cells_expand_wf` 要长 `T` 的，拆开 `C` 后 `subst`）；`ldivOf_wf`（`r`、`s` 已 canonical），`ldiv_wf` 经 `canon`
    调它，`ldivSel_wf` 对其除法 `d` 参数化（`hd : d R S UB UC = .ok t → t.WF`），`rdiv_wf` 用 `ldivOf_wf`，
    `inits_wf` 用 `lamOf_wf`。全量构建 0 error、0 sorry；TestCompile 982/982 相等，与 pin 无差。
  - ⬜ 切换本身（未开始）：直接依赖 `Rel.Wf`/`Rel.Reps` 的声明 136 个（GenSound 62、GenKBits 30、GenKSpec 25、
    GenKFold 10、GenKEst 3、GenKHylo 2、GenKFix 2）。步骤：(1) `Known.WF`（`dom`/`ran`/`pairs` 各 `Vals.WF`/`Tab.WF`）；
    `Rel.Wf` 改 `.tab (.ok t) => t.WF`、`.tab (.error _) => True`、`.lazy f => ∀ K, K.WF → (f K).Wf`，`bits` 加
    `ofBits` 结果 `WF`；`Rel.Wf.force`/`runE` 要 `K.WF`。(2) `lift1_wf`/`lift2_wf` 取 `f` 的保持引理与参数的 `Wf`，
    `ofVals_wf` 取 `f` 的（`K.WF` 给 `K.dom` 的 `Vals.WF`）；`compT` 在 `⟨some (ran r), K.ran, none⟩` 上 force，要
    `ran_wf`。(3) `gen_wf_spine` 每个构造子一行 `GenK.*_wf` + `RepWF`/`RepWFOps` 的 `_wf`；`primGen_ok` 的每个 row
    要其 op 的 `_wf`。(4) `Reps` 只在 `K.WF` 上要求，`Sound`/各 `_sound` 的 `∀ K` 加 `K.WF`。(5) 然后删 clamp。
  - 🔄 切换进行中（分支 `lohi6`）：
    - ✅ import 调整：`Arr.zeros_get` 从 `RepAsc` 移到 `RepWF`，`RepWF` 不再 import `RepAsc`（原来经它依赖
      `GenKFold`），`GenKSpec` import `RepWFOps`。于是所有 `Tab` 层 `_wf` 在 `Rel.Wf` 之上可见，`GenK.*_wf` 留在原处直接用。
    - ✅ `GenKSpec`（绿）：`Known.WF`、`BitsWf`、`Rel.Wf` 及 `force`（要 `K.WF`）、`retried`、`runE`（`Wf` 的值在
      `WF` 的 context 上只算出 `WF` 的表）移到 `GenKSpec`；`Rel.Wf` 的 `bits` 条款是 `BitsWf ∧ Vals.WF x ∧ Vals.WF y`
      （读回由 `Tab.ofBits_wf` 给 `WF`）。所有 `_sound` 的 `∀ K` 改成 `∀ K, K.WF →`；`lift1_sound`/`lift2_sound` 多取
      其 context 函数保持 `WF`（`hk`/`hkl`/`hkr`）；`ofVals_sound` 的 `hf` 多得 `Vals.WF X`；新 `cut_wf`、`bound_wf`；
      `pairOn`/`pairK`/`pair`/`diff` 的 sound 多取操作数的 `Wf`（它们在操作数算出的表的 `bound` 上运行另一操作数）；
      `cmp_side` 多取该侧的 `WF`；`succ` 的原子侧 `Vals.WF` 为 `True`。
    - ⬜ `GenKBits` 1683 起（`meetV_law` 之后的 meet/comp/ldiv 段）不通过：`meetOn_sound`/`meetK_sound`/`compT_sound`
      等要 `K.WF` 与 `bound_wf`、`Tab.ran_wf`；`_wf` 引理要真证明（`Tab.inter_wf`、`keepBits_wf`、`compSel_wf`、
      `compSelM_inl_wf`、`compTabMat_key_wf`、`ldivTabMat_sides_wf`）。之后 `GenKFold`、`GenKEst`、`GenKHylo`、
      `GenKFix`、`GenSound`（`Sound` 加 `K.WF`、`gen_wf_spine`、`primGen_ok` 每行 `_wf`），最后删 clamp。
  - ✅ 切换完成（分支 `lohi10`，0cddb58、f6abf97）：`Rel.Wf` `.tab (.ok t) => t.WF`，所有 `_sound` 取 `K.WF`；
    `gen_wf_spine` 对 `Tm.size` 强归纳（`hylo` 的 `kids`），每个构造子一行 `GenK.*_wf`；字面量 `val`/`uni` 在
    `Tm.gen` 以 `Vals.cellsOk` 检查格子（不经 `readVals`）。全量构建 0 error、0 sorryAx，GenSoundTest 1594/1594。
  - ✅ 删 clamp 第一步（分支 `lohi11`，50f6fa1、86a1805）：`Tab.mem` 不再把 `lo`/`hi` 夹到 `[0, m]`，按 `[lo, hi)` 原样读；
    `mem_holds`、`E_lam`、`E_holds`、`E_den`、`setify_den` 取 `Vals.WF X`；测试格子改成 WF。保留：`Vals.row` 的
    `filterMap`/`clampFin`（全函数模型）、`Vals.catSide` 与 `compBlocks` 的 `clampShift`（求和位置、块号，不是 lo/hi）。
  - ✅ 删 clamp 第二步之一（分支 8.5s2d–h）：`Vals.concat` arr 分支不再 `clampShift`，只把第二段移过第一段 payload
    （`Arr.shift` = 1 `colConst` + 1 `colArr .add`；每格 4 次 `clampShift` × 6 = 24 → 4）。`concat_row`/`concat_wf` 取
    x、y 的 `Vals.WF`，经 `cat/snoc/cons/zip/uncat/prefix/suffix/inits/tails/flatten/lam/comp/flat/positions` 的
    `_holds`/`_den` 传到 `GenK.*_sound`（多取操作数的 `Wf`）与 `gen_sound_spine`（`code_wf (gen_wf X η hs.2)`）。
    只加 WF 前提，无语句弱化；全量构建 0 error、0 sorryAx。
  - ✅ 删 clamp 第二步之二（8.5s2i）：`cellSpan` 删去，`pack`、`cat`、`zip`、`uncons`、`unsnoc`、`uncat`、`sumOn`、
    `Fix.map`、`length`、`atPos`、`Where.positions` 直接读格子的 `lo`/`hi`（每次使用 5 次 kernel 调用 → 0：
    2 `colArr .max` + 1 `colMap .min` + 2 `colConst`；`cat`/`zip` 每次 10 → 0）。`cellSpan_spec`/`cellSpan_where`/
    `cellSpan_start_le`/`Vals.cells_expand_row`/`expand_cells_le` 取 `Vals.WF` 的格子条款代替 `cellSpan` 的结果；
    `uncons/unsnoc/uncat/length/atPos/sum_holds`、`Vals.zip_row`/`zip_holds`、`Vals.pack_row`/`pack_holds`/
    `pack_toList`、`foldRounds_holds` 的 `hpack` 多取输入的 `WF`，经 `peelL/peelR_holds`、`mu/star_holds`、
    `nu_sound`、`comp_uncons`、`rowOK_*`（`ofVals_row_sound`/`after_row_sound` 已给的 `WF`）传入。只加 WF 前提，
    无语句弱化。`Vals.row` 的 `clampFin`（全函数模型）保留。
  - ✅ 删 clamp 第二步之三（8.5s2j）：C 发射器 `concatB`（`Lang/EmitC`）跟上 `Vals.concat`：`clampShiftB` 删去，第一段
    `lo`/`hi` 原样、第二段 `shiftB`（1 `constB` + 1 `mapB .add`）。每格 `lo`、`hi` 各 2 次 `clampShiftB`（每次 2 `constB`
    + 1 `wordsB` + 3 `mapB`）→ 第二段 2 kernel、第一段 0。剩下的 `sum` 位置 `clampFin`、`catSide`/`compBlocks` 的
    `clampShift` 是求和位置与块号，不是 `lo`/`hi`，不属 8.5。
  - ✅ 删 clamp 第三步（8.5s2k–s2p，内核改动 73a8853，下游 daa14c0…2ba4528、eb0d571；8.5s3 复核）：`kasc`/`kseen`
    的 `cells` 键按格子原样读：`Kernel.cellStart` = `lo` 的 `Int64.toNat`、`cellLen` = `hi.toNat - cellStart`，无
    `min … c`；Rust `Cells::span` 只 `max(0)`（对应 `Int.toNat`），无 `clamp(0, c)`。例：`c = 3000`、格子
    `[2990, 3005)`，原读 10 行，现在是非 WF 输入，`readVals`/`Vals.cellsOk` 拒收。`Vals.row_arr` 取该行格子的
    `0 ≤ lo ≤ hi ≤ c`，`cellFns_eq_iff` 取两格的 `cellLen ≤ c`（由 `Vals.cell_le` 从 `Vals.WF` 给出）；
    `cols_arr`、`codes_of_row`/`row_of_codes`/`lt_of_codes`、`select_ok`、`canon_pos_lt`、`sums_holds`、
    `seenKey_iff_row`、`lamOf_*`、`group_rows`、`compOne_canon` 一族、`inter_distinct`、`lamLaw` 与 `Tab.canon` 的
    读者多取 `Vals.WF`/`Tab.WF`，调用处由 `*_wf` 给出；无结论弱化。`AscTest.spans` 的 `hi = 3005` 改为 `3000`，
    `#guard` 与 Rust 一致。全量构建 0 error、0 sorry；`build.sh syms`、`pointfree`、`listban`、`bang` 绿。
  - ⬜ （旧方案，弃）类型不变式：`Vals (.arr b) n` 加证明字段 `∀ i, 0 ≤ lo i ≤ hi i ≤ m`。`Vals` 今天没有 WF 谓词（只有 `Arr` 的
    `Enc.WF`；`Rel.Wf` 是 `bits` 的），所以是新字段。阻塞：产生者的证明要 `colMap_get`、`Arr.gather_row`、
    `Arr.concat_get`、`Arr.zeros_get`（在 `RepCanon`/`RepCols`/`RepAsc`，`Run` 的下游），先把它们移进 `Run`；
    难的产生者 `Tab.lam`（`f + cD ≤ f + c ≤ N` 要 `kseen`/`kscatter .add` 的计数规格）、`Vals.cells`
    （前缀和 `≤ T` 要 `expand` 规格）、`uncons/unsnoc/uncat/zip`（`List.lean`）。每个 `⟨m, lo, hi, f⟩` 模式
    （`Run/*`、`GenKFold`、`GenKBits`、`GenSound`、`KernelWF.Read`、测试的字面量）都多一个分量。
  - 之后删的 clamp 与 kernel 次数（数 Lean body）：`∋`（`Tab.mem`）边界 2 `colConst` + 3 `colMap` + 宽度 1 `colMap`
    = 6 → 1（`colMap .sub hi lo`）；concat 的 `arr` 分支 4 次 `clampShift` × 6 = 24 → 3（1 `colConst` + 2
    `colArr .add`，只移第二段）；`cellSpan`（`pack`、`List.lean`）5 → 0（以上均已做）。Rust 侧 `asc.rs`
    `Cells::span` 的 `clamp(0, c)` 与 `Kernel.AscKey.cells` 的 Lean body 同一 commit 去掉（第三步，未做）。
- ✅ Tm28 B7（`doc/tm-minimal-design.zh.typ` §4）`star`：prelude 定义 `star(R) ≜ μX : 𝟙 ∪ R X`，`R*` 是它的记号
  （parser 不再造变量名）；fused 行 `star` → `Tab.star`（semi-naive：`(X, Δ)` 从 `(P, P)`，每轮只算 `Δ R − X`），
  `Tab.fixOn` 改为任意状态（`nu` `mu` 传 `Tab.n Tab.pack`，`star` 带前沿），定理 `Tab.star_holds`、`GenK.star_sound`、
  `rowOK_star`。`Party.guests` 改为 `(win boss° boss° ∪ ((𝟙 − win)boss°))* win`。行给 family 参数时的 lifting
  （对所有行，不是 `star` 特例）：`Prim.keyable`（对象全是变量，没有 `num` `ord` `whole`）的行由 `appliedRowL` 在
  `I×v` 上对 keyed 参数 `⟨π₁,Rᴵ⟩` 运行一次，结果 `rowSh = ⟨𝟙,⊤⟩⟨π₂,Xπ₂⟩` 是 family（`keyed` 认得它，给 `Xπ₂`）；
  `appliedL` 与 `useDef` 都走它，结果只由已有的 `Tm` 构造子组成，`gen_sound` 不变。`Chess.L` 删去，`r` `q` 写
  `(VD)*` `(De)*`（棋盘上 `R⁸ = 𝟘`，输出不变）。`starLinear : μX : S ∪ R X = star(R) S` 在 `Rel.Core.Rel`
  （`Rel/Core/Fix.lean`）证明；prelude 里 `rel_aop` 形式的陈述需要 freyd `relaop/RelAop/Prelude.lean` 的证明，未做。
- ✅ Tm28 B7c（b6b962a）lifting 由证明决定，不再按形状：删去 `Prim.keyable`，`Prim.keyLift` 只在 `Prim.KeyLifts`（行的意义与
  `keyOf F = ⟨π₁,Fᴵ⟩` 交换）有证明时设置，`Prim.keyLifts_ok` 由 `prims.filter keyLift = [starRow]` 列出全部义务；
  `star_keyOf`（由 `id/union/comp_keyOf` 与 `mu_keyOf`，`Rel.Core`，公理 {propext, Quot.sound}），`Tm.den_keyedRow`：lifted
  项的意义等于逐 key 的意义；无证明的行给 family 时报 `notLiftable` 并指名 `Prim.KeyLifts`（如 `$`，原形状测试会误放行）。
- ✅ Tm28 B8（§3.4）`mem inl inr` 升为 `Tm` 构造子，删行 `∋ inl inr inl° inr°`：`inl°` `inr°` 是 `conv inl`，`Tm.dem`
  对它为真（在需求的 sum 值上跑 `Tab.inlConv`），`Tm.convInj` 给它的 code，`elabE` 的 `.conv` 不再要求闭项；
  `Tm.memAt` 代 `Tm.kids` 里的 `∋` 行；codegen 复用 `Tab.mem/inl/inr/inlConv/inrConv`，无新 kernel。
- ✅ Tm28 B3（§1, §7）`dom ran nil` 不再是 `Tm` 构造子，而是 `prims` 行 `domRow ranRow nilRow`：`Tm.dom/ran/nil` 是造
  `.arg (.prim r) R` 的 def，`Tm.dom_den/ran_den/nil_den` 给其意义；`dom` `ran` 互为 `conv`（`Prim.den_conv` 以
  `Sem.one_corefl` 处理）；`Tm.kids` 的 `dom` 分支经 `Tm.idAt`；EmitC 的 `rowB` 按 `GenK.dom/ran/nil` 派发。

## 3. 各 phase 的并行与串行

| Phase | 步数 | 并行的 worktree（不共用 section）      | 串行                                        |
|-------|------|----------------------------------------|---------------------------------------------|
| P0    | 1    | —                                      | 0.1                                         |
| P1    | 3    | 1.3（freyd repo）与 1.1 并行           | 1.1 → 1.2；1.2 和 1.3 一起合并              |
| P2    | 6    | 2.1、2.2、2.4、2.5、2.6                | 2.2 → 2.3（`Den.lean` 的同一 section）      |
| P3    | 13   | 3.3 与 3.2 并行                        | 3.1 → 3.2 → 3.4 → 3.5 → … → 3.13，一个分支  |
| P4    | 5    | 无：每一步都编辑同样的 match 分支      | 4.1 → 4.2 → 4.3 → 4.4 → 4.5                 |
| P5    | 8    | 5.4a、5.4b、5.4c；5.2 与 5.3 并行      | 先 5.1；5.5 → 5.6 最后                      |
| P6    | 15   | 6.1、6.3；6.4、6.5；6.6-6.8；6.10 各组 | 先 6.0；6.2 → 6.4；6.9 → 6.10 → 6.11 → 6.12 |
| P7    | 4    | 7.5（独立分支 `gates3`）               | 7.1 → 7.2 → 7.3 → 7.4                       |

合计：8 个 phase，55 步（不含 dataframe D.1–D.12，✖ 不计；6.10 只计一次）。

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
  说 tag column 变成什么（i8，还是宽度 1 的 foR），也没有说装箱的 column 是否保留。1718 个 declaration
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
  kernel、与 `bytes` `bits` `syms` `enum` `gen` 并存的 `foR`）。每一个在一个 phase 的时间内都是同一事实的第二种形式，违反
  DRY 规则；每一个都有指名的删除步骤（3.12、3.9、6.11）。

给 owner 的问题：

| Q   | 问题                                                                                              |
|-----|---------------------------------------------------------------------------------------------------|
| Q1  | freyd：删除 `RelAop/Syn.lean`，还是把商移到 relaop 以保留 `Functor Syn RelSet`？                  |
| Q2  | 表层关键字 / `Pre.refold` 是否也变成 hylo？                                                       |
| Q3  | 答 M：`tab` 持有 `Option (Tab A B)`，`Tab` 是结构 `{n, key, val}`（3.1 的 rename）                |
| Q4  | 答 A：`Reps` 为 `K.dom ≫ rep t ≫ K.ran = K.dom ≫ T ≫ K.ran`；`tab none ↦ True`                    |
| Q5  | 答 L：`snoc`、`asc` 是 primitive；2.6 中每个 `+ slice` 行都是融合 kernel，由 `⟦row⟧ = ⟦def⟧` 联系 |
| Q6  | 没有 `d` 之后，Elab 在哪里插入今天由 `closeRes` 插入的宇宙前缀？                                  |
| Q7  | `Den` 的 inline：给 lean-refactor 加一个 unfold-abbrev 命令，还是把 `Den` 保留为 notation？       |
| Q8  | `Tm.symDiv` 的签名（宇宙参数同 `ldiv`？）及其表层语法。                                           |
| Q9  | `Tm.hylo` 的签名（保留 `k what ch body`？）以及把 `ch` 与 `body` 联系起来的前提。                 |
| Q10 | lam/E/thin 的 `Ordered`/`KeyInj` 假设在 `compile` 的类型中从哪里来？                              |
| Q11 | `Tm.den` 中 `call` 的含义（stage 5）：inline 被调用者的 term，还是一个 definition 的环境？        |
| Q12 | plan A 的 library 边界：证明移进 `RelRun`，还是把 `compile` 移出它？                              |

## 6. 构建与工作流（perf 会话，`/data/tmp/perf-report.md`）

2026-11-18 13:00–16:00 共 34 223 CPU-s：kernel 改动的重建范围 19 110，lean-refactor 7 887，compile-diff 4 211，
relk 线程池空转 2 526（与前三项重叠）。

- ✅ W.1 `Makefile`：gate 从 lake 列 module，不再依赖 `index`；整包目标在 worktree 中拒绝运行；compile-diff 排最后（5aba864）。
- ✅ W.2 cc-guard worktree 派发写明 build 命令：只 build 编辑过的 module 及其测试（6940c8d）。
- ✅ W.3 lean-refactor 扫描时 elaborate `#guard`/`#eval` 而不运行（4810844）。
- ✅ W.4 lean-refactor：`index` 为每个过时 module 起的 `syntax-rows` 子进程仍运行 relk，改为所有 elaboration 路径共用
  `Elaborate.headerEnv` 的不运行表（6706c7e）；`moduleNames` 移出循环（7406671）。6 个过时 module 的 `index`：
  105.4 s → 22.6 s wall，270 → 30 CPU-s。
- ✅ W.5 compile-diff 的耗时（owner 选 A，`w5a` 1dd5754 已合并）。按 `SPLIT` 以下的输入跑做不到：引起 split 的规模是各 program 自己的
  universe、字面表和 `muCap`，TestCompile 没有通用的开关，缩小还可能让收敛的定义变成 not ok。约 325 s 的分布：
  `Test.muGrow.g` 123 s（μ 每轮增长到 `muCap`=1024，225 920 次 split，本身 not ok）；`blocks.*`、`table.*`、`cycle.*`
  约 200 s，0 次 split（见 W.10）；其余每个定义 < 0.6 s。做法 A：TestCompile 先跑 `compile`，只在 `c.ok` 时
  `evalConst`，结果行不会变；split 由 W.6 消除。在 W.6 报告之后落地，前后各跑一次 `make check`。逐个 program 覆盖输入
  的做法不采纳：每个新 program 都要改一次。
- ⏸ W.5a `qlean_pool_stats` 移入 relk，即 `Rel.Kernel.poolStat`（worktree commit 65760d6，未合并）。只能和 qlean 删除
  qrs 那份 `qlean_pool_stats` 的 commit 一起合并，否则 qlean 链接时有两份同名符号。
- ✅ W.5b（分支 `pooltest`）：此前 rel 里没有测试走真实 `SPLIT`（8388608）以上的 pool 路径（`cargo test` 下
  `SPLIT_AT`=1，没有 Lean 测试读 pool 计数器）。现在 `pool::tests::pool_splits_at_real_threshold`（`crate/src/pool.rs`，
  0.32 s）：`Pool` 加字段 `at`（`Pool::new` = `with_at(_, SPLIT_AT)`，`worth` 读它），测试用一个 `at = SPLIT`、宽度 4
  的独立 pool，对 `SPLIT + 1000` 个元素的 FoR 列（宽度 8，生成，不入库）跑 `codec::decode`。检查：(a) 结果逐元素等于闭式
  期望值，并等于单线程（`serial` runner）的结果；(b) 该 pool 的计数器 `PASSES/SPLITS/SLICES/DECLINED` = 1/1/4/0；
  再对其中一个 block 解码，计数器变为 `DECLINED` = 1、`SPLITS` 仍为 1（阈值确实生效）。
- ✖ W.6 elaboration 时 `QLEAN_THREADS=1`：owner 放弃（2026-11-18）。没有测量，没有提交。只有会 split 的 program
  （`muGrow.g`、`digits`、`detab.tc`）受它影响；W.5 的做法 A 跳过 not ok 的 `muGrow.g`，不靠它也省掉那 123 s。
  W.5 的 A 因此不再等 W.6，单独落地。
- ✅ W.7 `-Wl,--build-id`（owner 选 F）：rel lakefile 52b6203（gates、relc、librelk.so、两个 precompiled lib），
  cc-guard 8d08fa4（已部署），lean-refactor 22bc2aa；`crate/build.sh` 只出 `.o`，不需要。lake 不跟踪 extern_lib 的
  link 参数，旧的 librelk.so 要重链接才带 build-id。cap 的 build-id 缓存在 947fbca。
- ✅ W.8 调查结论（Lean v4.28.0，实验在 /data/tmp/w8）：`module` 下 body 不 `@[expose]` 时下游不重建，但下游的
  `rfl`/`decide`/`simp [def]` 也展不开它；kernel body 是 spec，被 KernelSpec、Rep* 和 `#guard` 展开，必须 expose，
  于是改 body 仍重建全部下游（218 个模块里 217 个在 `Rel.Kernel.*` 下游）。要得益须全仓库迁到 `module` 并让下游只引用
  KernelSpec 的引理；只为提速不做。
- ✖ W.9 `SubagentStart` hook：首条命令被拒 0.4%，不值得多一个 hook（owner 选 B）。
- ✅ W.10 原因是差分测试的参照运行重跑了被 inline 的定义；在 `test/TestCompile.lean` 修复（99c595a），
  14m22s → 7m41s。原记录：`compile` 在每个后面的定义里重新展开前面所有的定义，耗时沿链条每步翻倍（Q 0.5 s、C 1.3、W 2.4、K 5、
  Z 11、ζ 21、plan 25 s）。`blocks.*`、`table.*`、`cycle.*` 在 compile-diff 中合计约 200 s，0 次 split，与输入规模
  无关。修法：`compile`/`CodeEnv` 引用已经编译好的定义，不再重新展开。参见 W.5a：poolStat 的合并要和 qlean 同步。
- ✅ W.11 日期显示：一个 atom 的值按 q 的写法 `yyyy.mm.dd`（datetime `yyyy.mm.ddDhh:mm:ss.fffffffff`）显示，出处只有
  `Db.Csv.fmtAtom`/`readAtom`（`print`、`check`、错误信息经 `Elab.wordText` 同源，CSV 与 `crate/src/csv.rs` 同步改为 `.`）；`sep` 参数去掉。
- ✅ W.12 compile-diff 的 pin（`test/compile-diff.json`、`compile-diff-write`、`REL_COMPILE_DIFF_OUT`）删除，只留差分测试
  （生成的代码对 `rel_program` 常量）；compile-diff 只在 master gate 跑（`main-only`）。
- ▶ perf9b 证明层迁到 `module`（23bf589）：`Rel.Kernel.*`（`Dep.Monadic` 除外）与 `KernelSpec.{Csv,Own}` 已是 module；
  头部 `module` / `public import` / `@[expose] public section`（脚本 `/data/tmp/perf9b/mod.awk`）。exposed body 只能引用
  public 声明，所以这些文件里的 `private def` 与 `@[csimp]` 定理及其 `*Impl` 改为 public。测量：改 `Kernel.Value` 的一个
  证明，重建 95 个模块、280 s，module 的 importer（其余 `Kernel.*`）不重建，非 module 的 importer（`KernelSpec.*`、
  `Rep*`）照旧重建。所以收益要等 KernelSpec 层迁完。阻碍：(a) `#print axioms` 在 module 里不允许，21 个文件约 60 处
  （`KernelSpec.{Asc,Assign,Elementwise,Encoding,EwEnc,Gather,Group,…}`、`Rep*`、`Lang.Den`、`Run.Core`），要移到一个
  非 module 的检查文件；(b) 证明 `unfold`/`rfl` 用到 core 未 expose 的定义（`Array.range`、`Nat.fold`：
  `KernelSpec.Encoding` 52、1141、1580 行），要改用 core 的引理；(c) `Kernel.Dep.Monadic` import `KernelSpec.Elementwise`；
  (d) `RepSums`、`Lang.DfnLaw` 依赖 `Run.Lang.Elab`（meta 代码），不在本项范围。
- ▶ perf9c `Rel.KernelSpec.*` 与 `Kernel.Dep.Monadic` 已是 module（(a)(b)(c) 解决）。`#print axioms` 的 pin 移到非 module 的
  `Rel/KernelSpec/AxiomsTest.lean`（`make axioms` 只查 `Rel.Core`，KernelSpec 可用 Classical，所以不能交给它）。
  测量：改 `KernelSpec.Encoding` 一个证明，KernelSpec/Kernel 中只重建 Encoding 本身，但 non-module 的 `Run.*`、`Rep*`、
  `Lang.*` 照旧全部重建：157 个模块、197 s。所以剩下的瓶颈是 (d)：`Run.*` 与 `Rel` 库要迁到 module。
- ▶ perf9e `Rel/Rep*.lean` 中 14 个（`Rep`、`RepBits`、`RepCanon`、`RepCast`、`RepCols`、`RepOrder`、`RepSeen`、`RepSetOps`、
  `RepStruct`、`RepTabArith`、`RepTabComp`、`RepTabDiv`、`RepWF`、`RepWFOps`）以及 `ObjOrder`、`AscOrder`、`Lang.Den` 已是 module；
  没有 `private` 需要改 public。两处改动：(a) module 里的 `#guard` 读不到 import 进来的编译代码的 IR（`Could not find native
  implementation of external declaration 'Rel.tab'`），所以每个文件的 `section Checks` 移到非 module 的 `Rel/RepChecks/<X>.lean`
  （`RepChecks.Canon` 的 `tab`、`specOk`、`sumTab` 等是其余检查与 `Lang.Test.Prelude` 共用的）；(b) `#print axioms` 的 pin 移到
  `Rel/RepAxiomsTest.lean`（`#guard_msgs`）。新目录 `Rel/RepChecks/` 需要 `lake -R`（`make` 的 `CONF` 自动做）。仍非 module：
  `RepAsc`、`RepWhere`、`RepSums`，因为它们 import `Lang.GenKFold`/`GenKBits`/`DfnLaw`（非 module），而 `Lang.GenKSpec` 又
  import `RepBits`/`RepTabArith`/`RepWFOps`，所以要等 `Rel/Lang/*` 迁完。测量：改 `RepCanon` 一个证明（证明内加注释），
  只重建 `RepCanon` 1 个模块（2.5 s），其余 module 的 importer 与非 module 的 importer 都只是 replay（公开接口不变），
  整个命令 3 s；perf9d 是 125 个模块、106 s。
- ▶ perf9f `Rel/Lang/{GenKSpec,GenKBits,GenKFold,GenKEst,GenKFix,GenKHylo,DfnLaw,GenSound,ConvSpec,Table,EmitC,PlanSpec}` 与
  `RepAsc`、`RepWhere`、`RepSums` 已是 module（这些文件里没有 `#guard`/`#print axioms`，无需搬检查；`Run.Lang.Elab` 已是
  module，perf9b 的 (d) 已不成立）。两处改动：(a) `GenKFold` 的 `simp [List.merge]` 改为 `simp`（`List.merge` 在 core 中没有
  expose）；(b) `Run/Lang/TmGen.lean` 里 `addAndCompile` 生成的 `rowGens`、`rowLongs` 在 `@[expose]` 段之外，body 不 expose，
  导致 `GenSound` 的 `rfl`/`cases` 失败（`Dependent elimination failed … ?m.3 σ []`）；改为 `addDecl d (forceExpose := true)`
  再 `compileDecl`。仍非 module：`Rel/Lang/Test*`、`*Test.lean`、`AllPrograms`（import 非 module 的 `Programs.*`）。
  测量：`GenSound` 的一个证明内加注释，只重建 `GenSound` 1 个模块（18 s），整个命令约 27 s；`RepSums` 同样只重建自身
  （2.5 s，命令约 5 s）。perf9e 之前 `Lang.*` 都是 non-module，改任何证明会重建整个下游。

## Baseline

compile-diff 只是差分测试：生成的代码对 `Tm.gen`，gate = 0 个不同。pin（`test/compile-diff.json`）已删（W.12），
所以旧的 241 / 25 phase-gate 目标不再成立。它只在 master gate 中运行，worktree 不运行。
