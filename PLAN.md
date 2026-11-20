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
    `sym`、`general`，`asc` 接受 float。`LamLaw` 与 `Obj.eq_of_not_lt` 的前提保留，原因只剩 `general`（key 为 `[]`）。
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

| #  | 设计项                         | 现有代码（module : 行）               | 差距                                    | Size | 状态       |
|----|--------------------------------|---------------------------------------|-----------------------------------------|------|------------|
| 1  | `Rel` = `tab` 或 `lazy`        | `Rel.Rel`, `Run/Core.lean:485`        | 没有 `lazy`、`Known`；2420 个依赖者     | L    | ✅ 3.8      |
| 2  | `Known = {dom, ran}`           | `Gen.Dem`, `Gen.lean:25`, 只有 dom    | `ran` 一侧没有对应物                    | M    | ✅ 3.3      |
| 3  | CRel 删除，ok → Option         | `CRel`, `Run/CRelDef.lean:8`          | 2297 个 decl；`.rel` 在 ok=false 时被读 | L    | 🔄 3.12     |
| 4  | `Fn`、`Dem` 删除               | `Gen.lean:48`, `:25`; `Pl` `:51`      | 7 个 module 中 224 + 182 个 decl        | L    | 🔄 3.12b    |
| 5  | `Den` 被 inline                | `abbrev Den`, `Lang/Den.lean:20`      | 274 个 decl；`LR` 没有 inline 命令      | M    | ⬜ 3.13     |
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
| 18 | gap：setify、asc               | `rowGaps`, `Rows.lean:107`            | 无 gap；浮点 key 是 `LamLaw` 前提       | M    | 🔄 5.2      |
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
- ✅ D.10（ee84ad8，make check 绿）：两个 `Row` 是不同概念，`Elab` 的改名 `LiftRow`/`liftRows`；TestMss 覆盖。原条目 F-c：`Rel.Lang.Row` 在 `Rel.Lang.Rows` 与 `Rel.Run.Lang.Elab` 各定义一次，同时 import 就报
  `environment already contains 'Rel.Lang.Row.mk.injEq'`，`Tm.gap` 因此不能在运行程序的模块里调用。在 master 上修，立即派。
- ⬜ D.9 语言里的 `input`/`output` 声明：改 `Elab`/`Expand`，在 3.10/3.11（去掉 demand bit 的 `Elab`、`Expand`）之后。
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
  步骤表（每步单独合并；I4 已完成，I0 由本次完成，I2、I5 进行中）：
  - ✅ I0 文档：`rel-architecture`、`dataframe-design`、本条。
  - ✅ I1 表代码移到 `Rel/Run/Table.lean`（`lean-refactor move`），律留在 lib `Rel`；需要 `d9step2` 合并。
  - 🔄 I2 语法与 AST：`sInput`、`sOutput`、`check`/`print` 的 `where`；`Decl.input`/`output`；elaboration 拒绝；run-time 名作参数。
  - ✅ I3 `n.io`、`n.inputs`、`n.outputs`，推论 `Sound.inputs`；需要 I1、I2。
  - ✅ I4 crate：导出分为 `RELK.txt`（kernel）与 `RELIO.txt`（IO），`syms` gate 读两个文件。
  - 🔄 I5 Lean 里的 CSV 模型（`csvWords`、`csvText`、每个 atom 的读写、往返律），尚无 extern。
  - ⬜ I6 `qlean_csv_read`；需要 I4、I5。 ⬜ I7 `qlean_csv_write`；需要 I6。
  - ⬜ I8 可空列 `V+1`、文本列 `[C]`、`sym`（在步骤 6 之后）。
  - ⬜ I9 `n.io` 中的 `from csv`/`to csv`，`relc run NAME`；需要 I3、I7。
  - ⬜ I10 native：`abi` 加 `ownMap`、`csvRead`、`csvWrite`，`Plan.ofTm` 读 input 变量；需要 I9。
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
  I7 ✅（分支 `io-i7`）：`qlean_csv_write`（列入 `RELIO.txt`），`@[extern]` 在 `Db.csvWrite` 上，body 即 `rawAll` + `csvText`；按 1024 行一块读编码列、逐行格式化、临时文件 rename；写侧 case 表 `decide +kernel`，extern 与 body 及读回在全部用例上一致。选择记在 `/data/tmp/io/i7-notes.md`。
- ✅ D.11 表层语法（`schema S = {k : K, v : N}`、`col S "v"`）已合并（da636a9）；`Schema` 层此前已合并（5ab6d2e，master 0fb9879，`Rel/Lang/Schema.lean`、`TestSchema.lean`）；余下：TestFrame 的
  frame 按 `Schema` 索引（随 D.9）。frame 的 schema 进入类型（owner 经 dataframe 会话决定，选 wrapper，不加 `Obj` constructor）：
  `Schema := List (String × Obj)`；`Schema.obj : Schema → Obj` 是 definition（按 `.d` 列序的嵌套 `prod`）；frame 的项按
  schema 索引；`col S "price"` 存在当且仅当 `("price", T) ∈ S`，在 elaboration 时判定，出错时报出列名；
  select/exclude/rename/derive/join 是 `Schema` 上的函数。kernel、存储、`rep`、`lam_sound` 不变。
  已知限制：字段类型相同、名字不同的两个 schema 是同一个 `Obj`，只有按 schema 索引的一层区分它们。
  顺序：`Schema` 层及其函数与 P3 无依赖，现在在 master 上做；D.7 的 `.d` 文件是同一个 `Schema` 的磁盘形式（一个来源）。
- 🔄 D.12 `kseen` 取代 `kdistinct`（owner 2026-11-18 批准；仍是五个 kernel，一个 declaration）：答 `(k, g, first)`，即
  组 id 与首次出现的位置；相等按 `kasc` 的序码（`-0.0 = 0.0`，所有 NaN 是同一个 key）。引擎：直接寻址（范围来自块元数据）
  与有序输入上的 run 检测；宽的无序 key 报可操作的错误（现在没有 hash，只做编码列；非编码 key 是向 owner 的新请求；
  `part` 引擎是解码，不批准）。
  ✅ 已落地：`kseen` kernel（212c171）；它的定律 `kseen_ok firsts_spec firsts_runs firsts_all kseen_pos`（e130504）；
  `kscatter` 接受 `Op`，覆盖是 `.last`，`last` 是位置的 scatter（23059eb）。
  ⬜ 未做：宽的无序 key 上 Lean body 有答案而 Rust 报错，且组 id 规则写了两次（`kseen` 的 body 与 `Order.idsBy`），
  修复 `seenfix` 已合并（0957f87：`kseen` 的 body 返回 Rust 的 hash 错误；`Order.groupIn` 是组 id 的唯一来源）；
  余下：composite 定理；`kasc ≫ kseen` 的 runs 引理；移植 `Order.groupIds*` 的调用者；
  `doc/rel-architecture.zh.typ` 仍写 `distinct`。
  决定 F 已落地（5617318，2026-11-19）：上面的 "引擎" 一句作废。`kseen` 在乱序行上报固定错误（指出第一处乱序的行），
  `seenEngine`/`keySpan`/`foRBounds` 与 Rust 的 `seen::direct` 删除（`Seen.lean` 74 → 32 行）；新引理 `kseen_sorted`。
  未做：1024 行块边界只有 Rust 测试，Lean 例子因 `decide +kernel` 归约不动而缺（与决定 C 有出入）。
  ✅ 运行路径上的平方解码（nodecode 765527b）：`foRBits` 每个元素重算 trailer 偏移 O(nblk)，`Vals.cols` 为判形状解码整列；
  改为 `foROk` 判形状、`foRExc`/`foRFrame` 取 `blockStarts` 的 trailer；10⁵ 行 leftJoin 40.2s→0.96s、带 null 的 group-by
  187s→1.54s；`make decode` 列出仍可达 `foRBits`/`alpBits` 的编译定义（`decode-allow.txt`，150 个，余为单元素读与 u1 位图）。
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
- ⬜ S4 行 `sqrt`；`sum` 按 atom。
- ⬜ S5 float 上的 `Obj.key = ordCode`；`key_ordCode`、`ascBad`、float 上的 `LamLaw`。
- 🟡 S6 行 `$`（分支 `tb-s6`，owner 裁定 J）：`x $ F` 与 `QAtomicType.embed s t` 的图复合（`castDen`），部分映射、不舍入；
  允许的对由 `castOK` 从两个 atom 的格式读出（加宽、整数 → 浮点）；有损方向在 elaboration 报错。`Tab.cast`（分支
  `tb-s6c`）是编码列上一次 `scan` map（`Op.cast s t`，无像写 null 字 `2^63`）+ `colMap .ne` 标志 + `keep` + `canon`，
  不在 `castOK` 中的对报错。定律 `Tab.cast_holds`（无前提，已证）、`rowOK_cast`、`embed_canonical`（全部输入）、
  `ofBits_word`；`Table.nonCanonical` 由 `QAtomicType.nonCanonical` 定义。测试 `Rel/Lang/TestCast.lean`。未完：
  `Rel/Lang/EmbedTest.lean:46` 的 `𝟙 $x` 现在被读成 cast 行，报 `expected a term` 而不是 antiquotation 错误（待裁定）。
- ✅ S7 `Op.cast s t`（`Op` 的最后一个构造子，带两个字段）：`kscan`/`kscatter` 以 `@& Op` 传对象，Rust `cast_word`
  （`CAST = 46`），无新导出；`Reg Op` 按对象传（`nullOps`）。所有数值对一个构造子，不只 `i64 → f64`。
- ⬜ S8 库定义 `mean` `stddev` `correlation` `skewness` `zScore` `valueProportions` float `describe` `daysBetween`
  （dataframe 会话）。
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
  3.12b ⬜ 未开始（`Out.Sound.memo`、`Dem`/`Dem.of`/`Cor`、多余的 `{d}` binder）。
- ⬜ 3.13 inline `Den`。

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
- ✅ 4.4 owner 决定：symmetric division 是定义，不是 `Tm` 构造子。`Pre.symDiv` = `R/S ∩ (S/R)°`（与 `/` 共用
  `Pre.rdivWhole`），`Tm.symDiv_den` 证其含义是 `symDivDen`，`TestSymDiv` 测行。表层语法是中缀 `R ÷ S`
  （owner 2026-11-20 决定；`Bin.table` 的一项，与 `/` 同一优先级），`TestSymDiv` 测它与手写定义行相同。
- ✅ 4.5 默认是 `[nil, snoc]` 上的左 fold；只用 `snoc` 构造。

### P5 按既定顺序关闭 gap — 7/8（5.4a-c 并行，其余串行）

- ✅ 5.1 share：`Tm.den` 在 `Val.empty` 下读 share，`Tm.gen` 在 `Code.empty` 下建它，`gen_sound` 的 share 情形已证；
  没有 gap 留给它（p56）。
- 🔄 5.2 Λ/thin/setify/asc 的 soundness：`Gen.thin_sound`、`Gen.setify_sound`、`Gen.asc_sound` 已证并接入（3006856）；
  `thin` 仍有缺口：元素对象不 canonical 或 pair test 不是 `Tm.cor`；浮点 key 仍有缺口。
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
  操作数，取第一个 NaN 并置 quiet 位）。未做：scatter 写仍两遍（`encode_scatter`）；scatter exactly-once 检查随 6.13。
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
      Lean 例子（`decide +kernel` 不归约，未诊断）。
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
      （基准 64 s → 0.39 s）；`own_write` 创建缺失的父目录。未做：编译器选用 `compBits`、去掉 `sudokupc9` 与 `muGrow` 的固定、
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
      未做（性能，不挡 T10）：`ldiv(tab, bits)` 每轮把 matrix 读回约 2800 万行再排序约 4 次，是 `sudokupc9` 剩下的主要
      开销（按排序来源推出，perf 无 Lean 侧调用栈）；不 decode 的做法约 40 行、无证明、估计到约 7 s。μ 的 semi-naive：不做（2026-11-19，
      owner 交我定）。试过 `Δ = f(X) − X` 再 `X ∪ Δ`：每轮排序两次，`muGrow` 66 s → 79 s，已撤回。要省需要循环体对
      `∪` 分配的判定（`X ≫ X`、带 `\` 的不满足）和已排序表的归并（新 kernel）；17 个程序里只有 `Party` 用 `μ`，
      运行时间可忽略。出现受益的程序时再议。
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
            每个 row 的定义（`length.dfn = ⦇[0, π₁ succ]⦈`，`sum.dfn = ⦇[0, plus]⦈ʳ`）；`Elab.build` 在 target 有 universe 时
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
          单调——后者可判定且全部通过）。待做：`Tm.ConvOK` 的 `callCv` 前提（`instObj` 与 `den`/`convTm` 交换）；`reread` 读最终
          registry 的检查；`Arr.pos_get`/`Arr.pos_clamp`、`expand_cells_le`/`Vals.cells_expand_row` 两处重复证明文本；`Tm.spineHead`
          的死分支。
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
- ✅ 7.2 已落地为 `Rel/Lang/CompileSpec.lean` 末尾的 `compileS` wrapper。subtype = wrapper（owner 2026-11-18）：`CompileSpec` 里的 `compileS (η) (ρ) (hη : η.Sound ρ) (t)
  (hw : t.gap = none) : {r : Rel A B // Gen.Sound r (t.den ρ)} := ⟨compile η t, (compile_sound t hw η ρ hη).1⟩`。
  `Tm.gen` 与 `compile_sound` 仍是两个递归；不一致时 `compile_sound` 编译不过。随去下标的 `CompileSpec` 移植一起落地。
- ⬜ 7.3 `rel_program` 发出 `compile t`，从 `Expand.lean` 删除旧路径。
- ⬜ 7.4 清理：`LR unused`、`unused-simp`、`remove-import`。
- ✅ 7.5 已合并（dbdc72d，`gates3`）：gate `bang`（allowlist 32）、`pointfree`（13）、`kernel-tested`（68 of 84）；`pointfree` 的范围 = L。原条目，规则 gate（owner 选）：三个 gate，allowlist 只减不增：`!` 下标（今天 32 个 def）；关系值 def 的 body 里的
  `∃`（`Rel/Lang/Den.lean` 11 个 + `thinLDen`）；测试 module 里用到的每个 extern（85 个里 69 个没有被用到）。
  分支 `gates3`。另：`CLAUDE.md` 的 14 条规则里 9 条没有 gate。

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
- ⬜ W.5b 缺口：rel 里没有测试走真实 `SPLIT`（8388608）以上的 pool 路径。`cargo test` 下 `SPLIT_AT`=1，没有 Lean
  测试读 pool 计数器；目前只有 TestCompile 本身（`muGrow.g`、`digits`、`detab.tc`）会达到这个阈值。
- ✖ W.6 elaboration 时 `QLEAN_THREADS=1`：owner 放弃（2026-11-18）。没有测量，没有提交。只有会 split 的 program
  （`muGrow.g`、`digits`、`detab.tc`）受它影响；W.5 的做法 A 跳过 not ok 的 `muGrow.g`，不靠它也省掉那 123 s。
  W.5 的 A 因此不再等 W.6，单独落地。
- ✅ W.7 `-Wl,--build-id`（owner 选 F）：rel lakefile 52b6203（gates、relc、librelk.so、两个 precompiled lib），
  cc-guard 8d08fa4（已部署），lean-refactor 22bc2aa；`crate/build.sh` 只出 `.o`，不需要。lake 不跟踪 extern_lib 的
  link 参数，旧的 librelk.so 要重链接才带 build-id。cap 的 build-id 缓存在 947fbca。
- ⬜ W.8 调查：Lean 的 module 系统（`module` + `public import`）能否让只改 kernel body 时不重建下游。
- ✖ W.9 `SubagentStart` hook：首条命令被拒 0.4%，不值得多一个 hook（owner 选 B）。
- ✅ W.10 原因是差分测试的参照运行重跑了被 inline 的定义；在 `test/TestCompile.lean` 修复（99c595a），
  14m22s → 7m41s。原记录：`compile` 在每个后面的定义里重新展开前面所有的定义，耗时沿链条每步翻倍（Q 0.5 s、C 1.3、W 2.4、K 5、
  Z 11、ζ 21、plan 25 s）。`blocks.*`、`table.*`、`cycle.*` 在 compile-diff 中合计约 200 s，0 次 split，与输入规模
  无关。修法：`compile`/`CodeEnv` 引用已经编译好的定义，不再重新展开。参见 W.5a：poolStat 的合并要和 qlean 同步。

## Baseline

在 `e78e922`，`make check` exit 0。compile-diff："compile agrees with the generated code on 241 definitions; not ok
on 25"（`sudokuac.s`、`Test.given.q{R,M,F,h}`、`Test.orders.Of`、`Test.muGrow.g`、`TestWumpus.given.f0`-`f16`、
`TestRefold.refoldCycle.bad`）。每个 phase gate 都必须复现 241 / 25，或解释差异。
