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
  - reader 是 mmap（`ownMap`）；`crate/RELK.txt` 的目标：五个 kernel + `stop`、`coc_encode`、`coc_decode`、`own_write`、
    `own_map`（owner 没有说 "5" 是否取字面）。
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
| 12 | flat 成为 definition           | `Tm.lean:72`, `Den.lean:103`          | 同上；`flat_sound` 消失                 | M    | ⬜ 4.2      |
| 13 | inl、inr constructor           | prim 第 3、4 行, `Syntax.lean:150`    | 行已存在，constructor 不存在；R9        | S    | ⬜ 4.1      |
| 14 | junc 是 definition，没有 juncD | `Tm.lean:35`, `:38`; `Gen.lean:247`   | `Core.Rel.junc` 已经是并集              | M    | ⬜ 4.1      |
| 15 | 对称除法 ctor                  | `Alg.symDiv`, `Run/Alg.lean:293`      | 没有 `Tm` ctor，没有 `Den`              | M    | ⬜ 4.4      |
| 16 | 拒绝非正的 μ/ν                 | `Tm.pol`, `Tm.lean:254`               | Elab `.fix`（1655-1670）：没有检查      | S    | ✅ 2.4      |
| 17 | gap：open share                | `Rows.lean:125`, `Expand.lean:530`    | 没有找到 producer；R6                   | M    | ⬜ 5.1      |
| 18 | gap：setify、asc               | `rowGaps`, `Rows.lean:107`            | canonical 上已证；浮点 key 仍是 gap     | M    | 🔄 5.2      |
| 19 | gap：hylo                      | `rep_refold`, `RefoldSpec.lean:124`   | `onNodes` 修复、`hylo_sound`；去 `ch`   | M    | ✅ 5.3      |
| 20 | gap：lam、E、thin              | `lamDen` `Den.lean:111`; `Canon`      | 三条已证；残留缺口：f32/f64 元素        | L    | ✅ 5.4c     |
| 21 | gap：call                      | `Tm.lean:79`; den `𝟘`, `none'`        | stage 5 在代码里没有说明                | L    | 🔄 5.5      |
| 22 | prim row 写成 fold/hylo        | 28 行, `Compile.lean:77-112`          | 没有逐行检查                            | M    | ✅ 2.6      |
| 23 | scan、scatter primitive        | driver, `Kernel/Driver.lean:25-38`    | 有定律，无 caller（见 W2–W3）           | L    | 🔄 W2–W3    |
| 24 | gather、asc、distinct          | `gatherPacked`, `Order.grade`, `nubC` | 无 caller；无 "= 复合" 定理（见 W2）    | L    | 🔄 W2       |
| 25 | 一种编码 `foR`              | `Ext.Enc`, 7 个 ctor, `Value.lean`    | 460 个 decl 依赖 `Enc`                  | L    | 🔄 W1b      |
| 26 | 九个 atom                      | `QAtomicType`, 18 个 ctor, `Value:13` | 1718 个 decl；boolean、general；R5      | L    | 🔄 6.9      |
| 27 | RELK.txt 84 → 5 + 5            | `crate/RELK.txt`, `crate/src/ffi/`    | native gate 需要更多；R4                | L    | 🔄 W5       |
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
| P5 关闭 gap          | 4 / 8       | 50%  | 5.2、5.5                                                    |
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
  整个 `out` 目录。第二部分只有列的 mmap（`d7store` d3926fd：`qlean_own_map` 移进 relk，`Rel.Db.fileMap`），未合并：
  qlean 的 HEAD 按路径用 rel 的主 checkout，合并后 `qlean_own_map` 重复定义；qlean 工作区另有未提交的改动把 rel 钉在
  `qlean-base` = e024297。删副本还是保持钉住，由 owner 在 qlean 会话里定。表目录未做，按规则已定：reader 用 qlean 现有的
  `ownColumn` 移进 Rel（DRY）；`.d` 是自有格式的 sym 列（no serialization）；共享字典用列头已有的 `domain` 字段。
  第二部分（mmap reader）owner 说需要：master 上只有 writer，没有 reader（`crate/src/os.rs` 的 `mmap`/`Map` 无人使用，
  没有 `own_map` export）；分支 `d7map` fbb31f7（未合并）：reader 是 mmap（`ownMap`），定律 `ownParse_ownImage`；
  未决：`own::check` 没有 Lean model。
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

### P4 `Tm` 的 constructor 变更 — 2/5（串行，共用同样的 match 分支）

- ⬜ 4.1 加 `inl`、`inr`；`junc` 成为 definition；删除 `juncD`。
- ⬜ 4.2 `flat` 成为 definition。
- ✅ 4.3 `foldI`：owner 选 D，constructor 保留为融合形式，
  用 `foldIDen_eq` + `foldI_sound` 与定义相连
  （已证，e172821 合并，无额外前提；`Gen.foldI` 的 step 是交 `S ∩ π₁π₁π₁°`）。
- ⬜ 4.4 加 `symDiv` constructor。
- ✅ 4.5 默认是 `[nil, snoc]` 上的左 fold；只用 `snoc` 构造。

### P5 按既定顺序关闭 gap — 4/8（5.4a-c 并行，其余串行）

- ⬜ 5.1 share。
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
- 🔄 5.5 call（stage 5）：提案 `doc/call-stage5.zh.pdf`（69a8e5d）。owner 定 B D F H J：保留按 form 的常量作共享代码，
  与调用点 `rfl` 相等；`Tm.instObj` 实例化对象；`Code` 带实参的 `Pl`；`cv` 存逆的 body；registry 存 body `Res`。
  实现排在 P3、P4 之后（改 `Tm.call`）。
- ⬜ 5.6 删除 `Tm.gap`；Done：compile-diff 0 个 not ok。

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
  `date`（自 epoch 的天数，存为 i32）与 `datetime`（自 epoch 的纳秒，存为 i64，即 q 的 timestamp），都不带时区；存为 foR
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
- ⬜ 6.12 native gate。
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
      - 算子定义在 prelude 里（`Rel/Programs/Prelude.lean`，`.rel` 语法），直接写在五个 kernel 上：`/`、`\`、`Λ`、
        `∋`、pair/product、`[R,S]`、fold/hylo、arith、`est`/`thin`，按同一规则也包括 `≫`、`∩` 等。它们不是 runtime
        的 Lean 函数。
      - 形式 A：一列是关系 `pos ⟶ α`，一张表是 tabulation `R = key(R)° val(R)`。`.rel` 可见的原语：`key`、`val`、
        `scan(op)`、`scatter(op)`、`asc`、`seen`；`gather` 是复合 `i c`。`Tm` 缩成这些原语加绑定。
      - compiler 现在就发原语，按程序切换：一个程序展开后只用原语，它就走新路径；"仍走旧路径的程序数" 是进度
        数字，到 0 时 W5 删除旧层。新旧算子不能在一个程序里混用（旧的写 `.bytes`，新 kernel 拒绝非 foR，转换被
        禁止）。
      - 设计：`doc/rel-prelude-kernels.zh.typ`（在写；原语的类型与 denotation、每个构造子的 prelude 定义、`Tm` 的
        去向、compiler、迁移步骤、给 owner 的未决点）。预计 `mu`/`nu`、fold 的迭代、`arr` cell 不能直接写（未验证）。
    - W3 已在 master（335b933）的 Lean `Tab` 算子与定律，在形式 A 下是 prelude 定义的复合与证明的来源，不再是
      实现；尚无程序运行它们：
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
    - W3 在做：`w3arrcat`（`arr` 侧的 `Vals.concat`；在它之前 `arr` 侧的 `∪ ∩ − ≫` 回答
      `.error "concat: an arr side is not atom columns"`）；`w3div`（`ldiv rdiv lam E nil lt leq`）、`w3struct`
      （`id top zero val pair prod outl outr junc juncD join flat`）、`w3arith`（`arith succ est thin`，部分 fold）
      —— 后三个是在形式 A 决定之前派出的 Lean `Tab` 算子，保留的是复合与定律。
    - W3 未做：prelude 形式的原语与 compiler 发射路径（等设计）；`hylo`、`mu`、`nu`、`atPos`；`prim` 表里程序实际
      用到的行（未数）。切换前给 compile-diff 补：旧表 dump 的对照、"not ok" 名单逐名比较（现在它只数个数，且
      两边跑同一个 `Gen.*`，新算子报错或算错都能通过）。
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
    全绿（2026-11-19）；16c3c79 全量 build 绿；335b933 的 `make check` 在跑。
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
- ⬜ W.10 `compile` 在每个后面的定义里重新展开前面所有的定义，耗时沿链条每步翻倍（Q 0.5 s、C 1.3、W 2.4、K 5、
  Z 11、ζ 21、plan 25 s）。`blocks.*`、`table.*`、`cycle.*` 在 compile-diff 中合计约 200 s，0 次 split，与输入规模
  无关。修法：`compile`/`CodeEnv` 引用已经编译好的定义，不再重新展开。参见 W.5a：poolStat 的合并要和 qlean 同步。

## Baseline

在 `e78e922`，`make check` exit 0。compile-diff："compile agrees with the generated code on 241 definitions; not ok
on 25"（`sudokuac.s`、`Test.given.q{R,M,F,h}`、`Test.orders.Of`、`Test.muGrow.g`、`TestWumpus.given.f0`-`f16`、
`TestRefold.refoldCycle.bad`）。每个 phase gate 都必须复现 241 / 25，或解释差异。
