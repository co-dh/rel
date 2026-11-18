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
| 25 | 一种编码 `foR`              | `Ext.Enc`, 7 个 ctor, `Value.lean`    | 460 个 decl 依赖 `Enc`                  | L    |
| 26 | 九个 atom                      | `QAtomicType`, 18 个 ctor, `Value:13` | 1718 个 decl；boolean、general；R5      | L    |
| 27 | RELK.txt 99 → 5                | `crate/RELK.txt`, `crate/src/ffi/`    | native gate 需要更多；R4                | L    |
| 28 | q-only kernel 离开             | 99 个 extern（`extern.tsv`）          | qlean 固定在 e024297：无工作            | S    |

## 2. Phases

顺序：P0 → P1 → P2 → P3 → P4 → P5 → P7；P6（kernels）在 Lean 层面独立于 P2-P5，只有浮点序例外（5.2 等待 6.9）。
状态：✅ 完成，🔄 进行中，⬜ 未开始，✖ 弃用。每步的旧文本（文件、行号、`LR` 命令、Done 条件）在 commit
178da18 的 `PLAN.md` §2：`git show 178da18:PLAN.md`。行号已过时，先用 index 重新定位。

进度：27 / 54 步（50%）。

| Phase                | 完成 / 步数 | %    |
|----------------------|-------------|------|
| P0 baseline          | 1 / 1       | 100% |
| P1 删除 `Syn`        | 3 / 3       | 100% |
| P2 不依赖 `Rel` 类型 | 6 / 6       | 100% |
| P3 `Rel` 类型        | 7 / 13      | 54%  |
| P4 `Tm` constructor  | 1 / 5       | 20%  |
| P5 关闭 gap          | 0 / 8       | 0%   |
| P6 kernels           | 9 / 14      | 64%  |
| P7 Plan A            | 0 / 4       | 0%   |

### 高优先级：dataframe（`doc/dataframe-design.zh.pdf` §2、§6、§7；stage 1 的 `Plan.ofTm` 由 dataframe 会话自己做）

按此顺序执行，排在其余未开始的步骤之前：
- ✅ D.1 `qlean_k_asc`（6.7，178da18）与 `qlean_k_distinct`（6.8，d1e6ff6）早已在 master。
- ✅ D.2 F17(2) Rust 与 Lean 的宽度平局：foR B（f0f9171）后 `Coc.encode` 就是 Rust 的代价选择，平局取较窄宽度，
  `CocTest` 的 `decide`/`#guard` 逐字节比较。gate 3 的文件字节两边相同。
- 🔄 D.3 6.9 atom（含 `date`、`datetime`、`u8`）：Rust tag 表 WIP，Lean rename 排在 3.8 之后（见 6.9）。
  执行约束：机器 30 GB，`cap` 的 20000 MB 是每个进程的虚拟地址上限（`ulimit -v`），不是占用；限不住多个 build 的总 RSS，所以 Lean build 一次只跑一个（并发时全部被杀过）。合并后把 sha 告诉 dataframe 会话，stage 1 rebase 到它上面。
- ⬜ D.4 6.13a 虚拟行号 `Enc.pos`：6.9 合并后立即开始（两者都改 `Value.lean`，不能并行）。
  验收（dataframe F-d）：排序编码要的位置 `til n` 直接读 `pos`，不再用 `gather(invert(p), p)` 绕。
- ⬜ D.5 F17(1) 布尔 `foR`：把 6.11 中「`bits` 是宽度 1 的 `foR`」这一项提前，`Enc.WF` 接受 `u1` 的 `foR`，`scan` 的布尔结果
  答 `foR`。在 6.10 的 `scan` agent 合并之后（同一个 kernel）。
- ⬜ D.6 `scan` 的方向参数（反向扫描，van Herk）：`kscan` 的扩展，不是新 kernel。与 D.5 同一个 agent，在 `scan` 合并之后。
- ⬜ D.7 stage 2 存储的 runtime 部分：export 把 column 目录 mmap 成 `Tab`（目录 = 表，文件 = 一列的 foR `Enc`，`.d` 列序，
  共享 sym 字典文件；`pos` 一侧不落盘，按 6.13）。只动 `crate/rt` 与 `Rel.Kernel`，6.9 合并后与 D.4 并行。
  同一 agent 补 dataframe F-e：`relc`/`rel-native` 跑不了算出来的程序，缺两条 plan 指令：把算出的 buffer 交给
  `qlean_own_write` 的 `parts : Array ByteArray`；把一个 size 寄存器变成单元素 buffer（`.hi` 列）。D.9 依赖它。
- ⬜ D.8 F2 `Λ` 的 canonical 形式（5.2 setify/asc 行、5.4a `lam_sound`）、`foldI`（4.3）、`hylo`（5.3）：在 `rel-lazy` 上紧接
  3.8 做，排在 3.9-3.13 之前。不在 master 上先做：这些步骤改的 `Gen`/`Compile` 组合子正被 P3 重写，先做就要写两遍。
  dataframe 的输入：F-a `groups(k)` 写不出（`strₗ` 不在 `prims`，带键的 `foldI` 缺），只能按 K 的整个 universe 逐元素
  播种左 fold，代价 |K|×n；F-b `filter(p)` 进入 `Tm` 时是 prelude 的 fold 展开，recipe 只能匹配 fold 的结构。
  D.8 一并决定 `filter`/`groupBy` 是否各有自己的 `Tm` 节点。
- ✅ D.10（ee84ad8，make check 绿）：两个 `Row` 是不同概念，`Elab` 的改名 `LiftRow`/`liftRows`；TestMss 覆盖。原条目 F-c：`Rel.Lang.Row` 在 `Rel.Lang.Rows` 与 `Rel.Run.Lang.Elab` 各定义一次，同时 import 就报
  `environment already contains 'Rel.Lang.Row.mk.injEq'`，`Tm.gap` 因此不能在运行程序的模块里调用。在 master 上修，立即派。
- ⬜ D.9 语言里的 `input`/`output` 声明：改 `Elab`/`Expand`，在 3.10/3.11（去掉 demand bit 的 `Elab`、`Expand`）之后。

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

### P3 `Rel` 类型 — 7/13（在分支 `rel-lazy` 上串行；phase gate 通过之前不动 master）

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
- 🔄 3.8 `Compile`、`Expand`、测试迁到新的 `Fn`。红：`Out.memo_eq`；`rel_program` 展开出 "function expected"。
- ⬜ 3.9 从 `Tm` 去掉下标。
- ⬜ 3.10 没有 demand bit 的 `Elab`。
- ⬜ 3.11 没有 demand bit 的 `Expand`。
- ⬜ 3.12 删除临时物（`CRel.ok/rel/mk`、`Gen.Dem`、…）。
- ⬜ 3.13 inline `Den`。

### P4 `Tm` 的 constructor 变更 — 1/5（串行，共用同样的 match 分支）

- ⬜ 4.1 加 `inl`、`inr`；`junc` 成为 definition；删除 `juncD`。
- ⬜ 4.2 `flat` 成为 definition。
- ⬜ 4.3 `foldI` 成为 definition。
- ⬜ 4.4 加 `symDiv` constructor。
- ✅ 4.5 默认是 `[nil, snoc]` 上的左 fold；只用 `snoc` 构造。

### P5 按既定顺序关闭 gap — 0/8（5.4a-c 并行，其余串行）

- ⬜ 5.1 share。
- ⬜ 5.2 setify、asc 行；浮点 key 等 6.9。
- ⬜ 5.3 hylo：`den_local`，得到 `hylo_sound`。
- ⬜ 5.4a / 5.4b / 5.4c `lam_sound`、`E_sound`、`thin_sound`。
- 🔄 5.5 call（stage 5）：提案 `doc/call-stage5.zh.pdf`（69a8e5d）。owner 定 B D F H J：保留按 form 的常量作共享代码，
  与调用点 `rfl` 相等；`Tm.instObj` 实例化对象；`Code` 带实参的 `Pl`；`cv` 存逆的 body；registry 存 body `Res`。
  实现排在 P3、P4 之后（改 `Tm.call`）。
- ⬜ 5.6 删除 `Tm.gap`；Done：compile-diff 0 个 not ok。

### P6 kernels — 9/14

- ✅ 6.0 替换表：每个旧 extern 由哪些新 kernel 组成（分析）。
- ✅ 6.0a 删除 class Q 的 22 个 extern。
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
- ⬜ 6.11 删除旧 extern 与旧 constructor；保留 SIMD 编解码函数。
- ⬜ 6.12 native gate。
- ⬜ 6.13 虚拟行号（owner 经 dataframe 会话决定）：frame 的行号对象 `I` 只存 `n`，磁盘与内存都不物化；每个 kernel 把它
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

### P7 Plan A — 0/4（串行）

- ⬜ 7.1 library 边界。
- ⬜ 7.2 subtype。
- ⬜ 7.3 `rel_program` 发出 `compile t`，从 `Expand.lean` 删除旧路径。
- ⬜ 7.4 清理：`LR unused`、`unused-simp`、`remove-import`。

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

合计：8 个 phase，54 步（6.10 只计一次；它在 6.0 之后展开）。Opus 39，sonnet 14。

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
- 🔄 W.5 compile-diff 的耗时（owner 选 D）。按 `SPLIT` 以下的输入跑做不到：引起 split 的规模是各 program 自己的
  universe、字面表和 `muCap`，TestCompile 没有通用的开关，缩小还可能让收敛的定义变成 not ok。约 325 s 的分布：
  `Test.muGrow.g` 123 s（μ 每轮增长到 `muCap`=1024，225 920 次 split，本身 not ok）；`blocks.*`、`table.*`、`cycle.*`
  约 200 s，0 次 split（见 W.10）；其余每个定义 < 0.6 s。做法 A：TestCompile 先跑 `compile`，只在 `c.ok` 时
  `evalConst`，结果行不会变；split 由 W.6 消除。在 W.6 报告之后落地，前后各跑一次 `make check`。逐个 program 覆盖输入
  的做法不采纳：每个新 program 都要改一次。
- ⏸ W.5a `qlean_pool_stats` 移入 relk，即 `Rel.Kernel.poolStat`（worktree commit 65760d6，未合并）。只能和 qlean 删除
  qrs 那份 `qlean_pool_stats` 的 commit 一起合并，否则 qlean 链接时有两份同名符号。
- ⬜ W.5b 缺口：rel 里没有测试走真实 `SPLIT`（8388608）以上的 pool 路径。`cargo test` 下 `SPLIT_AT`=1，没有 Lean
  测试读 pool 计数器；目前只有 TestCompile 本身（`muGrow.g`、`digits`、`detab.tc`）会达到这个阈值。
- 🔄 W.6 elaboration 时 `QLEAN_THREADS=1`，只设一处；先测 `make check` 前后的 wall 与 `user+sys`，不变慢才提交（owner 选 E）。
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
