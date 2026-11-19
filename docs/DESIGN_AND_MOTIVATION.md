# Anima (`.anm` / `.anbc`) 设计哲学、核心动机与项目交接白皮书

> **Author**: Nemo (🐻 熊云鹏) & Antigravity  
> **Date**: 2026-11-19  
> **Repository**: [https://github.com/xiongnemo/anima](https://github.com/xiongnemo/anima)  
> **Branch**: `docs/design-and-motivation`

---

## 目录

1. [项目概述与命名缘起](#1-项目概述与命名缘起)
2. [核心动机与软件工程哲学](#2-核心动机与软件工程哲学)
   - [2.1 “Rust 万能论”的幻觉与 Linus 的清醒反思](#21-rust-万能论的幻觉与-linus-的清醒反思)
   - [2.2 安全圈“Fuzzing 一把梭”的死穴与 Oracle 缺失](#22-安全圈fuzzing-一把梭的死穴与-oracle-缺失)
   - [2.3 为什么必须是 Deterministic Engineering？AI 时代的神经-符号闭环](#23-为什么必须是-deterministic-engineeringai-时代的神经-符号闭环)
   - [2.4 终极追问：Who Verifies the Spec？AI 到软件设计才是根本](#24-终极追问who-verifies-the-specai-到软件设计才是根本)
3. [语言定位与关键设计决策](#3-语言定位与关键设计决策)
   - [3.1 UML 现代重生：代码即模型（Code-Model Isomorphism）](#31-uml-现代重生代码即模型code-model-isomorphism)
   - [3.2 过程式内核 + 函数式人体工学：Pythonic 语法与强类型推断](#32-过程式内核--函数式人体工学pythonic-语法与强类型推断)
   - [3.3 拒绝外部 Z3：纯 Go 全自研三核形式化验证内核](#33-拒绝外部-z3纯-go-全自研三核形式化验证内核)
   - [3.4 OCaml 式双后端：32 位字节码 VM 与原生 C11/ELF 执行流](#34-ocaml-式双后端32-位字节码-vm-与原生-c11elf-执行流)
   - [3.5 纯正深色美学：Orchis Material Design 统一工作台](#35-纯正深色美学orchis-material-design-统一工作台)
4. [三大自研形式化验证核心技术拆解](#4-三大自研形式化验证核心技术拆解)
   - [4.1 Core 1: Ada/SPARK 级契约、区间精化与 AnimaSMT](#41-core-1-adaspark-级契约区间精化与-animasmt)
   - [4.2 Core 2: SWEN90004 FSP/LTSA 并发与线性 Typestate](#42-core-2-swen90004-fspltsa-并发与线性-typestate)
   - [4.3 Core 3: SWEN90004 Petri 网与 van der Aalst WF-Net 健全性](#43-core-3-swen90004-petri-网与-van-der-aalst-wf-net-健全性)
5. [8 大形式化验证标准库目录](#5-8-大形式化验证标准库目录)
6. [项目交接与代码库导读](#6-项目交接与代码库导读)
   - [6.1 目录全景图](#61-目录全景图)
   - [6.2 5 个旗舰工程案例](#62-5-个旗舰工程案例)
   - [6.3 14 个反例缺陷拦截回归库](#63-14-个反例缺陷拦截回归库)
   - [6.4 CLI 与日常运维速查](#64-cli-与日常运维速查)
7. [未来演进路线图 (Roadmap)](#7-未来演进路线图-roadmap)

---

## 1. 项目概述与命名缘起

**Anima**（拉丁语中意为“灵魂”、“生命力”或“呼吸”；在心理学中亦代表隐于内在的本质原型）。

过去数十年间，软件工程与形式化方法（Formal Methods）始终处于严重的割裂状态：
- 形式化规约（TLA+、Coq、Isabelle、Alloy）被视为只存在于航空航天或顶会论文里的“天书”，与实际编写业务的工程师相隔千里；
- 统一建模语言（UML）退化为产品经理画完即废弃、与底层代码毫不相关的 Visio / PlantUML 静态图；
- 工业级系统编程语言（C/C++、Go、Rust）专注于指令效率或内存生命周期，却将状态机完整性、并发死锁证明、资源 Typestate 泄漏与业务不变量完全丢给程序员肉眼审查。

**Anima 的愿景**，就是赋予现代系统级与应用级软件以**数学与逻辑的“灵魂”**——让它成为一门**单文件静态二进制分发、零外部求解器依赖、代码即模型、拥有 100% 确定性形式化保证**的通用编程与建模语言。

---

## 2. 核心动机与软件工程哲学

### 2.1 “Rust 万能论”的幻觉与 Linus 的清醒反思

当前安全社区与系统工程界存在一种极具迷惑性的声音：“只要把 C/C++ 全局重构成 Rust，软件安全就彻底解决了。”

正如 Linus Torvalds 在 LKML 以及多次公开讨论中给出的清醒当头棒喝：
- **内存安全（Memory Safety）并不等于系统正确（System Correctness）。**
- 微软 MSRC 与 Google 的“70% 定律”统计的是历史 C/C++ 内存破坏漏洞（UAF、OOB、双重释放、缓冲区溢出）。Rust 的借用检查器（Borrow Checker）确实能够高效消灭这一特定维度的内存破坏。
- 但是，**一旦消除了内存破坏，剩下的 100% 将全部由逻辑漏洞接管**：
  - 锁序颠倒导致的并发死锁与饥饿（Locking Inversion & Livelock）；
  - 异步任务中的资源与句柄泄漏（特别是错误处理分支与早返回）；
  - 业务状态机违规跳转（例如支付未扣款即放行、订单未审批直接执行）；
  - 跨系统与网络协议边界的语义断言假设不一致。
- 越往现代复杂软件（分布式系统、云原生编排、工作流引擎、AI Agent 协同）演进，**逻辑漏洞所占的比例越压倒性地逼近 80%~90%**。换用 Rust 无法改变任何因坏架构、坏协议或坏状态机引发的系统灾难。

### 2.2 安全圈“Fuzzing 一把梭”的死穴与 Oracle 缺失

目前安全工程界的常态是：很多安全工程师或安全研究人员缺少深厚的软件工程建模与设计能力，遇到目标程序习惯于挂载 AFL++、libFuzzer 或 Syzkaller 进行“暴力一把梭”。

这种做法的致命死穴在于 **测试预言（Test Oracle）的严重缺失**：
1. **内存破坏自带免费 Oracle**：访问非法指针引发 `SIGSEGV`，ASAN 抛出红字崩溃，Fuzzer 能够立刻捕获 Crash。
2. **逻辑漏洞不会产生段错误**：当托管理论余额被扣成负数、当分布式工作流陷入死锁活锁、当鉴权检查被绕过时，程序在操作系统层面依然是“正常退出”或“静默挂起”。缺乏语义契约的无脑 Fuzzing 即使千万次穿过该缺陷路径，也根本认不出这是一个致命漏洞。
3. **证明工具的真正价值是“提取确定性证据”**：
   - 无论是用 C 语言有界模型检测展开 SAT 的 **CBMC**，还是 OCaml 构建基于 ACSL 契约演绎证明的 **Frama-C**，其本质都在于**用数学逻辑提供证据（Evidence / Certificate）**。
   - 静态契约（Contracts）与基于属性的测试（Property-Based Testing, PBT）并非与 Fuzzing 对立，而是**给 Fuzzer 装上高精度的眼睛**：把设计层面的不变量转化为断言与监控态，让自动化探索拥有明确的审判准绳。

### 2.3 为什么必须是 Deterministic Engineering？AI 时代的神经-符号闭环

在大语言模型（LLM）与生成式 AI 狂飙突进的当下，软件工程正在经历一场剧烈振荡。业界出现了一种极端危险的倾向——盲信“Vibe Coding”，直接用概率模型生成上百行甚至上千行复杂的底层系统代码，再拿 LLM-as-a-Judge 去做安全审计。

这种模式的本质是**“用幻觉去验证幻觉”**：
- LLM 是概率分布上的词元采样器，它天生缺乏符号因果律和数理逻辑的完备性；
- 真正高可靠的工业级系统，必须扎根于 **Deterministic Engineering（确定性工程）**。

因此，Anima 所践行的是前沿的 **Neuro-Symbolic（神经-符号）闭环**：
```
       [ 概率世界 / AI ]                        [ 确定性世界 / Anima ]
+----------------------------+             +-------------------------------+
| LLM / Agent 自动探索与建模   |             | 100% 确定性形式化验证引擎       |
| • 需求意图转架构草图         |             | • AnimaSMT 证明数据与契约      |
| • 推断精细区间与前置/后置条件  | === 编译 ===> | • LTSA 证明并发与无死锁/活锁   |
| • 标注循环不变量与状态机       |             | • WF-Net 证明工作流 Soundness  |
+----------------------------+             +---------------+---------------+
              ^                                            |
              |            [ 确定性反例反馈 (CEGAR) ]         |
              +----------------- Trace JSON <--------------+
                               (精准定位违规执行轨迹)
```
- **AI 负责发散式生成与形式化提升（Auto-Formalization）**：自动编写 `requires`/`ensures`，标注 `int[lo..hi]`，设计状态机迁移；
- **Anima 形式化内核负责确定性裁决**：要么一次性放行，要么吐出一条比特级精准的反例轨迹（Counterexample Trace），直接让 AI 或工程师回放修复。

### 2.4 终极追问：Who Verifies the Spec？AI 到软件设计才是根本

如果形式化验证链能够做到 100% 自动化，是否意味着系统绝对安全？
**不。形式化验证只能保证 $Implementation \models Specification$（实现严格符合规格）。**

如果规格本身写漏了、写歪了，就会出现灾难性的 **空洞验证（Vacuous Specification）** 或 **代码-契约协同幻觉（Spec-Code Co-hallucination）**——验证内核显示 100% 通过，系统却带病上线。

因此，“**AI 到软件设计才是根本**”：
- 当底层代码搬砖、区间检查和语法纠错被形式化编译器彻底自动化之后，人类工程师的核心战场将全面上移至**高层软件工程设计（Software Architecture & Modeling）**；
- 软件工程师必须深入思考：核心数据的不变量是什么？并发共享资源的访问协议是什么？系统的故障恢复边界在哪里？
- Anima 正是为承载这一高阶软件工程建模而生的统一载体。

---

## 3. 语言定位与关键设计决策

### 3.1 UML 现代重生：代码即模型（Code-Model Isomorphism）

Anima 彻底终结了“文档画一套 UML，代码写另一套逻辑”的工程精神分裂：
- 语言内建一等公民原语：`entity`（实体与组合关联 `rel`）、`statechart`（状态机）、`workflow`（工作流活动网与泳池）；
- 单一 `.anm` 源文件即可同构投影为：
  1. **UML 类图与复合结构图（Class / Composite Structure Diagram）**
  2. **UML 状态机图（State Machine Diagram）**
  3. **UML 活动图 / Petri 网（Activity / Workflow Petri Net）**
  4. **形式化反例时序图（Counterexample Sequence Diagram）**

### 3.2 过程式内核 + 函数式人体工学：Pythonic 语法与强类型推断

- **过程式为主（Procedural Core）**：采用直观清爽的 Python 式缩进，保留显式变量赋值、条件分支与循环控制，符合系统级程序员的心智模型；
- **函数式加持（Functional Ergonomics）**：
  - 代数数据类型（ADT）与编译期穷尽性检查的 `match` 模式匹配；
  - 优雅的管道操作符 `|>`（例如 `quotes |> filter(is_valid) |> fold(0, add)`）；
  - 精简短 Lambda `x => x * 2`；
  - 纯正的错误处理体系：`Result[T, E]`、`Option[T]` 与 `?` 运算符（带 Typestate 线性资源析构保障）。

### 3.3 拒绝外部 Z3：纯 Go 全自研三核形式化验证内核

在技术选型之初，最容易走的捷径是通过 CGo 或子进程直接包装微软的 `z3` 二进制。但这种方案违背了 Anima 的纯粹工程目标：
1. **部署噩梦**：外部 Z3 会引入平台动态链接库（`libz3.so`/`z3.dll`），彻底破坏 Go 语言“单一静态二进制跨平台交叉编译”的最大优势；
2. **黑盒难控**：通用 SMT 求解器在大规模非线性整数算术下容易遭遇不可预测的超时与启发式震荡。

因此，**Anima 100% 用纯 Go 从零自研了轻量高效的数学内核**：
- **DBM (Difference Bound Matrix)**：基于 Floyd-Warshall 的区间与八角抽象域（Octagon），纳秒级处理简单区间上下界推断；
- **CDCL SAT 求解器**：实现 Tseitin CNF 转化、2-Watched-Literals 索引更新与 1-UIP（第一唯一蕴含点）冲突子句学习；
- **精确线性有理单纯形法（Exact Simplex）**：基于 Go 标准库 `math/big.Rat` 的高精度 Dutertre-de Moura 增量 Simplex 算法，彻底消灭浮点精度误差；
- **分支定界法（Branch-and-Bound）**：解决线性整数算术（LIA）可满足性；
- **Presburger 线性化规约**：创新性地将常见除法界校验 $lo \le \lfloor num / den \rfloor \le hi$（$den \ge 1, num \ge 0$）等价降维规约为线性约束：
  $$lo \cdot den \le num \quad \land \quad num < (hi + 1) \cdot den$$
  使得诸如列表折叠求均值等典型业务算式在自研 SMT 中实现 100% 封闭可解。

### 3.4 OCaml 式双后端：32 位字节码 VM 与原生 C11/ELF 执行流

借鉴 OCaml（`ocamlrun` 与 `ocamlopt`）的经典双模架构，Anima 具备两种协同执行途径：
1. **内置 32 位字节码虚拟机 (`AnimaVM`)**：
   - 紧凑的定长指令集，内置协程/纤程并发调度器；
   - 具备环境沙箱，支持 `--seed N` 确定性复现、`--animate` CLI 动画单步推进与 `--replay` 反例追溯。
2. **独立原生 C11 编译器 (`anima build`)**：
   - 将经过三核验证的 AST 转译为清晰合规的 ISO C11 源码；
   - 链接标准 POSIX `pthreads` 与 OpenSSL 3.0，经由系统底层 `gcc -O2` 编译为无虚拟机开销的高性能 Linux ELF 独立可执行文件；
   - 两套后端在全量测试套件（如真实 HTTP 请求、JSON 解码与并发管道）中实现 100% 输出字符级一致性（Dual-Backend Output Parity）。

### 3.5 纯正深色美学：Orchis Material Design 统一工作台

作为开发体验的重要组成部分，`anima studio` 拒绝丑陋简陋的默认前端，原生内嵌现代 **Orchis 深色 Material Design** 界面（基调配色采用夜空深蓝 `#16161e` 与面板表面 `#1e2030`）：
- 单一可执行二进制内嵌（`//go:embed`），无需 Node.js、无需前端构建链路；
- 实时三核验证反馈徽章；
- SVG 级交互式类图、状态机迁移高亮与 Petri 网动态 Token 动画推进。

---

## 4. 三大自研形式化验证核心技术拆解

```
                                    +-----------------------------------+
                                    |        Anima AST (.anm)           |
                                    +-----------------------------------+
                                                      |
           +------------------------------------------+----------------------------------------+
           |                                          |                                        |
           v                                          v                                        v
+-----------------------+                 +-----------------------+                +-----------------------+
|   Core 1: SPARK SMT   |                 |   Core 2: FSP/LTSA    |                |    Core 3: Petri WF   |
| • 契约: req/ens/old   |                 | • 进程代数复合 (||)     |                | • WF-Net 结构转换      |
| • 区间精化 int[lo..hi]|                 | • 死锁与 ERROR=-1 探测  |                | • Karp-Miller 覆盖树   |
| • AoRTE 零运行时越界  |                 | • Tarjan 强连通活锁检测 |                | • van der Aalst 健全性|
| • 独占借用抗别名检查  |                 | • 线性 Typestate 资源  |                | • Short-Circuit 定理  |
+-----------------------+                 +-----------------------+                +-----------------------+
```

### 4.1 Core 1: Ada/SPARK 级契约、区间精化与 AnimaSMT
- **位置**：`internal/verify/smt/` 与 `internal/verify/spark/`
- **主要保障**：
  - **精细类型（Refinement Types）**：`int[0..100]`，保证变量在其整个生命周期中不会越界；
  - **AoRTE（Absence of Run-Time Errors）**：在编译期数学证明数组下标必定合法、除数必定非零；
  - **霍尔三元组契约**：函数的 `requires`、`ensures` 与 `old(x)` 自动生成最弱前置条件（Weakest Preconditions, WP）；
  - **实体不变式（Entity Invariants）**：如 `score * weight <= 1000`，确保结构体构造与变异的每一步状态合法；
  - **内存互斥抗别名（Anti-Aliasing）**：严格限制 `mut` 引用独占，消灭指针悬挂与数据竞争可能；
  - **停机性证明**：循环与递归通过 `decreases` 序数确保终止。

### 4.2 Core 2: SWEN90004 FSP/LTSA 并发与线性 Typestate
- **位置**：`internal/verify/lts/`
- **主要保障**：
  - 继承自墨尔本大学 **SWEN90004**（Advanced Software Design）与 Magee & Kramer 经典的 FSP / LTSA 理论；
  - 将并发 `monitor`、`machine` 与工作流动作自动编译为标记迁移系统（LTS），计算并行动作同步积（Composition `||`）、动作重命名与隐匿；
  - **Safety 检查**：验证系统不可达特定的错误状态（`property` `ERROR=-1`）；
  - **Deadlock 检查**：穷尽状态空间中无外出边的非终态节点；
  - **Progress 属性与公平选择（Fair Choice）**：基于 Tarjan SCC 强连通分量算法检测终端环，彻底拦截线程/协程饥饿与活锁；
  - **线性 Typestate 分析**：把 Socket、文件、互斥锁的生命周期建模为编译期迁移状态机，对跨分支（尤其结合 `?` 早期返回）的所有控制流进行图遍历，拦截任何资源泄露（Resource Leak）与关闭后复用（Use-After-Close）。

### 4.3 Core 3: SWEN90004 Petri 网与 van der Aalst WF-Net 健全性
- **位置**：`internal/verify/petri/`
- **主要保障**：
  - 将具有 `pool`、`fork`/`join`（并发 AND）、`choice`/`merge`（互斥 XOR）的高阶业务工作流编译为标准 Place/Transition Petri 网；
  - **Karp-Miller 覆盖树**：推导可达标识，证明系统的有界性（Boundedness）与严格 `1_safe`（库所中至多存在 1 个 Token）；
  - **van der Aalst Soundness 三准则**：
    1. *Option to complete*：从初始标识出发的任意可达状态，最终均存在一条路径可以到达终止标识；
    2. *Proper completion*：当终止库所产生 Token 时，网内其余所有库所必须清空，绝不允许悬挂残留 Token；
    3. *No dead transitions*：工作流中不存在任何一条永远无法触发的死变迁。
  - **短接闭包定理（Short-Circuit Theorem）交叉验证**：构造自终止库所引向起始库所的虚变迁 $t^*$，数学验证其闭包强连通网 $\overline{N}$ 具备全局有界性与 $L_4$-活性（全局可再生复活）。

---

## 5. 8 大形式化验证标准库目录

Anima 的标准库非松散接口，每一个标准模块都在语义分析层与验证器层深度集成（可通过 `./anima stdlib` 查看）：

```
[1] std.fp
    • 全终止高阶算子: map, filter, fold, sum, zip, take, drop, filter_ok, unwrap_or
    • 形式化保障: 免除手动 decreases 标注的完备停机性 + SMT 列表长度/求和线性界自动传递

[2] std.concurrent
    • 构件: ThreadPool, Channel[T], Mutex, Semaphore, parallel_map
    • 形式化保障: Petri 网资源守恒与停机释放探测 + FSP 互斥无死锁证明

[3] std.socket
    • 接口: listen_tcp, connect_tcp, accept, send_text, recv_text, close
    • 形式化保障: 线性 Typestate 强制追踪，杜绝 FD 句柄泄漏与 use-after-close

[4] std.requests
    • 接口: get, post, Session, get_async, gather
    • 形式化保障: 强制限定 timeout_ms: int[1..300_000] 契约保证活性 + 异步 Future 消费完备性

[5] std.json
    • 接口: decode[EntityType], encode
    • 形式化保障: 系统物理边界的强力运行时断言，动态解码时强制检验字段 int[lo..hi] 及其实体 invariant

[6] std.bytes
    • 构件: ByteView (from_str, from_hex, len, read_u8, read_u16_be, read_u32_be, slice)
    • 形式化保障: SMT 静态证明游标偏移合法性，从数学上杜绝缓冲区读越界（AoRTE）

[7] std.crypto
    • 构件: sha256, hmac_sha256, constant_time_eq
    • 形式化保障: 侧信道常时间安全比较 + 原生编译与 OpenSSL 3.0 EVP 级精确等价

[8] std.fs / std.cli / std.time
    • 构件: File (open, read_text, write_atomic), cli.args, time.now_ms
    • 形式化保障: 文件句柄 Typestate 验证 + 基于原子临时文件替换的文件安全覆写
```

---

## 6. 项目交接与代码库导读

### 6.1 目录全景图

```
/home/nemo/projects/anima/
├── cmd/
│   └── anima/main.go            # 统一 CLI 命令分发器 (check, run, build, disasm, uml, export, studio, stdlib)
├── internal/
│   ├── ast/ast.go               # 语法树定义 (包含实体、契约、LTS 进程、Petri 工作流等全部一等节点)
│   ├── lexer/                   # 词法分析 (Python 缩进对齐, 1_safe/数值字面量识别)
│   ├── parser/                  # 递归下降语法解析器
│   ├── sema/                    # 语义检查、符号表、精细类型归一化与泛型单态化
│   ├── verify/
│   │   ├── smt/                 # [Core 1] 纯 Go 自研 SMT 求解器 (Octagon DBM + CDCL SAT + 精确有理数 Simplex)
│   │   ├── spark/               # [Core 1] 最弱前置条件 (WP) 演算与 Hoare 证明生成器
│   │   ├── lts/                 # [Core 2] SWEN90004 FSP/LTSA 进程代数复合、死锁、活锁与线性 Typestate
│   │   └── petri/               # [Core 3] SWEN90004 Petri WF-Net 覆盖树、健全性证明与短接定理
│   ├── vm/                      # 自研 32-bit 定长指令集虚拟机 (编译器、运行时、调度器、CLI 动画、反例重放)
│   ├── native/                  # C11 转译器 + gcc/pthreads/OpenSSL 3.0 本地编译后端
│   ├── studio/                  # Orchis 深色 Material 统一建模工作台 (嵌入式 web 服务与 SVG 渲染器)
│   └── stdlib/catalog.go        # 8 大可验证标准库规格元数据
├── examples/                    # 5 大旗舰综合案例 (.anm)
├── tests/
│   ├── bugs/                    # 14 个反例缺陷拦截验证库 (.anm)
│   └── e2e_test.go              # 全流程端到端回归测试 (双后端等价性、真实 HTTP 请求、死锁反例重放)
├── docs/
│   └── DESIGN_AND_MOTIVATION.md # [本交接文档]
├── .github/workflows/ci.yml     # 自动化持续集成工作流
├── go.mod                       # 纯 Go 标准库模块 (zero external dependencies)
├── Makefile                     # 自动化编译运维脚本
└── README.md                    # 英文技术概述
```

### 6.2 5 个旗舰工程案例

在 `/home/nemo/projects/anima/examples/` 中提供了 5 个具备完备工程深度的旗舰范例：
1. `escrow_service.anm`：并发托管服务。整合了实体不变式、并发互斥锁、工作流健全性与 `std.fp` 管道求和证明；
2. `single_lane_bridge.anm`：墨大 SWEN90004 经典单车道红蓝车通行模型，形式化证明无碰撞安全性与无饥饿活性；
3. `dining_philosophers_safe.anm`：哲学家就餐问题。展示非对称打破死锁对称性的并发证明；
4. `secure_gateway.anm`：高安全网络网关。结合了 `std.json` 边界校验、`ByteView` 二进制协议解析、HMAC-SHA256 签名以及真实回环 TCP 传输；
5. `agent_sandbox.anm`：针对 AI Agent 规划与工具执行的沙箱模型，证明了复杂动作规划在进入系统前的可达性与安全策略约束。

### 6.3 14 个反例缺陷拦截回归库

在 `/home/nemo/projects/anima/tests/bugs/` 中，系统建立了详尽的负向拦截体系，任何破坏形式化语义的程序都会在编译期被确定性拦截：
- `spark_overflow.anm`：越界运算拦截
- `spark_divzero.anm`：除零风险拦截
- `spark_aliasing.anm`：可变引用别名冲突拦截
- `spark_match_incomplete.anm`：未完全覆盖所有分支的 match 拦截
- `spark_choice_nonexclusive.anm`：条件重叠非互斥拦截
- `lts_safety_violation.anm`：状态机进入错误终态拦截
- `dining_philosophers_deadlock.anm`：经典对称就餐死锁拦截（支持反例 JSON 导出与重放）
- `lts_livelock_progress.anm`：Tarjan 强连通分量活锁/饥饿拦截
- `socket_leak.anm`：TCP 套接字在分支中漏关拦截
- `socket_use_after_close.anm`：关闭后继续读写拦截
- `petri_fork_merge_improper.anm`：并发分支与合并失衡导致残存 Token 拦截
- `petri_choice_join_deadlock.anm`：互斥分支进入并发合并导致永久卡死拦截
- `petri_pool_leak.anm`：工作流资源池未归还拦截
- `requests_missing_timeout.anm`：HTTP 请求缺失 bounded timeout 活性违背拦截

### 6.4 CLI 与日常运维速查

```bash
cd /home/nemo/projects/anima

# 1. 重新构建静态二进制
CGO_ENABLED=0 go build -o anima ./cmd/anima

# 2. 运行完整测试套件 (包含 -race 竞争检测)
go test -count=1 -race ./...

# 3. 运行三核形式化验证 (输出详细数学推导日志)
./anima check --explain examples/escrow_service.anm

# 4. 导出反例轨迹并用虚拟机进行确定性单步重放
./anima check --save-cex /tmp/cex.json tests/bugs/dining_philosophers_deadlock.anm
./anima run --replay /tmp/cex.json tests/bugs/dining_philosophers_deadlock.anm

# 5. 双后端构建与对比执行
./anima run examples/secure_gateway.anm
./anima build -o /tmp/gateway_elf examples/secure_gateway.anm && /tmp/gateway_elf

# 6. 打开 Orchis 深色统一建模工作台
./anima studio examples/escrow_service.anm

# 7. 导出业界标准格式 (LTSA .fsp 与 ISO .pnml)
./anima export --fsp /tmp/model.fsp --pnml /tmp/model.pnml examples/escrow_service.anm
```

---

## 7. 未来演进路线图 (Roadmap)

1. **Auto-Formalization Agent 闭环接入**：
   - 基于 Anima 的反例重放与编译错误提示，设计专用的 LLM Agent 提示链与自愈工具（Auto-Fixing Loop），让 AI 能够针对被拒绝的 `.anm` 文件自动修补不变式与状态机。
2. **分布式协议有界模型检测（Bounded Distributed LTS）**：
   - 扩展 FSP 模块，支持将 Paxos、Raft 或两阶段提交（2PC）的典型拓扑自动展开为有界网络延迟模型并进行状态空间剪枝搜索。
3. **AI Agent 安全沙箱与策略语言运行时**：
   - 将 Anima 直接作为高安全自主 Agent 的策略约束引擎（Policy Guardrail Runtime）：Agent 生成的每一个工具调用规划，必须先在 Anima 内部跑通 Petri 网 Soundness 与 Typestate 检查，证明其不会引发外部资源孤立或非预期权限跃迁，方可实际调度执行。

---

> **Nemo & Antigravity 敬上** 🐻  
> *“Formal verification is not about making coding harder; it is about bringing certainty and souls back to systems engineering.”*
