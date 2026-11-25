# 图 Laplacian 的迹与两个矩阵的秩

设 $G$ 是有 $n\ge2$ 个顶点的有限连通无向简单图，$A$ 是实邻接矩阵，$L=D-A$ 是通常的图 Laplacian，$r=\operatorname{rank}(A)$。Duhamel–Cazenave 语料条目 **#124806** 的结论成立：

$$\operatorname{tr}(L)\le r^{\operatorname{rank}(L)}.$$

**原式取等的图恰为 $K_2$、$P_3$ 和 $C_4$。** 项目同时证明了更强的界 $\operatorname{tr}(L)\le r\,2^{n-2}$。原式、加强式和等号分类均已通过 Lean 4 内核核验。

## 原始陈述与查重

Elie Duhamel 与 Tristan Cazenave 在 *Spectral Graph Theory Conjecture Generation*（2026）发布了生成语料。Tristan Cazenave 的 *Lemmas and Conjectures in Spectral Graph Theory*（2026，arXiv:2611.03879v1）第 1 节规定图的类别，第 8 节链接带状态的索引。补充文件 `index_conjectures.csv` 中编号 124806 的逐字陈述如下。[生成论文](https://www.lamsade.dauphine.fr/~cazenave/papers/SpectralGraphTheoryConjectureGeneration.pdf) · [后续原文](https://arxiv.org/html/2611.03879v1#S8) · [补充索引](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

> tr(L) ≤ (rank(A) ^ rank(L))

2026 年 11 月 25 日核查时，作者档案将这一行标为 `ouverte`，Lean 核验栏为 `non`。本次查阅的记录中未找到对此式的完整既有解答。此前纳入候选的 #105367 已被 Lu–Xu 的已发表定理直接覆盖，予以排除。[逐平台查重与候选表](audit/search.md) · [Lu–Xu 原文](https://www.scienceasia.org/2021.47.n6/scias47_779.pdf)

## 数学证明

记 $e=|E(G)|$。由于邻接矩阵的对角线为零，握手引理给出 $\operatorname{tr}(L)=2e$。实图 Laplacian 的核维数等于连通分支数，故本题中 $\operatorname{rank}(L)=n-1$。任取一条边，其两个端点给出邻接矩阵的一个行列式为 $-1$ 的 $2\times2$ 主子矩阵，故 $r\ge2$。同理，若有三角形，其三个顶点给出行列式为 $2$ 的主子矩阵，故 $r\ge3$。因此 $r=2$ 的图没有三角形，Mantel 定理给出 $e\le\lfloor n^2/4\rfloor$。

**先证加强式。** 当 $n\ge6$ 时，简单图满足

$$2e\le n(n-1)<2^{n-1}\le r\,2^{n-2}.$$

中间的严格不等式在 $n=6$ 化为 $30<32$；从 $n$ 增至 $n+1$ 时，左边乘 $(n+1)/(n-1)<2$，右边恰好加倍。当 $2\le n\le5$ 时，用如下整数界即可：

| $n$ | $2e$ 的一般上界 $n(n-1)$ | 若 $r=2$，则 $2e\le 2\lfloor n^2/4\rfloor$ | $2^{n-1}$ | $3\cdot2^{n-2}$ |
|---:|---:|---:|---:|---:|
| 2 | 2 | 2 | 2 | 3 |
| 3 | 6 | 4 | 4 | 6 |
| 4 | 12 | 8 | 8 | 12 |
| 5 | 20 | 12 | 16 | 24 |

对 $r=2$ 比较第三、四列；对 $r\ge3$ 比较第二、五列。这证明了 $2e\le r\,2^{n-2}$。再用 $r\ge2$，得到 $r\,2^{n-2}\le r^{n-1}$，从而得到原式。参数 $n=0,1$ 不在来源的定义域中。

**刻画等号。** 对 $n\ge6$，上面的严格界排除了取等。对 $2\le n\le5$，若 $r\ge3$，则逐一有 $n(n-1)<3^{n-1}$，也不能取等。余下 $r=2$；当 $n=5$ 时 $2e\le12<16$。在 $n=2,3,4$ 的情形，取等恰要求 $e=\lfloor n^2/4\rfloor$。图无三角形，Turán 定理的等号结论迫使它同构于平衡的完全二部图 $T(n,2)$。反过来，这些图的邻接矩阵只有两种行：一类在第一部为零、第二部为一，另一类相反。两部都非空，秩为 2；边数分别为 $1,2,4$，代入原式即取等。

## 声明忠实性

| 论文符号或断言 | Lean 中的实现 |
|---|---|
| 所有 $n\ge2$、连通、有限、无向、无自环、无重边的简单图 | `hn : 2 ≤ n`、`G : SimpleGraph (Fin n)`、`hc : G.Connected`。有限图可判定邻接。任意同阶有限图均可重标号至 `Fin n`。 |
| $A$ 与 $L=D-A$ | Mathlib 的 `G.adjMatrix ℝ`、`G.lapMatrix ℝ`，两者都是实际的 $n\times n$ 实矩阵。 |
| 迹与实秩 | `Matrix.trace` 与 `Matrix.rank`。后者为像空间的实维数，未把 $n-1$ 预设为 Laplacian 的秩。 |
| $\operatorname{rank}(L)=n-1$，$\operatorname{tr}(L)=2e$ | `TraceRanks.lap_rank`，`TraceRanks.lap_trace`。 |
| 原式、加强式及等号 | `TraceRanks.conjecture_124806`，`TraceRanks.stronger`，`TraceRanks.equality_iff`。等号结论用图同构 `G ≃g turanGraph n 2`。 |

## 复现

Lean 与 Mathlib 均锁定为 v4.36.0，Mathlib 提交为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。安装 elan 后，在本目录执行：

```sh
lake exe cache get
lake build
lake env lean TraceRanks.lean
lake env leanchecker TraceRanks
python3 scripts/enumerate.py
```

`lake build` 启用 `warningAsError`。三个主要声明的 `#print axioms` 均列出 `[propext, Classical.choice, Quot.sound]`。小图程序以整数行消元分别计算真实的 $A,L$ 的秩，并从矩阵对角线计算迹。覆盖 2 至 6 阶的全部 27,475 张连通标号图，等号计数按阶分别为 1、3、3、0、0。[Lean 源码](TraceRanks.lean) · [构建日志](audit/build.log) · [公理日志](audit/axioms.log) · [内核重放](audit/kernel.log) · [枚举日志](audit/exhaustive.log)
