# 候选、查重和来源核查

核查日期为 2026 年 11 月 25 日。下列候选均来自 Elie Duhamel、Tristan Cazenave 的 2026 年语料。Tristan Cazenave 在 *Lemmas and Conjectures in Spectral Graph Theory*（2026，arXiv:2611.03879v1）第 8 节公开了逐条状态。[原论文与附件说明](https://arxiv.org/html/2611.03879v1#S8)

| 候选 | 核查与取舍 |
|---|---|
| #105367，$\operatorname{rank}(L)\le\max_v r\,d(v)$ | 单行、易形式化。Lu 和 Xu 的 Theorem 1 已证明无孤点的带符号图 $r\Delta\ge n$；取所有边为正号即覆盖普通图，而 $\operatorname{rank}(L)=n-1$。弃题。[Lu–Xu，2021](https://www.scienceasia.org/2021.47.n6/scias47_779.pdf) |
| 正文 Conjecture 3、语料 #501193，$2R(G)\le r\lambda_1$ | Arizmendi 和 Arizmendi 的已发表结论为 $2R(G)\le\mathcal E(G)$。能量 $\mathcal E(G)$ 是所有非零邻接特征值绝对值之和，至多 $r\lambda_1$，因此原结论已直接得到。弃题。[原有能量界](https://arxiv.org/abs/2009.08041) |
| #124806，$\operatorname{tr}(L)\le r^{\operatorname{rank}(L)}$ | 原语料标记开放。选择此题，因为两个秩和迹都可直接在 Mathlib 中表达，且小阶图上的等号可以给出图同构意义的完整分类。 |

## 原始记录

`Conjectures.zip/open.txt` 第 6,541 行为 `124806 : <= sum eigen laplac Adj ^ rank Adj rank laplac Adj`。后续附件的 `preuves_spectrales/index_conjectures.csv` 将此式写作 `tr(L) ≤ (rank(A) ^ rank(L))`，状态 `ouverte`，`verifiee_lean=non`，无证明文件或反例。索引压缩包 SHA-256 为 `aa113f4a64c0a05260e381987de19c8ad7d66f8c372639f2543f1dd08c6ed500`。[原始语料](https://www.lamsade.dauphine.fr/~cazenave/papers/Conjectures.zip) · [后续附件](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

在 305,755 行中筛选左侧为 $\operatorname{tr}(L)$、右侧同时含邻接秩和 Laplacian 秩的记录，共 7 条。其他 6 行均标有反例。例如 #124988 交换底数和指数，#744411 再对整个右侧开方。全文检查归档的 3,673 个 Lean 文件，定理名 `g124806` 零匹配。[附件索引](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

## 公开查重

| 渠道 | 检索及结果 |
|---|---|
| Google Scholar、arXiv | 在桌面浏览器以 `"Cazenave" "124806"` 检索 Google Scholar，页面报告无匹配文章。arXiv 元数据 API 查 `all:"124806" AND all:"Cazenave"` 返回零项，精确论文标题返回原文。标识符通常只存在于补充材料中，因此另作全文和代码检索。[Scholar 查询](https://scholar.google.com/scholar?q=%22Cazenave%22+%22124806%22) · [arXiv 查询](https://export.arxiv.org/api/query?search_query=all:%22124806%22%20AND%20all:%22Cazenave%22) |
| 数学文献与前向引用 | 组合检索 `Laplacian trace`、`adjacency matrix rank`、`number of edges`、`rank(A)^rank(L)`、`2m`、`r^(n-1)`、`2^(n-2)`、作者、语料 ID 与 `proof`。已发现的正文猜想 5 的解涉及第二大 Laplacian 特征值，Kramer 的后续论文处理 6(ii)。OpenAlex W7225245562 的正式引用计数为零，显然尚未覆盖上述工作。Semantic Scholar 本次 API 核查限流，未将其计为零命中。[正文 5 的已知解](https://www.trureturing.org/research/op-cazenave2611c5/) · [Kramer 原文](https://hexagonmath.org/pdf/2611.00232v1) · [OpenAlex](https://api.openalex.org/works/W7225245562) |
| 研究数据存档 | DataCite 查询 `"124806" AND "Cazenave"`、`"spectral graph" AND "Laplacian trace" AND "adjacency rank"` 均无匹配。也结合 `site:zenodo.org`、`site:figshare.com`、`site:trureturing.org` 检索编号与作者。[DataCite 查询](https://api.datacite.org/dois?query=%22124806%22%20AND%20%22Cazenave%22) |
| GitHub | 认证代码搜索 `"rank(A) ^ rank(L)"` 返回零项。 `"124806" "spectral" "Cazenave"` 唯一匹配为论文参考文献库。单独缩写 `g124806` 会误匹配软件及生物标识。仓库 README 查询 `"124806" "Cazenave" in:readme` 无匹配。以 arXiv 编号反查，另核对相关的两个谱图反例仓库，其本地快照均未找到本编号。GitHub 议题编号的纯数字重合不作数学记录。[代码查询](https://github.com/search?q=%22rank%28A%29+%5E+rank%28L%29%22&type=code) · [已核查的反例集](https://github.com/AmirMakir/broken-conjectures) · [谱隙项目](https://github.com/Sulayman22S/gap-is-one) |
| MathOverflow | Stack Exchange API 的 `site=mathoverflow` 查询 `g124806`、`124806 Cazenave`、完整题名、`"Laplacian trace" "adjacency rank"`，各返回零个问题。[MathOverflow 查询](https://api.stackexchange.com/2.3/search/advanced?site=mathoverflow&q=124806%20Cazenave) |
| Lean Zulip 与 Mathlib | Zulip 所有网络公开频道检索 `g124806`、`124806`、`2611.03879`，均无匹配；私有频道不在检索范围。Mathlib 的 SimpleGraph 源码和文献表检查编号及迹–秩–秩形状，没有检出本定理。Mathlib 已含 Turán 定理、子矩阵秩单调性与 Laplacian 核维数公式，本项目使用这些既有引理。[Zulip 查询](https://leanprover.zulipchat.com/#narrow/channels/web-public/search/g124806) · [Mathlib 秩引理](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Rank.lean) · [Turán 定理](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean) |

该搜索支持“作者状态表中开放，所核查的公开来源中未找到此前直接证明”的表述。结论是现有图论和线性代数的初等推论。没有数据库能排除未经索引、使用其他表述或未公开的证明。

## 独立复核

2026-11-25 重新下载两份作者归档。原始文件第 6,541 行和后续状态索引都保留了同一底数与指数。将二者交换的 #124988 已被作者的图数据库反驳。重新检索索引共得到上文所列的 7 个相关条目，3,673 份 Lean 源文件中均未找到定理名 `g124806`。[原始前缀公式](https://www.lamsade.dauphine.fr/~cazenave/papers/Conjectures.zip) · [状态索引与代码](https://www.lamsade.dauphine.fr/~cazenave/papers/preuves_spectrales.zip)

邻接秩为 2 的连通图一定是完全二部图，这个结构结论已有独立证明，见 Vatandoost 与 Nozari（2018）Theorem 1.6 的证明。这里的 Lean 论证用三角形的秩与 Turán 极值等号定理得到所需分类。`equality_iff` 刻画的是目录原式的等号。三角形可以区分两个界，它满足加强式的等号 $6=3\cdot2$，而在原式中 $6<3^2$。[秩为 2 的结构结论](https://doi.org/10.1080/23311835.2018.1437668) · [形式化](../TraceRanks.lean)

本次从远端克隆重新执行了两个矩阵的整数消元、`lake build`、源文件公理打印和 `leanchecker`。原式在 2 至 6 阶连通标号图上的等号数依次为 1、3、3、0、0，三个受审计声明的公理均限于 `propext`、`Classical.choice`、`Quot.sound`。[枚举程序](../scripts/enumerate.py) · [公理输出](axioms.log)
