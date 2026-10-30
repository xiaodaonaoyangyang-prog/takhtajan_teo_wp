# 声明修改记录索引

2026-10-28 用户授权：定理陈述有问题时可自主修正，必须记录，不增加额外公理假设。

历史修正沿用 [ERRATA.md](ERRATA.md) 及 [LEADER.md](LEADER.md) 的最终交接，不覆盖历史。新修正由各会话写入独占文件后汇总；尚未作出新的数学声明修改。

| 会话 | 增量记录 |
|---|---|
| lean1 | [lean1](statement_changes/lean1.md) |
| lean2 | [lean2](statement_changes/lean2.md) |
| lean3 | [lean3](statement_changes/lean3.md) |
| lean4 | [lean4](statement_changes/lean4.md) |
| lean5 | [lean5](statement_changes/lean5.md) |
| lean6 | [lean6](statement_changes/lean6.md) |

每项须含修改前后、数学证据、消费者及验证状态；不得以附加目标假设或删除数学内容代替证明。

## 待完成的真实性审查
- 2026-10-28 lean6：`HC`/`piHat`/`nag_sullivan` 的任意逐点代表复合可能不尊重零测集；详见 [lean6记录](statement_changes/lean6.md)。已给数学反例方案，尚未构造Lean反例或安装修正版。后续应建立H½完备空间上的有界作用并保留光滑数据兼容性；不得删除原数学内容或把有界性作为假设。

## 原声明不变的安装记录
2026-10-28：AppB.thm_B_4 / remark_B_9 从 B_PeriodMapping 搬到 PeriodCompactCharacterization，以真实完整证明替换sorry；doc/header机械比较一致，无新假设/数学改写。原名审计标准3，root增量导出通过。详见 [PERIOD_COMPACT_DELIVERY](lean6/PERIOD_COMPACT_DELIVERY.md) 与 lean1/oct28_period_compact_root.log。

2026-10-28：原prop_3_9从S3_TopologicalGroup搬到TCurveTopGroupCompleted，现行doc/header机械比较完全一致，直接接入已完成tcg_prop_3_9；无新假设/数学修正。原名standard3及root增量通过，见lean1/prop39_original_axioms.log、oct28_prop39_cutoff_vertical_root.log。

2026-10-28：原Ch2.thm_4_1_variation从S4_WPPotential迁至S4VariationCompleted，现行doc/header逐字保留，完整辅助点处理后接入s4pv_variation；无额外假设、无数学修正。原名standard3审计及root增量通过，见lean5/S4_VARIATION_DELIVERY.md与lean1/oct28_graph_variation_root.log。
2026-10-28：原prop_7_2从S7_Curvature移至S7EnergyCompleted，现行doc/header机械比较完全一致，以真实完整s7re_prop_7_2证明替换sorry；无额外假设或语义修正。原名standard3审计与root增量通过，见lean1/prop72_original_axioms.log、oct28_prop72_orthogonality_root.log及statement_changes/lean1.md。
2026-10-28：原lemma_5_1从S5_ChernForms移至S5Lemma51Completed，doc/header逐字不变，真实实解析性与容量公式两个结论均由s5cf_lemma_5_1闭合。原名standard3及root增量通过；见lean1/lemma51_original_axioms.log、oct28_lemma51_root.log及statement_changes/lean1.md。
2026-10-28：原Ch2.thm_3_1与Ch2.cor_3_2从S3_Variations移至S3FirstVariationCompleted，现行doc/header机械比较逐字相同，以实际HS导数、trace面积配对和Schwarzian公式完整证明替换sorry。原名standard3与root增量通过；见lean1/ch2_s3_original_axioms.log、oct28_ch2_first_variation_root.log及statement_changes/lean1.md。
2026-10-28：原cor_7_3从S7_Curvature迁至S7PolarizationCompleted，原doc/header逐字保留；真实原函数/actualQdot线性与绝对可积配对展开后进行复极化，未假设自伴性或目标恒等式。原名standard3及root增量通过，见lean1/cor73_density_axioms.log、oct28_cor73_density_root.log及statement_changes/lean1.md。

## Claude Program G（2026-10-28 起，leader 批准并记录）
用户授权（2026-10-28）：可按需要修改陈述，须记录；忠实于原论文，除非论文本身有误。流程见 PROGRAM_G.md。
| 日期 | 声明 | 修改 | 理由/反例 | 论文 | 状态 |
|---|---|---|---|---|---|
| 2026-10-28 | Ch2 `nag_sullivan` (S5_PeriodMapping:510) | 所有 f/g 量词加 `ContinuousOn f unitCircle →`；条款1加有界性 `∃ C, … Σ'|n|‖c_n(piHat γ f)‖² ≤ C·Σ'|n|‖c_n f‖²`；HC/piHat/Θ/W± 定义不变（全文见 下属6/G1_NS_DEFECT.md 395aa8f9） | 奇异拟对称 γ 把满测度集映成零测集：f=1_{γ(E∩I)} 几乎处处为 0 ∈ HC，但 f∘γ=1_I a.e. 不在 H½（GPT lean6 发现，下属6 完成）。连续函数在 𝓗 中稠密，加上界后 Π̂(γ) 为唯一有界延拓，即论文算子 | 论文正确（TT:5478–5486），是我们的逐点模型错；无 ERRATA 行 | 已应用 2026-10-29（迁移至 S5NagSullivan，原名 standard3） |
| 2026-10-28 | Ch2 `remark_4_4` 条款1（S4_WPPotential:75） | 常数 `-(12 / (π : ℂ))` → `-(6 / (π : ℂ))`，docstring 同改并加 [CORRECTION 2026-10-28, Program G] | ∂_ε S(w_εν) = ẇ''' = −(6/π) PV∫ν/(w−z)⁴（已安装 qcv_ahVar_iter3；与 GPT H21 一致）；论文的 12 抄自 Thm 4.1（∂S₁=2ϑ 的因子 2）。下属5 发现，leader 复算 | 论文错误（TT:5387），ERRATA G-1 | 已应用 2026-10-29（迁移至 S4GRemark44） |
| 2026-10-28 | Ch1 S5_ChernForms 定义：新增 `tcCoordH`/`tcCoordHInv`；`tcCoordExpr`、`leviTC` 改用 tcCoordH；`vkNormSqCoordOrigin` 撤回 D6（Σ(n+2)\|c_{n+2}\|²+‖X.2‖²）；`horVec` 第二分量加 ∂_t fB(tμ)''(0)/2；`tcCoord` docstring 去掉“holomorphic”（全文 下属3/G1_FIX_B_BLOCKS.md dd95e537） | DEFECT G1：项目 Model B 焊接归一化 w(p_μ)=∞ 依赖 μ̄，s_proj = s_mem − fB''(0)/2，c 非全纯 ⇒ tcCoord 非全纯坐标，右平移非 ℂ-可微，fderiv 取垃圾值 0；lemma_5_4 为假（LHS 0 vs RHS −2/(1−\|z\|²)²），thm_5_3/prop_5_7/thm_5_10/cor_5_11 受影响。新坐标 = 论文 TT:568/586 坐标（f''(0)=0, s=1/z 中为平移，处处有定义），一阶检验 ∂̄ 右平移 = 0。D6 的 c₁ 修正是非全纯坐标的人工产物，故撤回 | 论文正确；我们的坐标错（ERRATA F） | 已应用 2026-10-28（S5_ChernForms 534fff6a） |
| 2026-10-29 | Ch1 S5_ChernForms `vkNormSq`（L149）与 `lemma_5_4`（L164–165） | fderiv 基点 `(tcCoord q)` → `(tcCoordH q)`（fix B 的遗漏） | tcCoordExpr 已在 tcCoordH 坐标下，旧基点 tcCoord q 对应另一点 q'（c([q])≠0 时）或垃圾值；下属3 发现 | 无论文关系（我们的错误，属 G1 批次） | 已应用（S5_ChernForms 574b3a9d） |
| 2026-10-29 | Ch1 S8 定义 `IsNormalizedFix`（→ `wD`, `RnmD`, `gGamma`, `riemannRGamma`；影响 lemma_8_4, thm_8_5, eq_8_1） | 归一化 `w (-1) = -1 ∧ w (-I) = -I ∧ w 1 = 1` → `w 0 = 0 ∧ w 1 = 1`（平面同胚另固定 ∞） | 定义缺陷（下属2）：extD κ 反射对称，平面同胚固定 −1,−i,1 ⇒ 由三点归一化球面解唯一性 w 与 refl∘w∘refl 相同 ⇒ w(0)=0，一般 κ 不成立 ⇒ 无解，wD κ = 垃圾 id，gGamma 不是 WP 度量。新归一化即 LiZhongQC 正规解（固定 0,1,∞），对称、保 𝔻；论文中各量在 Aut(𝔻) 后复合下不变，故忠实 | 我们的错误（ERRATA 8-6 记录了该归一化但漏掉 w(0)=0 的约束），ERRATA F 行 | 已应用（S8_FiniteDimensional 881b0bba） |
