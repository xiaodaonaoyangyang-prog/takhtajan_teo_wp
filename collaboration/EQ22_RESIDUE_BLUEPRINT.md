# 蓝图：eq_2_2 固定内圆的留数常数
环境：Lean 4.35.0-rc2，mathlib4-latest
导入：Mathlib.Analysis.Complex.CauchyIntegral
命名空间：TakhtajanTeo
全局约定：Ω : Set ℂ；q,Q1,Q2,Q3 : ℂ → ℂ；z : ℂ；r : ℝ。
主定理：L1

## L1 eq22_primitive_circle_integral
自然语言：第三重原函数的四次核圆积分给出精确的 2πI/3 常数。
陈述：
  IsOpen Ω → 0<r → closedBall z r ⊆ Ω → DifferentiableOn ℂ Q3 Ω →
  EqOn (deriv Q1) q Ω → EqOn (deriv Q2) Q1 Ω → EqOn (deriv Q3) Q2 Ω →
  (∮ u in C(z,r), 2*Q3 u/(u-z)^4) = (2*π*I/3)*q z
依赖：无
Mathlib：已检查 Set.EqOn.deriv、DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul、circleIntegral.integral_const_mul。
证明：
  1. 圆心属于闭球，因此属于Ω。〔依据：定义、0<r〕
  2. 对开域上的导数等式再求导，得到 iteratedDeriv 3 Q3 z=q z。〔依据：Set.EqOn.deriv、定义展开〕
  3. 将Q3全纯性限制到闭球，应用n=3的Cauchy导数积分公式。〔依据：Mathlib：上述已查Cauchy公式〕
  4. 提出常数2，整理3!=6，得到所需常数。〔依据：circleIntegral.integral_const_mul、环计算〕
风险点：只证明固定内圆的恒等式，不证明QC反射外边界或无穷远极限。
状态：已证。候选编译及原名公理检查 EXIT0，公理仅 propext/Classical.choice/Quot.sound；公开模块 Eq22Residue 精确导出 EXIT0。日志为 lean1/eq22_residue_candidate.log、lean1/eq22_residue_publish.log。未重复审计旧结果。
