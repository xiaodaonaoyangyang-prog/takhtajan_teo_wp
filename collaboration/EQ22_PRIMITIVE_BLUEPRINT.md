# 蓝图：eq_2_2 反射核的局部原函数
环境：Lean 4.35.0-rc2，当前 mathlib4-latest
导入：TakhtajanTeo.Ch1.GroupChain2，TakhtajanTeo.Ch1.S7_Curvature
命名空间：TakhtajanTeo
全局约定：h,Q1,Q2,Q3 : ℂ → ℂ；u,z,a : ℂ。
自定义定义：
  D1 eq22Primitive h Q1 Q2 Q3 z u :=
    (Q1(h u)*(u-h u)^2 + 2*(Q2(h u)*(u-h u)) + 2*Q3(h u))/(u-z)^4
主定理：L2

## L1 eq22_numerator_dzbar
自然语言：三重原函数的乘积导数中低阶项相消。
陈述：
  DifferentiableAt ℝ h u → HasDerivAt Q1 a (h u) →
  HasDerivAt Q2 (Q1(h u)) (h u) → HasDerivAt Q3 (Q2(h u)) (h u) →
  let N := fun v => Q1(h v)*(v-h v)^2 + 2*(Q2(h v)*(v-h v)) + 2*Q3(h v)
  DifferentiableAt ℝ N u ∧ dzbar N u = a*(u-h u)^2*dzbar h u
依赖：无
Mathlib：HasDerivAt.differentiableAt、HasDerivAt.deriv；已查本项目 grp_dzbar_comp_holo、wp_dzbar_add/sub/const_mul/pow 和 LiZhongQC.dzbar_mul。
证明：
  1. 各全纯原函数与实可微 h 的复合实可微。〔依据：Mathlib：限制标量及链式法则〕
  2. 令 d(v)=v-h(v)，得 ∂bar d=-∂bar h。〔依据：项目 wp_dzbar_sub、Cauchy–Riemann〕
  3. 对三项分别使用乘积、幂和复合求导。〔依据：上述已查项目引理〕
  4. 用 Q1'=a,Q2'=Q1,Q3'=Q2 替换，再消去低阶项。〔依据：HasDerivAt.deriv、环计算〕
风险点：这里只是点态实可微结论，不能作为弱导数或积分换序的证明。
状态：已证（eq22_primitive_candidate.log，标准三公理；不含积分或弱导数结论）

## L2 eq22_primitive_dzbar
自然语言：除以全纯的四次 Cauchy 核得到 eq_2_2 的被积函数。
陈述：
  DifferentiableAt ℝ h u → HasDerivAt Q1 a (h u) →
  HasDerivAt Q2 (Q1(h u)) (h u) → HasDerivAt Q3 (Q2(h u)) (h u) → u≠z →
  DifferentiableAt ℝ (eq22Primitive h Q1 Q2 Q3 z) u ∧
  dzbar (eq22Primitive h Q1 Q2 Q3 z) u = a*(u-h u)^2*dzbar h u/(u-z)^4
依赖：L1
Mathlib：复可微函数的 ∂bar 为零；实可微乘积法则（已查）。
证明：
  1. u≠z 保证 (v-z)^(-4) 在 u 附近全纯。〔依据：Mathlib：幂与逆的可微性〕
  2. 将 D1 写成 L1 的 N 乘以该逆幂。〔依据：定义展开〕
  3. 乘积求导，逆幂的 ∂bar 项为零，代入 L1。〔依据：L1、乘积法则、环计算〕
风险点：必须保留 u≠z；不要求 u-h(u)≠0。
状态：已证（eq22_primitive_candidate.log，标准三公理；不含积分或弱导数结论）

## L3 eq22_primitive_boundary
自然语言：在反射固定点上原函数的边界值只剩第三重原函数。
陈述：h u=u → eq22Primitive h Q1 Q2 Q3 z u = 2*Q3 u/(u-z)^4
依赖：无
Mathlib：代入与环恒等式。
证明：
  1. 代入 h(u)=u，前两项因 u-h(u)=0 消失。〔依据：定义展开、计算〕
风险点：此代数等式不声称有边界迹、积分极限或 q 的边界连续性。
状态：已证（eq22_primitive_candidate.log，标准三公理；不含积分或弱导数结论）
