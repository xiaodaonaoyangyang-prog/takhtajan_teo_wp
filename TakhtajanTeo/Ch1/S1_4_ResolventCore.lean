import TakhtajanTeo.Ch1.S1_3_Fuchsian
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Chapter 1, §1.4 — Resolvent kernel (TT:1064–1150)

* the Laplace–Beltrami operator `Δ₀ = -ρ⁻¹ ∂_z ∂_{z̄}` (1.18) of the hyperbolic metric
* the point-pair invariant `u(z, w)` and the kernel `G(z, w)` (1.19) of `G = ½(Δ₀ + ½)⁻¹`
* the properties RK1–RK4 on `𝔻` and on `𝔻*`
* the automorphic kernel `G_Γ` (1.20) of a cofinite group

**Modelling.**
- The operator statements are stated through the kernel:
  - "(1.18) defines a unique positive self-adjoint operator on `L²(𝔻, ρ d²z)`" (TT:1070);
  - "`G` is a bounded integral operator with kernel (1.19)" (TT:1080).
- RK3 says that `G` inverts `2(Δ₀ + ½)` on `BC^∞`; this is the content used later.
- Remark 1.10 (TT:1078, the normalization of [Hej76, Lan85]) and Remark 1.11 (TT:1150, a citation) are not
  mathematical statements.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **(1.18)** (TT:1067). The Laplace–Beltrami operator of the hyperbolic metric on functions:
`Δ₀ f = -ρ⁻¹ ∂_z ∂_{z̄} f`. -/
def laplace0 (f : ℂ → ℂ) (z : ℂ) : ℂ := -((rho z : ℂ)⁻¹ * dz (dzbar f) z)

/-- The point-pair invariant `u(z, w) = |z - w|²/((1 - |z|²)(1 - |w|²))` (TT:1089). -/
def pointPair (z w : ℂ) : ℝ := ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2))

/-- **(1.19)** (TT:1083). The kernel of `G = ½(Δ₀ + ½)⁻¹`:
`G(z, w) = ((2u + 1)/(2π)) log((u + 1)/u) - 1/π`, `u = u(z, w)`. The same formula is used on `𝔻*` (TT:1140). -/
def resolventKernel (z w : ℂ) : ℝ :=
  (2 * pointPair z w + 1) / (2 * π) * Real.log ((pointPair z w + 1) / pointPair z w) - 1 / π

/-- Symmetry of the point-pair invariant in (1.19). -/
theorem pointPair_symm (z w : ℂ) : pointPair z w = pointPair w z := by
  simp only [pointPair, norm_sub_rev z w, mul_comm]

/-- The symmetry component of RK1, including the chosen diagonal values. -/
theorem resolventKernel_symm (z w : ℂ) : resolventKernel z w = resolventKernel w z := by
  simp only [resolventKernel, pointPair_symm z w]

/-- Distinct points in either disk model have positive point-pair invariant. -/
theorem pointPair_pos {z w : ℂ} (hzw : z ≠ w)
    (h : z ∈ unitDisc ∧ w ∈ unitDisc ∨ z ∈ unitDiscExterior ∧ w ∈ unitDiscExterior) :
    0 < pointPair z w := by
  apply div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)))
  rcases h with ⟨hz, hw⟩ | ⟨hz, hw⟩
  · have hz : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
    have hw : ‖w‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hw
    have hz0 := norm_nonneg z
    have hw0 := norm_nonneg w
    exact mul_pos (by nlinarith) (by nlinarith)
  · change 1 < ‖z‖ at hz
    change 1 < ‖w‖ at hw
    exact mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)

/-- The scalar logarithmic inequality underlying RK2. -/
theorem resolvent_scalar_pos {u : ℝ} (hu : 0 < u) :
    0 < (2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π := by
  have hlog := Real.lt_log_one_add_of_pos (inv_pos.mpr hu)
  have harg : 1 + u⁻¹ = (u + 1) / u := by
    field_simp
  have hfrac : 2 * u⁻¹ / (u⁻¹ + 2) = 2 / (2 * u + 1) := by
    field_simp
    <;> ring
  rw [harg, hfrac] at hlog
  have hden : 0 < 2 * u + 1 := by positivity
  have hmul := (div_lt_iff₀ hden).mp hlog
  have hpi := Real.pi_pos
  apply (sub_pos.mpr ?_)
  apply (div_lt_iff₀ hpi).mpr
  have heq : ((2 * u + 1) / (2 * π) * Real.log ((u + 1) / u)) * π =
      (Real.log ((u + 1) / u) * (2 * u + 1)) / 2 := by
    field_simp
    <;> ring
  rw [heq]
  linarith

/-- Determinant normalization of an SU(1,1) matrix in norm coordinates. -/
theorem su11_norm_balance (g : SL2C) (hg : IsSU11 g) :
    ‖g 0 0‖ ^ 2 - ‖g 0 1‖ ^ 2 = 1 := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [hg.1, hg.2] at hd
  have hr := congrArg Complex.re hd
  simpa [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re] using hr

/-- The SU(1,1) identity controlling the disk and exterior denominators. -/
theorem su11_denominator_balance (g : SL2C) (hg : IsSU11 g) (z : ℂ) :
    ‖g 1 0 * z + g 1 1‖ ^ 2 - ‖g 0 0 * z + g 0 1‖ ^ 2 = 1 - ‖z‖ ^ 2 := by
  calc
    _ = (‖g 0 0‖ ^ 2 - ‖g 0 1‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
      rw [hg.1, hg.2]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring
    _ = _ := by rw [su11_norm_balance g hg, one_mul]

/-- Difference of two finite values of the determinant-one Mobius action. -/
theorem mob_sub_of_denominator_ne_zero (g : SL2C) (z w : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) (hw : g 1 0 * w + g 1 1 ≠ 0) :
    mob g z - mob g w = (z - w) / ((g 1 0 * z + g 1 1) * (g 1 0 * w + g 1 1)) := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  unfold mob
  rw [div_sub_div _ _ hz hw]
  have hnum : (g 0 0 * z + g 0 1) * (g 1 0 * w + g 1 1) -
      (g 1 0 * z + g 1 1) * (g 0 0 * w + g 0 1) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (z - w) := by ring
  rw [hnum, hd, one_mul]

/-- Hyperbolic density denominator under a finite SU(1,1) action. -/
theorem su11_one_sub_norm_mob (g : SL2C) (hg : IsSU11 g) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    1 - ‖mob g z‖ ^ 2 = (1 - ‖z‖ ^ 2) / ‖g 1 0 * z + g 1 1‖ ^ 2 := by
  have hn : ‖g 1 0 * z + g 1 1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  rw [mob, norm_div, div_pow]
  calc
    _ = (‖g 1 0 * z + g 1 1‖ ^ 2 - ‖g 0 0 * z + g 0 1‖ ^ 2) /
        ‖g 1 0 * z + g 1 1‖ ^ 2 := by rw [sub_div, div_self hn]
    _ = _ := by rw [su11_denominator_balance g hg z]

/-- Point-pair invariance away from the pole of the Mobius coordinate. -/
theorem pointPair_mob_of_denominator_ne_zero (g : SL2C) (hg : IsSU11 g) (z w : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) (hw : g 1 0 * w + g 1 1 ≠ 0) :
    pointPair (mob g z) (mob g w) = pointPair z w := by
  have hnz : ‖g 1 0 * z + g 1 1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hnw : ‖g 1 0 * w + g 1 1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw)
  unfold pointPair
  rw [mob_sub_of_denominator_ne_zero g z w hz hw,
    su11_one_sub_norm_mob g hg z hz, su11_one_sub_norm_mob g hg w hw,
    norm_div, norm_mul, div_pow, mul_pow, div_mul_div_comm,
    div_div_div_cancel_right₀ (mul_ne_zero hnz hnw)]

/-- Cross-multiplication identity, valid even at a Mobius pole. -/
theorem mob_cross_difference (g : SL2C) (z w : ℂ) :
    (g 0 0 * z + g 0 1) * (g 1 0 * w + g 1 1) -
      (g 1 0 * z + g 1 1) * (g 0 0 * w + g 0 1) = z - w := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  calc
    _ = (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (z - w) := by ring
    _ = _ := by rw [hd, one_mul]

/-- At a pole, the numerator of a determinant-one Mobius map does not vanish. -/
theorem mob_numerator_ne_zero_at_pole (g : SL2C) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 = 0) : g 0 0 * z + g 0 1 ≠ 0 := by
  intro hn
  have hc := mob_cross_difference g z (z + 1)
  simp [hz, hn] at hc

/-- The real kernel expression is unchanged by the reflection `u ↦ -1-u`.
This also holds at the totalized logarithm's exceptional values. -/
theorem resolvent_scalar_reflection (u : ℝ) :
    (2 * (-1 - u) + 1) / (2 * π) * Real.log (((-1 - u) + 1) / (-1 - u)) - 1 / π =
      (2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π := by
  have hratio : ((-1 - u) + 1) / (-1 - u) = ((u + 1) / u)⁻¹ := by
    rw [inv_div]
    calc
      _ = (-u) / (-(u + 1)) := by congr 1 <;> ring
      _ = _ := neg_div_neg_eq _ _
  rw [hratio, Real.log_inv]
  ring

/-- Point-pair transformation at a pole, with the finite-coordinate convention `mob = 0`.
For points off the unit circle the transformed parameter is `-1-u`, which leaves the kernel invariant. -/
theorem pointPair_mob_at_pole (g : SL2C) (hg : IsSU11 g) (z w : ℂ)
    (hz : g 1 0 * z + g 1 1 = 0) (hw : g 1 0 * w + g 1 1 ≠ 0)
    (hw1 : 1 - ‖w‖ ^ 2 ≠ 0) :
    pointPair (mob g z) (mob g w) = -1 - pointPair z w := by
  have hn : ‖g 0 0 * z + g 0 1‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (mob_numerator_ne_zero_at_pole g z hz))
  have hd : ‖g 1 0 * w + g 1 1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw)
  have hbalz : 1 - ‖z‖ ^ 2 = -‖g 0 0 * z + g 0 1‖ ^ 2 := by
    have hb := su11_denominator_balance g hg z
    simpa [hz] using hb.symm
  have hbalw := su11_denominator_balance g hg w
  have hcross := mob_cross_difference g z w
  rw [hz, zero_mul, sub_zero] at hcross
  have hnorm : ‖z - w‖ ^ 2 =
      ‖g 0 0 * z + g 0 1‖ ^ 2 * ‖g 1 0 * w + g 1 1‖ ^ 2 := by
    rw [← hcross, norm_mul, mul_pow]
  have hmz : mob g z = 0 := by simp [mob, hz]
  rw [pointPair, hmz, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, one_mul, zero_sub, norm_neg, su11_one_sub_norm_mob g hg w hw]
  rw [mob, norm_div, div_pow, pointPair, hnorm, hbalz]
  rw [div_div_div_cancel_right₀ hd, neg_mul, div_neg, mul_div_mul_left _ _ hn]
  apply (div_eq_iff hw1).mpr
  rw [sub_neg_eq_add, add_mul, div_mul_cancel₀ _ hw1]
  linarith [hbalw]

/-- **RK1** (TT:1094–1098). `G` is symmetric and a point-pair invariant: `G(γz, γw) = G(z, w)` for `γ ∈ PSU(1,1)`;
on `𝔻` and on `𝔻*`. -/
theorem RK1 (z w : ℂ) : resolventKernel z w = resolventKernel w z ∧
    ∀ g : SL2C, IsSU11 g → (z ∈ unitDisc ∧ w ∈ unitDisc ∨ z ∈ unitDiscExterior ∧ w ∈ unitDiscExterior) →
      resolventKernel (mob g z) (mob g w) = resolventKernel z w := by
  refine ⟨resolventKernel_symm z w, ?_⟩
  intro g hg h
  have hoff : ∀ v : ℂ, v ∈ unitDisc ∨ v ∈ unitDiscExterior → 1 - ‖v‖ ^ 2 ≠ 0 := by
    intro v hv
    rcases hv with hv | hv
    · have hv : ‖v‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hv
      have hv0 := norm_nonneg v
      nlinarith
    · change 1 < ‖v‖ at hv
      nlinarith
  have hz1 := hoff z (h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1))
  have hw1 := hoff w (h.elim (fun hh => Or.inl hh.2) (fun hh => Or.inr hh.2))
  by_cases hz : g 1 0 * z + g 1 1 = 0
  · by_cases hw : g 1 0 * w + g 1 1 = 0
    · have hc := mob_cross_difference g z w
      rw [hz, hw, mul_zero, zero_mul, sub_zero] at hc
      have heq : z = w := sub_eq_zero.mp hc.symm
      subst w
      simp [resolventKernel, pointPair]
    · unfold resolventKernel
      rw [pointPair_mob_at_pole g hg z w hz hw hw1]
      exact resolvent_scalar_reflection _
  · by_cases hw : g 1 0 * w + g 1 1 = 0
    · rw [resolventKernel_symm (mob g z) (mob g w), resolventKernel_symm z w]
      unfold resolventKernel
      rw [pointPair_mob_at_pole g hg w z hw hz hz1]
      exact resolvent_scalar_reflection _
    · unfold resolventKernel
      rw [pointPair_mob_of_denominator_ne_zero g hg z w hz hw]

/-- **RK2** (TT:1100). `G(z, w) > 0` for all `z ≠ w` in `𝔻` (and in `𝔻*`). -/
theorem RK2 {z w : ℂ} (hzw : z ≠ w)
    (h : z ∈ unitDisc ∧ w ∈ unitDisc ∨ z ∈ unitDiscExterior ∧ w ∈ unitDiscExterior) :
    0 < resolventKernel z w := by
  exact resolvent_scalar_pos (pointPair_pos hzw h)

/-- The point-pair parameter is measurable even with totalized division on the unit circle. -/
theorem measurable_pointPair : Measurable (fun p : ℂ × ℂ => pointPair p.1 p.2) := by
  unfold pointPair
  fun_prop

/-- The totalized resolvent kernel is jointly measurable; its diagonal values do not obstruct integration. -/
theorem measurable_resolventKernel : Measurable (fun p : ℂ × ℂ => resolventKernel p.1 p.2) := by
  have hp := measurable_pointPair
  unfold resolventKernel
  fun_prop

/-- Joint continuity of the point-pair parameter off the unit circle. -/
theorem pointPair_continuousAt (z w : ℂ)
    (hz : 1 - ‖z‖ ^ 2 ≠ 0) (hw : 1 - ‖w‖ ^ 2 ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => pointPair p.1 p.2) (z, w) := by
  unfold pointPair
  exact (((continuous_fst.sub continuous_snd).norm.pow 2).continuousAt).div
    (((continuous_const.sub (continuous_fst.norm.pow 2)).mul
      (continuous_const.sub (continuous_snd.norm.pow 2))).continuousAt)
    (mul_ne_zero hz hw)

/-- Joint continuity of the resolvent kernel away from its diagonal singularity in either disk model. -/
theorem resolventKernel_continuousAt {z w : ℂ} (hzw : z ≠ w)
    (h : z ∈ unitDisc ∧ w ∈ unitDisc ∨ z ∈ unitDiscExterior ∧ w ∈ unitDiscExterior) :
    ContinuousAt (fun p : ℂ × ℂ => resolventKernel p.1 p.2) (z, w) := by
  have hoff : ∀ v : ℂ, v ∈ unitDisc ∨ v ∈ unitDiscExterior → 1 - ‖v‖ ^ 2 ≠ 0 := by
    intro v hv
    rcases hv with hv | hv
    · have hv : ‖v‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hv
      have hv0 := norm_nonneg v
      nlinarith
    · change 1 < ‖v‖ at hv
      nlinarith
  have hp := pointPair_continuousAt z w
    (hoff z (h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)))
    (hoff w (h.elim (fun hh => Or.inl hh.2) (fun hh => Or.inr hh.2)))
  have hu := pointPair_pos hzw h
  have hr : ContinuousAt (fun p : ℂ × ℂ => (pointPair p.1 p.2 + 1) / pointPair p.1 p.2) (z, w) :=
    (hp.add continuousAt_const).div hp hu.ne'
  have hl := hr.log (ne_of_gt (div_pos (by linarith : 0 < pointPair z w + 1) hu))
  unfold resolventKernel
  exact ((((continuousAt_const.mul hp).add continuousAt_const).div_const (2 * π)).mul hl).sub
    continuousAt_const

/-- `BC^∞(D)` (TT:1112): smooth bounded functions on `D`.
[CORRECTION] The explicit `ENat` top denotes smoothness; the top of Mathlib's
`ℕ∞ω` index would instead impose real analyticity. -/
def BCinf (D : Set ℂ) : Set (ℂ → ℂ) := {f | ContDiffOn ℝ (⊤ : ℕ∞) f D ∧ ∃ C, ∀ z ∈ D, ‖f z‖ ≤ C}

/-- The operator `G(g)(z) = ∬_D G(z, w) g(w) ρ(w) d²w` on `D = 𝔻` or `𝔻*`. -/
def resolventOp (D : Set ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w in D, (resolventKernel z w : ℂ) * g w * rho w

/-! ### Independent mass-normalization proofs for RK4 -/

/-- Derivative of the radial mass primitive for the kernel (1.19). -/
theorem resolvent_radial_primitive_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => 2 * x * (x + 1) * Real.log ((x + 1) / x) - 2 * x)
      (2 * (2 * u + 1) * Real.log ((u + 1) / u) - 4) u := by
  have hu1 : u + 1 ≠ 0 := by positivity
  have hq := ((hasDerivAt_id u).add_const 1).div (hasDerivAt_id u) hu.ne'
  have hl := hq.log (div_ne_zero hu1 hu.ne')
  have hp := ((((hasDerivAt_id u).const_mul 2).mul
    ((hasDerivAt_id u).add_const 1)).mul hl).sub ((hasDerivAt_id u).const_mul 2)
  convert hp using 1
  · funext x
    rfl
  · simp only [id_eq, Pi.mul_apply, Pi.div_apply]
    field_simp [hu.ne', hu1]
    <;> ring

/-- The radial mass primitive vanishes at its lower endpoint. -/
theorem resolvent_radial_primitive_tendsto_zero :
    Tendsto (fun u : ℝ => 2 * u * (u + 1) * Real.log ((u + 1) / u) - 2 * u)
      (𝓝[>] 0) (𝓝 0) := by
  have hl : ContinuousAt (fun u : ℝ => Real.log (u + 1)) 0 :=
    (continuousAt_id.add continuousAt_const).log (by norm_num)
  have hc : ContinuousAt (fun u : ℝ =>
      2 * (u + 1) * (u * Real.log (u + 1) - u * Real.log u) - 2 * u) 0 :=
    ((continuousAt_const.mul (continuousAt_id.add continuousAt_const)).mul
      ((continuousAt_id.mul hl).sub Real.continuous_mul_log.continuousAt)).sub
      (continuousAt_const.mul continuousAt_id)
  have ht : Tendsto (fun u : ℝ =>
      2 * (u + 1) * (u * Real.log (u + 1) - u * Real.log u) - 2 * u)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  rw [Real.log_div (by linarith : u + 1 ≠ 0) (ne_of_gt hu)]
  ring

/-- Two rational bounds for the radial mass primitive, obtained from the first
term of the logarithmic series in the coordinate `x = 1/(2u+1)`. -/
theorem resolvent_radial_primitive_bounds {u : ℝ} (hu : 0 < u) :
    1 - 1 / (2 * u + 1) ≤ 2 * u * (u + 1) * Real.log ((u + 1) / u) - 2 * u ∧
      2 * u * (u + 1) * Real.log ((u + 1) / u) - 2 * u ≤ 1 := by
  let x : ℝ := 1 / (2 * u + 1)
  have hd : 0 < 2 * u + 1 := by positivity
  have hx0 : 0 < x := div_pos (by norm_num) hd
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_iff₀ hd]
    linarith
  have hxD : 1 - x ^ 2 ≠ 0 := by nlinarith
  have hratio : (1 + x) / (1 - x) = (u + 1) / u := by
    dsimp [x]
    field_simp
    <;> ring
  have hl := Real.sum_range_le_log_div hx0.le hx1 1
  have hr := Real.log_div_le_sum_range_add hx0.le hx1 1
  norm_num only [Finset.sum_range_one, mul_zero, zero_add, pow_one, Nat.cast_one,
    div_one, Nat.reduceAdd, Nat.reduceMul] at hl hr
  rw [hratio] at hl hr
  have hc : 0 ≤ 4 * u * (u + 1) := by positivity
  have hlo := mul_le_mul_of_nonneg_left hl hc
  have hup := mul_le_mul_of_nonneg_left hr hc
  have hcx : 4 * u * (u + 1) * x = 2 * u + (1 - 1 / (2 * u + 1)) := by
    dsimp [x]
    field_simp
    <;> ring
  have hcu : 4 * u * (u + 1) * (x + x ^ 3 / (1 - x ^ 2)) = 2 * u + 1 := by
    have hxmul : x * (2 * u + 1) = 1 := by dsimp [x]; exact div_mul_cancel₀ _ hd.ne'
    have hcx2 : 4 * u * (u + 1) * x ^ 2 = 1 - x ^ 2 := by
      nlinarith [congrArg (fun y : ℝ => y ^ 2) hxmul]
    have hcube : 4 * u * (u + 1) * (x ^ 3 / (1 - x ^ 2)) = x := by
      rw [← mul_div_assoc]
      apply (div_eq_iff hxD).mpr
      nlinarith [congrArg (fun y : ℝ => y * x) hcx2]
    rw [mul_add, hcube, hcx]
    dsimp [x]
    ring
  rw [hcx] at hlo
  rw [hcu] at hup
  constructor <;> nlinarith

/-- The upper endpoint of the radial mass primitive is one. -/
theorem resolvent_radial_primitive_tendsto_one :
    Tendsto (fun u : ℝ => 2 * u * (u + 1) * Real.log ((u + 1) / u) - 2 * u)
      atTop (𝓝 1) := by
  have hd : Tendsto (fun u : ℝ => 2 * u + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hi : Tendsto (fun u : ℝ => 1 / (2 * u + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  have hl : Tendsto (fun u : ℝ => 1 - 1 / (2 * u + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (resolvent_radial_primitive_bounds hu).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (resolvent_radial_primitive_bounds hu).2

/-- Positivity of the scalar radial density, a consequence of the logarithmic RK2 estimate. -/
theorem resolvent_radial_density_pos {u : ℝ} (hu : 0 < u) :
    0 < 2 * (2 * u + 1) * Real.log ((u + 1) / u) - 4 := by
  have hp := mul_pos (by positivity : 0 < 4 * π) (resolvent_scalar_pos hu)
  have heq : 4 * π * ((2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π) =
      2 * (2 * u + 1) * Real.log ((u + 1) / u) - 4 := by
    field_simp
    <;> ring
  rwa [heq] at hp

/-- Right continuity of the radial primitive at zero, in the form needed for improper FTC. -/
theorem resolvent_radial_primitive_continuousWithinAt_zero :
    ContinuousWithinAt (fun u : ℝ => 2 * u * (u + 1) * Real.log ((u + 1) / u) - 2 * u)
      (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  simpa only [ContinuousWithinAt, zero_mul, mul_zero, sub_zero] using
    resolvent_radial_primitive_tendsto_zero

/-- Absolute integrability of the scalar radial density; no undefined-integral convention is used. -/
theorem resolvent_radial_density_integrable :
    IntegrableOn (fun u : ℝ => 2 * (2 * u + 1) * Real.log ((u + 1) / u) - 4) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg
    resolvent_radial_primitive_continuousWithinAt_zero
    (fun u hu => resolvent_radial_primitive_hasDerivAt hu)
    (fun u hu => (resolvent_radial_density_pos hu).le)
    resolvent_radial_primitive_tendsto_one

/-- The scalar radial mass is exactly one. This is the one-dimensional normalization needed for RK4. -/
theorem resolvent_radial_density_integral :
    ∫ u in Ioi (0 : ℝ), (2 * (2 * u + 1) * Real.log ((u + 1) / u) - 4) = 1 := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    resolvent_radial_primitive_continuousWithinAt_zero
    (fun u hu => resolvent_radial_primitive_hasDerivAt hu)
    resolvent_radial_density_integrable
    resolvent_radial_primitive_tendsto_one
  simpa only [zero_mul, mul_zero, sub_zero] using hi

/-- Derivative of the hyperbolic radial coordinate. -/
theorem resolvent_radial_coordinate_hasDerivAt {r : ℝ} (hr : 1 - r ^ 2 ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ 2 / (1 - x ^ 2)) (2 * r / (1 - r ^ 2) ^ 2) r := by
  have hs := (hasDerivAt_id r).pow 2
  have hd := hs.div ((hasDerivAt_const r (1 : ℝ)).sub hs) hr
  convert hd using 1
  · funext x
    rfl
  · norm_num only [id_eq, Pi.sub_apply, Pi.pow_apply]
    field_simp [hr]
    <;> ring

/-- Injectivity of the radial coordinate on the open unit interval. -/
theorem resolvent_radial_coordinate_injOn :
    InjOn (fun r : ℝ => r ^ 2 / (1 - r ^ 2)) (Ioo 0 1) := by
  intro r hr s hs heq
  have hrD : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hsD : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hc := (div_eq_div_iff hrD hsD).mp heq
  nlinarith [hr.1, hs.1]

/-- Exact image of the open unit interval under the radial coordinate. -/
theorem resolvent_radial_coordinate_image :
    (fun r : ℝ => r ^ 2 / (1 - r ^ 2)) '' Ioo 0 1 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact div_pos (sq_pos_of_pos hr.1) (by nlinarith [hr.1, hr.2])
  · intro hu
    change 0 < u at hu
    have hup : 0 < u + 1 := by linarith
    have hv : 0 < u / (u + 1) := div_pos hu hup
    have hv1 : u / (u + 1) < 1 := (div_lt_one hup).mpr (by linarith)
    have hs := Real.sq_sqrt hv.le
    refine ⟨Real.sqrt (u / (u + 1)), ⟨Real.sqrt_pos.mpr hv, ?_⟩, ?_⟩
    · nlinarith [Real.sqrt_nonneg (u / (u + 1))]
    · dsimp only
      rw [hs]
      field_simp
      <;> ring

/-- The radial Jacobian is strictly positive on `(0,1)`. -/
theorem resolvent_radial_coordinate_deriv_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < 2 * r / (1 - r ^ 2) ^ 2 := by
  have hd : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  exact div_pos (mul_pos (by norm_num) hr.1) (sq_pos_of_ne_zero hd)

/-- Change of variables for integrability in the hyperbolic radial coordinate. -/
theorem resolvent_radial_coordinate_integrable (f : ℝ → ℝ) :
    IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => (2 * r / (1 - r ^ 2) ^ 2) * f (r ^ 2 / (1 - r ^ 2)))
        (Ioo 0 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun r hr => (resolvent_radial_coordinate_hasDerivAt
      (by nlinarith [hr.1, hr.2])).hasDerivWithinAt)
    resolvent_radial_coordinate_injOn f
  rw [resolvent_radial_coordinate_image] at h
  exact h.trans (integrableOn_congr_fun (fun r hr => by
    rw [abs_of_pos (resolvent_radial_coordinate_deriv_pos hr), smul_eq_mul]) measurableSet_Ioo)

/-- Change of variables for the radial mass integral. -/
theorem resolvent_radial_coordinate_integral (f : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), f u) =
      ∫ r in Ioo (0 : ℝ) 1, (2 * r / (1 - r ^ 2) ^ 2) * f (r ^ 2 / (1 - r ^ 2)) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun r hr => (resolvent_radial_coordinate_hasDerivAt
      (by nlinarith [hr.1, hr.2])).hasDerivWithinAt)
    resolvent_radial_coordinate_injOn f
  rw [resolvent_radial_coordinate_image] at h
  refine h.trans (setIntegral_congr_fun measurableSet_Ioo ?_)
  intro r hr
  dsimp only
  rw [abs_of_pos (resolvent_radial_coordinate_deriv_pos hr), smul_eq_mul]

/-- The kernel and density at the disk center depend only on radius. -/
theorem resolvent_center_weight_radial (z : ℂ) :
    resolventKernel 0 z * rho z = resolventKernel 0 (‖z‖ : ℂ) * rho (‖z‖ : ℂ) := by
  simp [resolventKernel, pointPair, rho, Complex.norm_real, abs_of_nonneg (norm_nonneg z)]

/-- The one-dimensional substitution matches the polar area weight of the original kernel. -/
theorem resolvent_center_radial_jacobian {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    2 * π * r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ)) =
      (2 * r / (1 - r ^ 2) ^ 2) *
        (2 * (2 * (r ^ 2 / (1 - r ^ 2)) + 1) *
          Real.log (((r ^ 2 / (1 - r ^ 2)) + 1) / (r ^ 2 / (1 - r ^ 2))) - 4) := by
  have hrD : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  simp only [resolventKernel, pointPair, rho, zero_sub, norm_neg, norm_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr.1]
  field_simp [hrD]
  <;> ring

/-- Absolute integrability of the original kernel's polar radius integrand. -/
theorem resolvent_center_radius_integrable :
    IntegrableOn (fun r : ℝ => 2 * π * r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ)))
      (Ioo 0 1) := by
  have hi := (resolvent_radial_coordinate_integrable _).mp resolvent_radial_density_integrable
  exact (integrableOn_congr_fun (fun r hr => resolvent_center_radial_jacobian hr)
    measurableSet_Ioo).mpr hi

/-- The original kernel's polar radius integral is one. -/
theorem resolvent_center_radius_integral :
    (∫ r in Ioo (0 : ℝ) 1, 2 * π * r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ))) = 1 := by
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, (2 * r / (1 - r ^ 2) ^ 2) *
        (2 * (2 * (r ^ 2 / (1 - r ^ 2)) + 1) *
          Real.log (((r ^ 2 / (1 - r ^ 2)) + 1) / (r ^ 2 / (1 - r ^ 2))) - 4) :=
      setIntegral_congr_fun measurableSet_Ioo (fun r hr => resolvent_center_radial_jacobian hr)
    _ = _ := (resolvent_radial_coordinate_integral _).symm.trans resolvent_radial_density_integral

/-- The radial area formula on the complex unit disk, with its exact factor `2π`. -/
theorem integral_unitDisc_radial (f : ℝ → ℝ) :
    (∫ z in LiZhongQC.unitDisc, f ‖z‖) = 2 * π * ∫ r in Ioo (0 : ℝ) 1, r * f r := by
  have hi := integral_fun_norm_addHaar (volume : Measure ℂ) ((Iio (1 : ℝ)).indicator f)
  have hleft : (fun z : ℂ => (Iio (1 : ℝ)).indicator f ‖z‖) =
      LiZhongQC.unitDisc.indicator (fun z => f ‖z‖) := by
    funext z
    by_cases hz : ‖z‖ < 1 <;>
      simp [Set.indicator, LiZhongQC.unitDisc, mem_ball, dist_zero_right, hz]
  rw [hleft] at hi
  change (∫ z : ℂ, (ball (0 : ℂ) 1).indicator (fun z => f ‖z‖) z) = _ at hi
  rw [integral_indicator measurableSet_ball] at hi
  have hunit : (volume : Measure ℂ).real (ball 0 1) = π := by simp [Measure.real]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, nsmul_eq_mul, smul_eq_mul] at hi
  rw [hunit] at hi
  have hright : (fun r : ℝ => r * (Iio (1 : ℝ)).indicator f r) =
      (Iio (1 : ℝ)).indicator (fun r => r * f r) := by
    funext r
    by_cases hr : r < 1 <;> simp [Set.indicator, hr]
  rw [hright, setIntegral_indicator measurableSet_Iio] at hi
  have hinter : Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 := by ext r; simp
  rw [hinter] at hi
  simpa only [LiZhongQC.unitDisc, Nat.cast_ofNat, mul_assoc] using hi

/-- Absolute integrability of the resolvent kernel's hyperbolic mass at the disk center. -/
theorem resolvent_center_disk_integrable :
    IntegrableOn (fun z : ℂ => resolventKernel 0 z * rho z) LiZhongQC.unitDisc := by
  have hr : IntegrableOn (fun r : ℝ => r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ)))
      (Ioo 0 1) := by
    have hc := resolvent_center_radius_integrable.const_mul (2 * π)⁻¹
    apply hc.congr
    filter_upwards with r
    field_simp
    <;> ring
  have hd : IntegrableOn
      (fun z : ℂ => resolventKernel 0 (‖z‖ : ℂ) * rho (‖z‖ : ℂ)) LiZhongQC.unitDisc := by
    unfold LiZhongQC.unitDisc
    apply (integrableOn_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun r : ℝ => resolventKernel 0 (r : ℂ) * rho (r : ℂ))).mpr
    simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul] using hr
  exact (integrableOn_congr_fun (fun z _ => resolvent_center_weight_radial z)
    (isOpen_ball.measurableSet)).mpr hd

/-- RK4 at the center of the disk, proved by radial integration rather than the unproved RK3. -/
theorem resolvent_center_disk_integral :
    (∫ z in LiZhongQC.unitDisc, resolventKernel 0 z * rho z) = 1 := by
  calc
    _ = ∫ z in LiZhongQC.unitDisc, resolventKernel 0 (‖z‖ : ℂ) * rho (‖z‖ : ℂ) :=
      setIntegral_congr_fun isOpen_ball.measurableSet (fun z _ => resolvent_center_weight_radial z)
    _ = 2 * π * ∫ r in Ioo (0 : ℝ) 1, r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ)) :=
      integral_unitDisc_radial (fun r : ℝ => resolventKernel 0 (r : ℂ) * rho (r : ℂ))
    _ = ∫ r in Ioo (0 : ℝ) 1, 2 * π * r * (resolventKernel 0 (r : ℂ) * rho (r : ℂ)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r _
      ring
    _ = 1 := resolvent_center_radius_integral

open LiZhongQC

/-- Moving a disk point to zero preserves its point-pair parameter. -/
theorem pointPair_blaschke_center {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    pointPair 0 (blaschke a w) = pointPair a w := by
  have hb := one_sub_normSq_blaschke ha hw
  simp only [Complex.normSq_eq_norm_sq] at hb
  have hn : ‖1 - conj a * w‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (blaschke_den_ne_zero ha hw))
  unfold pointPair
  simp only [zero_sub, norm_neg, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, one_mul]
  rw [hb, blaschke, norm_div, div_pow, div_div_div_cancel_right₀ hn,
    norm_sub_rev w a, mul_comm (1 - ‖w‖ ^ 2) (1 - ‖a‖ ^ 2)]

/-- The resolvent kernel is transported from a disk point to the center. -/
theorem resolventKernel_blaschke_center {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    resolventKernel 0 (blaschke a w) = resolventKernel a w := by
  simp only [resolventKernel, pointPair_blaschke_center ha hw]

/-- Hyperbolic area density is invariant under a disk Blaschke automorphism. -/
theorem rho_blaschke_jacobian {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    rho (blaschke a w) * ‖deriv (blaschke a) w‖ ^ 2 = rho w := by
  have hs := congrArg (fun r : ℝ => r ^ 2) (poincareDensityDisc_pullback_blaschke ha hw)
  norm_num [poincareDensityDisc, mul_pow, div_pow] at hs
  simpa only [rho] using hs

/-- The complete weighted kernel, including the Jacobian, is transported pointwise. -/
theorem resolventKernel_blaschke_weight {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖deriv (blaschke a) w‖ ^ 2 * (resolventKernel 0 (blaschke a w) * rho (blaschke a w)) =
      resolventKernel a w * rho w := by
  calc
    _ = resolventKernel a w * (rho (blaschke a w) * ‖deriv (blaschke a) w‖ ^ 2) := by
      rw [resolventKernel_blaschke_center ha hw]
      ring
    _ = _ := by rw [rho_blaschke_jacobian ha hw]

/-- Absolute integrability of the hyperbolic resolvent mass at every point of the disk. -/
theorem resolvent_disk_integrable {a : ℂ} (ha : a ∈ unitDisc) :
    IntegrableOn (fun w : ℂ => resolventKernel a w * rho w) unitDisc := by
  have ha' := mem_ball_zero_iff.mp ha
  have hf := isConformalOnto_blaschke ha'
  have hi := ahP_integrableOn_image (U := unitDisc)
    (show IsOpen unitDisc from isOpen_ball) hf.1 hf.2.1
    (fun w : ℂ => resolventKernel 0 w * rho w)
  rw [hf.2.2] at hi
  have h := hi.mp resolvent_center_disk_integrable
  apply h.congr
  filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with w hw
  change ‖deriv (blaschke a) w‖ ^ 2 * (resolventKernel 0 (blaschke a w) * rho (blaschke a w)) = _
  exact resolventKernel_blaschke_weight ha' (mem_ball_zero_iff.mp hw)

/-- The disk half of RK4, proved independently of RK3. -/
theorem resolvent_disk_integral {a : ℂ} (ha : a ∈ unitDisc) :
    (∫ w in unitDisc, resolventKernel a w * rho w) = 1 := by
  have ha' := mem_ball_zero_iff.mp ha
  have hf := isConformalOnto_blaschke ha'
  have hi := ahP_integral_image (U := unitDisc)
    (show IsOpen unitDisc from isOpen_ball) hf.1 hf.2.1
    (fun w : ℂ => resolventKernel 0 w * rho w)
  rw [hf.2.2] at hi
  calc
    _ = ∫ w in unitDisc, ‖deriv (blaschke a) w‖ ^ 2 •
        (resolventKernel 0 (blaschke a w) * rho (blaschke a w)) := by
      apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
      intro w hw
      exact (resolventKernel_blaschke_weight ha' (mem_ball_zero_iff.mp hw)).symm
    _ = _ := hi.symm.trans resolvent_center_disk_integral

open LiZhongQC

/-- Exterior points are nonzero. -/
theorem resolvent_exterior_ne_zero {z : ℂ} (hz : z ∈ unitDiscExterior) : z ≠ 0 := by
  intro h
  subst z
  norm_num [unitDiscExterior] at hz

/-- Inversion identifies the exterior with the punctured disk. -/
theorem resolvent_inv_exterior_image :
    (fun z : ℂ => z⁻¹) '' unitDiscExterior = unitDisc \ {0} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 := resolvent_exterior_ne_zero hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    refine ⟨?_, ?_⟩
    · apply mem_ball_zero_iff.mpr
      rw [norm_inv]
      exact (inv_lt_one₀ hn).mpr hz
    · simpa only [mem_singleton_iff, inv_eq_zero] using hz0
  · intro hw
    have hw0 : w ≠ 0 := hw.2
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨w⁻¹, ?_, inv_inv w⟩
    change 1 < ‖w⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ hn).mpr (mem_ball_zero_iff.mp hw.1)

/-- Conformality of inversion on the exterior disk. -/
theorem resolvent_inv_exterior_conformal :
    IsConformalOnto (fun z : ℂ => z⁻¹) unitDiscExterior (unitDisc \ {0}) := by
  have hsub : unitDiscExterior ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    exact resolvent_exterior_ne_zero hz
  exact ⟨nx_inv_isConformalOnto.1.mono hsub,
    nx_inv_isConformalOnto.2.1.mono hsub, resolvent_inv_exterior_image⟩

/-- Point-pair invariance under inversion, including the coincident-point case. -/
theorem pointPair_inv {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    pointPair z⁻¹ w⁻¹ = pointPair z w := by
  have hnz : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hnw : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hw)
  have hdiff : z⁻¹ - w⁻¹ = (w - z) / (z * w) := by field_simp
  have hscale (r : ℝ) (hr : r ≠ 0) : 1 - (r⁻¹) ^ 2 = -(1 - r ^ 2) / r ^ 2 := by
    field_simp
    <;> ring
  unfold pointPair
  rw [hdiff, norm_div, norm_mul, div_pow, mul_pow, norm_sub_rev w z, norm_inv, norm_inv,
    hscale ‖z‖ (norm_ne_zero_iff.mpr hz), hscale ‖w‖ (norm_ne_zero_iff.mpr hw),
    div_mul_div_comm, neg_mul_neg, div_div_div_cancel_right₀ (mul_ne_zero hnz hnw)]

/-- The kernel is invariant under the disk/exterior inversion. -/
theorem resolventKernel_inv {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    resolventKernel z⁻¹ w⁻¹ = resolventKernel z w := by
  simp only [resolventKernel, pointPair_inv hz hw]

/-- The hyperbolic area density absorbs the Jacobian of inversion. -/
theorem rho_inv_jacobian {w : ℂ} (hw : w ≠ 0) :
    rho w⁻¹ * ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2 = rho w := by
  rw [(hasDerivAt_inv hw).deriv]
  simp only [rho, norm_inv, norm_neg, norm_pow]
  field_simp [norm_ne_zero_iff.mpr hw]
  <;> ring

/-- The exterior is an open integration domain. -/
theorem resolvent_exterior_isOpen : IsOpen unitDiscExterior :=
  isOpen_lt continuous_const continuous_norm

/-- Inversion transports the complete hyperbolic kernel weight. -/
theorem resolventKernel_inv_weight {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) :
    ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2 * (resolventKernel a⁻¹ w⁻¹ * rho w⁻¹) =
      resolventKernel a w * rho w := by
  calc
    _ = resolventKernel a w * (rho w⁻¹ * ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2) := by
      rw [resolventKernel_inv ha hw]
      ring
    _ = _ := by rw [rho_inv_jacobian hw]

/-- Absolute integrability of the resolvent mass in the exterior model. -/
theorem resolvent_exterior_integrable {a : ℂ} (ha : a ∈ unitDiscExterior) :
    IntegrableOn (fun w : ℂ => resolventKernel a w * rho w) unitDiscExterior := by
  have ha' : a⁻¹ ∈ unitDisc \ {0} := by
    rw [← resolvent_inv_exterior_image]
    exact ⟨a, ha, rfl⟩
  have hf := resolvent_inv_exterior_conformal
  have hi := ahP_integrableOn_image (U := unitDiscExterior) resolvent_exterior_isOpen hf.1 hf.2.1
    (fun w : ℂ => resolventKernel a⁻¹ w * rho w)
  rw [hf.2.2] at hi
  have h := hi.mp ((resolvent_disk_integrable ha'.1).mono_set sdiff_subset)
  apply h.congr
  filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w hw
  exact resolventKernel_inv_weight (resolvent_exterior_ne_zero ha) (resolvent_exterior_ne_zero hw)

/-- The exterior half of RK4; the puncture in the disk is removed only as a null set. -/
theorem resolvent_exterior_integral {a : ℂ} (ha : a ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, resolventKernel a w * rho w) = 1 := by
  have ha' : a⁻¹ ∈ unitDisc \ {0} := by
    rw [← resolvent_inv_exterior_image]
    exact ⟨a, ha, rfl⟩
  have hf := resolvent_inv_exterior_conformal
  have hi := ahP_integral_image (U := unitDiscExterior) resolvent_exterior_isOpen hf.1 hf.2.1
    (fun w : ℂ => resolventKernel a⁻¹ w * rho w)
  rw [hf.2.2] at hi
  calc
    _ = ∫ w in unitDiscExterior, ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2 •
        (resolventKernel a⁻¹ w⁻¹ * rho w⁻¹) := by
      apply setIntegral_congr_fun resolvent_exterior_isOpen.measurableSet
      intro w hw
      exact (resolventKernel_inv_weight (resolvent_exterior_ne_zero ha)
        (resolvent_exterior_ne_zero hw)).symm
    _ = ∫ w in unitDisc \ {0}, resolventKernel a⁻¹ w * rho w := hi.symm
    _ = ∫ w in unitDisc, resolventKernel a⁻¹ w * rho w :=
      setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))
    _ = 1 := resolvent_disk_integral ha'.1

/-- Absolute integrability accompanying both cases of RK4. -/
theorem resolvent_mass_integrable {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) : IntegrableOn (fun w => resolventKernel z w * rho w) D := by
  rcases hD with rfl | rfl
  · exact resolvent_disk_integrable hz
  · exact resolvent_exterior_integrable hz

/-- Full mass normalization in both disk models, matching the original RK4 statement. -/
theorem resolvent_mass_integral {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) : ∫ w in D, resolventKernel z w * rho w = 1 := by
  rcases hD with rfl | rfl
  · exact resolvent_disk_integral hz
  · exact resolvent_exterior_integral hz

/-- **RK4** (TT:1126–1129). `∬_D G(z, w) ρ(w) d²w = 1` for all `z ∈ D`, on `D = 𝔻` and on `D = 𝔻*`. -/
theorem RK4 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {z : ℂ} (hz : z ∈ D) :
    ∫ w in D, resolventKernel z w * rho w = 1 := by
  exact resolvent_mass_integral hD hz

/-! ### Absolute convergence and the bounded-operator estimate in RK3 -/

/-- Both resolvent integration domains are open. -/
theorem resolvent_domain_isOpen {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) : IsOpen D := by
  rcases hD with rfl | rfl
  · exact isOpen_ball
  · exact resolvent_exterior_isOpen

/-- The hyperbolic kernel weight is nonnegative almost everywhere; its diagonal convention is a null exception. -/
theorem resolvent_mass_nonneg_ae {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) : ∀ᵐ w ∂(volume.restrict D), 0 ≤ resolventKernel z w * rho w := by
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ z := by rw [ae_iff]; simp
  filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet,
    ae_restrict_of_ae hne] with w hw hzw
  have hk : 0 < resolventKernel z w := by
    apply RK2 hzw.symm
    rcases hD with rfl | rfl
    · exact Or.inl ⟨hz, hw⟩
    · exact Or.inr ⟨hz, hw⟩
  exact mul_nonneg hk.le (by unfold rho; positivity)

/-- Absolute convergence for bounded measurable inputs, prior to any elliptic regularity argument. -/
theorem resolvent_integrand_integrable_of_bounded {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior) {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖g w‖ ≤ C) {z : ℂ} (hz : z ∈ D) :
    Integrable (fun w => (resolventKernel z w : ℂ) * g w * rho w) (volume.restrict D) := by
  have hmass : Integrable (fun w => ((resolventKernel z w * rho w : ℝ) : ℂ))
      (volume.restrict D) := (resolvent_mass_integrable hD hz).ofReal
  have hbound : ∀ᵐ w ∂(volume.restrict D), ‖g w‖ ≤ C := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
    exact hb w hw
  apply (hmass.mul_bdd hg hbound).congr
  filter_upwards with w
  push_cast
  ring

/-- The absolute-convergence clause of RK3 is proved independently of its smoothness and PDE clauses. -/
theorem RK3_absolute_convergence {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} (hg : g ∈ BCinf D) {z : ℂ} (hz : z ∈ D) :
    Integrable (fun w => (resolventKernel z w : ℂ) * g w * rho w) (volume.restrict D) := by
  obtain ⟨C, hb⟩ := hg.2
  exact resolvent_integrand_integrable_of_bounded hD
    (hg.1.continuousOn.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet) hb hz

/-- The resolvent does not increase a uniform bound on its input. -/
theorem resolventOp_norm_le {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} {C : ℝ} (hb : ∀ w ∈ D, ‖g w‖ ≤ C) {z : ℂ} (hz : z ∈ D) :
    ‖resolventOp D g z‖ ≤ C := by
  have hi := (resolvent_mass_integrable hD hz).const_mul C
  have hbound : ∀ᵐ w ∂(volume.restrict D),
      ‖(resolventKernel z w : ℂ) * g w * rho w‖ ≤ C * (resolventKernel z w * rho w) := by
    filter_upwards [resolvent_mass_nonneg_ae hD hz,
      ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hwpos hw
    have heq : (resolventKernel z w : ℂ) * g w * rho w =
        ((resolventKernel z w * rho w : ℝ) : ℂ) * g w := by push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwpos]
    calc
      _ ≤ (resolventKernel z w * rho w) * C := mul_le_mul_of_nonneg_left (hb w hw) hwpos
      _ = _ := mul_comm _ _
  have hn := norm_integral_le_of_norm_le hi hbound
  rw [integral_const_mul, RK4 hD hz, mul_one] at hn
  exact hn

/-- Boundedness of the resolvent output for a smooth bounded input. -/
theorem RK3_output_bounded {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} (hg : g ∈ BCinf D) : ∃ C, ∀ z ∈ D, ‖resolventOp D g z‖ ≤ C := by
  obtain ⟨C, hb⟩ := hg.2
  exact ⟨C, fun z hz => resolventOp_norm_le hD hb hz⟩

/-- The minimum of two mass weights is dominated by the fixed weight almost everywhere. -/
theorem resolvent_mass_min_bound {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z a : ℂ} (hz : z ∈ D) (ha : a ∈ D) :
    ∀ᵐ w ∂(volume.restrict D),
      ‖min (resolventKernel z w * rho w) (resolventKernel a w * rho w)‖ ≤ resolventKernel a w * rho w := by
  filter_upwards [resolvent_mass_nonneg_ae hD hz, resolvent_mass_nonneg_ae hD ha] with w hzpos hapos
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min hzpos hapos)]
  exact min_le_right _ _

/-- Integrability of the minimum used in the mass-one convergence argument. -/
theorem resolvent_mass_min_integrable {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z a : ℂ} (hz : z ∈ D) (ha : a ∈ D) :
    IntegrableOn (fun w => min (resolventKernel z w * rho w) (resolventKernel a w * rho w)) D := by
  have hm : AEStronglyMeasurable
      (fun w => min (resolventKernel z w * rho w) (resolventKernel a w * rho w)) (volume.restrict D) :=
    ((resolvent_mass_integrable hD hz).aestronglyMeasurable.aemeasurable.min
      (resolvent_mass_integrable hD ha).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  exact (resolvent_mass_integrable hD ha).mono' hm (resolvent_mass_min_bound hD hz ha)

/-- Dominated convergence for the common part of nearby kernel mass weights. -/
theorem resolvent_mass_min_integral_tendsto {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {a : ℂ} (ha : a ∈ D) :
    Tendsto (fun z : ℂ => ∫ w in D,
      min (resolventKernel z w * rho w) (resolventKernel a w * rho w)) (𝓝[D] a) (𝓝 1) := by
  have hm : ∀ᶠ z in 𝓝[D] a, AEStronglyMeasurable
      (fun w => min (resolventKernel z w * rho w) (resolventKernel a w * rho w)) (volume.restrict D) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (resolvent_mass_min_integrable hD hz ha).aestronglyMeasurable
  have hb : ∀ᶠ z in 𝓝[D] a, ∀ᵐ w ∂(volume.restrict D),
      ‖min (resolventKernel z w * rho w) (resolventKernel a w * rho w)‖ ≤ resolventKernel a w * rho w := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact resolvent_mass_min_bound hD hz ha
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ a := by rw [ae_iff]; simp
  have hl : ∀ᵐ w ∂(volume.restrict D), Tendsto
      (fun z : ℂ => min (resolventKernel z w * rho w) (resolventKernel a w * rho w))
      (𝓝[D] a) (𝓝 (resolventKernel a w * rho w)) := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet,
      ae_restrict_of_ae hne] with w hw hwa
    have hk : ContinuousAt (fun p : ℂ × ℂ => resolventKernel p.1 p.2) (a, w) := by
      apply resolventKernel_continuousAt hwa.symm
      rcases hD with rfl | rfl
      · exact Or.inl ⟨ha, hw⟩
      · exact Or.inr ⟨ha, hw⟩
    have hc : ContinuousAt (fun z : ℂ => resolventKernel z w * rho w) a :=
      (hk.comp₂ (g := fun z : ℂ => z) (h := fun _ : ℂ => w) (x := a)
        continuousAt_id continuousAt_const).mul continuousAt_const
    have hm : Tendsto (fun z : ℂ => min (resolventKernel z w * rho w) (resolventKernel a w * rho w))
        (𝓝 a) (𝓝 (min (resolventKernel a w * rho w) (resolventKernel a w * rho w))) :=
      hc.tendsto.min tendsto_const_nhds
    simpa only [min_self] using hm.mono_left nhdsWithin_le_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun w => resolventKernel a w * rho w) hm hb (resolvent_mass_integrable hD ha) hl
  rw [RK4 hD ha] at ht
  exact ht

/-- The L1 distance between two mass-one weights is controlled by their common part. -/
theorem resolvent_mass_l1_identity {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z a : ℂ} (hz : z ∈ D) (ha : a ∈ D) :
    (∫ w in D, ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖) =
      2 - 2 * ∫ w in D, min (resolventKernel z w * rho w) (resolventKernel a w * rho w) := by
  have hreal (x y : ℝ) : ‖x - y‖ = x + y - 2 * min x y := by
    rw [Real.norm_eq_abs]
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hzI := resolvent_mass_integrable hD hz
  have haI := resolvent_mass_integrable hD ha
  have hmI := resolvent_mass_min_integrable hD hz ha
  have hsumI : Integrable (fun w => resolventKernel z w * rho w + resolventKernel a w * rho w)
      (volume.restrict D) := hzI.add haI
  calc
    _ = ∫ w in D, (resolventKernel z w * rho w + resolventKernel a w * rho w) -
        2 * min (resolventKernel z w * rho w) (resolventKernel a w * rho w) :=
      setIntegral_congr_fun (resolvent_domain_isOpen hD).measurableSet (fun w _ => hreal _ _)
    _ = _ := by
      rw [integral_sub hsumI (hmI.const_mul 2), integral_add hzI haI,
        integral_const_mul, RK4 hD hz, RK4 hD ha]
      ring

/-- L1 continuity of the kernel mass, including its integrable diagonal singularity. -/
theorem resolvent_mass_l1_tendsto {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {a : ℂ} (ha : a ∈ D) :
    Tendsto (fun z : ℂ => ∫ w in D,
      ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖) (𝓝[D] a) (𝓝 0) := by
  have ht : Tendsto (fun z : ℂ => 2 - 2 * ∫ w in D,
      min (resolventKernel z w * rho w) (resolventKernel a w * rho w)) (𝓝[D] a) (𝓝 0) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul (resolvent_mass_min_integral_tendsto hD ha)) using 1
    norm_num
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (resolvent_mass_l1_identity hD hz ha).symm

/-- A bounded input converts the L1 kernel distance into an output difference estimate. -/
theorem resolventOp_diff_norm_le {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖g w‖ ≤ C) {z a : ℂ} (hz : z ∈ D) (ha : a ∈ D) :
    ‖resolventOp D g z - resolventOp D g a‖ ≤
      C * ∫ w in D, ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖ := by
  have hzI := resolvent_integrand_integrable_of_bounded hD hg hb hz
  have haI := resolvent_integrand_integrable_of_bounded hD hg hb ha
  have hsub : resolventOp D g z - resolventOp D g a =
      ∫ w in D, ((resolventKernel z w * rho w - resolventKernel a w * rho w : ℝ) : ℂ) * g w := by
    unfold resolventOp
    rw [← integral_sub hzI haI]
    apply setIntegral_congr_fun (resolvent_domain_isOpen hD).measurableSet
    intro w _
    push_cast
    ring
  rw [hsub]
  have hi : Integrable (fun w => C * ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖)
      (volume.restrict D) :=
    ((resolvent_mass_integrable hD hz).sub (resolvent_mass_integrable hD ha)).norm.const_mul C
  have hbound : ∀ᵐ w ∂(volume.restrict D),
      ‖((resolventKernel z w * rho w - resolventKernel a w * rho w : ℝ) : ℂ) * g w‖ ≤
        C * ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖ := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
    rw [norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (hb w hw) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hn := norm_integral_le_of_norm_le hi hbound
  rwa [integral_const_mul] at hn

/-- The resolvent sends bounded measurable inputs to continuous functions on either disk model. -/
theorem resolventOp_continuousOn_of_bounded {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖g w‖ ≤ C) : ContinuousOn (resolventOp D g) D := by
  intro a ha
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun z : ℂ => C * ∫ w in D,
      ‖resolventKernel z w * rho w - resolventKernel a w * rho w‖) (𝓝[D] a) (𝓝 0) := by
    simpa using (resolvent_mass_l1_tendsto hD ha).const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun z => norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact resolventOp_diff_norm_le hD hg hb hz ha

/-- The continuity part of the RK3 output assertion, before higher regularity is established. -/
theorem RK3_output_continuous {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g : ℂ → ℂ} (hg : g ∈ BCinf D) : ContinuousOn (resolventOp D g) D := by
  obtain ⟨C, hb⟩ := hg.2
  exact resolventOp_continuousOn_of_bounded hD
    (hg.1.continuousOn.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet) hb

/-- The hyperbolic density denominator does not vanish in either open disk model. -/
theorem resolvent_domain_denominator_ne_zero {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) : 1 - ‖z‖ ^ 2 ≠ 0 := by
  rcases hD with rfl | rfl
  · have h : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  · change 1 < ‖z‖ at hz
    nlinarith

/-- The point-pair parameter is smooth off the two unit-circle factors. -/
theorem pointPair_contDiffAt (z w : ℂ)
    (hz : 1 - ‖z‖ ^ 2 ≠ 0) (hw : 1 - ‖w‖ ^ 2 ≠ 0) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => pointPair p.1 p.2) (z, w) := by
  have hn : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ 2) :=
    (contDiff_fst.sub contDiff_snd).norm_sq ℂ
  have hfst : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => ‖p.1‖ ^ 2) := contDiff_fst.norm_sq ℂ
  have hsnd : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => ‖p.2‖ ^ 2) := contDiff_snd.norm_sq ℂ
  unfold pointPair
  exact hn.contDiffAt.div
    ((contDiffAt_const.sub hfst.contDiffAt).mul (contDiffAt_const.sub hsnd.contDiffAt))
    (mul_ne_zero hz hw)

/-- Smoothness of the kernel away from its diagonal singularity; no integral differentiation is asserted. -/
theorem resolventKernel_contDiffAt {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) (hzw : z ≠ w) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => resolventKernel p.1 p.2) (z, w) := by
  have hp := pointPair_contDiffAt z w (resolvent_domain_denominator_ne_zero hD hz)
    (resolvent_domain_denominator_ne_zero hD hw)
  have hu : 0 < pointPair z w := by
    apply pointPair_pos hzw
    rcases hD with rfl | rfl
    · exact Or.inl ⟨hz, hw⟩
    · exact Or.inr ⟨hz, hw⟩
  have hr : ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => (pointPair p.1 p.2 + 1) / pointPair p.1 p.2) (z, w) :=
    (hp.add contDiffAt_const).div hp hu.ne'
  have hl := hr.log (ne_of_gt (div_pos (by linarith : 0 < pointPair z w + 1) hu))
  unfold resolventKernel
  exact ((((contDiffAt_const.mul hp).add contDiffAt_const).div_const (2 * π)).mul hl).sub
    contDiffAt_const

/-- Smoothness of the hyperbolic density in its natural domain. -/
theorem rho_contDiffAt {z : ℂ} (hz : 1 - ‖z‖ ^ 2 ≠ 0) : ContDiffAt ℝ ⊤ rho z := by
  have hn : ContDiff ℝ ⊤ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℂ
  unfold rho
  exact contDiffAt_const.div ((contDiffAt_const.sub hn.contDiffAt).pow 2) (pow_ne_zero _ hz)

/-- Additivity of the resolvent for inputs whose absolute convergence is known from RK3's first clause. -/
theorem resolventOp_add {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {g h : ℂ → ℂ} (hg : g ∈ BCinf D) (hh : h ∈ BCinf D) {z : ℂ} (hz : z ∈ D) :
    resolventOp D (fun w => g w + h w) z = resolventOp D g z + resolventOp D h z := by
  unfold resolventOp
  rw [← integral_add (RK3_absolute_convergence hD hg hz) (RK3_absolute_convergence hD hh hz)]
  apply integral_congr_ae
  filter_upwards with w
  ring

/-- Scalar linearity of the resolvent integral. -/
theorem resolventOp_const_mul (D : Set ℂ) (g : ℂ → ℂ) (c z : ℂ) :
    resolventOp D (fun w => c * g w) z = c * resolventOp D g z := by
  unfold resolventOp
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  ring

/-- The mass normalization implies that the resolvent fixes constant functions. -/
theorem resolventOp_const {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    (c : ℂ) {z : ℂ} (hz : z ∈ D) : resolventOp D (fun _ => c) z = c := by
  calc
    _ = ∫ w in D, c * ((resolventKernel z w * rho w : ℝ) : ℂ) := by
      unfold resolventOp
      apply integral_congr_ae
      filter_upwards with w
      push_cast
      ring
    _ = c * ((∫ w in D, resolventKernel z w * rho w : ℝ) : ℂ) := by
      rw [integral_const_mul, integral_complex_ofReal]
    _ = c := by rw [RK4 hD hz]; simp

/-- (TT:1135) `2(Δ₀ + ½)(1) = 1`. -/
theorem laplace0_const_one (z : ℂ) : 2 * (laplace0 (fun _ => 1) z + (1 / 2) * 1) = 1 := by
  have h : dzbar (fun _ : ℂ => (1 : ℂ)) = fun _ => 0 := by
    funext w
    simp [dzbar]
  rw [laplace0, h]
  norm_num [dz]

/-- **(1.20)** (TT:1145). The kernel `G_Γ(z, w) = Σ_{γ ∈ Γ} G(z, γw)` of the resolvent on `Γ\𝔻` (and on `Γ\𝔻*`),
summed over `Γ/{±1}` (elements with the same action counted once, via the image `{mob γ}`). -/
def resolventKernelGamma (Γ : Subgroup SL2C) (z w : ℂ) : ℝ :=
  ∑' γ : (fun g : SL2C => mob g) '' (Γ : Set SL2C), resolventKernel z ((γ : ℂ → ℂ) w)

end TakhtajanTeo

