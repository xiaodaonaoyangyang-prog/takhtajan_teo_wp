import TakhtajanTeo.Ch1.S2Cover_Completed
import TakhtajanTeo.Ch1.Lemma29Restricted
import TakhtajanTeo.Ch1.ComponentTBasics
import TakhtajanTeo.Ch1.HarmonicResolventTransport

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Block B: A₂-holomorphy of the Bers chart and uncountably many components (`ctb_` prefix) -/

/-- `ψ ↦ (β ∘ Φ)(Λ(ψ) * κ)` is holomorphic on the ball of radius `2` of `A∞(𝔻)`. -/
theorem ctb_G_diff (κ : LinfStarBall) :
    DifferentiableOn ℂ (fun ψ : AInf unitDisc => bersPhi (beltramiMul (Lambda ψ) (κ : LinfStar)))
      (ball (0 : AInf unitDisc) 2) := by
  have h1 : DifferentiableOn ℂ (fun l => beltramiMul l (κ : LinfStar)) LinfStarBall :=
    bd_differentiableOn κ.2
  have h2 : DifferentiableOn ℂ (fun l => bersPhi (beltramiMul l (κ : LinfStar))) LinfStarBall :=
    bersPhi_differentiableOn.comp h1 (fun l hl => bg_mul_mem_ball κ.2 hl)
  exact h2.comp Lambda_differentiable.differentiableOn
    (fun φ hφ => Lambda_mem_ball (mem_ball_zero_iff.mp hφ))

/-- The element of `A₂(𝔻)` represented by `g ∈ A∞(𝔻)` whose function is in `A₂`. -/
theorem ctb_A2toAInf_toA2 {g : AInf unitDisc} (hg : AInf.toFun g ∈ A2fun unitDisc) :
    A2toAInf (toA2 unitDisc (AInf.toFun g)) = g := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  have hg' : g ∈ range A2toAInf := by rw [A2toAInf_range]; exact hg
  obtain ⟨ψ, rfl⟩ := hg'
  have he : EqOn (AInf.toFun (A2toAInf ψ)) (A2.toFun ψ) unitDisc := fun z hz =>
    (A2toAInf_bounded.2 ψ).2 z hz
  have h1 : toA2 unitDisc (AInf.toFun (A2toAInf ψ)) = ψ := by
    apply A2.ext_of_toFun_eqOn measurableSet_ball
    intro z hz
    exact (toA2_spec isOpen_ball hcircle hg hz).trans (he hz)
  rw [h1]

/-! ### Scalar Cauchy estimates in circle-mean form -/

/-- Jensen on `[0, 2π]`: `(∫ f)² ≤ 2π ∫ f²`. -/
theorem ctb_jensen {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ θ in (0 : ℝ)..2 * π, f θ) ^ 2 ≤ 2 * π * ∫ θ in (0 : ℝ)..2 * π, f θ ^ 2 := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∫ θ in (0 : ℝ)..2 * π, f θ) / (2 * π) := ⟨_, rfl⟩
  have hi1 : IntervalIntegrable f volume 0 (2 * π) := hf.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => f θ ^ 2) volume 0 (2 * π) := (hf.pow 2).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, (f θ - m) ^ 2 :=
    intervalIntegral.integral_nonneg hπ.le (fun θ _ => sq_nonneg _)
  have hexp : (fun θ => (f θ - m) ^ 2) = fun θ => f θ ^ 2 - 2 * m * f θ + m ^ 2 := by
    funext θ; ring
  rw [hexp, intervalIntegral.integral_add (hi2.sub (hi1.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hi2 (hi1.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hnn
  simp only [sub_zero, smul_eq_mul] at hnn
  have hI : (∫ θ in (0 : ℝ)..2 * π, f θ) = m * (2 * π) := by
    rw [hm]; field_simp
  rw [hI] at hnn ⊢
  nlinarith

/-- The kernel bound on the circle. -/
theorem ctb_kernel_bound {R : ℝ} (hR : 0 < R) {t w : ℂ} (ht : ‖t‖ ≤ R / 2) (hw : ‖w‖ = R) :
    ‖(w - t)⁻¹ - (w - 0)⁻¹ - t * (1 / (w - 0) ^ 2)‖ ≤ 2 * ‖t‖ ^ 2 / R ^ 3 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith
  have hwt : R / 2 ≤ ‖w - t‖ := by
    have := norm_sub_norm_le w t
    linarith
  have hwt0 : w - t ≠ 0 := by
    intro h; rw [h, norm_zero] at hwt; linarith
  have he : (w - t)⁻¹ - (w - 0)⁻¹ - t * (1 / (w - 0) ^ 2) = t ^ 2 / (w ^ 2 * (w - t)) := by
    rw [sub_zero]
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_pow, norm_pow, hw]
  have hpos : 0 < R ^ 2 * ‖w - t‖ := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have h2 : R ^ 3 ≤ 2 * (R ^ 2 * ‖w - t‖) := by nlinarith [sq_nonneg R]
  nlinarith [sq_nonneg ‖t‖]

/-- The norm of a circle integral of a continuous function, in mean form. -/
theorem ctb_circle_norm_le {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} :
    ‖∮ z in C(0, R), f z‖ ≤ R * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 R θ)‖ := by
  rw [circleIntegral]
  refine (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one,
    abs_of_pos hR]

/-- `‖2πi‖ = 2π`. -/
theorem ctb_norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- From `2π E ≤ R · c · A` and Jensen `A² ≤ 2π B` to `E² ≤ (R c)² (2π)⁻¹ B`. -/
theorem ctb_mean_square {E A B c R : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A) (hc : 0 ≤ c) (hR : 0 < R)
    (h1 : 2 * π * E ≤ R * (c * A)) (hJ : A ^ 2 ≤ 2 * π * B) :
    E ^ 2 ≤ (R * c) ^ 2 * ((2 * π)⁻¹ * B) := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have h2 : (2 * π * E) ^ 2 ≤ (R * c * A) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have h3 : (R * c * A) ^ 2 ≤ (R * c) ^ 2 * (2 * π * B) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hJ (by positivity)
  have h4 : E ^ 2 * (2 * π) ^ 2 ≤ (R * c) ^ 2 * (2 * π * B) := by nlinarith
  have h5 : (R * c) ^ 2 * ((2 * π)⁻¹ * B) = (R * c) ^ 2 * (2 * π * B) / (2 * π) ^ 2 := by
    field_simp
  rw [h5, le_div_iff₀ (by positivity)]
  exact h4

/-- **Second-order Cauchy remainder, mean form.** -/
theorem ctb_cauchy_rem_sq {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (closedBall 0 R))
    {t : ℂ} (ht : ‖t‖ ≤ R / 2) :
    ‖g t - g 0 - t * deriv g 0‖ ^ 2 ≤
      (2 * ‖t‖ ^ 2 / R ^ 2) ^ 2 * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap 0 R θ) - g 0‖ ^ 2) := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have htb : t ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hc : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (closedBall 0 R) := differentiableOn_const 1
  have E1 := hg.circleIntegral_sub_inv_smul htb
  have E2 := hg.circleIntegral_sub_inv_smul h0b
  have E3 := hg.deriv_eq_smul_circleIntegral hR
  have F1 := hc.circleIntegral_sub_inv_smul htb
  have F2 := hc.circleIntegral_sub_inv_smul h0b
  have F3 := hc.deriv_eq_smul_circleIntegral hR
  simp only [smul_eq_mul, deriv_const', mul_zero] at E1 E2 E3 F1 F2 F3
  have hgc : ContinuousOn g (sphere (0 : ℂ) R) := hg.continuousOn.mono sphere_subset_closedBall
  have hne : ∀ z ∈ sphere (0 : ℂ) R, z - t ≠ 0 := by
    intro z hz h
    rw [mem_sphere_zero_iff_norm] at hz
    rw [sub_eq_zero] at h
    rw [h] at hz; linarith
  have hne0 : ∀ z ∈ sphere (0 : ℂ) R, z - 0 ≠ 0 := by
    intro z hz h
    rw [mem_sphere_zero_iff_norm] at hz
    rw [sub_zero] at h
    rw [h, norm_zero] at hz; linarith
  have c1 : ContinuousOn (fun z : ℂ => (z - t)⁻¹) (sphere 0 R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have c2 : ContinuousOn (fun z : ℂ => (z - 0)⁻¹) (sphere 0 R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne0
  have c3 : ContinuousOn (fun z : ℂ => 1 / (z - 0) ^ 2) (sphere 0 R) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun z hz => pow_ne_zero 2 (hne0 z hz))
  obtain ⟨K, hK⟩ : ∃ K : ℂ → ℂ, ∀ z, K z = (z - t)⁻¹ - (z - 0)⁻¹ - t * (1 / (z - 0) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have ci : ∀ f : ℂ → ℂ, ContinuousOn f (sphere 0 R) → CircleIntegrable f 0 R :=
    fun f hf => hf.circleIntegrable hR.le
  have cP1 : ContinuousOn (fun z => (z - t)⁻¹ * g z - (z - 0)⁻¹ * g z) (sphere 0 R) :=
    (c1.mul hgc).sub (c2.mul hgc)
  have cP3 : ContinuousOn (fun z => t * (1 / (z - 0) ^ 2 * g z)) (sphere 0 R) :=
    continuousOn_const.mul (c3.mul hgc)
  have cQ1 : ContinuousOn (fun z => (z - t)⁻¹ * 1 - (z - 0)⁻¹ * 1) (sphere 0 R) :=
    (c1.mul continuousOn_const).sub (c2.mul continuousOn_const)
  have cQ3 : ContinuousOn (fun z => t * (1 / (z - 0) ^ 2 * 1)) (sphere 0 R) :=
    continuousOn_const.mul (c3.mul continuousOn_const)
  have hP : (∮ z in C(0, R), ((z - t)⁻¹ * g z - (z - 0)⁻¹ * g z) - t * (1 / (z - 0) ^ 2 * g z)) =
      2 * π * I * g t - 2 * π * I * g 0 - t * (2 * π * I * deriv g 0) := by
    rw [circleIntegral.integral_sub (ci _ cP1) (ci _ cP3),
      circleIntegral.integral_sub (ci (fun z => (z - t)⁻¹ * g z) (c1.mul hgc))
        (ci (fun z => (z - 0)⁻¹ * g z) (c2.mul hgc)),
      circleIntegral.integral_const_mul, E1, E2, E3]
  have hQ : (∮ z in C(0, R), ((z - t)⁻¹ * 1 - (z - 0)⁻¹ * 1) - t * (1 / (z - 0) ^ 2 * 1)) = 0 := by
    rw [circleIntegral.integral_sub (ci _ cQ1) (ci _ cQ3),
      circleIntegral.integral_sub (ci (fun z => (z - t)⁻¹ * 1) (c1.mul continuousOn_const))
        (ci (fun z => (z - 0)⁻¹ * 1) (c2.mul continuousOn_const)),
      circleIntegral.integral_const_mul, F1, F2, F3]
    ring
  have hsplit : (fun z => K z * (g z - g 0)) = fun z =>
      (((z - t)⁻¹ * g z - (z - 0)⁻¹ * g z) - t * (1 / (z - 0) ^ 2 * g z)) -
        g 0 * (((z - t)⁻¹ * 1 - (z - 0)⁻¹ * 1) - t * (1 / (z - 0) ^ 2 * 1)) := by
    funext z; rw [hK]; ring
  have hint : (∮ z in C(0, R), K z * (g z - g 0)) = 2 * π * I * (g t - g 0 - t * deriv g 0) := by
    rw [hsplit, circleIntegral.integral_sub
      (ci (fun z => ((z - t)⁻¹ * g z - (z - 0)⁻¹ * g z) - t * (1 / (z - 0) ^ 2 * g z)) (cP1.sub cP3))
      (ci (fun z => g 0 * (((z - t)⁻¹ * 1 - (z - 0)⁻¹ * 1) - t * (1 / (z - 0) ^ 2 * 1)))
        (continuousOn_const.mul (cQ1.sub cQ3)))]
    rw [circleIntegral.integral_const_mul, hP, hQ]
    ring
  have cK : ContinuousOn (fun z => K z * (g z - g 0)) (sphere 0 R) := by
    rw [hsplit]
    exact (cP1.sub cP3).sub (continuousOn_const.mul (cQ1.sub cQ3))
  have hΔc : Continuous (fun θ : ℝ => ‖g (circleMap 0 R θ) - g 0‖) :=
    ((hgc.comp_continuous (continuous_circleMap 0 R) (fun θ => circleMap_mem_sphere 0 hR.le θ)).sub
      continuous_const).norm
  have hKc : Continuous (fun θ : ℝ => ‖K (circleMap 0 R θ) * (g (circleMap 0 R θ) - g 0)‖) :=
    (cK.comp_continuous (continuous_circleMap 0 R) (fun θ => circleMap_mem_sphere 0 hR.le θ)).norm
  have hb := ctb_circle_norm_le hR (f := fun z => K z * (g z - g 0))
  have hmono : (∫ θ in (0 : ℝ)..2 * π, ‖K (circleMap 0 R θ) * (g (circleMap 0 R θ) - g 0)‖) ≤
      ∫ θ in (0 : ℝ)..2 * π, 2 * ‖t‖ ^ 2 / R ^ 3 * ‖g (circleMap 0 R θ) - g 0‖ := by
    apply intervalIntegral.integral_mono_on hπ.le (hKc.intervalIntegrable _ _)
      ((continuous_const.mul hΔc).intervalIntegrable _ _)
    intro θ _
    rw [norm_mul, hK]
    have hw : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_right (ctb_kernel_bound hR ht hw) (norm_nonneg _)
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hint, norm_mul, ctb_norm_two_pi_I] at hb
  have hJ := ctb_jensen hΔc
  have hA0 : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap 0 R θ) - g 0‖ :=
    intervalIntegral.integral_nonneg hπ.le (fun θ _ => norm_nonneg _)
  have h1 : 2 * π * ‖g t - g 0 - t * deriv g 0‖ ≤
      R * (2 * ‖t‖ ^ 2 / R ^ 3 * ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap 0 R θ) - g 0‖) :=
    hb.trans (mul_le_mul_of_nonneg_left hmono hR.le)
  have h2 := ctb_mean_square (norm_nonneg _) hA0 (by positivity) hR h1 hJ
  have h3 : R * (2 * ‖t‖ ^ 2 / R ^ 3) = 2 * ‖t‖ ^ 2 / R ^ 2 := by field_simp
  rw [h3] at h2
  exact h2

/-- **First-order Cauchy estimate, mean form.** -/
theorem ctb_cauchy_deriv_sq {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (closedBall 0 R)) :
    ‖deriv g 0‖ ^ 2 ≤ (1 / R) ^ 2 * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap 0 R θ) - g 0‖ ^ 2) := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have hc : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (closedBall 0 R) := differentiableOn_const 1
  have E3 := hg.deriv_eq_smul_circleIntegral hR
  have F3 := hc.deriv_eq_smul_circleIntegral hR
  simp only [smul_eq_mul, deriv_const', mul_zero] at E3 F3
  have hgc : ContinuousOn g (sphere (0 : ℂ) R) := hg.continuousOn.mono sphere_subset_closedBall
  have hne0 : ∀ z ∈ sphere (0 : ℂ) R, z - 0 ≠ 0 := by
    intro z hz h
    rw [mem_sphere_zero_iff_norm] at hz
    rw [sub_zero] at h
    rw [h, norm_zero] at hz; linarith
  have c3 : ContinuousOn (fun z : ℂ => 1 / (z - 0) ^ 2) (sphere 0 R) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun z hz => pow_ne_zero 2 (hne0 z hz))
  have hsplit : (fun z => 1 / (z - 0) ^ 2 * (g z - g 0)) = fun z =>
      1 / (z - 0) ^ 2 * g z - g 0 * (1 / (z - 0) ^ 2 * 1) := by
    funext z; ring
  have hint : (∮ z in C(0, R), 1 / (z - 0) ^ 2 * (g z - g 0)) = 2 * π * I * deriv g 0 := by
    rw [hsplit, circleIntegral.integral_sub
      ((c3.mul hgc).circleIntegrable hR.le (f := fun z => 1 / (z - 0) ^ 2 * g z))
      ((continuousOn_const.mul (c3.mul continuousOn_const)).circleIntegrable hR.le
        (f := fun z => g 0 * (1 / (z - 0) ^ 2 * 1))),
      circleIntegral.integral_const_mul, E3, F3]
    ring
  have hΔc : Continuous (fun θ : ℝ => ‖g (circleMap 0 R θ) - g 0‖) :=
    ((hgc.comp_continuous (continuous_circleMap 0 R) (fun θ => circleMap_mem_sphere 0 hR.le θ)).sub
      continuous_const).norm
  have hb := ctb_circle_norm_le hR (f := fun z => 1 / (z - 0) ^ 2 * (g z - g 0))
  have hmono : (∫ θ in (0 : ℝ)..2 * π, ‖1 / (circleMap 0 R θ - 0) ^ 2 * (g (circleMap 0 R θ) - g 0)‖) =
      ∫ θ in (0 : ℝ)..2 * π, 1 / R ^ 2 * ‖g (circleMap 0 R θ) - g 0‖ := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [norm_mul, norm_div, norm_one, norm_pow, sub_zero, norm_circleMap_zero, abs_of_pos hR]
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hint, norm_mul, ctb_norm_two_pi_I, hmono] at hb
  have hJ := ctb_jensen hΔc
  have hA0 : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap 0 R θ) - g 0‖ :=
    intervalIntegral.integral_nonneg hπ.le (fun θ _ => norm_nonneg _)
  have h2 := ctb_mean_square (norm_nonneg _) hA0 (by positivity) hR hb hJ
  have h3 : R * (1 / R ^ 2) = 1 / R := by field_simp
  rw [h3] at h2
  exact h2

/-! ### `A₂` norms of `A∞` elements -/

/-- Evaluation at a point of the disc is a continuous linear functional on `A∞(𝔻)`. -/
theorem ctb_ev {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ ev : AInf unitDisc →L[ℂ] ℂ, ∀ φ : AInf unitDisc, ev φ = AInf.toFun φ z := by
  refine ⟨((1 - ‖z‖ ^ 2 : ℂ) ^ 2)⁻¹ • ((BoundedContinuousFunction.evalCLM ℂ (⟨z, hz⟩ : unitDisc)).comp
      (Submodule.subtypeL _)), fun φ => ?_⟩
  simp [AInf.toFun, unweight, dite_eq_left hz, div_eq_inv_mul]

/-- `AInf.toFun` is additive. -/
theorem ctb_toFun_sub (a b : AInf unitDisc) : AInf.toFun (a - b) = AInf.toFun a - AInf.toFun b := by
  funext z
  by_cases hz : z ∈ unitDisc
  · obtain ⟨ev, hev⟩ := ctb_ev hz
    rw [Pi.sub_apply, ← hev, ← hev, ← hev, map_sub]
  · simp [AInf.toFun, unweight, hz]

/-- `AInf.toFun` is homogeneous. -/
theorem ctb_toFun_smul (c : ℂ) (a : AInf unitDisc) : AInf.toFun (c • a) = fun z => c * AInf.toFun a z := by
  funext z
  by_cases hz : z ∈ unitDisc
  · obtain ⟨ev, hev⟩ := ctb_ev hz
    rw [← hev, ← hev, map_smul, smul_eq_mul]
  · simp [AInf.toFun, unweight, hz]

/-- The `A₂` norm of an element of `A₂(𝔻)` through its `A∞` image. -/
theorem ctb_nnnorm_eq (ψ : A2 unitDisc) :
    (‖ψ‖₊ : ℝ≥0∞) = normA2 unitDisc (AInf.toFun (A2toAInf ψ)) := by
  rw [← A2.norm_toFun]
  exact normA2_congr measurableSet_ball (fun z hz => ((A2toAInf_bounded.2 ψ).2 z hz).symm)

theorem ctb_norm_le_of_normA2 {ψ : A2 unitDisc} {c : ℝ} (hc : 0 ≤ c)
    (h : normA2 unitDisc (AInf.toFun (A2toAInf ψ)) ≤ ENNReal.ofReal c) : ‖ψ‖ ≤ c := by
  rw [← ctb_nnnorm_eq] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa [ENNReal.toReal_ofReal hc] using this

/-- Triangle inequality for `normA2` on `A∞` elements. -/
theorem ctb_normA2_sub_le (a b : AInf unitDisc) :
    normA2 unitDisc (AInf.toFun (a - b)) ≤ normA2 unitDisc (AInf.toFun a) + normA2 unitDisc (AInf.toFun b) := by
  have ha := (wp_AInf_disc_measurable a).aestronglyMeasurable (μ := rhoInvMeasure unitDisc)
  have hb := (wp_AInf_disc_measurable b).aestronglyMeasurable (μ := rhoInvMeasure unitDisc)
  rw [ctb_toFun_sub, normA2_eq_eLpNorm _ _ (ha.sub hb), normA2_eq_eLpNorm _ _ ha,
    normA2_eq_eLpNorm _ _ hb]
  exact eLpNorm_sub_le (by norm_num)

/-- Integrated circle-mean bound: if `|e(z)|² ≤ c · (2π)⁻¹ ∫ |Φ(θ)(z)|² dθ` on the disc and every `Φ(θ)` has
`A₂` norm at most `N`, then `‖e‖₂ ≤ √c · N`. -/
theorem ctb_line_lintegral {Φ : ℝ → AInf unitDisc} (hΦ : Continuous Φ) {N c : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c)
    (hb : ∀ θ, normA2 unitDisc (AInf.toFun (Φ θ)) ≤ ENNReal.ofReal N) {e : ℂ → ℂ}
    (he : ∀ z ∈ unitDisc,
      ‖e z‖ ^ 2 ≤ c * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖AInf.toFun (Φ θ) z‖ ^ 2)) :
    normA2 unitDisc e ≤ ENNReal.ofReal (Real.sqrt c * N) := by
  have hπ : 0 < 2 * π := Real.two_pi_pos
  have hρm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) := by unfold rho; fun_prop
  -- continuity in `θ` of the values
  have hcz : ∀ z, Continuous (fun θ => AInf.toFun (Φ θ) z) := by
    intro z
    by_cases hz : z ∈ unitDisc
    · obtain ⟨ev, hev⟩ := ctb_ev hz
      simp only [← hev]
      exact ev.continuous.comp hΦ
    · have : (fun θ => AInf.toFun (Φ θ) z) = fun _ => 0 := by
        funext θ; simp [AInf.toFun, unweight, hz]
      rw [this]; exact continuous_const
  -- the inner `θ`-integral as a lintegral
  have hinner : ∀ z, ENNReal.ofReal (∫ θ in (0 : ℝ)..2 * π, ‖AInf.toFun (Φ θ) z‖ ^ 2) =
      ∫⁻ θ in Ioc 0 (2 * π), (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 := by
    intro z
    rw [intervalIntegral.integral_of_le hπ.le, ofReal_integral_eq_lintegral_ofReal]
    · apply lintegral_congr
      intro θ
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    · exact (((hcz z).norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact Eventually.of_forall (fun θ => sq_nonneg _)
  -- pointwise bound
  have hpt : ∀ z ∈ unitDisc, (‖e z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤
      ENNReal.ofReal (c * (2 * π)⁻¹) *
        ((∫⁻ θ in Ioc 0 (2 * π), (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (rho z)⁻¹) := by
    intro z hz
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← hinner z, ← ENNReal.ofReal_mul (by positivity), ← enorm_eq_nnnorm, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have := he z hz
    linarith [show c * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖AInf.toFun (Φ θ) z‖ ^ 2) =
      c * (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖AInf.toFun (Φ θ) z‖ ^ 2 by ring]
  -- joint measurability
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℂ → ℝ≥0∞, ∀ θ z,
      u θ z = (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := ⟨_, fun _ _ => rfl⟩
  have hu1 : ∀ z, Continuous fun θ => u θ z := by
    intro z
    simp only [hu]
    exact (ENNReal.continuous_mul_const ENNReal.ofReal_ne_top).comp
      ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp (hcz z).nnnorm))
  have hu2 : ∀ θ, Measurable (u θ) := by
    intro θ
    have : u θ = fun z => (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := funext (hu θ)
    rw [this]
    exact ((wp_AInf_disc_measurable (Φ θ)).nnnorm.coe_nnreal_ennreal.pow_const 2).mul hρm
  have hm0 : Measurable (fun p : ℂ × ℝ => u p.2 p.1) :=
    (measurable_uncurry_of_continuous_of_measurable hu1 hu2).comp measurable_swap
  have hmeas : Measurable (Function.uncurry fun (z : ℂ) (θ : ℝ) =>
      (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) := by
    have e : (Function.uncurry fun (z : ℂ) (θ : ℝ) =>
        (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) = fun p : ℂ × ℝ => u p.2 p.1 := by
      funext p
      rw [hu]
      rfl
    rw [e]
    exact hm0
  -- the `A₂` norms along the circle
  have hsq : ∀ θ, ∫⁻ z in unitDisc, (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤
      ENNReal.ofReal (N ^ 2) := by
    intro θ
    have h1 := hb θ
    unfold normA2 at h1
    have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hN (by norm_num)] at h2
    norm_num at h2
    simpa [Real.rpow_two] using h2
  -- assemble
  have hS : ∫⁻ z in unitDisc, (‖e z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤ ENNReal.ofReal (c * N ^ 2) := by
    calc ∫⁻ z in unitDisc, (‖e z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹
        ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (c * (2 * π)⁻¹) *
          ((∫⁻ θ in Ioc 0 (2 * π), (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (rho z)⁻¹) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (c * (2 * π)⁻¹) * ∫⁻ z in unitDisc, ∫⁻ θ in Ioc 0 (2 * π),
          (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          apply lintegral_congr
          intro z
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (c * (2 * π)⁻¹) * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ z in unitDisc,
          (‖AInf.toFun (Φ θ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
          rw [lintegral_lintegral_swap hmeas.aemeasurable]
      _ ≤ ENNReal.ofReal (c * (2 * π)⁻¹) * ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (N ^ 2) := by
          gcongr with θ
          exact hsq θ
      _ = ENNReal.ofReal (c * N ^ 2) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  unfold normA2
  calc (∫⁻ z in unitDisc, (‖e z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (c * N ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hS (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt c * N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_mul hc, Real.sqrt_sq hN]

/-! ### Holomorphy into `A₂(𝔻)` -/

/-- A map `F : U ⊂ A₂(𝔻) → A∞(𝔻)` that is Banach-holomorphic, takes values in `A₂(𝔻)` and is locally bounded in
the `A₂` norm, is holomorphic as a map into the Hilbert space `A₂(𝔻)` (the `A₂` derivative is the `A∞` derivative;
second-order remainder by the Cauchy integral on circles). -/
theorem ctb_holo_of_bounded {U : Set (A2 unitDisc)} (hU : IsOpen U) {F : A2 unitDisc → AInf unitDisc}
    (hF : DifferentiableOn ℂ F U) (hmem : ∀ x ∈ U, AInf.toFun (F x) ∈ A2fun unitDisc)
    (hbd : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ ball x r,
      y ∈ U ∧ normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal M) :
    DifferentiableOn ℂ (fun x => toA2 unitDisc (AInf.toFun (F x))) U := by
  intro x hx
  obtain ⟨r, hr, M₀, hM₀⟩ := hbd x hx
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max M₀ 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact le_max_right _ _
  have hMb : ∀ y ∈ ball x r, y ∈ U ∧ normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal M := by
    intro y hy
    refine ⟨(hM₀ y hy).1, (hM₀ y hy).2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [hM]; exact le_max_left _ _
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r / 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRr : R < r := by rw [hR]; linarith
  have hFd : ∀ y ∈ ball x r, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (hF.differentiableAt (hU.mem_nhds (hMb y hy).1)).hasFDerivAt
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℂ F x := ⟨_, rfl⟩
  have hFx : HasFDerivAt F L x := by rw [hL]; exact hFd x (mem_ball_self hr)
  -- the line through `x` in direction `u`
  have hin : ∀ u : A2 unitDisc, ‖u‖ ≤ 1 → ∀ w ∈ closedBall (0 : ℂ) R, x + w • u ∈ ball x r := by
    intro u hu w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have : ‖w‖ ≤ R := mem_closedBall_zero_iff.mp hw
    nlinarith [norm_nonneg w, norm_nonneg u]
  have hline : ∀ u : A2 unitDisc, ‖u‖ ≤ 1 → ∀ z ∈ unitDisc,
      DifferentiableOn ℂ (fun w : ℂ => AInf.toFun (F (x + w • u)) z) (closedBall 0 R) ∧
      deriv (fun w : ℂ => AInf.toFun (F (x + w • u)) z) 0 = AInf.toFun (L u) z := by
    intro u hu z hz
    obtain ⟨ev, hev⟩ := ctb_ev hz
    have hl : ∀ w : ℂ, HasDerivAt (fun w : ℂ => x + w • u) u w := by
      intro w
      simpa using ((hasDerivAt_id w).smul_const u).const_add x
    have hcomp : ∀ w ∈ closedBall (0 : ℂ) R, HasDerivAt (fun w : ℂ => AInf.toFun (F (x + w • u)) z)
        (ev (fderiv ℂ F (x + w • u) u)) w := by
      intro w hw
      have h1 := (hFd _ (hin u hu w hw)).comp_hasDerivAt w (hl w)
      have h2 := ev.hasFDerivAt.comp_hasDerivAt w h1
      simpa only [Function.comp_def, hev] using h2
    refine ⟨fun w hw => (hcomp w hw).differentiableAt.differentiableWithinAt, ?_⟩
    have h0 := hcomp 0 (mem_closedBall_self hR0.le)
    rw [h0.deriv, zero_smul, add_zero, ← hL, hev]
  -- the circle data
  have hcircle : ∀ u : A2 unitDisc, ‖u‖ ≤ 1 →
      Continuous (fun θ : ℝ => F (x + circleMap 0 R θ • u) - F x) ∧
      ∀ θ, normA2 unitDisc (AInf.toFun (F (x + circleMap 0 R θ • u) - F x)) ≤ ENNReal.ofReal (2 * M) := by
    intro u hu
    have hmemc : ∀ θ : ℝ, x + circleMap 0 R θ • u ∈ ball x r := fun θ =>
      hin u hu _ (sphere_subset_closedBall (circleMap_mem_sphere 0 hR0.le θ))
    refine ⟨?_, fun θ => ?_⟩
    · have hc : ContinuousOn F (ball x r) := hF.continuousOn.mono (fun y hy => (hMb y hy).1)
      exact (hc.comp_continuous (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const))
        hmemc).sub continuous_const
    · refine (ctb_normA2_sub_le _ _).trans ?_
      rw [show (2 * M) = M + M by ring, ENNReal.ofReal_add hM0 hM0]
      exact add_le_add (hMb _ (hmemc θ)).2 (hMb x (mem_ball_self hr)).2
  have hval : ∀ u : A2 unitDisc, ∀ z, ∀ θ : ℝ, AInf.toFun (F (x + circleMap 0 R θ • u) - F x) z =
      (fun w : ℂ => AInf.toFun (F (x + w • u)) z) (circleMap 0 R θ) -
        (fun w : ℂ => AInf.toFun (F (x + w • u)) z) 0 := by
    intro u z θ
    rw [ctb_toFun_sub]
    simp only [Pi.sub_apply, zero_smul, add_zero]
  -- the derivative maps into `A₂`, with a bound
  have hLu : ∀ u : A2 unitDisc, ‖u‖ ≤ 1 →
      normA2 unitDisc (AInf.toFun (L u)) ≤ ENNReal.ofReal (1 / R * (2 * M)) := by
    intro u hu
    obtain ⟨hc1, hc2⟩ := hcircle u hu
    have := ctb_line_lintegral hc1 (by positivity) (sq_nonneg (1 / R)) hc2 (e := AInf.toFun (L u))
      (fun z hz => by
        obtain ⟨hd, hdr⟩ := hline u hu z hz
        have h := ctb_cauchy_deriv_sq hR0 hd
        rw [hdr] at h
        simpa only [hval u z] using h)
    rwa [Real.sqrt_sq (by positivity)] at this
  have hLh : ∀ h : A2 unitDisc, normA2 unitDisc (AInf.toFun (L h)) ≤
      ENNReal.ofReal (1 / R * (2 * M) * ‖h‖) := by
    intro h
    by_cases h0 : h = 0
    · subst h0
      rw [map_zero]
      have : AInf.toFun (0 : AInf unitDisc) = fun z => (0 : ℂ) * AInf.toFun (0 : AInf unitDisc) z := by
        rw [← ctb_toFun_smul, zero_smul]
      rw [this, normA2_const_mul]
      simp
    · have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
      have hu : ‖((‖h‖ : ℂ))⁻¹ • h‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
          inv_mul_cancel₀ hn.ne']
      have heq : L h = ((‖h‖ : ℂ)) • L (((‖h‖ : ℂ))⁻¹ • h) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
      rw [heq, ctb_toFun_smul, normA2_const_mul]
      have h1 := hLu _ hu
      calc (‖((‖h‖ : ℂ))‖₊ : ℝ≥0∞) * normA2 unitDisc (AInf.toFun (L (((‖h‖ : ℂ))⁻¹ • h)))
          ≤ ENNReal.ofReal ‖h‖ * ENNReal.ofReal (1 / R * (2 * M)) := by
            gcongr
            rw [← enorm_eq_nnnorm, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
        _ = ENNReal.ofReal (1 / R * (2 * M) * ‖h‖) := by
            rw [← ENNReal.ofReal_mul hn.le, mul_comm]
  have hLmem : ∀ h, AInf.toFun (L h) ∈ A2fun unitDisc := fun h =>
    ⟨(L h).2, lt_of_le_of_lt (hLh h) ENNReal.ofReal_lt_top⟩
  -- the candidate derivative `D : A₂ → A₂`
  have hadd : ∀ a b : A2 unitDisc, A2toAInf (a + b) = A2toAInf a + A2toAInf b := fun a b =>
    map_add A2toAInfCLM a b
  have hsmul : ∀ (c : ℂ) (a : A2 unitDisc), A2toAInf (c • a) = c • A2toAInf a := fun c a =>
    map_smul A2toAInfCLM c a
  have hsub : ∀ a b : A2 unitDisc, A2toAInf (a - b) = A2toAInf a - A2toAInf b := fun a b =>
    map_sub A2toAInfCLM a b
  let D0 : A2 unitDisc →ₗ[ℂ] A2 unitDisc :=
    { toFun := fun h => toA2 unitDisc (AInf.toFun (L h))
      map_add' := fun a b => by
        apply A2toAInf_injective
        rw [hadd, ctb_A2toAInf_toA2 (hLmem _), ctb_A2toAInf_toA2 (hLmem _), ctb_A2toAInf_toA2 (hLmem _),
          map_add]
      map_smul' := fun c a => by
        apply A2toAInf_injective
        simp only [RingHom.id_apply]
        rw [hsmul, ctb_A2toAInf_toA2 (hLmem _), ctb_A2toAInf_toA2 (hLmem _), map_smul] }
  have hD0 : ∀ h, A2toAInf (D0 h) = L h := fun h => ctb_A2toAInf_toA2 (hLmem h)
  let D : A2 unitDisc →L[ℂ] A2 unitDisc := D0.mkContinuous (1 / R * (2 * M)) (fun h => by
    apply ctb_norm_le_of_normA2 (by positivity)
    rw [hD0]
    exact hLh h)
  have hD : ∀ h, A2toAInf (D h) = L h := hD0
  -- the remainder estimate
  have hG : ∀ y ∈ U, A2toAInf (toA2 unitDisc (AInf.toFun (F y))) = F y := fun y hy =>
    ctb_A2toAInf_toA2 (hmem y hy)
  have hrem : ∀ h : A2 unitDisc, ‖h‖ ≤ R / 2 →
      ‖toA2 unitDisc (AInf.toFun (F (x + h))) - toA2 unitDisc (AInf.toFun (F x)) - D h‖ ≤
        2 / R ^ 2 * (2 * M) * ‖h‖ ^ 2 := by
    intro h hh
    have hxh : x + h ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith
    apply ctb_norm_le_of_normA2 (by positivity)
    rw [hsub, hsub, hG _ (hMb _ hxh).1, hG x hx, hD]
    by_cases h0 : h = 0
    · subst h0
      rw [add_zero, sub_self, map_zero, sub_zero]
      have : AInf.toFun (0 : AInf unitDisc) = fun z => (0 : ℂ) * AInf.toFun (0 : AInf unitDisc) z := by
        rw [← ctb_toFun_smul, zero_smul]
      rw [this, normA2_const_mul]
      simp
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
    obtain ⟨u, hu⟩ : ∃ u : A2 unitDisc, u = ((‖h‖ : ℂ))⁻¹ • h := ⟨_, rfl⟩
    have hu1 : ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
        inv_mul_cancel₀ hn.ne']
    have hhu : h = ((‖h‖ : ℂ)) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    obtain ⟨hc1, hc2⟩ := hcircle u hu1
    have hres := ctb_line_lintegral hc1 (by positivity) (sq_nonneg (2 * ‖((‖h‖ : ℂ))‖ ^ 2 / R ^ 2)) hc2
      (e := AInf.toFun (F (x + h) - F x - L h)) (fun z hz => by
        obtain ⟨hd, hdr⟩ := hline u hu1 z hz
        have ht : ‖((‖h‖ : ℂ))‖ ≤ R / 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]; exact hh
        have hc := ctb_cauchy_rem_sq hR0 hd ht
        rw [hdr] at hc
        have hez : AInf.toFun (F (x + h) - F x - L h) z =
            (fun w : ℂ => AInf.toFun (F (x + w • u)) z) ((‖h‖ : ℂ)) -
              (fun w : ℂ => AInf.toFun (F (x + w • u)) z) 0 - ((‖h‖ : ℂ)) * AInf.toFun (L u) z := by
          have hLh' : L h = ((‖h‖ : ℂ)) • L u := by
            conv_lhs => rw [hhu]
            exact map_smul L _ _
          rw [ctb_toFun_sub, ctb_toFun_sub, hLh', ctb_toFun_smul]
          simp only [Pi.sub_apply, zero_smul, add_zero]
          rw [← hhu]
        rw [hez]
        simpa only [hval u z] using hc)
    rw [Real.sqrt_sq (by positivity), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] at hres
    refine hres.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  -- `HasFDerivAt`
  have hfd : HasFDerivAt (fun y => toA2 unitDisc (AInf.toFun (F y))) D x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound (2 / R ^ 2 * (2 * M)) ?_
    filter_upwards [ball_mem_nhds (0 : A2 unitDisc) (by positivity : (0 : ℝ) < R / 2)] with h hh
    have hh' : ‖h‖ ≤ R / 2 := (mem_ball_zero_iff.mp hh).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hrem h hh'
  exact hfd.differentiableAt.differentiableWithinAt

/-- `β` of the chart image, in terms of `β ∘ Φ`. -/
theorem ctb_bers_chartInv (μ : LinfStarBall) {ψ : AInf unitDisc} (hψ : ‖ψ‖ < 2) :
    bers (bersChartInv μ ψ) = bersPhi (beltramiMul (Lambda ψ) (μ : LinfStar)) := by
  rw [ct_bersChartInv_eq hψ, bt_rightTrans_phi, bers_Phi]

/-- **Theorem 2.13**, first two bullets, verbatim (the third bullet and `β(T(1))` open are separate). -/
theorem ctb_thm_2_13_b12 :
    ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
      (∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ) ∈ A2fun unitDisc) ∧
      DifferentiableOn ℂ
        (fun φ => toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ)))
        (ball 0 (Real.sqrt (π / 3))) := by
  intro μ hμ
  obtain ⟨F, hFdef⟩ : ∃ F : A2 unitDisc → AInf unitDisc, ∀ φ, F φ =
      bersPhi (beltramiMul (Lambda (A2toAInf φ)) (μ : LinfStar)) - bersPhi μ := ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (π / 3) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hFeq : ∀ φ ∈ ball (0 : A2 unitDisc) r,
      bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ = F φ := fun φ hφ => by
    rw [hFdef, ctb_bers_chartInv μ (ct_A2toAInf_norm_lt (hr ▸ hφ))]
  have hGd : DifferentiableOn ℂ (fun φ => bersPhi (beltramiMul (Lambda (A2toAInf φ)) (μ : LinfStar)))
      (ball (0 : A2 unitDisc) r) :=
    (ctb_G_diff μ).comp A2toAInfCLM.differentiableOn
      (fun φ hφ => mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt (hr ▸ hφ)))
  have hF : DifferentiableOn ℂ F (ball (0 : A2 unitDisc) r) := by
    have := hGd.sub (differentiableOn_const (bersPhi (μ : LinfStar)))
    exact this.congr (fun φ _ => hFdef φ)
  have hbd : ∀ x ∈ ball (0 : A2 unitDisc) r, ∃ ρ > 0, ∃ M : ℝ, ∀ y ∈ ball x ρ,
      y ∈ ball (0 : A2 unitDisc) r ∧ normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal M := by
    intro x hx
    have hnx : ‖A2toAInf x‖ < 2 := ct_A2toAInf_norm_lt (hr ▸ hx)
    obtain ⟨C, hC, hCb⟩ := l29r_restricted hμ (k := (‖A2toAInf x‖ + 2) / 2) (by linarith)
    have hk : ‖A2toAInf x‖ < (‖A2toAInf x‖ + 2) / 2 := by linarith
    have hxr : ‖x‖ < r := mem_ball_zero_iff.mp hx
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖A2toAInfCLM‖ := ⟨_, rfl⟩
    have hL0 : 0 ≤ L := by rw [hL]; exact norm_nonneg A2toAInfCLM
    refine ⟨min (r - ‖x‖) (((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1)), ?_, C * r, ?_⟩
    · apply lt_min (by linarith)
      apply div_pos (by linarith) (by linarith)
    · intro y hy
      have hd : dist y x < min (r - ‖x‖) (((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1)) :=
        mem_ball.mp hy
      have hd1 : dist y x < r - ‖x‖ := lt_of_lt_of_le hd (min_le_left _ _)
      have hd2 : dist y x < ((‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖) / (L + 1) :=
        lt_of_lt_of_le hd (min_le_right _ _)
      have hyx : ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
      have hyU : y ∈ ball (0 : A2 unitDisc) r := by
        rw [mem_ball_zero_iff]
        have := norm_le_norm_add_norm_sub' y x
        linarith
      refine ⟨hyU, ?_⟩
      have hyk : ‖A2toAInf y‖ ≤ (‖A2toAInf x‖ + 2) / 2 := by
        have e1 : A2toAInf y = A2toAInf x + A2toAInfCLM (y - x) := by
          rw [map_sub]; simp
        have e2 : ‖A2toAInfCLM (y - x)‖ ≤ L * ‖y - x‖ := by
          rw [hL]; exact A2toAInfCLM.le_opNorm _
        have e3 : L * ‖y - x‖ ≤ (L + 1) * ‖y - x‖ := by
          apply mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        have e4 : (L + 1) * ‖y - x‖ ≤ (‖A2toAInf x‖ + 2) / 2 - ‖A2toAInf x‖ := by
          rw [hyx]
          have := (lt_div_iff₀ (by linarith : (0:ℝ) < L + 1)).mp hd2
          linarith
        have e5 := norm_add_le (A2toAInf x) (A2toAInfCLM (y - x))
        rw [e1]
        linarith
      have h1 := hCb y hyk
      have h2 : normA2 unitDisc (AInf.toFun (F y)) ≤ ENNReal.ofReal C * (‖y‖₊ : ℝ≥0∞) := by
        rw [hFdef]; exact h1
      refine h2.trans ?_
      have hyr : ‖y‖ ≤ r := (mem_ball_zero_iff.mp hyU).le
      have : (‖y‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖y‖ := by
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
      rw [this, ← ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hyr hC.le)
  have hmem : ∀ x ∈ ball (0 : A2 unitDisc) r, AInf.toFun (F x) ∈ A2fun unitDisc := by
    intro x hx
    obtain ⟨ρ, hρ, M, hM⟩ := hbd x hx
    refine ⟨(F x).2, ?_⟩
    exact lt_of_le_of_lt (hM x (mem_ball_self hρ)).2 ENNReal.ofReal_lt_top
  have hH := ctb_holo_of_bounded isOpen_ball hF hmem hbd
  refine ⟨fun φ hφ => ?_, hH.congr (fun φ hφ => ?_)⟩
  · rw [hFeq φ hφ]; exact hmem φ hφ
  · rw [hFeq φ hφ]

/-- The Bers embedding is continuous from the Hilbert manifold topology of `T(1)` to that of `A∞(𝔻)`. -/
theorem ctb_bers_continuous_hilbert : @Continuous T1 (AInf unitDisc) hilbertTopology hilbertTopologyA bers := by
  unfold hilbertTopology
  rw [continuous_iSup_dom]
  intro μ
  rw [continuous_coinduced_dom]
  obtain ⟨hmem, hdiff⟩ := ctb_thm_2_13_b12 μ.1 μ.2
  have hcont : Continuous (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      toA2 unitDisc (AInf.toFun (bers (bersChartInv μ.1 (A2toAInf φ)) - bersPhi (μ.1 : LinfStar)))) :=
    hdiff.continuousOn.comp_continuous continuous_subtype_val (fun φ => φ.2)
  have hcl : Continuous[(inferInstance : TopologicalSpace (A2 unitDisc)), hilbertTopologyA]
      (fun ψ : A2 unitDisc => bersPhi (μ.1 : LinfStar) + A2toAInf ψ) := by
    apply continuous_iff_coinduced_le.mpr
    unfold hilbertTopologyA
    exact le_iSup (fun χ : AInf unitDisc =>
      (TopologicalSpace.coinduced (fun ψ : A2 unitDisc => χ + A2toAInf ψ)
        (inferInstance : TopologicalSpace (A2 unitDisc)) : TopologicalSpace (AInf unitDisc)))
      (bersPhi (μ.1 : LinfStar))
  have heq : (bers ∘ fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf φ)) = fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
        bersPhi (μ.1 : LinfStar) + A2toAInf
        (toA2 unitDisc (AInf.toFun (bers (bersChartInv μ.1 (A2toAInf φ)) - bersPhi (μ.1 : LinfStar)))) := by
    funext φ
    simp only [Function.comp_apply]
    rw [ctb_A2toAInf_toA2 (hmem φ φ.2)]
    abel
  rw [heq]
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  exact hcl.comp hcont

/-- (TT:1354) In the Hilbert manifold topology `T(1)` is a disjoint union of uncountably many components
(`componentT_uncountable`, verbatim). -/
theorem ctb_componentT_uncountable : ¬ (range componentT).Countable := by
  intro hcount
  let P := LinearMap.range A2toAInfCLM.toLinearMap
  haveI hunc : Uncountable (AInf unitDisc ⧸ P) := AInf_quotient_A2_uncountable
  -- the classes having a representative in the ball of radius `2`
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Set (AInf unitDisc ⧸ P), Q' = {q | ∃ φ : AInf unitDisc, ‖φ‖ < 2 ∧ P.mkQ φ = q} :=
    ⟨_, rfl⟩
  have hQ'unc : ¬ Q'.Countable := by
    intro hc
    have hcov : (univ : Set (AInf unitDisc ⧸ P)) =
        ⋃ n : ℕ, (fun q : AInf unitDisc ⧸ P => (((n + 1 : ℕ) : ℂ)) • q) '' Q' := by
      ext q
      simp only [mem_univ, mem_iUnion, mem_image, true_iff]
      obtain ⟨φ, rfl⟩ := P.mkQ_surjective q
      obtain ⟨n, hn⟩ := exists_nat_gt (‖φ‖ / 2)
      have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      refine ⟨n, P.mkQ (((n + 1 : ℕ) : ℂ)⁻¹ • φ), ?_, ?_⟩
      · rw [hQ']
        refine ⟨((n + 1 : ℕ) : ℂ)⁻¹ • φ, ?_, rfl⟩
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [inv_mul_lt_iff₀ hpos]
        push_cast
        linarith
      · show ((n + 1 : ℕ) : ℂ) • P.mkQ (((n + 1 : ℕ) : ℂ)⁻¹ • φ) = P.mkQ φ
        rw [map_smul, smul_smul, mul_inv_cancel₀ hn1, one_smul]
    have : (univ : Set (AInf unitDisc ⧸ P)).Countable := by
      rw [hcov]
      exact countable_iUnion (fun n => hc.image _)
    exact not_countable (Set.countable_univ_iff.mp this)
  have hex : ∀ q ∈ Q', ∃ p : T1, P.mkQ (bers p) = q := by
    intro q hq
    rw [hQ'] at hq
    obtain ⟨φ, hφ, rfl⟩ := hq
    obtain ⟨h, hb⟩ := ahlfors_weill hφ
    exact ⟨Phi ⟨Lambda φ, h⟩, by rw [hb]⟩
  choose! s hs using hex
  have hinj : Set.InjOn (fun q => componentT (s q)) Q' := by
    intro q hq q' hq' h
    letI : TopologicalSpace T1 := hilbertTopology
    letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
    have hmem : s q' ∈ componentT (s q) := by
      have : s q' ∈ componentT (s q') := mem_connectedComponent
      simpa only [h] using this
    have h1 := (ctb_bers_continuous_hilbert).image_connectedComponent_subset (s q)
      ⟨s q', hmem, rfl⟩
    rw [hilbertTopologyA_component, affine_A2_coset_eq_quotient_fiber] at h1
    have h2 : P.mkQ (bers (s q')) = P.mkQ (bers (s q)) := h1
    rw [hs q' hq', hs q hq] at h2
    exact h2.symm
  exact hQ'unc (Set.MapsTo.countable_of_injOn
    (f := fun q => componentT (s q)) (fun q _ => mem_range_self _) hinj hcount)

end TakhtajanTeo
