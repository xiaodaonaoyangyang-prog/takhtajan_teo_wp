import TakhtajanTeo.Ch2.S3DBase
import TakhtajanTeo.Ch2.S35WNorm
import TakhtajanTeo.Ch1.S5ExteriorChartRegularity

/-! # Density route: (D3) the `β`-term (Program G) -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Inversion of the circle: `∮_{|z| = R} F(z) z⁻² dz = ∮_{|t| = 1/R} F(1/t) dt`. -/
theorem s3e_cov (F : ℂ → ℂ) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(0, R), F z / z ^ 2) = ∮ t in C(0, R⁻¹), F t⁻¹ := by
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => circleMap 0 R⁻¹ θ * I * F (circleMap 0 R⁻¹ θ)⁻¹) (2 * π) (a := 0) (b := 2 * π)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hw : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR.ne'
  have e : circleMap 0 R⁻¹ (2 * π - θ) = (circleMap 0 R θ)⁻¹ := by
    simp only [circleMap, zero_add]
    rw [mul_inv, ← Complex.exp_neg, Complex.ofReal_inv]
    congr 1
    rw [show ((2 * π - θ : ℝ) : ℂ) * I = -((θ : ℂ) * I) + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  rw [e, inv_inv]
  field_simp

/-- The exterior chart at `∞`: `g(1/t) = φ(t)/t` with `φ` holomorphic and zero-free on `𝔻`, `φ(0) = g'(∞)`,
`φ'(0) = b₀ = lim (g(z) - g'(∞) z)`, and `g'(z) = φ(1/z) - φ'(1/z)/z` on `𝔻*`. -/
theorem s3e_chart {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc ∧ (∀ t ∈ unitDisc, φ t ≠ 0) ∧
      φ 0 = derivAtInfty (gsans μ) ∧
      (∀ t ∈ unitDisc, t ≠ 0 → gsans μ t⁻¹ = φ t / t) ∧
      limUnder (cocompact ℂ) (fun z => gsans μ z - derivAtInfty (gsans μ) * z) = deriv φ 0 ∧
      ∀ z : ℂ, 1 < ‖z‖ → deriv (gsans μ) z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set G := s5cf_gchart μ with hGdef
  have hGd : DifferentiableOn ℂ G unitDisc := fun t ht =>
    (s5cf_gchart_analytic hμ ht).differentiableAt.differentiableWithinAt
  have hds : DifferentiableOn ℂ (dslope G 0) unitDisc :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h0)).mpr hGd
  have hG0 : G 0 = 0 := by
    show (if (0 : ℂ) = 0 then 0 else (gMu μ (0 : ℂ)⁻¹)⁻¹) = 0
    simp
  have hGt : ∀ t : ℂ, t ≠ 0 → G t = (gMu μ t⁻¹)⁻¹ := fun t ht => by
    show (if t = 0 then 0 else (gMu μ t⁻¹)⁻¹) = _
    rw [if_neg ht]
  have hne : ∀ t ∈ unitDisc, dslope G 0 t ≠ 0 := by
    intro t ht
    by_cases h : t = 0
    · rw [h, dslope_same]
      exact s5cf_gchart_deriv_ne_zero hμ h0
    · rw [dslope_of_ne _ h, slope_def_field, hG0, sub_zero, sub_zero]
      refine div_ne_zero (fun hG => h ?_) h
      exact s5cf_gchart_inj hμ ht h0 (hG.trans hG0.symm)
  set φ : ℂ → ℂ := fun t => (dslope G 0 t)⁻¹ with hφdef
  have hφd : DifferentiableOn ℂ φ unitDisc := hds.inv hne
  have hφ0 : φ 0 = derivAtInfty (gsans μ) := by
    show (dslope G 0 0)⁻¹ = _
    rw [dslope_same, s35wn_derivAtInfty hμ]
    congr 1
    have hev : G =ᶠ[𝓝 0] fun w => s5cf_exterior_reciprocal (μ, star μ) w := by
      filter_upwards [isOpen_ball.mem_nhds h0] with s hs
      exact s5cf_gchart_eq hμ hs
    exact hev.deriv_eq
  have hch : ∀ t ∈ unitDisc, t ≠ 0 → gsans μ t⁻¹ = φ t / t := by
    intro t _ ht0
    show gsans μ t⁻¹ = (dslope G 0 t)⁻¹ / t
    rw [dslope_of_ne _ ht0, slope_def_field, hG0, sub_zero, sub_zero, hGt t ht0, s35wn_gsans_eq hμ,
      inv_div, div_inv_eq_mul, mul_div_cancel_left₀ _ ht0]
  have hext : ∀ z : ℂ, 1 < ‖z‖ → z⁻¹ ∈ unitDisc ∧ z⁻¹ ≠ 0 := fun z hz => by
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
    refine ⟨mem_ball_zero_iff.mpr ?_, inv_ne_zero hz0⟩
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have hgz : ∀ z : ℂ, 1 < ‖z‖ → gsans μ z = φ z⁻¹ * z := fun z hz => by
    obtain ⟨h1, h2⟩ := hext z hz
    have h := hch z⁻¹ h1 h2
    rw [inv_inv] at h
    rw [h, div_inv_eq_mul]
  refine ⟨φ, hφd, fun t ht => inv_ne_zero (hne t ht), hφ0, hch, ?_, ?_⟩
  · have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded
      · filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
        exact inv_ne_zero (by simpa using hz)
    have hs := ((hφd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.tendsto_slope).comp ht
    apply Tendsto.limUnder_eq
    apply hs.congr'
    filter_upwards [s5t53_ev_exterior] with z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
    simp only [Function.comp, slope_def_field, sub_zero]
    rw [hgz z hz1, ← hφ0]
    field_simp
  · intro z hz
    obtain ⟨h1, h2⟩ := hext z hz
    have hz0 : z ≠ 0 := fun h => h2 (by rw [h, inv_zero])
    have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    have hev : gsans μ =ᶠ[𝓝 z] fun w => φ w⁻¹ * w := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact hgz w hw
    have hd : HasDerivAt (fun w => φ w⁻¹ * w) (deriv φ z⁻¹ * (-(z ^ 2)⁻¹) * z + φ z⁻¹ * 1) z :=
      (((hφd.differentiableAt (isOpen_ball.mem_nhds h1)).hasDerivAt.comp z (hasDerivAt_inv hz0))).mul
        (hasDerivAt_id z)
    rw [hev.deriv_eq, hd.deriv]
    field_simp
    ring

/-- `Coef_R(g) = g'(∞)`: `∮_{|z| = R} g(z)/z² dz = 2πi g'(∞)` for `R > 1`. -/
theorem s3e_coef_g {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {R : ℝ} (hR : 1 < R) :
    (∮ z in C(0, R), gsans μ z / z ^ 2) = 2 * π * I * derivAtInfty (gsans μ) := by
  obtain ⟨φ, hφd, -, hφ0, hch, -, -⟩ := s3e_chart hμ
  have hp : 0 < R⁻¹ := inv_pos.mpr (by linarith)
  have hr : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hsub : closedBall (0 : ℂ) R⁻¹ ⊆ unitDisc := closedBall_subset_ball hr
  rw [s3e_cov _ (by linarith)]
  rw [circleIntegral.integral_congr hp.le (g := fun t => (t - 0)⁻¹ • φ t) fun t ht => ?_]
  · have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty (w := (0 : ℂ)) (mem_ball_self hp) (hφd.continuousOn.mono hsub)
      fun x hx => hφd.differentiableAt (isOpen_ball.mem_nhds (ball_subset_closedBall.trans hsub hx.1))
    rw [← hφ0, ← h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  · have ht1 : ‖t‖ = R⁻¹ := mem_sphere_zero_iff_norm.mp ht
    have ht0 : t ≠ 0 := fun h => by rw [h, norm_zero] at ht1; linarith
    show gsans μ t⁻¹ = (t - 0)⁻¹ • φ t
    rw [hch t (mem_ball_zero_iff.mpr (by rw [ht1]; exact hr)) ht0, sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- `Coef_R(g²) = 2 g'(∞) b₀`, `b₀ = lim (g(z) - g'(∞) z)`. -/
theorem s3e_coef_g2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {R : ℝ} (hR : 1 < R) :
    (∮ z in C(0, R), gsans μ z ^ 2 / z ^ 2) = 2 * π * I * (2 * derivAtInfty (gsans μ) *
      limUnder (cocompact ℂ) (fun z => gsans μ z - derivAtInfty (gsans μ) * z)) := by
  obtain ⟨φ, hφd, -, hφ0, hch, hb0, -⟩ := s3e_chart hμ
  have hp : 0 < R⁻¹ := inv_pos.mpr (by linarith)
  have hr : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hsub : closedBall (0 : ℂ) R⁻¹ ⊆ unitDisc := closedBall_subset_ball hr
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  rw [s3e_cov (fun z => gsans μ z ^ 2) (by linarith)]
  rw [circleIntegral.integral_congr hp.le (g := fun t => ((t - 0) ^ 2)⁻¹ • (φ t ^ 2)) fun t ht => ?_]
  · have h := two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable (f := fun t => φ t ^ 2)
      isOpen_ball hsub (hφd.pow 2) (mem_ball_self hp)
    have hd : deriv (fun t => φ t ^ 2) 0 = 2 * φ 0 * deriv φ 0 := by
      have hh := (hφd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.pow 2
      rw [show (fun t => φ t ^ 2) = φ ^ 2 from rfl, hh.deriv]
      ring
    rw [hb0, ← hφ0, ← hd, ← h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  · have ht1 : ‖t‖ = R⁻¹ := mem_sphere_zero_iff_norm.mp ht
    have ht0 : t ≠ 0 := fun h => by rw [h, norm_zero] at ht1; linarith
    show gsans μ t⁻¹ ^ 2 = ((t - 0) ^ 2)⁻¹ • (φ t ^ 2)
    rw [hch t (mem_ball_zero_iff.mpr (by rw [ht1]; exact hr)) ht0, sub_zero, smul_eq_mul, div_pow,
      div_eq_inv_mul]

/-- `∂ log|b| = ½ (∂b/b + conj(∂̄b/b))`: the real derivative of `t ↦ log‖b t‖` at `0` from that of `b`. -/
theorem s3e_logn {b : ℂ → ℂ} {X Y : ℂ}
    (hb : HasFDerivAt b (X • (1 : ℂ →L[ℝ] ℂ) + Y • (conjCLE : ℂ →L[ℝ] ℂ)) 0) (h0 : b 0 ≠ 0) :
    HasFDerivAt (fun t => ((Real.log ‖b t‖ : ℝ) : ℂ))
      (((1 / 2 : ℂ) * (X / b 0 + conj (Y / b 0))) • (1 : ℂ →L[ℝ] ℂ) +
        ((1 / 2 : ℂ) * (Y / b 0 + conj (X / b 0))) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have hq := hb.const_smul (b 0)⁻¹
  have hs : (b 0)⁻¹ • b 0 ∈ slitPlane := by
    rw [smul_eq_mul, inv_mul_cancel₀ h0]
    exact one_mem_slitPlane
  have hcomp := (hasStrictFDerivAt_log_real hs).hasFDerivAt.comp (0 : ℂ) hq
  have hre := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt
    (x := Complex.log ((b 0)⁻¹ • b 0))).comp (0 : ℂ) hcomp
  have hfin := hre.add_const ((Real.log ‖b 0‖ : ℝ) : ℂ)
  refine (hfin.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards [hb.continuousAt.eventually_ne h0] with t ht
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
      Complex.ofRealCLM_apply, Complex.log_re, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    rw [Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 h0)) (norm_ne_zero_iff.2 ht), Real.log_inv]
    push_cast
    ring
  · refine ContinuousLinearMap.ext fun t => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, Complex.reCLM_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    rw [Complex.re_eq_add_conj]
    simp only [map_add, map_mul, map_div₀, map_inv₀, conj_conj]
    field_simp
    ring

/-- A uniform first-order expansion of `G t` on the circle `|z| = R` passes to `∮ G t z / z²`. -/
theorem s3e_coef_exp {G : ℂ → ℂ → ℂ} {X Y : ℂ → ℂ} {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hG : ∀ t : ℂ, ‖t‖ < r → ContinuousOn (G t) (sphere 0 R)) (hX : ContinuousOn X (sphere 0 R))
    (hY : ContinuousOn Y (sphere 0 R))
    (hexp : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ sphere (0 : ℂ) R,
      ‖G t z - G 0 z - (t * X z + conj t * Y z)‖ ≤ ε * ‖t‖) :
    ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ →
      ‖(∮ z in C(0, R), G t z / z ^ 2) - (∮ z in C(0, R), G 0 z / z ^ 2) -
        (t * (∮ z in C(0, R), X z / z ^ 2) + conj t * ∮ z in C(0, R), Y z / z ^ 2)‖ ≤ ε * ‖t‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hexp (ε * R / (2 * π)) (by positivity)
  refine ⟨min δ r, lt_min hδ hr, fun t ht => ?_⟩
  have htδ : ‖t‖ < δ := ht.trans_le (min_le_left _ _)
  have htr : ‖t‖ < r := ht.trans_le (min_le_right _ _)
  have h0r : (0 : ℝ) < r := hr
  have hne : ∀ z ∈ sphere (0 : ℂ) R, z ^ 2 ≠ 0 := fun z hz => by
    refine pow_ne_zero 2 fun h => ?_
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
    linarith
  have cG : ∀ F : ℂ → ℂ, ContinuousOn F (sphere 0 R) → ContinuousOn (fun z => F z / z ^ 2) (sphere 0 R) :=
    fun F hF => hF.div (continuousOn_id.pow 2) hne
  have e : (∮ z in C(0, R), (G t z - G 0 z - (t * X z + conj t * Y z)) / z ^ 2) =
      (∮ z in C(0, R), G t z / z ^ 2) - (∮ z in C(0, R), G 0 z / z ^ 2) -
        (t * (∮ z in C(0, R), X z / z ^ 2) + conj t * ∮ z in C(0, R), Y z / z ^ 2) := by
    rw [circleIntegral.integral_congr hR.le (g := fun z => G t z / z ^ 2 - G 0 z / z ^ 2 -
      (t * (X z / z ^ 2) + conj t * (Y z / z ^ 2))) fun z _ => by ring]
    have hG0 := hG 0 (by rw [norm_zero]; exact h0r)
    have i1 : CircleIntegrable (fun z => G t z / z ^ 2) 0 R := (cG _ (hG t htr)).circleIntegrable hR.le
    have i2 : CircleIntegrable (fun z => G 0 z / z ^ 2) 0 R := (cG _ hG0).circleIntegrable hR.le
    have i3 : CircleIntegrable (fun z => t * (X z / z ^ 2)) 0 R :=
      (continuousOn_const.mul (cG X hX)).circleIntegrable hR.le
    have i4 : CircleIntegrable (fun z => conj t * (Y z / z ^ 2)) 0 R :=
      (continuousOn_const.mul (cG Y hY)).circleIntegrable hR.le
    have i12 : CircleIntegrable (fun z => G t z / z ^ 2 - G 0 z / z ^ 2) 0 R :=
      ((cG _ (hG t htr)).sub (cG _ hG0)).circleIntegrable hR.le
    have i34 : CircleIntegrable (fun z => t * (X z / z ^ 2) + conj t * (Y z / z ^ 2)) 0 R :=
      ((continuousOn_const.mul (cG X hX)).add (continuousOn_const.mul (cG Y hY))).circleIntegrable hR.le
    rw [circleIntegral.integral_sub i12 i34, circleIntegral.integral_sub i1 i2, circleIntegral.integral_add i3 i4,
      circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]
  rw [← e]
  calc ‖∮ z in C(0, R), (G t z - G 0 z - (t * X z + conj t * Y z)) / z ^ 2‖
      ≤ 2 * π * R * (ε * R / (2 * π) * ‖t‖ / R ^ 2) :=
        circleIntegral.norm_integral_le_of_norm_le_const hR.le fun z hz => by
          have hzR : ‖z‖ = R := mem_sphere_zero_iff_norm.1 hz
          rw [norm_div, norm_pow, hzR]
          exact div_le_div_of_nonneg_right (hb t htδ z hz) (by positivity)
    _ = ε * ‖t‖ := by
        field_simp

/-- `t⁻¹ ∈ 𝔻*` for `0 < ‖t‖ < 1`. -/
theorem s3e_inv_mem {t : ℂ} (h0 : t ≠ 0) (h1 : ‖t‖ < 1) : t⁻¹ ∈ unitDiscExterior := by
  show 1 < ‖t⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 h1

/-- The coefficient `∮_{|z| = R} h/z²` of a function holomorphic on `𝔻*` does not depend on `R > 1`. -/
theorem s3e_coef_indep {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDiscExterior) {R₁ R₂ : ℝ} (h1 : 1 < R₁)
    (h2 : 1 < R₂) : (∮ z in C(0, R₁), h z / z ^ 2) = ∮ z in C(0, R₂), h z / z ^ 2 := by
  wlog hle : R₁ ≤ R₂ generalizing R₁ R₂ with H
  · exact (H h2 h1 (le_of_not_ge hle)).symm
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  rw [s3e_cov h (by linarith), s3e_cov h (by linarith)]
  have hp2 : 0 < R₂⁻¹ := inv_pos.2 (by linarith)
  have hmem : ∀ t : ℂ, R₂⁻¹ ≤ ‖t‖ → ‖t‖ ≤ R₁⁻¹ → t ≠ 0 ∧ t⁻¹ ∈ unitDiscExterior := fun t ht1 ht2 => by
    have ht0 : t ≠ 0 := fun h => by rw [h, norm_zero] at ht1; linarith
    exact ⟨ht0, s3e_inv_mem ht0 (ht2.trans_lt (inv_lt_one_of_one_lt₀ h1))⟩
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (s := ∅) hp2
    (inv_anti₀ (by linarith) hle) countable_empty ?_ ?_
  · intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨ht0, hti⟩ := hmem t (not_lt.1 fun h => ht2 (mem_ball_zero_iff.2 h)) (mem_closedBall_zero_iff.1 ht1)
    exact ((hh.continuousOn.continuousAt (hE.mem_nhds hti)).comp (continuousAt_inv₀ ht0)).continuousWithinAt
  · intro t ht
    obtain ⟨⟨ht1, ht2⟩, -⟩ := ht
    obtain ⟨ht0, hti⟩ := hmem t (le_of_lt (not_le.1 fun h => ht2 (mem_closedBall_zero_iff.2 h)))
      (le_of_lt (mem_ball_zero_iff.1 ht1))
    exact (hh.differentiableAt (hE.mem_nhds hti)).comp t (differentiableAt_inv ht0)

/-- `Coef_R` through the chart: if `h(1/t) = H(t)/t²` on `|t| = 1/R` with `H` holomorphic on `|t| < ρ`, `ρ > 1/R`,
then `∮_{|z| = R} h/z² = 2πi H'(0)`. -/
theorem s3e_coef_chart {h H : ℂ → ℂ} {R ρ : ℝ} (hR : 0 < R) (hρ : R⁻¹ < ρ)
    (hH : DifferentiableOn ℂ H (ball 0 ρ)) (heq : ∀ t : ℂ, ‖t‖ = R⁻¹ → h t⁻¹ = H t / t ^ 2) :
    (∮ z in C(0, R), h z / z ^ 2) = 2 * π * I * deriv H 0 := by
  have hp : 0 < R⁻¹ := inv_pos.mpr hR
  rw [s3e_cov h hR]
  rw [circleIntegral.integral_congr hp.le (g := fun t => ((t - 0) ^ 2)⁻¹ • H t) fun t ht => ?_]
  · have h := two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable isOpen_ball
      (closedBall_subset_ball hρ) hH (mem_ball_self hp)
    rw [← h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  · show h t⁻¹ = ((t - 0) ^ 2)⁻¹ • H t
    rw [heq t (mem_sphere_zero_iff_norm.mp ht), sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- The chart form of the three-point kernel: `H_N(t) = ψ(t) P(t)/(Dn(u)(ut - 1))`, `ψ = φ - t φ'`,
`P(t) = (1 + t)(1 + it)(1 - t)`, is holomorphic on `|t| < ρ` with `H_N'(0) = -φ(0)(u + i)/Dn(u)`. -/
theorem s3e_HN {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) {u : ℂ} {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hu : ∀ t ∈ ball (0 : ℂ) ρ, u * t - 1 ≠ 0) (hDn : (u + 1) * (u + I) * (u - 1) ≠ 0) :
    DifferentiableOn ℂ (fun t => (φ t - t * deriv φ t) * ((1 + t) * (1 + I * t) * (1 - t)) /
      ((u + 1) * (u + I) * (u - 1) * (u * t - 1))) (ball 0 ρ) ∧
    HasDerivAt (fun t => (φ t - t * deriv φ t) * ((1 + t) * (1 + I * t) * (1 - t)) /
      ((u + 1) * (u + I) * (u - 1) * (u * t - 1))) (-(φ 0 * (u + I) / ((u + 1) * (u + I) * (u - 1)))) 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hsub : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_ball hρ1
  have hφ' : DifferentiableOn ℂ (deriv φ) unitDisc := hφd.deriv isOpen_ball
  constructor
  · exact (((hφd.mono hsub).sub (differentiableOn_id.mul (hφ'.mono hsub))).mul
      ((((differentiableOn_const 1).add differentiableOn_id).mul
        ((differentiableOn_const 1).add ((differentiableOn_const I).mul differentiableOn_id))).mul
          ((differentiableOn_const 1).sub differentiableOn_id))).div
      ((differentiableOn_const _).mul (((differentiableOn_const u).mul differentiableOn_id).sub
        (differentiableOn_const 1))) fun t ht => mul_ne_zero hDn (hu t ht)
  · have hφa : HasDerivAt φ (deriv φ 0) 0 := (hφd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hφ'a : HasDerivAt (deriv φ) (deriv (deriv φ) 0) 0 :=
      (hφ'.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hψ := hφa.sub ((hasDerivAt_id' (0 : ℂ)).mul hφ'a)
    have hP := (((hasDerivAt_id' (0 : ℂ)).const_add 1).mul (((hasDerivAt_id' (0 : ℂ)).const_mul I).const_add 1)).mul
      ((hasDerivAt_id' (0 : ℂ)).const_sub 1)
    have hD := (((hasDerivAt_id' (0 : ℂ)).const_mul u).sub_const 1).const_mul ((u + 1) * (u + I) * (u - 1))
    have hD0 : (u + 1) * (u + I) * (u - 1) * (u * 0 - 1) ≠ 0 := by
      rw [mul_zero, zero_sub, mul_neg_one]
      exact neg_ne_zero.2 hDn
    have h := (hψ.mul hP).div hD hD0
    convert h using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

/-- The chart form of the Cauchy part: `H_M(t) = t φ(t)²/(tγ - φ(t))` is holomorphic on `|t| < ρ` with
`H_M'(0) = -φ(0)`. -/
theorem s3e_HM {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφ0 : φ 0 ≠ 0) {γ : ℂ} {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hne : ∀ t ∈ ball (0 : ℂ) ρ, t * γ - φ t ≠ 0) :
    DifferentiableOn ℂ (fun t => t * (φ t ^ 2 / (t * γ - φ t))) (ball 0 ρ) ∧
    HasDerivAt (fun t => t * (φ t ^ 2 / (t * γ - φ t))) (-φ 0) 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hsub : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_ball hρ1
  constructor
  · exact differentiableOn_id.mul (((hφd.mono hsub).pow 2).div
      ((differentiableOn_id.mul (differentiableOn_const γ)).sub (hφd.mono hsub)) hne)
  · have hφa : HasDerivAt φ (deriv φ 0) 0 := (hφd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hd0 : 0 * γ - φ 0 ≠ 0 := by
      rw [zero_mul, zero_sub]
      exact neg_ne_zero.2 hφ0
    have h := (hasDerivAt_id' (0 : ℂ)).mul ((hφa.pow 2).div ((hasDerivAt_mul_const γ).sub hφa) hd0)
    convert h using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

/-- `Coef_R` of the explicit `t`-kernel `g'(z) K̃(u, z)` for `1 < ‖u‖ < R` (both poles of the chart form lie outside
`|t| ≤ 1/R`): `b (u + i)/Dn(u) - b g'(u)²/g(u)²`, `b = φ(0)`. -/
theorem s3e_coef_K {g φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφ0 : ∀ t ∈ unitDisc, φ t ≠ 0)
    (hch : ∀ t ∈ unitDisc, t ≠ 0 → g t⁻¹ = φ t / t)
    (hder : ∀ z : ℂ, 1 < ‖z‖ → deriv g z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹) (hgi : InjOn g unitDiscExterior)
    {u : ℂ} (hu : 1 < ‖u‖) (hgu : g u ≠ 0) (hDn : (u + 1) * (u + I) * (u - 1) ≠ 0) {R : ℝ} (huR : ‖u‖ < R) :
    (∮ z in C(0, R), (deriv g u ^ 2 * g z ^ 2 / (g u ^ 2 * (g u - g z)) -
      deriv g z * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)))) / z ^ 2) =
      2 * π * I * (φ 0 * ((u + I) / ((u + 1) * (u + I) * (u - 1)) - deriv g u ^ 2 / g u ^ 2)) := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hu0 : 0 < ‖u‖ := by linarith
  have hR : 0 < R := by linarith
  have hρ1 : ‖u‖⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hu).le
  have hρ : R⁻¹ < ‖u‖⁻¹ := inv_strictAnti₀ hu0 huR
  have hdisc : ∀ t : ℂ, ‖t‖ < ‖u‖⁻¹ → t ∈ unitDisc := fun t ht => mem_ball_zero_iff.2 (ht.trans_le hρ1)
  have hne : ∀ t ∈ ball (0 : ℂ) ‖u‖⁻¹, t * g u - φ t ≠ 0 := by
    intro t ht h
    have ht' := mem_ball_zero_iff.1 ht
    by_cases ht0 : t = 0
    · rw [ht0, zero_mul, zero_sub, neg_eq_zero] at h
      exact hφ0 0 h0 h
    · have hti : t⁻¹ ∈ unitDiscExterior := s3e_inv_mem ht0 (ht'.trans_le hρ1)
      have hg : g t⁻¹ = g u := by
        rw [hch t (hdisc t ht') ht0, ← sub_eq_zero.1 h]
        field_simp
      have := congrArg norm (hgi hti hu hg)
      rw [norm_inv] at this
      rw [← this, inv_inv] at ht'
      exact lt_irrefl _ ht'
  have hut : ∀ t ∈ ball (0 : ℂ) ‖u‖⁻¹, u * t - 1 ≠ 0 := by
    intro t ht h
    have ht' := mem_ball_zero_iff.1 ht
    have h1 : ‖u * t‖ = 1 := by rw [sub_eq_zero.1 h, norm_one]
    rw [norm_mul] at h1
    have : ‖u‖ * ‖t‖ < ‖u‖ * ‖u‖⁻¹ := mul_lt_mul_of_pos_left ht' hu0
    rw [mul_inv_cancel₀ hu0.ne'] at this
    linarith
  obtain ⟨hMd, hMa⟩ := s3e_HM hφd (hφ0 0 h0) hρ1 hne
  obtain ⟨hNd, hNa⟩ := s3e_HN hφd hρ1 hut hDn
  rw [s3e_coef_chart hR hρ ((hMd.const_mul (deriv g u ^ 2 / g u ^ 2)).sub hNd) fun t ht => ?_,
    ((hMa.const_mul (deriv g u ^ 2 / g u ^ 2)).sub hNa).deriv]
  · ring
  · have ht0 : t ≠ 0 := fun h => by rw [h, norm_zero] at ht; exact (inv_pos.2 hR).ne' ht.symm
    have htu : ‖t‖ < ‖u‖⁻¹ := by rw [ht]; exact hρ
    have hti : 1 < ‖t⁻¹‖ := s3e_inv_mem ht0 (htu.trans_le hρ1)
    have h1 := hne t (mem_ball_zero_iff.2 htu)
    have h2 := hut t (mem_ball_zero_iff.2 htu)
    have h3 : g u - φ t / t ≠ 0 := fun h => h1 (by field_simp at h ⊢; linear_combination h)
    have h4 : u - t⁻¹ ≠ 0 := fun h => h2 (by field_simp at h ⊢; linear_combination h)
    show (deriv g u ^ 2 * g t⁻¹ ^ 2 / (g u ^ 2 * (g u - g t⁻¹)) - deriv g t⁻¹ * ((t⁻¹ + 1) * (t⁻¹ + I) *
      (t⁻¹ - 1) / ((u + 1) * (u + I) * (u - 1) * (u - t⁻¹)))) = (deriv g u ^ 2 / g u ^ 2 *
        (t * (φ t ^ 2 / (t * g u - φ t))) - (φ t - t * deriv φ t) * ((1 + t) * (1 + I * t) * (1 - t)) /
          ((u + 1) * (u + I) * (u - 1) * (u * t - 1))) / t ^ 2
    rw [hder t⁻¹ hti, inv_inv, hch t (hdisc t htu) ht0]
    have e1 : g u - φ t / t = (t * g u - φ t) / t := by
      rw [eq_div_iff ht0, sub_mul, div_mul_cancel₀ _ ht0]
      ring
    have e2 : u - t⁻¹ = (u * t - 1) / t := by
      rw [eq_div_iff ht0, sub_mul, inv_mul_cancel₀ ht0]
    rw [e1, e2]
    generalize t * g u - φ t = w at h1 ⊢
    generalize u * t - 1 = q at h2 ⊢
    generalize (u + 1) * (u + I) * (u - 1) = D at hDn ⊢
    field_simp

/-- `Coef_R` of the three-point kernel `g'(z) Dn(z)/(Dn(ζ)(ζ - z))` for `‖ζ‖ < 1 < R`: `-b (ζ + i)/Dn(ζ)`. -/
theorem s3e_coef_N {g φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc)
    (hder : ∀ z : ℂ, 1 < ‖z‖ → deriv g z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹)
    {ζ : ℂ} (hζ : ‖ζ‖ < 1) (hDn : (ζ + 1) * (ζ + I) * (ζ - 1) ≠ 0) {R : ℝ} (hR : 1 < R) :
    (∮ z in C(0, R), deriv g z * ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2) =
      2 * π * I * (-(φ 0 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
  have hR0 : 0 < R := by linarith
  have hρ : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hut : ∀ t ∈ ball (0 : ℂ) 1, ζ * t - 1 ≠ 0 := by
    intro t ht h
    have ht' := mem_ball_zero_iff.1 ht
    have h1 : ‖ζ * t‖ = 1 := by rw [sub_eq_zero.1 h, norm_one]
    rw [norm_mul] at h1
    have : ‖ζ‖ * ‖t‖ < 1 := by nlinarith [norm_nonneg ζ, norm_nonneg t]
    linarith
  obtain ⟨hNd, hNa⟩ := s3e_HN hφd le_rfl hut hDn
  rw [s3e_coef_chart hR0 hρ hNd fun t ht => ?_, hNa.deriv]
  have ht0 : t ≠ 0 := fun h => by rw [h, norm_zero] at ht; exact (inv_pos.2 hR0).ne' ht.symm
  have htu : ‖t‖ < 1 := by rw [ht]; exact hρ
  have hti : 1 < ‖t⁻¹‖ := s3e_inv_mem ht0 htu
  have h2 := hut t (mem_ball_zero_iff.2 htu)
  have h4 : ζ - t⁻¹ ≠ 0 := fun h => h2 (by field_simp at h ⊢; linear_combination h)
  beta_reduce
  rw [hder t⁻¹ hti, inv_inv]
  field_simp

/-- `Coef_R` of the removable kernel `g'(z) K̃(u, z)` for every `u ∈ 𝔻*` and `R > 1` (holomorphic in `z` on `𝔻*`, so
`R` may be moved past `‖u‖`): `b (u + i)/Dn(u) - b g'(u)²/g(u)²`. -/
theorem s3e_coef_Kt {g φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφ0 : ∀ t ∈ unitDisc, φ t ≠ 0)
    (hch : ∀ t ∈ unitDisc, t ≠ 0 → g t⁻¹ = φ t / t)
    (hder : ∀ z : ℂ, 1 < ‖z‖ → deriv g z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹)
    (hgd : DifferentiableOn ℂ g unitDiscExterior) (hg'd : DifferentiableOn ℂ (deriv g) unitDiscExterior)
    (hgi : InjOn g unitDiscExterior) (hg' : ∀ u ∈ unitDiscExterior, deriv g u ≠ 0)
    (hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0) {u : ℂ} (hu : u ∈ unitDiscExterior) {R : ℝ} (hR : 1 < R) :
    (∮ z in C(0, R), deriv g z * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
      (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z / z ^ 2) =
      2 * π * I * (φ 0 * ((u + I) / ((u + 1) * (u + I) * (u - 1)) - deriv g u ^ 2 / g u ^ 2)) := by
  have hu1 : 1 < ‖u‖ := hu
  have hDn := d2e_dn_ne hu1
  rw [s3e_coef_indep (h := fun z => deriv g z * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z)
    (hg'd.mul (d2e_K_diff hgd hg'd hgi hg' hg0 hu)) hR (show 1 < ‖u‖ + 1 by linarith)]
  rw [circleIntegral.integral_congr (by positivity) (g := fun z => (deriv g u ^ 2 * g z ^ 2 / (g u ^ 2 * (g u - g z)) -
      deriv g z * ((z + 1) * (z + I) * (z - 1) / ((u + 1) * (u + I) * (u - 1) * (u - z)))) / z ^ 2) fun z hz => ?_]
  · exact s3e_coef_K hφd hφ0 hch hder hgi hu1 (hg0 u hu) hDn (by linarith)
  · have hz' : ‖z‖ = ‖u‖ + 1 := mem_sphere_zero_iff_norm.1 hz
    have hzE : z ∈ unitDiscExterior := show 1 < ‖z‖ by rw [hz']; linarith
    have hzu : z ≠ u := fun h => by rw [h] at hz'; linarith
    have hgz : g u ≠ g z := fun h => hzu (hgi hu hzE h).symm
    beta_reduce
    rw [d2e_K_eq hzu (hg0 u hu) (hg' u hu) (hg' z hzE) hgz hDn]
    have h4 := hg' z hzE
    have h5 : g u - g z ≠ 0 := sub_ne_zero.2 hgz
    have h6 : u - z ≠ 0 := sub_ne_zero.2 hzu.symm
    have h7 := hg0 u hu
    field_simp

/-- Fubini for a circle integral of a parametric integral, under an integrable majorant uniform on the circle. -/
theorem s3e_fubini {F : ℂ → ℂ → ℂ} {D : Set ℂ} {R : ℝ} (hR : 0 < R) {B : ℂ → ℝ}
    (hB : Integrable B (volume.restrict D))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => F p.2 (circleMap 0 R p.1))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict D)))
    (hbd : ∀ᵐ u ∂(volume.restrict D), ∀ z ∈ sphere (0 : ℂ) R, ‖F u z‖ ≤ B u) :
    (∮ z in C(0, R), ∫ u in D, F u z) = ∫ u in D, ∮ z in C(0, R), F u z := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hdc : Continuous (deriv (circleMap 0 R)) := by
    rw [show deriv (circleMap 0 R) = fun θ => circleMap 0 R θ * I from funext fun θ => deriv_circleMap 0 R θ]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hint : Integrable (Function.uncurry fun (θ : ℝ) (u : ℂ) => deriv (circleMap 0 R) θ • F u (circleMap 0 R θ))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict D)) := by
    have hc1 : IntegrableOn (fun _ : ℝ => R) (Ioc 0 (2 * π)) :=
      (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    refine (Integrable.mul_prod (μ := volume.restrict (Ioc 0 (2 * π))) hc1 hB).mono' ((hdc.comp continuous_fst).aestronglyMeasurable.smul hmeas) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hbd] with p hp
    show ‖deriv (circleMap 0 R) p.1 • F p.2 (circleMap 0 R p.1)‖ ≤ R * B p.2
    rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left (hp _ (circleMap_mem_sphere 0 hR.le _)) hR.le
  have hsw := integral_integral_swap hint
  simp only [circleIntegral, intervalIntegral.integral_of_le h2π]
  rw [show (∫ θ in Ioc 0 (2 * π), deriv (circleMap 0 R) θ • ∫ u in D, F u (circleMap 0 R θ)) =
      ∫ θ in Ioc 0 (2 * π), ∫ u in D, deriv (circleMap 0 R) θ • F u (circleMap 0 R θ) from
    integral_congr_ae (Filter.Eventually.of_forall fun θ => (integral_smul _ _).symm)]
  exact hsw

/-- The kernel `K̃(u, y)` has an integrable majorant in `u`, uniform for `y` on the circle `|y| = R > 1`
(off-diagonal bound `d2e_bound` on a closed annulus, maximum modulus near the diagonal). -/
theorem s3e_KB {g G : ℂ → ℂ} {ρ : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C) {R : ℝ} (hR : 1 < R) :
    ∃ B : ℂ → ℝ, Integrable B ∧ (∀ u, 0 ≤ B u) ∧ ∀ u ∈ unitDiscExterior, ∀ y ∈ sphere (0 : ℂ) R,
      ‖-dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y‖ ≤ B u := by
  obtain ⟨hgd, hg'd, hgi, hdd, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  set ε : ℝ := (R - 1) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set A : Set ℂ := closedBall 0 (R + 6 * ε) ∩ {w | R - 6 * ε ≤ ‖w‖} with hA
  have hAc : IsCompact A := (isCompact_closedBall 0 (R + 6 * ε)).inter_right (isClosed_le continuous_const continuous_norm)
  have hAE : A ⊆ unitDiscExterior := fun w hw => by
    show 1 < ‖w‖
    have := hw.2
    simp only [mem_setOf_eq] at this
    rw [hε] at this
    linarith
  have hnorm : ∀ y w : ℂ, ‖y‖ = R → ‖w - y‖ ≤ 6 * ε → w ∈ A := fun y w hy hw => by
    have h1 := norm_sub_norm_le w y
    have h2 := norm_sub_norm_le y w
    rw [norm_sub_rev] at h2
    exact ⟨mem_closedBall_zero_iff.2 (by linarith), show R - 6 * ε ≤ ‖w‖ by linarith⟩
  obtain ⟨B, hBi, hB0, hBk⟩ := d2e_bound hρ hG hGi hGd hGg hk hinf hAc hAE (by positivity : (0 : ℝ) < 2 * ε)
  have hKeq : ∀ u ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, w ≠ u → -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u w = deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * (g u - g w)) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1) * (u - w)) :=
    fun u hu w hw hwu => d2e_K_eq hwu (hg0 u hu) (hg' u hu) (hg' w hw) (fun h => hwu (hgi hu hw h).symm)
      (d2e_dn_ne hu)
  have htri : ∀ a b c : ℂ, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have := norm_add_le (a - b) (b - c)
    rwa [show a - b + (b - c) = a - c by ring] at this
  refine ⟨B, hBi, hB0, fun u hu y hy => ?_⟩
  have hyR : ‖y‖ = R := mem_sphere_zero_iff_norm.1 hy
  have hKc : closedBall y (6 * ε) ⊆ unitDiscExterior := fun w hw =>
    hAE (hnorm y w hyR (mem_closedBall_iff_norm.1 hw))
  by_cases hun : ‖u - y‖ < 4 * ε
  · have hdc : DiffContOnCl ℂ (fun y => -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u y) (ball y (6 * ε)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by positivity)]
      exact (d2e_K_diff hgd hg'd hgi hg' hg0 hu).mono hKc
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ ?_
    · intro w hw
      rw [frontier_ball _ (by positivity)] at hw
      have hw' : ‖w - y‖ = 6 * ε := mem_sphere_iff_norm.1 hw
      have hwK : w ∈ A := hnorm y w hyR hw'.le
      have hsep : 2 * ε ≤ ‖u - w‖ := by
        have := htri w u y
        rw [norm_sub_rev w u] at this
        linarith
      have hwu : w ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
      rw [hKeq u hu w (hAE hwK) hwu]
      exact hBk u hu w hwK hsep
    · rw [closure_ball _ (by positivity)]
      exact mem_closedBall_self (by positivity)
  · rw [not_lt] at hun
    have hyK : y ∈ A := hnorm y y hyR (by rw [sub_self, norm_zero]; positivity)
    have hsep : 2 * ε ≤ ‖u - y‖ := by linarith
    have hyu : y ≠ u := fun h => by rw [h, sub_self, norm_zero] at hsep; linarith
    rw [hKeq u hu y (hAE hyK) hyu]
    exact hBk u hu y hyK hsep

/-- `g = gsans μ` is holomorphic on `𝔻*` (through the exterior chart, `g(z) = z φ(1/z)`). -/
theorem s3e_gdiff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : DifferentiableOn ℂ (gsans μ) unitDiscExterior := by
  obtain ⟨φ, hφd, -, -, hch, -, -⟩ := s3e_chart hμ
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hinv : ∀ w : ℂ, 1 < ‖w‖ → w ≠ 0 ∧ w⁻¹ ∈ unitDisc := fun w hw =>
    ⟨fun h => by rw [h, norm_zero] at hw; linarith,
      mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hw)⟩
  intro z hz
  obtain ⟨hz0, hzi⟩ := hinv z hz
  have hev : gsans μ =ᶠ[𝓝 z] fun w => φ w⁻¹ * w := by
    filter_upwards [hE.mem_nhds hz] with w hw
    obtain ⟨hw0, hwi⟩ := hinv w hw
    have h := hch w⁻¹ hwi (inv_ne_zero hw0)
    rw [inv_inv] at h
    rw [h, div_inv_eq_mul]
  exact ((((hφd.differentiableAt (isOpen_ball.mem_nhds hzi)).comp z (differentiableAt_inv hz0)).mul
    differentiableAt_id).congr_of_eventuallyEq hev).differentiableWithinAt

/-- Joint measurability of the `t`-kernel `R(u) g'(z) K̃(u, z)/z²` on `(0, 2π] × 𝔻*`, `z = R e^{iθ}` (explicit and
continuous off the diagonal, which is null). -/
theorem s3e_Xmeas {g R : ℂ → ℂ} (hgd : DifferentiableOn ℂ g unitDiscExterior)
    (hg'd : DifferentiableOn ℂ (deriv g) unitDiscExterior) (hgi : InjOn g unitDiscExterior)
    (hg' : ∀ u ∈ unitDiscExterior, deriv g u ≠ 0) (hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior)) {Rr : ℝ} (hR : 1 < Rr) :
    AEStronglyMeasurable (fun p : ℝ × ℂ => R p.2 * (deriv g (circleMap 0 Rr p.1) *
      -dslope (fun w => deriv g p.2 ^ 2 * g w ^ 2 / (g p.2 ^ 2 * deriv g w * dslope g p.2 w) -
        (w + 1) * (w + I) * (w - 1) / ((p.2 + 1) * (p.2 + I) * (p.2 - 1))) p.2 (circleMap 0 Rr p.1) /
          circleMap 0 Rr p.1 ^ 2))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDiscExterior)) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hcE : ∀ θ : ℝ, circleMap 0 Rr θ ∈ unitDiscExterior := fun θ => by
    show 1 < ‖circleMap 0 Rr θ‖
    rw [norm_circleMap_zero, abs_of_pos (by linarith)]
    exact hR
  have hc0 : ∀ θ : ℝ, circleMap 0 Rr θ ≠ 0 := fun θ => circleMap_ne_center (by linarith)
  refine (hRm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul ?_
  set S : Set (ℝ × ℂ) := {p | p.2 ∈ unitDiscExterior ∧ p.2 ≠ circleMap 0 Rr p.1} with hS
  have hSm : MeasurableSet S := (measurable_snd hEm).inter
    (measurableSet_eq_fun measurable_snd ((continuous_circleMap 0 Rr).measurable.comp measurable_fst)).compl
  have hdiag : MeasurableSet {p : ℝ × ℂ | p.2 ≠ circleMap 0 Rr p.1} :=
    (measurableSet_eq_fun measurable_snd ((continuous_circleMap 0 Rr).measurable.comp measurable_fst)).compl
  have hae : ∀ᵐ p ∂((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDiscExterior)), p ∈ S := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hEm),
      (Measure.ae_prod_iff_ae_ae hdiag).2 (Filter.Eventually.of_forall fun θ => ae_restrict_of_ae
        ((measure_eq_zero_iff_ae_notMem.1 (measure_singleton (circleMap 0 Rr θ))).mono
          fun u hu => fun h => hu (Set.mem_singleton_iff.2 h)))] with p h1 h2
    exact ⟨h1, h2⟩
  have hgc := hgd.continuousOn
  have hg'c := hg'd.continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℂ => (deriv g p.2 ^ 2 * g (circleMap 0 Rr p.1) ^ 2 /
      (g p.2 ^ 2 * (g p.2 - g (circleMap 0 Rr p.1))) - deriv g (circleMap 0 Rr p.1) *
        ((circleMap 0 Rr p.1 + 1) * (circleMap 0 Rr p.1 + I) * (circleMap 0 Rr p.1 - 1) /
          ((p.2 + 1) * (p.2 + I) * (p.2 - 1) * (p.2 - circleMap 0 Rr p.1)))) / circleMap 0 Rr p.1 ^ 2) S := by
    have hcm : Continuous fun p : ℝ × ℂ => circleMap 0 Rr p.1 := (continuous_circleMap 0 Rr).comp continuous_fst
    have hu1 : ContinuousOn (fun p : ℝ × ℂ => g p.2) S := hgc.comp continuous_snd.continuousOn fun p hp => hp.1
    have hu2 : ContinuousOn (fun p : ℝ × ℂ => deriv g p.2) S := hg'c.comp continuous_snd.continuousOn fun p hp => hp.1
    have hz1 : ContinuousOn (fun p : ℝ × ℂ => g (circleMap 0 Rr p.1)) S :=
      hgc.comp hcm.continuousOn fun p _ => hcE p.1
    have hz2 : ContinuousOn (fun p : ℝ × ℂ => deriv g (circleMap 0 Rr p.1)) S :=
      hg'c.comp hcm.continuousOn fun p _ => hcE p.1
    refine ContinuousOn.div (ContinuousOn.sub ?_ (hz2.mul ?_)) (hcm.continuousOn.pow 2) fun p _ => pow_ne_zero 2 (hc0 p.1)
    · refine ((hu2.pow 2).mul (hz1.pow 2)).div ((hu1.pow 2).mul (hu1.sub hz1)) fun p hp => ?_
      exact mul_ne_zero (pow_ne_zero 2 (hg0 _ hp.1))
        (sub_ne_zero.2 fun h => hp.2 (hgi hp.1 (hcE p.1) h))
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_
      exact mul_ne_zero (d2e_dn_ne hp.1) (sub_ne_zero.2 hp.2)
  have hm := hcont.aestronglyMeasurable
    (μ := (volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDiscExterior)) hSm
  rw [Measure.restrict_eq_self_of_ae_mem hae] at hm
  refine hm.congr ?_
  filter_upwards [hae] with p hp
  have hzu : circleMap 0 Rr p.1 ≠ p.2 := fun h => hp.2 h.symm
  have hgz : g p.2 ≠ g (circleMap 0 Rr p.1) := fun h => hp.2 (hgi hp.1 (hcE p.1) h)
  rw [d2e_K_eq hzu (hg0 _ hp.1) (hg' _ hp.1) (hg' _ (hcE p.1)) hgz (d2e_dn_ne hp.1)]
  have h4 := hg' _ (hcE p.1)
  have h5 : g p.2 - g (circleMap 0 Rr p.1) ≠ 0 := sub_ne_zero.2 hgz
  have h6 : p.2 - circleMap 0 Rr p.1 ≠ 0 := sub_ne_zero.2 hp.2
  have h7 := hg0 _ hp.1
  have h8 := hc0 p.1
  have h9 := d2e_dn_ne hp.1
  field_simp

/-- **X-coefficient.** `∮_{|z| = 2} g'(z) (∫_{𝔻*} R K̃(·, z)) z⁻² dz = 2πi b ∫_{𝔻*} R ((u + i)/Dn(u) - g'(u)²/g(u)²)`
(Fubini, then `Coef` of the removable kernel). -/
theorem s3e_Xcoef {g G φ R : ℂ → ℂ} {ρ Rb : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφ0 : ∀ t ∈ unitDisc, φ t ≠ 0)
    (hch : ∀ t ∈ unitDisc, t ≠ 0 → g t⁻¹ = φ t / t)
    (hder : ∀ z : ℂ, 1 < ‖z‖ → deriv g z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹) :
    (∮ z in C(0, 2), deriv g z * (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) /
        z ^ 2) =
      2 * π * I * (φ 0 * ∫ u in unitDiscExterior, R u * ((u + I) / ((u + 1) * (u + I) * (u - 1)) -
        deriv g u ^ 2 / g u ^ 2)) := by
  obtain ⟨hgd, hg'd, hgi, -, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  obtain ⟨B, hBi, hB0, hBk⟩ := s3e_KB hρ hG hGi hGd hGg hk hinf (by norm_num : (1 : ℝ) < 2)
  have hsE : sphere (0 : ℂ) 2 ⊆ unitDiscExterior := fun z hz => show 1 < ‖z‖ by
    rw [mem_sphere_zero_iff_norm.1 hz]; norm_num
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 2).exists_bound_of_continuousOn (hg'd.continuousOn.mono hsE)
  have hpt : EqOn (fun z => deriv g z * (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) /
        z ^ 2)
      (fun z => ∫ u in unitDiscExterior, R u * (deriv g z * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z /
        z ^ 2)) (sphere 0 2) := fun z _ => by
    beta_reduce
    rw [← integral_const_mul, ← integral_div]
    congr 1
    funext u
    ring
  rw [circleIntegral.integral_congr (by norm_num) hpt]
  rw [s3e_fubini (B := fun u => Rb * M * B u / 4) (by norm_num) ((hBi.const_mul (Rb * M)).div_const 4).integrableOn
    (s3e_Xmeas hgd hg'd hgi hg' hg0 hRm (by norm_num)) ?_]
  · have hpt2 : ∀ᵐ u ∂(volume.restrict unitDiscExterior), (∮ z in C(0, 2), R u * (deriv g z *
        -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
          (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z / z ^ 2)) =
        2 * π * I * φ 0 * (R u * ((u + I) / ((u + 1) * (u + I) * (u - 1)) - deriv g u ^ 2 / g u ^ 2)) := by
      filter_upwards [ae_restrict_mem hEm] with u hu
      rw [circleIntegral.integral_const_mul, s3e_coef_Kt hφd hφ0 hch hder hgd hg'd hgi hg' hg0 hu (by norm_num)]
      ring
    rw [integral_congr_ae hpt2, integral_const_mul]
    ring
  · filter_upwards [hRb, ae_restrict_mem hEm] with u hRu hu z hz
    have hRb0 : 0 ≤ Rb := (norm_nonneg _).trans hRu
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
    rw [norm_mul, norm_div, norm_mul, norm_pow, mem_sphere_zero_iff_norm.1 hz]
    calc ‖R u‖ * (‖deriv g z‖ * ‖-dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
          (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z‖ / 2 ^ 2)
        ≤ Rb * (M * B u / 2 ^ 2) := by
          refine mul_le_mul hRu (div_le_div_of_nonneg_right ?_ (by positivity)) (by positivity) hRb0
          exact mul_le_mul (hM z hz) (hBk u hu z hz) (norm_nonneg _) hM0
      _ = Rb * M * B u / 4 := by ring

/-- **Y-coefficient.** `∮_{|z| = 2} g'(z) (∫_𝔻 S(ζ) Dn(z)/(Dn(ζ)(ζ - z))) z⁻² dz = 2πi ∫_𝔻 S(ζ) (-b (ζ + i)/Dn(ζ))`
for bounded measurable `S` (Fubini; no singularity, `|ζ| < 1 < 2 = |z|`). -/
theorem s3e_Ycoef {g G φ S : ℂ → ℂ} {ρ Sb : ℝ} (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior)
    (hSm : AEStronglyMeasurable S (volume.restrict unitDisc))
    (hSb : ∀ᵐ ζ ∂(volume.restrict unitDisc), ‖S ζ‖ ≤ Sb)
    (hφd : DifferentiableOn ℂ φ unitDisc)
    (hder : ∀ z : ℂ, 1 < ‖z‖ → deriv g z = φ z⁻¹ - deriv φ z⁻¹ * z⁻¹) :
    (∮ z in C(0, 2), deriv g z * (∫ ζ in unitDisc, S ζ * (((z + 1) * (z + I) * (z - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) / z ^ 2) =
      2 * π * I * ∫ ζ in unitDisc, S ζ * (-(φ 0 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
  obtain ⟨-, hg'd, -, -, -⟩ := d2e_basic hρ hG hGi hGd hGg
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hsE : sphere (0 : ℂ) 2 ⊆ unitDiscExterior := fun z hz => show 1 < ‖z‖ by
    rw [mem_sphere_zero_iff_norm.1 hz]; norm_num
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 2).exists_bound_of_continuousOn (hg'd.continuousOn.mono hsE)
  obtain ⟨M₂, hM₂⟩ := (isCompact_sphere (0 : ℂ) 2).exists_bound_of_continuousOn
    ((by fun_prop : Continuous fun z : ℂ => (z + 1) * (z + I) * (z - 1)).continuousOn)
  have hcE : ∀ θ : ℝ, circleMap 0 2 θ ∈ unitDiscExterior := fun θ => hsE (circleMap_mem_sphere 0 (by norm_num) θ)
  have hsep : ∀ ζ ∈ unitDisc, ∀ z ∈ sphere (0 : ℂ) 2, 1 ≤ ‖ζ - z‖ := fun ζ hζ z hz => by
    have h1 := norm_sub_norm_le z ζ
    rw [norm_sub_rev] at h1
    have := mem_ball_zero_iff.1 hζ
    rw [mem_sphere_zero_iff_norm.1 hz] at h1
    linarith
  have hpt : EqOn (fun z => deriv g z * (∫ ζ in unitDisc, S ζ * (((z + 1) * (z + I) * (z - 1)) /
      (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) / z ^ 2)
      (fun z => ∫ ζ in unitDisc, S ζ * (deriv g z * ((z + 1) * (z + I) * (z - 1) /
        ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2)) (sphere 0 2) := fun z _ => by
    beta_reduce
    rw [← integral_const_mul, ← integral_div]
    congr 1
    funext ζ
    ring
  rw [circleIntegral.integral_congr (by norm_num) hpt]
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => S p.2 * (deriv g (circleMap 0 2 p.1) *
      ((circleMap 0 2 p.1 + 1) * (circleMap 0 2 p.1 + I) * (circleMap 0 2 p.1 - 1) /
        ((p.2 + 1) * (p.2 + I) * (p.2 - 1) * (p.2 - circleMap 0 2 p.1))) / circleMap 0 2 p.1 ^ 2))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDisc)) := by
    refine (hSm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul ?_
    have hT : MeasurableSet {p : ℝ × ℂ | p.2 ∈ unitDisc} := measurable_snd hDm
    have hae : ∀ᵐ p ∂((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDisc)),
        p ∈ {p : ℝ × ℂ | p.2 ∈ unitDisc} := Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hDm)
    have hcm : Continuous fun p : ℝ × ℂ => circleMap 0 2 p.1 := (continuous_circleMap 0 2).comp continuous_fst
    have hcont : ContinuousOn (fun p : ℝ × ℂ => deriv g (circleMap 0 2 p.1) *
        ((circleMap 0 2 p.1 + 1) * (circleMap 0 2 p.1 + I) * (circleMap 0 2 p.1 - 1) /
          ((p.2 + 1) * (p.2 + I) * (p.2 - 1) * (p.2 - circleMap 0 2 p.1))) / circleMap 0 2 p.1 ^ 2)
        {p : ℝ × ℂ | p.2 ∈ unitDisc} := by
      refine ContinuousOn.div ((hg'd.continuousOn.comp hcm.continuousOn fun p _ => hcE p.1).mul
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp => ?_)) (hcm.continuousOn.pow 2)
          fun p _ => pow_ne_zero 2 (circleMap_ne_center (by norm_num))
      refine mul_ne_zero (d2e_dn_ne1 (mem_ball_zero_iff.1 hp)) fun h => ?_
      have := hsep p.2 hp _ (circleMap_mem_sphere 0 (by norm_num) p.1)
      rw [h, norm_zero] at this
      norm_num at this
    have hm := hcont.aestronglyMeasurable
      (μ := (volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict unitDisc)) hT
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm
  have hBi : Integrable (fun ζ : ℂ => Sb * M * M₂ / 4 * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹)
      (volume.restrict unitDisc) := (d2e_dn_int.const_mul (Sb * M * M₂ / 4)).integrableOn
  rw [s3e_fubini (by norm_num) hBi hmeas ?_]
  · have hpt2 : ∀ᵐ ζ ∂(volume.restrict unitDisc), (∮ z in C(0, 2), S ζ * (deriv g z *
        ((z + 1) * (z + I) * (z - 1) / ((ζ + 1) * (ζ + I) * (ζ - 1) * (ζ - z))) / z ^ 2)) =
        2 * π * I * (S ζ * (-(φ 0 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))))) := by
      filter_upwards [ae_restrict_mem hDm] with ζ hζ
      have hζ1 := mem_ball_zero_iff.1 hζ
      rw [circleIntegral.integral_const_mul, s3e_coef_N hφd hder hζ1 (d2e_dn_ne1 hζ1) (by norm_num)]
      ring
    rw [integral_congr_ae hpt2, integral_const_mul]
  · filter_upwards [hSb, ae_restrict_mem hDm] with ζ hSζ hζ z hz
    have hSb0 : 0 ≤ Sb := (norm_nonneg _).trans hSζ
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
    have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ z hz)
    have hD : 0 < ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ := norm_pos_iff.2 (d2e_dn_ne1 (mem_ball_zero_iff.1 hζ))
    have hs := hsep ζ hζ z hz
    rw [norm_mul, norm_div, norm_mul, norm_div, norm_mul _ (ζ - z), norm_pow, mem_sphere_zero_iff_norm.1 hz]
    calc ‖S ζ‖ * (‖deriv g z‖ * (‖(z + 1) * (z + I) * (z - 1)‖ /
          (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * ‖ζ - z‖)) / 2 ^ 2)
        ≤ Sb * (M * (M₂ / (‖(ζ + 1) * (ζ + I) * (ζ - 1)‖ * 1)) / 2 ^ 2) := by
          refine mul_le_mul hSζ (div_le_div_of_nonneg_right ?_ (by positivity)) (by positivity) hSb0
          refine mul_le_mul (hM z hz) ?_ (by positivity) hM0
          exact div_le_div₀ hM₂0 (hM₂ z hz) (by positivity) (mul_le_mul_of_nonneg_left hs hD.le)
      _ = Sb * M * M₂ / 4 * ‖(ζ + 1) * (ζ + I) * (ζ - 1)‖⁻¹ := by
          field_simp
          norm_num

/-- `b(t) = Coef₂(G t)` with a uniform first-order expansion of `G t` on `|z| = 2` is real differentiable at `0`,
with `∂b = Coef₂(X)`, `∂̄b = Coef₂(Y)`. -/
theorem s3e_bderiv {G : ℂ → ℂ → ℂ} {X Y b : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hb : ∀ t : ℂ, ‖t‖ < r → (∮ z in C(0, 2), G t z / z ^ 2) = 2 * π * I * b t)
    (hG : ∀ t : ℂ, ‖t‖ < r → ContinuousOn (G t) (sphere 0 2)) (hX : ContinuousOn X (sphere 0 2))
    (hY : ContinuousOn Y (sphere 0 2))
    (hexp : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ z ∈ sphere (0 : ℂ) 2,
      ‖G t z - G 0 z - (t * X z + conj t * Y z)‖ ≤ ε * ‖t‖) :
    HasFDerivAt b (((2 * π * I)⁻¹ * ∮ z in C(0, 2), X z / z ^ 2) • (1 : ℂ →L[ℝ] ℂ) +
      ((2 * π * I)⁻¹ * ∮ z in C(0, 2), Y z / z ^ 2) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 := by
  have h2 := s3e_coef_exp (by norm_num) hr hG hX hY hexp
  refine (s3d2u_hasFDeriv (c0 := b 0) fun ε hε => ?_).2
  obtain ⟨δ, hδ, hd⟩ := h2 (2 * π * ε) (by positivity)
  refine ⟨min δ r, lt_min hδ hr, fun t ht => ?_⟩
  have htδ : ‖t‖ < δ := ht.trans_le (min_le_left _ _)
  have htr : ‖t‖ < r := ht.trans_le (min_le_right _ _)
  have h0r : ‖(0 : ℂ)‖ < r := by rw [norm_zero]; exact hr
  have hbt : b t = (2 * π * I)⁻¹ * ∮ z in C(0, 2), G t z / z ^ 2 := by
    rw [hb t htr, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have hb0 : b 0 = (2 * π * I)⁻¹ * ∮ z in C(0, 2), G 0 z / z ^ 2 := by
    rw [hb 0 h0r, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have e : b t - b 0 - (t * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), X z / z ^ 2) +
      conj t * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), Y z / z ^ 2)) =
      (2 * π * I)⁻¹ * ((∮ z in C(0, 2), G t z / z ^ 2) - (∮ z in C(0, 2), G 0 z / z ^ 2) -
        (t * (∮ z in C(0, 2), X z / z ^ 2) + conj t * ∮ z in C(0, 2), Y z / z ^ 2)) := by
    rw [hbt, hb0]
    ring
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_two]
  rw [e, norm_mul, norm_inv, hn]
  calc (2 * π)⁻¹ * ‖(∮ z in C(0, 2), G t z / z ^ 2) - (∮ z in C(0, 2), G 0 z / z ^ 2) -
        (t * (∮ z in C(0, 2), X z / z ^ 2) + conj t * ∮ z in C(0, 2), Y z / z ^ 2)‖
      ≤ (2 * π)⁻¹ * (2 * π * ε * ‖t‖) := mul_le_mul_of_nonneg_left (hd t htδ) (by positivity)
    _ = ε * ‖t‖ := by
        field_simp

/-- The pointwise form of `ġ` on `𝔻*` through the removable kernel:
`ġ(z) = -(1/π) g'(z) ∫ R K̃(·, z) + C g(z)²` (the two singular pieces of the frozen formula recombined). -/
theorem s3e_Gdot {g G R : ℂ → ℂ} {ρ Rb : ℝ} (C : ℂ) (hρ : ρ < 1) (hG : DifferentiableOn ℂ G {z : ℂ | ρ < ‖z‖})
    (hGi : InjOn G {z : ℂ | ρ < ‖z‖}) (hGd : ∀ z : ℂ, ρ < ‖z‖ → deriv G z ≠ 0)
    (hGg : EqOn G g unitDiscExterior) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hinf : ∃ c > 0, ∃ C : ℝ, ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (-(1 / π : ℂ) * ∫ u in unitDiscExterior, R u * deriv g u ^ 2 *
          (1 / (g u - g z) - 1 / g u - g z / g u ^ 2)) + C * g z ^ 2 -
        deriv g z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, R ζ *
          (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) =
      -(1 / π : ℂ) * (deriv g z * ∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
        (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) +
        C * g z ^ 2 := by
  obtain ⟨-, -, hgi, -, hg'⟩ := d2e_basic hρ hG hGi hGd hGg
  have hg0 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu h => by
    have := hk u hu
    rw [h, norm_zero] at this
    norm_num at this
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  have hKint := (d2e_core hρ hG hGi hGd hGg hk hinf hRm hRb hz).1
  have hNint := d2e_N_int hRm hRb hz
  have hz' := hg' z hz
  have hpt : ∀ᵐ u ∂(volume.restrict unitDiscExterior), R u * deriv g u ^ 2 *
      (1 / (g u - g z) - 1 / g u - g z / g u ^ 2) / deriv g z =
      R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 / (g u ^ 2 * deriv g w * dslope g u w) -
        (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z +
      R u * (((z + 1) * (z + I) * (z - 1)) / (((u + 1) * (u + I) * (u - 1)) * (u - z))) := by
    filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae
      ((measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)).mono
        fun u hu => fun h => hu (Set.mem_singleton_iff.2 h))] with u hu hne
    have hzu : z ≠ u := fun h => hne h.symm
    have hgz : g u ≠ g z := fun h => hzu (hgi hu hz h).symm
    rw [d2e_K_eq hzu (hg0 u hu) (hg' u hu) hz' hgz (d2e_dn_ne hu)]
    have h5 : g u - g z ≠ 0 := sub_ne_zero.2 hgz
    have h6 : u - z ≠ 0 := sub_ne_zero.2 hne
    have h7 := hg0 u hu
    have h8 := d2e_dn_ne hu
    field_simp
    ring
  have hAint : Integrable (fun u => R u * deriv g u ^ 2 * (1 / (g u - g z) - 1 / g u - g z / g u ^ 2) /
      deriv g z) (volume.restrict unitDiscExterior) := (hKint.add hNint).congr (EventuallyEq.symm hpt)
  have hK : (∫ u in unitDiscExterior, R u * -dslope (fun w => deriv g u ^ 2 * g w ^ 2 /
      (g u ^ 2 * deriv g w * dslope g u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) =
      (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - g z) - 1 / g u - g z / g u ^ 2)) / deriv g z -
        ∫ ζ in unitDiscExterior, R ζ * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))) := by
    rw [← integral_div, ← integral_sub hAint hNint]
    refine integral_congr_ae ?_
    filter_upwards [hpt] with u hu
    rw [hu]
    ring
  rw [hK]
  generalize (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - g z) - 1 / g u - g z / g u ^ 2)) = A
  generalize (∫ ζ in unitDiscExterior, R ζ * (((z + 1) * (z + I) * (z - 1)) /
    (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) = B
  field_simp
  ring

/-- **(D3)** The `β`-term: `g_t'(∞)` from `g_t ∘ γ̂_t = W_t ∘ g` at `∞`
(`∂_t g'(∞)/b = (1/π)∫ R g'²/g² + 2 (c₂/b) b₀ - c₁`, `∂_t̄ g'(∞)/b = 2 (c₂'/b) b₀ - c₁'`, where `c₁, c₁'` are the
linear coefficients of `γ̇, ∂_t̄ γ̂` at `∞`), and `∂ log|G| = ½ (∂G/G + conj(∂̄G/G))`. `R` does not decay at `∞`
(harmonic on `𝔻*`), so `∫ R g'²/g²` and `c₁` are each log-divergent; they are kept as ONE integral, whose integrand
`R (g'²/g² - 1/(ζ² - 1))` is `O(|ζ|⁻³)`.
At `κ = 0, a = 0` (`g = id`, `b₀ = 0`): `π ∂ log|g_t'(∞)| = ½ π (∫ m/ζ² - πc₁ - conj(πc₁'))` with
`π c₁ = ∫ m/(ζ² - 1)`, `conj(π c₁') = ∫ m/(ζ²(1 - ζ²))` (substitute `ζ = 1/ū`), so it is `0`, as `∂S₁(origin) = 0`
(`s3wc_S1_origin` + `N_f, N_g = O(|t|²)`) requires. No installed formula for `g_t'(∞)` at `0` (W-NORM gives only
differentiability). -/
theorem s3d_D3 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    DifferentiableAt ℝ
      (fun t : ℂ => ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 ∧
    dz (fun t : ℂ => ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 =
      (1 / 2 : ℂ) *
        (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 /
              gsans (beltramiMul a κ) ζ ^ 2 - (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) +
          2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) /
            derivAtInfty (gsans (beltramiMul a κ)) *
            limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z) +
        conj (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
              ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) *
            limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z) -
          (1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) /
            ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  have hRm : AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) :=
    (bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ :=
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))
  have hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖gsans (beltramiMul a κ) u‖ := fun u hu => d2e_koebe hpair hu
  have hinf := d2e_growth hpair
  obtain ⟨hgd, hg'd, -, -, hg'⟩ := d2e_basic hρ hGd hGi hGd' hGg
  obtain ⟨φ, hφd, hφ0, hφb, hch, -, hder⟩ := s3e_chart hμ
  obtain ⟨-, -, -, hVu⟩ := s3d_pair_variation hκ hκD ha has haL haD hm hmD
  obtain ⟨hSm, hSb⟩ := d2e_S_ae hRm hRb
  have hsE : sphere (0 : ℂ) 2 ⊆ unitDiscExterior := fun z hz => show 1 < ‖z‖ by
    rw [mem_sphere_zero_iff_norm.1 hz]; norm_num
  have hne : ∀ z ∈ sphere (0 : ℂ) 2, z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 fun h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hz
    norm_num at hz
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hb00 : derivAtInfty (gsans (beltramiMul a κ)) ≠ 0 := hφb ▸ hφ0 0 h0
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨r₀, hr₀, hfam⟩ : ∃ r₀ > 0, ∀ t : ℂ, ‖t‖ < r₀ →
      beltramiMul (a + t • toLinf m) (κ : LinfStar) ∈ LinfStarBall := by
    refine ⟨(delta0 - ‖a‖) / (‖toLinf m‖ + 1), div_pos (by linarith) (by positivity), fun t ht => ?_⟩
    refine bg_mul_mem_ball κ.2 (mem_ball_zero_iff.2 (lt_trans ?_ hd.2))
    have h1 := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖toLinf m‖ + 1)).1 ht
    calc ‖a + t • toLinf m‖ ≤ ‖a‖ + ‖t‖ * ‖toLinf m‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖a‖ + ‖t‖ * (‖toLinf m‖ + 1) := by nlinarith [norm_nonneg t]
      _ < delta0 := by linarith
  have hη1 := d2e_eta1 (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) hρ hGd hGi hGd' hGg hk hinf hRm hRb
  have hη2 := d2e_eta2 (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) hρ hGd hGi hGd' hGg hRm hRb
  have hXc : ContinuousOn (fun y => (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 - deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) (sphere 0 2) :=
    ((hη1.mul hg'd).continuousOn.mono hsE).congr fun z hz => by
      simp only [Pi.mul_apply]
      exact (div_mul_cancel₀ _ (hg' z (hsE hz))).symm
  have hYc : ContinuousOn (fun y => ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 - deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) (sphere 0 2) :=
    ((hη2.mul hg'd).continuousOn.mono hsE).congr fun z hz => by
      simp only [Pi.mul_apply]
      exact (div_mul_cancel₀ _ (hg' z (hsE hz))).symm
  have hbF := s3e_bderiv (G := fun t z => gsans (beltramiMul (a + t • toLinf m) κ) z)
    (b := fun t => derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ)))
    (X := fun y => (-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) y / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 - deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) (Y := fun y => ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) y ^ 2 - deriv (gsans (beltramiMul a κ)) y * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((y + 1) * (y + I) * (y - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - y))))) hr₀
    (fun t ht => s3e_coef_g (hfam t ht) (by norm_num))
    (fun t ht => (s3e_gdiff (hfam t ht)).continuousOn.mono hsE) hXc hYc (fun ε hε => by
      obtain ⟨δ, hδ, h⟩ := hVu 2 2 (by norm_num) ε hε
      refine ⟨δ, hδ, fun t ht z hz => ?_⟩
      have hz2 := mem_sphere_zero_iff_norm.1 hz
      simp only [zero_smul, add_zero]
      exact h t ht z hz2.ge hz2.le)
  have hlog := s3e_logn hbF (by simp only [zero_smul, add_zero]; exact hb00)
  simp only [zero_smul, add_zero] at hlog
  refine ⟨hlog.differentiableAt, ?_⟩
  rw [(s3d2u_dz hlog).1]
  -- the `t`-coefficient `X' = Coef₂(ġ)`
  have hQc : ContinuousOn (fun z => deriv (gsans (beltramiMul a κ)) z * (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * -dslope (fun w => deriv (gsans (beltramiMul a κ)) u ^ 2 * gsans (beltramiMul a κ) w ^ 2 / (gsans (beltramiMul a κ) u ^ 2 * deriv (gsans (beltramiMul a κ)) w * dslope (gsans (beltramiMul a κ)) u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z)) (sphere 0 2) :=
    (hg'd.continuousOn.mono hsE).mul fun z hz =>
      (d2e_core hρ hGd hGi hGd' hGg hk hinf hRm hRb (hsE hz)).2.continuousAt.continuousWithinAt
  have hg2c : ContinuousOn (fun z => gsans (beltramiMul a κ) z ^ 2 / z ^ 2) (sphere 0 2) :=
    ((hgd.continuousOn.mono hsE).pow 2).div (continuousOn_id.pow 2) hne
  have hX' : (2 * π * I)⁻¹ * (∮ z in C(0, 2), ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) / z ^ 2) =
      derivAtInfty (gsans (beltramiMul a κ)) * ((1 / π : ℂ) * (∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / gsans (beltramiMul a κ) ζ ^ 2 - (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) + 2 * (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z)) := by
    rw [circleIntegral.integral_congr (by norm_num) (g := fun z => -(1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * -dslope (fun w => deriv (gsans (beltramiMul a κ)) u ^ 2 * gsans (beltramiMul a κ) w ^ 2 / (gsans (beltramiMul a κ) u ^ 2 * deriv (gsans (beltramiMul a κ)) w * dslope (gsans (beltramiMul a κ)) u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) / z ^ 2) +
      (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2)) fun z hz => ?_]
    · have i1 : CircleIntegrable (fun z => -(1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * -dslope (fun w => deriv (gsans (beltramiMul a κ)) u ^ 2 * gsans (beltramiMul a κ) w ^ 2 / (gsans (beltramiMul a κ) u ^ 2 * deriv (gsans (beltramiMul a κ)) w * dslope (gsans (beltramiMul a κ)) u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) / z ^ 2)) 0 2 :=
        (continuousOn_const.mul (hQc.div (continuousOn_id.pow 2) hne)).circleIntegrable (by norm_num)
      have i2 : CircleIntegrable (fun z => (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2)) 0 2 :=
        (continuousOn_const.mul hg2c).circleIntegrable (by norm_num)
      rw [circleIntegral.integral_add i1 i2, circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
        s3e_Xcoef hρ hGd hGi hGd' hGg hk hinf hRm hRb hφd hφ0 hch hder, s3e_coef_g2 hμ (by norm_num), hφb]
      have hJ : (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * ((u + I) / ((u + 1) * (u + I) * (u - 1)) - deriv (gsans (beltramiMul a κ)) u ^ 2 / gsans (beltramiMul a κ) u ^ 2)) = -(∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (deriv (gsans (beltramiMul a κ)) ζ ^ 2 / gsans (beltramiMul a κ) ζ ^ 2 - (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
        rw [← integral_neg]
        congr 1
        funext ζ
        ring
      rw [hJ]
      field_simp
    · show ((-(1 / π : ℂ) * ∫ u in unitDiscExterior, RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z) - 1 / gsans (beltramiMul a κ) u - gsans (beltramiMul a κ) z / gsans (beltramiMul a κ) u ^ 2)) + ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) / z ^ 2 = -(1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ u in unitDiscExterior, RnmFun (toLinf m) a u * -dslope (fun w => deriv (gsans (beltramiMul a κ)) u ^ 2 * gsans (beltramiMul a κ) w ^ 2 / (gsans (beltramiMul a κ) u ^ 2 * deriv (gsans (beltramiMul a κ)) w * dslope (gsans (beltramiMul a κ)) u w) - (w + 1) * (w + I) * (w - 1) / ((u + 1) * (u + I) * (u - 1))) u z) / z ^ 2) + (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2)
      rw [s3e_Gdot (((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) hρ hGd hGi hGd' hGg hk hinf hRm hRb (hsE hz)]
      ring
  -- the `t̄`-coefficient `Y' = Coef₂(∂_t̄ g)`
  have hQ2c : ContinuousOn (fun z => deriv (gsans (beltramiMul a κ)) z * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) (sphere 0 2) :=
    (continuousOn_const.mul (hYc.sub (continuousOn_const.mul ((hgd.continuousOn.mono hsE).pow 2)))).congr
      fun z _ => by
        show deriv (gsans (beltramiMul a κ)) z * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) = (π : ℂ) * ((((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) - (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * gsans (beltramiMul a κ) z ^ 2)
        generalize (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) = B
        field_simp
        ring
  have hY' : (2 * π * I)⁻¹ * (∮ z in C(0, 2), (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) / z ^ 2) =
      derivAtInfty (gsans (beltramiMul a κ)) * (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * limUnder (cocompact ℂ) (fun z => gsans (beltramiMul a κ) z - derivAtInfty (gsans (beltramiMul a κ)) * z) - (1 / π : ℂ) * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
    rw [circleIntegral.integral_congr (by norm_num) (g := fun z => (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2) +
      (1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) / z ^ 2)) fun z hz => ?_]
    · have i1 : CircleIntegrable (fun z => (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2)) 0 2 :=
        (continuousOn_const.mul hg2c).circleIntegrable (by norm_num)
      have i2 : CircleIntegrable (fun z => (1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) / z ^ 2)) 0 2 :=
        (continuousOn_const.mul (hQ2c.div (continuousOn_id.pow 2) hne)).circleIntegrable (by norm_num)
      rw [circleIntegral.integral_add i1 i2, circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
        s3e_Ycoef hρ hGd hGi hGd' hGg hSm hSb hφd hder, s3e_coef_g2 hμ (by norm_num), hφb]
      have hJ : (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (-(derivAtInfty (gsans (beltramiMul a κ)) * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1))))) = -(derivAtInfty (gsans (beltramiMul a κ)) * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (ζ + I) / ((ζ + 1) * (ζ + I) * (ζ - 1)))) := by
        rw [← integral_const_mul, ← integral_neg]
        congr 1
        funext ζ
        ring
      rw [hJ]
      field_simp
      ring
    · show (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) * gsans (beltramiMul a κ) z ^ 2 - deriv (gsans (beltramiMul a κ)) z * (-(1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z))))) / z ^ 2 = (((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) * (gsans (beltramiMul a κ) z ^ 2 / z ^ 2) + (1 / π : ℂ) * (deriv (gsans (beltramiMul a κ)) z * (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 * (((z + 1) * (z + I) * (z - 1)) / (((ζ + 1) * (ζ + I) * (ζ - 1)) * (ζ - z)))) / z ^ 2)
      ring
  rw [hX', hY', mul_div_cancel_left₀ _ hb00, mul_div_cancel_left₀ _ hb00]
  ring

end TakhtajanTeo.Ch2
