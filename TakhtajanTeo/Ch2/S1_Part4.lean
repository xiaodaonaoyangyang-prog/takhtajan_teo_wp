import TakhtajanTeo.Ch2.S1_UnivalentFunctions
import TakhtajanTeo.Appendix.BergmanPeriodModel
import Mathlib.Analysis.Complex.JensenFormula

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- Mean value of `log |Θ|` for the inverted derivative of a normalized exterior univalent function. -/
theorem w4_theta_average {φ : ℂ → ℂ} {b : ℂ} (hφd : DifferentiableOn ℂ φ unitDisc)
    (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hφ1 : deriv φ 0 = 1) (hb : b ≠ 0) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun s => Real.log ‖b * deriv φ s / (dslope φ 0 s) ^ 2‖) 0 r = Real.log ‖b‖ := by
  have hball : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hψd : DifferentiableOn ℂ (dslope φ 0) (ball (0 : ℂ) 1) :=
    (differentiableOn_dslope (hball.mem_nhds (mem_ball_self one_pos))).mpr hφd
  have hdd : DifferentiableOn ℂ (deriv φ) (ball (0 : ℂ) 1) := hφd.deriv hball
  have hψne : ∀ s ∈ ball (0 : ℂ) 1, dslope φ 0 s ≠ 0 := by
    intro s hs
    by_cases h0 : s = 0
    · subst h0
      rw [dslope_same, hφ1]; exact one_ne_zero
    · rw [dslope_of_ne _ h0, slope_def_field, hφ0, sub_zero, sub_zero]
      have : φ s ≠ φ 0 := fun he => h0 (hφi hs (mem_ball_self one_pos) he)
      rw [hφ0] at this
      exact div_ne_zero this h0
  have hdne : ∀ s ∈ ball (0 : ℂ) 1, deriv φ s ≠ 0 := fun s hs =>
    deriv_ne_zero_of_injOn hball hφd hφi hs
  have hΘd : DifferentiableOn ℂ (fun s => b * deriv φ s / (dslope φ 0 s) ^ 2) (ball (0 : ℂ) 1) :=
    ((differentiableOn_const b).mul hdd).div (hψd.pow 2) (fun s hs => pow_ne_zero 2 (hψne s hs))
  have hΘa : AnalyticOnNhd ℂ (fun s => b * deriv φ s / (dslope φ 0 s) ^ 2) (ball (0 : ℂ) 1) :=
    hΘd.analyticOnNhd hball
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball (0 : ℂ) 1 := by
    rw [abs_of_pos hr0]
    exact closedBall_subset_ball hr1
  have h := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (R := r) (c := 0)
    (g := fun s => b * deriv φ s / (dslope φ 0 s) ^ 2) (hΘa.mono hsub)
    (fun u hu => div_ne_zero (mul_ne_zero hb (hdne u (hsub hu)))
      (pow_ne_zero 2 (hψne u (hsub hu))))
  rw [h]
  simp [dslope_same, hφ1]

/-- `g'(1/s)` for `g(1/s) = b / φ(s)`. -/
theorem w4_deriv_inverted {g φ : ℂ → ℂ} {b : ℂ} (hφd : DifferentiableOn ℂ φ unitDisc)
    (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s) {s : ℂ} (hs : s ∈ unitDisc) (hs0 : s ≠ 0) :
    deriv g (1 / s) = b * deriv φ s / (dslope φ 0 s) ^ 2 := by
  have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
  have hz0 : 1 / s ≠ 0 := one_div_ne_zero hs0
  have hzE : 1 / s ∈ unitDiscExterior := by
    show 1 < ‖1 / s‖
    rw [norm_div, norm_one, lt_div_iff₀ (norm_pos_iff.mpr hs0)]
    linarith
  have hevent : g =ᶠ[𝓝 (1 / s)] fun w => b / φ (w⁻¹) := by
    have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hzE] with w hw
    have hw0 : w ≠ 0 := by
      intro h0; subst h0
      have h1 : (1 : ℝ) < ‖(0 : ℂ)‖ := hw
      norm_num at h1
    have hwn : 1 < ‖w‖ := hw
    have hs' : w⁻¹ ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn)
    have := hg w⁻¹ hs' (inv_ne_zero hw0)
    rwa [one_div, inv_inv] at this
  rw [hevent.deriv_eq]
  have hφne : φ s ≠ 0 := by
    intro h0
    exact hs0 (hφi hs (mem_ball_self one_pos) (h0.trans hφ0.symm))
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(((1 / s) ^ 2)⁻¹)) (1 / s) := hasDerivAt_inv hz0
  have hφat : HasDerivAt φ (deriv φ s) (1 / s)⁻¹ := by
    rw [one_div, inv_inv]
    exact (hφd.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
  have hcomp := hφat.comp (1 / s) hinv
  have hq := (hasDerivAt_const (1 / s) b).div hcomp (by
    simp only [Function.comp_apply, one_div, inv_inv]; exact hφne)
  have hq2 : HasDerivAt (fun w : ℂ => b / φ w⁻¹)
      ((0 * φ (1 / s)⁻¹ - b * (deriv φ s * -((1 / s) ^ 2)⁻¹)) / φ (1 / s)⁻¹ ^ 2) (1 / s) := hq
  rw [hq2.deriv]
  rw [dslope_of_ne _ hs0, slope_def_field, hφ0, sub_zero, sub_zero]
  simp only [Function.comp_apply, one_div, inv_inv]
  field_simp
  ring

/-- Circle integrals of `log |h|` converge as the radius decreases to `1`. -/
theorem w4_circle_limit {h : ℂ → ℂ} (hc : ContinuousOn h (unitDiscExterior ∪ unitCircle))
    (hne : ∀ z ∈ unitDiscExterior ∪ unitCircle, h z ≠ 0) :
    Tendsto (fun ρ : ℝ => ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖)
      (𝓝[>] 1) (𝓝 (∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (exp (-(θ : ℂ) * I))‖)) := by
  set S : Set ℂ := unitDiscExterior ∪ unitCircle with hS
  have hΛ : ContinuousOn (fun z => Real.log ‖h z‖) S := hc.norm.log (fun z hz => norm_ne_zero_iff.mpr (hne z hz))
  have hmem : ∀ (ρ θ : ℝ), 1 ≤ ρ → (ρ : ℂ) * exp (-(θ : ℂ) * I) ∈ S := by
    intro ρ θ hρ
    have hn : ‖(ρ : ℂ) * exp (-(θ : ℂ) * I)‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have : ‖exp (-(θ : ℂ) * I)‖ = 1 := by
        rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, mul_one]
    rcases eq_or_lt_of_le hρ with h1 | h1
    · right; show ‖_‖ = 1; rw [hn, ← h1]
    · left; show 1 < ‖_‖; rw [hn]; exact h1
  have hKc : IsCompact (closedBall (0 : ℂ) 2 \ ball (0 : ℂ) 1) :=
    (isCompact_closedBall 0 2).diff isOpen_ball
  have hKS : closedBall (0 : ℂ) 2 \ ball (0 : ℂ) 1 ⊆ S := by
    intro z hz
    have h1 : 1 ≤ ‖z‖ := by simpa using hz.2
    rcases eq_or_lt_of_le h1 with h2 | h2
    · right; exact h2.symm
    · left; exact h2
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΛ.mono hKS)
  have hcurve : ∀ ρ : ℝ, Continuous fun θ : ℝ => (ρ : ℂ) * exp (-(θ : ℂ) * I) := by
    intro ρ; fun_prop
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with ρ hρ
    exact ((hΛ.comp_continuous (hcurve ρ) (fun θ => hmem ρ θ hρ.1.le)).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with ρ hρ
    refine Eventually.of_forall fun θ _ => ?_
    apply hM
    refine ⟨?_, ?_⟩
    · have : ‖(ρ : ℂ) * exp (-(θ : ℂ) * I)‖ = ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.1])]
        rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [mem_closedBall_zero_iff, this]; exact hρ.2.le
    · intro hb
      have hn : ‖(ρ : ℂ) * exp (-(θ : ℂ) * I)‖ = ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hρ.1])]
        rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [mem_ball_zero_iff, hn] at hb
      linarith [hρ.1]
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ => ?_
    have h1 : ContinuousWithinAt (fun z => Real.log ‖h z‖) S (exp (-(θ : ℂ) * I)) := by
      apply hΛ
      have := hmem 1 θ le_rfl
      simpa using this
    have hc1 : Continuous fun ρ : ℝ => (ρ : ℂ) * exp (-(θ : ℂ) * I) := by fun_prop
    have h2 : Tendsto (fun ρ : ℝ => (ρ : ℂ) * exp (-(θ : ℂ) * I)) (𝓝[>] 1)
        (𝓝[S] (exp (-(θ : ℂ) * I))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have := (hc1.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact hmem ρ θ (le_of_lt hρ)
    have := h1.tendsto.comp h2
    simpa [Function.comp_def] using this

theorem w4_norm_mul_exp (a θ : ℝ) : ‖(a : ℂ) * exp ((θ : ℂ) * I)‖ = |a| := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Remark 1.14** (TT:3790–3796). -/
theorem w3_remark_1_14 {p : T1} (hp : p ∈ T01) {h : ℂ → ℂ}
    (hc : ContinuousOn h (unitDiscExterior ∪ unitCircle))
    (hh : EqOn h (deriv (gsans (Quotient.out p : LinfStarBall))) unitDiscExterior)
    (h0 : ∀ z ∈ unitCircle, h z ≠ 0) :
    -4 * π * Real.log ‖derivAtInfty (gsans (Quotient.out p : LinfStarBall))‖ =
      -2 * ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (exp (θ * I))‖ := by
  have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p).2
  set μ : LinfStar := ((Quotient.out p : LinfStarBall) : LinfStar) with hμdef
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb, hbg, hG⟩ := g1_inverted_exterior hpair
  have hGuniv : IsUnivalentAtInfty (gsans μ) := hpair.2.2.2.2.1
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hne : ∀ z ∈ unitDiscExterior ∪ unitCircle, h z ≠ 0 := by
    rintro z (hz | hz)
    · rw [hh hz]
      exact deriv_ne_zero_of_injOn hopen hGuniv.1 hGuniv.2.1 hz
    · exact h0 z hz
  -- the circle integrals for radius `ρ > 1`
  have hI : ∀ ρ : ℝ, 1 < ρ →
      ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖ = 2 * π * Real.log ‖b‖ := by
    intro ρ hρ
    have hρ0 : 0 < ρ := by linarith
    have hr0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
    have hr1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
    have hav := w4_theta_average hφd hφi hφ0 hφ1 hb hr0 hr1
    rw [Real.circleAverage_def, smul_eq_mul] at hav
    have hpt : ∀ θ : ℝ, Real.log ‖b * deriv φ (circleMap 0 ρ⁻¹ θ) /
        (dslope φ 0 (circleMap 0 ρ⁻¹ θ)) ^ 2‖ =
        Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖ := by
      intro θ
      have hcm : circleMap 0 ρ⁻¹ θ = ((ρ⁻¹ : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
        rw [circleMap_zero]
      have hn : ‖circleMap 0 ρ⁻¹ θ‖ = ρ⁻¹ := by
        rw [hcm, w4_norm_mul_exp, abs_of_pos hr0]
      have hs : circleMap 0 ρ⁻¹ θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hn]; exact hr1)
      have hs0 : circleMap 0 ρ⁻¹ θ ≠ 0 := by
        intro h0'; rw [h0', norm_zero] at hn; exact hr0.ne hn
      have hinv : 1 / circleMap 0 ρ⁻¹ θ = (ρ : ℂ) * exp (-(θ : ℂ) * I) := by
        have hexp : exp (-(θ : ℂ) * I) = (exp ((θ : ℂ) * I))⁻¹ := by
          rw [neg_mul, Complex.exp_neg]
        have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
        have hex : exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
        rw [hcm, hexp]
        push_cast
        field_simp
      have hE : 1 / circleMap 0 ρ⁻¹ θ ∈ unitDiscExterior := by
        show 1 < ‖1 / circleMap 0 ρ⁻¹ θ‖
        rw [norm_div, norm_one, hn]
        rw [lt_div_iff₀ hr0]; linarith [mul_inv_cancel₀ hρ0.ne']
      rw [← w4_deriv_inverted hφd hφi hφ0 hG hs hs0, ← hinv]
      rw [← hh hE]
    simp only [hpt] at hav
    have h2π : (2 * π) ≠ 0 := by positivity
    calc ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖
        = (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖) := by
          exact (mul_inv_cancel_left₀ h2π _).symm
      _ = 2 * π * Real.log ‖b‖ := by rw [hav]
  have hlim := w4_circle_limit hc hne
  have hconst : Tendsto (fun ρ : ℝ => ∫ θ in (0 : ℝ)..2 * π,
      Real.log ‖h ((ρ : ℂ) * exp (-(θ : ℂ) * I))‖) (𝓝[>] 1) (𝓝 (2 * π * Real.log ‖b‖)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact (hI ρ hρ).symm
  have hI1 := tendsto_nhds_unique hlim hconst
  -- reverse the orientation of the circle
  have hrev : ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (exp (-(θ : ℂ) * I))‖ =
      ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (exp ((θ : ℂ) * I))‖ := by
    have := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.log ‖h (exp ((θ : ℂ) * I))‖) (a := 0) (b := 2 * π) (2 * π)
    rw [sub_self, sub_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    congr 3
    rw [show ((2 * π - θ : ℝ) : ℂ) * I = 2 * π * I - θ * I by push_cast; ring, Complex.exp_sub,
      Complex.exp_two_pi_mul_I, neg_mul, Complex.exp_neg, one_div]
  rw [hbg, ← hrev]
  have := hI1
  rw [this]
  ring

/-! ### Original relocated (2026-10-26) -/

/-- **Remark 1.14** (TT:3790–3796). When `𝗀_μ'` is continuous on `S¹` (extends continuously from `𝔻*` to
`𝔻* ∪ S¹`, by `h`), the last term of `S₁` is `-4π log |𝗀_μ'(∞)| = -2 ∮_{S¹} log |𝗀_μ'(e^{iθ})| dθ`.

[CORRECTION 2026-10-25] `h ≠ 0` on `S¹` is assumed. The mean value of the harmonic `log |𝗀_μ'|` on the circles
`|z| = r` then passes to `r = 1`. If `h` vanishes on `S¹`, `log |h|` is singular there, and a disk-algebra function may
carry a singular inner factor (下属4: UNSURE). -/
theorem remark_1_14 {p : T1} (hp : p ∈ T01) {h : ℂ → ℂ} (hc : ContinuousOn h (unitDiscExterior ∪ unitCircle))
    (hh : EqOn h (deriv (gsans (Quotient.out p : LinfStarBall))) unitDiscExterior)
    (h0 : ∀ z ∈ unitCircle, h z ≠ 0) :
    -4 * π * Real.log ‖derivAtInfty (gsans (Quotient.out p : LinfStarBall))‖ =
      -2 * ∫ θ in (0 : ℝ)..2 * π, Real.log ‖h (exp (θ * I))‖ :=
  w3_remark_1_14 hp hc hh h0

end Ch2

end TakhtajanTeo
