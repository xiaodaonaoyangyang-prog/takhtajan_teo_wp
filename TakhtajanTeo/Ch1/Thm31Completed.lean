import TakhtajanTeo.Ch1.Cor32Completed

/-!
# Theorem 3.1, proved downstream of §3 (TT:1906–1922)

`t31_thm_3_1` is `thm_3_1`. TT's density argument through `Möb(S¹)\Diff₊(S¹)` is replaced by a dilation path:
for `ψ = β([μ]) ∈ A₂(𝔻)`, the path `r ↦ r² ψ(r·)`, `r ∈ [0, 1]`, stays in `β(T(1)) ∩ A₂(𝔻)` (if `F` is a q.c. map of `ℂ`
conformal on `𝔻`, so is `z ↦ F(rz)/r`, and `𝒮(F(r·)/r)(z) = r² 𝒮(F)(rz)`), is continuous in `A₂(𝔻)`, and joins `ψ`
to `0`. The inclusion `A₂(𝔻) → A∞(𝔻)` is continuous for the Hilbert manifold topology by construction.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
open QCV

/-- Real dilations are quasi-measure-preserving for Lebesgue measure on `ℂ`. -/
theorem t31_qmp_scale {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (fun z : ℂ => (r : ℂ) * z) volume volume := by
  have h : (fun z : ℂ => (r : ℂ) * z) = fun z => r • z := by
    funext z; simp [Complex.real_smul]
  rw [h]
  refine ⟨measurable_const_smul r, ?_⟩
  rw [Measure.map_addHaar_smul volume hr]
  exact Measure.smul_absolutelyContinuous

/-- The ℝ-derivatives of `z ↦ c F(rz)`. -/
theorem t31_fderiv_affine (F : ℂ → ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℝ) (z : ℂ) :
    fderiv ℝ (fun w => c * F ((r : ℂ) * w)) z = (r : ℝ) • (c • fderiv ℝ F ((r : ℂ) * z)) := by
  have hs : (fun w : ℂ => F ((r : ℂ) * w)) = fun w => F (r • w) := by
    funext w; rw [Complex.real_smul]
  have hinner : fderiv ℝ (fun w : ℂ => F ((r : ℂ) * w)) z = r • fderiv ℝ F ((r : ℂ) * z) := by
    rw [hs, fderiv_comp_smul (f := F) r, Complex.real_smul]
  set G : ℂ → ℂ := fun w => F ((r : ℂ) * w) with hG
  by_cases hd : DifferentiableAt ℝ G z
  · have h := (hd.hasFDerivAt.const_mul c).fderiv
    rw [h, hinner, smul_comm]
  · have hnd : ¬ DifferentiableAt ℝ (fun w => c * G w) z := by
      intro h
      apply hd
      refine (h.const_mul c⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
      simp only
      field_simp
    rw [fderiv_zero_of_not_differentiableAt hnd]
    have hz : fderiv ℝ G z = 0 := fderiv_zero_of_not_differentiableAt hd
    rw [hinner] at hz
    rw [smul_comm, hz, smul_zero]

/-- The complex dilatation is unchanged by `F ↦ c F(r ·)`. -/
theorem t31_dilatation_affine (F : ℂ → ℂ) {c : ℂ} (hc : c ≠ 0) {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    complexDilatation (fun w => c * F ((r : ℂ) * w)) z = complexDilatation F ((r : ℂ) * z) := by
  unfold complexDilatation dzbar dz
  rw [t31_fderiv_affine F hc r z]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.real_smul]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  by_cases h0 : fderiv ℝ F ((r : ℂ) * z) 1 - I * fderiv ℝ F ((r : ℂ) * z) I = 0
  · have h0' : (r : ℂ) * (c * fderiv ℝ F ((r : ℂ) * z) 1) -
        I * ((r : ℂ) * (c * fderiv ℝ F ((r : ℂ) * z) I)) = 0 := by
      linear_combination (r : ℂ) * c * h0
    rw [h0', h0, zero_div, div_zero, div_zero]
  · field_simp

/-- The Schwarzian of `z ↦ c F(rz)`. -/
theorem t31_schwarzian_affine (F : ℂ → ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℝ) (z : ℂ) :
    schwarzianHol (fun w => c * F ((r : ℂ) * w)) z = (r : ℂ) ^ 2 * schwarzianHol F ((r : ℂ) * z) := by
  have hcomp : ∀ g : ℂ → ℂ, deriv (fun w => g ((r : ℂ) * w)) = fun w => (r : ℂ) * deriv g ((r : ℂ) * w) := by
    intro g; funext w
    exact (deriv_comp_mul_left (r : ℂ) g w).trans (smul_eq_mul _ _)
  have hG1 : deriv (fun w => c * F ((r : ℂ) * w)) = fun w => c * ((r : ℂ) * deriv F ((r : ℂ) * w)) := by
    rw [deriv_const_mul_field', hcomp]
  have hG2 : deriv (deriv (fun w => c * F ((r : ℂ) * w))) =
      fun w => c * ((r : ℂ) * ((r : ℂ) * deriv (deriv F) ((r : ℂ) * w))) := by
    rw [hG1]
    funext w
    rw [deriv_const_mul_field c, deriv_const_mul_field (r : ℂ), congrFun (hcomp (deriv F)) w]
  set q : ℂ → ℂ := fun u => deriv (deriv F) u / deriv F u with hqdef
  have hq : (fun w => deriv (deriv (fun w => c * F ((r : ℂ) * w))) w / deriv (fun w => c * F ((r : ℂ) * w)) w) =
      fun w => (r : ℂ) * q ((r : ℂ) * w) := by
    funext w
    rw [hG2, hG1, hqdef]
    simp only
    by_cases hB : deriv F ((r : ℂ) * w) = 0
    · rw [hB]; simp
    by_cases hr : (r : ℂ) = 0
    · rw [hr]; simp
    field_simp
  have hdq : deriv (fun w => (r : ℂ) * q ((r : ℂ) * w)) z = (r : ℂ) * ((r : ℂ) * deriv q ((r : ℂ) * z)) := by
    rw [deriv_const_mul_field (r : ℂ), congrFun (hcomp q) z]
  have hqz : deriv (deriv (fun w => c * F ((r : ℂ) * w))) z / deriv (fun w => c * F ((r : ℂ) * w)) z =
      (r : ℂ) * q ((r : ℂ) * z) := congrFun hq z
  unfold schwarzianHol
  rw [hq, hdq, hqz]
  simp only [hqdef]
  ring

/-- Dilation of a Bers point (TT:1908, replacing the `Möb\Diff` argument). -/
theorem t31_bersPhi_dilate (μ : LinfStarBall) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ ν : LinfStarBall, ∀ z ∈ unitDisc,
      AInf.toFun (bersPhi ν) z = (r : ℂ) ^ 2 * AInf.toFun (bersPhi μ) ((r : ℂ) * z) := by
  have hk : ‖(μ : LinfStar)‖ < 1 := bc_norm_lt_one μ.2
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hext : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hqmp := t31_qmp_scale hr0.ne'
  -- the dilated coefficient
  let g : ℂ → ℂ := fun z => extB (μ : LinfStar) ((r : ℂ) * z)
  obtain ⟨hB1, hB2⟩ := extB_isBeltramiCoeff (μ : LinfStar)
  rw [Measure.restrict_univ] at hB1 hB2
  have hgm : AEStronglyMeasurable g volume := hB1.comp_quasiMeasurePreserving hqmp
  have hgb : ∀ᵐ z ∂volume, ‖g z‖ ≤ ‖(μ : LinfStar)‖ := hqmp.ae hB2
  have hmem : MemLp g ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound (hgm.restrict) _ (ae_restrict_of_ae hgb)
  let ν₀ : LinfStar := toLinf g
  have hνae := bc_toLinf_ae hmem
  have hνn : ‖ν₀‖ ≤ ‖(μ : LinfStar)‖ := by
    apply bc_Lp_norm_le _ (norm_nonneg _)
    filter_upwards [hνae, ae_restrict_of_ae hgb] with z h1 h2
    rw [h1]; exact h2
  have hν : ν₀ ∈ LinfStarBall := by
    simpa [LinfStarBall] using lt_of_le_of_lt hνn hk
  refine ⟨⟨ν₀, hν⟩, ?_⟩
  -- `extB ν₀ = g` a.e. on `ℂ`
  have hextν : extB ν₀ =ᵐ[volume] g := by
    have h1 : ∀ᵐ z ∂volume, z ∈ unitDiscExterior → ν₀ z = g z := (ae_restrict_iff' hext).mp hνae
    filter_upwards [h1] with z hz
    by_cases hzE : z ∈ unitDiscExterior
    · simp only [extB, indicator_of_mem hzE]; exact hz hzE
    · have hzn : ‖z‖ ≤ 1 := by
        simpa [unitDiscExterior] using hzE
      have hrz : (r : ℂ) * z ∉ unitDiscExterior := by
        simp only [unitDiscExterior, mem_setOf_eq, not_lt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr0]
        nlinarith [norm_nonneg z]
      simp only [extB, indicator_of_notMem hzE, g, indicator_of_notMem hrz]
  -- the normalized solutions
  obtain ⟨hW, hWhol, hWinj, hW0⟩ := qcv_W_props hk
  set W := normalizedSolution (extB (μ : LinfStar)) with hWdef
  have hWr : W (r : ℂ) ≠ 0 := by
    intro h
    exact hrc (hWinj (mem_univ _) (mem_univ _) (h.trans hW0.symm))
  set c : ℂ := (W (r : ℂ))⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hWr
  let V : ℂ → ℂ := fun w => c * W ((r : ℂ) * w)
  obtain ⟨⟨K, hK⟩, hWs, -, -, hWd⟩ := hW
  have hV : IsNormalizedSolution V (extB ν₀) := by
    obtain ⟨hVK, hVs⟩ := td_affine_comp hK hWs (α := (r : ℂ)) (γ := c) 0 0 hrc hc0
    have hVeq : (fun z => c * W ((r : ℂ) * z + 0) + 0) = V := by funext z; simp [V]
    rw [hVeq] at hVK hVs
    refine ⟨⟨K, hVK⟩, hVs, ?_, ?_, ?_⟩
    · simp [V, hW0]
    · simp [V, hc, inv_mul_cancel₀ hWr]
    · filter_upwards [hextν, hqmp.ae hWd] with z h1 h2
      rw [h1, t31_dilatation_affine W hc0 hr0.ne' z]
      exact h2
  have hkν : ‖ν₀‖ < 1 := lt_of_le_of_lt hνn hk
  have hVeq : normalizedSolution (extB ν₀) = V :=
    qcv_ns_eq (norm_nonneg ν₀) hkν (extB_isBeltramiCoeff ν₀) hV
  -- Schwarzians
  intro z hz
  have hrz : (r : ℂ) * z ∈ unitDisc := by
    simp only [unitDisc, mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  obtain ⟨hfν, hiν⟩ := fB_holomorphic_injective hν
  obtain ⟨hfμ, hiμ⟩ := fB_holomorphic_injective μ.2
  change AInf.toFun (toAInf unitDisc (schwarzianHol (fB ν₀))) z =
    (r : ℂ) ^ 2 * AInf.toFun (toAInf unitDisc (schwarzianHol (fB (μ : LinfStar)))) ((r : ℂ) * z)
  rw [(schwarzianHol_AInf_spec hfν hiν).1 z hz, (schwarzianHol_AInf_spec hfμ hiμ).1 _ hrz,
    qcv_schwarzian_fB_eq hν hz, qcv_schwarzian_fB_eq μ.2 hrz, hVeq]
  exact t31_schwarzian_affine W hc0 r z

/-- Dilations stay in `A₂(𝔻)`. -/
theorem t31_dilate_mem_A2 {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)) ∈ A2fun unitDisc := by
  rcases hr0.eq_or_lt with h0 | h0
  · subst h0
    have hz : (fun z => ((0 : ℝ) : ℂ) ^ 2 * f (((0 : ℝ) : ℂ) * z)) = fun _ => (0 : ℂ) := by
      funext z; simp
    rw [hz]
    refine ⟨differentiableOn_const _, ?_⟩
    simp [normA2]
  rcases hr1.eq_or_lt with h1 | h1
  · subst h1
    have hz : (fun z => ((1 : ℝ) : ℂ) ^ 2 * f (((1 : ℝ) : ℂ) * z)) = f := by
      funext z; simp
    rw [hz]
    exact hf
  obtain ⟨R, hR, hfs⟩ := holomorphic_inward_dilate hf.1 h0 h1
  have hd : DifferentiableOn ℂ (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)) (closedBall 0 R) :=
    hfs.const_mul _
  refine ⟨hd.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hR.le)), ?_⟩
  apply normA2_lt_top_of_integrable_weighted_sq
  have hw : Continuous (fun z : ℂ => (rho z)⁻¹) := by simp only [rho, inv_div]; fun_prop
  have hc : ContinuousOn (fun z => ‖(r : ℂ) ^ 2 * f ((r : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) (closedBall 0 1) :=
    (((hd.mono (closedBall_subset_closedBall hR.le)).continuousOn.norm.pow 2).mul hw.continuousOn)
  exact (hc.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall

/-- `‖v‖₊` as an `ofReal`. -/
theorem t31_coe_nnnorm (v : ℂ) : ((‖v‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖v‖ := by
  rw [ofReal_norm, enorm_eq_nnnorm]

/-- The squared `A₂` norm is the weighted lintegral. -/
theorem t31_normA2_sq (φ : ℂ → ℂ) :
    normA2 unitDisc φ ^ 2 = ∫⁻ z in unitDisc, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
  unfold normA2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `edist` in `A₂(𝔻)` is the `A₂` norm of the difference of representatives. -/
theorem t31_edist_toA2 {g h : ℂ → ℂ} (hg : g ∈ A2fun unitDisc) (hh : h ∈ A2fun unitDisc) :
    edist (toA2 unitDisc g) (toA2 unitDisc h) = normA2 unitDisc (fun z => g z - h z) := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  set a := toA2 unitDisc g
  set b := toA2 unitDisc h
  rw [edist_eq_enorm_sub, enorm_eq_nnnorm, ← A2.norm_toFun]
  apply normA2_congr (D := unitDisc) measurableSet_ball
  have hd : DifferentiableOn ℂ (fun z => A2.toFun a z - A2.toFun b z) unitDisc :=
    (A2.toFun_spec a).1.sub (A2.toFun_spec b).1
  have hrep : ((a - b : A2 unitDisc) : Lp ℂ 2 (rhoInvMeasure unitDisc)) =ᵐ[rhoInvMeasure unitDisc]
      fun z => A2.toFun a z - A2.toFun b z := by
    have hc : ((a - b : A2 unitDisc) : Lp ℂ 2 (rhoInvMeasure unitDisc)) =
        (a : Lp ℂ 2 (rhoInvMeasure unitDisc)) - (b : Lp ℂ 2 (rhoInvMeasure unitDisc)) := rfl
    rw [hc]
    filter_upwards [Lp.coeFn_sub (a : Lp ℂ 2 (rhoInvMeasure unitDisc)) b, (A2.toFun_spec a).2,
      (A2.toFun_spec b).2] with z hz ha hb
    rw [hz, Pi.sub_apply, ha, hb]
  intro z hz
  have hga : A2.toFun a z = g z := toA2_spec (D := unitDisc) isOpen_ball hcircle hg hz
  have hhb : A2.toFun b z = h z := toA2_spec (D := unitDisc) isOpen_ball hcircle hh hz
  rw [A2.toFun_eqOn (D := unitDisc) isOpen_ball hcircle (a - b) hd hrep hz]
  show A2.toFun a z - A2.toFun b z = g z - h z
  rw [hga, hhb]

/-- Dilations do not increase the `A₂` norm. -/
theorem t31_normA2_dilate_le {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    normA2 unitDisc (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)) ≤ normA2 unitDisc f := by
  rcases hr0.eq_or_lt with h0 | h0
  · subst h0
    have hz : (fun z => ((0 : ℝ) : ℂ) ^ 2 * f (((0 : ℝ) : ℂ) * z)) = fun _ => (0 : ℂ) := by
      funext z; simp
    rw [hz]
    simp [normA2]
  rcases hr1.eq_or_lt with h1 | h1
  · subst h1
    have hz : (fun z => ((1 : ℝ) : ℂ) ^ 2 * f (((1 : ℝ) : ℂ) * z)) = f := by
      funext z; simp
    rw [hz]
  have hm := t31_dilate_mem_A2 hf h0.le h1.le
  have hsq : normA2 unitDisc (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)) ^ 2 ≤ normA2 unitDisc f ^ 2 := by
    rw [A2fun.normA2_sq (D := unitDisc) isOpen_ball hm, A2fun.normA2_sq (D := unitDisc) isOpen_ball hf]
    apply ENNReal.ofReal_le_ofReal
    have hpt : ∀ z, ‖(r : ℂ) ^ 2 * f ((r : ℂ) * z)‖ ^ 2 * (rho z)⁻¹ =
        r ^ 4 * (‖f ((r : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) := by
      intro z
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    have hmass := A2fun.inward_dilate_mass_le hf h0 h1
    have hI : 0 ≤ ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ :=
      setIntegral_nonneg measurableSet_ball (fun z _ => by unfold rho; positivity)
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    calc r ^ 4 * ∫ z in unitDisc, ‖f ((r : ℂ) * z)‖ ^ 2 * (rho z)⁻¹
        ≤ r ^ 4 * ((r ^ 2)⁻¹ * ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = r ^ 2 * ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
          field_simp
      _ ≤ 1 * ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := mul_le_mul_of_nonneg_right hr2 hI
      _ = _ := one_mul _
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-- `∫⁻_𝔻 ρ⁻¹ < ∞`. -/
theorem t31_lintegral_rhoInv_ne_top : ∫⁻ z in unitDisc, ENNReal.ofReal (rho z)⁻¹ ≠ ∞ := by
  apply ne_of_lt
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (rho z)⁻¹ ≤ ∫⁻ _ in unitDisc, ENNReal.ofReal (1 / 4) := by
        apply setLIntegral_mono measurable_const
        intro z hz
        apply ENNReal.ofReal_le_ofReal
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have h1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
        simp only [rho, inv_div]
        have : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
        linarith
    _ = ENNReal.ofReal (1 / 4) * volume unitDisc := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- `‖a - b‖₊² ≤ 2‖a‖₊² + 2‖b‖₊²`. -/
theorem t31_nnnorm_sub_sq_le (a b : ℂ) :
    (‖a - b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  simp only [t31_coe_nnnorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := norm_sub_le a b
  have h2 := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

/-- Pointwise continuity of the dilation in `r`. -/
theorem t31_dilate_tendsto_pt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : z ∈ unitDisc)
    {r₀ : ℝ} (hr0 : 0 ≤ r₀) (hr1 : r₀ ≤ 1) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * f ((r : ℂ) * z)) (𝓝 r₀) (𝓝 ((r₀ : ℂ) ^ 2 * f ((r₀ : ℂ) * z))) := by
  have hrz : (r₀ : ℂ) * z ∈ unitDisc := by
    simp only [unitDisc, mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hfc : ContinuousAt f ((r₀ : ℂ) * z) := hf.continuousOn.continuousAt (isOpen_ball.mem_nhds hrz)
  have hlin : ContinuousAt (fun r : ℝ => (r : ℂ) * z) r₀ := by fun_prop
  have := ((continuous_ofReal.pow 2).continuousAt (x := r₀)).mul (ContinuousAt.comp (x := r₀) hfc hlin)
  exact this.tendsto

/-- The weighted lintegral `E(r, r₀)` of `|D_r f - D_{r₀} f|²` tends to `0` as `r → r₀` in `[0, 1]`. -/
theorem t31_dilate_lintegral_tendsto {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun r : ℝ => ∫⁻ z in unitDisc,
        (‖(r : ℂ) ^ 2 * f ((r : ℂ) * z) - (r₀ : ℂ) ^ 2 * f ((r₀ : ℂ) * z)‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (rho z)⁻¹) (𝓝[Icc 0 1] r₀) (𝓝 0) := by
  -- clamped parameter, so that every integrand is a.e.-measurable
  let c : ℝ → ℝ := fun r => max 0 (min 1 r)
  have hc_mem : ∀ r, c r ∈ Icc (0 : ℝ) 1 := fun r =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hc_eq : ∀ r ∈ Icc (0 : ℝ) 1, c r = r := fun r hr => by
    simp only [c, min_eq_right hr.2, max_eq_right hr.1]
  let D : ℝ → ℂ → ℂ := fun r z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)
  let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (rho z)⁻¹
  have hw : Measurable w := by
    have : Measurable (fun z : ℂ => (rho z)⁻¹) := by unfold rho; fun_prop
    exact ENNReal.measurable_ofReal.comp this
  have hDm : ∀ r ∈ Icc (0 : ℝ) 1, AEMeasurable (D r) (volume.restrict unitDisc) := fun r hr =>
    ((t31_dilate_mem_A2 hf hr.1 hr.2).1.continuousOn.aestronglyMeasurable measurableSet_ball).aemeasurable
  let F : ℝ → ℂ → ℝ≥0∞ := fun r z => (‖D (c r) z - D r₀ z‖₊ : ℝ≥0∞) ^ 2 * w z
  have hFm : ∀ r, AEMeasurable (F r) (volume.restrict unitDisc) := fun r =>
    ((((hDm _ (hc_mem r)).sub (hDm _ hr₀)).nnnorm.coe_nnreal_ennreal).pow_const 2).mul hw.aemeasurable
  have hIcc : ∀ᶠ r in 𝓝[Icc 0 1] r₀, r ∈ Icc (0 : ℝ) 1 := self_mem_nhdsWithin
  have hcongr : (fun r : ℝ => ∫⁻ z in unitDisc, F r z) =ᶠ[𝓝[Icc 0 1] r₀]
      fun r => ∫⁻ z in unitDisc, (‖(r : ℂ) ^ 2 * f ((r : ℂ) * z) - (r₀ : ℂ) ^ 2 * f ((r₀ : ℂ) * z)‖₊ :
        ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
    filter_upwards [hIcc] with r hr
    simp only [F, D, w, hc_eq r hr]
  refine Tendsto.congr' hcongr ?_
  -- pointwise convergence of the clamped dilations
  have hcT : Tendsto c (𝓝[Icc 0 1] r₀) (𝓝 r₀) := by
    have : Tendsto c (𝓝 r₀) (𝓝 (c r₀)) := by
      have : Continuous c := by fun_prop
      exact this.tendsto r₀
    rw [hc_eq r₀ hr₀] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hptD : ∀ z ∈ unitDisc, Tendsto (fun r => D (c r) z) (𝓝[Icc 0 1] r₀) (𝓝 (D r₀ z)) :=
    fun z hz => (t31_dilate_tendsto_pt hf.1 hz hr₀.1 hr₀.2).comp hcT
  rcases hr₀.2.lt_or_eq with hlt | heq
  · -- `r₀ < 1`: dominated convergence
    set r₁ : ℝ := (1 + r₀) / 2 with hr₁
    have hr₁1 : r₁ < 1 := by rw [hr₁]; linarith
    have hr₀₁ : r₀ < r₁ := by rw [hr₁]; linarith
    have hcont : ContinuousOn f (closedBall 0 r₁) :=
      hf.1.continuousOn.mono (closedBall_subset_ball hr₁1)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r₁).exists_bound_of_continuousOn hcont
    have hDb : ∀ r ∈ Icc (0 : ℝ) 1, r ≤ r₁ → ∀ z ∈ unitDisc, ‖D r z‖ ≤ M := by
      intro r hr hrr z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hrz : (r : ℂ) * z ∈ closedBall (0 : ℂ) r₁ := by
        simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr.1]
        nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_left hz1.le hr.1]
      have hr2 : ‖(r : ℂ) ^ 2‖ ≤ 1 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
        nlinarith [hr.1, hr.2]
      calc ‖D r z‖ = ‖(r : ℂ) ^ 2‖ * ‖f ((r : ℂ) * z)‖ := norm_mul _ _
        _ ≤ 1 * M := mul_le_mul hr2 (hM _ hrz) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
    have hnear : ∀ᶠ r in 𝓝[Icc 0 1] r₀, c r ≤ r₁ := by
      have : ∀ᶠ r in 𝓝[Icc 0 1] r₀, c r < r₁ := hcT (Iio_mem_nhds hr₀₁)
      filter_upwards [this] with r hr using hr.le
    have hfin : ∫⁻ z in unitDisc, ENNReal.ofReal ((2 * M) ^ 2) * w z ≠ ∞ := by
      rw [lintegral_const_mul _ hw]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top t31_lintegral_rhoInv_ne_top
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume.restrict unitDisc)
      (l := 𝓝[Icc 0 1] r₀)
      (F := F) (f := fun _ => 0) (fun z => ENNReal.ofReal ((2 * M) ^ 2) * w z)
      (Eventually.of_forall hFm) ?_ hfin ?_
    · simpa using h
    · filter_upwards [hnear] with r hr
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      gcongr ?_ * _
      rw [t31_coe_nnnorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := hDb _ (hc_mem r) hr z hz
      have h2 := hDb _ hr₀ hr₀₁.le z hz
      have h3 := norm_sub_le (D (c r) z) (D r₀ z)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans h2
      nlinarith [norm_nonneg (D (c r) z - D r₀ z)]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have h1 : Tendsto (fun r => D (c r) z - D r₀ z) (𝓝[Icc 0 1] r₀) (𝓝 0) := by
        simpa using (hptD z hz).sub_const (D r₀ z)
      have h2 := ((ENNReal.continuous_coe.comp continuous_nnnorm).tendsto (0 : ℂ)).comp h1
      have h3 := ENNReal.Tendsto.mul_const (b := w z) (((ENNReal.continuous_pow 2).tendsto _).comp h2) (Or.inr ENNReal.ofReal_ne_top)
      simpa using h3
  · -- `r₀ = 1`: Fatou
    subst heq
    have hD1 : ∀ z, D 1 z = f z := fun z => by simp [D]
    have : (𝓝[Icc (0 : ℝ) 1] (1 : ℝ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (subset_closure (right_mem_Icc.2 zero_le_one))
    let G : ℝ → ℂ → ℝ≥0∞ := fun r z => (‖D (c r) z‖₊ : ℝ≥0∞) ^ 2 * w z
    let H : ℂ → ℝ≥0∞ := fun z => (‖f z‖₊ : ℝ≥0∞) ^ 2 * w z
    set A : ℝ≥0∞ := ∫⁻ z in unitDisc, H z with hA
    have hAfin : A ≠ ∞ := by
      have h := hf.2
      rw [← ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)] at h
      have h2 : normA2 unitDisc f ^ (2 : ℝ) = A := by
        rw [ENNReal.rpow_two, t31_normA2_sq]
      rw [h2] at h
      exact h.ne
    have hGm : ∀ r, AEMeasurable (G r) (volume.restrict unitDisc) := fun r =>
      (((hDm _ (hc_mem r)).nnnorm.coe_nnreal_ennreal).pow_const 2).mul hw.aemeasurable
    have hHm : AEMeasurable H (volume.restrict unitDisc) := by
      have := hDm 1 ⟨zero_le_one, le_rfl⟩
      have hfm : AEMeasurable f (volume.restrict unitDisc) := by
        have hD1' : D 1 = f := funext hD1
        rwa [hD1'] at this
      exact ((hfm.nnnorm.coe_nnreal_ennreal).pow_const 2).mul hw.aemeasurable
    have hGA : ∀ r, ∫⁻ z in unitDisc, G r z ≤ A := by
      intro r
      have h := t31_normA2_dilate_le hf (hc_mem r).1 (hc_mem r).2
      have h2 := pow_le_pow_left₀ zero_le h 2
      rw [t31_normA2_sq, t31_normA2_sq] at h2
      exact h2
    have hFle : ∀ r z, F r z ≤ 2 * G r z + 2 * H z := by
      intro r z
      simp only [F, G, H]
      rw [hD1]
      calc (‖D (c r) z - f z‖₊ : ℝ≥0∞) ^ 2 * w z
          ≤ (2 * (‖D (c r) z‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖f z‖₊ : ℝ≥0∞) ^ 2) * w z :=
            by gcongr ?_ * _; exact t31_nnnorm_sub_sq_le _ _
        _ = _ := by ring
    have hFint : ∀ r, ∫⁻ z in unitDisc, F r z ≤ 4 * A := by
      intro r
      calc ∫⁻ z in unitDisc, F r z ≤ ∫⁻ z in unitDisc, (2 * G r z + 2 * H z) := lintegral_mono (hFle r)
        _ = 2 * (∫⁻ z in unitDisc, G r z) + 2 * A := by
            rw [lintegral_add_left' ((hGm r).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num), hA]
        _ ≤ 2 * A + 2 * A := add_le_add (mul_le_mul' le_rfl (hGA r)) le_rfl
        _ = 4 * A := by ring
    let g : ℝ → ℂ → ℝ≥0∞ := fun r z => (2 * G r z + 2 * H z) - F r z
    have hgm : ∀ r, AEMeasurable (g r) (volume.restrict unitDisc) := fun r =>
      ((((hGm r).const_mul 2).add (hHm.const_mul 2))).sub (hFm r)
    have hgint : ∀ r, ∫⁻ z in unitDisc, g r z ≤ 4 * A - ∫⁻ z in unitDisc, F r z := by
      intro r
      have hFfin : ∫⁻ z in unitDisc, F r z ≠ ∞ :=
        ((hFint r).trans_lt (ENNReal.mul_lt_top (by norm_num) hAfin.lt_top)).ne
      rw [lintegral_sub' (hFm r) hFfin (Eventually.of_forall (hFle r))]
      apply tsub_le_tsub_right
      calc ∫⁻ z in unitDisc, (2 * G r z + 2 * H z) = 2 * (∫⁻ z in unitDisc, G r z) + 2 * A := by
            rw [lintegral_add_left' ((hGm r).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num), hA]
        _ ≤ 2 * A + 2 * A := add_le_add (mul_le_mul' le_rfl (hGA r)) le_rfl
        _ = 4 * A := by ring
    have hliminf : ∫⁻ z in unitDisc, liminf (fun r => g r z) (𝓝[Icc 0 1] (1 : ℝ)) = 4 * A := by
      have hae : ∀ᵐ z ∂(volume.restrict unitDisc),
          liminf (fun r => g r z) (𝓝[Icc 0 1] (1 : ℝ)) = 4 * H z := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        have hH : H z ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
        have hT : Tendsto (fun r => D (c r) z) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 (f z)) := by
          simpa only [hD1] using hptD z hz
        have hN : Tendsto (fun r => (‖D (c r) z‖₊ : ℝ≥0∞)) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 (‖f z‖₊ : ℝ≥0∞)) :=
          ((ENNReal.continuous_coe.comp continuous_nnnorm).tendsto _).comp hT
        have hGt : Tendsto (fun r => G r z) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 (H z)) :=
          ENNReal.Tendsto.mul_const (((ENNReal.continuous_pow 2).tendsto _).comp hN) (Or.inr ENNReal.ofReal_ne_top)
        have hFt : Tendsto (fun r => F r z) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 0) := by
          have h1 : Tendsto (fun r => D (c r) z - D 1 z) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 0) := by
            simpa using (hptD z hz).sub_const (D 1 z)
          have h2 := ((ENNReal.continuous_coe.comp continuous_nnnorm).tendsto (0 : ℂ)).comp h1
          simpa using ENNReal.Tendsto.mul_const (b := w z) (((ENNReal.continuous_pow 2).tendsto _).comp h2) (Or.inr ENNReal.ofReal_ne_top)
        have hsum : Tendsto (fun r => 2 * G r z + 2 * H z) (𝓝[Icc 0 1] (1 : ℝ)) (𝓝 (2 * H z + 2 * H z)) :=
          (ENNReal.Tendsto.const_mul hGt (Or.inr (by norm_num))).add tendsto_const_nhds
        have hg := ENNReal.Tendsto.sub hsum hFt (Or.inr ENNReal.zero_ne_top)
        rw [tsub_zero] at hg
        rw [hg.liminf_eq]
        ring
      rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ (by norm_num)]
    have hfatou := lintegral_liminf_le' (μ := volume.restrict unitDisc) (u := 𝓝[Icc 0 1] (1 : ℝ)) hgm
    rw [hliminf] at hfatou
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεA : 4 * A ≤ ε
    · exact Eventually.of_forall fun r => (hFint r).trans hεA
    push_neg at hεA
    have h4A : 4 * A ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hAfin
    have hlt : 4 * A - ε < liminf (fun r => ∫⁻ z in unitDisc, g r z) (𝓝[Icc 0 1] (1 : ℝ)) :=
      lt_of_lt_of_le (ENNReal.sub_lt_self h4A (ne_bot_of_gt hεA) hε.ne') hfatou
    filter_upwards [eventually_lt_of_lt_liminf hlt] with r hr
    by_contra hcon
    push_neg at hcon
    have := (hr.trans_le (hgint r)).trans_le (tsub_le_tsub_left hcon.le _)
    exact lt_irrefl _ this

/-- Continuity of the dilation path in `A₂(𝔻)` on `[0, 1]`. -/
theorem t31_dilate_continuous {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) :
    ContinuousOn (fun r : ℝ => toA2 unitDisc (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z))) (Icc 0 1) := by
  intro r₀ hr₀
  unfold ContinuousWithinAt
  rw [tendsto_iff_edist_tendsto_0]
  have hcongr : (fun r : ℝ => edist (toA2 unitDisc (fun z => (r : ℂ) ^ 2 * f ((r : ℂ) * z)))
      (toA2 unitDisc (fun z => (r₀ : ℂ) ^ 2 * f ((r₀ : ℂ) * z)))) =ᶠ[𝓝[Icc 0 1] r₀]
      fun r => (∫⁻ z in unitDisc,
        (‖(r : ℂ) ^ 2 * f ((r : ℂ) * z) - (r₀ : ℂ) ^ 2 * f ((r₀ : ℂ) * z)‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (rho z)⁻¹) ^ (1 / 2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [t31_edist_toA2 (t31_dilate_mem_A2 hf hr.1 hr.2) (t31_dilate_mem_A2 hf hr₀.1 hr₀.2)]
    rfl
  refine Tendsto.congr' hcongr.symm ?_
  have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp
    (t31_dilate_lintegral_tendsto hf hr₀)
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h

/-- The inclusion `A₂(𝔻) → A∞(𝔻)` is continuous for the Hilbert manifold topology (TT:1872). -/
theorem t31_A2toAInf_continuous : @Continuous _ _ _ hilbertTopologyA A2toAInf := by
  rw [continuous_iff_coinduced_le]
  have h : (fun ψ : A2 unitDisc => (0 : AInf unitDisc) + A2toAInf ψ) = A2toAInf := by
    funext ψ; exact zero_add _
  calc TopologicalSpace.coinduced A2toAInf inferInstance
      = TopologicalSpace.coinduced (fun ψ : A2 unitDisc => (0 : AInf unitDisc) + A2toAInf ψ)
          inferInstance := by rw [h]
    _ ≤ hilbertTopologyA :=
      le_iSup (fun φ : AInf unitDisc =>
        TopologicalSpace.coinduced (fun ψ : A2 unitDisc => φ + A2toAInf ψ) inferInstance) 0

/-- The zero element of `A₂(𝔻)` is the class of any function vanishing on `𝔻`. -/
theorem t31_toA2_zero {g : ℂ → ℂ} (hg : EqOn g 0 unitDisc) : toA2 unitDisc g = 0 := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  have hgA : g ∈ A2fun unitDisc := by
    refine ⟨(differentiableOn_const (0 : ℂ)).congr (fun z hz => hg hz), ?_⟩
    rw [normA2_congr (D := unitDisc) measurableSet_ball hg]
    simp [normA2]
  apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
  intro z hz
  rw [toA2_spec (D := unitDisc) isOpen_ball hcircle hgA hz, hg hz]
  have h0 := A2.toFun_eqOn isOpen_ball hcircle (0 : A2 unitDisc) (ψ := fun _ => (0 : ℂ))
    (differentiableOn_const _) (by
      change ((0 : A2 unitDisc) : Lp ℂ 2 (rhoInvMeasure unitDisc)) =ᵐ[_] _
      exact Lp.coeFn_zero _ _ _)
  exact (h0 hz).symm

/-- **Theorem 3.1** (TT:1906). `β(T(1)) ∩ A₂(𝔻)` is connected in the Hilbert manifold topology of `A∞(𝔻)`. -/
theorem t31_thm_3_1 :
    @IsConnected _ hilbertTopologyA (range bers ∩ {φ | AInf.toFun φ ∈ A2fun unitDisc}) := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)
  let U : Set (A2 unitDisc) := {ψ | A2toAInf ψ ∈ range bers}
  let γ : A2 unitDisc → ℝ → A2 unitDisc := fun ψ r =>
    toA2 unitDisc (fun z => (r : ℂ) ^ 2 * A2.toFun ψ ((r : ℂ) * z))
  have hγ0 : ∀ ψ, γ ψ 0 = 0 := fun ψ => t31_toA2_zero (fun z _ => by simp)
  have hγ1 : ∀ ψ, γ ψ 1 = ψ := by
    intro ψ
    have h : (fun z => ((1 : ℝ) : ℂ) ^ 2 * A2.toFun ψ (((1 : ℝ) : ℂ) * z)) = A2.toFun ψ := by
      funext z; simp
    change toA2 unitDisc _ = ψ
    rw [h]
    exact toA2_toFun isOpen_ball hcircle ψ
  have hzeroU : (0 : A2 unitDisc) ∈ U := by
    refine ⟨Phi ⟨0, mem_ball_self one_pos⟩, ?_⟩
    rw [c32_bers_origin, A2toAInf_zero]
  have hγU : ∀ ψ ∈ U, ∀ r ∈ Icc (0 : ℝ) 1, γ ψ r ∈ U := by
    intro ψ hψ r hr
    rcases hr.1.eq_or_lt with h0 | h0
    · rw [← h0, hγ0]; exact hzeroU
    obtain ⟨p, hp⟩ := hψ
    obtain ⟨ν, hν⟩ := t31_bersPhi_dilate (Quotient.out p : LinfStarBall) h0 hr.2
    refine ⟨Phi ν, ?_⟩
    rw [bers_Phi]
    apply AInf.ext_toFun_disc
    intro z hz
    have hrz : (r : ℂ) * z ∈ unitDisc := by
      simp only [unitDisc, mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h0]
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      nlinarith [norm_nonneg z, hr.2]
    have hmem := t31_dilate_mem_A2 (A2.toFun_mem ψ) hr.1 hr.2
    rw [hν z hz, (A2toAInf_bounded.2 _).2 z hz,
      show A2.toFun (γ ψ r) z = _ from toA2_spec (D := unitDisc) isOpen_ball hcircle hmem hz]
    congr 1
    have hb : bers p = bersPhi (Quotient.out p : LinfStarBall) := rfl
    rw [← hb, hp, (A2toAInf_bounded.2 ψ).2 _ hrz]
  have hUeq : U = ⋃₀ ((fun ψ => γ ψ '' Icc (0 : ℝ) 1) '' U) := by
    ext ψ
    constructor
    · intro hψ
      exact ⟨γ ψ '' Icc 0 1, ⟨ψ, hψ, rfl⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1 ψ⟩⟩
    · rintro ⟨s, ⟨χ, hχ, rfl⟩, ⟨r, hr, rfl⟩⟩
      exact hγU χ hχ r hr
  have hUconn : IsConnected U := by
    refine ⟨⟨0, hzeroU⟩, ?_⟩
    rw [hUeq]
    apply isPreconnected_sUnion 0
    · rintro s ⟨ψ, -, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0 ψ⟩
    · rintro s ⟨ψ, -, rfl⟩
      exact isPreconnected_Icc.image _ (t31_dilate_continuous (A2.toFun_mem ψ))
  have himg : A2toAInf '' U = range bers ∩ {φ | AInf.toFun φ ∈ A2fun unitDisc} := by
    ext φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      refine ⟨hψ, ?_⟩
      have : A2toAInf ψ ∈ range A2toAInf := ⟨ψ, rfl⟩
      rwa [A2toAInf_range] at this
    · rintro ⟨hb, hA⟩
      have : φ ∈ range A2toAInf := by rw [A2toAInf_range]; exact hA
      obtain ⟨ψ, rfl⟩ := this
      exact ⟨ψ, hb, rfl⟩
  rw [← himg]
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  exact hUconn.image A2toAInf t31_A2toAInf_continuous.continuousOn

/-- **Theorem 3.1** (TT:1906). `β(T(1)) ∩ A₂(𝔻)` is connected in the Hilbert manifold topology of `A∞(𝔻)`. -/
theorem thm_3_1 : @IsConnected _ hilbertTopologyA (range bers ∩ {φ | AInf.toFun φ ∈ A2fun unitDisc}) :=
  t31_thm_3_1

end TakhtajanTeo
