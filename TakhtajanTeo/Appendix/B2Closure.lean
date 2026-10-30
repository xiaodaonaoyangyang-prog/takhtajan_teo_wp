import TakhtajanTeo.Appendix.B3DiffSymmetric
import TakhtajanTeo.Appendix.PeriodCompactCharacterization
import TakhtajanTeo.Ch2.S1_SymmetricT
import TakhtajanTeo.Ch2.S1_Part5
import TakhtajanTeo.Ch1.FiberCircleOrientation
import TakhtajanTeo.Ch1.ComponentBlowupSchwarzian
import TakhtajanTeo.Ch1.QCVariation
import LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# Lemma B.2: `S` is the closure of `Möb(S¹)\Diff₊(S¹)` (Program G, 下属6)

Host of `lemma_B_2` (TT:6018–6044). No reflection across analytic curves is needed. Let `μ = out p`, `r = n/(n+1)`,
`R = 1/r`, and take the explicit coefficient `μ_n = 1_{|z| ≥ R} μ(r·)`.
- Model B: `z ↦ V(rz)` solves `extB μ_n`, so `𝒮(𝖿^{μ_n}) = 𝒮(f_n)` for the dilation `f_n = dilateF (fB μ) n`.
- Model A: `extA μ_n` vanishes on `r < |z| < R`, so `w_{μ_n}` is holomorphic and injective near `S¹`, hence a
  smooth circle diffeomorphism.
- `remark_B_9` gives `𝒮(f_n) → 𝒮(f)` in `A_∞(𝔻)`.
- Conversely, `Diff ⊆ S` (`b3d_diffT_subset`), and the weighted-vanishing description of `S` (`symmetricT_spec`) is
  closed in the sup norm.

* L1 `b2c_scaled`: the coefficient `μ_n`.
* L2 `b2c_bers_dilate`: `β(μ_n) = 𝒮(dilateF (fB μ) n)`.
* L3 `b2c_wA_holo`: `w_{μ_n}` is holomorphic and injective on a neighbourhood of `S¹`.
* L4 `b2c_circle_diffeo`: a sense-preserving circle homeomorphism holomorphic and injective near `S¹` is a smooth
  diffeomorphism.
* L5 `b2c_tendsto`: `𝒮(dilateF f n) → β([μ])` in `A_∞(𝔻)` for `[μ] ∈ S`.
* L6 `b2c_closed`: `S` is closed under Bers limits.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppB

/-- L1. The scaled cut-off coefficient `μ_n = 1_{|z| ≥ (n+1)/n} μ((n/(n+1)) z)`. -/
theorem b2c_scaled {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {n : ℕ} (hn : 1 ≤ n) :
    ∃ ν : LinfStar, ν ∈ LinfStarBall ∧ (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : ((n : ℝ) / (n + 1)) ≠ 0 := (div_pos hn0 (by positivity)).ne'
  have hrR : ((n : ℝ) / (n + 1)) * ((n + 1 : ℝ) / n) = 1 := by field_simp
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hS : MeasurableSet {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  have hrz (z : ℂ) : (((n : ℝ) / (n + 1) : ℂ) * z) = ((n : ℝ) / (n + 1)) • z := by
    rw [Complex.real_smul]
    push_cast
    ring
  -- `μ` extended by zero, composed with the dilation
  have hμ' : AEStronglyMeasurable (unitDiscExterior.indicator (μ : ℂ → ℂ)) volume :=
    (aestronglyMeasurable_indicator_iff hE).mpr (Lp.aestronglyMeasurable μ)
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℂ) hr0
  have hcomp : AEStronglyMeasurable
      (fun z : ℂ => unitDiscExterior.indicator (μ : ℂ → ℂ) (((n : ℝ) / (n + 1)) • z)) volume :=
    hμ'.comp_quasiMeasurePreserving hq
  have hbd : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖unitDiscExterior.indicator (μ : ℂ → ℂ) (((n : ℝ) / (n + 1)) • z)‖ ≤ ‖μ‖ := by
    have h0 : ∀ᵐ w ∂(volume : Measure ℂ), ‖unitDiscExterior.indicator (μ : ℂ → ℂ) w‖ ≤ ‖μ‖ := by
      have h := LinfStar_ae_norm_le μ
      rw [ae_restrict_iff' hE] at h
      filter_upwards [h] with w hw
      by_cases hw' : w ∈ unitDiscExterior
      · rw [indicator_of_mem hw']
        exact hw hw'
      · rw [indicator_of_notMem hw', norm_zero]
        exact norm_nonneg _
    exact hq.ae h0
  -- off the sphere of radius `(n+1)/n`, the stated function is the extended composition
  have hsph : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (0 : ℂ) ((n + 1 : ℝ) / n) := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) ((n + 1 : ℝ) / n))
    simpa using hz
  have hgeq : ({z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z)))
      =ᵐ[volume] {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator
        (fun z => unitDiscExterior.indicator (μ : ℂ → ℂ) (((n : ℝ) / (n + 1)) • z)) := by
    filter_upwards [hsph] with z hz
    by_cases h1 : ((n + 1 : ℝ) / n) ≤ ‖z‖
    · rw [indicator_of_mem (show z ∈ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from h1),
        indicator_of_mem (show z ∈ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from h1)]
      have hlt : ((n + 1 : ℝ) / n) < ‖z‖ := by
        refine lt_of_le_of_ne h1 fun h => hz ?_
        rw [mem_sphere_zero_iff_norm]
        exact h.symm
      have hmem : ((n : ℝ) / (n + 1)) • z ∈ unitDiscExterior := by
        show 1 < ‖((n : ℝ) / (n + 1)) • z‖
        rw [norm_smul, Real.norm_of_nonneg (div_pos hn0 (by positivity)).le]
        calc (1 : ℝ) = ((n : ℝ) / (n + 1)) * ((n + 1 : ℝ) / n) := hrR.symm
          _ < ((n : ℝ) / (n + 1)) * ‖z‖ := mul_lt_mul_of_pos_left hlt (div_pos hn0 (by positivity))
      show (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z) = unitDiscExterior.indicator (μ : ℂ → ℂ) (((n : ℝ) / (n + 1)) • z)
      rw [indicator_of_mem hmem, hrz]
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from h1),
        indicator_of_notMem (show z ∉ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from h1)]
  have hm : AEStronglyMeasurable
      ({z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z)))
      (volume.restrict unitDiscExterior) :=
    ((hcomp.indicator hS).congr hgeq.symm).restrict
  have hb : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖{z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z)) z‖ ≤ ‖μ‖ := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hgeq, hbd] with z hz hbz
    rw [hz]
    exact (norm_indicator_le_norm_self _ _).trans hbz
  have hL : MemLp ({z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator
      (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z))) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hm ‖μ‖ hb
  have hae := bc_toLinf_ae hL
  refine ⟨_, ?_, hae⟩
  apply mem_ball_zero_iff.mpr
  refine (bc_Lp_norm_le _ (norm_nonneg _) ?_).trans_lt (bc_norm_lt_one hμ)
  filter_upwards [hae, hb] with z hz hbz
  rw [hz]
  exact hbz

/-- The scaling `z ↦ s z`, `s = n/(n+1)`, as a real dilation. -/
theorem b2c_smul_eq (n : ℕ) (z : ℂ) : (((n : ℝ) / (n + 1) : ℂ) * z) = ((n : ℝ) / (n + 1)) • z := by
  rw [Complex.real_smul]
  push_cast
  ring

/-- The norm of `s z`. -/
theorem b2c_norm_smul (n : ℕ) (z : ℂ) : ‖(((n : ℝ) / (n + 1) : ℂ) * z)‖ = ((n : ℝ) / (n + 1)) * ‖z‖ := by
  rw [b2c_smul_eq, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- The pulled-back coefficient: `extB μ (s z) = extB ν z` almost everywhere. -/
theorem b2c_extB_ae {μ ν : LinfStar} {n : ℕ} (hn : 1 ≤ n)
    (hν : (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z))) :
    ∀ᵐ z, extB μ (((n : ℝ) / (n + 1) : ℂ) * z) = extB ν z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) / (n + 1) := div_pos hn0 (by positivity)
  have hr1 : (n : ℝ) / (n + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hrR : ((n : ℝ) / (n + 1)) * ((n + 1 : ℝ) / n) = 1 := by field_simp
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hν' := (ae_restrict_iff' hE).mp hν
  have hsph : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (0 : ℂ) ((n + 1 : ℝ) / n) := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (Measure.addHaar_sphere (volume : Measure ℂ) (0 : ℂ) ((n + 1 : ℝ) / n))
    simpa using hz
  filter_upwards [hν', hsph] with z hz hzs
  have hn' := b2c_norm_smul n z
  unfold extB
  by_cases h1 : z ∈ unitDiscExterior
  · rw [indicator_of_mem h1, hz h1]
    by_cases hR : ((n + 1 : ℝ) / n) ≤ ‖z‖
    · have hlt : ((n + 1 : ℝ) / n) < ‖z‖ := by
        refine lt_of_le_of_ne hR fun h => hzs ?_
        rw [mem_sphere_zero_iff_norm]
        exact h.symm
      have hm : (((n : ℝ) / (n + 1) : ℂ) * z) ∈ unitDiscExterior := by
        show 1 < ‖(((n : ℝ) / (n + 1) : ℂ) * z)‖
        rw [hn']
        calc (1 : ℝ) = ((n : ℝ) / (n + 1)) * ((n + 1 : ℝ) / n) := hrR.symm
          _ < ((n : ℝ) / (n + 1)) * ‖z‖ := mul_lt_mul_of_pos_left hlt hr0
      rw [indicator_of_mem hm, indicator_of_mem (show z ∈ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from hR)]
    · have hm : (((n : ℝ) / (n + 1) : ℂ) * z) ∉ unitDiscExterior := by
        show ¬ 1 < ‖(((n : ℝ) / (n + 1) : ℂ) * z)‖
        rw [hn', not_lt]
        calc ((n : ℝ) / (n + 1)) * ‖z‖ ≤ ((n : ℝ) / (n + 1)) * ((n + 1 : ℝ) / n) :=
              mul_le_mul_of_nonneg_left (not_le.mp hR).le hr0.le
          _ = 1 := hrR
      rw [indicator_of_notMem hm, indicator_of_notMem (show z ∉ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from hR)]
  · have hm : (((n : ℝ) / (n + 1) : ℂ) * z) ∉ unitDiscExterior := by
      show ¬ 1 < ‖(((n : ℝ) / (n + 1) : ℂ) * z)‖
      have h1' : ‖z‖ ≤ 1 := not_lt.mp h1
      rw [hn', not_lt]
      calc ((n : ℝ) / (n + 1)) * ‖z‖ ≤ 1 * 1 := mul_le_mul hr1.le h1' (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [indicator_of_notMem hm, indicator_of_notMem h1]

/-- L2. The Bers image of `μ_n` is the Schwarzian of the dilation of `𝖿^μ`. -/
theorem b2c_bers_dilate {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) {n : ℕ} (hn : 1 ≤ n) (hν0 : ν ∈ LinfStarBall)
    (hν : (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z))) :
    bersPhi ν = toAInf unitDisc (schwarzianHol (dilateF (fB μ) n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) / (n + 1) := div_pos hn0 (by positivity)
  have hr1 : (n : ℝ) / (n + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hs0 : (((n : ℝ) / (n + 1) : ℂ)) ≠ 0 := by
    have h := b2c_smul_eq n 1
    intro h0
    rw [h0, zero_mul, Complex.real_smul, mul_one] at h
    exact hr0.ne' (by exact_mod_cast h.symm)
  have hsD (z : ℂ) (hz : z ∈ unitDisc) : (((n : ℝ) / (n + 1) : ℂ) * z) ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [b2c_norm_smul]
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    calc ((n : ℝ) / (n + 1)) * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hr1.le (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hz'
  obtain ⟨hVN, hVd, hVi, hV0⟩ := QCV.qcv_W_props (bc_norm_lt_one hμ)
  obtain ⟨hWN, -, -, -⟩ := QCV.qcv_W_props (bc_norm_lt_one hν0)
  -- `V(s·)` is a quasiconformal solution of `extB ν`
  obtain ⟨K, hVK⟩ := hVN.1
  have hsc : IsConformalOnto (fun z : ℂ => ((n : ℝ) / (n + 1) : ℂ) * z) univ univ := by
    refine ⟨(by fun_prop : Differentiable ℂ fun z : ℂ => ((n : ℝ) / (n + 1) : ℂ) * z).differentiableOn,
      fun x _ y _ h => mul_left_cancel₀ hs0 h, ?_⟩
    refine eq_univ_of_forall fun w => ⟨w / ((n : ℝ) / (n + 1) : ℂ), mem_univ _, ?_⟩
    field_simp [hnC]
  have hGK := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hsc) hVK (subset_univ _)
  have hGs : (normalizedSolution (extB μ) ∘ fun z : ℂ => ((n : ℝ) / (n + 1) : ℂ) * z) '' univ = univ := by
    rw [image_comp, hsc.2.2]
    exact hVN.2.1
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℂ) hr0.ne'
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ (normalizedSolution (extB μ)) (((n : ℝ) / (n + 1) : ℂ) * z) := by
    have h := thm9_3_differentiable_ae hVK
    rw [Measure.restrict_univ] at h
    filter_upwards [hq.ae h] with z hz
    rw [b2c_smul_eq]
    exact hz
  have hchar : ∀ᵐ z, complexDilatation (normalizedSolution (extB μ)) (((n : ℝ) / (n + 1) : ℂ) * z) =
      extB μ (((n : ℝ) / (n + 1) : ℂ) * z) := by
    filter_upwards [hq.ae hVN.2.2.2.2] with z hz
    rw [b2c_smul_eq]
    exact hz
  have hd : ∀ᵐ z, complexDilatation (normalizedSolution (extB μ) ∘ fun z : ℂ => ((n : ℝ) / (n + 1) : ℂ) * z) z =
      extB ν z := by
    filter_upwards [hdiff, hchar, b2c_extB_ae hn hν] with z hz1 hz2 hz3
    have hderiv : deriv (fun z : ℂ => ((n : ℝ) / (n + 1) : ℂ) * z) z = ((n : ℝ) / (n + 1) : ℂ) := by
      simp
    rw [complexDilatation_comp_conformal_right (by fun_prop) (by rw [hderiv]; exact hs0) hz1, hz2, hz3, hderiv]
    have hc : conj (((n : ℝ) / (n + 1) : ℂ)) = ((n : ℝ) / (n + 1) : ℂ) := by
      rw [Complex.conj_eq_iff_real]
      exact ⟨(n : ℝ) / (n + 1), by push_cast; rfl⟩
    rw [hc, div_self hs0, mul_one]
  -- uniqueness of the normalized solution
  have hWe : normalizedSolution (extB ν) = fun t =>
      (normalizedSolution (extB μ) (0 + ((n : ℝ) / (n + 1) : ℂ) * t) - 0) /
        normalizedSolution (extB μ) (((n : ℝ) / (n + 1) : ℂ)) := by
    funext t
    rw [k24_normalize hWN hGK hGs hd t]
    simp only [Function.comp_apply, mul_zero, mul_one, zero_add, hV0, sub_zero]
  have hb : normalizedSolution (extB μ) (((n : ℝ) / (n + 1) : ℂ)) ≠ 0 := by
    intro h
    rw [← hV0] at h
    exact hs0 (hVi (mem_univ _) (mem_univ _) h)
  -- the Schwarzians on `𝔻`
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  have hS : EqOn (schwarzianHol (fB ν)) (schwarzianHol (dilateF (fB μ) n)) unitDisc := by
    intro z hz
    have hsz := hsD z hz
    have hsz' : (0 + ((n : ℝ) / (n + 1) : ℂ) * z) ∈ unitDisc := by rw [zero_add]; exact hsz
    have hVa : AnalyticAt ℂ (normalizedSolution (extB μ)) (0 + ((n : ℝ) / (n + 1) : ℂ) * z) :=
      hVd.analyticAt (isOpen_ball.mem_nhds hsz')
    have hVd' : deriv (normalizedSolution (extB μ)) (0 + ((n : ℝ) / (n + 1) : ℂ) * z) ≠ 0 :=
      deriv_ne_zero_of_injOn isOpen_ball hVd (hVi.mono (subset_univ _)) hsz'
    have hfa : AnalyticAt ℂ (fB μ) (0 + ((n : ℝ) / (n + 1) : ℂ) * z) := hfd.analyticAt (isOpen_ball.mem_nhds hsz')
    have hfd' : deriv (fB μ) (0 + ((n : ℝ) / (n + 1) : ℂ) * z) ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hfd hfi hsz'
    have hdil : dilateF (fB μ) n = fun t => (fB μ (0 + ((n : ℝ) / (n + 1) : ℂ) * t) - 0) / ((n : ℝ) / (n + 1) : ℂ) := by
      funext t
      unfold dilateF
      rw [zero_add, sub_zero, eq_div_iff hs0]
      push_cast
      field_simp [hnC]
    rw [QCV.qcv_schwarzian_fB_eq hν0 hz, hWe, cbs_affine_schwarzian hs0 hb hVa hVd', hdil,
      cbs_affine_schwarzian hs0 hs0 hfa hfd', zero_add, QCV.qcv_schwarzian_fB_eq hμ hsz]
  exact toAInf_congr_disc hS

/-- `extA ν` vanishes almost everywhere on the annulus `n/(n+1) < |z| < (n+1)/n`. -/
theorem b2c_extA_annulus {μ ν : LinfStar} {n : ℕ} (hn : 1 ≤ n)
    (hν : (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z))) :
    ∀ᵐ z, (n : ℝ) / (n + 1) < ‖z‖ ∧ ‖z‖ < (n + 1 : ℝ) / n → extA ν z = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) / (n + 1) := div_pos hn0 (by positivity)
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hν' := (ae_restrict_iff' hE).mp hν
  filter_upwards [hν', ae_refl hν'] with z h1 h2
  rintro ⟨hlo, hhi⟩
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlo
    linarith
  unfold extA
  by_cases hzE : 1 < ‖z‖
  · rw [if_pos hzE, h1 hzE, indicator_of_notMem]
    exact not_le.mpr hhi
  · by_cases hzD : ‖z‖ < 1
    · rw [if_neg hzE, if_pos hzD]
      have hrE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr (mem_ball_zero_iff.mpr hzD)
      have hrn : ‖refl z‖ < (n + 1 : ℝ) / n := by
        rw [norm_refl, show (n + 1 : ℝ) / n = ((n : ℝ) / (n + 1))⁻¹ by rw [inv_div]]
        exact (inv_lt_inv₀ (norm_pos_iff.mpr hz0) hr0).mpr hlo
      rw [h2 hrE, indicator_of_notMem (show refl z ∉ {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖} from not_le.mpr hrn), map_zero,
        zero_mul, zero_div]
    · rw [if_neg hzE, if_neg hzD]

/-- L3. `w_{μ_n}` is holomorphic and injective on a neighbourhood of `S¹`. -/
theorem b2c_wA_holo {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) {n : ℕ} (hn : 1 ≤ n) (hν0 : ν ∈ LinfStarBall)
    (hν : (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | ((n + 1 : ℝ) / n) ≤ ‖z‖}.indicator (fun z => (μ : ℂ → ℂ) (((n : ℝ) / (n + 1) : ℂ) * z))) :
    ∃ U : Set ℂ, IsOpen U ∧ unitCircle ⊆ U ∧ DifferentiableOn ℂ (wA ν) U ∧ InjOn (wA ν) U := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < (n : ℝ) / (n + 1) := div_pos hn0 (by positivity)
  have hr1 : (n : ℝ) / (n + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hR1 : 1 < (n + 1 : ℝ) / n := (one_lt_div hn0).mpr (by linarith)
  obtain ⟨a, b, c, d, W, hdet, hW, hform, -⟩ := bc_wA_form hν0
  obtain ⟨K, hK⟩ := hW.1
  have hWc : Continuous W := continuousOn_univ.mp hK.2.2.1.1
  have hWi : InjOn W univ := hK.2.2.1.2.1
  set A : Set ℂ := {z : ℂ | (n : ℝ) / (n + 1) < ‖z‖ ∧ ‖z‖ < (n + 1 : ℝ) / n} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAz : ∀ᵐ z ∂(volume.restrict A), complexDilatation W z = 0 := by
    rw [ae_restrict_iff' hAo.measurableSet]
    filter_upwards [hW.2.2.2.2, b2c_extA_annulus hn hν] with z hz1 hz2 hzA
    rw [hz1, hz2 hzA]
  have hWd : DifferentiableOn ℂ W A :=
    nx_differentiableOn_of_dilatation_zero (nx_isKQC_restrict hK hAo (subset_univ _)) hAz
  have hwf : wA ν = fun z => mobiusFn a b c d (W z) := funext hform
  refine ⟨A ∩ {z | c * W z + d ≠ 0}, hAo.inter (isOpen_ne_fun (by fun_prop) continuous_const), ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : ‖z‖ = 1 := hz
    refine ⟨⟨by rw [hz1]; exact hr1, by rw [hz1]; exact hR1⟩, ?_⟩
    intro hp
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hν0 hz1
    have ha : wA ν z = u := congrArg finPart he
    rw [hform, mobiusFn, show c * W z + d = 0 from hp, div_zero] at ha
    rw [← ha, norm_zero] at hu
    exact zero_ne_one hu
  · rw [hwf]
    intro z hz
    exact ((bc_mobiusFn_hasDerivAt hz.2).differentiableAt.comp z
      ((hWd z hz.1).differentiableAt (hAo.mem_nhds hz.1))).differentiableWithinAt
  · rw [hwf]
    intro x hx y hy h
    exact hWi (mem_univ _) (mem_univ _)
      (bc_mobiusFn_injOn hdet (V := {w | c * w + d ≠ 0}) (fun w hw => hw) hx.2 hy.2 h)

/-- L4. A sense-preserving circle homeomorphism that is holomorphic and injective near `S¹` is a smooth circle
diffeomorphism. -/
theorem b2c_circle_diffeo {γ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hS : unitCircle ⊆ U)
    (hd : DifferentiableOn ℂ γ U) (hi : InjOn γ U) (hsp : Pommerenke1992.IsSensePreservingCircleHomeo γ) :
    IsCircleDiffeo γ := by
  obtain ⟨u, hu, hmono, hper, he⟩ := hsp
  have hcU (t : ℝ) : exp (t * I) ∈ U := hS (show ‖exp (t * I)‖ = 1 from Complex.norm_exp_ofReal_mul_I t)
  -- the circle curve `t ↦ γ(e^{it})` is smooth
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => exp (t * I)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hq (t₀ : ℝ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => γ (exp (t * I))) t₀ := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) γ (exp (t₀ * I)) :=
      ((hd.contDiffOn hU).contDiffAt (hU.mem_nhds (hcU t₀))).restrict_scalars ℝ
    exact h1.comp t₀ hexp.contDiffAt
  -- near `t₀`, `u` is `u t₀` plus a branch of the argument
  have hloc (t₀ : ℝ) : u =ᶠ[𝓝 t₀] fun t => u t₀ + (log (γ (exp (t * I)) / γ (exp (t₀ * I)))).im := by
    have hc : ∀ᶠ t in 𝓝 t₀, |u t - u t₀| < π :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp [Real.pi_pos])
    filter_upwards [hc] with t ht
    have h1 := (abs_lt.mp ht).1
    have h2 := (abs_lt.mp ht).2
    have him : (((u t - u t₀ : ℝ) : ℂ) * I).im = u t - u t₀ := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have hl1 : -π < (((u t - u t₀ : ℝ) : ℂ) * I).im := by
      rw [him]
      linarith
    have hl2 : (((u t - u t₀ : ℝ) : ℂ) * I).im ≤ π := by
      rw [him]
      linarith
    rw [he t, he t₀, ← Complex.exp_sub, ← sub_mul,
      show ((u t : ℂ) - u t₀) * I = ((u t - u t₀ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.log_exp hl1 hl2, him]
    ring
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) u := contDiff_iff_contDiffAt.mpr fun t₀ => by
    have hden : γ (exp (t₀ * I)) ≠ 0 := by
      rw [he t₀]
      exact Complex.exp_ne_zero _
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => γ (exp (t * I)) / γ (exp (t₀ * I))) t₀ :=
      (hq t₀).div_const _
    have h1' : γ (exp (t₀ * I)) / γ (exp (t₀ * I)) ∈ slitPlane := by
      rw [div_self hden]
      simp [slitPlane]
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) log (γ (exp (t₀ * I)) / γ (exp (t₀ * I))) :=
      (Complex.contDiffAt_log h1').restrict_scalars ℝ
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => (log (γ (exp (t * I)) / γ (exp (t₀ * I)))).im) t₀ :=
      have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => log (γ (exp (t * I)) / γ (exp (t₀ * I)))) t₀ :=
        ContDiffAt.comp (g := log) t₀ h2 h1
      Complex.imCLM.contDiff.contDiffAt.comp t₀ h4
    exact (contDiffAt_const.add h3).congr_of_eventuallyEq (hloc t₀)
  refine ⟨u, hsmooth, fun t => ?_, hper, he⟩
  have hud : HasDerivAt u (deriv u t) t := ((hsmooth.differentiable (by simp)) t).hasDerivAt
  have h0 : 0 ≤ deriv u t := hud.nonneg_of_monotone hmono.monotone
  refine lt_of_le_of_ne h0 fun hz => ?_
  -- differentiate `γ(e^{it}) = e^{iu(t)}`
  have hg : HasDerivAt γ (deriv γ (exp (t * I))) (exp (t * I)) :=
    (hd.differentiableAt (hU.mem_nhds (hcU t))).hasDerivAt
  have hR := hg.comp t ((Complex.hasDerivAt_exp _).comp t ((hasDerivAt_id t).ofReal_comp.mul_const I))
  have hL := (Complex.hasDerivAt_exp _).comp t (hud.ofReal_comp.mul_const I)
  have hfun : (γ ∘ exp ∘ fun s : ℝ => ((id s : ℝ) : ℂ) * I) = (exp ∘ fun s : ℝ => ((u s : ℝ) : ℂ) * I) := by
    funext s
    exact he s
  rw [hfun] at hR
  have heq := hR.unique hL
  rw [← hz, Complex.ofReal_zero, zero_mul, mul_zero] at heq
  rcases mul_eq_zero.mp heq with h | h
  · exact deriv_ne_zero_of_injOn hU hd hi (hcU t) h
  · simp [Complex.exp_ne_zero] at h

/-- L5. For `[μ] ∈ S`, the Schwarzians of the dilations converge to `β([μ])` in `A_∞(𝔻)`. -/
theorem b2c_tendsto {p : T1} (hp : p ∈ symmetricT) :
    Tendsto (fun n => toAInf unitDisc (schwarzianHol (dilateF (fB ((Quotient.out p : LinfStarBall) : LinfStar)) n)))
      atTop (𝓝 (bers p)) := by
  have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have h9 := (remark_B_9 hp).1
  rw [e13_fsans_eq hμ] at h9
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
  have hf : IsUnivalentDisc (fB ((Quotient.out p : LinfStarBall) : LinfStar)) := ⟨hfd, hfi⟩
  have hF := (schwarzianHol_AInf_spec hfd hfi).1
  have hbers : bers p = toAInf unitDisc (schwarzianHol (fB ((Quotient.out p : LinfStarBall) : LinfStar))) := rfl
  have hev := (eventually_ge_atTop 1).and (h9.eventually (gt_mem_nhds zero_lt_one))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (by simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h9)
  filter_upwards [hev] with n hn
  obtain ⟨hn1, hlt⟩ := hn
  obtain ⟨hR, hdd, hdi⟩ := dilateF_extension hf hn1
  have hsub : unitDisc ⊆ ball (0 : ℂ) ((n + 1 : ℝ) / n) := ball_subset_ball hR.le
  have hD := (schwarzianHol_AInf_spec (hdd.mono hsub) (hdi.mono hsub)).1
  simp only [Function.comp_apply]
  refine (BoundedContinuousFunction.norm_le ENNReal.toReal_nonneg).mpr fun x => ?_
  obtain ⟨w, hw⟩ := x
  refine (le_of_eq (d2_AInf_norm (φ := toAInf unitDisc (schwarzianHol (dilateF (fB ((Quotient.out p : LinfStarBall) :
    LinfStar)) n)) - bers p) hw)).trans ?_
  rw [ctb_toFun_sub, Pi.sub_apply, hD w hw, hbers, hF w hw]
  exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_lt hlt)).mp
    (le_iSup₂ (f := fun z (_ : z ∈ unitDisc) => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 2 *
      ‖schwarzianHol (dilateF (fB ((Quotient.out p : LinfStarBall) : LinfStar)) n) z -
        schwarzianHol (fB ((Quotient.out p : LinfStarBall) : LinfStar)) z‖)) w hw)

/-- L6. `S` is closed under limits in the Bers embedding. -/
theorem b2c_closed {p : T1} {q : ℕ → T1} (hq : ∀ n, q n ∈ symmetricT)
    (h : Tendsto (fun n => bers (q n)) atTop (𝓝 (bers p))) : p ∈ symmetricT := by
  rw [symmetricT_spec.1 p, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := ((tendsto_iff_norm_sub_tendsto_zero.mp h).eventually (gt_mem_nhds (half_pos hε))).exists
  have hqk := (symmetricT_spec.1 (q k)).mp (hq k)
  have hD : ∀ᶠ z : ℂ in comap (fun z : ℂ => ‖z‖) (𝓝[<] 1), ‖z‖ < 1 :=
    Filter.preimage_mem_comap self_mem_nhdsWithin
  filter_upwards [Metric.tendsto_nhds.mp hqk (ε / 2) (half_pos hε), hD] with z hz1 hz2
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz2
  rw [dist_zero_right] at hz1 ⊢
  have hμp : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hμq : ((Quotient.out (q k) : LinfStarBall) : LinfStar) ∈ LinfStarBall :=
    (Quotient.out (q k) : LinfStarBall).2
  have hw : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [show ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) = (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)]
  have e := d2_AInf_norm (φ := bersPhi ((Quotient.out p : LinfStarBall) : LinfStar) -
    bersPhi ((Quotient.out (q k) : LinfStarBall) : LinfStar)) hzD
  rw [ctb_toFun_sub, Pi.sub_apply, (bersPhi_spec hμp).1 z hzD, (bersPhi_spec hμq).1 z hzD] at e
  have hdiff : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out p : LinfStarBall)) z -
      ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out (q k) : LinfStarBall)) z‖ ≤
        ‖bers (q k) - bers p‖ := by
    calc _ = ‖(bersPhi ((Quotient.out p : LinfStarBall) : LinfStar) -
          bersPhi ((Quotient.out (q k) : LinfStarBall) : LinfStar)).1 ⟨z, hzD⟩‖ := by
          rw [← mul_sub, norm_mul, hw, e]
      _ ≤ ‖bersPhi ((Quotient.out p : LinfStarBall) : LinfStar) -
          bersPhi ((Quotient.out (q k) : LinfStarBall) : LinfStar)‖ :=
          BoundedContinuousFunction.norm_coe_le_norm _ _
      _ = ‖bers (q k) - bers p‖ := norm_sub_rev _ _
  have htri := norm_sub_norm_le (((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out p : LinfStarBall)) z)
    (((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (fB (Quotient.out (q k) : LinfStarBall)) z)
  linarith

/-- **Lemma B.2** (TT:6018–6044). The closure of `Möb(S¹)\Diff₊(S¹)` in the Banach manifold topology of `T(1)` (through
the Bers embedding into `A_∞(𝔻)`) is `S`. -/
theorem b2c_lemma_B_2 (p : T1) :
    p ∈ symmetricT ↔ ∃ q : ℕ → T1, (∀ n, q n ∈ diffT) ∧ Tendsto (fun n => bers (q n)) atTop (𝓝 (bers p)) := by
  constructor
  · intro hp
    have hμ : ((Quotient.out p : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
    choose ν hν0 hν using fun n : ℕ => b2c_scaled hμ (Nat.le_add_left 1 n)
    refine ⟨fun n => Phi ⟨ν n, hν0 n⟩, fun n => ?_, ?_⟩
    · have hr : teichSetoid.r (Phi ⟨ν n, hν0 n⟩).out ⟨ν n, hν0 n⟩ := Quotient.mk_out (s := teichSetoid) _
      obtain ⟨U, hU, hS, hd, hi⟩ := b2c_wA_holo hμ (Nat.le_add_left 1 n) (hν0 n) (hν n)
      obtain ⟨u, hu, hpos, hp2, he⟩ := b2c_circle_diffeo hU hS hd hi (wA_circle_sensePreserving (hν0 n))
      show IsCircleDiffeo (wA ((Quotient.out (Phi ⟨ν n, hν0 n⟩) : LinfStarBall) : LinfStar))
      refine ⟨u, hu, hpos, hp2, fun t => ?_⟩
      have hc : exp (t * I) ∈ unitCircle := by
        show ‖exp (t * I)‖ = 1
        exact Complex.norm_exp_ofReal_mul_I t
      rw [hr (exp (t * I)) hc]
      exact he t
    · refine ((b2c_tendsto hp).comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp_apply]
      rw [bers_Phi]
      exact (b2c_bers_dilate hμ (Nat.le_add_left 1 n) (hν0 n) (hν n)).symm
  · rintro ⟨q, hq, ht⟩
    exact b2c_closed (fun n => b3d_diffT_subset (hq n)) ht

/-- **Lemma B.2** (TT:6018–6044). The closure of `Möb(S¹)\Diff₊(S¹)` in the Banach manifold topology of `T(1)` (through
the Bers embedding into `A_∞(𝔻)`) is `S`. -/
theorem lemma_B_2 (p : T1) :
    p ∈ symmetricT ↔ ∃ q : ℕ → T1, (∀ n, q n ∈ diffT) ∧ Tendsto (fun n => bers (q n)) atTop (𝓝 (bers p)) := by
  exact b2c_lemma_B_2 p

end AppB

end TakhtajanTeo
