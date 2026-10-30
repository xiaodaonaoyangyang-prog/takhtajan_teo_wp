import TakhtajanTeo.Ch1.CauchyMorreyFour
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo

def mp_unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure mp_unitMeasure := by
  constructor
  simp [mp_unitMeasure, Measure.restrict_apply_univ, Real.volume_Icc]

theorem mp_integral_norm_four {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → E}
    (hf : Integrable f μ) (hf4 : Integrable (fun z => ‖f z‖ ^ 4) μ) :
    ‖∫ z, f z ∂μ‖ ^ 4 ≤ ∫ z, ‖f z‖ ^ 4 ∂μ := by
  have hconv : ConvexOn ℝ univ (fun z : E => ‖z‖ ^ 4) :=
    convexOn_univ_norm.pow (fun z _ => norm_nonneg z) 4
  exact hconv.map_integral_le (continuous_norm.pow 4).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hf hf4

/-- Pairwise fourth-power Poincare estimate on the unit interval, obtained
from FTC and Jensen. It applies to each coordinate slice of a square. -/
theorem mp_unit_pair_four {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    ‖f x - f y‖ ^ 4 ≤ ∫ t, ‖deriv f t‖ ^ 4 ∂mp_unitMeasure := by
  have hd : Continuous (deriv f) := hf.continuous_deriv_one
  have hFTC : (∫ t in y..x, deriv f t) = f x - f y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt) (hd.intervalIntegrable _ _)
  have hnorm : ‖f x - f y‖ ≤ ∫ t, ‖deriv f t‖ ∂mp_unitMeasure := by
    rw [← hFTC]
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
    exact setIntegral_mono_set hd.norm.integrableOn_Icc
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ hz => (uIcc_subset_Icc hy hx) (uIoc_subset_uIcc hz))
  have hJ := mp_integral_norm_four (μ := mp_unitMeasure)
    (f := fun t => ‖deriv f t‖) hd.norm.integrableOn_Icc
    (hd.norm.norm.pow 4).integrableOn_Icc
  have hnonneg : 0 ≤ ∫ t, ‖deriv f t‖ ∂mp_unitMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_norm] at hJ
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 4).trans hJ

/-- Fourth-power Poincare inequality with the mean as constant. -/
theorem mp_unit_poincare_four {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    ∫ x, ‖f x - ∫ y, f y ∂mp_unitMeasure‖ ^ 4 ∂mp_unitMeasure ≤
      ∫ t, ‖deriv f t‖ ^ 4 ∂mp_unitMeasure := by
  have hfi : Integrable f mp_unitMeasure := hf.continuous.integrableOn_Icc
  have hpoint : ∀ x ∈ Icc 0 1,
      ‖f x - ∫ y, f y ∂mp_unitMeasure‖ ^ 4 ≤
        ∫ t, ‖deriv f t‖ ^ 4 ∂mp_unitMeasure := by
    intro x hx
    have hc : Continuous (fun y => f x - f y) := continuous_const.sub hf.continuous
    have hJ := mp_integral_norm_four (μ := mp_unitMeasure)
      hc.integrableOn_Icc (hc.norm.pow 4).integrableOn_Icc
    rw [integral_sub (integrable_const _) hfi, integral_const, probReal_univ, one_smul] at hJ
    refine hJ.trans ?_
    calc (∫ y, ‖f x - f y‖ ^ 4 ∂mp_unitMeasure) ≤
        ∫ _y : ℝ, (∫ t, ‖deriv f t‖ ^ 4 ∂mp_unitMeasure) ∂mp_unitMeasure := by
          apply integral_mono_ae (hc.norm.pow 4).integrableOn_Icc (integrable_const _)
          filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
          exact mp_unit_pair_four hf hx hy
      _ = _ := by simp
  have hc : Continuous (fun x => ‖f x - ∫ y, f y ∂mp_unitMeasure‖ ^ 4) :=
    (hf.continuous.sub continuous_const).norm.pow 4
  calc (∫ x, ‖f x - ∫ y, f y ∂mp_unitMeasure‖ ^ 4 ∂mp_unitMeasure) ≤
      ∫ _x : ℝ, (∫ t, ‖deriv f t‖ ^ 4 ∂mp_unitMeasure) ∂mp_unitMeasure := by
        apply integral_mono_ae hc.integrableOn_Icc (integrable_const _)
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
        exact hpoint x hx
    _ = _ := by simp

def mp_unitSquare : Set (ℝ × ℝ) := (Icc 0 1) ×ˢ (Icc 0 1)

def mp_squareMeasure : Measure (ℝ × ℝ) := mp_unitMeasure.prod mp_unitMeasure

instance : IsProbabilityMeasure mp_squareMeasure := by
  dsimp [mp_squareMeasure]
  infer_instance

theorem mp_square_integrable {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) : Integrable f mp_squareMeasure := by
  change Integrable f ((volume.restrict (Icc 0 1)).prod (volume.restrict (Icc 0 1)))
  rw [Measure.prod_restrict]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem mp_ae_mem_square : ∀ᵐ p ∂mp_squareMeasure, p ∈ mp_unitSquare := by
  change ∀ᵐ p ∂(volume.restrict (Icc 0 1)).prod (volume.restrict (Icc 0 1)),
    p ∈ (Icc 0 1) ×ˢ (Icc 0 1)
  rw [Measure.prod_restrict]
  exact self_mem_ae_restrict (measurableSet_Icc.prod measurableSet_Icc)

theorem mp_square_integral_fst {H : ℝ → ℝ} (hH : Integrable H mp_unitMeasure) :
    ∫ p, H p.1 ∂mp_squareMeasure = ∫ x, H x ∂mp_unitMeasure := by
  rw [mp_squareMeasure, integral_prod _ (hH.comp_fst mp_unitMeasure)]
  simp

theorem mp_square_integral_snd {H : ℝ → ℝ} (hH : Integrable H mp_unitMeasure) :
    ∫ p, H p.2 ∂mp_squareMeasure = ∫ y, H y ∂mp_unitMeasure := by
  rw [mp_squareMeasure, integral_prod _ (hH.comp_snd mp_unitMeasure)]
  simp

theorem mp_norm_sub_four_le (a b c : ℂ) :
    ‖a - c‖ ^ 4 ≤ 8 * ‖a - b‖ ^ 4 + 8 * ‖b - c‖ ^ 4 := by
  have hnorm : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a - b) (b - c)
  refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 4).trans ?_
  have hpoly : 0 ≤ (‖a - b‖ - ‖b - c‖) ^ 2 *
      (7 * ‖a - b‖ ^ 2 + 10 * ‖a - b‖ * ‖b - c‖ + 7 * ‖b - c‖ ^ 2) := by positivity
  nlinarith only [hpoly]

/-- The two-coordinate averaging step. The path bounds are fourth moments of
the one-dimensional derivative estimates, not bounds on pointwise derivatives. -/
theorem mp_square_mean_four {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    {H V : ℝ → ℝ} (hH : Integrable H mp_unitMeasure) (hV : Integrable V mp_unitMeasure)
    (hpair : ∀ p ∈ mp_unitSquare, ∀ q ∈ mp_unitSquare,
      ‖f p - f q‖ ^ 4 ≤ 8 * H p.2 + 8 * V q.1) :
    ∫ p, ‖f p - ∫ q, f q ∂mp_squareMeasure‖ ^ 4 ∂mp_squareMeasure ≤
      8 * (∫ y, H y ∂mp_unitMeasure) + 8 * (∫ x, V x ∂mp_unitMeasure) := by
  have hfi := mp_square_integrable hf
  have hpoint : ∀ p ∈ mp_unitSquare,
      ‖f p - ∫ q, f q ∂mp_squareMeasure‖ ^ 4 ≤
        8 * H p.2 + 8 * (∫ x, V x ∂mp_unitMeasure) := by
    intro p hp
    have hdiff : Continuous (fun q => f p - f q) := continuous_const.sub hf
    have hJ := mp_integral_norm_four (mp_square_integrable hdiff)
      (mp_square_integrable (hdiff.norm.pow 4))
    rw [integral_sub (integrable_const _) hfi, integral_const, probReal_univ, one_smul] at hJ
    have hupper : Integrable (fun q : ℝ × ℝ => 8 * H p.2 + 8 * V q.1) mp_squareMeasure :=
      (integrable_const _).add ((hV.comp_fst mp_unitMeasure).const_mul 8)
    refine hJ.trans ((integral_mono_ae (mp_square_integrable (hdiff.norm.pow 4)) hupper
      (mp_ae_mem_square.mono fun q hq => hpair p hp q hq)).trans_eq ?_)
    have hVfst : Integrable (fun q : ℝ × ℝ => 8 * V q.1) mp_squareMeasure :=
      (hV.comp_fst mp_unitMeasure).const_mul 8
    rw [integral_add (integrable_const _) hVfst]
    simp only [integral_const_mul, mp_square_integral_fst hV,
      integral_const, probReal_univ, one_smul]
  have hupper : Integrable (fun p : ℝ × ℝ =>
      8 * H p.2 + 8 * (∫ x, V x ∂mp_unitMeasure)) mp_squareMeasure :=
    ((hH.comp_snd mp_unitMeasure).const_mul 8).add (integrable_const _)
  have hcont : Continuous (fun p => ‖f p - ∫ q, f q ∂mp_squareMeasure‖ ^ 4) :=
    (hf.sub continuous_const).norm.pow 4
  refine (integral_mono_ae (mp_square_integrable hcont) hupper
    (mp_ae_mem_square.mono fun p hp => hpoint p hp)).trans_eq ?_
  have hHsnd : Integrable (fun p : ℝ × ℝ => 8 * H p.2) mp_squareMeasure :=
    (hH.comp_snd mp_unitMeasure).const_mul 8
  rw [integral_add hHsnd (integrable_const _)]
  simp only [integral_const_mul, mp_square_integral_snd hH,
    integral_const, probReal_univ, one_smul]

/-- Unconditional two-dimensional Poincare inequality on the unit square, in
fourth-moment form. Its constant is numerical and independent of the function. -/
theorem mp_square_poincare_four {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    ∫ p, ‖f p - ∫ q, f q ∂mp_squareMeasure‖ ^ 4 ∂mp_squareMeasure ≤
      8 * (∫ p, ‖fderiv ℝ f p (1, 0)‖ ^ 4 ∂mp_squareMeasure) +
        8 * (∫ p, ‖fderiv ℝ f p (0, 1)‖ ^ 4 ∂mp_squareMeasure) := by
  let H : ℝ → ℝ := fun y => ∫ x, ‖fderiv ℝ f (x, y) (1, 0)‖ ^ 4 ∂mp_unitMeasure
  let V : ℝ → ℝ := fun x => ∫ y, ‖fderiv ℝ f (x, y) (0, 1)‖ ^ 4 ∂mp_unitMeasure
  have hdx : Continuous (fun p => ‖fderiv ℝ f p (1, 0)‖ ^ 4) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 4
  have hdy : Continuous (fun p => ‖fderiv ℝ f p (0, 1)‖ ^ 4) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 4
  have hH : Continuous H := by
    exact continuous_parametric_integral_of_continuous
      (f := fun y x : ℝ => ‖fderiv ℝ f (x, y) (1, 0)‖ ^ 4)
      (hdx.comp continuous_swap) isCompact_Icc
  have hV : Continuous V := by
    exact continuous_parametric_integral_of_continuous
      (f := fun x y : ℝ => ‖fderiv ℝ f (x, y) (0, 1)‖ ^ 4) hdy isCompact_Icc
  have hsx : ∀ y, ContDiff ℝ 1 (fun t => f (t, y)) :=
    fun y => hf.comp (contDiff_id.prodMk contDiff_const)
  have hsy : ∀ x, ContDiff ℝ 1 (fun t => f (x, t)) :=
    fun x => hf.comp (contDiff_const.prodMk contDiff_id)
  have hex : ∀ x y, deriv (fun t => f (t, y)) x = fderiv ℝ f (x, y) (1, 0) := by
    intro x y
    exact ((hf.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  have hey : ∀ x y, deriv (fun t => f (x, t)) y = fderiv ℝ f (x, y) (0, 1) := by
    intro x y
    exact ((hf.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv
  have hpair : ∀ p ∈ mp_unitSquare, ∀ q ∈ mp_unitSquare,
      ‖f p - f q‖ ^ 4 ≤ 8 * H p.2 + 8 * V q.1 := by
    intro p hp q hq
    have hx := mp_unit_pair_four (hsx p.2) hp.1 hq.1
    have hy := mp_unit_pair_four (hsy q.1) hp.2 hq.2
    simp only [hex] at hx
    simp only [hey] at hy
    have hb := mp_norm_sub_four_le (f p) (f (q.1, p.2)) (f q)
    dsimp only [H, V]
    linarith
  have h := mp_square_mean_four hf.continuous hH.integrableOn_Icc hV.integrableOn_Icc hpair
  have hHeq : (∫ y, H y ∂mp_unitMeasure) =
      ∫ p, ‖fderiv ℝ f p (1, 0)‖ ^ 4 ∂mp_squareMeasure := by
    exact (integral_prod_symm _ (mp_square_integrable hdx)).symm
  have hVeq : (∫ x, V x ∂mp_unitMeasure) =
      ∫ p, ‖fderiv ℝ f p (0, 1)‖ ^ 4 ∂mp_squareMeasure := by
    exact (integral_prod _ (mp_square_integrable hdy)).symm
  rwa [hHeq, hVeq] at h

theorem mp_l4_fourth_power {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 4 μ).toReal ^ 4 = ∫ z, ‖f z‖ ^ 4 ∂μ := by
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [show ∀ a : ℝ, a ^ (4 : ℝ) = a ^ (4 : ℕ) from
    fun a => Real.rpow_natCast a 4]
  have hN : 0 ≤ ∫ z, ‖f z‖ ^ (4 : ℕ) ∂μ := integral_nonneg fun z =>
    pow_nonneg (norm_nonneg (f z)) 4
  have hid := (Real.rpow_mul hN (1 / 4 : ℝ) (4 : ℝ)).symm
  norm_num at hid
  exact hid

theorem mp_fourth_le_two_sum {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4) : x ≤ 2 * (a + b) := by
  apply (pow_le_pow_iff_left₀ hx (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  have h1 := pow_le_pow_left₀ ha (le_add_of_nonneg_right hb) 4
  have h2 := pow_le_pow_left₀ hb (le_add_of_nonneg_left ha) 4
  nlinarith

/-- The L4 Poincare estimate on the unit square, with an explicit constant 2. -/
theorem mp_square_poincare_l4 {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    (eLpNorm (fun p => f p - ∫ q, f q ∂mp_squareMeasure) 4 mp_squareMeasure).toReal ≤
      2 * ((eLpNorm (fun p => fderiv ℝ f p (1, 0)) 4 mp_squareMeasure).toReal +
        (eLpNorm (fun p => fderiv ℝ f p (0, 1)) 4 mp_squareMeasure).toReal) := by
  have h := mp_square_poincare_four hf
  have hc : Continuous (fun p => f p - ∫ q, f q ∂mp_squareMeasure) :=
    hf.continuous.sub continuous_const
  have hx : Continuous (fun p => fderiv ℝ f p (1, 0)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hy : Continuous (fun p => fderiv ℝ f p (0, 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [← mp_l4_fourth_power hc.aestronglyMeasurable,
    ← mp_l4_fourth_power hx.aestronglyMeasurable,
    ← mp_l4_fourth_power hy.aestronglyMeasurable] at h
  exact mp_fourth_le_two_sum ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg h

end TakhtajanTeo

