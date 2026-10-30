import TakhtajanTeo.Ch1.HarmonicKernelIntegrability
import TakhtajanTeo.Ch1.HarmonicWeightedMoments

/-! Abel-damped kernels and dominated convergence for the resolvent identity (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_abel_denominator_bound {q : ℂ} (hq : ‖q‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖1 - q‖ ≤ 2 * ‖1 - (t : ℂ) * q‖ := by
  have htq : ‖(t : ℂ) * q‖ = t * ‖q‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hrev := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * q)
  rw [norm_one, htq] at hrev
  have hsmall : 1 - t ≤ ‖1 - (t : ℂ) * q‖ := by
    have hm := mul_le_mul_of_nonneg_left hq.le ht0
    nlinarith
  have hreal : ‖(t : ℂ) - 1‖ = 1 - t := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : t - 1 ≤ 0)]
    ring
  have he : (1 : ℂ) - q = (1 - (t : ℂ) * q) + ((t : ℂ) - 1) * q := by ring
  rw [he]
  have hs := norm_add_le (1 - (t : ℂ) * q) (((t : ℂ) - 1) * q)
  rw [norm_mul, hreal] at hs
  have hm := mul_le_mul_of_nonneg_left hq.le (by linarith : 0 ≤ 1 - t)
  nlinarith

theorem wp_abel_cauchy_bound {q : ℂ} (hq : ‖q‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - (t : ℂ) * q)⁻¹‖ ≤ 2 * ‖(1 - q)⁻¹‖ := by
  have hq0 : (1 : ℂ) - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    rw [← he, norm_one] at hq
    exact lt_irrefl _ hq
  have htq : ‖(t : ℂ) * q‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg q) ht1) hq
  have htq0 : (1 : ℂ) - (t : ℂ) * q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    rw [← he, norm_one] at htq
    exact lt_irrefl _ htq
  have h := (div_le_div_iff₀ (norm_pos_iff.mpr htq0) (norm_pos_iff.mpr hq0)).mpr
    (show (1 : ℝ) * ‖1 - q‖ ≤ 2 * ‖1 - (t : ℂ) * q‖ by
      simpa only [one_mul] using wp_abel_denominator_bound hq ht0 ht1)
  simpa only [norm_inv, one_div, div_eq_mul_inv, one_mul] using h

theorem wp_abel_double_kernel_bound {q : ℂ} (hq : ‖q‖ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((1 - (t : ℂ) * q)⁻¹) ^ 2 + (1 - (t : ℂ) * q)⁻¹‖ ≤
      4 * ‖(1 - q)⁻¹‖ ^ 2 + 2 * ‖(1 - q)⁻¹‖ := by
  have h := wp_abel_cauchy_bound hq ht0 ht1
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hs := norm_add_le (((1 - (t : ℂ) * q)⁻¹) ^ 2) ((1 - (t : ℂ) * q)⁻¹)
  rw [norm_pow] at hs
  nlinarith

theorem wp_weighted_abel_integral_tendsto {f g : ℂ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hbf : ∀ u ∈ unitDisc, ‖f u‖ ≤ M) (hbg : ∀ v ∈ unitDisc, ‖g v‖ ≤ N) :
    Tendsto (fun t : ℝ => ∫ p : ℂ × ℂ,
      f p.1 * g p.2 * (((1 - (t : ℂ) * (p.1 * conj p.2))⁻¹) ^ 2 +
        (1 - (t : ℂ) * (p.1 * conj p.2))⁻¹)
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)))
      (𝓝[<] 1) (𝓝 (∫ p : ℂ × ℂ,
        f p.1 * g p.2 * (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)
        ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)))) := by
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbf 0 hzero)
  have hN : 0 ≤ N := (norm_nonneg _).trans (hbg 0 hzero)
  let B : ℂ × ℂ → ℝ := fun p => M * N *
    (4 * ‖(1 - p.1 * conj p.2)⁻¹‖ ^ 2 + 2 * ‖(1 - p.1 * conj p.2)⁻¹‖)
  have hbi : Integrable B ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
    ((wp_cauchy_kernel_double_integrable.const_mul 4).add
      (wp_cauchy_kernel_complex_integrable.norm.const_mul 2)).const_mul (M * N)
  have hmem : ∀ᵐ p ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)),
      p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)
  have hq (p : ℂ × ℂ) (hp : p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc) : ‖p.1 * conj p.2‖ < 1 := by
    rw [norm_mul, norm_conj]
    exact lt_of_le_of_lt
      (mul_le_of_le_one_right (norm_nonneg p.1) (mem_ball_zero_iff.mp hp.2).le)
      (mem_ball_zero_iff.mp hp.1)
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hbi ?_
  · apply Filter.Eventually.of_forall
    intro t
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    filter_upwards [hmem] with p hp
    have hK := wp_abel_double_kernel_bound (hq p hp) ht.1.le ht.2.le
    have hfg : ‖f p.1‖ * ‖g p.2‖ ≤ M * N :=
      mul_le_mul (hbf _ hp.1) (hbg _ hp.2) (norm_nonneg _) hM
    simp only [norm_mul]
    exact mul_le_mul hfg hK (norm_nonneg _) (mul_nonneg hM hN)
  · filter_upwards [hmem] with p hp
    let q := p.1 * conj p.2
    have hden : (1 : ℂ) - q ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have h := hq p hp
      change ‖q‖ < 1 at h
      rw [← he, norm_one] at h
      exact lt_irrefl _ h
    have ht : ContinuousAt (fun t : ℝ => 1 - (t : ℂ) * q) 1 := by fun_prop
    have hInv := ht.inv₀ (by simpa only [Complex.ofReal_one, one_mul] using hden)
    have hT := ((hInv.pow 2).add hInv).const_mul (f p.1 * g p.2)
    simpa only [Pi.add_apply, Pi.pow_apply, Pi.inv_apply, q, Complex.ofReal_one, one_mul] using
      hT.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)

end TakhtajanTeo


