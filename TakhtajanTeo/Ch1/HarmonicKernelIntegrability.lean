import TakhtajanTeo.Ch1.HarmonicDoubleKernel
import Mathlib.Analysis.PSeries

/-! Absolute double-kernel integrability from finite geometric energies and Fatou (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_integrable_of_uniform_integral_bound {X : Type*} [MeasurableSpace X]
    {m : Measure X} {P : ℕ → X → ℝ} {f : X → ℝ}
    (hi : ∀ n, Integrable (P n) m)
    (hl : ∀ᵐ x ∂m, Tendsto (fun n => P n x) atTop (𝓝 (f x)))
    {C : ℝ} (hb : ∀ n, (∫ x, ‖P n x‖ ∂m) ≤ C) : Integrable f m := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae _ (fun n => (hi n).aestronglyMeasurable) hl, ?_⟩
  have he : (∫⁻ x, ‖f x‖ₑ ∂m) = ∫⁻ x, liminf (fun n => ‖P n x‖ₑ) atTop ∂m := by
    apply lintegral_congr_ae
    filter_upwards [hl] with x hx
    exact hx.enorm.liminf_eq.symm
  have hF := lintegral_liminf_le' (μ := m) (u := atTop)
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.enorm)
  have hB (n : ℕ) : (∫⁻ x, ‖P n x‖ₑ ∂m) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlim : liminf (fun n => ∫⁻ x, ‖P n x‖ₑ ∂m) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Filter.Frequently.of_forall hB)
  exact lt_of_le_of_lt (he.trans_le (hF.trans hlim)) ENNReal.ofReal_lt_top

theorem wp_geometric_partial_kernel_area (N : ℕ) (v : ℂ) :
    (∫ u in unitDisc, ‖∑ n ∈ Finset.range N, (u * conj v) ^ n‖ ^ 2) =
      π * ∑ n ∈ Finset.range N, ‖v‖ ^ (2 * n) / (n + 1 : ℝ) := by
  have h := wp_scalarSeriesPolynomial_unweighted_area (fun n => (conj v) ^ n) N
  simpa only [wp_scalarSeriesPolynomial_eval, mul_pow, norm_pow, norm_conj,
    ← pow_mul, Nat.mul_comm, mul_comm] using h

theorem wp_geometric_partial_kernel_integrable (N : ℕ) :
    Integrable (fun p : ℂ × ℂ => ‖∑ n ∈ Finset.range N, (p.1 * conj p.2) ^ n‖ ^ 2)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hc : Continuous (fun p : ℂ × ℂ => ‖∑ n ∈ Finset.range N, (p.1 * conj p.2) ^ n‖ ^ 2) := by
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact (μ := volume)
    ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) 1))
  have hsub : unitDisc ×ˢ unitDisc ⊆ closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1 :=
    Set.prod_mono ball_subset_closedBall ball_subset_closedBall
  have h := hi.mono_set hsub
  rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h

theorem wp_geometric_partial_kernel_double_area (N : ℕ) :
    (∫ p : ℂ × ℂ, ‖∑ n ∈ Finset.range N, (p.1 * conj p.2) ^ n‖ ^ 2
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      π ^ 2 * ∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) ^ 2 := by
  rw [integral_prod_symm _ (wp_geometric_partial_kernel_integrable N)]
  simp_rw [wp_geometric_partial_kernel_area]
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [integral_div, wp_disk_unweighted_monomial]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  · intro n hn
    have hc : Continuous (fun v : ℂ => ‖v‖ ^ (2 * n) / (n + 1 : ℝ)) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      ball_subset_closedBall

theorem wp_cauchy_kernel_double_integrable :
    Integrable (fun p : ℂ × ℂ => ‖(1 - p.1 * conj p.2)⁻¹‖ ^ 2)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hs : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  refine wp_integrable_of_uniform_integral_bound (wp_geometric_partial_kernel_integrable) ?_
    (C := π ^ 2 * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) ?_
  · have hmem : ∀ᵐ p ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)),
        p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)
    filter_upwards [hmem] with p hp
    have hnorm : ‖p.1 * conj p.2‖ < 1 := by
      rw [norm_mul, norm_conj]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg p.1) (mem_ball_zero_iff.mp hp.2).le)
        (mem_ball_zero_iff.mp hp.1)
    have h := (hasSum_geometric_of_norm_lt_one hnorm).tendsto_sum_nat.norm.pow 2
    simpa only [one_div] using h
  · intro N
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
    rw [wp_geometric_partial_kernel_double_area]
    exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum (Finset.range N) (fun _ _ => by positivity))
      (sq_nonneg π)

theorem wp_cauchy_kernel_complex_integrable :
    Integrable (fun p : ℂ × ℂ => (1 - p.1 * conj p.2)⁻¹)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hfinite : volume unitDisc < ∞ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : ℂ) 1).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict unitDisc) := ⟨by simpa using hfinite⟩
  have hi := (integrable_const (1 : ℝ)).add wp_cauchy_kernel_double_integrable
  apply hi.mono' (by fun_prop)
  filter_upwards with p
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖(1 - p.1 * conj p.2)⁻¹‖ - 1)]

theorem wp_cauchy_kernel_square_integrable :
    Integrable (fun p : ℂ × ℂ => ((1 - p.1 * conj p.2)⁻¹) ^ 2)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  apply wp_cauchy_kernel_double_integrable.mono' (by fun_prop)
  filter_upwards with p
  rw [norm_pow]

theorem wp_double_kernel_weighted_integrable {f g : ℂ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hbf : ∀ u ∈ unitDisc, ‖f u‖ ≤ M) (hbg : ∀ v ∈ unitDisc, ‖g v‖ ≤ N) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 *
      (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹))
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => f p.1 * g p.2)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
  have hb : ∀ᵐ p ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)),
      ‖f p.1 * g p.2‖ ≤ M * N := by
    have hmem : ∀ᵐ p ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)),
        p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)
    filter_upwards [hmem] with p hp
    rw [norm_mul]
    exact mul_le_mul (hbf _ hp.1) (hbg _ hp.2) (norm_nonneg _) ((norm_nonneg _).trans (hbf _ hp.1))
  have hi := (wp_cauchy_kernel_square_integrable.add wp_cauchy_kernel_complex_integrable).mul_bdd hm hb
  apply hi.congr
  filter_upwards with p
  simp only [Pi.add_apply]
  ring

end TakhtajanTeo


