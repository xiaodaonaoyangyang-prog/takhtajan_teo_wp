import TakhtajanTeo.Ch1.HarmonicResolventSeries

/-! Polynomial area and angular Cauchy-kernel energy for Corollary 6.4 (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Angular Cauchy-kernel energy, for the absolute double-integral estimate in (6.4), TT:2662–2666. -/
theorem wp_cauchy_kernel_circle_mean {a : ℂ} (ha : ‖a‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun w => ‖(1 - a * w)⁻¹‖ ^ 2) 0 r =
      (1 - ‖a‖ ^ 2 * r ^ 2)⁻¹ := by
  have haw {w : ℂ} (hw : w ∈ unitDisc) : ‖a * w‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg w) ha)
      (mem_ball_zero_iff.mp hw)
  have hc : ∀ w ∈ unitDisc, HasSum (fun n : ℕ => a ^ n * w ^ n) ((1 - a * w)⁻¹) := by
    intro w hw
    simpa only [mul_pow, one_div] using hasSum_geometric_of_norm_lt_one (haw hw)
  have hf : ContinuousOn (fun w : ℂ => (1 - a * w)⁻¹) unitDisc := by
    apply (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).inv₀
    intro w hw
    apply sub_ne_zero.mpr
    intro he
    change (1 : ℂ) = a * w at he
    have hh := haw hw
    rw [← he, norm_one] at hh
    exact lt_irrefl _ hh
  have hp := wp_disk_series_circle_energy hc hf hr0 hr1
  have hq0 : 0 ≤ ‖a‖ ^ 2 * r ^ 2 := by positivity
  have hq1 : ‖a‖ ^ 2 * r ^ 2 < 1 := by
    have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
    have hr2 : r ^ 2 < 1 := by nlinarith
    exact lt_of_le_of_lt (mul_le_of_le_one_left (sq_nonneg r) ha2) hr2
  have hterm (n : ℕ) : ‖a ^ n‖ ^ 2 * r ^ (2 * n) = (‖a‖ ^ 2 * r ^ 2) ^ n := by
    simp only [norm_pow, mul_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hterm] at hp
  have hg := hasSum_geometric_of_norm_lt_one
    (show ‖‖a‖ ^ 2 * r ^ 2‖ < 1 by rwa [Real.norm_of_nonneg hq0])
  exact hp.unique (by simpa only [one_div] using hg)

/-- The unweighted polynomial area formula used to bound geometric partial kernels (TT:2662–2666). -/
theorem wp_polynomial_unweighted_area (p : Polynomial ℂ) :
    (∫ z in unitDisc, ‖p.eval z‖ ^ 2) =
      π * ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 / (n + 1 : ℝ) := by
  rw [integral_unitDisc_circleAverage _ (by fun_prop)]
  have he : (∫ r in (0 : ℝ)..1, r * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r) =
      ∫ r in (0 : ℝ)..1, ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 * r ^ (2 * n + 1) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := (show r ∈ Icc (0 : ℝ) 1 by simpa using hr).1
    dsimp only
    rw [polynomial_circle_average_sq p hr0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_succ]
    ring
  rw [he, intervalIntegral.integral_finsetSum]
  · have ht (n : ℕ) : (∫ r in (0 : ℝ)..1, ‖p.coeff n‖ ^ 2 * r ^ (2 * n + 1)) =
        (1 / 2 : ℝ) * (‖p.coeff n‖ ^ 2 / (n + 1 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, pow_succ, mul_zero, sub_zero, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring
    simp_rw [ht]
    rw [← Finset.mul_sum]
    ring
  · intro n hn
    exact (by fun_prop : Continuous (fun r : ℝ => ‖p.coeff n‖ ^ 2 * r ^ (2 * n + 1))).intervalIntegrable _ _

theorem wp_scalarSeriesPolynomial_unweighted_area (a : ℕ → ℂ) (N : ℕ) :
    (∫ z in unitDisc, ‖(wp_scalarSeriesPolynomial a N).eval z‖ ^ 2) =
      π * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 / (n + 1 : ℝ) := by
  rw [wp_polynomial_unweighted_area]
  congr 1
  have hs : (wp_scalarSeriesPolynomial a N).support ⊆ Finset.range N := by
    intro n hn
    by_contra hnot
    have hnN : ¬ n < N := fun h => hnot (Finset.mem_range.mpr h)
    have hz : (wp_scalarSeriesPolynomial a N).coeff n = 0 := by
      rw [wp_scalarSeriesPolynomial_coeff, if_neg hnN]
    exact (Polynomial.mem_support_iff.mp hn) hz
  calc
    _ = ∑ n ∈ Finset.range N, ‖(wp_scalarSeriesPolynomial a N).coeff n‖ ^ 2 / (n + 1 : ℝ) := by
      apply Finset.sum_subset hs
      intro n _ hn
      have hz : (wp_scalarSeriesPolynomial a N).coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      rw [hz]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [wp_scalarSeriesPolynomial_coeff, if_pos (Finset.mem_range.mp hn)]

theorem wp_disk_unweighted_monomial (n : ℕ) :
    (∫ z in unitDisc, ‖z‖ ^ (2 * n)) = π / (n + 1 : ℝ) := by
  have h := wp_polynomial_unweighted_area (Polynomial.monomial n (1 : ℂ))
  rw [Polynomial.support_monomial n one_ne_zero] at h
  simpa [Polynomial.eval_monomial, norm_pow, ← pow_mul, Nat.mul_comm, div_eq_mul_inv,
    Polynomial.coeff_monomial] using h

end TakhtajanTeo


