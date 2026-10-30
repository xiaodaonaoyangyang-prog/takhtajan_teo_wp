import TakhtajanTeo.Ch1.S2_HilbertManifold

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Polynomial partial sums for the weighted Parseval calculation (TT:2206–2216). -/
def wp_scalarSeriesPolynomial (a : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (a n)

/-- The partial-sum polynomial has the prescribed coefficients below its cutoff (TT:2206–2216). -/
theorem wp_scalarSeriesPolynomial_coeff (a : ℕ → ℂ) (N n : ℕ) :
    (wp_scalarSeriesPolynomial a N).coeff n = if n < N then a n else 0 := by
  simp [wp_scalarSeriesPolynomial, Polynomial.coeff_sum, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', eq_comm]

/-- Evaluation of the partial-sum polynomial (TT:2206–2216). -/
theorem wp_scalarSeriesPolynomial_eval (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (wp_scalarSeriesPolynomial a N).eval z = ∑ n ∈ Finset.range N, a n * z ^ n := by
  simp [wp_scalarSeriesPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Finite weighted Parseval in the exact partial-sum indexing (TT:2206–2216). -/
theorem wp_scalarSeriesPolynomial_area (a : ℕ → ℂ) (N : ℕ) :
    (∫ z in unitDisc, ‖(wp_scalarSeriesPolynomial a N).eval z‖ ^ 2 * (rho z)⁻¹) =
      (π / 2) * ∑ n ∈ Finset.range N,
        ‖a n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  rw [polynomial_weighted_area]
  congr 1
  have hs : (wp_scalarSeriesPolynomial a N).support ⊆ Finset.range N := by
    intro n hn
    by_contra hnot
    have hnN : ¬ n < N := fun h => hnot (Finset.mem_range.mpr h)
    have hz : (wp_scalarSeriesPolynomial a N).coeff n = 0 := by
      rw [wp_scalarSeriesPolynomial_coeff, if_neg hnN]
    exact (Polynomial.mem_support_iff.mp hn) hz
  calc
    _ = ∑ n ∈ Finset.range N, ‖(wp_scalarSeriesPolynomial a N).coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
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

/-- Absolute coefficient summability implies summability of the weighted squared coefficients (TT:2206–2216). -/
theorem wp_scalarSeries_energy_summable {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n => ‖a n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
  have hbound (n : ℕ) : ‖a n‖ ≤ ∑' k, ‖a k‖ := by
    simpa only [Finset.sum_singleton] using ha.sum_le_tsum {n} (fun _ _ => norm_nonneg _)
  have hsq : Summable (fun n => ‖a n‖ ^ 2) := by
    apply (ha.mul_left (∑' k, ‖a k‖)).of_nonneg_of_le (fun n => sq_nonneg _)
    intro n
    simpa only [sq, mul_comm] using mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg (a n))
  apply hsq.of_nonneg_of_le (fun n => by positivity)
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : (1 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
    nlinarith [mul_nonneg hn (sq_nonneg (n : ℝ))]
  simpa only [div_one] using div_le_div_of_nonneg_left (sq_nonneg ‖a n‖) zero_lt_one hd

/-- The unit-disk monomial series is uniformly dominated by its coefficient norms (TT:2206–2216). -/
theorem wp_scalarSeries_monomial_bound (a : ℕ → ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) : ‖a n * z ^ n‖ ≤ ‖a n‖ := by
  rw [norm_mul, norm_pow]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact pow_le_one₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz)

/-- Weighted Parseval for an absolutely summable disk power series (TT:2206–2216). -/
theorem wp_scalarSeries_weighted_area {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    (∫ z in unitDisc, ‖∑' n, a n * z ^ n‖ ^ 2 * (rho z)⁻¹) =
      (π / 2) * ∑' n, ‖a n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hU := tendstoUniformlyOn_tsum_nat ha (fun n z hz => wp_scalarSeries_monomial_bound a n hz)
  have hc := continuousOn_tsum (fun n => (by fun_prop : ContinuousOn (fun z : ℂ => a n * z ^ n)
      (closedBall 0 1))) ha (fun n z hz => wp_scalarSeries_monomial_bound a n hz)
  have hp : TendstoUniformlyOn (fun N z => (wp_scalarSeriesPolynomial a N).eval z)
      (fun z => ∑' n, a n * z ^ n) atTop (closedBall 0 1) := by
    simpa only [wp_scalarSeriesPolynomial_eval] using hU
  have hi := weighted_polynomial_integral_tendsto (wp_scalarSeriesPolynomial a) hc hp
  simp_rw [wp_scalarSeriesPolynomial_area] at hi
  have hs := (wp_scalarSeries_energy_summable ha).hasSum.tendsto_sum_nat.const_mul (π / 2)
  exact tendsto_nhds_unique hi hs

end TakhtajanTeo
