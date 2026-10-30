import TakhtajanTeo.Ch1.S1_2_Homogeneous
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Iterated derivative of a shifted scalar monomial (TT:2206–2216). -/
theorem wp_shiftedMonomial_deriv (a : ℂ) (n k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => a * w ^ (n + 2)) z =
      a * ((n + 2).descFactorial k : ℂ) * z ^ (n + 2 - k) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  ring

/-- A cubic coefficient majorant controls the first three monomial derivatives on the closed disk (TT:2206–2216). -/
theorem wp_shiftedMonomial_deriv_bound (a : ℂ) (n : ℕ) {k : ℕ} (hk : k ≤ 3)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖iteratedDeriv k (fun w => a * w ^ (n + 2)) z‖ ≤ ((n + 2 : ℕ) : ℝ) ^ 3 * ‖a‖ := by
  rw [wp_shiftedMonomial_deriv, norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
  have hp : ‖z‖ ^ (n + 2 - k) ≤ 1 := pow_le_one₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz)
  have hd : ((n + 2).descFactorial k : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ 3 := by
    calc
      _ ≤ ((n + 2 : ℕ) : ℝ) ^ k := by exact_mod_cast Nat.descFactorial_le_pow (n + 2) k
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n + 2 by omega)) hk
  calc
    _ ≤ ‖a‖ * ((n + 2 : ℕ) : ℝ) ^ 3 * 1 := by gcongr
    _ = _ := by ring

/-- Third derivatives remove the shift by three and give the cubic Fourier weight (TT:2206–2216). -/
theorem wp_shiftedMonomial_third (a : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv 3 (fun w => a * w ^ (n + 3)) z =
      a * ((n + 1 : ℂ) * (n + 2) * (n + 3)) * z ^ n := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow, Nat.add_descFactorial_eq_ascFactorial]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  push_cast
  ring

/-- Termwise third differentiation of a disk series under a summable cubic majorant (TT:2206–2216). -/
theorem wp_shiftedSeries_third {a : ℕ → ℂ}
    (ha : Summable (fun n => ((n + 2 : ℕ) : ℝ) ^ 3 * ‖a n‖))
    {z : ℂ} (hz : z ∈ unitDisc) :
    iteratedDeriv 3 (fun w => ∑' n, a n * w ^ (n + 2)) z =
      ∑' n, a (n + 1) * ((n + 1 : ℂ) * (n + 2) * (n + 3)) * z ^ n := by
  have hopen : IsOpen unitDisc := isOpen_ball
  have hsum : ∀ w ∈ unitDisc, Summable (fun n => a n * w ^ (n + 2)) := by
    intro w hw
    apply Summable.of_norm_bounded ha
    intro n
    simpa only [iteratedDeriv_zero] using
      wp_shiftedMonomial_deriv_bound (a n) n (k := 0) (by omega) (ball_subset_closedBall hw)
  have huni : ∀ k, 1 ≤ k → k ≤ 3 → SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin k (fun w => a n * w ^ (n + 2)) unitDisc) unitDisc := by
    intro k _ hk
    refine ⟨_, (tendstoUniformlyOn_tsum ha ?_).tendstoLocallyUniformlyOn⟩
    intro n w hw
    rw [iteratedDerivWithin_of_isOpen hopen hw]
    exact wp_shiftedMonomial_deriv_bound (a n) n hk (ball_subset_closedBall hw)
  have hd : ∀ n k w, k ≤ 3 → w ∈ unitDisc →
      DifferentiableAt ℂ (iteratedDerivWithin k (fun v => a n * v ^ (n + 2)) unitDisc) w := by
    intro n k w _ hw
    have hc : ContDiffOn ℂ (k + 1 : ℕ) (fun v : ℂ => a n * v ^ (n + 2)) unitDisc := by fun_prop
    exact (hc.differentiableOn_iteratedDerivWithin (m := k)
      (by exact_mod_cast Nat.lt_succ_self k) hopen.uniqueDiffOn).differentiableAt
      (hopen.mem_nhds hw)
  rw [← iteratedDerivWithin_of_isOpen hopen hz,
    iteratedDerivWithin_tsum 3 hopen hz hsum huni hd]
  simp_rw [iteratedDerivWithin_of_isOpen hopen hz]
  have hs3 : Summable (fun n => iteratedDeriv 3 (fun w => a n * w ^ (n + 2)) z) := by
    apply Summable.of_norm_bounded ha
    intro n
    exact wp_shiftedMonomial_deriv_bound (a n) n (k := 3) le_rfl (ball_subset_closedBall hz)
  rw [hs3.tsum_eq_zero_add]
  have h0 : iteratedDeriv 3 (fun w : ℂ => a 0 * w ^ (0 + 2)) z = 0 := by
    rw [wp_shiftedMonomial_deriv]
    norm_num [show (2 : ℕ).descFactorial 3 = 0 by decide]
  rw [h0, zero_add]
  apply tsum_congr
  intro n
  simpa only [Nat.add_assoc, Nat.reduceAdd] using wp_shiftedMonomial_third (a (n + 1)) n z

/-- The third-derivative coefficients themselves are absolutely summable (TT:2206–2216). -/
theorem wp_shiftedSeries_third_coeff_summable {a : ℕ → ℂ}
    (ha : Summable (fun n => ((n + 2 : ℕ) : ℝ) ^ 3 * ‖a n‖)) :
    Summable (fun n => ‖a (n + 1) * ((n + 1 : ℂ) * (n + 2) * (n + 3))‖) := by
  have hs := (summable_nat_add_iff 1).mpr ha
  apply hs.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  have h := wp_shiftedMonomial_deriv_bound (a (n + 1)) (n + 1) (k := 3) le_rfl
    (z := (1 : ℂ)) (by simp)
  have hn : n + 1 + 2 = n + 3 := by omega
  rw [hn, wp_shiftedMonomial_third] at h
  simpa only [one_pow, mul_one, Nat.add_assoc, Nat.reduceAdd] using h

end TakhtajanTeo
