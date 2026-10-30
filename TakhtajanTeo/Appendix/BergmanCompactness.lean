import TakhtajanTeo.Appendix.BergmanKernelModel

/-! # Square-summable subsequences from uniform output tails -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

/-- Pointwise limits preserve a uniform square-mass bound, including genuine
square summability of the limit. -/
theorem b8_mass_of_pointwise_limit {v : ℕ → ℕ → ℂ} {y : ℕ → ℂ} {C : ℝ}
    (hv : ∀ k, Summable (fun n => ‖v k n‖ ^ 2))
    (hb : ∀ k, (∑' n, ‖v k n‖ ^ 2) ≤ C)
    (ht : ∀ n, Tendsto (fun k => v k n) atTop (𝓝 (y n))) :
    Summable (fun n => ‖y n‖ ^ 2) ∧ (∑' n, ‖y n‖ ^ 2) ≤ C := by
  have hs : ∀ s : Finset ℕ, (∑ n ∈ s, ‖y n‖ ^ 2) ≤ C := by
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun n _ => (ht n).norm.pow 2))
    exact Eventually.of_forall fun k =>
      ((hv k).sum_le_tsum s (fun _ _ => sq_nonneg _)).trans (hb k)
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hs,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hs⟩

/-- A bounded sequence with uniformly vanishing square-mass tails has a
strictly increasing subsequence converging in the actual square-sum norm. -/
theorem b8_subsequence_of_uniform_tails {v : ℕ → ℕ → ℂ} {C : ℝ}
    (hv : ∀ k, Summable (fun n => ‖v k n‖ ^ 2))
    (hb : ∀ k, (∑' n, ‖v k n‖ ^ 2) ≤ C)
    {M : ℕ → ℝ} (hM : Tendsto M atTop (𝓝 0))
    (htail : ∀ N k, (∑' n, ‖v k (n + N)‖ ^ 2) ≤ M N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → ℂ,
      Summable (fun n => ‖y n‖ ^ 2) ∧
      Tendsto (fun k => ∑' n, ‖v (φ k) n - y n‖ ^ 2) atTop (𝓝 0) := by
  have hc : ∀ k n, ‖v k n‖ ≤ Real.sqrt (max C 0) := by
    intro k n
    have hh : ‖v k n‖ ^ 2 ≤ max C 0 :=
      ((hv k).le_tsum n (fun _ _ => sq_nonneg _)).trans ((hb k).trans (le_max_left _ _))
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hh
  have hcompact : IsCompact {x : ℕ → ℂ | ∀ n, x n ∈ closedBall 0 (Real.sqrt (max C 0))} :=
    isCompact_pi_infinite (fun _ => isCompact_closedBall _ _)
  obtain ⟨y, _, φ, hφ, hpoint⟩ := hcompact.tendsto_subseq (fun k n => by
    simpa only [mem_closedBall_zero_iff] using hc k n)
  have hp : ∀ n, Tendsto (fun k => v (φ k) n) atTop (𝓝 (y n)) :=
    fun n => (continuous_apply n).continuousAt.tendsto.comp hpoint
  have hy := b8_mass_of_pointwise_limit (fun k => hv (φ k)) (fun k => hb (φ k)) hp
  have hyt : ∀ N, (∑' n, ‖y (n + N)‖ ^ 2) ≤ M N := by
    intro N
    exact (b8_mass_of_pointwise_limit
      (fun k => (hv (φ k)).comp_injective (fun _ _ h => Nat.add_right_cancel h))
      (fun k => htail N (φ k)) (fun n => hp (n + N))).2
  refine ⟨φ, hφ, y, hy.1, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (hM.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 8 by positivity))).exists
  have hhead : Tendsto (fun k => ∑ n ∈ Finset.range N, ‖v (φ k) n - y n‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range N) (fun n _ =>
      ((hp n).sub_const (y n)).norm.pow 2)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hhead.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  refine ⟨K, ?_⟩
  intro k hk
  have hd := b7_sub_sq_summable (hv (φ k)) hy.1
  have hdt : (∑' n, ‖v (φ k) (n + N) - y (n + N)‖ ^ 2) ≤ 4 * M N := by
    have hvN : Summable (fun n => ‖v (φ k) (n + N)‖ ^ 2) :=
      (hv (φ k)).comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hyN : Summable (fun n => ‖y (n + N)‖ ^ 2) :=
      hy.1.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hh := Summable.tsum_le_tsum (g := fun n =>
        2 * ‖v (φ k) (n + N)‖ ^ 2 + 2 * ‖y (n + N)‖ ^ 2) (fun n => by
      have ht := norm_sub_le (v (φ k) (n + N)) (y (n + N))
      nlinarith [norm_nonneg (v (φ k) (n + N) - y (n + N)),
        norm_nonneg (v (φ k) (n + N)), norm_nonneg (y (n + N)),
        sq_nonneg (‖v (φ k) (n + N)‖ - ‖y (n + N)‖)])
      (b7_sub_sq_summable hvN hyN) ((hvN.mul_left 2).add (hyN.mul_left 2))
    rw [Summable.tsum_add (hvN.mul_left 2) (hyN.mul_left 2),
      tsum_mul_left, tsum_mul_left] at hh
    linarith [htail N (φ k), hyt N]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ => sq_nonneg _),
    ← hd.sum_add_tsum_nat_add N]
  linarith [hK k hk]

end AppB
end TakhtajanTeo
