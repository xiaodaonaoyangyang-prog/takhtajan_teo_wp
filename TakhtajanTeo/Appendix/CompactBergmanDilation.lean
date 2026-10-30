import TakhtajanTeo.Appendix.CompactBergmanBounds

/-! # Operator norm convergence of compact matrix dilations -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

/-- A finite output truncation of the input-dilation error is controlled by
the square-summable errors of those finitely many rows. -/
theorem b9_input_error_bound {B : ℕ → ℕ → ℂ} (hB : IsBoundedMat B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : IsL2 x) (hx1 : sqSum x ≤ 1) (N : ℕ) :
    sqSum (matApply B (fun n => b7Diag r x n - x n)) ≤
      (∑ m ∈ Finset.range N, sqSum (fun n => b7Diag r (B m) n - B m n)) +
        (matOpNorm (fun m n => if m < N then 0 else B m n)).toReal ^ 2 := by
  let e := fun n => b7Diag r x n - x n
  have he : IsL2 e := b7_diag_sub_summable hr0 hr1 hx
  have he1 : sqSum e ≤ 1 := (b9_diag_error_mass_le hr0 hr1 hx).trans hx1
  have hs : IsL2 (matApply B e) := by obtain ⟨C,hC⟩ := hB; exact (hC e he).1
  have hpoint : ∀ m, ‖matApply B e m‖ ^ 2 ≤ sqSum (fun n => b7Diag r (B m) n - B m n) := by
    intro m
    have hrow := b7_diag_sub_summable hr0 hr1 (isBoundedMat_row_isL2 hB m)
    have hid : matApply B e m = ∑' n, (b7Diag r (B m) n - B m n) * x n := by
      apply tsum_congr
      intro n
      dsimp [e,b7Diag]
      ring
    rw [hid]
    exact (b9_pair_sq_le hrow hx).trans
      (mul_le_of_le_one_right (tsum_nonneg fun _ => sq_nonneg _) hx1)
  change sqSum (matApply B e) ≤ _
  rw [sqSum, ← hs.sum_add_tsum_nat_add N]
  exact add_le_add (Finset.sum_le_sum (fun m _ => hpoint m)) (b8_mat_tail_mass_le hB he he1 N)

/-- The output-dilation error is bounded by a finite diagonal error plus the
same genuine compact-operator tail. -/
theorem b9_output_error_bound {B : ℕ → ℕ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, IsL2 x → IsL2 (matApply B x) ∧ sqSum (matApply B x) ≤ C * sqSum x)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : IsL2 x) (hx1 : sqSum x ≤ 1) (N : ℕ) :
    sqSum (fun m => b7Diag r (matApply B x) m - matApply B x m) ≤
      C * (∑ m ∈ Finset.range N, ‖(r : ℂ) ^ (m+1) - 1‖ ^ 2) +
        (matOpNorm (fun m n => if m < N then 0 else B m n)).toReal ^ 2 := by
  have hy := hC x hx
  have hyC : sqSum (matApply B x) ≤ C :=
    hy.2.trans (mul_le_of_le_one_right hC0 hx1)
  have hc : ∀ m, ‖matApply B x m‖ ^ 2 ≤ C := fun m =>
    (hy.1.le_tsum m (fun _ _ => sq_nonneg _)).trans hyC
  have hs := b7_diag_sub_summable hr0 hr1 hy.1
  have hpoint : ∀ m, ‖b7Diag r (matApply B x) m - matApply B x m‖ ^ 2 ≤
      C * ‖(r : ℂ) ^ (m+1) - 1‖ ^ 2 := by
    intro m
    rw [show b7Diag r (matApply B x) m - matApply B x m =
      ((r : ℂ) ^ (m+1) - 1) * matApply B x m by dsimp [b7Diag]; ring,
      norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hc m) (sq_nonneg _)
  have ht : (∑' n, ‖b7Diag r (matApply B x) (n+N) - matApply B x (n+N)‖ ^ 2) ≤
      (matOpNorm (fun m n => if m < N then 0 else B m n)).toReal ^ 2 := by
    have hsN : Summable (fun n => ‖b7Diag r (matApply B x) (n+N) - matApply B x (n+N)‖ ^ 2) :=
      hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hyN : Summable (fun n => ‖matApply B x (n+N)‖ ^ 2) :=
      hy.1.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    exact (Summable.tsum_le_tsum (fun n => pow_le_pow_left₀ (norm_nonneg _)
      (b7_diag_sub_norm_le hr0 hr1 (matApply B x) (n+N)) 2) hsN hyN).trans
      (b8_mat_tail_mass_le ⟨C,hC⟩ hx hx1 N)
  rw [sqSum, ← hs.sum_add_tsum_nat_add N, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum (fun m _ => hpoint m)) ht

set_option maxHeartbeats 600000 in
/-- Uniform square-mass convergence on the entire unit ball. Finite rows
converge by dominated series convergence; the output tail is uniformly small. -/
theorem b9_uniform_square_error {B : ℕ → ℕ → ℂ} (hB : IsCompactMat B)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hr : Tendsto r atTop (𝓝 1)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x : ℕ → ℂ, IsL2 x → sqSum x ≤ 1 →
      sqSum (matApply (fun m n => b7Matrix (r k) B m n - B m n) x) < ε := by
  obtain ⟨C,hC0,hC⟩ := b9_bounded_mass hB.1
  have ht : Tendsto (fun N => (matOpNorm (fun m n => if m < N then 0 else B m n)).toReal ^ 2)
      atTop (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB.2
    simpa using hh.pow 2
  intro ε hε
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/8 by positivity))).exists
  have hrows : Tendsto (fun k => ∑ m ∈ Finset.range N,
      sqSum (fun n => b7Diag (r k) (B m) n - B m n)) atTop (𝓝 0) := by
    simpa only [sqSum, Finset.sum_const_zero] using tendsto_finsetSum (Finset.range N)
      (fun m _ => b7_diag_strong hr0 hr1 hr (isBoundedMat_row_isL2 hB.1 m))
  have hdiag : Tendsto (fun k => ∑ m ∈ Finset.range N, ‖(r k : ℂ) ^ (m+1) - 1‖ ^ 2)
      atTop (𝓝 0) := by
    have hrc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa using tendsto_finsetSum (Finset.range N)
      (fun m _ => ((hrc.pow (m+1)).sub_const 1).norm.pow 2)
  have hhead : Tendsto (fun k => 2 * (∑ m ∈ Finset.range N,
      sqSum (fun n => b7Diag (r k) (B m) n - B m n)) +
      2 * (C * ∑ m ∈ Finset.range N, ‖(r k : ℂ) ^ (m+1) - 1‖ ^ 2)) atTop (𝓝 0) := by
    simpa using (hrows.const_mul 2).add ((hdiag.const_mul C).const_mul 2)
  filter_upwards [hhead.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with k hk
  intro x hx hx1
  have hE := b9_matrix_error_mass_le hB.1 (hr0 k) (hr1 k) hx
  have hI := b9_input_error_bound hB.1 (hr0 k) (hr1 k) hx hx1 N
  have hO := b9_output_error_bound hC0 hC (hr0 k) (hr1 k) hx hx1 N
  linarith

/-- Compact matrices converge in the repaired extended operator norm under
two-sided diagonal dilation. Symmetry is not needed for this stronger result. -/
theorem b9_compact_matrix_norm_tendsto {B : ℕ → ℕ → ℂ} (hB : IsCompactMat B)
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun k => matOpNorm (fun m n => b7Matrix (r k) B m n - B m n)) atTop (𝓝 0) := by
  have hb : ∀ k, IsBoundedMat (fun m n => b7Matrix (r k) B m n - B m n) :=
    fun k => b9_isBounded_sub (b9_isBounded_dilate hB.1 (hr0 k) (hr1 k)) hB.1
  apply (ENNReal.tendsto_toReal_zero_iff (fun k => ((matOpNorm_lt_top_iff _).mpr (hb k)).ne)).mp
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (b9_uniform_square_error hB hr0 hr1 hr ((ε/2)^2) (sq_pos_of_pos (by positivity)))
  refine ⟨K, ?_⟩
  intro k hk
  have hn : matOpNorm (fun m n => b7Matrix (r k) B m n - B m n) ≤ ENNReal.ofReal (ε/2) := by
    rw [matOpNorm_of_bounded (hb k)]
    apply iSup_le
    intro x
    apply iSup_le
    rintro ⟨hx,hx1⟩
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.mpr
      ⟨by positivity, (hK k hk x hx hx1).le⟩)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  linarith

end AppB
end TakhtajanTeo
