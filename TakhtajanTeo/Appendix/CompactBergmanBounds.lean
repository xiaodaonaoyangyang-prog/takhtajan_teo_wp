import TakhtajanTeo.Appendix.B_PeriodMapping

/-! # Genuine square-mass bounds for compact Bergman matrix dilations -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b9_pair_sq_le {a x : ℕ → ℂ} (ha : IsL2 a) (hx : IsL2 x) :
    ‖∑' n, a n * x n‖ ^ 2 ≤ sqSum a * sqSum x := by
  have hp := (bergman_pair_summable ha hx).of_norm.hasSum.tendsto_sum_nat.norm.pow 2
  have hq := ha.hasSum.tendsto_sum_nat.mul hx.hasSum.tendsto_sum_nat
  apply le_of_tendsto_of_tendsto hp hq
  apply Eventually.of_forall
  intro N
  have hn := norm_sum_le (Finset.range N) (fun n => a n * x n)
  simp only [norm_mul] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ (fun n => ‖a n‖) (fun n => ‖x n‖))

theorem b9_bounded_mass {B : ℕ → ℕ → ℂ} (hB : IsBoundedMat B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, IsL2 x →
      IsL2 (matApply B x) ∧ sqSum (matApply B x) ≤ C * sqSum x := by
  obtain ⟨C,hC⟩ := hB
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact ⟨(hC x hx).1, (hC x hx).2.trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (tsum_nonneg fun _ => sq_nonneg _))⟩

theorem b9_add_mass_le {x y : ℕ → ℂ} (hx : IsL2 x) (hy : IsL2 y) :
    IsL2 (fun n => x n + y n) ∧
      sqSum (fun n => x n + y n) ≤ 2 * sqSum x + 2 * sqSum y := by
  have hb : ∀ n, ‖x n + y n‖ ^ 2 ≤ 2 * ‖x n‖ ^ 2 + 2 * ‖y n‖ ^ 2 := by
    intro n
    have ht := norm_add_le (x n) (y n)
    nlinarith [norm_nonneg (x n), norm_nonneg (y n), norm_nonneg (x n + y n),
      sq_nonneg (‖x n‖ - ‖y n‖)]
  have hs := (hx.mul_left 2).add (hy.mul_left 2)
  have hz := hs.of_nonneg_of_le (fun _ => sq_nonneg _) hb
  refine ⟨hz, ?_⟩
  have hh := Summable.tsum_le_tsum hb hz hs
  simpa only [sqSum, Summable.tsum_add (hx.mul_left 2) (hy.mul_left 2), tsum_mul_left] using hh

theorem b9_mat_apply_sub {A B : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (hB : IsBoundedMat B)
    {x : ℕ → ℂ} (hx : IsL2 x) :
    matApply (fun m n => A m n - B m n) x = fun m => matApply A x m - matApply B x m := by
  ext m
  simp only [matApply, sub_mul]
  exact (isBoundedMat_summable hA hx m).tsum_sub (isBoundedMat_summable hB hx m)

theorem b9_isBounded_sub {A B : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (hB : IsBoundedMat B) :
    IsBoundedMat (fun m n => A m n - B m n) := by
  obtain ⟨C,hC0,hC⟩ := b9_bounded_mass hA
  obtain ⟨D,hD0,hD⟩ := b9_bounded_mass hB
  refine ⟨2*C+2*D, ?_⟩
  intro x hx
  rw [b9_mat_apply_sub hA hB hx]
  have hn : IsL2 (fun m => -matApply B x m) := by
    simpa only [IsL2, norm_neg] using (hD x hx).1
  have hh := b9_add_mass_le (hC x hx).1 hn
  simp only [← sub_eq_add_neg, sqSum, norm_neg] at hh
  refine ⟨hh.1, ?_⟩
  change (∑' m, ‖matApply A x m - matApply B x m‖ ^ 2) ≤ (2*C+2*D)*sqSum x
  have hc := (hC x hx).2
  have hd := (hD x hx).2
  dsimp only [sqSum] at hc hd ⊢
  linarith [hh.2]

theorem b9_isBounded_dilate {B : ℕ → ℕ → ℂ} (hB : IsBoundedMat B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : IsBoundedMat (b7Matrix r B) := by
  obtain ⟨C,hC0,hC⟩ := b9_bounded_mass hB
  refine ⟨C, ?_⟩
  intro x hx
  have hd := b7_diag_summable hr0 hr1 hx
  have hy := hC (b7Diag r x) hd
  change IsL2 (b7Apply (b7Matrix r B) x) ∧ _
  change IsL2 (b7Apply (b7Matrix r B) x) ∧ sqSum (b7Apply (b7Matrix r B) x) ≤ C * sqSum x
  rw [b7_apply_matrix]
  refine ⟨b7_diag_summable hr0 hr1 hy.1, ?_⟩
  exact (b7_diag_mass_le hr0 hr1 hy.1).trans (hy.2.trans
    (mul_le_mul_of_nonneg_left (b7_diag_mass_le hr0 hr1 hx) hC0))

theorem b9_diag_error_mass_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : IsL2 x) :
    sqSum (fun n => b7Diag r x n - x n) ≤ sqSum x :=
  Summable.tsum_le_tsum (fun n => pow_le_pow_left₀ (norm_nonneg _)
    (b7_diag_sub_norm_le hr0 hr1 x n) 2) (b7_diag_sub_summable hr0 hr1 hx) hx

/-- Split the two-sided dilation error before estimating either term. -/
theorem b9_matrix_error_mass_le {B : ℕ → ℕ → ℂ} (hB : IsBoundedMat B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {x : ℕ → ℂ} (hx : IsL2 x) :
    sqSum (matApply (fun m n => b7Matrix r B m n - B m n) x) ≤
      2 * sqSum (matApply B (fun n => b7Diag r x n - x n)) +
      2 * sqSum (fun m => b7Diag r (matApply B x) m - matApply B x m) := by
  obtain ⟨C,hC⟩ := hB
  let e := fun n => b7Diag r x n - x n
  have he := b7_diag_sub_summable hr0 hr1 hx
  have hBe := (hC e he).1
  have hy := (hC x hx).1
  have hid : matApply (fun m n => b7Matrix r B m n - B m n) x =
      fun m => b7Diag r (matApply B e) m + (b7Diag r (matApply B x) m - matApply B x m) := by
    rw [b9_mat_apply_sub (b9_isBounded_dilate ⟨C,hC⟩ hr0 hr1) ⟨C,hC⟩ hx]
    have hs := b7_apply_sub (fun m => isBoundedMat_row_isL2 ⟨C,hC⟩ m)
      (b7_diag_summable hr0 hr1 hx) hx
    change b7Apply B e = _ at hs
    ext m
    change b7Apply (b7Matrix r B) x m - b7Apply B x m = _
    rw [b7_apply_matrix]
    dsimp only [b7Diag]
    change (r : ℂ) ^ (m+1) * b7Apply B (b7Diag r x) m - b7Apply B x m =
      (r : ℂ) ^ (m+1) * b7Apply B e m + ((r : ℂ) ^ (m+1) * b7Apply B x m - b7Apply B x m)
    rw [congrFun hs m]
    ring
  rw [hid]
  exact (b9_add_mass_le (b7_diag_summable hr0 hr1 hBe)
    (b7_diag_sub_summable hr0 hr1 hy)).2.trans
      (add_le_add (mul_le_mul_of_nonneg_left (b7_diag_mass_le hr0 hr1 hBe) (by norm_num)) le_rfl)

end AppB
end TakhtajanTeo
