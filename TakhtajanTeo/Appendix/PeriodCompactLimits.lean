import TakhtajanTeo.Appendix.CompactBergmanKernel
import TakhtajanTeo.Ch2.PeriodMatrixBridge

/-! # Matrix operator norm, Hilbert–Schmidt tails, and closedness of compactness -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

-- T1
theorem pcl_norm_eq {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) :
    matOpNorm A = ENNReal.ofReal ‖gopOp A‖ := by
  have he (x : ell2) : Real.sqrt (sqSum (matApply A x)) = ‖gopOp A x‖ := by
    have hs : sqSum (matApply A x) = ‖gopOp A x‖ ^ 2 := by
      simp only [gop_norm_sq, pmb_apply hA, sqSum]
    rw [hs, Real.sqrt_sq (norm_nonneg _)]
  apply le_antisymm
  · rw [matOpNorm_of_bounded hA]
    apply iSup_le
    intro x
    apply iSup_le
    rintro ⟨hx, hx1⟩
    let X : ell2 := ⟨x, gop_mem_of_summable hx⟩
    have hX : ‖X‖ ≤ 1 := by
      have hh : ‖X‖ ^ 2 ≤ 1 := by simpa only [gop_norm_sq, sqSum, X] using hx1
      nlinarith [norm_nonneg X]
    change ENNReal.ofReal (Real.sqrt (sqSum (matApply A X))) ≤ _
    rw [he]
    exact ENNReal.ofReal_le_ofReal ((ContinuousLinearMap.le_opNorm _ X).trans
      (mul_le_of_le_one_right (norm_nonneg _) hX))
  · have hfin : matOpNorm A ≠ ∞ := ((matOpNorm_lt_top_iff A).mpr hA).ne
    have hn : ‖gopOp A‖ ≤ (matOpNorm A).toReal := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm ENNReal.toReal_nonneg
      intro x hx
      have hs : sqSum x ≤ 1 := by
        change (∑' n, ‖x n‖ ^ 2) ≤ 1
        rw [← gop_norm_sq, hx]
        norm_num
      have hh : ENNReal.ofReal ‖gopOp A x‖ ≤ matOpNorm A := by
        rw [← he, matOpNorm_of_bounded hA]
        exact le_iSup_of_le (fun n => x n) (le_iSup_of_le ⟨gop_l2_summable x, hs⟩ le_rfl)
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.toReal_mono hfin hh
    simpa only [ENNReal.ofReal_toReal hfin] using ENNReal.ofReal_le_ofReal hn

-- T2
theorem pcl_sub {A B : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (hB : IsBoundedMat B) :
    gopOp (fun m n => A m n - B m n) = gopOp A - gopOp B := by
  apply gop_ext
  intro m n
  rw [pmb_entry (b9_isBounded_sub hA hB), ContinuousLinearMap.sub_apply, lp.coeFn_sub,
    Pi.sub_apply, pmb_entry hA, pmb_entry hB]

-- T3
theorem pcl_norm_le_add {A B : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (hB : IsBoundedMat B) :
    matOpNorm A ≤ matOpNorm B + matOpNorm (fun m n => B m n - A m n) := by
  rw [pcl_norm_eq hA, pcl_norm_eq hB, pcl_norm_eq (b9_isBounded_sub hB hA), pcl_sub hB hA,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h := norm_sub_le (gopOp B) (gopOp B - gopOp A)
  simpa only [sub_sub_cancel] using h

-- T4
theorem pcl_compact_of_limit {A : ℕ → ℕ → ℂ} {B : ℕ → ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : ∀ k, IsCompactMat (B k))
    (hlim : Tendsto (fun k => matOpNorm (fun m n => B k m n - A m n)) atTop (𝓝 0)) :
    IsCompactMat A := by
  refine ⟨hA, ENNReal.tendsto_nhds_zero.mpr ?_⟩
  intro ε hε
  by_cases htop : ε = ∞
  · subst ε
    exact Eventually.of_forall fun _ => le_top
  let e := ε.toReal / 2
  have he : 0 < e := half_pos (ENNReal.toReal_pos hε.ne' htop)
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.mp hlim (ENNReal.ofReal e)
    (ENNReal.ofReal_pos.mpr he)).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hB k).2 (ENNReal.ofReal e)
    (ENNReal.ofReal_pos.mpr he)] with N hN
  have hT : (fun m n => (if m < N then 0 else B k m n) - (if m < N then 0 else A m n)) =
      (fun m n => if m < N then 0 else B k m n - A m n) := by
    funext m n
    split_ifs <;> simp
  have hb := pcl_norm_le_add (isBoundedMat_tail hA N) (isBoundedMat_tail (hB k).1 N)
  rw [hT] at hb
  calc matOpNorm (fun m n => if m < N then 0 else A m n)
      ≤ matOpNorm (fun m n => if m < N then 0 else B k m n) +
        matOpNorm (fun m n => if m < N then 0 else B k m n - A m n) := hb
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal e :=
      add_le_add hN ((matOpNorm_tail_le (fun m n => B k m n - A m n) N).trans hk)
    _ = ε := by
      rw [← ENNReal.ofReal_add he.le he.le, show e + e = ε.toReal by dsimp [e]; ring,
        ENNReal.ofReal_toReal htop]

-- T5
theorem pcl_hilbert_schmidt {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A)
    (hHS : Summable (fun q : ℕ × ℕ => ‖A q.1 q.2‖ ^ 2)) : IsCompactMat A := by
  let r : ℕ → ell2 := fun m => ⟨fun k => conj (A m k),
    gop_mem_of_summable ((isBoundedMat_row_isL2 hA m).congr fun k => by rw [Complex.norm_conj])⟩
  have hrn : ∀ m, ‖r m‖ ^ 2 = ∑' k, ‖A m k‖ ^ 2 := by
    intro m
    simp only [gop_norm_sq, r, Complex.norm_conj]
  have hr : Summable (fun m => ‖r m‖ ^ 2) := by
    simp only [hrn]
    exact hHS.prod
  have ht : ∀ N, matOpNorm (fun m n => if m < N then 0 else A m n) ≤
      ENNReal.ofReal (Real.sqrt (∑' k, ‖r (k + N)‖ ^ 2)) := by
    intro N
    have hg : Summable (fun m => ‖(if m < N then 0 else r m : ell2)‖ ^ 2) :=
      hr.of_nonneg_of_le (fun m => by positivity) (fun m => by split_ifs <;> simp)
    obtain ⟨S, hS, hn⟩ := gop_rows_mk _ hg
    have hs : gopOp (fun m n => if m < N then 0 else A m n) = S := by
      apply gop_ext
      intro m n
      rw [pmb_entry (isBoundedMat_tail hA N), hS, lp.inner_single_right, gop_inner_apply, mul_one]
      by_cases hm : m < N
      · simp [hm]
      · simp [hm, r]
    rw [pcl_norm_eq (isBoundedMat_tail hA N), hs]
    apply ENNReal.ofReal_le_ofReal
    apply hn.trans
    apply Real.sqrt_le_sqrt
    apply le_of_eq
    rw [← hg.sum_add_tsum_nat_add N]
    have hz : ∑ i ∈ Finset.range N, ‖(if i < N then 0 else r i : ell2)‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [Finset.mem_range.mp hi]
    rw [hz, zero_add]
    exact tsum_congr fun k => by simp
  have hlim : Tendsto (fun N => ENNReal.ofReal (Real.sqrt (∑' k, ‖r (k + N)‖ ^ 2)))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_sum_nat_add fun k => ‖r k‖ ^ 2).sqrt)
  exact ⟨hA, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) ht⟩

end AppB
end TakhtajanTeo
