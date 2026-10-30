import TakhtajanTeo.Appendix.CompactBergmanKernel

/-! # Quantitative compactness of a strict inward dilation -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

theorem b9_strict_dilation_tail_le {B : ℕ → ℕ → ℂ} (hB : B7Contractive B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N : ℕ) :
    matOpNorm (fun m n => if m < N then 0 else b7Matrix r B m n) ≤ ENNReal.ofReal (r^(N+1)) := by
  have hBb : IsBoundedMat B := ⟨1, fun x hx =>
    ⟨(hB x hx).1, by simpa only [one_mul,sqSum,matApply,b7Apply] using (hB x hx).2⟩⟩
  have hBr := b9_isBounded_dilate hBb hr0 hr1
  have hT := isBoundedMat_tail hBr N
  rw [matOpNorm_of_bounded hT]
  apply iSup_le
  intro x
  apply iSup_le
  rintro ⟨hx,hx1⟩
  have hd := b7_diag_summable hr0 hr1 hx
  have hy := hB (b7Diag r x) hd
  have hy1 : sqSum (b7Apply B (b7Diag r x)) ≤ 1 :=
    hy.2.trans ((b7_diag_mass_le hr0 hr1 hx).trans hx1)
  have hs : IsL2 (matApply (fun m n => if m < N then 0 else b7Matrix r B m n) x) :=
    (matApply_tail_sqSum_le hBr hx N).1
  have hpoint : ∀ m, ‖matApply (fun m n => if m < N then 0 else b7Matrix r B m n) x m‖ ^ 2 ≤
      (r^(N+1))^2 * ‖b7Apply B (b7Diag r x) m‖ ^ 2 := by
    intro m
    by_cases hm : m < N
    · simp [matApply,hm,mul_nonneg (sq_nonneg _) (sq_nonneg _)]
    · have he : matApply (fun m n => if m < N then 0 else b7Matrix r B m n) x m =
          b7Diag r (b7Apply B (b7Diag r x)) m := by
        simpa only [matApply,b7Apply,ite_eq_right hm] using congrFun (b7_apply_matrix B r x) m
      rw [he]
      simp only [b7Diag,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr0,mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (pow_nonneg hr0 _) (pow_le_pow_of_le_one hr0 hr1 (by omega : N+1 ≤ m+1)) 2)
        (sq_nonneg _)
  have hmass := Summable.tsum_le_tsum hpoint hs (hy.1.mul_left ((r^(N+1))^2))
  rw [tsum_mul_left] at hmass
  have hb : sqSum (matApply (fun m n => if m < N then 0 else b7Matrix r B m n) x) ≤ (r^(N+1))^2 :=
    hmass.trans (mul_le_of_le_one_right (sq_nonneg _) hy1)
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.mpr ⟨pow_nonneg hr0 _,hb⟩)

/-- Strict inward dilation gives a compact matrix with a geometric tail
bound, even when the starting contraction is not compact. -/
theorem b9_strict_dilation_compact {B : ℕ → ℕ → ℂ} (hB : B7Contractive B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : IsCompactMat (b7Matrix r B) := by
  have hBb : IsBoundedMat B := ⟨1, fun x hx =>
    ⟨(hB x hx).1, by simpa only [one_mul,sqSum,matApply,b7Apply] using (hB x hx).2⟩⟩
  refine ⟨b9_isBounded_dilate hBb hr0 hr1.le, ?_⟩
  have ht : Tendsto (fun N : ℕ => r^(N+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const r
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [ENNReal.ofReal_zero] at he
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun _ => bot_le) (fun N => b9_strict_dilation_tail_le hB hr0 hr1.le N)

end AppB
end TakhtajanTeo
