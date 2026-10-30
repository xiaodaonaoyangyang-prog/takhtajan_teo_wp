import TakhtajanTeo.Ch1.S7DiskCutoff

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The real Frechet derivative of the actual radial cutoff. -/
theorem s7dc_fderiv (n : ℕ) (z : ℂ) :
    fderiv ℝ (s7dc_cutoff n) z =
      deriv Real.smoothTransition (((n : ℝ) + 2) * (1 - Complex.normSq z) - 1) •
        ((-2 * ((n : ℝ) + 2)) • innerSL ℝ z) := by
  have hq : HasFDerivAt (fun w : ℂ => Complex.normSq w) (2 • innerSL ℝ z) z := by
    simpa only [Complex.normSq_eq_norm_sq] using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hs : HasFDerivAt (fun w : ℂ => ((n : ℝ) + 2) * (1 - Complex.normSq w) - 1)
      ((-2 * ((n : ℝ) + 2)) • innerSL ℝ z) z := by
    convert (((hasFDerivAt_const (1 : ℝ) z).sub hq).const_mul ((n : ℝ) + 2)).sub_const 1 using 1
    ext v
    simp
    ring
  exact ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _
    |>.hasDerivAt.comp_hasFDerivAt z hs).fderiv

theorem s7dc_fderiv_norm (n : ℕ) (z : ℂ) :
    ‖fderiv ℝ (s7dc_cutoff n) z‖ =
      ‖deriv Real.smoothTransition (((n : ℝ) + 2) * (1 - Complex.normSq z) - 1)‖ *
        (2 * ((n : ℝ) + 2)) * ‖z‖ := by
  rw [s7dc_fderiv, norm_smul, norm_smul, innerSL_apply_norm, norm_mul]
  rw [Real.norm_eq_abs ((n : ℝ) + 2), abs_of_nonneg (by positivity)]
  norm_num
  ring

/-- Uniform hyperbolic first-derivative bound, proved from the transition collar. -/
theorem s7dc_weighted_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z ∈ unitDisc,
      (1 - Complex.normSq z) * ‖fderiv ℝ (s7dc_cutoff n) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := s7dc_transition_deriv_bounds
  refine ⟨4 * C, by positivity, fun n z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
  have hd : 0 < 1 - Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  let s := ((n : ℝ) + 2) * (1 - Complex.normSq z) - 1
  by_cases he : deriv Real.smoothTransition s = 0
  · rw [s7dc_fderiv_norm]
    change (1 - Complex.normSq z) * (‖deriv Real.smoothTransition s‖ * _ * _) ≤ _
    simp only [he, norm_zero, zero_mul, mul_zero]
    positivity
  · have hs := s7dc_transition_deriv_support (subset_closure he)
    have hnδ : ((n : ℝ) + 2) * (1 - Complex.normSq z) ≤ 2 := by
      have := hs.2
      dsimp [s] at this
      linarith
    calc
      (1 - Complex.normSq z) * ‖fderiv ℝ (s7dc_cutoff n) z‖ =
          2 * (((n : ℝ) + 2) * (1 - Complex.normSq z)) *
            (‖deriv Real.smoothTransition s‖ * ‖z‖) := by rw [s7dc_fderiv_norm]; dsimp [s]; ring
      _ ≤ 2 * 2 * (C * 1) := by
        gcongr
        exact (hb s).1
      _ = 4 * C := by ring

/-- The actual first derivative eventually vanishes at each interior point. -/
theorem s7dc_eventually_fderiv_zero {z : ℂ} (hz : z ∈ unitDisc) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (s7dc_cutoff n) z = 0 := by
  filter_upwards [s7dc_eventually_one hz] with n hn
  simpa using hn.fderiv_eq (𝕜 := ℝ)

end TakhtajanTeo
