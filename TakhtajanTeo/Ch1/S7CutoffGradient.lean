import TakhtajanTeo.Ch1.S7DiskCutoffBounds

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Exact comparison of the real cutoff gradient and its complex Wirtinger derivative. -/
theorem s7cg_cutoff_gradient (n : ℕ) (z : ℂ) :
    2 * ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ =
      ‖fderiv ℝ (s7dc_cutoff n) z‖ := by
  have he := (s7dc_radial_wirtinger ((n : ℝ) + 2) Real.smoothTransition z
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _)).1
  change dzbar (fun w => (s7dc_cutoff n w : ℂ)) z = _ at he
  rw [he, s7dc_fderiv_norm]
  simp only [norm_mul, norm_neg, Complex.norm_real]
  rw [Real.norm_eq_abs ((n : ℝ) + 2), abs_of_nonneg (by positivity)]
  ring

/-- A genuine uniform rho-weighted bound for the cutoff derivative used in Green. -/
theorem s7cg_cutoff_gradient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z ∈ unitDisc,
      ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ ^ 2 ≤ C * rho z := by
  obtain ⟨C,hC,hb⟩ := s7dc_weighted_fderiv_bound
  refine ⟨C ^ 2, sq_nonneg C, fun n z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
  have hd : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h := hb n z hz
  rw [Complex.normSq_eq_norm_sq, ← s7cg_cutoff_gradient n z] at h
  have hn := norm_nonneg (dzbar (fun w => (s7dc_cutoff n w : ℂ)) z)
  have hsmall : (1 - ‖z‖ ^ 2) * ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ ≤ C := by
    nlinarith
  have hsq := mul_self_le_mul_self (mul_nonneg hd.le hn) hsmall
  rw [rho, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [sq_nonneg C]

end TakhtajanTeo
