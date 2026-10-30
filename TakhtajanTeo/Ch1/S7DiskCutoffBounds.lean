import TakhtajanTeo.Ch1.S7DiskCutoffLaplacian

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual hyperbolic Laplacians are uniformly bounded over the entire exhaustion. -/
theorem s7dc_laplace_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z ∈ unitDisc,
      ‖laplace0 (fun w => (s7dc_cutoff n w : ℂ)) z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := s7dc_transition_deriv_bounds
  refine ⟨2 * C, by positivity, fun n z hz => ?_⟩
  let N : ℝ := (n : ℝ) + 2
  let Q : ℝ := Complex.normSq z
  let δ : ℝ := 1 - Q
  let s : ℝ := N * δ - 1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hQ : 0 ≤ Q := Complex.normSq_nonneg _
  have hQ1 : Q < 1 := by
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
    dsimp [Q]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hδ : 0 ≤ δ := sub_nonneg.mpr hQ1.le
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  have he := s7dc_laplace n z
  change laplace0 (fun w => (s7dc_cutoff n w : ℂ)) z =
    ((-δ ^ 2 / 4 * (N ^ 2 * deriv (deriv Real.smoothTransition) s * Q -
      N * deriv Real.smoothTransition s) : ℝ) : ℂ) at he
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_pow,
    abs_of_nonneg hδ]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · have hNd : N * δ ≤ 2 := by have := hs.2; dsimp [s] at this; linarith
    have hNd0 : 0 ≤ N * δ := mul_nonneg hN hδ
    have hNd2 : (N * δ) ^ 2 ≤ 4 := by nlinarith
    have ha : |N ^ 2 * deriv (deriv Real.smoothTransition) s * Q -
        N * deriv Real.smoothTransition s| ≤ N ^ 2 * C * Q + N * C := by
      calc
        _ ≤ |N ^ 2 * deriv (deriv Real.smoothTransition) s * Q| +
          |N * deriv Real.smoothTransition s| := abs_sub _ _
        _ = N ^ 2 * ‖deriv (deriv Real.smoothTransition) s‖ * Q +
          N * ‖deriv Real.smoothTransition s‖ := by
            simp only [abs_mul, abs_pow, abs_of_nonneg hN, abs_of_nonneg hQ,
              Real.norm_eq_abs]
        _ ≤ N ^ 2 * C * Q + N * C := by
          gcongr
          · exact (hb s).2
          · exact (hb s).1
    calc
      _ ≤ δ ^ 2 / 4 * (N ^ 2 * C * Q + N * C) := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = ((N * δ) ^ 2 * C * Q + (N * δ) * C * δ) / 4 := by ring
      _ ≤ (4 * C * 1 + 2 * C * 1) / 4 := by gcongr
      _ ≤ 2 * C := by nlinarith
  · have h0 : deriv Real.smoothTransition s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hs (s7dc_transition_deriv_support ht))
    have h1 : deriv (deriv Real.smoothTransition) s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hs
        (s7dc_transition_deriv_support (tsupport_deriv_subset ht)))
    simp only [h0, h1, mul_zero, zero_mul, sub_zero, abs_zero]
    positivity

/-- At every interior point the actual Laplacian eventually vanishes. -/
theorem s7dc_eventually_laplace_zero {z : ℂ} (hz : z ∈ unitDisc) :
    ∀ᶠ n : ℕ in atTop, laplace0 (fun w => (s7dc_cutoff n w : ℂ)) z = 0 := by
  filter_upwards [s7dc_eventually_one hz] with n hn
  have hc : (fun w => (s7dc_cutoff n w : ℂ)) =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
    filter_upwards [hn] with w hw
    simp only [hw, Complex.ofReal_one]
  have hb : dzbar (fun w => (s7dc_cutoff n w : ℂ)) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hc.fderiv (𝕜 := ℝ)] with w hw
    simp [dzbar, hw]
  have hh := hb.fderiv_eq (𝕜 := ℝ)
  simp [laplace0, dz, hh]

end TakhtajanTeo
