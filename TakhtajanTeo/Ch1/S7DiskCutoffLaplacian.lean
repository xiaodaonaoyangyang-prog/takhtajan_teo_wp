import TakhtajanTeo.Ch1.S7DiskCutoffDeriv

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Chain rule for a real radial profile, followed by the actual complex inclusion. -/
theorem s7dc_radial_hasFDerivAt (N : ℝ) (θ : ℝ → ℝ) (z : ℂ)
    (hθ : DifferentiableAt ℝ θ (N * (1 - Complex.normSq z) - 1)) :
    HasFDerivAt (fun w : ℂ => (θ (N * (1 - Complex.normSq w) - 1) : ℂ))
      (Complex.ofRealCLM.comp
        (deriv θ (N * (1 - Complex.normSq z) - 1) • ((-2 * N) • innerSL ℝ z))) z := by
  have hq : HasFDerivAt (fun w : ℂ => Complex.normSq w) (2 • innerSL ℝ z) z := by
    simpa only [Complex.normSq_eq_norm_sq] using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hs : HasFDerivAt (fun w : ℂ => N * (1 - Complex.normSq w) - 1)
      ((-2 * N) • innerSL ℝ z) z := by
    convert (((hasFDerivAt_const (1 : ℝ) z).sub hq).const_mul N).sub_const 1 using 1
    ext v
    simp
    ring
  exact Complex.ofRealCLM.hasFDerivAt.comp z (hθ.hasDerivAt.comp_hasFDerivAt z hs)

theorem s7dc_radial_wirtinger (N : ℝ) (θ : ℝ → ℝ) (z : ℂ)
    (hθ : DifferentiableAt ℝ θ (N * (1 - Complex.normSq z) - 1)) :
    dzbar (fun w : ℂ => (θ (N * (1 - Complex.normSq w) - 1) : ℂ)) z =
      -(N : ℂ) * ((deriv θ (N * (1 - Complex.normSq z) - 1) : ℝ) : ℂ) * z ∧
    dz (fun w : ℂ => (θ (N * (1 - Complex.normSq w) - 1) : ℂ)) z =
      -(N : ℂ) * ((deriv θ (N * (1 - Complex.normSq z) - 1) : ℝ) : ℂ) * conj z := by
  have he := (s7dc_radial_hasFDerivAt N θ z hθ).fderiv
  constructor <;> simp only [dzbar, dz, he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, Complex.inner, smul_eq_mul]
  all_goals
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Actual mixed Wirtinger derivative of a twice differentiable radial profile. -/
theorem s7dc_radial_second (N : ℝ) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ 2 θ) (z : ℂ) :
    dz (dzbar (fun w : ℂ => (θ (N * (1 - Complex.normSq w) - 1) : ℂ))) z =
      ((N ^ 2 * deriv (deriv θ) (N * (1 - Complex.normSq z) - 1) * Complex.normSq z -
        N * deriv θ (N * (1 - Complex.normSq z) - 1) : ℝ) : ℂ) := by
  let F : ℂ → ℂ := fun w => ((deriv θ (N * (1 - Complex.normSq w) - 1) : ℝ) : ℂ)
  have hf : DifferentiableAt ℝ F z :=
    (s7dc_radial_hasFDerivAt N (deriv θ) z (hθ.differentiable_deriv_two _)).differentiableAt
  have hfirst : dzbar (fun w : ℂ => (θ (N * (1 - Complex.normSq w) - 1) : ℂ)) =
      fun w => -(N : ℂ) * F w * w := by
    funext w
    exact (s7dc_radial_wirtinger N θ w (hθ.differentiable (by norm_num) _)).1
  rw [hfirst]
  have hp : dz (fun w => -(N : ℂ) * F w * w) z =
      -(N : ℂ) * F z + (-(N : ℂ)) * z * dz F z := by
    have hP := (hf.hasFDerivAt.const_mul (-(N : ℂ))).mul (hasFDerivAt_id z)
    change HasFDerivAt (fun w : ℂ => -(N : ℂ) * F w * w) _ z at hP
    unfold dz
    rw [hP.fderiv]
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hp, (s7dc_radial_wirtinger N (deriv θ) z (hθ.differentiable_deriv_two _)).2]
  simp only [F, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- The actual cutoff Laplacian, including its weight. -/
theorem s7dc_laplace (n : ℕ) (z : ℂ) :
    laplace0 (fun w => (s7dc_cutoff n w : ℂ)) z =
      ((-(1 - Complex.normSq z) ^ 2 / 4 *
        (((n : ℝ) + 2) ^ 2 * deriv (deriv Real.smoothTransition)
          (((n : ℝ) + 2) * (1 - Complex.normSq z) - 1) * Complex.normSq z -
        ((n : ℝ) + 2) * deriv Real.smoothTransition
          (((n : ℝ) + 2) * (1 - Complex.normSq z) - 1)) : ℝ) : ℂ) := by
  simp only [s7dc_cutoff]
  rw [laplace0, s7dc_radial_second _ _ Real.smoothTransition.contDiff,
    wp_rho_inv_complex]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.normSq_eq_conj_mul_self]
  ring

end TakhtajanTeo
