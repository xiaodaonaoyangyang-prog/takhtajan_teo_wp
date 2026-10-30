import TakhtajanTeo.Ch1.HarmonicKernelIntegrability

/-! Weighted holomorphic moments for the resolvent double-kernel identity (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_complex_circleMap_integral (F : ℂ → ℂ) (r : ℝ) :
    (∫ θ in Ioo (-π) π, F (circleMap 0 r θ)) =
      (2 * π : ℝ) • Real.circleAverage F 0 r := by
  have h := Real.circleAverage_eq_integral_add (f := F) (c := 0) (R := r) (-π)
  rw [intervalIntegral.integral_comp_add_right (fun θ => F (circleMap 0 r θ))] at h
  simp only [zero_add, show 2 * π + -π = π by ring] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at h
  rw [h, smul_smul, mul_inv_cancel₀ Real.two_pi_pos.ne', one_smul]

theorem wp_complex_disk_polar_integral {F : ℂ → ℂ}
    (hm : Measurable F) (hi : IntegrableOn F unitDisc) :
    (∫ w in unitDisc, F w) =
      ∫ r in Ioo (0 : ℝ) 1, (2 * π * r : ℝ) • Real.circleAverage F 0 r := by
  have hp := integrableOn_polar_of_integrableOn_ball hm hi
  change (∫ w in ball (0 : ℂ) 1, F w) = _
  rw [setIntegral_ball_zero_polar F 1, setIntegral_polar_fubini' hp]
  apply integral_congr_ae
  filter_upwards with r
  have he (θ : ℝ) : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    simpa using polarCoord_symm_add_eq_circleMap 0 r θ
  simp_rw [he]
  rw [integral_const_mul, wp_complex_circleMap_integral]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem wp_disk_series_circle_moment {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    Real.circleAverage (fun w => F w * conj w ^ n) 0 r = c n * (r : ℂ) ^ (2 * n) := by
  have he (θ : ℝ) : F (circleMap 0 r θ) * conj (circleMap 0 r θ) ^ n =
      (r : ℂ) ^ n * (F ((r : ℂ) * exp (θ * I)) * exp (-((n : ℤ) * θ * I))) := by
    simp only [circleMap, zero_add, map_mul, map_pow, Complex.conj_ofReal,
      ← Complex.exp_conj, Complex.conj_I, mul_neg, mul_pow]
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hmean : Real.circleAverage (fun w => F w * conj w ^ n) 0 r =
      (r : ℂ) ^ n * fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) (n : ℤ) := by
    unfold Real.circleAverage fourierCoeff
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat, one_div]
    ring
  rw [hmean, disk_series_fourierCoeff hc hr0 hr1]
  rw [Nat.mul_comm 2 n, pow_mul]
  ring

theorem wp_weighted_monomial_integrable {F : ℂ → ℂ} (hf : Measurable F)
    {M : ℝ} (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) (n : ℕ) :
    IntegrableOn (fun w => F w * conj w ^ n * (rho w : ℂ)⁻¹) unitDisc := by
  have hρ : Continuous (fun w : ℂ => (rho w : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  have hm : Measurable (fun w => F w * conj w ^ n * (rho w : ℂ)⁻¹) :=
    (hf.mul (Complex.continuous_conj.measurable.pow_const n)).mul hρ.measurable
  have hI : IntegrableOn (fun _ : ℂ => M) unitDisc :=
    (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      ball_subset_closedBall
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hr : 0 < rho w := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
  simp only [norm_mul, norm_pow, norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  calc
    _ = (‖F w‖ * (rho w)⁻¹) * ‖w‖ ^ n := by ring
    _ ≤ ‖F w‖ * (rho w)⁻¹ := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg w) (mem_ball_zero_iff.mp hw).le)
    _ ≤ M := hB w hw

theorem wp_disk_series_weighted_circle_moment {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    Real.circleAverage (fun w => F w * conj w ^ n * (rho w : ℂ)⁻¹) 0 r =
      (rho (r : ℂ) : ℂ)⁻¹ * (c n * (r : ℂ) ^ (2 * n)) := by
  have he : Real.circleAverage (fun w => F w * conj w ^ n * (rho w : ℂ)⁻¹) 0 r =
      (rho (r : ℂ) : ℂ)⁻¹ • Real.circleAverage (fun w => F w * conj w ^ n) 0 r := by
    rw [← Real.circleAverage_fun_smul]
    apply Real.circleAverage_congr_sphere
    intro w hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere_zero_iff_norm, abs_of_nonneg hr0] using hw
    have hρ : rho w = rho (r : ℂ) := by
      simp only [rho, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    simp only [hρ, smul_eq_mul]
    ring
  rw [he, wp_disk_series_circle_moment hc hr0 hr1 n, smul_eq_mul]

theorem wp_disk_series_weighted_moment {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hf : Measurable F) {M : ℝ} (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) (n : ℕ) :
    (∫ w in unitDisc, F w * conj w ^ n * (rho w : ℂ)⁻¹) =
      (π / 2 : ℂ) * c n / ((n + 1 : ℂ) * (n + 2) * (n + 3)) := by
  have hρ : Continuous (fun w : ℂ => (rho w : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  have hm : Measurable (fun w => F w * conj w ^ n * (rho w : ℂ)⁻¹) :=
    (hf.mul (Complex.continuous_conj.measurable.pow_const n)).mul hρ.measurable
  rw [wp_complex_disk_polar_integral hm (wp_weighted_monomial_integrable hf hB n)]
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1,
        (π / 2 : ℂ) * c n * ((r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [wp_disk_series_weighted_circle_moment hc hr.1.le hr.2 n]
      simp only [Complex.real_smul, ← Complex.ofReal_inv, rho, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1, inv_div, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat, pow_succ]
      ring
    _ = (π / 2 : ℂ) * c n * ((∫ r in (0 : ℝ)..1,
        r ^ (2 * n + 1) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) := by
      rw [integral_const_mul, integral_complex_ofReal,
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = _ := by
      rw [bergman_radial_moment]
      push_cast
      ring

end TakhtajanTeo


