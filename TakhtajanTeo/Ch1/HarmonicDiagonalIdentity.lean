import TakhtajanTeo.Ch1.HarmonicDoubleMoments

/-! The diagonal disk resolvent identity from weighted moments and Abel convergence (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_diagonal_kernel_identity {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hFc : ContinuousOn F unitDisc) (hf : Measurable F)
    {M : ℝ} (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) :
    (∫ p : ℂ × ℂ, (conj (F p.1) * (rho p.1 : ℂ)⁻¹) *
      (F p.2 * (rho p.2 : ℂ)⁻¹) *
        (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      (π ^ 2 / 2 : ℂ) * ((∫ w in unitDisc,
        resolventKernel 0 w * ‖F w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ) := by
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hM : 0 ≤ M :=
    (mul_nonneg (norm_nonneg _) (by unfold rho; positivity)).trans (hB 0 hzero)
  have hρ : Continuous (fun w : ℂ => (rho w : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  let f : ℂ → ℂ := fun w => conj (F w) * (rho w : ℂ)⁻¹
  let g : ℂ → ℂ := fun w => F w * (rho w : ℂ)⁻¹
  have hfm : Measurable f := (Complex.continuous_conj.measurable.comp hf).mul hρ.measurable
  have hgm : Measurable g := hf.mul hρ.measurable
  have hfb (w : ℂ) (hw : w ∈ unitDisc) : ‖f w‖ ≤ M := by
    have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
    simpa only [f, norm_mul, norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hB w hw
  have hgb (w : ℂ) (hw : w ∈ unitDisc) : ‖g w‖ ≤ M := by
    have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
    simpa only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hB w hw
  let E : ℕ → ℝ := fun n => ‖c n‖ ^ 2 /
    (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2)
  have hP : HasSum E (∫ w in unitDisc, resolventKernel 0 w * ‖F w‖ ^ 2 * (rho w)⁻¹) :=
    wp_resolvent_series_parseval hc hFc hf (wp_resolvent_quadratic_integrable hf hM hB hzero)
  have hEn (n : ℕ) : 0 ≤ E n := by dsimp [E]; positivity
  let A : ℝ → ℂ := fun t => ∫ p : ℂ × ℂ, f p.1 * g p.2 *
    (((1 - (t : ℂ) * (p.1 * conj p.2))⁻¹) ^ 2 + (1 - (t : ℂ) * (p.1 * conj p.2))⁻¹)
    ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))
  have hAt (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
      A t = (π ^ 2 / 2 : ℂ) * ((∑' n : ℕ, t ^ n * E n : ℝ) : ℂ) := by
    have hA := wp_damped_double_kernel_hasSum hfm hgm hfb hgb ht0 ht1
    have he (n : ℕ) : ((n + 2 : ℕ) : ℂ) * (t : ℂ) ^ n *
        (∫ p : ℂ × ℂ, f p.1 * g p.2 * (p.1 * conj p.2) ^ n
          ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
        (π ^ 2 / 2 : ℂ) * ((t ^ n * E n : ℝ) : ℂ) := by
      dsimp only [f, g]
      rw [wp_weighted_double_moment_diagonal hc hf hB n]
      dsimp only [E]
      push_cast
      have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
      have h2 : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
      have h3 : (n + 3 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 3 ≠ 0)
      field_simp
      <;> ring
    simp_rw [he] at hA
    have h := hA.tsum_eq.symm
    rw [tsum_mul_left, ← Complex.ofReal_tsum] at h
    exact h
  have hlimE := wp_nonnegative_abel_series_tendsto hEn hP.summable
  have hlimC := ((Complex.continuous_ofReal.tendsto _).comp hlimE).const_mul (π ^ 2 / 2 : ℂ)
  rw [hP.tsum_eq] at hlimC
  have hlimA : Tendsto A (𝓝[<] 1) (𝓝 ((π ^ 2 / 2 : ℂ) *
      ((∫ w in unitDisc, resolventKernel 0 w * ‖F w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ))) := by
    apply hlimC.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact (hAt t ht.1.le ht.2).symm
  exact tendsto_nhds_unique (wp_weighted_abel_integral_tendsto hfm hgm hfb hgb) hlimA

end TakhtajanTeo


