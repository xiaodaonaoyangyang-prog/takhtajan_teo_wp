import TakhtajanTeo.Ch1.HarmonicResolventSeries

/-! Weighted resolvent Parseval with dominated series integration for Lemma 5.8 (TT:2444–2462). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_radial_weight_circleAverage (q : ℝ → ℝ) (F : ℂ → ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage (fun z => q ‖z‖ * ‖F z‖ ^ 2) 0 r =
      q r * Real.circleAverage (fun z => ‖F z‖ ^ 2) 0 r := by
  calc
    _ = Real.circleAverage (fun z => q r • ‖F z‖ ^ 2) 0 r := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = r := by simpa only [mem_sphere_zero_iff_norm, abs_of_nonneg hr] using hz
      simpa only [hn, smul_eq_mul]
    _ = _ := Real.circleAverage_fun_smul

theorem wp_radial_weight_series_integral {F : ℂ → ℂ} {c : ℕ → ℂ} {q : ℝ → ℝ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    (hf : ContinuousOn F unitDisc) (hm : Measurable F) (hq : Measurable q)
    (hq0 : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ q r)
    (hi : IntegrableOn (fun z => q ‖z‖ * ‖F z‖ ^ 2) unitDisc) :
    HasSum (fun n => ∫ r in Ioo (0 : ℝ) 1,
      2 * π * r * q r * (‖c n‖ ^ 2 * r ^ (2 * n)))
      (∫ z in unitDisc, q ‖z‖ * ‖F z‖ ^ 2) := by
  let H : ℂ → ℝ := fun z => q ‖z‖ * ‖F z‖ ^ 2
  let P : ℕ → ℝ → ℝ := fun n r => 2 * π * r * q r * (‖c n‖ ^ 2 * r ^ (2 * n))
  have hHm : Measurable H := (hq.comp measurable_norm).mul (hm.norm.pow_const 2)
  have hP (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      HasSum (fun n => P n r) (2 * π * r * Real.circleAverage H 0 r) := by
    have h := (wp_disk_series_circle_energy hc hf hr.1.le hr.2).mul_left (2 * π * r * q r)
    simpa only [H, P, wp_radial_weight_circleAverage q F hr.1.le, mul_assoc] using h
  have hPi : IntegrableOn (fun r => ∑' n, P n r) (Ioo (0 : ℝ) 1) := by
    apply (wp_disk_circleAverage_integrable hHm hi).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hP r hr).tsum_eq.symm
  have hPn (n : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : 0 ≤ P n r := by
    dsimp [P]
    have hqr := hq0 r hr
    have hr0 := hr.1.le
    positivity
  have hs := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (F := P)
    (f := fun r => 2 * π * r * Real.circleAverage H 0 r) P
    (fun n => by dsimp [P]; exact
      ((((measurable_const.mul measurable_id).mul hq).mul
        (measurable_const.mul (measurable_id.pow_const _)))).aestronglyMeasurable)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [Real.norm_of_nonneg (hPn n hr)])
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hP r hr).summable)
    hPi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hP r hr)
  rw [← wp_disk_integral_circleAverage hHm hi] at hs
  exact hs

theorem wp_resolvent_series_parseval {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    (hf : ContinuousOn F unitDisc) (hm : Measurable F)
    (hi : IntegrableOn (fun z => resolventKernel 0 z * ‖F z‖ ^ 2 * (rho z)⁻¹) unitDisc) :
    HasSum (fun n => ‖c n‖ ^ 2 /
      (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2))
      (∫ z in unitDisc, resolventKernel 0 z * ‖F z‖ ^ 2 * (rho z)⁻¹) := by
  let q : ℝ → ℝ := fun r => resolventKernel 0 (r : ℂ) * (rho (r : ℂ))⁻¹
  have hqm : Measurable q := by
    have hG : Measurable (fun r : ℝ => resolventKernel 0 (r : ℂ)) := by
      simp_rw [resolvent_center_radius_log_formula]
      fun_prop
    have hρ : Measurable rho :=
      measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
    exact hG.mul (hρ.comp Complex.continuous_ofReal.measurable).inv
  have hq0 (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : 0 ≤ q r := by
    have hz : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
    have hrr : (r : ℂ) ∈ unitDisc := by
      simpa only [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1] using hr.2
    have hne : (0 : ℂ) ≠ (r : ℂ) := by exact_mod_cast hr.1.ne
    exact mul_nonneg (RK2 hne (Or.inl ⟨hz, hrr⟩)).le (by unfold rho; positivity)
  have hqval (z : ℂ) : q ‖z‖ = resolventKernel 0 z * (rho z)⁻¹ := by
    simp [q, resolventKernel, pointPair, rho, Complex.norm_real, abs_of_nonneg (norm_nonneg z)]
  have hfun : (fun z => q ‖z‖ * ‖F z‖ ^ 2) =
      (fun z => resolventKernel 0 z * ‖F z‖ ^ 2 * (rho z)⁻¹) := by
    funext z
    rw [hqval]
    ring
  have hi' : IntegrableOn (fun z => q ‖z‖ * ‖F z‖ ^ 2) unitDisc := by
    rwa [hfun]
  have hs := wp_radial_weight_series_integral hc hf hm hqm hq0 hi'
  rw [hfun] at hs
  have he (n : ℕ) : (∫ r in Ioo (0 : ℝ) 1,
      2 * π * r * q r * (‖c n‖ ^ 2 * r ^ (2 * n))) =
      ‖c n‖ ^ 2 / (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) := by
    calc
      _ = ‖c n‖ ^ 2 * ∫ r in Ioo (0 : ℝ) 1,
          2 * π * r * (resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with r
        dsimp [q]
        ring
      _ = _ := by rw [wp_resolvent_moment_radius_integral]; ring
  simp_rw [he] at hs
  exact hs

end TakhtajanTeo


