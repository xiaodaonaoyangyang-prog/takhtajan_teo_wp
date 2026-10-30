import TakhtajanTeo.Ch1.PattersonOrbit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo

/-- Scheffe's argument for a countably generated filter. Pointwise density
convergence and mass convergence are explicit hypotheses. -/
theorem pat_scheffe {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {F : ι → α → ℝ} {f : α → ℝ}
    (hf : Integrable f μ) (hfn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hFn : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ F i x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hmass : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ))) :
    Tendsto (fun i => ∫ x, ‖F i x - f x‖ ∂μ) l (𝓝 0) := by
  have hmin : Tendsto (fun i => ∫ x, min (F i x) (f x) ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence f
    · filter_upwards [hFi] with i hi
      exact (hi.inf hf).aestronglyMeasurable
    · filter_upwards [hFn] with i hi
      filter_upwards [hi, hfn] with x hix hfx
      rw [Real.norm_of_nonneg (le_min hix hfx)]
      exact min_le_right _ _
    · exact hf
    · filter_upwards [hlim] with x hx
      simpa using hx.min (tendsto_const_nhds :
        Tendsto (fun _ : ι => f x) l (𝓝 (f x)))
  have heq : ∀ᶠ i in l,
      (∫ x, ‖F i x - f x‖ ∂μ) =
        (∫ x, F i x ∂μ) + (∫ x, f x ∂μ) - 2 * (∫ x, min (F i x) (f x) ∂μ) := by
    filter_upwards [hFi] with i hi
    calc _ = ∫ x, (F i x + f x) - 2 * min (F i x) (f x) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change ‖F i x - f x‖ = F i x + f x - 2 * min (F i x) (f x)
            rw [Real.norm_eq_abs]
            rcases le_total (F i x) (f x) with h | h
            · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
            · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
      _ = _ := by
        have he := integral_sub (hi.add hf) ((hi.inf hf).const_mul 2)
        simp only [Pi.add_apply, Pi.inf_apply] at he
        rw [integral_add hi hf, integral_const_mul] at he
        exact he
  have ht := (hmass.add_const (∫ x, f x ∂μ)).sub (hmin.const_mul 2)
  have ht' : Tendsto (fun i => (∫ x, F i x ∂μ) + (∫ x, f x ∂μ) -
      2 * (∫ x, min (F i x) (f x) ∂μ)) l (𝓝 0) := by
    convert ht using 1 <;> ring
  exact ht'.congr' (heq.mono fun _ h => h.symm)

theorem pat_bounded_weight_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℂ} {f : α → ℝ} {C : ℝ} (hf : Integrable f μ)
    (hm : AEStronglyMeasurable h μ) (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ C) :
    Integrable (fun x => h x * (f x : ℂ)) μ := by
  apply (hf.norm.const_mul C).mono' (hm.mul hf.ofReal.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖h x * (f x : ℂ)‖ ≤ C * ‖f x‖
  simpa only [norm_mul, Complex.norm_real] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem pat_bounded_test_of_L1 {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {F : ι → α → ℝ} {f : α → ℝ} {h : α → ℂ} {C : ℝ}
    (hf : Integrable f μ) (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hm : AEStronglyMeasurable h μ) (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ C)
    (hL1 : Tendsto (fun i => ∫ x, ‖F i x - f x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, h x * (F i x : ℂ) ∂μ) l
      (𝓝 (∫ x, h x * (f x : ℂ) ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa using hL1.const_mul C)
  filter_upwards [hFi] with i hi
  rw [← integral_sub (pat_bounded_weight_integrable hi hm hb)
    (pat_bounded_weight_integrable hf hm hb)]
  calc _ ≤ ∫ x, ‖h x * (F i x : ℂ) - h x * (f x : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖F i x - f x‖ ∂μ := by
      apply integral_mono_ae
        ((pat_bounded_weight_integrable hi hm hb).sub (pat_bounded_weight_integrable hf hm hb)).norm
        ((hi.sub hf).norm.const_mul C)
      filter_upwards [hb] with x hx
      change ‖h x * (F i x : ℂ) - h x * (f x : ℂ)‖ ≤ C * ‖F i x - f x‖
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = _ := integral_const_mul C _

theorem pat_probability_real_integrable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun w => (patProbabilityDensity Γ r w).toReal) (fundDomain Γ) := by
  have hm : Measurable (patProbabilityDensity Γ r) :=
    measurable_const.mul (pat_orbit_density_measurable hΓ r)
  apply integrable_toReal_of_lintegral_ne_top hm.aemeasurable
  rw [pat_probability_density_mass hΓ hr]
  exact ENNReal.one_ne_top

theorem pat_probability_real_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) :
    (∫ w in fundDomain Γ, (patProbabilityDensity Γ r w).toReal) = 1 := by
  have hm : Measurable (patProbabilityDensity Γ r) :=
    measurable_const.mul (pat_orbit_density_measurable hΓ r)
  have ht : ∀ᵐ w ∂volume.restrict (fundDomain Γ), patProbabilityDensity Γ r w < ∞ := by
    apply ae_lt_top hm
    rw [pat_probability_density_mass hΓ hr]
    exact ENNReal.one_ne_top
  rw [integral_toReal hm.aemeasurable ht, pat_probability_density_mass hΓ hr, ENNReal.toReal_one]

/-- Conditional L1 convergence for the actual orbit densities. The missing
lattice-count asymptotic is precisely the explicit `hlim` premise. -/
theorem pat_orbit_L1_of_ae_limit {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hlim : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patProbabilityDensity Γ r w).toReal) (𝓝[>] 1)
        (𝓝 (rho w / (hypArea Γ).toReal))) :
    Tendsto (fun r : ℝ => ∫ w in fundDomain Γ,
      ‖(patProbabilityDensity Γ r w).toReal - rho w / (hypArea Γ).toReal‖)
      (𝓝[>] 1) (𝓝 0) := by
  have hi := (rho_integrableOn_fundDomain hΓ).div_const (hypArea Γ).toReal
  apply pat_scheffe hi
  · exact Eventually.of_forall fun w => div_nonneg
      (div_nonneg (by norm_num) (sq_nonneg _)) ENNReal.toReal_nonneg
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact pat_probability_real_integrable hΓ.1 hr
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  · exact hlim
  · have htarget : (∫ w in fundDomain Γ, rho w / (hypArea Γ).toReal) = 1 := by
      rw [integral_div, pat_rho_fundDomain, div_self (pat_hypArea_toReal_pos hΓ).ne']
    rw [htarget]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (pat_probability_real_mass hΓ.1 hr).symm

theorem pat_orbit_test_limit_of_ae_limit {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    {h : ℂ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict LiZhongQC.unitDiscExterior))
    (hb : ∃ C, ∀ᵐ w ∂volume.restrict LiZhongQC.unitDiscExterior, ‖h w‖ ≤ C)
    (hlim : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patProbabilityDensity Γ r w).toReal) (𝓝[>] 1)
        (𝓝 (rho w / (hypArea Γ).toReal))) :
    Tendsto (fun r : ℝ => ∫ w in fundDomain Γ, h w * ((patProbabilityDensity Γ r w).toReal : ℂ))
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ (fun w => h w * rho w) / (hypArea Γ).toReal)) := by
  obtain ⟨C, hC⟩ := hb
  have hFi : ∀ᶠ r in 𝓝[>] (1 : ℝ),
      IntegrableOn (fun w => (patProbabilityDensity Γ r w).toReal) (fundDomain Γ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact pat_probability_real_integrable hΓ.1 hr
  have hh := pat_bounded_test_of_L1
    ((rho_integrableOn_fundDomain hΓ).div_const (hypArea Γ).toReal) hFi
    (hm.mono_set (fundDomain_subset Γ))
    (ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) hC)
    (pat_orbit_L1_of_ae_limit hΓ hlim)
  simpa only [Complex.ofReal_div, ← mul_div_assoc, integral_div, quotientIntegral] using hh

end TakhtajanTeo
