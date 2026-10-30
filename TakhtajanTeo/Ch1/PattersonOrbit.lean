import TakhtajanTeo.Ch1.PattersonNormalization
import TakhtajanTeo.Ch1.ResolventGammaMass

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem pat_fundDomain_volume_ne_zero {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    volume (fundDomain Γ) ≠ 0 := by
  intro hz
  have hh := fd_unfold hΓ (isFundDomain_fundDomain hΓ) (fun _ => (1 : ℝ≥0∞))
  have hm : volume.restrict (fundDomain Γ) = 0 := Measure.restrict_eq_zero.mpr hz
  simp only [hm, lintegral_zero_measure, tsum_zero, lintegral_const, one_mul,
    Measure.restrict_apply_univ] at hh
  have hp : 0 < volume unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measure_pos _
      ⟨(2 : ℂ), by change 1 < ‖(2 : ℂ)‖; norm_num⟩
  exact hp.ne' hh

theorem pat_hypArea_pos {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    0 < hypArea Γ := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun z => ENNReal.ofReal (rho z)) := by unfold rho; fun_prop
  have hae := (lintegral_eq_zero_iff hm).mp hz
  have hf : ∀ᵐ z ∂volume.restrict (fundDomain Γ), False := by
    filter_upwards [hae, ae_restrict_mem (fundDomain_measurable Γ)] with z hz hzF
    have he : 1 < ‖z‖ := fundDomain_subset Γ hzF
    have hn : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
    have hp : 0 < rho z := div_pos (by norm_num) (sq_pos_of_ne_zero hn)
    exact hp.not_ge (ENNReal.ofReal_eq_zero.mp hz)
  have hv : volume (fundDomain Γ) = 0 := by simpa using hf
  exact pat_fundDomain_volume_ne_zero hΓ hv

theorem pat_hypArea_toReal_pos {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    0 < (hypArea Γ).toReal := ENNReal.toReal_pos (pat_hypArea_pos hΓ.1).ne' hΓ.2.ne

/-- The hyperbolic density on a fundamental domain, counted once per distinct
group action whose image lies in the truncated exterior. -/
def patOrbitDensity (Γ : Subgroup SL2C) (r : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
    ENNReal.ofReal (rho w) * (discExteriorR r).indicator (fun _ => 1) ((a : ℂ → ℂ) w)

theorem pat_orbit_density_measurable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) (r : ℝ) :
    Measurable (patOrbitDensity Γ r) := by
  letI : DiscreteTopology Γ := hΓ.2
  letI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    ((fd_countable (Γ := Γ)).image _).to_subtype
  apply Measurable.ennreal_tsum
  intro a
  exact gam_rho_measurable.ennreal_ofReal.mul
    ((measurable_const.indicator (pat_discExteriorR_measurable r)).comp
      (gam_action_measurable Γ a))

theorem pat_orbit_density_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {r : ℝ} (hr : 1 < r) :
    (∫⁻ w in fundDomain Γ, patOrbitDensity Γ r w) = ENNReal.ofReal (4 * π / (r ^ 2 - 1)) := by
  letI : DiscreteTopology Γ := hΓ.2
  letI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    ((fd_countable (Γ := Γ)).image _).to_subtype
  have hmass : (∫⁻ z in unitDiscExterior,
      (discExteriorR r).indicator (fun z => ENNReal.ofReal (rho z)) z) =
      ENNReal.ofReal (4 * π / (r ^ 2 - 1)) := by
    rw [lintegral_indicator (pat_discExteriorR_measurable r), Measure.restrict_restrict
      (pat_discExteriorR_measurable r), inter_eq_left.mpr
      (show discExteriorR r ⊆ unitDiscExterior from fun _ hz => hz.1)]
    rw [← ofReal_integral_eq_lintegral_ofReal (pat_rho_integrable hr)
      (Eventually.of_forall fun z => div_nonneg (by norm_num) (sq_nonneg _)), pat_rho_integral hr]
  rw [← hmass, fd_unfold hΓ (isFundDomain_fundDomain hΓ)]
  unfold patOrbitDensity
  rw [lintegral_tsum]
  · apply tsum_congr
    rintro ⟨_, g, hg, rfl⟩
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume))] with w hw
    by_cases he : mob g w ∈ discExteriorR r
    · simp only [indicator_of_mem he, mul_one]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      exact (mul_comm _ _).trans (gam_rho_mob_jacobian (hΓ.1 g hg) hw) |>.symm
    · simp only [indicator_of_notMem he, mul_zero]
  · intro a
    exact (gam_rho_measurable.ennreal_ofReal.mul
      ((measurable_const.indicator (pat_discExteriorR_measurable r)).comp
        (gam_action_measurable Γ a))).aemeasurable

theorem pat_orbit_density_finite_ae {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) :
    ∀ᵐ w ∂volume.restrict (fundDomain Γ), patOrbitDensity Γ r w < ∞ := by
  apply ae_lt_top (pat_orbit_density_measurable hΓ r)
  rw [pat_orbit_density_mass hΓ hr]
  exact ENNReal.ofReal_ne_top

def patProbabilityDensity (Γ : Subgroup SL2C) (r : ℝ) (w : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (4 * π / (r ^ 2 - 1)))⁻¹ * patOrbitDensity Γ r w

theorem pat_probability_density_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) :
    (∫⁻ w in fundDomain Γ, patProbabilityDensity Γ r w) = 1 := by
  unfold patProbabilityDensity
  rw [lintegral_const_mul _ (pat_orbit_density_measurable hΓ r),
    pat_orbit_density_mass hΓ hr]
  apply ENNReal.inv_mul_cancel
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (div_pos (mul_pos (by norm_num) Real.pi_pos) (by nlinarith)))
  · exact ENNReal.ofReal_ne_top

/-- Exact unfolding with an automorphic nonnegative test. This identity does
not assert convergence of the orbit densities. -/
theorem pat_orbit_test_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) (r : ℝ)
    {h : ℂ → ℝ≥0∞} (hm : Measurable h)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫⁻ z in discExteriorR r, h z * ENNReal.ofReal (rho z)) =
      ∫⁻ w in fundDomain Γ, h w * patOrbitDensity Γ r w := by
  letI : DiscreteTopology Γ := hΓ.2
  letI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    ((fd_countable (Γ := Γ)).image _).to_subtype
  have hcut : (∫⁻ z in unitDiscExterior,
      (discExteriorR r).indicator (fun z => h z * ENNReal.ofReal (rho z)) z) =
      ∫⁻ z in discExteriorR r, h z * ENNReal.ofReal (rho z) := by
    rw [lintegral_indicator (pat_discExteriorR_measurable r), Measure.restrict_restrict
      (pat_discExteriorR_measurable r), inter_eq_left.mpr
      (show discExteriorR r ⊆ unitDiscExterior from fun _ hz => hz.1)]
  rw [← hcut, fd_unfold hΓ (isFundDomain_fundDomain hΓ)]
  have hexp : (fun w => h w * patOrbitDensity Γ r w) =
      fun w => ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        h w * (ENNReal.ofReal (rho w) *
          (discExteriorR r).indicator (fun _ => 1) ((a : ℂ → ℂ) w)) := by
    funext w
    exact ENNReal.tsum_mul_left.symm
  rw [hexp, lintegral_tsum]
  · apply tsum_congr
    rintro ⟨_, g, hg, rfl⟩
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume)),
      ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) (ha g hg)] with w hw hauto
    by_cases he : mob g w ∈ discExteriorR r
    · simp only [indicator_of_mem he, mul_one, hauto]
      rw [mul_left_comm (ENNReal.ofReal _),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      exact (mul_comm _ _).trans (gam_rho_mob_jacobian (hΓ.1 g hg) hw)
    · simp only [indicator_of_notMem he, mul_zero]
  · intro a
    exact (hm.mul (gam_rho_measurable.ennreal_ofReal.mul
      ((measurable_const.indicator (pat_discExteriorR_measurable r)).comp
        (gam_action_measurable Γ a)))).aemeasurable

end TakhtajanTeo
