import TakhtajanTeo.Ch1.ResolventKernelEquation
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Integrable, rather than merely improper, radial Green identities. -/

open Real Filter Set Topology MeasureTheory

noncomputable section

namespace TakhtajanTeo

theorem resolvent_center_radius_log_formula (r : ℝ) :
    resolventKernel 0 (r : ℂ) =
      -(1 + r ^ 2) / (π * (1 - r ^ 2)) * Real.log r - 1 / π := by
  rw [resolvent_center_squared_profile]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, resolventSquaredProfile,
    Real.log_pow]
  by_cases hr : 1 - r ^ 2 = 0
  · simp [hr]
  · field_simp [hr]
    <;> ring

/-- The unweighted centered radial kernel is integrable even at its logarithmic endpoint. -/
theorem resolvent_center_radius_intervalIntegrable {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun r : ℝ => resolventKernel 0 (r : ℂ)) volume 0 b := by
  have hc : ContinuousOn (fun r : ℝ => -(1 + r ^ 2) / (π * (1 - r ^ 2))) (uIcc 0 b) := by
    intro r hr
    rw [uIcc_of_le hb.1.le] at hr
    have hD : π * (1 - r ^ 2) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by nlinarith [hr.1, hr.2, hb.2])
    exact (((continuousAt_const.add (continuousAt_id.pow 2)).neg.div
      (continuousAt_const.mul (continuousAt_const.sub (continuousAt_id.pow 2))) hD).continuousWithinAt)
  have hi := ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := b)).continuousOn_mul hc).sub
    (intervalIntegrable_const (c := (1 / π : ℝ)))
  convert hi using 1
  funext r
  exact resolvent_center_radius_log_formula r

/-- Integrability of the radial Green integrand for continuous test data up to the center. -/
theorem resolvent_center_green_intervalIntegrable {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc 0 b))
    (hφ' : ContinuousOn φ' (uIcc 0 b)) (hφ'' : ContinuousOn φ'' (uIcc 0 b)) :
    IntervalIntegrable (fun r : ℝ => π * resolventKernel 0 (r : ℂ) *
      (8 * r / (1 - r ^ 2) ^ 2 * φ r - φ' r - r * φ'' r)) volume 0 b := by
  have hc : ContinuousOn (fun r : ℝ => 8 * r / (1 - r ^ 2) ^ 2) (uIcc 0 b) := by
    intro r hr
    rw [uIcc_of_le hb.1.le] at hr
    have hD : (1 - r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2
      (by nlinarith [hr.1, hr.2, hb.2])
    exact (((continuousAt_const.mul continuousAt_id).div
      ((continuousAt_const.sub (continuousAt_id.pow 2)).pow 2) hD).continuousWithinAt)
  exact ((resolvent_center_radius_intervalIntegrable hb).const_mul π).mul_continuousOn
    (((hc.mul hφ).sub hφ').sub (continuousOn_id.mul hφ''))

/-- A genuine radial Green integral reproduces the center value of a C2 test function
whose value and first derivative vanish at the outer radius. -/
theorem resolvent_center_radial_green_integral {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    {φ φ' φ'' : ℝ → ℝ}
    (hφ : ∀ r, HasDerivAt φ (φ' r) r) (hφ' : ∀ r, HasDerivAt φ' (φ'' r) r)
    (hφ'' : Continuous φ'') (hbφ : φ b = 0) (hbφ' : φ' b = 0) :
    (∫ r in (0 : ℝ)..b, π * resolventKernel 0 (r : ℂ) *
      (8 * r / (1 - r ^ 2) ^ 2 * φ r - φ' r - r * φ'' r)) = φ 0 := by
  have hcφ : Continuous φ := continuous_iff_continuousAt.mpr fun r => (hφ r).continuousAt
  have hcφ' : Continuous φ' := continuous_iff_continuousAt.mpr fun r => (hφ' r).continuousAt
  have hi := resolvent_center_green_intervalIntegrable hb hcφ.continuousOn
    hcφ'.continuousOn hφ''.continuousOn
  have hc := ((intervalIntegral.continuousOn_primitive_interval' hi
    (a := b) right_mem_uIcc).neg 0 left_mem_uIcc).tendsto
  have hlim : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝[uIcc 0 b] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < b :=
      (gt_mem_nhds hb.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with a ha hab
    rw [uIcc_of_le hb.1.le]
    exact ⟨le_of_lt ha, hab.le⟩
  have ht : Tendsto (fun a : ℝ => ∫ r in a..b, π * resolventKernel 0 (r : ℂ) *
      (8 * r / (1 - r ^ 2) ^ 2 * φ r - φ' r - r * φ'' r)) (𝓝[>] 0)
      (𝓝 (∫ r in (0 : ℝ)..b, π * resolventKernel 0 (r : ℂ) *
        (8 * r / (1 - r ^ 2) ^ 2 * φ r - φ' r - r * φ'' r))) := by
    simpa only [Function.comp_def, Pi.neg_apply, intervalIntegral.integral_symm b, neg_neg]
      using hc.comp hlim
  exact tendsto_nhds_unique ht (resolvent_center_radial_green_source hb
    (fun r _ => hφ r) (fun r _ => hφ' r) hφ''.continuousOn
      hcφ.continuousAt hcφ'.continuousAt hbφ hbφ')

end TakhtajanTeo
