import TakhtajanTeo.Ch1.S7EnergyRegularity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual resolvent kernel defines a probability measure at each point. -/
theorem s7rp_probability {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) :
    IsProbabilityMeasure ((volume.restrict D).withDensity
      (fun w => ENNReal.ofReal (resolventKernel z w * rho w))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (resolvent_mass_integrable hD hz)
    (resolvent_mass_nonneg_ae hD hz), RK4 hD hz]
  norm_num

/-- The Bochner integral for the kernel probability measure is exactly G. -/
theorem s7rp_integral {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) (f : ℂ → ℂ) :
    (∫ w, f w ∂((volume.restrict D).withDensity
      (fun w => ENNReal.ofReal (resolventKernel z w * rho w)))) = resolventOp D f z := by
  have hm : Measurable (fun w => ENNReal.ofReal (resolventKernel z w * rho w)) := by
    apply Measurable.ennreal_ofReal
    exact (measurable_resolventKernel.comp (measurable_const.prodMk measurable_id)).mul
      (by unfold rho; fun_prop)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [resolvent_mass_nonneg_ae hD hz] with w hw
  simp only [ENNReal.toReal_ofReal hw, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Jensen's inequality for the actual resolvent, for every bounded measurable
input. This is the pointwise step of the L2 contraction, before Tonelli. -/
theorem s7rp_square_bound {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) {C : ℝ}
    (hb : ∀ᵐ w ∂(volume.restrict D), ‖f w‖ ≤ C) :
    ‖resolventOp D f z‖ ^ 2 ≤
      ∫ w in D, resolventKernel z w * ‖f w‖ ^ 2 * rho w := by
  let m := (volume.restrict D).withDensity
    (fun w => ENNReal.ofReal (resolventKernel z w * rho w))
  letI : IsProbabilityMeasure m := s7rp_probability hD hz
  have hac : m ≪ volume.restrict D := withDensity_absolutelyContinuous _ _
  have hfm : AEStronglyMeasurable f m := hf.mono_ac hac
  have hbm : ∀ᵐ w ∂m, ‖f w‖ ≤ C := hac.ae_le hb
  have hfi : Integrable f m := Integrable.of_bound hfm C hbm
  have hqi : Integrable (fun w => ‖f w‖ ^ 2) m := by
    apply Integrable.of_bound (hfm.norm.pow 2) (C ^ 2)
    filter_upwards [hbm] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hconv : ConvexOn ℝ (Set.univ : Set ℂ) (fun w => ‖w‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have hj := hconv.map_integral_le
    ((continuous_norm.pow 2).continuousOn) isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hfi hqi
  rw [s7rp_integral hD hz f] at hj
  have hm : Measurable (fun w => ENNReal.ofReal (resolventKernel z w * rho w)) := by
    apply Measurable.ennreal_ofReal
    exact (measurable_resolventKernel.comp (measurable_const.prodMk measurable_id)).mul
      (by unfold rho; fun_prop)
  have he : (∫ w, ‖f w‖ ^ 2 ∂m) =
      ∫ w in D, resolventKernel z w * ‖f w‖ ^ 2 * rho w := by
    rw [integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [resolvent_mass_nonneg_ae hD hz] with w hw
    simp only [ENNReal.toReal_ofReal hw, smul_eq_mul]
    ring
  exact hj.trans_eq he

end TakhtajanTeo
