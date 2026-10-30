import TakhtajanTeo.Ch1.QCVariationBergman

/-!
# The kernel of the infinitesimal Bers map

The exterior test space includes regularity of quadratic differentials at infinity.
The fourth-order Cauchy kernels satisfy this condition explicitly.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- Fourth-order Cauchy kernels have the decay required at infinity. -/
theorem qcv_cauchyKernel_decay (z : ℂ) :
    ∃ C R : ℝ, ∀ w : ℂ, R < ‖w‖ →
      ‖(1 : ℂ) / (w - z) ^ 4‖ ≤ C / ‖w‖ ^ 4 := by
  refine ⟨16, 2 * ‖z‖ + 1, ?_⟩
  intro w hw
  have hw0 : 0 < ‖w‖ := by linarith [norm_nonneg z]
  have hdist : ‖w‖ / 2 ≤ ‖w - z‖ := by
    have := norm_sub_norm_le w z
    linarith
  have hd0 : 0 < ‖w - z‖ := lt_of_lt_of_le (by positivity) hdist
  simp only [norm_div, norm_one, norm_pow]
  rw [div_le_div_iff₀ (pow_pos hd0 4) (pow_pos hw0 4)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖ / 2) hdist 4
  nlinarith

/-- Every evaluation kernel of the Bers derivative is an admissible test. -/
theorem qcv_cauchyKernel_mem_AOneStar {z : ℂ} (hz : z ∈ unitDisc) :
    (fun w : ℂ => (1 : ℂ) / (w - z) ^ 4) ∈ AOneStar := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hkernel : Measurable (fun w : ℂ => (1 : ℂ) / (w - z) ^ 4) := by
    fun_prop
  refine ⟨?_, ?_, qcv_cauchyKernel_decay z⟩
  · intro w hw
    have hwz : w - z ≠ 0 := by
      intro he
      have he' := sub_eq_zero.mp he
      have hw1 : 1 < ‖w‖ := hw
      rw [he'] at hw1
      linarith
    exact (differentiableWithinAt_const (c := (1 : ℂ))).div
      ((differentiableWithinAt_id.sub_const z).pow 4) (pow_ne_zero 4 hwz)
  · have hmajor : IntegrableOn
        (fun w => (12 / (1 - ‖z‖) ^ 4) * ‖ahKer (-1) w‖) unitDiscExterior :=
      ((ah_ker_integrable (-1)).norm.const_mul _).integrableOn
    apply hmajor.mono' hkernel.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hmeas] with w hw
    have hb := (qcv_ker_majorant (norm_nonneg z) hz1 le_rfl hw).2.2.2
    have hh : ‖(1 : ℂ) / (w - z) ^ 4‖ ≤ ‖kerD3 z w‖ := by
      simp only [kerD3, norm_div, norm_pow, norm_one]
      norm_num only [Complex.norm_ofNat]
      gcongr
      norm_num
    exact hh.trans hb

/-- The annihilator of exterior quadratic differentials is killed by the Bers derivative. -/
theorem qcv_trivialBeltrami_le_ker_D0Phi :
    trivialBeltrami ≤ LinearMap.ker
      (fderiv ℂ bersPhi 0 : LinfStar →ₗ[ℂ] AInf unitDisc) := by
  apply Submodule.span_le.mpr
  intro μ hμ
  change fderiv ℂ bersPhi 0 μ = 0
  apply AInf.ext_toFun_disc
  intro z hz
  rw [qcv_eq_1_4 μ z hz]
  have hzero := hμ (fun w : ℂ => (1 : ℂ) / (w - z) ^ 4)
    (qcv_cauchyKernel_mem_AOneStar hz)
  simp only [mul_one_div] at hzero
  rw [hzero]
  simp [AInf.toFun, unweight, hz]

end QCV
end TakhtajanTeo
