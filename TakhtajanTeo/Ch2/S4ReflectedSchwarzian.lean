import TakhtajanTeo.Ch2.S4PlaneVariation

/-! # Schwarzian parameter derivative of the actual reflected plane family

This is the antiholomorphic coefficient direction in the two-parameter
Model A construction. The remaining identification with that full family
is not assumed here.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- L13
theorem s4v_reflected_schwarzian (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    IntegrableOn (fun w => conj (ν w) / (1 - conj w * z) ^ 4) unitDiscExterior ∧
    HasDerivAt (fun t : ℂ => schwarzianHol
      (normalizedSolution (fun u => t * unitDisc.indicator (extA ν) u)) z)
      (-(6 / π : ℂ) * ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4) 0 := by
  refine ⟨s4v_kernel_integrable_bound (norm_nonneg ν) (Lp.aestronglyMeasurable ν)
    (LinfStar_ae_norm_le ν) hz, ?_⟩
  have hb : IsBeltramiCoeff (unitDisc.indicator (extA ν)) univ ‖ν‖ := by
    have hm := (extA_isBeltramiCoeff ν).1
    rw [Measure.restrict_univ] at hm
    have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
    refine ⟨by simpa only [Measure.restrict_univ] using hm.indicator hD, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [extA_ae_norm_le ν] with u hu
    by_cases h : u ∈ unitDisc
    · simpa only [indicator_of_mem h] using hu
    · simp only [indicator_of_notMem h, norm_zero]
      exact norm_nonneg ν
  have hzero : ∀ u ∈ unitDiscExterior, unitDisc.indicator (extA ν) u = 0 := by
    intro u hu
    exact indicator_of_notMem (fun h => (not_lt_of_ge hu.le) (mem_ball_zero_iff.mp h)) _
  simpa only [s4v_reflected_kernel ν hz] using
    s4v_normalized_schwarzian_variation (norm_nonneg ν) hb wp_exterior_isOpen hzero hz

-- L14
theorem s4v_reflected_schwarzian_harmonic {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasDerivAt (fun t : ℂ => schwarzianHol
      (normalizedSolution (fun u => t * unitDisc.indicator (extA (toLinf ν)) u)) z)
      (-(conj (ν z) * (rho z : ℂ) / 2)) 0 := by
  have hd := (s4v_reflected_schwarzian (toLinf ν) hz).2
  have hi : (∫ w in unitDiscExterior, conj ((toLinf ν) w) / (1 - conj w * z) ^ 4) =
      ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [wp_harmonic_toLinf_ae hν] with w hw
    rw [hw]
  convert hd using 1
  rw [hi, neg_mul, s4v_kernel_reproduce hν hz]

end Ch2
end TakhtajanTeo
