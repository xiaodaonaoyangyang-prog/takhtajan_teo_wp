import TakhtajanTeo.Ch1.S1_2_Homogeneous
import References.GardinerLakic2000.Ch16.S03_SymmetricHomeomorphisms

/-! A genuine Beurling–Ahlfors extension of the normalized real lift of a QS
circle map. Descending this periodic map to the punctured disk is separate. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem circle_quasisymmetric_ahlfors {h : ℂ → ℂ}
    (hh : Pommerenke1992.IsQuasisymmetric h) : Pommerenke1992.IsQuasisymmetricA h := by
  have hc := Pommerenke1992.isQuasisymmetric_continuousOn hh
  obtain ⟨lam, hi, hm, hlc, h0, hbound⟩ := hh
  refine ⟨hc, hi, lam 1, ?_⟩
  intro z₁ hz₁ z₂ hz₂ z₃ hz₃ hdist
  by_cases h23 : z₂ = z₃
  · subst z₃
    have h12 : z₁ = z₂ := norm_sub_eq_zero_iff.mp (by simpa using hdist)
    simp [h12]
  · have hd : 0 < ‖h z₂ - h z₃‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => h23 (hi hz₂ hz₃ he)))
    have hb := hbound z₁ hz₁ z₂ hz₂ z₃ hz₃ h23
    rw [hdist, div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h23))] at hb
    exact (div_le_iff₀ hd).mp hb

theorem circle_real_quasisymmetric_lift {h : ℂ → ℂ} (hh : IsQSCircleHomeo h) :
    ∃ u : ℝ → ℝ, ∃ ρ : ℝ, GardinerLakic2000.IsCircleLift h u ∧
      LiZhongQC.IsQuasisymmetric u ρ ∧
      ContDiffOn ℝ 1 (beurlingAhlfors u 1) upperHalf ∧
      HasQCExtensionH u (beurlingAhlfors u 1) (8 * ρ * (ρ + 1)) := by
  obtain ⟨u, hu⟩ := GardinerLakic2000.gl16_cl_lift hh.1
  obtain ⟨M, hM⟩ := GardinerLakic2000.gl16_cl_M_of_qsA (circle_quasisymmetric_ahlfors hh.2)
  obtain ⟨ρ, hρ⟩ := GardinerLakic2000.gl16_qs_of_M hu hM
  exact ⟨u, ρ, hu, hρ, thm17_2_beurling_ahlfors hρ⟩

theorem beurlingAhlfors_add_one {u : ℝ → ℝ} (hu : Continuous u)
    (hp : ∀ x, u (x + 1) = u x + 1) (r : ℝ) (z : ℂ) :
    beurlingAhlfors u r (z + 1) = beurlingAhlfors u r z + 1 := by
  have hplus : ∀ t : ℝ, u ((z + 1).re + t * (z + 1).im) + u ((z + 1).re - t * (z + 1).im) =
      (u (z.re + t * z.im) + u (z.re - t * z.im)) + 2 := by
    intro t
    simp only [add_re, one_re, add_im, one_im, add_zero]
    rw [show z.re + 1 + t * z.im = (z.re + t * z.im) + 1 by ring,
      show z.re + 1 - t * z.im = (z.re - t * z.im) + 1 by ring, hp, hp]
    ring
  have hminus : ∀ t : ℝ, u ((z + 1).re + t * (z + 1).im) - u ((z + 1).re - t * (z + 1).im) =
      u (z.re + t * z.im) - u (z.re - t * z.im) := by
    intro t
    simp only [add_re, one_re, add_im, one_im, add_zero]
    rw [show z.re + 1 + t * z.im = (z.re + t * z.im) + 1 by ring,
      show z.re + 1 - t * z.im = (z.re - t * z.im) + 1 by ring, hp, hp]
    ring
  have hc : Continuous (fun t : ℝ => u (z.re + t * z.im) + u (z.re - t * z.im)) :=
    (hu.comp (by fun_prop)).add (hu.comp (by fun_prop))
  have hI : (∫ t in (0 : ℝ)..1,
      u ((z + 1).re + t * (z + 1).im) + u ((z + 1).re - t * (z + 1).im)) =
      (∫ t in (0 : ℝ)..1, u (z.re + t * z.im) + u (z.re - t * z.im)) + 2 := by
    rw [show (fun t : ℝ => u ((z + 1).re + t * (z + 1).im) + u ((z + 1).re - t * (z + 1).im)) =
      (fun t => (u (z.re + t * z.im) + u (z.re - t * z.im)) + 2) from funext hplus,
      intervalIntegral.integral_add (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
    norm_num
  simp only [beurlingAhlfors, hI,
    show (fun t : ℝ => u ((z + 1).re + t * (z + 1).im) - u ((z + 1).re - t * (z + 1).im)) =
      (fun t => u (z.re + t * z.im) - u (z.re - t * z.im)) from funext hminus]
  push_cast
  ring

end TakhtajanTeo

#print axioms TakhtajanTeo.circle_real_quasisymmetric_lift
#print axioms TakhtajanTeo.beurlingAhlfors_add_one
