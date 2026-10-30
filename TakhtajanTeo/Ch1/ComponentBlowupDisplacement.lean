import TakhtajanTeo.Ch1.ComponentBlowupNormalization
import TakhtajanTeo.Ch1.Eq22BoundaryDisplacement

open Complex Set Metric Filter Topology
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The reflected evaluation point is bounded in the actual output blowup
scale whenever the corresponding normalized first derivative is bounded.
The constant comes from the real reflection geometry, not an extra premise. -/
theorem cbd_normalized_displacement {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ gsans μ '' unitDiscExterior, ‖u‖ ≤ R →
      ∀ a : ℂ, 0 < ‖a‖ → ‖a‖ < 1 → fsans μ a = h u → ∀ b : ℂ,
        ‖(u - h u) / b‖ ≤ 2 * D * ‖cbl_scale a * deriv (fsans μ) a / b‖ := by
  obtain ⟨D, hD, hgeom⟩ := eq22_reflection_bounded_displacement hμ hh R hR
  refine ⟨D, hD, ?_⟩
  intro u hu huR a ha0 ha1 he b
  have hf := S2C.s2c_conf_f hμ
  have ha : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  have hder : 0 < ‖deriv (fsans μ) a‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 ha)
  have hgap : 0 < 1 - ‖a‖^2 := by nlinarith [norm_nonneg a]
  have hden : 0 < (1 - ‖a‖^2) * ‖deriv (fsans μ) a‖ := mul_pos hgap hder
  have hg := (hgeom u hu huR).1
  rw [← he, eq22_density_formula hf ha] at hg
  have hnum : ‖u - h u‖ * 2 ≤ D * ((1 - ‖a‖^2) * ‖deriv (fsans μ) a‖) := by
    apply (div_le_iff₀ hden).mp
    simpa only [mul_div_assoc, he] using hg
  have hfac : 1 - ‖a‖^2 ≤ 2 * (1 - ‖a‖) := by
    nlinarith [sq_nonneg (1 - ‖a‖)]
  have hlarge : D * ((1 - ‖a‖^2) * ‖deriv (fsans μ) a‖) ≤
      D * (2 * (1 - ‖a‖) * ‖deriv (fsans μ) a‖) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hfac hder.le) hD.le
  have hraw : ‖u - h u‖ ≤ 2 * D * ((1 - ‖a‖)/2 * ‖deriv (fsans μ) a‖) := by
    nlinarith [hnum.trans hlarge]
  rw [norm_div, norm_div, norm_mul, cbl_scale_norm ha0 ha1]
  calc ‖u - h u‖ / ‖b‖ ≤ (2 * D * ((1 - ‖a‖)/2 * ‖deriv (fsans μ) a‖)) / ‖b‖ :=
      div_le_div_of_nonneg_right hraw (norm_nonneg b)
    _ = _ := by ring

end TakhtajanTeo
