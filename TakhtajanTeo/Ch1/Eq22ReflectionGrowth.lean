import TakhtajanTeo.Ch1.Eq22ReflectionSphere
import TakhtajanTeo.Ch1.Eq22ReflectionTransport
import TakhtajanTeo.Ch1.Eq22ReflectionGeometry

open Complex Set Metric Filter Topology
namespace TakhtajanTeo
open LiZhongQC

theorem eq22_reflection_growth {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ gsans μ '' unitDiscExterior,
      ‖u-h u‖^2 * LiZhongQC.poincareDensity (fsans μ '' unitDisc) (h u) ≤
        C*(1+‖u‖^2) := by
  obtain ⟨a,ha,F,hFc,hFs,hFa,hagree⟩ := eq22_reflection_sphere hμ hh
  obtain ⟨e,hΩimg,hEimg⟩ := eq22_welding_common_chart hμ
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hφ := (S2C.s2c_conf_f hμ).symm isOpen_ball
  have hp : e 1 ∈ frontier (fsans μ '' unitDisc) := by
    rw [hΩimg, ← e.image_frontier]
    apply mem_image_of_mem
    simp [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hq : e (-1) ∈ frontier (fsans μ '' unitDisc) := by
    rw [hΩimg, ← e.image_frontier]
    apply mem_image_of_mem
    simp [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hpq : e 1 ≠ e (-1) := fun he => (by norm_num : (1 : ℂ) ≠ -1) (e.injective he)
  obtain ⟨M1,hM1,hb1⟩ := eq22_chart_gap_bound hΩ hφ (eq22_welding_components hμ) hFs hagree hp
  obtain ⟨M2,hM2,hb2⟩ := eq22_chart_gap_bound hΩ hφ (eq22_welding_components hμ) hFs hagree hq
  have hbounded : Bornology.IsBounded (fsans μ '' unitDisc) := by
    rw [hΩimg]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  obtain ⟨B,hB⟩ := hbounded.exists_norm_le
  apply eq22_growth_of_two_chart_bounds (a := e 1) (b := e (-1))
    (B := max B 0) (M := max M1 M2) hpq (le_max_right _ _)
    (hM1.trans_le (le_max_left _ _))
  · intro u hu
    exact (s20l_a2_density_pos hΩ hφ (hh.2.1 hu)).le
  · intro u hu
    exact (hB _ (hh.2.1 hu)).trans (le_max_left _ _)
  · intro u hu
    exact (hb1 u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro u hu
    exact (hb2 u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end TakhtajanTeo
