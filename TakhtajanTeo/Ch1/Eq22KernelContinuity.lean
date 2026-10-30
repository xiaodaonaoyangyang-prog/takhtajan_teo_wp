import Mathlib

open Complex Set MeasureTheory Filter Topology Metric
namespace TakhtajanTeo

theorem eq22_kernel_local_bound {u z z0 F : ℂ} {r : ℝ}
    (hr : 0 < r) (hu : r ≤ ‖u-z0‖) (hz : ‖z-z0‖ < r/2) :
    ‖F/(u-z)^4‖ ≤ 16*‖F/(u-z0)^4‖ := by
  have hd := norm_sub_le_norm_sub_add_norm_sub u z z0
  have hp0 : 0 < ‖u-z0‖ := hr.trans_le hu
  have hp : 0 < ‖u-z‖ := by linarith
  have hb : ‖u-z0‖ ≤ 2*‖u-z‖ := by linarith
  have h0 := norm_pos_iff.mp hp0
  have hn := norm_pos_iff.mp hp
  have hratio : ‖(u-z0)/(u-z)‖ ≤ 2 := by
    rw [norm_div]
    exact (div_le_iff₀ hp).mpr hb
  have he : F/(u-z)^4 = F/(u-z0)^4*((u-z0)/(u-z))^4 := by
    field_simp
  rw [he, norm_mul, norm_pow]
  calc
    _ ≤ ‖F/(u-z0)^4‖*2^4 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hratio 4) (norm_nonneg _)
    _ = _ := by ring

theorem eq22_kernel_integral_continuousAt {E : Set ℂ} {F : ℂ → ℂ}
    {z0 : ℂ} {r : ℝ} (hE : MeasurableSet E) (hr : 0 < r)
    (hsep : ∀ u ∈ E, r ≤ ‖u-z0‖)
    (hF : IntegrableOn (fun u => F u/(u-z0)^4) E) :
    ContinuousAt (fun z => ∫ u in E, F u/(u-z)^4) z0 := by
  have hn : ∀ u ∈ E, u-z0 ≠ 0 := fun u hu => norm_pos_iff.mp (hr.trans_le (hsep u hu))
  have hm : AEStronglyMeasurable F (volume.restrict E) := by
    apply (hF.aestronglyMeasurable.mul
      (((continuous_id.sub continuous_const).pow 4).aestronglyMeasurable)).congr
    filter_upwards [ae_restrict_mem hE] with u hu
    dsimp
    field_simp [hn u hu]
  apply continuousAt_of_dominated (bound := fun u => 16*‖F u/(u-z0)^4‖)
  · exact Eventually.of_forall fun z => hm.div₀
      ((measurable_id.sub_const z).pow_const 4).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z0 (half_pos hr)] with z hz
    filter_upwards [ae_restrict_mem hE] with u hu
    apply eq22_kernel_local_bound hr (hsep u hu)
    simpa only [mem_ball, dist_eq_norm] using hz
  · exact hF.norm.const_mul 16
  · filter_upwards [ae_restrict_mem hE] with u hu
    exact continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 4)
      (pow_ne_zero 4 (hn u hu))

end TakhtajanTeo
