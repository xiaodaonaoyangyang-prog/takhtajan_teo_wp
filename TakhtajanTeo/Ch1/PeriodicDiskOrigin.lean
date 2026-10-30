import TakhtajanTeo.Ch1.PeriodicDiskDescent

/-! Quantitative control at the missing point of exponential descent. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem real_lift_linear_bounds {u : ℝ → ℝ} (hm : Monotone u)
    (hp : ∀ x, u (x + 1) = u x + 1) (x : ℝ) :
    u 0 + x - 1 ≤ u x ∧ u x ≤ u 0 + x + 1 := by
  have hh := GardinerLakic2000.gl16_lift_incr_floor hm hp 0 x
  simp only [zero_add] at hh
  have h₁ := Int.floor_le x
  have h₂ := Int.lt_floor_add_one x
  constructor <;> linarith

theorem beurlingAhlfors_im_linear_lower {u : ℝ → ℝ} (hc : Continuous u)
    (hm : Monotone u) (hp : ∀ x, u (x + 1) = u x + 1) (z : ℂ) :
    z.im / 2 - 1 ≤ (beurlingAhlfors u 1 z).im := by
  have hlow : ∀ t : ℝ, 2 * t * z.im - 2 ≤ u (z.re + t * z.im) - u (z.re - t * z.im) := by
    intro t
    have h₁ := (real_lift_linear_bounds hm hp (z.re + t * z.im)).1
    have h₂ := (real_lift_linear_bounds hm hp (z.re - t * z.im)).2
    linarith
  have hlin : Continuous (fun t : ℝ => 2 * t * z.im - 2) := by fun_prop
  have hfun : Continuous (fun t : ℝ => u (z.re + t * z.im) - u (z.re - t * z.im)) :=
    (hc.comp (by fun_prop)).sub (hc.comp (by fun_prop))
  have hI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hlin.intervalIntegrable 0 1) (hfun.intervalIntegrable 0 1) (fun t _ => hlow t)
  have hcalc : (∫ t in (0 : ℝ)..1, 2 * t * z.im - 2) = z.im - 2 := by
    have he : (fun t : ℝ => 2 * t * z.im - 2) = (fun t => (2 * z.im) * t - 2) := by
      funext t
      ring
    rw [he, intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ => (2 * z.im) * t)).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_const_mul]
    norm_num
    ring
  rw [hcalc] at hI
  have him : (beurlingAhlfors u 1 z).im =
      1 / 2 * ∫ t in (0 : ℝ)..1, u (z.re + t * z.im) - u (z.re - t * z.im) := by
    simp [beurlingAhlfors]
  rw [him]
  linarith

theorem beurlingAhlfors_disk_norm_sq {u : ℝ → ℝ} (hc : Continuous u)
    (hm : Monotone u) (hp : ∀ x, u (x + 1) = u x + 1) (z : ℂ) :
    ‖diskCover (beurlingAhlfors u 1 z)‖ ^ 2 ≤ Real.exp (4 * π) * ‖diskCover z‖ := by
  have hh := beurlingAhlfors_im_linear_lower hc hm hp z
  rw [diskCover_norm, diskCover_norm, pow_two, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hπ := Real.pi_pos
  nlinarith

theorem periodicDiskMap_zero (f : ℂ → ℂ) : periodicDiskMap f 0 = 0 := by
  simp [periodicDiskMap]

theorem periodicDiskMap_ne_zero {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) : periodicDiskMap f z ≠ 0 := by
  rw [periodicDiskMap, if_neg hz]
  exact diskCover_ne_zero _

theorem beurlingAhlfors_disk_continuousAt_zero {u : ℝ → ℝ} (hc : Continuous u)
    (hm : Monotone u) (hp : ∀ x, u (x + 1) = u x + 1) :
    ContinuousAt (periodicDiskMap (beurlingAhlfors u 1)) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hC : 0 < Real.exp (4 * π) := Real.exp_pos _
  refine ⟨ε ^ 2 / Real.exp (4 * π), div_pos (sq_pos_of_pos hε) hC, ?_⟩
  intro z hz
  rw [periodicDiskMap_zero, dist_zero_right]
  by_cases hz0 : z = 0
  · simpa [hz0, periodicDiskMap_zero] using hε
  · have hnorm := beurlingAhlfors_disk_norm_sq hc hm hp (diskCoverLog z)
    rw [← periodicDiskMap_cover (beurlingAhlfors_add_int hc hp 1), diskCover_log hz0] at hnorm
    rw [dist_zero_right] at hz
    have hbound := (lt_div_iff₀ hC).mp hz
    nlinarith [norm_nonneg (periodicDiskMap (beurlingAhlfors u 1) z)]

theorem beurlingAhlfors_disk_continuous {u : ℝ → ℝ} (hc : Continuous u)
    (hm : StrictMono u) (hp : ∀ x, u (x + 1) = u x + 1) :
    Continuous (periodicDiskMap (beurlingAhlfors u 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    exact beurlingAhlfors_disk_continuousAt_zero hc hm.monotone hp
  · exact periodicDiskMap_continuousAt_ne_zero (ba_f1_basic hm hc).1
      (beurlingAhlfors_add_int hc hp 1) hz

end TakhtajanTeo

#print axioms TakhtajanTeo.beurlingAhlfors_disk_norm_sq
#print axioms TakhtajanTeo.beurlingAhlfors_disk_continuous
