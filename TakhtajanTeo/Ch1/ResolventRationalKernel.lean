import TakhtajanTeo.Ch1.ResolventCompactSource

/-! A rational integral representation of the weighted resolvent kernel.
This form removes apparent boundary singularities from its logarithmic formula. -/

open Real Complex Filter Set Topology MeasureTheory Metric

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

set_option autoImplicit false

private theorem rational_profile_primitive {u t : ℝ} (hut : u + t ≠ 0) :
    HasDerivAt (fun s : ℝ => (2 * u + 1) * Real.log (u + s) - s +
      u * (u + 1) / (u + s)) (t * (1 - t) / (u + t) ^ 2) t := by
  have hl := (((hasDerivAt_id t).const_add u).log hut).const_mul (2 * u + 1)
  have hq := (hasDerivAt_const t (u * (u + 1))).div
    ((hasDerivAt_id t).const_add u) hut
  convert (hl.sub (hasDerivAt_id t)).add hq using 1
  · rfl
  · simp only [id_eq]
    field_simp [hut]
    <;> ring

/-- The scalar logarithmic kernel is an integral of rational nonnegative terms. -/
theorem resolvent_scalar_rational_integral {u : ℝ} (hu : 0 < u) :
    (2 * u + 1) / (2 * π) * Real.log ((u + 1) / u) - 1 / π =
      (1 / (2 * π)) * ∫ t in (0 : ℝ)..1, t * (1 - t) / (u + t) ^ 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => t * (1 - t) / (u + t) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
      ((continuousAt_const.add continuousAt_id).pow 2)
        (pow_ne_zero 2 (by linarith : u + t ≠ 0))).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t ∈ uIcc (0 : ℝ) 1) => rational_profile_primitive
      (by
        have ht0 : 0 ≤ t := by simpa using ht.1
        linarith : u + t ≠ 0)) hi
  rw [hFTC, Real.log_div (by positivity : u + 1 ≠ 0) hu.ne']
  simp only [add_zero, sub_zero]
  field_simp [hu.ne', show u + 1 ≠ 0 by positivity]
  <;> ring

/-- Rational representation of the kernel in either disk model, off the diagonal. -/
theorem resolventKernel_rational_integral {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) (hzw : z ≠ w) :
    resolventKernel z w = (1 / (2 * π)) *
      ∫ t in (0 : ℝ)..1, t * (1 - t) / (pointPair z w + t) ^ 2 := by
  have hu : 0 < pointPair z w := by
    apply pointPair_pos hzw
    rcases hD with rfl | rfl
    · exact Or.inl ⟨hz, hw⟩
    · exact Or.inr ⟨hz, hw⟩
  exact resolvent_scalar_rational_integral hu

/-- The weighted kernel has a representation with no denominator involving the
integration variable's distance from the unit circle. -/
theorem resolvent_weighted_rational_integral {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) (hzw : z ≠ w) :
    resolventKernel z w * rho w = (2 / π) * (1 - ‖z‖ ^ 2) ^ 2 *
      ∫ t in (0 : ℝ)..1, t * (1 - t) /
        (‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) ^ 2 := by
  have hzD := resolvent_domain_denominator_ne_zero hD hz
  have hwD := resolvent_domain_denominator_ne_zero hD hw
  have he (t : ℝ) : t * (1 - t) / (pointPair z w + t) ^ 2 =
      ((1 - ‖z‖ ^ 2) ^ 2 * (1 - ‖w‖ ^ 2) ^ 2) *
        (t * (1 - t) / (‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) ^ 2) := by
    unfold pointPair
    have hsum : ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) + t =
        (‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) /
          ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by field_simp [hzD, hwD] <;> ring
    rw [hsum, div_pow, div_div_eq_mul_div, mul_pow]
    ring
  rw [resolventKernel_rational_integral hD hz hw hzw]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  unfold rho
  field_simp [hwD]
  <;> ring

/-- Rational integrand extending the weighted kernel to the boundary away from the diagonal. -/
def resolventBoundaryIntegrand (z w : ℂ) (t : ℝ) : ℝ :=
  (2 / π) * (1 - ‖z‖ ^ 2) ^ 2 * (t * (1 - t) /
    (‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) ^ 2)

/-- The rational denominator stays positive on the closed disk for separated points. -/
theorem resolvent_boundary_denominator_pos {z w : ℂ} {t : ℝ}
    (hz : z ∈ unitDisc) (hw : w ∈ closedBall (0 : ℂ) 1) (hzw : z ≠ w) (ht : 0 ≤ t) :
    0 < ‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hwn : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have hDz : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hDw : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw)))
    (mul_nonneg (mul_nonneg ht hDz) hDw)

/-- The extended integrand is jointly real analytic, including at the boundary in w. -/
theorem resolventBoundaryIntegrand_contDiffAt {z w : ℂ} {t : ℝ}
    (hz : z ∈ unitDisc) (hw : w ∈ closedBall (0 : ℂ) 1) (hzw : z ≠ w) (ht : 0 ≤ t) :
    ContDiffAt ℝ ⊤ (fun p : (ℂ × ℂ) × ℝ => resolventBoundaryIntegrand p.1.1 p.1.2 p.2)
      ((z, w), t) := by
  have hZ : ContDiff ℝ ⊤ (fun p : (ℂ × ℂ) × ℝ => p.1.1) := contDiff_fst.fst
  have hW : ContDiff ℝ ⊤ (fun p : (ℂ × ℂ) × ℝ => p.1.2) := contDiff_fst.snd
  have hT : ContDiff ℝ ⊤ (fun p : (ℂ × ℂ) × ℝ => p.2) := contDiff_snd
  have hDz := (contDiff_const (c := (1 : ℝ))).sub (hZ.norm_sq ℂ)
  have hDw := (contDiff_const (c := (1 : ℝ))).sub (hW.norm_sq ℂ)
  have hden := ((hZ.sub hW).norm_sq ℂ).add ((hT.mul hDz).mul hDw)
  unfold resolventBoundaryIntegrand
  exact (contDiff_const.mul (hDz.pow 2)).contDiffAt.mul
    ((hT.mul (contDiff_const.sub hT)).contDiffAt.div (hden.pow 2).contDiffAt
      (pow_ne_zero 2 (resolvent_boundary_denominator_pos hz hw hzw ht).ne'))

/-- Integral extension of the weighted kernel, defined also on the unit circle. -/
def resolventBoundaryKernel (z w : ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, resolventBoundaryIntegrand z w t

theorem resolventBoundaryKernel_eq_weighted {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    resolventBoundaryKernel z w = resolventKernel z w * rho w := by
  rw [resolvent_weighted_rational_integral (Or.inl rfl) hz hw hzw]
  unfold resolventBoundaryKernel resolventBoundaryIntegrand
  rw [intervalIntegral.integral_const_mul]

/-- Absolute integrability of the extended rational profile, even for a boundary point w. -/
theorem resolventBoundaryIntegrand_intervalIntegrable {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ closedBall (0 : ℂ) 1) (hzw : z ≠ w) :
    IntervalIntegrable (resolventBoundaryIntegrand z w) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht0 : 0 ≤ t := by simpa using ht.1
  have hc := (resolventBoundaryIntegrand_contDiffAt hz hw hzw ht0).continuousAt
  exact (hc.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

/-- A single positive denominator bound works for all integration parameters near
each separated pair, including pairs with the second point on the unit circle. -/
theorem resolvent_boundary_denominator_uniform {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ closedBall (0 : ℂ) 1) (hzw : z ≠ w) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p : ℂ × ℂ in 𝓝 (z, w), ∀ t ∈ Icc (0 : ℝ) 1,
      c ≤ ‖p.1 - p.2‖ ^ 2 + t * (1 - ‖p.1‖ ^ 2) * (1 - ‖p.2‖ ^ 2) := by
  have hsep : 0 < ‖z - w‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))
  refine ⟨‖z - w‖ ^ 2 / 2, by positivity, ?_⟩
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hwn : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
  have hnonneg : 0 ≤ t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
    mul_nonneg (mul_nonneg ht.1 (by nlinarith [norm_nonneg z]))
      (by nlinarith [norm_nonneg w])
  have hb : ‖z - w‖ ^ 2 / 2 <
      ‖z - w‖ ^ 2 + t * (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by linarith
  have hcont : Continuous (fun p : (ℂ × ℂ) × ℝ =>
      ‖p.1.1 - p.1.2‖ ^ 2 + p.2 * (1 - ‖p.1.1‖ ^ 2) * (1 - ‖p.1.2‖ ^ 2)) := by fun_prop
  have he : ∀ᶠ p : (ℂ × ℂ) × ℝ in 𝓝 ((z, w), t), ‖z - w‖ ^ 2 / 2 <
      ‖p.1.1 - p.1.2‖ ^ 2 + p.2 * (1 - ‖p.1.1‖ ^ 2) * (1 - ‖p.1.2‖ ^ 2) :=
    (isOpen_lt continuous_const hcont).mem_nhds hb
  filter_upwards [he] with p hp
  exact hp.le

/-- Exact value of the extended weighted kernel at a boundary point. -/
theorem resolventBoundaryKernel_on_circle {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : ‖w‖ = 1) :
    resolventBoundaryKernel z w = (1 - ‖z‖ ^ 2) ^ 2 / (3 * π * ‖z - w‖ ^ 4) := by
  have hzw : z ≠ w := by
    intro h
    have hz' := mem_ball_zero_iff.mp hz
    rw [h, hw] at hz'
    linarith
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw)
  have hpoly : (∫ t in (0 : ℝ)..1, t * (1 - t)) = 1 / 6 := by
    have he : (fun t : ℝ => t * (1 - t)) = (fun t : ℝ => t - t ^ 2) := by funext t; ring
    rw [he, intervalIntegral.integral_sub (μ := volume)
      (f := fun t : ℝ => t) (g := fun t : ℝ => t ^ 2)
      (continuous_id.intervalIntegrable 0 1) (intervalIntegral.intervalIntegrable_pow 2)]
    norm_num [integral_id, integral_pow]
  unfold resolventBoundaryKernel resolventBoundaryIntegrand
  simp only [hw, one_pow, sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, hpoly]
  field_simp [hn]
  <;> ring

end TakhtajanTeo
