import TakhtajanTeo.Ch1.S7_Curvature

/-!
# Weighted moments of the resolvent kernel against holomorphic functions (TT:3466–3472)

For `φ` holomorphic on `𝔻` with `(1 - |w|²)² φ` bounded,
`∬_𝔻 G(a, w)(1 - |w|²)² φ(w)/(1 - a w̄)⁴ d²w = φ(a)/9`:
the centered case by polar integration and the mean value property
(`wpb_center_moment`), the general case by a Blaschke change of variables (`wpb_point_moment`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The centered resolvent kernel is integrable on the disk. -/
theorem wpb_gint : IntegrableOn (fun w : ℂ => resolventKernel 0 w) unitDisc := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  refine (resolvent_mass_integrable (Or.inl rfl) h0).mono' ?_ ?_
  · exact (measurable_resolventKernel.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball, resolvent_mass_nonneg_ae (Or.inl rfl) h0]
      with w hw hnn
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hq0 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hq1 : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
    have hρ : 1 ≤ rho w := by
      unfold rho
      rw [le_div_iff₀ (pow_pos hq0 2)]
      nlinarith [pow_le_one₀ hq0.le hq1 (n := 2)]
    have hρ0 : 0 < rho w := by linarith
    have hG : 0 ≤ resolventKernel 0 w := nonneg_of_mul_nonneg_left hnn hρ0
    rw [Real.norm_eq_abs, abs_of_nonneg hG]
    nlinarith

theorem wpb_radius_integrable :
    IntegrableOn (fun r : ℝ => r * resolventKernel 0 (r : ℂ)) (Ioo 0 1) := by
  have hi : IntegrableOn (fun w : ℂ => resolventKernel 0 (‖w‖ : ℂ)) unitDisc := by
    simpa [resolventKernel, pointPair, Complex.norm_real] using wpb_gint
  have h := (integrableOn_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => resolventKernel 0 (r : ℂ))).mp hi
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul] using h

theorem wpb_center_polar_integrable {Φ : ℂ → ℂ} (hΦ : ContinuousOn Φ unitDisc) {C : ℝ}
    (hC : ∀ w ∈ unitDisc, ‖((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w‖ ≤ C) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 •
      ((resolventKernel 0 (Complex.polarCoord.symm p) : ℂ) *
        ((1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ 2 : ℝ) * Φ (Complex.polarCoord.symm p)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  let ψ : ℝ × ℝ → ℂ := fun p => ((1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ 2 : ℝ) *
    Φ (Complex.polarCoord.symm p)
  have hpc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap : MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p) S unitDisc := by
    intro p hps
    apply mem_ball_zero_iff.mpr
    rw [norm_polarCoord_symm, abs_of_pos hps.1.1]
    exact hps.1.2
  have hc : ContinuousOn ψ S := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((1 - ‖Complex.polarCoord.symm p‖ ^ 2) ^ 2 : ℝ)) S := by
      apply Continuous.continuousOn
      fun_prop
    exact (Complex.continuous_ofReal.comp_continuousOn h1).mul (hΦ.comp hpc.continuousOn hmap)
  have hb : ∀ᵐ p ∂(volume.restrict S), ‖ψ p‖ ≤ C := by
    filter_upwards [ae_restrict_mem hSm] with p hps
    exact hC _ (hmap hps)
  have hi : IntegrableOn (fun p : ℝ × ℝ => ((p.1 * resolventKernel 0 (p.1 : ℂ) : ℝ) : ℂ)) S := by
    have h := (wpb_radius_integrable.ofReal (𝕜 := ℂ)).comp_fst (volume.restrict (Ioo (-π) π))
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  apply (hi.mul_bdd (hc.aestronglyMeasurable hSm) hb).congr
  filter_upwards [ae_restrict_mem hSm] with p hps
  have hG : resolventKernel 0 (Complex.polarCoord.symm p) = resolventKernel 0 (p.1 : ℂ) := by
    simp [resolventKernel, pointPair, norm_polarCoord_symm, Complex.norm_real]
  simp only [ψ, hG, Complex.ofReal_mul, Complex.real_smul]
  ring

theorem wpb_center_circle_average {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ unitDisc) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    Real.circleAverage (fun w : ℂ => (resolventKernel 0 w : ℂ) *
      ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w) 0 r =
      ((resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * Φ 0 := by
  have hsub : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro w hw
    apply mem_ball_zero_iff.mpr
    have := mem_closedBall_zero_iff.mp hw
    rw [abs_of_pos hr.1] at this
    exact lt_of_le_of_lt this hr.2
  have hc : ContinuousOn Φ (closedBall (0 : ℂ) |r|) := hΦ.continuousOn.mono hsub
  have hd : ∀ w ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ), DifferentiableAt ℂ Φ w := by
    intro w hw
    exact hΦ.differentiableAt (isOpen_ball.mem_nhds (hsub (ball_subset_closedBall hw.1)))
  have hmv : Real.circleAverage Φ 0 r = Φ 0 := by
    simpa using circleAverage_of_differentiable_on_off_countable countable_empty hc hd
  have h1 : Real.circleAverage (fun w : ℂ => (resolventKernel 0 w : ℂ) *
      ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w) 0 r = Real.circleAverage (fun w : ℂ =>
        (((resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2 : ℝ) : ℂ) • Φ w)) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro w hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right, abs_of_pos hr.1] using hw
    have hG : resolventKernel 0 w = resolventKernel 0 (r : ℂ) := by
      simp [resolventKernel, pointPair, hn, Complex.norm_real, abs_of_pos hr.1]
    simp only [hG, hn, smul_eq_mul, Complex.ofReal_mul]
  rw [h1, Real.circleAverage_fun_smul, hmv, smul_eq_mul]

set_option maxHeartbeats 800000 in
/-- The centered moment of a weighted-bounded holomorphic function against `G(0,·)(1 - |w|²)²`. -/
theorem wpb_center_moment {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ unitDisc) {C : ℝ}
    (hC : ∀ w ∈ unitDisc, ‖((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w‖ ≤ C) :
    (∫ w in unitDisc, (resolventKernel 0 w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w) = Φ 0 / 9 := by
  have hi := wpb_center_polar_integrable hΦ.continuousOn hC
  have key := bKernel_polar_integral (fun w : ℂ => (resolventKernel 0 w : ℂ) *
    ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w) hi
  rw [key]
  have h1 : (∫ r in Ioo (0 : ℝ) 1, r • ((2 * π) • Real.circleAverage (fun w : ℂ =>
      (resolventKernel 0 w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * Φ w) 0 r)) =
      ∫ r in Ioo (0 : ℝ) 1,
        ((2 * π * r * (resolventKernel 0 (r : ℂ) * (1 - r ^ 2) ^ 2) : ℝ) : ℂ) * Φ 0 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [wpb_center_circle_average hΦ hr]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [h1, integral_mul_const, integral_complex_ofReal, bKernel_center_radius_integral]
  push_cast
  ring


theorem wpb_one_add {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 + conj a * blaschke a w = (1 - a * conj a) / (1 - conj a * w) := by
  have hd := blaschke_den_ne_zero ha hw
  unfold blaschke
  field_simp
  ring

theorem wpb_Phi_at {φ : ℂ → ℂ} {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    φ (blaschke (-a) (blaschke a w)) / (1 + conj a * blaschke a w) ^ 4 =
      φ w * (1 - conj a * w) ^ 4 / (1 - a * conj a) ^ 4 := by
  rw [blaschke_neg_blaschke ha hw, wpb_one_add ha hw]
  have hd := blaschke_den_ne_zero ha hw
  have hn := one_sub_mul_conj_ne_zero ha
  field_simp

set_option maxHeartbeats 800000 in
theorem wpb_blaschke_integrand {φ : ℂ → ℂ} {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    (‖deriv (blaschke a) w‖ ^ 2 : ℝ) •
      ((resolventKernel 0 (blaschke a w) : ℂ) * ((1 - ‖blaschke a w‖ ^ 2) ^ 2 : ℝ) *
        (φ (blaschke (-a) (blaschke a w)) / (1 + conj a * blaschke a w) ^ 4)) =
      (resolventKernel a w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * φ w / (1 - a * conj w) ^ 4 := by
  have hwd := blaschke_den_ne_zero ha hw
  have hwdc : 1 - a * conj w ≠ 0 := by
    intro h
    apply hwd
    simpa using congrArg (starRingEnd ℂ) h
  have ha0 := one_sub_mul_conj_ne_zero ha
  have hA : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 1 - a * conj a := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hD : ((‖1 - conj a * w‖ ^ 2 : ℝ) : ℂ) = (1 - conj a * w) * (1 - a * conj w) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_sub, map_one, map_mul, conj_conj]
  have hB := one_sub_normSq_blaschke ha hw
  simp only [Complex.normSq_eq_norm_sq] at hB
  rw [wpb_Phi_at ha hw, bKernel_blaschke_jacobian ha hw, resolventKernel_blaschke_center ha hw, hB]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_mul]
  have hnorm : (‖1 - conj a * w‖ : ℂ) ^ 2 = (1 - conj a * w) * (1 - a * conj w) := by
    exact_mod_cast hD
  rw [hA, hnorm]
  field_simp [ha0, hwd, hwdc]
  <;> ring


theorem wpb_Phi_bound {φ : ℂ → ℂ} {C : ℝ}
    (hC : ∀ w ∈ unitDisc, ‖((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * φ w‖ ≤ C) {a : ℂ} (ha1 : ‖a‖ < 1)
    {u : ℂ} (hu : u ∈ unitDisc) :
    ‖((1 - ‖u‖ ^ 2) ^ 2 : ℝ) * (φ (blaschke (-a) u) / (1 + conj a * u) ^ 4)‖ ≤ C / (1 - ‖a‖ ^ 2) ^ 2 := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hna : ‖-a‖ < 1 := by simpa using ha1
  have hw1 : ‖blaschke (-a) u‖ < 1 := blaschke_mem_unitDisc hna hu1
  set w : ℂ := blaschke (-a) u with hwdef
  have huw : u = blaschke a w := (blaschke_blaschke_neg ha1 hu1).symm
  have hK : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hd := blaschke_den_ne_zero ha1 hw1
  have hN : 0 < ‖1 - conj a * w‖ := norm_pos_iff.mpr hd
  have hB := one_sub_normSq_blaschke ha1 hw1
  simp only [Complex.normSq_eq_norm_sq] at hB
  have e1 : 1 - ‖u‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖a‖ ^ 2) / ‖1 - conj a * w‖ ^ 2 := by
    rw [huw]; exact hB
  have e2 : ‖1 + conj a * u‖ = (1 - ‖a‖ ^ 2) / ‖1 - conj a * w‖ := by
    rw [huw, wpb_one_add ha1 hw1, norm_div]
    congr 1
    have h2 : (1 : ℂ) - a * conj a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
  have hCw := hC w (mem_ball_zero_iff.mpr hw1)
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), e1, e2]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hCw
  have hφ : (1 - ‖w‖ ^ 2) ^ 2 * ‖φ w‖ ≤ C := hCw
  have key : ((1 - ‖w‖ ^ 2) * (1 - ‖a‖ ^ 2) / ‖1 - conj a * w‖ ^ 2) ^ 2 *
      (‖φ w‖ / ((1 - ‖a‖ ^ 2) / ‖1 - conj a * w‖) ^ 4) =
      (1 - ‖w‖ ^ 2) ^ 2 * ‖φ w‖ / (1 - ‖a‖ ^ 2) ^ 2 := by
    field_simp
  rw [key]
  exact div_le_div_of_nonneg_right hφ (sq_nonneg _)

set_option maxHeartbeats 1600000 in
/-- **The point moment**: `∬ G(a,w)(1 - |w|²)² φ(w)/(1 - a w̄)⁴ = φ(a)/9`. -/
theorem wpb_point_moment {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {C : ℝ}
    (hC : ∀ w ∈ unitDisc, ‖((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * φ w‖ ≤ C) {a : ℂ} (ha : a ∈ unitDisc) :
    (∫ w in unitDisc, (resolventKernel a w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * φ w /
      (1 - a * conj w) ^ 4) = φ a / 9 := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hna : ‖-a‖ < 1 := by simpa using ha1
  have hden : ∀ u ∈ unitDisc, 1 + conj a * u ≠ 0 := by
    intro u hu h0
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have h1 : conj a * u = -1 := by linear_combination h0
    have h2 : ‖conj a * u‖ < 1 := by
      rw [norm_mul, norm_conj]; nlinarith [norm_nonneg a, norm_nonneg u]
    rw [h1] at h2
    simp at h2
  have hΦd : DifferentiableOn ℂ (fun u => φ (blaschke (-a) u) / (1 + conj a * u) ^ 4) unitDisc := by
    intro u hu
    have h1 : DifferentiableAt ℂ φ (blaschke (-a) u) :=
      hφ.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
        (blaschke_mem_unitDisc hna (mem_ball_zero_iff.mp hu))))
    have h2 : DifferentiableAt ℂ (blaschke (-a)) u :=
      (differentiableOn_blaschke hna).differentiableAt (isOpen_ball.mem_nhds hu)
    have h3 : DifferentiableAt ℂ (fun u : ℂ => (1 + conj a * u) ^ 4) u := by fun_prop
    exact ((h1.comp u h2).div h3 (pow_ne_zero 4 (hden u hu))).differentiableWithinAt
  have hΦb : ∀ u ∈ unitDisc, ‖((1 - ‖u‖ ^ 2) ^ 2 : ℝ) *
      (φ (blaschke (-a) u) / (1 + conj a * u) ^ 4)‖ ≤ C / (1 - ‖a‖ ^ 2) ^ 2 :=
    fun u hu => wpb_Phi_bound hC ha1 hu
  have hcenter := wpb_center_moment hΦd hΦb
  have hΦ0 : φ (blaschke (-a) 0) / (1 + conj a * 0) ^ 4 = φ a := by simp
  rw [hΦ0] at hcenter
  have hf := isConformalOnto_blaschke ha1
  have hi := ahP_integral_image (U := unitDisc) (show IsOpen unitDisc from isOpen_ball)
    hf.1 hf.2.1 (fun u : ℂ => (resolventKernel 0 u : ℂ) * ((1 - ‖u‖ ^ 2) ^ 2 : ℝ) *
      (φ (blaschke (-a) u) / (1 + conj a * u) ^ 4))
  rw [hf.2.2] at hi
  rw [← hcenter, hi]
  apply setIntegral_congr_fun measurableSet_ball
  intro w hw
  exact (wpb_blaschke_integrand ha1 (mem_ball_zero_iff.mp hw)).symm

end TakhtajanTeo
