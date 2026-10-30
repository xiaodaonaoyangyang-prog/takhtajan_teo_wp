import TakhtajanTeo.Ch1.ResolventLogPotential

/-! Regularity of the full resolvent kernel integral for compact sources in the disk. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped BigOperators

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

set_option autoImplicit false

private def sourceWeight (i : Fin 5) (w : ℂ) : ℝ :=
  ![1, 1 / (1 - ‖w‖ ^ 2), ‖w‖ ^ 2 / (1 - ‖w‖ ^ 2),
    w.re / (1 - ‖w‖ ^ 2), w.im / (1 - ‖w‖ ^ 2)] i

private def targetWeight (i : Fin 5) (z : ℂ) : ℝ :=
  ![1 / π, 2 * ‖z‖ ^ 2 / (π * (1 - ‖z‖ ^ 2)), 2 / (π * (1 - ‖z‖ ^ 2)),
    -(4 * z.re) / (π * (1 - ‖z‖ ^ 2)), -(4 * z.im) / (π * (1 - ‖z‖ ^ 2))] i

private theorem sourceWeight_contDiffAt (i : Fin 5) {w : ℂ} (hw : w ∈ unitDisc) :
    ContDiffAt ℝ ⊤ (sourceWeight i) w := by
  have hD := resolvent_domain_denominator_ne_zero (Or.inl rfl) hw
  have hn : ContDiffAt ℝ ⊤ (fun v : ℂ => ‖v‖ ^ 2) w :=
    (contDiff_id.norm_sq ℂ).contDiffAt
  have hd : ContDiffAt ℝ ⊤ (fun v : ℂ => 1 - ‖v‖ ^ 2) w := contDiffAt_const.sub hn
  fin_cases i <;> dsimp [sourceWeight]
  · exact contDiffAt_const
  · exact contDiffAt_const.div hd hD
  · exact hn.div hd hD
  · exact Complex.reCLM.contDiff.contDiffAt.div hd hD
  · exact Complex.imCLM.contDiff.contDiffAt.div hd hD

private theorem targetWeight_contDiffAt (i : Fin 5) {z : ℂ} (hz : z ∈ unitDisc) :
    ContDiffAt ℝ ⊤ (targetWeight i) z := by
  have hD := mul_ne_zero Real.pi_ne_zero (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)
  have hn : ContDiffAt ℝ ⊤ (fun v : ℂ => ‖v‖ ^ 2) z :=
    (contDiff_id.norm_sq ℂ).contDiffAt
  have hd : ContDiffAt ℝ ⊤ (fun v : ℂ => π * (1 - ‖v‖ ^ 2)) z :=
    contDiffAt_const.mul (contDiffAt_const.sub hn)
  fin_cases i <;> dsimp [targetWeight]
  · exact contDiffAt_const
  · exact (contDiffAt_const.mul hn).div hd hD
  · exact contDiffAt_const.div hd hD
  · exact (contDiffAt_const.mul Complex.reCLM.contDiff.contDiffAt).neg.div hd hD
  · exact (contDiffAt_const.mul Complex.imCLM.contDiff.contDiffAt).neg.div hd hD

private theorem sourceWeight_complex_contDiffOn (n : ℕ∞) (i : Fin 5) :
    ContDiffOn ℝ n (fun w => (sourceWeight i w : ℂ)) unitDisc := by
  intro w hw
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w
    (sourceWeight_contDiffAt i hw)).of_le le_top).contDiffWithinAt

private theorem targetWeight_complex_contDiffOn (n : ℕ∞) (i : Fin 5) :
    ContDiffOn ℝ n (fun z => (targetWeight i z : ℂ)) unitDisc := by
  intro z hz
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
    (targetWeight_contDiffAt i hz)).of_le le_top).contDiffWithinAt

private theorem coefficient_eq_sum {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    (resolventLogCoefficient z w : ℂ) =
      ∑ i : Fin 5, (targetWeight i z : ℂ) * (sourceWeight i w : ℂ) := by
  rw [resolventLogCoefficient_separated hz hw]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sourceWeight, targetWeight,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  push_cast
  ring

private theorem weightedSource_contDiff {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hs : tsupport h ⊆ unitDisc) (i : Fin 5) :
    ContDiff ℝ n (fun w => (sourceWeight i w : ℂ) * h w) :=
  resolvent_source_mul_contDiff (show IsOpen unitDisc from isOpen_ball)
    hh (sourceWeight_complex_contDiffOn n i) hs

private theorem singular_eq_sum {h : ℂ → ℂ} (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) (w : ℂ) :
    (resolventLogCoefficient z w : ℂ) * (Real.log ‖z - w‖ : ℂ) * h w =
      ∑ i : Fin 5, (targetWeight i z : ℂ) *
        ((Real.log ‖z - w‖ : ℂ) * ((sourceWeight i w : ℂ) * h w)) := by
  by_cases hw : w ∈ unitDisc
  · rw [coefficient_eq_sum hz hw, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · have he : h w = 0 := image_eq_zero_of_notMem_tsupport (fun hw' => hw (hs hw'))
    simp only [he, mul_zero, Finset.sum_const_zero]

/-- The logarithmic portion of the full kernel is absolutely integrable against a
compact smooth source supported in the disk. -/
theorem resolvent_singular_integrable_compact {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Integrable (fun w => (resolventLogCoefficient z w : ℂ) *
      (Real.log ‖z - w‖ : ℂ) * h w) volume := by
  have hi : ∀ i : Fin 5, Integrable (fun w => (targetWeight i z : ℂ) *
      ((Real.log ‖z - w‖ : ℂ) * ((sourceWeight i w : ℂ) * h w))) volume := by
    intro i
    exact (resolventLogPotential_integrable (weightedSource_contDiff hh hs i).continuous
      (hc.mul_left (f := fun w => (sourceWeight i w : ℂ))) z).const_mul _
  have hsum := integrable_finset_sum Finset.univ (fun i _ => hi i)
  exact hsum.congr (Filter.Eventually.of_forall fun w => (singular_eq_sum hs hz w).symm)

private theorem singular_integral_eq_sum {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w : ℂ, (resolventLogCoefficient z w : ℂ) * (Real.log ‖z - w‖ : ℂ) * h w) =
      ∑ i : Fin 5, (targetWeight i z : ℂ) *
        resolventLogPotential (fun w => (sourceWeight i w : ℂ) * h w) z := by
  have hi : ∀ i : Fin 5, Integrable (fun w => (targetWeight i z : ℂ) *
      ((Real.log ‖z - w‖ : ℂ) * ((sourceWeight i w : ℂ) * h w))) volume := by
    intro i
    exact (resolventLogPotential_integrable (weightedSource_contDiff hh hs i).continuous
      (hc.mul_left (f := fun w => (sourceWeight i w : ℂ))) z).const_mul _
  calc
    _ = ∫ w : ℂ, ∑ i : Fin 5, (targetWeight i z : ℂ) *
        ((Real.log ‖z - w‖ : ℂ) * ((sourceWeight i w : ℂ) * h w)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (singular_eq_sum hs hz)
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hi i)]
      simp only [integral_const_mul, resolventLogPotential]

/-- Smoothness of the logarithmic portion after finite separation of its coefficient. -/
theorem resolvent_singular_contDiffOn_compact {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc) :
    ContDiffOn ℝ n (fun z => ∫ w : ℂ,
      (resolventLogCoefficient z w : ℂ) * (Real.log ‖z - w‖ : ℂ) * h w) unitDisc := by
  have hp : ContDiffOn ℝ n (fun z => ∑ i : Fin 5, (targetWeight i z : ℂ) *
      resolventLogPotential (fun w => (sourceWeight i w : ℂ) * h w) z) unitDisc := by
    apply ContDiffOn.sum
    intro i hi
    exact (targetWeight_complex_contDiffOn n i).mul
      (resolventLogPotential_contDiff (weightedSource_contDiff hh hs i)
        (hc.mul_left (f := fun w => (sourceWeight i w : ℂ)))).contDiffOn
  exact hp.congr (fun z hz => singular_integral_eq_sum hh hc hs hz)

/-- Absolute integrability of the regular part against a compact smooth source. -/
theorem resolvent_regular_integrable_compact {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Integrable (fun w => (resolventRegularPart z w : ℂ) * h w) volume := by
  have hβ : ContDiffOn ℝ n (fun w => (resolventRegularPart z w : ℂ)) unitDisc := by
    intro w hw
    have hr : ContDiffAt ℝ ⊤ (fun v : ℂ => resolventRegularPart z v) w :=
      (resolventRegularPart_contDiffAt hz hw).comp w (contDiffAt_const.prodMk contDiffAt_id)
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w hr).of_le le_top).contDiffWithinAt
  exact (resolvent_source_mul_contDiff (show IsOpen unitDisc from isOpen_ball) hh hβ hs).continuous
    |>.integrable_of_hasCompactSupport (hc.mul_left (f := fun w => (resolventRegularPart z w : ℂ)))

private theorem kernel_source_decomposition_ae {h : ℂ → ℂ} (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (fun w => (resolventKernel z w : ℂ) * h w) =ᵐ[volume]
      (fun w => (resolventRegularPart z w : ℂ) * h w -
        (resolventLogCoefficient z w : ℂ) * (Real.log ‖z - w‖ : ℂ) * h w) := by
  have hne : ∀ᵐ w : ℂ ∂volume, w ≠ z := by rw [ae_iff]; simp
  filter_upwards [hne] with w hwz
  by_cases hw : w ∈ unitDisc
  · rw [resolventKernel_log_decomposition hz hw hwz.symm]
    push_cast
    ring
  · have he : h w = 0 := image_eq_zero_of_notMem_tsupport (fun hw' => hw (hs hw'))
    simp only [he, mul_zero, sub_zero]

/-- Absolute convergence for the full kernel with compact smooth source. -/
theorem resolvent_kernel_integrable_compact {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    Integrable (fun w => (resolventKernel z w : ℂ) * h w) volume := by
  exact ((resolvent_regular_integrable_compact hh hc hs hz).sub
    (resolvent_singular_integrable_compact hh hc hs hz)).congr
      (kernel_source_decomposition_ae hs hz).symm

private theorem kernel_integral_decomposition {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ w : ℂ, (resolventKernel z w : ℂ) * h w) =
      (∫ w : ℂ, (resolventRegularPart z w : ℂ) * h w) -
        ∫ w : ℂ, (resolventLogCoefficient z w : ℂ) * (Real.log ‖z - w‖ : ℂ) * h w := by
  rw [integral_congr_ae (kernel_source_decomposition_ae hs hz)]
  exact integral_sub (resolvent_regular_integrable_compact hh hc hs hz)
    (resolvent_singular_integrable_compact hh hc hs hz)

/-- Smoothness of the full kernel integral for a compact source supported in the disk.
The diagonal is excluded only as a null singleton in the integral decomposition. -/
theorem resolvent_kernel_contDiffOn_compact {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc) :
    ContDiffOn ℝ n (fun z => ∫ w : ℂ, (resolventKernel z w : ℂ) * h w) unitDisc := by
  have hp := (resolventRegularPart_integral_contDiffOn hh hc hs).sub
    (resolvent_singular_contDiffOn_compact hh hc hs)
  exact hp.congr (fun z hz => kernel_integral_decomposition hh hc hs hz)

/-- Genuine C^n regularity of the original hyperbolic resolvent operator for a
global C^n input with compact support strictly inside the disk. -/
theorem resolventOp_contDiffOn_compact {n : ℕ∞} {g : ℂ → ℂ}
    (hg : ContDiff ℝ n g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ unitDisc) :
    ContDiffOn ℝ n (resolventOp unitDisc g) unitDisc := by
  let h : ℂ → ℂ := fun w => (rho w : ℂ) * g w
  have hρ : ContDiffOn ℝ n (fun w => (rho w : ℂ)) unitDisc := by
    intro w hw
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp w
      (rho_contDiffAt (resolvent_domain_denominator_ne_zero (Or.inl rfl) hw))).of_le
        le_top).contDiffWithinAt
  have hh : ContDiff ℝ n h :=
    resolvent_source_mul_contDiff (show IsOpen unitDisc from isOpen_ball) hg hρ hs
  have hhc : HasCompactSupport h := hc.mul_left (f := fun w => (rho w : ℂ))
  have hhs : tsupport h ⊆ unitDisc := by
    intro w hw
    exact hs (tsupport_mul_subset_right (f := fun w => (rho w : ℂ)) (g := g) hw)
  have hp := resolvent_kernel_contDiffOn_compact hh hhc hhs
  apply hp.congr
  intro z hz
  unfold resolventOp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)]
  · apply integral_congr_ae
    filter_upwards [] with w
    dsimp [h]
    ring
  · rw [image_eq_zero_of_notMem_tsupport (fun hw' => hw (hs hw'))]
    simp

end TakhtajanTeo
