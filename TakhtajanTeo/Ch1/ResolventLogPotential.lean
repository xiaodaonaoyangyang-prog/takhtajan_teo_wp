import TakhtajanTeo.Ch1.S1_4_ResolventCore
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Logarithmic singularities and compact-source smoothing for the resolvent. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate Convolution

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The planar logarithmic kernel is locally integrable, including at zero. -/
theorem resolvent_log_norm_locallyIntegrable :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume := by
  have hi : LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by norm_num)
      (by norm_num)
    · filter_upwards [] with z
      simp [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    · exact measurable_norm.inv.aestronglyMeasurable
  have hn : LocallyIntegrable (fun z : ℂ => ‖z‖) volume := continuous_norm.locallyIntegrable
  apply (hn.add hi).mono (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  filter_upwards [] with z
  have hnp := norm_nonneg z
  have hip := inv_nonneg.mpr hnp
  change |Real.log ‖z‖| ≤ |‖z‖ + ‖z‖⁻¹|
  rw [abs_of_nonneg (add_nonneg hnp hip)]
  exact abs_le.mpr ⟨by linarith [Real.neg_inv_le_log hnp], by linarith [Real.log_le_self hnp]⟩

/-- Logarithmic potential of a complex-valued source. -/
def resolventLogPotential (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w : ℂ, (Real.log ‖z - w‖ : ℂ) * h w

/-- Absolute convergence of a logarithmic potential with continuous compact source. -/
theorem resolventLogPotential_integrable {h : ℂ → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h) (z : ℂ) :
    Integrable (fun w : ℂ => (Real.log ‖z - w‖ : ℂ) * h w) volume := by
  have hi := (hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip hh
    resolvent_log_norm_locallyIntegrable z).integrable
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul] using hi

/-- Compact smooth sources produce smooth logarithmic potentials. This moves derivatives
onto the source through convolution; it does not differentiate the singular kernel. -/
theorem resolventLogPotential_contDiff {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) :
    ContDiff ℝ n (resolventLogPotential h) := by
  have hp := hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip hh
    resolvent_log_norm_locallyIntegrable
  convert hp using 1
  funext z
  simp only [MeasureTheory.convolution_def, resolventLogPotential,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

/-- Smooth coefficient of the diagonal logarithmic singularity. -/
def resolventLogCoefficient (z w : ℂ) : ℝ := (2 * pointPair z w + 1) / π

/-- The nonsingular part of the kernel on the product of two disks. -/
def resolventRegularPart (z w : ℂ) : ℝ :=
  resolventLogCoefficient z w * Real.log ‖1 - conj z * w‖ - 1 / π

/-- Exact separation of the kernel's diagonal logarithm on the disk. -/
theorem resolventKernel_log_decomposition {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    resolventKernel z w = resolventRegularPart z w -
      resolventLogCoefficient z w * Real.log ‖z - w‖ := by
  have hzD := resolvent_domain_denominator_ne_zero (Or.inl rfl) hz
  have hwD := resolvent_domain_denominator_ne_zero (Or.inl rfl) hw
  have hN := blaschke_den_ne_zero (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
  have hB := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw)
  have hk := normSq_blaschke_key z w
  simp only [Complex.normSq_eq_norm_sq, norm_sub_rev w z] at hk
  have hA : ‖1 - conj z * w‖ ^ 2 = ‖z - w‖ ^ 2 +
      (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by nlinarith [hk]
  have hratio : (pointPair z w + 1) / pointPair z w =
      ‖1 - conj z * w‖ ^ 2 / ‖z - w‖ ^ 2 := by
    unfold pointPair
    rw [hA]
    field_simp [hzD, hwD, hB]
    <;> ring
  rw [resolventKernel, hratio,
    Real.log_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hN)) (pow_ne_zero 2 hB),
    Real.log_pow, Real.log_pow]
  unfold resolventRegularPart resolventLogCoefficient
  field_simp
  <;> ring

/-- The coefficient is real analytic even on the diagonal. -/
theorem resolventLogCoefficient_contDiffAt {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => resolventLogCoefficient p.1 p.2) (z, w) := by
  unfold resolventLogCoefficient
  have hp := pointPair_contDiffAt z w
    (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)
    (resolvent_domain_denominator_ne_zero (Or.inl rfl) hw)
  exact ((contDiffAt_const.mul hp).add contDiffAt_const).div contDiffAt_const Real.pi_ne_zero

/-- The remaining kernel part is real analytic on the whole product disk. -/
theorem resolventRegularPart_contDiffAt {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ContDiffAt ℝ ⊤ (fun p : ℂ × ℂ => resolventRegularPart p.1 p.2) (z, w) := by
  have hN := blaschke_den_ne_zero (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
  have hcj : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have hn : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => 1 - conj p.1 * p.2) :=
    contDiff_const.sub (hcj.mul contDiff_snd)
  unfold resolventRegularPart
  exact ((resolventLogCoefficient_contDiffAt hz hw).mul
    ((hn.contDiffAt.norm ℂ hN).log (norm_ne_zero_iff.mpr hN))).sub contDiffAt_const

/-- A compactly supported source may be multiplied by a coefficient smooth only
on an open neighborhood of its support. -/
theorem resolvent_source_mul_contDiff {n : ℕ∞} {D : Set ℂ} (hD : IsOpen D)
    {h β : ℂ → ℂ} (hh : ContDiff ℝ n h) (hβ : ContDiffOn ℝ n β D)
    (hs : tsupport h ⊆ D) : ContDiff ℝ n (fun w => β w * h w) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ D
  · exact (hβ.contDiffAt (hD.mem_nhds hz)).mul hh.contDiffAt
  · have hzS : z ∉ tsupport h := fun hz' => hz (hs hz')
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hzS] with w hw
    simp only [image_eq_zero_of_notMem_tsupport hw, mul_zero]

/-- Smoothness of the logarithmic potentials with weighted compact sources used
in the finite separation of the resolvent's singular coefficient. -/
theorem resolventLogPotential_weighted_contDiff {n : ℕ∞} {D : Set ℂ} (hD : IsOpen D)
    {h β : ℂ → ℂ} (hh : ContDiff ℝ n h) (hc : HasCompactSupport h)
    (hβ : ContDiffOn ℝ n β D) (hs : tsupport h ⊆ D) :
    ContDiff ℝ n (resolventLogPotential (fun w => β w * h w)) := by
  exact resolventLogPotential_contDiff (resolvent_source_mul_contDiff hD hh hβ hs)
    (hc.mul_left (f := β))

/-- Finite separation of the logarithmic coefficient into functions of each variable.
This reduces its compact-source integral to ordinary logarithmic potentials. -/
theorem resolventLogCoefficient_separated {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    resolventLogCoefficient z w = 1 / π +
      (2 * ‖z‖ ^ 2 / (π * (1 - ‖z‖ ^ 2))) * (1 / (1 - ‖w‖ ^ 2)) +
      (2 / (π * (1 - ‖z‖ ^ 2))) * (‖w‖ ^ 2 / (1 - ‖w‖ ^ 2)) -
      (4 * z.re / (π * (1 - ‖z‖ ^ 2))) * (w.re / (1 - ‖w‖ ^ 2)) -
      (4 * z.im / (π * (1 - ‖z‖ ^ 2))) * (w.im / (1 - ‖w‖ ^ 2)) := by
  have hzD := resolvent_domain_denominator_ne_zero (Or.inl rfl) hz
  have hwD := resolvent_domain_denominator_ne_zero (Or.inl rfl) hw
  have hn : ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * z.re * w.re - 2 * z.im * w.im := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  unfold resolventLogCoefficient pointPair
  rw [hn]
  field_simp [hzD, hwD]
  <;> ring

/-- A parameterized smooth integral with support in a fixed compact set. This is
the constant-factor case of Mathlib's parameterized convolution theorem. -/
theorem resolvent_contDiffOn_integral_compact {n : ℕ∞} {D k : Set ℂ}
    (hD : IsOpen D) (hk : IsCompact k) {g : ℂ → ℂ → ℂ}
    (hs : ∀ z w, z ∈ D → w ∉ k → g z w = 0)
    (hg : ContDiffOn ℝ n (fun p : ℂ × ℂ => g p.1 p.2) (D ×ˢ univ)) :
    ContDiffOn ℝ n (fun z => ∫ w : ℂ, g z w) D := by
  have hf : LocallyIntegrable (fun _ : ℂ => (1 : ℝ)) volume :=
    continuous_const.locallyIntegrable
  have hp := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip (v := fun _ : ℂ => (0 : ℂ))
    (g := g) contDiffOn_const hD hk hs hf hg
  convert hp using 1
  funext z
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, one_smul]

/-- The nonsingular part of the resolvent integral is smooth for a compact smooth
source supported strictly inside the disk. -/
theorem resolventRegularPart_integral_contDiffOn {n : ℕ∞} {h : ℂ → ℂ}
    (hh : ContDiff ℝ n h) (hc : HasCompactSupport h) (hs : tsupport h ⊆ unitDisc) :
    ContDiffOn ℝ n (fun z => ∫ w : ℂ, (resolventRegularPart z w : ℂ) * h w) unitDisc := by
  apply resolvent_contDiffOn_integral_compact (show IsOpen unitDisc from isOpen_ball) hc
  · intro z w hz hw
    simp only [image_eq_zero_of_notMem_tsupport hw, mul_zero]
  · intro p hp
    by_cases hw : p.2 ∈ unitDisc
    · have hr := resolventRegularPart_contDiffAt hp.1 hw
      have hrc : ContDiffAt ℝ n (fun q : ℂ × ℂ => (resolventRegularPart q.1 q.2 : ℂ)) p :=
        (Complex.ofRealCLM.contDiff.contDiffAt.comp p hr).of_le le_top
      exact (hrc.mul (hh.contDiffAt.comp p contDiffAt_snd)).contDiffWithinAt
    · have hwS : p.2 ∉ tsupport h := fun hw' => hw (hs hw')
      have hv : ∀ᶠ w in 𝓝 p.2, h w = 0 := by
        filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hwS] with w hw'
        exact image_eq_zero_of_notMem_tsupport hw'
      have heq : (fun q : ℂ × ℂ => (resolventRegularPart q.1 q.2 : ℂ) * h q.2) =ᶠ[𝓝 p]
          (fun _ => (0 : ℂ)) := by
        filter_upwards [continuousAt_snd.tendsto.eventually hv] with q hq
        simp only [hq, mul_zero]
      exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq heq).contDiffWithinAt

end TakhtajanTeo
