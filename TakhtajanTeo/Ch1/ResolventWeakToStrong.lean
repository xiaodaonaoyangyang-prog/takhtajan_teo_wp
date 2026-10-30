import TakhtajanTeo.Ch1.ResolventIntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! From the justified weak equation to the pointwise disk resolvent equation. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem resolvent_mixed_continuousOn {u : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u unitDisc) :
    ContinuousOn (dz (dzbar u)) unitDisc := by
  have hb := (resolvent_contDiffOn_wirtinger isOpen_ball hu).2
  have hd : ContDiffOn ℝ 0 (fderiv ℝ (dzbar u)) unitDisc :=
    hb.fderiv_of_isOpen isOpen_ball (by norm_num)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  exact ((h1.sub (contDiffOn_const.mul hI)).div_const 2).continuousOn

theorem resolvent_rho_continuousOn : ContinuousOn (fun z : ℂ => (rho z : ℂ)) unitDisc := by
  intro z hz
  exact (Complex.continuous_ofReal.continuousAt.comp
    (rho_contDiffAt (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)).continuousAt).continuousWithinAt

/-- Integration by parts turns one weak test equation into vanishing of the
ordinary continuous residual against that test. -/
theorem resolvent_weak_residual_test {u f φ : ℂ → ℂ}
    (hu : ContDiffOn ℝ 2 u unitDisc) (hf : ContinuousOn f unitDisc)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc)
    (hw : (∫ z in unitDisc, u z * (2 * laplace0 φ z + φ z) * rho z) =
      ∫ z in unitDisc, f z * φ z * rho z) :
    (∫ z in unitDisc, ((rho z : ℂ) * (u z - f z) - 2 * dz (dzbar u) z) * φ z) = 0 := by
  have hMc : Continuous (dz (dzbar φ)) := continuous_dz (resolvent_contDiff_wirtinger hφ).2
  have hMC : HasCompactSupport (dz (dzbar φ)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) resolvent_mixed_tsupport
  have hMs : tsupport (dz (dzbar φ)) ⊆ unitDisc := resolvent_mixed_tsupport.trans hs
  have hA := resolvent_mul_test_integrable (resolvent_rho_continuousOn.mul hu.continuousOn)
    hφ.continuous hc hs
  have hB := resolvent_mul_test_integrable hu.continuousOn hMc hMC hMs
  have hC := resolvent_mul_test_integrable (resolvent_rho_continuousOn.mul hf)
    hφ.continuous hc hs
  have hD := resolvent_mul_test_integrable (resolvent_mixed_continuousOn hu) hφ.continuous hc hs
  simp only [Pi.mul_apply] at hA hC
  have hAC : IntegrableOn (fun z => ((rho z : ℂ) * u z) * φ z - ((rho z : ℂ) * f z) * φ z)
      unitDisc := hA.sub hC
  have hpair : (∫ z in unitDisc, u z * dz (dzbar φ) z) =
      ∫ z in unitDisc, dz (dzbar u) z * φ z := by
    rw [resolvent_mixed_pairing_disc hu hφ hc hs]
    simp only [mul_comm]
  have hWL : (∫ z in unitDisc, u z * (2 * laplace0 φ z + φ z) * rho z) =
      (∫ z in unitDisc, ((rho z : ℂ) * u z) * φ z) -
        2 * ∫ z in unitDisc, u z * dz (dzbar φ) z := by
    rw [← integral_const_mul, ← integral_sub hA (hB.const_mul 2)]
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro z hz
    dsimp only
    have hρ : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)))
    unfold laplace0
    field_simp
    <;> ring
  have hWR : (∫ z in unitDisc, f z * φ z * rho z) =
      ∫ z in unitDisc, ((rho z : ℂ) * f z) * φ z := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [hWL, hWR, hpair] at hw
  have he : (fun z => ((rho z : ℂ) * (u z - f z) - 2 * dz (dzbar u) z) * φ z) =
      (fun z => (((rho z : ℂ) * u z) * φ z - ((rho z : ℂ) * f z) * φ z) -
        2 * (dz (dzbar u) z * φ z)) := by funext z; ring
  rw [he, integral_sub hAC (hD.const_mul 2), integral_sub hA hC, integral_const_mul]
  linear_combination hw

/-- The full inhomogeneous equation on the disk for the original resolvent
operator and every bounded smooth input. -/
theorem RK3_output_equation_disc {f : ℂ → ℂ} (hf : f ∈ BCinf unitDisc) :
    ∀ z ∈ unitDisc, 2 * (laplace0 (resolventOp unitDisc f) z +
      (1 / 2) * resolventOp unitDisc f z) = f z := by
  let u := resolventOp unitDisc f
  have hu : ContDiffOn ℝ 2 u unitDisc := (RK3_output_smooth_disc hf).of_le (by norm_num)
  let E : ℂ → ℂ := fun z => (rho z : ℂ) * (u z - f z) - 2 * dz (dzbar u) z
  have hEc : ContinuousOn E unitDisc :=
    (resolvent_rho_continuousOn.mul (hu.continuousOn.sub hf.1.continuousOn)).sub
      (continuousOn_const.mul (resolvent_mixed_continuousOn hu))
  have hEl : LocallyIntegrableOn E unitDisc volume := hEc.locallyIntegrableOn measurableSet_ball
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∈ unitDisc → E z = 0 := by
    apply (show IsOpen unitDisc from isOpen_ball).ae_eq_zero_of_integral_contDiff_smul_eq_zero hEl
    intro ψ hψ hc hs
    let φ : ℂ → ℂ := fun z => (ψ z : ℂ)
    have hφ : ContDiff ℝ 2 φ :=
      (Complex.ofRealCLM.contDiff.comp hψ).of_le (by norm_num)
    have hφs : tsupport φ ⊆ tsupport ψ := tsupport_comp_subset (g := Complex.ofReal) (by simp) ψ
    have hφC : HasCompactSupport φ := hc.of_isClosed_subset (isClosed_tsupport _) hφs
    obtain ⟨C, hb⟩ := hf.2
    have hw := resolvent_disc_weak_equation
      (hf.1.continuousOn.aestronglyMeasurable measurableSet_ball) hb hφ hφC (hφs.trans hs)
    have hr := resolvent_weak_residual_test hu hf.1.continuousOn hφ hφC (hφs.trans hs) hw
    have he : (∫ z : ℂ, ψ z • E z) = ∫ z in unitDisc, E z * φ z := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := unitDisc)
        (fun z hz => by
          have hzS : z ∉ tsupport ψ := fun h => hz (hs h)
          rw [image_eq_zero_of_notMem_tsupport hzS, zero_smul])]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [φ, Complex.real_smul]
      ring
    rw [he]
    exact hr
  have hAE : E =ᵐ[volume.restrict unitDisc] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)]
      with z hz hzD
    exact hz hzD
  have hEq := Measure.eqOn_open_of_ae_eq (μ := volume) hAE
    (show IsOpen unitDisc from isOpen_ball) hEc continuousOn_const
  intro z hz
  have he := hEq hz
  change (rho z : ℂ) * (u z - f z) - 2 * dz (dzbar u) z = 0 at he
  have hρ : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)))
  change 2 * (laplace0 u z + (1 / 2) * u z) = f z
  unfold laplace0
  field_simp
  linear_combination he

/-- The reverse inverse identity on bounded smooth disk functions follows from
the pointwise equation and the independently proved bounded uniqueness theorem. -/
theorem RK3_inverse_disc {f : ℂ → ℂ} (hf : f ∈ BCinf unitDisc)
    (hg : (fun z => 2 * (laplace0 f z + (1 / 2) * f z)) ∈ BCinf unitDisc) :
    ∀ z ∈ unitDisc, f z = resolventOp unitDisc (fun w => 2 * (laplace0 f w + (1 / 2) * f w)) z := by
  let g : ℂ → ℂ := fun z => 2 * (laplace0 f z + (1 / 2) * f z)
  have hu := RK3_output_BCinf_disc hg
  have hf2 : ContDiffOn ℝ 2 f unitDisc := hf.1.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (resolventOp unitDisc g) unitDisc := hu.1.of_le (by norm_num)
  have hb : ∃ C : ℝ, ∀ z ∈ unitDisc, ‖f z - resolventOp unitDisc g z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hf.2
    obtain ⟨B, hB⟩ := hu.2
    exact ⟨C + B, fun z hz => (norm_sub_le _ _).trans (add_le_add (hC z hz) (hB z hz))⟩
  have he : ∀ z ∈ unitDisc, laplace0 (fun w => f w - resolventOp unitDisc g w) z +
      (f z - resolventOp unitDisc g z) / 2 = 0 := by
    intro z hz
    rw [resolvent_laplace_sub isOpen_ball hf2 hu2 hz]
    have hp := RK3_output_equation_disc hg z hz
    change 2 * (laplace0 (resolventOp unitDisc g) z + (1 / 2) * resolventOp unitDisc g z) =
      2 * (laplace0 f z + (1 / 2) * f z) at hp
    linear_combination -hp / 2
  have hzero := resolvent_homogeneous_unique_disc_C2 (hf2.sub hu2) hb he
  intro z hz
  exact sub_eq_zero.mp (hzero hz)

/-- All clauses of RK3 in the disk model, with the original input space and normalization. -/
theorem RK3_disc :
    (∀ g ∈ BCinf unitDisc,
      (∀ z ∈ unitDisc, Integrable (fun w => (resolventKernel z w : ℂ) * g w * rho w)
        (volume.restrict unitDisc)) ∧ resolventOp unitDisc g ∈ BCinf unitDisc ∧
      ∀ z ∈ unitDisc, 2 * (laplace0 (resolventOp unitDisc g) z + (1 / 2) * resolventOp unitDisc g z) = g z) ∧
      ∀ f ∈ BCinf unitDisc, (fun z => 2 * (laplace0 f z + (1 / 2) * f z)) ∈ BCinf unitDisc →
        ∀ z ∈ unitDisc, f z = resolventOp unitDisc (fun w => 2 * (laplace0 f w + (1 / 2) * f w)) z := by
  exact ⟨fun g hg => ⟨fun z hz => RK3_absolute_convergence (Or.inl rfl) hg hz,
    RK3_output_BCinf_disc hg, RK3_output_equation_disc hg⟩,
    fun f hf hg => RK3_inverse_disc hf hg⟩

end TakhtajanTeo
