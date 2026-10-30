import TakhtajanTeo.Ch1.ResolventSourceTransport

/-! Absolutely convergent resolvent duality and the weak inhomogeneous equation. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

/-- The integral of the absolute kernel-input integrand obeys the same bound as
the output. Positivity is used only almost everywhere, excluding the diagonal. -/
theorem resolvent_integral_norm_le {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖f w‖ ≤ C) {z : ℂ} (hz : z ∈ D) :
    (∫ w in D, ‖(resolventKernel z w : ℂ) * f w * rho w‖) ≤ C := by
  have hi := resolvent_integrand_integrable_of_bounded hD hf hb hz
  have hm := (resolvent_mass_integrable hD hz).const_mul C
  have hbound : ∀ᵐ w ∂(volume.restrict D),
      ‖(resolventKernel z w : ℂ) * f w * rho w‖ ≤ C * (resolventKernel z w * rho w) := by
    filter_upwards [resolvent_mass_nonneg_ae hD hz,
      ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hwpos hw
    have he : (resolventKernel z w : ℂ) * f w * rho w =
        ((resolventKernel z w * rho w : ℝ) : ℂ) * f w := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwpos]
    exact (mul_le_mul_of_nonneg_left (hb w hw) hwpos).trans_eq (mul_comm _ _)
  have h := integral_mono_ae hi.norm hm hbound
  simpa only [integral_const_mul, RK4 hD hz, mul_one] using h

/-- Actual product integrability underlying the resolvent's bilinear symmetry:
one input is bounded measurable and the other has integrable hyperbolic weight. -/
theorem resolvent_bilinear_integrable {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f ψ : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D))
    (hψ : AEStronglyMeasurable ψ (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖f w‖ ≤ C)
    (hψi : IntegrableOn (fun z => ψ z * (rho z : ℂ)) D) :
    Integrable (fun p : ℂ × ℂ =>
      ((resolventKernel p.1 p.2 : ℂ) * f p.2 * rho p.2) * (ψ p.1 * (rho p.1 : ℂ)))
      ((volume.restrict D).prod (volume.restrict D)) := by
  have hρ : Measurable (fun z : ℂ => (rho z : ℂ)) := by unfold rho; fun_prop
  have hK : Measurable (fun p : ℂ × ℂ => (resolventKernel p.1 p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_resolventKernel
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ =>
      ((resolventKernel p.1 p.2 : ℂ) * f p.2 * rho p.2) * (ψ p.1 * (rho p.1 : ℂ)))
      ((volume.restrict D).prod (volume.restrict D)) :=
    ((hK.aestronglyMeasurable.mul hf.comp_snd).mul hρ.aestronglyMeasurable.comp_snd).mul
      (hψ.comp_fst.mul hρ.aestronglyMeasurable.comp_fst)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with z hz
    exact (resolvent_integrand_integrable_of_bounded hD hf hb hz).mul_const _
  · apply (hψi.norm.const_mul C).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [norm_mul]
    rw [integral_mul_const]
    simpa only [norm_mul] using
      mul_le_mul_of_nonneg_right (resolvent_integral_norm_le hD hf hb hz)
        (norm_nonneg (ψ z * (rho z : ℂ)))

/-- Bilinear symmetry, justified by product integrability rather than a formal
exchange of two potentially divergent integrals. -/
theorem resolvent_bilinear_swap {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f ψ : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D))
    (hψ : AEStronglyMeasurable ψ (volume.restrict D)) {C : ℝ}
    (hb : ∀ w ∈ D, ‖f w‖ ≤ C)
    (hψi : IntegrableOn (fun z => ψ z * (rho z : ℂ)) D) :
    (∫ z in D, resolventOp D f z * ψ z * rho z) =
      ∫ w in D, f w * resolventOp D ψ w * rho w := by
  have hi := resolvent_bilinear_integrable hD hf hψ hb hψi
  calc
    _ = ∫ z in D, ∫ w in D,
        ((resolventKernel z w : ℂ) * f w * rho w) * (ψ z * (rho z : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [integral_mul_const]
      unfold resolventOp
      ring
    _ = ∫ w in D, ∫ z in D,
        ((resolventKernel z w : ℂ) * f w * rho w) * (ψ z * (rho z : ℂ)) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with w
      have he : (fun z => ((resolventKernel z w : ℂ) * f w * rho w) * (ψ z * (rho z : ℂ))) =
          (fun z => (f w * (rho w : ℂ)) * ((resolventKernel w z : ℂ) * ψ z * rho z)) := by
        funext z
        rw [resolventKernel_symm z w]
        ring
      rw [he, integral_const_mul]
      unfold resolventOp
      ring

/-- A continuous compact test supported inside the disk has integrable
hyperbolic weight; the density's boundary singularity lies outside its support. -/
theorem resolvent_test_weight_integrable {ψ : ℂ → ℂ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ unitDisc) :
    IntegrableOn (fun z => ψ z * (rho z : ℂ)) unitDisc := by
  have ht : Continuous (fun z => ψ z * (rho z : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z ∈ unitDisc
    · exact hψ.continuousAt.mul (Complex.continuous_ofReal.continuousAt.comp
        (rho_contDiffAt (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz)).continuousAt)
    · have hzS : z ∉ tsupport ψ := fun h => hz (hs h)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzS] with w hw
      simpa only [hw, Pi.zero_apply, zero_mul]
  have htc : HasCompactSupport (fun z => ψ z * (rho z : ℂ)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
  exact (ht.integrable_of_hasCompactSupport htc).integrableOn

/-- The disk resolvent satisfies the inhomogeneous equation weakly for every
bounded measurable input, tested against arbitrary compact C2 functions. -/
theorem resolvent_disc_weak_equation {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict unitDisc)) {C : ℝ}
    (hb : ∀ w ∈ unitDisc, ‖f w‖ ≤ C) {φ : ℂ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc) :
    (∫ z in unitDisc, resolventOp unitDisc f z * (2 * laplace0 φ z + φ z) * rho z) =
      ∫ z in unitDisc, f z * φ z * rho z := by
  have ht := resolvent_test_operator_continuous hφ
  have htc : HasCompactSupport (fun z => 2 * laplace0 φ z + φ z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) resolvent_test_operator_tsupport
  have hts : tsupport (fun z => 2 * laplace0 φ z + φ z) ⊆ unitDisc :=
    resolvent_test_operator_tsupport.trans hs
  rw [resolvent_bilinear_swap (Or.inl rfl) hf ht.aestronglyMeasurable hb
    (resolvent_test_weight_integrable ht htc hts)]
  apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
  intro z hz
  dsimp only
  rw [show resolventOp unitDisc (fun w => 2 * laplace0 φ w + φ w) z = φ z from
    resolvent_disc_test_inverse hφ hc hs hz]

end TakhtajanTeo
