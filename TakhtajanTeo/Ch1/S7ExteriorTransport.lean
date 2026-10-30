import TakhtajanTeo.Ch1.S7EnergyRegularity
import TakhtajanTeo.Ch1.S7ResolventL2
import TakhtajanTeo.Ch1.FundDomainReflect
import TakhtajanTeo.Ch1.ResolventExteriorSmoothness

/-!
# Exterior forcing transported through infinity

The actual Lambda correspondence supplies smooth disk representatives.
The two Beltrami phases cancel in the forcing product. Hyperbolic area
invariance and the established resolvent inversion then transport the
forcing and its potential without assuming removability for arbitrary
bounded smooth exterior functions.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The smooth disk contraction underlying the actual Lambda formula. -/
def s7et_diskRep (φ : AInf unitDisc) (z : ℂ) : ℂ :=
  -2 * (rho z : ℂ)⁻¹ * AInf.toFun φ (conj z)

theorem s7et_diskRep_smooth (φ : AInf unitDisc) :
    ContDiffOn ℝ (⊤ : ℕ∞) (s7et_diskRep φ) unitDisc := by
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (AInf.toFun φ) unitDisc :=
    (φ.2.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hc : MapsTo (conj : ℂ → ℂ) unitDisc unitDisc := by
    intro z hz
    simpa only [unitDisc, mem_ball_zero_iff, norm_conj] using hz
  exact (contDiffOn_const.mul (wp_rho_inv_contDiff.of_le le_top).contDiffOn).mul
    (hφ.comp Complex.conjCLE.contDiff.contDiffOn hc)

theorem s7et_diskRep_bound (φ : AInf unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖s7et_diskRep φ z‖ ≤ ‖φ‖ / 2 := by
  have hcz : conj z ∈ unitDisc := by
    simpa only [unitDisc, mem_ball_zero_iff, norm_conj] using hz
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hd : (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by
    have hdR : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
    exact_mod_cast hdR
  have he : s7et_diskRep φ z = -(1 / 2 : ℂ) * φ.1 ⟨conj z, hcz⟩ := by
    simp only [s7et_diskRep, rho, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one, inv_div,
      AInf.toFun, unweight, dite_eq_left hcz, norm_conj]
    field_simp
    <;> ring
  rw [he, norm_mul]
  norm_num only [norm_neg, norm_div, norm_one, norm_ofNat]
  have hb := BoundedContinuousFunction.norm_coe_le_norm φ.1 ⟨conj z, hcz⟩
  change ‖φ.1 ⟨conj z, hcz⟩‖ ≤ ‖φ‖ at hb
  linarith

/-- The actual exterior representative carries only a unit-modulus phase. -/
theorem s7et_lambda_phase (φ : AInf unitDisc) :
    (Lambda φ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      (fun w => s7et_diskRep φ w⁻¹ * (w ^ 2 / conj w ^ 2)) := by
  filter_upwards [wp_Lambda_harmonicDisk_ae φ,
    ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w hw hwE
  rw [hw]
  have hw0 := resolvent_exterior_ne_zero hwE
  have hc0 : conj w ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hw0
  simp only [wp_harmonicOfDisk, s7et_diskRep, map_div₀, map_pow,
    conj_conj, wp_rho_inv_complex, map_inv₀]
  field_simp
  <;> ring

/-- The inversion phases cancel in a coefficient times a conjugate coefficient. -/
theorem s7et_phase_cancel (a b w : ℂ) (hw : w ≠ 0) :
    (a * (w ^ 2 / conj w ^ 2)) * conj (b * (w ^ 2 / conj w ^ 2)) = a * conj b := by
  have hc : conj w ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hw
  simp only [map_mul, map_div₀, map_pow, conj_conj]
  field_simp

/-- Hyperbolic L2 norm is invariant under inversion, including infinite norms. -/
theorem s7et_normL2_inv (F : ℂ → ℂ) :
    normL2 unitDiscExterior (fun w => F w⁻¹) = normL2 unitDisc F := by
  have hi := fdr_lintegral_inv resolvent_exterior_isOpen.measurableSet
    (fun w hw => resolvent_exterior_ne_zero hw)
    (fun z => (‖F z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z))
  rw [resolvent_inv_exterior_conformal.2.2] at hi
  unfold normL2
  congr 1
  calc
    _ = ∫⁻ w in unitDiscExterior,
        ENNReal.ofReal (‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2) *
          ((‖F w⁻¹‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w⁻¹)) := by
      apply setLIntegral_congr_fun resolvent_exterior_isOpen.measurableSet
      intro w hw
      dsimp only
      rw [mul_left_comm,
        ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm (‖deriv _ w‖ ^ 2),
        rho_inv_jacobian (resolvent_exterior_ne_zero hw)]
    _ = ∫⁻ z in unitDisc \ {0}, (‖F z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := hi.symm
    _ = _ := setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))

/-- The raw forcing of Proposition 7.2 is the inversion of a genuinely smooth,
bounded, finite-energy function on the entire disk, including zero. -/
theorem s7et_forcing_disk {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ F : ℂ → ℂ, F ∈ BCinf unitDisc ∧ normL2 unitDisc F < ∞ ∧
      (fun w => μ w * conj (ν w)) =ᵐ[volume.restrict unitDiscExterior]
        (fun w => F w⁻¹) := by
  have hm := (harmonicL2_subset_harmonic.choose_spec μ hμ).1
  obtain ⟨φ, hφ⟩ := Lambda_surjective_harmonic hm
  obtain ⟨ψ, hψ⟩ := Lambda_surjective_harmonic hν
  let F := fun z => s7et_diskRep φ z * conj (s7et_diskRep ψ z)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) F unitDisc :=
    (s7et_diskRep_smooth φ).mul
      (Complex.conjCLE.contDiff.comp_contDiffOn (s7et_diskRep_smooth ψ))
  have hb : ∀ z ∈ unitDisc, ‖F z‖ ≤ (‖φ‖ / 2) * (‖ψ‖ / 2) := by
    intro z hz
    simp only [F, norm_mul, norm_conj]
    exact mul_le_mul (s7et_diskRep_bound φ hz) (s7et_diskRep_bound ψ hz)
      (norm_nonneg _) (by positivity)
  have he : (fun w => μ w * conj (ν w)) =ᵐ[volume.restrict unitDiscExterior]
      (fun w => F w⁻¹) := by
    filter_upwards [s7et_lambda_phase φ, s7et_lambda_phase ψ, wp_harmonic_toLinf_ae hμ,
      ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with w ha hb hμw hw
    rw [hφ, hμw] at ha
    rw [hψ] at hb
    change μ w * conj (ν w) = s7et_diskRep φ w⁻¹ * conj (s7et_diskRep ψ w⁻¹)
    rw [ha, hb]
    exact s7et_phase_cancel _ _ _ (resolvent_exterior_ne_zero hw)
  refine ⟨F, ⟨hsm, _, hb⟩, ?_, he⟩
  rw [← s7et_normL2_inv F, ← grp_normL2_congr_ae he]
  exact s7ed_forcing_finite hμ ν

/-- Inverting a disk input transports the actual resolvent integral.
The arbitrary center value of the measurable pullback is discarded only a.e. -/
theorem s7et_resolvent_inv (F : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    resolventStar (fun w => F w⁻¹) z = resolventOp unitDisc F z⁻¹ := by
  rw [resolventStar, resolventOp_exterior_inv _ hz]
  apply integral_congr_ae
  have hn : ∀ᵐ w ∂(volume.restrict unitDisc), w ≠ (0 : ℂ) :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton 0))
  filter_upwards [ae_restrict_mem measurableSet_ball, hn] with w hw hw0
  have hwp : w ∈ unitDisc \ {0} := ⟨hw, hw0⟩
  simp only [resolventExteriorPullback, piecewise_eq_of_mem _ _ _ hwp, inv_inv]

/-- Completed forcing and potential bridge for Proposition 7.2. The disk
potential is smooth at zero and has finite weighted L2 norm. -/
theorem s7et_forcing_potential_bridge {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ F : ℂ → ℂ, F ∈ BCinf unitDisc ∧ normL2 unitDisc F < ∞ ∧
      (fun w => μ w * conj (ν w)) =ᵐ[volume.restrict unitDiscExterior]
        (fun w => F w⁻¹) ∧
      resolventOp unitDisc F ∈ BCinf unitDisc ∧
      normL2 unitDisc (resolventOp unitDisc F) < ∞ ∧
      ∀ z ∈ unitDiscExterior,
        resolventStar (fun w => μ w * conj (ν w)) z = resolventOp unitDisc F z⁻¹ := by
  obtain ⟨F, hF, hn, he⟩ := s7et_forcing_disk hμ hν
  refine ⟨F, hF, hn, he, RK3_output_BCinf_disc hF, s7rl_finite (Or.inl rfl) hF hn, ?_⟩
  intro z hz
  rw [← s7et_resolvent_inv F hz]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  simp only [hw]

end TakhtajanTeo
