import TakhtajanTeo.Ch1.S7ExteriorTransport

/-! Actual second antiholomorphic differential and weighted energy under
disk/exterior inversion. No energy identity is assumed. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual weighted second antiholomorphic differential. -/
def s7et_q (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar h w) z

/-- Both derivatives depend only on the original function germ. -/
theorem s7et_q_congr {h g : ℂ → ℂ} {z : ℂ} (he : h =ᶠ[𝓝 z] g) :
    s7et_q h z = s7et_q g z := by
  have hb : dzbar h =ᶠ[𝓝 z] dzbar g := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    simp only [dzbar, hw]
  apply dzbar_congr_of_eventuallyEq
  filter_upwards [hb] with w hw
  rw [hw]

/-- The genuine Wirtinger chain rule for inversion. -/
theorem s7et_dzbar_inv {h : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hh : DifferentiableAt ℝ h z⁻¹) :
    dzbar (fun w => h w⁻¹) z = -(dzbar h z⁻¹) / conj z ^ 2 := by
  have he := (eq6_4 (differentiableAt_inv hz) hh).2
  rw [(hasDerivAt_inv hz).deriv] at he
  simpa only [Function.comp_def, map_neg, map_inv₀, map_pow, div_eq_mul_inv,
    mul_neg, neg_mul] using he

/-- Actual inversion covariance, including the complex phase rather than
only a norm identity. -/
theorem s7et_q_inv {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s7et_q (fun w => h w⁻¹) z = (z / conj z) ^ 2 * s7et_q h z⁻¹ := by
  let b := fun w => (rho w : ℂ)⁻¹ * dzbar h w
  have hbsm : ContDiffOn ℝ (⊤ : ℕ∞) b unitDisc :=
    (wp_rho_inv_contDiff.of_le le_top).contDiffOn.mul
      (wp_contDiffOn_dzbar hh isOpen_ball (by simp))
  have hzd := (resolvent_inv_exterior_conformal.mapsTo hz).1
  have hz0 := resolvent_exterior_ne_zero hz
  have hcz0 : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz0
  have hbd : DifferentiableAt ℝ b z⁻¹ :=
    (hbsm.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hzd)
  have he : (fun w => (rho w : ℂ)⁻¹ * dzbar (fun v => h v⁻¹) w) =ᶠ[𝓝 z]
      (fun w => -(w ^ 2) * b w⁻¹) := by
    filter_upwards [resolvent_exterior_isOpen.mem_nhds hz] with w hw
    have hw0 := resolvent_exterior_ne_zero hw
    have hcw0 : conj w ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hw0
    have hwd := (resolvent_inv_exterior_conformal.mapsTo hw).1
    have hhd : DifferentiableAt ℝ h w⁻¹ :=
      (hh.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hwd)
    rw [s7et_dzbar_inv hw0 hhd]
    dsimp only [b]
    simp only [wp_rho_inv_complex, map_inv₀]
    field_simp
    <;> ring
  have hc : DifferentiableAt ℂ (fun w : ℂ => -(w ^ 2)) z := differentiableAt_id.pow 2 |>.neg
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz0
  have hi : DifferentiableAt ℝ (fun w => b w⁻¹) z :=
    hbd.comp z (hinv.restrictScalars ℝ)
  change dzbar _ z = _
  rw [dzbar_congr_of_eventuallyEq he, dzbar_mul (hc.restrictScalars ℝ) hi,
    (cauchyRiemann_iff.mp hc).2, mul_zero, add_zero, s7et_dzbar_inv hz0 hbd]
  dsimp only [s7et_q, b]
  field_simp

/-- Equality throughout the exterior supplies the neighborhood equality
needed before taking the two derivatives. -/
theorem s7et_q_of_eqOn_inv {H h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (he : EqOn H (fun w => h w⁻¹) unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s7et_q H z = (z / conj z) ^ 2 * s7et_q h z⁻¹ := by
  have hg : H =ᶠ[𝓝 z] (fun w => h w⁻¹) := by
    filter_upwards [resolvent_exterior_isOpen.mem_nhds hz] with w hw
    exact he hw
  rw [s7et_q_congr hg, s7et_q_inv hh hz]

theorem s7et_phase_norm {z : ℂ} (hz : z ≠ 0) : ‖(z / conj z) ^ 2‖ = 1 := by
  simp only [norm_pow, norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hz), one_pow]

/-- Multiplication by the actual inversion phase preserves the weighted norm. -/
theorem s7et_normL2_phase_inv (F : ℂ → ℂ) :
    normL2 unitDiscExterior (fun z => (z / conj z) ^ 2 * F z⁻¹) = normL2 unitDisc F := by
  rw [← s7et_normL2_inv F]
  unfold normL2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
  have hn : ‖(z / conj z) ^ 2 * F z⁻¹‖₊ = ‖F z⁻¹‖₊ := by
    apply Subtype.ext
    change ‖(z / conj z) ^ 2 * F z⁻¹‖ = ‖F z⁻¹‖
    rw [norm_mul, s7et_phase_norm (resolvent_exterior_ne_zero hz), one_mul]
  simp only [hn]

/-- Energy transfer for the actual second differential, without assuming
that either side is finite. -/
theorem s7et_q_normL2 {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) :
    normL2 unitDiscExterior (s7et_q (fun w => h w⁻¹)) = normL2 unitDisc (s7et_q h) := by
  have he : s7et_q (fun w => h w⁻¹) =ᵐ[volume.restrict unitDiscExterior]
      (fun z => (z / conj z) ^ 2 * s7et_q h z⁻¹) := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact s7et_q_inv hh hz
  rw [grp_normL2_congr_ae he, s7et_normL2_phase_inv]

/-- Exact hyperbolic complex pairing under inversion. The existing conformal
change of variables also handles totalized integrals. -/
theorem s7et_pairing_inv (F G : ℂ → ℂ) :
    (∫ z in unitDiscExterior, F z⁻¹ * conj (G z⁻¹) * rho z) =
      ∫ z in unitDisc, F z * conj (G z) * rho z := by
  have hc := resolvent_inv_exterior_conformal
  have hi := ahP_integral_image (U := unitDiscExterior) resolvent_exterior_isOpen
    hc.1 hc.2.1 (fun z => F z * conj (G z) * rho z)
  rw [hc.2.2] at hi
  calc
    _ = ∫ z in unitDiscExterior, ‖deriv (fun w : ℂ => w⁻¹) z‖ ^ 2 •
        (F z⁻¹ * conj (G z⁻¹) * rho z⁻¹) := by
      apply setIntegral_congr_fun resolvent_exterior_isOpen.measurableSet
      intro z hz
      dsimp only
      have hr := congrArg Complex.ofReal (rho_inv_jacobian (resolvent_exterior_ne_zero hz))
      push_cast at hr
      simp only [Complex.real_smul, Complex.ofReal_pow]
      linear_combination -(F z⁻¹ * conj (G z⁻¹)) * hr
    _ = ∫ z in unitDisc \ {0}, F z * conj (G z) * rho z := hi.symm
    _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))

/-- Pairing transport for actual representatives known only almost everywhere. -/
theorem s7et_pairing_transport_ae {f g F G : ℂ → ℂ}
    (hf : f =ᵐ[volume.restrict unitDiscExterior] (fun z => F z⁻¹))
    (hg : g =ᵐ[volume.restrict unitDiscExterior] (fun z => G z⁻¹)) :
    l2Inner f g = ∫ z in unitDisc, F z * conj (G z) * rho z := by
  rw [← s7et_pairing_inv F G]
  apply integral_congr_ae
  filter_upwards [hf, hg] with z hfz hgz
  simp only [hfz, hgz]

/-- The phase cancels in the full complex pairing, not only in its diagonal. -/
theorem s7et_pairing_phase_inv (F G : ℂ → ℂ) :
    l2Inner (fun z => (z / conj z) ^ 2 * F z⁻¹)
      (fun z => (z / conj z) ^ 2 * G z⁻¹) =
      ∫ z in unitDisc, F z * conj (G z) * rho z := by
  rw [← s7et_pairing_inv F G]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
  have he : ((z / conj z) ^ 2 * F z⁻¹) * conj ((z / conj z) ^ 2 * G z⁻¹) =
      F z⁻¹ * conj (G z⁻¹) := by
    simpa only [div_pow, mul_comm] using
      s7et_phase_cancel (F z⁻¹) (G z⁻¹) z (resolvent_exterior_ne_zero hz)
  rw [he]

/-- The original Qdot formula is transported using equality of potential
germs and the actual second-derivative phase law. -/
theorem s7et_Qdot_of_potential {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (he : EqOn (resolventStar (fun w => μ w * conj (ν w)))
      (fun w => h w⁻¹) unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Qdot (toLinf μ) ν z = (z / conj z) ^ 2 * (-2 * s7et_q h z⁻¹) := by
  rw [s7ed_Qdot_raw hμ hν hz]
  change -2 * s7et_q (resolventStar (fun w => μ w * conj (ν w))) z = _
  rw [s7et_q_of_eqOn_inv hh he hz]
  ring

/-- All three terms in the original Proposition 7.2 energy identity transfer
to the disk, as does its norm-finiteness target. This does not assume or assert
the disk energy identity, which is a separate theorem. -/
theorem s7et_prop72_reduction {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ F : ℂ → ℂ, F ∈ BCinf unitDisc ∧ normL2 unitDisc F < ∞ ∧
      resolventOp unitDisc F ∈ BCinf unitDisc ∧
      normL2 unitDisc (resolventOp unitDisc F) < ∞ ∧
      (∀ z ∈ unitDiscExterior, Qdot (toLinf μ) ν z =
        (z / conj z) ^ 2 * (-2 * s7et_q (resolventOp unitDisc F) z⁻¹)) ∧
      normL2 unitDiscExterior (Qdot (toLinf μ) ν) =
        normL2 unitDisc (fun z => -2 * s7et_q (resolventOp unitDisc F) z) ∧
      l2Inner (Qdot (toLinf μ) ν) (Qdot (toLinf μ) ν) =
        (∫ z in unitDisc, (-2 * s7et_q (resolventOp unitDisc F) z) *
          conj (-2 * s7et_q (resolventOp unitDisc F) z) * rho z) ∧
      l2Inner (fun z => μ z * conj (ν z)) (fun z => μ z * conj (ν z)) =
        (∫ z in unitDisc, F z * conj (F z) * rho z) ∧
      l2Inner (fun z => μ z * conj (ν z)) (resolventStar (fun z => μ z * conj (ν z))) =
        ∫ z in unitDisc, F z * conj (resolventOp unitDisc F z) * rho z := by
  obtain ⟨F, hF, hFn, he, hH, hHn, hpot⟩ := s7et_forcing_potential_bridge hμ hν
  let D := fun z => -2 * s7et_q (resolventOp unitDisc F) z
  have hQ : ∀ z ∈ unitDiscExterior,
      Qdot (toLinf μ) ν z = (z / conj z) ^ 2 * D z⁻¹ := by
    intro z hz
    exact s7et_Qdot_of_potential hμ hν hH.1 (fun w hw => hpot w hw) hz
  have hQae : Qdot (toLinf μ) ν =ᵐ[volume.restrict unitDiscExterior]
      (fun z => (z / conj z) ^ 2 * D z⁻¹) := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact hQ z hz
  have hPae : resolventStar (fun z => μ z * conj (ν z)) =ᵐ[volume.restrict unitDiscExterior]
      (fun z => resolventOp unitDisc F z⁻¹) := by
    filter_upwards [ae_restrict_mem resolvent_exterior_isOpen.measurableSet] with z hz
    exact hpot z hz
  refine ⟨F, hF, hFn, hH, hHn, hQ, ?_, ?_,
    s7et_pairing_transport_ae he he, s7et_pairing_transport_ae he hPae⟩
  · rw [grp_normL2_congr_ae hQae, s7et_normL2_phase_inv]
  · change l2Inner _ _ = ∫ z in unitDisc, D z * conj (D z) * rho z
    rw [← s7et_pairing_phase_inv D D]
    apply integral_congr_ae
    filter_upwards [hQae] with z hz
    simp only [hz]

end TakhtajanTeo
