import TakhtajanTeo.Ch1.ResolventExteriorSmoothness
import TakhtajanTeo.Ch1.ResolventUniqueness
import TakhtajanTeo.Ch1.ResolventWeakToStrong

/-! The exterior half of RK3 (TT:1112–1124): the inhomogeneous equation and the inverse identity on `𝔻*`,
obtained from the disk resolvent of the inverted input on the punctured disk. The inverted input is only
continuous on `𝔻 \ {0}`; the center is never assumed regular. -/

open Real Complex Filter Set Topology MeasureTheory Metric
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem resolvent_punct_isOpen : IsOpen (unitDisc \ {(0 : ℂ)}) :=
  isOpen_ball.sdiff isClosed_singleton

/-- A global C² representative of a function C² on the punctured disk, equal to it near a compact
subset of the punctured disk. -/
theorem resolvent_punct_global_rep {f φ : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f (unitDisc \ {0}))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc \ {0}) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ tsupport φ ⊆ ball (0 : ℂ) R ∧
      ∃ F : ℂ → ℂ, ContDiff ℝ 2 F ∧ ∀ z ∈ tsupport φ, F =ᶠ[𝓝 z] f := by
  obtain ⟨R, hR0, hR1, hRs⟩ := resolvent_compact_subdisk hc (hs.trans sdiff_subset)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ tsupport φ, m ≤ ‖z‖ := by
    by_cases hn : (tsupport φ).Nonempty
    · obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hn continuous_norm.continuousOn
      exact ⟨‖z‖, norm_pos_iff.mpr (by simpa using (hs hz).2), fun w hw => hmin hw⟩
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hn⟩
  let bR : ContDiffBump (0 : ℂ) :=
    { rIn := (R + 1) / 2, rOut := (R + 3) / 4,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let b0 : ContDiffBump (0 : ℂ) :=
    { rIn := m / 4, rOut := m / 2,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let h : ℂ → ℂ := fun z => (bR z : ℂ) * (1 - (b0 z : ℂ))
  have hbR : ContDiff ℝ (2 : ℕ∞) (fun z => (bR z : ℂ)) := Complex.ofRealCLM.contDiff.comp bR.contDiff
  have hb0 : ContDiff ℝ (2 : ℕ∞) (fun z => (b0 z : ℂ)) := Complex.ofRealCLM.contDiff.comp b0.contDiff
  have hh : ContDiff ℝ (2 : ℕ∞) h := hbR.mul (contDiff_const.sub hb0)
  have hP : IsOpen (unitDisc \ {(0 : ℂ)}) := resolvent_punct_isOpen
  have hh0 : h =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [b0.eventuallyEq_one_of_mem_ball (mem_ball_self b0.rIn_pos)] with w hw
    simp [h, hw]
  have hhs : tsupport h ⊆ unitDisc \ {0} := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have h1 : z ∈ tsupport (fun z => (bR z : ℂ)) := tsupport_mul_subset_left hz
      have h2 := tsupport_comp_subset (g := Complex.ofReal) (by simp) bR h1
      rw [bR.tsupport_eq] at h2
      have hn : ‖z‖ ≤ (R + 3) / 4 := mem_closedBall_zero_iff.mp h2
      apply mem_ball_zero_iff.mpr
      linarith
    · intro hz0
      have hz0' : z = 0 := by simpa using hz0
      subst hz0'
      exact (notMem_tsupport_iff_eventuallyEq.mpr hh0) hz
  refine ⟨R, hR0, hR1, hRs, fun w => f w * h w, ?_, ?_⟩
  · exact resolvent_source_mul_contDiff hP hh hf hhs
  · intro z hz
    have hzR : z ∈ ball (0 : ℂ) bR.rIn := mem_ball_zero_iff.mpr (by
      have := mem_ball_zero_iff.mp (hRs hz)
      dsimp [bR]; linarith)
    have hzb : z ∉ tsupport (b0 : ℂ → ℝ) := by
      rw [b0.tsupport_eq]
      intro hz'
      have := mem_closedBall_zero_iff.mp hz'
      have := hm z hz
      dsimp [b0] at *
      linarith
    filter_upwards [bR.eventuallyEq_one_of_mem_ball hzR,
      notMem_tsupport_iff_eventuallyEq.mp hzb] with w h1 h2
    simp [h, h1, h2]

/-- Integration by parts on the punctured disk against compact tests supported there. -/
theorem resolvent_mixed_pairing_punct {f φ : ℂ → ℂ} (hf : ContDiffOn ℝ 2 f (unitDisc \ {0}))
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc \ {0}) :
    (∫ z in unitDisc, f z * dz (dzbar φ) z) = ∫ z in unitDisc, φ z * dz (dzbar f) z := by
  obtain ⟨R, hR0, hR1, hRs, F, hF, hFe⟩ := resolvent_punct_global_rep hf hc hs
  have p1 : ∀ z, f z * dz (dzbar φ) z = F z * dz (dzbar φ) z := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [(hFe z hz).self_of_nhds]
    · rw [resolvent_mixed_zero_of_notMem_tsupport hz]; simp
  have p2 : ∀ z, φ z * dz (dzbar f) z = φ z * dz (dzbar F) z := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [resolvent_mixed_congr_of_eventuallyEq (hFe z hz)]
    · rw [image_eq_zero_of_notMem_tsupport hz]; simp
  have hD : MeasurableSet unitDisc := measurableSet_ball
  calc (∫ z in unitDisc, f z * dz (dzbar φ) z) = ∫ z in unitDisc, F z * dz (dzbar φ) z := by
        congr 1; funext z; exact p1 z
    _ = ∫ z in ball (0 : ℂ) R, F z * dz (dzbar φ) z := by
        rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD (ball_subset_ball hR1.le)]
        intro z hz
        rw [resolvent_mixed_zero_of_notMem_tsupport (fun h => hz.2 (hRs h)), mul_zero]
    _ = ∫ z in ball (0 : ℂ) R, φ z * dz (dzbar F) z := resolvent_mixed_pairing_subdisk hF hφ hR0 hRs
    _ = ∫ z in unitDisc, φ z * dz (dzbar F) z := by
        rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD (ball_subset_ball hR1.le)]
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hRs h)), zero_mul]
    _ = ∫ z in unitDisc, φ z * dz (dzbar f) z := by
        congr 1; funext z; exact (p2 z).symm

/-- A locally continuous punctured-disk function times a compact test supported there is integrable. -/
theorem resolvent_mul_test_integrable_punct {f ψ : ℂ → ℂ} (hf : ContinuousOn f (unitDisc \ {0}))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ unitDisc \ {0}) :
    IntegrableOn (fun z => f z * ψ z) unitDisc := by
  have ht : Continuous (fun z => f z * ψ z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z ∈ unitDisc \ {0}
    · exact (hf.continuousAt (resolvent_punct_isOpen.mem_nhds hz)).mul hψ.continuousAt
    · have hzS : z ∉ tsupport ψ := fun h => hz (hs h)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzS] with w hw
      simp only [hw, Pi.zero_apply, mul_zero]
  have htc : HasCompactSupport (fun z => f z * ψ z) :=
    hc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right
  exact (ht.integrable_of_hasCompactSupport htc).integrableOn

theorem resolvent_mixed_continuousOn_punct {u : ℂ → ℂ} (hu : ContDiffOn ℝ 2 u (unitDisc \ {0})) :
    ContinuousOn (dz (dzbar u)) (unitDisc \ {0}) := by
  have hb := (resolvent_contDiffOn_wirtinger resolvent_punct_isOpen hu).2
  have hd : ContDiffOn ℝ 0 (fderiv ℝ (dzbar u)) (unitDisc \ {0}) :=
    hb.fderiv_of_isOpen resolvent_punct_isOpen (by norm_num)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hI := hd.clm_apply (contDiffOn_const (c := I))
  exact ((h1.sub (contDiffOn_const.mul hI)).div_const 2).continuousOn

/-- The weak equation tested against compact functions of the punctured disk gives a vanishing residual. -/
theorem resolvent_weak_residual_test_punct {u f φ : ℂ → ℂ}
    (hu : ContDiffOn ℝ 2 u (unitDisc \ {0})) (hf : ContinuousOn f (unitDisc \ {0}))
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ unitDisc \ {0})
    (hw : (∫ z in unitDisc, u z * (2 * laplace0 φ z + φ z) * rho z) =
      ∫ z in unitDisc, f z * φ z * rho z) :
    (∫ z in unitDisc, ((rho z : ℂ) * (u z - f z) - 2 * dz (dzbar u) z) * φ z) = 0 := by
  have hMc : Continuous (dz (dzbar φ)) := continuous_dz (resolvent_contDiff_wirtinger hφ).2
  have hMC : HasCompactSupport (dz (dzbar φ)) :=
    hc.of_isClosed_subset (isClosed_tsupport _) resolvent_mixed_tsupport
  have hMs : tsupport (dz (dzbar φ)) ⊆ unitDisc \ {0} := resolvent_mixed_tsupport.trans hs
  have hρP : ContinuousOn (fun z : ℂ => (rho z : ℂ)) (unitDisc \ {0}) :=
    resolvent_rho_continuousOn.mono sdiff_subset
  have hA := resolvent_mul_test_integrable_punct (hρP.mul hu.continuousOn) hφ.continuous hc hs
  have hB := resolvent_mul_test_integrable_punct hu.continuousOn hMc hMC hMs
  have hC := resolvent_mul_test_integrable_punct (hρP.mul hf) hφ.continuous hc hs
  have hD := resolvent_mul_test_integrable_punct (resolvent_mixed_continuousOn_punct hu)
    hφ.continuous hc hs
  simp only [Pi.mul_apply] at hA hC
  have hAC : IntegrableOn (fun z => ((rho z : ℂ) * u z) * φ z - ((rho z : ℂ) * f z) * φ z)
      unitDisc := hA.sub hC
  have hpair : (∫ z in unitDisc, u z * dz (dzbar φ) z) =
      ∫ z in unitDisc, dz (dzbar u) z * φ z := by
    rw [resolvent_mixed_pairing_punct hu hφ hc hs]
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
    ring
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

/-- The pointwise equation on the punctured disk for the disk resolvent of a bounded measurable input
that is smooth there. -/
theorem resolvent_equation_punct {g : ℂ → ℂ} (hgm : Measurable g)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (unitDisc \ {0})) (hb : ∃ C : ℝ, ∀ w ∈ unitDisc, ‖g w‖ ≤ C) :
    ∀ z ∈ unitDisc \ {0}, 2 * (laplace0 (resolventOp unitDisc g) z +
      (1 / 2) * resolventOp unitDisc g z) = g z := by
  have hP : IsOpen (unitDisc \ {(0 : ℂ)}) := resolvent_punct_isOpen
  let u := resolventOp unitDisc g
  have hu : ContDiffOn ℝ 2 u (unitDisc \ {0}) :=
    (resolventOp_contDiffOn_of_measurable_locally_smooth hP sdiff_subset hgm hg hb).of_le
      (by norm_num)
  have hgc : ContinuousOn g (unitDisc \ {0}) := hg.continuousOn
  let E : ℂ → ℂ := fun z => (rho z : ℂ) * (u z - g z) - 2 * dz (dzbar u) z
  have hEc : ContinuousOn E (unitDisc \ {0}) :=
    ((resolvent_rho_continuousOn.mono sdiff_subset).mul (hu.continuousOn.sub hgc)).sub
      (continuousOn_const.mul (resolvent_mixed_continuousOn_punct hu))
  have hEl : LocallyIntegrableOn E (unitDisc \ {0}) volume :=
    hEc.locallyIntegrableOn hP.measurableSet
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∈ unitDisc \ {0} → E z = 0 := by
    apply hP.ae_eq_zero_of_integral_contDiff_smul_eq_zero hEl
    intro ψ hψ hc hs
    let φ : ℂ → ℂ := fun z => (ψ z : ℂ)
    have hφ : ContDiff ℝ 2 φ :=
      (Complex.ofRealCLM.contDiff.comp hψ).of_le (by norm_num)
    have hφs : tsupport φ ⊆ tsupport ψ := tsupport_comp_subset (g := Complex.ofReal) (by simp) ψ
    have hφC : HasCompactSupport φ := hc.of_isClosed_subset (isClosed_tsupport _) hφs
    obtain ⟨C, hC⟩ := hb
    have hw := resolvent_disc_weak_equation
      (hgm.aestronglyMeasurable) hC hφ hφC ((hφs.trans hs).trans sdiff_subset)
    have hr := resolvent_weak_residual_test_punct hu hgc hφ hφC (hφs.trans hs) hw
    have he : (∫ z : ℂ, ψ z • E z) = ∫ z in unitDisc, E z * φ z := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := unitDisc)
        (fun z hz => by
          have hzS : z ∉ tsupport ψ := fun h => hz (sdiff_subset (hs h))
          rw [image_eq_zero_of_notMem_tsupport hzS, zero_smul])]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [φ, Complex.real_smul]
      ring
    rw [he]
    exact hr
  have hAE : E =ᵐ[volume.restrict (unitDisc \ {0})] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hP.measurableSet] with z hz hzD
    exact hz hzD
  have hEq := Measure.eqOn_open_of_ae_eq (μ := volume) hAE hP hEc continuousOn_const
  intro z hz
  have he := hEq hz
  change (rho z : ℂ) * (u z - g z) - 2 * dz (dzbar u) z = 0 at he
  have hρ : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inl rfl) hz.1)))
  change 2 * (laplace0 u z + (1 / 2) * u z) = g z
  unfold laplace0
  field_simp
  linear_combination he

/-- The inhomogeneous equation of RK3 on `𝔻*`. -/
theorem RK3_output_equation_exterior {g : ℂ → ℂ} (hg : g ∈ BCinf unitDiscExterior) :
    ∀ z ∈ unitDiscExterior, 2 * (laplace0 (resolventOp unitDiscExterior g) z +
      (1 / 2) * resolventOp unitDiscExterior g z) = g z := by
  obtain ⟨C, hC⟩ := hg.2
  have hCb : ∀ w ∈ unitDiscExterior, ‖g w‖ ≤ max C 0 :=
    fun w hw => (hC w hw).trans (le_max_left _ _)
  have hbound : ∃ C : ℝ, ∀ w ∈ unitDisc, ‖resolventExteriorPullback g w‖ ≤ C :=
    ⟨max C 0, resolventExteriorPullback_bound (le_max_right _ _) hCb⟩
  have hP : IsOpen (unitDisc \ {(0 : ℂ)}) := resolvent_punct_isOpen
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (resolventOp unitDisc (resolventExteriorPullback g))
      (unitDisc \ {0}) :=
    resolventOp_contDiffOn_of_measurable_locally_smooth hP sdiff_subset
      (resolventExteriorPullback_measurable hg.1.continuousOn)
      (resolventExteriorPullback_contDiffOn hg.1) hbound
  have heqP := resolvent_equation_punct (resolventExteriorPullback_measurable hg.1.continuousOn)
    (resolventExteriorPullback_contDiffOn hg.1) hbound
  intro z hz
  have hz0 : z ≠ 0 := resolvent_exterior_ne_zero hz
  have hm : MapsTo (fun z : ℂ => z⁻¹) unitDiscExterior (unitDisc \ {0}) :=
    resolvent_inv_exterior_conformal.mapsTo
  have hzP : z⁻¹ ∈ unitDisc \ {0} := hm hz
  have hi : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) unitDiscExterior := fun w hw =>
    (differentiableAt_inv (resolvent_exterior_ne_zero hw)).differentiableWithinAt
  have hρ : rho z ≠ 0 := div_ne_zero (by norm_num)
    (pow_ne_zero 2 (resolvent_domain_denominator_ne_zero (Or.inr rfl) hz))
  have heq : resolventOp unitDiscExterior g =ᶠ[𝓝 z]
      (resolventOp unitDisc (resolventExteriorPullback g) ∘ fun w : ℂ => w⁻¹) := by
    filter_upwards [resolvent_exterior_isOpen.mem_nhds hz] with w hw
    exact resolventOp_exterior_inv g hw
  rw [laplace0_congr_of_eventuallyEq heq,
    laplace0_comp_of_density_pullback resolvent_exterior_isOpen hP hi hm
      (hsm.of_le (by norm_num)) hz hρ (rho_inv_jacobian hz0),
    resolventOp_exterior_inv g hz]
  have h := heqP z⁻¹ hzP
  have hG : resolventExteriorPullback g z⁻¹ = g z := by
    simp [resolventExteriorPullback, hzP]
  rw [hG] at h
  exact h

/-- The reverse identity of RK3 on `𝔻*`. -/
theorem RK3_inverse_exterior {f : ℂ → ℂ} (hf : f ∈ BCinf unitDiscExterior)
    (hg : (fun z => 2 * (laplace0 f z + (1 / 2) * f z)) ∈ BCinf unitDiscExterior) :
    ∀ z ∈ unitDiscExterior,
      f z = resolventOp unitDiscExterior (fun w => 2 * (laplace0 f w + (1 / 2) * f w)) z := by
  let g : ℂ → ℂ := fun z => 2 * (laplace0 f z + (1 / 2) * f z)
  have hu := RK3_output_BCinf_exterior hg
  have hf2 : ContDiffOn ℝ 2 f unitDiscExterior := hf.1.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (resolventOp unitDiscExterior g) unitDiscExterior :=
    hu.1.of_le (by norm_num)
  have hb : ∃ C : ℝ, ∀ z ∈ unitDiscExterior, ‖f z - resolventOp unitDiscExterior g z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hf.2
    obtain ⟨B, hB⟩ := hu.2
    exact ⟨C + B, fun z hz => (norm_sub_le _ _).trans (add_le_add (hC z hz) (hB z hz))⟩
  have he : ∀ z ∈ unitDiscExterior, laplace0 (fun w => f w - resolventOp unitDiscExterior g w) z +
      (f z - resolventOp unitDiscExterior g z) / 2 = 0 := by
    intro z hz
    rw [resolvent_laplace_sub resolvent_exterior_isOpen hf2 hu2 hz]
    have hp := RK3_output_equation_exterior hg z hz
    change 2 * (laplace0 (resolventOp unitDiscExterior g) z +
      (1 / 2) * resolventOp unitDiscExterior g z) =
      2 * (laplace0 f z + (1 / 2) * f z) at hp
    linear_combination -hp / 2
  have hzero := resolvent_homogeneous_unique_exterior_C2 (hf2.sub hu2) hb he
  intro z hz
  exact sub_eq_zero.mp (hzero hz)

end TakhtajanTeo
