import TakhtajanTeo.Ch1.Remark24Completed
import TakhtajanTeo.Ch1.Lemma29Plane
import TakhtajanTeo.Ch1.ComponentTB
import TakhtajanTeo.Ch1.GroupAlgebra

/-! The actual Hilbert Bers differential: forward estimates and its bounded
A2 lift. General-base injectivity and surjectivity are separate obligations.
This downstream module preserves the existing upstream HilbertBersDifferential. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The first clause of Theorem 2.3, independently of the reproducing formula. -/
theorem hbL2_forward {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    AInf.toFun (D0BersR μ (toLinf ν)) ∈ A2fun unitDisc ∧
      normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤
        ENNReal.ofReal 24 * normL2 unitDiscExterior ν := by
  have hae := bc_toLinf_ae (d2_harmonicL2_memLp hν)
  have hn : normL2 unitDiscExterior (toLinf ν) = normL2 unitDiscExterior ν := by
    unfold normL2
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hae] with z hz
    rw [hz]
  have hb := remark_2_4 hμ (toLinf ν)
  rw [hn] at hb
  have hb' : normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤
      ENNReal.ofReal 24 * normL2 unitDiscExterior ν := by simpa using hb
  obtain ⟨φ, hφ, hrep, hfin⟩ := hν
  exact ⟨⟨(D0BersR μ (toLinf ν)).property,
    hb'.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)⟩, hb'⟩

theorem hbL2_distT_subset {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    distT μ ⊆ A2fun unitDisc := by
  rintro f ⟨ν, hν, rfl⟩
  exact (hbL2_forward hμ hν).1

theorem hbL2_distT_saturation_subset {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    {φ | ∃ ψ ∈ distT μ, EqOn ψ φ unitDisc} ⊆
      {φ | ∃ ψ ∈ A2fun unitDisc, EqOn ψ φ unitDisc} := by
  rintro φ ⟨ψ, hψ, heq⟩
  exact ⟨ψ, hbL2_distT_subset hμ hψ, heq⟩

/-- The ambient A-infinity-valued derivative in A2 coordinates. -/
def hbL2_ambient (μ : LinfStar) : A2 unitDisc →L[ℂ] AInf unitDisc :=
  (D0BersR μ).comp (((Submodule.subtypeL harmonicBeltrami).comp
    LambdaEquiv.toContinuousLinearMap).comp A2toAInfCLM)

theorem hbL2_ambient_apply (μ : LinfStar) (φ : A2 unitDisc) :
    hbL2_ambient μ φ = D0BersR μ (Lambda (A2toAInf φ)) := rfl

theorem hbL2_ambient_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (φ : A2 unitDisc) :
    normA2 unitDisc (AInf.toFun (hbL2_ambient μ φ)) ≤ ENNReal.ofReal (48 * ‖φ‖) := by
  rw [hbL2_ambient_apply]
  have hb := remark_2_4 hμ (Lambda (A2toAInf φ))
  rw [l29b_Lambda_L2] at hb
  calc normA2 unitDisc (AInf.toFun (D0BersR μ (Lambda (A2toAInf φ))))
      ≤ 24 * (2 * (‖φ‖₊ : ℝ≥0∞)) := hb
    _ = ENNReal.ofReal (48 * ‖φ‖) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 48), ofReal_norm, enorm_eq_nnnorm]
      norm_num
      ring

theorem hbL2_ambient_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (φ : A2 unitDisc) :
    AInf.toFun (hbL2_ambient μ φ) ∈ A2fun unitDisc :=
  ⟨(hbL2_ambient μ φ).property, (hbL2_ambient_bound hμ φ).trans_lt ENNReal.ofReal_lt_top⟩

def hbL2_linear (μ : LinfStarBall) : A2 unitDisc →ₗ[ℂ] A2 unitDisc where
  toFun φ := toA2 unitDisc (AInf.toFun (hbL2_ambient μ φ))
  map_add' a b := by
    apply A2toAInf_injective
    have hadd : ∀ x y, A2toAInf (x + y) = A2toAInf x + A2toAInf y := fun x y => map_add A2toAInfCLM x y
    rw [hadd, ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 _),
      ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 _), ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 _), map_add]
  map_smul' c a := by
    apply A2toAInf_injective
    simp only [RingHom.id_apply]
    have hsmul : ∀ (c : ℂ) x, A2toAInf (c • x) = c • A2toAInf x := fun c x => map_smul A2toAInfCLM c x
    rw [hsmul, ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 _),
      ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 _), map_smul]

theorem hbL2_linear_spec (μ : LinfStarBall) (φ : A2 unitDisc) :
    A2toAInf (hbL2_linear μ φ) = hbL2_ambient μ φ :=
  ctb_A2toAInf_toA2 (hbL2_ambient_mem μ.2 φ)

/-- A bounded operator with the actual Bers derivative, not an abstract transported quotient. -/
def hbL2_bersOperator (μ : LinfStarBall) : A2 unitDisc →L[ℂ] A2 unitDisc :=
  (hbL2_linear μ).mkContinuous 48 (fun φ => by
    apply ctb_norm_le_of_normA2 (by positivity)
    rw [hbL2_linear_spec]
    exact hbL2_ambient_bound μ.2 φ)

theorem hbL2_bersOperator_spec (μ : LinfStarBall) (φ : A2 unitDisc) :
    A2toAInf (hbL2_bersOperator μ φ) = D0BersR μ (Lambda (A2toAInf φ)) :=
  hbL2_linear_spec μ φ

theorem hbL2_bersOperator_bound (μ : LinfStarBall) (φ : A2 unitDisc) :
    ‖hbL2_bersOperator μ φ‖ ≤ 48 * ‖φ‖ := by
  apply ctb_norm_le_of_normA2 (by positivity)
  rw [hbL2_bersOperator_spec]
  exact hbL2_ambient_bound μ.2 φ

theorem hbL2_bersOperator_opNorm (μ : LinfStarBall) : ‖hbL2_bersOperator μ‖ ≤ 48 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (hbL2_bersOperator_bound μ)

/-- Bijectivity is an explicit remaining analytic hypothesis. -/
def hbL2_equivOfBijective (μ : LinfStarBall) (h : Function.Bijective (hbL2_bersOperator μ)) :
    A2 unitDisc ≃L[ℂ] A2 unitDisc :=
  ContinuousLinearEquiv.ofBijective (hbL2_bersOperator μ)
    (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2)

theorem hbL2_toLinf_norm {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    normL2 unitDiscExterior (toLinf ν) = normL2 unitDiscExterior ν := by
  unfold normL2
  congr 1
  apply lintegral_congr_ae
  filter_upwards [bc_toLinf_ae (d2_harmonicL2_memLp hν)] with z hz
  rw [hz]

theorem hbL2_harmonic_continuous {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ContinuousOn ν unitDiscExterior := by
  obtain ⟨φ, hφ, hrep, -⟩ := hν
  have hw : Continuous (fun z : ℂ => (rho z : ℂ)⁻¹) := by
    simp only [← Complex.ofReal_inv, rho, inv_div]
    fun_prop
  have hh := hw.continuousOn.mul (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)
  exact hh.congr (fun z hz => hrep z hz)

theorem hbL2_toLinf_injective {ν₁ ν₂ : ℂ → ℂ}
    (h₁ : ν₁ ∈ harmonicL2 unitDiscExterior) (h₂ : ν₂ ∈ harmonicL2 unitDiscExterior)
    (he : toLinf ν₁ = toLinf ν₂) : EqOn ν₁ ν₂ unitDiscExterior := by
  have hcoe := bc_toLinf_ae (d2_harmonicL2_memLp h₁)
  rw [he] at hcoe
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    (hcoe.symm.trans (bc_toLinf_ae (d2_harmonicL2_memLp h₂))) resolvent_exterior_isOpen
    (hbL2_harmonic_continuous h₁) (hbL2_harmonic_continuous h₂)

/-- Every harmonic L2 representative has an A2 coordinate, with the exact factor two. -/
theorem hbL2_harmonic_coordinate {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ φ : A2 unitDisc, Lambda (A2toAInf φ) = toLinf ν ∧
      2 * (‖φ‖₊ : ℝ≥0∞) = normL2 unitDiscExterior ν := by
  have hA := D0bers_harmonicL2.1 ν hν
  let φ := toA2 unitDisc (AInf.toFun (fderiv ℂ bersPhi 0 (toLinf ν)))
  have he : A2toAInf φ = fderiv ℂ bersPhi 0 (toLinf ν) := ctb_A2toAInf_toA2 hA
  have hνh := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  have hΛ : Lambda (A2toAInf φ) = toLinf ν := by
    rw [he, QCV.qcv_lambda_inverse_D0bers.2.2 _ hνh]
  refine ⟨φ, hΛ, ?_⟩
  have hn := l29b_Lambda_L2 φ
  rw [hΛ, hbL2_toLinf_norm hν] at hn
  exact hn.symm

/-- Conversely every A2 coordinate has a genuine harmonic L2 representative. -/
theorem hbL2_coordinate_representative (φ : A2 unitDisc) :
    ∃ ν ∈ harmonicL2 unitDiscExterior, toLinf ν = Lambda (A2toAInf φ) ∧
      normL2 unitDiscExterior ν = 2 * (‖φ‖₊ : ℝ≥0∞) := by
  have hA : AInf.toFun (A2toAInf φ) ∈ A2fun unitDisc := by
    refine ⟨(A2toAInf φ).property, ?_⟩
    rw [← l29b_nnnorm_eq]
    exact ENNReal.coe_lt_top
  obtain ⟨ν, hν, hval⟩ := D0bers_harmonicL2.2 _ hA
  have he : fderiv ℂ bersPhi 0 (toLinf ν) = A2toAInf φ :=
    AInf.ext_of_toFun_eqOn (fun z hz => (mem_ball_zero_iff.mp hz).ne) hval
  have hΛ : toLinf ν = Lambda (A2toAInf φ) := by
    rw [← he]
    exact (QCV.qcv_lambda_inverse_D0bers.2.2 _
      (harmonicL2_subset_harmonic.choose_spec ν hν).1).symm
  refine ⟨ν, hν, hΛ, ?_⟩
  rw [← hbL2_toLinf_norm hν, hΛ, l29b_Lambda_L2]

/-- At the origin the Hilbert operator is the identity, using the actual right action. -/
theorem hbL2_bersOperator_zero : hbL2_bersOperator ⟨0, mem_ball_self one_pos⟩ =
    ContinuousLinearMap.id ℂ (A2 unitDisc) := by
  have hR : (fun l : LinfStar => beltramiMul l 0) =ᶠ[𝓝 0] id := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos : (0 : LinfStar) ∈ LinfStarBall)] with l hl
    exact grp_mul_zero hl
  have hD : D0BersR 0 = fderiv ℂ bersPhi 0 := by
    rw [hb_D0BersR_chain (mem_ball_self one_pos), hR.fderiv_eq]
    simp
  apply ContinuousLinearMap.ext
  intro φ
  apply A2toAInf_injective
  rw [hbL2_bersOperator_spec, hD, QCV.qcv_D0_Lambda]
  rfl

/-- Reduction of harmonic injectivity to the concrete A2 operator. -/
theorem hbL2_injective_of_operator (μ : LinfStarBall)
    (hinj : Function.Injective (hbL2_bersOperator μ))
    {ν₁ ν₂ : ℂ → ℂ} (h₁ : ν₁ ∈ harmonicL2 unitDiscExterior)
    (h₂ : ν₂ ∈ harmonicL2 unitDiscExterior)
    (he : D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂)) : EqOn ν₁ ν₂ unitDiscExterior := by
  obtain ⟨φ₁, hφ₁, -⟩ := hbL2_harmonic_coordinate h₁
  obtain ⟨φ₂, hφ₂, -⟩ := hbL2_harmonic_coordinate h₂
  have hφ : φ₁ = φ₂ := by
    apply hinj
    apply A2toAInf_injective
    rwa [hbL2_bersOperator_spec, hbL2_bersOperator_spec, hφ₁, hφ₂]
  apply hbL2_toLinf_injective h₁ h₂
  rw [← hφ₁, ← hφ₂, hφ]

/-- Surjectivity onto the A2 domain, with no unproved reproducing identity hidden. -/
theorem hbL2_surjective_of_operator (μ : LinfStarBall)
    (hsurj : Function.Surjective (hbL2_bersOperator μ))
    {q : ℂ → ℂ} (hq : q ∈ A2fun unitDisc) :
    ∃ ν ∈ harmonicL2 unitDiscExterior,
      EqOn (AInf.toFun (D0BersR μ (toLinf ν))) q unitDisc := by
  obtain ⟨φ, hφ⟩ := hsurj (toA2 unitDisc q)
  obtain ⟨ν, hν, hνφ, -⟩ := hbL2_coordinate_representative φ
  refine ⟨ν, hν, ?_⟩
  intro z hz
  rw [hνφ, ← hbL2_bersOperator_spec, hφ, (A2toAInf_bounded.2 _).2 z hz]
  exact toA2_spec isOpen_ball (fun w hw => (mem_ball_zero_iff.mp hw).ne) hq hz

theorem hbL2_distT_eq_of_surjective (μ : LinfStarBall)
    (hsurj : Function.Surjective (hbL2_bersOperator μ)) :
    {φ | ∃ ψ ∈ distT μ, EqOn ψ φ unitDisc} =
      {φ | ∃ ψ ∈ A2fun unitDisc, EqOn ψ φ unitDisc} := by
  apply Subset.antisymm (hbL2_distT_saturation_subset μ.2)
  rintro φ ⟨ψ, hψ, he⟩
  obtain ⟨ν, hν, hv⟩ := hbL2_surjective_of_operator μ hsurj hψ
  exact ⟨_, ⟨ν, hν, rfl⟩, hv.trans he⟩

theorem hbL2_toA2_norm {q : ℂ → ℂ} (hq : q ∈ A2fun unitDisc) :
    (‖toA2 unitDisc q‖₊ : ℝ≥0∞) = normA2 unitDisc q := by
  rw [← A2.norm_toFun]
  exact normA2_congr measurableSet_ball
    (toA2_spec isOpen_ball (fun z hz => (mem_ball_zero_iff.mp hz).ne) hq)

/-- Quantitative surjectivity follows from actual operator bijectivity and the
bounded inverse theorem; bijectivity remains an explicit hypothesis. -/
theorem hbL2_quantitative_surjective (μ : LinfStarBall)
    (hbij : Function.Bijective (hbL2_bersOperator μ)) :
    ∃ C' : ℝ, ∀ q ∈ A2fun unitDisc, ∃ ν ∈ harmonicL2 unitDiscExterior,
      EqOn (AInf.toFun (D0BersR μ (toLinf ν))) q unitDisc ∧
      normL2 unitDiscExterior ν ≤ ENNReal.ofReal C' * normA2 unitDisc q := by
  let e := hbL2_equivOfBijective μ hbij
  let C : ℝ := ‖(e.symm : A2 unitDisc →L[ℂ] A2 unitDisc)‖
  refine ⟨2 * C, ?_⟩
  intro q hq
  let φ := toA2 unitDisc q
  obtain ⟨ν, hν, hνe, hνnorm⟩ := hbL2_coordinate_representative (e.symm φ)
  have he : hbL2_bersOperator μ (e.symm φ) = φ := e.apply_symm_apply φ
  refine ⟨ν, hν, ?_, ?_⟩
  · intro z hz
    rw [hνe, ← hbL2_bersOperator_spec, he, (A2toAInf_bounded.2 _).2 z hz]
    exact toA2_spec isOpen_ball (fun w hw => (mem_ball_zero_iff.mp hw).ne) hq hz
  · rw [hνnorm]
    have hn : ‖e.symm φ‖ ≤ C * ‖φ‖ := (e.symm : A2 unitDisc →L[ℂ] A2 unitDisc).le_opNorm φ
    have heN : (‖e.symm φ‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞) := by
      have hh := ENNReal.ofReal_le_ofReal hn
      have hC : 0 ≤ C := norm_nonneg (e.symm : A2 unitDisc →L[ℂ] A2 unitDisc)
      rw [ENNReal.ofReal_mul hC] at hh
      simpa only [ofReal_norm, enorm_eq_nnnorm] using hh
    calc 2 * (‖e.symm φ‖₊ : ℝ≥0∞) ≤ 2 * (ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞)) := by gcongr
      _ = ENNReal.ofReal (2 * C) * normA2 unitDisc q := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hbL2_toA2_norm hq]
        norm_num
        ring

/-- Exact Theorem 2.3 reduction. This theorem does not assert the missing bijectivity. -/
theorem hbL2_thm_2_3_of_bijective (μ : LinfStarBall)
    (hbij : Function.Bijective (hbL2_bersOperator μ)) :
    ∃ C C' : ℝ,
      (∀ ν ∈ harmonicL2 unitDiscExterior, AInf.toFun (D0BersR μ (toLinf ν)) ∈ A2fun unitDisc ∧
        normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν) ∧
      (∀ ν₁ ∈ harmonicL2 unitDiscExterior, ∀ ν₂ ∈ harmonicL2 unitDiscExterior,
        D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂) → EqOn ν₁ ν₂ unitDiscExterior) ∧
      ∀ q ∈ A2fun unitDisc, ∃ ν ∈ harmonicL2 unitDiscExterior,
        (∀ z ∈ unitDisc, AInf.toFun (D0BersR μ (toLinf ν)) z = q z) ∧
        normL2 unitDiscExterior ν ≤ ENNReal.ofReal C' * normA2 unitDisc q := by
  obtain ⟨C', hC'⟩ := hbL2_quantitative_surjective μ hbij
  exact ⟨24, C', (fun ν hν => hbL2_forward μ.2 hν),
    (fun ν₁ h₁ ν₂ h₂ he => hbL2_injective_of_operator μ hbij.1 h₁ h₂ he), hC'⟩

/-- Identification with the derivative of the actual Hilbert Bers chart at
its center. The groupO premise comes from the proved A2 chart differentiability. -/
theorem hbL2_chart_fderiv_zero (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    fderiv ℂ (fun φ : A2 unitDisc =>
      toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ))) 0 =
      hbL2_bersOperator μ := by
  let G : A2 unitDisc → A2 unitDisc := fun φ =>
    toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ))
  let J : A2 unitDisc →L[ℂ] LinfStar :=
    ((Submodule.subtypeL harmonicBeltrami).comp LambdaEquiv.toContinuousLinearMap).comp A2toAInfCLM
  have hJ : ∀ φ, J φ = Lambda (A2toAInf φ) := fun _ => rfl
  have h0 : (0 : A2 unitDisc) ∈ ball 0 (Real.sqrt (π / 3)) := mem_ball_self (by positivity)
  obtain ⟨hmem, hdiff⟩ := ctb_thm_2_13_b12 μ hμ
  have hG : DifferentiableAt ℂ G 0 := hdiff.differentiableAt (isOpen_ball.mem_nhds h0)
  have hdirect : HasFDerivAt
      (fun φ => bersPhi (beltramiMul (J φ) (μ : LinfStar)) - bersPhi μ)
      (hbL2_ambient μ) 0 := by
    have hb : HasFDerivAt (fun l => bersPhi (beltramiMul l (μ : LinfStar))) (D0BersR μ) (J 0) := by
      simpa using hb_D0BersR_hasFDerivAt μ.2
    exact (hb.comp 0 J.hasFDerivAt).sub_const _
  have hev : (fun φ => bersPhi (beltramiMul (J φ) (μ : LinfStar)) - bersPhi μ) =ᶠ[𝓝 0]
      (A2toAInfCLM ∘ G) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with φ hφ
    change _ = A2toAInf (toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ)))
    rw [ctb_A2toAInf_toA2 (hmem φ hφ), ctb_bers_chartInv μ (ct_A2toAInf_norm_lt hφ), hJ]
  have hcomp : A2toAInfCLM.comp (fderiv ℂ G 0) = hbL2_ambient μ :=
    (A2toAInfCLM.hasFDerivAt.comp 0 hG.hasFDerivAt).unique (hdirect.congr_of_eventuallyEq hev.symm)
  apply ContinuousLinearMap.ext
  intro φ
  apply A2toAInf_injective
  have hh := congrArg (fun L : A2 unitDisc →L[ℂ] AInf unitDisc => L φ) hcomp
  exact hh.trans (hbL2_bersOperator_spec μ φ).symm

end TakhtajanTeo

#print axioms TakhtajanTeo.hbL2_forward
#print axioms TakhtajanTeo.hbL2_distT_saturation_subset
#print axioms TakhtajanTeo.hbL2_bersOperator_spec
#print axioms TakhtajanTeo.hbL2_bersOperator_opNorm
#print axioms TakhtajanTeo.hbL2_equivOfBijective
#print axioms TakhtajanTeo.hbL2_harmonic_coordinate
#print axioms TakhtajanTeo.hbL2_coordinate_representative
#print axioms TakhtajanTeo.hbL2_bersOperator_zero
#print axioms TakhtajanTeo.hbL2_injective_of_operator
#print axioms TakhtajanTeo.hbL2_distT_eq_of_surjective
#print axioms TakhtajanTeo.hbL2_thm_2_3_of_bijective
#print axioms TakhtajanTeo.hbL2_chart_fderiv_zero
