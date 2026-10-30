import TakhtajanTeo.Ch1.HilbertBersDifferentialL2
import TakhtajanTeo.Ch1.QCVariationSurjSmall
import TakhtajanTeo.Ch1.HilbertBersKernel

/-! Actual injectivity on the Ahlfors–Weill coordinate region. The condition
on the base coordinate is explicit; general-base kernel separation is not
asserted here. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV

/-- The actual A-infinity chart has a differentiable left inverse near zero
when the base Bers coordinate is in the Ahlfors–Weill ball. -/
theorem hbInj_small_leftInverse {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : ‖bersPhi μ‖ < 2) :
    ∃ J : AInf unitDisc → AInf unitDisc,
      DifferentiableAt ℂ J (bersPhi μ) ∧
      ∀ᶠ φ in 𝓝 (0 : AInf unitDisc),
        J (bersPhi (beltramiMul (Lambda φ) μ)) = φ := by
  obtain ⟨-, -, hμi, -, -⟩ := bc_wA_mul hμ hμ
  let H : AInf unitDisc → AInf unitDisc :=
    fun φ => bersPhi (beltramiMul (Lambda φ) μ)
  let J : AInf unitDisc → AInf unitDisc :=
    fun ψ => bersPhi (beltramiMul (Lambda ψ) (beltramiInv μ))
  have hΛ0 : Lambda 0 = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  have hH0 : H 0 = bersPhi μ := by simp only [H, hΛ0, hb_zero_mul hμ]
  have hHd : DifferentiableAt ℂ H 0 := by
    have hd := (hb_D0BersR_hasFDerivAt hμ).differentiableAt
    have hd' : DifferentiableAt ℂ (fun l => bersPhi (beltramiMul l μ)) (Lambda 0) := by
      rw [hΛ0]; exact hd
    exact hd'.comp 0 (Lambda_differentiable 0)
  have hAW0 := qs_AW hs
  have hJd : DifferentiableAt ℂ J (bersPhi μ) := by
    have hm : DifferentiableAt ℂ (fun l => beltramiMul l (beltramiInv μ))
        (Lambda (bersPhi μ)) :=
      ((bd_differentiableOn hμi) _ hAW0.1).differentiableAt
        (isOpen_ball.mem_nhds hAW0.1)
    have hb : DifferentiableAt ℂ bersPhi
        (beltramiMul (Lambda (bersPhi μ)) (beltramiInv μ)) :=
      (qcv_bersPhi_differentiableOn _ (bg_mul_mem_ball hμi hAW0.1)).differentiableAt
        (isOpen_ball.mem_nhds (bg_mul_mem_ball hμi hAW0.1))
    exact DifferentiableAt.comp (g := bersPhi)
      (f := fun ψ => beltramiMul (Lambda ψ) (beltramiInv μ))
      (bersPhi μ) hb (hm.comp (bersPhi μ) (Lambda_differentiable (bersPhi μ)))
  refine ⟨J, hJd, ?_⟩
  have h1 : ∀ᶠ φ in 𝓝 (0 : AInf unitDisc), φ ∈ ball 0 2 :=
    isOpen_ball.mem_nhds (mem_ball_self (by norm_num))
  have h2 : ∀ᶠ φ in 𝓝 (0 : AInf unitDisc), H φ ∈ ball 0 2 :=
    hHd.continuousAt.eventually (isOpen_ball.mem_nhds (by
      rw [hH0]; exact mem_ball_zero_iff.mpr hs))
  filter_upwards [h1, h2] with φ hφ hh
  obtain ⟨hΛφ, hbφ⟩ := qs_AW (mem_ball_zero_iff.mp hφ)
  obtain ⟨hΛH, hbH⟩ := qs_AW (mem_ball_zero_iff.mp hh)
  have hm := bg_mul_mem_ball hμ hΛφ
  have he : bersPhi (Lambda (H φ)) = bersPhi (beltramiMul (Lambda φ) μ) := hbH
  exact (qs_bersPhi_mul_congr hΛH hm hμi he).trans
    ((qs_bersPhi_mul_inv hΛφ hμ).trans hbφ)

/-- Genuine kernel separation on harmonic coordinates in the small Bers region. -/
theorem hbInj_ambient_small {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : ‖bersPhi μ‖ < 2) :
    Function.Injective (fun φ : AInf unitDisc => D0BersR μ (Lambda φ)) := by
  obtain ⟨J, hJd, hleft⟩ := hbInj_small_leftInverse hμ hs
  have hΛ0 : Lambda 0 = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  let L : AInf unitDisc →L[ℂ] AInf unitDisc :=
    (D0BersR μ).comp (fderiv ℂ Lambda 0)
  have hHd : HasFDerivAt (fun φ => bersPhi (beltramiMul (Lambda φ) μ)) L 0 := by
    have hd : HasFDerivAt (fun l => bersPhi (beltramiMul l μ)) (D0BersR μ) (Lambda 0) := by
      rw [hΛ0]; exact hb_D0BersR_hasFDerivAt hμ
    exact hd.comp 0 (Lambda_differentiable 0).hasFDerivAt
  have hbase : bersPhi (beltramiMul (Lambda 0) μ) = bersPhi μ := by
    rw [hΛ0, hb_zero_mul hμ]
  have hJ : HasFDerivAt J (fderiv ℂ J (bersPhi μ))
      (bersPhi (beltramiMul (Lambda 0) μ)) := by
    rw [hbase]; exact hJd.hasFDerivAt
  have hc := hJ.comp 0 hHd
  have hid : HasFDerivAt
      (fun φ => J (bersPhi (beltramiMul (Lambda φ) μ)))
      (ContinuousLinearMap.id ℂ (AInf unitDisc)) 0 :=
    (hasFDerivAt_id _).congr_of_eventuallyEq hleft
  have he := hc.unique hid
  have hΛ : ∀ φ : AInf unitDisc, (fderiv ℂ Lambda 0) φ = Lambda φ := by
    intro φ
    exact congrArg (fun F : AInf unitDisc →L[ℂ] LinfStar => F φ)
      (((Submodule.subtypeL harmonicBeltrami).comp
        LambdaEquiv.toContinuousLinearMap).hasFDerivAt.fderiv)
  intro φ ψ h
  have hL : L φ = L ψ := by simpa only [L, ContinuousLinearMap.comp_apply, hΛ] using h
  have heq := congrArg (fderiv ℂ J (bersPhi μ)) hL
  change ((fderiv ℂ J (bersPhi μ)).comp L) φ =
    ((fderiv ℂ J (bersPhi μ)).comp L) ψ at heq
  simpa only [he, ContinuousLinearMap.id_apply] using heq

/-- The actual Hilbert Bers operator is injective in the small Bers region. -/
theorem hbInj_hilbert_small (μ : LinfStarBall) (hs : ‖bersPhi μ‖ < 2) :
    Function.Injective (hbL2_bersOperator μ) := by
  intro φ ψ h
  apply A2toAInf_injective
  apply hbInj_ambient_small μ.2 hs
  have he := congrArg A2toAInf h
  simpa only [hbL2_bersOperator_spec] using he

/-- On this explicit region the full actual kernel, not merely its harmonic
restriction, is the original trivial Beltrami subspace. -/
theorem hbInj_kernel_small {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : ‖bersPhi μ‖ < 2) (a : LinfStar) :
    D0BersR μ a = 0 ↔ a ∈ trivialBeltrami := by
  have hΛ0 : Lambda 0 = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  rw [← QCV.qcv_ker_D0Phi, LinearMap.mem_ker]
  constructor
  · intro ha
    change (fderiv ℂ bersPhi 0) a = 0
    apply hbInj_ambient_small hμ hs
    change D0BersR μ (Lambda ((fderiv ℂ bersPhi 0) a)) = D0BersR μ (Lambda 0)
    rw [← hp_eq_Lambda, hbPre_derivative_projection hμ, ha, hΛ0, map_zero]
  · intro ha
    change (fderiv ℂ bersPhi 0) a = 0 at ha
    rw [← hbPre_derivative_projection hμ, hp_eq_Lambda, ha, hΛ0, map_zero]

/-- The harmonic L2 representatives are separated pointwise on the exterior. -/
theorem hbInj_harmonicL2_small (μ : LinfStarBall) (hs : ‖bersPhi μ‖ < 2)
    {ν₁ ν₂ : ℂ → ℂ} (h₁ : ν₁ ∈ harmonicL2 unitDiscExterior)
    (h₂ : ν₂ ∈ harmonicL2 unitDiscExterior)
    (he : D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂)) :
    EqOn ν₁ ν₂ unitDiscExterior :=
  hbL2_injective_of_operator μ (hbInj_hilbert_small μ hs) h₁ h₂ he

#print axioms hbInj_small_leftInverse
#print axioms hbInj_ambient_small
#print axioms hbInj_hilbert_small
#print axioms hbInj_kernel_small
#print axioms hbInj_harmonicL2_small
end TakhtajanTeo
