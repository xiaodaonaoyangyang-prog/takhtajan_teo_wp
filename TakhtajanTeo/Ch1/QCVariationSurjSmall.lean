import TakhtajanTeo.Ch1.BersInjective
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.QCVariationTransport
import TakhtajanTeo.Ch1.S4_Metrics

/-!
# Surjectivity of `D_μ(β ∘ Φ)` for `‖β[μ]‖ < 2`

Uses Ahlfors–Weill (`ahlfors_weill`), injectivity of `bers`, the group law on the sphere level
(`bc_wA_mul`) and the differentiability of the right translations.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

theorem qs_bersPhi_zero : bersPhi 0 = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  obtain ⟨hf, hi⟩ := fB_holomorphic_injective h0
  apply AInf.ext_toFun_disc
  intro z hz
  have h1 := (schwarzianHol_AInf_spec hf hi).1 z hz
  have hz0 : AInf.toFun (0 : AInf unitDisc) z = 0 := by simp [AInf.toFun, unweight, hz]
  rw [hz0]
  change AInf.toFun (toAInf unitDisc (schwarzianHol (fB 0))) z = 0
  rw [h1, qcv_schwarzian_fB_eq h0 hz]
  have hW := qcv_W_zero (0 : LinfStar)
  simp only [zero_smul] at hW
  rw [hW]
  simp [schwarzianHol]

/-- Equal Bers coordinates give equal classes. -/
theorem qs_class_of_bersPhi_eq {l₁ l₂ : LinfStar} (h₁ : l₁ ∈ LinfStarBall) (h₂ : l₂ ∈ LinfStarBall)
    (h : bersPhi l₁ = bersPhi l₂) :
    Phi ⟨l₁, h₁⟩ = Phi ⟨l₂, h₂⟩ := by
  apply bers_injective
  rw [bers_Phi, bers_Phi]
  exact h

/-- Right translation respects the Bers coordinate (it is a function of the class). -/
theorem qs_bersPhi_mul_congr {l₁ l₂ μ : LinfStar} (h₁ : l₁ ∈ LinfStarBall) (h₂ : l₂ ∈ LinfStarBall)
    (hμ : μ ∈ LinfStarBall) (h : bersPhi l₁ = bersPhi l₂) :
    bersPhi (beltramiMul l₁ μ) = bersPhi (beltramiMul l₂ μ) := by
  have hc : Phi ⟨l₁, h₁⟩ = Phi ⟨l₂, h₂⟩ := qs_class_of_bersPhi_eq h₁ h₂ h
  have hcl : teichSetoid.r (⟨l₁, h₁⟩ : LinfStarBall) ⟨l₂, h₂⟩ := Quotient.exact hc
  have hm : teichSetoid.r (⟨μ, hμ⟩ : LinfStarBall) ⟨μ, hμ⟩ := fun _ _ => rfl
  have hmul := bc_beltramiMul_respects hcl hm
  have hP : Phi ⟨beltramiMul l₁ μ, bg_mul_mem_ball hμ h₁⟩ =
      Phi ⟨beltramiMul l₂ μ, bg_mul_mem_ball hμ h₂⟩ := Quotient.sound hmul
  have := congrArg bers hP
  rw [bers_Phi, bers_Phi] at this
  exact this

/-- `(l * μ) * μ⁻¹` has the same class as `l`. -/
theorem qs_bersPhi_mul_inv {l μ : LinfStar} (hl : l ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall) :
    bersPhi (beltramiMul (beltramiMul l μ) (beltramiInv μ)) = bersPhi l := by
  obtain ⟨hlm, hS1, hi, hi1, hi2⟩ := bc_wA_mul hμ hl
  obtain ⟨hlmi, hS2, -⟩ := bc_wA_mul hi hlm
  have hS : wAS (beltramiMul (beltramiMul l μ) (beltramiInv μ)) = wAS l := by
    rw [hS2, hS1]
    funext p
    simp only [Function.comp_apply]
    have := congrFun hi1 p
    simp only [Function.comp_apply, id_eq] at this
    rw [this]
  have hP : Phi ⟨beltramiMul (beltramiMul l μ) (beltramiInv μ), hlmi⟩ = Phi ⟨l, hl⟩ := by
    apply Quotient.sound
    intro z _
    simp only [wA, hS]
  have := congrArg bers hP
  rw [bers_Phi, bers_Phi] at this
  exact this

theorem qs_bersPhi_inv_mul {l μ : LinfStar} (hl : l ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall) :
    bersPhi (beltramiMul (beltramiMul l (beltramiInv μ)) μ) = bersPhi l := by
  obtain ⟨-, -, hi, hi1, hi2⟩ := bc_wA_mul hμ hl
  obtain ⟨hlm, hS1, -⟩ := bc_wA_mul hi hl
  obtain ⟨hlmi, hS2, -⟩ := bc_wA_mul hμ hlm
  have hS : wAS (beltramiMul (beltramiMul l (beltramiInv μ)) μ) = wAS l := by
    rw [hS2, hS1]
    funext p
    simp only [Function.comp_apply]
    have := congrFun hi2 p
    simp only [Function.comp_apply, id_eq] at this
    rw [this]
  have hP : Phi ⟨beltramiMul (beltramiMul l (beltramiInv μ)) μ, hlmi⟩ = Phi ⟨l, hl⟩ := by
    apply Quotient.sound
    intro z _
    simp only [wA, hS]
  have := congrArg bers hP
  rw [bers_Phi, bers_Phi] at this
  exact this

/-- `μ * μ⁻¹` has Bers coordinate `0`. -/
theorem qs_bersPhi_self_inv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    bersPhi (beltramiMul μ (beltramiInv μ)) = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  obtain ⟨-, -, hi, hi1, -⟩ := bc_wA_mul hμ hμ
  obtain ⟨hm, hS, -⟩ := bc_wA_mul hi hμ
  have hw : wA (beltramiMul μ (beltramiInv μ)) = id := by
    funext z
    unfold wA
    rw [hS]
    have := congrFun hi1 (z : ExtPlane)
    simp only [Function.comp_apply, id_eq] at this
    show finPart (wAS μ (wAS (beltramiInv μ) (z : ExtPlane))) = z
    rw [this]
    simp [finPart]
  have hP : Phi ⟨beltramiMul μ (beltramiInv μ), hm⟩ = Phi ⟨0, h0⟩ := by
    apply Quotient.sound
    intro z _
    show wA (beltramiMul μ (beltramiInv μ)) z = wA 0 z
    rw [hw, wp_wA_zero]
  have := congrArg bers hP
  rw [bers_Phi, bers_Phi] at this
  exact this.trans qs_bersPhi_zero

/-- Ahlfors–Weill in the form used here. -/
theorem qs_AW {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    Lambda φ ∈ LinfStarBall ∧ bersPhi (Lambda φ) = φ := by
  obtain ⟨h, hb⟩ := ahlfors_weill hφ
  exact ⟨h, by rw [← bers_Phi ⟨Lambda φ, h⟩]; exact hb⟩

/-- The derivative of `bersPhi` at `μ` is onto when `‖β[μ]‖ < 2`. -/
theorem qcv_bersPhi_deriv_surjective_small {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hs : ‖bersPhi μ‖ < 2) :
    LinearMap.range (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) = ⊤ := by
  obtain ⟨-, -, hμi, -, -⟩ := bc_wA_mul hμ hμ
  obtain ⟨H, hH⟩ : ∃ H : AInf unitDisc → AInf unitDisc,
      ∀ φ, H φ = bersPhi (beltramiMul (Lambda φ) μ) := ⟨_, fun _ => rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : AInf unitDisc → AInf unitDisc,
      ∀ ψ, H' ψ = bersPhi (beltramiMul (Lambda ψ) (beltramiInv μ)) := ⟨_, fun _ => rfl⟩
  have hΛ0 : Lambda 0 = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  have hHfun : H = fun φ => bersPhi (beltramiMul (Lambda φ) μ) := funext hH
  have hH'fun : H' = fun ψ => bersPhi (beltramiMul (Lambda ψ) (beltramiInv μ)) := funext hH'
  -- the derivative of `H` at `0`
  have hHd : HasFDerivAt H (((fderiv ℂ bersPhi μ).comp (qcv_rightDerivative μ)).comp
      (fderiv ℂ Lambda 0)) 0 := by
    have h1 : HasFDerivAt (fun l => bersPhi (beltramiMul l μ))
        ((fderiv ℂ bersPhi μ).comp (qcv_rightDerivative μ)) (Lambda 0) := by
      rw [hΛ0]; exact qcv_bers_rightTranslation_hasFDerivAt hμ
    rw [hHfun]
    exact h1.comp 0 (Lambda_differentiable 0).hasFDerivAt
  -- `H'` is differentiable at `φ0 = β[μ]`
  have hAW0 := qs_AW hs
  have hH'd : DifferentiableAt ℂ H' (bersPhi μ) := by
    have hmul : DifferentiableAt ℂ (fun l => beltramiMul l (beltramiInv μ)) (Lambda (bersPhi μ)) :=
      ((bd_differentiableOn hμi) (Lambda (bersPhi μ)) hAW0.1).differentiableAt
        (isOpen_ball.mem_nhds hAW0.1)
    have hb : DifferentiableAt ℂ bersPhi (beltramiMul (Lambda (bersPhi μ)) (beltramiInv μ)) :=
      (qcv_bersPhi_differentiableOn _ (bg_mul_mem_ball hμi hAW0.1)).differentiableAt
        (isOpen_ball.mem_nhds (bg_mul_mem_ball hμi hAW0.1))
    rw [hH'fun]
    exact DifferentiableAt.comp (g := bersPhi) (f := fun ψ => beltramiMul (Lambda ψ) (beltramiInv μ))
      (bersPhi μ) hb (hmul.comp (bersPhi μ) (Lambda_differentiable (bersPhi μ)))
  -- `H' φ0 = 0`
  have hH'0 : H' (bersPhi μ) = 0 := by
    rw [hH']
    exact (qs_bersPhi_mul_congr hAW0.1 hμ hμi hAW0.2).trans (qs_bersPhi_self_inv hμ)
  -- `H ∘ H' = id` near `φ0`
  have hcont : ContinuousAt H' (bersPhi μ) := hH'd.continuousAt
  have h1 : ∀ᶠ ψ in 𝓝 (bersPhi μ), ψ ∈ ball (0 : AInf unitDisc) 2 :=
    isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hs)
  have h2 : ∀ᶠ ψ in 𝓝 (bersPhi μ), H' ψ ∈ ball (0 : AInf unitDisc) 2 :=
    hcont.eventually (isOpen_ball.mem_nhds (by rw [hH'0]; exact mem_ball_self (by norm_num)))
  have hHH : ∀ᶠ ψ in 𝓝 (bersPhi μ), H (H' ψ) = ψ := by
    filter_upwards [h1, h2] with ψ ha hb
    have hψ : ‖ψ‖ < 2 := mem_ball_zero_iff.mp ha
    have hm : ‖H' ψ‖ < 2 := mem_ball_zero_iff.mp hb
    obtain ⟨hΛψ, hbψ⟩ := qs_AW hψ
    obtain ⟨hΛm, hbm⟩ := qs_AW hm
    have hl2 : beltramiMul (Lambda ψ) (beltramiInv μ) ∈ LinfStarBall := bg_mul_mem_ball hμi hΛψ
    have hsame : bersPhi (Lambda (H' ψ)) = bersPhi (beltramiMul (Lambda ψ) (beltramiInv μ)) := by
      rw [hbm, hH']
    have h3 := qs_bersPhi_mul_congr hΛm hl2 hμ hsame
    have h4 := qs_bersPhi_inv_mul hΛψ hμ
    rw [hH, h3, h4, hbψ]
  -- chain rule at `φ0`
  have hHd' : HasFDerivAt H (((fderiv ℂ bersPhi μ).comp (qcv_rightDerivative μ)).comp
      (fderiv ℂ Lambda 0)) (H' (bersPhi μ)) := by rw [hH'0]; exact hHd
  have hcomp := hHd'.comp (bersPhi μ) hH'd.hasFDerivAt
  have hid : HasFDerivAt (H ∘ H') (ContinuousLinearMap.id ℂ (AInf unitDisc)) (bersPhi μ) :=
    (hasFDerivAt_id (bersPhi μ)).congr_of_eventuallyEq (hHH.mono fun ψ h => h)
  have huniq := hcomp.unique hid
  rw [LinearMap.range_eq_top]
  intro χ
  have hχ : ((((fderiv ℂ bersPhi μ).comp (qcv_rightDerivative μ)).comp (fderiv ℂ Lambda 0)).comp
      (fderiv ℂ H' (bersPhi μ))) χ = χ := by rw [huniq]; rfl
  exact ⟨qcv_rightDerivative μ ((fderiv ℂ Lambda 0) ((fderiv ℂ H' (bersPhi μ)) χ)), hχ⟩

end QCV
end TakhtajanTeo
