import TakhtajanTeo.Ch1.HilbertBersAllBase
import TakhtajanTeo.Ch1.HilbertBersIsomorphism

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Theorem 2.3** (TT:1460–1466, proof to TT:1590). For every `[μ] ∈ T(1)` the linear map
`D₀(β ∘ R_[μ]) : H^{-1,1}(𝔻*) → A₂(𝔻)` is a topological isomorphism:
- it maps into `A₂(𝔻)` with `‖D₀(β ∘ R_[μ])(ν)‖₂ ≤ C ‖ν‖₂`;
- it is injective (elements equal on `𝔻*`);
- every `φ ∈ A₂(𝔻)` is attained by some `ν` with `‖ν‖₂ ≤ C' ‖φ‖₂`.

In particular `𝔇_T([μ]) = 𝔇_A(β([μ])) = A₂(𝔻)` (TT:1458). -/
theorem thm_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ C C' : ℝ,
      (∀ ν ∈ harmonicL2 unitDiscExterior, AInf.toFun (D0BersR μ (toLinf ν)) ∈ A2fun unitDisc ∧
        normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν) ∧
      (∀ ν₁ ∈ harmonicL2 unitDiscExterior, ∀ ν₂ ∈ harmonicL2 unitDiscExterior,
        D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂) → EqOn ν₁ ν₂ unitDiscExterior) ∧
      ∀ φ ∈ A2fun unitDisc, ∃ ν ∈ harmonicL2 unitDiscExterior,
        (∀ z ∈ unitDisc, AInf.toFun (D0BersR μ (toLinf ν)) z = φ z) ∧
        normL2 unitDiscExterior ν ≤ ENNReal.ofReal C' * normA2 unitDisc φ := by
  exact hbAll_thm_2_3 hμ

/-- (TT:1458) The distributions agree: `𝔇_T([μ]) = A₂(𝔻)` in Bers coordinates. -/
theorem distT_eq_A2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    {φ | ∃ ψ ∈ distT μ, EqOn ψ φ unitDisc} = {φ | ∃ ψ ∈ A2fun unitDisc, EqOn ψ φ unitDisc} := by
  exact hbSurj_distT_eq ⟨μ, hμ⟩

/-- **Theorem 2.13** (TT:1874–1894). The Bers embedding `β : T(1) → β(T(1)) ⊂ A∞(𝔻)` is biholomorphic for the Hilbert
manifold structures. For every `μ ∈ 𝒪(𝔻*)₁`:
- `β ∘ h̃_μ⁻¹` maps the ball of radius `√(π/3)` of `A₂(𝔻)` into `(β ∘ Φ)(μ) + A₂(𝔻)`;
- the map `φ ↦ β(h̃_μ⁻¹(φ)) - (β ∘ Φ)(μ)`, as a map of that ball into `A₂(𝔻)`, is holomorphic, with invertible
  differential everywhere;
- `β(T(1))` is open in the Hilbert manifold `A∞(𝔻)`. -/
theorem thm_2_13 :
    (∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
      (∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ) ∈ A2fun unitDisc) ∧
      DifferentiableOn ℂ
        (fun φ => toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ)))
        (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)), Function.Bijective
        (fderiv ℂ (fun ψ => toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf ψ)) - bersPhi μ))) φ)) ∧
      @IsOpen _ hilbertTopologyA (range bers) := by
  exact hbSurj_thm_2_13

/-- **Corollary 3.2** (TT:1924–1927). `T₀(1) = {[μ] ∈ T(1) : β([μ]) ∈ A₂(𝔻)}`. -/
theorem cor_3_2 : T01 = {p | AInf.toFun (bers p) ∈ A2fun unitDisc} := by
  exact hbSurj_cor_3_2

end TakhtajanTeo
