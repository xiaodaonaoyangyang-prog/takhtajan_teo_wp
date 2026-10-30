import TakhtajanTeo.Ch1.ChartTranslation
import TakhtajanTeo.Ch1.AhlforsWeillCompleted

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! # Originals of §2 relocated from `S2_HilbertManifold` (2026-10-25)

Proved downstream of `ChartTranslation` and `AhlforsWeillCompleted`. -/

/-- **Corollary 2.12** (TT:1858–1860). Right translations are biholomorphic on the Hilbert manifold `T(1)`. For
`λ, μ ∈ 𝒪(𝔻*)₁`, `R_[μ](V_λ) = V_{λ * μ}` and `h̃_{λ * μ} ∘ R_[μ] ∘ h̃_λ⁻¹` is the identity on `h̃_λ(V_λ)`. -/
theorem cor_2_12 (l μ : LinfStarBall) (hl : (l : LinfStar) ∈ groupO) (hμ : (μ : LinfStar) ∈ groupO) :
    ∃ h : beltramiMul l μ ∈ LinfStarBall,
      rightTrans μ '' hilbertChartDomain l = hilbertChartDomain ⟨_, h⟩ ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        hilbertChart ⟨_, h⟩ (rightTrans μ (bersChartInv l (A2toAInf φ))) = φ :=
  ct_cor_2_12 (fun _ h => ahlfors_weill h) l μ

end TakhtajanTeo
