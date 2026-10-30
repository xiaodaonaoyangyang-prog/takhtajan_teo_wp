import TakhtajanTeo.Ch2.S1_T112Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- **Theorem 1.12** (TT:3738–3746). Let `w_μ = 𝗀_μ⁻¹ ∘ 𝖿^μ` be the conformal welding (1.15) of `[μ] ∈ T(1)`. Then
`[μ] ∈ T₀(1)` iff any one of the following holds:
- (i) `𝒮(𝖿^μ) ∈ A₂(𝔻)`;
- (ii) `𝒜(𝖿^μ) ∈ A₂¹(𝔻)`;
- (iii) `𝒮(𝗀_μ) ∈ A₂(𝔻*)`;
- (iv) `𝒜(𝗀_μ) ∈ A₂¹(𝔻*)`. -/
theorem thm_1_12 (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (p ∈ T01 ↔ schwarzianHol (fsans μ) ∈ A2fun unitDisc) ∧
      (p ∈ T01 ↔ preSchwarzian (fsans μ) ∈ A21fun unitDisc) ∧
      (p ∈ T01 ↔ schwarzianHol (gsans μ) ∈ A2fun unitDiscExterior) ∧
      (p ∈ T01 ↔ preSchwarzian (gsans μ) ∈ A21fun unitDiscExterior) := by
  exact ab112_thm_1_12 p

end TakhtajanTeo.Ch2
