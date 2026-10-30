import TakhtajanTeo.Ch2.S3SchwarzianVariation

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
namespace Ch2
open LiZhongQC

/-- **Theorem 3.1** (TT:4596–4662). `S₂ : T₀(1) → ℝ` is differentiable at every `[ν] ∈ T₀(1)`, and in the Bers
coordinates `ε_μ` of the chart `V_ν`:
`∂S₂/∂ε_μ([ν]) = -(1/6π) ∬_{𝔻*} 𝒮(𝗀_ν)(z) μ(z) d²z`. -/
theorem thm_3_1 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    BersDiffAt liouvilleS2 ν μ ∧
      bersDz liouvilleS2 ν μ = -(1 / (6 * π)) * ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z := s3sv_thm_3_1 hp hμ

/-- **Corollary 3.2** (TT:4668). `∂S₂ = -(1/6π) ϑ` on `T₀(1)`. -/
theorem cor_3_2 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS2 (Quotient.out p : LinfStarBall) μ = -(1 / (6 * π)) * varthetaPair p μ := s3sv_cor_3_2 hp hμ

end Ch2
end TakhtajanTeo
