import TakhtajanTeo.Ch2.S4PoleRemoval

/-! # The original Chapter 2 §4 variational formula -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- (TT:5320) The variational formula in the proof of Theorem 4.1: for `z ∈ 𝔻*`,
`∂/∂ε̄|_{ε=0} 𝒮(g_ε) ∘ w_{εν} (w_{εν})_z² = (6/π) ∬_{𝔻*} \overline{ν(w)}/(1 - w̄ z)⁴ d²w`. -/
theorem thm_4_1_variation {κ : LinfStar} (hκ : ∃ h : κ ∈ LinfStarBall, Phi ⟨κ, h⟩ ∈ T01) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    dzbar (fun e => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ)) (wA (e • toLinf ν) z) *
        dz (wA (e • toLinf ν)) z ^ 2) 0 =
      6 / π * ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
  exact s4pv_variation hκ.choose hν hz

end Ch2
end TakhtajanTeo
