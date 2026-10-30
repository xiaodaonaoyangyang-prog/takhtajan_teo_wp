import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.GroupChain1

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **Lemma 2.5** (TT:1610–1616). For every `ε > 0` there is `0 < δ < 1` with `Lemma25Prop ε δ`. -/
theorem lemma_2_5 {ε : ℝ} (hε : 0 < ε) : ∃ δ, Lemma25Prop ε δ := by
  exact grp25_lemma_2_5 hε

-- Exact original declarations released after the unconditional Lemma 2.5 proof.

/-- **Corollary 2.6** (TT:1640–1646). Let `μ ∈ Ω^{-1,1}(𝔻*)` with `‖μ‖∞ < δ` (`δ` of Lemma 2.5 for `ε = 1`). For
every `λ ∈ L∞(𝔻*)₁`, `D_λR_μ` extends to an invertible bounded operator on `L²(𝔻*, ρ d²z)`:
`‖D_λR_μ(ν)‖₂ ≤ √2/(1 - ‖μ‖∞)² ‖ν‖₂`, and the same for `D_λR_{μ⁻¹}`. -/
theorem cor_2_6 {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {l : LinfStar} (hl : l ∈ LinfStarBall)
    (ν : LinfStar) :
    normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x μ) l ν) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - ‖μ‖) ^ 2) * normL2 unitDiscExterior ν ∧
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x (beltramiInv μ)) l ν) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - ‖μ‖) ^ 2) * normL2 unitDiscExterior ν := by
  exact grp_cor_2_6 hμ hδ hl ν

/-- **Lemma 2.7** (TT:1676–1682; `≤` for the memoir's `<`, see the module docstring). For every `μ ∈ 𝒪(𝔻*)₁` there
is `C > 0` with `‖R_μ(λ₁) - R_μ(λ₂)‖₂ ≤ C ‖λ₁ - λ₂‖₂` for all `λ₁, λ₂ ∈ L∞(𝔻*)₁` with
`λ₁ - λ₂ ∈ L²(𝔻*, ρ d²z)`. -/
theorem lemma_2_7 {μ : LinfStar} (hμ : μ ∈ groupO) :
    ∃ C > 0, ∀ l₁ ∈ LinfStarBall, ∀ l₂ ∈ LinfStarBall, normL2 unitDiscExterior (l₁ - l₂ : LinfStar) < ∞ →
      normL2 unitDiscExterior (beltramiMul l₁ μ - beltramiMul l₂ μ : LinfStar) ≤
        ENNReal.ofReal C * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  exact grp_lemma_2_7 hμ

/-- **Remark 2.8** (TT:1708–1714). For every `μ ∈ 𝒪(𝔻*)₁` there is `C > 0` (depending only on `‖μ‖∞`) with
`‖D_λR_μ(ν)‖₂ ≤ C ‖ν‖₂` for all `ν` and all `λ ∈ L∞(𝔻*)₁`. -/
theorem remark_2_8 {μ : LinfStar} (hμ : μ ∈ groupO) :
    ∃ C > 0, ∀ l ∈ LinfStarBall, ∀ ν : LinfStar,
      normL2 unitDiscExterior (fderiv ℂ (fun x => beltramiMul x μ) l ν) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν := by
  exact grp_remark_2_8 hμ

/-- (TT:1934) `L²(𝔻*, ρ d²z) ∩ 𝒪(𝔻*)₁` is a subgroup of `L∞(𝔻*)₁`. -/
theorem L2_inter_groupO_subgroup {l ν : LinfStar} (hl : l ∈ groupO) (hν : ν ∈ groupO)
    (hl2 : normL2 unitDiscExterior l < ∞) (hν2 : normL2 unitDiscExterior ν < ∞) :
    beltramiMul l (beltramiInv ν) ∈ groupO ∧ normL2 unitDiscExterior (beltramiMul l (beltramiInv ν)) < ∞ := by
  exact grp_L2_inter_groupO_subgroup hl hν hl2 hν2

/-- **Lemma 3.3** (TT:1932). Every `[μ] ∈ T₀(1)` has a representative `μ ∈ L²(𝔻*, ρ d²z) ∩ 𝒪(𝔻*)₁`. -/
theorem lemma_3_3 {p : T1} (hp : p ∈ T01) :
    ∃ μ : LinfStarBall, normL2 unitDiscExterior μ < ∞ ∧ (μ : LinfStar) ∈ groupO ∧ Phi μ = p := by
  exact glr_lemma_3_3 hp

end TakhtajanTeo
