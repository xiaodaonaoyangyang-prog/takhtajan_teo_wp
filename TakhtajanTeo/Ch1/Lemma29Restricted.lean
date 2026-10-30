import TakhtajanTeo.Ch1.Lemma29Plane

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **Restricted Lemma 2.9** (TT:1724–1730), frozen cross-lane stub. For `μ ∈ 𝒪(𝔻*)₁` and `k < 2` there is `C > 0`
with `‖(β ∘ Φ)(Λ(φ) * μ) - (β ∘ Φ)(μ)‖₂ ≤ C ‖φ‖₂` for all `φ ∈ A₂(𝔻)` with `‖φ‖∞ ≤ k`. Here the Beltrami
differential `λ = Λ(φ)` is harmonic, `‖λ‖∞ ≤ k/2 < 1`, and `λ ∈ L²(𝔻*, ρ d²z)` since `φ ∈ A₂(𝔻)`. This is the
special case of `lemma_2_9` that `thm_2_10` and `thm_2_13` use; the constant depends on `μ` and `k` only. -/
theorem l29r_restricted {μ : LinfStar} (hμ : μ ∈ groupO) {k : ℝ} (hk : k < 2) :
    ∃ C > 0, ∀ φ : A2 unitDisc, ‖A2toAInf φ‖ ≤ k →
      normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (Lambda (A2toAInf φ)) μ) - bersPhi μ)) ≤
        ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞) := by
  exact l29b_l29r hμ hk

/-- **Lemma 2.9** (TT:1724–1730), restricted form. For `μ ∈ 𝒪(𝔻*)₁` and `k < 2` there is `C > 0` with
`‖(β ∘ Φ)(Λ(φ) * μ) - (β ∘ Φ)(μ)‖₂ ≤ C ‖φ‖₂` for all `φ ∈ A₂(𝔻)` with `‖φ‖∞ ≤ k`.
- **[CORRECTION 2026-10-28, user-approved]** Restricted to harmonic `λ = Λ(φ)` with the constant depending on `k`:
the uniform form (all `λ ∈ L² ∩ L∞(𝔻*)₁`, `C` independent of `‖λ‖∞`) is doubtful (`λ_k = kχ_B`, `k → 1`) and its book
proof applies Remark 2.8 outside `𝒪`; this is the form used by `thm_2_10` and `thm_2_13`. -/
theorem lemma_2_9 {μ : LinfStar} (hμ : μ ∈ groupO) {k : ℝ} (hk : k < 2) :
    ∃ C > 0, ∀ φ : A2 unitDisc, ‖A2toAInf φ‖ ≤ k →
      normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (Lambda (A2toAInf φ)) μ) - bersPhi μ)) ≤
        ENNReal.ofReal C * (‖φ‖₊ : ℝ≥0∞) :=
  l29r_restricted hμ hk

end TakhtajanTeo
