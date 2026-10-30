import TakhtajanTeo.Ch1.QCVariationTransport
import TakhtajanTeo.Ch1.BeltramiGroup

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate BoundedContinuousFunction Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! # Originals of §1.1 relocated from `S1_1` (2026-10-25)

Their proofs live downstream of `S1_1` (`BeltramiCompose`, `QCVariationKernelEquality`, `QCVariationTransport`), so the
statements are restated here unchanged and proved by those results. -/

/-- (TT:351) The kernel of `D₀Φ` is the subspace `𝓝(𝔻*)` of infinitesimally trivial Beltrami differentials. -/
theorem ker_D0Phi : LinearMap.ker (fderiv ℂ bersPhi 0 : LinfStar →ₗ[ℂ] AInf unitDisc) = trivialBeltrami :=
  QCV.qcv_ker_D0Phi

/-- **(1.3)** (TT:367). `L∞(𝔻*) = 𝓝(𝔻*) ⊕ Ω^{-1,1}(𝔻*)`. -/
theorem eq_1_3 : IsCompl trivialBeltrami harmonicBeltrami :=
  QCV.qcv_origin_isCompl

/-- (TT:451) The explicit group law: `λ = ν * μ⁻¹` is
`λ = ((ν - μ)/(1 - μ̄ ν) · (w_μ)_z/\overline{(w_μ)_z}) ∘ w_μ⁻¹` a.e. on `𝔻*`. Here
`(\bar w_μ)_{z̄} = \overline{(w_μ)_z}`. -/
theorem beltramiMul_inv_formula {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      beltramiMul ν (beltramiInv μ) z =
        (fun u => (ν u - μ u) / (1 - conj (μ u) * ν u) * (dz (wA μ) u / conj (dz (wA μ) u)))
          (Function.invFun (wA μ) z) :=
  bc_beltramiMul_inv_formula hμ hν

/-- **(1.5)** (TT:539). `D_μ R_μ⁻¹(ν) = R(ν, μ)`, where `R_μ⁻¹ = R_{μ⁻¹} : λ ↦ λ * μ⁻¹` on `L∞(𝔻*)`. Hence, under
`Ω^{-1,1}(𝔻*) ≅ A∞(𝔻)`, the vector field `∂/∂ε_ν` at `[μ] ∈ U₀` is `P(R(ν, μ))` (TT:533–539). -/
theorem eq_1_5 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    fderiv ℂ (fun l => beltramiMul l (beltramiInv μ)) μ ν = Rnm ν μ :=
  bc_eq_1_5 hμ ν

/-- **Remark 1.3** (TT:557). Right translation of `ν ∈ T₀T(1)`:
`D₀R_[μ](ν) = (1 - |μ|²) (ν ∘ w_μ) (\bar w_μ)_{z̄}/(w_μ)_z` (a.e. on `𝔻*`), with
`(\bar w_μ)_{z̄} = \overline{(w_μ)_z}`. -/
theorem remark_1_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      fderiv ℂ (fun l => beltramiMul l μ) 0 ν z =
        (1 - ‖μ z‖ ^ 2) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) :=
  bc_remark_1_3 hμ ν

/-- (TT:449) The group law is induced by composition: `w_{ν * μ} = w_ν ∘ w_μ`, `w_{μ⁻¹} = w_μ⁻¹`, and `L∞(𝔻*)₁` is
closed under both operations.
- **[CORRECTION 2026-10-25]** The three identities are stated for the sphere maps `wAS`. For the finite maps
  `wA = finPart ∘ wAS` they fail at the pole `p = (wAS μ)⁻¹(∞)`, a finite point of `𝔻*` in general, where `wA μ p` is
  the junk value `0` (found by 下属2). Consequence of the sphere-map form of Model A (correction 14 in
  `collaboration/LEADER.md`). -/
theorem wA_mul {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    beltramiMul ν μ ∈ LinfStarBall ∧ wAS (beltramiMul ν μ) = wAS ν ∘ wAS μ ∧
      beltramiInv μ ∈ LinfStarBall ∧ wAS μ ∘ wAS (beltramiInv μ) = id ∧ wAS (beltramiInv μ) ∘ wAS μ = id :=
  bc_wA_mul hμ hν

/-- (TT:458) The group law projects to `T(1)`: `[λ] * [μ] = [λ * μ]` is well defined. -/
theorem beltramiMul_respects {l₁ l₂ μ₁ μ₂ : LinfStarBall} (hl : teichSetoid l₁ l₂) (hμ : teichSetoid μ₁ μ₂) :
    ∀ z ∈ unitCircle, wA (beltramiMul l₁ μ₁) z = wA (beltramiMul l₂ μ₂) z :=
  bc_beltramiMul_respects hl hμ

end TakhtajanTeo
