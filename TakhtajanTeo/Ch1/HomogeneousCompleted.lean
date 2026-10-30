import TakhtajanTeo.Ch1.FiberCircleOrientation
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.GeneralConformalWelding

/-! # Completed statements of Chapter 1, §1.2

These original theorem names live downstream of their constructive welding
proofs, avoiding imports from S1_2 back into its own dependent modules.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- (TT:738–768) The fiber of `𝒯(1) → T(1)` at `[μ]` is `S¹\Möb(S¹) ≅ 𝔻*`. The point `([μ], g_μ(w))`, `w ∈ 𝔻*`,
corresponds to `σ_w ∘ 𝗀_μ ∈ S¹\Homeo_qs(S¹)`, whose welding CW2′ is `f = λ_w ∘ f^μ`,
`g = λ_w ∘ g_μ ∘ σ_w⁻¹`, with `c_w = -1/g_μ(w) = -½ (f''(0) - (f^μ)''(0))/f'(0)`. The latter is computed for the new
`f = λ_w ∘ f^μ`.
- **[CORRECTION 2026-10-25]** With the corrected normalization of `f^μ` (no condition on `(f^μ)''(0)`),
  `(λ_c ∘ F)''(0) = F''(0) - 2c` when `F(0) = 0` and `F'(0) = 1`, so the identity reads as stated.
- **[USER-APPROVED CORRECTION 2026-10-25]** Compose the inverse fiber map, the
  normalized welding and the final Möbius map on the sphere; take finite part
  only after the complete composition. This retains the inverse-pole value. -/
theorem fiber_welding {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    let c := -1 / gMu μ w
    IsOneFixedQS (fun z : ℂ => sigmaW w (finPart (gammaMu μ z))) ∧
      IsWeldingPrime (fun z : ℂ => sigmaW w (finPart (gammaMu μ z))) (fun z => lambdaW c (fB μ z))
        (fun z => finPart (mobiusExt 1 0 c 1
          (normalizedWeldingSphere μ
            (sigmaInvSphere (w : ExtPlane) (z : ExtPlane))))) ∧
      c = -(1 / 2) * (deriv (deriv fun z => lambdaW c (fB μ z)) 0 - deriv (deriv (fB μ)) 0) /
        deriv (fun z => lambdaW c (fB μ z)) 0 := by
  exact fiber_welding_sphere_candidate hμ hw

/-! ### Originals relocated from `S1_2` (2026-10-25) -/

/-- **Conformal welding** (TT:624–634, Beurling–Ahlfors). For every `h ∈ Möb(S¹)\Homeo_qs(S¹)` there are univalent
`f`, `g` satisfying CW1–CW4 (with `α = id`), and they are unique (`f` on `𝔻`, `g` on `𝔻*`).
- **[CORRECTION 2026-10-25]** TT's `α ∈ Möb(S¹)` is the identity for the corrected normalization of `f`. -/
theorem conformal_welding {h : ℂ → ℂ} (hh : IsNormalizedQS h) :
    (∃ α f g, IsWelding h α f g) ∧ ∀ f₁ f₂ g₁ g₂, IsWelding h id f₁ g₁ → IsWelding h id f₂ g₂ →
      EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior :=
  conformal_welding_complete hh

/-- (TT:636) For `[μ] ∈ T(1)`, the welding of `w_μ|S¹` is `(α_μ, f^μ, g_μ)`, and
`g_μ = w^μ ∘ w_μ⁻¹ ∘ α_μ⁻¹` on `𝔻*`.
- **[CORRECTION 2026-10-25]** The inverse of `w_μ` is taken on the sphere (`wAS μ`). `w_μ(∞)` is in general a finite
  point of `𝔻*`, which has no preimage under the finite map `wA μ = finPart ∘ wAS μ`, so the former form
  `Function.invFun (wA μ) (finPart …)` was false there (found by 下属2). Consequence of the sphere-map form of Model A
  (correction 14 in `collaboration/LEADER.md`); compare `eq_1_10`. -/
theorem welding_of_wA {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsWelding (wA μ) (alphaMu μ) (fB μ) (gMu μ) ∧
      ∀ z ∈ unitDiscExterior, (gMu μ z : ExtPlane) =
        wB μ (Function.invFun (wAS μ) (Function.invFun (alphaMu μ) (z : ExtPlane))) := by
  refine ⟨gMu_isWelding hμ, fun z hz => ?_⟩
  have hid : Function.invFun (id : ExtPlane → ExtPlane) (z : ExtPlane) = (z : ExtPlane) :=
    Function.leftInverse_invFun Function.injective_id (z : ExtPlane)
  rw [alphaMu_eq_id, hid]
  exact gMu_sphere_factorization hμ hz

/-- (TT:732) For every `h ∈ S¹\Homeo_qs(S¹)` there are unique univalent `f` on `𝔻` and `g` on `𝔻*` with CW1, CW2′,
CW3′, CW4. -/
theorem conformal_welding_prime {h : ℂ → ℂ} (hh : IsOneFixedQS h) :
    (∃ f g, IsWeldingPrime h f g) ∧
      ∀ f₁ f₂ g₁ g₂, IsWeldingPrime h f₁ g₁ → IsWeldingPrime h f₂ g₂ →
        EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior :=
  conformal_welding_prime_complete hh

/-- **(1.15)** (TT:814–826). `w_μ`, viewed in `S¹\Homeo_qs(S¹)`, has the conformal welding
`w_μ = 𝗀^μ⁻¹ ∘ 𝖿^μ` (CW1, CW2′, CW3′, CW4), with `𝖿^μ = λ_μ ∘ f^μ` and `𝗀^μ = λ_μ ∘ g_μ ∘ α_μ⁻¹`. Here `λ_μ` is the
Möbius map `z ↦ z/(c z + 1)` determined by `𝖿^μ(0) = 0`, `(𝖿^μ)'(0) = 1`, `𝗀^μ(∞) = ∞`.
- Under the welding normalization `g_μ` already fixes `∞`, so `λ_μ = id` (`c = 0`) is TT's content. -/
theorem eq_1_15 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ c : ℂ, IsWeldingPrime (wA μ) (fun z => lambdaW c (fB μ z))
      (fun z => lambdaW c (gMu μ (finPart (Function.invFun (alphaMu μ) (z : ExtPlane))))) := by
  refine ⟨0, ?_⟩
  have hw : IsWelding (wA μ) id (fB μ) (gMu μ) := by
    have h := gMu_isWelding hμ
    rwa [alphaMu_eq_id] at h
  have hid : ∀ z : ℂ, finPart (Function.invFun (id : ExtPlane → ExtPlane) (z : ExtPlane)) = z := by
    intro z
    have h : Function.invFun (id : ExtPlane → ExtPlane) (z : ExtPlane) = (z : ExtPlane) :=
      Function.leftInverse_invFun Function.injective_id (z : ExtPlane)
    rw [h]
    rfl
  have h := weldingPrime_of_welding hw
  simp only [alphaMu_eq_id, hid, lambdaW, zero_mul, zero_add, div_one]
  exact h

end TakhtajanTeo

#print axioms TakhtajanTeo.fiber_welding
