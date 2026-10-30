import TakhtajanTeo.Ch1.S1_2_Homogeneous

/-!
# The welding pair `(𝖿^μ, 𝗀_μ)` (TT:823)

`weldConst`, `fsans` and `gsans`, moved byte-identical from `Ch1/S2_HilbertManifold.lean` (2026-10-25). They now sit
below the modules that need their holomorphy (`QCVariationWeld`), with no import cycle.

With the welding normalization of Model B (`collaboration/MODEL_AB_SPEC.md`, Amendment 1), `α_μ = id` and the
constant is `0`. So `fsans = fB` and `gsans = gMu`: the pair is TT Chapter 2's `(𝖿^μ, 𝗀_μ)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The welding functions `𝖿 = λ ∘ f^μ`, `𝗀 = λ ∘ g_μ ∘ α_μ⁻¹` of `w_μ = 𝗀⁻¹ ∘ 𝖿` (1.15), for the constant `c` of
`eq_1_15` (chosen; junk `0` if none). -/
def weldConst (μ : LinfStar) : ℂ :=
  if h : ∃ c : ℂ, IsWeldingPrime (wA μ) (fun z => lambdaW c (fB μ z))
      (fun z => lambdaW c (gMu μ (finPart (Function.invFun (alphaMu μ) (z : ExtPlane))))) then h.choose else 0

/-- `𝖿 = λ_μ ∘ f^μ` (TT:823). -/
def fsans (μ : LinfStar) (z : ℂ) : ℂ := lambdaW (weldConst μ) (fB μ z)

/-- `𝗀 = λ_μ ∘ g_μ ∘ α_μ⁻¹` (TT:823). -/
def gsans (μ : LinfStar) (z : ℂ) : ℂ :=
  lambdaW (weldConst μ) (gMu μ (finPart (Function.invFun (alphaMu μ) (z : ExtPlane))))

/-- Poincaré density (curvature `-1`, `λ = 2|φ'|/(1 - |φ|²)`) of a domain `Ω* ⊂ ℂ` that contains a punctured neighbourhood of
`∞` and has `0` outside its closure (`Ω* = 𝗀(𝔻*)`, since `0 = 𝖿(0) ∈ 𝖿(𝔻)`), taken in the sphere chart `w ↦ 1/w`: the domain
`Ω' = (w ↦ 1/w)(Ω*) ∪ {0}` is a bounded simply connected plane domain, and `λ_{Ω*}(z) = λ_{Ω'}(1/z) / |z|²`.
`LiZhongQC.poincareDensity` itself is junk `0` on such `Ω*`: `{|z| > 1}` is a punctured neighbourhood of `∞` and is not
conformally equivalent to `𝔻` (see `collaboration/下属4/D1_PROPOSAL.md`). -/
def poincareDensityNearInfty (Ωs : Set ℂ) (z : ℂ) : ℝ :=
  poincareDensity ((fun w : ℂ => w⁻¹) '' Ωs ∪ {0}) z⁻¹ / ‖z‖ ^ 2

end TakhtajanTeo
