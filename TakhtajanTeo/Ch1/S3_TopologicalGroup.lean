import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.WeightedBergman
import TakhtajanTeo.Ch1.HalfPlaneBergman
import TakhtajanTeo.Ch1.NormalizedWelding

/-!
# Chapter 1, §3 — `T₀(1)` as a topological group (TT:1900–2120)

* Theorem 3.1 (`β(T(1)) ∩ A₂(𝔻)` is connected), Corollary 3.2 (`T₀(1) = β⁻¹(A₂(𝔻))`)
* Lemma 3.3 (representatives in `L² ∩ 𝒪(𝔻*)₁`), Lemma 3.4 (`T₀(1)` is a subgroup)
* Lemma 3.5 (left translations are continuous on `T₀(1)`), Corollary 3.6, Lemma 3.7
* Theorem 3.8 (`T₀(1)` is a topological group), Proposition 3.9 (`𝒯₀(1)` is a topological group)

**Modelling.**
- The group operations of `T(1)` are computed on representatives (`Quotient.out`).
- All topologies are the Hilbert manifold topologies of §2: `hilbertTopology` on `T(1)`, `hilbertTopologyA` on
  `A∞(𝔻)`.
- `𝒯(1) ⊂ T(1) × ℂ̄` carries the subspace topology of `hilbertTopology × ℂ̄`. This matches the parametrization
  `T(1) × 𝔻* ≅ 𝒯(1)` of TT:571.
- "Topological group" is stated in the memoir's own form (TT:2070): `(x, y) ↦ x * y⁻¹` is continuous on
  `T₀(1) × T₀(1)`, and `T₀(1)` is closed under the group operations.
- The intermediate claims inside the proofs are not stated: the density of `β(Möb(S¹)\Diff₊(S¹))`, the continuity of
  the Fréchet inclusion, and the continuity of `(σ, [μ]) ↦ [(σ⁻¹)^*μ]`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The product `[μ] * [ν] = [μ * ν]` on `T(1)` (TT:458), computed on representatives (junk `[μ]` if `μ * ν` leaves the
ball, which does not happen). -/
def mulT (p q : T1) : T1 :=
  if h : beltramiMul (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) ∈ LinfStarBall then Phi ⟨_, h⟩
  else p

/-- The inverse `[μ]⁻¹ = [μ⁻¹]` on `T(1)`, computed on a representative. -/
def invT (p : T1) : T1 :=
  if h : beltramiInv (Quotient.out p : LinfStarBall) ∈ LinfStarBall then Phi ⟨_, h⟩ else p

/-- The origin `0 = [0]` of `T(1)`. -/
def originT : T1 := Phi ⟨0, mem_ball_self one_pos⟩

-- `thm_3_1` moved to `Ch1/Thm31Completed.lean` (2026-10-26).

-- Original cor_3_2 moved unchanged to Ch1/HilbertManifoldCompleted.lean (2026-10-27).

-- Original lemma_3_3 moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

-- Original L2_inter_groupO_subgroup moved unchanged to Ch1/GroupChainCompleted.lean (2026-10-26).

-- `lemma_3_4` moved to `Ch1/GroupChain1.lean` (2026-10-26).

-- `lemma_3_5` moved to `Ch1/GroupTranslation.lean` (2026-10-27).

-- `cor_3_6` moved to `Ch1/GroupTranslation.lean` (2026-10-27).

-- `lemma_3_7` moved to `Ch1/GroupTopology.lean` (2026-10-27).

-- `thm_3_8` moved to `Ch1/GroupTopGroup.lean` (2026-10-27).

/-- `𝒯₀(1) = π⁻¹(T₀(1))` (TT:1902). -/
def TCurve0 : Set (T1 × ExtPlane) := TCurve ∩ {q | q.1 ∈ T01}

/-- The group law `𝛾₁ * 𝛾₂⁻¹` of `𝒯(1)` by (1.13)–(1.14) (TT:2102–2112). For `𝛾₁ = ([ν], ζ)` and `𝛾₂ = ([μ], w)`:
- `𝛾₁ * 𝛾₂⁻¹ = ([λ], z)`, with `λ` given by (1.13) and `z` by (1.14);
- the extension is `𝗀 = σ_u ∘ 𝗀_μ`, with `u = g_μ⁻¹(w)`.

Representatives are `Quotient.out` (junk first component `[ν]` if `λ` leaves the ball).

[CORRECTION 2026-10-26, user-approved] `𝗀` is a chosen plane q.c. extension of `σ_u ∘ 𝗀_μ|S¹` (formerly the
pointwise finite formula of the sphere map, which has a pole and is not a homeomorphism of `ℂ`), and the fibre coordinate
`u` is the inverse of the normalized sphere welding (formerly `invFun (gMu μ) (finPart w)`, junk off `g_μ(𝔻*)` and at
`w = ∞`). Found by 下属3; see `collaboration/下属3/PROP39_PROPOSAL.md`. -/
def tcurveMulInv (a b : T1 × ExtPlane) : T1 × ExtPlane :=
  let ν : LinfStar := (Quotient.out a.1 : LinfStarBall)
  let μ : LinfStar := (Quotient.out b.1 : LinfStarBall)
  -- fibre coordinate u = g_μ⁻¹(w) of b.2 = w (TT:800); u = ∞ for w = ∞
  let u : ExtPlane := Function.invFun (normalizedWeldingSphere μ) b.2
  -- a q.c. extension 𝗀 of σ_u ∘ 𝗀_μ|S¹ to ℂ (exists: Beurling–Ahlfors; the result is independent of the choice)
  let G : ℂ → ℂ :=
    if h : ∃ G : ℂ → ℂ, IsQuasiconformal G univ ∧ G '' univ = univ ∧
        EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle
    then h.choose else id
  let lam := tcurveLambda ν G            -- option B (dilatation of 𝗀)
  (if h : lam ∈ LinfStarBall then Phi ⟨lam, h⟩ else a.1, tcurveZ ν G lam a.2)

-- `prop_3_9` moved unchanged to `Ch1/TCurveTopGroupCompleted.lean` (2026-10-28).

end TakhtajanTeo
