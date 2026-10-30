# Model A / Model B refactor — leader spec (2026-10-25)

Implementer: 下属2 (owner of S1_1/S1_2). The leader authorizes exactly the statement/definition changes below. Any
other change needs the leader. The leader audits the diff before integration.

## Why

- **Model A (下属2, defect #2).** `IsNormalizedA` demands a homeomorphism of `ℂ` onto `ℂ` (so `w(∞) = ∞`) that also
  fixes `-1, -i, 1`. By reflection symmetry, `w(0) = refl(w(∞))`, so such a `w` fixes `0, 1, ∞` and equals the plane
  solution `W`. Then `W(-1) = -1` and `W(-i) = -i` are forced, which fails in general.
  - Result: `wA` falls back to `id` for most `μ`, and `T(1)` collapses.
  - TT's `w_μ` is a map of the sphere. `w_μ(∞) = refl(w_μ(0))` is in general a finite point of `𝔻*`.
- **Model B (下属2, defect #1; user-approved fix).** The normalization `f''(0) = 0` can force a pole in `𝔻` (poleTest).
  The new normalization is `w(∞) = ∞`, `f(0) = 0`, `f'(0) = 1`.
  - With it, the welding of `w_μ|S¹` has `α = id`.
  - `f^μ` is then TT Chapter 2's `𝖿^μ` and `g_μ = f^μ ∘ w_μ⁻¹` on `𝔻*`, so `weldConst = 0`.
  - For harmonic `μ` nothing changes: TT's Lemma 1.5 says the old `f^μ` already fixes `∞`.

## S1_1 changes

1. Move `finPart` (and its docstring) above Model A.
2. Model A becomes a sphere map, mirroring Model B:
   ```lean
   def IsNormalizedA (μ : LinfStar) (w : ExtPlane → ExtPlane) : Prop :=
     ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ W : ℂ → ℂ, IsNormalizedSolution W (extA μ) ∧
       (∀ z : ℂ, w z = M (W z)) ∧ w extInf = M extInf ∧
       w ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧ w ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
       w ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)
   /-- `w_μ` as a map of `ℂ̄` (junk `id` if none). -/
   def wAS (μ : LinfStar) : ExtPlane → ExtPlane := if h : ∃ w, IsNormalizedA μ w then h.choose else id
   /-- `w_μ` at finite points (junk `0` at its pole, a point of `𝔻*` when `w_μ(∞) ≠ ∞`). -/
   def wA (μ : LinfStar) (z : ℂ) : ℂ := finPart (wAS μ z)
   ```
   Then:
   - `wA_bijective` is replaced by `wAS_bijective`.
   - `wA_spec : IsNormalizedA μ (wAS μ)` for `μ ∈ ball`. It is now provable: take `W` from
     `extA_normalized_plane_exists`, and `M` the Möbius map sending `W(-1), W(-i), W(1)` to `-1, -i, 1`.
   - `wA_unique` takes `w : ExtPlane → ExtPlane`. Its proof: plane uniqueness, then two Möbius maps agreeing at three
     points are equal.
   - Write a `[CORRECTION 2026-10-25]` docstring giving the reason above.
3. Model B:
   - In `IsNormalizedB`, replace the conjunct `deriv (deriv f) 0 = 0` by `w extInf = extInf`.
   - Update the docstring, with a `[CORRECTION 2026-10-25]` note on poleTest and user approval.
   - Re-prove `IsNormalizedB.unique` (now `M` is affine, `M = (z ↦ z / W'(0))`), `wB_unique` and `wB_spec`. Existence
     is now provable: `W` is holomorphic and injective on `𝔻`, so `W'(0) ≠ 0`.
   - `fB_normalization`: the third conjunct becomes `wB μ extInf = extInf`. Keep the conjunct order:
     Appendix A uses `hn.1` and `hn.2.1`.
   - Delete the f''-jet helpers (`mobius_eq_id_of_normalized_jet`, `normalized_mobius_comp_*`) if unused, or keep
     them.
4. Every other S1_1 statement keeps its text. Re-prove proofs broken by the type change.

## S1_2 changes

5. `IsWelding h α f g`:
   - replace `IsDiscMobius α ∧ α ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)` by `α = id`;
   - drop `deriv (deriv f) 0 = 0`.

   Docstring: with this normalization, TT's `α` is the identity. `conformal_welding` keeps existence. Its uniqueness
   part becomes:
   ```lean
   ∀ f₁ f₂ g₁ g₂, IsWelding h id f₁ g₁ → IsWelding h id f₂ g₂ → EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior
   ```
6. `gammaMu μ z := alphaMu μ (wAS μ z)`. Its type `ℂ → ExtPlane` is unchanged; this avoids the `finPart` junk value.
   Fix the `alphaMu_bijective` proof (`α = id`).
7. `eq_1_9_classD` (the left map of (1.9)) is restated as follows (keep the `ClassD` definition):
   ```lean
   (∀ p : T1, fB (Quotient.out p : LinfStarBall) ∈ ClassDtilde) ∧
     (∀ p q : T1, EqOn (fB (Quotient.out p : LinfStarBall)) (fB (Quotient.out q : LinfStarBall)) unitDisc → p = q) ∧
     ∀ h, IsNormalizedQS h → ∀ f g, IsWeldingPrime h f g → ∃ p : T1, EqOn (fB (Quotient.out p : LinfStarBall)) f unitDisc
   ```
   - `IsWeldingPrime` is defined later in the file. Move it, and `IsUnivalentAtInfty`, above this statement if needed.
   - Docstring: TT's bijection `T(1) ≅ 𝒟` fails (poleTest); `T(1)` embeds in `𝒟̃`, with image the welding functions of
     normalized `h`.
8. `eq_1_10` is restated with sphere maps:
   ```lean
   ∀ z : ℂ, wB μ (Function.invFun (wAS μ) (Function.invFun (alphaMu μ) (gammaMu μ z))) = wB μ (z : ExtPlane)
   ```
   Its proof is as before, using `wAS_bijective` and `alphaMu_bijective`.
9. `fiber_welding`: the last conjunct becomes
   ```lean
   c = -(1 / 2) * (deriv (deriv fun z => lambdaW c (fB μ z)) 0 - deriv (deriv (fB μ)) 0) /
         deriv (fun z => lambdaW c (fB μ z)) 0
   ```
   This holds because `(λ_c ∘ F)''(0) = F''(0) - 2c` when `F(0) = 0` and `F'(0) = 1`.
10. `lemma_1_5`, `lemma_1_5_fB_infty`, `remark_1_6`, `welding_of_wA`: the text is unchanged (they stay true). Add a
    docstring line where the meaning changed: `α_μ = id`, and `w^μ(∞) = ∞` for every `μ`.

## Outside S1_1/S1_2

- S4 `gWP_origin` proof (line ~683, uses `IsNormalizedA 0 id`) belongs to 下属1's file.
  - 下属2 may make the minimal proof fix there, using `id : ExtPlane → ExtPlane`.
  - Tell 下属1 before editing, and do not change anything else in S4.
- The leader edits the downstream statements:
  - Ch2 `bers_curve_factorization`: `½𝒜(f)(0) = ½ f^μ''(0) + 1/g_μ(w)`;
  - docstrings of `weldConst`/`fsans`/`gsans`.
- 下属5 re-points the QCVariation premises (`hA : IsNormalizedA μ (wAS μ)`).

## Delivery

- Compile S1_1, then S1_2, then direct consumers that break (S1_3, S2 if needed), each with `lake env lean -o …`.
- Send the leader:
  - the list of changed declarations;
  - every proved helper that had to be re-proved or deleted;
  - `#print axioms` for re-proved originals.
- The leader then runs `lake build`.


## AMENDMENT 1 (2026-10-25, after 下属2's DEFECT #3) — supersedes the Model B parts above

**What was wrong.** Normalizing Model B by `w(∞) = ∞` makes `fB μ` depend on the representative `μ`, not only on its
class `[μ]`.
- `w_μ(∞)` is a finite point in general, so the welding `g = W ∘ w_μ⁻¹` does not fix `∞`.
- 下属2's example: `w^ν|𝔻 = z/(1 + cz)`.

**The correct Model B normalization** is the welding normalization of TT Chapter 2:
`w^μ ∘ w_μ⁻¹` fixes `∞`, i.e. `w^μ` sends the pole `p_μ = w_μ⁻¹(∞) ∈ 𝔻* ∪ {∞}` to `∞`; plus `f(0) = 0`, `f'(0) = 1`.

Properties:
- It always exists, with `f` holomorphic on `𝔻`, because `p_μ ∉ 𝔻̄`.
- It depends only on `w_μ|S¹`: `f^μ` is the welding function of `h = w_μ|S¹` with `g(∞) = ∞`.
- For harmonic `μ`, `p_μ = ∞` (TT Lemma 1.5), and it agrees with TT.
- Under it, `α_μ = id`, `weldConst = 0`, `fsans = fB`, `gsans = gMu`, and TT's zero section `([μ], w^μ(∞))` is in
  general a finite point, as in TT.

Concretely, in `IsNormalizedB` the new conjunct is
```lean
w (Function.invFun (wAS μ) extInf) = extInf
```
replacing `deriv (deriv f) 0 = 0`, instead of `w extInf = extInf`.
- Existence: `M` is the Möbius map with `M(W(p)) = ∞`, `M(0) = 0` and `(M ∘ W)'(0) = 1`.
- Uniqueness: plane uniqueness, plus three Möbius conditions.
- `fB_normalization`, third conjunct: `wB μ (Function.invFun (wAS μ) extInf) = extInf`.

Consequences:
- `modelA_iff_modelB` keeps its original text: both directions are true again (welding uniqueness).
- Do not delete `bersPhi_eq_iff_fB_eq` unless it is false under this normalization. Under it, both sides determine
  the class, so it should be true.
- `eq_1_9_classD` stays as specified above.
- `wA_mapsTo` is restated through the sphere map, since `wA` has a junk value at the pole:
  ```lean
  wAS μ '' toExt unitDisc = toExt unitDisc ∧
    wAS μ '' (toExt unitDiscExterior ∪ {extInf}) = toExt unitDiscExterior ∪ {extInf} ∧
    wAS μ '' toExt unitCircle = toExt unitCircle
  ```
