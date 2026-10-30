# Architecture — Lean skeleton of Takhtajan–Teo, *Weil–Petersson metric on the universal Teichmüller space*

Source: L. A. Takhtajan, L.-P. Teo, Mem. AMS 183 (2006), no. 861.
- Main text (OCR): `D:\lean\Weil–Petersson metric on the universal Teichmüller space\source\TakhtajanTeo2006.md`, cited below as `TT:<line>`.
- References: `…\refs\` (see `MANIFEST.md` there).

## Decisions (user, 2026-10-24)

1. **Dependency.** The project depends on the Li Zhong project (`D:\lean\lizhong_quasiconformal_teichmuller`, library `LiZhongQC`; also `References`).
   - Quasiconformal maps, the Beltrami equation, Schwarzian derivatives, the Poincaré density, Möbius maps and the measurable Riemann mapping theorem are **reused**, not restated.
   - `packagesDir` points at the Li Zhong project's package checkouts, and `lake-manifest.json` is written by hand (copied from Li Zhong plus the path dependency), so lake never fetches anything.
   - Lean `v4.35.0-rc2`, Mathlib `2f3d8f6` (same as Li Zhong).
2. **Model.** The memoir's own unit-disk model is used: Beltrami differentials on `𝔻* = {|z| > 1}`, reflection `z ↦ 1/z̄`, `w_μ` fixing `-1, -i, 1`. A bridge to Li Zhong's half-plane model (`LiZhongQC.UniversalTeichmuller`) is a later theorem (Cayley transform), used to transport proved results.
3. **Location.** The project lives in this ASCII directory. The references stay in the original folder.
4. **Author.** The leader writes the skeleton alone, chapter by chapter, and reports after each part.

## Goal of the skeleton (statement level)

As for Li Zhong:
- Every definition of the memoir is a genuine Lean definition.
- Every theorem, lemma, corollary, proposition and numbered formula that asserts something is stated, with `sorry` proofs.
- Numbered formulas that only *define* something become definitions. The equation tag goes in the docstring.
- Remarks are stated when they assert a mathematical fact; otherwise they are recorded in the module docstring.
- Each declaration's docstring cites the memoir item and `TT:<line>`.

## Modelling conventions

- **Function spaces are Lean types with their norms**, so that differentiability (`DifferentiableAt ℂ`) and inner products make sense:
  - `L∞(𝔻*) = MeasureTheory.Lp ℂ ∞ (volume.restrict 𝔻*)` (Banach).
  - `L²` spaces likewise (Hilbert, `MeasureTheory.L2`).
  - `A∞(𝔻)`, `A₂(𝔻)`, `Ω^{-1,1}(𝔻*)`, `H^{-1,1}(𝔻*)` are `Submodule`s of these, so they inherit norms and inner products.
- **Junk values of `Lp` coercions.** The function `⇑μ` of `μ : Lp ℂ ∞ (volume.restrict 𝔻*)` is only determined a.e. on `𝔻*`; off `𝔻*` it is arbitrary. Every use outside `𝔻*` goes through an explicit extension (`extA`: by reflection to `𝔻`; `extB`: by `0`).
- **Choice-defined solutions.** As in Li Zhong (`normalizedSolution`):
  - A solution is written `if h : ∃ w, P w then h.choose else id`, where `P` is the defining predicate.
  - A `…_spec` theorem shows that `P` holds.
  - Uniqueness is a separate theorem.
- **Manifold structures without `ChartedSpace` instances.**
  - `T(1)` is a quotient type with the quotient topology.
  - Its complex Banach structure is expressed through the Bers embedding `β : T(1) → A∞(𝔻)` and the Bers charts `h_μ`, as explicit maps.
  - "Holomorphic on `T(1)`" means holomorphic in Bers coordinates.
  - Tangent spaces are the explicit spaces the memoir identifies them with (`T₀T(1) ≅ Ω^{-1,1}(𝔻*)`).
  - The Hilbert manifold structure of §2 is handled the same way, with charts into `A₂(𝔻)`.
  - **Why:** an instance would need proofs inside a definition, which could only be `sorry` at statement level.
- **Curvature (§7), Chern forms (§5).** Defined by the memoir's coordinate formulas in Bers coordinates (holomorphic normal coordinates at the origin, then right translation). Not via a general theory of infinite-dimensional Kähler manifolds, which Mathlib lacks.
- **Helpers.** Shared definitions live in `TakhtajanTeo/Basic.lean`. Everything is in `namespace TakhtajanTeo`.

## File layout (one file per section; Chapter 1 §1 split by subsection)

```
TakhtajanTeo/Basic.lean                       disks, reflection, L∞(𝔻*), ρ, A∞, A₁, Ω^{-1,1}, N
TakhtajanTeo/Ch1/S1_1_TeichmullerTheory.lean  §1.1   T(1), group law, Bers embedding, charts, Teichmüller curve
TakhtajanTeo/Ch1/S1_2_Homogeneous.lean        §1.2   Homeo_qs(S¹), 𝒟, welding, Lemma 1.5, TV1–2, TS1–4
TakhtajanTeo/Ch1/S1_3_Fuchsian.lean           §1.3   T(Γ), WP metric of T(Γ), Lemma 1.9
TakhtajanTeo/Ch1/S1_4_Resolvent.lean          §1.4   Δ₀, G, (1.19), RK1–4, (1.20)
TakhtajanTeo/Ch1/S1_5_Variational.lean        §1.5   F, Φ, (1.21)–(1.26), Lemmas 1.12–1.13, Cor. 1.15
TakhtajanTeo/Ch1/S2_HilbertManifold.lean      §2
TakhtajanTeo/Ch1/S3_TopologicalGroup.lean     §3
…                                             §4–§8, Chapter 2 §1–§5, Appendices A–B
```

## Rules

- No `sorry` inside a definition.
- No `axiom`.
- Docstrings in English.
- Statements are checked against the memoir's displayed formulas, not against paraphrases. Corrections of misprints are marked `[CORRECTION]` with the recomputation.

## Status

**2026-10-24.** Chapter 1 (§1–§8) skeleton complete.
- Files: `Basic`, `S1_1` … `S1_5`, `S2` … `S8`.
- Size: 182 statements (all `sorry`) and 212 `def`/`abbrev` (plus instances).
- Checks:
  - `lake build` green (9094 jobs);
  - no `sorry` inside any definition;
  - `#print axioms` of every definition shows no `sorryAx`.

Readings and corrections recorded in module docstrings:
- the zero section of `𝒯(1)` is `([μ], w^μ(∞))`;
- Lemma 2.7 is stated with `≤`;
- TV1/TV2 are stated in their derived form;
- the pull-back factor is `(w̄)_{z̄}` (OCR misreading);
- Cor. 6.4 is stated on `Ω^{-1,1}(𝕌)`;
- the kernel `B` (7.8) is stated on `𝔻`.

Modelling in §5: holomorphic coordinates `(β, 1/z)` on `𝒯(1)`; `Θ` is the polarized Levi form; VK is defined at the
origin through TS2/TV2 and transported by right translation; `κ_n` is the fiber integral at the origin (the constant
of Theorem 5.10 is checked).

**2026-10-24.** Chapter 2 (§1–§5) and Appendices A–B skeleton complete. The whole memoir is now stated.
- Files: `Ch2/S1` … `S5` (namespace `TakhtajanTeo.Ch2`) and `Appendix/A`, `Appendix/B` (namespaces `AppA`, `AppB`).
- Size, whole project: 274 statements (all `sorry`) and 292 `def`/`abbrev`.
- Checks:
  - `lake build` green (9101 jobs);
  - `#print axioms` of all 292 definitions shows no `sorryAx`;
  - a scan for the binder-precedence trap (`∑ x, a + b` parses as `(∑ x, a) + b`) is clean.

Modelling in Chapter 2:
- Operators on `ℓ²` are matrices; identities are stated entrywise and inverses through two-sided relations.
- Operator norms are valued in `ℝ≥0∞`, so an unbounded matrix has norm `∞`, not a junk `0`.
- `Det_F` is the product over a chosen singular value sequence of `B₁`.
- Bers-coordinate derivatives are the Wirtinger `dz`/`dzbar` of `ε ↦ F([εμ * ν])`.
- The `𝔻`-model of §3.2 is reached by conjugating with `ι(z) = 1/z`.
- Points of `𝒯(1)` in Appendix A are `([μ], 𝗀_μ(w))`, with welding `(λ_c ∘ f^μ, λ_c ∘ g_μ ∘ σ_w⁻¹)`.

Readings and corrections in Chapter 2:
- the Lemma 3.6 kernel misprint `g(w) - g(w)` is corrected;
- in Lemma 2.7 the `u`-integral is absolutely convergent, so it is stated without a principal value;
- `\varliminf` in Corollary A.6 and Lemma B.7 is an OCR rendering of `lim`.

Not stated (each listed in its module docstring):
- (3.1) and Corollary 3.12/(3.3): general Fredholm determinant facts and zeta-regularized determinants;
- Remark 5.6;
- the abstract `Sp(𝓗)/U ≃ 𝔇_∞`.

Next: proof phase, at the user's direction.

## Proof-phase update (2026-10-24)

The user replaced the earlier leader/subordinate organization with six peer chats. File ownership and current work are recorded in `collaboration/README.md` and the individual `lean1.md`–`lean6.md` files. Work uses incremental compilation of modified/directly affected modules, not a whole-project rebuild.

The user explicitly approved the C-infinity order correction described in `collaboration/lean1/C_INFINITY_ORDER_PROPOSAL.md`. In this Mathlib version the index of `ContDiff` is `ℕ∞ω`: bare `⊤` means the analytic order `ω`, while `(⊤ : ℕ∞)` coerces to the genuinely smooth order `∞`. The correction covers `IsCircleDiffeo`, `BCinf`, `IsTensor`, `remark_4_4`, and `laplace_factorization`. Genuine analytic formulas for the density/kernel may keep their stronger order. Scope-specific compiler and axiom results are recorded by each owner.

Theorem 7.14's raw-function independence issue and the exterior-Psi inclusion issue are separate, pending mathematical/statement decisions. The C-infinity approval must not be interpreted as approval for those changes.
