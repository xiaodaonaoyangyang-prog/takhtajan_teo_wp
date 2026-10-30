# 下属4 — Ch2 S1 + S2 triage (2026-10-25 evening, current files)

Scouting is read-only. "TRUE?" is checked against the book formula/definitions only where stated. Estimates are Lean lines.
GrunskyOperator now has 0 source `sorry` (`faber_exists`, `kerK1_opNorm_le`, `faber_grunsky` are closed by GPT).

## 0. Two STATEMENT DEFECTS found (for the leader / user; nothing edited)

**D1. `poincareDensity` of an exterior image is junk 0.** `LiZhongQC.poincareDensity D z = sSup {2|f'(z)|/(1-|f z|²) | IsConformalOnto f D unitDisc}`.
`unitDiscExterior = {z | 1 < ‖z‖} ⊂ ℂ` does not contain `∞`. So `Ω* = gsans μ '' unitDiscExterior` is `ℂ \ K`, a punctured
domain, and no injective holomorphic `f` maps it onto the unit disc (bounded ⇒ removable at ∞ ⇒ extension is injective and
open ⇒ contradiction). The set is empty, `sSup ∅ = 0`, so `poincareDensity Ω* z = 0` for every `z`.
- Ch2 `eq_2_8` and `remark_2_8` then read `∫_{f(𝔻)} |w-z|⁻⁴ ≤ 0`. The integrand is positive on a nonempty open bounded
  set at positive distance from `z`, so both statements are **FALSE** as formalized.
- Ch1 `S2_HilbertManifold.lean:1986` `eq_2_3` (`1/C ≤ |z-h z|⁴ ρ₁(h z) ρ₂(z)`) uses the same `ρ₂`: the lower bound reads
  `1/C ≤ 0`, so it is **FALSE** as formalized (the owner of S1_1/S1_2 should be told). Ch1 `eq_2_2` only uses `ρ₁` on the
  bounded `Ω`, which is fine.
- The mathematics is right: with the curvature −1 density `λ = 2/(|z|²-1)` on `𝔻*`, `∫_𝔻 |w-z|⁻⁴ = π/(|z|²-1)² = (π/4) λ²`.
  So `remark_2_8` is sharp and `eq_2_8` (4π) is weaker.
- Suggested repair (leader/user decides): take the density in the sphere chart, e.g. `λ_{Ω*}(z) := λ_{Ω'}(1/z)/|z|²` with
  `Ω' = (fun w => w⁻¹) '' Ω* ∪ {0}` (a bounded simply connected domain, `0 ∈ Ω*` side since `f(0) = 0 ∈ Ω`).

**D2. Ch2 `remark_2_3`.** Needs a strict contraction `‖B₁‖ ≤ c < 1` for every `μ ∈ LinfStarBall` (Kühnau–Grunsky `‖B₁‖ ≤ ‖μ‖∞`).
That theorem is not in the project; see the NO-GO table. The statement itself looks TRUE.

## 1. Import-closure facts

- `S2_Grunsky` imports only `S1_UnivalentFunctions`. The proofs of `thm_2_1`, `remark_2_2`, `eq_2_1`, `eq_2_2`,
  `grunsky_unitary`, `kernels_spec`, `eq_2_4`, `lemma_2_5` need `GrunskyOperator` / `FaberGram*` / `BergmanSeries`, which import
  `S2_Grunsky`. This is the cycle that `cor_2_16` hit.
- Request: approval to move these originals (statements and docstrings byte-identical) into a new module
  `Ch2/S2_Completed.lean` placed after `FaberGramCorollary`, like `Ch1/S1_1_Completed.lean`.
  - No theorem in S3/S4/S5/Appendix/Ch1 uses these names. `S3_Variations` imports `S2_Grunsky`, `Appendix/B_PeriodMapping`
    imports `GrunskyOperator`.
  - The definitions `kerK*`, `kerKK*`, `B1..B4`, `detF`, … stay in S2.
- `S1` items need `LiZhongQC` Koebe/Nehari–Kraus results (`koebe_bieberbach` in Ch01/S05…, `thm19_2_nehari` in Ch05/S19_Schwarzian,
  `kraus_nehari_coeff` in Lemmas/KrausNehari). S1 currently imports only `SchottkyDirectD3a`. Request: import of the narrowest
  module that holds `koebe_bieberbach` (to be pinned with `#check` before the leader decides).

## 2. S1 (11 open)

| item | TRUE? | existing support | est. | verdict |
|---|---|---|---|---|
| `remark_1_2` | TRUE as corrected (cubic-decay premise present; unqualified clause 4 was refuted by lean4) | `lemma_1_3`, `a21_mem_AInf1fun`, `lemma_1_5_disc`, `lemma_1_5_exterior_of_cubic_decay`, `PsiOp_inversion_identity`; clause 1 needs `(1-|z|²)|f''/f'| ≤ 6` from `koebe_bieberbach` + Koebe transform; clause 2 `g` at ∞ (`g'' / g' = O(z⁻³)`) | 350 | GO (import) |
| `bers_curve_factorization` | TRUE? (sign of `lambdaW` to confirm) | `schwarzian_eq_Psi_preSchwarzian`, `schwarzianHol_mul_comp_mul`, Möbius invariance (LiZhongQC), `fB_normalization`, Ch1 `bersPhi` defs | 200 | GO |
| `eq_1_3` (Ch2) | TRUE (normalizations check: `conj b · refl(g(refl z)) ≈ z`) | `wB_unique`, `wB_spec`, `fB_normalization`, `gMu_isWelding`, `beltramiMul_inv_formula`/`eq_1_5` (S1_1_Completed) | 400 | GO (medium) |
| `remark_1_14` | TRUE (with `h0`) | `deriv_ne_zero_of_injOn`; mean value of `log‖·‖` on circles (Mathlib `circleAverage`); need gsans univalent at ∞ from welding facts | 350 | GO |
| `remark_1_9` | clause 1 TRUE and elementary (C¹, `u'>0` ⇒ asymptotically symmetric); clause 2 needs smooth ⇒ `T01` | clause 1: direct from `IsSymmetricHomeo`. clause 2: Douady–Earle/`Appendix/SymmetricBoundaryExtension` + `T01` characterization | 120 + ? | clause 1 GO; clause 2 UNSURE (scout) → whole item PARTIAL |
| `lemma_1_11` | TRUE as corrected (Jordan, bounded) | analytic half done (`lemma_1_11_disc_of_boundary_small`, `a21_iff_boundary_decay_of_Psi_A2`); missing `(1-|z|²)𝒜(f) → 0` from `S ∈ A2` | – | NO-GO: wall = `thm_1_6` (ii ⇒ iii, Becker–Pommerenke) |
| `thm_1_6` | TRUE (BP78) | none (needs Becker's extension and the converse) | >2000 | NO-GO |
| `symmetricT_spec` | TRUE? | clause 1 needs `thm_1_6` + the symmetric-extension theorem; clauses 2–3 need `mulT`/`invT` on welding homeos | – | NO-GO (wall `thm_1_6`) |
| `cor_1_8` | TRUE | needs `thm_1_6` and the Ch1 `T01` description | – | NO-GO (blocked by `thm_1_6`) |
| `thm_1_12` | TRUE | `lemma_1_11`, `thm_1_6`, Ch1 Bers/`T01` facts | – | NO-GO (blocked) |
| `liouvilleS1_wellDefined` | TRUE | = `thm_1_12` (A21 = L² norm) + `gMu_exterior_ne_zero` | 60 after `thm_1_12` | BLOCKED |

S1 total GO: ~1400 lines (`remark_1_2`, `bers_curve_factorization`, `eq_1_3`, `remark_1_14`, clause 1 of `remark_1_9`).

## 3. S2 (21 open)

| item | TRUE? | existing support | est. | verdict |
|---|---|---|---|---|
| `thm_2_1` | TRUE (Hummel) | `faber_finite_differential_energy/pairing` (`ℂ\f(𝔻)` energy `= π(Σk|μ|² − Σ(p+1)|c|²)`), `faber_exists`, `IsFaber.unique_pos`, `cor_2_16_gram_exterior`, `FaberGramInversion`; split `ℂ\f(𝔻) = g(𝔻*) ∪ F`, `∫_F ≥ 0`; equality ⇒ `vol F = ∫_F|P₁'|² = 0` since `P₁' = 1` | 700 | GO (needs relocation) |
| `grunsky_unitary` | TRUE | = conjugates of `eq_2_2` clauses via symmetry (`grunsky_spec`): `B1ᵀ=B1`, `B3=B2ᵀ`, `B4ᵀ=B4` | 100 after `eq_2_2` | GO |
| `eq_2_2` | TRUE | clauses 1/4 = `cor_2_16` blocks (HS premise looks removable: rows of `B1` are ℓ² by `grunsky_B1_bound`); cross clauses 2/3 and last (norm) clause new: polarized pairing across `f(𝔻) ⊔ g(𝔻*)` + `B2,B3` bounds from unitarity | 700 | GO (relocation) |
| `eq_2_1` | TRUE | polarized finite-window form of `eq_2_2` | 200 after `eq_2_2` | GO |
| `remark_2_2` | TRUE | clause 3 = `thm_2_1` with `λ = δ₀`; clause 4 = log-energy `π Σ k|a_{p0}|²` from `hexp` at `w = 0`; clauses 1–2 need `IsNormalizedDisjointPair (fsans μ)(gsans μ)` and `vol(w_μ(S¹)) = 0` (qc maps preserve null sets: confirm in LiZhongQC) | 500 | GO (medium; scout qc null-set lemma) |
| `kernels_spec` | TRUE | clause 1 = `g2c_normalized_kernel_series_exists` + affine reduction + Grunsky uniqueness (`IsGrunskyCoeff` uniqueness exists); clause 3 = `g2c_kernel_row_series`/`A21_basis_pairing`; clauses 2, 4 (`K4`) analog by inversion `g1_inverted_exterior` | 600 | GO (relocation) |
| `lemma_2_5` | TRUE | clause 1–2 Parseval on `𝔻×𝔻` from `kernels_spec`, `A21_area_parseval`; `S ∈ A2` via `K1(z,z) = −S/(6π)` + `KK1(z,z)`; clause 3 continuity of the series (diagonal definition `kerK1_diag`) | 600 | GO after `kernels_spec` |
| `eq_2_4` | TRUE | `B1B1* + B2B2* = I` in kernel form: needs `K2` expansion (mixed block) + Parseval | 700 | GO after `eq_2_2`, `kernels_spec` |
| `eq_2_9` (Ch2) | TRUE | reflection `u ↦ 1/ū` + Ch2 `eq_1_3` | 400 | GO after `eq_1_3` |
| `lemma_2_12` | TRUE | standalone Takagi factorization of a compact symmetric operator on ℓ²; Mathlib compact self-adjoint spectral theory | 800 | GO (independent lane item) |
| `eq_2_8`, `remark_2_8` | **FALSE as formalized (D1)** | – | – | STATEMENT DEFECT: stop, leader |
| `remark_2_3` | TRUE | none (Kühnau–Grunsky `‖B₁‖ ≤ ‖μ‖∞ < 1`); `C` bound follows from `eq_2_2` | >1500 | NO-GO (wall) |
| `thm_2_6` | TRUE | needs `T01 ⇒ HS` (via `thm_1_12`, `lemma_2_5`) | – | NO-GO / BLOCKED |
| `cor_2_9` | TRUE? | needs `T01` characterization by `HS` (blocked as `thm_2_6`) | – | BLOCKED |
| `periodP_injective` | TRUE | Grunsky coefficients determine `f` (`log(f(z)/z)` from `hexp` at `w = 0`) and then `g`, then the welding and `[μ]` (Ch1 `WeldingUniqueness`, `bersPhi_congr_fB`, Ch1 injectivity of `Φ`) | 400 | GO? (scout Ch1 injectivity) |
| `lemma_2_7` | TRUE | variation of `K1` along `fsans(tμ)`: GPT `QCVariation*` modules | 1000+ | UNSURE (heavy; scout after the GO items) |
| `thm_2_10` | TRUE | needs `lemma_2_7`, `thm_2_6` | – | BLOCKED |
| `eq_2_12` | TRUE | needs `cor_2_9`/`thm_2_6` (compactness), `lemma_2_12`, Bergman kernel model | 800 | BLOCKED |
| `detF_spec` | TRUE | needs compactness (`cor_2_9`), `eq_2_12`; independence of the choice = multiset of singular values | 700 | BLOCKED |
| `eq_2_13` | TRUE | `detF_spec` + `eq_2_9` | 100 | BLOCKED |

S2 total GO: ~5900 lines (`thm_2_1`, `eq_2_2`, `grunsky_unitary`, `eq_2_1`, `remark_2_2`, `kernels_spec`, `lemma_2_5`, `eq_2_4`, `eq_2_9`, `lemma_2_12`, `periodP_injective`).

## 4. Proposed order (cheapest unlocks first)

1. Relocation approval (`Ch2/S2_Completed.lean`) and import of the Koebe/Nehari module.
2. `eq_2_2` → `grunsky_unitary`, `eq_2_1` (unlocks `thm_2_1`'s machinery) → `thm_2_1` → `remark_2_2`.
3. `kernels_spec` → `lemma_2_5` → `eq_2_4`.
4. S1: `bers_curve_factorization`, `remark_1_2`, `eq_1_3`, `remark_1_14`, `remark_1_9` clause 1.
5. `eq_2_9`, `lemma_2_12`, `periodP_injective`.

Blocked/NO-GO after this: `thm_1_6` (Becker–Pommerenke), `remark_2_3` (Kühnau–Grunsky), and everything downstream of the `T01` ⇔ HS ⇔ A2 chain.

## Re-scout 2026-10-26 (S3 lemma_3_6 / remark_3_10 / thm_3_5 / thm_3_8) -- all NO-GO
- lemma_3_6: book route = smooth case (Green/Cauchy on quasicircle domains g(D), f(D*), welding relation differentiated twice, j∘γ=γ∘j) + dilation limit f_n=r_n^-1∘f∘r_n needing cor_A_4, cor_A_6 (both sorry; depend on thm_A_3, lemma_A_5, betaHat_spec, Ch2 Thm 1.12). S2_Mixed mg_gap_green gives only the *quadratic* ∬|U'|² on the ρ-gap (analytic curves), no Cauchy–Pompeiu with double-pole kernel, no sesquilinear/point evaluation; T1–T5 only do inversion bookkeeping. Est >= 4-6k, walls: App.A convergence, Cauchy-Pompeiu with 1/(z-w)^2.
- remark_3_10: needs lemma_3_6 for p and invT p, plus K w̄ = w (l=0 generalized Grunsky = thm_2_1 equality / remark_2_2 (3rd conjunct), both sorry; mg_eq_2_1 covers l,l'≠0 only). u=v-2w part alone is algebraic (~150) but cannot be delivered separately.
- thm_3_5, thm_3_8: depend on lemma_3_6 / cor_3_7 / Thm 3.1 chain. NO-GO.

## Scout 2026-10-26: corrected remark_B_6 conjunct 4, remark_B_9
- B_6 conj 1,2,3,5 closed (下属5). Conj 4 (null complement => ‖K1‖=1): eq_2_4 not applicable (needs partner g). Route = single-curve Grunsky equality via g~=1/f(1/.) on D*, Green on interior of g~(|z|=r), r->1+, area->0 => B4 isometric. Est 1100-1300; not started. Beurling-isometry route worse (not in project).
- B_9: NO-GO. Part 1 needs symmetricT_spec (sorry) then ~250; part 2 needs norm continuity of period map (thm_B_1 only line-differentiability; lemma_B_2/thm_B_4/remark_B_3 sorry); strong conv + compact limit != norm conv. >=2k.

## T0(1) lane Phase 0 (2026-10-26): thm_1_6 -> lemma_1_11 -> thm_1_12
Statement check: thm_1_6 OK (pointwise complexDilatation in (i) is stronger than a.e.-limit: fine for (i)=>(ii)/(iii), constructible for the converse). lemma_1_11 (corrected) OK; g-part needs shift c in interior of the Jordan curve: f~(s)=1/(g(1/s)-c) is univalent on D incl. 0, bounded Jordan image, S(f~)=S(g)∘ι·ι'^2 in A2; A(g)=A(1/h)+2h'/h with h=g-c, difference 2g'/(g-c)-2/z=O(z^-2). thm_1_12 uses open originals cor_3_2 (T01 = bers in A2; sorry, behind thm_3_1/componentT_spec) and lemma_3_4 (T01 group, inv closed; sorry).
Pieces: P1 analytic half of 1.11 = DONE (a21_of_Psi_A2_of_boundary_small, lemma_1_11_disc_of_boundary_small). P2 f-part from thm_1_6((ii)=>(iii)) + remark_2_2-type S in A2 => (ii) ~150. P3 g-part reduction ~500. P4 thm_1_12 assembly (fB vs fsans Schwarzian, bounded Jordan of welding pairs, inversion (1.3) j.g.j, A2 under j, T01 inverse) ~1000. P5 thm_1_6 (BP): >=3000-4000 (wall: blow-up/normal families + topological Jordan argument for (ii)=>(iii); or (i)=>(iii) via K-qc normal families). Direct route avoiding thm_1_6: none cheap; for thm_1_12 only (i)=>(iii) for lemma_3_3 representatives (harmonic L2: remark_2_2 gives mu->0) is needed, still >=2k (qc compactness).
Recommendation: GO P2+P3+P4 (~1.6k) with sorryAx only via thm_1_6, cor_3_2, lemma_3_4; P5 separate funding decision.

## T112 2026-10-26: P2 done (ab112_lemma_1_11_f, S1_T112Completed). DEFECT in lemma_1_11: hJg (IsJordanCurve (frontier (toExt (g '' unitDiscExterior)))) is unsatisfiable for IsUnivalentAtInfty g: image unbounded => ∞ in frontier(toExt Ω) but ∞ is an isolated point of it (finite part compact), a Jordan curve has no isolated points. So g-part of lemma_1_11 is vacuous as stated; intended: frontier taken in ℂ (toExt (frontier (g '' unitDiscExterior))). thm_1_12 (iii),(iv) do not need the g-part: use eq_1_3 (gsans μ = conj b * refl (fsans μ⁻¹ (refl z))) and the f-part for μ⁻¹. P3 therefore not needed for thm_1_12.
