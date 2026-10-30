# 下属5 phase-2 triage (2026-10-25) — Ch2 S3/S4/S5, App. B, S1_1 phi_submersion / ker_DmuPhi

Read-only pass over the current files (statements + lean3/lean5 notes + GPT support modules). "TRUE?" is a statement-level
reading only (no counterexample found, no defect found); nothing was compiled. Estimates are lines of Lean.

Wall names:
- **W-GRP** Model-A group law: `wA_mul`, `beltramiMul_respects`, `componentT_spec`, `rightTrans_biholomorphic`, `ahlfors_weill` (all `sorry`, S1_1/S2_Hilbert, other lanes).
- **W-112** `thm_1_12` / `lemma_1_11` / `eq_1_3` (Ch2 S1; 下属4 lane).
- **W-GRUN** Grunsky/Faber layer: `eq_2_1`, `eq_2_12`, `detF_spec`, `kernels_spec`, `remark_2_2` (Ch2 S2 / Ch1 §2; 下属4/3).
- **W-B1** `thm_B_1` operator-norm holomorphy of μ ↦ B₁ (mine, open).
- **W-NS** Nag–Sullivan boundedness of the composition operator on H^{1/2}.

## S1_1 (2)

| item | TRUE? | existing support | est. | verdict |
|---|---|---|---|---|
| phi_submersion (general μ) | yes | `qcv_phi_submersion_zero`; `qcv_bers_surjective_iff` (reduces to the translated derivative); `qcv_bers_differential_covariance` (D_μΦ(ν)(z) = (ahVar κ)'''(W z)·W'(z)²); `qcv_ahVar_iter3`; `qcv_base_dot_fourth_kernel_source` → D_μΦ(ν)(z) = −(6/π)W'(z)²∫_{𝔻*}ν W_u²/(W u−W z)⁴. All axiom-clean. | 600–900 | **NO-GO (wall named)** — see below |
| ker_DmuPhi | yes | same + `qcv_ker_DmuPhi_iff`, `qcv_bers_kernel_iff_third_variation_zero`, `qcv_ker_D0Phi` | 600–900 | **NO-GO (wall named)** |

Wall for both. With F = wA μ (disc-preserving) and W = g∘F on 𝔻* (Stoilow, g conformal onto the complement of f(𝔻)), the change
of variables v = F(u) turns the translated condition into ∫_{𝔻*} λ(v) g'(v)²/(g(v)−y)⁴ dv = 0 for all y ∈ f(𝔻), λ ∈ L∞(𝔻*).
Two ingredients are missing:
1. **(A)** the Model-A↔plane link (Stoilow factorization `W|𝔻* = g∘wA μ` and `D₀R_μ(λ) = (1−|μ|²)·λ(F u)·conj F_u/F_u`). About 300–500 lines. Needs `wA` Jacobian/dilatation algebra from S1_1; `wA_mul` itself is not needed on this route.
2. **(B)** density: the kernels `g'(v)²/(g(v)−y)⁴`, y ∈ f(𝔻), are weak-* total in A₁(𝔻*). This is the "⊆" half of the kernel and is also what surjectivity needs. It is a Runge/quasidisc-area-zero argument, not the Laurent-moment argument used for the disc.
Surjectivity alternatively needs a section: Ahlfors–Weill (`ahlfors_weill`, still `sorry`) plus biholomorphy of R̂_μ (W-GRP).
Plan if the leader wants it: (A) first (self-contained, GO ~400 lines), then (B). The "⊇" half of `ker_DmuPhi` needs only (A) plus `k_y ∈ A₁(𝔻*)` (regularity at ∞ via the new `AOneStar` decay conjunct).

## Ch2 S3 (10)

| item | TRUE? | support | est. | verdict |
|---|---|---|---|---|
| thm_3_1 | plausible (constants not re-derived) | `qcv_schwarzian_fB_variation_origin` (variation at origin only); `detF` is a junk-1 definition and `detF_spec`, `eq_2_12` are open | 1500+ | NO-GO W-GRUN, W-B1 |
| vartheta_spec | yes | needs `thm_1_12 (iii)` and independence of the representative (gsans analogue of `modelA_to_modelB`) | 150 after W-112 | NO-GO W-112 |
| cor_3_2 | yes | pure rewrite from `thm_3_1` + `vartheta` | 30 | blocked by thm_3_1 |
| liouvilleS1Tilde_eq | plausible | `lemma_3_4` and its helpers are closed (GPT); needs `lemma_1_11`, Ch2 `eq_1_3` | 400 | NO-GO W-112 |
| thm_3_5 | plausible | TT proof ~180 lines; needs `lemma_3_6`, `liouvilleS1Tilde_eq`, `thm_3_1`-type machinery | 900 | NO-GO W-112, W-GRUN |
| lemma_3_6 | plausible (misprint already corrected) | needs kernels_spec/Grunsky identities for the welding pair | 700 | NO-GO W-GRUN |
| cor_3_7 | yes | from `thm_3_5` | 30 | blocked |
| thm_3_8 | plausible | needs `thm_3_1`, `thm_3_5`, connectedness of T₀(1) (`Ch1.thm_3_1`/`cor_3_2`, open) | 200 after | blocked |
| cor_3_9 | yes | from `thm_3_8` | 30 | blocked |
| remark_3_10 | plausible | needs Faber/Grunsky kernel identities (`kernels_spec`, `remark_2_3`) | 600 | NO-GO W-GRUN |

## Ch2 S4 (8)

| item | TRUE? | support | est. | verdict |
|---|---|---|---|---|
| thm_4_1 | plausible | needs `eq_4_1`, `thm_4_1_variation`, `thm_3_1`-class differentiation | 400 after | blocked |
| eq_4_1 | yes | `fB`/`W` composition, `qcv_bers_covariance`, `qcv_planeTransition` (GPT) cover the Model-B algebra; the `wA`-based `w_{εν}`/`schwarzianDz` form needs the Model-A composition | 300–500 | NO-GO W-GRP |
| thm_4_1_variation | plausible | ∂_ε̄ comes only from the reflected coefficient of `wA(εν)`; needs first variation of `wA` in the conj direction (= `qcv_plane_hasFDerivAt` on the reflected term) | 500 | NO-GO W-GRP |
| cor_4_2 | yes | from `thm_4_1` and `omegaWPOrigin` unfolding | 50 | blocked |
| remark_4_3 | yes | from `thm_3_8` and `cor_4_2` | 50 | blocked |
| remark_4_4 | plausible | principal-value limit and symmetry; needs the `lieTheta` computation (from `eq_4_1`) | 500 | blocked |
| componentBase_spec | yes | clauses 1–2 are cheap (`componentT` is `connectedComponent`: `mem_connectedComponent`, `connectedComponent_eq`); clause 3 needs `componentT_spec` (right translations permute components) | 80 (+W-GRP for clause 3) | **partial GO**: clauses 1–2 now, clause 3 blocked |
| wpPotential_spec | plausible | right invariance of ω_WP at every chart centre; needs `rightTrans_biholomorphic` + `wpInner` invariance | 300 | NO-GO W-GRP |

## Ch2 S5 (9)

| item | TRUE? | support | est. | verdict |
|---|---|---|---|---|
| nag_sullivan | yes ([NS95]) | `lean2_circle_qs*` (BA extension, translation covariance) give QS circle pieces; Dirichlet-norm boundedness of f∘γ missing | 1200+ | NO-GO W-NS |
| matAB_spec | yes | clauses 3–5 are circle-integral algebra given clause 1–2; clauses 1–2 need `nag_sullivan` (symplectic identity) | 700 | NO-GO W-NS |
| prop_5_1 | plausible | needs welding pair + `matAB_spec` + Grunsky identities | 700 | NO-GO W-GRUN, W-NS |
| cor_5_2 | plausible (`kyns` is a junk-0 choice; existence follows from `prop_5_1`) | from `prop_5_1`, B1 symmetric | 200 | blocked |
| cor_5_4 | plausible | needs `thm_1_12` + `cor_5_2` + Hilbert–Schmidt criterion | 300 | blocked |
| remark_5_5 | plausible | needs `detF_spec`/singular sequences (`IsSingularSeq` junk-free) and `cor_5_4` | 400 | blocked |
| embedding_spec | plausible | Faber polynomials (`IsFaber`), Grunsky expansion `Q_n(f)=…`; HS of B₁ via `cor_2_9` | 500 | NO-GO W-GRUN |
| remark_5_7 | plausible | as above + `eq_2_13`-type inversion (`B4 = conj B1([μ]⁻¹)` needs `eq_1_3`) | 500 | NO-GO W-112, W-GRUN |
| remark_5_8 | plausible ([Teo03], very large) | Hirota/Schottky characterization | 3000+ | **NO-GO** (new theory) |

## Appendix B (6)

| item | TRUE? | support | est. | verdict |
|---|---|---|---|---|
| remark_B_6 | yes | conjuncts 1, 2, 3, 5 are closed: `brazD_schwarzian_bound`, `brazD_le_kerOpNorm`, `kerOpNorm_kerK1_le_one`, `brazD_id_le_one`; `kerK1_id` makes conjunct 6 follow from conjunct 4. **Open core:** `kerOpNorm (kerK1 f) = 1 ↔ null complement` (both directions). The statement sits above its support (line 208); it must move later in the file (own file; leader approval). | 400–700 for the iff | **GO** for the assembly; the iff is the work |
| remark_B_9 | yes | `remark_B_9_of_compact` (conditional), `b9_symmetric_lift_BA` | 1000+ | NO-GO: symmetric ⇒ compact bridge (needs `thm_B_4` or direct vanishing-dilatation ⇒ small period tails) |
| thm_B_1 | yes | my `qcv_param_hasDerivAt_iter` machinery gives pointwise Taylor-coefficient derivatives; operator-norm convergence needs uniform tail control of the Grunsky matrix over `ν+tμ` | 800–1200 | **GO-conditional** (own-lane; start with a uniform Grunsky tail bound) |
| lemma_B_2 | yes | needs approximation of symmetric classes by diffeos | 1500+ | NO-GO |
| remark_B_3 | yes | Hilbert-topology closure + `lemma_B_2`; `T₀` through `thm_1_12` | 800 | NO-GO W-112 |
| thm_B_4 | yes | `remark_B_9_of_compact` gives one direction of the downstream; this needs both directions of compact ⇔ symmetric | 2000+ | NO-GO |

## Recommended order (cheapest unlocks first)
1. `componentBase_spec` clauses 1–2 (as a lemma, 30–80 lines) — only useful once clause 3 lands; park.
2. `remark_B_6` core iff (the one real unlock in Appendix B that is independent of W-GRP/W-112).
3. Stoilow/dilatation link (A) — also unlocks the "⊇" half of `ker_DmuPhi`, and is reused by `eq_4_1`.
4. `thm_B_1` (uniform Grunsky tail bound) — feeds `thm_3_1`.
Everything else waits for W-GRP, W-112, W-GRUN, or is new theory (`remark_5_8`, `lemma_B_2`, `thm_B_4`).

Unfinished lean5 WIP (`collaboration/lean5/wip_uncompiled/`: `BergmanPlaneIdentification`, `HolomorphicMatrixEstimate`): not yet read; I will triage them when I start (3).
