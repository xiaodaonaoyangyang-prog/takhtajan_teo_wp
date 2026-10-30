# PORT_PLAN (2026-10-27). The user authorized: download external Lean projects and translate them for our needs.

Clones (shallow, read-only, UNTRUSTED). Never run `lake`/`lean` inside them; only read and copy text.
- `D:\lean\external\no-wandering-domains` (Li–Luo, Apache-2.0, Lean v4.33.0, 172 files / 157k lines incl. vendored RMT4 + Carleson)
- `D:\lean\external\EllipticPDE` (Soto Franco, Apache-2.0, Lean v4.35.0-rc3, 214 files / 49k lines; ℝⁿ divergence-form PDE)
- `D:\lean\external\DeGiorgi` (Armstrong–Kempe, Apache-2.0, Lean v4.29.0-rc6, 94 files / 56k lines; d ≥ 3 only)

Port rules
- Ported code goes in new modules `TakhtajanTeo/External/<Repo>/...`, never into chapter files.
- Each ported module's docstring names its source file, repository, commit and authors, says "Apache-2.0, modified for
  TakhtajanTeo", and lists the changes.
- Port only the import closure that is needed. Fix the version drift to Lean v4.35.0-rc2 / Mathlib 2f3d8f6.
- Rename into namespace `TakhtajanTeo.External.<Repo>` so nothing collides with LiZhongQC or Mathlib.
- Bridges to our definitions (LiZhongQC `IsKQC`, `complexDilatation`, `dz/dzbar`; our `LinfStar`, `wA`, ...) are
  separate prefixed theorems.
- The usual gates apply: standard axioms only; relocation only when sorryAx-free; frozen statements; max 2 slots;
  incremental builds by the leader only.

Phase 1: read-only scouts (no Lean). Each scout returns one table:
`NO-GO item | wall | external results that apply (file:line, conclusion quoted) | missing pieces | port closure (files/lines)
| bridge cost | estimate | verdict`
- 下属1: W-REG cluster (joint C² of `(ε,z) ↦ w^{εμ}(z)`, ~22 S6/S7 items, plus exists_realAnalytic_rep,
  realAnalyticBeltrami_subgroup, remark_1_2) against NWD `QC/MRMT/{SmoothCase,NeumannSeries,AnalyticDependence}`,
  `QC/Calculus/Weyl*`.
- 下属4: B₃ removability cluster (detF_spec, eq_2_12, eq_2_13: W^{1,2} removability across quasicircles) plus
  remark_2_3 (Kühnau), against NWD `Analysis/Sobolev/*`, `QC/Calculus/Composition`, `QC/InverseQC/*`,
  `QC/Equivalence`, `QC/LengthArea/*`.
- 下属2: Appendix A/B and S1_1 NO-GOs (cor_A_2, cor_A_4, cor_A_6, lemma_A_5 conj 5, symmetricT_spec, lemma_B_2,
  remark_B_3, exists_leftTrans_not_continuous) against all three clones.
- 下属5: a sweep of EllipticPDE and DeGiorgi for anything usable by any remaining sorry (ℝⁿ→ℂ bridge cost included).
- 下属3: standing by (porting lane after the scouts).

Phase 2: the leader picks GO ports from the scouts and reports the choice to the user.
