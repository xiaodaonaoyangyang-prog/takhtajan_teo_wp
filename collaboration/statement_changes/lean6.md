# lean6 — statement review and changes

## 2026-10-28 B.4 and B.9 proof relocation (no mathematical change)

Original names `TakhtajanTeo.AppB.thm_B_4` and `remark_B_9` moved from
`Appendix/B_PeriodMapping.lean` to `Appendix/PeriodCompactCharacterization.lean`.
Original docstrings and theorem signatures preserved exactly (line endings
normalized for mechanical comparison); original snippets retained as
`collaboration/lean6/original_thm_B_4.txt` and `original_remark_B_9.txt`.
New proofs are `pcb_thm_B_4` and `pcb_remark_B_9` with identical signatures.
All 35 supporting/new declarations have standard-three-only axiom audits.
Original-name final compilation/audit tracked in PERIOD_COMPACT_DELIVERY.md.
Consumers should import the new host; root integration is lean1-owned.
No extra premises, deleted conclusions, or new axioms. Existing ERRATA unchanged.

## 2026-10-28 Nag–Sullivan representative issue (review; no source change)

Target: `Ch2/S5_PeriodMapping.lean`, `HC`, `piHat`, `nag_sullivan`.

Current formulation: HC consists of arbitrary pointwise functions with integrable
circle trace and finite weighted Fourier energy. `piHat γ f` is literal
pointwise composition minus its mean. The first clause claims this preserves HC
for every quasisymmetric circle homeomorphism.

Evidence requiring resolution: the standard H½ action is not an action on
arbitrary Lebesgue-a.e. representatives by pointwise composition. If γ is a
singular quasisymmetric circle homeomorphism with a measurable full-measure set
E mapped into an arclength-null set, choose a proper arc I and let
f = indicator of γ(E∩I). Then f=0 a.e., hence all its Fourier coefficients and
its HC seminorm vanish. However f∘γ=indicator of I a.e.; subtracting the mean
does not affect nonzero coefficients. For a semicircle the odd Fourier
coefficients have size 1/(π|n|), so Σ|n||c_n|² diverges. Thus the literal
composition clause fails for this representative. Constructing such a singular
QS map in Lean has NOT yet been done here; this is a mathematical model review,
not a compiled counterexample or a completed correction.

Required faithful correction: define the bounded action on the H½ completion
(equivalently via canonical quasi-continuous traces), agree with composition
on smooth boundary data, and retain the symplectic/right-action/Möbius claims.
Merely requiring the desired preservation as a hypothesis, deleting the claim,
or asserting full-space completion from smooth calculations is not acceptable.
No replacement signature has been installed.

Consumers: matAB_spec uses the basis matrices; prop_5_1 needs genuine bounded
composition on the completion or a direct boundary Dirichlet-energy proof,
but need not invoke the flawed arbitrary-representative statement. Corrected
kyns already requires IsBoundedMat; that existing correction is unchanged.

Relationship to ERRATA: new modelling issue, separate from the already applied
D1 bounded-choice repair. Pending leader review and eventual formal interface.
Audit: no original declaration changed; no new hypotheses or axioms introduced.
