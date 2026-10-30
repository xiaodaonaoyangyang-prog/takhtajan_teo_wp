# Hilbert differential — precise initial claim, 2026-10-26

## DELIVERED 2026-10-27 (client date)

`Ch1/HilbertBersDifferentialL2.lean`: **324 lines**, MD5
`300d688b802878e3fbb1e9e34eda18cf`. Production compile/export exits 0 in
`collaboration/lean2_hilbert_bers_l2.log`. All 12 printed endpoints have only
`propext`, `Classical.choice`, `Quot.sound`; no sorryAx. The pending-validation
language farther below is historical. No original is counted closed.

Safe consumer import: `TakhtajanTeo.Ch1.HilbertBersDifferentialL2`.
- Unconditional: hbL2_forward (C=24), hbL2_distT_subset/saturation_subset,
  hbL2_bersOperator_spec/opNorm (48), exact harmonic-coordinate/representative
  correspondence with factor 2, hbL2_bersOperator_zero.
- Actual chart derivative: hbL2_chart_fderiv_zero μ hgroup, at the center
  only, with exactly lean3's hib_chart function expression.
- Explicit conditional reductions: hbL2_equivOfBijective,
  hbL2_thm_2_3_of_bijective (C=24, inverse bound supplied), and
  hbL2_distT_eq_of_surjective. General-base bijectivity is still unproved.

Next analytic interface is precisely
`∀ μ : LinfStarBall, Function.Bijective (hbL2_bersOperator μ)`
(or a suitably proved restricted variant for the groupO inverse-chart task).
It must be established for the actual operator; no use of eq_2_2, eq_2_3,
ker_DmuPhi, thm_2_3 or distT_eq_A2 placeholders occurred. Center derivative
identification does not by itself prove all-point hibDerivativeIso.
Source ownership and the genuine analytic dependencies below remain in force.
Own compiler finished and slot was released; no old group audit was repeated.

Authorized phase: EQ22_IFT_PHASE.md. Lean2 owns the Hilbert differential
reduction; lean5 owns the reproducing identity, lean3 owns inverse charts.
No original statements or definitions are changed.

## File placement correction from source inspection

`Ch1/HilbertBersDifferential.lean` already exists and exports the actual chain
rule and kernel transport. S2Core imports it, and Remark24Completed depends
on S2Core. Importing the proved L2 estimate back into that file would create
a cycle. Preserve that existing file. The new downstream extension is
**`Ch1/HilbertBersDifferentialL2.lean`**, exclusively lean2, prefix `hbL2_`.
This is a placement correction, not a relocation or alteration of old proofs.

## Immediate interfaces and estimates

1. `hbL2_forward hμ hν`, for μ in LinfStarBall and ν in harmonicL2 exterior:
   the actual `AInf.toFun (D0BersR μ (toLinf ν))` belongs to A2fun disk and
   its normA2 is at most `ENNReal.ofReal 24 * normL2 exterior ν`.
   Dependencies: d2_harmonicL2_memLp, bc_toLinf_ae, remark_2_4; no eq_2_2.
2. Define `hbL2_bersOperator (μ : LinfStarBall) : A2 unitDisc →L[ℂ] A2 unitDisc`
   by the actual lift of `D0BersR μ (Lambda (A2toAInf φ))`.
   Required specification:
   `A2toAInf (hbL2_bersOperator μ φ) = D0BersR μ (Lambda (A2toAInf φ))`.
   Bound: `‖hbL2_bersOperator μ φ‖ ≤ 48 * ‖φ‖`, using the existing exact
   `l29b_Lambda_L2` factor 2 and Remark 2.4 factor 24.
3. Range identification: distT μ is contained in A2fun disk; its EqOn-saturated
   version is likewise included. Equality still needs actual surjectivity.
4. At μ=0 the lifted operator is the identity, by qcv_D0_Lambda and the
   genuine right-translation derivative. No reproducing assumption.
5. Conditional downstream interface, explicitly NOT a completed claim:
   `Function.Bijective (hbL2_bersOperator μ)` yields a continuous linear
   equivalence on A2 by the bounded inverse theorem. This is the operator
   lean3 should use for the inverse-chart derivative, with the above formula.

## Open analytic obligations — do not disguise as closed

The existing `ker_DmuPhi`, `thm_2_3`, `distT_eq_A2`, `eq_2_2`, and `eq_2_3`
are not admissible proved dependencies. The transported origin quotient in
QCVariationTransportSplitting is explicitly not yet identified with the
actual Bers derivative at μ. Thus its kernel/surjectivity cannot be substituted
for D0BersR μ.

For general μ, injection still requires a genuine kernel argument for the
actual fourth-order welding kernel. Surjection requires a genuine bounded
preimage construction, followed by harmonic representative identification.
The intended reproducing input is the frozen eq_2_2 formula for an actual
QC reflection on fsans μ '' disk / gsans μ '' exterior; the corresponding
weighted L2 estimate and any use of the still-open eq_2_3 must be discharged
separately. Eq_2_2 alone will not be labeled an operator-isomorphism proof.

The frozen thm_2_3 has three clauses: forward bound, injection on harmonic
representatives (EqOn), and quantitative surjection. Only the first is an
immediate independent target. The IFT identification with the derivative of
the A2 chart additionally uses its actual A2 differentiability; the existing
ctb_thm_2_13_b12 supplies this only for μ in groupO.

Initial implementation estimate: 150–300 lines for forward membership,
bounded lift, inclusion, and origin identity; another 100–200 for exact
representative/range and conditional inverse interfaces. Reassess the actual
kernel/preimage proof with lean5's reproducing delivery before estimating it.
No Löwner, W-REG, projector_kernel, new agents, full build, or old group audit.

## Concrete implemented interface (new-module final validation in progress)

The module now defines `hbL2_bersOperator (μ : LinfStarBall)` and proves the
bound 48, exact ambient formula, identity at μ=0, harmonic-coordinate and
representative existence with exact L2 factor 2, and distribution inclusion.
Those endpoints passed the previous compile's standard-axiom checks. The
following additional identification also passed:

```lean
hbL2_chart_fderiv_zero (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
  fderiv ℂ (fun φ : A2 unitDisc =>
    toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ))) 0
    = hbL2_bersOperator μ
```

This is definitionally the `hib_chart μ` expression in lean3's file. It proves
the actual derivative identity at the center; it does not prove the
all-interior-points `hibDerivativeIso` proposition. Recentering through the
verified Hilbert transitions is still needed for that stronger interface.

`hbL2_equivOfBijective μ hbij` is a genuine bounded linear equivalence **with
explicit hbij**. `hbL2_thm_2_3_of_bijective μ hbij` gives exactly the original
three-clause target, with C=24 and C'=2*norm(inverse operator). The final two
ENNReal algebra repairs in that quantitative corollary are being checked.
`hbL2_distT_eq_of_surjective μ hsurj` requires only surjectivity and yields the
original EqOn-saturated distribution equality. None closes an original until
its analytic injectivity/surjectivity premises are proved.
