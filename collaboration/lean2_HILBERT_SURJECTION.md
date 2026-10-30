# Actual Hilbert surjection assembly — lean2 exclusive, 2026-10-27

## FINAL DELIVERY — all actual analytic obligations in this lane discharged

Four new modules exported EXIT0; 16 endpoint audits standard3, no sorryAx:

| Module | Lines | MD5 | Log in collaboration/ |
|---|---:|---|---|
| HilbertPreimageMetric | 86 | 9417bd47058b616512df69b352047960 | lean2_hilbert_preimage_metric.log |
| HilbertBersSurjection | 148 | 58db9bd7e1bf63badbe6d020911ae6da | lean2_hilbert_surjection.log |
| HilbertBersIsomorphism | 59 | 28856d97b2b1ac23c9ec608e07691099 | lean2_hilbert_isomorphism.log |
| HilbertBersGeneralBase | 60 | e56dc4f40da761f81cd0d4124cecb752 | lean2_hilbert_general_base.log |

Total 353 lines. All completed modules now frozen. Own compiler/slot released.
First three modules are the requested surjection/groupO/IFT assembly.
Fourth is the independently started pre-delegation representative-equality
route described below; its validation also PASSED, all four endpoints clean.
Lean1 retains original migration and its own AllBase integration choice.

Exact consumer proofs for unchanged originals:
- thm_2_3 hmu := hbGeneral_thm_2_3 hmu (unrestricted, quantitatively bounded).
- distT_eq_A2 hmu := hbSurj_distT_eq (⟨mu,hmu⟩ : LinfStarBall).
- thm_2_13 := hbSurj_thm_2_13 (definitional hib_chart abbreviation only).
- cor_3_2 := hbSurj_cor_3_2.

The last three original headers were independently replayed, EXIT0 and
standard3 in lean2_hilbert_closure_replay.log. hbGeneral_thm_2_3 itself has
the exact original header copied from S2; its public audit is standard3.

No groupO condition was silently dropped: hbGeneral_derivative_eq proves
actual nonlinear-map germ equality from Phi mu=Phi nu using the already
proved TWO-sided quotient product compatibility. hbGeneral_operator_eq
then proves equality of the A2 lifts. ctb_exists_groupO_rep yields a real
groupO representative, so hbGeneral_bijective transfers the established
actual groupO bijection to the original base. No generic transported-origin
quotient or pending global density theorem is used.

Safe consumer import for requested groupO lane:
TakhtajanTeo.Ch1.HilbertBersIsomorphism.
Optional fully general representative-invariance route:
TakhtajanTeo.Ch1.HilbertBersGeneralBase.

No original declarations, peer modules, root imports or configuration changed.
Original installation is not claimed until lean1 performs its integration.

## Final integration ownership acknowledged

Lean1's latest delegation claims HilbertBersAllBase and original migration.
Lean2 freezes the already-clean Metric/Surjection/Isomorphism modules and
does not edit original S2/S3 or the root. Isomorphism has now exported EXIT0,
59 lines, MD5 28856d97b2b1ac23c9ec608e07691099; seven endpoint audits are
standard3 in lean2_hilbert_isomorphism.log. Three exact original-header
replays (distT_eq_A2, thm_2_13, cor_3_2) also EXIT0, standard3, in
lean2_hilbert_closure_replay.log.

Race note: immediately BEFORE receiving lean1's final AllBase claim, lean2
had written and launched HilbertBersGeneralBase (own new module only), using
an independent representative-equality shortcut. It proves actual D0BersR
equality for Phi(mu)=Phi(nu) by quotient multiplication on a neighborhood,
then uses the existing ctb_exists_groupO_rep. Its one already-running
validation will be collected; no further competing all-base assembly or
original migration will be undertaken. It is optional evidence, not a
replacement for lean1's chosen all-base regularity integration.

## PUBLIC actual surjection COMPLETE

Two production/exported modules, all five endpoint audits standard3:
- HilbertPreimageMetric: 86 lines, MD5 9417bd47058b616512df69b352047960,
  log lean2_hilbert_preimage_metric.log, EXIT0.
- HilbertBersSurjection: 148 lines, MD5 58db9bd7e1bf63badbe6d020911ae6da,
  log lean2_hilbert_surjection.log, EXIT0.

Safe import: TakhtajanTeo.Ch1.HilbertBersSurjection.

`hbSurj_bersOperator (mu : LinfStarBall)` proves
`Function.Surjective (hbL2_bersOperator mu)` with NO additional assumptions.
`hbSurj_harmonic_preimage hmu hP` gives a real harmonic L2 coefficient whose
actual D0BersR image agrees with P on the disk. All target, raw coefficient,
reproducing, projection and coordinate steps are discharged, no hsurj input.

HilbertBersIsomorphism is now compiling its groupO bijection, full chart
derivative isomorphisms, actual distribution equality, exact thm_2_13 and
cor_3_2 conclusions. Do not count those until this final validation finishes.

New owned modules: HilbertPreimageMetric.lean (density identification) and
HilbertBersSurjection.lean (actual q, raw L2/essential bound, reproduction,
harmonic projection and A2 onto), followed by HilbertBersIsomorphism.lean
(groupO bijection and IFT input). Prefix hbSurj_.

Actual inputs are now proved: Eq22ReproducingFinal.eq22_reproducing,
HilbertReflectionProduct.hr6_reflection_density_product,
HilbertChosenReflection.hc6_chosen_raw_coefficient, and
HilbertInjectiveSubmersion.his_injective_of_surjective. Do not label these
as remaining analytic hypotheses.

We must still prove exact exterior metric transport, construct target q via
the inverse interior welding map, prove its finite physical A2 mass, pull
the same chosen reflection coefficient to the exterior with boundedness and
finite L2, then consume hbPre_reflection_preimage. The groupO hypothesis is
needed only for actual chart strictness/local injectivity in the final
bijection; surjection itself targets every LinfStarBall base.
Original source migrations and root imports remain lean1-owned.

## Metric bridge exported; assembly validation active

hbSurj_exterior_density is now proved/exported EXIT0, standard3, in
HilbertPreimageMetric.lean. It identifies the square of the FILLED exterior
density exactly with rho(invFunOn g E u)*norm(deriv(invFunOn g E)u)^2.
The removable reciprocal chart includes zero; no punctured-domain density
was substituted. Log: lean2_hilbert_preimage_metric.log.

HilbertBersSurjection is written and compiling. It constructs q from the
inverse conformal disk map, proves finite mass using eq22_pullback_mass,
obtains its weighted supremum using eq22_A2_weighted_sup, uses the SAME
chosen reflection for boundedness and hr6's product bound, and combines
hbPre_reflected_mass with the exact metric identity. Expected final endpoint
hbSurj_bersOperator has no groupO or surjectivity hypothesis.

HilbertBersIsomorphism is written but not compiled until that dependency
passes. It consumes his_injective_of_surjective with the actual chart data,
retaining groupO, then supplies hibOriginDerivativeIso/hibDerivativeIso.
No assembly endpoint is counted proved while its compilation is pending.
