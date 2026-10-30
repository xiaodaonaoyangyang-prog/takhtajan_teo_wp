# Actual Hilbert differential injectivity — lean2 exclusive continuation

## DELIVERED: restricted genuine separation, 2026-10-27

`Ch1/HilbertBersInjectivity.lean`: 138 lines, MD5
`fa04d5bab89d883a3b80fef658650431`. Production compile/export EXIT 0;
`collaboration/lean2_hilbert_injectivity.log` prints five endpoints with only
propext, Classical.choice, Quot.sound (no sorryAx). Own slot released.

Safe import: `TakhtajanTeo.Ch1.HilbertBersInjectivity`.
Every endpoint has the explicit condition `norm (bersPhi mu) < 2`:
- hbInj_small_leftInverse: constructs the actual differentiable local left
  inverse, no inverse/injectivity assumption.
- hbInj_ambient_small: injection of phi -> D0BersR mu (Lambda phi).
- hbInj_hilbert_small: Function.Injective (hbL2_bersOperator mu).
- hbInj_kernel_small: D0BersR mu a=0 iff a belongs to trivialBeltrami,
  using the already proved actual derivative projection preservation.
- hbInj_harmonicL2_small: equal actual images imply EqOn of the harmonic
  L2 representatives on the exterior.

This is actual restricted kernel separation, not another hInjective wrapper.
General-base injection and the frozen original statements remain OPEN.
No previous batch, original, root import, or peer module was changed.

2026-10-27. New exclusive module: `Ch1/HilbertBersInjectivity.lean`.
Completed differential and preimage modules remain unchanged.

The frozen final target is `Function.Injective (hbL2_bersOperator μ)` for
every `μ : LinfStarBall`. The next genuine step constructs a local LEFT
inverse of the actual A-infinity chart from Ahlfors–Weill, right translation,
and its inverse, under the explicit condition `norm (bersPhi μ) < 2`.
Differentiating this identity proves actual injection, rather than assuming
injection or a local inverse. This restricted result is not the full target.

The existing small-coordinate theorem proves only a right inverse and ambient
surjection. No existing general-base kernel identification may be assumed.
In particular ker_DmuPhi, thm_2_3, and abstract transported-origin splitting
are not admissible substitutes. The extension beyond the Ahlfors–Weill ball
remains a genuine global-slice or fourth-order-kernel separation obligation.

## Exact boundary of the new proof

Write H(phi)=bersPhi(beltramiMul(Lambda phi) mu) and
J(psi)=bersPhi(beltramiMul(Lambda psi)(beltramiInv mu)). The proof obtains
J(H(phi))=phi near zero from TWO actual Ahlfors–Weill identities, for phi
and for H(phi), followed by the proved quotient group cancellation.
Differentiability of J at bersPhi mu also needs Lambda(bersPhi mu) to lie
in the coefficient unit ball. Both uses are justified by the stated
norm(bersPhi mu)<2 condition; they are not justified for arbitrary mu.
The existing global estimate is norm(bersPhi mu)<=6 (bersPhi_spec).

The exact global-slice extension needed by this method is a map
S : AInf unitDisc -> LinfStar, differentiable at bersPhi mu, locally valued
in LinfStarBall and satisfying bersPhi(S psi)=psi near bersPhi mu.
Then replacing Lambda by S in J would prove the desired left inverse.
Such a section would itself need a genuine general-domain construction;
neither the abstract transported-origin quotient nor injectivity of the
nonlinear Bers map supplies it. We do not assume it or create a conditional
wrapper around it. Alternatively, proving density/separation of the actual
fourth-order welding tests would bypass this global-slice issue.

A possible later continuation through the surjective A2 operator family
would additionally require operator-norm continuity along t*mu and a
proved perturbation/connectedness argument. Forward norm<=48 alone does
not establish that continuity, and an unproved reproduction theorem cannot
be used to assert surjectivity. No claim that this route is implemented.
