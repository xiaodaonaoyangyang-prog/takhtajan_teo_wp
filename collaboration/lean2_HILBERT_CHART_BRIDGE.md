# Actual A2 chart bridge — lean2 exclusive, 2026-10-27

## DELIVERED: actual inputs, three standard-only endpoints

HilbertBersChartBridge.lean: 47 lines, MD5
`2907ef4192f3880e5b030f98756d891d`. First-pass direct production/export
EXIT0; all three printed axioms exactly propext/Classical.choice/Quot.sound.
Log: collaboration/lean2_hilbert_chart_bridge.log. Own slot released.

Safe import: `TakhtajanTeo.Ch1.HilbertBersChartBridge`.

```
hbBridge_chart_injOn mu hgroup :
  InjOn (hib_chart mu) (ball 0 (Real.sqrt (pi/3)))

hbBridge_chart_strict_zero mu hgroup :
  HasStrictFDerivAt (hib_chart mu) (hbL2_bersOperator mu) 0

hbBridge_chart_local_data mu hgroup :
  HasStrictFDerivAt (hib_chart mu) (hbL2_bersOperator mu) 0 /\
  exists U in nhds (0 : A2 unitDisc), InjOn (hib_chart mu) U
```

There is NO norm(bersPhi mu)<2 restriction and NO assumed injection.
The proof reuses existing ba_injOn and bers_injective after recovering
the exact ambient Bers value via hib_chart_value. Thus it does not duplicate
lean1's new direct AInf coefficient proof.

Consumer for lean3: instantiate the generic fiber lemma with
E=F=A2 unitDisc, f=hib_chart mu, L=hbL2_bersOperator mu, x=0, and the two
fields of hbBridge_chart_local_data. The ONLY analytic operator premise
left for that application is actual Function.Surjective L. The existing
groupO condition remains, sufficient for hibOriginDerivativeIso; arbitrary
mu without groupO still needs additional A2 chart regularity.

No generic theorem was copied, no hsurj-to-hinj wrapper added before its
proof, no peer file or original modified, and no old audit repeated.

New module: Ch1/HilbertBersChartBridge.lean, prefix hbBridge_.
Lean1 owns the AInf nonlinear local injection; lean3 owns the generic
strict-surjection/local-injection fiber argument. Neither is duplicated here.

The actual map is the existing hib_chart mu, on the A2 ball of radius
sqrt(pi/3). ct_A2toAInf_norm_lt sends this ball into the AInf ball radius 2.
The existing ba_injOn and bers_injective already allow actual A2 injection
after using hib_chart_value to recover the embedded Bers value.

The strict derivative at zero is exactly hbL2_bersOperator mu, by
hib_chart_strict and hbL2_chart_fderiv_zero. Both are currently proved for
mu in groupO. This covers the intended Hilbert inverse-chart/IFT application;
it does NOT prove arbitrary-base thm_2_3 injection. This condition must remain
explicit when consuming lean3's generic theorem.

Final surjection is still supplied by the actual reproducing/preimage lanes.
No general bijectivity or strict differentiability outside groupO is asserted.
