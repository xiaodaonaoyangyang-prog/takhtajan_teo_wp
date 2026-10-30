# Synchronized blowup normalization — lean2 exclusive, 2026-10-27

## FINAL DELIVERY — 14 standard-only endpoints, public export EXIT0

`Ch1/ComponentBlowupNormalization.lean`: 122 lines, MD5
`9581eea5d6a372340f67b9844a772529`. Log:
`collaboration/lean2_component_blowup_normalization.log`.
All 14 printed endpoints use only propext/Classical.choice/Quot.sound,
without sorryAx. Own compiler/slot released. Definitions remain exactly
as agreed; no old module, peer file, original declaration or root was changed.

Safe import: `TakhtajanTeo.Ch1.ComponentBlowupNormalization`.
Main regular-family API:
```
cbl_normalized_plane e heK ha0 ha1 :
  IsKQCNormalizedPlane (cbl_normalized e a) K
```
For a synchronized sequence a n, use this pointwise with its actual
0<norm(a n)<1 bounds. K is UNCHANGED by both affine normalizations.
The denominator is proved nonzero from cbl_source_one_ne and e.injective;
no nondegeneracy or relative-derivative premise appears.

`cbl_actual_welding_family hmu` also constructs e,K directly from actual
welding data, retaining EqOn e (fsans mu) disk and the family theorem for
ALL admissible centers a. The same e and same K therefore serve the whole
sequence. Interior formulas explicitly require cbl_source a t in disk;
the denominator endpoint's disk membership is already proved.

Lean4 can now import the exact scale/source definitions and scale-norm
formula. Lean3 can import the actual normalized-plane family. Neither the
fixed-half-plane compact inclusion nor the normal-family/jet limit theorem
is claimed in this module. Pending-validation wording below is historical.

PUBLIC DEFINITIONS WRITTEN in Ch1/ComponentBlowupNormalization.lean:
```
cbl_scale (a : C) : C := -(((1-norm a)/2:R):C)*a/(norm a:C)
cbl_source (a t : C) : C := a+cbl_scale a*t
cbl_normalized (e : C ≃t C) (a t : C) : C :=
  (e(cbl_source a t)-e a)/(e(cbl_source a 1)-e a)
```
Exactly the coordinator's common definitions, namespace TakhtajanTeo.
Lean4 may consume these for fixed-half-plane compact inclusion and scaled
Schwarzian difference decay; lean3 owns normal family/jet assembly. The
new module is being proved/exported; definition spelling will not change.

This lane proves for 0<norm a<1: scale nonzero, source0=a, source1 distinct
and inside disk, image difference nonzero, and for actual globally K-QC
plane homeomorphism e: normalized is globally SAME-K QC, onto, fixes0/1,
and satisfies IsKQCNormalizedPlane. It also supplies the interior formula
when e agrees with fsans on disk. No nondegeneracy premise is added.
No old geometry module, root, original or peer file is edited.

Consumer names now implemented (final export validation active):
- cbl_scale_ne_zero / cbl_scale_norm: norm(scale)=(1-norm a)/2.
- cbl_source_zero / cbl_source_one_ne / cbl_source_one_mem.
- cbl_image_difference_ne_zero: denominator derived from actual e.injective.
- cbl_source_conformal: source affine map conformal onto the whole plane.
- cbl_normalized_zero / cbl_normalized_one.
- cbl_normalized_qc: same K globally and image univ=univ.
- cbl_normalized_plane e heK ha0 ha1: exact IsKQCNormalizedPlane interface.
- cbl_normalized_interior / cbl_interior_difference_ne_zero: actual fsans
  formula on {t | cbl_source a t in disk}, with denominator nonzero.
- cbl_actual_welding_family hmu: constructs a SINGLE actual e and K from
  existing welding data and supplies normalized-plane membership for EVERY
  admissible a. Thus sequence callers can fix e,K once and specialize at a n.

No derivative jet or fixed-half-plane geometry is duplicated in this lane.
