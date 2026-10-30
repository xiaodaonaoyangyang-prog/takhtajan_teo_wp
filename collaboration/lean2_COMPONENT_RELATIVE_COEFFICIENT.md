# Actual relative coefficient bridge — lean2 exclusive, 2026-10-27

## FINAL DELIVERY — actual normalization/class bridge COMPLETE

Both new modules production/export EXIT0, eight audited endpoints standard3:

| Module | Lines | MD5 | Log in collaboration/ |
|---|---:|---|---|
| ComponentRelativeNormalization | 194 | 7c32afccd11b1aaeeba7c99b4fbe5d55 | lean2_component_relative_normalization.log |
| ComponentRelativeCoefficient | 197 | ce42d2625026471a87b170fc534e6240 | lean2_component_relative_coefficient.log |

Safe import: `TakhtajanTeo.Ch1.ComponentRelativeCoefficient`.
Own compiler/slot released. No original, old Hilbert/Ambient, peer or root
module changed or re-audited.

Exact principal consumer, with NO groupO premise:
```
crc_relative_coefficient_of_qc hmu hnu hF hFs hmatch hL2 :
  exists omega : LinfStarBall,
    normL2 unitDiscExterior (omega : LinfStar) < infinity /\
    Phi ⟨beltramiMul (omega : LinfStar) mu, grp_mul_mem omega.2 hmu⟩
      = Phi ⟨nu,hnu⟩
```
Inputs are exactly the actual physical extension contract: F globally
K-QC, F image univ=univ, F(fsans mu w)=fsans nu w on disk, and finite L2
of hbPre_pullback(complexDilatation F)(gsans mu). No target class equation,
boundary matching or extra normalization is assumed. The function-form
interface constructs its homeomorphism via t203_pack_homeo.

`crc_relative_coefficient` is the corresponding homeomorphism-form endpoint.
`crc_circle_map` provides the actual T, global QC, normalized circle action,
and exact a.e. equality of its complex dilatation with the specified raw
pullback. `crc_coefficient` constructs omega=toLinf(complexDilatation T),
proving norm<1 and retaining its a.e. formula. Combining these equalities
proves equality of the two weighted L2 norms, not merely a norm estimate.
`crc_normalized_boundary` then proves wA omega=T on the circle for this
SPECIFIED coefficient; bc_wA_mul proves the RIGHT product class omega*mu.

The requested implication is closed. Existence of a physical F with the
finite energy input remains the nonlinear collar/filling lane; no original
componentT_spec closure or such F existence is claimed here. Pending text
below is historical.

## Current verification

ComponentRelativeNormalization exported EXIT0 on first pass; 194 lines,
MD5 7c32afccd11b1aaeeba7c99b4fbe5d55. crc_normalized_boundary has only the
three standard axioms (lean2_component_relative_normalization.log).
Its input is a specified admissible coefficient with the actual a.e.
exterior dilatation identity, and it proves equality of normalized circle
values. No original Eq19 file was changed or recompiled.

ComponentRelativeCoefficient is now written and compiling. It builds the
real circle conjugacy, proves its exact complex dilatation including phase,
extracts the coefficient using the global QC essential bound, retains L2
by a.e. equality, and proves the RIGHT product class by bc_wA_mul.
No endpoint in this main file is counted proved before validation passes.

Main file: Ch1/ComponentRelativeCoefficient.lean (crc_ prefix).
Auxiliary strengthening: Ch1/ComponentRelativeNormalization.lean.
The latter retains the ACTUAL exterior coefficient in Eq19's normalized
circle-boundary proof; eq19_exists_mu alone discards that datum, so cannot
justify the requested L2 conclusion.

Route: pack the actual normalized exterior weldings as e_mu,e_nu and define
T=e_nu.symm composed F composed e_mu. Interior matching and continuous
boundary extension give T(wA mu z)=wA nu z on the circle. T is globally QC,
preserves the circle and fixes -1,-i,1. Its exterior dilatation equals the
specified hbPre_pullback(complexDilatation F)(gsans mu): right conformal
pullback supplies the phase; the left conformal inverse changes no coefficient.
Thus omega=toLinf(complexDilatation T) is admissible and finite L2. The
coefficient-retaining normalization theorem proves wA omega=T on the circle;
the actual product boundary formula yields Phi(omega*mu)=Phi nu.

No F-existence assumption beyond the user's stated input, no target class
equality as a hypothesis, and no derivative-only identification. Existing
Hilbert/Ambient modules stay frozen; no original or peer edits. The helper
adapts the already-proved Eq19 boundary argument to a specified coefficient,
rather than treating its existential witness as the specified coefficient.
