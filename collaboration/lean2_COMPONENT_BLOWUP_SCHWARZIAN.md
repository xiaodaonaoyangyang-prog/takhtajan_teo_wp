# Exact normalized Schwarzian scaling — lean2 exclusive, 2026-10-27

## FINAL DELIVERY — 7 endpoints standard-only, production/export EXIT0

`Ch1/ComponentBlowupSchwarzian.lean`: 110 lines, MD5
`f957bc248dcd8c9967a74d1d70c8fe01`. Log:
`collaboration/lean2_component_blowup_schwarzian.log`.
All seven printed endpoints use only propext/Classical.choice/Quot.sound;
no sorryAx. Own compiler/slot released. Normalization and public definitions
remain frozen; no old/root/original/peer modules edited or re-audited.

Safe import: `TakhtajanTeo.Ch1.ComponentBlowupSchwarzian`.
The exact endpoint requested by lean3 L6 is cbs_schwarzian_difference,
with the signature shown below and NO assumed difference/limit identity.
cbs_normalized_holomorphic supplies DifferentiableOn on the whole moving
open domain; cbs_normalized_deriv_ne_zero supplies the actual nonzero
derivative at every point in that domain. cbs_normalized_injective proves
global injectivity from the affine source and actual homeomorphism.

Proof uses the actual normalized_interior identity on an open neighborhood,
schwarzianHol_congr, the affine-input chain rule, and nonzero affine-output
Möbius invariance. All denominator nonvanishing is obtained from the already
proved normalization lemmas. The single-map theorem is
```
cbs_normalized_schwarzian hmu e he ha0 ha1 ht :
  schwarzianHol (cbl_normalized e a) t
    = (cbl_scale a)^2 * schwarzianHol (fsans mu) (cbl_source a t)
```
Actual bersPhi_spec and the AInf subtraction formula give the two-map
identity. No global holomorphy of e is used. Pending-validation text below
is historical; the new module is ready for consumer import.

New file: Ch1/ComponentBlowupSchwarzian.lean (cbs_ prefix).
Public cbl_scale/source/normalized definitions and normalization module stay
frozen. The moving open domain is cbl_source a preimage unitDisc.

Prove actual normalized function holomorphic on that domain, derivative
nonzero, and the exact two-map identity requested by lean3 L6. Use the
actual interior equality as a neighborhood germ; apply Schwarzian chain
rule for affine input and nonzero affine output invariance. No hypothesis
equating Schwarzians, no global holomorphy assumption on the QC extension,
no duplication of compact-domain/limit or normal-family/jet work.

Implemented consumer endpoint (validation active):
```
cbs_schwarzian_difference hmu hnu eMu eNu heMu heNu ha0 ha1 ht :
  schwarzianHol (cbl_normalized eNu a) t
    - schwarzianHol (cbl_normalized eMu a) t
  = (cbl_scale a)^2 *
      AInf.toFun (bersPhi nu-bersPhi mu) (cbl_source a t)
```
ht is the actual condition cbl_source a t in unitDisc; heMu/heNu are
actual agreement on disk, with no assumed Schwarzian relation or limit.

Supporting endpoints: cbs_domain_open, cbs_normalized_holomorphic,
cbs_normalized_injective, cbs_normalized_deriv_ne_zero,
cbs_affine_schwarzian, cbs_normalized_schwarzian. The holomorphy domain is
exactly the source preimage of the disk. The full-plane map is only assumed
to be a homeomorphism agreeing with fsans on disk; global QC is unnecessary
for this stronger local identity, and is supplied separately by the already
proved normalization module for normal-family consumers.
