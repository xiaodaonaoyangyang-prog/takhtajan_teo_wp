# Actual kernel / preimage continuation — 2026-10-27

## FINAL BATCH DELIVERY — 375 lines, 10 checked endpoints

All four modules compile/export EXIT 0; all ten endpoint axiom checks have
only propext/Classical.choice/Quot.sound. Prior 12-endpoint module unchanged.

| Module | Lines | MD5 | Log in collaboration/ |
|---|---:|---|---|
| HilbertBersPreimage | 75 | 2738158ff5b713c894cf1d593d149977 | lean2_hilbert_preimage.log |
| HilbertBersKernel | 127 | 111e6372d22a52e6250d05afd5a78478 | lean2_hilbert_kernel.log |
| HilbertReflectionPreimage | 92 | 6761cd0c41290a63e03298c778f2fec5 | lean2_hilbert_reflection_preimage.log |
| HilbertBersPreimageAssembly | 81 | c5e1636782af0ac12eb792af2bf68ca7 | lean2_hilbert_preimage_assembly.log |

Import `TakhtajanTeo.Ch1.HilbertBersPreimageAssembly` for the whole batch.
Unconditional: actual harmonicProj L2 bound 48; welding kernel AOne membership
(holomorphy, absolute integrability, fourth-order decay); actual identity
`D0BersR μ (harmonicProj a) = D0BersR μ a`; conformal weighted-mass and
fourth-order integral transport with the correct phase. In particular the
trivial subspace is contained in the actual kernel; reverse separation is open.

`hbPre_reflection_preimage` constructs the actual harmonic preimage from
lean5's genuine reproducing equality and MemLp-infinity/finite-L2 of the
specific raw coefficient below. It has no hbij assumption, and bounds the
result by 48 times the raw norm. It does NOT assert those analytic inputs.

Exact remaining geometry alignment for lean5/lean6:
- `hbPre_reflected_mass` proves raw mass ≤ `(C*K/4)*target_mass` from anti-K-QC
  and `|u-hu|^4*rho1(hu)*rho2(u)≤C`. Set rho1=inner lambda squared;
  rho2 is the transported exterior metric. Identifying it with the filled
  inversion-chart density remains an actual obligation.
- `hbPre_reflected_bound` gives `M*C0/2` from `|q|≤M*rho1` and
  `|u-hu|^2*|dzbar h|*rho1(hu)≤C0`. Measurability/boundedness must be proved
  before using toLinf. Arbitrary QC regularity alone is not that bound.
- A chosen reflection with both controls is not constructed here. Lean6 G1
  alone does not imply the L2 product bound. No eq_2_3 placeholder was used.
- After genuine metric/mass identifications the coarse inverse constant is
  expected to be `24*sqrt(C*K)`; that specialization is not claimed proved.

General-base injection and full original thm_2_3/distT_eq_A2 remain open.
Own compiler/slot released. Earlier compiling language below is historical.

Lean2's next exclusive module: `Ch1/HilbertBersPreimage.lean`, prefix `hbPre_`.
HilbertBersDifferentialL2's 12 validated endpoints remain frozen; no old audit.
The actual welding-test proof is split into the additional lean2-owned
`Ch1/HilbertBersKernel.lean`, importing Preimage. No peer owns/edits either file.

First genuine analytic delivery: `hbPre_projection_L2`,
`hbPre_projection_pairing`, `hbPre_pullback_norm` all compiled/exported with
standard-only axioms in `lean2_hilbert_preimage.log` (exit 0). The kernel's
holomorphy, integrability, infinity decay and derivative projection invariance
are now proved and exported in HilbertBersKernel. Its production log
`lean2_hilbert_kernel.log` exits 0, both public endpoints have standard axioms
only. In particular `hbPre_derivative_projection hμ a` proves the genuine
identity `D0BersR μ (harmonicProj a) = D0BersR μ a` for EVERY coefficient a.
The AOne proof establishes holomorphy, absolute integrability by conformal
area change, and O(w^-4) decay using the filled reciprocal welding chart.

New lean2-owned `Ch1/HilbertReflectionPreimage.lean` is compiling the actual
raw coefficient's weighted mass, exact exterior conformal mass transport,
and its pointwise boundedness under the derivative-weight geometry input.
It imports lean5's existing eq22_weighted_pullback, not the unproved eq_2_2.
Its explicit geometry premises remain open and do not close a theorem.

UPDATE: HilbertReflectionPreimage now exports all three quantitative endpoints,
standard-only (`lean2_hilbert_reflection_preimage.log`, exit 0). It proves
the raw reflected mass bound `(C*K/4) * target_mass`, exact conformal
pullback mass, and raw coefficient bound `M*C/2` under the respective
explicit geometry inputs. The remaining geometry has not been asserted.
The actual formula-to-harmonic-preimage assembly is lean2-owned in new
`HilbertBersPreimageAssembly.lean`, now compiling. Its inputs are the genuine
reproducing equality and MemLp-infinity/L2 of the specific raw formula,
not hbij. This records an explicit constructive interface for lean5/lean6.

## Source check and precise injectivity gap

Read local memoir source TakhtajanTeo2006.md, TT:1440–1590 (printed pp.24–26).
The proof states the bounded forward map and constructs onto preimages via
the reflected coefficient and harmonic projection; injectivity uses the
previous ambient Bers/tangent identification. The currently proved Lean
ambient formula is qcv_bers_kernel_iff_third_variation_zero, not that tangent
identification. ker_DmuPhi remains a sorry original and cannot be used.

With f=fsans μ and g=gsans μ, the exact remaining separation statement is:

```lean
∀ ν ∈ harmonicBeltrami,
  (∀ ζ ∈ unitDisc,
    (∫ w in unitDiscExterior, ν w * deriv g w ^ 2 / (g w - f ζ) ^ 4) = 0) → ν = 0
```

The completed r24_phi_formula identifies this with the actual kernel of
D0BersR μ on harmonic coefficients. Bijection of right-translation on all
L∞ tangents, or bijection of the separately defined transported origin
quotient, does not prove this separation statement. No existing source proof
found so far closes it directly. A domain-transformed A1 density/separation
argument or an actual ambient differential kernel theorem is still needed.

## Genuine preimage and estimates — alignment with lean5/lean6

For target φ, set q(u)=φ(f⁻¹u)*(f⁻¹)'(u)^2 on Ω=f(disk). For a genuine
reflection h:E→Ω, E=g(exterior), the raw coefficient is

`b(u)=(1/2)*q(h u)*(u-h u)^2*dzbar h u`.

Its exterior coordinate is

`a(w)=b(g w)*conj(deriv g w)/deriv g w`.

The sign and factor 1/2 follow directly by comparing the coefficients -3/π
in (2.2) and -6/π in (2.1). The final coefficient is `harmonicProj (toLinf a)`;
projection may be applied only after a is genuinely MemLp infinity.

Lean2 is proving, without projector_kernel or eq_2_3:
1. Every bounded L2 coefficient admits a harmonic L2 representative of its
   actual harmonicProj, with norm ≤48 times the original norm. Existing
   hp_eq_Lambda, zero-base derivative formula and Remark2.4 suffice. A weaker
   constant than the orthogonal projection norm is sufficient for thm_2_3.
2. The actual welding kernel belongs to AOneStar, hence the harmonic projection
   preserves its pairings. This is the missing concrete projection step in
   the raw preimage assembly, not a new hbij wrapper.

Lean5's proved/ongoing weighted energy estimate supplies
`∫E |dzbar h|² G(h) ≤ K ∫Ω G`.
For the preimage L2 bound the additional geometric requirement is the product
bound `|u-hu|^4*λΩ(hu)^2*λE(u)^2 ≤ C`, with λE the **filled inversion-chart**
density. Lean6's current G1 quadratic-growth bound alone does not imply this
weighted L2 preimage bound. Also MemLp infinity of b is a separate obligation;
arbitrary QC differentiability does not bound its derivatives pointwise.

A concrete existing source for a chosen smooth reflection is LiZhong S20
`t203_reflection` (3505): for a bounded K-quasidisc it returns an actual C1
reflection with `|h(u)-u|²*norm(fderiv h u)*λΩ(hu)² ≤ c0`.
This can supply boundedness of b from the A∞ bound on q. It is not being
treated as the missing density-product estimate. Its source and target must
first be matched to the actual welding domains, including the puncture.

No unproved eq_2_2/eq_2_3 or stronger reflection hypotheses are silently
inserted into originals. Initial estimate: 200–450 lines for the projection
and welding-kernel support; reassess full geometric construction separately.
