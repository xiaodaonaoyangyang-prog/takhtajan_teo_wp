# Actual relative ambient QC extension — lean2 exclusive, 2026-10-27

## DELIVERED — 7 clean endpoints, actual extension with no new hypotheses

`Ch1/ComponentRelativeAmbient.lean`: 111 lines, MD5
`f5ae5cf30ab4f0abdf6835896d05d7f4`. Direct production/export EXIT0;
all seven printed endpoints use only propext/Classical.choice/Quot.sound.
Log: collaboration/lean2_component_relative_ambient.log.
Safe import: `TakhtajanTeo.Ch1.ComponentRelativeAmbient`.
Own compiler and lean2 slot released; no old module or original edited.

Public endpoints:
- cra_welding_extension: actual global QC homeomorphism extending fsans on disk.
- cra_ambient_exists: actual H=e_nu composed e_mu.symm and exact disk formula.
- cra_relative_eqOn: relative conformal-map agreement inside Omega_mu.
- cra_ambient_images: exact interior/closure/frontier/exterior images.
- cra_relative_conformal: H is conformal onto the target interior.
- cra_relative_boundary_limit: trace of the relative interior map is H(z).
- cra_relative_ambient: one existential package of all required data, only
  the two original LinfStarBall premises; K>=1 explicit.

Concrete package extraction:
```
obtain ⟨H, K, hK1, hHK, hfw, hconf, hrel, hclosure, hfrontier, hE, htrace⟩ :=
  cra_relative_ambient hmu hnu
```
Interior image equality is hconf.2.2, global continuity H.continuous,
inverse continuity H.symm.continuous; global onto comes from H.surjective.
The two ambient extensions come directly from gMu_isWelding.2.1 and
t203_pack_homeo, and QC of H uses the existing inverse/composition theorems.

This closes the requested ambient extension prerequisite only. No L2
relative coefficient, collar gluing, compact filling or componentT_spec
closure is claimed. Lower validation-in-progress wording is historical.

Owned new module: Ch1/ComponentRelativeAmbient.lean, prefix cra_.
Input is only mu,nu in LinfStarBall. Use the actual plane QC extensions
provided by gMu_isWelding, pack them as e_mu,e_nu, and set
H=e_nu composed e_mu.symm. Reuse existing homeomorph_inverse_isKQC and QC
composition. No extension-existence premise is added.

Deliver H globally QC, H(fsans mu w)=fsans nu w for disk w, exact interior,
closure, frontier and exterior images, conformality on the interior, and a
continuous boundary-extension interface for fsans nu composed invFunOn
(fsans mu) disk. The boundary trace must use that interior function, not
unjustified total-function values of fsans on the boundary.

No claim that H's relative coefficient is L2, no nonlinear collar/filling
construction, no componentT_spec closure. Relative Schwarzian is lean1's;
relative boundary is lean6's. Previously clean Hilbert modules stay frozen.

## Consumer interface

The main endpoint `cra_relative_ambient hmu hnu` returns H : C ≃t C and
K>=1 with IsKQC H univ K, together with:
1. H(fsans mu w)=fsans nu w for every disk w;
2. IsConformalOnto H Omega_mu Omega_nu;
3. EqOn H (fsans nu composed invFunOn(fsans mu) disk) Omega_mu;
4. H image closure(Omega_mu)=closure(Omega_nu);
5. H image frontier(Omega_mu)=frontier(Omega_nu);
6. H image E_mu=E_nu;
7. The relative interior function tends to H(z) from Omega_mu at every
   boundary z. Continuity of H itself is supplied by its homeomorphism type.

Helper endpoints separate actual ambient existence from the general
homeomorphism consequences, so later filling constructions can reuse the
image/trace lemmas for a modified witness. No boundary evaluation of the
totalized invFunOn is claimed equal to H(z).

New-module validation is active; the first check required only explicit
composition coercions and using Tendsto.congr' for the boundary trace
instead of ContinuousWithinAt (which would require the wrong boundary
value equality). No mathematical assumption changed.
