# lean5 — Chapter 2 S4 Weil–Petersson potential

## Active task — holomorphic variation / Remark 4.4 (2026-10-28)

Root accepted and froze original `thm_4_1_variation` (root integration EXIT0,
original-target count 53→52). No re-audit/rebuild of that package.
New exclusive lane: `Ch2/S4HolomorphicVariation.lean`, prefix `s4hv_`.
Goal: actual dz variation, genuine Euclidean-ball PV, and bilinear symmetry
for original `remark_4_4`. Blueprint: `lean5/S4_HOLOMORPHIC_BLUEPRINT.md`.
The `−12/π` constant is under explicit normalization review against the
actual `−6/π` first-variation kernel. No statement change or error claim yet.
No dependence on unfinished S3 thm3.1 or S7 thm7.4 is allowed.

H1–H10 are verified: `S4HolomorphicVariation` (`s4hv2.log`, MD5
`a4ee7c884f8a1b41caa1b1467e1d1292`) and `S4PrincipalValue`
(`s4hvp2.log`, MD5 `a8fdfcedccd1991f60a5467198cde7d8`) production EXIT0;
`s4hv_pv_axioms.log` checks every new theorem, all standard3. The actual
quartic difference kernel has genuine Euclidean-ball PV and an exact
regular-square / quadratic-PV decomposition. The endpoint is not yet
identified with `lieTheta`, and the bilinear symmetry is not yet proved.
H11–H21 are now verified in `S4MixedVariation`,
`S4SchwarzianLinearization`, `S4HolomorphicTransport`, and
`S4HolomorphicChart`: production logs `s4hvm3`, `s4hvlin2`, `s4hvt1`,
`s4hvchart1` all EXIT0; audits `s4hv_mixed_axioms`, `s4hvt_axioms`,
`s4hvchart_axioms` each check the new declarations only, all standard3.
The parameter/spatial third derivative exchange uses Cauchy integrals
without C4. Actual `wA` and plane-transition derivatives are actual third
`dz` derivatives of `ahVar`; the actual `lieTheta` chart formula is proved.
Root has already accepted/frozen H11–H19. H20–H21 are ready for integration.
Remaining: identify those actual third derivatives with the genuine
cutoff PV, prove coordinate-cutoff transport, and establish bilinear
symmetry with justified integrability/operator limits. The original
Remark 4.4 is still open; no normalization defect has been asserted.

## Current result — original variation completed (2026-10-28)

**`TakhtajanTeo.Ch2.thm_4_1_variation` is proved with its original statement
unchanged, including every exterior point.** It is relocated to
`TakhtajanTeo/Ch2/S4VariationCompleted.lean:13`; the old host contains a
relocation comment. Strict production `s4_variation_original.log` EXIT0;
original-name `s4_variation_original_axioms.log` EXIT0, exactly
`[propext, Classical.choice, Quot.sound]`. The old host was incrementally
published in `s4_variation_relocation_host.log` EXIT0 and retains its five
other original sorry bodies. No new sorry/axiom/resource-limit option was
introduced. The 20 new supports P1–P20 are all individually standard3-audited.

Full handoff: `collaboration/lean5/S4_VARIATION_DELIVERY.md`. Lean1 received
the verified result and the request to add the shared top-level import
`TakhtajanTeo.Ch2.S4VariationCompleted`; that entry is owned by lean1.
`thm_4_1` and its consumers remain outside this completed variation package.

The milestone entries below are historical progress notes superseded by
this result. There is no outstanding compile session in the lean5 lane.

## Active continuation (2026-10-28)

The preceding 20 declarations are accepted and frozen for this continuation.
Exclusive new files: `Ch2/S4ModelAVariation.lean` (`s4ma_`) and subsequently
`Ch2/S4PullbackVariation.lean`. Target remains original `thm_4_1_variation`;
no installation of dependent thm_4_1 or use of open S7 orthogonality.
First package: actual Model A coefficient splitting; normalized-family
Schwarzian separate holomorphy; real-slice Wirtinger extraction; Möbius
invariance identifying the actual wA Schwarzian. Only new/affected modules
will be compiled through the shared atomic slot wrapper.

**Continuation milestone:** `S4ModelAVariation` (9 declarations) production
`s4ma5.log` EXIT0; focused `s4ma_axioms.log` EXIT0, all nine standard-only.
`s4ma_wA_variation` now proves actual wA real differentiability and its
antiholomorphic dz-Schwarzian derivative with the negative reflected kernel.
The previous 20 declarations were not rebuilt or re-audited. Continuing
in exclusive `S4PullbackVariation` (`s4pv_`) with exact global quotient
coefficient linearity and the actual normalized transition identity.

**Pullback milestone (2026-10-28):** `S4PullbackVariation` P1–P4 passed
`s4pv3.log` EXIT0 and `s4pv_axioms.log` EXIT0 (all four standard-only).
The actual quotient coefficient is exactly `e * ahT_dot` a.e.; the actual
normalized transition equals its normalized solution under explicit local
small-parameter bounds. Continuing in `S4PullbackSmooth` to derive the actual
target-domain smooth representative. Original `thm_4_1_variation` remains open.

**Smooth representative milestone:** `S4PullbackSmooth` P5–P8 compiled and
published (`s4pvs6.log` EXIT0, no warnings). Actual local conformal coordinate
`J ∘ Nκ = wAκ`, a.e. coefficient phase cancellation, target exterior openness,
and a globally equivalent Beltrami coefficient smooth on that open set are
proved. Focused axiom audit will run with the next actual-transition package.

**Actual transition regularity:** `S4PullbackHolomorphic.s4pv_plane_transition_regular`
compiled and published (`s4pvh3.log` EXIT0, no warnings). It proves a genuine
open parameter neighborhood of 0 with spatial C3, joint continuous jets
through order 3, nonzero dz, and complex-parameter Schwarzian holomorphy for
the actual normalized moving-base transition. Continuing `S4PullbackAssembly`
to identify the original welding expression. Focused new-package audit pending.

**Assembly milestone:** `S4PullbackAssembly` P10–P12 compiled/published
(`s4pva3.log` EXIT0). `s4pv_regular_axioms.log` verifies all P5–P12 standard3.
The actual composed welding Schwarzian is parameter holomorphic away from
the auxiliary coordinate point. `S4JointContinuity` P13–P16 also compiled
(`s4j2.log` EXIT0). Final `S4PoleRemoval` P17–P20 is under incremental check;
the original name has not yet been relocated or counted complete.

**Current 2026-10-28 ownership supersedes historical ownership below:** only
Ch2 S4_WPPotential and the new Ch2 S4 support modules (`s4v_`). S3 is lean4; Appendix B
and S5 are lean6. See the resumed-task section at the end for current status.

The following 2026-10-25 entries are historical; current results are at the end.

Updated 2026-10-25 (Asia/Tokyo). Work continues autonomously under the user's
six-peer sustained-work instruction; no waiting for another batch assignment.

## Ownership and constraints

Owned scope: `Ch2/S3_Variations.lean`, `Ch2/S4_WPPotential.lean`,
`Ch2/S5_PeriodMapping.lean`, `Appendix/B_PeriodMapping.lean`.
Sections §3, §5 and Appendix B have been edited. No peer-owned source, shared Basic,
top-level import, build configuration, new chat, or subagent changes.
Old Li Zhong archive work is stopped.

Use existing artifacts, direct module compilation with
`-DautoImplicit=false -DrelaxedAutoImplicit=false`, and explicit axiom checks
of new/changed results. No full build/rebuild or dependency fetch. Do not use
unfinished memoir statements as completed dependencies.

## Completed original statements

**`AppB.psi_A1inf0` is fully proved with its original statement unchanged.**
A localized Cauchy estimate bounds the weighted derivative by 16 times the
weighted bound on an outer annulus. This transfers boundary vanishing from
`(1-|z|²)ψ` to `(1-|z|²)²ψ'`; the quadratic term is the square of the
original weighted function.

Supporting helpers: `weighted_deriv_annulus_bound`,
`weighted_deriv_boundary`. All three have only
`[propext, Classical.choice, Quot.sound]`.
Evidence: `lean5_B_batch3.log`, `lean5_batch3_axioms.log`.

**`Ch2.thetaSymp_spec` is also fully proved with its original statement unchanged.**
The proof includes realness and antisymmetry, both isotropy clauses, the
positive/negative Fourier decomposition, and the normalized basis pairing.
The decomposition uses Mathlib's Hilbert Fourier basis to synthesize masked
coefficients and transports Haar integrals to the memoir's interval integrals;
no pointwise series convergence or unfinished project theorem is assumed.
Strict compilation and all four new/full axiom checks passed with only the
standard three axioms: `lean5_S5_decomposition.log`, `lean5_theta_axioms.log`.

**`AppB.dilateF_spec` is fully proved with its original statement unchanged.**
The kernel boundary limit follows from a holomorphic divided-difference
extension, maximum modulus on an outer circle, a compact uniform bound, and
a finite row-integral bound. It does not assume the unfinished Grunsky inequality.
Evidence: `lean5_B_dilation_complete.log`, `lean5_dilation_complete_axioms.log`.
All five support lemmas and the original theorem have only the standard three axioms.

**`Ch2.lemma_3_4` is fully proved with its original statement unchanged.**
The proof derives the area mean from sharp point evaluation, transports it by
Blaschke automorphisms to obtain Bergman reproduction, justifies differentiation
under the integral to obtain Dirichlet reproduction, and evaluates the real
pre-Schwarzian cross term using a holomorphic logarithm of the nonzero derivative.
The elementary kernel energy is `-π log(1-|w|²)`. Its contribution and the cross
term cancel the derivative-at-zero logarithm; source rotations complete the
stated general automorphism. The explicit A21 hypothesis is retained throughout.
Prototype axiom inspection passed with the standard three axioms in
`lean5_lemma34.log`; final publication passed in `lean5_S3_lemma34.log`.
Original-name axiom inspection also passed (exit 0) in
`lean5_lemma34_original_axioms.log`: exactly `[propext, Classical.choice, Quot.sound]`.

Appendix B retains 10 original `sorry` bodies, down from 12. Section 5 retains
9, down from 10; Section 3 retains 10, down from 11. Exactly **four original
statements** are closed in this lane.

## Published independent support results

All results listed here passed direct compilation and focused axiom inspection;
all have only the standard three axioms and no `sorryAx`.

- Symplectic form: `thetaSymp_antisymm`, `thetaSymp_Wplus`,
  `thetaSymp_Wminus`.
- Realness and Fourier bases: `thetaSymp_real_of_coeff`,
  `circleCoeff_neg_of_real`, `thetaSymp_real`, `circleCoeff_zpow`,
  `circleCoeff_div_const`, `thetaSymp_zpow`, `thetaSymp_div_const`,
  `thetaSymp_basis`, `zpow_div_mem_HC`, `zpow_div_mem_Wplus`,
  `zpow_div_mem_Wminus`.
- Fourier synthesis: `exists_circleFn_of_sq_summable`,
  `exists_HC_of_weighted_sq_summable`, `HC_fourier_decomposition`.
- Dilation: `dilateF_extension`, `dilateF_normalized`,
  `dilateF_argument_mem`, `dilateF_hasDerivAt`, `dilateF_deriv`,
  `dilateF_tendsto`, `dilateF_deriv_tendsto`.
- Schwarzian: `dilateF_schwarzian`, `dilateF_schwarzian_tendsto`,
  `dilateF_schwarzian_boundary`.
- Corrected Grunsky kernel: `kerK1_dilateF`, `kerK1_dilateF_tendsto`.
  The diagonal cases use genuine Schwarzian scaling/convergence, not zero.
- Kernel bounds: `deriv_eq_dslope_add`, `kerK1_exists_holomorphic_extension`,
  `kerK1_uniform_bound_of_extension`, `kerK1_row_integral_bound_of_extension`,
  `kerK1_weighted_row_boundary_of_extension`.
- Kernel holomorphy: `kerK1_symm`, `kerK1_eq_divided_difference`,
  `differentiableOn_kerK1`, `kerK1_row_mem_A21_of_extension`,
  `dilateF_kernel_row_mem_A21`, `kerK1_id`, `brazF_id_formula`.
- Brazilevic bounds and pseudometric properties: `brazF_schwarzian_lower`,
  `normA21_eq_eLpNorm`, `normA21_add_le`, `differentiableOn_kerK1_right`,
  `brazF_symm`, `brazF_self`, `brazF_triangle`, `brazD_symm`, `brazD_self`,
  `brazD_triangle`, `brazD_schwarzian_bound`, `brazD_zero_schwarzian_eq`.
- Pre-Schwarzian transformations: `preSchwarzian_comp_of_analyticAt`,
  `preSchwarzian_inv`, `preSchwarzian_inv_comp`, `preSchwarzian_inversion`,
  `preSchwarzian_add_const`, `deriv_affine_precomp`,
  `preSchwarzian_affine_precomp`, `preSchwarzian_affine_postcomp`.
- Matrix convergence: `isBoundedMat_row_isL2`,
  `isBoundedMat_summable_norm`, `isBoundedMat_summable`,
  `matApply_add_of_bounded`.
- Matrix norm: `matOpNorm_of_bounded`, `matOpNorm_of_not_bounded`,
  `matOpNorm_lt_top_iff`, `norm_entry_le_matOpNorm`,
  `matOpNorm_zero`, `matOpNorm_eq_zero_iff`.
- Row tails: `matApply_tail_sqSum_le`, `isBoundedMat_tail`,
  `matOpNorm_tail_le`.

Additional published §3 support results: `isConformalOnto_inv_puncturedDisc`,
`preSchwarzian_inversion_area`, `normA21_sdiff_singleton`,
`isConformalOnto_inv_exterior`, `preSchwarzian_inversion_area_exterior`,
`preSchwarzian_inversion_integral`, `preSchwarzian_inversion_integral_exterior`,
`a21_integral_add_const_sq`, `a21_area_mean`.
The real inversion integral identities retain explicit finite-energy hypotheses.
The area mean follows by polarization of the sharp origin bound; both new results
passed with exactly the standard three axioms in `lean5_area_mean.log`, and
publication compiled successfully in `lean5_S3_area_mean.log`.

The Bergman batch is also published and axiom-clean: `integral_image_conformal_complex`,
`a21_pairing_pullback`, `a21_inverse_deriv_pairing`, `a21_blaschke_deriv_pairing`,
`a21_bergman_reproducing`. Evidence: `lean5_bergman.log`, `lean5_S3_bergman.log`.

The seven Dirichlet helpers have passed their focused axiom checks:
`one_sub_mul_conj_norm_lower`, `a21_hasDerivAt_dirichlet_integral`,
`a21_dirichlet_reproducing`, `preSchwarzian_dirichlet_integral`,
`dirichlet_kernel_mem_A21`, `hasDerivAt_dirichlet_kernel_primitive`,
`dirichlet_kernel_energy`. Publication compilation passed in `lean5_S3_dirichlet.log`.

The seven energy/coordinate helpers are published and axiom-clean:
`integral_sq_norm_pullback`, `a21_integral_add_sq`, `preSchwarzian_eqOn`,
`preSchwarzian_blaschke`, `preSchwarzian_inverse_pullback`,
`preSchwarzian_energy_inverse`, `preSchwarzian_energy_rotation`.
Evidence: `lean5_energy.log`, `lean5_S3_energy.log`.

The final combination helper `lemma_3_4_blaschke` is also published and axiom-clean.

This is 105 published helper results, including the two Cauchy helpers above,
plus four completed original statements. Helpers are not counted as original
memoir theorem completions.

Latest publication logs: `lean5_S5_decomposition.log`,
`lean5_B_brazilevic_smooth.log`, `lean5_S3_lemma34.log`. Earlier focused axiom evidence:
`lean5_axioms.log`, `lean5_batch2_axioms.log`,
`lean5_batch3_axioms.log`, `lean5_norm_kernel_axioms.log`,
`lean5_matrix_bounds.log`, `lean5_norm_entries.log`,
`lean5_matrix_tails.log`, `lean5_symplectic_real.log`,
`lean5_symplectic_basis.log`.
Source passages checked: TT:5428–5446, 6224–6226, 6238–6278, 6436–6441.

## Matrix norm modelling repair — complete

The old unit-ball supremum assigned zero to the all-ones matrix even though
that matrix does not preserve `ℓ²`: a nonsummable real `tsum` in `sqSum`
was totalized to zero. This contradicted ARCHITECTURE.md's explicit infinity
convention for unbounded matrices.

Following coordination with lean1, `matOpNorm Z` now first tests
`IsBoundedMat Z`. Bounded matrices retain exactly the original supremum;
unbounded matrices have norm `∞`. Existing memoir theorem statement text is
unchanged. Finiteness is proved equivalent to boundedness; zero norm is proved
equivalent to the zero matrix; entries are norm-controlled.

The boundedness test has a genuine operator interpretation: finitely supported
conjugate-row test vectors bound every finite row square sum by `max C 0`.
Hence every row is in `ℓ²`, and `ab ≤ a²+b²` yields absolute convergence of
every coordinate series on `ℓ²`. Additivity is then proved from convergent
series. The proof does not infer convergence from totalized sums.

Historical and corrected regression evidence is in
`lean5_matrix_diagnostic.lean/log`: `oldMatOpNorm_ones` gives zero,
`not_isBoundedMat_ones` proves unboundedness, and corrected `matOpNorm_ones`
gives infinity. All have only the standard three axioms.

Affected statements: `IsCompactMat`, Theorem B.1's operator-norm limit,
Theorem B.4, and Lemma B.8's compactness hypothesis. These original proofs
remain open. Row tails are proved bounded and contractive, so the guard has
the intended behavior in `IsCompactMat`. `kerOpNorm` was not changed.

## Kernel diagonal modelling repair — integrated

Lean4 owns and corrected K1/K4 in §2 to use
`-schwarzianHol f z / (6*π)` on the diagonal, in agreement with TT:4657.
Lean5 did not edit §2. The old zero-diagonal quotient is retained explicitly
as historical evidence in `lean5_axioms.lean`; it is no longer asserted of
the public corrected kernel.

Both all-pairs kernel helpers have been repaired using `kerK1_diag` and
`kerK1_of_ne` and were recompiled/re-audited after publication of the corrected
§2 artifact. Evidence: `lean5_norm_kernel_axioms.log`.
The two Schwarzian helpers are also independently proved in Appendix B.

## Current work

### RK3 exterior smooth output — verified (2026-10-25)

New owned module: `TakhtajanTeo/Ch1/ResolventExteriorSmoothness.lean`, importing
only `ResolventTail`. No peer Tail/Smoothness/SourceTransport file is modified.
The bounded measurable tail extension is implemented locally using the existing
smooth compact factor, product-space convolution, separation, and absolutely
integrable Fubini interface. Its first incremental compile passed.

New general interfaces: `resolventTailInput_locallyIntegrable_measurable`,
`resolvent_tail_potential_eq_measurable`,
`resolvent_tail_operator_contDiffAt_measurable`, and
`resolventOp_contDiffOn_of_measurable_locally_smooth`. They use global
`Measurable g`, a uniform disk bound, and (for the last result) smoothness only
on the specified open subset of the disk. The application uses the zero
extension of the inverted input off the punctured disk, which is globally
measurable without continuity at zero.

The complete assembly compiled and published successfully (exit 0, no diagnostics)
in `lean5/exterior_smoothness.log`: measurable pullback, punctured local smoothness,
uniform bound, actual resolvent inversion change of variables, and the target
`RK3_output_smooth_exterior` / `RK3_output_BCinf_exterior`. The one focused audit
of its ten public results also passed (exit 0) in `lean5/axioms_exterior_smoothness.log`;
all ten have exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
No removable-center assumption or repetition of the completed uniqueness audits
is used. No change to a peer-owned tail interface was necessary.

The actual transport theorem `resolventOp_exterior_inv` states, for exterior z,
`resolventOp unitDiscExterior g z = resolventOp unitDisc (resolventExteriorPullback g) z⁻¹`.
Its proof uses `ahP_integral_image`, `resolventKernel_inv_weight`, and deletion of
the center only as a null singleton. The input pullback's three interfaces are
`resolventExteriorPullback_measurable`, `resolventExteriorPullback_contDiffOn`,
and `resolventExteriorPullback_bound`. All smoothness orders use genuine C∞,
`(⊤ : ℕ∞)`. The original combined RK3 declaration remains untouched.

### RK3 disk uniqueness — proved (2026-10-25)

Published module: `TakhtajanTeo/Ch1/ResolventUniqueness.lean`, importing only
`TakhtajanTeo.Ch1.RadialWirtinger` and `TakhtajanTeo.Ch1.ConformalLaplacian`.
No lean1 source file was edited and no S6/S7 import was introduced.

All 13 new theorems passed incremental compilation and focused axiom inspection
(exit 0, `lean5/resolvent_uniqueness.log`), each with exactly
`[propext, Classical.choice, Quot.sound]`. There is no sorry or axiom declaration
in the source. The proof is independent of RK3 and all unproved memoir statements.
Publication to the existing build library also passed (exit 0), recorded in
`lean5/resolvent_uniqueness_module.log`. Preferred import path:
`TakhtajanTeo.Ch1.ResolventUniqueness`. The former
`collaboration.lean5.ResolventUniqueness` is now a compiled forwarding import
(`lean5/resolvent_uniqueness_forward.log`), preserving the earlier consumer path.
No existing axiom audit was repeated for this move.
The focused reusable audit entry point is `lean5/AuditResolventUniqueness.lean`;
no repeat audit of unchanged completed proofs is needed.

Main interfaces, all in namespace `TakhtajanTeo`:
- `resolvent_homogeneous_unique_disc`: if `f ∈ BCinf unitDisc` and
  `∀ z ∈ unitDisc, laplace0 f z + f z / 2 = 0`, then `EqOn f (fun _ => 0) unitDisc`.
- `resolvent_homogeneous_unique_disc_C2`: the same conclusion using only
  `ContDiffOn ℝ 2 f unitDisc` and an explicit uniform norm bound.
- `resolvent_homogeneous_re_nonpos_disc`: the real-component maximum principle
  under those C2/bounded/homogeneous hypotheses.
- `resolvent_mixed_eq_hessian_trace`: under `ContDiffAt ℝ 2 f z`,
  `dz (dzbar f) z = (fderiv ℝ (fderiv ℝ f) z 1 1 + fderiv ℝ (fderiv ℝ f) z I I) / 4`.
- `resolvent_mixed_commute`: under the same local C2 hypothesis,
  `dz (dzbar f) z = dzbar (dz f) z`.
- `resolvent_real_line_second`, `resolvent_mixed_re_nonpos_at_max`,
  `resolvent_laplace_sub`, `resolvent_laplace_const_mul`.
- `resolventBarrier_pos`, `resolventBarrier_contDiffOn`,
  `resolventBarrier_equation`, `resolventBarrier_large_circle`.

The barrier is B(z)=(1+|z|²)/(1-|z|²). Its exact equation is
`laplace0 (fun u => (resolventBarrier u : ℂ)) z + (resolventBarrier z : ℂ)/2 = 0`.
The proof subtracts εB, puts the positive maximum on a compact inner disk,
uses the real Hessian sign and positive rho, and obtains a contradiction.
Multiplication by conj(f(z)) reduces complex uniqueness to the real upper bound.
The original RK3 declaration is unchanged and is not claimed closed.

### Punctured-disk and exterior uniqueness — proved (2026-10-25)

All eleven additions passed the focused incremental compile and axiom inspection
in `lean5/resolvent_punctured.log` (exit 0); every result has exactly the standard
three axioms, with no `sorryAx`. The proof bodies are merged into the same owned
low-dependency module `TakhtajanTeo/Ch1/ResolventUniqueness.lean`; its final
publication compile passed (exit 0) in `lean5/resolvent_uniqueness_both_models.log`.
The former prototype `lean5/ResolventPunctured.lean` is now an audit entry point.
Existing disk-result axiom audits were not repeated.

New reusable declarations (namespace `TakhtajanTeo`):
- `resolvent_re_nonpos_of_barrier`: open-domain maximum principle with a
  positive C2 supersolution and compact exhaustion boundary domination.
- `resolvent_log_norm_contDiffAt`, `resolvent_laplace_log_norm`.
- `resolventPuncturedBarrier_contDiffOn`, `resolventPuncturedBarrier_pos`,
  `resolventPuncturedBarrier_equation`, `resolventPuncturedBarrier_exhaustion`.
- `resolvent_homogeneous_unique_punctured_disc_C2` and
  `resolvent_homogeneous_unique_punctured_disc` (BCinf version).
- `resolvent_homogeneous_unique_exterior_C2` and
  `resolvent_homogeneous_unique_exterior` (BCinf version).

The punctured barrier is B=(1+|z|²)/(1-|z|²)-log|z|. Its verified defect is
`laplace0 B z + B z/2 = -log(norm z)/2`, positive in the punctured disk.
The compact-annulus proof controls both boundary circles explicitly; it never
fills the missing center. Exterior uniqueness uses
`laplace0_comp_of_density_pullback` and `rho_inv_jacobian` under inversion,
without asserting removability or a value at infinity. In both domains the
actual theorem only requires C2 and a uniform bound; BCinf is a corollary.
The original RK3 statement is still unchanged and not claimed fully closed.

The existing `TakhtajanTeo.differentiableOn_dzbar_of_contDiffOn` in
`Ch1/ConformalLaplacian.lean` supplies the other local C2 regularity interface
for lean1's Green/PDE existence work. These 24 independently verified uniqueness
and support results are additional to the 105 earlier support results in this
lane (129 before the ten exterior-regularity results above; 139 now); the count
of closed original memoir statements remains four.

The complete Lemma 3.4 proof passed prototype compilation and axiom inspection
with exactly the standard three axioms (`lean5_lemma34.log`). Its body is now
published in the original declaration with its signature and explicit A21
hypothesis unchanged. Final publication compilation passed in
`lean5_S3_lemma34.log`; original-name axiom inspection passed in
`lean5_lemma34_original_axioms.log`, with no `sorryAx`.
The area mean, Bergman and Dirichlet reproducing formulas, real pre-Schwarzian
cross integral, logarithmic kernel energy, inverse pullback, and rotation
invariance are already published and axiom-clean. These supply the complete
cancellation argument without any unproved memoir dependency.

The completed prototype files have been converted to focused import/axiom audit
entry points, avoiding duplicate published declarations. The next unresolved
§3 dependencies are the normalized-welding/tilde-action identification and the
variational kernel identity of Lemma 3.6; no closure is claimed for those.

Lean4 proved the unqualified disk branch of Lemma 1.11 false using
f(z)=1/(1-z). None of this lane's completed results uses that statement;
all required finite-energy hypotheses remain explicit.

The direct C∞ impact check is complete: `lean5_smooth_impact.lean` compiled
against lean2's corrected IsCircleDiffeo artifact, and Appendix B's normal
incremental compilation passed in `lean5_B_brazilevic_smooth.log`.
No completed proof used the former analytic interpretation. Lemma B.2 and
Remark B.3 remain unfinished; no Ψ or (7.14) assumption was changed.

The first inequality of B.5 and the Schwarzian supremum inequality of B.6
are proved independently in the published Brazilevic batch. The combined
originals remain open. B.5's operator upper bound and B.7's strong convergence
still require a genuine general Grunsky operator estimate; pointwise kernel
limits are not substituted for these operator assertions.

## 2026-10-25 resumed GPT lane: ker_D0Phi

The coordinator explicitly cancelled the old ExteriorEquation assignment: Claude
completed and integrated exterior RK3. Current assignment is `ker_D0Phi` against
the corrected `AOneStar`, including the QCVariation modules inherited from 下属5.
Read `LEADER.md` and `下属5.md`; their earlier pause is superseded by the resume.

Coordination with lean2: `S1_1_TeichmullerTheory.lean` is not being edited or
relocated. Work is in new downward-importing modules `QCVariationKernel.lean`
and `QCVariationLaurent.lean`; the original `ker_D0Phi` remains open there.
The following modules passed strict direct compilation, each with exit 0 and
no diagnostics: `QCVariationKernel.lean`, `QCVariationLaurent.lean`,
`QCVariationMoments.lean`, `QCVariationDensity.lean`. Logs respectively:
`collaboration/lean5/qcv_kernel.log`, `qcv_laurent.log`, `qcv_moments.log`,
`qcv_density.log`.

The proof route now exists completely in source: admissible fourth-order
Cauchy kernels; removable origin of the quadratic pullback; Laurent expansion
starting at exponent -4; vanishing of all Cauchy/Laurent moments by dominated
differentiation; absolute-series pairing; outward dilation contracts the L1
norm; a Scheffe-type argument supplies L1 convergence. Final assembly is
`QCVariationKernelEquality.lean`, now also strictly compiled with exit 0 and no
diagnostics (`qcv_kernel_equality.log`). The single focused
`collaboration/lean5/AuditQCVKernel.lean` audit succeeded with exit 0:
`qcv_kernel_axioms.log` lists all 22 new theorems and the one new definition;
every entry has exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The audit also type-checks the complete original signature as an `example`.

### Ready for lean1/lean2 integration

`TakhtajanTeo.QCV.qcv_ker_D0Phi`, in
`TakhtajanTeo/Ch1/QCVariationKernelEquality.lean:116`, proves the **full unchanged
signature** of `ker_D0Phi` under the currently installed corrected `AOneStar`.
The complete reverse inclusion is `qcv_ker_D0Phi_pairing` at line 88.
This is one complete original-equivalent proof plus 21 support theorems and one
definition. The declaration named `ker_D0Phi` in S1_1 is still unchanged/open,
so it is not yet counted as an original-name closure. No peer-owned file was
edited and the umbrella module was not changed.

Integration must be coordinated with lean2: the original cannot simply import
the new proof back into S1_1, because the QCVariation dependency chain already
imports S1_1. As with the previous `eq_1_4` relocation, move the original
declaration to `QCVariationKernelEquality.lean`, outside `namespace QCV`, with
body `QCV.qcv_ker_D0Phi`, and import that module from the umbrella/consumers.
Only the coordinator/owner should perform this core relocation and required
incremental consumer compilation. There are no other source uses of the old
name as of this handoff. No existing definitions or hypotheses were weakened.

MD5 of the five new sources:

- Kernel: `38f501f262a97d164679cc2b497e49f6`
- Laurent: `4bf38a3f212df1182d79dd45ac6ecec3`
- Moments: `eb55565e6966741e248cc747aa51f1b6`
- Density: `d9e7d635ad4c14424a8617a698316877`
- KernelEquality: `311257e53e0e587e381a24cd4ba0e01b`.

No own compiler or lean5 slot remains. Compiles used the shared slot admission
and free-RAM check, with a second slot-count check after admission added to
reduce concurrent admission races. No full build, no re-audit of earlier
accepted work, and no subagents. Next mathematical dependency unlocked:
`eq_1_3` (the harmonic complement) can combine this kernel identification with
the already proved `qcv_D0_Lambda` / `qcv_lambda_inverse_D0bers`.

The seven inversion-area and finite-energy integral helpers are published
and verified in `lean5_S3_inversion_integral.log`. Removing the origin only
uses an area-null singleton, with no holomorphy assertion at a totalized value.

## 2026-10-25 — ker_D0Phi full equivalent proof READY

`Ch1/QCVariationKernelEquality.lean:116` now proves `QCV.qcv_ker_D0Phi`,
the complete original signature. Both inclusions are finished: kernel tests,
removable origin/Laurent expansion, all vanishing moments, absolutely summable
pairing, outward-dilation L1 convergence. Five new modules strictly compiled,
exit 0; one focused audit of all 22 theorems and one definition has only the
standard three axioms, no sorryAx (`collaboration/lean5/qcv_kernel_axioms.log`).
KernelEquality MD5 `311257e53e0e587e381a24cd4ba0e01b`.
S1_1 unchanged; lean1/lean2 must relocate the original `ker_D0Phi` to this new
module (body `QCV.qcv_ker_D0Phi`) to avoid the existing import cycle. Integration
details are in the resumed-lane section above. No original-name closure counted
yet. No own compiler remains. Next unlocked: `eq_1_3` via the harmonic splitting.

## 2026-10-25 — CLAIM / coordination: general-mu tangent transport

Following lean1's new task, `QCVariationTransport.lean` is already published and
strictly compiled (exit 0, no diagnostics). It proves the two bounded-inverse
relationships between D0Rmu and Rnm, defines `qcv_rightDerivativeEquiv`, and
proves the actual Fréchet chain rule for `bersPhi (beltramiMul l mu)` at zero.
LEAN3: please reuse this module for the analogous D0BersR bridge instead of
duplicating the inverse proof. The focused batch audit has now passed.
Exact interfaces: `qcv_rightDerivative_Rnm`, `qcv_Rnm_rightDerivative`,
`qcv_rightDerivativeEquiv`, `qcv_bers_rightTranslation_hasFDerivAt` (all in QCV).
The same file proves full `qcv_origin_isCompl` (original eq_1_3 signature) and
`qcv_phi_submersion_zero`. `QCVariationTransportSplitting` proves the transported
closed complements and explicit split surjection. `QCVariationTransportCriteria`
proves unconditional kernel and surjectivity transport for the actual Bers map.
Neither general `phi_submersion` nor `ker_DmuPhi` is claimed proved:
the actual Bers covariance/descent at a nonzero base remains the analytic wall.

## 2026-10-25 — general-mu transport batch verified / ready for lean3

All three new modules compiled strictly with exit 0 and no diagnostics:

- `Ch1/QCVariationTransport.lean` (MD5 `6306f9ca28249b3307a9173e42073179`):
  D0Rmu and Rnm are bounded two-sided inverses, explicit continuous linear
  equivalence, forward norm bound 1 and inverse bound `1/(1-‖mu‖²)`, actual
  Fréchet chain rule. `qcv_origin_isCompl` at line 125 exactly matches eq_1_3;
  `qcv_phi_submersion_zero` at 145 proves the original submersion assertion at 0.
- `Ch1/QCVariationTransportSplitting.lean`
  (MD5 `8769b83aa2ec83768cf1adc67b0f471e`): the images of trivial/harmonic spaces
  are closed and complementary; `D0bers ∘ Rnm` has explicit right inverse
  `D0Rmu ∘ Lambda`, kernel exactly the transported trivial space, and an
  explicit harmonic/trivial decomposition.
- `Ch1/QCVariationTransportCriteria.lean`
  (MD5 `3d156fd539913c8ff6ae52e22a356326`): for the ACTUAL translated Bers family,
  `ker(Dmu bersPhi) = D0Rmu(ker(D0(bersPhi ∘ Rmu)))`, and exact equivalences
  reducing general-base kernel identification and surjectivity to that family.
  Do not confuse `qcv_translatedBersDerivative` (actual derivative) with
  `qcv_transportedOriginDerivative` (`D0bers ∘ Rnm`). They are intentionally
  distinct, with no unproved equality between them.

Evidence: `collaboration/lean5/qcv_transport.log`,
`qcv_transport_splitting.log`, `qcv_transport_criteria.log`; single new-only audit
`AuditQCVTransport.lean` / `qcv_transport_axioms.log` exited 0. All 23 new
theorems and 7 new definitions have exactly the standard three axioms, no
`sorryAx`. No preceding batch was re-audited. S1_1, root imports, and peer files
are unchanged. Original eq_1_3 name still awaits lean2 integration; one complete
equivalent proof is ready, not counted as an original-name closure.

LEAN3 reuse interfaces: `qcv_rightDerivativeEquiv`,
`qcv_bers_rightTranslation_hasFDerivAt`, `qcv_bers_kernel_transport`,
`qcv_ker_DmuPhi_iff`, `qcv_bers_surjective_iff` (all in `TakhtajanTeo.QCV`).
Next analytic step: prove the translated Bers derivative has kernel
`trivialBeltrami` and is surjective, using actual welding-domain/Schwarzian
covariance. `wA_mul`, `rightTrans_biholomorphic`, and original-name placeholders
were not used. No own compiler or slot remains.

## 2026-10-25 — actual nonlinear/general-base Bers covariance VERIFIED

Four new production modules are strictly compiled with exit 0, no diagnostics:
`QCVariationCovariance`, `QCVariationBasePoint`,
`QCVariationSchwarzianBasePoint`, `QCVariationDifferentialCovariance`.
One focused new-only audit (`AuditQCVCovariance.lean`,
`qcv_covariance_axioms.log`) exited 0: all 24 new theorems and 3 definitions
have exactly propext, Classical.choice, Quot.sound. Prior audits were not rerun.

These results concern the ACTUAL functions, with no welding assumption:

- `qcv_planeSolution mu = normalizedSolution (extB mu)`; its moving disk is
  `qcv_planeDisk mu = Wmu '' unitDisc`; the actual transition is
  `qcv_planeTransition nu mu = Wnu ∘ invFun Wmu`. It is conformal between the
  moving disks, is the identity when nu=mu, and satisfies the cocycle identity.
- `qcv_bers_covariance` (`QCVariationCovariance.lean:91`) proves
  `Phi(nu)(z)-Phi(mu)(z) = S(Hnu,mu)(Wmu z) * (Wmu'(z))^2` for all mu,nu in
  the open ball and z in the disk, using established Möbius invariance.
- `qcv_planeSolution_base_variation` and
  `qcv_planeTransition_base_hasDerivAt` prove the actual parameter first
  variation at arbitrary mu, including the source-coordinate integral.
- `qcv_base_dot_zero_on_disk` and `qcv_base_dot_isBeltramiCoeff` establish that
  kappa=`ahT_dot (extB nu) (extB mu) Wmu` is pointwise zero on the moving disk
  and is globally a Beltrami coefficient with bound `‖nu‖/(1-‖mu‖^2)`.
- `qcv_planeTransition_schwarzian_variation` uses parameter Cauchy estimates
  and spatial holomorphy on a fixed local ball to justify commuting derivatives.
  Its derivative is exactly `iteratedDeriv 3 (ahVar kappa)`; it is not an
  unproved differentiation-under-integral assertion.
- `qcv_bers_differential_covariance`
  (`QCVariationDifferentialCovariance.lean:36`) proves
  `DmuPhi(nu)(z) = (ahVar kappa)'''(Wmu z) * (Wmu'(z))^2`.
  `qcv_translatedBers_differential_covariance` specializes to D0Rmu(nu).
  `qcv_bers_kernel_iff_third_variation_zero` exactly characterizes the actual
  kernel by vanishing of this third derivative on the moving disk.

MD5: Covariance `1ab4e7d16a3520a0d41518bf32fee2d9`;
BasePoint `545331cf2a7eb3879407834544687d92`;
SchwarzianBasePoint `b890a92c543eb26e324d7f7e71f30d5b`;
DifferentialCovariance `93e8eb76ab19dee5730233ffb141f081`.
Compile logs: `qcv_covariance.log`, `qcv_basepoint.log`,
`qcv_schwarzian_basepoint.log`, `qcv_differential_covariance.log` in lean5/.

Coordination: after reading the human's restored cooperation instruction in
lean1's thread, sent exact interfaces to lean3 and a verified progress report
to lean1. Per latest division, lean3 owns the generic local formula
`(ahVar kappa)'''(y)=-(6/pi)*integral kappa(v)/(v-y)^4` for a bounded measurable
kappa zero on an open neighborhood. I do not duplicate that kernel calculation.
The actual QC source change for that fourth kernel is now verified in
`QCVariationKernelSource.lean` (two theorems, both audited).
General phi_submersion / ker_DmuPhi remain open: do not confuse this actual
covariance progress with a proof of domain-side annihilator equivalence and
surjectivity. No original statements, peer files or umbrella imports changed.

### Fourth-kernel source transport complete

`QCVariationKernelSource.lean:17`, `qcv_base_dot_kernel_source`, gives the exact
QC change of variables for any measurable complex kernel K:
`integral kappa(v)*K(v) = integral_ext nu(u)*K(Wmu u)*(dz Wmu u)^2`.
At line 86, `qcv_base_dot_fourth_kernel_source` specializes it to
`K(v)=(v-y)^(-4)`. All denominator, phase and Jacobian cancellations are proved
a.e.; finite inverse identities use the actual plane solution's injectivity.
No extra smoothness/welding assumption or unpublished third-derivative formula
is introduced. The identity is stated for Bochner integrals; the local-hole
integrability required for spatial differentiation belongs to lean3's interface.

Strict incremental compile `qcv_kernel_source.log` exited 0 (one harmless unused
push_cast linter warning). Separate two-name audit `AuditQCVKernelSource.lean` /
`qcv_kernel_source_axioms.log` exited 0, standard three axioms only. MD5
`c379403160eff4d39bfa134ce8266193`. No earlier audit was repeated.

This covariance batch totals 26 new theorems and 3 definitions across five
modules, all verified without sorryAx. No original general phi_submersion or
ker_DmuPhi closure is claimed. Once lean3's local ahVar third-derivative theorem
lands, the precise next assembly is:
`qcv_bers_differential_covariance` + `qcv_base_dot_fourth_kernel_source`.
For the remaining actual welding identification, lean2 received the requested
exterior germ `fBmu = normalizedWeldingExterior mu ∘ wA mu` and its dz chain
rule, valid away from the finite sphere exceptions. No own compiler remains.

## 2026-10-25 — Appendix B operator batch: TWO ORIGINALS CLOSED

Published into the owned `TakhtajanTeo/Appendix/B_PeriodMapping.lean`:

- **Original `brazF_id`, line 1302**, complete formula, row A21 membership, and
  sharp square-integral bound.
- **Original `lemma_B_5`, line 1313**, both inequalities, with the full original
  statement unchanged. Compared both signatures byte-for-byte with the saved
  before-publication source; both comparisons returned true.

New public support: `kerOpNorm_kerK1_le_one` (1112),
`brazF_le_kerOpNorm` (1225), `brazD_le_kerOpNorm` (1261),
`brazD_id_le_one` (1265), plus honest row membership and normalized reproducing
test interfaces. B.6's operator <=1 is not confused with the B.5 difference
bound: the former is a direct supremum application of lean4's G2c; the latter
uses an actual norm-one test whose operator output is exactly the normalized
kernel row. The row's square-summability is obtained from the verified Grunsky
matrix contraction and actual Bergman expansion before invoking reproduction.
All norms remain the actual extended area/operator norms.

The two original declarations were moved later WITHIN the same owned file so
their proved support precedes them; documentation, names and signatures are
unchanged. Added only the downward import `Ch2.GrunskyOperator`; no core module
split or consumer-chain rebuild. Other originals, especially the combined B.6
equality/null-area characterization and B.7, remain unchanged/open.

Evidence: checked candidate `b_operator_bound.log` exit 0; strict production
compile/export `b_operator_publication.log` exit 0 (only remaining original
sorry warnings elsewhere); single focused live audit `AuditBOperator.lean` /
`b_operator_axioms.log` exit 0. All 15 audited entries (two originals, twelve
support theorems, one definition) have exactly propext, Classical.choice,
Quot.sound, no sorryAx. No audit of lean4's already accepted foundation or the
unchanged previous lower bound was repeated. Current Appendix B MD5:
`81e374bbf2f85e156285b96079b4f18a`.

The scratch candidate is now an import-only forwarding file. The publication
script is guarded against rerunning, and the before-publication snapshot is
retained under lean5/. No own compiler or slot remains. Next possible B.7 route:
use the actual diagonal dilation action on the Bergman coefficient model and
the now-proved uniform operator contraction; pointwise kernel convergence alone
is not enough for strong convergence. No equality characterization was touched.

## 2026-10-25 — Original B.7 CLOSED, live source and axioms verified

**Original `TakhtajanTeo.AppB.lemma_B_7`, now line 827 of
`TakhtajanTeo/Appendix/B_PeriodMapping.lean`, is proved.** Its original signature
is byte-identical to the saved pre-publication source. Exactly its one sorry
was removed; it remains in its original section. The actual integral kernels,
extended area norm, arbitrary A21 input and original normalization assumptions
are retained. The h0 hypothesis is mathematically unnecessary for this proof
but is retained in the statement (one harmless unused-variable warning).

Proof chain:
- `BergmanDilation.lean`: actual coefficient diagonal action `D_r B D_r`,
  square-summability, contraction, two-term error bound and strong convergence.
- `BergmanKernelModel.lean`: reconstructs the genuine integral action using
  Bergman pairing, the actual Grunsky matrix and Parseval; the resulting norm
  is precisely the square root of the coefficient error mass.
- `kerK1_dilateF_bergman_series`, AppB line 803: proves the actual n>=1 kernel
  has coefficients `r^(m+1) B_mn r^(n+1)` with r=n/(n+1). Only the eventual
  n>=1 tail is used; no false zero-kernel claim is made for the n=0 dilation.
- Original B.7 applies that model to r tending to 1.

Evidence under `collaboration/lean5/`:
- `bergman_dilation.log`: strict helper compile/export exit 0.
- `bergman_kernel_model.log`: strict helper compile/export exit 0.
- `b_strong_candidate.log`: complete candidate exit 0.
- `b_strong_publication.log`: strict live AppB compile/export exit 0.
- `AuditBStrong.lean` / `b_strong_axioms.log`: focused live audit exit 0;
  all 23 entries (original B.7, 18 support theorems, 4 definitions) have exactly
  propext, Classical.choice, Quot.sound, with no sorryAx.
- `B_PeriodMapping_before_strong.lean`: pre-publication snapshot;
  `publish_b_strong.py` asserts identical original signature and exactly one
  sorry removal. The candidate is now an import-only forwarding file.

MD5: AppB `55c138257e4f08ba34867951fe1c1aa3`;
BergmanDilation `5932eec1d053b2b541a70fb71188b130`;
BergmanKernelModel `eb678f65cfe8a7f6dc04dcfaf5b4245d`.

All compiles used the guarded two-slot / >=6 GiB admission script; none was
started below the threshold. No full build, foundation re-audit, peer edit or
cross-chat notification was attempted. B.6's equality characterization and
other open originals were left untouched. No own compiler or slot remains.

## 2026-10-25 — Original B.8 CLOSED, live source and axioms verified

**Original `TakhtajanTeo.AppB.lemma_B_8`, now line 1467 of
`TakhtajanTeo/Appendix/B_PeriodMapping.lean`, is proved.** The signature is
byte-identical to `B_PeriodMapping_before_compact.lean`; exactly its one sorry
was removed (AppB total 7 -> 6). The original declaration/documentation moved
later within the same owned module to follow its reproducing-test support.

Proof chain and new interfaces:
- `BergmanCompactness.lean` (2 theorems): finite-coordinate subsequence plus
  uniformly vanishing square-mass tails gives a strictly increasing subsequence
  converging in square-sum norm. The limit's square summability is proved.
- `BergmanChosenCoefficients.lean` (2 theorems): the actual chosen exponential
  series extends continuously over the bidisk, its lift is jointly holomorphic,
  and its mixed derivative gives the actual kernel. No separately selected
  coefficient array is substituted for the period matrix.
- `BergmanPeriodModel.lean` (4 theorems): actual exterior normalization forces
  weldConst=0; using lean2's published actual welding/uniqueness, fsans/gsans
  form a normalized disjoint pair. `b8_pair_model` provides symmetry, genuine
  square-summability/contraction and the kernel expansion for the exact chosen
  B1 matrix. No unresolved remark_2_2, kernels_spec or eq_1_15 is used.
- AppB `b8_mat_tail_mass_le` (1352) converts the finite extended operator norm
  into a genuine output tail mass bound; `b8_compact_matrix_subsequence` (1385)
  is the exact IsCompactMat -> sequential relative compactness bridge.
- AppB `b8_kernel_compact_sequence` (1407) reconstructs an actual A21 limit
  through Bergman series and Parseval. Original B.8 then uses norm-one
  reproducing tests and the exact sqrt(pi) normalization to obtain precisely
  its stated weighted kernel rows and actual extended area-norm convergence.

Evidence under `collaboration/lean5/`: all strict incremental compiles/export
exited 0 (`bergman_compactness.log`, `bergman_chosen_coefficients.log`,
`bergman_period_model.log`); full candidate `b_compact_kernel.log` exited 0;
live AppB `b_compact_publication.log` exited 0. The latter only reports the
other open original sorries and the previously retained B.7 unused h0 warning.
The candidate's unused push_cast was removed before the successful live run.

`AuditBCompact.lean` / `b_compact_axioms.log`: focused live audit exited 0.
All 12 entries (original B.8 and 11 new support theorems) have exactly propext,
Classical.choice, Quot.sound, no sorryAx. No old B.5/B.7/G2c or peer interface
audit was repeated. The candidate is now import-only; publication is guarded
against rerunning. No peer files, full build or cross-chat notification used.
Every compile respected two slots and >=6 GiB available RAM admission.

MD5: AppB `5b060635c3d455654b5a5228157b627f`;
BergmanCompactness `100535e05ee03e74a8d4490fe81643d8`;
BergmanChosenCoefficients `d8c6ebe73925149b0c9dfba5c9a30e5e`;
BergmanPeriodModel `b275237214f11c0d1a98be89be656550`.
No own compiler or slot remains.

### B.9 next: precise unresolved prerequisites

Original `remark_B_9` remains at AppB line 848 and is not claimed complete.
Its hypothesis is p in symmetricT, not compactness. Source inspection confirms
`thm_B_4` (AppB line 185, compact iff symmetric) and `symmetricT_spec`
(S1_UnivalentFunctions line 1138, symmetric iff vanishing weighted Schwarzian)
still contain sorry. Thus neither can be used as a verified shortcut from the
original B.9 hypothesis. The new B.8 supplies the compactness -> kernel-row
subsequence direction only; it does not establish symmetric -> compact.
The independent operator step (completed in the batch below) is norm convergence
of D_r B D_r for compact B, followed by the actual kernel model. Closing original B.9 still
requires the genuine symmetric-class bridge (or a direct proof from its boundary
homeomorphism definition). B.6's equality characterization remains untouched.

## 2026-10-25 — Compact-dilation operator route verified; original B.9 still open

`CompactBergmanBounds.lean`, `CompactBergmanDilation.lean`, and
`CompactBergmanKernel.lean` have each strictly compiled/exported (exit 0,
empty logs). Focused `AuditB9Compact.lean` / `b9_compact_axioms.log` exited 0:
all 16 NEW theorems have exactly propext, Classical.choice, Quot.sound.
No old B.8/B.7/B.5 audits or recompilations were performed.

The finite-output-truncation / tail-bound proof establishes the stronger
result `b9_compact_matrix_norm_tendsto` (Dilation line 110): ANY IsCompactMat B
has D_r B D_r -> B in the actual extended matOpNorm for 0<=r<=1 tending to 1;
symmetry is unnecessary. Input errors are controlled on finitely many rows
by Cauchy–Schwarz and square-summable row dilation errors; output errors use
the finite diagonal plus the same uniformly small output tail. All outputs
and differences have actual summability and boundedness proofs.

`b9_kernel_norm_le_matrix` (Kernel line 29) compares the genuine integral
difference norm with that matrix error norm. Integrability of both rows is
proved BEFORE subtracting Bochner integrals; Parseval gives exact coefficient
norms. `b9_kernel_norm_tendsto_of_compact` (line 97) applies this to the actual
chosen periodP model, using n>=1 kernel identities. `remark_B_9_of_compact`
(line 125) gives BOTH original B.9 conclusions under IsCompactMat(periodP p);
the Schwarzian conclusion uses the accepted B.5 bound. This is explicitly
conditional support, NOT closure of original remark_B_9.

MD5: Bounds `a8723033c746ecd304d21d6bfea1f748`;
Dilation `8972935e726feabca25892c1f8925d0b`;
Kernel `924a5e4a811acf557cf3e4db2fe62387`.
AppB itself is unchanged, still `5b060635c3d455654b5a5228157b627f`.

### Genuine boundary bridge tracking

New discovery: the dependency's GardinerLakic2000 Ch16 S04 has a proved
`gl16_bal_local`, a localized Beurling–Ahlfors coefficient estimate, so the
first boundary step need not start from scratch. `SymmetricBoundaryExtension`
has now strictly compiled/exported (empty log, exit 0): it directly converts this project's absolute ratio
condition to reciprocal ratio bounds, then proves the actual BA extension of
the defining real lift has Beltrami coefficient uniformly tending to zero as
Im z -> 0+. This does not use symmetricT_spec, thm_B_4, or thm_1_6.

Remaining beyond this real-lift step: descend the periodic extension to the
circle/disk collar and identify the actual welding class; then prove that the
resulting vanishing boundary dilatation forces the period-matrix tails small
(e.g. compact-support approximation plus a proved Grunsky operator estimate).
The reference's thm16_3 (same S04) and para16_5_symmetric_iff (S05), as well as
the project's symmetricT_spec and thm_B_4, still have sorry and were not used.

`b9_lift_BA_vanishing` (Boundary line 20) is the uniform real-lift estimate;
`b9_symmetric_lift_BA` (line 45) extracts the actual lift and its circle-covering
identity from this project's IsSymmetricHomeo. No extra extension or vanishing
assumption is inserted. Focused `AuditB9Boundary.lean` / `b9_boundary_axioms.log`
exited 0: both new names have only propext, Classical.choice, Quot.sound.
MD5 `7011f4bacf4e77fec6ab83af1f41cd89`.

This batch totals 18 new verified support theorems in four owned modules.
The only new consumer compilation was the kernel module depending on the new
matrix bounds/dilation modules; no old module rebuild or old audit occurred.
Import `TakhtajanTeo.Appendix.CompactBergmanKernel` for the conditional B.9
endpoint, and `TakhtajanTeo.Appendix.SymmetricBoundaryExtension` for the genuine
boundary-lift progress. Original remark_B_9, thm_B_4 and symmetricT_spec remain
unchanged/open. No own compiler or slot remains. Resource guard, no-agent,
no-peer-edit and no-cross-chat-notification constraints were respected.
## 2026-10-28 resumed all-sorry task — active ownership

Owner lean5 exclusively claims `TakhtajanTeo/Ch2/S4_WPPotential.lean` and new
downstream support `TakhtajanTeo/Ch2/S4Variation.lean` (prefix `s4v_`).
Also exclusively claimed: `TakhtajanTeo/Ch2/S4ReflectedKernel.lean`, same prefix,
for the actual extA reflected coefficient kernel and Ahlfors triple derivative.
Also claimed: `Ch2/S4PlaneVariation.lean`, same prefix, deriving the actual
normalized plane-solution Schwarzian parameter derivative off coefficient support.
Specialized consumer `Ch2/S4ReflectedSchwarzian.lean` is also exclusively lean5:
actual reflected plane-family derivative, with a genuine integrability conjunct.
Next active exclusive module: `Ch2/S4ParameterJets.lean`, same prefix, for
parameter holomorphy of spatial jets using locally uniform difference quotients.
First endpoint: the original `thm_4_1_variation`, with no extra assumptions.
Installed `S4Eq41`/`WRegFoundation` are read-only inputs. Appendix B belongs
to lean6; S3 belongs to lean4. No old ContactNormalization or Appendix work
is resumed or re-audited.

Plan: derive the antiholomorphic parameter variation of the actual pulled-back
Schwarzian, using the installed identity (4.1), genuine parameter regularity,
and the reflected kernel integral. Then link the S3 first variation to the
fixed-chart mixed derivative and derive the S4 consequences. Current caution:
the auxiliary (4.1) excludes `wAS κ extInf`; the variation endpoint has no such
exclusion, so its proof must remove that auxiliary exceptional point rather
than add a hypothesis. No statement change has been made.

Status: inspected build10222 HANDOFF, ALL_SORRY_PLAN and current S4/S4Eq41;
preparing exact blueprint and checking reusable derivative APIs. No compiler
started in this resumed task.

### 2026-10-28 first verified analytic pieces (current)

`S4Variation` production `s4_variation3.log` EXIT0: denominator nonvanishing,
genuine bounded-coefficient kernel integrability, harmonic reproduction
`(6/pi) integral = conjugate(nu(z))*rho(z)/2`, and the integrable WP pairing.
`S4ReflectedKernel` production `s4_reflected3.log` EXIT0: reflection area
change of variables, exact actual extA/indicator kernel identity, and the
three-space-derivative Ahlfors formula. Seven new declarations so far, focused
axiom audit to follow with the plane-variation module. No original sorry
is counted closed yet. No statement changed.

Next: `S4PlaneVariation` actual normalized-solution Schwarzian derivative
off coefficient support, via Cauchy estimates and actual one-parameter
normalized solutions. This avoids falsely treating C3 joint regularity as
enough to commute four mixed derivatives. The full wA and general-base
pullback identity remain to be linked. `thm_4_1` also needs S7 `thm_7_4`
infinitesimally-trivial variation pairing, communicated to lean1; lean4
confirmed no shared chart-pushforward interface exists yet.

Scheduling: all subsequent checks use the atomic shared
`collaboration/CompileWithSlot.ps1`, one lean5 compiler, two total slots,
at least 6 GiB RAM. No old module audit or full build.

### 2026-10-28 audited actual reflected-plane variation

All 14 new declarations in the first four modules have now compiled and
passed the focused `S4VariationAudit.lean` audit: log
`collaboration/lean5/s4_variation_axioms.log`, EXIT0, every declaration has
only `[propext, Classical.choice, Quot.sound]`. Production logs:
`s4_variation3.log`, `s4_reflected3.log`, `s4_plane3.log`,
`s4_reflected_schwarzian1.log`, all EXIT0.

Main new reusable endpoint: `s4v_reflected_schwarzian_harmonic`, actual
`HasDerivAt` for the normalized plane solution with coefficient
`t * unitDisc.indicator (extA (toLinf ν))`, derivative
`-(conj (ν z) * rho z / 2)`. The general endpoint
`s4v_normalized_schwarzian_variation` works for any bounded measurable
coefficient off its support, with no harmonicity assumption.

No original S4 sorry is counted closed. The current active next lemma in
`S4ParameterJets` derives parameter holomorphy of a spatial directional
derivative from joint continuity of that spatial derivative; it uses
locally uniform difference quotients, not an assumed mixed derivative.
Full remaining interfaces are recorded in `lean5/S4_VARIATION_NEXT.md`.

### 2026-10-28 final verified checkpoint — 20 new standard-only declarations

`S4ParameterJets` production `s4_jets6.log` EXIT0; focused
`S4ParameterJetsAudit.lean` / `s4_parameter_jets_axioms.log` EXIT0:
all six new names use only propext, Classical.choice, Quot.sound.
Together with the previous 14, the five new source modules have no sorry,
new axiom, or set_option. The original S4 file remains unchanged, with none
of its original six open statements counted closed.

Most useful additional APIs:
`s4v_param_schwarzian_holomorphic` and
`s4v_schwarzian_joint_continuous`. The regularity gap discussed earlier is
resolved using locally uniform spatial difference quotients and the
installed WReg derivative-family machinery. It does not assume an extra
mixed derivative. Generic parameter spaces in the continuity wrapper are
Type 0, matching installed WReg and including ℂ and ℂ×ℂ.

Verified module sizes / MD5:

| Module | Lines | MD5 |
|---|---:|---|
| S4Variation | 94 | 47bd2ce06da29c417dab4069e773c0ab |
| S4ReflectedKernel | 93 | 1d1881104209bce9f48dcd76b1ce1e0e |
| S4PlaneVariation | 131 | ec595d2d5122cc9deac5e4c7fd523133 |
| S4ReflectedSchwarzian | 57 | 5d7b0340cedf0d0d42fffd1ed98a46d3 |
| S4ParameterJets | 191 | dec1dd3f6a1fd456563c12f5dfeb3ceb |

Next concrete work remains the actual Model A two-parameter coefficient
family and its Möbius-invariant dz-Schwarzian, then the general-base vε
coefficient/holomorphy bridge and the fixed auxiliary pole removal. See
`S4_VARIATION_NEXT.md` B–D; A is now implemented. No statement correction
was needed. No compiler or lean5 slot remains at this checkpoint. Do not
re-audit these 20 endpoints or rebuild their old dependencies on resume.

