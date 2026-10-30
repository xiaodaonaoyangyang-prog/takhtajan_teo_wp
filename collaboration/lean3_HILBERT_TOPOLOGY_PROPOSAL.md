# Hilbert atlas topology: two-line correction proposal

Status: proposed, not applied. Date: 2026-10-24.

Owned source: `TakhtajanTeo/Ch1/S2_HilbertManifold.lean`.

The docstrings of `hilbertTopology` (TT:1844–1856) and `hilbertTopologyA`
(TT:1872) specify the finest topology making every inverse chart continuous.
Both current definitions use `⨅` over the coinduced topologies. Under Lean's
reverse topology order this is the wrong direction: continuity of every map
means each coinduced topology is ≤ the target, equivalently their `⨆` is ≤ it.

Proposed edits, and no other definition changes:

```diff
 def hilbertTopology : TopologicalSpace T1 :=
-  ⨅ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO},
+  ⨆ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO},
 ...
 def hilbertTopologyA : TopologicalSpace (AInf unitDisc) :=
-  ⨅ φ : AInf unitDisc, TopologicalSpace.coinduced (fun ψ : A2 unitDisc => φ + A2toAInf ψ) inferInstance
+  ⨆ φ : AInf unitDisc, TopologicalSpace.coinduced (fun ψ : A2 unitDisc => φ + A2toAInf ψ) inferInstance
```

Checked evidence: `collaboration/lean3_topology_check.lean`, exit 0, log
`collaboration/lean3_topology_check.log`. Both lemmas use only the standard three
axioms, no `sorryAx`:

1. `family_continuous_iff_iSup_coinduced_le`: the precise universal property.
2. `infimum_coinduced_chart_not_continuous`: for the two maps ℝ → ℝ × Bool,
   x ↦ (x,false) and x ↦ (x,true), the infimum construction makes the first map
   discontinuous. Its preimage of an open target singleton is the non-open
   real singleton {0}.

This is a verified counterexample to the generic infimum construction, not a
claim that a complete counterexample in the project's T1 quotient has already
been proved. The universal-property mismatch alone identifies the required edit.
The already-proved analytic A2 estimates do not use these topology definitions.

After approval: apply only these two edits, add the corresponding continuity and
universal-property interface lemmas, incrementally compile §2, and audit the new
interfaces. Existing dependent statements will be retained verbatim; no full rebuild.

## Stronger project-specific diagnosis (2026-10-25)

The actual current `hilbertTopologyA` has now been proved equal to the discrete
topology, not just shown to have the wrong generic universal property.
`collaboration/lean3_actual_topology_diagnostic.lean` compiled with exit 0;
both `current_hilbertTopologyA_is_discrete` and
`current_hilbertTopologyA_component_formula_false` have only
`[propext, Classical.choice, Quot.sound]`. Log:
`collaboration/lean3_actual_topology_diagnostic.log`.

The argument uses the newly proved double boundary pole `1/(1-z)^2`, which is in
AInf but not A2. For any point x, choose a chart whose affine A2 image misses x;
that chart's coinduced topology makes {x} open. The infimum therefore makes every
singleton open. Its connected components are singletons, contradicting the
claimed nontrivial affine A2 components. The nontrivial A2 witness is the constant
function 1. No unproved theorem or disputed topology theorem was used.

The two-line proposal remains unapplied pending explicit user approval.

## Corrected AInf specification prepared and verified

`collaboration/lean3_proposed_topology_spec.lean` defines a review-only
`proposedHilbertTopologyA` with `⨆`, leaving the original untouched. Its three
specification clauses are now proved:

- `proposedHilbertTopologyA_le`: finer than the Banach topology.
- `proposedHilbertTopologyA_component`: components are precisely affine A2 cosets.
- `proposedHilbertTopologyA_components_uncountable`: those components are uncountable.

The accompanying algebraic fiber lemma is also checked. All four declarations
have only `[propext, Classical.choice, Quot.sound]`; compilation exited 0 in
`collaboration/lean3_proposed_topology_spec.log`. Thus the complete content of
the original `hilbertTopologyA_spec` has a checked implementation for the proposed
definition. Approval is needed only for changing the two original mathematical
definitions and then integrating this prepared proof. The original specification
has not been replaced or weakened.
