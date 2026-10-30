# lean4 statement changes — 2026-10-28

No mathematical statement changes in the symmetricT_spec work.

- Original `TakhtajanTeo.Ch2.symmetricT_spec`: docstring and full statement retained verbatim; moved from `Ch2/S1_UnivalentFunctions.lean` to `Ch2/S1_SymmetricT.lean`, body `symt_symmetricT_spec`.
- No extra assumptions, definitions, axioms, or removed conclusions. Both boundary-decay directions and both subgroup assertions are proved.
- No executable consumers of the original name found before relocation. New Appendix B consumers belong to lean6; root integration belongs to lean1.
- All 20 new support declarations: `collaboration/lean4/symmetric-t-axioms.log`, EXIT0, each exactly `[propext, Classical.choice, Quot.sound]`.
- Original-name installation/audit complete: lower source export, final module export, and original audit all EXIT0. `collaboration/lean4/symmetric-t-original-axioms.log` reports exactly `[propext, Classical.choice, Quot.sound]`. Detailed final files/hashes are in `collaboration/lean4.md`.
