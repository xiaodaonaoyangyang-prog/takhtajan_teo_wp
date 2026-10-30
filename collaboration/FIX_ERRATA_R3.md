# Round 3 (2026-10-28, user-approved): statement fixes D1-D7, then the project-vs-paper catalogue

User decision: fix D1-D7 as proposed in RANKED_R2.md §D; D8 (thm_7_14) KEEPS strict negativity (no change).
Then collect every difference between our statements and the memoir, and mark the places where the memoir is wrong.

## Part 1. Statement fixes (draft only; the leader applies them and builds once)
Deliver to the leader, per fix: the exact OLD and NEW text (docstring + statement / def), with a docstring note
`[CORRECTION 2026-10-28, user-approved] <one-sentence reason>`; the list of consumers (`grep -rnw <name> TakhtajanTeo`)
and whether each consumer's proof still goes through unchanged; a scratch compile check (a scratch file importing the
module's imports, containing the NEW statement with `sorry`, `lake env lean` EXIT 0; one Lean process, FIFO slot).
Do not edit TakhtajanTeo/.
- D1 下属6: `def kyns` (Ch2/S5_PeriodMapping:540): add `IsBoundedMat Z` to the existential.
- D2 下属2: `realAnalyticBeltrami` (Ch1/S1_1:3255): require analyticity at ∞ (of the ι-pullback as a (−1,1)-form).
  Check exists_realAnalytic_rep and remark_1_2 stay true and their consumers are unaffected.
- D3 下属2: `lemma_2_9` (Ch1/S2): replace by the restricted form (constant depending on k), matching `l29r_restricted`
  (Ch1/Lemma29Restricted). If l29r_restricted proves the new statement verbatim, say so: then lemma_2_9 closes by relocation.
- D4 下属4: `thm_2_10` (Ch2/S2_Grunsky:2370): sum in ℝ≥0∞ (`∑' q, (‖…‖₊ : ℝ≥0∞) ^ 2 → 0`).
- D5 下属3: `eq_5_3_5_4` clause 2 (Ch1/S5): C² into the weighted ℓ² (or up to the boundary) — pick the form TT's proof uses;
  give the counterexample to the current clause 2 in the docstring note.
- D6 下属3 (consult 下属2 on the corrected lemma_1_5): check whether the S5 setup (`vkNormSqCoordOrigin`, thm_5_3 cl.2,
  prop_5_7(i)) rests on the pre-correction lemma_1_5. If it does, draft the fix; if not, report "no change".
- D7 下属1: `thm_7_4` clause 1 and `cor_7_5` (Ch1/S7): add the DifferentiableAt conjunct (as in p71_prop_7_1U).

## Part 2. Catalogue of differences from the memoir (read-only; after Part 1)
Source: ../Weil–Petersson metric on the universal Teichmüller space/source/TakhtajanTeo2006.md (cite TT:<line>).
Scan every docstring in your area (CORRECTION / misprint / OCR / user-approved / removable value / junk notes),
LEADER.md ("Corrections applied by the leader", later log lines) and your own memory/notes. Write
collaboration/<you>/DIFF_<you>.md with one row per difference:
`id | item (Lean name, file) | TT:line(s) | what the memoir says (short paraphrase, no long quotes) | what we state | class | why`
Classes:
- **P** the memoir is wrong (false claim, misprint, wrong constant/sign/holomorphy, OCR error in the source text) — say exactly what is wrong and the correct version;
- **H** a hypothesis/normalization the memoir uses implicitly or omits (e.g. Jordan domain, smoothness of μ, h ≠ 0);
- **F** formalization only (junk-value guards, removable values, sphere vs plane maps, ENat ⊤, a.e. classes, PV made explicit) — the memoir is fine.
Keep paraphrases short (no copying of long passages).

Areas:
- 下属1: Ch1 §6–§7 (S6*, S7*, S7First, S7Eq74, S7Prop71) + Basic.lean
- 下属2: Ch1 §1.1–§1.3 (S1_1*, S1_2*, S1_3*, TCurve*, Homogeneous*, Eq19*, Model A/B), §2, §3
- 下属3: Ch1 §1.4–§1.5 (S1_4*, S1_5*, Eq124General, L613, L112, WRegFoundation), §4, §5
- 下属4: Ch2 §1–§3
- 下属5: Ch1 §8, Ch2 §4, Appendix A
- 下属6: Ch2 §5, Appendix B
The leader merges these into collaboration/ERRATA.md and an annotated copy of the memoir with markers at the wrong places.
