# Ranked list of the 66 open sorries (build 10215), 2026-10-28

Merged from collaboration/下属{1..6}/TRIAGE_R2_*.md. Estimates are lines of new proof. Risk L/M/H.

## A. Closable now (no open dependency)
| # | item | est | risk | owner-fit | note |
|---|---|---|---|---|---|
| 1 | lemma_5_5 (Ch1 S5) | 300-450 | M | 下属3 | then eq_5_3_5_4 cl.1 +150-250 (cl.2 suspected false, see D5) |
| 2 | tcCoord_chart (Ch1 S5) | 300-500 | M | 下属3 | needs a continuous local section of bers∘Phi |
| 3 | eq_4_1 (Ch2 S4) | 450-650 | M | 下属5 | opens the Ch2 S4 chain |
| 4 | remark_1_6 (Ch1 S1_2) | 600-1000 | M | 下属2 | W-REG removed the old wall |
| 5 | lemma_4_2 (Ch1 S4) | 700-1100 | M-H | 下属3 | missing step: w_z -> 1 in L²_loc |
| 6 | thm_2_10 (Ch2 S2) | 800-1300 | M | 下属4 | only after statement fix D4 |
| 7 | projector_kernel (Ch1 S8) | ~1500 | M | 下属5 | parked earlier by the user |

## B. Medium programs (unlock chains)
| item | est | risk | unlocks |
|---|---|---|---|
| symmetricT_spec (Ch2 S1) | 2-3.2k | H | all 4 Appendix B items: remark_B_9 (part 1 200-350, part 2 400-800), thm_B_4 (0.8-1.4k), lemma_B_2 (1.2-2k) |
| prop_3_9 (Ch1 S3) | 1.5-2.5k | H | — (old NO-GO lifted) |
| prop_5_1 (Ch2 S5) + fix D1 | 1.5-2.5k | H | cor_5_2 (150-250) -> cor_5_4 (30-60), remark_5_5 (50-100) |
| thm_4_1_variation (Ch2 S4), after eq_4_1 | 0.8-1.2k | H | thm_4_1 also needs Ch2 S3 + a chart-change wall (1.5-2.5k) |
| thm_5_10 -> cor_5_11 | 0.4-0.6k | M | gated by prop_5_7(ii) (W-HOL) |

## C. Large / NO-GO
- S7 remainder (10 items): 9-15k, roots high risk (F1 7_2-7_5 3.4-5.8k; F2 7_8/7_7'/7_9 4.2-7k; F3 7_11/7_12/7_14 1.3-2.3k).
- Ch2 S3 (8 items): 10-15k (W-FREDHOLM, W-APPROX, W-CONST); the 3 corollaries ~30 each once parents close.
- S8 chain: lemma_1_9 (Patterson) -> petersson_average -> lemma_8_2 -> lemma_8_4; thm_8_5 >= 2.5k; eq_8_1 after it.
- nag_sullivan 2.5-4k (W-H½), matAB_spec (needs it), remark_5_8, remark_4_4, remark_4_3 (W-ANA), lemma_5_1/thm_5_3/lemma_5_4/prop_5_7 (W-HOL, W-RT), componentT_spec, exists_realAnalytic_rep (then remark_1_2 +40), harmonicGamma_finiteDimensional, cor_A_4 (then cor_A_6 +200-350), wpPotential_spec / cor_4_2 / remark_4_3 (Ch2) after thm_4_1.

## D. Statement / definition decisions (user)
| id | item | problem | proposed fix |
|---|---|---|---|
| D1 | def kyns (Ch2 S5) | ∃ Z over all matrices with totalized tsums: not unique, can pick junk | add IsBoundedMat Z |
| D2 | realAnalyticBeltrami_subgroup (Ch1 S1_1) | FALSE: no analyticity at ∞, group law moves ∞ into 𝔻* (witness given) | require analyticity at ∞ |
| D3 | lemma_2_9 (Ch1 S2) | suspected FALSE: C independent of ‖λ‖∞ | use the installed restricted form (C depends on k) |
| D4 | thm_2_10 (Ch2 S2) | real tsum of a non-summable family is junk 0, so the statement is trivially true | sum in ℝ≥0∞ |
| D5 | eq_5_3_5_4 cl.2 (Ch1 S5) | suspected FALSE: C² on open sets doesn't control the coefficient tail | C² into weighted ℓ² / up to the boundary |
| D6 | S5 modelling (vkNormSqCoordOrigin) | UNSURE: may rest on the pre-correction lemma_1_5 | check before any S5 proof |
| D7 | thm_7_4 cl.1, cor_7_5 | true but junk-weak (no differentiability) | optional strengthening |
| D8 | thm_7_14 | strict R<0, memoir proves ≤ 0 | keep (+300 lines) or weaken |
