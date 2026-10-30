# Program F (user-funded 2026-10-28): RANKED_R2.md section A, "closable now"

Budget: ~4.6-6.5k total; hard stop 9k, report at 7k. Per item: stop = 1.5 x the upper estimate.
Workflow per item: INTERFACE (frozen stubs + assembly, host module, prefix) -> leader audit -> prove -> deliver host + md5.
All relocations (including S1_2/S4/S5 originals) are batched into ONE round-end build. Max 2 worker Lean slots (FIFO);
check `tasklist | grep -c lean` before launching (fewer than 2 worker lean processes). Usual rules (frozen statements,
no set_option / new defs / lemma / private / attributes, standard axioms only, no pattern-matching binders).

| # | item | file | owner | est | stop | host / prefix | notes (R2 triage) |
|---|---|---|---|---|---|---|---|
| 1 | lemma_5_5 | Ch1/S5_ChernForms | 下属3 | 300-450 | 675 | Ch1/L55 / l55_ (imports Ch2.S2_Mixed) | mg_gap_green, ab6_*, qc null images |
| 2 | tcCoord_chart | Ch1/S5_ChernForms | 下属3 (after 1) | 300-500 | 750 | Ch1/TcChart / tcc_ | continuous local section of bers∘Phi |
| 3 | eq_4_1 | Ch2/S4_WPPotential | 下属5 | 450-650 | 975 | Ch2/S4Eq41 / e41_ | wA(beltramiMul(εν,κ)) = wA(εν)∘wA κ, welding identity, ∂_z-Schwarzian chain rules, W-REG model A |
| 4 | remark_1_6 | Ch1/S1_2_Homogeneous | 下属2 | 600-1000 | 1500 | Ch1/Remark16 / r16_ | W-REG D2b wr_ns2_z_regular for C³ near 0, lemma_1_5 machinery |
| 5 | lemma_4_2 | Ch1/S4_Metrics | 下属1 | 700-1100 | 1650 | Ch1/L42 / l42_ | lemma_2_5/cor_2_6; missing step w_z -> 1 in L²_loc (R(μ,κ) -> μ in L²(ρ)) |
| 6 | thm_2_10 (fixed, ℝ≥0∞) | Ch2/S2_Grunsky | 下属4 | 800-1300 | 1950 | Ch2/S2Thm210 / t210_ (below B1Entries: import cycle) | b1_entries holomorphy + local uniform HS bound (gk_*), Cauchy estimate (2.10) |
| 7 | projector_kernel | Ch1/S8_FiniteDimensional | 下属6 | ~1500 | 2250 | Ch1/ProjKernel / pk_ | 下属5's R2 notes (constant 12/π rechecked); 下属5 advises |
