import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Ch1.GroupChainCompleted
import TakhtajanTeo.Ch1.GroupCov
import TakhtajanTeo.Ch1.GroupBaseCompleted
import TakhtajanTeo.Ch1.GroupTopology
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.GroupTranslation

/-!
# Theorem 3.8: `T₀(1)` is a topological group (Module C)

`gtr_thm_3_8`: `(p, q) ↦ p * q⁻¹` is continuous on `T₀(1) × T₀(1)`. In the charts at `μ`, `ν` and `κ = μ * ν⁻¹`
(TT:2076–2082) the map is `(φ₁, φ₂) ↦ Λφ₁ * (κ * (Λφ₂)⁻¹ * κ⁻¹)`, so it is the composite of Lemma 3.7 (i)
(`gtr_inv_SM`), Corollary 3.6 at `κ` (`gtr_adjoint_SM`) and Lemma 3.7 (ii) (`gtr_mul_SM`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### The group `T(1)` on classes -/

theorem gtr_c_assoc (p q r : T1) : mulT (mulT p q) r = mulT p (mulT q r) := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  obtain ⟨c, rfl⟩ := Quotient.exists_rep r
  change mulT (mulT (Phi a) (Phi b)) (Phi c) = mulT (Phi a) (mulT (Phi b) (Phi c))
  rw [gtp_mulT_phi, gtp_mulT_phi, gtp_mulT_phi, gtp_mulT_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_mul_assoc a.2 b.2 c.2)

theorem gtr_c_inv_mul_rev (p q : T1) : invT (mulT p q) = mulT (invT q) (invT p) := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  change invT (mulT (Phi a) (Phi b)) = mulT (invT (Phi b)) (invT (Phi a))
  rw [gtp_mulT_phi, gtp_invT_phi, gtp_invT_phi, gtp_invT_phi, gtp_mulT_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_inv_mul_rev a.2 b.2)

theorem gtr_c_inv_mul_self (p : T1) : mulT (invT p) p = originT := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  change mulT (invT (Phi a)) (Phi a) = originT
  rw [gtp_invT_phi, gtp_mulT_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_inv_mul a.2)

theorem gtr_c_mul_one (p : T1) : mulT p originT = p := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  change mulT (Phi a) originT = Phi a
  unfold originT
  rw [gtp_mulT_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_mul_zero a.2)

/-! ### Charts at a general base point `κ ∈ 𝒪(𝔻*)₁` -/

theorem gtr_c_chart_mul (m : LinfStarBall) {φ : A2 unitDisc} (hφ : ‖φ‖ < Real.sqrt (π / 3)) :
    bersChartInv m (A2toAInf φ) =
      mulT (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) (Phi m) := by
  have hn : ‖A2toAInf φ‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 hφ)
  rw [gtp_chart0 φ hn, gtp_mulT_phi, ct_bersChartInv_eq hn, bt_rightTrans_phi]

theorem gtr_c_chart_zero (κ : LinfStarBall) : bersChartInv κ (A2toAInf (0 : A2 unitDisc)) = Phi κ := by
  have h0 : ‖(0 : A2 unitDisc)‖ < Real.sqrt (π / 3) := by
    rw [norm_zero]
    positivity
  rw [gtr_c_chart_mul κ h0, gtp_chart0_zero]
  unfold originT
  rw [gtp_mulT_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_zero_mul κ.2)

theorem gtr_c_chart_continuous {κ : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO) :
    Continuous[(inferInstance : TopologicalSpace (ball (0 : A2 unitDisc) (Real.sqrt (π / 3)))),
        hilbertTopology]
      (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) => bersChartInv κ (A2toAInf (φ : A2 unitDisc))) := by
  rw [continuous_iff_coinduced_le]
  unfold hilbertTopology
  exact le_iSup (fun μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO} =>
    TopologicalSpace.coinduced (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf (φ : A2 unitDisc))) inferInstance) ⟨κ, hκ⟩

theorem gtr_c_nhds {κ : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO) {W : Set T1}
    (hW : W ∈ @nhds T1 hilbertTopology (Phi κ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.sqrt (π / 3) ∧ ∀ φ : A2 unitDisc, ‖φ‖ < ε → bersChartInv κ (A2toAInf φ) ∈ W := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  obtain ⟨U, hUW, hUo, hU0⟩ := _root_.mem_nhds_iff.1 hW
  have hco : ContinuousOn (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_domRestrict.2 (gtr_c_chart_continuous hκ)
  have hpre := hco.isOpen_inter_preimage isOpen_ball hUo
  have h0mem : (0 : A2 unitDisc) ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∩
      (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) ⁻¹' U := by
    refine ⟨mem_ball_self hr0, ?_⟩
    show bersChartInv κ (A2toAInf (0 : A2 unitDisc)) ∈ U
    rw [gtr_c_chart_zero]
    exact hU0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0mem
  refine ⟨min ε (Real.sqrt (π / 3)), lt_min hε hr0, min_le_right _ _, fun φ hφ => ?_⟩
  have hφε : ‖φ‖ < ε := lt_of_lt_of_le hφ (min_le_left _ _)
  exact hUW (hball (mem_ball_zero_iff.2 hφε)).2

theorem gtr_c_image_mem {κ : LinfStarBall} (hκ : (κ : LinfStar) ∈ groupO) {δ : ℝ} (hδ : 0 < δ)
    (hδr : δ ≤ Real.sqrt (π / 3)) :
    (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) '' ball 0 δ ∈ @nhds T1 hilbertTopology (Phi κ) := by
  have hopen := glr_chart_image_open hκ (isOpen_ball (x := (0 : A2 unitDisc)) (ε := δ)) (ball_subset_ball hδr)
  exact @IsOpen.mem_nhds T1 hilbertTopology _ _ hopen ⟨0, mem_ball_self hδ, gtr_c_chart_zero κ⟩

/-- Product version of `gtr_continuousAt_chart`. -/
theorem gtr_continuousAt_chart_prod {κ₁ κ₂ κ' : LinfStarBall} (hκ₁ : (κ₁ : LinfStar) ∈ groupO)
    (hκ₂ : (κ₂ : LinfStar) ∈ groupO) (hκ' : (κ' : LinfStar) ∈ groupO) {f : T1 × T1 → T1}
    (h0 : f (Phi κ₁, Phi κ₂) = Phi κ')
    (hs : ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ₁ φ₂ : A2 unitDisc, ‖φ₁‖ < δ → ‖φ₂‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        f (bersChartInv κ₁ (A2toAInf φ₁), bersChartInv κ₂ (A2toAInf φ₂)) =
          bersChartInv κ' (A2toAInf φ')) :
    @ContinuousAt (T1 × T1) T1 (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology)
      hilbertTopology f (Phi κ₁, Phi κ₂) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  intro W hW
  rw [h0] at hW
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hεr, hεW⟩ := gtr_c_nhds hκ' hW
  obtain ⟨δ, hδ, hδr, hδ'⟩ := hs ε hε hεr
  have hnhds := prod_mem_nhds (gtr_c_image_mem hκ₁ hδ hδr) (gtr_c_image_mem hκ₂ hδ hδr)
  refine Filter.mem_of_superset hnhds ?_
  rintro ⟨_, _⟩ ⟨⟨φ₁, hφ₁, rfl⟩, ⟨φ₂, hφ₂, rfl⟩⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ₁ φ₂ (mem_ball_zero_iff.1 hφ₁) (mem_ball_zero_iff.1 hφ₂)
  show f _ ∈ W
  rw [he]
  exact hεW φ' hφ'

/-! ### Lemma 3.7 in the `SM` form -/

/-- Lemma 3.7 (i) in the `SM` form (small coordinates go to small coordinates); same proof as `gtp_lemma_3_7_inv`.
(Copy of the `gtp_continuousAt` argument body of `gtp_lemma_3_7_inv`, internal there.) -/
theorem gtr_inv_SM :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        invT (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) =
          bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ') := by
  have hd := delta0_bounds
  obtain ⟨C, hC, hch⟩ := gtp_chart_of_small hd.1.le hd.2
  intro ε hε hεr
  set K : ℝ := 1 / (1 - delta0) ^ 2 * Real.sqrt 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - delta0 := by linarith [hd.2]
    positivity
  refine ⟨min (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) (ε / (2 * C * K + 1)),
    ?_, ?_, fun φ hφ => ?_⟩
  · have hc0 : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
    exact lt_min (lt_min (by positivity) (div_pos (by linarith [hd.1]) hc0))
      (div_pos hε (by nlinarith [mul_nonneg hC.le hK0]))
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · have hφ1 : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) :=
      lt_of_lt_of_le hφ (min_le_left _ _)
    have hφ2 : ‖φ‖ < ε / (2 * C * K + 1) := lt_of_lt_of_le hφ (min_le_right _ _)
    obtain ⟨hn, hharm, hsm, hchart⟩ := gtp_small_a hφ1
    set a : LinfStarBall := ⟨Lambda (A2toAInf φ), Lambda_mem_ball hn⟩ with ha
    have hlip := gtp_lip_inv hharm hsm (l₁ := Lambda (A2toAInf φ)) (l₂ := 0) a.2
      (mem_ball_self one_pos)
    rw [grp_mul_inv a.2, grp_zero_mul (grp_inv_mem a.2), zero_sub, gtp_normL2_neg, sub_zero] at hlip
    have hL : normL2 unitDiscExterior (beltramiInv (a : LinfStar)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (2 * ‖φ‖) := by
      rw [← gtp_normL2_Lambda φ]
      exact hlip
    have hsmall : ENNReal.ofReal C * normL2 unitDiscExterior (beltramiInv (a : LinfStar)) <
        ENNReal.ofReal ε := by
      refine lt_of_le_of_lt (mul_le_mul' le_rfl hL) ?_
      refine gtp_ennreal_small1 hC.le hK0 (norm_nonneg _) ?_
      have h3 : ‖φ‖ * (2 * C * K + 1) < ε := by
        rwa [lt_div_iff₀ (by nlinarith [mul_nonneg hC.le hK0])] at hφ2
      nlinarith [norm_nonneg φ, mul_nonneg hC.le hK0]
    obtain ⟨φ', hφ', he⟩ := hch ⟨beltramiInv (a : LinfStar), grp_inv_mem a.2⟩ (by
        show ‖beltramiInv (a : LinfStar)‖ ≤ delta0
        exact ((bc_beltramiInv_norm_le a.2).trans hsm.le)) ε hε hεr hsmall
    refine ⟨φ', hφ', ?_⟩
    rw [hchart, gtp_invT_phi]
    exact he

/-- Lemma 3.7 (ii) in the `SM` form; same proof as `gtp_lemma_3_7_mul`.
(Copy of the `gtp_continuousAt_prod` argument body of `gtp_lemma_3_7_mul`, internal there.) -/
theorem gtr_mul_SM :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ₁ φ₂ : A2 unitDisc, ‖φ₁‖ < δ → ‖φ₂‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        mulT (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ₁))
            (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ₂)) =
          bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ') := by
  have hd := delta0_bounds
  have hc0 : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
  set k1 : ℝ := Real.sqrt (1 - (1 - delta0 ^ 2) ^ 2 / 4) with hk1def
  have hk10 : 0 ≤ k1 := Real.sqrt_nonneg _
  have hk11 : k1 < 1 := by
    rw [hk1def, Real.sqrt_lt' (by norm_num)]
    have : 0 < (1 - delta0 ^ 2) ^ 2 := by
      have : 0 < 1 - delta0 ^ 2 := by nlinarith [hd.1, hd.2]
      positivity
    nlinarith
  obtain ⟨C, hC, hch⟩ := gtp_chart_of_small hk10 hk11
  set K : ℝ := 1 / (1 - delta0) ^ 2 * Real.sqrt 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - delta0 := by linarith [hd.2]
    positivity
  intro ε hε hεr
  have hdpos : 0 < min (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)))
      (ε / (2 * C * K + 2 * C + 1)) :=
    lt_min (lt_min (by positivity) (div_pos (by linarith [hd.1]) hc0))
      (div_pos hε (by nlinarith [mul_nonneg hC.le hK0]))
  refine ⟨min (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) (ε / (2 * C * K + 2 * C + 1)),
    hdpos, (min_le_left _ _).trans (min_le_left _ _), fun φ₁ φ₂ hφ₁ hφ₂ => ?_⟩
  have hφ₁' : ‖φ₁‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) :=
    lt_of_lt_of_le hφ₁ (min_le_left _ _)
  have hφ₂' : ‖φ₂‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) :=
    lt_of_lt_of_le hφ₂ (min_le_left _ _)
  have hφ₁e : ‖φ₁‖ < ε / (2 * C * K + 2 * C + 1) := lt_of_lt_of_le hφ₁ (min_le_right _ _)
  have hφ₂e : ‖φ₂‖ < ε / (2 * C * K + 2 * C + 1) := lt_of_lt_of_le hφ₂ (min_le_right _ _)
  obtain ⟨hn₁, hharm₁, hsm₁, hchart₁⟩ := gtp_small_a hφ₁'
  obtain ⟨hn₂, hharm₂, hsm₂, hchart₂⟩ := gtp_small_a hφ₂'
  set a₁ : LinfStarBall := ⟨Lambda (A2toAInf φ₁), Lambda_mem_ball hn₁⟩ with ha₁
  set a₂ : LinfStarBall := ⟨Lambda (A2toAInf φ₂), Lambda_mem_ball hn₂⟩ with ha₂
  have hlam : beltramiMul (a₁ : LinfStar) (a₂ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball a₂.2 a₁.2
  have hsup : ‖beltramiMul (a₁ : LinfStar) (a₂ : LinfStar)‖ ≤ k1 := by
    refine (gtp_mul_norm_le a₂.2 a₁.2).trans (Real.sqrt_le_sqrt ?_)
    have h1 : ‖(a₂ : LinfStar)‖ ^ 2 ≤ delta0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsm₂.le 2
    have h2 : ‖(a₁ : LinfStar)‖ ^ 2 ≤ delta0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsm₁.le 2
    have h3 : 0 < 1 - delta0 ^ 2 := by nlinarith [hd.1, hd.2]
    have h4 : (1 - delta0 ^ 2) * (1 - delta0 ^ 2) ≤ (1 - ‖(a₂ : LinfStar)‖ ^ 2) * (1 - ‖(a₁ : LinfStar)‖ ^ 2) := by
      apply mul_le_mul <;> linarith
    nlinarith
  have hlip := gtp_lip_fwd hharm₂ hsm₂ (l₁ := (a₁ : LinfStar)) (l₂ := 0) a₁.2 (mem_ball_self one_pos)
  rw [grp_zero_mul a₂.2, sub_zero] at hlip
  have hL1 : normL2 unitDiscExterior (beltramiMul (a₁ : LinfStar) (a₂ : LinfStar) - (a₂ : LinfStar) : LinfStar) ≤
      ENNReal.ofReal K * ENNReal.ofReal (2 * ‖φ₁‖) := by
    rw [← gtp_normL2_Lambda φ₁]
    exact hlip
  have hL2 : normL2 unitDiscExterior (a₂ : LinfStar) = ENNReal.ofReal (2 * ‖φ₂‖) := gtp_normL2_Lambda φ₂
  have hL : normL2 unitDiscExterior (beltramiMul (a₁ : LinfStar) (a₂ : LinfStar)) ≤
      ENNReal.ofReal K * ENNReal.ofReal (2 * ‖φ₁‖) + ENNReal.ofReal (2 * ‖φ₂‖) := by
    refine (gtp_normL2_le_add_sub _ (a₂ : LinfStar)).trans ?_
    rw [hL2]
    exact add_le_add hL1 le_rfl
  have hsmall : ENNReal.ofReal C * normL2 unitDiscExterior
      (beltramiMul (a₁ : LinfStar) (a₂ : LinfStar)) < ENNReal.ofReal ε := by
    refine lt_of_le_of_lt (mul_le_mul' le_rfl hL) ?_
    refine gtp_ennreal_small hC.le hK0 (norm_nonneg _) (norm_nonneg _) ?_
    have hD : 0 < 2 * C * K + 2 * C + 1 := by nlinarith [mul_nonneg hC.le hK0]
    have e1 : ‖φ₁‖ * (2 * C * K + 2 * C + 1) < ε := by
      rwa [lt_div_iff₀ hD] at hφ₁e
    have e2 : ‖φ₂‖ * (2 * C * K + 2 * C + 1) < ε := by
      rwa [lt_div_iff₀ hD] at hφ₂e
    have ha : (2 * C * K) * (‖φ₁‖ * (2 * C * K + 2 * C + 1)) ≤ (2 * C * K) * ε :=
      mul_le_mul_of_nonneg_left e1.le (mul_nonneg (mul_nonneg (by norm_num) hC.le) hK0)
    have hb : (2 * C) * (‖φ₂‖ * (2 * C * K + 2 * C + 1)) < (2 * C) * ε :=
      mul_lt_mul_of_pos_left e2 (by linarith)
    have key : (C * (K * (2 * ‖φ₁‖) + 2 * ‖φ₂‖)) * (2 * C * K + 2 * C + 1) < ε * (2 * C * K + 2 * C + 1) := by
      nlinarith
    exact lt_of_mul_lt_mul_right key hD.le
  obtain ⟨φ', hφ', he⟩ := hch ⟨beltramiMul (a₁ : LinfStar) (a₂ : LinfStar), hlam⟩ hsup ε hε hεr hsmall
  refine ⟨φ', hφ', ?_⟩
  rw [hchart₁, hchart₂, gtp_mulT_phi]
  exact he

/-! ### Theorem 3.8 -/

/-- The chart form of the map `(p, q) ↦ p * q⁻¹` of Theorem 3.8 (TT:2076–2082): in the charts at `μ`, `ν` and
`κ = μ * ν⁻¹` it is `(φ₁, φ₂) ↦ Λφ₁ * (κ * (Λφ₂)⁻¹ * κ⁻¹)`. -/
theorem gtr_thm38_SM {μ ν : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO) (hν : (ν : LinfStar) ∈ groupO)
    (hμ2 : normL2 unitDiscExterior μ < ⊤) (hν2 : normL2 unitDiscExterior ν < ⊤) :
    ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ₁ φ₂ : A2 unitDisc, ‖φ₁‖ < δ → ‖φ₂‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        mulT (bersChartInv μ (A2toAInf φ₁)) (invT (bersChartInv ν (A2toAInf φ₂))) =
          bersChartInv ⟨beltramiMul (μ : LinfStar) (beltramiInv (ν : LinfStar)),
            bg_mul_mem_ball (grp_inv_mem ν.2) μ.2⟩ (A2toAInf φ') := by
  set κ : LinfStarBall := ⟨beltramiMul (μ : LinfStar) (beltramiInv (ν : LinfStar)),
    bg_mul_mem_ball (grp_inv_mem ν.2) μ.2⟩ with hκdef
  obtain ⟨hκO, hκ2⟩ := L2_inter_groupO_subgroup hμ hν hμ2 hν2
  have hK : Phi κ = mulT (Phi μ) (invT (Phi ν)) := by
    rw [gtp_invT_phi, gtp_mulT_phi]
  intro ε hε hεr
  obtain ⟨δ3, hδ3, hδ3r, hmul⟩ := gtr_mul_SM ε hε hεr
  obtain ⟨δ2, hδ2, hδ2r, had⟩ := gtr_adjoint_SM (μ := κ) hκO hκ2 δ3 hδ3 hδ3r
  obtain ⟨δ1, hδ1, hδ1r, hinv⟩ := gtr_inv_SM δ2 hδ2 hδ2r
  refine ⟨min δ1 δ3, lt_min hδ1 hδ3, (min_le_right _ _).trans hδ3r, fun φ₁ φ₂ hφ₁ hφ₂ => ?_⟩
  have hφ₁3 : ‖φ₁‖ < δ3 := lt_of_lt_of_le hφ₁ (min_le_right _ _)
  have hφ₂1 : ‖φ₂‖ < δ1 := lt_of_lt_of_le hφ₂ (min_le_left _ _)
  obtain ⟨ψ, hψ, hψe⟩ := hinv φ₂ hφ₂1
  obtain ⟨ψ', hψ', hψ'e⟩ := had ψ hψ
  obtain ⟨φ', hφ', hφ'e⟩ := hmul φ₁ ψ' hφ₁3 hψ'
  refine ⟨φ', hφ', ?_⟩
  set c := fun φ : A2 unitDisc => bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)
    with hc
  rw [gtr_c_chart_mul μ (hφ₁3.trans_le hδ3r), gtr_c_chart_mul ν (hφ₂1.trans_le hδ1r),
    gtr_c_chart_mul κ (hφ'.trans_le hεr), ← hφ'e, ← hψ'e, ← hψe, hK]
  -- `(A M)(B N)⁻¹ = (A ((M N⁻¹) B⁻¹ (M N⁻¹)⁻¹)) (M N⁻¹)`
  set A := c φ₁
  set B := c φ₂
  set K := mulT (Phi μ) (invT (Phi ν))
  rw [gtr_c_inv_mul_rev B (Phi ν), gtr_c_assoc A (mulT (mulT K (invT B)) (invT K)) K,
    gtr_c_assoc (mulT K (invT B)) (invT K) K, gtr_c_inv_mul_self K, gtr_c_mul_one,
    gtr_c_assoc A (Phi μ)]
  exact congrArg (mulT A) (gtr_c_assoc _ _ _).symm

/-- **Theorem 3.8** (TT:2068–2082), byte-identical copy of `thm_3_8`. -/
theorem gtr_thm_3_8 :
    @ContinuousOn _ _ (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology) hilbertTopology
      (fun pq : T1 × T1 => mulT pq.1 (invT pq.2)) (T01 ×ˢ T01) := by
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  obtain ⟨μ, hμ2, hμO, rfl⟩ := lemma_3_3 hp
  obtain ⟨ν, hν2, hνO, rfl⟩ := lemma_3_3 hq
  have hκ := L2_inter_groupO_subgroup hμO hνO hμ2 hν2
  have h0 : (fun pq : T1 × T1 => mulT pq.1 (invT pq.2)) (Phi μ, Phi ν) =
      Phi ⟨beltramiMul (μ : LinfStar) (beltramiInv (ν : LinfStar)), bg_mul_mem_ball (grp_inv_mem ν.2) μ.2⟩ := by
    show mulT (Phi μ) (invT (Phi ν)) = _
    rw [gtp_invT_phi, gtp_mulT_phi]
  have hca := gtr_continuousAt_chart_prod (f := fun pq : T1 × T1 => mulT pq.1 (invT pq.2)) hμO hνO hκ.1 h0
    (gtr_thm38_SM hμO hνO hμ2 hν2)
  exact @ContinuousAt.continuousWithinAt (T1 × T1) T1 (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology)
    hilbertTopology _ (T01 ×ˢ T01) (Phi μ, Phi ν) hca

/-- **Theorem 3.8** (TT:2068–2082). The Hilbert manifold `T₀(1)` is a topological group:
`([μ], [ν]) ↦ [μ * ν⁻¹]` is continuous on `T₀(1) × T₀(1)` (and `T₀(1)` is a subgroup, `lemma_3_4`). -/
theorem thm_3_8 :
    @ContinuousOn _ _ (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology) hilbertTopology
      (fun pq : T1 × T1 => mulT pq.1 (invT pq.2)) (T01 ×ˢ T01) :=
  gtr_thm_3_8

end TakhtajanTeo
