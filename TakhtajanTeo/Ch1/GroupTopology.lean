import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Ch1.GroupChainCompleted
import TakhtajanTeo.Ch1.BersInjective
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.ComponentTBasics

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### Topology of `T(1)` near the origin, in the chart at `0` -/

theorem gtp_chart0 (φ : A2 unitDisc) (hn : ‖A2toAInf φ‖ < 2) :
    bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ) =
      Phi ⟨Lambda (A2toAInf φ), Lambda_mem_ball hn⟩ := by
  rw [ct_bersChartInv_eq hn, bt_rightTrans_phi]
  apply congrArg Phi
  exact Subtype.ext (grp_mul_zero (Lambda_mem_ball hn))

theorem gtp_chart0_zero :
    bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf (0 : A2 unitDisc)) = originT := by
  have hn : ‖A2toAInf (0 : A2 unitDisc)‖ < 2 := by
    rw [A2toAInf_zero, norm_zero]
    norm_num
  rw [gtp_chart0 0 hn]
  apply congrArg Phi
  refine Subtype.ext ?_
  show Lambda (A2toAInf (0 : A2 unitDisc)) = 0
  rw [A2toAInf_zero]
  exact glr_lambda_zero

theorem gtp_chart0_continuous :
    Continuous[(inferInstance : TopologicalSpace (ball (0 : A2 unitDisc) (Real.sqrt (π / 3)))),
        hilbertTopology]
      (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
        bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf (φ : A2 unitDisc))) := by
  rw [continuous_iff_coinduced_le]
  unfold hilbertTopology
  exact le_iSup (fun μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO} =>
    TopologicalSpace.coinduced (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf (φ : A2 unitDisc))) inferInstance) ⟨⟨0, mem_ball_self one_pos⟩, zero_mem_groupO⟩

theorem gtp_nhds_origin {W : Set T1} (hW : W ∈ @nhds T1 hilbertTopology originT) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.sqrt (π / 3) ∧ ∀ φ : A2 unitDisc, ‖φ‖ < ε →
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ) ∈ W := by
  letI : TopologicalSpace T1 := hilbertTopology
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  obtain ⟨U, hUW, hUo, hU0⟩ := _root_.mem_nhds_iff.1 hW
  have hco : ContinuousOn (fun φ : A2 unitDisc =>
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_restrict.2 gtp_chart0_continuous
  have hpre := hco.isOpen_inter_preimage isOpen_ball hUo
  have h0mem : (0 : A2 unitDisc) ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∩
      (fun φ : A2 unitDisc => bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) ⁻¹' U := by
    refine ⟨mem_ball_self hr0, ?_⟩
    show bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf (0 : A2 unitDisc)) ∈ U
    rw [gtp_chart0_zero]
    exact hU0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0mem
  refine ⟨min ε (Real.sqrt (π / 3)), lt_min hε hr0, min_le_right _ _, fun φ hφ => ?_⟩
  have hφε : ‖φ‖ < ε := lt_of_lt_of_le hφ (min_le_left _ _)
  exact hUW (hball (mem_ball_zero_iff.2 hφε)).2

theorem gtp_chart0_image_open {ε : ℝ} (hε : ε ≤ Real.sqrt (π / 3)) :
    @IsOpen T1 hilbertTopology
      ((fun φ : A2 unitDisc => bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) ''
        ball 0 ε) :=
  glr_chart_image_open (μ := ⟨0, mem_ball_self one_pos⟩) zero_mem_groupO isOpen_ball
    (ball_subset_ball hε)

/-- Continuity at the origin in the chart at `0`: if `f` fixes the origin and small chart points go to small
chart points, `f` is continuous at the origin. -/
theorem gtp_continuousAt {f : T1 → T1} (h0 : f originT = originT)
    (hs : ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ : A2 unitDisc, ‖φ‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        f (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) =
          bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ')) :
    @ContinuousAt T1 T1 hilbertTopology hilbertTopology f originT := by
  letI : TopologicalSpace T1 := hilbertTopology
  intro W hW
  rw [h0] at hW
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hεr, hεW⟩ := gtp_nhds_origin hW
  obtain ⟨δ, hδ, hδr, hδ'⟩ := hs ε hε hεr
  have hopen := gtp_chart0_image_open hδr
  have hmem : originT ∈ (fun φ : A2 unitDisc =>
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) '' ball 0 δ :=
    ⟨0, mem_ball_self hδ, gtp_chart0_zero⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ (mem_ball_zero_iff.1 hφ)
  show f _ ∈ W
  rw [he]
  exact hεW φ' hφ'

theorem gtp_continuousAt_prod {f : T1 × T1 → T1} (h0 : f (originT, originT) = originT)
    (hs : ∀ ε : ℝ, 0 < ε → ε ≤ Real.sqrt (π / 3) → ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt (π / 3) ∧
      ∀ φ₁ φ₂ : A2 unitDisc, ‖φ₁‖ < δ → ‖φ₂‖ < δ → ∃ φ' : A2 unitDisc, ‖φ'‖ < ε ∧
        f (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ₁),
            bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ₂)) =
          bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ')) :
    @ContinuousAt (T1 × T1) T1 (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology)
      hilbertTopology f (originT, originT) := by
  letI : TopologicalSpace T1 := hilbertTopology
  intro W hW
  rw [h0] at hW
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hεr, hεW⟩ := gtp_nhds_origin hW
  obtain ⟨δ, hδ, hδr, hδ'⟩ := hs ε hε hεr
  have hopen := gtp_chart0_image_open hδr
  have hmem : originT ∈ (fun φ : A2 unitDisc =>
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) '' ball 0 δ :=
    ⟨0, mem_ball_self hδ, gtp_chart0_zero⟩
  have hnhds := prod_mem_nhds (hopen.mem_nhds hmem) (hopen.mem_nhds hmem)
  refine Filter.mem_of_superset hnhds ?_
  rintro ⟨_, _⟩ ⟨⟨φ₁, hφ₁, rfl⟩, ⟨φ₂, hφ₂, rfl⟩⟩
  obtain ⟨φ', hφ', he⟩ := hδ' φ₁ φ₂ (mem_ball_zero_iff.1 hφ₁) (mem_ball_zero_iff.1 hφ₂)
  show f _ ∈ W
  rw [he]
  exact hεW φ' hφ'

/-! ### From a small `L²` Beltrami differential to a small chart coordinate -/

theorem gtp_chart_of_small {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : LinfStarBall, ‖(lam : LinfStar)‖ ≤ k → ∀ r : ℝ, 0 < r →
      r ≤ Real.sqrt (π / 3) →
      ENNReal.ofReal C * normL2 unitDiscExterior (lam : LinfStar) < ENNReal.ofReal r →
      ∃ φ' : A2 unitDisc, ‖φ'‖ < r ∧
        Phi lam = bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ') := by
  obtain ⟨C, hC, hcui⟩ := CUI.cui_A2_bound hk0 hk1
  refine ⟨C, hC, fun lam hk r hr hrs hsmall => ?_⟩
  have h1 := hcui lam hk
  have hfin : normA2 unitDisc (AInf.toFun (bersPhi lam)) < ENNReal.ofReal r :=
    lt_of_le_of_lt h1 hsmall
  have hA2 : AInf.toFun (bersPhi lam) ∈ A2fun unitDisc :=
    ⟨(bersPhi lam).2, hfin.trans ENNReal.ofReal_lt_top⟩
  have hcirc := ctb_A2toAInf_toA2 hA2
  set φ' : A2 unitDisc := toA2 unitDisc (AInf.toFun (bersPhi lam)) with hφ'
  have hnorm : (‖φ'‖₊ : ℝ≥0∞) = normA2 unitDisc (AInf.toFun (bersPhi lam)) := by
    rw [l29b_nnnorm_eq, hcirc]
  have hnr : ‖φ'‖ < r := by
    have : (‖φ'‖₊ : ℝ≥0∞) < ENNReal.ofReal r := by rw [hnorm]; exact hfin
    have h2 : ‖φ'‖₊ < r.toNNReal := ENNReal.coe_lt_coe.1 this
    have h3 : ((‖φ'‖₊ : ℝ≥0) : ℝ) < r := Real.lt_toNNReal_iff_coe_lt.1 h2
    simpa using h3
  refine ⟨φ', hnr, ?_⟩
  have hn2 : ‖A2toAInf φ'‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hnr hrs))
  rw [gtp_chart0 φ' hn2]
  apply bers_injective
  rw [bers_Phi]
  obtain ⟨h, hb⟩ := ahlfors_weill hn2
  rw [hb, hcirc]

/-! ### Algebra of classes and `L²` norms -/

theorem gtp_inv_zero : beltramiInv (0 : LinfStar) = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have h1 := grp_mul_inv h0
  rwa [grp_zero_mul (grp_inv_mem h0)] at h1

theorem gtp_invT_phi (a : LinfStarBall) :
    invT (Phi a) = Phi ⟨beltramiInv (a : LinfStar), grp_inv_mem a.2⟩ := by
  have h1 : invT (Phi a) = Phi ⟨beltramiInv (Quotient.out (Phi a) : LinfStarBall),
      grp_inv_mem (Quotient.out (Phi a) : LinfStarBall).2⟩ := by
    unfold invT
    exact dif_pos (grp_inv_mem (Quotient.out (Phi a) : LinfStarBall).2)
  rw [h1]
  exact Quotient.sound (grp_inv_respects (Quotient.mk_out (s := teichSetoid) a))

theorem gtp_mulT_eq (p q : T1) : mulT p q = rightTrans (Quotient.out q) p := by
  have hm : beltramiMul (Quotient.out p : LinfStarBall) (Quotient.out q : LinfStarBall) ∈ LinfStarBall :=
    bg_mul_mem_ball (Quotient.out q).2 (Quotient.out p).2
  unfold mulT rightTrans
  rw [dif_pos hm]

theorem gtp_mulT_phi (a b : LinfStarBall) :
    mulT (Phi a) (Phi b) = Phi ⟨beltramiMul (a : LinfStar) (b : LinfStar), bg_mul_mem_ball b.2 a.2⟩ := by
  rw [gtp_mulT_eq]
  have hb : Phi (Quotient.out (Phi b) : LinfStarBall) = Phi b := Quotient.out_eq (Phi b)
  rw [ctb_rightTrans_congr hb]
  exact bt_rightTrans_phi b a

theorem gtp_mul_norm_le {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ‖beltramiMul ν μ‖ ≤ Real.sqrt (1 - (1 - ‖μ‖ ^ 2) * (1 - ‖ν‖ ^ 2) / 4) :=
  norm_toLinf_le_of_ae_bound (Real.sqrt_nonneg _) (bg_mul_bound hμ hν)

theorem gtp_normL2_neg (x : LinfStar) : normL2 unitDiscExterior (-x : LinfStar) = normL2 unitDiscExterior x := by
  unfold normL2
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg x] with z hz
  rw [hz]
  simp

theorem gtp_normL2_add_le {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior)) :
    normL2 unitDiscExterior (fun z => f z + g z) ≤
      normL2 unitDiscExterior f + normL2 unitDiscExterior g := by
  have h1 := grp_normL2_eq unitDiscExterior (f := fun z => f z + g z) (hf.add hg)
  rw [h1, grp_normL2_eq _ hf, grp_normL2_eq _ hg]
  exact eLpNorm_add_le (f := f) (g := g) (by norm_num)

theorem gtp_normL2_le_add_sub (x y : LinfStar) :
    normL2 unitDiscExterior x ≤ normL2 unitDiscExterior (x - y : LinfStar) + normL2 unitDiscExterior y := by
  have hae : (x : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] fun z => (x - y : LinfStar) z + y z := by
    filter_upwards [Lp.coeFn_sub x y] with z hz
    rw [hz]
    simp
  rw [grp_normL2_congr_ae hae]
  exact gtp_normL2_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)

/-- The uniform `L²`-Lipschitz constant of right translation by a small harmonic differential. -/
theorem gtp_lip_fwd {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {l₁ l₂ : LinfStar}
    (h1 : l₁ ∈ LinfStarBall) (h2 : l₂ ∈ LinfStarBall) :
    normL2 unitDiscExterior (beltramiMul l₁ μ - beltramiMul l₂ μ : LinfStar) ≤
      ENNReal.ofReal (1 / (1 - delta0) ^ 2 * Real.sqrt 2) * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) :=
  grp_lip_gen (grp_mem_ball_of_lt_delta0 hδ) hδ.le delta0_bounds.2
    (fun F hF => grp_density_fwd hμ hδ hF) h1 h2

theorem gtp_lip_inv {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hδ : ‖μ‖ < delta0) {l₁ l₂ : LinfStar}
    (h1 : l₁ ∈ LinfStarBall) (h2 : l₂ ∈ LinfStarBall) :
    normL2 unitDiscExterior (beltramiMul l₁ (beltramiInv μ) - beltramiMul l₂ (beltramiInv μ) : LinfStar) ≤
      ENNReal.ofReal (1 / (1 - delta0) ^ 2 * Real.sqrt 2) * normL2 unitDiscExterior (l₁ - l₂ : LinfStar) := by
  have hb := grp_mem_ball_of_lt_delta0 hδ
  exact grp_lip_gen (grp_inv_mem hb) ((bc_beltramiInv_norm_le hb).trans hδ.le) delta0_bounds.2
    (fun F hF => grp_density_inv hμ hδ hF) h1 h2

theorem gtp_nnnorm_ofReal (x : A2 unitDisc) : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

theorem gtp_normL2_Lambda (φ : A2 unitDisc) :
    normL2 unitDiscExterior ⇑(Lambda (A2toAInf φ)) = ENNReal.ofReal (2 * ‖φ‖) := by
  rw [l29b_Lambda_L2, gtp_nnnorm_ofReal, ENNReal.ofReal_mul (by norm_num)]
  simp

theorem gtp_ennreal_small {C K s t r : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : C * (K * (2 * s) + 2 * t) < r) :
    ENNReal.ofReal C * (ENNReal.ofReal K * ENNReal.ofReal (2 * s) + ENNReal.ofReal (2 * t)) <
      ENNReal.ofReal r := by
  have hr : 0 < r := lt_of_le_of_lt (by positivity) h
  rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hC]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 h

theorem gtp_ennreal_small1 {C K s r : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (h : C * (K * (2 * s)) < r) :
    ENNReal.ofReal C * (ENNReal.ofReal K * ENNReal.ofReal (2 * s)) < ENNReal.ofReal r := by
  have hr : 0 < r := lt_of_le_of_lt (by positivity) h
  rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hC]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 h

/-! ### Small coordinates give small harmonic differentials -/

theorem gtp_small_a {φ : A2 unitDisc}
    (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    ∃ hn : ‖A2toAInf φ‖ < 2,
      Lambda (A2toAInf φ) ∈ harmonicBeltrami ∧ ‖Lambda (A2toAInf φ)‖ < delta0 ∧
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ) =
        Phi ⟨Lambda (A2toAInf φ), Lambda_mem_ball hn⟩ := by
  have hc0 : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
  have hd := delta0_bounds
  have h1 : ‖φ‖ < 2 * delta0 / Real.sqrt (12 / π) := lt_of_lt_of_le hφ (min_le_right _ _)
  have h2 : ‖A2toAInf φ‖ < 2 * delta0 := by
    have hb := (A2toAInf_bounded.2 φ).1
    calc ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := hb
      _ < Real.sqrt (12 / π) * (2 * delta0 / Real.sqrt (12 / π)) := by gcongr
      _ = 2 * delta0 := by field_simp
  have hn : ‖A2toAInf φ‖ < 2 := by linarith [hd.2]
  refine ⟨hn, Lambda_mem_harmonic _, ?_, gtp_chart0 φ hn⟩
  have := Lambda_norm_le (A2toAInf φ)
  linarith

/-! ### Lemma 3.7 -/

theorem gtp_lemma_3_7_inv :
    @ContinuousWithinAt _ _ hilbertTopology hilbertTopology invT T01 originT := by
  suffices hca : @ContinuousAt T1 T1 hilbertTopology hilbertTopology invT originT from
    @ContinuousAt.continuousWithinAt T1 T1 hilbertTopology hilbertTopology invT T01 originT hca
  have h0 : invT originT = originT := by
    unfold originT
    rw [gtp_invT_phi]
    apply congrArg Phi
    exact Subtype.ext gtp_inv_zero
  have hd := delta0_bounds
  obtain ⟨C, hC, hch⟩ := gtp_chart_of_small hd.1.le hd.2
  refine gtp_continuousAt h0 ?_
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
    have hainv : (⟨beltramiInv (a : LinfStar), grp_inv_mem a.2⟩ : LinfStarBall) ∈
        {lam : LinfStarBall | ‖(lam : LinfStar)‖ ≤ delta0} := by
      show ‖beltramiInv (a : LinfStar)‖ ≤ delta0
      exact ((bc_beltramiInv_norm_le a.2).trans hsm.le)
    -- the L² bound for the inverse
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

theorem gtp_lemma_3_7_mul :
    @ContinuousWithinAt _ _ (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology) hilbertTopology
      (fun pq : T1 × T1 => mulT pq.1 pq.2) (T01 ×ˢ T01) (originT, originT) := by
  suffices hca : @ContinuousAt (T1 × T1) T1 (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology)
      hilbertTopology (fun pq : T1 × T1 => mulT pq.1 pq.2) (originT, originT) from
    @ContinuousAt.continuousWithinAt (T1 × T1) T1 (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology)
      hilbertTopology (fun pq : T1 × T1 => mulT pq.1 pq.2) (T01 ×ˢ T01) (originT, originT) hca
  have h0 : (fun pq : T1 × T1 => mulT pq.1 pq.2) (originT, originT) = originT := by
    show mulT originT originT = originT
    unfold originT
    rw [gtp_mulT_phi]
    apply congrArg Phi
    exact Subtype.ext (grp_mul_zero (mem_ball_self one_pos))
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
  refine gtp_continuousAt_prod h0 ?_
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
  -- sup bound
  have hsup : ‖beltramiMul (a₁ : LinfStar) (a₂ : LinfStar)‖ ≤ k1 := by
    refine (gtp_mul_norm_le a₂.2 a₁.2).trans (Real.sqrt_le_sqrt ?_)
    have h1 : ‖(a₂ : LinfStar)‖ ^ 2 ≤ delta0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsm₂.le 2
    have h2 : ‖(a₁ : LinfStar)‖ ^ 2 ≤ delta0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsm₁.le 2
    have h3 : 0 < 1 - delta0 ^ 2 := by nlinarith [hd.1, hd.2]
    have h4 : (1 - delta0 ^ 2) * (1 - delta0 ^ 2) ≤ (1 - ‖(a₂ : LinfStar)‖ ^ 2) * (1 - ‖(a₁ : LinfStar)‖ ^ 2) := by
      apply mul_le_mul <;> linarith
    nlinarith
  -- L² bound
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
  show mulT _ _ = _
  rw [hchart₁, hchart₂, gtp_mulT_phi]
  exact he

/-- Prefixed copy of `lemma_3_7` (statement byte-identical): continuity of inverse and multiplication of
`T₀(1)` at the origin. -/
theorem gtp_lemma_3_7 :
    @ContinuousWithinAt _ _ hilbertTopology hilbertTopology invT T01 originT ∧
      @ContinuousWithinAt _ _ (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology) hilbertTopology
        (fun pq : T1 × T1 => mulT pq.1 pq.2) (T01 ×ˢ T01) (originT, originT) :=
  ⟨gtp_lemma_3_7_inv, gtp_lemma_3_7_mul⟩

/-- **Lemma 3.7** (TT:2048–2052).
- (i) The inverse `[μ] ↦ [μ⁻¹]` of `T₀(1)` is continuous at the origin.
- (ii) The multiplication `([μ], [ν]) ↦ [μ * ν]` of `T₀(1)` is continuous at the origin. -/
theorem lemma_3_7 :
    @ContinuousWithinAt _ _ hilbertTopology hilbertTopology invT T01 originT ∧
      @ContinuousWithinAt _ _ (@instTopologicalSpaceProd _ _ hilbertTopology hilbertTopology) hilbertTopology
        (fun pq : T1 × T1 => mulT pq.1 pq.2) (T01 ×ˢ T01) (originT, originT) :=
  gtp_lemma_3_7

end TakhtajanTeo
