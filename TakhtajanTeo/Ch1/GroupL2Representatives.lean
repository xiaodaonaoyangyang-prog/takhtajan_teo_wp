import TakhtajanTeo.Ch1.GroupChain1
import TakhtajanTeo.Ch1.ComponentTC
import TakhtajanTeo.Ch1.Lemma29Plane

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Classes admitting a square-integrable representative in the generated group. -/
def glr_good : Set T1 := {p | ∃ μ : LinfStarBall,
  normL2 unitDiscExterior μ < ∞ ∧ (μ : LinfStar) ∈ groupO ∧ Phi μ = p}

theorem glr_lambda_zero : Lambda (0 : AInf unitDisc) = 0 := by
  have h := Lambda_smul 0 (0 : AInf unitDisc)
  simpa using h

theorem glr_zero_l2 : normL2 unitDiscExterior (0 : LinfStar) < ∞ := by
  have h := l29b_Lambda_L2 (0 : A2 unitDisc)
  rw [A2toAInf_zero, glr_lambda_zero] at h
  simp only [nnnorm_zero, ENNReal.coe_zero, mul_zero] at h
  rw [h]
  exact ENNReal.zero_lt_top

theorem glr_inv_l2 {μ : LinfStar} (hμ : μ ∈ groupO)
    (hL : normL2 unitDiscExterior μ < ∞) : normL2 unitDiscExterior (beltramiInv μ) < ∞ := by
  have h := (grp_L2_inter_groupO_subgroup zero_mem_groupO hμ glr_zero_l2 hL).2
  rwa [grp_zero_mul (grp_inv_mem (l29b_groupO_ball hμ))] at h

theorem glr_mul_l2 {μ ν : LinfStar} (hμ : μ ∈ groupO) (hν : ν ∈ groupO)
    (hμL : normL2 unitDiscExterior μ < ∞) (hνL : normL2 unitDiscExterior ν < ∞) :
    normL2 unitDiscExterior (beltramiMul μ ν) < ∞ := by
  have h := (grp_L2_inter_groupO_subgroup hμ (groupO_inv_mem hν) hμL (glr_inv_l2 hν hνL)).2
  rwa [grp_inv_inv (l29b_groupO_ball hν)] at h

theorem glr_good_right {ν : LinfStarBall} (hν : (ν : LinfStar) ∈ groupO)
    (hνL : normL2 unitDiscExterior ν < ∞) {p : T1} (hp : p ∈ glr_good) :
    rightTrans ν p ∈ glr_good := by
  obtain ⟨μ, hμL, hμ, rfl⟩ := hp
  exact ⟨⟨beltramiMul (μ : LinfStar) ν, bg_mul_mem_ball ν.2 μ.2⟩,
    glr_mul_l2 hμ hν hμL hνL, groupO_mul_mem hμ hν, (bt_rightTrans_phi ν μ).symm⟩

theorem glr_good_cancel {ν : LinfStarBall} {p : T1} (hp : p ∈ glr_good)
    (hq : rightTrans ν p ∈ glr_good) : Phi ν ∈ glr_good := by
  obtain ⟨a, haL, ha, rfl⟩ := hp
  obtain ⟨c, hcL, hc, he⟩ := hq
  rw [bt_rightTrans_phi] at he
  have hcancel := hc_left_cancel a ν c he
  exact ⟨⟨beltramiMul (beltramiInv (a : LinfStar)) c,
    bg_mul_mem_ball c.2 (grp_inv_mem a.2)⟩,
    glr_mul_l2 (groupO_inv_mem ha) hc (glr_inv_l2 ha haL) hcL,
    groupO_mul_mem (groupO_inv_mem ha) hc, hcancel.symm⟩

/-- Open subsets of a Hilbert coordinate ball have open images, directly from
the proved transition maps and the final topology. No inverse function theorem. -/
theorem glr_chart_image_open {μ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    {U : Set (A2 unitDisc)} (hU : IsOpen U)
    (hUB : U ⊆ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    @IsOpen T1 hilbertTopology ((fun φ => bersChartInv μ (A2toAInf φ)) '' U) := by
  unfold hilbertTopology
  apply isOpen_iSup_iff.mpr
  intro ν
  rw [isOpen_coinduced]
  obtain ⟨hS, hT⟩ := ctc_one_side μ ν.1 hμ ν.2
  have hopen := hT.continuousOn.isOpen_inter_preimage hS hU
  have he : (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv ν.1 (A2toAInf φ)) ⁻¹' ((fun φ => bersChartInv μ (A2toAInf φ)) '' U) =
      Subtype.val ⁻¹' ((hilbertChart ν.1 '' (hilbertChartDomain μ ∩ hilbertChartDomain ν.1)) ∩
        (fun φ => hilbertChart μ (bersChartInv ν.1 (A2toAInf φ))) ⁻¹' U) := by
    ext φ
    constructor
    · rintro ⟨ψ, hψ, heq⟩
      dsimp only at heq
      refine ⟨(ctc_image_iff μ ν.1 φ).mpr ⟨φ.2, ψ, hUB hψ, heq⟩, ?_⟩
      change hilbertChart μ (bersChartInv ν.1 (A2toAInf φ)) ∈ U
      rw [← heq, ctc_chart_left_inv μ ψ (hUB hψ)]
      exact hψ
    · rintro ⟨hφ, hψ⟩
      obtain ⟨ψ, hψB, heq⟩ := ((ctc_image_iff μ ν.1 φ).mp hφ).2
      refine ⟨ψ, ?_, heq⟩
      change hilbertChart μ (bersChartInv ν.1 (A2toAInf φ)) ∈ U at hψ
      rwa [← heq, ctc_chart_left_inv μ ψ hψB] at hψ
  rw [he]
  exact hopen.preimage continuous_subtype_val

/-- A small Ahlfors--Weill coordinate neighbourhood consists of good classes. -/
theorem glr_good_neighbourhood : ∃ U : Set T1,
    @IsOpen T1 hilbertTopology U ∧ originT ∈ U ∧ U ⊆ glr_good := by
  let z : LinfStarBall := ⟨0, mem_ball_self one_pos⟩
  let B : Set (A2 unitDisc) := ball 0 (Real.sqrt (π / 3)) ∩
    {φ | ‖A2toAInf φ‖ < 2 * delta0}
  have hBo : IsOpen B := isOpen_ball.inter
    (isOpen_lt (continuous_norm.comp A2toAInfCLM.continuous) continuous_const)
  have hB0 : (0 : A2 unitDisc) ∈ B := by
    refine ⟨mem_ball_self (by positivity), ?_⟩
    simp only [mem_setOf_eq, A2toAInf_zero, norm_zero]
    linarith [delta0_bounds.1]
  refine ⟨(fun φ => bersChartInv z (A2toAInf φ)) '' B,
    glr_chart_image_open zero_mem_groupO hBo inter_subset_left, ?_, ?_⟩
  · refine ⟨0, hB0, ?_⟩
    change bersChartInv z (A2toAInf 0) = originT
    rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
    apply congrArg Phi
    apply Subtype.ext
    exact (congrArg (fun a => beltramiMul a 0) glr_lambda_zero).trans (grp_mul_zero z.2)
  · rintro p ⟨φ, hφ, rfl⟩
    have hn := ct_A2toAInf_norm_lt hφ.1
    have hl := Lambda_mem_ball hn
    have hsmall : ‖A2toAInf φ‖ < 2 * delta0 := hφ.2
    have hO : Lambda (A2toAInf φ) ∈ groupO :=
      groupO_mem_of_harmonic (Lambda_mem_harmonic _)
        (lt_of_le_of_lt (Lambda_norm_le _) (by linarith only [hsmall]))
    have hL : normL2 unitDiscExterior (Lambda (A2toAInf φ)) < ∞ := by
      rw [l29b_Lambda_L2]
      exact ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top
    refine ⟨⟨Lambda (A2toAInf φ), hl⟩, hL, hO, ?_⟩
    dsimp only
    rw [ct_bersChartInv_eq hn, bt_rightTrans_phi]
    apply congrArg Phi
    exact Subtype.ext (grp_mul_zero hl).symm

theorem glr_right_image_open {ν : LinfStarBall} (hν : (ν : LinfStar) ∈ groupO)
    {U : Set T1} (hU : @IsOpen T1 hilbertTopology U) :
    @IsOpen T1 hilbertTopology (rightTrans ν '' U) := by
  letI : TopologicalSpace T1 := hilbertTopology
  have he : rightTrans ν '' U = (rightTrans ⟨_, grp_inv_mem ν.2⟩) ⁻¹' U := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [mem_preimage, bt_rightTrans_inv_left] using hq
    · intro hp
      exact ⟨_, hp, bt_rightTrans_inv_right ν (grp_inv_mem ν.2) p⟩
  rw [he]
  exact hU.preimage (ctb_rightTrans_continuous (groupO_inv_mem hν))

theorem glr_good_clopen : @IsClopen T1 hilbertTopology glr_good := by
  letI : TopologicalSpace T1 := hilbertTopology
  obtain ⟨U, hU, hU0, hUG⟩ := glr_good_neighbourhood
  have ho : IsOpen glr_good := by
    rw [isOpen_iff_forall_mem_open]
    rintro p ⟨ν, hνL, hν, rfl⟩
    refine ⟨rightTrans ν '' U, ?_, glr_right_image_open hν hU, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact glr_good_right hν hνL (hUG hq)
    · exact ⟨originT, hU0, grp_rightTrans_origin ν⟩
  refine ⟨?_, ho⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨ν, hν, rfl⟩ := ctb_exists_groupO_rep p
  refine ⟨rightTrans ν '' U, ?_, glr_right_image_open hν hU, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩ hbad
    exact hp (glr_good_cancel (hUG hq) hbad)
  · exact ⟨originT, hU0, grp_rightTrans_origin ν⟩

/-- **Lemma 3.3** (TT:1932). Every `[μ] ∈ T₀(1)` has a representative `μ ∈ L²(𝔻*, ρ d²z) ∩ 𝒪(𝔻*)₁`. -/
theorem glr_lemma_3_3 {p : T1} (hp : p ∈ T01) :
    ∃ μ : LinfStarBall, normL2 unitDiscExterior μ < ∞ ∧ (μ : LinfStar) ∈ groupO ∧ Phi μ = p := by
  letI : TopologicalSpace T1 := hilbertTopology
  have h0 : originT ∈ glr_good :=
    ⟨⟨0, mem_ball_self one_pos⟩, glr_zero_l2, zero_mem_groupO, rfl⟩
  exact glr_good_clopen.connectedComponent_subset h0 hp

end TakhtajanTeo
