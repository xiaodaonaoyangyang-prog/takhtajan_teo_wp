import TakhtajanTeo.Ch1.Lemma29Plane
import TakhtajanTeo.Ch1.GroupChain1
import TakhtajanTeo.Ch1.ComponentTC
import TakhtajanTeo.Ch1.GroupL2Representatives

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Classes having a representative at finite L2 distance from the fixed base coefficient. -/
def cst_L2leaf (μ : LinfStarBall) : Set T1 :=
  {p | ∃ ν : LinfStarBall, Phi ν = p ∧ normL2 unitDiscExterior (ν - μ : LinfStar) < ∞}

-- L1
theorem cst_bers_mul_sub_mem_A2 {μ ω : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hω : ω ∈ LinfStarBall) (hL : normL2 unitDiscExterior ω < ∞) :
    AInf.toFun (bersPhi (beltramiMul ω μ) - bersPhi μ) ∈ A2fun unitDisc := by
  let W := QCV.qcv_planeSolution μ
  let F := QCV.qcv_planeSolution (beltramiMul ω μ) ∘ Function.invFunOn W univ
  let ν := complexDilatation F
  let ρs : ℂ → ℝ := fun u =>
    (∫⁻ y in W '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4)).toReal
  obtain ⟨K, hF, hFs⟩ := l29b_F_qc hμ hω
  obtain ⟨hFΩ, hS⟩ := l29b_plane_schwarzian hμ hω
  have hfd := QCV.qcv_planeSolution_conformal hμ
  have hI : ∀ u ∈ interior ((W '' unitDisc)ᶜ),
      ∫⁻ y in W '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≤ ENNReal.ofReal (1 * ρs u) := by
    intro u hu
    simpa only [one_mul] using (ENNReal.ofReal_toReal (l29b_kernel_finite hμ hu)).ge
  have hcui := CUI.cui_disc_bound (norm_nonneg ω) (bc_norm_lt_one hω)
    (by norm_num : (0 : ℝ) ≤ 1) hfd.1 hfd.2.1 hF hFs hFΩ
    (l29b_qc_equation hF) (l29b_F_bound hμ hω) (l29b_plane_frontier_null hμ) ρs hI
  have hmass : (∫⁻ u in unitDiscExterior,
      (‖ω u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)) < ∞ := by
    simpa only [normL2, ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hL
  have hR : (∫⁻ u in (W '' unitDisc)ᶜ, (‖ν u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ρs u)) < ∞ := by
    refine lt_of_le_of_lt
      (le_trans (lintegral_mono fun u => mul_le_mul' le_rfl ENNReal.ofReal_toReal_le)
        (l29b_plane_energy hμ hω)) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass
  have hfin := lt_of_le_of_lt hcui (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR)
  refine ⟨(bersPhi (beltramiMul ω μ) - bersPhi μ).property, ?_⟩
  have he : normA2 unitDisc (AInf.toFun (bersPhi (beltramiMul ω μ) - bersPhi μ)) =
      (∫⁻ z in unitDisc, (‖schwarzianHol (F ∘ W) z - schwarzianHol W z‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (rho z)⁻¹) ^ (1 / 2 : ℝ) := by
    unfold normA2
    congr 1
    apply setLIntegral_congr_fun measurableSet_ball
    intro z hz
    beta_reduce
    rw [hS z hz]
  rw [he]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

-- L2, forward estimate
theorem cst_coeff_right_finite {κ μ ν : LinfStar} (hκ : κ ∈ groupO)
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hL : normL2 unitDiscExterior (ν - μ : LinfStar) < ∞) :
    normL2 unitDiscExterior (beltramiMul ν κ - beltramiMul μ κ : LinfStar) < ∞ := by
  obtain ⟨C, -, hC⟩ := grp_lemma_2_7 hκ
  exact lt_of_le_of_lt (hC ν hν μ hμ hL) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL)

theorem cst_mul_cancel_right {μ κ : LinfStar} (hμ : μ ∈ LinfStarBall) (hκ : κ ∈ LinfStarBall) :
    beltramiMul (beltramiMul μ κ) (beltramiInv κ) = μ := by
  rw [grp_mul_assoc hμ hκ (grp_inv_mem hκ), grp_mul_inv hκ, grp_mul_zero hμ]

-- L2
theorem cst_coeff_right_finite_iff {κ μ ν : LinfStar} (hκ : κ ∈ groupO)
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    normL2 unitDiscExterior (beltramiMul ν κ - beltramiMul μ κ : LinfStar) < ∞ ↔
      normL2 unitDiscExterior (ν - μ : LinfStar) < ∞ := by
  constructor
  · intro h
    have hk := l29b_groupO_ball hκ
    have hh := cst_coeff_right_finite (groupO_inv_mem hκ) (grp_mul_mem hμ hk) (grp_mul_mem hν hk) h
    simpa only [cst_mul_cancel_right hμ hk, cst_mul_cancel_right hν hk] using hh
  · exact cst_coeff_right_finite hκ hμ hν

-- L3
theorem cst_bers_sub_mem_of_coeff_L2 {μ ν : LinfStar} (hμ : μ ∈ groupO)
    (hν : ν ∈ LinfStarBall) (hL : normL2 unitDiscExterior (ν - μ : LinfStar) < ∞) :
    AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc := by
  have hμb := l29b_groupO_ball hμ
  have hωb := grp_mul_mem hν (grp_inv_mem hμb)
  have hωL := cst_coeff_right_finite (groupO_inv_mem hμ) hμb hν hL
  rw [grp_mul_inv hμb, sub_zero] at hωL
  have h := cst_bers_mul_sub_mem_A2 hμb hωb hωL
  rwa [grp_mul_assoc hν (grp_inv_mem hμb) hμb, grp_inv_mul hμb, grp_mul_zero hν] at h

-- L4, pointwise form
theorem cst_mem_L2leaf_right_iff (μ κ : LinfStarBall) (hκ : (κ : LinfStar) ∈ groupO) (p : T1) :
    rightTrans κ p ∈ cst_L2leaf ⟨beltramiMul (μ : LinfStar) κ, bg_mul_mem_ball κ.2 μ.2⟩ ↔
      p ∈ cst_L2leaf μ := by
  constructor
  · rintro ⟨η, hη, hηL⟩
    let ν : LinfStarBall := ⟨beltramiMul (η : LinfStar) (beltramiInv (κ : LinfStar)),
      grp_mul_mem η.2 (grp_inv_mem κ.2)⟩
    refine ⟨ν, ?_, ?_⟩
    · calc Phi ν = rightTrans ⟨_, grp_inv_mem κ.2⟩ (Phi η) :=
            (bt_rightTrans_phi ⟨_, grp_inv_mem κ.2⟩ η).symm
        _ = p := by rw [hη, bt_rightTrans_inv_left]
    · have hh := cst_coeff_right_finite (groupO_inv_mem hκ)
        (grp_mul_mem μ.2 κ.2) η.2 hηL
      simpa only [cst_mul_cancel_right μ.2 κ.2] using hh
  · rintro ⟨ν, hν, hνL⟩
    refine ⟨⟨beltramiMul (ν : LinfStar) κ, grp_mul_mem ν.2 κ.2⟩, ?_,
      cst_coeff_right_finite hκ μ.2 ν.2 hνL⟩
    rw [← hν]
    exact (bt_rightTrans_phi κ ν).symm

-- L4
theorem cst_right_L2leaf (μ κ : LinfStarBall) (hκ : (κ : LinfStar) ∈ groupO) :
    rightTrans κ '' cst_L2leaf μ =
      cst_L2leaf ⟨beltramiMul (μ : LinfStar) κ, bg_mul_mem_ball κ.2 μ.2⟩ := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (cst_mem_L2leaf_right_iff μ κ hκ p).mpr hp
  · intro hq
    obtain ⟨p, rfl⟩ := (bt_rightTrans_bijective κ).1.surjective q
    exact ⟨p, (cst_mem_L2leaf_right_iff μ κ hκ p).mp hq, rfl⟩

-- L5
theorem cst_image_L2leaf_subset_slice (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    bers '' cst_L2leaf μ ⊆
      {a | ∃ ψ : A2 unitDisc, a = bers (Phi μ) + A2toAInf ψ} ∩ range bers := by
  rintro a ⟨p, ⟨ν, hν, hL⟩, rfl⟩
  have hA := cst_bers_sub_mem_of_coeff_L2 hμ ν.2 hL
  rw [← bers_Phi ν, hν] at hA
  obtain ⟨ψ, hψ⟩ := ctc_mem_range.mp hA
  refine ⟨⟨ψ, ?_⟩, ⟨p, rfl⟩⟩
  rw [bers_Phi, hψ]
  abel

-- L6: the actual Bers differences before and after the same right translation.
theorem cst_bers_sub_pair_of_coeff_L2 {μ ν κ : LinfStar} (hμ : μ ∈ groupO)
    (hκ : κ ∈ groupO) (hν : ν ∈ LinfStarBall)
    (hL : normL2 unitDiscExterior (ν - μ : LinfStar) < ∞) :
    AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc ∧
      AInf.toFun (bersPhi (beltramiMul ν κ) - bersPhi (beltramiMul μ κ)) ∈ A2fun unitDisc := by
  exact ⟨cst_bers_sub_mem_of_coeff_L2 hμ hν hL,
    cst_bers_sub_mem_of_coeff_L2 (groupO_mul_mem hμ hκ)
      (grp_mul_mem hν (l29b_groupO_ball hκ))
      (cst_coeff_right_finite hκ (l29b_groupO_ball hμ) hν hL)⟩

-- L7: locate the true component inside the L2-representative leaf.
theorem cst_component_subset_L2leaf (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    componentT (Phi μ) ⊆ cst_L2leaf μ := by
  intro p hp
  rw [← grp_image_T01 μ] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  obtain ⟨ν, hνL, -, hνq⟩ := glr_lemma_3_3 hq
  have hL : normL2 unitDiscExterior ((ν : LinfStar) - 0 : LinfStar) < ∞ := by
    simpa only [sub_zero] using hνL
  have hR := cst_coeff_right_finite hμ (mem_ball_self one_pos) ν.2 hL
  rw [grp_zero_mul μ.2] at hR
  refine ⟨⟨beltramiMul (ν : LinfStar) μ, grp_mul_mem ν.2 μ.2⟩, ?_, hR⟩
  calc _ = rightTrans μ (Phi ν) := (bt_rightTrans_phi μ ν).symm
    _ = p := by rw [hνq]; exact hqp

end TakhtajanTeo
