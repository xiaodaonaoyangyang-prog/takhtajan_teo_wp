import TakhtajanTeo.Ch1.S2Cover_Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Block A: right translations and components (`ctb_` prefix) -/

/-- `R_[ν]` depends only on the class of `ν`. -/
theorem ctb_rightTrans_congr {ν ν' : LinfStarBall} (h : Phi ν = Phi ν') : rightTrans ν = rightTrans ν' := by
  funext p
  obtain ⟨l, rfl⟩ := Quotient.exists_rep p
  change rightTrans ν (Phi l) = rightTrans ν' (Phi l)
  rw [bt_rightTrans_phi, bt_rightTrans_phi]
  apply Quotient.sound
  intro z hz
  exact bc_beltramiMul_respects (fun _ _ => rfl) (Quotient.exact h) z hz

/-- Every class of `T(1)` has a representative in `𝒪(𝔻*)₁`. Mirrors the `hall : H = univ` step (clopen
argument) of `s2c_hilbertChartDomain_cover`, which is not exposed as a theorem. -/
theorem ctb_exists_groupO_rep (p : T1) :
    ∃ μ : LinfStarBall, (μ : LinfStar) ∈ groupO ∧ p = Phi μ := by
  set H : Set T1 := {p | ∃ μ : LinfStarBall, (μ : LinfStar) ∈ groupO ∧ p = Phi μ} with hHdef
  have hz0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hH0 : Phi ⟨0, hz0⟩ ∈ H := ⟨⟨0, hz0⟩, zero_mem_groupO, rfl⟩
  have hHmul : ∀ p ∈ H, ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO → rightTrans μ p ∈ H := by
    rintro p ⟨l, hl, rfl⟩ μ hμ
    exact ⟨⟨beltramiMul (l : LinfStar) μ, bg_mul_mem_ball μ.2 l.2⟩, groupO_mul_mem hl hμ,
      bt_rightTrans_phi μ l⟩
  set r : ℝ := 2 * delta0 with hr
  have hδ := delta0_bounds
  have hU : ∀ q : T1, ‖bers q‖ < r → ∃ a : LinfStarBall, (a : LinfStar) ∈ groupO ∧ q = Phi a := by
    intro q hq
    have hφ2 : ‖bers q‖ < 2 := by rw [hr] at hq; linarith [hδ.2]
    obtain ⟨h, hφq⟩ := ahlfors_weill hφ2
    refine ⟨⟨Lambda (bers q), h⟩, ?_, ?_⟩
    · exact groupO_mem_of_harmonic (Lambda_mem_harmonic _)
        (lt_of_le_of_lt (Lambda_norm_le _) (by rw [hr] at hq; linarith))
    · exact bers_injective (by rw [hφq])
  have hbers0 : bers (Phi ⟨0, hz0⟩) = 0 := by
    have h0 : Lambda (0 : AInf unitDisc) = 0 := by
      have := Lambda_smul 0 (0 : AInf unitDisc)
      simpa using this
    obtain ⟨h, hφ⟩ := ahlfors_weill (φ := (0 : AInf unitDisc)) (by simp)
    have : (⟨Lambda (0 : AInf unitDisc), h⟩ : LinfStarBall) = ⟨0, hz0⟩ := Subtype.ext h0
    rw [this] at hφ
    exact hφ
  have hNopen : ∀ ν : LinfStarBall, IsOpen {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := fun ν =>
    isOpen_lt (continuous_norm.comp (hc_bers_continuous.comp (hc_rightTrans_continuous _)))
      continuous_const
  have hNmem : ∀ ν : LinfStarBall, Phi ν ∈ {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := by
    intro ν
    have hi := bc_beltramiInv_mem_ball ν.2
    have e1 : Phi ν = rightTrans ν (Phi ⟨0, hz0⟩) := by
      rw [bt_rightTrans_phi]
      exact congrArg Phi (Subtype.ext (hb_zero_mul ν.2).symm)
    show ‖bers (rightTrans ⟨_, hi⟩ (Phi ν))‖ < r
    rw [e1, bt_rightTrans_inv_left ν hi, hbers0, norm_zero]
    rw [hr]; linarith [hδ.1]
  have hopen : IsOpen H := by
    rw [isOpen_iff_forall_mem_open]
    rintro q ⟨ν, hν, rfl⟩
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro q' hq'
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hqa⟩ := hU _ hq'
    have : q' = rightTrans ν (Phi a) := by
      rw [← hqa, bt_rightTrans_inv_right ν hi]
    rw [this]
    exact hHmul _ ⟨a, ha, rfl⟩ ν hν
  have hclosed : IsClosed H := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨ν, rfl⟩ := Quotient.exists_rep p
    change Phi ν ∉ H at hp
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro y hy hyH
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hya⟩ := hU _ hy
    obtain ⟨μ', hμ', hyμ⟩ := hyH
    have hy2 : y = Phi ⟨beltramiMul (a : LinfStar) ν, bg_mul_mem_ball ν.2 a.2⟩ := by
      have : y = rightTrans ν (rightTrans ⟨_, hi⟩ y) := (bt_rightTrans_inv_right ν hi y).symm
      rw [this, hya, bt_rightTrans_phi]
    have hcl := hc_left_cancel a ν μ' (by rw [← hyμ, hy2])
    apply hp
    refine ⟨⟨beltramiMul (beltramiInv (a : LinfStar)) (μ' : LinfStar),
      bg_mul_mem_ball μ'.2 (bc_beltramiInv_mem_ball a.2)⟩, ?_, hcl⟩
    exact groupO_mul_mem (groupO_inv_mem ha) hμ'
  have hconn : PreconnectedSpace T1 := by
    have hb : IsPreconnected (LinfStarBall : Set LinfStar) :=
      (convex_ball (0 : LinfStar) 1).isPreconnected
    have hb' : PreconnectedSpace LinfStarBall := isPreconnected_iff_preconnectedSpace.1 hb
    have hr : IsPreconnected (range (Phi : LinfStarBall → T1)) :=
      isPreconnected_range isQuotientMap_quotient_mk'.continuous
    have hrange : range (Phi : LinfStarBall → T1) = univ :=
      Set.range_eq_univ.2 (Quotient.mk_surjective (s := teichSetoid))
    exact ⟨hrange ▸ hr⟩
  have hall : H = univ := by
    have := hconn
    exact (show IsClopen H from ⟨hclosed, hopen⟩).eq_univ ⟨_, hH0⟩
  have hp : p ∈ H := by rw [hall]; trivial
  exact hp

/-- `R_[ν]` is continuous in the Hilbert manifold topology for `ν ∈ 𝒪(𝔻*)₁`
(`R_ν ∘ h̃_μ⁻¹ = h̃_{μ*ν}⁻¹`). -/
theorem ctb_rightTrans_continuous {ν : LinfStarBall} (hν : (ν : LinfStar) ∈ groupO) :
    @Continuous T1 T1 hilbertTopology hilbertTopology (rightTrans ν) := by
  unfold hilbertTopology
  rw [continuous_iSup_dom]
  intro μ
  rw [continuous_coinduced_dom]
  have hm : (beltramiMul (μ.1 : LinfStar) ν) ∈ LinfStarBall := bg_mul_mem_ball ν.2 μ.1.2
  have hmO : (beltramiMul (μ.1 : LinfStar) ν) ∈ groupO := groupO_mul_mem μ.2 hν
  have heq : rightTrans ν ∘ (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf φ)) =
      fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
        bersChartInv ⟨beltramiMul (μ.1 : LinfStar) ν, hm⟩ (A2toAInf φ) := by
    funext φ
    have hn := ct_A2toAInf_norm_lt φ.2
    simp only [Function.comp_apply]
    rw [ct_bersChartInv_eq hn, ct_rightTrans_comp,
      (ct_bersChartInv_eq (m := ⟨beltramiMul (μ.1 : LinfStar) ν, hm⟩) hn).symm]
  rw [heq]
  apply continuous_iff_coinduced_le.mpr
  exact le_iSup (fun μ' : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO} =>
    (TopologicalSpace.coinduced (fun φ : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ'.1 (A2toAInf φ)) inferInstance : TopologicalSpace T1))
    ⟨⟨beltramiMul (μ.1 : LinfStar) ν, hm⟩, hmO⟩

/-- For `ν ∈ 𝒪(𝔻*)₁`, `R_[ν]` maps components onto components. -/
theorem ctb_image_componentT {ν : LinfStarBall} (hν : (ν : LinfStar) ∈ groupO) (p : T1) :
    rightTrans ν '' componentT p = componentT (rightTrans ν p) := by
  have hi : beltramiInv (ν : LinfStar) ∈ LinfStarBall := bc_beltramiInv_mem_ball ν.2
  have hνi : ((⟨_, hi⟩ : LinfStarBall) : LinfStar) ∈ groupO := groupO_inv_mem hν
  letI : TopologicalSpace T1 := hilbertTopology
  let e : T1 ≃ₜ T1 :=
    { toFun := rightTrans ν
      invFun := rightTrans ⟨_, hi⟩
      left_inv := bt_rightTrans_inv_left ν hi
      right_inv := bt_rightTrans_inv_right ν hi
      continuous_toFun := ctb_rightTrans_continuous hν
      continuous_invFun := ctb_rightTrans_continuous hνi }
  apply Set.Subset.antisymm
  · exact e.continuous.image_connectedComponent_subset p
  · intro q hq
    have h1 := e.symm.continuous.image_connectedComponent_subset (rightTrans ν p) ⟨q, hq, rfl⟩
    refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
    have h2 : e.symm (rightTrans ν p) = p := e.symm_apply_apply p
    rwa [h2] at h1

/-- Conjunct 2 of `componentT_spec`, verbatim. -/
theorem ctb_componentT_spec_two :
    ∀ (p : T1) (ν : LinfStarBall), ∃ h : beltramiMul (Quotient.out p : LinfStarBall) ν ∈ LinfStarBall,
      rightTrans ν '' componentT p = componentT (Phi ⟨_, h⟩) := by
  intro p ν
  have h : beltramiMul (Quotient.out p : LinfStarBall) ν ∈ LinfStarBall :=
    bg_mul_mem_ball ν.2 (Quotient.out p).2
  refine ⟨h, ?_⟩
  obtain ⟨ν', hν', hp⟩ := ctb_exists_groupO_rep (Phi ν)
  have e1 : rightTrans ν = rightTrans ν' := ctb_rightTrans_congr hp
  have e2 : Phi ⟨_, h⟩ = rightTrans ν p := by
    have : rightTrans ν p = rightTrans ν (Phi (Quotient.out p)) := by
      rw [show Phi (Quotient.out p) = p from Quotient.out_eq p]
    rw [this, bt_rightTrans_phi]
  rw [e2, e1]
  exact ctb_image_componentT hν' p

end TakhtajanTeo
