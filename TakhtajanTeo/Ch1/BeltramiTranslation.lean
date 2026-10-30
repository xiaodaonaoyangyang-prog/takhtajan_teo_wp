import TakhtajanTeo.Ch1.BeltramiGroup

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Right translations on `T(1)` (`bt_` prefix) -/

/-- `R_[μ]` on the class of `l` is the class of `l * μ`. -/
theorem bt_rightTrans_phi (μ l : LinfStarBall) :
    rightTrans μ (Phi l) = Phi ⟨beltramiMul (l : LinfStar) μ, bg_mul_mem_ball μ.2 l.2⟩ := by
  have hm : beltramiMul (Quotient.out (Phi l) : LinfStarBall) μ ∈ LinfStarBall :=
    bg_mul_mem_ball μ.2 (Quotient.out (Phi l)).2
  unfold rightTrans
  rw [dif_pos hm]
  apply Quotient.sound
  intro z hz
  exact bc_beltramiMul_respects (Quotient.mk_out (s := teichSetoid) l) (fun _ _ => rfl) z hz

/-- Left inverse: `R_[μ⁻¹] ∘ R_[μ] = id`. -/
theorem bt_rightTrans_inv_left (μ : LinfStarBall) (h : beltramiInv (μ : LinfStar) ∈ LinfStarBall)
    (p : T1) : rightTrans ⟨_, h⟩ (rightTrans μ p) = p := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep p
  change rightTrans ⟨_, h⟩ (rightTrans μ (Phi l)) = Phi l
  rw [bt_rightTrans_phi, bt_rightTrans_phi]
  apply Quotient.sound
  intro z hz
  have h1 := congrFun (bc_wA_mul h (bg_mul_mem_ball μ.2 l.2)).2.1 (z : ExtPlane)
  have h2 := congrFun (bc_wA_mul μ.2 l.2).2.1 (wAS (beltramiInv (μ : LinfStar)) (z : ExtPlane))
  have h3 := bg_inverse_right_sphere μ.2 (z : ExtPlane)
  show finPart (wAS (beltramiMul (beltramiMul (l : LinfStar) μ) (beltramiInv (μ : LinfStar))) (z : ExtPlane)) =
    finPart (wAS (l : LinfStar) (z : ExtPlane))
  rw [h1]
  simp only [Function.comp_apply] at h2 ⊢
  rw [h2, h3]

/-- Right inverse: `R_[μ] ∘ R_[μ⁻¹] = id`. -/
theorem bt_rightTrans_inv_right (μ : LinfStarBall) (h : beltramiInv (μ : LinfStar) ∈ LinfStarBall)
    (p : T1) : rightTrans μ (rightTrans ⟨_, h⟩ p) = p := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep p
  change rightTrans μ (rightTrans ⟨_, h⟩ (Phi l)) = Phi l
  rw [bt_rightTrans_phi, bt_rightTrans_phi]
  apply Quotient.sound
  intro z hz
  have h1 := congrFun (bc_wA_mul μ.2 (bg_mul_mem_ball h l.2)).2.1 (z : ExtPlane)
  have h2 := congrFun (bc_wA_mul h l.2).2.1 (wAS (μ : LinfStar) (z : ExtPlane))
  have h3 := bg_inverse_left_sphere μ.2 (z : ExtPlane)
  show finPart (wAS (beltramiMul (beltramiMul (l : LinfStar) (beltramiInv (μ : LinfStar))) μ) (z : ExtPlane)) =
    finPart (wAS (l : LinfStar) (z : ExtPlane))
  rw [h1]
  simp only [Function.comp_apply] at h2 ⊢
  rw [h2, h3]

/-- Part (a) and the identity of part (c) of `rightTrans_biholomorphic`. -/
theorem bt_rightTrans_bijective (μ : LinfStarBall) :
    Function.Bijective (rightTrans μ) ∧
      ∃ h : beltramiInv (μ : LinfStar) ∈ LinfStarBall,
        rightTrans ⟨_, h⟩ ∘ rightTrans μ = id := by
  have h : beltramiInv (μ : LinfStar) ∈ LinfStarBall := bc_beltramiInv_mem_ball μ.2
  refine ⟨⟨?_, ?_⟩, h, funext (bt_rightTrans_inv_left μ h)⟩
  · intro a b hab
    have := congrArg (rightTrans ⟨_, h⟩) hab
    rwa [bt_rightTrans_inv_left μ h, bt_rightTrans_inv_left μ h] at this
  · intro q
    exact ⟨rightTrans ⟨_, h⟩ q, bt_rightTrans_inv_right μ h q⟩

end TakhtajanTeo
