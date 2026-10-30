import TakhtajanTeo.Ch1.S2_HilbertManifold
import TakhtajanTeo.Ch1.BeltramiTranslation

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Charts and right translations (`ct_` prefix) -/

/-- `R_[μ] ∘ R_[l] = R_[l * μ]` on `T(1)`. -/
theorem ct_rightTrans_comp (l μ : LinfStarBall) (p : T1) :
    rightTrans μ (rightTrans l p) = rightTrans ⟨beltramiMul (l : LinfStar) μ, bg_mul_mem_ball μ.2 l.2⟩ p := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  change rightTrans μ (rightTrans l (Phi a)) = rightTrans _ (Phi a)
  rw [bt_rightTrans_phi, bt_rightTrans_phi, bt_rightTrans_phi]
  apply Quotient.sound
  intro z hz
  have e1 := congrFun (bc_wA_mul μ.2 (bg_mul_mem_ball l.2 a.2)).2.1 (z : ExtPlane)
  have e2 := congrFun (bc_wA_mul l.2 a.2).2.1 (wAS (μ : LinfStar) (z : ExtPlane))
  have e3 := congrFun (bc_wA_mul (bg_mul_mem_ball μ.2 l.2) a.2).2.1 (z : ExtPlane)
  have e4 := congrFun (bc_wA_mul μ.2 l.2).2.1 (z : ExtPlane)
  show finPart (wAS (beltramiMul (beltramiMul (a : LinfStar) l) μ) (z : ExtPlane)) =
    finPart (wAS (beltramiMul (a : LinfStar) (beltramiMul (l : LinfStar) μ)) (z : ExtPlane))
  rw [e1, e3]
  simp only [Function.comp_apply] at e2 e4 ⊢
  rw [e2, e4]

/-- The chart map `φ ↦ h̃_μ⁻¹(φ)` in terms of right translation of the Ahlfors–Weill section. -/
theorem ct_bersChartInv_eq {m : LinfStarBall} {φ : AInf unitDisc} (hφ : ‖φ‖ < 2) :
    bersChartInv m φ = rightTrans m (Phi ⟨Lambda φ, Lambda_mem_ball hφ⟩) := by
  rw [bt_rightTrans_phi]
  unfold bersChartInv
  rw [dif_pos (bg_mul_mem_ball m.2 (Lambda_mem_ball hφ))]

theorem ct_A2toAInf_norm_lt {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    ‖A2toAInf φ‖ < 2 := by
  have h1 := (A2toAInf_bounded.2 φ).1
  have h2 : ‖φ‖ < Real.sqrt (π / 3) := mem_ball_zero_iff.mp hφ
  have h3 : Real.sqrt (12 / π) * Real.sqrt (π / 3) = 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : 12 / π * (π / 3) = 2 ^ 2 := by field_simp; norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  have h4 : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.mpr (by positivity)
  calc ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := h1
    _ < Real.sqrt (12 / π) * Real.sqrt (π / 3) := by gcongr
    _ = 2 := h3

/-- **Corollary 2.12**, conditional on the Ahlfors–Weill identity `β ∘ Φ ∘ Λ = id` on the ball of radius `2`
(`ahlfors_weill`, S1_1). -/
theorem ct_cor_2_12
    (hAW : ∀ φ : AInf unitDisc, ‖φ‖ < 2 →
      ∃ h : Lambda φ ∈ LinfStarBall, bers (Phi ⟨Lambda φ, h⟩) = φ)
    (l μ : LinfStarBall) :
    ∃ h : beltramiMul l μ ∈ LinfStarBall,
      rightTrans μ '' hilbertChartDomain l = hilbertChartDomain ⟨_, h⟩ ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        hilbertChart ⟨_, h⟩ (rightTrans μ (bersChartInv l (A2toAInf φ))) = φ := by
  have h : beltramiMul (l : LinfStar) μ ∈ LinfStarBall := bg_mul_mem_ball μ.2 l.2
  refine ⟨h, ?_, ?_⟩
  · unfold hilbertChartDomain
    rw [Set.image_image]
    apply Set.image_congr
    intro φ hφ
    have hn := ct_A2toAInf_norm_lt hφ
    rw [ct_bersChartInv_eq hn, ct_bersChartInv_eq hn, ct_rightTrans_comp]
  · intro φ hφ
    have hn := ct_A2toAInf_norm_lt hφ
    -- injectivity of the chart map
    have hinj : InjOn (fun ψ : A2 unitDisc => bersChartInv ⟨_, h⟩ (A2toAInf ψ))
        (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) := by
      intro a ha b hb hab
      have hna := ct_A2toAInf_norm_lt ha
      have hnb := ct_A2toAInf_norm_lt hb
      simp only [] at hab
      rw [ct_bersChartInv_eq hna, ct_bersChartInv_eq hnb] at hab
      obtain ⟨hbi, -⟩ := bt_rightTrans_bijective ⟨_, h⟩
      have h0 := hbi.1 hab
      have h1 := congrArg bers h0
      obtain ⟨ha', hA⟩ := hAW _ hna
      obtain ⟨hb', hB⟩ := hAW _ hnb
      rw [hA, hB] at h1
      exact A2toAInf_injective h1
    unfold hilbertChart
    rw [ct_bersChartInv_eq hn, ct_rightTrans_comp, ← ct_bersChartInv_eq hn]
    exact hinj.leftInvOn_invFunOn hφ

end TakhtajanTeo
