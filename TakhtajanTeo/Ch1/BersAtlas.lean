import TakhtajanTeo.Ch1.BersAtlasPartial
import TakhtajanTeo.Ch1.BersInjective

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Transition maps of the Bers atlas (`ba_` prefix), given injectivity of `β` -/

/-- The transition map `ψ ↦ β(R_{μ⁻¹}(h_ν⁻¹ ψ))`, as an explicit holomorphic expression. -/
theorem ba_T_diff (μ ν : LinfStarBall) :
    DifferentiableOn ℂ (fun ψ : AInf unitDisc =>
      bersPhi (beltramiMul (beltramiMul (Lambda ψ) (ν : LinfStar)) (beltramiInv (μ : LinfStar))))
      (ball (0 : AInf unitDisc) 2) := by
  have hi := bc_beltramiInv_mem_ball μ.2
  have h1 : DifferentiableOn ℂ (fun l => beltramiMul l (ν : LinfStar)) LinfStarBall :=
    bd_differentiableOn ν.2
  have h2 : DifferentiableOn ℂ (fun l => beltramiMul l (beltramiInv (μ : LinfStar))) LinfStarBall :=
    bd_differentiableOn hi
  have h3 : DifferentiableOn ℂ (fun l => bersPhi l) LinfStarBall := bersPhi_differentiableOn
  have hΛ : DifferentiableOn ℂ Lambda (ball (0 : AInf unitDisc) 2) :=
    Lambda_differentiable.differentiableOn
  have hΛ1 : DifferentiableOn ℂ (fun ψ => beltramiMul (Lambda ψ) (ν : LinfStar))
      (ball (0 : AInf unitDisc) 2) :=
    h1.comp hΛ (fun ψ hψ => Lambda_mem_ball (mem_ball_zero_iff.mp hψ))
  have hΛ2 : DifferentiableOn ℂ
      (fun ψ => beltramiMul (beltramiMul (Lambda ψ) (ν : LinfStar)) (beltramiInv (μ : LinfStar)))
      (ball (0 : AInf unitDisc) 2) :=
    h2.comp hΛ1 (fun ψ hψ => bg_mul_mem_ball ν.2 (Lambda_mem_ball (mem_ball_zero_iff.mp hψ)))
  exact h3.comp hΛ2 (fun ψ hψ => bg_mul_mem_ball hi
    (bg_mul_mem_ball ν.2 (Lambda_mem_ball (mem_ball_zero_iff.mp hψ))))

theorem ba_T_eq (μ ν : LinfStarBall) (hi : beltramiInv (μ : LinfStar) ∈ LinfStarBall)
    {ψ : AInf unitDisc} (hψ : ‖ψ‖ < 2) :
    bers (rightTrans ⟨_, hi⟩ (bersChartInv ν ψ)) =
      bersPhi (beltramiMul (beltramiMul (Lambda ψ) (ν : LinfStar)) (beltramiInv (μ : LinfStar))) := by
  rw [ct_bersChartInv_eq hψ, bt_rightTrans_phi, bt_rightTrans_phi, bers_Phi]

/-- Clause 3 of `bers_atlas`, assuming injectivity of the Bers embedding. -/
theorem ba_transition (hinj : Function.Injective bers) (μ ν : LinfStarBall) :
    IsOpen (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν)) ∧
      DifferentiableOn ℂ (bersChart μ ∘ bersChartInv ν)
        (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν)) := by
  have hi : beltramiInv (μ : LinfStar) ∈ LinfStarBall := bc_beltramiInv_mem_ball μ.2
  set T : AInf unitDisc → AInf unitDisc := fun ψ =>
    bersPhi (beltramiMul (beltramiMul (Lambda ψ) (ν : LinfStar)) (beltramiInv (μ : LinfStar))) with hTdef
  have hT : DifferentiableOn ℂ T (ball (0 : AInf unitDisc) 2) := ba_T_diff μ ν
  have hleft : ∀ (m : LinfStarBall), ∀ ψ ∈ ball (0 : AInf unitDisc) 2,
      bersChart m (bersChartInv m ψ) = ψ := fun m ψ hψ =>
    (ba_injOn m).leftInvOn_invFunOn hψ
  have hkey : ∀ ψ ∈ ball (0 : AInf unitDisc) 2,
      bers (rightTrans ⟨_, hi⟩ (bersChartInv ν ψ)) = T ψ :=
    fun ψ hψ => ba_T_eq μ ν hi (mem_ball_zero_iff.mp hψ)
  -- description of the image
  have hS : bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν) =
      ball (0 : AInf unitDisc) 2 ∩ T ⁻¹' ball (0 : AInf unitDisc) 2 := by
    ext ψ
    constructor
    · rintro ⟨p, ⟨⟨φ', hφ', hp1⟩, ⟨ψ', hψ', hp2⟩⟩, rfl⟩
      have h0 : bersChart ν p = ψ' := by rw [← hp2]; exact hleft ν ψ' hψ'
      rw [h0]
      refine ⟨hψ', ?_⟩
      have hn' : ‖φ'‖ < 2 := mem_ball_zero_iff.mp hφ'
      have e1 : T ψ' = bers (rightTrans ⟨_, hi⟩ p) := by rw [← hkey ψ' hψ', hp2]
      have e2 : bers (rightTrans ⟨_, hi⟩ p) = φ' := by
        rw [← hp1, ct_bersChartInv_eq hn', bt_rightTrans_inv_left μ hi]
        exact (ahlfors_weill hn').choose_spec
      show T ψ' ∈ ball (0 : AInf unitDisc) 2
      rw [e1, e2]; exact hφ'
    · rintro ⟨hψ, hTψ⟩
      refine ⟨bersChartInv ν ψ, ⟨?_, ⟨ψ, hψ, rfl⟩⟩, hleft ν ψ hψ⟩
      refine ⟨T ψ, hTψ, ?_⟩
      have hn' : ‖T ψ‖ < 2 := mem_ball_zero_iff.mp hTψ
      have e3 : Phi ⟨Lambda (T ψ), Lambda_mem_ball hn'⟩ = rightTrans ⟨_, hi⟩ (bersChartInv ν ψ) := by
        apply hinj
        rw [(ahlfors_weill hn').choose_spec, hkey ψ hψ]
      rw [ct_bersChartInv_eq hn', e3]
      exact bt_rightTrans_inv_right μ hi _
  have hopen : IsOpen (ball (0 : AInf unitDisc) 2 ∩ T ⁻¹' ball (0 : AInf unitDisc) 2) :=
    hT.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
  rw [hS]
  refine ⟨hopen, ?_⟩
  refine (hT.mono inter_subset_left).congr ?_
  rintro ψ ⟨hψ, hTψ⟩
  have hn' : ‖T ψ‖ < 2 := mem_ball_zero_iff.mp hTψ
  have e3 : Phi ⟨Lambda (T ψ), Lambda_mem_ball hn'⟩ = rightTrans ⟨_, hi⟩ (bersChartInv ν ψ) := by
    apply hinj
    rw [(ahlfors_weill hn').choose_spec, hkey ψ hψ]
  have e4 : bersChartInv μ (T ψ) = bersChartInv ν ψ := by
    rw [ct_bersChartInv_eq hn', e3]
    exact bt_rightTrans_inv_right μ hi _
  show bersChart μ (bersChartInv ν ψ) = T ψ
  rw [← e4]
  exact hleft μ (T ψ) hTψ

/-- **The Bers atlas** (statement of `bers_atlas`, S1_1). -/
theorem ba_bers_atlas :
    (∀ μ, InjOn (bersChartInv μ) (ball 0 2)) ∧ (⋃ μ, bersChartDomain μ) = univ ∧
      (∀ μ ν, IsOpen (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν)) ∧
        DifferentiableOn ℂ (bersChart μ ∘ bersChartInv ν)
          (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν))) ∧
      ∀ μ, DifferentiableOn ℂ (bers ∘ bersChartInv μ) (ball 0 2) :=
  ⟨ba_injOn, ba_cover, ba_transition bers_injective, ba_bers_chart⟩

/-! ### Original relocated from `S1_1` (2026-10-26) -/

/-- (TT:506–512) **The Bers atlas.**
- Each `h_μ⁻¹` is injective on the ball of radius `2`.
- The domains `U_μ` cover `T(1)`.
- The transition maps `h_μ ∘ h_ν⁻¹ : h_ν(U_μ ∩ U_ν) → h_μ(U_μ ∩ U_ν)` are holomorphic on these open sets of `A∞(𝔻)`.
- The Bers embedding is holomorphic in every chart: `β ∘ h_μ⁻¹` is holomorphic on the ball of radius `2`, so `β` is
  biholomorphic onto its image for this structure. -/
theorem bers_atlas :
    (∀ μ, InjOn (bersChartInv μ) (ball 0 2)) ∧ (⋃ μ, bersChartDomain μ) = univ ∧
      (∀ μ ν, IsOpen (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν)) ∧
        DifferentiableOn ℂ (bersChart μ ∘ bersChartInv ν)
          (bersChart ν '' (bersChartDomain μ ∩ bersChartDomain ν))) ∧
      ∀ μ, DifferentiableOn ℂ (bers ∘ bersChartInv μ) (ball 0 2) :=
  ba_bers_atlas

end TakhtajanTeo
