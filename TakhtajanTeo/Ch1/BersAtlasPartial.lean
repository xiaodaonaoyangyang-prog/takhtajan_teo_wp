import TakhtajanTeo.Ch1.ChartTranslation
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.HilbertBersDifferential

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Clauses of the Bers atlas (`ba_` prefix) -/

/-- Clause 1 of `bers_atlas`: every inverse Bers chart is injective on the ball of radius `2`. -/
theorem ba_injOn (μ : LinfStarBall) : InjOn (bersChartInv μ) (ball (0 : AInf unitDisc) 2) := by
  intro a ha b hb hab
  have hna : ‖a‖ < 2 := mem_ball_zero_iff.mp ha
  have hnb : ‖b‖ < 2 := mem_ball_zero_iff.mp hb
  rw [ct_bersChartInv_eq hna, ct_bersChartInv_eq hnb] at hab
  have h0 := (bt_rightTrans_bijective μ).1.1 hab
  have h1 := congrArg bers h0
  obtain ⟨_, hA⟩ := ahlfors_weill hna
  obtain ⟨_, hB⟩ := ahlfors_weill hnb
  rwa [hA, hB] at h1

/-- Clause 2 of `bers_atlas`: the chart domains cover `T(1)`. -/
theorem ba_cover : (⋃ μ, bersChartDomain μ) = univ := by
  apply eq_univ_of_forall
  intro p
  refine mem_iUnion.mpr ⟨Quotient.out p, 0, mem_ball_self (by norm_num), ?_⟩
  have h0 : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  have hz : beltramiMul (Lambda (0 : AInf unitDisc)) ((Quotient.out p : LinfStarBall) : LinfStar) ∈
      LinfStarBall := by
    rw [h0, hb_zero_mul (Quotient.out p).2]
    exact (Quotient.out p).2
  unfold bersChartInv
  rw [dif_pos hz]
  simp only [h0, hb_zero_mul (Quotient.out p).2]
  exact Quotient.out_eq p

/-- Clause 4 of `bers_atlas`: `β` is holomorphic in every chart. -/
theorem ba_bers_chart (μ : LinfStarBall) :
    DifferentiableOn ℂ (bers ∘ bersChartInv μ) (ball (0 : AInf unitDisc) 2) := by
  have hcomp : DifferentiableOn ℂ (fun φ : AInf unitDisc => bersPhi (beltramiMul (Lambda φ) μ))
      (ball (0 : AInf unitDisc) 2) := by
    have h1 : DifferentiableOn ℂ (fun l => beltramiMul l (μ : LinfStar)) LinfStarBall :=
      bd_differentiableOn μ.2
    have h2 : DifferentiableOn ℂ (fun l => bersPhi (beltramiMul l (μ : LinfStar))) LinfStarBall :=
      bersPhi_differentiableOn.comp h1 (fun l hl => bg_mul_mem_ball μ.2 hl)
    exact h2.comp Lambda_differentiable.differentiableOn
      (fun φ hφ => Lambda_mem_ball (mem_ball_zero_iff.mp hφ))
  refine hcomp.congr ?_
  intro φ hφ
  have hn : ‖φ‖ < 2 := mem_ball_zero_iff.mp hφ
  simp only [Function.comp_apply]
  rw [ct_bersChartInv_eq hn, bt_rightTrans_phi, bers_Phi]

end TakhtajanTeo
