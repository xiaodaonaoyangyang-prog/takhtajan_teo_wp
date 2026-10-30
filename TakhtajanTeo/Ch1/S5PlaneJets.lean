import TakhtajanTeo.Ch1.S5WeldingNormalization

/-! Actual joint disk analyticity and normalization jets of the Model B plane family. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_partial_deriv_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ → ℂ} {p : E} {z : ℂ}
    (ha : AnalyticAt ℂ (fun q : E × ℂ => F q.1 q.2) (p, z)) :
    AnalyticAt ℂ (fun q : E => deriv (F q) z) p := by
  have hEval : AnalyticAt ℂ
      (fun q : E × ℂ => fderiv ℂ (fun q : E × ℂ => F q.1 q.2) q (0, 1)) (p, z) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp_of_eq ha.fderiv rfl
  have hm : AnalyticAt ℂ (fun q : E => (q, z)) p := analyticAt_id.prod analyticAt_const
  apply (hEval.comp_of_eq hm rfl).congr
  filter_upwards [hm.continuousAt.eventually ha.eventually_analyticAt] with q hq
  have hh := hq.differentiableAt.hasFDerivAt.comp z (hasFDerivAt_prodMk_right (𝕜 := ℂ) q z)
  change fderiv ℂ (fun q : E × ℂ => F q.1 q.2) (q, z) (0, 1) = deriv (F q) z
  convert! hh.hasDerivAt.deriv.symm using 1

-- L2
theorem s5cf_planeB_disk_analytic :
    AnalyticOnNhd ℂ (fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2)
      (LinfStarBall ×ˢ unitDisc) := by
  have hs : ∀ μ ∈ LinfStarBall, DifferentiableOn ℂ (normalizedSolution (extB μ)) unitDisc :=
    fun μ hμ => (QCV.qcv_W_props (mem_ball_zero_iff.mp hμ)).2.1
  have hc : ContinuousOn (fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2)
      (LinfStarBall ×ˢ unitDisc) := s5cf_planeB_cont.mono (prod_mono subset_rfl (subset_univ _))
  have hD := s5cf_spatial_deriv_cont isOpen_ball isOpen_ball hc hs
  have hd : DifferentiableOn ℂ (fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2)
      (LinfStarBall ×ˢ unitDisc) := by
    rintro ⟨μ, z⟩ ⟨hμ, hz⟩
    exact (s5cf_joint_differentiableAt isOpen_ball hμ isOpen_ball hz hs
      (hD.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμ, hz⟩))
      ((QCV.qcv_planeB_differentiableOn z).differentiableAt (isOpen_ball.mem_nhds hμ))).differentiableWithinAt
  exact bha_analyticOnNhd (isOpen_ball.prod isOpen_ball) hd

-- L3
theorem s5cf_planeB_deriv_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℂ (fun ν : LinfStar => deriv (normalizedSolution (extB ν)) 0) μ := by
  exact s5cf_partial_deriv_analytic (s5cf_planeB_disk_analytic (μ, 0) ⟨hμ, by simp [unitDisc]⟩)

theorem s5cf_planeB_deriv_ne_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    deriv (normalizedSolution (extB μ)) 0 ≠ 0 := by
  obtain ⟨_, hd, hi, _⟩ := QCV.qcv_W_props (mem_ball_zero_iff.mp hμ)
  exact deriv_ne_zero_of_injOn isOpen_ball hd (hi.mono (subset_univ _)) (by simp [unitDisc])

-- L4
theorem s5cf_planeB_deriv_product_analytic {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    AnalyticAt ℂ (fun q : LinfStar × LinfStar => deriv (normalizedSolution (extB q.1)) 0) p := by
  have hp1 : p.1 ∈ LinfStarBall := mem_ball_zero_iff.mpr ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hp))
  exact (s5cf_planeB_deriv_analytic hp1).comp_of_eq analyticAt_fst rfl

end TakhtajanTeo
