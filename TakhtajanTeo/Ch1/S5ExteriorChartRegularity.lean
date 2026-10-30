import TakhtajanTeo.Ch1.S5ExteriorReciprocalFormula
import TakhtajanTeo.Ch1.S5FiberGeometry

/-! Univalence and actual inverse identities for the exterior reciprocal coordinate. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_gchart_sphere {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    ((s5cf_gchart μ t : ℂ) : ExtPlane) =
      mobiusExt 0 1 1 0 (normalizedWeldingSphere μ (mobiusExt 0 1 1 0 (t : ExtPlane))) := by
  rw [s5cf_gchart_eq hμ ht]
  exact (s5cf_exterior_reciprocal_sphere hμ ht).symm

-- L2
theorem s5cf_gchart_analytic {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    AnalyticAt ℂ (s5cf_gchart μ) t := by
  have ha := (s5cf_exterior_reciprocal_analytic hμ ht).comp_of_eq
    (analyticAt_const.prod analyticAt_id) rfl
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds ht] with s hs
  exact (s5cf_gchart_eq hμ hs).symm

theorem s5cf_gchart_realAnalytic {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    AnalyticAt ℝ (fun q : LinfStar × ℂ => s5cf_gchart q.1 q.2) (μ, t) := by
  have hc : AnalyticAt ℝ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2)
      ((μ, star μ), t) := (s5cf_exterior_reciprocal_analytic hμ ht).restrictScalars
  have hs : AnalyticAt ℝ (fun q : LinfStar × ℂ => star q.1) (μ, t) :=
    (s5cf_star_analytic μ).comp_of_eq analyticAt_fst rfl
  have hm : AnalyticAt ℝ (fun q : LinfStar × ℂ => ((q.1, star q.1), q.2)) (μ, t) :=
    (analyticAt_fst.prod hs).prod analyticAt_snd
  apply (hc.comp_of_eq hm rfl).congr
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds
    (show (μ, t) ∈ LinfStarBall ×ˢ unitDisc from ⟨hμ, ht⟩)] with q hq
  exact (s5cf_gchart_eq hq.1 hq.2).symm

-- L3
theorem s5cf_gchart_inj {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : InjOn (s5cf_gchart μ) unitDisc := by
  intro t ht s hs he
  have h := congrArg (fun z : ℂ => (z : ExtPlane)) he
  rw [s5cf_gchart_sphere hμ ht, s5cf_gchart_sphere hμ hs] at h
  have h1 : normalizedWeldingSphere μ (mobiusExt 0 1 1 0 (t : ExtPlane)) =
      normalizedWeldingSphere μ (mobiusExt 0 1 1 0 (s : ExtPlane)) := by
    simpa only [sigma_invol] using congrArg (mobiusExt 0 1 1 0) h
  have h2 := (normalizedWeldingSphere_bijective μ).1 h1
  apply OnePoint.coe_injective
  simpa only [sigma_invol] using congrArg (mobiusExt 0 1 1 0) h2

-- L4
theorem s5cf_gchart_deriv_ne_zero {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    deriv (s5cf_gchart μ) t ≠ 0 := by
  exact deriv_ne_zero_of_injOn isOpen_ball
    (fun s hs => (s5cf_gchart_analytic hμ hs).differentiableAt.differentiableWithinAt)
    (s5cf_gchart_inj hμ) ht

theorem s5cf_exterior_reciprocal_deriv_ne_zero {μ : LinfStar} {t : ℂ}
    (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    deriv (fun w => s5cf_exterior_reciprocal (μ, star μ) w) t ≠ 0 := by
  have he : (fun w => s5cf_exterior_reciprocal (μ, star μ) w) =ᶠ[𝓝 t] s5cf_gchart μ := by
    filter_upwards [isOpen_ball.mem_nhds ht] with w hw
    exact (s5cf_gchart_eq hμ hw).symm
  rw [he.deriv_eq]
  exact s5cf_gchart_deriv_ne_zero hμ ht

-- L5
theorem s5cf_uniformizer_left {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    fiberUniformizer μ (s5cf_gchart μ t) = t := by
  by_cases ht0 : t = 0
  · subst t; simp [s5cf_gchart, fiberUniformizer]
  have hw : t⁻¹ ∈ unitDiscExterior := by
    change 1 < ‖t⁻¹‖
    rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ht0, mem_ball_zero_iff.mp ht⟩
  have hg : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hi := hg.2.1.leftInvOn_invFunOn hw
  have hn := gMu_exterior_ne_zero hμ hw
  simp only [s5cf_gchart, if_neg ht0, fiberUniformizer, if_neg (inv_ne_zero hn), inv_inv, hi]

-- L7
theorem s5cf_uniformizer_inverse_data {μ : LinfStar} {ζ : ℂ} (hμ : μ ∈ LinfStarBall)
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    fiberUniformizer μ ζ ∈ unitDisc ∧ s5cf_gchart μ (fiberUniformizer μ ζ) = ζ := by
  refine ⟨mem_ball_zero_iff.mpr (s5fg_uniformizer_regular hμ hζ).2.1, ?_⟩
  rcases hζ with rfl | ⟨w, hw, rfl⟩
  · simp [fiberUniformizer, s5cf_gchart]
  · rw [(s5wr_uniformizer_jet hμ hw).1]
    have hw0 : w ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hw
    simp only [s5cf_gchart, if_neg (inv_ne_zero hw0), inv_inv]

end TakhtajanTeo
