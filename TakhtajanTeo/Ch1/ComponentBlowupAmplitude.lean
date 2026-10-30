import TakhtajanTeo.Ch1.ComponentBlowupNormalization

open Complex Set Metric Filter Topology
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem cba_source_distance {a : ℕ → ℂ}
    (ha0 : ∀ n, 0 < ‖a n‖) (ha1 : ∀ n, ‖a n‖ < 1)
    (ht : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    Tendsto (fun n => dist (cbl_source (a n) 1) (a n)) atTop (𝓝 0) := by
  have he : (fun n => dist (cbl_source (a n) 1) (a n)) =
      fun n => (1 - ‖a n‖) / 2 := by
    funext n
    rw [dist_eq_norm, cbl_source, mul_one, add_sub_cancel_left,
      cbl_scale_norm (ha0 n) (ha1 n)]
  rw [he]
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).div_const 2

/-- Actual output normalization differences shrink to zero, even if the
centers have no limiting point on the circle. Compact uniform continuity
supplies the uniform estimate; no derivative-scale comparison is assumed. -/
theorem cba_difference_tendsto_zero {e : ℂ → ℂ}
    (he : ContinuousOn e (closedBall (0 : ℂ) 1)) {a : ℕ → ℂ}
    (ha0 : ∀ n, 0 < ‖a n‖) (ha1 : ∀ n, ‖a n‖ < 1)
    (ht : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    Tendsto (fun n => e (cbl_source (a n) 1) - e (a n)) atTop (𝓝 0) := by
  have huc := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous he
  have hd := cba_source_distance ha0 ha1 ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [hd (gt_mem_nhds hδ)] with n hn
  have hx : cbl_source (a n) 1 ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (cbl_source_one_mem (ha0 n) (ha1 n))
  have hy : a n ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (ha1 n).le
  have hb := hclose _ hx _ hy hn
  simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hb

/-- The amplitude used for the genuine welding function vanishes; the
continuous plane extension is supplied by the actual welding data. -/
theorem cba_welding_difference {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {a : ℕ → ℂ} (ha0 : ∀ n, 0 < ‖a n‖) (ha1 : ∀ n, ‖a n‖ < 1)
    (ht : Tendsto (fun n => ‖a n‖) atTop (𝓝 1)) :
    Tendsto (fun n => fsans μ (cbl_source (a n) 1) - fsans μ (a n)) atTop (𝓝 0) := by
  obtain ⟨e, K, _, he⟩ := cra_welding_extension hμ
  have hl := cba_difference_tendsto_zero e.continuous.continuousOn ha0 ha1 ht
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [he (cbl_source_one_mem (ha0 n) (ha1 n)), he (mem_ball_zero_iff.mpr (ha1 n))]

end TakhtajanTeo
