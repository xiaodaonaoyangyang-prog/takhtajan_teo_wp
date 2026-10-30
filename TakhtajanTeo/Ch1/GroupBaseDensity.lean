import TakhtajanTeo.Ch1.GroupBase
import TakhtajanTeo.Ch1.GroupCov

/-! Removing the disk automorphism from the S3 origin density. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp25b_normalized_density {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {W : ℂ → ℂ} (hW : IsNormalizedSolution W (extA μ))
    (hWcd : ContDiffAt ℝ 1 W 0) :
    ‖dz (wA μ) 0‖ ^ 2 / (1 - ‖wA μ 0‖ ^ 2) ^ 2 = ‖dz W 0‖ ^ 2 := by
  obtain ⟨M, hM, V, hV, hwf, -, hm1, hmI, hm2⟩ := wA_spec hμ
  have hVW : V = W := thm13_5_uniqueness_plane hV.1 hW.1 hV.2.1 hW.2.1
    (by filter_upwards [hV.2.2.2.2, hW.2.2.2.2] with z hv hw; exact hv.trans hw.symm)
    hV.2.2.1 hV.2.2.2.1 hW.2.2.1 hW.2.2.2.1
  subst V
  let P : ℂ → ℂ := fun z => finPart (M (z : ExtPlane))
  have hPmap : ∀ z ∈ unitDisc, P z ∈ unitDisc ∧ (P z : ExtPlane) = M (z : ExtPlane) := by
    intro z hz
    obtain ⟨u, hu, hMu⟩ := modelA_mobius_disc (v := z) hW hM ((hwf (-1)).symm.trans hm1)
      ((hwf (-I)).symm.trans hmI) ((hwf 1).symm.trans hm2) (mem_ball_zero_iff.mp hz)
    have hPu : P z = u := by simp [P, hMu, finPart]
    exact ⟨hPu ▸ mem_ball_zero_iff.mpr hu, by rw [hPu, hMu]⟩
  have hPfinite : ∀ z ∈ unitDisc, M (z : ExtPlane) ≠ extInf := by
    intro z hz
    rw [← (hPmap z hz).2]
    exact OnePoint.coe_ne_infty _
  have hMo := mobius_finite_open hM
  have hMc := mobius_finite_conformal hM
  have hPconf : IsConformalOnto P unitDisc unitDisc := by
    refine ⟨fun z hz => (hMc.1.differentiableAt (hMo.mem_nhds (hPfinite z hz))).differentiableWithinAt,
      fun x hx y hy hxy => ?_, ?_⟩
    · apply OnePoint.coe_injective
      apply (mobius_sphere_continuous_bijective hM).2.1
      rw [← (hPmap x hx).2, ← (hPmap y hy).2, hxy]
    · apply Subset.antisymm
      · rintro v ⟨z, hz, rfl⟩
        exact (hPmap z hz).1
      · intro v hv
        have hvS : (v : ExtPlane) ∈ wAS μ '' toExt unitDisc := by
          rw [(wA_mapsTo hμ).1]
          exact ⟨v, hv, rfl⟩
        obtain ⟨p, ⟨z, hz, rfl⟩, hp⟩ := hvS
        refine ⟨W z, mem_ball_zero_iff.mpr (normalized_solution_disc (z := z) hW
          (mem_ball_zero_iff.mp hz)), ?_⟩
        have hh := congrArg finPart hp
        simpa [hwf z, P, finPart] using hh
  have heq : wA μ = fun z => P (W z) := by
    funext z
    unfold wA
    rw [hwf z]
  have h0 : (0 : ℂ) ∈ unitDisc := by norm_num [unitDisc]
  have hPd := hPconf.1.differentiableAt (isOpen_ball.mem_nhds h0)
  have hdz := (grp_dz_comp_holo (hWcd.differentiableAt one_ne_zero)
    (show DifferentiableAt ℂ P (W 0) by simpa [hW.2.2.1] using hPd)).2
  have hden := grp25c_density hPconf h0
  rw [heq, hdz, hW.2.2.1, norm_mul, mul_pow]
  simp only [hW.2.2.1]
  calc (‖deriv P 0‖ ^ 2 * ‖dz W 0‖ ^ 2) / (1 - ‖P 0‖ ^ 2) ^ 2 =
      (‖deriv P 0‖ ^ 2 / (1 - ‖P 0‖ ^ 2) ^ 2) * ‖dz W 0‖ ^ 2 := by ring
    _ = ‖dz W 0‖ ^ 2 := by rw [hden]; norm_num

end TakhtajanTeo

#print axioms TakhtajanTeo.grp25b_normalized_density
