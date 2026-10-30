import TakhtajanTeo.Ch1.S5ConformalReciprocal

/-! Real diagonal and analytic coefficients of the actual Model A normalization. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_star_analytic (μ : LinfStar) : AnalyticAt ℝ (fun ν : LinfStar => star ν) μ := by
  let J : LinfStar →L[ℝ] LinfStar :=
    Complex.conjCLE.toContinuousLinearMap.compLpL ∞ (volume.restrict unitDiscExterior)
  have he : (J : LinfStar → LinfStar) = fun ν => star ν := by
    funext ν
    apply Lp.ext
    filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL (p := ∞)
      (μ := volume.restrict unitDiscExterior) ν, Lp.coeFn_star ν] with z h1 h2
    exact h1.trans h2.symm
  rw [← he]
  exact J.analyticAt μ

-- L2
theorem s5cf_star_norm (μ : LinfStar) : ‖star μ‖ = ‖μ‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [Lp.coeFn_star μ] with z hz
  rw [hz]
  exact norm_star (μ z)

theorem s5cf_diagonal_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (μ, star μ) ∈ ball (0 : LinfStar × LinfStar) 1 := by
  rw [mem_ball_zero_iff, Prod.norm_mk, s5cf_star_norm, max_self]
  exact mem_ball_zero_iff.mp hμ

-- L3
theorem s5cf_planeA_realAnalytic (z : ℂ) :
    AnalyticOnNhd ℝ (fun μ : LinfStar => normalizedSolution (extA μ) z) LinfStarBall := by
  intro μ hμ
  have hJ : AnalyticAt ℝ (fun ν : LinfStar => (ν, star ν)) μ := analyticAt_id.prod (s5cf_star_analytic μ)
  have ha : AnalyticAt ℝ (fun p : LinfStar × LinfStar => normalizedSolution (s5cf_coeff p) z)
      (μ, star μ) := (s5cf_coeff_plane_analytic z (μ, star μ) (s5cf_diagonal_mem hμ)).restrictScalars
  apply (ha.comp_of_eq hJ rfl).congr
  filter_upwards [isOpen_ball.mem_nhds hμ] with ν hν
  exact congrFun (s5cf_plane_diagonal hν) z

def s5cf_three_coeff (w₁ w₂ : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  ((I - 1) * (w₂ - 1) + (I + 1) * (w₂ - w₁),
   -(I - 1) * w₁ * (w₂ - 1) - (I + 1) * (w₂ - w₁),
   (I - 1) * (w₂ - 1) - (I + 1) * (w₂ - w₁),
   -(I - 1) * w₁ * (w₂ - 1) + (I + 1) * (w₂ - w₁))

def s5cf_normCoeffs (p : LinfStar × LinfStar) : ℂ × ℂ × ℂ × ℂ :=
  s5cf_three_coeff (normalizedSolution (s5cf_coeff p) (-1)) (normalizedSolution (s5cf_coeff p) (-I))

-- L4
theorem s5cf_three_point {M : ExtPlane → ExtPlane} (hM : IsMobius M) {w₁ w₂ : ℂ}
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ 1) (h23 : w₂ ≠ 1)
    (e₁ : M (w₁ : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (e₂ : M (w₂ : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (e₃ : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)) :
    M = mobiusExt (s5cf_three_coeff w₁ w₂).1 (s5cf_three_coeff w₁ w₂).2.1
      (s5cf_three_coeff w₁ w₂).2.2.1 (s5cf_three_coeff w₁ w₂).2.2.2 := by
  rw [wr_three_point hM h12 h13 h23 e₁ e₂ e₃]
  dsimp [s5cf_three_coeff]
  congr 1 <;> ring

theorem s5cf_three_det {w₁ w₂ : ℂ} (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ 1) (h23 : w₂ ≠ 1) :
    (s5cf_three_coeff w₁ w₂).1 * (s5cf_three_coeff w₁ w₂).2.2.2 -
      (s5cf_three_coeff w₁ w₂).2.1 * (s5cf_three_coeff w₁ w₂).2.2.1 ≠ 0 := by
  have he : (s5cf_three_coeff w₁ w₂).1 * (s5cf_three_coeff w₁ w₂).2.2.2 -
      (s5cf_three_coeff w₁ w₂).2.1 * (s5cf_three_coeff w₁ w₂).2.2.1 =
      4 * (w₂ - 1) * (w₂ - w₁) * (w₁ - 1) := by
    dsimp [s5cf_three_coeff]
    ring_nf
    simp [I_sq]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h23))
    (sub_ne_zero.mpr h12.symm)) (sub_ne_zero.mpr h13)

-- L5
theorem s5cf_three_coeff_analytic (w : ℂ × ℂ) :
    AnalyticAt ℂ (fun w : ℂ × ℂ => s5cf_three_coeff w.1 w.2) w := by
  have hu : AnalyticAt ℂ (fun w : ℂ × ℂ => (I - 1) * (w.2 - 1)) w :=
    analyticAt_const.mul (analyticAt_snd.sub analyticAt_const)
  have hv : AnalyticAt ℂ (fun w : ℂ × ℂ => (I + 1) * (w.2 - w.1)) w :=
    analyticAt_const.mul (analyticAt_snd.sub analyticAt_fst)
  have hs : AnalyticAt ℂ (fun w : ℂ × ℂ => -(I - 1) * w.1 * (w.2 - 1)) w :=
    (analyticAt_const.mul analyticAt_fst).mul (analyticAt_snd.sub analyticAt_const)
  exact (hu.add hv).prod ((hs.sub hv).prod ((hu.sub hv).prod (hs.add hv)))

theorem s5cf_normCoeffs_analytic {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    AnalyticAt ℂ s5cf_normCoeffs p := by
  exact (s5cf_three_coeff_analytic _).comp_of_eq
    ((s5cf_coeff_plane_analytic (-1) p hp).prod (s5cf_coeff_plane_analytic (-I) p hp)) rfl

theorem s5cf_normalization_points {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    normalizedSolution (s5cf_coeff p) (-1) ≠ normalizedSolution (s5cf_coeff p) (-I) ∧
    normalizedSolution (s5cf_coeff p) (-1) ≠ 1 ∧ normalizedSolution (s5cf_coeff p) (-I) ≠ 1 := by
  have hN := QCV.qcv_ns_spec (norm_nonneg p) (mem_ball_zero_iff.mp hp) (s5cf_coeff_bound p)
  have hi := (s5cf_coeff_bijective hp).1
  have hm1I : (-1 : ℂ) ≠ -I := by intro h; have := congrArg Complex.im h; simp at this
  have hmI1 : (-I : ℂ) ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
  exact ⟨hi.ne hm1I, by simpa only [hN.2.2.2.1] using hi.ne (show (-1 : ℂ) ≠ 1 by norm_num),
    by simpa only [hN.2.2.2.1] using hi.ne hmI1⟩

-- L6
theorem s5cf_normCoeffs_det {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    (s5cf_normCoeffs p).1 * (s5cf_normCoeffs p).2.2.2 -
      (s5cf_normCoeffs p).2.1 * (s5cf_normCoeffs p).2.2.1 ≠ 0 := by
  obtain ⟨h12, h13, h23⟩ := s5cf_normalization_points hp
  exact s5cf_three_det h12 h13 h23

-- L8
theorem s5cf_wAS_rep {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (z : ExtPlane) :
    wAS μ z = mobiusExt (s5cf_normCoeffs (μ, star μ)).1 (s5cf_normCoeffs (μ, star μ)).2.1
      (s5cf_normCoeffs (μ, star μ)).2.2.1 (s5cf_normCoeffs (μ, star μ)).2.2.2
      (OnePoint.map (normalizedSolution (extA μ)) z) := by
  obtain ⟨M, hM, W, hW, hfin, hinf, hm1, hmI, h1⟩ := wA_spec hμ
  have heW : W = normalizedSolution (extA μ) :=
    (QCV.qcv_ns_eq (norm_nonneg μ) (mem_ball_zero_iff.mp hμ) (extA_isBeltramiCoeff μ) hW).symm
  have heC : W = normalizedSolution (s5cf_coeff (μ, star μ)) :=
    heW.trans (s5cf_plane_diagonal hμ).symm
  have hW1 : normalizedSolution (s5cf_coeff (μ, star μ)) 1 = 1 := by
    rw [← heC]; exact hW.2.2.2.1
  obtain ⟨h12, h13, h23⟩ := s5cf_normalization_points (s5cf_diagonal_mem hμ)
  have e1 : M ((normalizedSolution (s5cf_coeff (μ, star μ)) (-1) : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [← heC]; exact (hfin (-1)).symm.trans hm1
  have e2 : M ((normalizedSolution (s5cf_coeff (μ, star μ)) (-I) : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    rw [← heC]; exact (hfin (-I)).symm.trans hmI
  have e3 : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    have hh := (hfin 1).symm.trans h1
    rwa [hW.2.2.2.1] at hh
  have hrep := s5cf_three_point hM h12 h13 h23 e1 e2 e3
  change M = mobiusExt (s5cf_normCoeffs (μ, star μ)).1 (s5cf_normCoeffs (μ, star μ)).2.1
    (s5cf_normCoeffs (μ, star μ)).2.2.1 (s5cf_normCoeffs (μ, star μ)).2.2.2 at hrep
  rw [← hrep]
  induction z using OnePoint.rec with
  | infty => exact hinf
  | coe z =>
    change wAS μ (z : ExtPlane) = M ((normalizedSolution (extA μ) z : ℂ) : ExtPlane)
    rw [← heW]
    exact hfin z

end TakhtajanTeo
