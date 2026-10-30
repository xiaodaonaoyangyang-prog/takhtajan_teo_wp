import TakhtajanTeo.Ch1.S5PlaneJets
import TakhtajanTeo.Ch1.TCurveSigmaCoordinates

/-! The actual inverse normalization coordinate stays in the reciprocal transition chart. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def s5cf_normalizingMobius (p : LinfStar × LinfStar) : ExtPlane → ExtPlane :=
  mobiusExt (s5cf_normCoeffs p).1 (s5cf_normCoeffs p).2.1
    (s5cf_normCoeffs p).2.2.1 (s5cf_normCoeffs p).2.2.2

def s5cf_alpha (p : LinfStar × LinfStar) (t : ℂ) : ℂ :=
  ((s5cf_normCoeffs p).1 * t - (s5cf_normCoeffs p).2.2.1) /
    ((s5cf_normCoeffs p).2.2.2 - (s5cf_normCoeffs p).2.1 * t)

-- L1
theorem s5cf_normalizing_closed_maps {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    MapsTo (s5cf_normalizingMobius (μ, star μ)) (toExt (closedBall (0 : ℂ) 1))
      (toExt (closedBall (0 : ℂ) 1)) := by
  rintro _ ⟨x, hx, rfl⟩
  let A := normalizedSolution (extA μ)
  have hN : IsNormalizedSolution A (extA μ) :=
    QCV.qcv_ns_spec (norm_nonneg μ) (mem_ball_zero_iff.mp hμ) (extA_isBeltramiCoeff μ)
  have hbij : Function.Bijective A := by
    simpa only [s5cf_plane_diagonal hμ] using s5cf_coeff_bijective (s5cf_diagonal_mem hμ)
  have hAx : A (Function.invFun A x) = x := Function.invFun_eq (hbij.2 x)
  have hy : Function.invFun A x ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]
    by_contra! hh
    have he := normalized_solution_exterior hN hh
    rw [hAx] at he
    have hx' := mem_closedBall_zero_iff.mp hx
    linarith
  have hW := mem_image_of_mem (wAS μ)
    (show ((Function.invFun A x : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) from ⟨_, hy, rfl⟩)
  rw [wAS_closed_image hμ] at hW
  have hrep := s5cf_wAS_rep hμ ((Function.invFun A x : ℂ) : ExtPlane)
  change wAS μ ((Function.invFun A x : ℂ) : ExtPlane) =
    s5cf_normalizingMobius (μ, star μ) ((A (Function.invFun A x) : ℂ) : ExtPlane) at hrep
  rw [hAx] at hrep
  rwa [hrep] at hW

-- L2
theorem s5cf_normalizing_zero_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (s5cf_normCoeffs (μ, star μ)).2.2.2 ≠ 0 ∧
      ‖(s5cf_normCoeffs (μ, star μ)).2.1‖ ≤ ‖(s5cf_normCoeffs (μ, star μ)).2.2.2‖ := by
  let C := s5cf_normCoeffs (μ, star μ)
  have h0 := s5cf_normalizing_closed_maps hμ
    (show ((0 : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) from ⟨0, by simp, rfl⟩)
  change mobiusExt C.1 C.2.1 C.2.2.1 C.2.2.2 ((0 : ℂ) : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) at h0
  have hd : C.2.2.2 ≠ 0 := by
    intro hd
    rw [mobiusExt_coe_of_eq_zero (by simp [hd])] at h0
    simpa [toExt, extInf] using h0
  rw [mobiusExt_coe (by simpa using hd)] at h0
  have hn : ‖C.2.1 / C.2.2.2‖ ≤ 1 := by simpa [toExt, mobiusFn] using h0
  rw [norm_div] at hn
  exact ⟨hd, (div_le_one (norm_pos_iff.mpr hd)).mp hn⟩

theorem s5cf_alpha_den {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    (s5cf_normCoeffs (μ, star μ)).2.2.2 - (s5cf_normCoeffs (μ, star μ)).2.1 * t ≠ 0 := by
  obtain ⟨hd, hb⟩ := s5cf_normalizing_zero_bound hμ
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  rw [norm_mul] at hn
  have hle := mul_le_mul_of_nonneg_right hb (norm_nonneg t)
  have hlt := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp ht) (norm_pos_iff.mpr hd)
  nlinarith

-- L3
theorem s5cf_inverse_chart_formula (p : LinfStar × LinfStar) (t : ℂ)
    (hd : (s5cf_normCoeffs p).2.2.2 - (s5cf_normCoeffs p).2.1 * t ≠ 0) :
    mobiusExt (s5cf_normCoeffs p).2.2.2 (-(s5cf_normCoeffs p).2.1)
      (-(s5cf_normCoeffs p).2.2.1) (s5cf_normCoeffs p).1 (mobiusExt 0 1 1 0 (t : ExtPlane)) =
      mobiusExt 0 1 1 0 ((s5cf_alpha p t : ℂ) : ExtPlane) := by
  let C := s5cf_normCoeffs p
  have hn : -C.2.1 * t + C.2.2.2 ≠ 0 := by
    convert hd using 1 <;> ring
  rw [AppA.acc_mob_swap_inv, AppA.acc_mob_eq_inv hn]
  congr 1
  congr 1
  dsimp [s5cf_alpha, C]
  congr 1 <;> ring

-- L4
theorem s5cf_inversion_disk_exterior {t : ℂ} (ht : t ∈ unitDisc) :
    mobiusExt 0 1 1 0 (t : ExtPlane) ∈ extDiscExterior := by
  by_cases ht0 : t = 0
  · subst t
    rw [mobiusExt_coe_of_eq_zero (by norm_num)]
    exact Or.inr rfl
  · rw [mobiusExt_coe (by simpa using ht0)]
    have hn : 1 < ‖t⁻¹‖ := by
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ht0, mem_ball_zero_iff.mp ht⟩
    exact Or.inl ⟨t⁻¹, hn, by simp [mobiusFn]⟩

theorem s5cf_alpha_mem_disk {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    s5cf_alpha (μ, star μ) t ∈ unitDisc := by
  let C := s5cf_normCoeffs (μ, star μ)
  have hdet := s5cf_normCoeffs_det (s5cf_diagonal_mem hμ)
  have hdi : C.2.2.2 * C.1 - (-C.2.1) * (-C.2.2.1) ≠ 0 := by
    convert hdet using 1 <;> ring
  have hright : s5cf_normalizingMobius (μ, star μ)
      (mobiusExt C.2.2.2 (-C.2.1) (-C.2.2.1) C.1 (mobiusExt 0 1 1 0 (t : ExtPlane))) =
      mobiusExt 0 1 1 0 (t : ExtPlane) := by
    change mobiusExt C.1 C.2.1 C.2.2.1 C.2.2.2
      (mobiusExt C.2.2.2 (-C.2.1) (-C.2.2.1) C.1 (mobiusExt 0 1 1 0 (t : ExtPlane))) = _
    simpa only [neg_neg] using mobiusExt_inv_apply hdi (mobiusExt 0 1 1 0 (t : ExtPlane))
  have hnot : mobiusExt 0 1 1 0 (t : ExtPlane) ∉ toExt (closedBall (0 : ℂ) 1) := by
    simpa only [fi_extDiscExterior_eq_compl, mem_compl_iff] using s5cf_inversion_disk_exterior ht
  have hE : mobiusExt C.2.2.2 (-C.2.1) (-C.2.2.1) C.1 (mobiusExt 0 1 1 0 (t : ExtPlane)) ∈
      extDiscExterior := by
    rw [fi_extDiscExterior_eq_compl, mem_compl_iff]
    intro hh
    have h := s5cf_normalizing_closed_maps hμ hh
    rw [hright] at h
    exact hnot h
  have h := tcg_sigma_coordinate_mem hE
  dsimp only [C] at h
  rw [s5cf_inverse_chart_formula (μ, star μ) t (s5cf_alpha_den hμ ht), sigma_invol] at h
  exact mem_ball_zero_iff.mpr (by simpa [finPart] using h)

-- L5
theorem s5cf_alpha_analytic {p : LinfStar × LinfStar} {t : ℂ} (hp : p ∈ ball 0 1)
    (hd : (s5cf_normCoeffs p).2.2.2 - (s5cf_normCoeffs p).2.1 * t ≠ 0) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_alpha q.1 q.2) (p, t) := by
  have hc : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_normCoeffs q.1) (p, t) :=
    (s5cf_normCoeffs_analytic hp).comp_of_eq analyticAt_fst rfl
  have h1 : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).1) (p, t) :=
    analyticAt_fst.comp_of_eq hc rfl
  have hs : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).2) (p, t) :=
    analyticAt_snd.comp_of_eq hc rfl
  have hb : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).2.1) (p, t) :=
    analyticAt_fst.comp_of_eq hs rfl
  have hss : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).2.2) (p, t) :=
    analyticAt_snd.comp_of_eq hs rfl
  have hcc : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).2.2.1) (p, t) :=
    analyticAt_fst.comp_of_eq hss rfl
  have hdd : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (s5cf_normCoeffs q.1).2.2.2) (p, t) :=
    analyticAt_snd.comp_of_eq hss rfl
  exact ((h1.mul analyticAt_snd).sub hcc).div (hdd.sub (hb.mul analyticAt_snd)) hd

-- L6
theorem s5cf_alpha_transition_domain {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    s5cf_alpha (μ, star μ) t = 0 ∨ (s5cf_alpha (μ, star μ) t)⁻¹ ∈
      normalizedSolution (s5cf_coeff (μ, star μ)) '' unitDiscExterior := by
  by_cases h0 : s5cf_alpha (μ, star μ) t = 0
  · exact Or.inl h0
  right
  rw [s5cf_plane_diagonal hμ]
  have hN := QCV.qcv_ns_spec (norm_nonneg μ) (mem_ball_zero_iff.mp hμ) (extA_isBeltramiCoeff μ)
  change (s5cf_alpha (μ, star μ) t)⁻¹ ∈ normalizedSolution (extA μ) '' {z : ℂ | 1 < ‖z‖}
  rw [normalized_solution_exterior_image hN]
  change 1 < ‖(s5cf_alpha (μ, star μ) t)⁻¹‖
  rw [norm_inv]
  exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp (s5cf_alpha_mem_disk hμ ht)⟩

-- L8
theorem s5cf_normalized_transition_analytic {μ : LinfStar} {t : ℂ}
    (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ =>
      s5cf_reciprocal q.1 (s5cf_alpha q.1 q.2)) ((μ, star μ), t) := by
  have hp := s5cf_diagonal_mem hμ
  have ha := s5cf_alpha_analytic hp (s5cf_alpha_den hμ ht)
  have hΞ : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 q.2)
      ((μ, star μ), s5cf_alpha (μ, star μ) t) := by
    by_cases h0 : s5cf_alpha (μ, star μ) t = 0
    · rw [h0]
      exact s5cf_reciprocal_analytic_zero hp
    · exact s5cf_reciprocal_analytic_nonzero hp h0 ((s5cf_alpha_transition_domain hμ ht).resolve_left h0)
  exact hΞ.comp_of_eq (analyticAt_fst.prod ha) rfl

end TakhtajanTeo
