import TakhtajanTeo.Ch1.S5NormalizationCoordinate
import TakhtajanTeo.Appendix.AppACont

/-! Exact sphere identities for the normalized exterior reciprocal welding. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def s5cf_inverseMobius (p : LinfStar × LinfStar) : ExtPlane → ExtPlane :=
  mobiusExt (s5cf_normCoeffs p).2.2.2 (-(s5cf_normCoeffs p).2.1)
    (-(s5cf_normCoeffs p).2.2.1) (s5cf_normCoeffs p).1

def s5cf_exterior_reciprocal (p : LinfStar × LinfStar) (t : ℂ) : ℂ :=
  deriv (normalizedSolution (extB p.1)) 0 *
    (s5cf_reciprocal p (s5cf_alpha p t) - s5cf_reciprocal p (s5cf_alpha p 0))

def s5cf_gchart (μ : LinfStar) (t : ℂ) : ℂ :=
  if t = 0 then 0 else (gMu μ t⁻¹)⁻¹

-- L1
theorem s5cf_transition_sphere {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) (v : ExtPlane) :
    OnePoint.map (normalizedSolution (extB p.1)) v =
      OnePoint.map (s5cf_transition p) (OnePoint.map (normalizedSolution (s5cf_coeff p)) v) := by
  induction v using OnePoint.rec with
  | infty => rfl
  | coe y =>
    change ((normalizedSolution (extB p.1) y : ℂ) : ExtPlane) =
      ((s5cf_transition p (normalizedSolution (s5cf_coeff p) y) : ℂ) : ExtPlane)
    exact congrArg (fun z : ℂ => (z : ExtPlane)) (s5cf_transition_at_source hp y).symm

-- L2
theorem s5cf_reciprocal_sphere {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) (t : ℂ) :
    mobiusExt 0 1 1 0 (OnePoint.map (s5cf_transition p) (mobiusExt 0 1 1 0 (t : ExtPlane))) =
      ((s5cf_reciprocal p t : ℂ) : ExtPlane) := by
  by_cases ht : t = 0
  · subst t
    rw [mobiusExt_coe_of_eq_zero (by norm_num)]
    change mobiusExt 0 1 1 0 extInf = ((s5cf_reciprocal p 0 : ℂ) : ExtPlane)
    rw [mobiusExt_infty_of_ne one_ne_zero]
    simp [s5cf_reciprocal]
  · have htinv : mobiusExt 0 1 1 0 (t : ExtPlane) = ((t⁻¹ : ℂ) : ExtPlane) := by
      rw [mobiusExt_coe (by simpa using ht)]
      simp [mobiusFn]
    rw [htinv]
    change mobiusExt 0 1 1 0 ((s5cf_transition p t⁻¹ : ℂ) : ExtPlane) = _
    rw [mobiusExt_coe (by simpa using s5cf_transition_ne_zero hp (inv_ne_zero ht))]
    congr 1
    simp [mobiusFn, s5cf_reciprocal, ht]

-- L3
theorem s5cf_planeB_inverse_wAS {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (w : ExtPlane) :
    OnePoint.map (normalizedSolution (extB μ)) (Function.invFun (wAS μ) w) =
      OnePoint.map (s5cf_transition (μ, star μ)) (s5cf_inverseMobius (μ, star μ) w) := by
  let v := Function.invFun (wAS μ) w
  have hrep := s5cf_wAS_rep hμ v
  rw [← s5cf_plane_diagonal hμ] at hrep
  have hM : s5cf_normalizingMobius (μ, star μ)
      (OnePoint.map (normalizedSolution (s5cf_coeff (μ, star μ))) v) = w :=
    hrep.symm.trans (Function.invFun_eq ((wAS_bijective μ).2 w))
  have hleft := mobiusExt_inv_apply (s5cf_normCoeffs_det (s5cf_diagonal_mem hμ))
    (OnePoint.map (normalizedSolution (s5cf_coeff (μ, star μ))) v)
  change s5cf_inverseMobius (μ, star μ) (s5cf_normalizingMobius (μ, star μ)
      (OnePoint.map (normalizedSolution (s5cf_coeff (μ, star μ))) v)) =
      OnePoint.map (normalizedSolution (s5cf_coeff (μ, star μ))) v at hleft
  rw [hM] at hleft
  have h := s5cf_transition_sphere (s5cf_diagonal_mem hμ) v
  rw [← hleft] at h
  exact h

-- L4
theorem s5cf_planeB_inverse_wAS_reciprocal {μ : LinfStar} {t : ℂ}
    (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
      (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (t : ExtPlane)))) =
      ((s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) t) : ℂ) : ExtPlane) := by
  rw [s5cf_planeB_inverse_wAS hμ]
  unfold s5cf_inverseMobius
  rw [s5cf_inverse_chart_formula (μ, star μ) t (s5cf_alpha_den hμ ht)]
  exact s5cf_reciprocal_sphere (s5cf_diagonal_mem hμ) (s5cf_alpha (μ, star μ) t)

-- L5
theorem s5cf_normalized_mobius_reciprocal {d c x : ℂ} {Z : ExtPlane}
    (hd : d ≠ 0) (hZ : mobiusExt 0 1 1 0 Z = (x : ExtPlane)) :
    mobiusExt 0 1 1 0 (mobiusExt (1 / d) 0 c 1 Z) = ((d * (x + c) : ℂ) : ExtPlane) := by
  rw [← sigma_invol Z, hZ, AppA.acc_mob_swap_inv]
  have hinner : (0 : ℂ) * c - (1 / d) * 1 ≠ 0 := by simp [hd]
  rw [s16p_mobiusExt_comp hinner]
  simp only [zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero]
  rw [mobiusExt_coe (by simpa using one_div_ne_zero hd)]
  congr 1
  dsimp [mobiusFn]
  field_simp <;> ring

-- L6
theorem s5cf_exterior_reciprocal_sphere {μ : LinfStar} {t : ℂ}
    (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    mobiusExt 0 1 1 0 (normalizedWeldingSphere μ (mobiusExt 0 1 1 0 (t : ExtPlane))) =
      ((s5cf_exterior_reciprocal (μ, star μ) t : ℂ) : ExtPlane) := by
  have h0 := s5cf_planeB_inverse_wAS_reciprocal hμ (t := 0) (by simp [unitDisc])
  rw [mobiusExt_coe_of_eq_zero (by norm_num)] at h0
  have hpole : finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
      (Function.invFun (wAS μ) extInf))) = s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := by
    simpa [finPart] using congrArg finPart h0
  change mobiusExt 0 1 1 0 (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (t : ExtPlane)))) = _
  rw [(AppA.acc_wB_rep hμ).2.2 _, hpole]
  simpa only [s5cf_exterior_reciprocal, sub_eq_add_neg] using
    s5cf_normalized_mobius_reciprocal (s5cf_planeB_deriv_ne_zero hμ)
      (s5cf_planeB_inverse_wAS_reciprocal hμ ht)

-- L7
theorem s5cf_exterior_reciprocal_analytic {μ : LinfStar} {t : ℂ}
    (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_exterior_reciprocal q.1 q.2)
      ((μ, star μ), t) := by
  have hd : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => deriv (normalizedSolution (extB q.1.1)) 0)
      ((μ, star μ), t) := (s5cf_planeB_deriv_product_analytic (s5cf_diagonal_mem hμ)).comp_of_eq analyticAt_fst rfl
  have h0 : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ =>
      s5cf_reciprocal q.1 (s5cf_alpha q.1 0)) ((μ, star μ), t) :=
    (s5cf_normalized_transition_analytic hμ (t := 0) (by simp [unitDisc])).comp_of_eq
      (analyticAt_fst.prod analyticAt_const) rfl
  exact hd.mul ((s5cf_normalized_transition_analytic hμ ht).sub h0)

-- L8
theorem s5cf_gchart_eq {μ : LinfStar} {t : ℂ} (hμ : μ ∈ LinfStarBall) (ht : t ∈ unitDisc) :
    s5cf_gchart μ t = s5cf_exterior_reciprocal (μ, star μ) t := by
  by_cases ht0 : t = 0
  · subst t; simp [s5cf_gchart, s5cf_exterior_reciprocal]
  have hw : t⁻¹ ∈ unitDiscExterior := by
    change 1 < ‖t⁻¹‖
    rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ht0, mem_ball_zero_iff.mp ht⟩
  have htinv : mobiusExt 0 1 1 0 (t : ExtPlane) = ((t⁻¹ : ℂ) : ExtPlane) := by
    rw [mobiusExt_coe (by simpa using ht0)]
    simp [mobiusFn]
  have hs := s5cf_exterior_reciprocal_sphere hμ ht
  change mobiusExt 0 1 1 0 (wB μ (Function.invFun (wAS μ) (mobiusExt 0 1 1 0 (t : ExtPlane)))) = _ at hs
  rw [htinv, ← gMu_sphere_factorization hμ hw,
    mobiusExt_coe (by simpa using gMu_exterior_ne_zero hμ hw)] at hs
  simpa [s5cf_gchart, ht0, mobiusFn] using OnePoint.coe_injective hs

end TakhtajanTeo
