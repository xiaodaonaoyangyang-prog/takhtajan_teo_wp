import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Set Metric Filter Topology Asymptotics
open scoped Topology
namespace TakhtajanTeo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- L1
theorem med_uniform_spatial_remainder
    {U : Set E} {V : Set ℂ} {p0 : E} {z0 : ℂ} {T : E → ℂ → ℂ}
    (hU : IsOpen U) (hp0 : p0 ∈ U) (hV : IsOpen V) (hz0 : z0 ∈ V)
    (hT : ∀ p ∈ U, DifferentiableOn ℂ (T p) V)
    (hD : ContinuousAt (fun q : E × ℂ => deriv (T q.1) q.2) (p0, z0)) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ p ∈ ball p0 r, ∀ z ∈ ball z0 r,
        ‖T p z - T p z0 - deriv (T p0) z0 * (z - z0)‖ ≤ ε * ‖z - z0‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp
    (hD.tendsto.eventually (ball_mem_nhds (deriv (T p0) z0) hε))
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp0)
  obtain ⟨rV, hrV, hballV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hz0)
  let r := min δ (min rU rV)
  have hr : 0 < r := lt_min hδ (lt_min hrU hrV)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrU' : r ≤ rU := (min_le_right _ _).trans (min_le_left _ _)
  have hrV' : r ≤ rV := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, ?_⟩
  intro p hp z hz
  have hpU : p ∈ U := hballU ((mem_ball.mp hp).trans_le hrU')
  have hderiv : ∀ w ∈ ball z0 r,
      HasDerivWithinAt (fun w => T p w - deriv (T p0) z0 * w)
        (deriv (T p) w - deriv (T p0) z0) (ball z0 r) w := by
    intro w hw
    have hwV : w ∈ V := hballV ((mem_ball.mp hw).trans_le hrV')
    have hTw := ((hT p hpU).differentiableAt (hV.mem_nhds hwV)).hasDerivAt
    have hlinear : HasDerivAt (fun v : ℂ => deriv (T p0) z0 * v)
        (deriv (T p0) z0) w := hasDerivAt_const_mul _
    exact (hTw.fun_sub hlinear).hasDerivWithinAt
  have hbound : ∀ w ∈ ball z0 r, ‖deriv (T p) w - deriv (T p0) z0‖ ≤ ε := by
    intro w hw
    have hpair : (p, w) ∈ ball (p0, z0) δ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(mem_ball.mp hp).trans_le hrδ, (mem_ball.mp hw).trans_le hrδ⟩
    exact le_of_lt (by simpa only [mem_ofPred_eq, mem_ball, dist_eq_norm] using hδD hpair)
  have hmv := (convex_ball z0 r).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (mem_ball_self hr) hz
  convert hmv using 1
  congr 1
  ring

-- L2
theorem med_moving_remainder_littleO
    {U : Set E} {V : Set ℂ} {p0 : E} {A : E → ℂ} {T : E → ℂ → ℂ}
    (hU : IsOpen U) (hp0 : p0 ∈ U) (hV : IsOpen V) (hA0 : A p0 ∈ V)
    (hT : ∀ p ∈ U, DifferentiableOn ℂ (T p) V)
    (hD : ContinuousAt (fun q : E × ℂ => deriv (T q.1) q.2) (p0, A p0))
    (hA : ContinuousAt A p0) :
    (fun p => T p (A p) - T p (A p0) - deriv (T p0) (A p0) * (A p - A p0))
      =o[𝓝 p0] (fun p => A p - A p0) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hbound⟩ := med_uniform_spatial_remainder hU hp0 hV hA0 hT hD ε hε
  filter_upwards [ball_mem_nhds p0 hr,
    hA.tendsto.eventually (ball_mem_nhds (A p0) hr)] with p hp hAp
  exact hbound p hp (A p) hAp

-- L3
theorem med_hasFDerivAt_fixed_evaluation
    {U : Set E} {V : Set ℂ} {p0 : E} {A : E → ℂ} {T : E → ℂ → ℂ}
    {LA LB : E →L[ℂ] ℂ}
    (hU : IsOpen U) (hp0 : p0 ∈ U) (hV : IsOpen V) (hA0 : A p0 ∈ V)
    (hT : ∀ p ∈ U, DifferentiableOn ℂ (T p) V)
    (hD : ContinuousAt (fun q : E × ℂ => deriv (T q.1) q.2) (p0, A p0))
    (hA : HasFDerivAt A LA p0)
    (hB : HasFDerivAt (fun p => T p (A p)) LB p0) :
    HasFDerivAt (fun p => T p (A p0)) (LB - deriv (T p0) (A p0) • LA) p0 := by
  let d0 := deriv (T p0) (A p0)
  let R := fun p => T p (A p) - T p (A p0) - d0 * (A p - A p0)
  have hRsmall : R =o[𝓝 p0] (fun p => p - p0) :=
    (med_moving_remainder_littleO hU hp0 hV hA0 hT hD hA.continuousAt).trans_isBigO
      hA.isBigO_sub
  have hR0 : R p0 = 0 := by simp [R]
  have hRderiv : HasFDerivAt R (0 : E →L[ℂ] ℂ) p0 := by
    rw [hasFDerivAt_iff_isLittleO]
    simpa only [hR0, zero_apply, sub_zero] using hRsmall
  have hlinear : HasFDerivAt (fun p => d0 * (A p - A p0)) (d0 • LA) p0 := by
    simpa only [smul_eq_mul] using (hA.sub_const (A p0)).fun_const_smul d0
  have heq : (fun p => (T p (A p) - d0 * (A p - A p0)) - R p) =
      (fun p => T p (A p0)) := by
    funext p
    dsimp [R]
    ring
  have hfinal := (hB.fun_sub hlinear).fun_sub hRderiv
  rw [heq, sub_zero] at hfinal
  exact hfinal

end TakhtajanTeo
