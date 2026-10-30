import TakhtajanTeo.Ch2.S4PullbackSmooth

/-! # Spatial jets and parameter holomorphy of the actual transition (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P9
theorem s4pv_plane_transition_regular {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    let U := qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}
    let F := fun e : ℂ => qcv_planeTransition (beltramiMul (e • ν) κ) κ
    ∃ P : Set ℂ, IsOpen P ∧ 0 ∈ P ∧
      (∀ e ∈ P, ContDiffOn ℝ 3 (F e) U) ∧
      (∀ j ≤ 3, ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U)) ∧
      (∀ e ∈ P, ∀ y ∈ U, dz (F e) y ≠ 0) ∧
      (∀ y ∈ U, DifferentiableOn ℂ (fun e => schwarzianDz (F e) y) P) := by
  let U := qcv_planeSolution κ ''
    {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}
  let F := fun e : ℂ => qcv_planeTransition (beltramiMul (e • ν) κ) κ
  change ∃ P : Set ℂ, IsOpen P ∧ 0 ∈ P ∧ _
  let k : ℝ := ‖qcv_rightDerivative κ ν‖ / (1 - ‖κ‖ ^ 2)
  have hk : 0 ≤ k := by
    have hκn := bc_norm_lt_one hκ
    have hden : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    exact div_nonneg (norm_nonneg _) hden.le
  obtain ⟨m, he, hm, hs⟩ := s4pv_dot_smooth_rep hκ hν
  change IsBeltramiCoeff m univ k at hm
  have hm₀ : IsBeltramiCoeff (fun _ : ℂ => 0) univ k :=
    ⟨aestronglyMeasurable_const, Eventually.of_forall fun _ => by simpa using hk⟩
  have hs₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => (0 : ℂ)) U := contDiffOn_const
  have hU : IsOpen U := s4pv_plane_exterior_isOpen hκ
  let V : Set (ℂ × ℂ) := {q | (2 * k) * ‖q‖ < 1}
  let W := fun q : ℂ × ℂ => normalizedSolution (fun y => q.1 * m y + q.2 * (0 : ℂ))
  have hV : IsOpen V := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hVk : ∀ q ∈ V, ∃ c < 1, IsBeltramiCoeff (fun y => q.1 * m y + q.2 * (0 : ℂ)) univ c := by
    intro q hq
    refine ⟨(2 * k) * ‖q‖, hq, ?_⟩
    simpa only [abs_of_nonneg hk, two_mul] using wr_coeff_lin hm hm₀ q
  have hreg : (∀ q ∈ V, ContDiffOn ℝ 3 (W q) U) ∧
      ∀ j ≤ 3, ContinuousOn
        (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (W q.1) q.2) (V ×ˢ U) :=
    wr_ns2_z_regular hm hm₀ hU hs hs₀ hV hVk
  have hS := s4ma_ns2_schwarzian hk hm hm₀ hU hs hs₀
  let P : Set ℂ := {e | (2 * k) * ‖e‖ < 1 ∧ ‖e • ν‖ < 1}
  have hP : IsOpen P :=
    (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).inter
      (isOpen_lt ((continuous_id.smul continuous_const).norm) continuous_const)
  have hpV : ∀ e ∈ P, (e, (0 : ℂ)) ∈ V := by
    intro e heP
    simpa only [V, mem_ofPred_eq, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg e)] using heP.1
  have hsmall : ∀ e ∈ P, ‖e‖ * k < 1 := by
    intro e heP
    have hh := heP.1
    have hn := mul_nonneg hk (norm_nonneg e)
    nlinarith
  have hFW : ∀ e ∈ P, F e = W (e, 0) := by
    intro e heP
    change qcv_planeTransition (beltramiMul (e • ν) κ) κ = _
    rw [s4pv_plane_transition hκ ν heP.2 (hsmall e heP)]
    have hcoeff : (fun y => e * ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ)
        (qcv_planeSolution κ) y) =ᵐ[volume] fun y => e * m y := by
      filter_upwards [he] with y hy
      rw [hy]
    have hEq := qcv_ns_congr_ae (mul_nonneg (norm_nonneg e) hk) (hsmall e heP)
      (s4v_linear_coeff (qcv_base_dot_isBeltramiCoeff hκ _) e) hcoeff
    simpa only [W, zero_mul, add_zero] using hEq
  refine ⟨P, hP, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P]
  · intro e heP
    change ContDiffOn ℝ 3 (F e) U
    rw [hFW e heP]
    exact hreg.1 _ (hpV e heP)
  · intro j hj
    change ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U)
    have hc := (hreg.2 j hj).comp (f := fun q : ℂ × ℂ => ((q.1, (0 : ℂ)), q.2))
      ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun (q : ℂ × ℂ) (hq : q ∈ P ×ˢ U) => ⟨hpV q.1 hq.1, hq.2⟩)
    exact hc.congr fun q hq => by rw [hFW q.1 hq.1]; rfl
  · intro e heP y hy hzero
    have hpos := wr_local_jacobian_pos hm hm₀ hU hs hs₀ (hVk _ (hpV e heP)) hy
    change 0 < ‖dz (W (e, 0)) y‖ ^ 2 - ‖dzbar (W (e, 0)) y‖ ^ 2 at hpos
    change dz (F e) y = 0 at hzero
    rw [hFW e heP] at hzero
    rw [hzero, norm_zero] at hpos
    nlinarith [sq_nonneg ‖dzbar (W (e, 0)) y‖]
  · intro y hy e heP
    have hd : DifferentiableAt ℂ (fun t => schwarzianDz (W (t, 0)) y) e :=
      (hS.2 (e, 0) (hpV e heP) y hy).1
    apply DifferentiableAt.differentiableWithinAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [hP.mem_nhds heP] with t ht
    change schwarzianDz (F t) y = schwarzianDz (W (t, 0)) y
    rw [hFW t ht]

end Ch2
end TakhtajanTeo
