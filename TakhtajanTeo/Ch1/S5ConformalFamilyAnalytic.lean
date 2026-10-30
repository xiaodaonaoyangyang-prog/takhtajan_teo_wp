import TakhtajanTeo.Ch1.S5ConformalFamilyContinuity
import TakhtajanTeo.Ch1.MovingEvaluationDerivative

/-! Genuine parameter holomorphy of the exterior transition, without differentiating a QC inverse. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_deriv_cont_ball {X : Type*} [TopologicalSpace X] {S : Set X}
    {F : X → ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun q : X × ℂ => F q.1 q.2) (S ×ˢ closedBall c R))
    (hd : ∀ p ∈ S, DifferentiableOn ℂ (F p) (ball c R)) :
    ContinuousOn (fun q : X × ℂ => deriv (F q.1) q.2) (S ×ˢ ball c R) := by
  have hFc : ∀ p ∈ S, ContinuousOn (F p) (closedBall c R) := fun p hp =>
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨hp, hw⟩)
  let H : X → ℂ → ℂ := fun p w => (2 * π * I)⁻¹ * F p w
  have hH : ContinuousOn (fun q : X × ℂ => H q.1 q.2) (S ×ˢ sphere c R) :=
    (hc.mono (prod_mono subset_rfl sphere_subset_closedBall)).const_mul _
  have hHp : ∀ p ∈ S, ContinuousOn (H p) (sphere c R) := fun p hp =>
    hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨hp, hw⟩)
  have he : ∀ p ∈ S, EqOn (F p) (fun w => ∮ ξ in C(c, R), (ξ - w) ^ (-1 : ℤ) • H p ξ)
      (ball c R) := by
    intro p hp w hw
    have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw (hFc p hp)
      (fun x hx => (hd p hp).differentiableAt (isOpen_ball.mem_nhds hx.1))
    have h' : F p w = (2 * π * I)⁻¹ * ∮ ξ in C(c, R), F p ξ / (ξ - w) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h.symm
    exact h'.trans (wr_cauchy_form (F p) c w R)
  apply (wr_param_circ_cont hR hH (-2)).congr
  rintro ⟨p, w⟩ ⟨hp, hw⟩
  have hew : F p =ᶠ[𝓝 w] fun w => ∮ ξ in C(c, R), (ξ - w) ^ (-1 : ℤ) • H p ξ :=
    eventually_of_mem (isOpen_ball.mem_nhds hw) (he p hp)
  change deriv (F p) w = ∮ ξ in C(c, R), (ξ - w) ^ (-2 : ℤ) • H p ξ
  rw [hew.deriv_eq]
  simpa using wr_cauchy_iteratedDeriv hR (hHp p hp) 1 hw

-- L2
theorem s5cf_spatial_deriv_cont {X : Type*} [TopologicalSpace X] {U : Set X} {V : Set ℂ}
    {F : X → ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hc : ContinuousOn (fun q : X × ℂ => F q.1 q.2) (U ×ˢ V))
    (hd : ∀ p ∈ U, DifferentiableOn ℂ (F p) V) :
    ContinuousOn (fun q : X × ℂ => deriv (F q.1) q.2) (U ×ˢ V) := by
  rintro ⟨p, z⟩ ⟨hp, hz⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV z hz
  have hcl : closedBall z (r / 2) ⊆ V :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrV
  have hs := s5cf_deriv_cont_ball (half_pos hr) (hc.mono (prod_mono subset_rfl hcl))
    (fun q hq => (hd q hq).mono (ball_subset_closedBall.trans hcl))
  exact (hs.continuousAt ((hU.prod isOpen_ball).mem_nhds ⟨hp, mem_ball_self (half_pos hr)⟩)).continuousWithinAt

-- L3
theorem s5cf_joint_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {V : Set ℂ} {F : E → ℂ → ℂ} {p : E} {z : ℂ}
    (hU : IsOpen U) (hp : p ∈ U) (hV : IsOpen V) (hz : z ∈ V)
    (hF : ∀ q ∈ U, DifferentiableOn ℂ (F q) V)
    (hD : ContinuousAt (fun q : E × ℂ => deriv (F q.1) q.2) (p, z))
    (hP : DifferentiableAt ℂ (fun q => F q z) p) :
    DifferentiableAt ℂ (fun q : E × ℂ => F q.1 q.2) (p, z) := by
  let R : E × ℂ → ℂ := fun q => F q.1 q.2 - F q.1 z - deriv (F p) z * (q.2 - z)
  have hA : HasFDerivAt (fun q : E × ℂ => q.2) (ContinuousLinearMap.snd ℂ E ℂ) (p, z) :=
    hasFDerivAt_snd
  have hm : ContinuousAt (fun q : (E × ℂ) × ℂ => (q.1.1, q.2)) ((p, z), z) := by fun_prop
  have hDc : ContinuousAt (fun q : (E × ℂ) × ℂ => deriv (F q.1.1) q.2) ((p, z), z) :=
    hD.comp_of_eq hm rfl
  have hsmall : R =o[𝓝 (p, z)] (fun q => q - (p, z)) :=
    (med_moving_remainder_littleO (hU.prod isOpen_univ) (show (p, z) ∈ U ×ˢ univ from ⟨hp, mem_univ _⟩)
      hV hz (fun q hq => hF q.1 hq.1) hDc hA.continuousAt).trans_isBigO hA.isBigO_sub
  have hR0 : R (p, z) = 0 := by simp [R]
  have hR : HasFDerivAt R (0 : (E × ℂ) →L[ℂ] ℂ) (p, z) := by
    rw [hasFDerivAt_iff_isLittleO]
    simpa only [hR0, zero_apply, sub_zero] using hsmall
  have hlin := (hA.sub_const z).fun_const_smul (deriv (F p) z)
  have hfix := hP.hasFDerivAt.comp (p, z) (hasFDerivAt_fst (𝕜 := ℂ) (E := E) (F := ℂ))
  have he : (fun q : E × ℂ => (F q.1 z + deriv (F p) z • (q.2 - z)) + R q) =
      (fun q : E × ℂ => F q.1 q.2) := by
    funext q
    dsimp [R]
    ring
  have hh := (hfix.fun_add hlin).fun_add hR
  change HasFDerivAt (fun q : E × ℂ => (F q.1 z + deriv (F p) z • (q.2 - z)) + R q) _ (p, z) at hh
  rw [he] at hh
  exact hh.differentiableAt

theorem s5cf_coeff_bijective {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    Function.Bijective (normalizedSolution (s5cf_coeff p)) := by
  have hA := QCV.qcv_ns_spec (norm_nonneg p) (mem_ball_zero_iff.mp hp) (s5cf_coeff_bound p)
  obtain ⟨KA, hKA⟩ := hA.1
  refine ⟨injOn_univ.mp hKA.2.2.1.2.1, ?_⟩
  apply range_eq_univ.mp
  simpa only [image_univ] using hA.2.1

theorem s5cf_transition_deriv_cont {U : Set (LinfStar × LinfStar)} {V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUb : U ⊆ ball 0 1)
    (hdom : ∀ q ∈ U, V ⊆ normalizedSolution (s5cf_coeff q) '' unitDiscExterior) :
    ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ => deriv (s5cf_transition q.1) q.2)
      (U ×ˢ V) := by
  exact s5cf_spatial_deriv_cont hU hV
    (s5cf_transition_cont.mono (prod_mono hUb (subset_univ V)))
    (fun q hq => (s5cf_transition_conformal (hUb hq)).1.mono (hdom q hq))

theorem s5cf_inverse_domain_rectangle {X : Type*} [TopologicalSpace X]
    {U : Set X} {D : Set ℂ} {A : X → ℂ → ℂ} (hU : IsOpen U) (hD : IsOpen D)
    (hc : ContinuousOn (fun q : X × ℂ => Function.invFun (A q.1) q.2) (U ×ˢ univ))
    (hb : ∀ p ∈ U, Function.Bijective (A p)) {p : X} {z : ℂ}
    (hp : p ∈ U) (hz : z ∈ A p '' D) :
    ∃ W : Set X, ∃ V : Set ℂ, IsOpen W ∧ p ∈ W ∧ IsOpen V ∧ z ∈ V ∧
      W ⊆ U ∧ ∀ q ∈ W, V ⊆ A q '' D := by
  have hIz : Function.invFun (A p) z ∈ D := by
    obtain ⟨y, hy, rfl⟩ := hz
    rwa [Function.leftInverse_invFun (hb p hp).1 y]
  have hIc := hc.continuousAt
    ((hU.prod isOpen_univ).mem_nhds (show (p, z) ∈ U ×ˢ univ from ⟨hp, mem_univ _⟩))
  have hnear : ∀ᶠ q : X × ℂ in 𝓝 (p, z), q.1 ∈ U ∧ Function.invFun (A q.1) q.2 ∈ D :=
    ((continuous_fst.tendsto (p, z)).eventually (hU.mem_nhds hp)).and
      (hIc.eventually (hD.mem_nhds hIz))
  obtain ⟨W, V, hW, hpW, hV, hzV, hWV⟩ := mem_nhds_prod_iff'.mp hnear
  have hWU : W ⊆ U := fun q hq => (hWV (show (q, z) ∈ W ×ˢ V from ⟨hq, hzV⟩)).1
  refine ⟨W, V, hW, hpW, hV, hzV, hWU, ?_⟩
  intro q hq w hw
  exact ⟨_, (hWV (show (q, w) ∈ W ×ˢ V from ⟨hq, hw⟩)).2, Function.invFun_eq ((hb q (hWU hq)).2 w)⟩

-- L4
theorem s5cf_transition_local {p : LinfStar × LinfStar} {z : ℂ} (hp : p ∈ ball 0 1)
    (hz : z ∈ normalizedSolution (s5cf_coeff p) '' unitDiscExterior) :
    ∃ U : Set (LinfStar × LinfStar), ∃ V : Set ℂ,
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ z ∈ V ∧ U ⊆ ball 0 1 ∧
      (∀ q ∈ U, V ⊆ normalizedSolution (s5cf_coeff q) '' unitDiscExterior) ∧
      ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ => deriv (s5cf_transition q.1) q.2)
        (U ×ˢ V) := by
  obtain ⟨U, V, hU, hpU, hV, hzV, hUb, hdom⟩ := s5cf_inverse_domain_rectangle
    isOpen_ball (isOpen_lt continuous_const continuous_norm) s5cf_coeff_inv_cont
    (fun _ hq => s5cf_coeff_bijective hq) hp hz
  refine ⟨U, V, hU, hpU, hV, hzV, hUb, hdom, ?_⟩
  exact s5cf_transition_deriv_cont hU hV hUb hdom

-- L5
theorem s5cf_transition_parameter_differentiableAt {p : LinfStar × LinfStar} {z : ℂ}
    (hp : p ∈ ball 0 1) (hz : z ∈ normalizedSolution (s5cf_coeff p) '' unitDiscExterior) :
    DifferentiableAt ℂ (fun q : LinfStar × LinfStar => s5cf_transition q z) p := by
  obtain ⟨U, V, hU, hpU, hV, hzV, hUb, hdom, hD⟩ := s5cf_transition_local hp hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hA := (s5cf_coeff_plane_analytic y p hp).differentiableAt.hasFDerivAt
  have hp1 : p.1 ∈ LinfStarBall := mem_ball_zero_iff.mpr ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hp))
  have hB := ((QCV.qcv_planeB_differentiableOn y).differentiableAt
    (isOpen_ball.mem_nhds hp1)).hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℂ) (E := LinfStar) (F := LinfStar))
  have he : (fun q : LinfStar × LinfStar => s5cf_transition q (normalizedSolution (s5cf_coeff q) y))
      =ᶠ[𝓝 p] fun q => normalizedSolution (extB q.1) y := by
    filter_upwards [isOpen_ball.mem_nhds hp] with q hq
    change normalizedSolution (extB q.1) (Function.invFun (normalizedSolution (s5cf_coeff q))
      (normalizedSolution (s5cf_coeff q) y)) = _
    rw [Function.leftInverse_invFun (s5cf_coeff_bijective hq).1 y]
  have hB' := hB.congr_of_eventuallyEq he
  have hDc : ContinuousAt (fun q : (LinfStar × LinfStar) × ℂ => deriv (s5cf_transition q.1) q.2)
      (p, normalizedSolution (s5cf_coeff p) y) := by
    rw [hyz]
    exact hD.continuousAt ((hU.prod hV).mem_nhds ⟨hpU, hzV⟩)
  have hh := med_hasFDerivAt_fixed_evaluation hU hpU hV (hyz.symm ▸ hzV)
    (fun q hq => (s5cf_transition_conformal (hUb hq)).1.mono (hdom q hq)) hDc hA hB'
  rw [hyz] at hh
  exact hh.differentiableAt

-- L6
theorem s5cf_transition_analytic {p : LinfStar × LinfStar} {z : ℂ}
    (hp : p ∈ ball 0 1) (hz : z ∈ normalizedSolution (s5cf_coeff p) '' unitDiscExterior) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_transition q.1 q.2) (p, z) := by
  obtain ⟨U, V, hU, hpU, hV, hzV, hUb, hdom, hD⟩ := s5cf_transition_local hp hz
  have hd : DifferentiableOn ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_transition q.1 q.2)
      (U ×ˢ V) := by
    rintro ⟨q, w⟩ ⟨hq, hw⟩
    exact (s5cf_joint_differentiableAt hU hq hV hw
      (fun a ha => (s5cf_transition_conformal (hUb ha)).1.mono (hdom a ha))
      (hD.continuousAt ((hU.prod hV).mem_nhds ⟨hq, hw⟩))
      (s5cf_transition_parameter_differentiableAt (hUb hq) (hdom q hq hw))).differentiableWithinAt
  exact bha_analyticOnNhd (hU.prod hV) hd (p, z) ⟨hpU, hzV⟩

end TakhtajanTeo

