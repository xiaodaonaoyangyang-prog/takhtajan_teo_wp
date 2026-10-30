import TakhtajanTeo.Ch1.S5ConformalFamilyAnalytic
import TakhtajanTeo.Ch1.GroupOrigin

/-! The actual conformal transition in the reciprocal coordinate at infinity. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_local_compact_bound {X : Type*} [TopologicalSpace X]
    {U : Set X} {F : X → ℂ → ℂ} {K : Set ℂ} {p : X}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hc : ContinuousOn (fun q : X × ℂ => F q.1 q.2) (U ×ˢ univ)) :
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∃ C > 0,
      ∀ q ∈ W, ∀ z ∈ K, ‖F q z‖ ≤ C := by
  obtain ⟨N, hKN, hN, hb⟩ := Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
    (isCompact_singleton.prod hK) (hU.prod isOpen_univ)
    (show {p} ×ˢ K ⊆ U ×ˢ univ from fun q hq => ⟨by simpa only [mem_singleton_iff.mp hq.1] using hp, mem_univ _⟩) hc
  obtain ⟨W, V, hW, _, hpW, hKV, hWV⟩ := generalized_tube_lemma isCompact_singleton hK hN hKN
  obtain ⟨C, hC, hbC⟩ := hb.exists_pos_norm_le
  refine ⟨W ∩ U, hW.inter hU, ⟨hpW (mem_singleton p), hp⟩, inter_subset_right, C, hC, ?_⟩
  intro q hq z hz
  exact hbC _ ⟨(q, z), hWV ⟨hq.1, hKV hz⟩, rfl⟩

-- L2
theorem s5cf_transition_at_source {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) (y : ℂ) :
    s5cf_transition p (normalizedSolution (s5cf_coeff p) y) = normalizedSolution (extB p.1) y := by
  change normalizedSolution (extB p.1) (Function.invFun (normalizedSolution (s5cf_coeff p))
    (normalizedSolution (s5cf_coeff p) y)) = _
  rw [Function.leftInverse_invFun (s5cf_coeff_bijective hp).1 y]

theorem s5cf_transition_zero {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    s5cf_transition p 0 = 0 := by
  have hA := QCV.qcv_ns_spec (norm_nonneg p) (mem_ball_zero_iff.mp hp) (s5cf_coeff_bound p)
  have hB := QCV.qcv_ns_spec (norm_nonneg p.1)
    ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hp)) (extB_isBeltramiCoeff p.1)
  have h := s5cf_transition_at_source hp 0
  rwa [hA.2.2.1, hB.2.2.1] at h

theorem s5cf_transition_ne_zero {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1)
    {z : ℂ} (hz : z ≠ 0) : s5cf_transition p z ≠ 0 := by
  have hA := QCV.qcv_ns_spec (norm_nonneg p) (mem_ball_zero_iff.mp hp) (s5cf_coeff_bound p)
  have hB := QCV.qcv_ns_spec (norm_nonneg p.1)
    ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hp)) (extB_isBeltramiCoeff p.1)
  obtain ⟨K, hK⟩ := hB.1
  have hi := injOn_univ.mp hK.2.2.1.2.1
  intro he
  have hh : Function.invFun (normalizedSolution (s5cf_coeff p)) z = 0 :=
    hi (he.trans hB.2.2.1.symm)
  apply hz
  calc z = normalizedSolution (s5cf_coeff p) (Function.invFun (normalizedSolution (s5cf_coeff p)) z) :=
      (Function.invFun_eq ((s5cf_coeff_bijective hp).2 z)).symm
    _ = 0 := by rw [hh, hA.2.2.1]

def s5cf_reciprocal (p : LinfStar × LinfStar) (t : ℂ) : ℂ :=
  if t = 0 then 0 else (s5cf_transition p t⁻¹)⁻¹

-- L3
theorem s5cf_reciprocal_regular_zero {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    AnalyticAt ℂ (s5cf_reciprocal p) 0 ∧ deriv (s5cf_reciprocal p) 0 ≠ 0 := by
  have hA := wr_ns_qc (norm_nonneg p) (mem_ball_zero_iff.mp hp) (s5cf_coeff_bound p) le_rfl
  have hB := wr_ns_qc (norm_nonneg p.1)
    ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hp)) (extB_isBeltramiCoeff p.1) le_rfl
  obtain ⟨eA, heA⟩ := t1_homeomorph hA.1 hA.2.1
  obtain ⟨eB, heB⟩ := t1_homeomorph hB.1 hB.2.1
  have hc : IsConformalOnto (s5cf_transition p) (eA '' unitDiscExterior) (eB '' unitDiscExterior) := by
    rw [heA, heB]
    exact s5cf_transition_conformal hp
  have hrel : ∀ y ∈ unitDiscExterior, eB y = s5cf_transition p (eA y) := by
    intro y _
    rw [heA, heB]
    exact (s5cf_transition_at_source hp y).symm
  obtain ⟨ξ, hξa, hξ0, hξd, hξ⟩ := grp25z_transition_chart eA eB hc hrel
  have heq : ξ = s5cf_reciprocal p := by
    funext t
    by_cases ht : t = 0
    · subst t; simp [s5cf_reciprocal, hξ0]
    · rw [hξ t ht, s5cf_reciprocal, if_neg ht]
      change (eB (eA.symm t⁻¹))⁻¹ = (normalizedSolution (extB p.1)
        (Function.invFun (normalizedSolution (s5cf_coeff p)) t⁻¹))⁻¹
      rw [wr_invFun_eq heA, heB]
  rw [← heq]
  exact ⟨hξa, hξd⟩

-- L4
theorem s5cf_reciprocal_analytic_nonzero {p : LinfStar × LinfStar} {t : ℂ}
    (hp : p ∈ ball 0 1) (ht : t ≠ 0)
    (hz : t⁻¹ ∈ normalizedSolution (s5cf_coeff p) '' unitDiscExterior) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 q.2) (p, t) := by
  have hi : AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => (q.1, q.2⁻¹)) (p, t) :=
    analyticAt_fst.prod (analyticAt_snd.inv ht)
  have ha := (s5cf_transition_analytic hp hz).comp_of_eq hi rfl
  have hb := ha.inv (s5cf_transition_ne_zero hp (inv_ne_zero ht))
  apply hb.congr
  filter_upwards [(continuous_snd.tendsto (p, t)).eventually (eventually_ne_nhds ht)] with q hq
  simp only [s5cf_reciprocal, if_neg hq]
  rfl

-- L5
theorem s5cf_common_exterior {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    ∃ U : Set (LinfStar × LinfStar), IsOpen U ∧ p ∈ U ∧ U ⊆ ball 0 1 ∧ ∃ r > 0,
      ∀ q ∈ U, ∀ t ∈ closedBall (0 : ℂ) r, t ≠ 0 →
        t⁻¹ ∈ normalizedSolution (s5cf_coeff q) '' unitDiscExterior := by
  have hc := s5cf_linear_family_cont s5cf_coeff s5cf_coeff_bound s5cf_coeff_linear
  obtain ⟨U, hU, hpU, hUb, C, hC, hb⟩ := s5cf_local_compact_bound
    (F := fun q z => normalizedSolution (s5cf_coeff q) z) isOpen_ball
    (isCompact_closedBall (0 : ℂ) 1) hp hc
  refine ⟨U, hU, hpU, hUb, 1 / (C + 1), by positivity, ?_⟩
  intro q hq t ht ht0
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have ht' : ‖t‖ * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
    (mem_closedBall_zero_iff.mp ht)
  have hlarge : C < ‖t⁻¹‖ := by
    rw [norm_inv, inv_eq_one_div, lt_div_iff₀ htn]
    nlinarith
  have hi : Function.invFun (normalizedSolution (s5cf_coeff q)) t⁻¹ ∈ unitDiscExterior := by
    change 1 < ‖Function.invFun (normalizedSolution (s5cf_coeff q)) t⁻¹‖
    by_contra hn
    have hsmall := hb q hq _ (mem_closedBall_zero_iff.mpr (le_of_not_gt hn))
    rw [Function.invFun_eq ((s5cf_coeff_bijective (hUb hq)).2 t⁻¹)] at hsmall
    exact (not_lt_of_ge hsmall) hlarge
  exact ⟨_, hi, Function.invFun_eq ((s5cf_coeff_bijective (hUb hq)).2 t⁻¹)⟩

-- L6
theorem s5cf_cauchy_family_regular {X : Type*} [TopologicalSpace X] {S : Set X}
    {F : X → ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun q : X × ℂ => F q.1 q.2) (S ×ˢ sphere c R))
    (hf : ∀ p ∈ S, ContinuousOn (F p) (closedBall c R))
    (hd : ∀ p ∈ S, DifferentiableOn ℂ (F p) (ball c R)) :
    ContinuousOn (fun q : X × ℂ => F q.1 q.2) (S ×ˢ ball c R) ∧
    ContinuousOn (fun q : X × ℂ => deriv (F q.1) q.2) (S ×ˢ ball c R) := by
  let H : X → ℂ → ℂ := fun p w => (2 * π * I)⁻¹ * F p w
  have hH : ContinuousOn (fun q : X × ℂ => H q.1 q.2) (S ×ˢ sphere c R) := hc.const_mul _
  have hHp : ∀ p ∈ S, ContinuousOn (H p) (sphere c R) := fun p hp =>
    hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨hp, hw⟩)
  have he : ∀ p ∈ S, EqOn (F p) (fun w => ∮ ξ in C(c, R), (ξ - w) ^ (-1 : ℤ) • H p ξ)
      (ball c R) := by
    intro p hp w hw
    have h := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw (hf p hp)
      (fun x hx => (hd p hp).differentiableAt (isOpen_ball.mem_nhds hx.1))
    have h' : F p w = (2 * π * I)⁻¹ * ∮ ξ in C(c, R), F p ξ / (ξ - w) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h.symm
    exact h'.trans (wr_cauchy_form (F p) c w R)
  refine ⟨(wr_param_circ_cont hR hH (-1)).congr (fun q hq => he q.1 hq.1 hq.2), ?_⟩
  apply (wr_param_circ_cont hR hH (-2)).congr
  rintro ⟨p, w⟩ ⟨hp, hw⟩
  have hew : F p =ᶠ[𝓝 w] fun w => ∮ ξ in C(c, R), (ξ - w) ^ (-1 : ℤ) • H p ξ :=
    eventually_of_mem (isOpen_ball.mem_nhds hw) (he p hp)
  change deriv (F p) w = ∮ ξ in C(c, R), (ξ - w) ^ (-2 : ℤ) • H p ξ
  rw [hew.deriv_eq]
  simpa using wr_cauchy_iteratedDeriv hR (hHp p hp) 1 hw

-- L7
theorem s5cf_reciprocal_spatial {U : Set (LinfStar × LinfStar)} {r : ℝ}
    (hUb : U ⊆ ball 0 1) (hr : 0 < r)
    (hdom : ∀ q ∈ U, ∀ t ∈ closedBall (0 : ℂ) r, t ≠ 0 →
      t⁻¹ ∈ normalizedSolution (s5cf_coeff q) '' unitDiscExterior) :
    ∀ p ∈ U, ContinuousOn (s5cf_reciprocal p) (closedBall 0 r) ∧
      DifferentiableOn ℂ (s5cf_reciprocal p) (ball 0 r) := by
  intro p hp
  have ha : ∀ t ∈ closedBall (0 : ℂ) r, AnalyticAt ℂ (s5cf_reciprocal p) t := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t; exact (s5cf_reciprocal_regular_zero (hUb hp)).1
    · exact (s5cf_reciprocal_analytic_nonzero (hUb hp) ht0 (hdom p hp t ht ht0)).comp_of_eq
        (analyticAt_const.prod analyticAt_id) rfl
  exact ⟨fun t ht => (ha t ht).continuousAt.continuousWithinAt,
    fun t ht => (ha t (ball_subset_closedBall ht)).differentiableAt.differentiableWithinAt⟩

-- L8
theorem s5cf_reciprocal_parameter_zero (p : LinfStar × LinfStar) :
    DifferentiableAt ℂ (fun q : LinfStar × LinfStar => s5cf_reciprocal q 0) p := by
  simpa only [s5cf_reciprocal, ite_true] using (differentiable_const (0 : ℂ) p)

-- L9
theorem s5cf_reciprocal_analytic_zero {p : LinfStar × LinfStar} (hp : p ∈ ball 0 1) :
    AnalyticAt ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 q.2) (p, 0) := by
  obtain ⟨U, hU, hpU, hUb, r, hr, hdom⟩ := s5cf_common_exterior hp
  have hs := s5cf_reciprocal_spatial hUb hr hdom
  have hcircle : ContinuousOn (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 q.2)
      (U ×ˢ sphere 0 r) := by
    intro q hq
    have ht : q.2 ≠ 0 := by
      intro ht
      have hn : ‖q.2‖ = r := by simpa using hq.2
      rw [ht, norm_zero] at hn
      linarith
    exact (s5cf_reciprocal_analytic_nonzero (hUb hq.1) ht
      (hdom q.1 hq.1 q.2 (sphere_subset_closedBall hq.2) ht)).continuousAt.continuousWithinAt
  have hreg := s5cf_cauchy_family_regular hr hcircle (fun q hq => (hs q hq).1) (fun q hq => (hs q hq).2)
  have hd : DifferentiableOn ℂ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 q.2)
      (U ×ˢ ball 0 r) := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    have hpar : DifferentiableAt ℂ (fun a : LinfStar × LinfStar => s5cf_reciprocal a t) q := by
      by_cases ht0 : t = 0
      · subst t; exact s5cf_reciprocal_parameter_zero q
      · exact ((s5cf_reciprocal_analytic_nonzero (hUb hq) ht0
          (hdom q hq t (ball_subset_closedBall ht) ht0)).comp_of_eq
          (analyticAt_id.prod analyticAt_const) rfl).differentiableAt
    exact (s5cf_joint_differentiableAt hU hq isOpen_ball ht (fun a ha => (hs a ha).2)
      (hreg.2.continuousAt ((hU.prod isOpen_ball).mem_nhds ⟨hq, ht⟩)) hpar).differentiableWithinAt
  exact bha_analyticOnNhd (hU.prod isOpen_ball) hd (p, 0) ⟨hpU, mem_ball_self hr⟩

end TakhtajanTeo
