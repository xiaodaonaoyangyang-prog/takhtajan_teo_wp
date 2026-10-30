import TakhtajanTeo.Ch1.ComponentTB

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Block C: Theorem 2.10 (`ctc_` prefix)
Sorry sources: `l29r_restricted` only (through `ctb_thm_2_13_b12`). -/

/-- The Hilbert chart map is injective on the ball of radius `√(π/3)`. -/
theorem ctc_chart_injOn (μ : LinfStarBall) :
    InjOn (fun ψ : A2 unitDisc => bersChartInv μ (A2toAInf ψ)) (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) := by
  intro a ha b hb hab
  have hna := ct_A2toAInf_norm_lt ha
  have hnb := ct_A2toAInf_norm_lt hb
  exact A2toAInf_injective (ba_injOn μ (mem_ball_zero_iff.mpr hna) (mem_ball_zero_iff.mpr hnb) hab)

/-- `h̃_μ ∘ h̃_μ⁻¹ = id` on the ball of radius `√(π/3)`. -/
theorem ctc_chart_left_inv (μ : LinfStarBall) :
    ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)), hilbertChart μ (bersChartInv μ (A2toAInf φ)) = φ :=
  fun _ hφ => (ctc_chart_injOn μ).leftInvOn_invFunOn hφ

/-- The transition `β ∘ R_{μ⁻¹} ∘ h_ν⁻¹` is `ψ ↦ (β ∘ Φ)(Λ(ψ) * κ)` with `κ = ν * μ⁻¹` (class-level
associativity of the group law). -/
theorem ctc_T_assoc (μ ν : LinfStarBall) {ψ : AInf unitDisc} (hψ : ‖ψ‖ < 2) :
    bersPhi (beltramiMul (beltramiMul (Lambda ψ) (ν : LinfStar)) (beltramiInv (μ : LinfStar))) =
      bersPhi (beltramiMul (Lambda ψ) (beltramiMul (ν : LinfStar) (beltramiInv (μ : LinfStar)))) := by
  have hl := Lambda_mem_ball hψ
  have hi := bc_beltramiInv_mem_ball μ.2
  have e := ct_rightTrans_comp ν ⟨_, hi⟩ (Phi ⟨Lambda ψ, hl⟩)
  rw [bt_rightTrans_phi, bt_rightTrans_phi, bt_rightTrans_phi] at e
  have := congrArg bers e
  rwa [bers_Phi, bers_Phi] at this

/-- `A₂` membership of an `A∞` element is membership in the range of the inclusion. -/
theorem ctc_mem_range {a : AInf unitDisc} : AInf.toFun a ∈ A2fun unitDisc ↔ a ∈ range A2toAInf := by
  rw [A2toAInf_range]; rfl

theorem ctc_A2fun_sub {a b : AInf unitDisc} (ha : AInf.toFun a ∈ A2fun unitDisc)
    (hb : AInf.toFun b ∈ A2fun unitDisc) : AInf.toFun (a - b) ∈ A2fun unitDisc := by
  obtain ⟨a', rfl⟩ := ctc_mem_range.mp ha
  obtain ⟨b', rfl⟩ := ctc_mem_range.mp hb
  exact ctc_mem_range.mpr ⟨a' - b', map_sub A2toAInfCLM a' b'⟩

theorem ctc_A2fun_add {a b : AInf unitDisc} (ha : AInf.toFun a ∈ A2fun unitDisc)
    (hb : AInf.toFun b ∈ A2fun unitDisc) : AInf.toFun (a + b) ∈ A2fun unitDisc := by
  obtain ⟨a', rfl⟩ := ctc_mem_range.mp ha
  obtain ⟨b', rfl⟩ := ctc_mem_range.mp hb
  exact ctc_mem_range.mpr ⟨a' + b', map_add A2toAInfCLM a' b'⟩

/-- The point `h̃_ν⁻¹(φ)` lies in `V_μ` iff the transition value lies in the `A₂` ball, and then `h̃_μ` of it is
that value. -/
theorem ctc_mem_V_iff (μ ν : LinfStarBall) {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    (bersChartInv ν (A2toAInf φ) ∈ hilbertChartDomain μ ↔
      AInf.toFun (bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
          (beltramiInv (μ : LinfStar)))) ∈ A2fun unitDisc ∧
        toA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
          (beltramiInv (μ : LinfStar))))) ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) ∧
    (bersChartInv ν (A2toAInf φ) ∈ hilbertChartDomain μ →
      hilbertChart μ (bersChartInv ν (A2toAInf φ)) =
        toA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
          (beltramiInv (μ : LinfStar)))))) := by
  have hψ : ‖A2toAInf φ‖ < 2 := ct_A2toAInf_norm_lt hφ
  have hi : beltramiInv (μ : LinfStar) ∈ LinfStarBall := bc_beltramiInv_mem_ball μ.2
  obtain ⟨T, hT⟩ : ∃ T, T = bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
      (beltramiInv (μ : LinfStar))) := ⟨_, rfl⟩
  rw [← hT]
  have hkey : bers (rightTrans ⟨_, hi⟩ (bersChartInv ν (A2toAInf φ))) = T := by
    rw [hT]; exact ba_T_eq μ ν hi hψ
  -- forward direction, with the value
  have hfwd : bersChartInv ν (A2toAInf φ) ∈ hilbertChartDomain μ →
      ∃ φ₂ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)), A2toAInf φ₂ = T ∧
        hilbertChart μ (bersChartInv ν (A2toAInf φ)) = φ₂ := by
    rintro ⟨φ₂, hφ₂, hp⟩
    have hn₂ := ct_A2toAInf_norm_lt hφ₂
    refine ⟨φ₂, hφ₂, ?_, ?_⟩
    · rw [← hkey, ← hp]
      simp only []
      rw [ct_bersChartInv_eq hn₂, bt_rightTrans_inv_left μ hi]
      exact (ahlfors_weill hn₂).choose_spec.symm
    · rw [← hp]
      exact ctc_chart_left_inv μ φ₂ hφ₂
  have hval : ∀ φ₂ : A2 unitDisc, A2toAInf φ₂ = T → toA2 unitDisc (AInf.toFun T) = φ₂ := by
    intro φ₂ h
    apply A2toAInf_injective
    rw [ctb_A2toAInf_toA2 (ctc_mem_range.mpr ⟨φ₂, h⟩), h]
  refine ⟨⟨fun hp => ?_, fun hT2 => ?_⟩, fun hp => ?_⟩
  · obtain ⟨φ₂, hφ₂, h1, -⟩ := hfwd hp
    refine ⟨ctc_mem_range.mpr ⟨φ₂, h1⟩, ?_⟩
    rw [hval φ₂ h1]; exact hφ₂
  · obtain ⟨hTm, hTb⟩ := hT2
    refine ⟨toA2 unitDisc (AInf.toFun T), hTb, ?_⟩
    simp only []
    have hA := ctb_A2toAInf_toA2 hTm
    rw [hA]
    have hn' : ‖T‖ < 2 := by rw [← hA]; exact ct_A2toAInf_norm_lt hTb
    have e3 : Phi ⟨Lambda T, Lambda_mem_ball hn'⟩ = rightTrans ⟨_, hi⟩ (bersChartInv ν (A2toAInf φ)) := by
      apply bers_injective
      rw [(ahlfors_weill hn').choose_spec, hkey]
    rw [ct_bersChartInv_eq hn', e3]
    exact bt_rightTrans_inv_right μ hi _
  · obtain ⟨φ₂, -, h1, h2⟩ := hfwd hp
    rw [h2, hval φ₂ h1]

/-- The image `h̃_ν(V_μ ∩ V_ν)`, described pointwise. -/
theorem ctc_image_iff (μ ν : LinfStarBall) (φ : A2 unitDisc) :
    φ ∈ hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν) ↔
      φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∧ bersChartInv ν (A2toAInf φ) ∈ hilbertChartDomain μ := by
  constructor
  · rintro ⟨p, ⟨hpμ, ⟨φ', hφ', rfl⟩⟩, rfl⟩
    rw [ctc_chart_left_inv ν φ' hφ']
    exact ⟨hφ', hpμ⟩
  · rintro ⟨hφ, h⟩
    exact ⟨_, ⟨h, ⟨φ, hφ, rfl⟩⟩, ctc_chart_left_inv ν φ hφ⟩

/-- One side of Theorem 2.10: `h̃_ν(V_μ ∩ V_ν)` is open and `h̃_μ ∘ h̃_ν⁻¹` is holomorphic on it. -/
theorem ctc_one_side (μ ν : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) (hν : (ν : LinfStar) ∈ groupO) :
    IsOpen (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      DifferentiableOn ℂ (fun φ => hilbertChart μ (bersChartInv ν (A2toAInf φ)))
        (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) := by
  have hi : beltramiInv (μ : LinfStar) ∈ LinfStarBall := bc_beltramiInv_mem_ball μ.2
  have hκ : beltramiMul (ν : LinfStar) (beltramiInv (μ : LinfStar)) ∈ LinfStarBall := bg_mul_mem_ball hi ν.2
  have hκO : beltramiMul (ν : LinfStar) (beltramiInv (μ : LinfStar)) ∈ groupO :=
    groupO_mul_mem hν (groupO_inv_mem hμ)
  obtain ⟨K, hK⟩ : ∃ K : LinfStarBall, K = ⟨_, hκ⟩ := ⟨_, rfl⟩
  have hKO : (K : LinfStar) ∈ groupO := by rw [hK]; exact hκO
  obtain ⟨hb1, hb2⟩ := ctb_thm_2_13_b12 K hKO
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (π / 3) := ⟨_, rfl⟩
  -- the transition value through the chart at `K`
  have hTK : ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
      bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar)) (beltramiInv (μ : LinfStar))) =
        bers (bersChartInv K (A2toAInf φ)) := by
    intro φ hφ
    have hψ := ct_A2toAInf_norm_lt hφ
    rw [ctc_T_assoc μ ν hψ, ctb_bers_chartInv K hψ, hK]
  have hS := ctc_image_iff μ ν
  by_cases hc : AInf.toFun (bersPhi (K : LinfStar)) ∈ A2fun unitDisc
  · -- the transition is `Θ = Θ₀ + const`
    obtain ⟨c, hc'⟩ : ∃ c : A2 unitDisc, c = toA2 unitDisc (AInf.toFun (bersPhi (K : LinfStar))) := ⟨_, rfl⟩
    have hΘ : ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        AInf.toFun (bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
          (beltramiInv (μ : LinfStar)))) ∈ A2fun unitDisc ∧
        toA2 unitDisc (AInf.toFun (bersPhi (beltramiMul (beltramiMul (Lambda (A2toAInf φ)) (ν : LinfStar))
          (beltramiInv (μ : LinfStar))))) =
          toA2 unitDisc (AInf.toFun (bers (bersChartInv K (A2toAInf φ)) - bersPhi (K : LinfStar))) + c := by
      intro φ hφ
      rw [hTK φ hφ]
      have hm : AInf.toFun (bers (bersChartInv K (A2toAInf φ))) ∈ A2fun unitDisc := by
        have := ctc_A2fun_add (hb1 φ hφ) hc
        rwa [sub_add_cancel] at this
      refine ⟨hm, ?_⟩
      apply A2toAInf_injective
      rw [show ∀ a b : A2 unitDisc, A2toAInf (a + b) = A2toAInf a + A2toAInf b from
        fun a b => map_add A2toAInfCLM a b, ctb_A2toAInf_toA2 hm,
        ctb_A2toAInf_toA2 (hb1 φ hφ), hc', ctb_A2toAInf_toA2 hc, sub_add_cancel]
    obtain ⟨Θ, hΘdef⟩ : ∃ Θ : A2 unitDisc → A2 unitDisc, ∀ φ, Θ φ =
        toA2 unitDisc (AInf.toFun (bers (bersChartInv K (A2toAInf φ)) - bersPhi (K : LinfStar))) + c :=
      ⟨_, fun _ => rfl⟩
    have hΘd : DifferentiableOn ℂ Θ (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
      (hb2.add_const c).congr (fun φ _ => hΘdef φ)
    have hset : hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν) =
        ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∩ Θ ⁻¹' ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) := by
      ext φ
      rw [hS φ]
      constructor
      · rintro ⟨hφ, h⟩
        obtain ⟨-, h2⟩ := ((ctc_mem_V_iff μ ν hφ).1.mp h)
        refine ⟨hφ, ?_⟩
        rw [mem_preimage, hΘdef, ← (hΘ φ hφ).2]
        exact h2
      · rintro ⟨hφ, h⟩
        refine ⟨hφ, (ctc_mem_V_iff μ ν hφ).1.mpr ⟨(hΘ φ hφ).1, ?_⟩⟩
        rw [(hΘ φ hφ).2, ← hΘdef]
        exact h
    rw [hset]
    refine ⟨hΘd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball, ?_⟩
    refine (hΘd.mono inter_subset_left).congr ?_
    rintro φ ⟨hφ, hφ2⟩
    have hp : bersChartInv ν (A2toAInf φ) ∈ hilbertChartDomain μ := ((hS φ).mp (by
      rw [hset]; exact ⟨hφ, hφ2⟩)).2
    rw [(ctc_mem_V_iff μ ν hφ).2 hp, (hΘ φ hφ).2, ← hΘdef]
  · -- the overlap is empty: the transition differs from `(β ∘ Φ)(κ)` by an element of `A₂` (`l29r_restricted`),
    -- so a point of the overlap would put `(β ∘ Φ)(κ)` in `A₂`
    have hempty : hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν) = ∅ := by
      ext φ
      simp only [mem_empty_iff_false, iff_false]
      intro hφS
      obtain ⟨hφ, h⟩ := (hS φ).mp hφS
      obtain ⟨h1, -⟩ := (ctc_mem_V_iff μ ν hφ).1.mp h
      rw [hTK φ hφ] at h1
      apply hc
      have := ctc_A2fun_sub h1 (hb1 φ hφ)
      rwa [sub_sub_cancel] at this
    rw [hempty]
    exact ⟨isOpen_empty, differentiableOn_empty⟩

/-- **Theorem 2.10** (verbatim). -/
theorem ctc_thm_2_10 (μ ν : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) (hν : (ν : LinfStar) ∈ groupO) :
    IsOpen (hilbertChart μ '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      IsOpen (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      DifferentiableOn ℂ (fun φ => hilbertChart μ (bersChartInv ν (A2toAInf φ)))
        (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      DifferentiableOn ℂ (fun φ => hilbertChart ν (bersChartInv μ (A2toAInf φ)))
        (hilbertChart μ '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) := by
  obtain ⟨h1, h2⟩ := ctc_one_side μ ν hμ hν
  obtain ⟨h3, h4⟩ := ctc_one_side ν μ hν hμ
  rw [inter_comm] at h3 h4
  exact ⟨h3, h1, h2, h4⟩

/-- `componentT_spec`, conjunct 1, inclusion `⊆`: the Bers image of a component lies in `(β(p) + A₂(𝔻)) ∩ β(T(1))`.
(The reverse inclusion needs local invertibility of the Bers chart in `A₂` coordinates.) -/
theorem ctd_componentT_spec_one_subset (p : T1) :
    bers '' componentT p ⊆ {φ | ∃ ψ : A2 unitDisc, φ = bers p + A2toAInf ψ} ∩ range bers := by
  rintro φ ⟨q, hq, rfl⟩
  refine ⟨?_, ⟨q, rfl⟩⟩
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  have h1 := ctb_bers_continuous_hilbert.image_connectedComponent_subset p ⟨q, hq, rfl⟩
  rw [hilbertTopologyA_component] at h1
  obtain ⟨ψ, -, hψ⟩ := h1
  exact ⟨ψ, hψ.symm⟩

end TakhtajanTeo
