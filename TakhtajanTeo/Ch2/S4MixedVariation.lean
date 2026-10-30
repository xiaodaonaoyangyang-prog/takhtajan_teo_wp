import TakhtajanTeo.Ch2.S4PrincipalValue

/-! # Parameter variation commutes with spatial Wirtinger derivatives (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- H11
theorem s4hv_dz_circleIntegral {F : ℂ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (sphere c R ×ˢ U))
    (hd : ∀ t ∈ sphere c R, DifferentiableOn ℝ (F t) U)
    (hD : ContinuousOn (fun p : ℂ × ℂ => fderiv ℝ (F p.1) p.2) (sphere c R ×ˢ U))
    {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun w => ∮ t in C(c, R), F t w) z ∧
      dz (fun w => ∮ t in C(c, R), F t w) z = ∮ t in C(c, R), dz (F t) z := by
  let t := circleMap c R
  let a := deriv (circleMap c R)
  have ht : ∀ θ : ℝ, t θ ∈ sphere c R := circleMap_mem_sphere c hR.le
  have htc : Continuous t := continuous_circleMap c R
  have hac : Continuous a := by
    change Continuous (fun θ : ℝ => deriv (circleMap c R) θ)
    simp only [deriv_circleMap]
    fun_prop
  have hFc : ∀ w ∈ U, Continuous (fun θ : ℝ => a θ * F (t θ) w) := by
    intro w hw
    apply hac.mul
    apply continuousOn_univ.mp
    exact hc.comp (f := fun θ : ℝ => (t θ, w)) (htc.prodMk continuous_const).continuousOn
      (fun θ _ => ⟨ht θ, hw⟩)
  have hDc : ContinuousOn (fun p : ℝ × ℂ => a p.1 • fderiv ℝ (F (t p.1)) p.2) (univ ×ˢ U) := by
    have hprod := ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_continuousOn
      (hac.comp continuous_fst).continuousOn).clm_comp
      (hD.comp (f := fun p : ℝ × ℂ => (t p.1, p.2))
        ((htc.comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun (p : ℝ × ℂ) (hp : p ∈ (univ : Set ℝ) ×ˢ U) => ⟨ht p.1, hp.2⟩))
    exact hprod.congr fun p hp => by ext v; rfl
  have hDθ : ∀ w ∈ U, Continuous (fun θ : ℝ => a θ • fderiv ℝ (F (t θ)) w) := by
    intro w hw
    apply continuousOn_univ.mp
    exact hDc.comp (f := fun θ : ℝ => (θ, w)) (continuous_id.prodMk continuous_const).continuousOn
      (fun θ _ => ⟨mem_univ θ, hw⟩)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).prod (isCompact_closedBall z ρ)
    |>.exists_bound_of_continuousOn (hDc.mono (prod_mono (subset_univ _) hρU))
  have hI : HasFDerivAt (fun w => ∮ u in C(c, R), F u w)
      (∫ θ : ℝ in 0..2 * π, a θ • fderiv ℝ (F (t θ)) z) z := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (F := fun w θ => a θ * F (t θ) w)
      (F' := fun w θ => a θ • fderiv ℝ (F (t θ)) w) (bound := fun _ => M) (ball_mem_nhds z hρ)
    · filter_upwards [hU.mem_nhds hz] with w hw
      exact (hFc w hw).aestronglyMeasurable
    · exact (hFc z hz).intervalIntegrable 0 (2 * π)
    · exact (hDθ z hz).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with θ hθ
      intro w hw
      have hθ' : θ ∈ Icc (0 : ℝ) (2 * π) := by
        rw [uIoc_of_le Real.two_pi_pos.le] at hθ
        exact ⟨hθ.1.le, hθ.2⟩
      exact hM (θ, w) ⟨hθ', ball_subset_closedBall hw⟩
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun θ w hw =>
        (((hd (t θ) (ht θ)).differentiableAt (hU.mem_nhds (hρU (ball_subset_closedBall hw)))).hasFDerivAt.const_smul (a θ))
  let L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ 1 - I • ContinuousLinearMap.apply ℝ ℂ I)
  have hLd (f : ℂ → ℂ) (w : ℂ) : L (fderiv ℝ f w) = dz f w := by
    simp [L, dz, div_eq_inv_mul]
  have hLs (b : ℂ) (A : ℂ →L[ℝ] ℂ) : L (b • A) = b * L A := by
    change (2 : ℂ)⁻¹ * (b * A 1 - I * (b * A I)) = b * ((2 : ℂ)⁻¹ * (A 1 - I * A I))
    ring
  refine ⟨hI.differentiableAt, ?_⟩
  rw [← hLd, hI.fderiv, ← L.intervalIntegral_comp_comm ((hDθ z hz).intervalIntegrable 0 (2 * π))]
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ hθ
  change L (a θ • fderiv ℝ (F (t θ)) z) = a θ * dz (F (t θ)) z
  rw [hLs, hLd]

-- H12
theorem s4hv_cauchy_dz_commute {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hc : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U))
    (hs : ∀ t ∈ P, DifferentiableOn ℝ (F t) U)
    (hD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U))
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hpz : ∀ z ∈ U, DifferentiableOn ℂ (fun t => dz (F t) z) P)
    {e : ℂ} (he : e ∈ P) :
    DifferentiableOn ℝ (fun z => deriv (fun t => F t z) e) U ∧
      ∀ z ∈ U, dz (fun w => deriv (fun t => F t w) e) z = deriv (fun t => dz (F t) z) e := by
  obtain ⟨R, hR, hRP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds he)
  let K := fun t : ℂ => 1 / (t - e) ^ 2
  let A := fun t w : ℂ => K t * F t w
  let J := fun w : ℂ => ∮ t in C(e, R), A t w
  let V := fun w : ℂ => deriv (fun t => F t w) e
  let C : ℂ := 2 * π * I
  have hC : C ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hSP : sphere e R ⊆ P := sphere_subset_closedBall.trans hRP
  have hne : ∀ t ∈ sphere e R, t - e ≠ 0 := by
    intro t ht heq
    have hn : ‖t - e‖ = R := by simpa only [mem_sphere, dist_eq_norm] using ht
    rw [heq, norm_zero] at hn
    exact hR.ne' hn.symm
  have hK : ContinuousOn K (sphere e R) :=
    continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun t ht => pow_ne_zero _ (hne t ht))
  have hAc : ContinuousOn (fun q : ℂ × ℂ => A q.1 q.2) (sphere e R ×ˢ U) :=
    (hK.comp continuousOn_fst (fun q hq => hq.1)).mul (hc.mono (prod_mono hSP Subset.rfl))
  have hAs : ∀ t ∈ sphere e R, DifferentiableOn ℝ (A t) U :=
    fun t ht => (hs t (hSP ht)).const_mul (K t)
  have hAD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (A q.1) q.2) (sphere e R ×ˢ U) := by
    have hw : ContinuousOn (fun q : ℂ × ℂ =>
        ((ContinuousLinearMap.mul ℝ ℂ) (K q.1)).comp (fderiv ℝ (F q.1) q.2)) (sphere e R ×ˢ U) :=
      ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_continuousOn
        (hK.comp continuousOn_fst (fun q hq => hq.1))).clm_comp
        (hD.mono (prod_mono hSP Subset.rfl))
    refine hw.congr ?_
    intro q hq
    have hdq := (hs q.1 (hSP hq.1)).differentiableAt (hU.mem_nhds hq.2)
    change fderiv ℝ (fun w => K q.1 * F q.1 w) q.2 = _
    rw [fderiv_const_mul hdq]
    ext v
    rfl
  have hJV : ∀ w ∈ U, J w = C * V w := by
    intro w hw
    simpa only [J, A, K, C, V, smul_eq_mul] using
      ((hp w hw).mono hRP).deriv_eq_smul_circleIntegral hR
  have hDformula : ∀ w ∈ U, (∮ t in C(e, R), K t * dz (F t) w) =
      C * deriv (fun t => dz (F t) w) e := by
    intro w hw
    simpa only [K, C, smul_eq_mul] using ((hpz w hw).mono hRP).deriv_eq_smul_circleIntegral hR
  have key : ∀ z ∈ U, DifferentiableAt ℝ V z ∧
      dz V z = deriv (fun t => dz (F t) z) e := by
    intro z hz
    have hJz := s4hv_dz_circleIntegral hU hR hAc hAs hAD hz
    have hVe : V =ᶠ[𝓝 z] (fun w => C⁻¹ * J w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      rw [hJV w hw, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
    have hVd : DifferentiableAt ℝ V z := (hJz.1.const_mul C⁻¹).congr_of_eventuallyEq hVe
    have hJdz : dz J z = C * deriv (fun t => dz (F t) z) e := by
      calc dz J z = ∮ t in C(e, R), dz (A t) z := hJz.2
        _ = ∮ t in C(e, R), K t * dz (F t) z := by
          apply circleIntegral.integral_congr hR.le
          intro t ht
          exact wp_dz_const_mul ((hs t (hSP ht)).differentiableAt (hU.mem_nhds hz)) (K t)
        _ = _ := hDformula z hz
    have hJe : J =ᶠ[𝓝 z] (fun w => C * V w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hJV w hw
    have hdz := (t203_c1_dz_congr hJe).1
    rw [wp_dz_const_mul hVd C] at hdz
    exact ⟨hVd, mul_left_cancel₀ hC (hdz.symm.trans hJdz)⟩
  exact ⟨fun z hz => (key z hz).1.differentiableWithinAt, fun z hz => (key z hz).2⟩

-- H13
theorem s4hv_parameter_dz3_commute {F : ℂ → ℂ → ℂ} {P U : Set ℂ}
    (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 3 (F t) U)
    (hc : ∀ j ≤ 3, ContinuousOn
      (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    {e z : ℂ} (he : e ∈ P) (hz : z ∈ U) :
    deriv (fun t => dz (dz (dz (F t))) z) e =
      dz (dz (dz (fun w => deriv (fun t => F t w) e))) z := by
  have step {G : ℂ → ℂ → ℂ} {n : ℕ}
      (hGp : ∀ w ∈ U, DifferentiableOn ℂ (fun t => G t w) P)
      (hGs : ∀ t ∈ P, ContDiffOn ℝ (n + 1 : ℕ) (G t) U)
      (hGc : ∀ j ≤ n + 1, ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (G q.1) q.2) (P ×ˢ U)) :
      ∀ w ∈ U, dz (fun v => deriv (fun t => G t v) e) w = deriv (fun t => dz (G t) w) e := by
    have hraw := wr_d2a_der hU hGs hGc (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ))
    have hFD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (G q.1) q.2) (P ×ˢ U) := by
      apply wr_d2a_zero (a := fun t => fderiv ℝ (G t))
      simpa only [ContinuousLinearMap.id_apply] using hraw.2 0 (Nat.zero_le n)
    exact (s4hv_cauchy_dz_commute hP hU (wr_d2a_zero (hGc 0 (by omega)))
      (fun t ht => (hGs t ht).differentiableOn (by norm_cast)) hFD hGp
      (fun w hw => s4v_param_dz_holomorphic hP hU hGp hGs hGc hw) he).2
  have h0 := step (n := 2) hp hs hc
  have hreg1 := s4v_dz_family_regular (n := 2) hU hs hc
  have hp1 : ∀ w ∈ U, DifferentiableOn ℂ (fun t => dz (F t) w) P :=
    fun w hw => s4v_param_dz_holomorphic hP hU hp hs hc hw
  have h1 := step (n := 1) hp1 hreg1.1 hreg1.2
  have hreg2 := s4v_dz_family_regular (n := 1) hU hreg1.1 hreg1.2
  have hp2 : ∀ w ∈ U, DifferentiableOn ℂ (fun t => dz (dz (F t)) w) P :=
    fun w hw => s4v_param_dz_holomorphic hP hU hp1 hreg1.1 hreg1.2 hw
  have h2 := step (n := 0) hp2 hreg2.1 hreg2.2
  have heq1 : (fun w => deriv (fun t => dz (F t) w) e) =ᶠ[𝓝 z]
      dz (fun w => deriv (fun t => F t w) e) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (h0 w hw).symm
  have heq2 : (fun w => deriv (fun t => dz (dz (F t)) w) e) =ᶠ[𝓝 z]
      dz (dz (fun w => deriv (fun t => F t w) e)) := by
    filter_upwards [hU.mem_nhds hz, heq1.eventually_nhds] with w hw heq
    exact (h1 w hw).symm.trans ((t203_c1_dz_congr heq).1)
  exact (h2 z hz).symm.trans ((t203_c1_dz_congr heq2).1)

end Ch2
end TakhtajanTeo
