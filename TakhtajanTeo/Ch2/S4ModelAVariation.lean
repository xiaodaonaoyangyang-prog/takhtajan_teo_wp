import TakhtajanTeo.Ch2.S4ParameterJets

/-! # Actual Model A Schwarzian variation (`s4ma_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- M1
theorem s4ma_coefficients {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    ∃ m : ℂ → ℂ, IsBeltramiCoeff m univ ‖ν‖ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m unitDiscExterior ∧
      (m =ᵐ[volume] unitDiscExterior.indicator (extA ν)) ∧
      ∀ e : ℂ, extA (e • ν) =ᵐ[volume]
        (fun u => e * m u + conj e * unitDisc.indicator (extA ν) u) := by
  obtain ⟨g, hg, he⟩ := wr_harm_rep hν
  let m := unitDiscExterior.indicator g
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hm : m =ᵐ[volume] unitDiscExterior.indicator (extA ν) := by
    filter_upwards [(ae_restrict_iff' hE).mp he] with u hu
    by_cases h : u ∈ unitDiscExterior
    · simp only [m, indicator_of_mem h, extA_eq_on_exterior ν h, hu h]
    · simp only [m, indicator_of_notMem h]
  have hBC : IsBeltramiCoeff (unitDiscExterior.indicator (extA ν)) univ ‖ν‖ :=
    ⟨(extA_isBeltramiCoeff ν).1.indicator hE,
      (extA_isBeltramiCoeff ν).2.mono fun u hu => (norm_indicator_le_norm_self _ _).trans hu⟩
  refine ⟨m, wr_isBC_congr hBC hm.symm, hg.congr (fun u hu => indicator_of_mem hu g), hm, ?_⟩
  intro e
  filter_upwards [wr_extA_smul e ν, hm] with u hu hmu
  have hfirst : (if 1 < ‖u‖ then ν u else 0) = unitDiscExterior.indicator (extA ν) u := by
    by_cases h : 1 < ‖u‖
    · rw [ite_eq_left h, indicator_of_mem (show u ∈ unitDiscExterior from h), extA_eq_on_exterior ν h]
    · rw [ite_eq_right h, indicator_of_notMem (show u ∉ unitDiscExterior from h)]
  have hsecond : (if ‖u‖ < 1 then conj (ν (refl u)) * u ^ 2 / conj u ^ 2 else 0) =
      unitDisc.indicator (extA ν) u := by
    by_cases h : ‖u‖ < 1
    · rw [ite_eq_left h, indicator_of_mem (show u ∈ unitDisc from mem_ball_zero_iff.mpr h)]
      simp only [extA, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]
    · rw [ite_eq_right h, indicator_of_notMem (show u ∉ unitDisc from fun hx => h (mem_ball_zero_iff.mp hx))]
  rw [hu, hfirst, hsecond, hmu]

-- M2
theorem s4ma_schwarzianDz_mobius {f : ℂ → ℂ} {z a b c d : ℂ}
    (hf : ContDiffAt ℝ 3 f z) (hf' : dz f z ≠ 0)
    (hdet : a * d - b * c ≠ 0) (hp : c * f z + d ≠ 0) :
    schwarzianDz (fun u => (a * f u + b) / (c * f u + d)) z = schwarzianDz f z := by
  have hM : AnalyticAt ℂ (fun u => (a * u + b) / (c * u + d)) (f z) :=
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hp
  have hMd : deriv (fun u => (a * u + b) / (c * u + d)) (f z) ≠ 0 := by
    rw [(hasDerivAt_mobius hp).deriv]
    exact div_ne_zero hdet (pow_ne_zero 2 hp)
  have h := e41_schw_left hM hMd hf hf'
  rw [schwarzianHol_mobius hdet hp, zero_mul, zero_add] at h
  exact h

-- M3
theorem s4ma_wA_schwarzian {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ}
    (hp : wAS μ (z : ExtPlane) ≠ extInf)
    (hc : ContDiffAt ℝ 3 (normalizedSolution (extA μ)) z)
    (hd : dz (normalizedSolution (extA μ)) z ≠ 0) :
    schwarzianDz (wA μ) z = schwarzianDz (normalizedSolution (extA μ)) z := by
  obtain ⟨M, hM, W, hW, hfin, _⟩ := wA_spec hμ
  have hNW : normalizedSolution (extA μ) = W :=
    qcv_ns_eq (norm_nonneg μ) (bc_norm_lt_one hμ) (extA_isBeltramiCoeff μ) hW
  rw [← hNW] at hfin
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hden : c * normalizedSolution (extA μ) z + d ≠ 0 := by
    intro hzero
    exact hp ((hfin z).trans (mobiusExt_coe_of_eq_zero hzero))
  have he : wA μ = fun u =>
      (a * normalizedSolution (extA μ) u + b) / (c * normalizedSolution (extA μ) u + d) := by
    funext u
    show finPart (wAS μ (u : ExtPlane)) = _
    rw [hfin u]
    by_cases hu : c * normalizedSolution (extA μ) u + d = 0
    · rw [mobiusExt_coe_of_eq_zero hu]
      simp [finPart, hu]
    · rw [mobiusExt_coe hu]
      rfl
  rw [he]
  exact s4ma_schwarzianDz_mobius hc hd hdet hden

-- M4
theorem s4ma_diagonal_dzbar {G : ℂ × ℂ → ℂ}
    (hG : DifferentiableAt ℝ G (0, 0))
    (h₁ : DifferentiableAt ℂ (fun a : ℂ => G (a, 0)) 0)
    (h₂ : DifferentiableAt ℂ (fun b : ℂ => G (0, b)) 0) :
    dzbar (fun e => G (e, conj e)) 0 = deriv (fun b : ℂ => G (0, b)) 0 := by
  let L := fderiv ℝ G (0, 0)
  have he₁ : HasFDerivAt (fun a : ℂ => (a, (0 : ℂ)))
      ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) 0 :=
    (hasFDerivAt_id 0).prodMk (hasFDerivAt_const 0 0)
  have he₂ : HasFDerivAt (fun b : ℂ => ((0 : ℂ), b))
      ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) 0 :=
    (hasFDerivAt_const 0 0).prodMk (hasFDerivAt_id 0)
  have hd₁ := hG.hasFDerivAt.comp (f := fun a : ℂ => (a, (0 : ℂ))) 0 he₁
  have hd₂ := hG.hasFDerivAt.comp (f := fun b : ℂ => ((0 : ℂ), b)) 0 he₂
  simp only [Function.comp_def] at hd₁ hd₂
  have hv₁ (v : ℂ) : L (v, 0) = deriv (fun a : ℂ => G (a, 0)) 0 * v := by
    calc
      _ = fderiv ℝ (fun a : ℂ => G (a, 0)) 0 v := by rw [hd₁.fderiv]; rfl
      _ = _ := by
        rw [fderiv_eq_dz_dzbar (h₁.restrictScalars ℝ), dz_eq_deriv h₁, (cauchyRiemann_iff.mp h₁).2]
        ring
  have hv₂ (v : ℂ) : L (0, v) = deriv (fun b : ℂ => G (0, b)) 0 * v := by
    calc
      _ = fderiv ℝ (fun b : ℂ => G (0, b)) 0 v := by rw [hd₂.fderiv]; rfl
      _ = _ := by
        rw [fderiv_eq_dz_dzbar (h₂.restrictScalars ℝ), dz_eq_deriv h₂, (cauchyRiemann_iff.mp h₂).2]
        ring
  have hadd (a b : ℂ) : L (a, b) = L (a, 0) + L (0, b) := by
    rw [← map_add]
    congr 1
    simp
  have he : HasFDerivAt (fun e : ℂ => (e, conj e))
      ((ContinuousLinearMap.id ℝ ℂ).prod (Complex.conjCLE : ℂ →L[ℝ] ℂ)) 0 :=
    (hasFDerivAt_id 0).prodMk (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hG' : HasFDerivAt G (fderiv ℝ G (0, 0)) ((0 : ℂ), conj (0 : ℂ)) := by
    simpa only [map_zero] using hG.hasFDerivAt
  have hd := hG'.comp (f := fun e : ℂ => (e, conj e)) 0 he
  simp only [Function.comp_def] at hd
  rw [dzbar, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  change (L (1, conj (1 : ℂ)) + I * L (I, conj I)) / 2 = _
  rw [map_one, Complex.conj_I]
  rw [hadd 1 1, hadd I (-I)]
  simp only [hv₁, hv₂]
  ring_nf
  simp [Complex.I_sq]
  ring

-- M5
theorem s4ma_ns2_schwarzian {m₁ m₂ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm₁ : IsBeltramiCoeff m₁ univ k) (hm₂ : IsBeltramiCoeff m₂ univ k)
    {U : Set ℂ} (hU : IsOpen U)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ U)
    (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ U) :
    let V : Set (ℂ × ℂ) := {P | (2 * k) * ‖P‖ < 1}
    let W := fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u)
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ => schwarzianDz (W q.1) q.2) (V ×ˢ U) ∧
    ∀ P ∈ V, ∀ z ∈ U,
      DifferentiableAt ℂ (fun a => schwarzianDz (W (a, P.2)) z) P.1 ∧
      DifferentiableAt ℂ (fun b => schwarzianDz (W (P.1, b)) z) P.2 := by
  let V : Set (ℂ × ℂ) := {P | (2 * k) * ‖P‖ < 1}
  let W := fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u)
  change ContinuousOn (fun q : (ℂ × ℂ) × ℂ => schwarzianDz (W q.1) q.2) (V ×ˢ U) ∧ _
  have hVo : IsOpen V := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hVk : ∀ P ∈ V, ∃ c < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ c := by
    intro P hP
    refine ⟨(2 * k) * ‖P‖, hP, ?_⟩
    simpa only [abs_of_nonneg hk, two_mul] using wr_coeff_lin hm₁ hm₂ P
  have hreg : (∀ P ∈ V, ContDiffOn ℝ 3 (W P) U) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (W q.1) q.2) (V ×ˢ U) :=
    wr_ns2_z_regular hm₁ hm₂ hU hs₁ hs₂ hVo hVk
  have hn : ∀ P ∈ V, ∀ z ∈ U, dz (W P) z ≠ 0 := by
    intro P hP z hz he
    have hj := wr_local_jacobian_pos hm₁ hm₂ hU hs₁ hs₂ (hVk P hP) hz
    change 0 < ‖dz (W P) z‖ ^ 2 - ‖dzbar (W P) z‖ ^ 2 at hj
    rw [he, norm_zero] at hj
    nlinarith [sq_nonneg ‖dzbar (W P) z‖]
  refine ⟨s4v_schwarzian_joint_continuous (F := W) hU hreg.1 hreg.2 hn, ?_⟩
  intro P hP z hz
  constructor
  · let A : Set ℂ := {a | (a, P.2) ∈ V}
    have hA : IsOpen A := hVo.preimage (continuous_id.prodMk continuous_const)
    have hparam : ∀ w ∈ U, DifferentiableOn ℂ (fun a => W (a, P.2) w) A :=
      fun w _ => (wr_ns2_holo hm₁ hm₂ hVo hVk w).1 P.2
    have hspace : ∀ a ∈ A, ContDiffOn ℝ 3 (W (a, P.2)) U := fun a ha => hreg.1 _ ha
    have hj : ∀ j ≤ 3, ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (W (q.1, P.2)) q.2) (A ×ˢ U) := by
      intro j hj
      exact (hreg.2 j hj).comp (f := fun q : ℂ × ℂ => ((q.1, P.2), q.2))
        ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
        (fun q hq => ⟨hq.1, hq.2⟩)
    exact s4v_param_schwarzian_holomorphic (F := fun a => W (a, P.2))
      hA hU hparam hspace hj hz hP (hn P hP z hz)
  · let B : Set ℂ := {b | (P.1, b) ∈ V}
    have hB : IsOpen B := hVo.preimage (continuous_const.prodMk continuous_id)
    have hparam : ∀ w ∈ U, DifferentiableOn ℂ (fun b => W (P.1, b) w) B :=
      fun w _ => (wr_ns2_holo hm₁ hm₂ hVo hVk w).2 P.1
    have hspace : ∀ b ∈ B, ContDiffOn ℝ 3 (W (P.1, b)) U := fun b hb => hreg.1 _ hb
    have hj : ∀ j ≤ 3, ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (W (P.1, q.1)) q.2) (B ×ˢ U) := by
      intro j hj
      exact (hreg.2 j hj).comp (f := fun q : ℂ × ℂ => ((P.1, q.1), q.2))
        ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
        (fun q hq => ⟨hq.1, hq.2⟩)
    exact s4v_param_schwarzian_holomorphic (F := fun b => W (P.1, b))
      hB hU hparam hspace hj hz hP (hn P hP z hz)

-- M6
theorem s4ma_schwarzianDz_hol {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hn : deriv f z ≠ 0) :
    schwarzianDz f z = schwarzianHol f z := by
  have h1 : dz f =ᶠ[𝓝 z] deriv f := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact dz_eq_deriv hw.differentiableAt
  have h2 : dz (dz f) =ᶠ[𝓝 z] deriv (deriv f) := by
    filter_upwards [h1.eventually_nhds, hf.deriv.eventually_analyticAt] with w hw hh
    rw [(t203_c1_dz_congr hw).1, dz_eq_deriv hh.differentiableAt]
  have hQ : AnalyticAt ℂ (fun w => deriv (deriv f) w / deriv f w) z :=
    hf.deriv.deriv.div hf.deriv hn
  have hD : dz (fun u => dz (dz f) u / dz f u) z =
      dz (fun u => deriv (deriv f) u / deriv f u) z :=
    (t203_c1_dz_congr (h2.div h1)).1
  unfold schwarzianDz schwarzianHol
  rw [hD, dz_eq_deriv hQ.differentiableAt,
    h2.self_of_nhds, h1.self_of_nhds]

-- M7
theorem s4ma_ns2_diagonal_variation {m₁ m₂ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm₁ : IsBeltramiCoeff m₁ univ k) (hm₂ : IsBeltramiCoeff m₂ univ k)
    {U : Set ℂ} (hU : IsOpen U)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ U)
    (hzero : ∀ u ∈ U, m₂ u = 0) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun e => schwarzianDz
      (normalizedSolution (fun u => e * m₁ u + conj e * m₂ u)) z) 0 ∧
    dzbar (fun e => schwarzianDz
      (normalizedSolution (fun u => e * m₁ u + conj e * m₂ u)) z) 0 =
        -(6 / π : ℂ) * ∫ u, m₂ u / (u - z) ^ 4 := by
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ U :=
    contDiffOn_const.congr (fun u hu => hzero u hu)
  let V : Set (ℂ × ℂ) := {P | (2 * k) * ‖P‖ < 1}
  let W := fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u)
  let G := fun P : ℂ × ℂ => schwarzianDz (W P) z
  obtain ⟨hC, hH⟩ := s4ma_ns2_schwarzian hk hm₁ hm₂ hU hs₁ hs₂
  change ContinuousOn (fun q : (ℂ × ℂ) × ℂ => schwarzianDz (W q.1) q.2) (V ×ˢ U) at hC
  let R : ℝ := 1 / (4 * (k + 1))
  have hR : 0 < R := by dsimp [R]; positivity
  have hRk : (2 * k) * R < 1 := by
    dsimp [R]
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hsub : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ⊆ V := by
    intro P hP
    have hn : ‖P‖ ≤ R := by
      rw [Prod.norm_mk]
      exact max_le (mem_closedBall_zero_iff.mp hP.1) (mem_closedBall_zero_iff.mp hP.2)
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_lt hRk
  have hGC : ContinuousOn G (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    hC.comp (f := fun P : ℂ × ℂ => (P, z)) (continuous_id.prodMk continuous_const).continuousOn
      (fun P hP => ⟨hsub hP, hz⟩)
  have hH₁ : ∀ b ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun a => G (a, b)) (ball 0 R) := by
    intro b hb a ha
    exact ((hH (a, b) (hsub ⟨ball_subset_closedBall ha, hb⟩) z hz).1).differentiableWithinAt
  have hH₂ : ∀ a ∈ closedBall (0 : ℂ) R, DifferentiableOn ℂ (fun b => G (a, b)) (ball 0 R) := by
    intro a ha b hb
    exact ((hH (a, b) (hsub ⟨ha, ball_subset_closedBall hb⟩) z hz).2).differentiableWithinAt
  have hGd : DifferentiableAt ℝ G (0, 0) :=
    ((wr_bidisc_contDiffOn (c := (0, 0)) hR hGC hH₁ hH₂).contDiffAt
      (ball_mem_nhds _ (by positivity))).differentiableAt (by norm_num)
  have hGd' : DifferentiableAt ℝ G ((0 : ℂ), conj (0 : ℂ)) := by simpa only [map_zero] using hGd
  have hdiag : DifferentiableAt ℝ (fun e : ℂ => G (e, conj e)) 0 :=
    hGd'.comp (f := fun e : ℂ => (e, conj e)) 0 (by fun_prop)
  have hsmall : ∀ᶠ b : ℂ in 𝓝 0, ‖b‖ * k < 1 := by
    have htc : Continuous (fun b : ℂ => ‖b‖ * k) := by fun_prop
    exact htc.continuousAt.eventually_lt continuousAt_const (by simp)
  have haxis : (fun b : ℂ => G (0, b)) =ᶠ[𝓝 0]
      (fun b : ℂ => schwarzianHol (normalizedSolution (fun u => b * m₂ u)) z) := by
    filter_upwards [hsmall] with b hb
    obtain ⟨hh, hi⟩ := s4v_normalized_holo hk hm₂ hU hzero hb
    dsimp only [G, W]
    simp only [zero_mul, zero_add]
    exact s4ma_schwarzianDz_hol (hh.analyticAt (hU.mem_nhds hz))
      (deriv_ne_zero_of_injOn hU hh hi.injOn hz)
  have hdaxis := (s4v_normalized_schwarzian_variation hk hm₂ hU hzero hz).congr_of_eventuallyEq haxis
  refine ⟨hdiag, ?_⟩
  exact (s4ma_diagonal_dzbar hGd
    (hH (0, 0) (by simp) z hz).1 (hH (0, 0) (by simp) z hz).2).trans hdaxis.deriv

-- M8
theorem s4ma_pole_absent_eventually (ν : LinfStar) (z : ℂ) :
    ∀ᶠ e in 𝓝 (0 : ℂ), wAS (e • ν) (z : ExtPlane) ≠ extInf := by
  have hμ : (0 : ℂ) • ν ∈ LinfStarBall := by simp [LinfStarBall]
  have hS : LinfStarBall ×ˢ (univ : Set ExtPlane) ∈
      𝓝 (((0 : ℂ) • ν, (z : ExtPlane)) : LinfStar × ExtPlane) :=
    prod_mem_nhds (isOpen_ball.mem_nhds hμ) univ_mem
  have hi : ContinuousAt (fun e : ℂ => ((e • ν, (z : ExtPlane)) : LinfStar × ExtPlane)) 0 := by fun_prop
  have hC : ContinuousAt (fun e : ℂ => wAS (e • ν) (z : ExtPlane)) 0 :=
    (AppA.acc_wAS_cont.continuousAt hS).comp
      (f := fun e : ℂ => ((e • ν, (z : ExtPlane)) : LinfStar × ExtPlane)) hi
  have hp : wAS ((0 : ℂ) • ν) (z : ExtPlane) ≠ extInf := by
    simp only [zero_smul, grp_wAS_zero, id_eq]
    exact OnePoint.coe_ne_infty z
  exact hC.eventually_ne hp

-- M9
theorem s4ma_wA_variation {ν : LinfStar} (hν : ν ∈ harmonicBeltrami)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    DifferentiableAt ℝ (fun e : ℂ => schwarzianDz (wA (e • ν)) z) 0 ∧
    dzbar (fun e : ℂ => schwarzianDz (wA (e • ν)) z) 0 =
      -(6 / π : ℂ) * ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
  obtain ⟨m₁, hm₁, hs₁, _, hcoeff⟩ := s4ma_coefficients hν
  let m₂ := unitDisc.indicator (extA ν)
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  have hm₂ : IsBeltramiCoeff m₂ univ ‖ν‖ :=
    ⟨(extA_isBeltramiCoeff ν).1.indicator hD,
      (extA_isBeltramiCoeff ν).2.mono fun u hu => (norm_indicator_le_norm_self _ _).trans hu⟩
  have hzero : ∀ u ∈ unitDiscExterior, m₂ u = 0 := by
    intro u hu
    exact indicator_of_notMem (fun h => (not_lt_of_ge hu.le) (mem_ball_zero_iff.mp h)) _
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ unitDiscExterior :=
    contDiffOn_const.congr (fun u hu => hzero u hu)
  let V : Set (ℂ × ℂ) := {P | (2 * ‖ν‖) * ‖P‖ < 1}
  let W := fun P : ℂ × ℂ => normalizedSolution (fun u => P.1 * m₁ u + P.2 * m₂ u)
  have hVo : IsOpen V := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hVk : ∀ P ∈ V, ∃ c < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ c := by
    intro P hP
    refine ⟨(2 * ‖ν‖) * ‖P‖, hP, ?_⟩
    simpa only [abs_of_nonneg (norm_nonneg ν), two_mul] using wr_coeff_lin hm₁ hm₂ P
  have hspace : ∀ P ∈ V, ContDiffOn ℝ 3 (W P) unitDiscExterior :=
    (wr_ns2_z_regular hm₁ hm₂ wp_exterior_isOpen hs₁ hs₂ hVo hVk).1
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, (2 * ‖ν‖) * ‖e‖ < 1 := by
    have hc : Continuous (fun e : ℂ => (2 * ‖ν‖) * ‖e‖) := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  have heq : (fun e : ℂ => schwarzianDz (wA (e • ν)) z) =ᶠ[𝓝 0]
      (fun e => schwarzianDz (W (e, conj e)) z) := by
    filter_upwards [hsmall, s4ma_pole_absent_eventually ν z] with e he hp
    have hP : (e, conj e) ∈ V := by simpa only [V, mem_ofPred_eq, Prod.norm_mk, norm_conj, max_self] using he
    have he1 : ‖e‖ * ‖ν‖ < 1 := by nlinarith [norm_nonneg e, norm_nonneg ν]
    have hμ : e • ν ∈ LinfStarBall := by simpa only [LinfStarBall, mem_ball_zero_iff, norm_smul] using he1
    have hN : normalizedSolution (extA (e • ν)) = W (e, conj e) :=
      qcv_ns_congr_ae (norm_nonneg _) (by simpa only [norm_smul] using he1)
        (extA_isBeltramiCoeff _) (hcoeff e)
    have hnc : ContDiffAt ℝ 3 (normalizedSolution (extA (e • ν))) z := by
      rw [hN]
      exact (hspace _ hP).contDiffAt (wp_exterior_isOpen.mem_nhds hz)
    have hnd : dz (normalizedSolution (extA (e • ν))) z ≠ 0 := by
      rw [hN]
      intro h0
      have hj := wr_local_jacobian_pos hm₁ hm₂ wp_exterior_isOpen hs₁ hs₂ (hVk _ hP) hz
      change 0 < ‖dz (W (e, conj e)) z‖ ^ 2 - ‖dzbar (W (e, conj e)) z‖ ^ 2 at hj
      rw [h0, norm_zero] at hj
      nlinarith [sq_nonneg ‖dzbar (W (e, conj e)) z‖]
    simpa only [hN] using s4ma_wA_schwarzian hμ hp hnc hnd
  have hplane := s4ma_ns2_diagonal_variation (norm_nonneg ν) hm₁ hm₂ wp_exterior_isOpen hs₁ hzero hz
  refine ⟨hplane.1.congr_of_eventuallyEq heq, ?_⟩
  calc
    _ = dzbar (fun e : ℂ => schwarzianDz (W (e, conj e)) z) 0 := dzbar_congr_of_eventuallyEq heq
    _ = -(6 / π : ℂ) * ∫ u, m₂ u / (u - z) ^ 4 := hplane.2
    _ = _ := by rw [s4v_reflected_kernel ν hz]

end Ch2
end TakhtajanTeo
