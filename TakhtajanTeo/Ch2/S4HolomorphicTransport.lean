import TakhtajanTeo.Ch2.S4SchwarzianLinearization

/-! # The actual holomorphic Model A and moving-base derivatives (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- H16
theorem s4hv_diagonal_dz {G : ℂ × ℂ → ℂ}
    (hG : DifferentiableAt ℝ G (0, 0))
    (h₁ : DifferentiableAt ℂ (fun a : ℂ => G (a, 0)) 0)
    (h₂ : DifferentiableAt ℂ (fun b : ℂ => G (0, b)) 0) :
    dz (fun e : ℂ => G (e, conj e)) 0 = deriv (fun a : ℂ => G (a, 0)) 0 := by
  let F := fun e : ℂ => G (e, conj e)
  have hG₀ : DifferentiableAt ℝ G ((0 : ℂ), conj (0 : ℂ)) := by simpa only [map_zero] using hG
  have hF : DifferentiableAt ℝ F 0 :=
    hG₀.comp (f := fun e : ℂ => (e, conj e)) 0 (by fun_prop)
  have hswap : DifferentiableAt ℝ (fun p : ℂ × ℂ => G (p.2, p.1)) (0, 0) :=
    hG.comp (f := fun p : ℂ × ℂ => (p.2, p.1)) (0, 0)
      (differentiableAt_snd.prodMk differentiableAt_fst)
  have hs := s4ma_diagonal_dzbar hswap h₂ h₁
  have hconj : HasFDerivAt (fun w : ℂ => conj w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hbar : dzbar (fun w : ℂ => conj w) 0 = 1 := by
    rw [t203_dzbar_of_hasFDerivAt hconj]
    change (conj (1 : ℂ) + I * conj I) / 2 = 1
    norm_num [Complex.conj_I, Complex.I_sq]
  have hid : dzbar (fun w : ℂ => w) 0 = 0 := by
    norm_num [dzbar, fderiv_id, Complex.I_sq]
  have hF₀ : DifferentiableAt ℝ F (conj (0 : ℂ)) := by simpa only [map_zero] using hF
  have hchain := eq6_2_dzbar_comp hconj.differentiableAt hF₀
  simp only [Function.comp_def, F, conj_conj, map_zero, hbar, hid, mul_one, mul_zero, add_zero] at hchain
  exact hchain.symm.trans hs

-- H17
theorem s4hv_ns2_diagonal_dz {m₁ m₂ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm₁ : IsBeltramiCoeff m₁ univ k) (hm₂ : IsBeltramiCoeff m₂ univ k)
    {U : Set ℂ} (hU : IsOpen U)
    (hs₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁ U)
    (hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ U) {z : ℂ} (hz : z ∈ U) :
    dz (fun e : ℂ => schwarzianDz
      (normalizedSolution (fun u => e * m₁ u + conj e * m₂ u)) z) 0 =
        dz (dz (dz (ahVar m₁))) z := by
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
  have hV₀ : ((0 : ℂ), (0 : ℂ)) ∈ V := by simp [V]
  have hdz := s4hv_diagonal_dz hGd (hH (0, 0) hV₀ z hz).1 (hH (0, 0) hV₀ z hz).2
  have haxis : (fun a : ℂ => G (a, 0)) =
      (fun a : ℂ => schwarzianDz (normalizedSolution (fun u => a * m₁ u)) z) := by
    funext a
    simp only [G, W, zero_mul, add_zero]
  rw [haxis] at hdz
  exact hdz.trans (s4hv_normalized_schwarzian_derivative hk hm₁ hU hs₁ hz).deriv

-- H18
theorem s4hv_wA_holomorphic_variation {ν : LinfStar} (hν : ν ∈ harmonicBeltrami)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    dz (fun e : ℂ => schwarzianDz (wA (e • ν)) z) 0 = dz (dz (dz (ahVar (extB ν)))) z := by
  obtain ⟨m₁, hm₁, hs₁, hme, hcoeff⟩ := s4ma_coefficients hν
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
  have hflat : m₁ =ᵐ[volume] extB ν := by
    filter_upwards [hme] with u hu
    rw [hu]
    by_cases h : u ∈ unitDiscExterior
    · simp only [indicator_of_mem h, extB, extA_eq_on_exterior ν h]
    · simp only [indicator_of_notMem h, extB]
  have hvar : ahVar m₁ = ahVar (extB ν) := funext fun u => qcv_ahVar_congr_ae hflat u
  calc dz (fun e : ℂ => schwarzianDz (wA (e • ν)) z) 0 =
        dz (fun e : ℂ => schwarzianDz (W (e, conj e)) z) 0 := (t203_c1_dz_congr heq).1
    _ = dz (dz (dz (ahVar m₁))) z :=
      s4hv_ns2_diagonal_dz (norm_nonneg ν) hm₁ hm₂ wp_exterior_isOpen hs₁ hs₂ hz
    _ = _ := by rw [hvar]

-- H19
theorem s4hv_plane_transition_derivative {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {y : ℂ}
    (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    HasDerivAt (fun e : ℂ => schwarzianDz (qcv_planeTransition (beltramiMul (e • ν) κ) κ) y)
      (dz (dz (dz (ahVar (ahT_dot (extB (qcv_rightDerivative κ ν))
        (extB κ) (qcv_planeSolution κ))))) y) 0 := by
  obtain ⟨m, he, hm, hms⟩ := s4pv_dot_smooth_rep hκ hν
  let k := ‖qcv_rightDerivative κ ν‖ / (1 - ‖κ‖ ^ 2)
  have hk : 0 ≤ k := by
    have hκn := bc_norm_lt_one hκ
    have hden : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    exact div_nonneg (norm_nonneg _) hden.le
  change IsBeltramiCoeff m univ k at hm
  have hd := s4hv_normalized_schwarzian_derivative hk hm (s4pv_plane_exterior_isOpen hκ) hms hy
  have hvar : ahVar m = ahVar (ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ)) :=
    funext fun w => qcv_ahVar_congr_ae he.symm w
  rw [hvar] at hd
  have hsmall₁ : ∀ᶠ e : ℂ in 𝓝 0, ‖e • ν‖ < 1 :=
    (continuous_id.smul continuous_const).norm.continuousAt.eventually_lt continuousAt_const (by simp)
  have hsmall₂ : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * k < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hsmall₁, hsmall₂] with e he₁ he₂
  rw [s4pv_plane_transition hκ ν he₁ he₂]
  have hcoeff : (fun w => e * ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ)
      (qcv_planeSolution κ) w) =ᵐ[volume] fun w => e * m w := by
    filter_upwards [he] with w hw
    rw [hw]
  rw [qcv_ns_congr_ae (mul_nonneg (norm_nonneg e) hk) he₂
    (s4v_linear_coeff (qcv_base_dot_isBeltramiCoeff hκ _) e) hcoeff]

end Ch2
end TakhtajanTeo
