import TakhtajanTeo.Ch2.WReg3
import TakhtajanTeo.Ch2.S4ParameterJets
import TakhtajanTeo.Ch1.BeltramiRealAnalytic

/-!
# S35Gamma: the off-centre welding factor `γ_t` (Program G, 下属6; shared with 下属3's W-NORM)

Statement file for audit. Helpers used by W-GSIDE (`s35_wgside`), W-GUNIF and W-NORM (`s35_wnorm`).

* G1 (generic). For a family `F t z` that is holomorphic in `t` and has `z`-jets up to order `n` jointly continuous,
  the `t`-derivative `∂_t F` has the same regularity, and `∂_t` commutes with `∂_z`. Route: a Cauchy integral in `t`,
  differentiated under the integral sign.
* G2. The Model A family `w_{a + t μ}` (`a`, `μ` harmonic) is the restriction to `P = (t, t̄)` of a family `U P z`
  that is holomorphic in each coordinate of `P`, `C³` in `z` on `𝔻*` with jointly continuous jets, and has
  `∂_z U ≠ 0`. Built from `wr3_*` and the three-point normalization, as `wr_joint_contDiff_A` is.
* G3. `w_{l * a⁻¹} ∘ w_a = w_l` on finite points, so `γ_t = w_{λ_t} = w_{a+tm} ∘ w_a⁻¹` (`grp_wAS_mul`).

Prefix `s35g_`. No new definitions.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- Differentiation under a circle integral: for `F s w` with `w`-derivatives jointly continuous on
`sphere c R × U`, `w ↦ ∮ k s • F s w` is real differentiable with the integrated derivative. -/
theorem s35g_circle_hasFDerivAt {F : ℂ → ℂ → ℂ} {k : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) (hk : ContinuousOn k (sphere c R))
    (hF : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (sphere c R ×ˢ U))
    (hd : ∀ s ∈ sphere c R, DifferentiableOn ℝ (F s) U)
    (hD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (sphere c R ×ˢ U)) {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun w => ∮ s in C(c, R), k s • F s w) L w₀ ∧
      ∀ v, L v = ∮ s in C(c, R), k s • fderiv ℝ (F s) w₀ v := by
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw₀)
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le
  have hK : IsCompact (sphere c R ×ˢ closedBall w₀ ε) := (isCompact_sphere c R).prod (isCompact_closedBall w₀ ε)
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn (hD.mono (prod_mono subset_rfl hεU))
  obtain ⟨Ck, hCk⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hk
  have hγ : Continuous (circleMap c R) := continuous_circleMap c R
  have hkc : Continuous (fun θ : ℝ => k (circleMap c R θ)) := hk.comp_continuous hγ hmem
  have hdc : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hcc : Continuous (fun θ : ℝ => deriv (circleMap c R) θ * k (circleMap c R θ)) := hdc.mul hkc
  have hball : ball w₀ ε ⊆ U := ball_subset_closedBall.trans hεU
  have hFc : ∀ w ∈ U, Continuous (fun θ : ℝ => F (circleMap c R θ) w) := fun w hw =>
    hF.comp_continuous (hγ.prodMk continuous_const) (fun θ => ⟨hmem θ, hw⟩)
  have hDc : Continuous (fun θ : ℝ => fderiv ℝ (F (circleMap c R θ)) w₀) :=
    hD.comp_continuous (hγ.prodMk continuous_const) (fun θ => ⟨hmem θ, hw₀⟩)
  have hF'c : Continuous (fun θ : ℝ => (ContinuousLinearMap.mul ℝ ℂ
      (deriv (circleMap c R) θ * k (circleMap c R θ))).comp (fderiv ℝ (F (circleMap c R θ)) w₀)) :=
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp hcc).clm_comp hDc
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (a := 0)
    (b := 2 * π) (F := fun w θ => deriv (circleMap c R) θ • (k (circleMap c R θ) • F (circleMap c R θ) w))
    (F' := fun w θ => (ContinuousLinearMap.mul ℝ ℂ
      (deriv (circleMap c R) θ * k (circleMap c R θ))).comp (fderiv ℝ (F (circleMap c R θ)) w))
    (bound := fun _ => R * Ck * Cf) (ball_mem_nhds w₀ hε)
    (Filter.eventually_of_mem (ball_mem_nhds w₀ hε) fun w hw =>
      (hdc.smul (hkc.smul (hFc w (hball hw)))).aestronglyMeasurable)
    ((hdc.smul (hkc.smul (hFc w₀ hw₀))).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ w hw => by
      have h1 : ‖deriv (circleMap c R) θ‖ = R := by
        rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hR]
      have h2 := hCk _ (hmem θ)
      have h3 := hCf (circleMap c R θ, w) ⟨hmem θ, ball_subset_closedBall hw⟩
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ _) (norm_nonneg _)).trans ?_
      rw [norm_mul, h1, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _) ((norm_nonneg _).trans h2)) hR.le)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ w hw => by
      have hdw := ((hd _ (hmem θ)) w (hball hw)).differentiableAt (hU.mem_nhds (hball hw))
      have h := (ContinuousLinearMap.mul ℝ ℂ
        (deriv (circleMap c R) θ * k (circleMap c R θ))).hasFDerivAt.comp w hdw.hasFDerivAt
      convert h using 1
      funext x
      simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul, mul_assoc])
  refine ⟨_, key, fun v => ?_⟩
  rw [ContinuousLinearMap.intervalIntegral_apply (hF'c.intervalIntegrable _ _)]
  simp only [circleIntegral, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul,
    mul_assoc]

/-- Joint continuity of `∂_t F` from joint continuity of `F` and holomorphy in `t` (Cauchy integral over a fixed
circle, `wr_param_circ_cont`). -/
theorem s35g_param_deriv_cont {F : ℂ → ℂ → ℂ} {P U : Set ℂ} (hP : IsOpen P)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hcF : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U)) :
    ContinuousOn (fun q : ℂ × ℂ => deriv (fun s => F s q.2) q.1) (P ×ˢ U) := by
  refine continuousOn_of_locally_continuousOn fun q hq => ?_
  obtain ⟨R, hR, hRP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds hq.1)
  refine ⟨ball q.1 R ×ˢ univ, isOpen_ball.prod isOpen_univ, ⟨mem_ball_self hR, mem_univ _⟩, ?_⟩
  have hS : sphere q.1 R ⊆ P := sphere_subset_closedBall.trans hRP
  have hh : ContinuousOn (fun p : ℂ × ℂ => F p.2 p.1) (U ×ˢ sphere q.1 R) :=
    hcF.comp continuous_swap.continuousOn (fun p hp => ⟨hS hp.2, hp.1⟩)
  have hI := wr_param_circ_cont (h := fun w ξ => F ξ w) hR hh (-2)
  have hI' : ContinuousOn (fun p : ℂ × ℂ =>
      (2 * π * I : ℂ)⁻¹ • ∮ ξ in C(q.1, R), (ξ - p.1) ^ (-2 : ℤ) • F ξ p.2) ((P ×ˢ U) ∩ (ball q.1 R ×ˢ univ)) :=
    (hI.comp continuous_swap.continuousOn (fun (p : ℂ × ℂ) (hp : p ∈ (P ×ˢ U) ∩ (ball q.1 R ×ˢ univ)) =>
      show (p.2, p.1) ∈ U ×ˢ ball q.1 R from ⟨hp.1.2, hp.2.1⟩)).const_smul ((2 * π * I : ℂ)⁻¹)
  refine hI'.congr fun p hpm => ?_
  show deriv (fun s => F s p.2) p.1 = (2 * π * I : ℂ)⁻¹ • ∮ ξ in C(q.1, R), (ξ - p.1) ^ (-2 : ℤ) • F ξ p.2
  rw [← two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hP hRP (hp p.2 hpm.1.2) hpm.2.1]
  congr 2

/-- The `w`-derivative of `∂_t F` is `∂_t` of the `w`-derivative (directional form). -/
theorem s35g_fderiv_param_deriv {F : ℂ → ℂ → ℂ} {P U : Set ℂ} (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 1 (F t) U)
    (hc : ∀ j ≤ 1, ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    {t z : ℂ} (ht : t ∈ P) (hz : z ∈ U) :
    DifferentiableAt ℝ (fun w => deriv (fun s => F s w) t) z ∧
      ∀ v, fderiv ℝ (fun w => deriv (fun s => F s w) t) z v = deriv (fun s => fderiv ℝ (F s) z v) t := by
  obtain ⟨R, hR, hRP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds ht)
  have hmemS : sphere t R ⊆ P := sphere_subset_closedBall.trans hRP
  have hcz : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U) := wr_d2a_zero (hc 0 (by norm_num))
  have hdiff : ∀ s ∈ P, DifferentiableOn ℝ (F s) U := fun s hs' => (hs s hs').differentiableOn one_ne_zero
  have hD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U) := by
    refine ((continuousMultilinearCurryFin1 ℝ ℂ ℂ).continuous.comp_continuousOn (hc 1 le_rfl)).congr ?_
    intro q _
    ext v
    simp [iteratedFDeriv_one_apply]
  set k : ℂ → ℂ := fun s => ((s - t) ^ 2)⁻¹ with hkdef
  have hk : ContinuousOn k (sphere t R) :=
    ((continuousOn_id.sub continuousOn_const).pow 2).inv₀ fun s hs' =>
      pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_sphere hs' hR.ne'))
  obtain ⟨L, hL, hLv⟩ := s35g_circle_hasFDerivAt hR hU hk (hcz.mono (prod_mono hmemS subset_rfl))
    (fun s hs' => hdiff s (hmemS hs')) (hD.mono (prod_mono hmemS subset_rfl)) hz
  have hrep : ∀ w ∈ U, deriv (fun s => F s w) t = (2 * π * I : ℂ)⁻¹ • ∮ s in C(t, R), k s • F s w :=
    fun w hw => (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hP hRP (hp w hw)
      (mem_ball_self hR)).symm
  have hev : (fun w => deriv (fun s => F s w) t) =ᶠ[𝓝 z]
      fun w => (2 * π * I : ℂ)⁻¹ • ∮ s in C(t, R), k s • F s w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) hrep
  have h := (ContinuousLinearMap.mul ℝ ℂ (2 * π * I : ℂ)⁻¹).hasFDerivAt.comp z hL
  have hΦ : HasFDerivAt (fun w => (2 * π * I : ℂ)⁻¹ • ∮ s in C(t, R), k s • F s w)
      ((ContinuousLinearMap.mul ℝ ℂ (2 * π * I : ℂ)⁻¹).comp L) z := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  have hDD := hΦ.congr_of_eventuallyEq hev
  refine ⟨hDD.differentiableAt, fun v => ?_⟩
  have hhol := s4v_param_fderiv_holomorphic hP hU hp hdiff hD hz v
  rw [hDD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', hLv,
    ← two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hP hRP hhol (mem_ball_self hR),
    smul_eq_mul]

/-- **G1a** (parameter regularity of `∂_t F`). If `t ↦ F t z` is holomorphic on `P` and the `z`-jets of `F t` up
to order `n` are jointly continuous on `P × U`, then `∂_t F` is holomorphic in `t`, `Cⁿ` in `z`, and its jets up to
order `n` are jointly continuous. -/
theorem s35g_param_deriv_regular {F : ℂ → ℂ → ℂ} {P U : Set ℂ} {n : ℕ} (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ n (F t) U)
    (hc : ∀ j ≤ n, ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U)) :
    (∀ z ∈ U, DifferentiableOn ℂ (fun t => deriv (fun s => F s z) t) P) ∧
      (∀ t ∈ P, ContDiffOn ℝ n (fun w => deriv (fun s => F s w) t) U) ∧
      ∀ j ≤ n, ContinuousOn
        (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (fun w => deriv (fun s => F s w) q.1) q.2) (P ×ˢ U) := by
  induction n generalizing F with
  | zero =>
    have hDc := s35g_param_deriv_cont hP hp (wr_d2a_zero (hc 0 le_rfl))
    refine ⟨fun z hz => (hp z hz).deriv hP, fun t ht => ?_, fun j hj => ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      exact hDc.comp (continuousOn_const.prodMk continuousOn_id) (fun w hw => ⟨ht, hw⟩)
    · obtain rfl : j = 0 := by omega
      refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp_continuousOn hDc).congr fun q _ => ?_
      simp [iteratedFDeriv_zero_eq_comp]
  | succ n ih =>
    have hs1 : ∀ t ∈ P, ContDiffOn ℝ 1 (F t) U := fun t ht => (hs t ht).of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hc1 : ∀ j ≤ 1, ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U) :=
      fun j hj => hc j (by omega)
    have hdiff : ∀ t ∈ P, DifferentiableOn ℝ (F t) U := fun t ht => (hs1 t ht).differentiableOn one_ne_zero
    have hD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U) := by
      refine ((continuousMultilinearCurryFin1 ℝ ℂ ℂ).continuous.comp_continuousOn (hc1 1 le_rfl)).congr ?_
      intro q _
      ext v
      simp [iteratedFDeriv_one_apply]
    have hv : ∀ v : ℂ, (∀ z ∈ U, DifferentiableOn ℂ (fun t => fderiv ℝ (F t) z v) P) ∧
        (∀ t ∈ P, ContDiffOn ℝ n (fun w => fderiv ℝ (F t) w v) U) ∧
        ∀ j ≤ n, ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (fun w => fderiv ℝ (F q.1) w v) q.2)
          (P ×ˢ U) := by
      intro v
      obtain ⟨h1, h2⟩ := wr_d2a_der hU (a := F) (S := P) (n := n) hs hc (ContinuousLinearMap.apply ℝ ℂ v)
      exact ⟨fun z hz => s4v_param_fderiv_holomorphic hP hU hp hdiff hD hz v, h1, h2⟩
    obtain ⟨-, h1B, h1C⟩ := ih (F := fun t w => fderiv ℝ (F t) w 1) (hv 1).1 (hv 1).2.1 (hv 1).2.2
    obtain ⟨-, hIB, hIC⟩ := ih (F := fun t w => fderiv ℝ (F t) w I) (hv I).1 (hv I).2.1 (hv I).2.2
    set A : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM with hA
    set B : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM with hB
    have hfd : ∀ t ∈ P, ∀ w ∈ U, fderiv ℝ (fun w => deriv (fun s => F s w) t) w =
        A (deriv (fun s => fderiv ℝ (F s) w 1) t) + B (deriv (fun s => fderiv ℝ (F s) w I) t) := by
      intro t ht w hw
      obtain ⟨-, hK⟩ := s35g_fderiv_param_deriv hP hU hp hs1 hc1 ht hw
      refine ContinuousLinearMap.ext fun v => ?_
      have hvdec : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
        apply Complex.ext <;> simp
      have e1 : (A (deriv (fun s => fderiv ℝ (F s) w 1) t) + B (deriv (fun s => fderiv ℝ (F s) w I) t)) v =
          (v.re : ℝ) • deriv (fun s => fderiv ℝ (F s) w 1) t + (v.im : ℝ) • deriv (fun s => fderiv ℝ (F s) w I) t :=
        rfl
      rw [e1]
      conv_lhs => rw [hvdec]
      rw [map_add, map_smul, map_smul, hK, hK]
    refine ⟨fun z hz => (hp z hz).deriv hP, fun t ht => ?_, fun j hj => ?_⟩
    · have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun w hw => (s35g_fderiv_param_deriv hP hU hp hs1 hc1 ht hw).1.differentiableWithinAt,
        fun h => by simp at h, ?_⟩
      exact ((A.contDiff.comp_contDiffOn (h1B t ht)).add (B.contDiff.comp_contDiffOn (hIB t ht))).congr
        fun w hw => hfd t ht w hw
    · rcases j with _ | i
      · have hDc := s35g_param_deriv_cont hP hp (wr_d2a_zero (hc 0 (by omega)))
        refine ((continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.continuous.comp_continuousOn hDc).congr
          fun q _ => ?_
        simp [iteratedFDeriv_zero_eq_comp]
      · have hi : i ≤ n := by omega
        set cA := (continuousMultilinearCurryRightEquiv' ℝ i ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => ℂ) ℂ (ℂ →L[ℝ] ℂ) A) with hcA
        set cB := (continuousMultilinearCurryRightEquiv' ℝ i ℂ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => ℂ) ℂ (ℂ →L[ℝ] ℂ) B) with hcB
        have hcont : ContinuousOn (fun q : ℂ × ℂ =>
            cA (iteratedFDeriv ℝ i (fun w => deriv (fun s => fderiv ℝ (F s) w 1) q.1) q.2) +
              cB (iteratedFDeriv ℝ i (fun w => deriv (fun s => fderiv ℝ (F s) w I) q.1) q.2)) (P ×ˢ U) :=
          (cA.continuous.comp_continuousOn (h1C i hi)).add (cB.continuous.comp_continuousOn (hIC i hi))
        refine hcont.congr fun q hq => ?_
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        have hev : (fun y => fderiv ℝ (fun w => deriv (fun s => F s w) q.1) y) =ᶠ[𝓝 q.2]
            ((fun y => A (deriv (fun s => fderiv ℝ (F s) y 1) q.1)) +
              fun y => B (deriv (fun s => fderiv ℝ (F s) y I) q.1)) :=
          Filter.eventually_of_mem (hU.mem_nhds hq.2) fun y hy => hfd q.1 hq.1 y hy
        have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hi
        have hc1' : ContDiffAt ℝ i (fun y => deriv (fun s => fderiv ℝ (F s) y 1) q.1) q.2 :=
          ((h1B q.1 hq.1).of_le hi').contDiffAt (hU.mem_nhds hq.2)
        have hcI' : ContDiffAt ℝ i (fun y => deriv (fun s => fderiv ℝ (F s) y I) q.1) q.2 :=
          ((hIB q.1 hq.1).of_le hi').contDiffAt (hU.mem_nhds hq.2)
        rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
        rw [show ((fun y => A (deriv (fun s => fderiv ℝ (F s) y 1) q.1)) +
              fun y => B (deriv (fun s => fderiv ℝ (F s) y I) q.1)) =
            (A ∘ (fun y => deriv (fun s => fderiv ℝ (F s) y 1) q.1)) +
              (B ∘ (fun y => deriv (fun s => fderiv ℝ (F s) y I) q.1)) from rfl,
          iteratedFDeriv_add_apply (A.contDiff.contDiffAt.comp q.2 hc1') (B.contDiff.contDiffAt.comp q.2 hcI'),
          A.iteratedFDeriv_comp_left hc1' le_rfl, B.iteratedFDeriv_comp_left hcI' le_rfl, map_add]
        rfl

/-- **G1b** (`∂_t` commutes with `∂_z`). Under the hypotheses of G1a with `n = 1`,
`∂_t (∂_z F_t)(z) = ∂_z (∂_t F)(z)`. -/
theorem s35g_param_deriv_dz {F : ℂ → ℂ → ℂ} {P U : Set ℂ} (hP : IsOpen P) (hU : IsOpen U)
    (hp : ∀ z ∈ U, DifferentiableOn ℂ (fun t => F t z) P)
    (hs : ∀ t ∈ P, ContDiffOn ℝ 1 (F t) U)
    (hc : ∀ j ≤ 1, ContinuousOn (fun q : ℂ × ℂ => iteratedFDeriv ℝ j (F q.1) q.2) (P ×ˢ U))
    {t z : ℂ} (ht : t ∈ P) (hz : z ∈ U) :
    deriv (fun s => dz (F s) z) t = dz (fun w => deriv (fun s => F s w) t) z := by
  obtain ⟨R, hR, hRP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds ht)
  have hmemS : sphere t R ⊆ P := sphere_subset_closedBall.trans hRP
  have hcz : ContinuousOn (fun q : ℂ × ℂ => F q.1 q.2) (P ×ˢ U) := wr_d2a_zero (hc 0 (by norm_num))
  have hdiff : ∀ s ∈ P, DifferentiableOn ℝ (F s) U := fun s hs' => (hs s hs').differentiableOn one_ne_zero
  have hD : ContinuousOn (fun q : ℂ × ℂ => fderiv ℝ (F q.1) q.2) (P ×ˢ U) := by
    refine ((continuousMultilinearCurryFin1 ℝ ℂ ℂ).continuous.comp_continuousOn (hc 1 le_rfl)).congr ?_
    intro q _
    ext v
    simp [iteratedFDeriv_one_apply]
  set k : ℂ → ℂ := fun s => ((s - t) ^ 2)⁻¹ with hkdef
  have hk : ContinuousOn k (sphere t R) :=
    ((continuousOn_id.sub continuousOn_const).pow 2).inv₀ fun s hs' =>
      pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_sphere hs' hR.ne'))
  obtain ⟨L, hL, hLv⟩ := s35g_circle_hasFDerivAt hR hU hk (hcz.mono (prod_mono hmemS subset_rfl))
    (fun s hs' => hdiff s (hmemS hs')) (hD.mono (prod_mono hmemS subset_rfl)) hz
  have hrep : ∀ w ∈ U, deriv (fun s => F s w) t = (2 * π * I : ℂ)⁻¹ • ∮ s in C(t, R), k s • F s w :=
    fun w hw => (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hP hRP (hp w hw)
      (mem_ball_self hR)).symm
  have hev : (fun w => deriv (fun s => F s w) t) =ᶠ[𝓝 z]
      fun w => (2 * π * I : ℂ)⁻¹ • ∮ s in C(t, R), k s • F s w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) hrep
  have hfd : fderiv ℝ (fun w => deriv (fun s => F s w) t) z =
      (ContinuousLinearMap.mul ℝ ℂ (2 * π * I : ℂ)⁻¹).comp L := by
    rw [hev.fderiv_eq]
    have h := (ContinuousLinearMap.mul ℝ ℂ (2 * π * I : ℂ)⁻¹).hasFDerivAt.comp z hL
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).fderiv
    simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  have hdzh : DifferentiableOn ℂ (fun s => dz (F s) z) P :=
    s4v_param_dz_holomorphic (n := 0) hP hU hp (fun s hs' => by exact_mod_cast hs s hs')
      (fun j hj => hc j (by omega)) hz
  have hlhs := (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hP hRP hdzh
    (mem_ball_self hR)).symm
  rw [hlhs]
  show _ = (fderiv ℝ (fun w => deriv (fun s => F s w) t) z 1 -
    I * fderiv ℝ (fun w => deriv (fun s => F s w) t) z I) / 2
  rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.mul_apply', hLv, hLv]
  have hDz : ContinuousOn (fun s => fderiv ℝ (F s) z) (sphere t R) :=
    hD.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs' => ⟨hmemS hs', hz⟩)
  have hD1 : ContinuousOn (fun s => fderiv ℝ (F s) z 1) (sphere t R) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn hDz
  have hDI : ContinuousOn (fun s => fderiv ℝ (F s) z I) (sphere t R) :=
    (ContinuousLinearMap.apply ℝ ℂ I).continuous.comp_continuousOn hDz
  have hi1 : CircleIntegrable (fun s => (1 / 2 : ℂ) • (k s • fderiv ℝ (F s) z 1)) t R :=
    ContinuousOn.circleIntegrable hR.le ((hk.smul hD1).const_smul (1 / 2 : ℂ))
  have hiI : CircleIntegrable (fun s => (I / 2 : ℂ) • (k s • fderiv ℝ (F s) z I)) t R :=
    ContinuousOn.circleIntegrable hR.le ((hk.smul hDI).const_smul (I / 2 : ℂ))
  have hfun : (fun s => k s • dz (F s) z) =
      fun s => (1 / 2 : ℂ) • (k s • fderiv ℝ (F s) z 1) - (I / 2 : ℂ) • (k s • fderiv ℝ (F s) z I) := by
    funext s
    simp only [dz, smul_eq_mul]
    ring
  rw [hfun, circleIntegral.integral_sub hi1 hiI, circleIntegral.integral_smul, circleIntegral.integral_smul]
  simp only [smul_eq_mul]
  ring

/-- Slice jets: if `G` is jointly `C³` on an open set `D`, its `z`-slices are `C³` with jointly continuous jets. -/
theorem s35g_slice_jets {G : (ℂ × ℂ) × ℂ → ℂ} {D : Set ((ℂ × ℂ) × ℂ)} (hD : IsOpen D)
    (hG : ContDiffOn ℝ 3 G D) :
    (∀ q ∈ D, ContDiffAt ℝ 3 (fun z => G (q.1, z)) q.2) ∧
      ∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (fun z => G (q.1, z)) q.2) D := by
  set ι : ℂ →L[ℝ] (ℂ × ℂ) × ℂ := ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ with hι
  have key : ∀ q ∈ D, ∀ j ≤ 3, iteratedFDeriv ℝ j (fun z => G (q.1, z)) q.2 =
      (iteratedFDeriv ℝ j G q).compContinuousLinearMap (fun _ => ι) := by
    intro q hq j hj
    set c : (ℂ × ℂ) × ℂ := (q.1, 0) with hc
    set f : (ℂ × ℂ) × ℂ → ℂ := fun y => G (y + c) with hf
    set s : Set ((ℂ × ℂ) × ℂ) := (fun y => y + c) ⁻¹' D with hsdef
    have hs : IsOpen s := hD.preimage (continuous_id.add continuous_const)
    have hfs : ContDiffOn ℝ 3 f s := hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun y hy => hy)
    have hs' : IsOpen (ι ⁻¹' s) := hs.preimage ι.continuous
    have hfun : (fun z => G (q.1, z)) = f ∘ ι := by
      funext z
      simp [hf, hc, hι]
    have hιq : ι q.2 ∈ s := by
      show ι q.2 + c ∈ D
      simpa [hι, hc] using hq
    have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
    rw [hfun, ← iteratedFDerivWithin_of_isOpen j hs' (show q.2 ∈ ι ⁻¹' s from hιq),
      ι.iteratedFDerivWithin_comp_right hfs hs.uniqueDiffOn hs'.uniqueDiffOn hιq hj',
      iteratedFDerivWithin_of_isOpen j hs hιq]
    congr 1
    rw [hf, iteratedFDeriv_comp_add_right]
    simp [hι, hc]
  refine ⟨fun q hq => ?_, fun j hj => ?_⟩
  · have h1 : ContDiffAt ℝ 3 G (q.1, q.2) := hG.contDiffAt (hD.mem_nhds hq)
    exact h1.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  · have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj
    have hc := (hG.continuousOn_iteratedFDerivWithin hj' hD.uniqueDiffOn).congr
      (fun q hq => (iteratedFDerivWithin_of_isOpen j hD hq).symm)
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => ι)).continuous.comp_continuousOn
      hc).congr fun q hq => ?_
    exact key q hq j hj

/-- The derivative of the three-point normalization `w ↦ M_{w₁,w₂}(w)` does not vanish. -/
theorem s35g_mob_deriv {w₁ w₂ w : ℂ} (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ 1) (h23 : w₂ ≠ 1)
    (hden : (-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁)) * w +
      (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))) ≠ 0) :
    deriv (fun x => ((-(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁)) * x +
      (-(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁))))) /
      ((-(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁)) * x +
      (-(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁)))))) w ≠ 0 := by
  set α : ℂ := -(1 * (-I - -1)) * (w₂ - 1) + -(-((-1) * (-I - 1))) * (w₂ - w₁) with hα
  set β : ℂ := -(1 * (-I - -1)) * (-(w₁ * (w₂ - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (w₂ - w₁))) with hβ
  set γ : ℂ := -(-I - -1) * (w₂ - 1) + (-I - 1) * (w₂ - w₁) with hγ
  set δ : ℂ := -(-I - -1) * (-(w₁ * (w₂ - 1))) + (-I - 1) * (-(1 * (w₂ - w₁))) with hδ
  have h := (((hasDerivAt_id' w).const_mul α).add_const β).div (((hasDerivAt_id' w).const_mul γ).add_const δ) hden
  have hd : deriv (fun x => (α * x + β) / (γ * x + δ)) w =
      (α * 1 * (γ * w + δ) - (α * w + β) * (γ * 1)) / (γ * w + δ) ^ 2 := h.deriv
  rw [hd]
  refine div_ne_zero ?_ (pow_ne_zero 2 hden)
  have key : α * 1 * (γ * w + δ) - (α * w + β) * (γ * 1) = 4 * ((w₂ - 1) * (w₂ - w₁) * (w₁ - 1)) := by
    rw [hα, hβ, hγ, hδ]
    linear_combination (-2 * ((w₂ - 1) * (w₂ - w₁) * (w₁ - 1))) * I_sq
  rw [key]
  exact mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 h23) (sub_ne_zero.2 h12.symm)) (sub_ne_zero.2 h13))

/-- **G2** (the two-parameter Model A family). For harmonic `a`, `μ` with `‖a‖ < 1` there are `r > 0`, an open set
`D` of `((P, z))` with `z ∈ 𝔻*`, and `U` such that:
- `U (t, t̄) z = w_{a + t μ}(z)` whenever `‖t‖ < r`, `z ∈ 𝔻*` and `w_{a+tμ}(z) ≠ ∞`, and then `((t, t̄), z) ∈ D`;
- `U` is holomorphic in each coordinate of `P` on `D`;
- `U P` is `C³` near `z`, with jets up to order 3 jointly continuous on `D`;
- `∂_z U P z ≠ 0` on `D`. -/
theorem s35g_family {a μ : LinfStar} (ha : a ∈ harmonicBeltrami) (ha1 : ‖a‖ < 1) (hμ : μ ∈ harmonicBeltrami) :
    ∃ r > 0, ∃ D : Set ((ℂ × ℂ) × ℂ), ∃ U : ℂ × ℂ → ℂ → ℂ, IsOpen D ∧
      (∀ q ∈ D, q.2 ∈ unitDiscExterior) ∧
      (∀ t : ℂ, ‖t‖ < r → ∀ z ∈ unitDiscExterior, wAS (a + t • μ) (z : ExtPlane) ≠ extInf →
        ((t, conj t), z) ∈ D ∧ U (t, conj t) z = wA (a + t • μ) z) ∧
      (∀ q ∈ D, DifferentiableAt ℂ (fun b => U (b, q.1.2) q.2) q.1.1 ∧
        DifferentiableAt ℂ (fun b => U (q.1.1, b) q.2) q.1.2) ∧
      (∀ q ∈ D, ContDiffAt ℝ 3 (U q.1) q.2) ∧
      (∀ j ≤ 3, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => iteratedFDeriv ℝ j (U q.1) q.2) D) ∧
      ∀ q ∈ D, dz (U q.1) q.2 ≠ 0 := by
  obtain ⟨m₀, m₁, hm₀, hm₁, hs₀, hs₁, hcoef⟩ := wr3_coeffs ha hμ
  set m₂ : ℂ → ℂ := unitDisc.indicator (extA μ) with hm₂def
  have hm₂ : IsBeltramiCoeff m₂ univ ‖μ‖ :=
    ⟨(extA_isBeltramiCoeff μ).1.indicator isOpen_ball.measurableSet,
      (extA_isBeltramiCoeff μ).2.mono fun u hu => (norm_indicator_le_norm_self _ _).trans hu⟩
  have hΩ : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hs₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₂ unitDiscExterior :=
    contDiffOn_const.congr fun u hu =>
      indicator_of_notMem (fun h => (not_lt_of_ge (le_of_lt hu)) (mem_ball_zero_iff.mp h)) _
  set W : Set (ℂ × ℂ) := {P | ‖a‖ + 2 * ‖μ‖ * ‖P‖ < 1} with hWdef
  have hWo : IsOpen W := isOpen_lt (continuous_const.add (continuous_const.mul continuous_norm)) continuous_const
  have hbc : ∀ P : ℂ × ℂ,
      IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ (‖a‖ + 2 * ‖μ‖ * ‖P‖) := by
    intro P
    have hl := wr_coeff_lin hm₁ hm₂ P
    refine ⟨(hm₀.1.add (hm₁.1.const_mul P.1)).add (hm₂.1.const_mul P.2), ?_⟩
    filter_upwards [hm₀.2, hl.2] with u h0 h1
    have h1' : ‖P.1 * m₁ u + P.2 * m₂ u‖ ≤ (|‖μ‖| + |‖μ‖|) * ‖P‖ := h1
    calc ‖m₀ u + P.1 * m₁ u + P.2 * m₂ u‖ = ‖m₀ u + (P.1 * m₁ u + P.2 * m₂ u)‖ := by rw [add_assoc]
      _ ≤ ‖m₀ u‖ + ‖P.1 * m₁ u + P.2 * m₂ u‖ := norm_add_le _ _
      _ ≤ ‖a‖ + (|‖μ‖| + |‖μ‖|) * ‖P‖ := add_le_add h0 h1'
      _ = ‖a‖ + 2 * ‖μ‖ * ‖P‖ := by rw [abs_of_nonneg (norm_nonneg μ)]; ring
  have hWk : ∀ P ∈ W, ∃ k < 1, IsBeltramiCoeff (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) univ k :=
    fun P hP => ⟨_, hP, hbc P⟩
  set N : ℂ × ℂ → ℂ → ℂ := fun P => normalizedSolution (fun u => m₀ u + P.1 * m₁ u + P.2 * m₂ u) with hNdef
  set Φ : ℂ × ℂ × ℂ → ℂ := fun x =>
    ((-(1 * (-I - -1)) * (x.2.1 - 1) + -(-((-1) * (-I - 1))) * (x.2.1 - x.1)) * x.2.2 +
      (-(1 * (-I - -1)) * (-(x.1 * (x.2.1 - 1))) + -(-((-1) * (-I - 1))) * (-(1 * (x.2.1 - x.1))))) /
    ((-(-I - -1) * (x.2.1 - 1) + (-I - 1) * (x.2.1 - x.1)) * x.2.2 +
      (-(-I - -1) * (-(x.1 * (x.2.1 - 1))) + (-I - 1) * (-(1 * (x.2.1 - x.1))))) with hΦdef
  set den : ℂ × ℂ × ℂ → ℂ := fun x =>
    (-(-I - -1) * (x.2.1 - 1) + (-I - 1) * (x.2.1 - x.1)) * x.2.2 +
      (-(-I - -1) * (-(x.1 * (x.2.1 - 1))) + (-I - 1) * (-(1 * (x.2.1 - x.1)))) with hdendef
  have hdenc : Continuous den := by rw [hdendef]; fun_prop
  have hΦd : ∀ x, den x ≠ 0 → ContDiffAt ℂ 3 Φ x := by
    intro x hx
    rw [hΦdef]
    exact ContDiffAt.div (by fun_prop) (by fun_prop) hx
  set U : ℂ × ℂ → ℂ → ℂ := fun P z => Φ (N P (-1), N P (-I), N P z) with hUdef
  set g : (ℂ × ℂ) × ℂ → ℂ × ℂ × ℂ × ℂ := fun q =>
    (N q.1 (-1) - N q.1 (-I), N q.1 (-1) - 1, N q.1 (-I) - 1, den (N q.1 (-1), N q.1 (-I), N q.1 q.2)) with hgdef
  set T : Set (ℂ × ℂ × ℂ × ℂ) := {x | x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2.1 ≠ 0 ∧ x.2.2.2 ≠ 0} with hTdef
  have hTo : IsOpen T :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      ((isOpen_ne_fun (continuous_fst.comp continuous_snd) continuous_const).inter
        ((isOpen_ne_fun (continuous_fst.comp (continuous_snd.comp continuous_snd)) continuous_const).inter
          (isOpen_ne_fun (continuous_snd.comp (continuous_snd.comp continuous_snd)) continuous_const)))
  have hNc : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ univ) := wr3_cont hm₀ hm₁ hm₂ hWo hWk
  have hNpt : ∀ z : ℂ, ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 z) (W ×ˢ unitDiscExterior) := by
    intro z
    have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ => N q.1 q.2)
      (f := fun q : (ℂ × ℂ) × ℂ => (q.1, z)) hNc (continuous_fst.prodMk continuous_const).continuousOn
      (fun (q : (ℂ × ℂ) × ℂ) (hq : q ∈ W ×ˢ unitDiscExterior) => show (q.1, z) ∈ W ×ˢ univ from ⟨hq.1, mem_univ _⟩)
    exact h
  have hNz : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ unitDiscExterior) :=
    hNc.mono (prod_mono subset_rfl (subset_univ _))
  have hgc : ContinuousOn g (W ×ˢ unitDiscExterior) :=
    ((hNpt _).sub (hNpt _)).prodMk (((hNpt _).sub continuousOn_const).prodMk (((hNpt _).sub continuousOn_const).prodMk
      (hdenc.comp_continuousOn ((hNpt _).prodMk ((hNpt _).prodMk hNz)))))
  set D : Set ((ℂ × ℂ) × ℂ) := (W ×ˢ unitDiscExterior) ∩ g ⁻¹' T with hDdef
  have hDo : IsOpen D := hgc.isOpen_inter_preimage (hWo.prod hΩ) hTo
  obtain ⟨hz3, hzc⟩ := wr3_z_regular hm₀ hm₁ hm₂ hΩ hs₀ hs₁ hs₂ hWo hWk
  have hH := wr3_holo hm₀ hm₁ hm₂ hWo hWk
  have hJ : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => N q.1 q.2) (W ×ˢ unitDiscExterior) :=
    wr_joint_of_holo_param (u := N) hWo hΩ (fun z _ => (hH z).1) (fun z _ => (hH z).2) hNz hz3 hzc
  have hPz : ∀ z : ℂ, ContDiffOn ℝ 3 (fun P => N P z) W := by
    intro z
    refine contDiffOn_of_locally_contDiffOn fun P₀ hP₀ => ?_
    obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hWo P₀ hP₀
    have hsub : closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2) ⊆ W := by
      intro P hP
      apply hRW
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨lt_of_le_of_lt hP.1 (by linarith), lt_of_le_of_lt hP.2 (by linarith)⟩
    have hcont : ContinuousOn (fun P : ℂ × ℂ => N P z) (closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) := by
      have h := ContinuousOn.comp (g := fun q : (ℂ × ℂ) × ℂ => N q.1 q.2)
        (f := fun P : ℂ × ℂ => (P, z)) hNc (continuous_id.prodMk continuous_const).continuousOn
        (fun (P : ℂ × ℂ) (hP : P ∈ closedBall P₀.1 (R / 2) ×ˢ closedBall P₀.2 (R / 2)) =>
          show (P, z) ∈ W ×ˢ univ from ⟨hsub hP, mem_univ _⟩)
      exact h
    have h₁ : ∀ b ∈ closedBall P₀.2 (R / 2), DifferentiableOn ℂ (fun a => N (a, b) z) (ball P₀.1 (R / 2)) :=
      fun b hb => ((hH z).1 b).mono fun a ha => hsub ⟨ball_subset_closedBall ha, hb⟩
    have h₂ : ∀ a ∈ closedBall P₀.1 (R / 2), DifferentiableOn ℂ (fun b => N (a, b) z) (ball P₀.2 (R / 2)) :=
      fun a ha => ((hH z).2 a).mono fun b hb => hsub ⟨ha, ball_subset_closedBall hb⟩
    refine ⟨ball P₀ (R / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
    exact (wr_bidisc_contDiffOn (c := P₀) (by positivity) hcont h₁ h₂).mono
      (inter_subset_right.trans (ball_subset_ball (le_of_eq (by ring))))
  have hDW : ∀ q ∈ D, q.1 ∈ W := fun q hq => hq.1.1
  have hUj : ContDiffOn ℝ 3 (fun q : (ℂ × ℂ) × ℂ => U q.1 q.2) D := by
    intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have hin : ContDiffWithinAt ℝ 3 (fun q : (ℂ × ℂ) × ℂ => (N q.1 (-1), N q.1 (-I), N q.1 q.2)) D q :=
      (((hPz (-1)).comp contDiffOn_fst hDW).prodMk (((hPz (-I)).comp contDiffOn_fst hDW).prodMk
        (hJ.mono inter_subset_left))) q hq
    exact ((hΦd _ hden).restrict_scalars ℝ).comp_contDiffWithinAt q hin
  obtain ⟨hU1, hU2⟩ := s35g_slice_jets hDo hUj
  have hr : 0 < (1 - ‖a‖) / (2 * ‖μ‖ + 1) := div_pos (by linarith) (by positivity)
  refine ⟨(1 - ‖a‖) / (2 * ‖μ‖ + 1), hr, D, U, hDo, fun q hq => hq.1.2, ?_, ?_, fun q hq => hU1 q hq,
    fun j hj => hU2 j hj, ?_⟩
  · intro t ht z hz hpole
    have hnt : ‖((t, conj t) : ℂ × ℂ)‖ = ‖t‖ := by rw [Prod.norm_mk, Complex.norm_conj, max_self]
    have ht' : (2 * ‖μ‖ + 1) * ‖t‖ < 1 - ‖a‖ := by
      rw [lt_div_iff₀ (by positivity)] at ht
      linarith
    have hP : ((t, conj t) : ℂ × ℂ) ∈ W := by
      show ‖a‖ + 2 * ‖μ‖ * ‖((t, conj t) : ℂ × ℂ)‖ < 1
      rw [hnt]
      nlinarith [norm_nonneg t, norm_nonneg μ]
    have hk : ‖a + t • μ‖ < 1 := by
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul]
      nlinarith [norm_nonneg t, norm_nonneg μ]
    have hμt : a + t • μ ∈ LinfStarBall := by simpa [LinfStarBall] using hk
    obtain ⟨M, hM, W', hW', hfin, -, hm1, hmi, hp1⟩ := wA_spec hμt
    have hWeq : W' = N (t, conj t) :=
      (QCV.qcv_ns_eq (norm_nonneg _) hk (extA_isBeltramiCoeff _) hW').symm.trans
        (QCV.qcv_ns_congr_ae (norm_nonneg _) hk (extA_isBeltramiCoeff _) (hcoef t))
    subst hWeq
    obtain ⟨K, hK⟩ := hW'.1
    obtain ⟨e, he⟩ := t1_homeomorph hK hW'.2.1
    have hinj : Function.Injective (N (t, conj t)) := by rw [← he]; exact e.injective
    have hW1 : N (t, conj t) 1 = 1 := hW'.2.2.2.1
    have hm1I : (-1 : ℂ) ≠ -I := by
      intro h; have := congrArg Complex.im h; simp at this
    have hmI1 : (-I : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h12 := hinj.ne hm1I
    have h13 : N (t, conj t) (-1) ≠ 1 := by
      have h := hinj.ne (show (-1 : ℂ) ≠ 1 by norm_num)
      rwa [hW1] at h
    have h23 : N (t, conj t) (-I) ≠ 1 := by
      have h := hinj.ne hmI1
      rwa [hW1] at h
    have e₁ := (hfin (-1)).symm.trans hm1
    have e₂ := (hfin (-I)).symm.trans hmi
    have e₃ : M ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
      have h := (hfin 1).symm.trans hp1
      rwa [hW1] at h
    have hMN := wr_three_point hM h12 h13 h23 e₁ e₂ e₃
    have hz' := hfin z
    rw [hMN] at hz'
    have hden : (-(-I - -1) * (N (t, conj t) (-I) - 1) + (-I - 1) * (N (t, conj t) (-I) - N (t, conj t) (-1))) *
        N (t, conj t) z + (-(-I - -1) * (-(N (t, conj t) (-1) * (N (t, conj t) (-I) - 1))) +
          (-I - 1) * (-(1 * (N (t, conj t) (-I) - N (t, conj t) (-1))))) ≠ 0 := by
      intro h0
      rw [mobiusExt_coe_of_eq_zero h0] at hz'
      exact hpole hz'
    refine ⟨⟨⟨hP, hz⟩, ⟨sub_ne_zero.2 h12, sub_ne_zero.2 h13, sub_ne_zero.2 h23, hden⟩⟩, ?_⟩
    show _ = finPart (wAS (a + t • μ) (z : ExtPlane))
    rw [hz', mobiusExt_coe hden]
    rfl
  · intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have hW : q.1 ∈ W := hq.1.1
    have hd1 : ∀ z, DifferentiableAt ℂ (fun b => N (b, q.1.2) z) q.1.1 := fun z =>
      ((hH z).1 q.1.2).differentiableAt ((hWo.preimage (continuous_id.prodMk continuous_const)).mem_nhds hW)
    have hd2 : ∀ z, DifferentiableAt ℂ (fun b => N (q.1.1, b) z) q.1.2 := fun z =>
      ((hH z).2 q.1.1).differentiableAt ((hWo.preimage (continuous_const.prodMk continuous_id)).mem_nhds hW)
    have hΦq : DifferentiableAt ℂ Φ (N (q.1.1, q.1.2) (-1), N (q.1.1, q.1.2) (-I), N (q.1.1, q.1.2) q.2) :=
      (hΦd _ hden).differentiableAt (by norm_num)
    have e1 := hΦq.comp q.1.1 ((hd1 (-1)).prodMk ((hd1 (-I)).prodMk (hd1 q.2)))
    have e2 := hΦq.comp q.1.2 ((hd2 (-1)).prodMk ((hd2 (-I)).prodMk (hd2 q.2)))
    exact ⟨e1, e2⟩
  · intro q hq
    have hden : den (N q.1 (-1), N q.1 (-I), N q.1 q.2) ≠ 0 := hq.2.2.2.2
    have h12 : N q.1 (-1) ≠ N q.1 (-I) := sub_ne_zero.1 hq.2.1
    have h13 : N q.1 (-1) ≠ 1 := sub_ne_zero.1 hq.2.2.1
    have h23 : N q.1 (-I) ≠ 1 := sub_ne_zero.1 hq.2.2.2.1
    set φ : ℂ → ℂ := fun w => Φ (N q.1 (-1), N q.1 (-I), w) with hφdef
    have hΦq : DifferentiableAt ℂ Φ (N q.1 (-1), N q.1 (-I), N q.1 q.2) :=
      (hΦd _ hden).differentiableAt (by norm_num)
    have hin : DifferentiableAt ℂ (fun w : ℂ => (N q.1 (-1), N q.1 (-I), w)) (N q.1 q.2) := by fun_prop
    have hφ0 := hΦq.comp (N q.1 q.2) hin
    have hφ : DifferentiableAt ℂ φ (N q.1 q.2) := hφ0
    have hNd : DifferentiableAt ℝ (N q.1) q.2 :=
      ((hz3 q.1 hq.1.1).contDiffAt (hΩ.mem_nhds hq.1.2)).differentiableAt (by norm_num)
    rw [show U q.1 = φ ∘ N q.1 from rfl, (ra_dz_comp_holo hφ hNd).1]
    refine mul_ne_zero (s35g_mob_deriv h12 h13 h23 hden) ?_
    intro h0
    have hj := wr3_jacobian_pos hΩ hs₀ hs₁ hs₂ (hWk q.1 hq.1.1) hq.1.2
    change 0 < ‖dz (N q.1) q.2‖ ^ 2 - ‖dzbar (N q.1) q.2‖ ^ 2 at hj
    rw [h0, norm_zero] at hj
    nlinarith [sq_nonneg ‖dzbar (N q.1) q.2‖]

/-- **G3** (factorization of `γ`). For `a, l` in the ball and a finite point `z` with `w_a(z)` and `w_l(z)` finite,
`w_{l * a⁻¹}(w_a(z)) = w_l(z)`. -/
theorem s35g_gamma_eq {a l : LinfStar} (ha : a ∈ LinfStarBall) (hl : l ∈ LinfStarBall) {z : ℂ}
    (hza : wAS a (z : ExtPlane) ≠ extInf) (hzl : wAS l (z : ExtPlane) ≠ extInf) :
    wA (beltramiMul l (beltramiInv a)) (wA a z) = wA l z := by
  have hai : beltramiInv a ∈ LinfStarBall := grp_inv_mem ha
  have hinv : wAS (beltramiInv a) (wAS a (z : ExtPlane)) = (z : ExtPlane) :=
    congrFun (grp_wAS_inv_right ha) (z : ExtPlane)
  show finPart (wAS (beltramiMul l (beltramiInv a)) ((finPart (wAS a (z : ExtPlane)) : ℂ) : ExtPlane)) =
    finPart (wAS l (z : ExtPlane))
  rw [coe_finPart_of_ne hza, grp_wAS_mul hl hai, Function.comp_apply, hinv]

end Ch2

end TakhtajanTeo
