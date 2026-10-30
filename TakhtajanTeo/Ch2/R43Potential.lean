import TakhtajanTeo.Ch2.S4GThm41
import TakhtajanTeo.Ch1.ChartTranslation
import TakhtajanTeo.Ch1.S4_Metrics
import TakhtajanTeo.Ch1.BanachHolomorphicAnalytic
import TakhtajanTeo.Ch1.WeakHolomorphy
import TakhtajanTeo.Appendix.B1Entries
import TakhtajanTeo.Ch1.ComponentTCompleted
import TakhtajanTeo.Ch1.WPChangeOfVariables
import TakhtajanTeo.Ch1.HilbertBersKernel
import TakhtajanTeo.Ch1.HilbertBersPreimage
import TakhtajanTeo.Ch1.HilbertBersDifferential
import TakhtajanTeo.Ch1.HarmonicL2Bers
import TakhtajanTeo.Ch1.HarmonicProjCompleted
import TakhtajanTeo.Ch1.ComponentTBasics
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.AhlforsWeillCompleted

/-!
# Remark 4.3 (Ch1): real-analyticity of the Weil–Petersson metric via the potential `S₂` (Program G, 下属6)

Host of Ch1 `remark_4_3` (S4_Metrics, TT:2188–2198), downstream of Ch2 `S4GThm41`.
- `s₂(φ) = S₂([Λφ])` (`S₂ = log det(I − B₁B₁*)`, Grunsky operator `B₁` of `f` with `𝒮f = φ`) is real-analytic on
  `V₀ = ball 0 √(π/3) ⊂ A₂(𝔻)`.
- `∂∂̄S₂ = −(1/12π)⟨·,·⟩_WP` at every point of `T₀(1)` in its right-translated Bers chart (`s4g_S2_ddbar`, proved).
  Changing to the fixed Hilbert chart gives `g_{μν̄}(φ) = −12π ∂_{e₁}∂̄_{e₂} s₂(φ + e₁ v(φ) + e₂ w(φ))|₀`, where
  `v, w` are the chart coordinates of the tangent vectors `μ, ν` at `[Λφ]`.
- A mixed second derivative of a real-analytic function along real-analytic vector fields is real-analytic.

* P1 `r43p_S2_analytic`: `s₂` is ℝ-analytic on `V₀`.
* P2 `r43p_bridge`: the chart-change identity, with real-analytic vector fields `v, w`.
* P3 `r43p_ddbar_analytic`: the generic calculus step.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

/-- A partial derivative in the last `ℂ` variable of an ℝ-analytic function is ℝ-analytic. -/
theorem r43p_partial {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X × ℂ → ℂ} {S : Set (X × ℂ)}
    (hS : IsOpen S) (hf : AnalyticOnNhd ℝ f S) (u : ℂ) :
    AnalyticOnNhd ℝ (fun p : X × ℂ => fderiv ℝ (fun t => f (p.1, t)) p.2 u) S := by
  have hd : AnalyticOnNhd ℝ (fun p => fderiv ℝ f p ((0 : X), u)) S := fun p hp =>
    ((ContinuousLinearMap.apply ℝ ℂ ((0 : X), u)).analyticAt _).comp (hf.fderiv p hp)
  refine hd.congr hS fun p hp => ?_
  have hfd : HasFDerivAt f (fderiv ℝ f p) (p.1, p.2) := (hf p hp).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun t : ℂ => (p.1, t)) ((0 : ℂ →L[ℝ] X).prod (ContinuousLinearMap.id ℝ ℂ)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hc := (hfd.comp p.2 hι).fderiv
  rw [show (fun t => f (p.1, t)) = f ∘ (fun t : ℂ => (p.1, t)) from rfl, hc]
  simp

/-- `∂_z̄` in the last variable of an ℝ-analytic function is ℝ-analytic. -/
theorem r43p_partial_dzbar {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X × ℂ → ℂ}
    {S : Set (X × ℂ)} (hS : IsOpen S) (hf : AnalyticOnNhd ℝ f S) :
    AnalyticOnNhd ℝ (fun p : X × ℂ => dzbar (fun t => f (p.1, t)) p.2) S := by
  have h := (analyticOnNhd_const (v := (1 / 2 : ℂ))).mul
    ((r43p_partial hS hf 1).add ((analyticOnNhd_const (v := I)).mul (r43p_partial hS hf I)))
  exact h.congr hS fun p _ => by simp only [dzbar, Pi.add_apply]; ring

/-- `∂_z` in the last variable of an ℝ-analytic function is ℝ-analytic. -/
theorem r43p_partial_dz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X × ℂ → ℂ}
    {S : Set (X × ℂ)} (hS : IsOpen S) (hf : AnalyticOnNhd ℝ f S) :
    AnalyticOnNhd ℝ (fun p : X × ℂ => dz (fun t => f (p.1, t)) p.2) S := by
  have h := (analyticOnNhd_const (v := (1 / 2 : ℂ))).mul
    ((r43p_partial hS hf 1).sub ((analyticOnNhd_const (v := I)).mul (r43p_partial hS hf I)))
  exact h.congr hS fun p _ => by simp only [dz, Pi.sub_apply]; ring

/-- The polarized trace-series summands `(A, D) ↦ tr((AD)^N A D)` are entire. -/
theorem r43p_term_diff (N : ℕ) :
    Differentiable ℂ (fun p : s3tc_HS × s3tc_HS =>
      s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2) := by
  have h1 : Differentiable ℂ (fun p : s3tc_HS × s3tc_HS => s3tc_toOperator p.1 * s3tc_toOperator p.2) :=
    (s3tc_toOperator.differentiable.comp differentiable_fst).mul
      (s3tc_toOperator.differentiable.comp differentiable_snd)
  have h3 : Differentiable ℂ (fun p : s3tc_HS × s3tc_HS =>
      s3tc_leftAction ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) :=
    (s3tc_leftAction.differentiable.comp (h1.pow N)).clm_apply differentiable_fst
  exact (s3tc_tracePair.differentiable.comp h3).clm_apply differentiable_snd

/-- `‖T^N‖ ≤ ‖T‖^N` for bounded operators on `ℓ²`. -/
theorem r43p_pow_norm (T : ell2 →L[ℂ] ell2) (N : ℕ) : ‖T ^ N‖ ≤ ‖T‖ ^ N := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- The summand bound `|tr((AD)^N A D)| ≤ ‖A‖ ‖D‖ ‖AD‖^N`. -/
theorem r43p_term_bound (A D : s3tc_HS) (N : ℕ) :
    ‖s3tc_trace (s3tc_left ((s3tc_toOperator A * s3tc_toOperator D) ^ N) A) D‖ ≤
      ‖A‖ * ‖D‖ * ‖s3tc_toOperator A * s3tc_toOperator D‖ ^ N := by
  refine (s3tc_trace_norm _ _).trans ?_
  have h1 := s3tc_left_norm ((s3tc_toOperator A * s3tc_toOperator D) ^ N) A
  have h2 := r43p_pow_norm (s3tc_toOperator A * s3tc_toOperator D) N
  calc ‖s3tc_left ((s3tc_toOperator A * s3tc_toOperator D) ^ N) A‖ * ‖D‖
      ≤ (‖s3tc_toOperator A * s3tc_toOperator D‖ ^ N * ‖A‖) * ‖D‖ :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- The complexified log-determinant series is holomorphic near every `(A₀, D₀)` with `‖A₀ D₀‖ < 1`. -/
theorem r43p_Q_analytic {a : s3tc_HS × s3tc_HS} (ha : ‖s3tc_toOperator a.1 * s3tc_toOperator a.2‖ < 1) :
    AnalyticAt ℂ (fun p : s3tc_HS × s3tc_HS => ∑' N : ℕ,
      s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2 / (N + 1)) a := by
  set T : s3tc_HS × s3tc_HS → ell2 →L[ℂ] ell2 := fun p => s3tc_toOperator p.1 * s3tc_toOperator p.2 with hT
  have hTc : Continuous T :=
    (s3tc_toOperator.continuous.comp continuous_fst).mul (s3tc_toOperator.continuous.comp continuous_snd)
  set c : ℝ := (1 + ‖T a‖) / 2 with hc
  have hc1 : c < 1 := by rw [hc]; linarith
  have hca : ‖T a‖ < c := by rw [hc]; linarith
  obtain ⟨ρ₀, hρ₀, hρ₀b⟩ : ∃ ρ₀ > 0, ∀ p ∈ ball a ρ₀, ‖T p‖ < c :=
    Metric.isOpen_iff.mp (isOpen_lt (continuous_norm.comp hTc) continuous_const) a hca
  set ρ : ℝ := ρ₀ / 3 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  set K : ℝ := (‖a‖ + 3 * ρ) ^ 2 with hK
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  -- uniform bounds on `ball a (ρ + 2ρ)`
  have hb : ∀ N : ℕ, ∀ p ∈ ball a (ρ + 2 * ρ),
      ‖s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2 / (N + 1)‖ ≤
        K * c ^ N := by
    intro N p hp
    have hp3 : p ∈ ball a ρ₀ := ball_subset_ball (by rw [hρ]; linarith) hp
    have hpn : ‖p‖ ≤ ‖a‖ + 3 * ρ := by
      have : ‖p - a‖ < ρ + 2 * ρ := mem_ball_iff_norm.mp hp
      have := norm_le_norm_add_norm_sub' p a
      linarith [norm_sub_rev p a]
    have h1 : ‖p.1‖ * ‖p.2‖ ≤ K := by
      rw [hK, sq]
      exact mul_le_mul ((norm_fst_le p).trans hpn) ((norm_snd_le p).trans hpn) (norm_nonneg _)
        (by positivity)
    have hN1 : (1 : ℝ) ≤ ‖((N : ℂ) + 1)‖ := by
      rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    rw [norm_div]
    refine (div_le_self (norm_nonneg _) hN1).trans ((r43p_term_bound p.1 p.2 N).trans ?_)
    exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (hρ₀b p hp3).le N) (by positivity) (by positivity)
  have hdiff : ∀ N : ℕ, Differentiable ℂ (fun p : s3tc_HS × s3tc_HS =>
      s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2 / (N + 1)) :=
    fun N => by
    have h := (r43p_term_diff N).mul_const (((N : ℂ) + 1)⁻¹)
    simpa only [div_eq_mul_inv] using h
  have hsum : Summable fun N : ℕ => K * c ^ N / (2 * ρ) :=
    ((summable_geometric_of_lt_one hc0 hc1).mul_left K).div_const _
  have hder : ∀ N : ℕ, ∀ x ∈ ball a ρ, ‖fderiv ℂ (fun p : s3tc_HS × s3tc_HS =>
      s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2 / (N + 1)) x‖ ≤
        K * c ^ N / (2 * ρ) := fun N x hx =>
    bha_fderiv_bound (by positivity) (hdiff N).differentiableOn (hb N) hx
  have hd : DifferentiableOn ℂ (fun p : s3tc_HS × s3tc_HS => ∑' N : ℕ,
      s3tc_trace (s3tc_left ((s3tc_toOperator p.1 * s3tc_toOperator p.2) ^ N) p.1) p.2 / (N + 1)) (ball a ρ) := by
    intro x hx
    refine (hasFDerivAt_tsum_of_isPreconnected hsum isOpen_ball (convex_ball a ρ).isPreconnected
      (fun N y _ => ((hdiff N) y).hasFDerivAt) hder (mem_ball_self hρ0) ?_ hx).differentiableAt.differentiableWithinAt
    exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hc0 hc1).mul_left K)
      (fun N => hb N a (mem_ball_self (by positivity)))
  exact bha_analyticOnNhd isOpen_ball hd a (mem_ball_self hρ0)

/-- The adjoint `A ↦ A*` is a continuous ℝ-linear map of the HS space. -/
theorem r43p_adjointL : ∃ L : s3tc_HS →L[ℝ] s3tc_HS, ∀ A, L A = s3tc_adjoint A := by
  refine ⟨LinearMap.mkContinuous
    { toFun := s3tc_adjoint
      map_add' := fun A B => lp.ext (funext fun q => by
        obtain ⟨m, n⟩ := q
        show s3tc_adjoint (A + B) (m, n) = s3tc_adjoint A (m, n) + s3tc_adjoint B (m, n)
        rw [s3tc_adjoint_apply, s3tc_adjoint_apply, s3tc_adjoint_apply, lp.coeFn_add, Pi.add_apply, map_add])
      map_smul' := fun r A => lp.ext (funext fun q => by
        obtain ⟨m, n⟩ := q
        show s3tc_adjoint (r • A) (m, n) = r • s3tc_adjoint A (m, n)
        rw [s3tc_adjoint_apply, s3tc_adjoint_apply, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul,
          Complex.real_smul, map_mul, Complex.conj_ofReal]) } 1 (fun A => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, s3tc_adjoint_norm, le_refl]), fun A => rfl⟩

/-- **P1a.** The trace series `S₂ = -Σ tr((AA*)^{N+1})/(N+1)` is ℝ-analytic on the open operator-norm unit ball. -/
theorem r43p_logSeries_analytic :
    AnalyticOnNhd ℝ s3fd_logSeries {A : s3tc_HS | ‖s3tc_toOperator A‖ < 1} := by
  obtain ⟨L, hL⟩ := r43p_adjointL
  have hopen : IsOpen {A : s3tc_HS | ‖s3tc_toOperator A‖ < 1} :=
    isOpen_lt (continuous_norm.comp s3tc_toOperator.continuous) continuous_const
  have hgram : ∀ A : s3tc_HS, s3tc_toOperator A * s3tc_toOperator (s3tc_adjoint A) = s3fd_gram A := fun A => by
    rw [s3tc_adjoint_operator]; rfl
  have hsmall : ∀ A ∈ {A : s3tc_HS | ‖s3tc_toOperator A‖ < 1},
      ‖s3tc_toOperator A * s3tc_toOperator (s3tc_adjoint A)‖ < 1 := fun A hA => by
    have hA' : ‖s3tc_toOperator A‖ < 1 := hA
    rw [s3tc_adjoint_operator]
    calc ‖s3tc_toOperator A * star (s3tc_toOperator A)‖ ≤ ‖s3tc_toOperator A‖ * ‖star (s3tc_toOperator A)‖ :=
          norm_mul_le _ _
      _ = ‖s3tc_toOperator A‖ * ‖s3tc_toOperator A‖ := by rw [s3fd_star_norm]
      _ < 1 := by nlinarith [norm_nonneg (s3tc_toOperator A)]
  -- the diagonal restriction of the complexified series
  have heq : ∀ A ∈ {A : s3tc_HS | ‖s3tc_toOperator A‖ < 1}, s3fd_logSeries A =
      -(∑' N : ℕ, s3tc_trace (s3tc_left ((s3tc_toOperator A * s3tc_toOperator (L A)) ^ N) A) (L A) /
        (N + 1)).re := by
    intro A hA
    have hs : Summable fun N : ℕ =>
        s3tc_trace (s3tc_left ((s3tc_toOperator A * s3tc_toOperator (L A)) ^ N) A) (L A) / (N + 1) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one
        (r := ‖s3tc_toOperator A * s3tc_toOperator (L A)‖) (norm_nonneg _) (by
        rw [hL]; exact hsmall A hA)).mul_left (‖A‖ * ‖L A‖)) (fun N => ?_)
      have hN1 : (1 : ℝ) ≤ ‖((N : ℂ) + 1)‖ := by
        rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hN1).trans (r43p_term_bound _ _ N)
    rw [Complex.re_tsum hs, ← tsum_neg]
    unfold s3fd_logSeries
    refine tsum_congr fun N => ?_
    unfold s3fd_coeff
    rw [hL, hgram, s3tc_trace_gram_pair,
      show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    ring
  intro A hA
  have hQ := (r43p_Q_analytic (a := (A, L A)) (by rw [hL]; exact hsmall A hA)).restrictScalars (𝕜 := ℝ)
  have hι : AnalyticAt ℝ (fun B : s3tc_HS => (B, L B)) A := analyticAt_id.prod (L.analyticAt A)
  have hc := (Complex.reCLM.analyticAt _).comp (hQ.comp (f := fun B : s3tc_HS => (B, L B)) hι)
  refine (hc.neg).congr ?_
  filter_upwards [hopen.mem_nhds hA] with B hB
  exact (heq B hB).symm
/-- Every point of `T(1)` has a representative in `𝒪(𝔻*)₁` (the clopen argument of `s2c_hilbertChartDomain_cover`). -/
theorem r43p_groupO_rep (p : T1) : ∃ μ : LinfStarBall, (μ : LinfStar) ∈ groupO ∧ p = Phi μ := by
  set H : Set T1 := {p | ∃ μ : LinfStarBall, (μ : LinfStar) ∈ groupO ∧ p = Phi μ} with hHdef
  have hz0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hH0 : Phi ⟨0, hz0⟩ ∈ H := ⟨⟨0, hz0⟩, zero_mem_groupO, rfl⟩
  have hHmul : ∀ p ∈ H, ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO → rightTrans μ p ∈ H := by
    rintro p ⟨l, hl, rfl⟩ μ hμ
    exact ⟨⟨beltramiMul (l : LinfStar) μ, bg_mul_mem_ball μ.2 l.2⟩, groupO_mul_mem hl hμ,
      bt_rightTrans_phi μ l⟩
  -- the Bers norm ball of radius `r = 2 δ₀` consists of classes of small harmonic differentials
  set r : ℝ := 2 * delta0 with hr
  have hδ := delta0_bounds
  have hU : ∀ q : T1, ‖bers q‖ < r → ∃ a : LinfStarBall, (a : LinfStar) ∈ groupO ∧ q = Phi a := by
    intro q hq
    have hφ2 : ‖bers q‖ < 2 := by rw [hr] at hq; linarith [hδ.2]
    obtain ⟨h, hφq⟩ := ahlfors_weill hφ2
    refine ⟨⟨Lambda (bers q), h⟩, ?_, ?_⟩
    · exact groupO_mem_of_harmonic (Lambda_mem_harmonic _)
        (lt_of_le_of_lt (Lambda_norm_le _) (by rw [hr] at hq; linarith))
    · exact bers_injective (by rw [hφq])
  have hbers0 : bers (Phi ⟨0, hz0⟩) = 0 := by
    have h0 : Lambda (0 : AInf unitDisc) = 0 := by
      have := Lambda_smul 0 (0 : AInf unitDisc)
      simpa using this
    obtain ⟨h, hφ⟩ := ahlfors_weill (φ := (0 : AInf unitDisc)) (by simp)
    have : (⟨Lambda (0 : AInf unitDisc), h⟩ : LinfStarBall) = ⟨0, hz0⟩ := Subtype.ext h0
    rw [this] at hφ
    exact hφ
  -- the neighbourhood of `Phi ν` in which `R_{ν⁻¹}` has small Bers norm
  have hNopen : ∀ ν : LinfStarBall, IsOpen {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := fun ν =>
    isOpen_lt (continuous_norm.comp (hc_bers_continuous.comp (hc_rightTrans_continuous _)))
      continuous_const
  have hNmem : ∀ ν : LinfStarBall, Phi ν ∈ {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := by
    intro ν
    have hi := bc_beltramiInv_mem_ball ν.2
    have e1 : Phi ν = rightTrans ν (Phi ⟨0, hz0⟩) := by
      rw [bt_rightTrans_phi]
      exact congrArg Phi (Subtype.ext (hb_zero_mul ν.2).symm)
    show ‖bers (rightTrans ⟨_, hi⟩ (Phi ν))‖ < r
    rw [e1, bt_rightTrans_inv_left ν hi, hbers0, norm_zero]
    rw [hr]; linarith [hδ.1]
  have hopen : IsOpen H := by
    rw [isOpen_iff_forall_mem_open]
    rintro q ⟨ν, hν, rfl⟩
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro q' hq'
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hqa⟩ := hU _ hq'
    have : q' = rightTrans ν (Phi a) := by
      rw [← hqa, bt_rightTrans_inv_right ν hi]
    rw [this]
    exact hHmul _ ⟨a, ha, rfl⟩ ν hν
  have hclosed : IsClosed H := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨ν, rfl⟩ := Quotient.exists_rep p
    change Phi ν ∉ H at hp
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro y hy hyH
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hya⟩ := hU _ hy
    obtain ⟨μ', hμ', hyμ⟩ := hyH
    have hy2 : y = Phi ⟨beltramiMul (a : LinfStar) ν, bg_mul_mem_ball ν.2 a.2⟩ := by
      have : y = rightTrans ν (rightTrans ⟨_, hi⟩ y) := (bt_rightTrans_inv_right ν hi y).symm
      rw [this, hya, bt_rightTrans_phi]
    have hcl := hc_left_cancel a ν μ' (by rw [← hyμ, hy2])
    apply hp
    refine ⟨⟨beltramiMul (beltramiInv (a : LinfStar)) (μ' : LinfStar),
      bg_mul_mem_ball μ'.2 (bc_beltramiInv_mem_ball a.2)⟩, ?_, hcl⟩
    exact groupO_mul_mem (groupO_inv_mem ha) hμ'
  have hconn : PreconnectedSpace T1 := by
    have hb : IsPreconnected (LinfStarBall : Set LinfStar) :=
      (convex_ball (0 : LinfStar) 1).isPreconnected
    have hb' : PreconnectedSpace LinfStarBall := isPreconnected_iff_preconnectedSpace.1 hb
    have hr : IsPreconnected (range (Phi : LinfStarBall → T1)) :=
      isPreconnected_range isQuotientMap_quotient_mk'.continuous
    have hrange : range (Phi : LinfStarBall → T1) = univ :=
      Set.range_eq_univ.2 (Quotient.mk_surjective (s := teichSetoid))
    exact ⟨hrange ▸ hr⟩
  have hall : H = univ := by
    have := hconn
    exact (show IsClopen H from ⟨hclosed, hopen⟩).eq_univ ⟨_, hH0⟩
  have hp : p ∈ H := by rw [hall]; trivial
  exact hp
/-- Quantitative form of `gk_step`: a small harmonic right translation changes `∬|K₁|²` by a bounded amount. -/
theorem r43p_K1_step {κ ν : LinfStarBall} {φ : A2 unitDisc}
    (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)))
    (hνe : (ν : LinfStar) = Lambda (A2toAInf φ)) :
    (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (beltramiMul (ν : LinfStar) (κ : LinfStar))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      2 * (ENNReal.ofReal (1 / (4 * π)) *
        (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖)) ^ 2) +
      2 * ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨hn, hharm, hsm, -⟩ := gtp_small_a hφ
  rw [← hνe] at hharm hsm
  have hd := delta0_bounds
  have hν1 : ‖(ν : LinfStar)‖ < 1 := hsm.trans hd.2
  have hνL : normL2 unitDiscExterior (ν : LinfStar) = ENNReal.ofReal (2 * ‖φ‖) := by
    rw [hνe]; exact gtp_normL2_Lambda φ
  obtain ⟨γ', hγ'c, hγ'⟩ := gk_path_C1 (ν := (ν : LinfStar)) (κ := (κ : LinfStar)) hν1 κ.2
  set γ : ℝ → LinfStar := fun t => beltramiMul ((t : ℂ) • (ν : LinfStar)) (κ : LinfStar) with hγ
  have hsν : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • (ν : LinfStar) ∈ LinfStarBall := by
    intro s hs
    have : ‖(s : ℂ) • (ν : LinfStar)‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    simpa [LinfStarBall] using this
  have hγb : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ LinfStarBall := fun s hs => bg_mul_mem_ball κ.2 (hsν s hs)
  have hγ0 : γ 0 = (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_zero, zero_smul]
    exact grp_zero_mul κ.2
  have hγ1 : γ 1 = beltramiMul (ν : LinfStar) (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_one, one_smul]
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hγcont : ContinuousOn γ (Icc 0 1) := fun s hs =>
    (hγ' s hs).1.continuousAt.continuousWithinAt
  -- the variation kernel
  set D := {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} with hDdef
  set k : ℝ → ℂ × ℂ → ℂ := fun s q => fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) q.1 q.2) (γ s) (γ' s)
    with hk
  have hkder : ∀ q ∈ D, ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => kerK1 (fsans (γ t)) q.1 q.2) (k s q) s := by
    intro q hq s hs
    have hΦ := ((l27_kerK1_differentiableOn hq.1 hq.2.1 hq.2.2 (γ s) (hγb s hs)).differentiableAt
      (isOpen_ball.mem_nhds (hγb s hs))).hasFDerivAt
    exact (hΦ.restrictScalars ℝ).comp_hasDerivAt s (hγ' s hs).1
  have hkcont : ∀ q ∈ D, ContinuousOn (fun s => k s q) (Icc 0 1) := by
    intro q hq
    have hF := (l27_fderiv_continuousOn hq.1 hq.2.1 hq.2.2).comp hγcont (fun s hs => hγb s hs)
    exact hF.clm_apply hγ'c
  -- the tangent: `μ̃_s = D_{sν}R_{(sν)⁻¹}(ν)`
  set xs : ℝ → LinfStar := fun s =>
    fderiv ℂ (fun l => beltramiMul l (beltramiInv ((s : ℂ) • (ν : LinfStar)))) ((s : ℂ) • (ν : LinfStar))
      (ν : LinfStar) with hxs
  have hkform : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ D, k s q =
      1 / π ^ 2 * (deriv (fsans (γ s)) q.1 * deriv (fsans (γ s)) q.2) *
        ∫ u in gsans (γ s) '' unitDiscExterior,
          xs s (Function.invFunOn (gsans (γ s)) unitDiscExterior u) *
            (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u) /
              conj (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u))) /
            ((u - fsans (γ s) q.1) ^ 2 * (u - fsans (γ s) q.2) ^ 2) := by
    intro s hs q hq
    have h := gk_k_eq (hγ' s hs).1 (hγb s hs) hq.1 hq.2.1 hq.2.2
    rw [(hγ' s hs).2] at h
    exact h
  -- uniform bound for the tangent
  set B : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖)) ^ 2 with hB
  have hBfin : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  have hxbound : ∀ s ∈ Icc (0 : ℝ) 1, normL2 unitDiscExterior (xs s) ≤
      ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖) := by
    intro s hs
    have hsn : ‖(s : ℂ) • (ν : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    have hh : (s : ℂ) • (ν : LinfStar) ∈ harmonicBeltrami := Submodule.smul_mem _ _ hharm
    have hδ : ‖(s : ℂ) • (ν : LinfStar)‖ < delta0 := lt_of_le_of_lt hsn hsm
    have h := (grp_cor_2_6 hh hδ (hsν s hs) (ν : LinfStar)).2
    rw [hνL] at h
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h1 : 0 < 1 - ‖(ν : LinfStar)‖ := by linarith
    have h2 : 1 - ‖(ν : LinfStar)‖ ≤ 1 - ‖(s : ℂ) • (ν : LinfStar)‖ := by linarith
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  -- a jointly measurable version of the kernel (Carathéodory)
  set c : ℝ → ℝ := fun s => max 0 (min 1 s) with hcdef
  have hcI : ∀ s, c s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcs : ∀ s ∈ Icc (0 : ℝ) 1, c s = s := fun s hs => by
    simp only [hcdef, min_eq_right hs.2, max_eq_right hs.1]
  set K : ℝ → ℂ × ℂ → ℂ := fun s q => D.indicator (fun q => k (c s) q) q with hKdef
  have hKform : ∀ s, K s = D.indicator fun q =>
      1 / π ^ 2 * (deriv (fsans (γ (c s))) q.1 * deriv (fsans (γ (c s))) q.2) *
        ∫ u in gsans (γ (c s)) '' unitDiscExterior,
          xs (c s) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) *
            (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) /
              conj (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u))) /
            ((u - fsans (γ (c s)) q.1) ^ 2 * (u - fsans (γ (c s)) q.2) ^ 2) := by
    intro s
    funext q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact hkform (c s) (hcI s) q hq
    · simp only [hKdef, Set.indicator_of_notMem hq]
  have hKm : ∀ s, Measurable (K s) := fun s => by
    rw [hKform s]
    exact gk_kform_meas (hγb (c s) (hcI s)) (xs (c s))
  have hKc : ∀ q, Continuous fun s => K s q := by
    intro q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact (hkcont q hq).comp_continuous hcc hcI
    · simp only [hKdef, Set.indicator_of_notMem hq]
      exact continuous_const
  have hjoint : Measurable (Function.uncurry K) := measurable_uncurry_of_continuous_of_measurable hKc hKm
  -- pointwise FTC
  have hpt : ∀ q ∈ D, (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    intro q hq
    have h := gk_ftc_sq (F := fun t => kerK1 (fsans (γ t)) q.1 q.2) (F' := fun s => k s q)
      (hkder q hq) (hkcont q hq)
    refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_))
    simp only [hKdef, Set.indicator_of_mem hq, hcs s hs]
  -- per-`s` bound
  have hper : ∀ s, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 ≤ B := by
    intro s
    have hb := gk_I_bound (hγb (c s) (hcI s)) (xs (c s)) (k := fun a b => K s (a, b)) (by
      intro a ha b hb hab
      have hq : (a, b) ∈ D := ⟨ha, hb, hab⟩
      show K s (a, b) = _
      rw [hKform s, Set.indicator_of_mem hq])
    refine hb.trans ?_
    rw [hB]
    exact mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (hxbound (c s) (hcI s)) 2)
  -- Tonelli
  have hswap : ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 =
      ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    refine lintegral_lintegral_swap ?_
    have hm2 : Measurable (fun p : (ℂ × ℂ) × ℝ => (‖K p.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      ((hjoint.comp measurable_swap).nnnorm.coe_nnreal_ennreal).pow_const 2
    exact hm2.aemeasurable
  have hdiff : ∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤ B := by
    calc _ ≤ ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 :=
          lintegral_mono_ae (gk_offdiag_ae.mono fun q hq => hpt q hq)
      _ = _ := hswap
      _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, B := lintegral_mono fun s => hper s
      _ = B * volume (Icc (0 : ℝ) 1) := setLIntegral_const _ _
      _ = B := by rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  rw [← hγ1, ← hγ0]
  calc ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (γ 1)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ q in unitDisc ×ˢ unitDisc,
          (2 * (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
        lintegral_mono fun q => gk_sq_tri _ _
    _ = 2 * (∫⁻ q in unitDisc ×ˢ unitDisc,
            (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
        rw [lintegral_add_right' _ ((gk_kerK1_aemeas (hγb 0 h01)).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ _ := by
        rw [hB] at hdiff
        exact add_le_add (mul_le_mul' le_rfl hdiff) le_rfl

/-- `Λ` as a continuous ℂ-linear map. -/
theorem r43p_Lambda_clm : ∃ L : AInf unitDisc →L[ℂ] LinfStar, ∀ φ, L φ = Lambda φ :=
  ⟨LinearMap.mkContinuous { toFun := Lambda, map_add' := Lambda_add, map_smul' := Lambda_smul } (1 / 2)
    (fun φ => by
      show ‖Lambda φ‖ ≤ 1 / 2 * ‖φ‖
      linarith [Lambda_norm_le φ]), fun _ => rfl⟩

/-- The points of `V₀` lie in `T₀(1)`. -/
theorem r43p_V0_T01 {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    Phi ⟨Lambda (A2toAInf φ), Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)⟩ ∈ T01 := by
  rw [TakhtajanTeo.cor_3_2]
  obtain ⟨h, he⟩ := ahlfors_weill (ct_A2toAInf_norm_lt hφ)
  show AInf.toFun (bers (Phi ⟨Lambda (A2toAInf φ), _⟩)) ∈ A2fun unitDisc
  rw [show (⟨Lambda (A2toAInf φ), Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)⟩ : LinfStarBall) =
    ⟨Lambda (A2toAInf φ), h⟩ from rfl, he]
  have hr : A2toAInf φ ∈ range A2toAInf := mem_range_self φ
  rw [A2toAInf_range] at hr
  exact hr

/-- Entries of `B₁` are bounded by `1`. -/
theorem r43p_entry_le {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (m n : ℕ) :
    ‖B1 (grunsky (fsans μ) (gsans μ)) m n‖ ≤ 1 := by
  have hb := pgb_bounded hμ (A := B1 (grunsky (fsans μ) (gsans μ))) (by simp)
  have he := pmb_entry hb m n
  have h1 := (pgb_norm_lt_one hμ).1
  rw [← he]
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  calc ‖gopOp (B1 (grunsky (fsans μ) (gsans μ))) (lp.single 2 n 1 : ell2) m‖
      ≤ ‖gopOp (B1 (grunsky (fsans μ) (gsans μ))) (lp.single 2 n 1 : ell2)‖ :=
        lp.norm_apply_le_norm (by norm_num) _ m
    _ ≤ ‖gopOp (B1 (grunsky (fsans μ) (gsans μ)))‖ * ‖(lp.single 2 n 1 : ell2)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 := by
        rw [lp.norm_single (by norm_num), norm_one, mul_one]
        exact h1.le

/-- Each entry of `B₁` is holomorphic on the Beltrami ball. -/
theorem r43p_entry_holo (m n : ℕ) :
    DifferentiableOn ℂ (fun κ : LinfStar => B1 (grunsky (fsans κ) (gsans κ)) m n) LinfStarBall := by
  refine QCV.qcv_gateaux_to_frechet isOpen_ball (fun x hx => ?_) (fun x hx v => ?_)
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball : IsOpen LinfStarBall) x hx
    exact ⟨r, hr, 1, fun y hy => r43p_entry_le (hsub hy) m n⟩
  · obtain ⟨r, hr, -, hd⟩ := AppB.b1_entries (ν := x) (μ := v) (t0 := 0) (by rw [zero_smul, add_zero]; exact hx)
    exact (hd m n).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))

/-- Reindexing `ℓ²(ℕ × ℕ)` by `ℓ²(ℕ)`. -/
theorem r43p_reindex : ∃ e : ℕ ≃ ℕ × ℕ, ∃ S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] s3tc_HS,
    ∃ R : s3tc_HS → lp (fun _ : ℕ => ℂ) 2,
      (∀ A, S (R A) = A) ∧ (∀ A n, R A n = A (e n)) ∧ (∀ A, ‖R A‖ = ‖A‖) := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  set e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  have hmemR : ∀ A : s3tc_HS, Memℓp (fun n => A (e n)) 2 := fun A => by
    rw [memℓp_gen_iff h2]
    have := (memℓp_gen_iff h2).mp (lp.memℓp A)
    exact (e.summable_iff (f := fun q => ‖A q‖ ^ (2 : ℝ≥0∞).toReal)).mpr this
  have hmemS : ∀ B : lp (fun _ : ℕ => ℂ) 2, Memℓp (fun q => B (e.symm q)) 2 := fun B => by
    rw [memℓp_gen_iff h2]
    have := (memℓp_gen_iff h2).mp (lp.memℓp B)
    exact (e.symm.summable_iff (f := fun n => ‖B n‖ ^ (2 : ℝ≥0∞).toReal)).mpr this
  have hnormS : ∀ B : lp (fun _ : ℕ => ℂ) 2, ‖(⟨_, hmemS B⟩ : s3tc_HS)‖ = ‖B‖ := fun B => by
    rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
    congr 1
    exact e.symm.tsum_eq (fun n => ‖B n‖ ^ (2 : ℝ≥0∞).toReal)
  refine ⟨e, LinearMap.mkContinuous
    { toFun := fun B => ⟨_, hmemS B⟩
      map_add' := fun B C => lp.ext (funext fun q => rfl)
      map_smul' := fun c B => lp.ext (funext fun q => rfl) } 1 (fun B => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (hnormS B).le), fun A => ⟨_, hmemR A⟩, fun A => ?_, fun A n => rfl, fun A => ?_⟩
  · exact lp.ext (funext fun q => by show A (e (e.symm q)) = A q; rw [Equiv.apply_symm_apply])
  · rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
    congr 1
    exact e.tsum_eq (fun q => ‖A q‖ ^ (2 : ℝ≥0∞).toReal)

/-- Local Hilbert–Schmidt bound for `B₁` in the Hilbert coordinates of `V₀`. -/
theorem r43p_HS_local {φ₀ : A2 unitDisc} (hφ₀ : φ₀ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    ∃ r > 0, ∃ M : ℝ, ∀ φ ∈ ball φ₀ r,
      Summable (fun q : ℕ × ℕ =>
        ‖B1 (grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ)))) q.1 q.2‖ ^ 2) ∧
      ∑' q : ℕ × ℕ, ‖B1 (grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ)))) q.1 q.2‖ ^ 2 ≤ M := by
  set V : Set (A2 unitDisc) := ball 0 (Real.sqrt (π / 3)) with hVdef
  set c0 : LinfStarBall := ⟨0, mem_ball_self one_pos⟩ with hc0
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  have hinv : ∀ (m : LinfStarBall) {P : T1}, P ∈ hilbertChartDomain m →
      bersChartInv m (A2toAInf (hilbertChart m P)) = P ∧ hilbertChart m P ∈ V := fun m P hP =>
    ⟨Function.invFunOn_eq hP, Function.invFunOn_mem hP⟩
  have hleft : ∀ (m : LinfStarBall) {φ : A2 unitDisc}, φ ∈ V →
      hilbertChart m (bersChartInv m (A2toAInf φ)) = φ := fun m φ hφ =>
    (ctc_chart_injOn m).leftInvOn_invFunOn hφ
  have hcenter : ∀ m : LinfStarBall, bersChartInv m (A2toAInf 0) = Phi m := fun m => by
    rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
    exact congrArg Phi (Subtype.ext (by simp only [hz, hb_zero_mul m.2]))
  have hφ₀n := ct_A2toAInf_norm_lt hφ₀
  obtain ⟨μ₀, hμ₀, hp₀⟩ := r43p_groupO_rep (bersChartInv c0 (A2toAInf φ₀))
  obtain ⟨-, hWo, hτd, -⟩ := TakhtajanTeo.thm_2_10 μ₀ c0 hμ₀ zero_mem_groupO
  have hdom0 : bersChartInv c0 (A2toAInf φ₀) ∈ hilbertChartDomain c0 := ⟨φ₀, hφ₀, rfl⟩
  have hdomμ : bersChartInv c0 (A2toAInf φ₀) ∈ hilbertChartDomain μ₀ :=
    ⟨0, mem_ball_self (by positivity), by show bersChartInv μ₀ (A2toAInf 0) = _; rw [hcenter, hp₀]⟩
  have hφ₀W : φ₀ ∈ hilbertChart c0 '' (hilbertChartDomain μ₀ ∩ hilbertChartDomain c0) :=
    ⟨_, ⟨hdomμ, hdom0⟩, hleft c0 hφ₀⟩
  have hτ0 : hilbertChart μ₀ (bersChartInv c0 (A2toAInf φ₀)) = 0 := by
    rw [hp₀, ← hcenter μ₀, hleft μ₀ (mem_ball_self (by positivity))]
  have hτc : ContinuousAt (fun φ => hilbertChart μ₀ (bersChartInv c0 (A2toAInf φ))) φ₀ :=
    (hτd.differentiableAt (hWo.mem_nhds hφ₀W)).continuousAt
  have hd := delta0_bounds
  set ε₁ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (div_pos (by linarith [hd.1]) (Real.sqrt_pos.2 (by positivity)))
  obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.continuousAt_iff.mp hτc ε₁ hε₁0
  obtain ⟨r₂, hr₂, hr₂b⟩ := Metric.isOpen_iff.mp hWo φ₀ hφ₀W
  -- the base kernel
  have hT₀ : Phi μ₀ ∈ T01 := by
    rw [← hp₀, gtp_chart0 φ₀ hφ₀n]
    exact r43p_V0_T01 hφ₀
  have hK0 := gk_K1_T01 _ hT₀ μ₀ rfl
  set K0 := ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (μ₀ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
  set Bmax : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - delta0) ^ 2) * ENNReal.ofReal (2 * ε₁)) ^ 2 with hBmax
  have hMfin : 2 * Bmax + 2 * K0 ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) ?_, ENNReal.mul_ne_top (by norm_num) hK0.ne⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (2 * Bmax + 2 * K0).toReal, fun φ hφ => ?_⟩
  have hφ1 : dist φ φ₀ < r₁ := lt_of_lt_of_le hφ (min_le_left _ _)
  have hφ2 : φ ∈ ball φ₀ r₂ := mem_ball.mpr (lt_of_lt_of_le hφ (min_le_right _ _))
  obtain ⟨P, ⟨hPμ, hP0⟩, hPφ⟩ := hr₂b hφ2
  have hφV : φ ∈ V := hPφ ▸ (hinv c0 hP0).2
  have hch : bersChartInv c0 (A2toAInf φ) = P := by rw [← hPφ]; exact (hinv c0 hP0).1
  set ψ : A2 unitDisc := hilbertChart μ₀ (bersChartInv c0 (A2toAInf φ)) with hψ
  have hψs : ‖ψ‖ < ε₁ := by
    have := hr₁b hφ1
    rwa [hτ0, dist_zero_right] at this
  have hψV : ψ ∈ V := by rw [hψ, hch]; exact (hinv μ₀ hPμ).2
  obtain ⟨hψn, hharm, hνs, -⟩ := gtp_small_a hψs
  set ν : LinfStarBall := ⟨Lambda (A2toAInf ψ), Lambda_mem_ball hψn⟩ with hν
  have hκ' : beltramiMul (ν : LinfStar) μ₀ ∈ LinfStarBall := bg_mul_mem_ball μ₀.2 ν.2
  -- the class of `Λφ` is the right translate of `μ₀` by the small `ν`
  have hclass : Phi ⟨Lambda (A2toAInf φ), Lambda_mem_ball (ct_A2toAInf_norm_lt hφV)⟩ =
      Phi ⟨beltramiMul (ν : LinfStar) μ₀, hκ'⟩ := by
    rw [← gtp_chart0 φ (ct_A2toAInf_norm_lt hφV), hch, ← (hinv μ₀ hPμ).1, ← hch,
      ct_bersChartInv_eq (ct_A2toAInf_norm_lt hψV), bt_rightTrans_phi]
  have hgr : grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ))) =
      grunsky (fsans (beltramiMul (ν : LinfStar) μ₀)) (gsans (beltramiMul (ν : LinfStar) μ₀)) :=
    FB.fb_grunsky_class (Lambda_mem_ball (ct_A2toAInf_norm_lt hφV)) hκ' (Quotient.exact hclass)
  -- the kernel bound at the translate
  have hstep := r43p_K1_step (κ := μ₀) (ν := ν) (φ := ψ) hψs rfl
  have hBle : ENNReal.ofReal (1 / (4 * π)) *
      (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖ψ‖)) ^ 2 ≤ Bmax := by
    rw [hBmax]
    refine mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
      (ENNReal.ofReal_le_ofReal (by linarith))) 2)
    have h1 : 0 < 1 - delta0 := by linarith [hd.2]
    have h2 : 1 - delta0 ≤ 1 - ‖(ν : LinfStar)‖ := by have : ‖(ν : LinfStar)‖ < delta0 := hνs; linarith
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  have hKle : (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (beltramiMul (ν : LinfStar) μ₀)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ 2 * Bmax + 2 * K0 :=
    hstep.trans (add_le_add (mul_le_mul' le_rfl hBle) le_rfl)
  have hKfin := lt_of_le_of_lt hKle hMfin.lt_top
  -- Hilbert–Schmidt norm = kernel norm
  have L := s2c_lemma_2_5 (AppB.b8_welding_normalized_pair hκ') (r22_complement_null hκ')
  have hsumw := L.1.mp hKfin
  have heqw := (L.2.1 hKfin).1
  have hterm : (fun q : ℕ × ℕ =>
      ‖B1 (grunsky (fsans (beltramiMul (ν : LinfStar) μ₀)) (gsans (beltramiMul (ν : LinfStar) μ₀))) q.1 q.2‖ ^ 2) =
      fun q : ℕ × ℕ => ((q.1 + 1) * (q.2 + 1) : ℝ) *
        ‖grunsky (fsans (beltramiMul (ν : LinfStar) μ₀)) (gsans (beltramiMul (ν : LinfStar) μ₀))
          (-(q.1 + 1 : ℤ)) (-(q.2 + 1 : ℤ))‖ ^ 2 := by
    funext q
    unfold B1
    exact s29_norm_sq _ (by positivity) _
  rw [hgr, hterm]
  refine ⟨hsumw, ?_⟩
  have hle := heqw.le.trans hKle
  exact (ENNReal.ofReal_le_iff_le_toReal hMfin).mp hle

/-- **P1b.** `φ ↦ B₁(Λφ)` is a holomorphic Hilbert–Schmidt-valued map on `V₀`. -/
theorem r43p_B1_holo :
    ∃ A : A2 unitDisc → s3tc_HS, DifferentiableOn ℂ A (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)), ∀ m n : ℕ,
        A φ (m, n) = B1 (grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ)))) m n := by
  obtain ⟨e, S, R, hSR, hR, hRn⟩ := r43p_reindex
  obtain ⟨L, hL⟩ := r43p_Lambda_clm
  set V : Set (A2 unitDisc) := ball 0 (Real.sqrt (π / 3)) with hVdef
  set b : A2 unitDisc → ℕ × ℕ → ℂ := fun φ q =>
    B1 (grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ)))) q.1 q.2 with hb
  have hmem : ∀ φ ∈ V, Memℓp (b φ) 2 := fun φ hφ => by
    obtain ⟨r, hr, M, hM⟩ := r43p_HS_local hφ
    obtain ⟨hs, -⟩ := hM φ (mem_ball_self hr)
    exact (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr (by simpa using hs)
  set A : A2 unitDisc → s3tc_HS := fun φ => if h : Memℓp (b φ) 2 then ⟨b φ, h⟩ else 0 with hA
  have hAe : ∀ φ ∈ V, ∀ q, A φ q = b φ q := fun φ hφ q => by
    simp only [hA, dif_pos (hmem φ hφ)]
  -- entries are holomorphic in `φ`
  have hent : ∀ q : ℕ × ℕ, DifferentiableOn ℂ (fun φ => b φ q) V := fun q φ hφ => by
    have hκ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
    have h1 := ((r43p_entry_holo q.1 q.2).differentiableAt (isOpen_ball.mem_nhds hκ))
    have h2 : DifferentiableAt ℂ (fun φ : A2 unitDisc => Lambda (A2toAInf φ)) φ := by
      have : (fun φ : A2 unitDisc => Lambda (A2toAInf φ)) = fun φ => L (A2toAInfCLM φ) := by
        funext φ; rw [hL, A2toAInfCLM_apply]
      rw [this]
      exact (L.comp A2toAInfCLM).differentiableAt
    exact (h1.comp φ h2).differentiableWithinAt
  -- the reindexed `ℓ²(ℕ)` map
  have hg : DifferentiableOn ℂ (fun φ => R (A φ)) V := by
    refine wh_lp_banach isOpen_ball (fun x hx => ?_) (fun n => ?_)
    · obtain ⟨r, hr, M, hM⟩ := r43p_HS_local hx
      obtain ⟨r', hr', hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball : IsOpen V) x hx
      refine ⟨min r r', lt_min hr hr', Real.sqrt M, fun y hy => ?_⟩
      have hyr : y ∈ ball x r := mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
      have hyV : y ∈ V := hsub (mem_ball.mpr (lt_of_lt_of_le hy (min_le_right _ _)))
      obtain ⟨hs, hsM⟩ := hM y hyr
      rw [hRn, hA]
      simp only [dif_pos (hmem y hyV)]
      have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      refine lp.norm_le_of_tsum_le h2 (Real.sqrt_nonneg _) ?_
      have h22 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
      have hM0 : 0 ≤ M := (tsum_nonneg fun q => sq_nonneg _).trans hsM
      simp only [h22, Real.rpow_natCast, Real.sq_sqrt hM0]
      exact hsM
    · refine (hent (e n)).congr fun φ hφ => ?_
      rw [hR, hAe φ hφ]
  refine ⟨A, ?_, fun φ hφ m n => hAe φ hφ (m, n)⟩
  have hc : DifferentiableOn ℂ (fun φ => S (R (A φ))) V := S.differentiable.comp_differentiableOn hg
  exact hc.congr fun φ _ => (hSR (A φ)).symm

/-- **P1c → P1.** -/
theorem r43p_S2_analytic_proof :
    AnalyticOnNhd ℝ (fun φ : A2 unitDisc => liouvilleS2 (ptT (Lambda (A2toAInf φ))))
      (ball 0 (Real.sqrt (π / 3))) := by
  obtain ⟨A, hA, hAe⟩ := r43p_B1_holo
  have hAa := (bha_analyticOnNhd isOpen_ball hA).restrictScalars (𝕜 := ℝ)
  intro φ hφ
  have hκ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
  have hop : ‖s3tc_toOperator (A φ)‖ < 1 := by
    have : s3tc_toOperator (A φ) = gopOp (B1 (grunsky (fsans (Lambda (A2toAInf φ))) (gsans (Lambda (A2toAInf φ))))) := by
      change gopOp (fun m n => A φ (m, n)) = _
      congr 1
      funext m n
      exact hAe φ hφ m n
    rw [this]
    exact (pgb_norm_lt_one hκ).1
  have hc := (r43p_logSeries_analytic (A φ) hop).comp (hAa φ hφ)
  refine hc.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hφ] with ψ hψ
  have hκψ : Lambda (A2toAInf ψ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hψ)
  show s3fd_logSeries (A ψ) = liouvilleS2 (ptT (Lambda (A2toAInf ψ)))
  rw [s3fd_liouville_eq hκψ (A ψ) (hAe ψ hψ)]
  unfold ptT
  rw [dif_pos hκψ]

/-- The mixed derivative `∂_{e₁}∂̄_{e₂}` of `s ∘ Ψ` at `0`, for `s` real-analytic and `Ψ` holomorphic, depends only
on `Ψ 0` and the first derivative of `Ψ` at `0`. -/
theorem r43p_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {S : Set E}
    {s : E → ℝ} (hs : AnalyticOnNhd ℝ s S) {Ψ : ℂ × ℂ → E} {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) (h0 : (0 : ℂ × ℂ) ∈ U) (hΨ : AnalyticOnNhd ℂ Ψ U) (hΨS : MapsTo Ψ U S) :
    dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => ((s (Ψ (e₁, e₂)) : ℝ) : ℂ)) 0) 0 =
      (((fderiv ℝ (fderiv ℝ s) (Ψ 0) (fderiv ℂ Ψ 0 (1, 0)) (fderiv ℂ Ψ 0 (0, 1)) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ s) (Ψ 0) (fderiv ℂ Ψ 0 (1, 0)) (I • fderiv ℂ Ψ 0 (0, 1)) : ℝ) : ℂ) -
        I * ((fderiv ℝ (fderiv ℝ s) (Ψ 0) (I • fderiv ℂ Ψ 0 (1, 0)) (fderiv ℂ Ψ 0 (0, 1)) : ℝ) : ℂ) +
        ((fderiv ℝ (fderiv ℝ s) (Ψ 0) (I • fderiv ℂ Ψ 0 (1, 0)) (I • fderiv ℂ Ψ 0 (0, 1)) : ℝ) : ℂ)) / 4 := by
  set Bf : ℂ → E := fun e₁ => fderiv ℂ Ψ (e₁, 0) (0, 1) with hBf
  set Φ : ℂ → ℂ := fun e₁ => (1 / 2 : ℂ) * (((fderiv ℝ s (Ψ (e₁, 0)) (Bf e₁) : ℝ) : ℂ) +
    I * ((fderiv ℝ s (Ψ (e₁, 0)) (I • Bf e₁) : ℝ) : ℂ)) with hΦ
  have hc1 : Continuous fun e₁ : ℂ => ((e₁, (0 : ℂ)) : ℂ × ℂ) := continuous_id.prodMk continuous_const
  have hU1 : (fun e₁ : ℂ => ((e₁, (0 : ℂ)) : ℂ × ℂ)) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hc1.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  -- the inner `∂̄`
  have hin : (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => ((s (Ψ (e₁, e₂)) : ℝ) : ℂ)) 0) =ᶠ[𝓝 0] Φ := by
    filter_upwards [hU1] with e₁ he₁
    have he₁' : ((e₁, (0 : ℂ)) : ℂ × ℂ) ∈ U := he₁
    have hd : HasFDerivAt Ψ (fderiv ℂ Ψ (e₁, 0)) (e₁, 0) := (hΨ (e₁, 0) he₁').differentiableAt.hasFDerivAt
    have hl : HasFDerivAt (fun e₂ : ℂ => ((e₁, e₂) : ℂ × ℂ))
        ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) (0 : ℂ) :=
      (hasFDerivAt_const e₁ (0 : ℂ)).prodMk (hasFDerivAt_id (0 : ℂ))
    have hc : HasFDerivAt (fun e₂ : ℂ => Ψ (e₁, e₂))
        ((fderiv ℂ Ψ (e₁, 0)).comp ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) (0 : ℂ) :=
      hd.comp (0 : ℂ) hl
    have hsd : HasFDerivAt s (fderiv ℝ s (Ψ (e₁, 0))) (Ψ (e₁, 0)) :=
      (hs _ (hΨS he₁')).differentiableAt.hasFDerivAt
    have hg : HasFDerivAt (fun e₂ : ℂ => ((s (Ψ (e₁, e₂)) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((fderiv ℝ s (Ψ (e₁, 0))).comp
          (((fderiv ℂ Ψ (e₁, 0)).comp ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))).restrictScalars ℝ)))
        (0 : ℂ) :=
      Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) (hsd.comp (0 : ℂ) (hc.restrictScalars ℝ))
    have hI : fderiv ℂ Ψ (e₁, 0) ((0 : ℂ), I) = I • Bf e₁ := by
      show fderiv ℂ Ψ (e₁, 0) ((0 : ℂ), I) = I • fderiv ℂ Ψ (e₁, 0) ((0 : ℂ), (1 : ℂ))
      rw [← map_smul]
      congr 1
      ext <;> simp
    unfold dzbar
    rw [hg.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply,
      Complex.ofRealCLM_apply]
    rw [hI]
    simp only [hΦ, hBf]
    ring
  -- the outer `∂`
  have hx0 : Ψ 0 ∈ S := hΨS h0
  have hs1 : HasFDerivAt (fderiv ℝ s) (fderiv ℝ (fderiv ℝ s) (Ψ 0)) (Ψ 0) :=
    (hs.fderiv _ hx0).differentiableAt.hasFDerivAt
  have hd0 : HasFDerivAt Ψ (fderiv ℂ Ψ 0) (((0 : ℂ), (0 : ℂ)) : ℂ × ℂ) :=
    (hΨ 0 h0).differentiableAt.hasFDerivAt
  have hd0' : HasFDerivAt (fderiv ℂ Ψ) (fderiv ℂ (fderiv ℂ Ψ) 0) (((0 : ℂ), (0 : ℂ)) : ℂ × ℂ) :=
    (hΨ.fderiv 0 h0).differentiableAt.hasFDerivAt
  have hl1 : HasFDerivAt (fun e₁ : ℂ => ((e₁, (0 : ℂ)) : ℂ × ℂ))
      ((ContinuousLinearMap.id ℂ ℂ).prod (0 : ℂ →L[ℂ] ℂ)) (0 : ℂ) :=
    (hasFDerivAt_id (0 : ℂ)).prodMk (hasFDerivAt_const (0 : ℂ) (0 : ℂ))
  set A1 : ℂ →L[ℂ] E := (fderiv ℂ Ψ 0).comp ((ContinuousLinearMap.id ℂ ℂ).prod (0 : ℂ →L[ℂ] ℂ)) with hA1
  set B1' : ℂ →L[ℂ] E := (ContinuousLinearMap.apply ℂ E ((0 : ℂ), (1 : ℂ))).comp
    ((fderiv ℂ (fderiv ℂ Ψ) 0).comp ((ContinuousLinearMap.id ℂ ℂ).prod (0 : ℂ →L[ℂ] ℂ))) with hB1'
  have hΨ1 : HasFDerivAt (fun e₁ : ℂ => Ψ (e₁, 0)) A1 (0 : ℂ) := HasFDerivAt.comp (g := Ψ) (f := fun e₁ : ℂ => ((e₁, (0 : ℂ)) : ℂ × ℂ)) (0 : ℂ) hd0 hl1
  have hD : HasFDerivAt (fun e₁ : ℂ => fderiv ℝ s (Ψ (e₁, 0)))
      ((fderiv ℝ (fderiv ℝ s) (Ψ 0)).comp (A1.restrictScalars ℝ)) (0 : ℂ) :=
    hs1.comp (0 : ℂ) (hΨ1.restrictScalars ℝ)
  have hB : HasFDerivAt Bf B1' (0 : ℂ) :=
    (ContinuousLinearMap.apply ℂ E ((0 : ℂ), (1 : ℂ))).hasFDerivAt.comp (0 : ℂ) (HasFDerivAt.comp (g := fderiv ℂ Ψ) (f := fun e₁ : ℂ => ((e₁, (0 : ℂ)) : ℂ × ℂ)) (0 : ℂ) hd0' hl1)
  have hBr := hB.restrictScalars ℝ
  have hBI : HasFDerivAt (fun e₁ => I • Bf e₁) (I • B1'.restrictScalars ℝ) (0 : ℂ) := hBr.const_smul I
  have hP1 := hD.clm_apply hBr
  have hP2 := hD.clm_apply hBI
  have hΦd : HasFDerivAt Φ ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp
      ((fderiv ℝ s (Ψ ((0 : ℂ), 0))).comp (B1'.restrictScalars ℝ) +
        ((fderiv ℝ (fderiv ℝ s) (Ψ 0)).comp (A1.restrictScalars ℝ)).flip (Bf 0)) +
      I • Complex.ofRealCLM.comp ((fderiv ℝ s (Ψ ((0 : ℂ), 0))).comp (I • B1'.restrictScalars ℝ) +
        ((fderiv ℝ (fderiv ℝ s) (Ψ 0)).comp (A1.restrictScalars ℝ)).flip (I • Bf 0)))) (0 : ℂ) :=
    ((Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hP1).add
      ((Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hP2).const_mul I)).const_mul (1 / 2 : ℂ)
  have hz0 : ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) := rfl
  have hA1I : A1 I = I • A1 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hB1I : B1' I = I • B1' 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hBf0 : Bf 0 = fderiv ℂ Ψ 0 (0, 1) := rfl
  have hA11 : A1 1 = fderiv ℂ Ψ 0 (1, 0) := by
    simp only [hA1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  unfold dz
  rw [hin.fderiv_eq, hΦd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, hz0]
  rw [hA1I, hB1I, hBf0, hA11, smul_smul, I_mul_I, neg_one_smul, map_neg]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `∂∂̄` at `0` depends only on the germ at `0`. -/
theorem r43p_germ {F G : ℂ × ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => F (e₁, e₂)) 0) 0 =
      dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => G (e₁, e₂)) 0) 0 := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp h
  have hout : (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => F (e₁, e₂)) 0) =ᶠ[𝓝 0]
      (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => G (e₁, e₂)) 0) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with e₁ he₁
    have hin : (fun e₂ : ℂ => F (e₁, e₂)) =ᶠ[𝓝 0] (fun e₂ : ℂ => G (e₁, e₂)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with e₂ he₂
      apply hb
      rw [Prod.dist_eq]
      exact max_lt (mem_ball.mp he₁) (mem_ball.mp he₂)
    unfold dzbar
    rw [hin.fderiv_eq]
  unfold dz
  rw [hout.fderiv_eq]

/-- A harmonic `L²` Beltrami differential is `Λ` of an `A₂` element. -/
theorem r43p_harm_A2 {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    ∃ χ : A2 unitDisc, Lambda (A2toAInf χ) = toLinf m := by
  have h1 := D0bers_harmonicL2.1 m hm
  have h2 : fderiv ℂ bersPhi 0 (toLinf m) ∈ range A2toAInf := by
    rw [A2toAInf_range]
    exact h1
  obtain ⟨χ, hχ⟩ := h2
  refine ⟨χ, ?_⟩
  rw [hχ, ← hp_eq_Lambda, wp_harmonicProj_fix hm]

/-- The Hilbert chart at the origin of the right translates `[l * Λφ]`, near `l = 0`. -/
theorem r43p_chartT {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    ∃ T : A2 unitDisc → A2 unitDisc, ∃ W : Set (A2 unitDisc), IsOpen W ∧ (0 : A2 unitDisc) ∈ W ∧
      DifferentiableOn ℂ T W ∧ T 0 = φ ∧ ∀ χ ∈ W, T χ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) ∧
        ptT (Lambda (A2toAInf (T χ))) = ptT (beltramiMul (Lambda (A2toAInf χ)) (Lambda (A2toAInf φ))) ∧
        A2toAInf (T χ) = bersPhi (beltramiMul (Lambda (A2toAInf χ)) (Lambda (A2toAInf φ))) := by
  set V : Set (A2 unitDisc) := ball 0 (Real.sqrt (π / 3)) with hVdef
  set c0 : LinfStarBall := ⟨0, mem_ball_self one_pos⟩ with hc0
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  have hinv : ∀ (m : LinfStarBall) {P : T1}, P ∈ hilbertChartDomain m →
      bersChartInv m (A2toAInf (hilbertChart m P)) = P ∧ hilbertChart m P ∈ V := fun m P hP =>
    ⟨Function.invFunOn_eq hP, Function.invFunOn_mem hP⟩
  have hleft : ∀ (m : LinfStarBall) {φ : A2 unitDisc}, φ ∈ V →
      hilbertChart m (bersChartInv m (A2toAInf φ)) = φ := fun m φ hφ =>
    (ctc_chart_injOn m).leftInvOn_invFunOn hφ
  have hcenter : ∀ m : LinfStarBall, bersChartInv m (A2toAInf 0) = Phi m := fun m => by
    rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
    exact congrArg Phi (Subtype.ext (by simp only [hz, hb_zero_mul m.2]))
  have hκ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
  have hp : bersChartInv c0 (A2toAInf φ) = Phi ⟨Lambda (A2toAInf φ), hκ⟩ :=
    gtp_chart0 φ (ct_A2toAInf_norm_lt hφ)
  obtain ⟨μ₀, hμ₀, hp₀⟩ := r43p_groupO_rep (bersChartInv c0 (A2toAInf φ))
  obtain ⟨hWo, -, -, hTd⟩ := TakhtajanTeo.thm_2_10 μ₀ c0 hμ₀ zero_mem_groupO
  have hdom0 : bersChartInv c0 (A2toAInf φ) ∈ hilbertChartDomain c0 := ⟨φ, hφ, rfl⟩
  have hdomμ : bersChartInv c0 (A2toAInf φ) ∈ hilbertChartDomain μ₀ :=
    ⟨0, mem_ball_self (by positivity), by show bersChartInv μ₀ (A2toAInf 0) = _; rw [hcenter, hp₀]⟩
  have h0W : (0 : A2 unitDisc) ∈ hilbertChart μ₀ '' (hilbertChartDomain μ₀ ∩ hilbertChartDomain c0) := by
    refine ⟨_, ⟨hdomμ, hdom0⟩, ?_⟩
    rw [hp₀, ← hcenter μ₀, hleft μ₀ (mem_ball_self (by positivity))]
  have hμκ : Phi μ₀ = Phi ⟨Lambda (A2toAInf φ), hκ⟩ := by rw [← hp₀, hp]
  refine ⟨fun χ => hilbertChart c0 (bersChartInv μ₀ (A2toAInf χ)), _, hWo, h0W, hTd, ?_, fun χ hχ => ?_⟩
  · show hilbertChart c0 (bersChartInv μ₀ (A2toAInf 0)) = φ
    rw [hcenter, ← hp₀, hleft c0 hφ]
  · obtain ⟨P, ⟨hPμ, hP0⟩, rfl⟩ := hχ
    have hχV := (hinv μ₀ hPμ).2
    have hPe : bersChartInv μ₀ (A2toAInf (hilbertChart μ₀ P)) = P := (hinv μ₀ hPμ).1
    show hilbertChart c0 (bersChartInv μ₀ (A2toAInf (hilbertChart μ₀ P))) ∈ V ∧
      ptT (Lambda (A2toAInf (hilbertChart c0 (bersChartInv μ₀ (A2toAInf (hilbertChart μ₀ P)))))) =
        ptT (beltramiMul (Lambda (A2toAInf (hilbertChart μ₀ P))) (Lambda (A2toAInf φ))) ∧
      A2toAInf (hilbertChart c0 (bersChartInv μ₀ (A2toAInf (hilbertChart μ₀ P)))) =
        bersPhi (beltramiMul (Lambda (A2toAInf (hilbertChart μ₀ P))) (Lambda (A2toAInf φ)))
    rw [hPe]
    have hτV : hilbertChart c0 P ∈ V := (hinv c0 hP0).2
    have hτe : bersChartInv c0 (A2toAInf (hilbertChart c0 P)) = P := (hinv c0 hP0).1
    have hψn := ct_A2toAInf_norm_lt hχV
    have hτn := ct_A2toAInf_norm_lt hτV
    have hm : beltramiMul (Lambda (A2toAInf (hilbertChart μ₀ P))) (Lambda (A2toAInf φ)) ∈ LinfStarBall :=
      bg_mul_mem_ball hκ (Lambda_mem_ball hψn)
    have hP1 : P = Phi ⟨_, hm⟩ := by
      calc P = bersChartInv μ₀ (A2toAInf (hilbertChart μ₀ P)) := hPe.symm
        _ = Phi ⟨_, hm⟩ := by rw [ct_bersChartInv_eq hψn, ctb_rightTrans_congr hμκ, bt_rightTrans_phi]
    have hP2 : P = Phi ⟨Lambda (A2toAInf (hilbertChart c0 P)), Lambda_mem_ball hτn⟩ := by
      calc P = bersChartInv c0 (A2toAInf (hilbertChart c0 P)) := hτe.symm
        _ = _ := gtp_chart0 _ hτn
    obtain ⟨hL, hLe⟩ := ahlfors_weill hτn
    refine ⟨hτV, ?_, ?_⟩
    · unfold ptT
      rw [dif_pos (Lambda_mem_ball hτn), dif_pos hm, ← hP2, ← hP1]
    · calc A2toAInf (hilbertChart c0 P) = bers (Phi ⟨Lambda (A2toAInf (hilbertChart c0 P)), hL⟩) := hLe.symm
        _ = bers (Phi ⟨_, hm⟩) := by rw [← hP2, ← hP1]
        _ = _ := bers_Phi _

/-- The first derivative of the chart transition is the translated Bers differential. -/
theorem r43p_T_fderiv {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)))
    {T : A2 unitDisc → A2 unitDisc} {W : Set (A2 unitDisc)} (hWo : IsOpen W) (h0 : (0 : A2 unitDisc) ∈ W)
    (hTd : DifferentiableOn ℂ T W)
    (hTe : ∀ χ ∈ W, A2toAInf (T χ) = bersPhi (beltramiMul (Lambda (A2toAInf χ)) (Lambda (A2toAInf φ))))
    (ψ : A2 unitDisc) :
    A2toAInf (fderiv ℂ T 0 ψ) = D0BersR (Lambda (A2toAInf φ)) (Lambda (A2toAInf ψ)) := by
  obtain ⟨L, hL⟩ := r43p_Lambda_clm
  set L' : A2 unitDisc →L[ℂ] LinfStar := L.comp A2toAInfCLM with hL'def
  have hL' : ∀ χ, L' χ = Lambda (A2toAInf χ) := fun χ => by
    rw [hL'def, ContinuousLinearMap.comp_apply, A2toAInfCLM_apply, hL]
  have hκ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
  have h1 : HasFDerivAt (fun χ => A2toAInf (T χ)) (A2toAInfCLM.comp (fderiv ℂ T 0)) 0 :=
    A2toAInfCLM.hasFDerivAt.comp 0 (hTd.differentiableAt (hWo.mem_nhds h0)).hasFDerivAt
  have h2 : HasFDerivAt (fun χ => bersPhi (beltramiMul (L' χ) (Lambda (A2toAInf φ))))
      ((D0BersR (Lambda (A2toAInf φ))).comp L') 0 := by
    have hb := hb_D0BersR_hasFDerivAt hκ
    rw [← map_zero L'] at hb
    exact hb.comp 0 L'.hasFDerivAt
  have h2' : HasFDerivAt (fun χ => A2toAInf (T χ)) ((D0BersR (Lambda (A2toAInf φ))).comp L') 0 := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hWo.mem_nhds h0] with χ hχ
    rw [hTe χ hχ, hL']
  have h3 := congrArg (fun F : A2 unitDisc →L[ℂ] AInf unitDisc => F ψ) (h1.unique h2')
  simpa only [ContinuousLinearMap.comp_apply, A2toAInfCLM_apply, hL'] using h3

/-- The Bers differential at `Λφ` along a harmonic direction `Λχ` is `χ`. -/
theorem r43p_bers_dir {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)))
    {χ : A2 unitDisc} {m : LinfStar} (hχ : Lambda (A2toAInf χ) = m) :
    fderiv ℂ bersPhi (Lambda (A2toAInf φ)) m = A2toAInf χ := by
  obtain ⟨L, hL⟩ := r43p_Lambda_clm
  set L' : A2 unitDisc →L[ℂ] LinfStar := L.comp A2toAInfCLM with hL'def
  have hL' : ∀ χ, L' χ = Lambda (A2toAInf χ) := fun χ => by
    rw [hL'def, ContinuousLinearMap.comp_apply, A2toAInfCLM_apply, hL]
  have hκ : L' φ ∈ LinfStarBall := by rw [hL']; exact Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
  have hb : HasFDerivAt bersPhi (fderiv ℂ bersPhi (L' φ)) (L' φ) :=
    (bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds hκ)).hasFDerivAt
  have h1 : HasFDerivAt (fun ψ => bersPhi (L' ψ)) ((fderiv ℂ bersPhi (L' φ)).comp L') φ :=
    hb.comp φ L'.hasFDerivAt
  have h2 : HasFDerivAt (fun ψ => bersPhi (L' ψ)) A2toAInfCLM φ := by
    refine A2toAInfCLM.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hφ] with ψ hψ
    obtain ⟨h, he⟩ := ahlfors_weill (ct_A2toAInf_norm_lt hψ)
    rw [hL', A2toAInfCLM_apply]
    exact (bers_Phi ⟨Lambda (A2toAInf ψ), h⟩).symm.trans he
  have h3 := congrArg (fun F : A2 unitDisc →L[ℂ] AInf unitDisc => F χ) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, A2toAInfCLM_apply, hL', hχ] at h3
  exact h3

/-- `g_{μν̄}(κ)` is the WP pairing of the harmonic representatives of `P R(μ, κ)` and `P R(ν, κ)`. -/
theorem r43p_gWP_eq {μ ν : ℂ → ℂ} {κ : LinfStar} {m₁ m₂ : ℂ → ℂ}
    (hm₁ : m₁ ∈ harmonicL2 unitDiscExterior) (hm₂ : m₂ ∈ harmonicL2 unitDiscExterior)
    (he₁ : toLinf m₁ = harmonicProj (Rnm (toLinf μ) κ)) (he₂ : toLinf m₂ = harmonicProj (Rnm (toLinf ν) κ)) :
    gWP μ ν κ = wpInner m₁ m₂ := by
  have hae : ∀ {m : ℂ → ℂ}, m ∈ harmonicL2 unitDiscExterior →
      ⇑(toLinf m) =ᵐ[volume.restrict unitDiscExterior] m := fun hm => by
    unfold toLinf
    rw [dif_pos (d2_harmonicL2_memLp hm)]
    exact MemLp.coeFn_toLp _
  unfold gWP wpInner
  refine integral_congr_ae ?_
  filter_upwards [hae hm₁, hae hm₂] with z h1 h2
  rw [← he₁, ← he₂, h1, h2]

/-- **P2, pointwise.** The chart-change identity at `φ ∈ V₀`, with the constant fields `χ_μ`, `χ_ν`. -/
theorem r43p_bridge_pt {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hs : AnalyticOnNhd ℝ (fun x : A2 unitDisc => liouvilleS2 (ptT (Lambda (A2toAInf x))))
      (ball 0 (Real.sqrt (π / 3))))
    {χμ χν : A2 unitDisc} (hχμ : Lambda (A2toAInf χμ) = toLinf μ) (hχν : Lambda (A2toAInf χν) = toLinf ν)
    {φ : A2 unitDisc} (hφ : φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    gWPChart μ ν (A2toAInf φ) = -(12 * π : ℂ) * dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
      ((liouvilleS2 (ptT (Lambda (A2toAInf (φ + e₁ • χμ + e₂ • χν)))) : ℝ) : ℂ)) 0) 0 := by
  set V : Set (A2 unitDisc) := ball 0 (Real.sqrt (π / 3)) with hVdef
  have hκ : Lambda (A2toAInf φ) ∈ LinfStarBall := Lambda_mem_ball (ct_A2toAInf_norm_lt hφ)
  -- the harmonic representatives of `P R(μ, κ)`, `P R(ν, κ)` and their `A₂` preimages
  obtain ⟨m₁, hm₁, hm₁e, -⟩ := hbPre_projection_L2 _ (WPCV.x5_Rnm_L2 hμ hκ)
  obtain ⟨m₂, hm₂, hm₂e, -⟩ := hbPre_projection_L2 _ (WPCV.x5_Rnm_L2 hν hκ)
  obtain ⟨ψ₁, hψ₁⟩ := r43p_harm_A2 hm₁
  obtain ⟨ψ₂, hψ₂⟩ := r43p_harm_A2 hm₂
  -- the chart transition and its first derivatives
  obtain ⟨T, W, hWo, h0W, hTd, hT0, hTW⟩ := r43p_chartT hφ
  have hTe : ∀ χ ∈ W, A2toAInf (T χ) =
      bersPhi (beltramiMul (Lambda (A2toAInf χ)) (Lambda (A2toAInf φ))) := fun χ hχ => (hTW χ hχ).2.2
  have hdir : ∀ {ψ χ : A2 unitDisc} {m n : ℂ → ℂ}, Lambda (A2toAInf ψ) = toLinf m →
      toLinf m = harmonicProj (Rnm (toLinf n) (Lambda (A2toAInf φ))) →
      Lambda (A2toAInf χ) = toLinf n → fderiv ℂ T 0 ψ = χ := fun hψ hm hχ => by
    apply A2toAInf_injective
    rw [r43p_T_fderiv hφ hWo h0W hTd hTe, hψ, hm, hbPre_derivative_projection hκ, hb_D0BersR_chain hκ,
      ContinuousLinearMap.comp_apply, hb_D0Right_Rnm hκ, r43p_bers_dir hφ hχ]
  have hT1 : fderiv ℂ T 0 ψ₁ = χμ := hdir hψ₁ hm₁e hχμ
  have hT2 : fderiv ℂ T 0 ψ₂ = χν := hdir hψ₂ hm₂e hχν
  -- `g = ⟨PRμ, PRν⟩_WP = -12π ∂∂̄S₂` along the right-translated line
  have hg : gWPChart μ ν (A2toAInf φ) = wpInner m₁ m₂ := r43p_gWP_eq hm₁ hm₂ hm₁e hm₂e
  have hS4 : bersDzDzbar liouvilleS2 (Lambda (A2toAInf φ)) m₁ m₂ = -(1 / (12 * π)) * wpInner m₁ m₂ :=
    s4g_S2_ddbar (κ := ⟨Lambda (A2toAInf φ), hκ⟩) (r43p_V0_T01 hφ) hm₁ hm₂
  -- the two holomorphic parametrizations
  set M : ℂ × ℂ →L[ℂ] A2 unitDisc := (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight ψ₁ +
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight ψ₂ with hM
  set N : ℂ × ℂ →L[ℂ] A2 unitDisc := (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight χμ +
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight χν with hN
  have hMe : ∀ e : ℂ × ℂ, M e = e.1 • ψ₁ + e.2 • ψ₂ := fun e => by
    simp only [hM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hNe : ∀ e : ℂ × ℂ, N e = e.1 • χμ + e.2 • χν := fun e => by
    simp only [hN, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hTa : AnalyticOnNhd ℂ T W := bha_analyticOnNhd hWo hTd
  have hUT : IsOpen (M ⁻¹' W) := hWo.preimage M.continuous
  have h0T : (0 : ℂ × ℂ) ∈ M ⁻¹' W := by
    show M 0 ∈ W
    rw [map_zero]
    exact h0W
  have hΨT : AnalyticOnNhd ℂ (fun e => T (M e)) (M ⁻¹' W) := fun e he =>
    AnalyticAt.comp (g := T) (f := ⇑M) (hTa (M e) he) (M.analyticAt e)
  have jT := r43p_jet hs hUT h0T hΨT (by intro e he; exact (hTW (M e) he).1)
  have hHN : ∀ e : ℂ × ℂ, φ + e.1 • χμ + e.2 • χν = φ + N e := fun e => by rw [hNe, add_assoc]
  have hHf : (fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν) = fun e => φ + N e := funext hHN
  have hUH : IsOpen ((fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν) ⁻¹' V) := by
    rw [hHf]
    exact isOpen_ball.preimage (continuous_const.add N.continuous)
  have h0H : (0 : ℂ × ℂ) ∈ (fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν) ⁻¹' V := by
    show φ + (0 : ℂ × ℂ).1 • χμ + (0 : ℂ × ℂ).2 • χν ∈ V
    simpa using hφ
  have hΨH : AnalyticOnNhd ℂ (fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν)
      ((fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν) ⁻¹' V) := fun e _ => by
    rw [hHf]
    exact analyticAt_const.add (N.analyticAt e)
  have jH := r43p_jet hs hUH h0H hΨH (by intro e he; exact he)
  dsimp only at jT jH
  have hdT : HasFDerivAt (fun e => T (M e)) ((fderiv ℂ T 0).comp M) (0 : ℂ × ℂ) := by
    have h : HasFDerivAt T (fderiv ℂ T 0) (M 0) := by
      rw [map_zero M]
      exact (hTd.differentiableAt (hWo.mem_nhds h0W)).hasFDerivAt
    exact h.comp 0 M.hasFDerivAt
  have hdH : HasFDerivAt (fun e : ℂ × ℂ => φ + e.1 • χμ + e.2 • χν) N (0 : ℂ × ℂ) := by
    rw [hHf]
    exact N.hasFDerivAt.const_add φ
  -- the germ of the translated line
  have hgerm : bersDzDzbar liouvilleS2 (Lambda (A2toAInf φ)) m₁ m₂ =
      dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
        ((liouvilleS2 (ptT (Lambda (A2toAInf (T (M (e₁, e₂)))))) : ℝ) : ℂ)) 0) 0 := by
    unfold bersDzDzbar
    refine r43p_germ (F := fun e : ℂ × ℂ =>
      ((liouvilleS2 (ptT (beltramiMul (e.1 • toLinf m₁ + e.2 • toLinf m₂) (Lambda (A2toAInf φ)))) : ℝ) : ℂ))
      (G := fun e => ((liouvilleS2 (ptT (Lambda (A2toAInf (T (M e))))) : ℝ) : ℂ)) ?_
    filter_upwards [hUT.mem_nhds h0T] with e he
    have h1 := (hTW (M e) he).2.1
    have h2 : Lambda (A2toAInf (M e)) = e.1 • toLinf m₁ + e.2 • toLinf m₂ := by
      rw [hMe, ← A2toAInfCLM_apply, map_add, map_smul, map_smul, A2toAInfCLM_apply, A2toAInfCLM_apply,
        Lambda_add, Lambda_smul, Lambda_smul, hψ₁, hψ₂]
    show ((liouvilleS2 (ptT (beltramiMul (e.1 • toLinf m₁ + e.2 • toLinf m₂) (Lambda (A2toAInf φ)))) : ℝ) : ℂ) =
      ((liouvilleS2 (ptT (Lambda (A2toAInf (T (M e))))) : ℝ) : ℂ)
    rw [h1, h2]
  -- the two jets agree
  have hjet : dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
        ((liouvilleS2 (ptT (Lambda (A2toAInf (T (M (e₁, e₂)))))) : ℝ) : ℂ)) 0) 0 =
      dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
        ((liouvilleS2 (ptT (Lambda (A2toAInf (φ + e₁ • χμ + e₂ • χν)))) : ℝ) : ℂ)) 0) 0 := by
    have hM10 : (fderiv ℂ T 0).comp M (1, 0) = χμ := by
      rw [ContinuousLinearMap.comp_apply, hMe]
      simp only [one_smul, zero_smul, add_zero]
      exact hT1
    have hM01 : (fderiv ℂ T 0).comp M (0, 1) = χν := by
      rw [ContinuousLinearMap.comp_apply, hMe]
      simp only [one_smul, zero_smul, zero_add]
      exact hT2
    have hN10 : N (1, 0) = χμ := by rw [hNe]; simp only [one_smul, zero_smul, add_zero]
    have hN01 : N (0, 1) = χν := by rw [hNe]; simp only [one_smul, zero_smul, zero_add]
    rw [jT, jH, hdT.fderiv, hdH.fderiv]
    simp only [hM10, hM01, hN10, hN01, map_zero, hT0, Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc gWPChart μ ν (A2toAInf φ) = wpInner m₁ m₂ := hg
    _ = -(12 * π : ℂ) * bersDzDzbar liouvilleS2 (Lambda (A2toAInf φ)) m₁ m₂ := by
        rw [hS4, ← mul_assoc, neg_mul_neg, mul_one_div_cancel (mul_ne_zero (by norm_num) hπ), one_mul]
    _ = _ := by rw [hgerm, hjet]

/-- **P2.** -/
theorem r43p_bridge_proof {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hs : AnalyticOnNhd ℝ (fun x : A2 unitDisc => liouvilleS2 (ptT (Lambda (A2toAInf x))))
      (ball 0 (Real.sqrt (π / 3)))) :
    ∃ v w : A2 unitDisc → A2 unitDisc,
      AnalyticOnNhd ℝ v (ball 0 (Real.sqrt (π / 3))) ∧ AnalyticOnNhd ℝ w (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        gWPChart μ ν (A2toAInf φ) = -(12 * π : ℂ) * dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
          ((liouvilleS2 (ptT (Lambda (A2toAInf (φ + e₁ • v φ + e₂ • w φ)))) : ℝ) : ℂ)) 0) 0 := by
  obtain ⟨χμ, hχμ⟩ := r43p_harm_A2 hμ
  obtain ⟨χν, hχν⟩ := r43p_harm_A2 hν
  exact ⟨fun _ => χμ, fun _ => χν, analyticOnNhd_const, analyticOnNhd_const,
    fun φ hφ => r43p_bridge_pt hμ hν hs hχμ hχν hφ⟩

/-- P1. The potential `S₂` is real-analytic in the Hilbert coordinates of `V₀`. -/
theorem r43p_S2_analytic :
    AnalyticOnNhd ℝ (fun φ : A2 unitDisc => liouvilleS2 (ptT (Lambda (A2toAInf φ))))
      (ball 0 (Real.sqrt (π / 3))) := by
  exact r43p_S2_analytic_proof

/-- P2. Chart change: `g_{μν̄}(φ) = −12π ∂_{e₁}∂̄_{e₂} s₂(φ + e₁ v(φ) + e₂ w(φ))|₀` on `V₀`, with real-analytic
vector fields `v, w`. -/
theorem r43p_bridge {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ∃ v w : A2 unitDisc → A2 unitDisc,
      AnalyticOnNhd ℝ v (ball 0 (Real.sqrt (π / 3))) ∧ AnalyticOnNhd ℝ w (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        gWPChart μ ν (A2toAInf φ) = -(12 * π : ℂ) * dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ =>
          ((liouvilleS2 (ptT (Lambda (A2toAInf (φ + e₁ • v φ + e₂ • w φ)))) : ℝ) : ℂ)) 0) 0 := by
  exact r43p_bridge_proof hμ hν r43p_S2_analytic_proof

/-- P3. A mixed `∂∂̄` derivative of a real-analytic function along real-analytic vector fields is real-analytic. -/
theorem r43p_ddbar_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {V : Set E}
    (hV : IsOpen V) {s : E → ℝ} (hs : AnalyticOnNhd ℝ s V) {v w : E → E} (hv : AnalyticOnNhd ℝ v V)
    (hw : AnalyticOnNhd ℝ w V) :
    AnalyticOnNhd ℝ (fun φ => dz (fun e₁ : ℂ => dzbar (fun e₂ : ℂ => ((s (φ + e₁ • v φ + e₂ • w φ) : ℝ) : ℂ)) 0) 0)
      V := by
  -- the jointly analytic integrand on `(E × ℂ) × ℂ`
  set G : (E × ℂ) × ℂ → E := fun p => p.1.1 + p.1.2 • v p.1.1 + p.2 • w p.1.1 with hG
  set S₁ : Set ((E × ℂ) × ℂ) := {p | p.1.1 ∈ V} ∩ G ⁻¹' V with hS₁
  have hP : IsOpen {p : (E × ℂ) × ℂ | p.1.1 ∈ V} := hV.preimage (continuous_fst.comp continuous_fst)
  have hGa : ∀ p ∈ {p : (E × ℂ) × ℂ | p.1.1 ∈ V}, AnalyticAt ℝ G p := fun p hp => by
    have h11 : AnalyticAt ℝ (fun p : (E × ℂ) × ℂ => p.1.1) p :=
      ((ContinuousLinearMap.fst ℝ E ℂ).comp (ContinuousLinearMap.fst ℝ (E × ℂ) ℂ)).analyticAt p
    have h12 : AnalyticAt ℝ (fun p : (E × ℂ) × ℂ => p.1.2) p :=
      ((ContinuousLinearMap.snd ℝ E ℂ).comp (ContinuousLinearMap.fst ℝ (E × ℂ) ℂ)).analyticAt p
    have h2 : AnalyticAt ℝ (fun p : (E × ℂ) × ℂ => p.2) p := (ContinuousLinearMap.snd ℝ (E × ℂ) ℂ).analyticAt p
    exact (h11.add (h12.smul ((hv _ hp).comp (f := fun p : (E × ℂ) × ℂ => p.1.1) h11))).add
      (h2.smul ((hw _ hp).comp (f := fun p : (E × ℂ) × ℂ => p.1.1) h11))
  have hS₁o : IsOpen S₁ :=
    ContinuousOn.isOpen_inter_preimage (fun p hp => (hGa p hp).continuousAt.continuousWithinAt) hP hV
  have hH : AnalyticOnNhd ℝ (fun p : (E × ℂ) × ℂ => ((s (G p) : ℝ) : ℂ)) S₁ := fun p hp =>
    (Complex.ofRealCLM.analyticAt _).comp ((hs _ hp.2).comp (hGa p hp.1))
  -- `∂_z̄` in `e₂`, then restrict to `e₂ = 0`
  have hK := r43p_partial_dzbar hS₁o hH
  set S₂ : Set (E × ℂ) := (fun q : E × ℂ => (q, (0 : ℂ))) ⁻¹' S₁
  have hι₂ : ∀ q : E × ℂ, AnalyticAt ℝ (fun q : E × ℂ => (q, (0 : ℂ))) q := fun q =>
    analyticAt_id.prod analyticAt_const
  have hS₂o : IsOpen S₂ := hS₁o.preimage (continuous_id.prodMk continuous_const)
  have hK₂ : AnalyticOnNhd ℝ (fun q : E × ℂ => dzbar (fun t => ((s (G (q, t)) : ℝ) : ℂ)) 0) S₂ :=
    fun q hq => (hK _ hq).comp (f := fun q : E × ℂ => (q, (0 : ℂ))) (hι₂ q)
  -- `∂_z` in `e₁`, then restrict to `e₁ = 0`
  have hL := r43p_partial_dz hS₂o hK₂
  have hι₁ : ∀ φ : E, AnalyticAt ℝ (fun φ : E => (φ, (0 : ℂ))) φ := fun φ => analyticAt_id.prod analyticAt_const
  intro φ hφ
  have hmem : (φ, (0 : ℂ)) ∈ S₂ := by
    show ((φ, (0 : ℂ)), (0 : ℂ)) ∈ S₁
    refine ⟨hφ, ?_⟩
    show φ + (0 : ℂ) • v φ + (0 : ℂ) • w φ ∈ V
    simpa using hφ
  exact (hL _ hmem).comp (f := fun φ : E => (φ, (0 : ℂ))) (hι₁ φ)

/-- **Remark 4.3** (TT:2188–2198). The Weil–Petersson metric is real-analytic on `T(1)`.
- For `μ, ν ∈ H^{-1,1}(𝔻*)`, the map `κ ↦ g_{μν̄}(κ)` is real-analytic on `V₀`.
- `V₀` is in Hilbert coordinates: the ball of radius `√(π/3)` in `A₂(𝔻)`.
- The memoir omits the proof. -/
theorem r43p_remark_4_3 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    AnalyticOnNhd ℝ (fun φ : A2 unitDisc => gWPChart μ ν (A2toAInf φ)) (ball 0 (Real.sqrt (π / 3))) := by
  obtain ⟨v, w, hv, hw, heq⟩ := r43p_bridge hμ hν
  have hA := r43p_ddbar_analytic isOpen_ball r43p_S2_analytic hv hw
  have hc : AnalyticOnNhd ℝ (fun _ : A2 unitDisc => -(12 * π : ℂ)) (ball 0 (Real.sqrt (π / 3))) :=
    analyticOnNhd_const
  refine (hc.mul hA).congr isOpen_ball fun φ hφ => ?_
  exact (heq φ hφ).symm

/-- **Remark 4.3** (TT:2188–2198). The Weil–Petersson metric is real-analytic on `T(1)`.
- For `μ, ν ∈ H^{-1,1}(𝔻*)`, the map `κ ↦ g_{μν̄}(κ)` is real-analytic on `V₀`.
- `V₀` is in Hilbert coordinates: the ball of radius `√(π/3)` in `A₂(𝔻)`.
- The memoir omits the proof. -/
theorem remark_4_3 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    AnalyticOnNhd ℝ (fun φ : A2 unitDisc => gWPChart μ ν (A2toAInf φ)) (ball 0 (Real.sqrt (π / 3))) := by
  exact r43p_remark_4_3 hμ hν

end TakhtajanTeo
