import TakhtajanTeo.Ch1.S1_1_TeichmullerTheory

/-!
# Lemma 1.5 (TT:658): `w^μ(∞)` for harmonic `μ`  [下属2]

For harmonic `μ ∈ Ω^{-1,1}(𝔻*)₁` the plane solution `W` of `extB μ` fixing `0, 1, ∞` has `W''(0) = 0`
(`l15_W_second`), whence `l15_conj2` and `l15_fB_infty` (the bodies of `lemma_1_5` (2nd conjunct) and
`lemma_1_5_fB_infty` in `S1_2_Homogeneous`).

Route (ι-chart, compact support): `nxInvConj W` is the normalized solution of `ν = ι*(extB μ)`, which for
`μ = Λφ` is `ν^{[1]}` with `ν^{[t]}(w) = (1 - |w|²)² t² conj h(t̄ w)`, `h(w) = -½ conj φ(w̄)`.  The Laurent data
`Q_n(t) = (2πi)⁻¹ ∮_{|z|=2} G_t z⁻ⁿ` of the normalized solutions `G_t` are holomorphic in `t` (Ahlfors–Bers,
Theorem 13.8 + the uniform bound NB), satisfy the rotation law `Q_n(λ̄t) = λ^{n-1} Q_n(t)/G_t(λ)`, and equal
`-cauchyT ω_t 0` (resp. `1`) times the hydrodynamic normalization; rigidity gives `cauchyT ω_t 0 = 0` for `|t|<1`
and `eq12_1_solution_tendsto_cauchyT` passes to `t = 1`.  All helpers are prefixed `l15_`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Rigidity.**  A holomorphic `P` on the unit disc with `P(λ t) = λ P(t)` for `|λ| = 1` and `|P(t)| ≤ C|t|²`
vanishes identically. -/
theorem l15_rigid {P : ℂ → ℂ} (hP : DifferentiableOn ℂ P (ball (0 : ℂ) 1))
    (hrot : ∀ l : ℂ, ‖l‖ = 1 → ∀ t ∈ ball (0 : ℂ) 1, P (l * t) = l * P t)
    {C : ℝ} (hC : ∀ t ∈ ball (0 : ℂ) 1, ‖P t‖ ≤ C * ‖t‖ ^ 2) : ∀ t ∈ ball (0 : ℂ) 1, P t = 0 := by
  have hP0 : P 0 = 0 := by
    have := hC 0 (mem_ball_self one_pos)
    simpa using this
  have hg : DifferentiableOn ℂ (dslope P 0) (ball (0 : ℂ) 1) :=
    (differentiableOn_dslope (ball_mem_nhds _ one_pos)).2 hP
  have hgt : ∀ t : ℂ, t ≠ 0 → dslope P 0 t = P t / t := by
    intro t ht
    rw [dslope_of_ne _ ht, slope_def_field, hP0, sub_zero, sub_zero]
  have hg0 : dslope P 0 0 = 0 := by
    have hcont : ContinuousAt (dslope P 0) 0 := (hg.differentiableAt (ball_mem_nhds _ one_pos)).continuousAt
    have h1 : Tendsto (dslope P 0) (𝓝[≠] 0) (𝓝 (dslope P 0 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (dslope P 0) (𝓝[≠] 0) (𝓝 0) := by
      have hb : Tendsto (fun t : ℂ => C * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℂ => C * ‖t‖) (𝓝 0) (𝓝 (C * ‖(0 : ℂ)‖)) :=
          (continuous_const.mul continuous_norm).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with t ht1 ht2
      have ht0 : t ≠ 0 := ht1
      rw [hgt t ht0, norm_div]
      have hn : 0 < ‖t‖ := norm_pos_iff.2 ht0
      rw [div_le_iff₀ hn]
      calc ‖P t‖ ≤ C * ‖t‖ ^ 2 := hC t ht2
        _ = C * ‖t‖ * ‖t‖ := by ring
    exact tendsto_nhds_unique h1 h2
  intro t ht
  by_cases ht0 : t = 0
  · rw [ht0]; exact hP0
  have htn : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
  have hconst : ∀ s ∈ sphere (0 : ℂ) |‖t‖|, dslope P 0 s = dslope P 0 t := by
    intro s hs
    rw [abs_of_nonneg (norm_nonneg t), mem_sphere_zero_iff_norm] at hs
    have hsn : s ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hs; exact ht0 (norm_eq_zero.1 hs.symm)
    set l := s / t with hl
    have hl1 : ‖l‖ = 1 := by
      rw [hl, norm_div, hs, div_self (norm_ne_zero_iff.2 ht0)]
    have hlt : l * t = s := by rw [hl]; field_simp
    have hl0 : l ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hl1; exact zero_ne_one hl1
    rw [hgt s hsn, hgt t ht0, ← hlt, hrot l hl1 t ht]
    field_simp
  have hdc : DiffContOnCl ℂ (dslope P 0) (ball (0 : ℂ) |‖t‖|) := by
    rw [abs_of_nonneg (norm_nonneg t)]
    refine DifferentiableOn.diffContOnCl (hg.mono ?_)
    rw [closure_ball _ (norm_ne_zero_iff.2 ht0)]
    intro s hs
    rw [mem_closedBall_zero_iff] at hs
    exact mem_ball_zero_iff.2 (lt_of_le_of_lt hs htn)
  have havg := hdc.circleAverage
  have hcongr : Real.circleAverage (dslope P 0) 0 ‖t‖ = Real.circleAverage (fun _ => dslope P 0 t) 0 ‖t‖ :=
    Real.circleAverage_congr_sphere hconst
  rw [hcongr, Real.circleAverage_const, hg0] at havg
  have := hgt t ht0
  rw [havg] at this
  field_simp at this
  simpa using this.symm

theorem l15_nu_bound {h : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {t : ℂ} (ht : ‖t‖ ≤ 1) (w : ℂ) : ‖nu t w‖ ≤ k * ‖t‖ ^ 2 := by
  rw [hnu]
  split_ifs with hw
  · have hw' : conj t * w ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_conj]
      calc ‖t‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hw
    have h1 := hbd _ hw'
    have hn : ‖conj t * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖t‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
        _ = ‖w‖ := one_mul _
    have h2 : (1 - ‖w‖ ^ 2) ^ 2 ≤ (1 - ‖conj t * w‖ ^ 2) ^ 2 := by
      have a1 : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      have a2 : 1 - ‖w‖ ^ 2 ≤ 1 - ‖conj t * w‖ ^ 2 := by nlinarith [norm_nonneg (conj t * w)]
      exact pow_le_pow_left₀ a1 a2 2
    have a1 : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hc : ‖(1 - (‖w‖ : ℂ) ^ 2) ^ 2‖ = (1 - ‖w‖ ^ 2) ^ 2 := by
      rw [norm_pow]
      have : (1 - (‖w‖ : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg a1]
    rw [norm_mul, norm_mul, hc, norm_pow, Complex.norm_conj]
    calc (1 - ‖w‖ ^ 2) ^ 2 * ‖t‖ ^ 2 * ‖h (conj t * w)‖
        = ((1 - ‖w‖ ^ 2) ^ 2 * ‖h (conj t * w)‖) * ‖t‖ ^ 2 := by ring
      _ ≤ k * ‖t‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (1 - ‖w‖ ^ 2) ^ 2 * ‖h (conj t * w)‖
              ≤ (1 - ‖conj t * w‖ ^ 2) ^ 2 * ‖h (conj t * w)‖ :=
                mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
            _ ≤ k := h1
  · simp only [norm_zero]
    positivity

/-- Beltrami data of the family: measurable, `‖ν^{[t]}‖ ≤ k |t|²`, supported in the closed unit disc. -/
theorem l15_nu_beltrami {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {t : ℂ} (ht : ‖t‖ ≤ 1) :
    IsBeltramiCoeff (nu t) univ k ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → nu t w = 0) ∧ ∀ w : ℂ, ‖nu t w‖ ≤ k * ‖t‖ ^ 2 := by
  have hb := l15_nu_bound hk0 hbd hnu ht
  refine ⟨⟨?_, ?_⟩, fun w hw => ?_, hb⟩
  · rw [Measure.restrict_univ]
    have hF : ContinuousOn (fun w : ℂ => (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w))) (ball (0 : ℂ) 1) := by
      have hc : ContinuousOn (fun w : ℂ => h (conj t * w)) (ball (0 : ℂ) 1) := by
        refine hh.continuousOn.comp (continuous_const.mul continuous_id).continuousOn ?_
        intro w hw
        rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_conj]
        rw [mem_ball_zero_iff] at hw
        calc ‖t‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hw
      have h1 : Continuous fun w : ℂ => (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 := by fun_prop
      exact h1.continuousOn.mul (Complex.continuous_conj.comp_continuousOn hc)
    have hF' := hF.aestronglyMeasurable (μ := volume) measurableSet_ball
    have hind : nu t = (ball (0 : ℂ) 1).indicator (fun w : ℂ => (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w))) := by
      funext w
      rw [hnu]
      by_cases hw : ‖w‖ < 1
      · rw [if_pos hw, indicator_of_mem (mem_ball_zero_iff.2 hw)]
      · rw [if_neg hw, indicator_of_notMem (fun hm => hw (mem_ball_zero_iff.1 hm))]
    rw [hind]
    exact (aestronglyMeasurable_indicator_iff measurableSet_ball).2 hF'
  · refine Filter.Eventually.of_forall fun w => ?_
    refine (hb w).trans ?_
    calc k * ‖t‖ ^ 2 ≤ k * 1 := mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg t]) hk0
      _ = k := mul_one k
  · rw [hnu, if_neg (not_lt.2 hw)]

/-- Pointwise holomorphy in `t` on `|t| < 1`. -/
theorem l15_nu_hol {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    (w : ℂ) : DifferentiableOn ℂ (fun t => nu t w) (ball (0 : ℂ) 1) := by
  by_cases hw : ‖w‖ < 1
  · have heq : (fun t => nu t w) = fun t => (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) := by
      funext t; rw [hnu, if_pos hw]
    rw [heq]
    intro t ht
    have ht' : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
    have hmem : conj (t * conj w) ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj, norm_mul, Complex.norm_conj]
      calc ‖t‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hw
    have hd : DifferentiableAt ℂ h (conj (t * conj w)) :=
      hh.differentiableAt (isOpen_ball.mem_nhds hmem)
    have hcc := hd.conj_conj
    have hcc' : DifferentiableAt ℂ (conj ∘ h ∘ conj) (t * conj w) := by
      simpa using hcc
    have hcomp : DifferentiableAt ℂ (fun t : ℂ => (conj ∘ h ∘ conj) (t * conj w)) t :=
      hcc'.comp (f := fun t : ℂ => t * conj w) t (differentiableAt_id.mul_const _)
    have hfun : (fun t : ℂ => conj (h (conj t * w))) = fun t : ℂ => (conj ∘ h ∘ conj) (t * conj w) := by
      funext t
      simp [Function.comp]
    have hd2 : DifferentiableAt ℂ (fun t : ℂ => (1 - (‖w‖ : ℂ) ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w))) t := by
      have := ((differentiableAt_const ((1 - (‖w‖ : ℂ) ^ 2) ^ 2)).mul ((differentiableAt_id.pow 2))).mul hcomp
      refine this.congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun t' => by simp [Function.comp]
    exact hd2.differentiableWithinAt
  · have heq : (fun t => nu t w) = fun _ => (0 : ℂ) := by
      funext t; rw [hnu, if_neg hw]
    rw [heq]
    exact differentiableOn_const _

/-- Rotation covariance of the coefficient: `ν^{[λ̄ t]}(w) = ν^{[t]}(λ w) · λ̄/λ`  (`|λ| = 1`). -/
theorem l15_nu_rot {h : ℂ → ℂ} {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {l : ℂ} (hl : ‖l‖ = 1) (t w : ℂ) : nu (conj l * t) w = nu t (l * w) * (conj l / l) := by
  have hlw : ‖l * w‖ = ‖w‖ := by rw [norm_mul, hl, one_mul]
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl; exact zero_ne_one hl
  have hll : l * conj l = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hl]; simp
  rw [hnu, hnu, hlw]
  split_ifs with hw
  · have hX : conj (conj l * t) * w = conj t * (l * w) := by
      rw [map_mul, Complex.conj_conj]; ring
    rw [hX]
    have hc : conj l / l = conj l * conj l := by
      field_simp
      linear_combination (-(conj l)) * hll
    rw [hc]
    ring
  · simp

/-- **The `r → 1` continuity lemma** (the only place where `t = 1` is reached).  For real `r_n ↑ 1` and the
hydrodynamic solutions `ω_n` of `ν^{[r_n]}` and `ω` of `ν^{[1]}`, `cauchyT ω_n 0 → cauchyT ω 0`.
(Proof: `ν^{[r_n]} → ν^{[1]}` pointwise on `𝔻`, common bound `k`, common support `closedBall 0 1`;
`eq12_1_solution_tendsto_cauchyT` gives uniform convergence of `cauchyT ω_n`.) -/
theorem l15_limit {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1) (hr : Tendsto r atTop (𝓝 1))
    {ωn : ℕ → ℂ → ℂ} (hωn : ∀ n, MemLp (ωn n) (ENNReal.ofReal p))
    (hsn : ∀ n, ωn n =ᵐ[volume] fun z => nu (r n) z * hilbertH (ωn n) z + nu (r n) z)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z) :
    Tendsto (fun n => cauchyT (ωn n) 0) atTop (𝓝 (cauchyT ω 0)) := by
  have hbn : ∀ n, IsBeltramiCoeff (nu (r n)) univ k ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → nu (r n) w = 0) := fun n => by
    have := l15_nu_beltrami hh hk0 hk1 hbd hnu (t := ((r n : ℝ) : ℂ))
      (by rw [Complex.norm_real, Real.norm_of_nonneg (hr0 n)]; exact (hr1 n).le)
    exact ⟨this.1, this.2.1⟩
  have hb1 : IsBeltramiCoeff (nu 1) univ k ∧ (∀ w : ℂ, 1 ≤ ‖w‖ → nu 1 w = 0) := by
    have := l15_nu_beltrami hh hk0 hk1 hbd hnu (t := 1) (by simp)
    exact ⟨this.1, this.2.1⟩
  have hlim : ∀ᵐ z, Tendsto (fun n => nu (r n) z) atTop (𝓝 (nu 1 z)) := by
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : ‖z‖ < 1
    · have hz' : z ∈ unitDisc := mem_ball_zero_iff.2 hz
      have hmem : ∀ s : ℂ, ‖s‖ ≤ 1 → s * z ∈ unitDisc := fun s hs => by
        rw [unitDisc, mem_ball_zero_iff, norm_mul]
        calc ‖s‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hz
      have hcont : ContinuousAt (fun s : ℂ => (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * s ^ 2 * conj (h (conj s * z))) 1 := by
        have h1 : ContinuousAt (fun s : ℂ => h (conj s * z)) 1 := by
          have hc : ContinuousAt h (conj (1 : ℂ) * z) := by
            have : conj (1 : ℂ) * z ∈ unitDisc := by simpa using hz'
            exact (hh.differentiableAt (isOpen_ball.mem_nhds this)).continuousAt
          exact hc.comp (f := fun s : ℂ => conj s * z) ((Complex.continuous_conj.mul continuous_const).continuousAt)
        exact (continuousAt_const.mul (continuousAt_id.pow 2)).mul (Complex.continuous_conj.continuousAt.comp h1)
      have hr' : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 1) := by
        have := (Complex.continuous_ofReal.tendsto 1).comp hr
        rw [Complex.ofReal_one] at this
        exact this
      have := hcont.tendsto.comp hr'
      refine (this.congr fun n => ?_).trans ?_
      · simp only [Function.comp, hnu, if_pos hz]
      · rw [hnu, if_pos hz]
    · have h0 : ∀ t, nu t z = 0 := fun t => by rw [hnu, if_neg hz]
      simp only [h0]
      exact tendsto_const_nhds
  have hsupp' : ∀ n z, 1 < ‖z‖ → nu (r n) z = 0 := fun n z hz => (hbn n).2 z hz.le
  have hu := eq12_1_solution_tendsto_cauchyT (μn := fun n => nu (r n)) (μ := nu 1) (k := k) (p := p) (R := 1)
    hk0 hp hkp (fun n => (hbn n).1) hb1.1 hsupp' (fun z hz => hb1.2 z hz.le) hlim hωn hsn hω hs
  exact hu.tendsto_at 0

theorem l15_lp_bound {μ ω : ℂ → ℂ} {κ p : ℝ} (hκ : 0 ≤ κ) (hp : 2 < p)
    (hμ : IsBeltramiCoeff μ univ κ) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) (hν : MemLp μ (ENNReal.ofReal p)) :
    eLpNorm ω (ENNReal.ofReal p) volume ≤
      eLpNorm μ (ENNReal.ofReal p) volume +
        ENNReal.ofReal (κ * hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ) < p := by linarith
  have hμbd : ∀ᵐ z ∂volume, ‖μ z‖ ≤ κ := by simpa using hμ.2
  have hmeas : AEStronglyMeasurable μ volume := by simpa using hμ.1
  have hkenorm : ‖(κ : ℝ)‖ₑ = ENNReal.ofReal κ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hκ]
  have hHm : MemLp (hilbertH ω) (ENNReal.ofReal p) := hilbertH_memLp hp1 hω
  have h1 : eLpNorm (fun z => μ z * hilbertH ω z) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (κ * hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) volume := by
    calc eLpNorm (fun z => μ z * hilbertH ω z) (ENNReal.ofReal p) volume
        ≤ eLpNorm (κ • hilbertH ω) (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono_ae ?_ ?_
          · exact hmeas.mul hHm.aestronglyMeasurable
          filter_upwards [hμbd] with z hz
          simp only [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hκ]
          exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ENNReal.ofReal κ * eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume := by
          rw [eLpNorm_const_smul, hkenorm]
      _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal (hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) volume) := by
          gcongr
          exact eq11_16_eLpNorm hp1 hω
      _ = ENNReal.ofReal (κ * hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hκ]
  calc eLpNorm ω (ENNReal.ofReal p) volume
      = eLpNorm (fun z => μ z * hilbertH ω z + μ z) (ENNReal.ofReal p) volume := eLpNorm_congr_ae hsol
    _ ≤ eLpNorm (fun z => μ z * hilbertH ω z) (ENNReal.ofReal p) volume + eLpNorm μ (ENNReal.ofReal p) volume := by
        refine eLpNorm_add_le (f := fun z => μ z * hilbertH ω z) (g := μ) ?_
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
    _ ≤ ENNReal.ofReal (κ * hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) volume +
          eLpNorm μ (ENNReal.ofReal p) volume := add_le_add_left h1 _
    _ = _ := add_comm _ _

theorem l15_nu_Lp {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {t : ℂ} (ht : ‖t‖ ≤ 1) {p : ℝ} (hp0 : 0 < p) :
    MemLp (nu t) (ENNReal.ofReal p) ∧ eLpNorm (nu t) (ENNReal.ofReal p) volume ≤
      volume (closedBall (0 : ℂ) 1) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal (k * ‖t‖ ^ 2) := by
  obtain ⟨hbel, hsupp, hbd'⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
  have hκ : 0 ≤ k * ‖t‖ ^ 2 := by positivity
  have hνind : nu t = (closedBall (0 : ℂ) 1).indicator (nu t) := by
    funext w
    by_cases hw : w ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw, hsupp w]
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
  have hmeasν : AEStronglyMeasurable (nu t) volume := by simpa using hbel.1
  have hνB : eLpNorm (nu t) (ENNReal.ofReal p) volume ≤
      volume (closedBall (0 : ℂ) 1) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal (k * ‖t‖ ^ 2) := by
    rw [hνind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict (closedBall (0 : ℂ) 1)) (p := ENNReal.ofReal p)
      (f := nu t) (C := k * ‖t‖ ^ 2) hmeasν.restrict (Filter.Eventually.of_forall hbd')
    rwa [Measure.restrict_apply_univ] at this
  have hvolfin : volume (closedBall (0 : ℂ) 1) < ⊤ := measure_closedBall_lt_top
  refine ⟨?_, hνB⟩
  refine lt_of_le_of_lt hνB ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hvolfin.ne) ENNReal.ofReal_lt_top

/-- **Smallness near `t = 0`.**  `‖cauchyT ω 0‖ ≤ C ‖t‖²` for the hydrodynamic solution of `ν^{[t]}`
(fixed-point bound `‖ω‖_p ≤ ‖ν‖_p/(1 - kΛ_p)` and Lemma 11.1). -/
theorem l15_small {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1) :
    ∃ C : ℝ, ∀ t : ℂ, ‖t‖ ≤ 1 → ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) →
      (ω =ᵐ[volume] fun z => nu t z * hilbertH ω z + nu t z) → ‖cauchyT ω 0‖ ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp (R := 1) one_pos
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  set Λ := hilbertNorm p with hΛ
  have hΛ0 : 0 ≤ Λ := hilbertNorm_nonneg p
  have hden : 0 < 1 - k * Λ := by linarith
  set Vol : ℝ := (volume (closedBall (0 : ℂ) 1)).toReal ^ (1 / p) with hVol
  have hVol0 : 0 ≤ Vol := by positivity
  refine ⟨max M₁ 0 * (k * Vol / (1 - k * Λ)), fun t ht ω hω hsol => ?_⟩
  obtain ⟨hbel, hsupp, hbd'⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
  have ht2 : ‖t‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg t]
  have hκ : 0 ≤ k * ‖t‖ ^ 2 := by positivity
  -- ν ∈ L_p with a bound
  have hνind : nu t = (closedBall (0 : ℂ) 1).indicator (nu t) := by
    funext w
    by_cases hw : w ∈ closedBall (0 : ℂ) 1
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw, hsupp w]
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
  have hmeasν : AEStronglyMeasurable (nu t) volume := by simpa using hbel.1
  have hνB : eLpNorm (nu t) (ENNReal.ofReal p) volume ≤
      volume (closedBall (0 : ℂ) 1) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal (k * ‖t‖ ^ 2) := by
    rw [hνind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict (closedBall (0 : ℂ) 1)) (p := ENNReal.ofReal p)
      (f := nu t) (C := k * ‖t‖ ^ 2) hmeasν.restrict (Filter.Eventually.of_forall hbd')
    rwa [Measure.restrict_apply_univ] at this
  have hvolfin : volume (closedBall (0 : ℂ) 1) < ⊤ := measure_closedBall_lt_top
  have hνmem : MemLp (nu t) (ENNReal.ofReal p) := by
    refine lt_of_le_of_lt hνB ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hvolfin.ne) ENNReal.ofReal_lt_top
  have hbound := l15_lp_bound hk0 hp hbel hω hsol hνmem
  -- real-number bookkeeping
  have hωfin : eLpNorm ω (ENNReal.ofReal p) volume ≠ ⊤ := hω.eLpNorm_ne_top
  have hνfin : eLpNorm (nu t) (ENNReal.ofReal p) volume ≠ ⊤ := hνmem.eLpNorm_ne_top
  set E := (eLpNorm ω (ENNReal.ofReal p) volume).toReal with hE
  set B := (eLpNorm (nu t) (ENNReal.ofReal p) volume).toReal with hB
  have hEB : E ≤ B + k * Λ * E := by
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hνfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin⟩) hbound
    rwa [ENNReal.toReal_add hνfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  have hBle : B ≤ Vol * (k * ‖t‖ ^ 2) := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hvolfin.ne)
      ENNReal.ofReal_ne_top) hνB
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ, ← ENNReal.toReal_rpow] at h1
    have hpt : (ENNReal.ofReal p).toReal⁻¹ = 1 / p := by
      rw [ENNReal.toReal_ofReal hp0.le, one_div]
    rw [hpt] at h1
    exact h1
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hEle : E ≤ Vol * (k * ‖t‖ ^ 2) / (1 - k * Λ) := by
    rw [le_div_iff₀ hden]
    nlinarith
  -- Lemma 11.1 on the representative supported in the closed disc
  set ωR : ℂ → ℂ := (closedBall (0 : ℂ) 1).indicator ω with hωR
  have hωas : ω =ᵐ[volume] ωR := t2_omega_ae_eq_indicator (fun z hz => hsupp z hz.le) hsol
  have hωRmem : MemLp ωR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
  have hωRsupp : ∀ z : ℂ, 1 < ‖z‖ → ωR z = 0 := fun z hz =>
    indicator_of_notMem (by simpa [mem_closedBall_zero_iff, not_le] using hz) _
  have hcT : cauchyT ω = cauchyT ωR := cauchyT_congr_ae hωas
  have hnorm : eLpNorm ωR (ENNReal.ofReal p) volume = eLpNorm ω (ENNReal.ofReal p) volume :=
    (eLpNorm_congr_ae hωas).symm
  have h11 := hM₁ ωR hωRmem hωRsupp 0
  rw [hcT]
  rw [hnorm] at h11
  calc ‖cauchyT ωR 0‖ ≤ M₁ * E := h11
    _ ≤ max M₁ 0 * E := mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
    _ ≤ max M₁ 0 * (Vol * (k * ‖t‖ ^ 2) / (1 - k * Λ)) := mul_le_mul_of_nonneg_left hEle (le_max_right _ _)
    _ = max M₁ 0 * (k * Vol / (1 - k * Λ)) * ‖t‖ ^ 2 := by ring

theorem l15_rot_normalized {ν G : ℂ → ℂ} {l : ℂ} (hl : ‖l‖ = 1) (hG : IsNormalizedSolution G ν) :
    IsNormalizedSolution (fun z => (G l)⁻¹ * G (l * z)) (fun z => ν (l * z) * (conj l / l)) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hG
  have hl0 : l ≠ 0 := by
    intro h0'; rw [h0', norm_zero] at hl; exact zero_ne_one hl
  have hGl : G l ≠ 0 := by
    intro h
    have hinj := hK.2.2.1.2.1
    exact hl0 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
  have hγ : (G l)⁻¹ ≠ 0 := inv_ne_zero hGl
  obtain ⟨hq, hsurj⟩ := b4_rat_affine_comp hK hs (α := l) (γ := (G l)⁻¹) 0 0 hl0 hγ
  have hfun : (fun z => (G l)⁻¹ * G (l * z + 0) + 0) = fun z => (G l)⁻¹ * G (l * z) := by
    funext z; simp
  rw [hfun] at hq hsurj
  refine ⟨⟨K, hq⟩, hsurj, by simp [h0], by simp [hGl], ?_⟩
  have hρ : IsConformalOnto (fun z => l * z + 0) univ univ := b4_rat_affine_conformal 0 hl0
  have hdiff : ∀ᵐ u ∂(volume.restrict (univ : Set ℂ)), DifferentiableAt ℝ G u :=
    thm9_3_differentiable_ae hK
  have hd' : ∀ᵐ u ∂(volume.restrict (univ : Set ℂ)), complexDilatation G u = ν u := by
    rwa [Measure.restrict_univ]
  have hP : ∀ᵐ u ∂(volume.restrict (univ : Set ℂ)), DifferentiableAt ℝ G u ∧ complexDilatation G u = ν u := by
    filter_upwards [hdiff, hd'] with u h1 h2 using ⟨h1, h2⟩
  have hT := t1_ae_transport isOpen_univ isOpen_univ hρ hP
  rw [Measure.restrict_univ] at hT
  filter_upwards [hT] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [add_zero] at hz1 hz2
  have hρd : DifferentiableAt ℂ (fun z : ℂ => l * z) z := by fun_prop
  have hρ' : deriv (fun z : ℂ => l * z) z = l := by simp
  have hc1 : DifferentiableAt ℝ (G ∘ fun z : ℂ => l * z) z := hz1.comp z (hρd.restrictScalars ℝ)
  have hφ : DifferentiableAt ℂ (fun w : ℂ => (G l)⁻¹ * w) ((G ∘ fun z : ℂ => l * z) z) := by fun_prop
  have hφ' : deriv (fun w : ℂ => (G l)⁻¹ * w) ((G ∘ fun z : ℂ => l * z) z) ≠ 0 := by
    simpa using hγ
  have e1 := complexDilatation_comp_conformal_left hc1 hφ hφ'
  have e2 := complexDilatation_comp_conformal_right (g := G) hρd (by rw [hρ']; exact hl0) hz1
  have hcomp : (fun z => (G l)⁻¹ * G (l * z)) = (fun w : ℂ => (G l)⁻¹ * w) ∘ (G ∘ fun z : ℂ => l * z) := rfl
  rw [hcomp, e1, e2, hρ', hz2]

/-- Rotation covariance of the normalized solutions (Theorem 13.5 uniqueness). -/
theorem l15_G_rot {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {G : ℂ → ℂ → ℂ} (hG : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t))
    {l : ℂ} (hl : ‖l‖ = 1) {t : ℂ} (ht : ‖t‖ < 1) (z : ℂ) :
    G (conj l * t) z = G t (l * z) / G t l := by
  have ht' : t ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 ht
  have hct : conj l * t ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_conj, hl, one_mul]; exact ht
  have h1 := l15_rot_normalized hl (hG t ht')
  have hfun : (fun z => nu t (l * z) * (conj l / l)) = nu (conj l * t) := by
    funext w; rw [l15_nu_rot hnu hl]
  rw [hfun] at h1
  have h2 := thm13_5_uniqueness_plane (hG _ hct).1 h1.1 (hG _ hct).2.1 h1.2.1 (by
    filter_upwards [(hG _ hct).2.2.2.2, h1.2.2.2.2] with w a b using by rw [a, b])
    (hG _ hct).2.2.1 (hG _ hct).2.2.2.1 h1.2.2.1 h1.2.2.2.1
  rw [congrFun h2 z, div_eq_inv_mul]

theorem l15_G_kqc {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {t : ℂ} (ht : ‖t‖ ≤ 1) {g : ℂ → ℂ} (hg : IsNormalizedSolution g (nu t)) :
    IsKQCNormalizedPlane g ((1 + k) / (1 - k)) := by
  obtain ⟨hb, -, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
  obtain ⟨f, hf, hfK, huniq⟩ := thm13_7_normalized_existence hk0 hk1 hb
  have hgf : g = f := huniq g hg
  subst hgf
  exact ⟨hfK, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩

/-- Uniform local bound `‖G_t(z)‖ ≤ M` for `‖z‖ ≤ 2` (`t203_lim_nb_upper`, `K = (1+k)/(1-k)`). -/
theorem l15_G_bound {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {G : ℂ → ℂ → ℂ} (hG : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t)) :
    ∃ M : ℝ, ∀ t ∈ ball (0 : ℂ) 1, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖G t z‖ ≤ M := by
  refine ⟨lambdaInv ((1 + k) / (1 - k) * quadLambda 2), fun t ht z hz => ?_⟩
  exact t203_lim_nb_upper (l15_G_kqc hh hk0 hk1 hbd hnu (mem_ball_zero_iff.1 ht).le (hG t ht))
    (by norm_num) hz

theorem l15_circle_rot (F : ℂ → ℂ) {l : ℂ} (hl : ‖l‖ = 1) (n : ℕ) :
    ∮ z in C(0, 2), F (l * z) / z ^ n = l ^ n * l⁻¹ * ∮ z in C(0, 2), F z / z ^ n := by
  obtain ⟨α, hα⟩ := (Complex.norm_eq_one_iff l).1 hl
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl; exact zero_ne_one hl
  have hc : ∀ θ : ℝ, circleMap 0 2 (θ + α) = l * circleMap 0 2 θ := by
    intro θ
    simp only [circleMap, zero_add, ← hα]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  set B : ℝ → ℂ := fun φ => (circleMap 0 2 φ * I) • (F (circleMap 0 2 φ) / circleMap 0 2 φ ^ n) with hB
  have hBper : Function.Periodic B (2 * π) := by
    intro φ
    simp only [hB, circleMap, zero_add]
    rw [show ((φ + 2 * π : ℝ) : ℂ) * I = (φ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hA : ∀ θ : ℝ, (circleMap 0 2 θ * I) • (F (l * circleMap 0 2 θ) / circleMap 0 2 θ ^ n) =
      l ^ n * l⁻¹ * B (θ + α) := by
    intro θ
    simp only [hB, hc θ, smul_eq_mul]
    have hcn : circleMap 0 2 θ ≠ 0 := circleMap_ne_center (by norm_num)
    field_simp
    rw [mul_pow]
    ring
  unfold circleIntegral
  simp only [deriv_circleMap]
  simp_rw [hA]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_comp_add_right B α]
  have := hBper.intervalIntegral_add_eq α 0
  simp only [zero_add] at this
  rw [show 2 * π + α = α + 2 * π by ring, zero_add]
  exact this

/-- Rotation behaviour of `Q_n`:  `Q_n(λ̄ t) = λ^{n-1} Q_n(t) / G_t(λ)`  (from `l15_G_rot` and the substitution
`z ↦ λ z` on the circle `|z| = 2`). -/
theorem l15_QS_rot {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {G : ℂ → ℂ → ℂ} (hG : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t)) (n : ℕ) (hn : 1 ≤ n)
    {l : ℂ} (hl : ‖l‖ = 1) {t : ℂ} (ht : ‖t‖ < 1) :
    (2 * π * I)⁻¹ * ∮ z in C(0, 2), G (conj l * t) z / z ^ n =
      l ^ (n - 1) * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), G t z / z ^ n) / G t l := by
  have hl0 : l ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hl; exact zero_ne_one hl
  have hfun : (fun z => G (conj l * t) z / z ^ n) = fun z => (G t l)⁻¹ * (G t (l * z) / z ^ n) := by
    funext z
    rw [l15_G_rot hh hk0 hk1 hbd hnu hG hl ht z]
    ring
  rw [hfun, circleIntegral.integral_const_mul, l15_circle_rot (G t) hl n]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : l ^ (m + 1) * l⁻¹ = l ^ m := by
    rw [pow_succ]; field_simp
  rw [this]
  ring

theorem l15_param_circle {Gf : ℂ → ℂ → ℂ} {M : ℝ} (n : ℕ)
    (hcont : ∀ t ∈ ball (0 : ℂ) 1, Continuous (Gf t))
    (hdiff : ∀ z : ℂ, DifferentiableOn ℂ (fun t => Gf t z) (ball (0 : ℂ) 1))
    (hM : ∀ t ∈ ball (0 : ℂ) 1, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖Gf t z‖ ≤ M) :
    DifferentiableOn ℂ (fun t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), Gf t z / z ^ n) (ball (0 : ℂ) 1) := by
  intro t0 ht0
  have ht0n : ‖t0‖ < 1 := mem_ball_zero_iff.1 ht0
  refine DifferentiableAt.differentiableWithinAt ?_
  set ρ : ℝ := (1 - ‖t0‖) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hsub : ∀ x ∈ ball t0 ρ, closedBall x ρ ⊆ ball (0 : ℂ) 1 := by
    intro x hx w hw
    rw [mem_ball_zero_iff]
    have h1 : ‖x - t0‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hx
    have h2 : ‖w - x‖ ≤ ρ := by rwa [mem_closedBall, dist_eq_norm] at hw
    have : ‖w‖ ≤ ‖w - x‖ + ‖x - t0‖ + ‖t0‖ := by
      calc ‖w‖ = ‖(w - x) + (x - t0) + t0‖ := by congr 1; ring
        _ ≤ ‖(w - x) + (x - t0)‖ + ‖t0‖ := norm_add_le _ _
        _ ≤ ‖w - x‖ + ‖x - t0‖ + ‖t0‖ := by gcongr; exact norm_add_le _ _
    linarith
  have hxball : ∀ x ∈ ball t0 ρ, x ∈ ball (0 : ℂ) 1 := fun x hx =>
    hsub x hx (mem_closedBall_self hρ0.le)
  have hder : ∀ x ∈ ball t0 ρ, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖deriv (fun t => Gf t z) x‖ ≤ M / ρ := by
    intro x hx z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 ?_
      (fun w hw => hM w (hsub x hx (sphere_subset_closedBall hw)) z hz)
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hρ0.ne']
    exact (hdiff z).mono (hsub x hx)
  have hcn : ∀ θ : ℝ, circleMap 0 2 θ ≠ 0 := fun θ => circleMap_ne_center (by norm_num)
  have hcn' : ∀ θ : ℝ, ‖circleMap 0 2 θ‖ = 2 := fun θ => by simp [circleMap]
  set F : ℂ → ℝ → ℂ := fun t θ =>
    (circleMap 0 2 θ * I) • (Gf t (circleMap 0 2 θ) / circleMap 0 2 θ ^ n) with hF
  set F' : ℂ → ℝ → ℂ := fun t θ =>
    (circleMap 0 2 θ * I) • (deriv (fun s => Gf s (circleMap 0 2 θ)) t / circleMap 0 2 θ ^ n) with hF'
  have hFc : ∀ t ∈ ball (0 : ℂ) 1, Continuous (F t) := by
    intro t ht
    have h1 : Continuous fun θ : ℝ => Gf t (circleMap 0 2 θ) := (hcont t ht).comp (continuous_circleMap 0 2)
    refine Continuous.smul ((continuous_circleMap 0 2).mul continuous_const) (Continuous.div h1 ((continuous_circleMap 0 2).pow n) fun θ => pow_ne_zero n (hcn θ))
  have hmeas' : AEStronglyMeasurable (F' t0) (volume.restrict (Set.uIoc 0 (2 * π))) := by
    -- `F' t0` is a pointwise limit of continuous difference quotients
    set h : ℕ → ℂ := fun m => ((ρ / 2) / ((m : ℝ) + 1) : ℝ) with hh
    have hh0 : ∀ m, h m ≠ 0 := fun m => by
      simp only [hh]; exact_mod_cast (div_pos (half_pos hρ0) (by positivity)).ne'
    have hhn : ∀ m, ‖h m‖ ≤ ρ / 2 := fun m => by
      simp only [hh, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos (half_pos hρ0) (by positivity))]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hhlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hh0⟩
      have : Tendsto (fun m : ℕ => (ρ / 2) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ρ / 2)
        simpa [div_eq_mul_inv, mul_comm] using this
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h2
      exact h2
    have hq : ∀ m, AEStronglyMeasurable (fun θ : ℝ => (circleMap 0 2 θ * I) •
        ((h m)⁻¹ * (Gf (t0 + h m) (circleMap 0 2 θ) - Gf t0 (circleMap 0 2 θ)) / circleMap 0 2 θ ^ n))
        (volume.restrict (Set.uIoc 0 (2 * π))) := by
      intro m
      have hmem : t0 + h m ∈ ball (0 : ℂ) 1 := by
        refine hxball _ ?_
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact lt_of_le_of_lt (hhn m) (half_lt_self hρ0)
      refine Continuous.aestronglyMeasurable ?_
      have h1 : Continuous fun θ : ℝ => Gf (t0 + h m) (circleMap 0 2 θ) := (hcont _ hmem).comp (continuous_circleMap 0 2)
      have h2 : Continuous fun θ : ℝ => Gf t0 (circleMap 0 2 θ) := (hcont _ ht0).comp (continuous_circleMap 0 2)
      refine Continuous.smul ((continuous_circleMap 0 2).mul continuous_const)
        (Continuous.div ((continuous_const.mul (h1.sub h2))) ((continuous_circleMap 0 2).pow n)
        fun θ => pow_ne_zero n (hcn θ))
    refine aestronglyMeasurable_of_tendsto_ae atTop hq (Filter.Eventually.of_forall fun θ => ?_)
    have hd : HasDerivAt (fun s => Gf s (circleMap 0 2 θ)) (deriv (fun s => Gf s (circleMap 0 2 θ)) t0) t0 :=
      ((hdiff _).differentiableAt (isOpen_ball.mem_nhds ht0)).hasDerivAt
    have hs := hasDerivAt_iff_tendsto_slope_zero.1 hd
    have hs' := hs.comp hhlim
    have hlim := (hs'.div_const (circleMap 0 2 θ ^ n)).const_smul (circleMap 0 2 θ * I)
    refine hlim.congr fun m => ?_
    simp only [Function.comp, smul_eq_mul]
  have hFint : IntervalIntegrable (F t0) volume 0 (2 * π) := (hFc t0 ht0).intervalIntegrable _ _
  have hbound : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * π) → ∀ x ∈ ball t0 ρ, ‖F' x θ‖ ≤ 2 * (M / ρ) / 2 ^ n := by
    refine Filter.Eventually.of_forall fun θ _ x hx => ?_
    have hb := hder x hx (circleMap 0 2 θ) (by rw [hcn' θ])
    simp only [hF', smul_eq_mul, norm_mul, norm_div, norm_pow, hcn', Complex.norm_I, mul_one]
    calc 2 * (‖deriv (fun s => Gf s (circleMap 0 2 θ)) x‖ / 2 ^ n) = 2 * ‖deriv (fun s => Gf s (circleMap 0 2 θ)) x‖ / 2 ^ n := by ring
      _ ≤ 2 * (M / ρ) / 2 ^ n := by gcongr
  have hdiffθ : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * π) → ∀ x ∈ ball t0 ρ, HasDerivAt (fun x => F x θ) (F' x θ) x := by
    refine Filter.Eventually.of_forall fun θ _ x hx => ?_
    have hd : HasDerivAt (fun s => Gf s (circleMap 0 2 θ)) (deriv (fun s => Gf s (circleMap 0 2 θ)) x) x :=
      ((hdiff _).differentiableAt (isOpen_ball.mem_nhds (hxball x hx))).hasDerivAt
    exact (hd.div_const (circleMap 0 2 θ ^ n)).const_smul (circleMap 0 2 θ * I)
  have hFmeas : ∀ᶠ x in 𝓝 t0, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc 0 (2 * π))) := by
    filter_upwards [isOpen_ball.mem_nhds ht0] with x hx using (hFc x hx).aestronglyMeasurable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := 0) (b := 2 * π)
    (μ := volume) (F := F) (F' := F') (x₀ := t0) (s := ball t0 ρ) (bound := fun _ => 2 * (M / ρ) / 2 ^ n)
    (ball_mem_nhds t0 hρ0) hFmeas hFint hmeas' hbound intervalIntegrable_const hdiffθ
  have hfun : (fun t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), Gf t z / z ^ n) =
      fun t => (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F t θ := by
    funext t
    simp only [circleIntegral, deriv_circleMap, hF]
  rw [hfun]
  exact (key.2.const_mul _).differentiableAt

/-- **Holomorphy of the Laurent data.**  `Q_n(t) = (2πi)⁻¹ ∮_{|z|=2} G_t(z) z^{-n} dz` is holomorphic on `|t|<1`
(Theorem 13.8 gives `t ↦ G_t(z)` holomorphic; `l15_G_bound` + joint measurability + Cauchy–Fubini). -/
theorem l15_QS_hol {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {G : ℂ → ℂ → ℂ} (hG : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t)) (n : ℕ) :
    DifferentiableOn ℂ (fun t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), G t z / z ^ n) (ball (0 : ℂ) 1) := by
  obtain ⟨M, hM⟩ := l15_G_bound hh hk0 hk1 hbd hnu hG
  refine l15_param_circle n (fun t ht => ?_)
    (thm13_8_ahlfors_bers_holomorphic isOpen_ball hk0 hk1
      (fun t ht => (l15_nu_beltrami hh hk0 hk1 hbd hnu (mem_ball_zero_iff.1 ht).le).1)
      (l15_nu_hol hh hnu) hG) hM
  obtain ⟨⟨K, hK⟩, -⟩ := hG t ht
  exact continuousOn_univ.mp hK.2.2.1.1

theorem l15_hydro_data {nu : ℂ → ℂ} {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hnu : IsBeltramiCoeff nu univ k) (hsupp : ∀ w : ℂ, 1 ≤ ‖w‖ → nu w = 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => nu z * hilbertH ω z + nu z) :
    IsKQC (fun z => z + cauchyT ω z) univ ((1 + k) / (1 - k)) ∧
      (fun z => z + cauchyT ω z) '' univ = univ ∧
      (∀ᵐ z, complexDilatation (fun z => z + cauchyT ω z) z = nu z) := by
  have hμ : IsCompactBeltramiCoeff nu k := ⟨hnu, 1, fun z hz => hsupp z hz.le⟩
  obtain ⟨hkqc, e', he'⟩ := thm12_1_isKQC hk0 hk1 hμ hp hkp hω hsol
  have himg : (fun z => z + cauchyT ω z) '' univ = univ := by
    rw [← he', Set.image_univ]; exact e'.surjective.range_eq
  refine ⟨hkqc, himg, ?_⟩
  have hgen : IsGenHomeoSolution (fun z => z + cauchyT ω z) nu univ (ENNReal.ofReal p) := by
    refine ⟨hkqc.2.2.1, ?_⟩
    obtain ⟨R', hR', hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → nu z = 0 :=
      ⟨1, one_pos, fun z hz => hsupp z hz.le⟩
    set omR : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator ω with homRdef
    have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hRR' hsol
    have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
    have hHT : hilbertH ω = hilbertH omR := hilbertH_congr_ae homs
    have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
    have homRbdd : Bornology.IsBounded (Function.support omR) := t3_isBounded_support_indicator
    obtain ⟨hgp, heqbar, heqz⟩ := thm11_1 hp homRmem homRbdd
    have hgp' := t3_hasGenPartials_add_id hgp
    have hpteq : ∀ z : ℂ, genDzbar (fun z => 1 + (hilbertH omR z + omR z))
        (fun z => I + I * (hilbertH omR z - omR z)) z = omR z := by
      intro z
      have h1 := heqbar z
      rw [genDzbar] at h1 ⊢
      linear_combination h1 + (1 / 2 : ℂ) * I_sq
    have hpteq2 : ∀ z : ℂ, genDz (fun z => 1 + (hilbertH omR z + omR z))
        (fun z => I + I * (hilbertH omR z - omR z)) z = 1 + hilbertH omR z := by
      intro z
      have h2 := heqz z
      rw [genDz] at h2 ⊢
      linear_combination h2 - (1 / 2 : ℂ) * I_sq
    refine ⟨fun z => 1 + (hilbertH omR z + omR z), fun z => I + I * (hilbertH omR z - omR z),
      ?_, ?_⟩
    · rw [show (fun z => z + cauchyT ω z) = (fun z => z + cauchyT omR z) from
        by funext z; rw [hcT]]
      exact hgp'
    · rw [Measure.restrict_univ]
      filter_upwards [hsol, homs] with z hsolz hz
      rw [hpteq z, hpteq2 z, ← hz, hsolz, congrFun hHT z]
      ring
  exact t2_complexDilatation_ae hkqc hp hgen

theorem l15_cauchyT_outside {p : ℝ} (hp : 2 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hω0 : ω =ᵐ[volume] (closedBall (0 : ℂ) 1).indicator ω) :
    DifferentiableOn ℂ (cauchyT ω) {z : ℂ | 1 < ‖z‖} ∧
      ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖cauchyT ω z‖ ≤ C / ‖z‖ := by
  set D : Set ℂ := closedBall (0 : ℂ) 1 with hD
  have hbdd : Bornology.IsBounded D := isBounded_closedBall
  have hωD : MemLp ω (ENNReal.ofReal p) (volume.restrict D) := hω.restrict D
  obtain ⟨hdiff, C, R, hCR⟩ := eq11_8 hbdd hp hωD
  have hcT : ∀ z, cauchyT ω z = cauchyTOn D ω z := by
    intro z
    rw [cauchyT_congr_ae hω0]
    unfold cauchyT cauchyTOn
    congr 1
    rw [← integral_indicator measurableSet_closedBall]
    congr 1
    funext ζ
    by_cases hζ : ζ ∈ D
    · rw [indicator_of_mem hζ, indicator_of_mem hζ]
    · rw [indicator_of_notMem hζ, indicator_of_notMem hζ, zero_div]
  have hcl : (closure D)ᶜ = {z : ℂ | 1 < ‖z‖} := by
    rw [hD, closure_closedBall]
    ext z; simp [not_le]
  refine ⟨?_, C, R, fun z hz => ?_⟩
  · rw [← hcl]
    exact hdiff.congr fun z _ => hcT z
  · rw [hcT]; exact hCR z hz

theorem l15_contour_zero {r : ℂ → ℂ} (hd : DifferentiableOn ℂ r {z : ℂ | 1 < ‖z‖}) {C R : ℝ}
    (hCR : ∀ z : ℂ, R < ‖z‖ → ‖r z‖ ≤ C / ‖z‖) (n : ℕ) (hn : 1 ≤ n) :
    ∮ z in C(0, 2), r z / z ^ n = 0 := by
  set J := ∮ z in C(0, 2), r z / z ^ n with hJ
  by_contra hne
  have hJpos : 0 < ‖J‖ := norm_pos_iff.2 hne
  set M := max R 2 with hM
  have hM2 : 2 ≤ M := le_max_right _ _
  have hMR : R ≤ M := le_max_left _ _
  -- choose ρ large
  obtain ⟨ρ, hρM, hρbig⟩ : ∃ ρ : ℝ, M < ρ ∧ 2 * π * |C| / ρ < ‖J‖ := by
    refine ⟨max (M + 1) (2 * π * |C| / ‖J‖ + 1), lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
    have hρ0 : 0 < max (M + 1) (2 * π * |C| / ‖J‖ + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    rw [div_lt_iff₀ hρ0]
    have h1 : 2 * π * |C| / ‖J‖ + 1 ≤ max (M + 1) (2 * π * |C| / ‖J‖ + 1) := le_max_right _ _
    have h2 : 2 * π * |C| / ‖J‖ < max (M + 1) (2 * π * |C| / ‖J‖ + 1) := by linarith
    rw [div_lt_iff₀ hJpos] at h2
    linarith
  have hρ2 : 2 ≤ ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hsub : ∀ z : ℂ, 2 ≤ ‖z‖ → z ∈ {z : ℂ | 1 < ‖z‖} := fun z hz => by
    show 1 < ‖z‖; linarith
  have hcont : ContinuousOn (fun z => r z / z ^ n) (closedBall (0 : ℂ) ρ \ ball (0 : ℂ) 2) := by
    refine ContinuousOn.div (hd.continuousOn.mono ?_) (continuousOn_pow n) ?_
    · intro z hz
      apply hsub
      have := hz.2
      simp only [mem_ball, dist_zero_right, not_lt] at this
      exact this
    · intro z hz
      apply pow_ne_zero
      have := hz.2
      simp only [mem_ball, dist_zero_right, not_lt] at this
      intro h0; rw [h0, norm_zero] at this; linarith
  have hdiff : ∀ z ∈ (ball (0 : ℂ) ρ \ closedBall (0 : ℂ) 2) \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z => r z / z ^ n) z := by
    intro z hz
    have hz2 : 2 < ‖z‖ := by
      have := hz.1.2
      simp only [mem_closedBall, dist_zero_right, not_le] at this
      exact this
    have hz1 : z ∈ {z : ℂ | 1 < ‖z‖} := hsub z hz2.le
    have hopen : IsOpen {z : ℂ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
    refine DifferentiableAt.div (hd.differentiableAt (hopen.mem_nhds hz1)) (differentiableAt_pow n) ?_
    apply pow_ne_zero
    intro h0; rw [h0, norm_zero] at hz2; linarith
  have heq := circleIntegral_eq_of_differentiable_on_annulus_off_countable (by norm_num : (0 : ℝ) < 2) hρ2
    countable_empty hcont hdiff
  have hbound : ‖∮ z in C(0, ρ), r z / z ^ n‖ ≤ 2 * π * ρ * (C / ρ / ρ ^ n) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hρ0.le fun z hz => ?_
    rw [mem_sphere_zero_iff_norm] at hz
    rw [norm_div, norm_pow, hz]
    have hr := hCR z (by rw [hz]; linarith)
    rw [hz] at hr
    exact div_le_div_of_nonneg_right hr (by positivity)
  rw [heq] at hbound
  have : 2 * π * ρ * (C / ρ / ρ ^ n) ≤ 2 * π * |C| / ρ := by
    have h1 : C / ρ / ρ ^ n ≤ |C| / ρ / ρ ^ n := by gcongr; exact le_abs_self C
    have hρn : ρ ≤ ρ ^ n := by
      calc ρ = ρ ^ 1 := (pow_one ρ).symm
        _ ≤ ρ ^ n := pow_le_pow_right₀ (by linarith) hn
    have h2 : |C| / ρ / ρ ^ n ≤ |C| / ρ / ρ := by
      apply div_le_div_of_nonneg_left (by positivity) hρ0 hρn
    calc 2 * π * ρ * (C / ρ / ρ ^ n) ≤ 2 * π * ρ * (|C| / ρ / ρ) := by
          apply mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 2 * π * |C| / ρ := by field_simp
  linarith

theorem l15_G_formula {nu : ℂ → ℂ} {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hnu : IsBeltramiCoeff nu univ k) (hsupp : ∀ w : ℂ, 1 ≤ ‖w‖ → nu w = 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => nu z * hilbertH ω z + nu z)
    {G : ℂ → ℂ} (hG : IsNormalizedSolution G nu) :
    ∃ D : ℂ, D ≠ 0 ∧ ∀ z : ℂ, G z = D⁻¹ * (z + cauchyT ω z - cauchyT ω 0) := by
  obtain ⟨hKqc, himg, hdil⟩ := l15_hydro_data hk0 hk1 hp hkp hnu hsupp hω hsol
  set r : ℂ → ℂ := cauchyT ω with hr
  set f : ℂ → ℂ := fun z => z + r z with hf
  have hinj : InjOn f univ := hKqc.2.2.1.2.1
  have hD : f 1 - f 0 ≠ 0 := fun h => one_ne_zero (hinj (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  set D := f 1 - f 0 with hDdef
  have hDi : D⁻¹ ≠ 0 := inv_ne_zero hD
  obtain ⟨hq, hsurj⟩ := b4_rat_affine_comp hKqc himg (α := 1) (γ := D⁻¹) 0 (-(D⁻¹ * f 0)) one_ne_zero hDi
  have hfun : (fun z => D⁻¹ * f (1 * z + 0) + -(D⁻¹ * f 0)) = fun z => D⁻¹ * (f z - f 0) := by
    funext z; simp; ring
  rw [hfun] at hq hsurj
  have hdiffae : ∀ᵐ z ∂(volume.restrict (univ : Set ℂ)), DifferentiableAt ℝ f z := thm9_3_differentiable_ae hKqc
  rw [Measure.restrict_univ] at hdiffae
  have hH : IsNormalizedSolution (fun z => D⁻¹ * (f z - f 0)) nu := by
    refine ⟨⟨_, hq⟩, hsurj, by simp, ?_, ?_⟩
    · show D⁻¹ * (f 1 - f 0) = 1
      rw [← hDdef]; exact inv_mul_cancel₀ hD
    · filter_upwards [hdiffae, hdil] with z h1 h2
      have hfz : DifferentiableAt ℝ (fun z => f z - f 0) z := h1.sub_const _
      have hφ : DifferentiableAt ℂ (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) := by fun_prop
      have hφ' : deriv (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) ≠ 0 := by simpa using hDi
      have e1 := complexDilatation_comp_conformal_left hfz hφ hφ'
      have e0 : complexDilatation (fun z => f z - f 0) z = complexDilatation f z := by
        unfold complexDilatation dz dzbar
        have : fderiv ℝ (fun z => f z - f 0) z = fderiv ℝ f z := by
          rw [fderiv_sub_const]
        rw [this]
      have hcomp : (fun z => D⁻¹ * (f z - f 0)) = (fun w : ℂ => D⁻¹ * w) ∘ (fun z => f z - f 0) := rfl
      rw [hcomp, e1, e0]; exact h2
  have hGH : G = fun z => D⁻¹ * (f z - f 0) :=
    thm13_5_uniqueness_plane hG.1 hH.1 hG.2.1 hH.2.1
      (by filter_upwards [hG.2.2.2.2, hH.2.2.2.2] with z a b using by rw [a, b]) hG.2.2.1 hG.2.2.2.1
      hH.2.2.1 hH.2.2.2.1
  refine ⟨D, hD, fun z => ?_⟩
  rw [hGH]; simp only [hf]; ring

/-- **Identification** of `Q_1, Q_2` with the hydrodynamic data.  `ν` is a Beltrami coefficient with `‖ν‖ ≤ k < 1`
supported in `closedBall 0 1`, `ω` solves (12.4) in `L_p`, and `G` is the normalized solution of `ν`.
Then `Q_1 = - cauchyT ω 0 · Q_2` and `Q_2 ≠ 0`. -/
theorem l15_identify {nu : ℂ → ℂ} {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hnu : IsBeltramiCoeff nu univ k) (hsupp : ∀ w : ℂ, 1 ≤ ‖w‖ → nu w = 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => nu z * hilbertH ω z + nu z)
    {G : ℂ → ℂ} (hG : IsNormalizedSolution G nu) :
    ((2 * π * I)⁻¹ * ∮ z in C(0, 2), G z / z ^ 1) +
        cauchyT ω 0 * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), G z / z ^ 2) = 0 ∧
      (2 * π * I)⁻¹ * ∮ z in C(0, 2), G z / z ^ 2 ≠ 0 := by
  obtain ⟨hKqc, himg, hdil⟩ := l15_hydro_data hk0 hk1 hp hkp hnu hsupp hω hsol
  set r : ℂ → ℂ := cauchyT ω with hr
  set f : ℂ → ℂ := fun z => z + r z with hf
  have hω0 : ω =ᵐ[volume] (closedBall (0 : ℂ) 1).indicator ω :=
    t2_omega_ae_eq_indicator (fun z hz => hsupp z hz.le) hsol
  obtain ⟨hdiffr, C, R, hCR⟩ := l15_cauchyT_outside hp hω hω0
  have hinj : InjOn f univ := hKqc.2.2.1.2.1
  have hD : f 1 - f 0 ≠ 0 := fun h => one_ne_zero (hinj (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  set D := f 1 - f 0 with hDdef
  have hDi : D⁻¹ ≠ 0 := inv_ne_zero hD
  -- the normalized map built from `f`
  obtain ⟨hq, hsurj⟩ := b4_rat_affine_comp hKqc himg (α := 1) (γ := D⁻¹) 0 (-(D⁻¹ * f 0)) one_ne_zero hDi
  have hfun : (fun z => D⁻¹ * f (1 * z + 0) + -(D⁻¹ * f 0)) = fun z => D⁻¹ * (f z - f 0) := by
    funext z; simp; ring
  rw [hfun] at hq hsurj
  have hdiffae : ∀ᵐ z ∂(volume.restrict (univ : Set ℂ)), DifferentiableAt ℝ f z := thm9_3_differentiable_ae hKqc
  rw [Measure.restrict_univ] at hdiffae
  have hH : IsNormalizedSolution (fun z => D⁻¹ * (f z - f 0)) nu := by
    refine ⟨⟨_, hq⟩, hsurj, by simp, ?_, ?_⟩
    · show D⁻¹ * (f 1 - f 0) = 1
      rw [← hDdef]; exact inv_mul_cancel₀ hD
    · filter_upwards [hdiffae, hdil] with z h1 h2
      have hfz : DifferentiableAt ℝ (fun z => f z - f 0) z := h1.sub_const _
      have hφ : DifferentiableAt ℂ (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) := by fun_prop
      have hφ' : deriv (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) ≠ 0 := by simpa using hDi
      have e1 := complexDilatation_comp_conformal_left hfz hφ hφ'
      have e0 : complexDilatation (fun z => f z - f 0) z = complexDilatation f z := by
        unfold complexDilatation dz dzbar
        have : fderiv ℝ (fun z => f z - f 0) z = fderiv ℝ f z := by
          rw [fderiv_sub_const]
        rw [this]
      have hcomp : (fun z => D⁻¹ * (f z - f 0)) = (fun w : ℂ => D⁻¹ * w) ∘ (fun z => f z - f 0) := rfl
      rw [hcomp, e1, e0]; exact h2
  have hGH : G = fun z => D⁻¹ * (f z - f 0) :=
    thm13_5_uniqueness_plane hG.1 hH.1 hG.2.1 hH.2.1
      (by filter_upwards [hG.2.2.2.2, hH.2.2.2.2] with z a b using by rw [a, b]) hG.2.2.1 hG.2.2.2.1
      hH.2.2.1 hH.2.2.2.1
  -- contour integrals
  have hr1 := l15_contour_zero hdiffr hCR 1 le_rfl
  have hr2 := l15_contour_zero hdiffr hCR 2 (by norm_num)
  have hsph : ∀ z ∈ sphere (0 : ℂ) 2, z ≠ 0 := fun z hz h0 => by
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz; norm_num at hz
  have hsub : sphere (0 : ℂ) 2 ⊆ {z : ℂ | 1 < ‖z‖} := fun z hz => by
    show 1 < ‖z‖
    rw [mem_sphere_zero_iff_norm] at hz; rw [hz]; norm_num
  have hrc : ContinuousOn r (sphere (0 : ℂ) 2) := hdiffr.continuousOn.mono hsub
  have hone : ∮ z in C(0, 2), (1 : ℂ) = 0 := by
    simpa using circleIntegral.integral_sub_zpow_of_ne (n := 0) (by norm_num) (0 : ℂ) (0 : ℂ) (2 : ℝ)
  have hinv : ∮ z in C(0, 2), (z - 0)⁻¹ = 2 * π * I :=
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self (by norm_num))
  have hinv2 : ∮ z in C(0, 2), (z - 0) ^ (-2 : ℤ) = 0 :=
    circleIntegral.integral_sub_zpow_of_ne (by norm_num) _ _ _
  have hGs : ∀ z : ℂ, G z = D⁻¹ * (z + r z - r 0) := fun z => by
    rw [hGH]; simp only [hf]; ring
  have hci : ∀ g : ℂ → ℂ, ContinuousOn g (sphere (0 : ℂ) 2) → CircleIntegrable g 0 2 := fun g hg =>
    hg.circleIntegrable (by norm_num)
  have hz0 : ContinuousOn (fun z : ℂ => (z - 0)⁻¹) (sphere (0 : ℂ) 2) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun z hz => ?_
    simpa using hsph z hz
  have hz2 : ContinuousOn (fun z : ℂ => (z - 0) ^ (-2 : ℤ)) (sphere (0 : ℂ) 2) := by
    refine ContinuousOn.zpow₀ (by fun_prop) _ fun z hz => Or.inl ?_
    simpa using hsph z hz
  have hrz : ∀ n : ℕ, ContinuousOn (fun z : ℂ => r z / z ^ n) (sphere (0 : ℂ) 2) := fun n =>
    hrc.div (by fun_prop) fun z hz => pow_ne_zero _ (hsph z hz)
  -- Q₁
  have hQ1 : ∮ z in C(0, 2), G z / z ^ 1 = D⁻¹ * (- (r 0 * (2 * π * I))) := by
    have heq : ∮ z in C(0, 2), G z / z ^ 1 =
        ∮ z in C(0, 2), D⁻¹ * (1 + r z / z ^ 1 - r 0 * (z - 0)⁻¹) := by
      refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
      have := hsph z hz
      simp only [hGs, sub_zero, pow_one]
      field_simp
    have i1 : CircleIntegrable (fun _ : ℂ => (1 : ℂ)) 0 2 := hci _ continuousOn_const
    have i2 : CircleIntegrable (fun z : ℂ => r z / z ^ 1) 0 2 := hci _ (hrz 1)
    have i3 : CircleIntegrable (fun z : ℂ => r 0 * (z - 0)⁻¹) 0 2 := hci _ (continuousOn_const.mul hz0)
    have i12 : CircleIntegrable (fun z : ℂ => 1 + r z / z ^ 1) 0 2 := hci _ (continuousOn_const.add (hrz 1))
    rw [heq, circleIntegral.integral_const_mul, circleIntegral.integral_sub i12 i3,
      circleIntegral.integral_add i1 i2, circleIntegral.integral_const_mul, hone, hinv, hr1]
    ring
  have hQ2 : ∮ z in C(0, 2), G z / z ^ 2 = D⁻¹ * (2 * π * I) := by
    have heq : ∮ z in C(0, 2), G z / z ^ 2 =
        ∮ z in C(0, 2), D⁻¹ * ((z - 0)⁻¹ + r z / z ^ 2 - r 0 * (z - 0) ^ (-2 : ℤ)) := by
      refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
      have := hsph z hz
      simp only [hGs, sub_zero, zpow_neg, zpow_ofNat]
      field_simp
    have i1 : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 0 2 := hci _ hz0
    have i2 : CircleIntegrable (fun z : ℂ => r z / z ^ 2) 0 2 := hci _ (hrz 2)
    have i3 : CircleIntegrable (fun z : ℂ => r 0 * (z - 0) ^ (-2 : ℤ)) 0 2 := hci _ (continuousOn_const.mul hz2)
    have i12 : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹ + r z / z ^ 2) 0 2 := hci _ (hz0.add (hrz 2))
    rw [heq, circleIntegral.integral_const_mul, circleIntegral.integral_sub i12 i3,
      circleIntegral.integral_add i1 i2, circleIntegral.integral_const_mul, hinv, hr2, hinv2]
    ring
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  rw [hQ1, hQ2]
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · exact mul_ne_zero (inv_ne_zero hπ) (mul_ne_zero hDi hπ)

/-- **Core** (the book's `f(0) = 0`): for `h` as above the hydrodynamic solution of `ν^{[1]}` has `cauchyT ω 0 = 0`. -/
theorem l15_core {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k)
    {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hs : ω =ᵐ[volume] fun z => nu 1 z * hilbertH ω z + nu 1 z) : cauchyT ω 0 = 0 := by
  -- normalized plane solutions `G t` of `ν^{[t]}` (|t| ≤ 1)
  have hGex : ∀ t : ℂ, ‖t‖ ≤ 1 → ∃ g : ℂ → ℂ, IsNormalizedSolution g (nu t) := fun t ht => by
    obtain ⟨hb, -, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
    obtain ⟨g, hg, -, -⟩ := thm13_7_normalized_existence hk0 hk1 hb
    exact ⟨g, hg⟩
  have hΩex : ∀ t : ℂ, ‖t‖ ≤ 1 → ∃ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) ∧
      (ω' =ᵐ[volume] fun z => nu t z * hilbertH ω' z + nu t z) := fun t ht => by
    obtain ⟨hb, -, hbd'⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu ht
    have hμmem : MemLp (nu t) (ENNReal.ofReal p) :=
      (l15_nu_Lp hh hk0 hk1 hbd hnu ht (by linarith)).1
    obtain ⟨ω', hω', hsol, -⟩ := eq12_1_solution hk0 hb hp hkp hμmem
    exact ⟨ω', hω', hsol⟩
  choose! G hG using hGex
  choose! Ω hΩ using hΩex
  have hGb : ∀ t ∈ ball (0 : ℂ) 1, IsNormalizedSolution (G t) (nu t) := fun t ht =>
    hG t (mem_ball_zero_iff.1 ht).le
  set Q : ℕ → ℂ → ℂ := fun n t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), G t z / z ^ n with hQ
  have hid : ∀ t ∈ ball (0 : ℂ) 1, Q 1 t + cauchyT (Ω t) 0 * Q 2 t = 0 ∧ Q 2 t ≠ 0 := fun t ht => by
    obtain ⟨hb, hsupp, -⟩ := l15_nu_beltrami hh hk0 hk1 hbd hnu (mem_ball_zero_iff.1 ht).le
    exact l15_identify hk0 hk1 hp hkp hb hsupp (hΩ t (mem_ball_zero_iff.1 ht).le).1
      (hΩ t (mem_ball_zero_iff.1 ht).le).2 (hGb t ht)
  set P : ℂ → ℂ := fun t => Q 1 t / Q 2 t with hP
  have hPv : ∀ t ∈ ball (0 : ℂ) 1, P t = -cauchyT (Ω t) 0 := fun t ht => by
    obtain ⟨h1, h2⟩ := hid t ht
    rw [hP]
    simp only
    rw [div_eq_iff h2]
    linear_combination h1
  have hPhol : DifferentiableOn ℂ P (ball (0 : ℂ) 1) :=
    (l15_QS_hol hh hk0 hk1 hbd hnu hGb 1).div (l15_QS_hol hh hk0 hk1 hbd hnu hGb 2) fun t ht => (hid t ht).2
  have hProt : ∀ l : ℂ, ‖l‖ = 1 → ∀ t ∈ ball (0 : ℂ) 1, P (l * t) = l * P t := by
    intro l hl t ht
    have hl' : ‖conj l‖ = 1 := by rw [Complex.norm_conj, hl]
    have h1 := l15_QS_rot hh hk0 hk1 hbd hnu hGb 1 le_rfl hl' (mem_ball_zero_iff.1 ht)
    have h2 := l15_QS_rot hh hk0 hk1 hbd hnu hGb 2 (by norm_num) hl' (mem_ball_zero_iff.1 ht)
    rw [Complex.conj_conj] at h1 h2
    have hg : G t (conj l) ≠ 0 := by
      intro h0
      obtain ⟨⟨K, hK⟩, -, hG0, -, -⟩ := hGb t ht
      have hinj := hK.2.2.1.2.1
      have : conj l = 0 := hinj (mem_univ _) (mem_univ _) (h0.trans hG0.symm)
      rw [map_eq_zero] at this
      rw [this, norm_zero] at hl
      exact zero_ne_one hl
    have hll : l * conj l = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hl]; simp
    have hcl : conj l ≠ 0 := by
      intro h0; rw [h0] at hll; simp at hll
    have hQ2 := (hid t ht).2
    have h1' : Q 1 (l * t) = Q 1 t / G t (conj l) := by
      rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul] at h1; exact h1
    have h2' : Q 2 (l * t) = conj l * Q 2 t / G t (conj l) := by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h2; exact h2
    have alg : ∀ a b g c : ℂ, g ≠ 0 → b ≠ 0 → c ≠ 0 → l * c = 1 → (a / g) / (c * b / g) = l * (a / b) := by
      intro a b g c hg hb hc hlc
      field_simp
      linear_combination (-a) * hlc
    show Q 1 (l * t) / Q 2 (l * t) = l * (Q 1 t / Q 2 t)
    rw [h1', h2']
    exact alg _ _ _ _ hg hQ2 hcl hll
  obtain ⟨C, hC⟩ := l15_small hh hk0 hk1 hbd hnu hp hkp
  have hPb : ∀ t ∈ ball (0 : ℂ) 1, ‖P t‖ ≤ C * ‖t‖ ^ 2 := fun t ht => by
    rw [hPv t ht, norm_neg]
    exact hC t (mem_ball_zero_iff.1 ht).le (Ω t) (hΩ t (mem_ball_zero_iff.1 ht).le).1
      (hΩ t (mem_ball_zero_iff.1 ht).le).2
  have hP0 := l15_rigid hPhol hProt hPb
  have hz : ∀ t ∈ ball (0 : ℂ) 1, cauchyT (Ω t) 0 = 0 := fun t ht => by
    have := hPv t ht
    rw [hP0 t ht] at this
    exact (neg_eq_zero.1 this.symm)
  -- the limit r → 1
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hr]; linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  have hrt : Tendsto r atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat 1).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine this.congr fun n => ?_
      push_cast; ring_nf
    simpa [hr] using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  have hmemr : ∀ n, (r n : ℂ) ∈ ball (0 : ℂ) 1 := fun n => by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (hr0 n)]; exact hr1 n
  have hlim := l15_limit hh hk0 hk1 hbd hnu hp hkp hr0 hr1 hrt
    (ωn := fun n => Ω (r n)) (fun n => (hΩ _ (mem_ball_zero_iff.1 (hmemr n)).le).1)
    (fun n => (hΩ _ (mem_ball_zero_iff.1 (hmemr n)).le).2) hω hs
  have hconst : (fun n => cauchyT (Ω (r n)) 0) = fun _ => (0 : ℂ) := funext fun n => hz _ (hmemr n)
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

theorem l15_phi_hol (φ : AInf unitDisc) :
    DifferentiableOn ℂ (fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w))) unitDisc := by
  intro w hw
  have hw' : conj w ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hw
  have hd : DifferentiableAt ℂ (AInf.toFun φ) (conj w) :=
    (φ.2 : DifferentiableOn ℂ (unweight unitDisc φ.1) unitDisc).differentiableAt (isOpen_ball.mem_nhds hw')
  have hcc := hd.conj_conj
  rw [Complex.conj_conj] at hcc
  exact ((differentiableAt_const _).mul hcc).differentiableWithinAt

theorem l15_phi_bound (φ : AInf unitDisc) :
    ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖-(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w))‖ ≤ ‖φ‖ / 2 := by
  intro w hw
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hw' : conj w ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_conj]; exact hwn
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have e : AInf.toFun φ (conj w) = φ.1 ⟨conj w, hw'⟩ / (1 - (‖w‖ : ℂ) ^ 2) ^ 2 := by
    simp [AInf.toFun, unweight, hw', Complex.norm_conj]
  have hn : ‖(1 - (‖w‖ : ℂ) ^ 2) ^ 2‖ = (1 - ‖w‖ ^ 2) ^ 2 := by
    rw [norm_pow]
    have : (1 - (‖w‖ : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hle : ‖φ.1 ⟨conj w, hw'⟩‖ ≤ ‖φ‖ := by
    have := BoundedContinuousFunction.norm_coe_le_norm φ.1 ⟨conj w, hw'⟩
    exact this
  rw [norm_mul, Complex.norm_conj, e, norm_div, hn]
  have h2 : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by simp
  rw [h2]
  have hq : 0 < (1 - ‖w‖ ^ 2) ^ 2 := by positivity
  calc (1 - ‖w‖ ^ 2) ^ 2 * (1 / 2 * (‖φ.1 ⟨conj w, hw'⟩‖ / (1 - ‖w‖ ^ 2) ^ 2))
      = 1 / 2 * ‖φ.1 ⟨conj w, hw'⟩‖ := by field_simp
    _ ≤ 1 / 2 * ‖φ‖ := by gcongr
    _ = ‖φ‖ / 2 := by ring

theorem l15_extB_beltrami (μ : LinfStar) :
    IsBeltramiCoeff (extB μ) univ ‖μ‖ ∧ (∀ ζ : ℂ, ‖ζ‖ < 1 → extB μ ζ = 0) := by
  have hms : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  refine ⟨⟨?_, ?_⟩, fun ζ hζ => ?_⟩
  · rw [Measure.restrict_univ]
    exact (aestronglyMeasurable_indicator_iff hms).2 (Lp.aestronglyMeasurable μ)
  · rw [Measure.restrict_univ]
    have h1 : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖μ z‖ ≤ ‖μ‖ := LinfStar_ae_norm_le μ
    rw [ae_restrict_iff' hms] at h1
    filter_upwards [h1] with z hz
    by_cases hzm : z ∈ unitDiscExterior
    · rw [extB, indicator_of_mem hzm]; exact hz hzm
    · rw [extB, indicator_of_notMem hzm, norm_zero]; exact norm_nonneg _
  · rw [extB]
    apply indicator_of_notMem
    intro h
    have : 1 < ‖ζ‖ := h
    linarith

theorem l15_nu_ae (φ : AInf unitDisc) {nu : ℂ → ℂ → ℂ}
    (hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 *
      conj ((fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w))) (conj t * w)) else 0) :
    ∀ᵐ w, nxMu2t (extB (Lambda φ)) w = nu 1 w := by
  have hms : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hae1 := Lambda_coe_ae φ
  rw [Filter.EventuallyEq, ae_restrict_iff' hms] at hae1
  have hae2 := nx_ae_inv hae1
  have hne : ∀ᵐ w : ℂ, w ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hae2, hne] with w hw hw0
  by_cases hw1 : ‖w‖ < 1
  · have hwi : w⁻¹ ∈ unitDiscExterior := by
      show 1 < ‖w⁻¹‖
      rw [norm_inv]; exact one_lt_inv_iff₀.2 ⟨norm_pos_iff.2 hw0, hw1⟩
    have hwc := hw hwi
    have hnot : w⁻¹ ∈ unitDiscᶜ := by
      intro h
      have : ‖w⁻¹‖ < 1 := mem_ball_zero_iff.1 h
      have h2 : 1 < ‖w⁻¹‖ := hwi
      linarith
    rw [nxMu2t, nxMu2, indicator_of_mem hnot, extB, indicator_of_mem hwi, hwc, hnu, if_pos hw1]
    simp only [refl, map_inv₀, Complex.conj_conj, map_mul, map_neg, map_div₀, map_one, map_ofNat, one_mul,
      inv_inv, one_pow, norm_inv]
    have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw0).ne'
    have hc : conj w ≠ 0 := (map_ne_zero _).2 hw0
    have hn2 : (‖w‖ : ℂ) ^ 2 = w * conj w := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    push_cast
    field_simp
    linear_combination (((‖w‖ : ℂ) ^ 2 - 1) ^ 2 * AInf.toFun φ (conj w) * (conj w * w + (‖w‖ : ℂ) ^ 2)) * hn2
  · have hwi : w⁻¹ ∉ unitDiscExterior := by
      intro h
      have : 1 < ‖w⁻¹‖ := h
      rw [norm_inv] at this
      have := (one_lt_inv_iff₀.1 this).2
      exact hw1 this
    rw [nxMu2t, nxMu2, hnu, if_neg hw1]
    by_cases hnot : w⁻¹ ∈ unitDiscᶜ
    · rw [indicator_of_mem hnot, extB, indicator_of_notMem hwi]; simp
    · rw [indicator_of_notMem hnot]; simp

/-- The plane solution `W` of `extB μ` fixing `0, 1, ∞` has `W''(0) = 0` for harmonic `μ ∈ L∞(𝔻*)₁`
(`ahI_invConj_isNormalizedSolution` + `l15_core` + `thm13_5_uniqueness_plane` + `cauchyTOn` decay). -/
theorem l15_W_second {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extB μ)) : deriv (deriv W) 0 = 0 := by
  obtain ⟨φ, hφ⟩ := Lambda_surjective_harmonic hh
  subst hφ
  set k := ‖φ‖ / 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hLn : ‖Lambda φ‖ = k := Lambda_norm_eq φ
  have hk1 : k < 1 := by
    have h' : ‖Lambda φ‖ < 1 := by simpa [LinfStarBall] using hμ
    linarith
  set h : ℂ → ℂ := fun w => -(1 / 2 : ℂ) * conj (AInf.toFun φ (conj w)) with hhdef
  have hh1 : DifferentiableOn ℂ h unitDisc := l15_phi_hol φ
  have hbd : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖h w‖ ≤ k := l15_phi_bound φ
  set nu : ℂ → ℂ → ℂ := fun t w => if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0
    with hnudef
  have hnu : ∀ t w, nu t w = if ‖w‖ < 1 then (1 - ‖w‖ ^ 2) ^ 2 * t ^ 2 * conj (h (conj t * w)) else 0 :=
    fun _ _ => rfl
  obtain ⟨p, hp, -, hkp⟩ := eq12_1_exists_exponent hk1 (show (2 : ℝ) < 3 by norm_num)
  obtain ⟨hb1, hs1, -⟩ := l15_nu_beltrami hh1 hk0 hk1 hbd hnu (t := 1) (by simp)
  obtain ⟨ω, hω, hsol, -⟩ := eq12_1_solution hk0 hb1 hp hkp
    (l15_nu_Lp hh1 hk0 hk1 hbd hnu (t := 1) (by simp) (by linarith)).1
  have hcore : cauchyT ω 0 = 0 := l15_core hh1 hk0 hk1 hbd hnu hp hkp hω hsol
  -- the inverted normalized solution
  obtain ⟨hβ, hβ0⟩ := l15_extB_beltrami (Lambda φ)
  rw [hLn] at hβ
  have hGn := ahI_invConj_isNormalizedSolution hk0 hk1 hβ hβ0 hW
  have hae : ∀ᵐ w, nxMu2t (extB (Lambda φ)) w = nu 1 w := l15_nu_ae φ hnu
  have hG1 : IsNormalizedSolution (nxInvConj W) (nu 1) :=
    ⟨hGn.1, hGn.2.1, hGn.2.2.1, hGn.2.2.2.1, by
      filter_upwards [hGn.2.2.2.2, hae] with z a b; rw [a, b]⟩
  obtain ⟨D, hD, hGform⟩ := l15_G_formula hk0 hk1 hp hkp hb1 hs1 hω hsol hG1
  have hω0 : ω =ᵐ[volume] (closedBall (0 : ℂ) 1).indicator ω :=
    t2_omega_ae_eq_indicator (fun z hz => hs1 z hz.le) hsol
  obtain ⟨-, C, R, hCR⟩ := l15_cauchyT_outside hp hω hω0
  set r : ℂ → ℂ := cauchyT ω with hr
  have hr0 : r 0 = 0 := hcore
  have hW0 : W 0 = 0 := hW.2.2.1
  have hWd : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hnb : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0mem
  have hWinj : InjOn W univ := hW.1.choose_spec.2.2.1.2.1
  set V : ℂ → ℂ := dslope W 0 with hV
  have hVd : DifferentiableOn ℂ V unitDisc := (differentiableOn_dslope hnb).2 hWd
  have hVu : ∀ u : ℂ, u ≠ 0 → V u = W u / u := by
    intro u hu
    rw [hV, dslope_of_ne _ hu, slope_def_field, hW0, sub_zero, sub_zero]
  have hWne : ∀ u : ℂ, u ≠ 0 → W u ≠ 0 := fun u hu he =>
    hu (hWinj (mem_univ _) (mem_univ _) (he.trans hW0.symm))
  have hWform : ∀ u : ℂ, u ≠ 0 → (W u)⁻¹ = D⁻¹ * (u⁻¹ + r u⁻¹) := by
    intro u hu
    have h1 := hGform u⁻¹
    simp only [nxInvConj, inv_inv] at h1
    rw [h1, hr0, sub_zero]
  -- the small quantity `s u = r (1/u)`
  set R' : ℝ := max R 1 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsb : ∀ u : ℂ, u ≠ 0 → ‖u‖ < 1 / R' → ‖r u⁻¹‖ ≤ C * ‖u‖ := by
    intro u hu hub
    have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hbig : R < ‖u⁻¹‖ := by
      rw [norm_inv]
      have : R' < ‖u‖⁻¹ := by
        rw [lt_inv_comm₀ hR'0 hun]; rwa [one_div] at hub
      exact lt_of_le_of_lt (le_max_left _ _) this
    have := hCR u⁻¹ hbig
    rwa [norm_inv, div_inv_eq_mul] at this
  have hs0 : Tendsto (fun u : ℂ => r u⁻¹) (𝓝[≠] 0) (𝓝 0) := by
    have hb : Tendsto (fun u : ℂ => |C| * ‖u‖) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun u : ℂ => |C| * ‖u‖) (𝓝 0) (𝓝 (|C| * ‖(0 : ℂ)‖)) :=
        (continuous_const.mul continuous_norm).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (one_div_pos.2 hR'0))]
      with u hu1 hu2
    have hu0 : u ≠ 0 := hu1
    have := hsb u hu0 (by simpa using hu2)
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
  have hε0 : Tendsto (fun u : ℂ => u * r u⁻¹) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℂ => u) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h1.mul hs0
  have hVform : ∀ᶠ u in 𝓝[≠] (0 : ℂ), V u = D / (1 + u * r u⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := hu
    have hX : u⁻¹ + r u⁻¹ ≠ 0 := by
      intro hX
      have := hWform u hu0
      rw [hX, mul_zero] at this
      exact hWne u hu0 (inv_eq_zero.1 this)
    have h1 : W u = D * (u⁻¹ + r u⁻¹)⁻¹ := by
      have := hWform u hu0
      rw [← inv_inv (W u), this, mul_inv, inv_inv]
    have h2 : 1 + u * r u⁻¹ = u * (u⁻¹ + r u⁻¹) := by field_simp
    rw [hVu u hu0, h1, h2]
    field_simp
  have hVcont : ContinuousAt V 0 := (hVd.differentiableAt hnb).continuousAt
  have hV0 : V 0 = D := by
    have h1 : Tendsto V (𝓝[≠] 0) (𝓝 (V 0)) := hVcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun u : ℂ => D / (1 + u * r u⁻¹)) (𝓝[≠] 0) (𝓝 (D / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add hε0) (by simp)
    rw [add_zero, div_one] at h2
    exact tendsto_nhds_unique h1 (h2.congr' (hVform.mono fun u hu => hu.symm))
  have hdV0 : deriv V 0 = 0 := by
    have hd : HasDerivAt V (deriv V 0) 0 := (hVd.differentiableAt hnb).hasDerivAt
    have h1 := hasDerivAt_iff_tendsto_slope.1 hd
    have h2 : Tendsto (fun u : ℂ => -D * r u⁻¹ / (1 + u * r u⁻¹)) (𝓝[≠] 0) (𝓝 (-D * 0 / (1 + 0))) :=
      (tendsto_const_nhds.mul hs0).div (tendsto_const_nhds.add hε0) (by simp)
    simp only [mul_zero, zero_div] at h2
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [hVform, self_mem_nhdsWithin] with u hu hu1
    have hu0 : u ≠ 0 := hu1
    have hden : 1 + u * r u⁻¹ ≠ 0 := by
      intro he
      rw [he, div_zero, hVu u hu0] at hu
      exact hWne u hu0 ((div_eq_zero_iff.1 hu).resolve_right hu0)
    rw [slope_def_field, hu, hV0, sub_zero]
    generalize r u⁻¹ = s at hden ⊢
    have hx : (1 + u * s) * (1 + u * s)⁻¹ = 1 := mul_inv_cancel₀ hden
    field_simp
    linear_combination (-1) * hx
  have hWuV : ∀ u : ℂ, W u = u * V u := by
    intro u
    by_cases hu : u = 0
    · rw [hu, hW0, zero_mul]
    · rw [hVu u hu]; field_simp
  have hderW : ∀ u ∈ unitDisc, deriv W u = V u + u * deriv V u := by
    intro u hu
    have hVa : DifferentiableAt ℂ V u := hVd.differentiableAt (isOpen_ball.mem_nhds hu)
    have h2 := ((hasDerivAt_id u).mul hVa.hasDerivAt).deriv
    have hfun : W = fun u => id u * V u := funext hWuV
    rw [hfun]
    refine h2.trans ?_
    simp
  have hev : deriv W =ᶠ[𝓝 (0 : ℂ)] fun u => V u + u * deriv V u :=
    Filter.eventuallyEq_of_mem hnb hderW
  have hVa0 : AnalyticAt ℂ V 0 := hVd.analyticOnNhd isOpen_ball 0 h0mem
  have hdVd : DifferentiableAt ℂ (deriv V) 0 := hVa0.deriv.differentiableAt
  have hVdd : DifferentiableAt ℂ V 0 := hVd.differentiableAt hnb
  have hH := hVdd.hasDerivAt.add ((hasDerivAt_id (0 : ℂ)).mul hdVd.hasDerivAt)
  rw [hev.deriv_eq]
  have h3 := hH.deriv
  simp only [id, zero_mul, add_zero, one_mul, hdV0] at h3
  exact h3

theorem l15_fB_jets {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    ∃ a c : ℂ, a ≠ 0 ∧ deriv (deriv (fB μ)) 0 = -2 * c / a ∧
      wB μ extInf = (if c = 0 then extInf else ((a / c : ℂ) : ExtPlane)) := by
  obtain ⟨hB, -⟩ := wB_spec hμ
  obtain ⟨M, hM, W, hW, hfin, hinf, f, hf, hf0, hf1, hfp⟩ := hB
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hW2 := l15_W_second hμ hh hW
  have hhol : DifferentiableOn ℂ W unitDisc := extB_solution_holomorphic hW
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hWan : AnalyticAt ℂ W 0 := hhol.analyticOnNhd isOpen_ball 0 h0mem
  have hW0 : W 0 = 0 := hW.2.2.1
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin' := (hfin z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin'
    exact OnePoint.infty_ne_coe _ hfin'
  have hrep : EqOn (fB μ) (fun z => mobiusFn a b c d (W z)) unitDisc := by
    intro z hz
    rw [fB, hfin z, mobiusExt_coe (hden z hz)]
    rfl
  have hnhds : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0mem
  have hev : fB μ =ᶠ[𝓝 (0 : ℂ)] fun z => mobiusFn a b c d (W z) :=
    Filter.eventuallyEq_of_mem hnhds hrep
  obtain ⟨hF0, hF1, -⟩ := fB_normalization μ
  have hd0 : c * W 0 + d ≠ 0 := hden 0 h0mem
  rw [hW0, mul_zero, zero_add] at hd0
  obtain ⟨j1, j2⟩ := mobius_comp_first_second (a := a) (b := b) (c := c) (d := d) hWan
    (by rw [hW0, mul_zero, zero_add]; exact hd0)
  have e0 : fB μ 0 = b / d := by
    rw [hev.eq_of_nhds]
    simp [mobiusFn, hW0]
  have hb : b = 0 := by
    rw [hF0] at e0
    have := e0.symm
    rw [div_eq_zero_iff] at this
    exact this.resolve_right hd0
  subst hb
  have e1 : deriv (fB μ) 0 = (a * d / d ^ 2) * deriv W 0 := by
    rw [hev.deriv_eq, j1, hW0]
    simp
  have e2 : deriv (deriv (fB μ)) 0 = (-(2 * c * (a * d - 0 * c)) / (c * 0 + d) ^ 3) * (deriv W 0) ^ 2 +
      ((a * d - 0 * c) / (c * 0 + d) ^ 2) * deriv (deriv W) 0 := by
    rw [hev.deriv.deriv_eq, j2, hW0]
  rw [hW2] at e2
  set w1 := deriv W 0 with hw1
  have hd : d ≠ 0 := hd0
  have h1 : a * w1 = d := by
    have := e1.symm.trans hF1
    field_simp at this
    linear_combination this
  have ha : a ≠ 0 := by
    intro ha0; rw [ha0, zero_mul] at h1; exact hd h1.symm
  have hw : w1 = d / a := by rw [eq_div_iff ha, mul_comm]; exact h1
  refine ⟨a, c, ha, ?_, ?_⟩
  · rw [e2, hw]
    simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    field_simp
  · rw [hinf]
    by_cases hc : c = 0
    · simp [mobiusExt, hc]
    · simp [mobiusExt, hc]

theorem l15_conj2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ extInf) = extInf := by
  obtain ⟨a, c, ha, hF2, hw⟩ := l15_fB_jets hμ hh
  rw [hw, hF2]
  by_cases hc : c = 0
  · subst hc
    simp [mobiusExt]
  · rw [if_neg hc]
    apply mobiusExt_coe_of_eq_zero
    field_simp
    ring

theorem l15_fB_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    wB μ extInf = mobiusExt 1 0 (-(deriv (deriv (fB μ)) 0 / 2)) 1 extInf := by
  obtain ⟨a, c, ha, hF2, hw⟩ := l15_fB_jets hμ hh
  rw [hw, hF2]
  by_cases hc : c = 0
  · subst hc
    simp [mobiusExt]
  · rw [if_neg hc]
    have hne : -(-2 * c / a / 2) ≠ 0 := by
      have : -(-2 * c / a / 2) = c / a := by ring
      rw [this]; exact div_ne_zero hc ha
    simp only [mobiusExt, OnePoint.elim_infty, if_neg hne]
    congr 1
    field_simp

end TakhtajanTeo
