import TakhtajanTeo.Ch1.S5Thm53Curve
import TakhtajanTeo.Ch1.L55
import TakhtajanTeo.Ch2.S2_Thm21
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch2.PeriodGrunskyBounds
import TakhtajanTeo.Ch2.S2_GrunskyOp
import TakhtajanTeo.Ch2.S2_MixedHook
import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.GrunskyOperator

/-!
# `thm_5_3` via Grunsky unitarity (`s5gr_`, 下属5, Program G)

Host: new module `TakhtajanTeo/Ch1/S5Thm53Grunsky.lean` (route C of `collaboration/下属5/SCOUT_T53_Wb.md`).

Along `τ ↦ τ • Y`, `Y = (φ, s)`, the potential is `K = log|G_τ'(∞)|` for the normalized pair
`(F_τ, G_τ)`, where `F_τ = λ_{c(μ_τ) - τ s} ∘ f^{μ_τ}`. This `F_τ` is holomorphic in `τ`, with `F_0 = id`,
`S(F_τ) = τ φ` and `F_τ''(0)/2 = τ s`. Notation: `c_∓ = (√k b_{∓k,0})_k`.

* `r22_sum`: `2K = ‖c_-‖² + ‖c_+‖²`.
* W1 (`s5gr_cross`): the `λ₀`-polarization of `thm_2_1` gives `B₁ᵗ c̄_- + B₃ᵗ c̄_+ = c_-`.
* W3 (`s5gr_two_sided`): with `x = c_- - B₁ᵗ c̄_-` (f-only), `‖x‖² ≤ ‖c_+‖² ≤ ‖x‖²/(1 - ‖B₁‖²)`.
  - The upper bound needs `B₃` onto (W2, W4–W6).
* W7: in `ℓ²`, `c_-(τ) = τ ċ + O(τ²)` and `‖B₁(τ)‖ = O(τ)`.
* W8: `ċ_k = -√k ȧ_k`, where `ȧ` are the coefficients of `∂_τ F_τ`, so `‖ċ‖² = ‖Y‖²_VK`.
* Hence `K(τY) = ‖Y‖²_VK |τ|² + o(|τ|²)` (W9), and the Levi form at the origin is `‖Y‖²_VK` (W10, W11).
* `thm_5_3` then follows from the published reductions `s5t53_ii_of_origin` and `s5t53_i_of_ii`.

The vertical and mixed parts need no separate treatment: `ȧ_1 = s`.
-/

open Complex Set MeasureTheory Metric Filter Topology Asymptotics
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

/-- One variable: a `C²` function with `h(t) = B t² + o(t²)` has `h''(0) = 2B` (L'Hôpital). -/
theorem s5gr_second_deriv {h : ℝ → ℝ} (hh : ContDiffAt ℝ 2 h 0) {B : ℝ}
    (ho : (fun t : ℝ => h t - B * t ^ 2) =o[𝓝 0] (fun t : ℝ => t ^ 2)) : deriv (deriv h) 0 = 2 * B := by
  set e : ℝ → ℝ := fun t => h t - B * t ^ 2 with he
  have hq : ContDiff ℝ 2 (fun t : ℝ => B * t ^ 2) := contDiff_const.mul (contDiff_id.pow 2)
  have hec : ContDiffAt ℝ 2 e 0 := hh.sub hq.contDiffAt
  -- `e(0) = 0`, `e'(0) = 0`
  have he0 : e 0 = 0 := by
    have hb := (ho.bound one_pos).self_of_nhds
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      norm_le_zero_iff] at hb
    exact hb
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ e t :=
    (hec.eventually (by simp)).mono fun t ht => ht.differentiableAt two_ne_zero
  have hd0 : HasDerivAt e 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have h1 : (fun t : ℝ => e (0 + t) - e 0 - t • (0 : ℝ)) = e := by
      funext t; simp [he0]
    rw [h1]
    exact ho.trans (Asymptotics.isLittleO_pow_id (by norm_num))
  have hec' : ContDiffAt ℝ ((1 : ℕ) + 1) e 0 := by norm_num; exact hec
  obtain ⟨F', ⟨u, hu, huF⟩, hF'c⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hec'
  set e' : ℝ → ℝ := fun t => F' t 1 with he'def
  have hue : ∀ y ∈ u, HasDerivAt e (e' y) y := fun y hy => (huF y hy).hasDerivAt
  have he'c : DifferentiableAt ℝ e' 0 := by
    have h1 : DifferentiableAt ℝ F' 0 := hF'c.differentiableAt (by norm_num)
    exact h1.clm_apply (differentiableAt_const _)
  have hde : deriv e =ᶠ[𝓝 0] e' := by
    filter_upwards [hu] with y hy
    exact (hue y hy).deriv
  have hd2 : DifferentiableAt ℝ e' 0 := he'c
  have he'0 : e' 0 = 0 := by rw [← hde.self_of_nhds, hd0.deriv]
  set L := deriv e' 0 with hLdef
  -- L'Hôpital: `e(t)/t² → L/2`
  have hslope := hd2.hasDerivAt.tendsto_slope_zero
  have hdiv : Tendsto (fun x : ℝ => e' x / (2 * x)) (𝓝[≠] 0) (𝓝 (L / 2)) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ • (e' (0 + t) - e' 0) / 2) (𝓝[≠] 0) (𝓝 (L / 2)) :=
      hslope.div_const 2
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, he'0, sub_zero, smul_eq_mul]
    field_simp
  have hlh := HasDerivAt.lhopital_zero_nhdsNE (f := e) (f' := e') (g := fun t : ℝ => t ^ 2)
    (g' := fun t => 2 * t)
    (by filter_upwards [nhdsWithin_le_nhds hu] with y hy; exact hue y hy)
    (Eventually.of_forall fun t => by simpa using hasDerivAt_pow 2 t)
    (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mul_ne_zero two_ne_zero ht)
    (by
      have hc : Tendsto e (𝓝 0) (𝓝 (e 0)) := hec.continuousAt.tendsto
      rw [he0] at hc
      exact hc.mono_left nhdsWithin_le_nhds)
    (by
      have hc : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_pow 2).tendsto (0 : ℝ))
      exact hc.mono_left nhdsWithin_le_nhds)
    hdiv
  have hzero : Tendsto (fun x : ℝ => e x / x ^ 2) (𝓝[≠] 0) (𝓝 0) :=
    ho.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hL : L / 2 = 0 := tendsto_nhds_unique hlh hzero
  have hL0 : L = 0 := by linarith
  -- `h' = e' + 2Bt` near `0`
  have hdh : deriv h =ᶠ[𝓝 0] fun t => e' t + 2 * B * t := by
    filter_upwards [hu] with y hy
    have h1 : HasDerivAt (fun t => B * t ^ 2) (B * (2 * y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_mul B
    have h2 : h = fun t => e t + B * t ^ 2 := by funext t; simp [he]
    rw [h2]
    have h3 : HasDerivAt (fun t => e t + B * t ^ 2) (e' y + B * (2 * y)) y := (hue y hy).add h1
    rw [h3.deriv]
    ring
  rw [hdh.deriv_eq]
  have h3 : HasDerivAt (fun t => e' t + 2 * B * t) (L + 2 * B) 0 := by
    have := hd2.hasDerivAt.add ((hasDerivAt_id (0 : ℝ)).const_mul (2 * B))
    convert this using 1
    · funext t; simp
    · simp [hLdef]
  rw [h3.deriv, hL0, zero_add]

/-- The Levi form from a second-order expansion (stub W10 helper). -/
theorem s5gr_hess_quadratic {k : ℂ → ℝ} (hk : ContDiffAt ℝ 2 k 0) {A : ℝ}
    (ho : (fun τ : ℂ => k τ - A * ‖τ‖ ^ 2) =o[𝓝 0] (fun τ : ℂ => ‖τ‖ ^ 2)) (v : ℂ) :
    fderiv ℝ (fderiv ℝ k) 0 v v = 2 * (A * ‖v‖ ^ 2) := by
  rw [← s5t53_hess_line hk v]
  have hL : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ) * v) := (Complex.ofRealCLM.contDiff).mul contDiff_const
  have hk' : ContDiffAt ℝ 2 k ((fun t : ℝ => (t : ℂ) * v) 0) := by simpa using hk
  apply s5gr_second_deriv (ContDiffAt.comp (g := k) (f := fun t : ℝ => (t : ℂ) * v) 0 hk' hL.contDiffAt)
  have hT : Tendsto (fun t : ℝ => (t : ℂ) * v) (𝓝 0) (𝓝 0) := by
    have h := (hL.continuous.tendsto 0)
    simpa using h
  have h1 := ho.comp_tendsto hT
  have h2 : (fun t : ℝ => ‖(t : ℂ) * v‖ ^ 2) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (‖v‖ ^ 2) (Eventually.of_forall fun t => le_of_eq ?_)
    simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    ring
  refine (h1.trans_isBigO h2).congr_left fun t => ?_
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- **Stub W10.** A real `C²` function with `k(τ) = A|τ|² + o(|τ|²)` at `0` has `∂_τ∂_τ̄ k(0) = A`. -/
theorem s5gr_levi_of_isLittleO {k : ℂ → ℝ} (hk : ContDiffAt ℝ 2 k 0) {A : ℝ}
    (ho : (fun τ : ℂ => k τ - A * ‖τ‖ ^ 2) =o[𝓝 0] (fun τ : ℂ => ‖τ‖ ^ 2)) :
    dz (dzbar fun τ : ℂ => ((k τ : ℝ) : ℂ)) 0 = (A : ℂ) := by
  have hc := s5l54_levi_curve (g := k) (γ := fun t : ℂ => t) (by simpa using hk) analyticAt_id
  obtain ⟨-, he⟩ := hc
  have hd : deriv (fun t : ℂ => t) 0 = 1 := deriv_id 0
  simp only [hd, smul_eq_mul, mul_one] at he
  rw [he, s5gr_hess_quadratic hk ho 1, s5gr_hess_quadratic hk ho I]
  simp only [norm_one, Complex.norm_I]
  push_cast
  ring

/-- **Stub W2.** If `T₁*T₁ + T₃*T₃ = 1`, `‖T₁‖ ≤ β` and `T₃` is onto, then `T₃*` is bounded below:
`(1 - β²)‖v‖² ≤ ‖T₃* v‖²`. -/
theorem s5gr_adj_lower {T₁ T₃ : ell2 →L[ℂ] ell2} {β : ℝ} (hβ0 : 0 ≤ β) (hT₁ : ‖T₁‖ ≤ β)
    (hid : ContinuousLinearMap.adjoint T₁ * T₁ + ContinuousLinearMap.adjoint T₃ * T₃ = 1)
    (hs : Function.Surjective T₃) (v : ell2) :
    (1 - β ^ 2) * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint T₃ v‖ ^ 2 := by
  obtain ⟨u, rfl⟩ := hs v
  have hu : ContinuousLinearMap.adjoint T₃ (T₃ u) = u - ContinuousLinearMap.adjoint T₁ (T₁ u) := by
    have h1 := congrArg (fun S : ell2 →L[ℂ] ell2 => S u) hid
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h1
    exact eq_sub_of_add_eq' h1
  have hre : RCLike.re (inner ℂ (u - ContinuousLinearMap.adjoint T₁ (T₁ u)) u) = ‖u‖ ^ 2 - ‖T₁ u‖ ^ 2 := by
    have e2 := T₁.apply_norm_sq_eq_inner_adjoint_left u
    rw [ContinuousLinearMap.comp_apply] at e2
    rw [inner_sub_left, map_sub, ← e2, inner_self_eq_norm_sq]
  -- `‖T₃ u‖² = ‖u‖² - ‖T₁ u‖²`
  have hv : ‖T₃ u‖ ^ 2 = ‖u‖ ^ 2 - ‖T₁ u‖ ^ 2 := by
    have e1 := T₃.apply_norm_sq_eq_inner_adjoint_left u
    rw [ContinuousLinearMap.comp_apply, hu, hre] at e1
    exact e1
  have hT1 : ‖T₁ u‖ ≤ β * ‖u‖ := (T₁.le_opNorm u).trans (mul_le_mul_of_nonneg_right hT₁ (norm_nonneg u))
  -- Cauchy–Schwarz: `re ⟪u - D T₁ u, u⟫ ≤ ‖u - D T₁ u‖ ‖u‖`
  have hcs : ‖u‖ ^ 2 - ‖T₁ u‖ ^ 2 ≤ ‖u - ContinuousLinearMap.adjoint T₁ (T₁ u)‖ * ‖u‖ := by
    have h1 := re_inner_le_norm (𝕜 := ℂ) (u - ContinuousLinearMap.adjoint T₁ (T₁ u)) u
    rw [hre] at h1
    exact h1
  rw [hu, hv]
  set x := ‖u‖ with hx
  set a := ‖T₁ u‖ with ha
  set b := ‖u - ContinuousLinearMap.adjoint T₁ (T₁ u)‖ with hb
  have hx0 : 0 ≤ x := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hxa : a ^ 2 ≤ x ^ 2 := by nlinarith [hv, sq_nonneg ‖T₃ u‖]
  rcases eq_or_lt_of_le hx0 with h0 | hpos
  · have : a = 0 := by nlinarith
    rw [← h0, this]
    nlinarith [sq_nonneg b]
  · have hβa : a ^ 2 ≤ β ^ 2 * x ^ 2 := by nlinarith
    have hbx : (x ^ 2 - a ^ 2) ^ 2 ≤ (b * x) ^ 2 := pow_le_pow_left₀ (by nlinarith) hcs 2
    have hx2 : 0 < x ^ 2 := by positivity
    have key : (1 - β ^ 2) * (x ^ 2 - a ^ 2) * x ^ 2 ≤ b ^ 2 * x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxa) (sub_nonneg.mpr hβa)]
    exact le_of_mul_le_mul_right key hx2

/-- `‖aX + βY‖² = |a|²‖X‖² + 2 Re(ā β ⟪X, Y⟫) + |β|²‖Y‖²` in `ℓ²`. -/
theorem s5gr_polar (X Y : ell2) (a β : ℂ) :
    ‖a • X + β • Y‖ ^ 2 = ‖a‖ ^ 2 * ‖X‖ ^ 2 + 2 * (conj a * β * inner ℂ X Y).re + ‖β‖ ^ 2 * ‖Y‖ ^ 2 := by
  rw [@norm_add_sq ℂ, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  simp only [RCLike.re_to_complex]
  ring_nf

/-- `‖√(j+1) z‖² = (j+1)‖z‖²`. -/
theorem s5gr_sqrt_norm_sq (j : ℕ) (z : ℂ) :
    ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * z‖ ^ 2 = ((j : ℝ) + 1) * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]

/-- An `ℓ²` vector from a square-summable sequence. -/
theorem s5gr_mk_apply {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) (n : ℕ) :
    (⟨x, gop_mem_of_summable hx⟩ : ell2) n = x n := rfl

/-- The `ℓ²` inner product as a series `Σ \bar x_n y_n`. -/
theorem s5gr_inner_tsum (X Y : ell2) : inner ℂ X Y = ∑' n, conj (X n) * Y n := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr fun n => by rw [gop_inner_apply]

/-- **Stub W1.** The `λ₀`-polarization of the generalized Grunsky equality (`thm_2_1`, null complement):
`Σ_k |k| \bar b_{k0} b_{kl} = b_{0l}`, rescaled and restricted to the columns `l = -(l'+1)`:
`B₁ᵗ c̄_- + B₃ᵗ c̄_+ = c_-`. -/
theorem s5gr_cross {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    let cm : ℕ → ℂ := fun j => (Real.sqrt ((j : ℝ) + 1) : ℂ) * b (-((j : ℤ) + 1)) 0
    let cp : ℕ → ℂ := fun j => (Real.sqrt ((j : ℝ) + 1) : ℂ) * b ((j : ℤ) + 1) 0
    ∀ l : ℕ, (∑' k : ℕ, (conj (cm k) * B1 b k l + conj (cp k) * B3 b k l)) = cm l := by
  intro b cm cp l
  have hsym := (grunsky_unitary h hF).1
  have hbd := gop_grunsky_bounds h hF
  obtain ⟨hs1, hs2, -⟩ := r22_sum h hF
  -- the four `ℓ²` vectors
  have hcm : Summable (fun j => ‖cm j‖ ^ 2) := by
    refine hs1.congr fun j => ?_
    show _ = ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2
    rw [s5gr_sqrt_norm_sq]; push_cast; ring
  have hcp : Summable (fun j => ‖cp j‖ ^ 2) := by
    refine hs2.congr fun j => ?_
    show _ = ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky f g ((j : ℤ) + 1) 0‖ ^ 2
    rw [s5gr_sqrt_norm_sq]; push_cast; ring
  have hym : Summable (fun j => ‖B1 b j l‖ ^ 2) := by
    refine ((hbd (B1 (grunsky f g)) (by simp)).1 l).congr fun j => ?_
    exact congrArg (fun z => ‖z‖ ^ 2) (hsym l j).1
  have hyp : Summable (fun j => ‖B3 b j l‖ ^ 2) := by
    refine ((hbd (B2 (grunsky f g)) (by simp)).1 l).congr fun j => ?_
    exact congrArg (fun z => ‖z‖ ^ 2) (hsym j l).2.2.symm
  set Xm : ell2 := ⟨cm, gop_mem_of_summable hcm⟩ with hXm
  set Xp : ell2 := ⟨cp, gop_mem_of_summable hcp⟩ with hXp
  set Ym : ell2 := ⟨fun j => B1 b j l, gop_mem_of_summable hym⟩ with hYm
  set Yp : ell2 := ⟨fun j => B3 b j l, gop_mem_of_summable hyp⟩ with hYp
  set L : ℤ := -((l : ℤ) + 1) with hL
  set sl : ℂ := (Real.sqrt ((l : ℝ) + 1) : ℂ) with hsl
  -- the generalized Grunsky equality, specialized to `λ = a e₀ + β√(l+1) e_L`
  have hEq := (thm_2_1 h (l + 1)).2.mpr hF
  have hE : ∀ a β : ℂ, ‖a • Xm + β • Ym‖ ^ 2 + ‖a • Xp + β • Yp‖ ^ 2 =
      ‖β‖ ^ 2 + 2 * (conj a * (b 0 0 * a + b 0 L * (β * sl))).re := by
    intro a β
    set lam : ℤ → ℂ := fun j => (if j = 0 then a else 0) + (if j = L then β * sl else 0) with hlam
    have hS0 : (0 : ℤ) ∈ Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ) := by
      simp only [Finset.mem_Icc]; constructor <;> omega
    have hSL : L ∈ Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ) := by
      simp only [Finset.mem_Icc, hL]; push_cast; constructor <;> omega
    have hL0 : L ≠ 0 := by rw [hL]; omega
    have hsum : ∀ k : ℤ, (∑ j ∈ Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ), b k j * lam j) =
        b k 0 * a + b k L * (β * sl) := by
      intro k
      simp only [hlam, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', hS0, hSL,
        if_true]
    have herr : (∑ k ∈ (Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ)).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) =
        ‖β‖ ^ 2 := by
      have e1 : ∀ k ∈ (Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ)).erase 0,
          ‖lam k‖ ^ 2 / |(k : ℝ)| = if k = L then ‖β‖ ^ 2 else 0 := by
        intro k hk
        have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
        simp only [hlam, if_neg hk0, zero_add]
        by_cases hkL : k = L
        · rw [if_pos hkL, if_pos hkL, norm_mul, mul_pow, hsl, Complex.norm_real,
            Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity), hkL, hL]
          push_cast
          rw [abs_of_neg (by linarith)]
          field_simp
          first | done | ring
        · rw [if_neg hkL, if_neg hkL, norm_zero]; first | done | simp
      rw [Finset.sum_congr rfl e1, Finset.sum_ite_eq' _ _ _]
      rw [if_pos (Finset.mem_erase.mpr ⟨hL0, hSL⟩)]
    have h1 : (∑' k : ℤ, |(k : ℝ)| * ‖∑ j ∈ Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ), b k j * lam j‖ ^ 2) =
        (∑ k ∈ (Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ)).erase 0, ‖lam k‖ ^ 2 / |(k : ℝ)|) +
          2 * (conj (lam 0) * ∑ j ∈ Finset.Icc (-((l + 1 : ℕ) : ℤ)) ((l + 1 : ℕ) : ℤ), b 0 j * lam j).re :=
      hEq lam
    rw [herr] at h1
    simp only [hsum] at h1
    have hlam0 : lam 0 = a := by simp [hlam, hL0.symm]
    rw [hlam0] at h1
    rw [← h1]
    -- the `ℤ` series as two `ℕ` series
    set F : ℤ → ℝ := fun k => |(k : ℝ)| * ‖b k 0 * a + b k L * (β * sl)‖ ^ 2 with hF'
    have hFp : ∀ j : ℕ, F (((j + 1 : ℕ) : ℤ)) = ‖(a • Xp + β • Yp) j‖ ^ 2 := by
      intro j
      rw [show (a • Xp + β • Yp) j = a * cp j + β * B3 b j l from rfl]
      show |((((j : ℤ) + 1) : ℤ) : ℝ)| * ‖b ((j : ℤ) + 1) 0 * a + b ((j : ℤ) + 1) L * (β * sl)‖ ^ 2 = _
      have e : a * cp j + β * B3 b j l = (Real.sqrt ((j : ℝ) + 1) : ℂ) *
          (b ((j : ℤ) + 1) 0 * a + b ((j : ℤ) + 1) L * (β * sl)) := by
        simp only [cp, B3, hsl, hL]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
      rw [e, s5gr_sqrt_norm_sq]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    have hFm : ∀ j : ℕ, F (-((j : ℤ) + 1)) = ‖(a • Xm + β • Ym) j‖ ^ 2 := by
      intro j
      rw [show (a • Xm + β • Ym) j = a * cm j + β * B1 b j l from rfl]
      show |((-((j : ℤ) + 1) : ℤ) : ℝ)| * ‖b (-((j : ℤ) + 1)) 0 * a + b (-((j : ℤ) + 1)) L * (β * sl)‖ ^ 2 = _
      have e : a * cm j + β * B1 b j l = (Real.sqrt ((j : ℝ) + 1) : ℂ) *
          (b (-((j : ℤ) + 1)) 0 * a + b (-((j : ℤ) + 1)) L * (β * sl)) := by
        simp only [cm, B1, hsl, hL]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
      rw [e, s5gr_sqrt_norm_sq]
      push_cast
      rw [abs_of_neg (by linarith)]
      ring
    have hF0 : F 0 = 0 := by simp [hF']
    have hpos : Summable (fun j : ℕ => F (((j + 1 : ℕ) : ℤ))) := by
      simp_rw [hFp]; exact gop_l2_summable _
    have hneg : Summable (fun j : ℕ => F (-((j : ℤ) + 1))) := by
      simp_rw [hFm]; exact gop_l2_summable _
    have hFs : Summable F := Summable.of_nat_of_neg_add_one ((summable_nat_add_iff 1).mp hpos) hneg
    rw [mg_tsum_int_split hFs hF0]
    simp_rw [hFp, hFm]
    rw [← gop_norm_sq, ← gop_norm_sq]
    ring
  -- extract the cross term
  set S : ℂ := inner ℂ Xm Ym + inner ℂ Xp Yp with hS
  have hlin : ∀ β : ℂ, (β * S).re = (β * (sl * b 0 L)).re := by
    intro β
    have h1 := hE 1 β
    have h2 := hE 1 0
    have h3 := hE 0 1
    rw [s5gr_polar, s5gr_polar] at h1 h2 h3
    simp only [map_one, map_zero, one_mul, zero_mul, norm_one, norm_zero, mul_zero, zero_add, add_zero,
      Complex.zero_re, mul_one, one_pow, zero_pow two_ne_zero, mul_comm _ (0 : ℂ)] at h1 h2 h3
    have e1 : (β * S).re = (β * inner ℂ Xm Ym).re + (β * inner ℂ Xp Yp).re := by
      rw [hS, mul_add, Complex.add_re]
    have e2 : (b 0 0 + b 0 L * (β * sl)).re = (b 0 0).re + (β * (sl * b 0 L)).re := by
      rw [Complex.add_re]; ring_nf
    rw [e2] at h1
    nlinarith [h1, h2, h3, e1]
  have hSre := hlin 1
  have hSim := hlin I
  simp only [one_mul, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hSre hSim
  have hSeq : S = sl * b 0 L := Complex.ext hSre (by linarith)
  -- the target series is `S`
  have hsplit : (∑' k : ℕ, (conj (cm k) * B1 b k l + conj (cp k) * B3 b k l)) = S := by
    rw [hS, s5gr_inner_tsum, s5gr_inner_tsum]
    have hs1' : Summable (fun k => conj (Xm k) * Ym k) := by
      have := lp.summable_inner (𝕜 := ℂ) Xm Ym
      simpa only [gop_inner_apply] using this
    have hs2' : Summable (fun k => conj (Xp k) * Yp k) := by
      have := lp.summable_inner (𝕜 := ℂ) Xp Yp
      simpa only [gop_inner_apply] using this
    rw [← hs1'.tsum_add hs2']
    first | done | rfl
  rw [hsplit, hSeq]
  -- `b_{0,L} = b_{L,0}`
  have hsy := ((grunsky_spec h).2 0 (l + 1)).2
  simp only [Nat.cast_zero, neg_zero, Nat.cast_add, Nat.cast_one] at hsy
  show sl * b 0 L = (Real.sqrt ((l : ℝ) + 1) : ℂ) * b (-((l : ℤ) + 1)) 0
  rw [hsl, hL]
  exact congrArg _ hsy

/-- Entries of the adjoint of a matrix operator: `(A* v)_l = Σ_k \bar A_{kl} v_k`. -/
theorem s5gr_adjoint_apply {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2) (v : ell2) (l : ℕ) :
    (ContinuousLinearMap.adjoint (gopOp A) v) l = ∑' k, conj (A k l) * v k := by
  have h1 : (ContinuousLinearMap.adjoint (gopOp A) v) l =
      inner ℂ (lp.single 2 l (1 : ℂ) : ell2) (ContinuousLinearMap.adjoint (gopOp A) v) := by
    rw [lp.inner_single_left]
    simp
  rw [h1, ContinuousLinearMap.adjoint_inner_right, s5gr_inner_tsum]
  refine tsum_congr fun k => ?_
  rw [gop_single_entry hrow hbd]

/-- A matrix bound gives the operator-norm bound. -/
theorem s5gr_opNorm_of_bound {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, A m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2) : ‖gopOp A‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro X
  have hs : ‖gopOp A X‖ ^ 2 ≤ c ^ 2 * ‖X‖ ^ 2 := by
    rw [gop_norm_sq, gop_norm_sq]
    have h1 := hB (fun n => X n) (gop_l2_summable X)
    simp only [gop_apply hrow hbd]
    exact h1
  nlinarith [norm_nonneg (gopOp A X), norm_nonneg X, mul_nonneg hc (norm_nonneg X)]

/-- **Stub W3.** Two-sided f-only bounds on the g-side energy `‖c_+‖²`, given `B₃` onto and `‖B₁‖ ≤ β < 1`.
Here `x = c_- - B₁ᵗ c̄_-`; the lower bound uses `‖B₂‖ ≤ 1` and the upper bound uses W2. -/
theorem s5gr_two_sided {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0)
    (hU : IsUnit (gopOp (B3 (grunsky f g)))) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hB1 : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 (grunsky f g) m n * x n‖ ^ 2 ≤ β ^ 2 * ∑' n, ‖x n‖ ^ 2) :
    let b := grunsky f g
    let cm : ℕ → ℂ := fun j => (Real.sqrt ((j : ℝ) + 1) : ℂ) * b (-((j : ℤ) + 1)) 0
    let cp : ℕ → ℂ := fun j => (Real.sqrt ((j : ℝ) + 1) : ℂ) * b ((j : ℤ) + 1) 0
    let x : ℕ → ℂ := fun l => cm l - ∑' k, conj (cm k) * B1 b k l
    Summable (fun l => ‖x l‖ ^ 2) ∧ Summable (fun j => ‖cp j‖ ^ 2) ∧
      (∑' l, ‖x l‖ ^ 2) ≤ ∑' j, ‖cp j‖ ^ 2 ∧ (1 - β ^ 2) * ∑' j, ‖cp j‖ ^ 2 ≤ ∑' l, ‖x l‖ ^ 2 := by
  intro b cm cp x
  have hbd := gop_grunsky_bounds h hF
  obtain ⟨hr1, hb1⟩ := hbd (B1 (grunsky f g)) (by simp)
  obtain ⟨hr3, hb3⟩ := hbd (B3 (grunsky f g)) (by simp)
  obtain ⟨-, -, -, hT3T, -⟩ := gop_blocks h hF
  obtain ⟨hs1, hs2, -⟩ := r22_sum h hF
  have hcp : Summable (fun j => ‖cp j‖ ^ 2) := by
    refine hs2.congr fun j => ?_
    show _ = ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky f g ((j : ℤ) + 1) 0‖ ^ 2
    rw [s5gr_sqrt_norm_sq]; push_cast; ring
  set Cp : ell2 := ⟨cp, gop_mem_of_summable hcp⟩ with hCp
  set T1 := gopOp (B1 (grunsky f g)) with hT1
  set T3 := gopOp (B3 (grunsky f g)) with hT3
  -- `x = conj (T₃* c_+)` (W1)
  have hcross := s5gr_cross h hF
  have hx : ∀ l, x l = conj ((ContinuousLinearMap.adjoint T3 Cp) l) := by
    intro l
    rw [hT3, s5gr_adjoint_apply hr3 hb3 Cp l]
    have hc := hcross l
    have hsA : Summable (fun k => conj (cm k) * B1 b k l) := by
      have hcm : Summable (fun j => ‖cm j‖ ^ 2) := by
        refine hs1.congr fun j => ?_
        show _ = ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2
        rw [s5gr_sqrt_norm_sq]; push_cast; ring
      have hcol : Summable (fun j => ‖B1 b j l‖ ^ 2) := by
        refine (hr1 l).congr fun j => ?_
        exact congrArg (fun z => ‖z‖ ^ 2) ((grunsky_unitary h hF).1 l j).1
      refine (bergman_pair_summable (x := fun k => conj (cm k)) (y := fun k => B1 b k l) ?_ hcol).of_norm
      simpa only [Complex.norm_conj] using hcm
    have hsB : Summable (fun k => conj (cp k) * B3 b k l) := by
      have hcol : Summable (fun j => ‖B3 b j l‖ ^ 2) := by
        refine ((hbd (B2 (grunsky f g)) (by simp)).1 l).congr fun j => ?_
        exact congrArg (fun z => ‖z‖ ^ 2) ((grunsky_unitary h hF).1 j l).2.2.symm
      refine (bergman_pair_summable (x := fun k => conj (cp k)) (y := fun k => B3 b k l) ?_ hcol).of_norm
      simpa only [Complex.norm_conj] using hcp
    rw [hsA.tsum_add hsB] at hc
    have hx' : x l = ∑' k, conj (cp k) * B3 b k l := by
      show cm l - (∑' k, conj (cm k) * B1 b k l) = _
      linear_combination -hc
    rw [hx', Complex.conj_tsum]
    refine tsum_congr fun k => ?_
    show conj (cp k) * B3 b k l = conj (conj (B3 b k l) * cp k)
    rw [map_mul (starRingEnd ℂ) (conj (B3 b k l)) (cp k), Complex.conj_conj, mul_comm]
  have hxs : Summable (fun l => ‖x l‖ ^ 2) :=
    (gop_l2_summable (ContinuousLinearMap.adjoint T3 Cp)).congr fun l => by rw [hx l, Complex.norm_conj]
  have hxn : (∑' l, ‖x l‖ ^ 2) = ‖ContinuousLinearMap.adjoint T3 Cp‖ ^ 2 := by
    rw [gop_norm_sq]
    exact tsum_congr fun l => by rw [hx l, Complex.norm_conj]
  have hcpn : (∑' j, ‖cp j‖ ^ 2) = ‖Cp‖ ^ 2 := (gop_norm_sq Cp).symm
  have hT3n : ‖T3‖ ≤ 1 := by
    refine s5gr_opNorm_of_bound hr3 hb3 zero_le_one fun y hy => ?_
    have := (eq_2_2 h hF).2.2.2.2 (B3 (grunsky f g)) (by simp) y hy
    simpa using this
  have hT1n : ‖T1‖ ≤ β := s5gr_opNorm_of_bound hr1 hb1 hβ0 hB1
  have hsurj : Function.Surjective T3 := by
    obtain ⟨u, hu⟩ := hU
    intro v
    refine ⟨(↑u⁻¹ : ell2 →L[ℂ] ell2) v, ?_⟩
    rw [← hu, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
  have hup := s5gr_adj_lower hβ0 hT1n hT3T hsurj Cp
  have hlo : ‖ContinuousLinearMap.adjoint T3 Cp‖ ≤ ‖Cp‖ := by
    calc ‖ContinuousLinearMap.adjoint T3 Cp‖ ≤ ‖ContinuousLinearMap.adjoint T3‖ * ‖Cp‖ :=
          (ContinuousLinearMap.adjoint T3).le_opNorm Cp
      _ ≤ 1 * ‖Cp‖ := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul_of_nonneg_right hT3n (norm_nonneg _)
      _ = ‖Cp‖ := one_mul _
  refine ⟨hxs, hcp, ?_, ?_⟩
  · rw [hxn, hcpn]
    exact pow_le_pow_left₀ (norm_nonneg _) hlo 2
  · rw [hxn, hcpn]
    exact hup

/-- Möbius difference quotient: `σz - σw = (pu - qr)(z - w)/((rz + u)(rw + u))`. -/
theorem s5gr_mob_sub {p q r u z w : ℂ} (hz : r * z + u ≠ 0) (hw : r * w + u ≠ 0) :
    (p * z + q) / (r * z + u) - (p * w + q) / (r * w + u) =
      (p * u - q * r) * (z - w) / ((r * z + u) * (r * w + u)) := by
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- Derivative of a Möbius map. -/
theorem s5gr_mob_hasDerivAt {p q r u z : ℂ} (hz : r * z + u ≠ 0) :
    HasDerivAt (fun z => (p * z + q) / (r * z + u)) ((p * u - q * r) / (r * z + u) ^ 2) z := by
  have h1 : HasDerivAt (fun z => p * z + q) p z := by
    simpa using ((hasDerivAt_id z).const_mul p).add_const q
  have h2 : HasDerivAt (fun z => r * z + u) r z := by
    simpa using ((hasDerivAt_id z).const_mul r).add_const u
  convert h1.div h2 hz using 1
  ring

/-- `𝔻*` is open. -/
theorem s5gr_ext_open : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm

/-- A Möbius bijection `T` of `𝔻*` onto `𝔻`: conformal, with derivative `(pu - qr)/(rz + u)²`. -/
theorem s5gr_T_conf {T : ℂ → ℂ} {p q r u : ℂ} {V : Set ℂ} (hTd : ∀ z ∈ unitDiscExterior, r * z + u ≠ 0)
    (hT : ∀ z ∈ unitDiscExterior, T z = (p * z + q) / (r * z + u)) (hTb : BijOn T unitDiscExterior V) :
    IsConformalOnto T unitDiscExterior V ∧
      ∀ z ∈ unitDiscExterior, HasDerivAt T ((p * u - q * r) / (r * z + u) ^ 2) z := by
  have hd : ∀ z ∈ unitDiscExterior, HasDerivAt T ((p * u - q * r) / (r * z + u) ^ 2) z := by
    intro z hz
    have hev : T =ᶠ[𝓝 z] fun z => (p * z + q) / (r * z + u) := by
      filter_upwards [s5gr_ext_open.mem_nhds hz] with v hv
      exact hT v hv
    exact (s5gr_mob_hasDerivAt (hTd z hz)).congr_of_eventuallyEq hev
  exact ⟨⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, hTb.injOn, hTb.image_eq⟩, hd⟩

/-- Change of variables under a conformal map `f : U → V` (Bochner, any Banach target, no integrability). -/
theorem s5gr_cov_gen {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hf : IsConformalOnto f U V)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E) :
    (∫ x in V, F x) = ∫ x in U, (‖deriv f x‖ ^ 2) • F (f x) := by
  have hder : ∀ x ∈ U, HasFDerivWithinAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f x)).restrictScalars ℝ) U x :=
    fun x hx => ((hf.1.differentiableAt (hU.mem_nhds hx)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hder hf.2.1 F
  rw [hf.2.2] at hcv
  rw [hcv]
  refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (by positivity)]

/-- The inverse of a conformal map `f : U → V`: `f⁻¹(f w) = w` and `(f⁻¹)'(f w) f'(w) = 1`. -/
theorem s5gr_inv_gen {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hf : IsConformalOnto f U V) :
    IsConformalOnto (Function.invFunOn f U) V U ∧
      ∀ w ∈ U, Function.invFunOn f U (f w) = w ∧ deriv (Function.invFunOn f U) (f w) * deriv f w = 1 := by
  set ρ := Function.invFunOn f U with hρ
  have hρc : IsConformalOnto ρ V U := hf.symm hU
  refine ⟨hρc, fun w hw => ⟨hf.2.1.leftInvOn_invFunOn hw, ?_⟩⟩
  have hρd : DifferentiableAt ℂ ρ (f w) := hf.differentiableAt_invFunOn hU hw
  have hfd : DifferentiableAt ℂ f w := hf.1.differentiableAt (hU.mem_nhds hw)
  have hcomp := hρd.hasDerivAt.comp w hfd.hasDerivAt
  have hev : (ρ ∘ f) =ᶠ[𝓝 w] id := by
    filter_upwards [hU.mem_nhds hw] with v hv
    exact hf.2.1.leftInvOn_invFunOn hv
  have hid : HasDerivAt (ρ ∘ f) 1 w := (hasDerivAt_id w).congr_of_eventuallyEq hev
  exact hcomp.unique hid

/-- The punctured disc has the same restricted measure as the disc. -/
theorem s5gr_punct_measure : volume.restrict (unitDisc \ {(0 : ℂ)}) = volume.restrict unitDisc := by
  apply Measure.restrict_congr_set
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  simp [hz]

/-- A punctured disc has the same restricted measure as the disc. -/
theorem s5gr_punct_measure_at (ω : ℂ) : volume.restrict (unitDisc \ {ω}) = volume.restrict unitDisc := by
  apply Measure.restrict_congr_set
  filter_upwards [volume.ae_ne ω] with z hz
  simp [hz]

/-- Inversion is conformal from `𝔻*` onto `𝔻 ∖ {0}`. -/
theorem s5gr_inv_ext_conf : IsConformalOnto (fun z : ℂ => z⁻¹) unitDiscExterior (unitDisc \ {0}) := by
  refine ⟨?_, inv_injective.injOn, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; norm_num [unitDiscExterior] at hz
    exact (differentiableAt_inv hz0).differentiableWithinAt
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact a21_inv_exterior hz
    · intro hw
      exact ⟨w⁻¹, a21_inv_punctured hw, inv_inv w⟩

/-- `K₄` is symmetric. -/
theorem s5gr_kerK4_symm (g : ℂ → ℂ) (z w : ℂ) : kerK4 g z w = kerK4 g w z := by
  by_cases h : z = w
  · rw [h]
  · rw [kerK4_of_ne g h, kerK4_of_ne g (Ne.symm h)]
    have e1 : (z - w) ^ 2 = (w - z) ^ 2 := by ring
    have e2 : (g z - g w) ^ 2 = (g w - g z) ^ 2 := by ring
    rw [e1, e2, mul_comm (deriv g z)]

/-- The algebra behind `s5gr_K1_lambda`. -/
theorem s5gr_K1_alg {P z w a A B A' B' : ℂ} (hzw : z - w ≠ 0) (hAB : A - B ≠ 0) (hA : a * A + 1 ≠ 0)
    (hB : a * B + 1 ≠ 0) :
    P * (1 / (z - w) ^ 2 - (1 * 1 - 0 * a) / (a * A + 1) ^ 2 * A' * ((1 * 1 - 0 * a) / (a * B + 1) ^ 2 * B') /
        (A / (a * A + 1) - B / (a * B + 1)) ^ 2) =
      P * (1 / (z - w) ^ 2 - A' * B' / (A - B) ^ 2) := by
  rw [div_sub_div _ _ hA hB]
  have e : A * (a * B + 1) - (a * A + 1) * B = A - B := by ring
  rw [e]
  field_simp
  ring

/-- `K₁` is unchanged by `f' = λ_a ∘ f`, `λ_a(w) = w/(aw + 1)`. -/
theorem s5gr_K1_lambda {f f' : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) {a : ℂ}
    (hd : ∀ z ∈ unitDisc, a * f z + 1 ≠ 0) (hf' : ∀ z ∈ unitDisc, f' z = lambdaW a (f z))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    kerK1 f' z w = kerK1 f z w := by
  have hgd : ∀ v ∈ unitDisc, HasDerivAt f' ((1 * 1 - 0 * a) / (a * f v + 1) ^ 2 * deriv f v) v := by
    intro v hv
    have h1 := (hf.differentiableAt (isOpen_ball.mem_nhds hv)).hasDerivAt
    have h2 := (s5gr_mob_hasDerivAt (p := 1) (q := 0) (r := a) (u := 1) (hd v hv)).comp v h1
    have hev : f' =ᶠ[𝓝 v] fun v => (1 * f v + 0) / (a * f v + 1) := by
      filter_upwards [isOpen_ball.mem_nhds hv] with t ht
      rw [hf' t ht]
      simp [lambdaW]
    exact h2.congr_of_eventuallyEq hev
  have hAB : f z - f w ≠ 0 := sub_ne_zero.mpr fun h => hzw (hfi hz hw h)
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hA := hd z hz
  have hB := hd w hw
  rw [kerK1_of_ne f' hzw, kerK1_of_ne f hzw, (hgd z hz).deriv, (hgd w hw).deriv, hf' z hz, hf' w hw]
  unfold lambdaW
  generalize f z = A at hAB hA ⊢
  generalize f w = B at hAB hB ⊢
  generalize deriv f z = A'
  generalize deriv f w = B'
  exact s5gr_K1_alg hzw' hAB hA hB

/-- **Stub W5.** `B₁` depends only on the interior map up to `λ_a(w) = w/(aw + 1)`:
if `f' = λ_a ∘ f` on `𝔻`, then the `f`–`f` coefficients `b_{-m,-n}` (`m, n ≥ 1`) agree. -/
theorem s5gr_B1_lambda {f g f' g' : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (h' : IsNormalizedDisjointPair f' g') {a : ℂ} (hd : ∀ z ∈ unitDisc, a * f z + 1 ≠ 0)
    (hf' : ∀ z ∈ unitDisc, f' z = lambdaW a (f z)) :
    ∀ m n, B1 (grunsky f' g') m n = B1 (grunsky f g) m n := by
  intro m n
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℂ, c = fun p q => 1 / π * (((p + 1) * (q + 1) : ℕ) : ℂ) *
      grunsky f g (-(p + 1 : ℤ)) (-(q + 1 : ℤ)) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c : ℕ → ℕ → ℂ, c = fun p q => 1 / π * (((p + 1) * (q + 1) : ℕ) : ℂ) *
      grunsky f' g' (-(p + 1 : ℤ)) (-(q + 1 : ℤ)) := ⟨_, rfl⟩
  have hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (kerK1 f z w) := by
    intro z hz w hw hzw
    rw [hc]
    exact s2c_kernels_K1 h z hz w hw hzw
  have hK' : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => c' p.1 p.2 * z ^ p.1 * w ^ p.2) (kerK1 f' z w) := by
    intro z hz w hw hzw
    rw [hc']
    exact s2c_kernels_K1 h' z hz w hw hzw
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun z w => ∑' p : ℕ × ℕ, c p.1 p.2 * z ^ p.1 * w ^ p.2 := ⟨_, rfl⟩
  obtain ⟨F', hF'def⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun z w => ∑' p : ℕ × ℕ, c' p.1 p.2 * z ^ p.1 * w ^ p.2 :=
    ⟨_, rfl⟩
  have hFs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w) := by
    rw [hFdef]
    exact s2c_bidisk_hasSum fun z hz w hw hzw => (hK z hz w hw hzw).summable
  have hFs' : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, HasSum (fun p : ℕ × ℕ => c' p.1 p.2 * z ^ p.1 * w ^ p.2) (F' z w) := by
    rw [hF'def]
    exact s2c_bidisk_hasSum fun z hz w hw hzw => (hK' z hz w hw hzw).summable
  have hoff : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → F z w = F' z w := by
    intro z hz w hw hzw
    rw [(hFs z hz w hw).unique (hK z hz w hw hzw), (hFs' z hz w hw).unique (hK' z hz w hw hzw)]
    exact (s5gr_K1_lambda h.1 h.2.1 hd hf' hz hw hzw).symm
  have hc1 := s2c_bidisk_continuousOn hFs
  have hc2 := s2c_bidisk_continuousOn hFs'
  have hall : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, F z w = F' z w := by
    intro z hz w hw
    by_cases hzw : z = w
    · subst hzw
      have hn : unitDisc ×ˢ unitDisc ∈ 𝓝 (z, z) := prod_mem_nhds (isOpen_ball.mem_nhds hz) (isOpen_ball.mem_nhds hz)
      have hl : Continuous (fun v : ℂ => (z, v)) := continuous_const.prodMk continuous_id
      have ht1 : ContinuousAt (fun v => F z v) z :=
        ContinuousAt.comp (g := fun x : ℂ × ℂ => F x.1 x.2) (hc1.continuousAt hn) hl.continuousAt
      have ht2 : ContinuousAt (fun v => F' z v) z :=
        ContinuousAt.comp (g := fun x : ℂ × ℂ => F' x.1 x.2) (hc2.continuousAt hn) hl.continuousAt
      have hev : (fun v => F z v) =ᶠ[𝓝[≠] z] fun v => F' z v := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with v hv hvD
        exact hoff z hz v hvD (Ne.symm hv)
      exact tendsto_nhds_unique (ht1.tendsto.mono_left nhdsWithin_le_nhds)
        ((ht2.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
    · exact hoff z hz w hw hzw
  have hcc : c = c' := double_powerSeries_coeff_unique hFs fun z hz w hw => by
    rw [hall z hz w hw]
    exact hFs' z hz w hw
  have e := congrFun (congrFun hcc m) n
  rw [hc, hc'] at e
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : (1 / π : ℂ) * (((m + 1) * (n + 1) : ℕ) : ℂ) ≠ 0 := by
    apply mul_ne_zero (one_div_ne_zero hπ)
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos n)).ne'
  have hb := mul_left_cancel₀ hk e
  unfold B1
  rw [hb]

/-- The disc automorphism `M_ω(t) = (t + ω)/(ω̄ t + 1)`: `|M_ω t| < 1` on `𝔻`. -/
theorem s5gr_aut_norm {ω t : ℂ} (hω : ω ∈ unitDisc) (ht : t ∈ unitDisc) :
    conj ω * t + 1 ≠ 0 ∧ (t + ω) / (conj ω * t + 1) ∈ unitDisc := by
  have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
  have hden : conj ω * t + 1 ≠ 0 := by
    intro h
    have h1 : ‖conj ω * t‖ = 1 := by
      have : conj ω * t = -1 := by linear_combination h
      rw [this, norm_neg, norm_one]
    rw [norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg ω, norm_nonneg t, mul_le_mul hω1.le ht1.le (norm_nonneg t) zero_le_one]
  refine ⟨hden, ?_⟩
  apply mem_ball_zero_iff.mpr
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have key : ‖conj ω * t + 1‖ ^ 2 - ‖t + ω‖ ^ 2 = (1 - ‖ω‖ ^ 2) * (1 - ‖t‖ ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  have hpos : 0 < (1 - ‖ω‖ ^ 2) * (1 - ‖t‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg ω, norm_nonneg t]
  nlinarith [norm_nonneg (conj ω * t + 1), norm_nonneg (t + ω)]

/-- `M_{-ω} ∘ M_ω = id` on `𝔻`. -/
theorem s5gr_aut_inv {ω t : ℂ} (hω : ω ∈ unitDisc) (ht : t ∈ unitDisc) :
    ((t + ω) / (conj ω * t + 1) + -ω) / (conj (-ω) * ((t + ω) / (conj ω * t + 1)) + 1) = t := by
  obtain ⟨hden, -⟩ := s5gr_aut_norm hω ht
  have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have hk : 1 - conj ω * ω ≠ 0 := by
    intro h
    have e : conj ω * ω = ((‖ω‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e] at h
    have h2 : (‖ω‖ ^ 2 : ℝ) = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    nlinarith [norm_nonneg ω]
  set s := (t + ω) / (conj ω * t + 1) with hsdef
  have hs : s * (conj ω * t + 1) = t + ω := by rw [hsdef, div_mul_cancel₀ _ hden]
  have hne : conj (-ω) * s + 1 ≠ 0 := by
    intro h
    apply hk
    rw [map_neg] at h
    linear_combination (conj ω * t + 1) * h + conj ω * hs
  rw [div_eq_iff hne, map_neg]
  linear_combination hs

/-- The disc automorphism `M_ω` is differentiable on `𝔻`. -/
theorem s5gr_aut_diff {ω : ℂ} (hω : ω ∈ unitDisc) :
    DifferentiableOn ℂ (fun t => (t + ω) / (conj ω * t + 1)) unitDisc := by
  intro t ht
  obtain ⟨hden, -⟩ := s5gr_aut_norm hω ht
  have h := s5gr_mob_hasDerivAt (p := 1) (q := ω) (r := conj ω) (u := 1) hden
  simp only [one_mul] at h
  exact h.differentiableAt.differentiableWithinAt

/-- `M_ω` maps `𝔻` onto `𝔻` conformally, and `𝔻 ∖ {0}` onto `𝔻 ∖ {ω}`. -/
theorem s5gr_aut_conf {ω : ℂ} (hω : ω ∈ unitDisc) :
    IsConformalOnto (fun t => (t + ω) / (conj ω * t + 1)) unitDisc unitDisc ∧
      IsConformalOnto (fun t => (t + ω) / (conj ω * t + 1)) (unitDisc \ {0}) (unitDisc \ {ω}) := by
  have hω' : -ω ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr; rw [norm_neg]; exact mem_ball_zero_iff.mp hω
  have hinj : InjOn (fun t => (t + ω) / (conj ω * t + 1)) unitDisc := by
    intro a ha b hb hab
    rw [← s5gr_aut_inv hω ha, ← s5gr_aut_inv hω hb]
    simp only at hab
    rw [hab]
  have hback : ∀ s ∈ unitDisc, (s + -ω) / (conj (-ω) * s + 1) ∈ unitDisc ∧
      ((s + -ω) / (conj (-ω) * s + 1) + ω) / (conj ω * ((s + -ω) / (conj (-ω) * s + 1)) + 1) = s := by
    intro s hs
    refine ⟨(s5gr_aut_norm hω' hs).2, ?_⟩
    have h := s5gr_aut_inv hω' hs
    simp only [neg_neg] at h
    exact h
  have hm0 : (fun t => (t + ω) / (conj ω * t + 1)) 0 = ω := by simp
  refine ⟨⟨s5gr_aut_diff hω, hinj, ?_⟩, ⟨(s5gr_aut_diff hω).mono sdiff_subset, hinj.mono sdiff_subset, ?_⟩⟩
  · ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (s5gr_aut_norm hω ht).2
    · intro hs
      exact ⟨_, (hback s hs).1, (hback s hs).2⟩
  · ext s
    constructor
    · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
      refine ⟨(s5gr_aut_norm hω ht).2, fun h => ht0 ?_⟩
      have h' : (fun t => (t + ω) / (conj ω * t + 1)) t = (fun t => (t + ω) / (conj ω * t + 1)) 0 := by
        rw [hm0]; exact h
      exact hinj ht (mem_ball_self one_pos) h'
    · rintro ⟨hs, hsω⟩
      refine ⟨_, ⟨(hback s hs).1, fun h0 => hsω ?_⟩, (hback s hs).2⟩
      have h1 := (hback s hs).2
      rw [h0] at h1
      simp only [mem_singleton_iff] at h0 ⊢
      rw [← h1]
      simp

/-- The removable singularity at an interior point of `𝔻` for `A²` functions. -/
theorem s5gr_remove_pt {ψ : ℂ → ℂ} {ω : ℂ} (hω : ω ∈ unitDisc) (hψ : ψ ∈ A21fun (unitDisc \ {ω})) :
    ∃ g : ℂ → ℂ, g ∈ A21fun unitDisc ∧ EqOn g ψ (unitDisc \ {ω}) := by
  have hω' : -ω ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr; rw [norm_neg]; exact mem_ball_zero_iff.mp hω
  set m : ℂ → ℂ := fun t => (t + ω) / (conj ω * t + 1) with hm
  set n : ℂ → ℂ := fun t => (t + -ω) / (conj (-ω) * t + 1) with hn
  obtain ⟨-, hmc⟩ := s5gr_aut_conf hω
  obtain ⟨hnc, -⟩ := s5gr_aut_conf hω'
  have hU0 : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hpull : (fun t => ψ (m t) * deriv m t) ∈ A21fun (unitDisc \ {0}) := a21_pullback hU0 hmc hψ
  obtain ⟨gt, hgtA, hgteq, -⟩ := a21_remove_puncture hpull
  refine ⟨fun s => gt (n s) * deriv n s, a21_pullback isOpen_ball hnc hgtA, fun s hs => ?_⟩
  have hsD : s ∈ unitDisc := hs.1
  have hns : n s ∈ unitDisc := (s5gr_aut_norm hω' hsD).2
  have hmn : ∀ v ∈ unitDisc, m (n v) = v := by
    intro v hv
    have h := s5gr_aut_inv hω' hv
    simp only [neg_neg] at h
    exact h
  have hns0 : n s ≠ 0 := by
    intro h0
    apply hs.2
    have h1 := hmn s hsD
    rw [h0] at h1
    simp only [mem_singleton_iff]
    rw [← h1]
    simp [hm]
  simp only
  rw [hgteq ⟨hns, hns0⟩]
  simp only
  rw [hmn s hsD]
  -- `m'(n s) n'(s) = 1`
  have hmd : DifferentiableAt ℂ m (n s) := (s5gr_aut_diff hω).differentiableAt (isOpen_ball.mem_nhds hns)
  have hnd : DifferentiableAt ℂ n s := (s5gr_aut_diff hω').differentiableAt (isOpen_ball.mem_nhds hsD)
  have hcomp := hmd.hasDerivAt.comp s hnd.hasDerivAt
  have hev : (m ∘ n) =ᶠ[𝓝 s] id := by
    filter_upwards [isOpen_ball.mem_nhds hsD] with v hv
    exact hmn v hv
  have hid : HasDerivAt (m ∘ n) 1 s := (hasDerivAt_id s).congr_of_eventuallyEq hev
  have h1 := hcomp.unique hid
  rw [mul_assoc, h1, mul_one]

/-- The algebra behind `s5gr_K4_cov`. -/
theorem s5gr_K4_alg {P z w D1 D2 Δ a b A B E1 E2 Δ' : ℂ} (hzw : z - w ≠ 0) (hD1 : D1 ≠ 0) (hD2 : D2 ≠ 0)
    (hΔ : Δ ≠ 0) (hab : a - b ≠ 0) (hE1 : E1 ≠ 0) (hE2 : E2 ≠ 0) (hΔ' : Δ' ≠ 0) :
    P * (1 / (z - w) ^ 2 - Δ' / E1 ^ 2 * (A * (Δ / D1 ^ 2)) * (Δ' / E2 ^ 2 * (B * (Δ / D2 ^ 2))) /
        (Δ' * (a - b) / (E1 * E2)) ^ 2) =
      Δ / D1 ^ 2 * (Δ / D2 ^ 2) * (P * (1 / (Δ * (z - w) / (D1 * D2)) ^ 2 - A * B / (a - b) ^ 2)) := by
  field_simp

/-- **Covariance in the disc chart.** If `g' = 1/(φ ∘ T + a)` on `𝔻*` with `T` a Möbius bijection onto `𝔻`, then
`K₄_{g'}(z, w) = T'(z) T'(w) K₁_φ(Tz, Tw)` off the diagonal. -/
theorem s5gr_K4_disc_cov {g' φ T : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc)
    {p q r u : ℂ} (hpq : p * u - q * r ≠ 0) (hTd : ∀ z ∈ unitDiscExterior, r * z + u ≠ 0)
    (hT : ∀ z ∈ unitDiscExterior, T z = (p * z + q) / (r * z + u)) {ω : ℂ}
    (hTb : BijOn T unitDiscExterior (unitDisc \ {ω})) {a : ℂ} (hg' : ∀ z ∈ unitDiscExterior, φ (T z) + a ≠ 0 ∧ g' z = 1 / (φ (T z) + a))
    {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) (hzw : z ≠ w) :
    kerK4 g' z w = deriv T z * deriv T w * kerK1 φ (T z) (T w) := by
  obtain ⟨-, hd⟩ := s5gr_T_conf hTd hT hTb
  have hZ : T z ∈ unitDisc := (hTb.mapsTo hz).1
  have hW : T w ∈ unitDisc := (hTb.mapsTo hw).1
  have hZW : T z ≠ T w := fun h => hzw (hTb.injOn hz hw h)
  have hab : φ (T z) ≠ φ (T w) := fun h => hZW (hφi hZ hW h)
  have hMd : ∀ v ∈ unitDiscExterior, 1 * φ (T v) + a ≠ 0 := fun v hv => by rw [one_mul]; exact (hg' v hv).1
  have hgd : ∀ v ∈ unitDiscExterior, HasDerivAt g' ((0 * a - 1 * 1) / (1 * φ (T v) + a) ^ 2 *
      (deriv φ (T v) * ((p * u - q * r) / (r * v + u) ^ 2))) v := by
    intro v hv
    have hV : T v ∈ unitDisc := (hTb.mapsTo hv).1
    have h1 : HasDerivAt (fun v => φ (T v)) (deriv φ (T v) * ((p * u - q * r) / (r * v + u) ^ 2)) v :=
      (hφd.differentiableAt (isOpen_ball.mem_nhds hV)).hasDerivAt.comp v (hd v hv)
    have h2 := (s5gr_mob_hasDerivAt (p := 0) (q := 1) (hMd v hv)).comp v h1
    have hev : g' =ᶠ[𝓝 v] fun v => (0 * φ (T v) + 1) / (1 * φ (T v) + a) := by
      filter_upwards [s5gr_ext_open.mem_nhds hv] with t ht
      rw [(hg' t ht).2]
      ring
    exact h2.congr_of_eventuallyEq hev
  have hdiff : T z - T w = (p * u - q * r) * (z - w) / ((r * z + u) * (r * w + u)) := by
    rw [hT z hz, hT w hw]
    exact s5gr_mob_sub (hTd z hz) (hTd w hw)
  have hgz : g' z = (0 * φ (T z) + 1) / (1 * φ (T z) + a) := by rw [(hg' z hz).2]; ring
  have hgw : g' w = (0 * φ (T w) + 1) / (1 * φ (T w) + a) := by rw [(hg' w hw).2]; ring
  rw [kerK4_of_ne g' hzw, kerK1_of_ne φ hZW, (hgd z hz).deriv, (hgd w hw).deriv, (hd z hz).deriv,
    (hd w hw).deriv, hgz, hgw, s5gr_mob_sub (hMd z hz) (hMd w hw), hdiff]
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hab' : φ (T z) - φ (T w) ≠ 0 := sub_ne_zero.mpr hab
  have hMz := hMd z hz
  have hMw := hMd w hw
  have hz0 := hTd z hz
  have hw0 := hTd w hw
  have hΔ' : (0 : ℂ) * a - 1 * 1 ≠ 0 := by norm_num
  generalize φ (T z) = A at hab' hMz ⊢
  generalize φ (T w) = B at hab' hMw ⊢
  generalize deriv φ (T z) = A'
  generalize deriv φ (T w) = B'
  exact s5gr_K4_alg hzw' hz0 hw0 hpq hab' hMz hMw hΔ'

/-- `B₄` of a normalized null pair is a bounded matrix, and `gopOp B₄` acts by the matrix. -/
theorem s5gr_B4_op {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    IsBoundedMat (B4 (grunsky f g)) ∧
      ∀ (x : ell2) (m : ℕ), gopOp (B4 (grunsky f g)) x m = ∑' n, B4 (grunsky f g) m n * x n := by
  obtain ⟨hr, hb⟩ := gop_grunsky_bounds h hF (B4 (grunsky f g)) (by simp)
  exact ⟨pmb_of_operator _ (gop_single_entry hr hb), fun x m => gop_apply hr hb x m⟩

/-- The `B₄` operator kernel is `K₄` off the diagonal (generic form of `s3st_B4_kernel_off`). -/
theorem s5gr_kernel_off {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) (hzw : z ≠ w) :
    s3st_kernel (gopOp (B4 (grunsky f g))) z w = kerK4 g z w := by
  let B := B4 (grunsky f g)
  have hB : IsBoundedMat B := (s5gr_B4_op h hF).1
  have hs := e24_hK4 h hF z hz w hw hzw
  rw [s3st_kernel_series _ hz w, ← hs.tsum_eq, hs.summable.tsum_prod]
  apply tsum_congr
  intro m
  rw [pmb_apply hB]
  change (∑' n, B m n * s3st_vector w n) * basisF m z = _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [s3st_vector_apply hw]
  ring

/-- The column expansion `K₄(z, w) = Σ_n (B₄ e_z)_n f_n(w)` for `w ≠ z`. -/
theorem s5gr_K4_col {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {z w : ℂ}
    (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) (hwz : w ≠ z) :
    HasSum (fun n => (gopOp (B4 (grunsky f g)) (s3st_vector z)) n * basisF n w) (kerK4 g z w) := by
  have hs := bergman_pair_summable (gop_l2_summable (gopOp (B4 (grunsky f g)) (s3st_vector z)))
    (s3st_basisF_sq hw)
  have h1 := hs.of_norm.hasSum
  rwa [← s3st_kernel_series _ hw z, s5gr_kernel_off h hF hw hz hwz, s5gr_kerK4_symm] at h1

/-- **The kernel pairing.** For `H = Σ Y_n f_n` in `A²(𝔻*)`:
`∫_{𝔻*} K₄(z, w) \overline{H(w)} = Σ_m \overline{(B₄^* Y)_m} f_m(z)`. -/
theorem s5gr_K4_pair {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {Y : ell2} {H : ℂ → ℂ}
    (hH : ∀ u ∈ unitDiscExterior, HasSum (fun n => Y n * basisF n u) (H u)) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, kerK4 g z w * conj (H w)) =
      ∑' m, conj ((ContinuousLinearMap.adjoint (gopOp (B4 (grunsky f g))) Y) m) * basisF m z := by
  set T := gopOp (B4 (grunsky f g)) with hT
  have hp := e24_ext_pair (F := fun w => kerK4 g z w) (G := H) (x := fun n => T (s3st_vector z) n)
    (y := fun n => Y n) (gop_l2_summable _) (gop_l2_summable Y) (E := {z}) (finite_singleton z)
    (fun u hu hne => s5gr_K4_col h hF hz hu hne) (fun u hu _ => hH u hu)
  rw [← hp.tsum_eq]
  have e1 : (∑' n, T (s3st_vector z) n * conj (Y n)) = inner ℂ Y (T (s3st_vector z)) := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [gop_inner_apply, mul_comm]
  rw [e1, ← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [gop_inner_apply, s3st_vector_apply hz]

/-- **Stub W4 (C-d core).** The `B₄`-bound transfers from `g` to `g' = 1/(φ ∘ T + a)`, where `φ = ι ∘ g ∘ ι` is the
disc chart of `g` and `T` is a Möbius bijection of `𝔻*` onto `𝔻 ∖ {ω}` (`ω = T(∞)`). Both kernels reduce to `K₁_φ`:
`K_g(z,w) = z⁻²w⁻² K₁_φ(z⁻¹,w⁻¹)` and `K_{g'}(z,w) = T'(z)T'(w) K₁_φ(Tz,Tw)`; the `A²` pullbacks by `ι` and `T` are
unitary. -/
theorem s5gr_B4_mobius {f g f' g' : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) (h' : IsNormalizedDisjointPair f' g')
    (hF' : volume ((f' '' unitDisc ∪ g' '' unitDiscExterior)ᶜ) = 0)
    {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0)
    (hgφ : ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = 1 / φ s)
    {T : ℂ → ℂ} {p q r u : ℂ} (hpq : p * u - q * r ≠ 0) (hTd : ∀ z ∈ unitDiscExterior, r * z + u ≠ 0)
    (hT : ∀ z ∈ unitDiscExterior, T z = (p * z + q) / (r * z + u))
    {ω : ℂ} (hω : ω ∈ unitDisc) (hTb : BijOn T unitDiscExterior (unitDisc \ {ω}))
    {a : ℂ} (hg' : ∀ z ∈ unitDiscExterior, φ (T z) + a ≠ 0 ∧ g' z = 1 / (φ (T z) + a))
    {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B4 (grunsky f g) m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2) :
    ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B4 (grunsky f' g') m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 := by
  obtain ⟨hTc, -⟩ := s5gr_T_conf hTd hT hTb
  obtain ⟨-, hTapp⟩ := s5gr_B4_op h hF
  obtain ⟨-, hTapp'⟩ := s5gr_B4_op h' hF'
  obtain ⟨hρc, hρinv⟩ := s5gr_inv_gen s5gr_ext_open hTc
  have hι := s5gr_inv_ext_conf
  have hK : ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w →
      kerK4 g z w = (z⁻¹) ^ 2 * (w⁻¹) ^ 2 * kerK1 φ z⁻¹ w⁻¹ :=
    fun z hz w hw hzw => s2c_kerK4_eq hφd hφi hφ0 one_ne_zero hgφ hz hw hzw
  have hK' : ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, z ≠ w →
      kerK4 g' z w = deriv T z * deriv T w * kerK1 φ (T z) (T w) :=
    fun z hz w hw hzw => s5gr_K4_disc_cov hφd hφi hpq hTd hT hTb hg' hz hw hzw
  set Op := gopOp (B4 (grunsky f g)) with hOp
  set Op' := gopOp (B4 (grunsky f' g')) with hOp'
  -- `‖Op‖ ≤ c`
  have hTn : ‖Op‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro X
    have hs : ‖Op X‖ ^ 2 ≤ c ^ 2 * ‖X‖ ^ 2 := by
      rw [gop_norm_sq, gop_norm_sq]
      have h1 := hB (fun n => X n) (gop_l2_summable X)
      simp only [hTapp]
      exact h1
    nlinarith [norm_nonneg (Op X), norm_nonneg X, mul_nonneg hc (norm_nonneg X)]
  -- the norm of an adjoint image as an area integral
  have hnorm : ∀ (A : ell2 →L[ℂ] ell2) (Z : ell2) (U : ℂ → ℂ),
      (∀ z ∈ unitDiscExterior, U z = ∑' m, conj ((ContinuousLinearMap.adjoint A Z) m) * basisF m z) →
      ‖ContinuousLinearMap.adjoint A Z‖ ^ 2 = ∫ z in unitDiscExterior, ‖U z‖ ^ 2 := by
    intro A Z U hU
    have hs : Summable (fun m => ‖conj ((ContinuousLinearMap.adjoint A Z) m)‖ ^ 2) := by
      simpa only [Complex.norm_conj] using gop_l2_summable (ContinuousLinearMap.adjoint A Z)
    have hP := (s35_ext_parseval hs).tsum_eq
    simp only [Complex.norm_conj] at hP
    rw [gop_norm_sq, hP]
    refine setIntegral_congr_fun s5gr_ext_open.measurableSet fun z hz => ?_
    rw [hU z hz]
  -- the adjoint bound
  have hadj : ∀ Y : ell2, ‖ContinuousLinearMap.adjoint Op' Y‖ ^ 2 ≤ c ^ 2 * ‖Y‖ ^ 2 := by
    intro Y
    set v : ℂ → ℂ := fun w => ∑' n, Y n * basisF n w with hvdef
    have hvs : ∀ u ∈ unitDiscExterior, HasSum (fun n => Y n * basisF n u) (v u) :=
      fun u hu => s35_seriesF_hasSum (gop_l2_summable Y) hu
    have hvA : v ∈ A21fun unitDiscExterior := e212_ext_series (gop_l2_summable Y)
    set ρ := Function.invFunOn T unitDiscExterior with hρ
    -- push `v` to the disc by `T`, then pull it back to `𝔻*` by inversion
    have hwAp : (fun t => v (ρ t) * deriv ρ t) ∈ A21fun (unitDisc \ {ω}) :=
      a21_pullback (isOpen_ball.sdiff isClosed_singleton) hρc hvA
    obtain ⟨wd, hwA, hwdeq⟩ := s5gr_remove_pt hω hwAp
    have hwA0 : wd ∈ A21fun (unitDisc \ {0}) := by
      refine ⟨hwA.1.mono sdiff_subset, lt_of_le_of_lt ?_ hwA.2⟩
      unfold normA21
      exact ENNReal.rpow_le_rpow (lintegral_mono_set sdiff_subset) (by norm_num)
    have hvtA : (fun W => wd W⁻¹ * deriv (fun z : ℂ => z⁻¹) W) ∈ A21fun unitDiscExterior :=
      a21_pullback s5gr_ext_open hι hwA0
    set vt : ℂ → ℂ := fun W => wd W⁻¹ * deriv (fun z : ℂ => z⁻¹) W with hvt
    obtain ⟨Yt, hYts, hYt, hYtP⟩ := s35_ext_expansion hvtA
    set Ytv : ell2 := ⟨Yt, gop_mem_of_summable hYts⟩ with hYtv
    set Φ : ℂ → ℂ := fun s => ∫ t in unitDisc, kerK1 φ s t * conj (wd t) with hΦ
    set V : ℂ → ℂ := fun Z => ∫ W in unitDiscExterior, kerK4 g Z W * conj (vt W) with hVdef
    set V' : ℂ → ℂ := fun z => ∫ w in unitDiscExterior, kerK4 g' z w * conj (v w) with hV'def
    have hV : ∀ Z ∈ unitDiscExterior,
        V Z = ∑' m, conj ((ContinuousLinearMap.adjoint Op Ytv) m) * basisF m Z :=
      fun Z hZ => s5gr_K4_pair h hF (Y := Ytv) (H := vt) hYt hZ
    have hV' : ∀ z ∈ unitDiscExterior,
        V' z = ∑' m, conj ((ContinuousLinearMap.adjoint Op' Y) m) * basisF m z :=
      fun z hz => s5gr_K4_pair h' hF' hvs hz
    -- pointwise transfer identities
    have hTv : ∀ w ∈ unitDiscExterior, deriv T w * conj (v w) =
        ((‖deriv T w‖ ^ 2 : ℝ) : ℂ) * conj (wd (T w)) := by
      intro w hw
      obtain ⟨h1, h2⟩ := hρinv w hw
      rw [hwdeq (hTb.mapsTo hw)]
      simp only
      rw [h1]
      have h3 : conj (deriv ρ (T w)) * conj (deriv T w) = 1 := by rw [← map_mul, h2, map_one]
      have h4 : ((‖deriv T w‖ ^ 2 : ℝ) : ℂ) = deriv T w * conj (deriv T w) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h4, map_mul]
      linear_combination (-(deriv T w * conj (v w))) * h3
    have hTn2 : ∀ w ∈ unitDiscExterior, ‖deriv T w‖ ^ 2 * ‖wd (T w)‖ ^ 2 = ‖v w‖ ^ 2 := by
      intro w hw
      obtain ⟨h1, h2⟩ := hρinv w hw
      rw [hwdeq (hTb.mapsTo hw)]
      simp only
      rw [h1]
      calc ‖deriv T w‖ ^ 2 * ‖v w * deriv ρ (T w)‖ ^ 2 = ‖v w‖ ^ 2 * ‖deriv ρ (T w) * deriv T w‖ ^ 2 := by
            rw [norm_mul, norm_mul]; ring
        _ = ‖v w‖ ^ 2 := by rw [h2, norm_one]; ring
    have hι2 : ∀ W : ℂ, ((‖deriv (fun z : ℂ => z⁻¹) W‖ ^ 2 : ℝ) : ℂ) = (W⁻¹) ^ 2 * conj ((W⁻¹) ^ 2) := by
      intro W
      rw [deriv_inv, norm_neg, ← inv_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    -- `V' = T' · Φ ∘ T`
    have hrel' : ∀ z ∈ unitDiscExterior, V' z = deriv T z * Φ (T z) := by
      intro z hz
      have e1 : V' z = ∫ w in unitDiscExterior,
          deriv T z * ((‖deriv T w‖ ^ 2 : ℝ) • (kerK1 φ (T z) (T w) * conj (wd (T w)))) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem s5gr_ext_open.measurableSet,
          ae_restrict_of_ae (volume.ae_ne z)] with w hw hwz
        rw [hK' z hz w hw (Ne.symm hwz), Complex.real_smul]
        calc deriv T z * deriv T w * kerK1 φ (T z) (T w) * conj (v w) =
            deriv T z * kerK1 φ (T z) (T w) * (deriv T w * conj (v w)) := by ring
          _ = _ := by rw [hTv w hw]; ring
      rw [e1, integral_const_mul]
      congr 1
      show _ = ∫ t in unitDisc, kerK1 φ (T z) t * conj (wd t)
      rw [← s5gr_punct_measure_at ω]
      exact (s5gr_cov_gen s5gr_ext_open hTc (fun t => kerK1 φ (T z) t * conj (wd t))).symm
    -- `V = -(Z⁻¹)² · Φ ∘ ι`
    have hrel : ∀ Z ∈ unitDiscExterior, V Z = -((Z⁻¹) ^ 2) * Φ Z⁻¹ := by
      intro Z hZ
      have e1 : V Z = ∫ W in unitDiscExterior,
          -((Z⁻¹) ^ 2) * ((‖deriv (fun z : ℂ => z⁻¹) W‖ ^ 2 : ℝ) • (kerK1 φ Z⁻¹ W⁻¹ * conj (wd W⁻¹))) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem s5gr_ext_open.measurableSet,
          ae_restrict_of_ae (volume.ae_ne Z)] with W hW hWZ
        simp only [hVdef, hvt]
        rw [hK Z hZ W hW (Ne.symm hWZ), Complex.real_smul, hι2 W, deriv_inv, ← inv_pow, map_mul, map_neg]
        ring
      rw [e1, integral_const_mul]
      congr 1
      show _ = ∫ t in unitDisc, kerK1 φ Z⁻¹ t * conj (wd t)
      rw [← s5gr_punct_measure]
      exact (s5gr_cov_gen s5gr_ext_open hι (fun t => kerK1 φ Z⁻¹ t * conj (wd t))).symm
    -- the norms
    have hn' := hnorm Op' Y V' hV'
    have hn := hnorm Op Ytv V hV
    have hV'Φ : (∫ z in unitDiscExterior, ‖V' z‖ ^ 2) = ∫ s in unitDisc, ‖Φ s‖ ^ 2 := by
      rw [← s5gr_punct_measure_at ω, s5gr_cov_gen s5gr_ext_open hTc (fun s => ‖Φ s‖ ^ 2)]
      refine setIntegral_congr_fun s5gr_ext_open.measurableSet fun z hz => ?_
      simp only [smul_eq_mul]
      rw [hrel' z hz, norm_mul, mul_pow]
    have hVΦ : (∫ Z in unitDiscExterior, ‖V Z‖ ^ 2) = ∫ s in unitDisc, ‖Φ s‖ ^ 2 := by
      rw [← s5gr_punct_measure, s5gr_cov_gen s5gr_ext_open hι (fun s => ‖Φ s‖ ^ 2)]
      refine setIntegral_congr_fun s5gr_ext_open.measurableSet fun Z hZ => ?_
      simp only [smul_eq_mul]
      rw [hrel Z hZ, norm_mul, mul_pow, deriv_inv, norm_neg, norm_neg, ← inv_pow]
    have hYt2 : ‖Ytv‖ ^ 2 = ‖Y‖ ^ 2 := by
      rw [gop_norm_sq, gop_norm_sq]
      have e2 : (∑' n, ‖Ytv n‖ ^ 2) = ∫ W in unitDiscExterior, ‖vt W‖ ^ 2 := hYtP.tsum_eq
      have e3 : (∫ W in unitDiscExterior, ‖vt W‖ ^ 2) = ∫ t in unitDisc, ‖wd t‖ ^ 2 := by
        rw [← s5gr_punct_measure, s5gr_cov_gen s5gr_ext_open hι (fun t => ‖wd t‖ ^ 2)]
        refine setIntegral_congr_fun s5gr_ext_open.measurableSet fun W hW => ?_
        simp only [smul_eq_mul, hvt]
        rw [norm_mul, mul_pow, mul_comm]
      have e4 : (∫ t in unitDisc, ‖wd t‖ ^ 2) = ∫ w in unitDiscExterior, ‖v w‖ ^ 2 := by
        rw [← s5gr_punct_measure_at ω, s5gr_cov_gen s5gr_ext_open hTc (fun t => ‖wd t‖ ^ 2)]
        refine setIntegral_congr_fun s5gr_ext_open.measurableSet fun w hw => ?_
        simp only [smul_eq_mul]
        exact hTn2 w hw
      rw [e2, e3, e4, (s35_ext_parseval (gop_l2_summable Y)).tsum_eq]
    have hle : ‖ContinuousLinearMap.adjoint Op Ytv‖ ≤ c * ‖Ytv‖ := by
      calc ‖ContinuousLinearMap.adjoint Op Ytv‖ ≤ ‖ContinuousLinearMap.adjoint Op‖ * ‖Ytv‖ :=
            (ContinuousLinearMap.adjoint Op).le_opNorm Ytv
        _ ≤ c * ‖Ytv‖ := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul_of_nonneg_right hTn (norm_nonneg _)
    have hle2 : ‖ContinuousLinearMap.adjoint Op Ytv‖ ^ 2 ≤ c ^ 2 * ‖Ytv‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    rw [hn', hV'Φ, ← hVΦ, ← hn, ← hYt2]
    exact hle2
  -- `‖Op'‖ ≤ c`
  have hT'n : ‖Op'‖ ≤ c := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint Op']
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro Y
    have h1 := hadj Y
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint Op' Y), norm_nonneg Y, mul_nonneg hc (norm_nonneg Y)]
  intro x hx
  set X : ell2 := ⟨x, gop_mem_of_summable hx⟩ with hX
  have h1 : ‖Op' X‖ ^ 2 ≤ c ^ 2 * ‖X‖ ^ 2 := by
    have h2 : ‖Op' X‖ ≤ c * ‖X‖ :=
      (Op'.le_opNorm X).trans (mul_le_mul_of_nonneg_right hT'n (norm_nonneg _))
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [gop_norm_sq, gop_norm_sq] at h1
  simp only [hTapp'] at h1
  exact h1

/-- Partial derivatives of a function of two variables, in the second variable. -/
theorem s5gr_partial_z {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : E × ℂ → ℂ} {a : E} {z : ℂ}
    (hΦ : DifferentiableAt ℂ Φ (a, z)) : HasDerivAt (fun z' => Φ (a, z')) (fderiv ℂ Φ (a, z) (0, 1)) z := by
  have h2 : HasDerivAt (fun z' : ℂ => (a, z')) (0, 1) z := (hasDerivAt_const z a).prodMk (hasDerivAt_id z)
  exact hΦ.hasFDerivAt.comp_hasDerivAt z h2

/-- Partial derivatives of a function of two variables, in the first variable. -/
theorem s5gr_partial_t {Φ : ℂ × ℂ → ℂ} {τ z : ℂ} (hΦ : DifferentiableAt ℂ Φ (τ, z)) :
    HasDerivAt (fun τ' => Φ (τ', z)) (fderiv ℂ Φ (τ, z) (1, 0)) τ := by
  have h2 : HasDerivAt (fun τ' : ℂ => (τ', z)) (1, 0) τ := (hasDerivAt_id τ).prodMk (hasDerivAt_const τ z)
  exact hΦ.hasFDerivAt.comp_hasDerivAt τ h2

/-- A directional derivative of an analytic map is analytic. -/
theorem s5gr_dir_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Ψ : E → ℂ} {U : Set E} (hΨ : AnalyticOnNhd ℂ Ψ U) (v : E) :
    AnalyticOnNhd ℂ (fun q => fderiv ℂ Ψ q v) U := fun q hq =>
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (hΨ.fderiv q hq)

/-- Mixed partials of an analytic function commute. -/
theorem s5gr_mixed {Ψ : ℂ × ℂ → ℂ} {p : ℂ × ℂ} (hΨ : AnalyticAt ℂ Ψ p) (v w : ℂ × ℂ) :
    fderiv ℂ (fun q => fderiv ℂ Ψ q v) p w = fderiv ℂ (fun q => fderiv ℂ Ψ q w) p v := by
  have hs := (hΨ.contDiffAt (n := ⊤)).isSymmSndFDerivAt_of_omega
  have hd : DifferentiableAt ℂ (fderiv ℂ Ψ) p := hΨ.fderiv.differentiableAt
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hs w v

/-- The Schwarzian through the third derivative. -/
theorem s5gr_schw_formula {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h1 : deriv f z ≠ 0) :
    schwarzianHol f z = (deriv (deriv (deriv f)) z * deriv f z - deriv (deriv f) z ^ 2) / deriv f z ^ 2 -
      1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2 := by
  have hd1 : DifferentiableAt ℂ (deriv f) z := hf.deriv.differentiableAt
  have hd2 : DifferentiableAt ℂ (deriv (deriv f)) z := hf.deriv.deriv.differentiableAt
  have hq : HasDerivAt (fun w => deriv (deriv f) w / deriv f w)
      ((deriv (deriv (deriv f)) z * deriv f z - deriv (deriv f) z * deriv (deriv f) z) / deriv f z ^ 2) z :=
    hd2.hasDerivAt.div hd1.hasDerivAt h1
  show deriv (fun w => deriv (deriv f) w / deriv f w) z - 1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2 = _
  rw [hq.deriv]
  ring

/-- Linearization of the Schwarzian at the identity. -/
theorem s5gr_schw_lin {A1 A2 A3 : ℂ → ℂ} {φz : ℂ} (h1 : DifferentiableAt ℂ A1 0) (h2 : DifferentiableAt ℂ A2 0)
    (h3 : DifferentiableAt ℂ A3 0) (e1 : A1 0 = 1) (e2 : A2 0 = 0) (e3 : A3 0 = 0)
    (h : ∀ᶠ τ in 𝓝 (0 : ℂ), (A3 τ * A1 τ - A2 τ ^ 2) / A1 τ ^ 2 - 1 / 2 * (A2 τ / A1 τ) ^ 2 = τ * φz) :
    deriv A3 0 = φz := by
  have hA1 : A1 0 ≠ 0 := by rw [e1]; exact one_ne_zero
  have hL : HasDerivAt (fun τ => (A3 τ * A1 τ - A2 τ ^ 2) / A1 τ ^ 2 - 1 / 2 * (A2 τ / A1 τ) ^ 2)
      (deriv A3 0) 0 := by
    have := (((h3.hasDerivAt.mul h1.hasDerivAt).sub (h2.hasDerivAt.pow 2)).div (h1.hasDerivAt.pow 2)
      (pow_ne_zero 2 hA1)).sub (((h2.hasDerivAt.div h1.hasDerivAt hA1).pow 2).const_mul (1 / 2))
    convert this using 1
    simp [e1, e2, e3]
  have hR : HasDerivAt (fun τ : ℂ => τ * φz) φz 0 := by simpa using (hasDerivAt_id (0 : ℂ)).mul_const φz
  exact hL.unique (hR.congr_of_eventuallyEq h)

/-- The Möbius form of the curve pair: `λ_{f''(0)/2 - s} ∘ f^μ = W/(eW + d)` with `W = w^μ`, `d = W'(0)`,
`e = W''(0)/(2d) - s` (the real-analytic `P` of `s5t53_fB_formula` cancels). -/
theorem s5gr_lam_formula {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {s : ℂ}
    (hden : ∀ x ∈ unitDisc, (deriv (deriv (fB μ)) 0 / 2 - s) * fB μ x + 1 ≠ 0) :
    deriv (normalizedSolution (extB μ)) 0 ≠ 0 ∧ ∀ x ∈ unitDisc,
      (deriv (deriv (normalizedSolution (extB μ))) 0 / (2 * deriv (normalizedSolution (extB μ)) 0) - s) *
          normalizedSolution (extB μ) x + deriv (normalizedSolution (extB μ)) 0 ≠ 0 ∧
        lambdaW (deriv (deriv (fB μ)) 0 / 2 - s) (fB μ x) = normalizedSolution (extB μ) x /
          ((deriv (deriv (normalizedSolution (extB μ))) 0 / (2 * deriv (normalizedSolution (extB μ)) 0) - s) *
            normalizedSolution (extB μ) x + deriv (normalizedSolution (extB μ)) 0) := by
  obtain ⟨W, hW⟩ : ∃ W, W = normalizedSolution (extB μ) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := ⟨_, rfl⟩
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  obtain ⟨-, hWd, hWi, hW0⟩ := QCV.qcv_W_props hk
  rw [← hW] at hWd hWi hW0 ⊢
  have hd : deriv W 0 ≠ 0 :=
    deriv_ne_zero_of_injOn isOpen_ball hWd (hWi.mono (subset_univ _)) (mem_ball_self one_pos)
  obtain ⟨d, hdd⟩ : ∃ d, d = deriv W 0 := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hfB : ∀ x ∈ unitDisc, -P * W x + 1 ≠ 0 ∧ fB μ x = (1 / d * W x + 0) / (-P * W x + 1) := by
    intro x hx
    have := s5t53_fB_formula hμ hx
    rw [← hW, ← hP, ← hdd] at this
    exact this
  -- the second derivative: `f''(0) = W''(0)/d + 2dP`
  have hWa : AnalyticAt ℂ W 0 := hWd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hGa : AnalyticAt ℂ (fun z => W z / d) 0 := hWa.div analyticAt_const hd
  have hG0 : W 0 / d = 0 := by rw [hW0, zero_div]
  have hGd : deriv (fun z => W z / d) = fun z => deriv W z / d := funext fun z => deriv_div_const d
  have hG1 : deriv (fun z => W z / d) 0 = 1 := by rw [hGd]; show deriv W 0 / d = 1; rw [← hdd, div_self hd]
  have hGdd : deriv (deriv (fun z => W z / d)) 0 = deriv (deriv W) 0 / d := by
    rw [hGd]; exact deriv_div_const d
  have hjet := (lambdaW_comp_jets hGa hG0 hG1 (-(d * P))).2
  have hev : fB μ =ᶠ[𝓝 0] fun z => lambdaW (-(d * P)) (W z / d) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with z hz
    obtain ⟨h1, h2⟩ := hfB z hz
    rw [h2]
    show _ = W z / d / (-(d * P) * (W z / d) + 1)
    have e : -(d * P) * (W z / d) + 1 = -P * W z + 1 := by field_simp
    rw [e, add_zero, one_div_mul_eq_div]
  have hdd2 : deriv (deriv (fB μ)) 0 = deriv (deriv W) 0 / d + 2 * (d * P) := by
    rw [hev.deriv.deriv_eq, hjet, hGdd]; ring
  rw [hdd2]
  refine ⟨hd, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hfB x hx
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = -P * W x + 1 := ⟨_, rfl⟩
  rw [← hQ] at h1 h2
  have key : (deriv (deriv W) 0 / d + 2 * (d * P)) / 2 - s = (deriv (deriv W) 0 / (2 * d) - s) + d * P := by
    field_simp; ring
  have key2 : ((deriv (deriv W) 0 / (2 * d) - s) + d * P) * fB μ x + 1 =
      ((deriv (deriv W) 0 / (2 * d) - s) * W x + d) / (d * Q) := by
    rw [h2, eq_div_iff (mul_ne_zero hd h1)]
    field_simp
    rw [hQ]
    ring
  have hne : (deriv (deriv W) 0 / (2 * d) - s) * W x + d ≠ 0 := by
    intro h0
    have := hden x hx
    rw [hdd2, key, key2, h0, zero_div] at this
    exact this rfl
  refine ⟨hne, ?_⟩
  rw [key]
  show fB μ x / (((deriv (deriv W) 0 / (2 * d) - s) + d * P) * fB μ x + 1) = _
  rw [key2, h2, add_zero]
  field_simp

/-- The Möbius map `T` of `s5t53_G_eq`: a bijection of `𝔻*` onto `𝔻 ∖ {ω}`. -/
theorem s5gr_T_bij {ω : ℂ} (hω : ω ∈ unitDisc) :
    ω * (conj ω - 1) * ((ω - 1) * conj ω) - (ω - 1) * (conj ω - 1) ≠ 0 ∧
      (∀ z ∈ unitDiscExterior, (conj ω - 1) * z + (ω - 1) * conj ω ≠ 0) ∧
      BijOn (fun x => (x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1)))
        unitDiscExterior (unitDisc \ {ω}) := by
  have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have hne1 : ω - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero.mp h, norm_one] at hω1; exact lt_irrefl _ hω1
  have hcj : conj ω - 1 = conj (ω - 1) := by simp
  have hne2 : conj ω - 1 ≠ 0 := by rw [hcj]; exact (map_ne_zero _).mpr hne1
  have hnn : ‖conj ω - 1‖ = ‖ω - 1‖ := by rw [hcj, Complex.norm_conj]
  have hωω : conj ω * ω - 1 ≠ 0 := by
    intro h
    have h' : ((‖ω‖ : ℂ)) ^ 2 = 1 := by rw [← Complex.conj_mul']; exact sub_eq_zero.mp h
    have : ‖ω‖ ^ 2 = 1 := by exact_mod_cast h'
    nlinarith [norm_nonneg ω]
  have hext : ∀ z ∈ unitDiscExterior, 1 < ‖z‖ := fun z hz => hz
  have hTd : ∀ z ∈ unitDiscExterior, (conj ω - 1) * z + (ω - 1) * conj ω ≠ 0 := by
    intro z hz h0
    have hz' : z = -((ω - 1) * conj ω) / (conj ω - 1) := by
      field_simp; linear_combination h0
    have := hext z hz
    rw [hz', norm_div, norm_neg, norm_mul, Complex.norm_conj, hnn,
      mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hne1)] at this
    linarith
  refine ⟨?_, hTd, ?_⟩
  · have e : ω * (conj ω - 1) * ((ω - 1) * conj ω) - (ω - 1) * (conj ω - 1) =
        (ω - 1) * (conj ω - 1) * (conj ω * ω - 1) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero hne1 hne2) hωω
  · obtain ⟨e, he⟩ : ∃ e : ℂ, e = (ω - 1) / (conj ω - 1) := ⟨_, rfl⟩
    have hen : ‖e‖ = 1 := by rw [he, norm_div, hnn, div_self (norm_ne_zero_iff.mpr hne1)]
    have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at hen; exact zero_ne_one hen
    -- `z ↦ e/z` maps `𝔻*` onto `𝔻 ∖ {0}`
    have hinv : BijOn (fun z => e / z) unitDiscExterior (unitDisc \ {0}) := by
      refine ⟨fun z hz => ?_, fun z hz w hw h => ?_, fun s hs => ?_⟩
      · have hz1 := hext z hz
        have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; linarith
        refine ⟨mem_ball_zero_iff.mpr ?_, div_ne_zero he0 hz0⟩
        rw [norm_div, hen, div_lt_one (by linarith)]; exact hz1
      · have hz0 : z ≠ 0 := by intro h; have := hext z hz; rw [h, norm_zero] at this; linarith
        have hw0 : w ≠ 0 := by intro h; have := hext w hw; rw [h, norm_zero] at this; linarith
        have h' : e / z = e / w := h
        exact (mul_left_cancel₀ he0 ((div_eq_div_iff hz0 hw0).mp h')).symm
      · obtain ⟨hs1, hs0⟩ := hs
        have hs0' : s ≠ 0 := hs0
        refine ⟨e / s, ?_, ?_⟩
        · show 1 < ‖e / s‖
          rw [norm_div, hen, one_lt_div (norm_pos_iff.mpr hs0')]
          exact mem_ball_zero_iff.mp hs1
        · simp only; field_simp
    have hA := (s5gr_aut_conf hω).2
    have hAb : BijOn (fun t => (t + ω) / (conj ω * t + 1)) (unitDisc \ {0}) (unitDisc \ {ω}) := by
      have := hA.2.1.bijOn_image
      rwa [hA.2.2] at this
    refine (hAb.comp hinv).congr fun z hz => ?_
    have hz1 := hext z hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; linarith
    have hmem : e / z ∈ unitDisc := (hinv.1 hz).1
    obtain ⟨hden, -⟩ := s5gr_aut_norm hω hmem
    have hden2 : (ω - 1) * conj ω + z * (conj ω - 1) ≠ 0 := by
      have := hTd z hz
      intro h0; exact this (by linear_combination h0)
    simp only [Function.comp_apply]
    rw [he] at hden ⊢
    field_simp
    ring

/-- The curve data at `y` (`s5t53_c1_welding`, `c5_potential`, `den`, `fibre_mem` along `t ↦ sin t • y`, at `t = π/2`). -/
theorem s5gr_line_data {sec : AInf unitDisc → LinfStar} {ε0 : ℝ} (hε0 : 0 < ε0)
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε0)) (hs0 : sec 0 = ((Quotient.out originT : LinfStarBall) : LinfStar))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε0 → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    (y : AInf unitDisc × ℂ) (hy : ‖y‖ < ε0) :
    (∃ h, IsOneFixedQS h ∧ IsWeldingPrime h
      (fun x => lambdaW (deriv (deriv (fB (sec y.1))) 0 / 2 - y.2) (fB (sec y.1) x))
      (fun x => finPart (mobiusExt 1 0 (deriv (deriv (fB (sec y.1))) 0 / 2 - y.2) 1
        (normalizedWeldingSphere (sec y.1) (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec y.1))
          (inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane)))))) ∧
    potentialK (tcCoordHInv y) = Real.log ‖derivAtInfty (fun x => finPart (mobiusExt 1 0
      (deriv (deriv (fB (sec y.1))) 0 / 2 - y.2) 1 (normalizedWeldingSphere (sec y.1)
        (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec y.1))
          (inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane)))))‖ ∧
    sec y.1 ∈ LinfStarBall ∧
    (∀ x ∈ unitDisc, (deriv (deriv (fB (sec y.1))) 0 / 2 - y.2) * fB (sec y.1) x + 1 ≠ 0) ∧
    inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane) ∈ wB (sec y.1) '' extDiscExterior := by
  have hψb : ∀ t, ‖((Real.sin t : ℝ) : ℂ) • y‖ < ε0 := by
    intro t
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |Real.sin t| * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg _)
      _ < ε0 := by rw [one_mul]; exact hy
  have h1 := s5t53_c1_welding hε0 hsa hs0 hsec Real.contDiff_sin Real.sin_zero hψb (π / 2)
  have h5 := s5t53_c5_potential hε0 hsa hs0 hsec Real.contDiff_sin Real.sin_zero hψb (π / 2)
  have hf := s5t53_fibre_mem hsec hψb (π / 2)
  simp only [Real.sin_pi_div_two, Complex.ofReal_one, one_smul, one_mul] at h1 h5 hf
  refine ⟨h1, h5, hf.1, fun x hx => ?_, hf.2⟩
  have := s5t53_den hsec hψb (π / 2) hx
  simp only [Real.sin_pi_div_two, Complex.ofReal_one, one_smul, one_mul] at this
  exact this.2

/-- **`B₃` is invertible for the curve pair** (`pgb_unit_of_defects`; `‖B₁‖ < 1` by W5, `‖B₄‖ < 1` by W4). -/
theorem s5gr_B3_unit {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {c ζ : ℂ} (hζ : ζ = -c) {f g : ℂ → ℂ}
    (hpair : IsNormalizedDisjointPair f g) (hnull : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0)
    (hf : ∀ z ∈ unitDisc, f z = lambdaW c (fB μ z)) (hden : ∀ z ∈ unitDisc, c * fB μ z + 1 ≠ 0)
    (hfib : inversion (ζ : ExtPlane) ∈ wB μ '' extDiscExterior)
    (hg : ∀ x ∈ unitDiscExterior, g x = finPart (mobiusExt 1 0 c 1 (normalizedWeldingSphere μ
      (sigmaInvSphere (Function.invFun (normalizedWeldingSphere μ) (inversion (ζ : ExtPlane))) (x : ExtPlane))))) :
    IsUnit (gopOp (B3 (grunsky f g))) := by
  obtain ⟨hfs, hgs⟩ := r22_fsans_gsans hμ
  have hbase := AppB.b8_welding_normalized_pair hμ
  have hbnull := r22_complement_null hμ
  have hB1 : B1 (grunsky f g) = B1 (grunsky (fsans μ) (gsans μ)) := by
    funext m n
    exact s5gr_B1_lambda hbase hpair (a := c) (fun z hz => by rw [hfs]; exact hden z hz)
      (fun z hz => by rw [hfs]; exact hf z hz) m n
  have hn1 : ‖gopOp (B1 (grunsky f g))‖ < 1 := by rw [hB1]; exact (pgb_norm_lt_one hμ).1
  obtain ⟨c0, hc0, hc1, C, hC⟩ := remark_2_3 hμ
  obtain ⟨hpar1, hpar2⟩ := s5t53_G_param hμ hfib
  obtain ⟨hωD, hωg⟩ := s5cf_uniformizer_inverse_data hμ hpar1
  have hgω : s5cf_gchart μ (fiberUniformizer μ ζ) = -c := by rw [hωg, hζ]
  obtain ⟨hpq, hTd, hTb⟩ := s5gr_T_bij hωD
  have hB4 := s5gr_B4_mobius hbase hbnull hpair hnull (φ := s5cf_gchart μ)
    (fun t ht => (s5cf_gchart_analytic hμ ht).differentiableAt.differentiableWithinAt)
    (s5cf_gchart_inj hμ) (by simp [s5cf_gchart])
    (fun s hs hs0 => by rw [hgs]; simp [s5cf_gchart, hs0])
    (T := fun x => (x * fiberUniformizer μ ζ * (conj (fiberUniformizer μ ζ) - 1) + fiberUniformizer μ ζ - 1) /
      ((fiberUniformizer μ ζ - 1) * conj (fiberUniformizer μ ζ) + x * (conj (fiberUniformizer μ ζ) - 1)))
    (p := fiberUniformizer μ ζ * (conj (fiberUniformizer μ ζ) - 1)) (q := fiberUniformizer μ ζ - 1)
    (r := conj (fiberUniformizer μ ζ) - 1) (u := (fiberUniformizer μ ζ - 1) * conj (fiberUniformizer μ ζ))
    hpq hTd (fun z _ => by congr 1 <;> ring) hωD hTb (a := c)
    (fun z hz => by
      obtain ⟨-, h2, h3⟩ := s5t53_G_eq hμ hωD hgω hpar2 hz
      exact ⟨h2, by rw [hg z hz, h3, one_div]⟩)
    hc0 (fun x hx => (hC x hx).2.1)
  have hn4 : ‖gopOp (B4 (grunsky f g))‖ < 1 := by
    obtain ⟨hr4, hb4⟩ := gop_grunsky_bounds hpair hnull (B4 (grunsky f g)) (by simp)
    exact (s5gr_opNorm_of_bound hr4 hb4 hc0 hB4).trans_lt hc1
  obtain ⟨-, h2, -, h3, -⟩ := gop_blocks hpair hnull
  exact pgb_unit_of_defects _ _ _ hn4 hn1 (eq_sub_of_add_eq h2) (eq_sub_of_add_eq' h3)

/-- `(τ, x) ↦ sec((τ • Y).1)` is holomorphic. -/
theorem s5gr_sec_line {sec : AInf unitDisc → LinfStar} {ε0 : ℝ} (hsa : AnalyticOnNhd ℂ sec (ball 0 ε0))
    {Y : AInf unitDisc × ℂ} {q : ℂ × ℂ} (hq : ‖q.1 • Y‖ < ε0) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => sec (q.1 • Y).1) q := by
  have hq1 : ‖q.1 • Y.1‖ < ε0 := lt_of_le_of_lt (norm_fst_le (q.1 • Y)) hq
  obtain ⟨L, hL⟩ : ∃ L : ℂ × ℂ →L[ℂ] AInf unitDisc, L = (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight Y.1 :=
    ⟨_, rfl⟩
  have hLq : ∀ r : ℂ × ℂ, L r = r.1 • Y.1 := fun r => by rw [hL]; rfl
  have hc : AnalyticAt ℂ (sec ∘ L) q := by
    apply (hsa _ _).comp (L.analyticAt q)
    rw [hLq]; exact mem_ball_zero_iff.mpr hq1
  refine hc.congr (Filter.Eventually.of_forall fun r => ?_)
  show sec (L r) = sec (r.1 • Y.1)
  rw [hLq]

/-- **Joint holomorphy of the curve pair** `(τ, x) ↦ λ_{c(τ)} f^{μ_τ}(x) = W/(eW + d)` (`s5gr_lam_formula`,
`s5cf_planeB_disk_analytic`). -/
theorem s5gr_F_analytic {sec : AInf unitDisc → LinfStar} {ε0 ε : ℝ} (hsa : AnalyticOnNhd ℂ sec (ball 0 ε0))
    {Y : AInf unitDisc × ℂ}
    (hY : ∀ τ ∈ ball (0 : ℂ) ε, ‖τ • Y‖ < ε0 ∧ sec (τ • Y).1 ∈ LinfStarBall ∧
      ∀ x ∈ unitDisc, (deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2) * fB (sec (τ • Y).1) x + 1 ≠ 0) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => lambdaW (deriv (deriv (fB (sec (p.1 • Y).1))) 0 / 2 - (p.1 • Y).2)
      (fB (sec (p.1 • Y).1) p.2)) (ball 0 ε ×ˢ unitDisc) := by
  obtain ⟨Wf, hWf⟩ : ∃ Wf : LinfStar × ℂ → ℂ, Wf = fun q => normalizedSolution (extB q.1) q.2 := ⟨_, rfl⟩
  have hWa : AnalyticOnNhd ℂ Wf (LinfStarBall ×ˢ unitDisc) := by rw [hWf]; exact s5cf_planeB_disk_analytic
  have hD1a := s5gr_dir_analytic hWa (0, 1)
  have hD2a := s5gr_dir_analytic hD1a (0, 1)
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd1 : ∀ μ ∈ LinfStarBall, deriv (fun z => Wf (μ, z)) 0 = fderiv ℂ Wf (μ, 0) (0, 1) := fun μ hμ =>
    (s5gr_partial_z ((hWa (μ, 0) ⟨hμ, h0D⟩).differentiableAt)).deriv
  have hd2 : ∀ μ ∈ LinfStarBall, deriv (deriv (fun z => Wf (μ, z))) 0 =
      fderiv ℂ (fun r => fderiv ℂ Wf r (0, 1)) (μ, 0) (0, 1) := by
    intro μ hμ
    have hev : deriv (fun z => Wf (μ, z)) =ᶠ[𝓝 0] fun z => fderiv ℂ Wf (μ, z) (0, 1) := by
      filter_upwards [isOpen_ball.mem_nhds h0D] with z hz
      exact (s5gr_partial_z ((hWa (μ, z) ⟨hμ, hz⟩).differentiableAt)).deriv
    rw [hev.deriv_eq]
    exact (s5gr_partial_z ((hD1a (μ, 0) ⟨hμ, h0D⟩).differentiableAt)).deriv
  have hform : ∀ q ∈ ball (0 : ℂ) ε ×ˢ unitDisc,
      fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1) ≠ 0 ∧
      (fderiv ℂ (fun r => fderiv ℂ Wf r (0, 1)) (sec (q.1 • Y).1, 0) (0, 1) /
          (2 * fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1)) - (q.1 • Y).2) * Wf (sec (q.1 • Y).1, q.2) +
          fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1) ≠ 0 ∧
      lambdaW (deriv (deriv (fB (sec (q.1 • Y).1))) 0 / 2 - (q.1 • Y).2) (fB (sec (q.1 • Y).1) q.2) =
        Wf (sec (q.1 • Y).1, q.2) / ((fderiv ℂ (fun r => fderiv ℂ Wf r (0, 1)) (sec (q.1 • Y).1, 0) (0, 1) /
          (2 * fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1)) - (q.1 • Y).2) * Wf (sec (q.1 • Y).1, q.2) +
          fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1)) := by
    intro q hq
    obtain ⟨-, hμ, hden⟩ := hY q.1 hq.1
    obtain ⟨h1, h2⟩ := s5gr_lam_formula hμ hden
    have hWμ : normalizedSolution (extB (sec (q.1 • Y).1)) = fun z => Wf (sec (q.1 • Y).1, z) := by rw [hWf]
    rw [hWμ, hd1 _ hμ] at h1
    rw [hWμ, hd2 _ hμ, hd1 _ hμ] at h2
    exact ⟨h1, (h2 q.2 hq.2).1, (h2 q.2 hq.2).2⟩
  have hm : ∀ q ∈ ball (0 : ℂ) ε ×ˢ unitDisc, AnalyticAt ℂ (fun q : ℂ × ℂ => sec (q.1 • Y).1) q :=
    fun q hq => s5gr_sec_line hsa (hY q.1 hq.1).1
  have hU : IsOpen (ball (0 : ℂ) ε ×ˢ unitDisc) := isOpen_ball.prod isOpen_ball
  obtain ⟨Wq, hWq⟩ : ∃ f : ℂ × ℂ → ℂ, f = fun q => Wf (sec (q.1 • Y).1, q.2) := ⟨_, rfl⟩
  obtain ⟨D1q, hD1q⟩ : ∃ f : ℂ × ℂ → ℂ, f = fun q => fderiv ℂ Wf (sec (q.1 • Y).1, 0) (0, 1) := ⟨_, rfl⟩
  obtain ⟨D2q, hD2q⟩ : ∃ f : ℂ × ℂ → ℂ,
      f = fun q => fderiv ℂ (fun r => fderiv ℂ Wf r (0, 1)) (sec (q.1 • Y).1, 0) (0, 1) := ⟨_, rfl⟩
  obtain ⟨Sq, hSq⟩ : ∃ f : ℂ × ℂ → ℂ, f = fun q => (q.1 • Y).2 := ⟨_, rfl⟩
  intro p hp
  obtain ⟨hd0, hden0, -⟩ := hform p hp
  have hmp := hm p hp
  have hμp := (hY p.1 hp.1).2.1
  have hW : AnalyticAt ℂ Wq p := by
    rw [hWq]; exact AnalyticAt.comp (g := Wf) (f := fun q : ℂ × ℂ => (sec (q.1 • Y).1, q.2)) (x := p)
      (hWa (sec (p.1 • Y).1, p.2) ⟨hμp, hp.2⟩) (hmp.prod analyticAt_snd)
  have hD1 : AnalyticAt ℂ D1q p := by
    rw [hD1q]; exact AnalyticAt.comp (g := fun r => fderiv ℂ Wf r (0, 1)) (f := fun q : ℂ × ℂ => (sec (q.1 • Y).1, (0 : ℂ)))
      (x := p) (hD1a (sec (p.1 • Y).1, 0) ⟨hμp, h0D⟩) (hmp.prod analyticAt_const)
  have hD2 : AnalyticAt ℂ D2q p := by
    rw [hD2q]; exact AnalyticAt.comp (g := fun r => fderiv ℂ (fun r => fderiv ℂ Wf r (0, 1)) r (0, 1))
      (f := fun q : ℂ × ℂ => (sec (q.1 • Y).1, (0 : ℂ))) (x := p) (hD2a (sec (p.1 • Y).1, 0) ⟨hμp, h0D⟩)
      (hmp.prod analyticAt_const)
  have hs : AnalyticAt ℂ Sq p := by
    rw [hSq]
    show AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 * Y.2) p
    exact analyticAt_fst.mul analyticAt_const
  have hd0' : 2 * D1q p ≠ 0 := by rw [hD1q]; exact mul_ne_zero two_ne_zero hd0
  have hden0' : (D2q p / (2 * D1q p) - Sq p) * Wq p + D1q p ≠ 0 := by rw [hWq, hD1q, hD2q, hSq]; exact hden0
  have h2 : AnalyticAt ℂ (fun q => 2 * D1q q) p := analyticAt_const.mul hD1
  have hq : AnalyticAt ℂ (fun q => D2q q / (2 * D1q q)) p := hD2.div h2 hd0'
  have hden : AnalyticAt ℂ (fun q => (D2q q / (2 * D1q q) - Sq q) * Wq q + D1q q) p :=
    ((hq.sub hs).mul hW).add hD1
  have hA : AnalyticAt ℂ (fun q => Wq q / ((D2q q / (2 * D1q q) - Sq q) * Wq q + D1q q)) p := hW.div hden hden0'
  refine hA.congr ?_
  filter_upwards [hU.mem_nhds hp] with q hq
  rw [hWq, hD1q, hD2q, hSq]
  exact ((hform q hq).2.2).symm

/-- **The `τ`-jet of a holomorphic family with `S(F_τ) = τφ`** (mixed partials commute; Taylor on `𝔻`). -/
theorem s5gr_jet {ε : ℝ} (hε : 0 < ε) {F : ℂ → ℂ → ℂ} {s : ℂ} {φ : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc))
    (h0 : ∀ z ∈ unitDisc, F 0 z = z) (hF0 : ∀ τ ∈ ball (0 : ℂ) ε, F τ 0 = 0)
    (hF1 : ∀ τ ∈ ball (0 : ℂ) ε, deriv (F τ) 0 = 1)
    (hF2 : ∀ τ ∈ ball (0 : ℂ) ε, deriv (deriv (F τ)) 0 = 2 * τ * s)
    (hF' : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, deriv (F τ) z ≠ 0)
    (hS : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, schwarzianHol (F τ) z = τ * φ z) :
    ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (if n = 0 then s else
        iteratedDeriv (n + 1 - 2) φ 0 / ((n + 1 - 2).factorial : ℂ) /
          (((n + 1 : ℕ) : ℂ) ^ 3 - ((n + 1 : ℕ) : ℂ))) * z ^ (n + 2)) (deriv (fun τ => F τ z) 0) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ, Φ = fun p => F p.1 p.2 := ⟨_, rfl⟩
  rw [← hΦ] at han
  have hU : IsOpen (ball (0 : ℂ) ε ×ˢ unitDisc) := isOpen_ball.prod isOpen_ball
  have hmem : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, (τ, z) ∈ ball (0 : ℂ) ε ×ˢ unitDisc :=
    fun τ hτ z hz => ⟨hτ, hz⟩
  have h0ε : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- the `z`-derivatives `Ψ₁, Ψ₂, Ψ₃`
  obtain ⟨Ψ1, hΨ1⟩ : ∃ Ψ : ℂ × ℂ → ℂ, Ψ = fun q => fderiv ℂ Φ q (0, 1) := ⟨_, rfl⟩
  obtain ⟨Ψ2, hΨ2⟩ : ∃ Ψ : ℂ × ℂ → ℂ, Ψ = fun q => fderiv ℂ Ψ1 q (0, 1) := ⟨_, rfl⟩
  obtain ⟨Ψ3, hΨ3⟩ : ∃ Ψ : ℂ × ℂ → ℂ, Ψ = fun q => fderiv ℂ Ψ2 q (0, 1) := ⟨_, rfl⟩
  have ha1 : AnalyticOnNhd ℂ Ψ1 (ball 0 ε ×ˢ unitDisc) := by rw [hΨ1]; exact s5gr_dir_analytic han (0, 1)
  have ha2 : AnalyticOnNhd ℂ Ψ2 (ball 0 ε ×ˢ unitDisc) := by rw [hΨ2]; exact s5gr_dir_analytic ha1 (0, 1)
  have ha3 : AnalyticOnNhd ℂ Ψ3 (ball 0 ε ×ˢ unitDisc) := by rw [hΨ3]; exact s5gr_dir_analytic ha2 (0, 1)
  -- partial derivatives as `deriv`
  have hz' : ∀ Ψ : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) → ∀ τ ∈ ball (0 : ℂ) ε,
      ∀ z ∈ unitDisc, deriv (fun z' => Ψ (τ, z')) z = fderiv ℂ Ψ (τ, z) (0, 1) := fun Ψ hΨ τ hτ z hz =>
    (s5gr_partial_z ((hΨ _ (hmem τ hτ z hz)).differentiableAt)).deriv
  have ht' : ∀ Ψ : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) → ∀ z ∈ unitDisc,
      deriv (fun τ => Ψ (τ, z)) 0 = fderiv ℂ Ψ (0, z) (1, 0) := fun Ψ hΨ z hz =>
    (s5gr_partial_t ((hΨ _ (hmem 0 h0ε z hz)).differentiableAt)).deriv
  have hzev : ∀ Ψ : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) → ∀ τ ∈ ball (0 : ℂ) ε,
      ∀ (g : ℂ → ℂ), (∀ z ∈ unitDisc, g z = Ψ (τ, z)) → ∀ z ∈ unitDisc,
        deriv g z = fderiv ℂ Ψ (τ, z) (0, 1) := by
    intro Ψ hΨ τ hτ g hg z hz
    have hev : g =ᶠ[𝓝 z] fun z' => Ψ (τ, z') := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hg w hw
    rw [hev.deriv_eq, hz' Ψ hΨ τ hτ z hz]
  have e1 : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, deriv (F τ) z = Ψ1 (τ, z) := by
    intro τ hτ z hz
    rw [hΨ1]
    exact hzev Φ han τ hτ (F τ) (fun w _ => by rw [hΦ]) z hz
  have e2 : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, deriv (deriv (F τ)) z = Ψ2 (τ, z) := by
    intro τ hτ z hz
    rw [hΨ2]
    exact hzev Ψ1 ha1 τ hτ _ (e1 τ hτ) z hz
  have e3 : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, deriv (deriv (deriv (F τ))) z = Ψ3 (τ, z) := by
    intro τ hτ z hz
    rw [hΨ3]
    exact hzev Ψ2 ha2 τ hτ _ (e2 τ hτ) z hz
  -- `V = ∂_τ F(0, ·)` and its derivatives
  obtain ⟨V, hV⟩ : ∃ V : ℂ → ℂ, V = fun z => deriv (fun τ => F τ z) 0 := ⟨_, rfl⟩
  have hmix : ∀ Ψ : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) → ∀ z ∈ unitDisc,
      fderiv ℂ (fun q => fderiv ℂ Ψ q (1, 0)) (0, z) (0, 1) = fderiv ℂ (fun q => fderiv ℂ Ψ q (0, 1)) (0, z) (1, 0) :=
    fun Ψ hΨ z hz => s5gr_mixed (hΨ _ (hmem 0 h0ε z hz)) (1, 0) (0, 1)
  have hτa : ∀ Ψ : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) →
      AnalyticOnNhd ℂ (fun q => fderiv ℂ Ψ q (1, 0)) (ball 0 ε ×ˢ unitDisc) := fun Ψ hΨ => s5gr_dir_analytic hΨ (1, 0)
  have v0 : ∀ z ∈ unitDisc, V z = fderiv ℂ Φ (0, z) (1, 0) := by
    intro z hz
    rw [hV, ← ht' Φ han z hz, hΦ]
  have v1 : ∀ z ∈ unitDisc, deriv V z = fderiv ℂ Ψ1 (0, z) (1, 0) := by
    intro z hz
    rw [hzev _ (hτa Φ han) 0 h0ε V v0 z hz, hmix Φ han z hz, hΨ1]
  have v2 : ∀ z ∈ unitDisc, deriv (deriv V) z = fderiv ℂ Ψ2 (0, z) (1, 0) := by
    intro z hz
    rw [hzev _ (hτa Ψ1 ha1) 0 h0ε (deriv V) v1 z hz, hmix Ψ1 ha1 z hz, hΨ2]
  have v3 : ∀ z ∈ unitDisc, deriv (deriv (deriv V)) z = fderiv ℂ Ψ3 (0, z) (1, 0) := by
    intro z hz
    rw [hzev _ (hτa Ψ2 ha2) 0 h0ε (deriv (deriv V)) v2 z hz, hmix Ψ2 ha2 z hz, hΨ3]
  -- `τ`-derivatives of the `z`-jets
  have hτev : ∀ (A : ℂ → ℂ) (Ψ : ℂ × ℂ → ℂ), AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) → ∀ z ∈ unitDisc,
      (∀ τ ∈ ball (0 : ℂ) ε, A τ = Ψ (τ, z)) → deriv A 0 = fderiv ℂ Ψ (0, z) (1, 0) := by
    intro A Ψ hΨ z hz hA
    have hev : A =ᶠ[𝓝 0] fun τ => Ψ (τ, z) := by
      filter_upwards [isOpen_ball.mem_nhds h0ε] with τ hτ
      exact hA τ hτ
    rw [hev.deriv_eq, ht' Ψ hΨ z hz]
  have hV0 : V 0 = 0 := by
    rw [hV]
    show deriv (fun τ => F τ 0) 0 = 0
    have hev : (fun τ => F τ 0) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds h0ε] with τ hτ
      exact hF0 τ hτ
    rw [hev.deriv_eq, deriv_const]
  have hV1 : deriv V 0 = 0 := by
    rw [v1 0 h0D, ← hτev (fun _ => (1 : ℂ)) Ψ1 ha1 0 h0D (fun τ hτ => by rw [← e1 τ hτ 0 h0D, hF1 τ hτ]),
      deriv_const]
  have hV2 : deriv (deriv V) 0 = 2 * s := by
    rw [v2 0 h0D, ← hτev (fun τ => 2 * τ * s) Ψ2 ha2 0 h0D (fun τ hτ => by rw [← e2 τ hτ 0 h0D, hF2 τ hτ])]
    have : HasDerivAt (fun τ : ℂ => 2 * τ * s) (2 * 1 * s) 0 :=
      ((hasDerivAt_id (0 : ℂ)).const_mul 2).mul_const s
    rw [this.deriv]; ring
  -- `V''' = φ` (linearized Schwarzian)
  have hid : ∀ z ∈ unitDisc, F 0 =ᶠ[𝓝 z] id := fun z hz => by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact h0 w hw
  have hV3 : ∀ z ∈ unitDisc, deriv (deriv (deriv V)) z = φ z := by
    intro z hz
    rw [v3 z hz]
    have hd : ∀ (Ψ : ℂ × ℂ → ℂ), AnalyticOnNhd ℂ Ψ (ball 0 ε ×ˢ unitDisc) →
        DifferentiableAt ℂ (fun τ => Ψ (τ, z)) 0 := fun Ψ hΨ =>
      (s5gr_partial_t ((hΨ _ (hmem 0 h0ε z hz)).differentiableAt)).differentiableAt
    have hid1 : Ψ1 (0, z) = 1 := by rw [← e1 0 h0ε z hz, (hid z hz).deriv_eq, deriv_id]
    have hid2 : Ψ2 (0, z) = 0 := by
      rw [← e2 0 h0ε z hz, (hid z hz).deriv.deriv_eq]
      simp
    have hid3 : Ψ3 (0, z) = 0 := by
      rw [← e3 0 h0ε z hz, (hid z hz).deriv.deriv.deriv_eq]
      simp
    rw [← ht' Ψ3 ha3 z hz]
    refine s5gr_schw_lin (hd Ψ1 ha1) (hd Ψ2 ha2) (hd Ψ3 ha3) hid1 hid2 hid3 ?_
    filter_upwards [isOpen_ball.mem_nhds h0ε] with τ hτ
    have hFa : AnalyticAt ℂ (F τ) z := by
      have := (han _ (hmem τ hτ z hz))
      rw [hΦ] at this
      exact this.comp_of_eq ((analyticAt_const).prod analyticAt_id) rfl
    rw [← e1 τ hτ z hz, ← e2 τ hτ z hz, ← e3 τ hτ z hz, ← s5gr_schw_formula hFa (hF' τ hτ z hz), hS τ hτ z hz]
  -- the Taylor series of `V`
  have hVd : DifferentiableOn ℂ V (ball 0 1) := by
    have h := (hτa Φ han)
    intro z hz
    have ha : AnalyticAt ℂ (fun z' => fderiv ℂ Φ (0, z') (1, 0)) z :=
      (h _ (hmem 0 h0ε z hz)).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    refine (ha.differentiableAt.differentiableWithinAt).congr (fun w hw => v0 w hw) (v0 z hz)
  intro z hz
  have hT := Complex.hasSum_taylorSeries_on_ball hVd hz
  have hT2 := (hasSum_nat_add_iff' 2).mpr hT
  have hsum2 : ∑ i ∈ Finset.range 2, ((i.factorial : ℂ))⁻¹ • (z - 0) ^ i • iteratedDeriv i V 0 = 0 := by
    simp [Finset.sum_range_succ, hV0, hV1]
  rw [hsum2] at hT2
  simp only [sub_zero] at hT2
  have hVz : V z = deriv (fun τ => F τ z) 0 := by rw [hV]
  rw [hVz] at hT2
  convert hT2 using 1
  funext n
  have hev3 : deriv (deriv (deriv V)) =ᶠ[𝓝 0] φ := by
    filter_upwards [isOpen_ball.mem_nhds h0D] with w hw
    exact hV3 w hw
  rcases n with _ | m
  · simp only [if_true, smul_eq_mul, sub_zero]
    rw [show (0 + 2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ', iteratedDeriv_one, hV2]
    simp [Nat.factorial]
    ring
  · simp only [Nat.add_one_ne_zero, if_false, smul_eq_mul, sub_zero]
    have hid : iteratedDeriv (m + 1 + 2) V 0 = iteratedDeriv m φ 0 := by
      rw [show m + 1 + 2 = m + 1 + 1 + 1 by rfl, iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ']
      exact hev3.iteratedDeriv_eq m
    rw [hid, show m + 1 + 1 - 2 = m by omega]
    have hf : ((m + 1 + 2).factorial : ℂ) = (m.factorial : ℂ) * ((m + 1 : ℂ) * (m + 2) * (m + 3)) := by
      rw [show m + 1 + 2 = m + 3 by rfl, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hf]
    have hm0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hm1 : ((m + 1 : ℂ) * (m + 2) * (m + 3)) ≠ 0 := by
      have h : ((m + 1) * (m + 2) * (m + 3) : ℕ) ≠ 0 := by positivity
      exact_mod_cast h
    have hc : (((m + 1 + 1 : ℕ) : ℂ) ^ 3 - ((m + 1 + 1 : ℕ) : ℂ)) = (m + 1 : ℂ) * (m + 2) * (m + 3) := by
      push_cast; ring
    rw [hc]
    field_simp

/-- **Stub W6 (the curve pair).** Along `τ ↦ τ • Y`, the potential is `log|G_τ'(∞)|` for a normalized pair with
null complement and `B₃` invertible. `F_τ = λ_{c(μ_τ) - τ Y.2} ∘ f^{μ_τ}` (from `s5t53_c5_potential` and
`s5t53_c1_welding`) is jointly holomorphic, `F_0 = id`, and
`∂_τ F_τ|₀ = Y.2 z² + Σ_{k ≥ 2} i·tangentCoeff Y.1 k · z^{k+1}` (`S(F_τ) = τ Y.1`). -/
theorem s5gr_curve_pair (Y : AInf unitDisc × ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F G : ℂ → ℂ → ℂ,
      (∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ) ∧
        volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0 ∧
        potentialK (tcCoordHInv (τ • Y)) = Real.log ‖derivAtInfty (G τ)‖ ∧
        IsUnit (gopOp (B3 (grunsky (F τ) (G τ))))) ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc) ∧
      (∀ z ∈ unitDisc, F 0 z = z) ∧
      ∀ z ∈ unitDisc, HasSum
        (fun n : ℕ => (if n = 0 then Y.2 else I * tangentCoeff Y.1 (n + 1)) * z ^ (n + 2))
        (deriv (fun τ => F τ z) 0) := by
  obtain ⟨sec, ε0, hε0, hsa, hs0, hsec⟩ := s5t53_c6_section
  have himg := s5l54_image_nhds s5rh_tOrigin_mem
  rw [s5t53_tcCoordH_origin] at himg
  obtain ⟨ε1, hε1, hball1⟩ := Metric.mem_nhds_iff.mp himg
  have hm : 0 < min ε0 ε1 := lt_min hε0 hε1
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min ε0 ε1 / (‖Y‖ + 1) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hsmall : ∀ τ ∈ ball (0 : ℂ) ε, ‖τ • Y‖ < min ε0 ε1 := by
    intro τ hτ
    have h1 : ‖τ‖ < ε := mem_ball_zero_iff.mp hτ
    rw [norm_smul]
    have h2 : ε * (‖Y‖ + 1) = min ε0 ε1 := by rw [hε]; field_simp
    nlinarith [norm_nonneg Y, norm_nonneg τ]
  have hs0' : ∀ τ ∈ ball (0 : ℂ) ε, ‖τ • Y‖ < ε0 := fun τ hτ => lt_of_lt_of_le (hsmall τ hτ) (min_le_left _ _)
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ → ℂ, F = fun (τ : ℂ) (x : ℂ) =>
      lambdaW (deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2) (fB (sec (τ • Y).1) x) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ → ℂ, G = fun (τ : ℂ) (x : ℂ) => finPart (mobiusExt 1 0
      (deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2) 1 (normalizedWeldingSphere (sec (τ • Y).1)
        (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec (τ • Y).1))
          (inversion (((τ • Y).2 - deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane)))) :=
    ⟨_, rfl⟩
  have hdat : ∀ τ ∈ ball (0 : ℂ) ε, (∃ h, IsOneFixedQS h ∧ IsWeldingPrime h (F τ) (G τ)) ∧
      potentialK (tcCoordHInv (τ • Y)) = Real.log ‖derivAtInfty (G τ)‖ ∧ sec (τ • Y).1 ∈ LinfStarBall ∧
      (∀ x ∈ unitDisc, (deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2) * fB (sec (τ • Y).1) x + 1 ≠ 0) ∧
      inversion (((τ • Y).2 - deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 : ℂ) : ExtPlane) ∈
        wB (sec (τ • Y).1) '' extDiscExterior := by
    intro τ hτ
    rw [hF, hG]
    exact s5gr_line_data hε0 hsa hs0 hsec (τ • Y) (hs0' τ hτ)
  have hpairs : ∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ) ∧
      volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0 := by
    intro τ hτ
    obtain ⟨⟨h, hh, hw⟩, -⟩ := hdat τ hτ
    exact l55_disjoint_pair hh hw
  have han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc) := by
    rw [hF]
    exact s5gr_F_analytic hsa (fun τ hτ => ⟨hs0' τ hτ, (hdat τ hτ).2.2.1, (hdat τ hτ).2.2.2.1⟩)
  have h0 : ∀ z ∈ unitDisc, F 0 z = z := by
    intro z hz
    have hψb : ∀ t, ‖((Real.sin t : ℝ) : ℂ) • (0 : AInf unitDisc × ℂ)‖ < ε0 := fun t => by simpa using hε0
    have := (s5t53_c2_origin hε0 hsa hs0 hsec Real.contDiff_sin Real.sin_zero hψb).1 z hz
    rw [hF]
    simpa using this
  -- the jets of `F_τ`
  have hfB : ∀ τ ∈ ball (0 : ℂ) ε, AnalyticAt ℂ (fB (sec (τ • Y).1)) 0 ∧ fB (sec (τ • Y).1) 0 = 0 ∧
      deriv (fB (sec (τ • Y).1)) 0 = 1 := by
    intro τ hτ
    have hμ := (hdat τ hτ).2.2.1
    have hp := AppB.b8_welding_normalized_pair hμ
    rw [(r22_fsans_gsans hμ).1] at hp
    exact ⟨hp.1.analyticAt (isOpen_ball.mem_nhds (mem_ball_self one_pos)), hp.2.2.1, hp.2.2.2.1⟩
  have hF2 : ∀ τ ∈ ball (0 : ℂ) ε, deriv (deriv (F τ)) 0 = 2 * τ * Y.2 := by
    intro τ hτ
    obtain ⟨ha, h00, h01⟩ := hfB τ hτ
    rw [hF]
    show deriv (deriv (fun z => lambdaW (deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2)
      (fB (sec (τ • Y).1) z))) 0 = _
    rw [(lambdaW_comp_jets ha h00 h01 _).2, Prod.smul_snd, smul_eq_mul]
    ring
  have hS : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc, schwarzianHol (F τ) z = τ * AInf.toFun Y.1 z := by
    intro τ hτ z hz
    have hμ := (hdat τ hτ).2.2.1
    have hden := (hdat τ hτ).2.2.2.1 z hz
    obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
    obtain ⟨c, hc⟩ : ∃ c, c = deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2 := ⟨_, rfl⟩
    rw [← hc] at hden
    have hFτ : F τ = (fun w => (1 * w + 0) / (c * w + 1)) ∘ fB (sec (τ • Y).1) := by
      rw [hF, hc]; funext w
      show _ / (_ * _ + 1) = (1 * _ + 0) / (_ * _ + 1)
      ring
    have hg := hfd.analyticAt (isOpen_ball.mem_nhds hz)
    have hg' := deriv_ne_zero_of_injOn isOpen_ball hfd hfi hz
    have hden' : c * fB (sec (τ • Y).1) z + 1 ≠ 0 := hden
    have hcomp : AnalyticAt ℂ (fun w => (1 * fB (sec (τ • Y).1) w + 0) / (c * fB (sec (τ • Y).1) w + 1)) z :=
      ((analyticAt_const.mul hg).add analyticAt_const).div ((analyticAt_const.mul hg).add analyticAt_const) hden'
    have hFτ' : F τ = fun w => (1 * fB (sec (τ • Y).1) w + 0) / (c * fB (sec (τ • Y).1) w + 1) := hFτ
    rw [hFτ', ← schwarzian_of_analyticAt hcomp, schwarzian_mobius_comp_of_ne hg hg' (by simp) hden',
      schwarzian_of_analyticAt hg]
    -- `S(f^μ) = Y.1` along the line
    have hy : τ • Y ∈ tcCoordH '' TCurve :=
      hball1 (mem_ball_zero_iff.mpr (lt_of_lt_of_le (hsmall τ hτ) (min_le_right _ _)))
    have hHy : tcCoordH (tcCoordHInv (τ • Y)) = τ • Y := Function.invFunOn_eq hy
    obtain ⟨h, hb, -⟩ := hsec (τ • Y) (hs0' τ hτ)
    have hbers : bersPhi (sec (τ • Y).1) = (τ • Y).1 := by
      have h1 := congrArg Prod.fst hHy
      rw [hb] at h1
      have h2 : bers (Phi ⟨sec (τ • Y).1, h⟩) = (τ • Y).1 := h1
      rwa [bers_Phi] at h2
    have hsp := (schwarzianHol_AInf_spec hfd hfi).1 z hz
    rw [← hsp]
    change AInf.toFun (bersPhi (sec (τ • Y).1)) z = _
    rw [hbers]
    show unweight unitDisc (τ • Y.1).1 z = τ * unweight unitDisc Y.1.1 z
    rw [Submodule.coe_smul, unweight_smul]
    rfl
  have hjet := s5gr_jet hεpos (s := Y.2) (φ := AInf.toFun Y.1) han h0
    (fun τ hτ => (hpairs τ hτ).1.2.2.1) (fun τ hτ => (hpairs τ hτ).1.2.2.2.1) hF2
    (fun τ hτ z hz => deriv_ne_zero_of_injOn isOpen_ball (hpairs τ hτ).1.1 (hpairs τ hτ).1.2.1 hz) hS
  refine ⟨ε, hεpos, F, G, fun τ hτ => ⟨(hpairs τ hτ).1, (hpairs τ hτ).2, (hdat τ hτ).2.1, ?_⟩, han, h0, ?_⟩
  · exact s5gr_B3_unit (hdat τ hτ).2.2.1 (c := deriv (deriv (fB (sec (τ • Y).1))) 0 / 2 - (τ • Y).2)
      (ζ := (τ • Y).2 - deriv (deriv (fB (sec (τ • Y).1))) 0 / 2) (by ring) (hpairs τ hτ).1 (hpairs τ hτ).2
      (fun z _ => by rw [hF]) (hdat τ hτ).2.2.2.1 (hdat τ hτ).2.2.2.2 (fun x _ => by rw [hG])
  · intro z hz
    convert hjet z hz using 1
    funext n
    rcases n with _ | n
    · simp
    · simp only [Nat.add_one_ne_zero, if_false]
      congr 1
      show I * (iteratedDeriv (n + 1 + 1 - 2) (AInf.toFun Y.1) 0 / ((n + 1 + 1 - 2).factorial : ℂ) /
        (I * (((n + 1 + 1 : ℕ) : ℂ) ^ 3 - ((n + 1 + 1 : ℕ) : ℂ)))) = _
      rw [mul_div_assoc', mul_div_mul_left _ _ Complex.I_ne_zero]

/-- Cauchy estimate for power-series coefficients: `|d_m| ≤ K (ρ/2)^{-m}` if `Σ d_m z^m = h` on `B(0, ρ)`, `|h| ≤ K`. -/
theorem s5gr_coeff_bound {h : ℂ → ℂ} {d : ℕ → ℂ} {ρ K : ℝ} (hρ : 0 < ρ) (hh : DifferentiableOn ℂ h (ball 0 ρ))
    (hK : ∀ z ∈ ball (0 : ℂ) ρ, ‖h z‖ ≤ K) (hd : ∀ z ∈ ball (0 : ℂ) ρ, HasSum (fun m => d m * z ^ m) (h z))
    (m : ℕ) : ‖d m‖ ≤ K / (ρ / 2) ^ m := by
  have hr0 : 0 < ρ / 2 := half_pos hρ
  set r : NNReal := ⟨ρ / 2, hr0.le⟩ with hr
  have hrr : (r : ℝ) = ρ / 2 := rfl
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 ρ := closedBall_subset_ball (by rw [hrr]; linarith)
  have hdc : DiffContOnCl ℂ h (ball (0 : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by rw [hrr]; exact hr0.ne')]
    exact hh.mono hsub
  have hP := hdc.hasFPowerSeriesOnBall (by rw [← NNReal.coe_pos, hrr]; exact hr0)
  have hQ : HasFPowerSeriesAt h (FormalMultilinearSeries.ofScalars ℂ d) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using hd z hz
  have heq := hP.hasFPowerSeriesAt.eq_formalMultilinearSeries hQ
  have hc : d m = (cauchyPowerSeries h 0 r).coeff m := by
    rw [heq, FormalMultilinearSeries.coeff_ofScalars]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  rw [hc]
  calc ‖(cauchyPowerSeries h 0 r).coeff m‖ ≤ ‖cauchyPowerSeries h 0 r m‖ := by
        rw [FormalMultilinearSeries.coeff]
        refine ((cauchyPowerSeries h 0 r m).le_opNorm _).trans ?_
        simp
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖h (circleMap 0 r θ)‖) * |(r : ℝ)|⁻¹ ^ m :=
        norm_cauchyPowerSeries_le h 0 r m
    _ ≤ ((2 * π)⁻¹ * ∫ _θ : ℝ in 0..2 * π, K) * |(r : ℝ)|⁻¹ ^ m := by
        gcongr
        refine intervalIntegral.integral_mono_on (by positivity) ?_ (by simp) ?_
        · have hcm : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
          refine (ContinuousOn.comp_continuous (hh.continuousOn.mono hsub) hcm ?_).norm.intervalIntegrable (μ := MeasureTheory.volume) _ _
          intro θ
          exact sphere_subset_closedBall (circleMap_mem_sphere 0 r.2 θ)
        · intro θ _
          exact hK _ (hsub (sphere_subset_closedBall (circleMap_mem_sphere 0 r.2 θ)))
    _ = K / (ρ / 2) ^ m := by
        rw [intervalIntegral.integral_const, hrr, abs_of_pos hr0, smul_eq_mul, inv_pow, sub_zero]
        have hπ := Real.pi_ne_zero
        field_simp

/-- **Parametric Taylor coefficients (G1).** If `H(τ, ·) = Σ d_m(τ) z^m` on `B(0, ρ)` for `τ ∈ B(0, δ)`, with `H`
holomorphic in each variable and bounded, then each `d_m` is holomorphic on `B(0, δ)` and
`∂_τ H(0, z) = Σ d_m'(0) z^m` on `B(0, ρ/2)`. -/
theorem s5gr_param_coeff {H : ℂ → ℂ → ℂ} {d : ℕ → ℂ → ℂ} {δ ρ K : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hHτ : ∀ z ∈ ball (0 : ℂ) ρ, DifferentiableOn ℂ (fun τ => H τ z) (ball 0 δ))
    (hHz : ∀ τ ∈ ball (0 : ℂ) δ, DifferentiableOn ℂ (H τ) (ball 0 ρ))
    (hK : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) ρ, ‖H τ z‖ ≤ K)
    (hd : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) ρ, HasSum (fun m => d m τ * z ^ m) (H τ z)) :
    (∀ m, DifferentiableOn ℂ (d m) (ball 0 δ)) ∧
      ∀ z ∈ ball (0 : ℂ) (ρ / 2), HasSum (fun m => deriv (d m) 0 * z ^ m) (deriv (fun τ => H τ z) 0) := by
  have hbd : ∀ τ ∈ ball (0 : ℂ) δ, ∀ m, ‖d m τ‖ ≤ K / (ρ / 2) ^ m := fun τ hτ m =>
    s5gr_coeff_bound hρ (hHz τ hτ) (hK τ hτ) (hd τ hτ) m
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hδ) 0 (mem_ball_self hρ))
  have hr4 : 0 < ρ / 4 := by positivity
  -- holomorphy of the coefficients (discrete Fourier extraction, `b1_df_coeff_diff`)
  have hdiff : ∀ m, DifferentiableOn ℂ (d m) (ball 0 δ) := by
    intro m
    have hc := AppB.b1_df_coeff_diff isOpen_ball (c := fun t p q => if q = 0 then d p t else 0)
      (L := fun p q => if q = 0 then K / (ρ / 2) ^ p else 0) (ρ1 := ρ / 4) (ρ2 := 1 / 2) hr4 (by norm_num)
      (fun p q => by split_ifs <;> positivity)
      (by
        have hs : Summable (fun p : ℕ => K / (ρ / 2) ^ p * (ρ / 4) ^ p) := by
          have e : (fun p : ℕ => K / (ρ / 2) ^ p * (ρ / 4) ^ p) = fun p => K * (1 / 2 : ℝ) ^ p := by
            funext p
            rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow]
            congr 2
            field_simp
            ring
          rw [e]
          exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left K
        have hinj : Function.Injective (fun p : ℕ => (p, 0)) := fun a b h => (Prod.mk.inj h).1
        refine (hinj.summable_iff (fun x hx => ?_)).mp ?_
        · have hx2 : x.2 ≠ 0 := by
            intro h0; exact hx ⟨x.1, Prod.ext rfl h0.symm⟩
          simp [hx2]
        · exact hs.congr fun p => by simp)
      (fun t ht p q => by
        split_ifs
        · exact hbd t ht p
        · simp)
      (by
        intro z w hz hw
        have hzρ : z ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.mpr (by rw [hz]; linarith)
        refine (hHτ z hzρ).congr fun t ht => ?_
        have hinj : Function.Injective (fun p : ℕ => (p, 0)) := fun a b h => (Prod.mk.inj h).1
        have hs := hd t ht z hzρ
        have h2 : HasSum (fun r : ℕ × ℕ => (if r.2 = 0 then d r.1 t else 0) * z ^ r.1 * w ^ r.2) (H t z) := by
          refine (hinj.hasSum_iff (fun x hx => ?_)).mp ?_
          · have hx2 : x.2 ≠ 0 := by
              intro h0; exact hx ⟨x.1, Prod.ext rfl h0.symm⟩
            simp [hx2]
          · convert hs using 1
            funext p
            simp
        exact h2.tsum_eq)
      m 0
    simpa using hc
  refine ⟨hdiff, fun z hz => ?_⟩
  -- termwise differentiation on `B(0, δ/2)`
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hz1 : ‖z‖ < ρ / 2 := mem_ball_zero_iff.mp hz
  have hzρ : z ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.mpr (by linarith)
  have hder : ∀ m (y : ℂ), y ∈ ball (0 : ℂ) (δ / 2) → ‖deriv (d m) y‖ ≤ K / (ρ / 2) ^ m / (δ / 2) := by
    intro m y hy
    have hsub : closedBall y (δ / 2) ⊆ ball (0 : ℂ) δ := by
      intro u hu
      rw [mem_ball_zero_iff]
      have h1 := mem_closedBall.mp hu
      have h2 := mem_ball_zero_iff.mp hy
      calc ‖u‖ ≤ ‖u - y‖ + ‖y‖ := by simpa using norm_add_le (u - y) y
        _ < δ := by rw [← dist_eq_norm]; linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ2
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hδ2.ne']
      exact (hdiff m).mono hsub
    · intro u hu
      exact hbd u (hsub (sphere_subset_closedBall hu)) m
  set u : ℕ → ℝ := fun m => K / (ρ / 2) ^ m / (δ / 2) * ‖z‖ ^ m with hu
  have hus : Summable u := by
    have hq : ‖z‖ / (ρ / 2) < 1 := by rw [div_lt_one (by positivity)]; exact hz1
    have e : u = fun m => K / (δ / 2) * (‖z‖ / (ρ / 2)) ^ m := by
      funext m; rw [hu, div_pow]; field_simp
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) hq).mul_left _
  have hD := hasDerivAt_tsum_of_isPreconnected (g := fun m τ => d m τ * z ^ m)
    (g' := fun m τ => deriv (d m) τ * z ^ m) hus isOpen_ball (convex_ball _ _).isPreconnected
    (fun m y hy => ((hdiff m).differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith) hy))).hasDerivAt.mul_const _)
    (fun m y hy => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (hder m y hy) (by positivity))
    (mem_ball_self hδ2) (hd 0 (mem_ball_self hδ) z hzρ).summable (mem_ball_self hδ2)
  have hev : (fun τ => ∑' m, d m τ * z ^ m) =ᶠ[𝓝 (0 : ℂ)] fun τ => H τ z := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with τ hτ
    exact (hd τ hτ z hzρ).tsum_eq
  rw [← hev.deriv_eq, hD.deriv]
  refine (hus.of_norm_bounded fun m => ?_).hasSum
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hder m 0 (mem_ball_self hδ2)) (by positivity)

/-- Power-series uniqueness on a ball around `0`. -/
theorem s5gr_coeff_unique {p q : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hp : ∀ z ∈ ball (0 : ℂ) r, HasSum (fun n => p n * z ^ n) (f z))
    (hq : ∀ z ∈ ball (0 : ℂ) r, HasSum (fun n => q n * z ^ n) (f z)) : p = q := by
  have hP : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ p) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using hp z hz
  have hQ : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ q) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using hq z hz
  have heq := hP.eq_formalMultilinearSeries hQ
  funext n
  have := congrArg (fun P => FormalMultilinearSeries.coeff P n) heq
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using this

/-- The axis series: `f(z) = z exp(-Σ_{n ≥ 1} b_{-n,0} zⁿ)` on `𝔻` (the third clause of `IsGrunskyCoeff` at
`ζ = 0`; as in `s310_w1_series`). -/
theorem s5gr_axis {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (if n = 0 then 0 else grunsky f g (-(n : ℤ)) 0) * z ^ n)
        (∑' n : ℕ, (if n = 0 then 0 else grunsky f g (-(n : ℤ)) 0) * z ^ n) ∧
      f z = z * exp (-∑' n : ℕ, (if n = 0 then 0 else grunsky f g (-(n : ℤ)) 0) * z ^ n) := by
  have hspec := (grunsky_spec h).1
  have hf0 : f 0 = 0 := h.2.2.1
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n : ℕ => if n = 0 then 0 else grunsky f g (-(n : ℤ)) 0 := ⟨_, rfl⟩
  suffices key : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (∑' n, c n * z ^ n) ∧
      f z = z * exp (-∑' n, c n * z ^ n) by
    subst hc; exact key
  have hser : ∀ z ∈ unitDisc, z ≠ 0 → ∃ D, HasSum (fun n => c n * z ^ n) D ∧ f z / z = exp (-D) := by
    intro z hz hz0
    obtain ⟨S, hS, he⟩ := hspec.2.2.2.1 z hz 0 (mem_ball_self one_pos) hz0
    have hT : HasSum (fun n : ℕ => grunsky f g (-(n : ℤ)) 0 * z ^ n) S := by
      refine hS.prod_fiberwise (fun n => ?_)
      apply (hasSum_ite_eq (0 : ℕ) (grunsky f g (-(n : ℤ)) 0 * z ^ n)).congr_fun
      intro m
      by_cases hm : m = 0
      · subst hm; simp
      · simp [hm]
    refine ⟨S - grunsky f g 0 0, ?_, ?_⟩
    · have h1 := hT.sub (hasSum_ite_eq (0 : ℕ) (grunsky f g 0 0))
      refine h1.congr_fun (fun n => ?_)
      by_cases hn : n = 0
      · subst hn; simp [hc]
      · simp [hc, hn]
    · rw [hf0, sub_zero, sub_zero] at he
      rw [he]
      congr 1
      ring
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : (fun n => c n * (0 : ℂ) ^ n) = fun _ => 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn; simp [hc]
      · simp [zero_pow hn]
    rw [h0, hf0, zero_mul]
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  · obtain ⟨D, hD, he⟩ := hser z hz hz0
    refine ⟨hD.summable.hasSum, ?_⟩
    rw [hD.tsum_eq, ← he]
    field_simp

/-- `‖w - 1‖ ≤ 1/4` puts `w` in the slit plane. -/
theorem s5gr_slit {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 4) : w ∈ slitPlane ∧ w ≠ 0 := by
  have h1 : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h1
  have hre : 0 < w.re := by linarith [(abs_le.mp (h1.trans hw)).1]
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl hre), fun h => ?_⟩
  rw [h, Complex.zero_re] at hre
  exact lt_irrefl _ hre

/-- Near the identity: `|F_τ(z) - z| ≤ |z|/4` for `|τ| < δ`, `|z| < 1/2` (tube lemma + Schwarz). -/
theorem s5gr_near_id {ε : ℝ} (hε : 0 < ε) {F : ℂ → ℂ → ℂ}
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc))
    (h0 : ∀ z ∈ unitDisc, F 0 z = z) (hF0 : ∀ τ ∈ ball (0 : ℂ) ε, F τ 0 = 0) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) (1 / 2), ‖F τ z - z‖ ≤ ‖z‖ / 4 := by
  obtain ⟨n, hn⟩ : ∃ n : Set (ℂ × ℂ), n = (ball (0 : ℂ) ε ×ˢ unitDisc) ∩
      (fun p : ℂ × ℂ => F p.1 p.2 - p.2) ⁻¹' ball 0 (1 / 8) := ⟨_, rfl⟩
  have hno : IsOpen n := by
    rw [hn]
    apply ContinuousOn.isOpen_inter_preimage _ (isOpen_ball.prod isOpen_ball) isOpen_ball
    exact han.continuousOn.sub continuous_snd.continuousOn
  have hsub : ({0} : Set ℂ) ×ˢ closedBall (0 : ℂ) (1 / 2) ⊆ n := by
    rintro ⟨τ, z⟩ ⟨hτ, hz⟩
    simp only [mem_singleton_iff] at hτ
    subst hτ
    have hz1 : z ∈ unitDisc :=
      mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (by norm_num))
    rw [hn]
    refine ⟨⟨mem_ball_self hε, hz1⟩, ?_⟩
    show F 0 z - z ∈ ball (0 : ℂ) (1 / 8)
    rw [h0 z hz1, sub_self]
    exact mem_ball_self (by norm_num)
  obtain ⟨u, v, hu, -, hu0, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall (0 : ℂ) (1 / 2)) hno hsub
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.mp hu 0 (hu0 rfl)
  refine ⟨min δ0 ε, lt_min hδ0 hε, min_le_right _ _, fun τ hτ z hz => ?_⟩
  have hτu : τ ∈ u := hball (ball_subset_ball (min_le_left _ _) hτ)
  have hmem : ∀ w ∈ ball (0 : ℂ) (1 / 2), (τ, w) ∈ n := fun w hw =>
    huv ⟨hτu, hv (ball_subset_closedBall hw)⟩
  rw [hn] at hmem
  have hτε : τ ∈ ball (0 : ℂ) ε := (hmem 0 (mem_ball_self (by norm_num))).1.1
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun w => F τ w - w := ⟨_, rfl⟩
  have hgd : DifferentiableOn ℂ g (ball 0 (1 / 2)) := by
    intro w hw
    have hw1 : w ∈ unitDisc := (hmem w hw).1.2
    have ha := han (τ, w) ⟨hτε, hw1⟩
    have hd : DifferentiableAt ℂ (fun w => F τ w) w :=
      ha.differentiableAt.comp w ((differentiableAt_const τ).prodMk differentiableAt_id)
    rw [hg]
    exact (hd.sub differentiableAt_id).differentiableWithinAt
  have hg0 : g 0 = 0 := by rw [hg]; simp [hF0 τ hτε]
  have hmaps : MapsTo g (ball 0 (1 / 2)) (closedBall (g 0) (1 / 8)) := by
    intro w hw
    rw [hg0, hg]
    exact ball_subset_closedBall (hmem w hw).2
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps hz
  rw [hg0, dist_zero_right, dist_zero_right] at hs
  have hgz : g z = F τ z - z := by rw [hg]
  rw [hgz] at hs
  calc ‖F τ z - z‖ ≤ 1 / 8 / (1 / 2) * ‖z‖ := hs
    _ = ‖z‖ / 4 := by ring

/-- **The log family.** For a holomorphic family of normalized pairs with `F_0 = id`, the axis coefficients
`b_{-n,0}(τ)` are holomorphic near `τ = 0` and `Σ_n ∂_τ b_{-n,0}(0) zⁿ = -∂_τ F_τ(z)|₀ / z` for `0 < |z| < 1/4`
(`log(F_τ(z)/z) = -Σ b_{-n,0} zⁿ` and `s5gr_param_coeff`). -/
theorem s5gr_log_family {ε : ℝ} (hε : 0 < ε) {F G : ℂ → ℂ → ℂ}
    (hpair : ∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ))
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc))
    (h0 : ∀ z ∈ unitDisc, F 0 z = z) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧
      (∀ n : ℕ, DifferentiableOn ℂ (fun τ => if n = 0 then 0 else grunsky (F τ) (G τ) (-(n : ℤ)) 0)
        (ball 0 δ)) ∧
      ∀ z ∈ ball (0 : ℂ) (1 / 4), z ≠ 0 →
        HasSum (fun n : ℕ => deriv (fun τ => if n = 0 then 0 else grunsky (F τ) (G τ) (-(n : ℤ)) 0) 0 * z ^ n)
          (-(deriv (fun τ => F τ z) 0 / z)) := by
  have hF0 : ∀ τ ∈ ball (0 : ℂ) ε, F τ 0 = 0 := fun τ hτ => (hpair τ hτ).2.2.1
  obtain ⟨δ, hδ, hδε, hnear⟩ := s5gr_near_id hε han h0 hF0
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ → ℂ,
      c = fun (n : ℕ) (τ : ℂ) => if n = 0 then 0 else grunsky (F τ) (G τ) (-(n : ℤ)) 0 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ → ℂ, H = fun τ z => ∑' n, c n τ * z ^ n := ⟨_, rfl⟩
  have hτε : ∀ τ ∈ ball (0 : ℂ) δ, τ ∈ ball (0 : ℂ) ε := fun τ hτ => ball_subset_ball hδε hτ
  have hz1 : ∀ z ∈ ball (0 : ℂ) (1 / 2), z ∈ unitDisc := fun z hz => ball_subset_ball (by norm_num) hz
  have hser : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z ∈ unitDisc,
      HasSum (fun n => c n τ * z ^ n) (H τ z) ∧ F τ z = z * exp (-H τ z) := by
    intro τ hτ z hz
    subst hH hc
    exact s5gr_axis (hpair τ hτ) z hz
  have hFd : ∀ τ ∈ ball (0 : ℂ) ε, DifferentiableOn ℂ (F τ) unitDisc := fun τ hτ => (hpair τ hτ).1
  have hQval : ∀ τ ∈ ball (0 : ℂ) ε, ∀ z, z ≠ 0 → dslope (F τ) 0 z = F τ z / z := by
    intro τ hτ z hz
    rw [dslope_of_ne _ hz, slope_def_field, hF0 τ hτ, sub_zero, sub_zero]
  have hQ0 : ∀ τ ∈ ball (0 : ℂ) ε, dslope (F τ) 0 0 = 1 := fun τ hτ => by
    rw [dslope_same]; exact (hpair τ hτ).2.2.2.1
  have hQnear : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) (1 / 2), ‖dslope (F τ) 0 z - 1‖ ≤ 1 / 4 := by
    intro τ hτ z hz
    by_cases hz0 : z = 0
    · subst hz0; rw [hQ0 τ (hτε τ hτ), sub_self, norm_zero]; norm_num
    · rw [hQval τ (hτε τ hτ) z hz0]
      have e : F τ z / z - 1 = (F τ z - z) / z := by field_simp
      rw [e, norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]
      have := hnear τ hτ z hz
      linarith
  -- `H_τ = -log (F_τ(z)/z)` on `B(0, 1/2)`
  have hHlog : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) (1 / 2), H τ z = -log (dslope (F τ) 0 z) := by
    intro τ hτ
    have hτ' := hτε τ hτ
    haveI : PreconnectedSpace (ball (0 : ℂ) (1 / 2)) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : ℂ) (1 / 2)).isPreconnected
    have hHc : ContinuousOn (H τ) unitDisc :=
      (differentiableOn_of_powerSeries fun z hz => (hser τ hτ' z hz).1).continuousOn
    have hQd : DifferentiableOn ℂ (dslope (F τ) 0) unitDisc :=
      (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr (hFd τ hτ')
    have hc1 : Continuous (fun x : ball (0 : ℂ) (1 / 2) => -H τ (x : ℂ)) :=
      (hHc.comp_continuous continuous_subtype_val (fun x => hz1 _ x.2)).neg
    have hc2 : Continuous (fun x : ball (0 : ℂ) (1 / 2) => log (dslope (F τ) 0 (x : ℂ))) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hx := hz1 _ x.2
      have hsl := (s5gr_slit (hQnear τ hτ _ x.2)).1
      exact ((continuousAt_clog hsl).comp (hQd.continuousOn.continuousAt (isOpen_ball.mem_nhds hx))).comp
        continuous_subtype_val.continuousAt
    have hH0 : H τ 0 = 0 := by
      have h1 := (hser τ hτ' 0 (mem_ball_self one_pos)).1
      have e : (fun n => c n τ * (0 : ℂ) ^ n) = fun _ => 0 := by
        funext n
        by_cases hn : n = 0
        · subst hn; simp [hc]
        · simp [zero_pow hn]
      rw [e] at h1
      exact h1.unique hasSum_zero
    have hexp : ∀ x ∈ ball (0 : ℂ) (1 / 2), exp (-H τ x) = exp (log (dslope (F τ) 0 x)) := by
      intro x hx
      rw [exp_log (s5gr_slit (hQnear τ hτ x hx)).2]
      by_cases hx0 : x = 0
      · subst hx0; rw [hH0, neg_zero, exp_zero, hQ0 τ hτ']
      · rw [hQval τ hτ' x hx0, (hser τ hτ' x (hz1 x hx)).2, mul_div_cancel_left₀ _ hx0]
    have hu := continuous_exp_lift_unique hc1 hc2 (fun x => hexp x x.2)
      (x₀ := ⟨0, mem_ball_self (by norm_num)⟩)
      (show -H τ 0 = log (dslope (F τ) 0 0) by rw [hH0, hQ0 τ hτ', log_one, neg_zero])
    intro z hz
    have := congrFun hu ⟨z, hz⟩
    simp only at this
    linear_combination -this
  have hK : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) (1 / 2), ‖H τ z‖ ≤ 1 := by
    intro τ hτ z hz
    rw [hHlog τ hτ z hz, norm_neg]
    have h := hQnear τ hτ z hz
    have hl := Complex.norm_log_one_add_half_le_self (z := dslope (F τ) 0 z - 1) (by linarith)
    have e : 1 + (dslope (F τ) 0 z - 1) = dslope (F τ) 0 z := by ring
    rw [e] at hl
    linarith
  have hFτ : ∀ z ∈ unitDisc, ∀ τ ∈ ball (0 : ℂ) ε, DifferentiableAt ℂ (fun τ => F τ z) τ :=
    fun z hz τ hτ => by
      have ha := han (τ, z) ⟨hτ, hz⟩
      have hp : DifferentiableAt ℂ (fun t : ℂ => (t, z)) τ :=
        differentiableAt_id.prodMk (differentiableAt_const z)
      exact ha.differentiableAt.comp τ hp
  have hHτ : ∀ z ∈ ball (0 : ℂ) (1 / 2), DifferentiableOn ℂ (fun τ => H τ z) (ball 0 δ) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      refine (differentiableOn_const (0 : ℂ)).congr fun τ hτ => ?_
      rw [hHlog τ hτ 0 hz, hQ0 τ (hτε τ hτ), log_one, neg_zero]
    · refine DifferentiableOn.congr (f := fun τ => -log (F τ z / z)) ?_ fun τ hτ => ?_
      · intro τ hτ
        have hsl := s5gr_slit (hQnear τ hτ z hz)
        rw [hQval τ (hτε τ hτ) z hz0] at hsl
        exact (((hFτ z (hz1 z hz) τ (hτε τ hτ)).div_const z).clog hsl.1).neg.differentiableWithinAt
      · rw [hHlog τ hτ z hz, hQval τ (hτε τ hτ) z hz0]
  have hHz : ∀ τ ∈ ball (0 : ℂ) δ, DifferentiableOn ℂ (H τ) (ball 0 (1 / 2)) := fun τ hτ =>
    (differentiableOn_of_powerSeries fun z hz => (hser τ (hτε τ hτ) z hz).1).mono fun z hz => hz1 z hz
  have hd : ∀ τ ∈ ball (0 : ℂ) δ, ∀ z ∈ ball (0 : ℂ) (1 / 2), HasSum (fun n => c n τ * z ^ n) (H τ z) :=
    fun τ hτ z hz => (hser τ (hτε τ hτ) z (hz1 z hz)).1
  obtain ⟨hcd, hsum⟩ := s5gr_param_coeff hδ (by norm_num : (0 : ℝ) < 1 / 2) hHτ hHz hK hd
  refine ⟨δ, hδ, hδε, fun n => by subst hc; exact hcd n, fun z hz hz0 => ?_⟩
  have hz2 : z ∈ ball (0 : ℂ) (1 / 2 / 2) := by
    rw [show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num]; exact hz
  have hS := hsum z hz2
  have hz' : z ∈ ball (0 : ℂ) (1 / 2) := ball_subset_ball (by norm_num) hz
  have hev : (fun τ => H τ z) =ᶠ[𝓝 (0 : ℂ)] fun τ => -log (F τ z / z) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with τ hτ
    rw [hHlog τ hτ z hz', hQval τ (hτε τ hτ) z hz0]
  have hsl0 : F 0 z / z ∈ slitPlane := by
    rw [h0 z (hz1 z hz'), div_self hz0]; exact Complex.one_mem_slitPlane
  have hdd : HasDerivAt (fun τ => -log (F τ z / z)) (-(deriv (fun τ => F τ z) 0 / z / (F 0 z / z))) 0 :=
    (((hFτ z (hz1 z hz') 0 (mem_ball_self hε)).hasDerivAt.div_const z).clog hsl0).neg
  rw [hev.deriv_eq, hdd.deriv, h0 z (hz1 z hz'), div_self hz0, div_one] at hS
  subst hc
  exact hS

/-- Second-order Schwarz lemma: `|ψ'(0)| ≤ A/R` and `|ψ(τ) - τψ'(0)| ≤ 2A(|τ|/R)²` for `|ψ| ≤ A` on `B(0, R)`,
`ψ(0) = 0`. -/
theorem s5gr_schwarz2 {ψ : ℂ → ℂ} {R A : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ ψ (ball 0 R))
    (hA : ∀ σ ∈ ball (0 : ℂ) R, ‖ψ σ‖ ≤ A) (h0 : ψ 0 = 0) :
    ‖deriv ψ 0‖ ≤ A / R ∧ ∀ τ ∈ ball (0 : ℂ) R, ‖ψ τ - τ * deriv ψ 0‖ ≤ 2 * A * (‖τ‖ / R) ^ 2 := by
  have hmaps : MapsTo ψ (ball 0 R) (closedBall (ψ 0) A) := fun σ hσ => by
    rw [h0, mem_closedBall_zero_iff]; exact hA σ hσ
  have hD := Complex.norm_deriv_le_div_of_mapsTo_ball hd hmaps hR
  refine ⟨hD, fun τ hτ => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun σ => ψ σ - σ * deriv ψ 0 := ⟨_, rfl⟩
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    rw [hg]; exact hd.sub (differentiableOn_id.mul_const _)
  have hg0 : g 0 = 0 := by rw [hg]; simp [h0]
  have hgm : MapsTo g (ball 0 R) (closedBall (g 0) (2 * A)) := by
    intro σ hσ
    rw [hg0, mem_closedBall_zero_iff, hg]
    have h1 := hA σ hσ
    have h2 : ‖σ‖ < R := mem_ball_zero_iff.mp hσ
    calc ‖ψ σ - σ * deriv ψ 0‖ ≤ ‖ψ σ‖ + ‖σ‖ * ‖deriv ψ 0‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ A + R * (A / R) := by gcongr
      _ = 2 * A := by field_simp; ring
  have hlo : (g · - g 0) =o[𝓝 0] (fun w => ‖w - 0‖ ^ 1) := by
    have hda : HasDerivAt ψ (deriv ψ 0) 0 := (hd.differentiableAt (ball_mem_nhds 0 hR)).hasDerivAt
    have hl := (hasDerivAt_iff_isLittleO.mp hda).norm_right
    refine (hl.congr_left fun σ => ?_).congr_right fun σ => by rw [pow_one]
    rw [hg0, hg, h0]
    simp [smul_eq_mul, mul_comm]
  have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hgd hgm hlo hτ
  rw [hg0, dist_zero_right, dist_zero_right] at hs
  have hgt : g τ = ψ τ - τ * deriv ψ 0 := by rw [hg]
  rw [hgt] at hs
  exact hs

/-- `0 ≤ S ≤ a√S` gives `S ≤ a²`. -/
theorem s5gr_sq_of_le_sqrt {S a : ℝ} (hS : 0 ≤ S) (ha : 0 ≤ a) (h : S ≤ a * Real.sqrt S) : S ≤ a ^ 2 := by
  have hs := Real.sq_sqrt hS
  have hs0 := Real.sqrt_nonneg S
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · have hS0 : S = 0 := by rw [← hs, ← h0]; norm_num
    rw [hS0]; positivity
  · have : Real.sqrt S ≤ a := by nlinarith
    nlinarith

/-- Truncated `ℓ²` Schwarz estimates for a holomorphic family of sequences with `Σ_{j<N} |φ_j|² ≤ M`. -/
theorem s5gr_trunc {φ : ℕ → ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hd : ∀ j, DifferentiableOn ℂ (φ j) (ball 0 R)) (h0 : ∀ j, φ j 0 = 0)
    (hb : ∀ σ ∈ ball (0 : ℂ) R, ∀ N, ∑ j ∈ Finset.range N, ‖φ j σ‖ ^ 2 ≤ M) (v : ℕ → ℂ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, conj (v j) * deriv (φ j) 0‖ ≤
        Real.sqrt (∑ j ∈ Finset.range N, ‖v j‖ ^ 2) * Real.sqrt M / R ∧
      ∀ τ ∈ ball (0 : ℂ) R, ‖∑ j ∈ Finset.range N, conj (v j) * (φ j τ - τ * deriv (φ j) 0)‖ ≤
        2 * (Real.sqrt (∑ j ∈ Finset.range N, ‖v j‖ ^ 2) * Real.sqrt M) * (‖τ‖ / R) ^ 2 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = fun σ => ∑ j ∈ Finset.range N, conj (v j) * φ j σ := ⟨_, rfl⟩
  have hψd : DifferentiableOn ℂ ψ (ball 0 R) := by
    rw [hψ]
    exact DifferentiableOn.fun_sum fun j _ => (hd j).const_mul _
  have hψ0 : ψ 0 = 0 := by rw [hψ]; simp [h0]
  have hψb : ∀ σ ∈ ball (0 : ℂ) R, ‖ψ σ‖ ≤ Real.sqrt (∑ j ∈ Finset.range N, ‖v j‖ ^ 2) * Real.sqrt M := by
    intro σ hσ
    rw [hψ]
    calc ‖∑ j ∈ Finset.range N, conj (v j) * φ j σ‖ ≤ ∑ j ∈ Finset.range N, ‖v j‖ * ‖φ j σ‖ :=
          (norm_sum_le _ _).trans (by simp [norm_mul])
      _ ≤ Real.sqrt (∑ j ∈ Finset.range N, ‖v j‖ ^ 2) * Real.sqrt (∑ j ∈ Finset.range N, ‖φ j σ‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hb σ hσ N)) (Real.sqrt_nonneg _)
  have hψD : deriv ψ 0 = ∑ j ∈ Finset.range N, conj (v j) * deriv (φ j) 0 := by
    have hh : HasDerivAt ψ (∑ j ∈ Finset.range N, conj (v j) * deriv (φ j) 0) 0 := by
      rw [hψ]
      apply HasDerivAt.fun_sum
      intro j _
      exact (((hd j).differentiableAt (ball_mem_nhds 0 hR)).hasDerivAt).const_mul _
    exact hh.deriv
  obtain ⟨hs1, hs2⟩ := s5gr_schwarz2 hR hψd hψb hψ0
  rw [hψD] at hs1 hs2
  refine ⟨hs1, fun τ hτ => ?_⟩
  have e : ∑ j ∈ Finset.range N, conj (v j) * (φ j τ - τ * deriv (φ j) 0) =
      ψ τ - τ * ∑ j ∈ Finset.range N, conj (v j) * deriv (φ j) 0 := by
    rw [hψ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact hs2 τ hτ

/-- `B₁` as a finite bilinear form of norm `≤ 1` (`eq_2_2`). -/
theorem s5gr_finBil_B1 {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) : AppB.FinBil (B1 (grunsky f g)) 1 := by
  apply AppB.b1_finBil_of_contractive
  intro x hx
  obtain ⟨-, C, hC⟩ := gop_grunsky_bounds h hF (B1 (grunsky f g)) (by simp)
  have hle := (eq_2_2 h hF).2.2.2.2 (B1 (grunsky f g)) (by simp) x hx
  exact ⟨summable_of_sum_range_le (fun _ => sq_nonneg _) (hC x hx), hle⟩

/-- `B₁ = 0` when `f = id` on `𝔻` (`K₁ = 0` off the diagonal, continuity, uniqueness of the double series). -/
theorem s5gr_B1_zero {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (hid : ∀ z ∈ unitDisc, f z = z)
    (m n : ℕ) : B1 (grunsky f g) m n = 0 := by
  have hder : ∀ z ∈ unitDisc, deriv f z = 1 := by
    intro z hz
    have hev : f =ᶠ[𝓝 z] id := by
      filter_upwards [isOpen_ball.mem_nhds hz] with u hu
      exact hid u hu
    rw [hev.deriv_eq, deriv_id]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ → ℂ, a = fun p q =>
      1 / π * (((p + 1) * (q + 1) : ℕ) : ℂ) * grunsky f g (-(p + 1 : ℤ)) (-(q + 1 : ℤ)) := ⟨_, rfl⟩
  have hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (kerK1 f z w) := by
    intro z hz w hw hzw
    rw [ha]
    exact s2c_kernels_K1 h z hz w hw hzw
  have hK0 : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → kerK1 f z w = 0 := by
    intro z hz w hw hzw
    rw [kerK1_of_ne _ hzw, hder z hz, hder w hw, hid z hz, hid w hw]
    simp
  have hall := s2c_bidisk_hasSum (fun z hz w hw hzw => (hK z hz w hw hzw).summable)
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ → ℂ, T = fun z w => ∑' p : ℕ × ℕ, a p.1 p.2 * z ^ p.1 * w ^ p.2 :=
    ⟨_, rfl⟩
  have hall' : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (T z w) := by
    rw [hT]; exact hall
  have hcont : ContinuousOn (fun x : ℂ × ℂ => T x.1 x.2) (unitDisc ×ˢ unitDisc) := s2c_bidisk_continuousOn hall'
  have hoff : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → T z w = 0 := by
    intro z hz w hw hzw
    rw [← hK0 z hz w hw hzw]
    exact (hall' z hz w hw).unique (hK z hz w hw hzw)
  have hT0 : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, T z w = 0 := by
    intro z hz w hw
    by_cases hzw : z = w
    · subst hzw
      have hc : ContinuousAt (fun w => T z w) z :=
        (hcont.comp (continuousOn_const.prodMk continuousOn_id) (fun w hw => ⟨hz, hw⟩)).continuousAt
          (isOpen_ball.mem_nhds hz)
      have ht1 : Tendsto (fun w => T z w) (𝓝[≠] z) (𝓝 (T z z)) := hc.tendsto.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (fun w => T z w) (𝓝[≠] z) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with w hw hwz
        exact (hoff z hz w hw (Ne.symm hwz)).symm
      exact tendsto_nhds_unique ht1 ht2
    · exact hoff z hz w hw hzw
  have hU := double_powerSeries_coeff_unique (F := T) (a := a) (b := fun _ _ => 0) hall' (fun z hz w hw => by
      rw [hT0 z hz w hw]
      simpa using (hasSum_zero : HasSum (fun _ : ℕ × ℕ => (0 : ℂ)) 0))
  have hmn : a m n = 0 := congrFun (congrFun hU m) n
  rw [ha] at hmn
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : (((m + 1) * (n + 1) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (m + 1) * (n + 1) ≠ 0)
  have hb : grunsky f g (-(m + 1 : ℤ)) (-(n + 1 : ℤ)) = 0 := by
    rcases mul_eq_zero.mp hmn with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (one_div_ne_zero hπ)
      · exact absurd h2 hne
    · exact h1
  show (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (-(m + 1 : ℤ)) (-(n + 1 : ℤ)) = 0
  rw [hb, mul_zero]

/-- The axis coefficients vanish when `f = id` on `𝔻`. -/
theorem s5gr_axis_zero {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (hid : ∀ z ∈ unitDisc, f z = z)
    (n : ℕ) : grunsky f g (-((n : ℤ) + 1)) 0 = 0 := by
  have hax := s5gr_axis h
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n : ℕ => if n = 0 then 0 else grunsky f g (-(n : ℤ)) 0 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun z => ∑' n, c n * z ^ n := ⟨_, rfl⟩
  have hser : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (H z) ∧ f z = z * exp (-H z) := by
    intro z hz; subst hH hc; exact hax z hz
  have hH0 : H 0 = 0 := by
    have h1 := (hser 0 (mem_ball_self one_pos)).1
    have e : (fun n => c n * (0 : ℂ) ^ n) = fun _ => 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn; simp [hc]
      · simp [zero_pow hn]
    rw [e] at h1
    exact h1.unique hasSum_zero
  haveI : PreconnectedSpace unitDisc :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : ℂ) 1).isPreconnected
  have hHc : ContinuousOn H unitDisc :=
    (differentiableOn_of_powerSeries fun z hz => (hser z hz).1).continuousOn
  have hu := continuous_exp_lift_unique (X := unitDisc) (L := fun x => -H (x : ℂ)) (M := fun _ => 0)
    (hHc.comp_continuous continuous_subtype_val (fun x => x.2)).neg continuous_const
    (fun x => by
      by_cases hx0 : (x : ℂ) = 0
      · rw [hx0, hH0, neg_zero]
      · have h2 := (hser x x.2).2
        rw [hid x x.2] at h2
        have h3 : exp (-H x) = 1 := by
          have := congrArg (fun u => u / (x : ℂ)) h2
          rw [div_self hx0, mul_div_cancel_left₀ _ hx0] at this
          exact this.symm
        rw [h3, exp_zero])
    (x₀ := ⟨0, mem_ball_self one_pos⟩) (by simp only; rw [hH0, neg_zero])
  have hHz : ∀ z ∈ ball (0 : ℂ) 1, H z = 0 := by
    intro z hz
    have := congrFun hu ⟨z, hz⟩
    simp only at this
    linear_combination -this
  have hcu := s5gr_coeff_unique (p := c) (q := fun _ => 0) (f := H) one_pos
    (fun z hz => (hser z hz).1) (fun z hz => by rw [hHz z hz]; simpa using hasSum_zero)
  have h1 := congrFun hcu (n + 1)
  rw [hc] at h1
  simp only [Nat.add_one_ne_zero, if_false] at h1
  push_cast at h1
  exact h1

/-- **`B₁` entries along a holomorphic family** (as `AppB.b1_entries`, via `K₁` and `b1_df_coeff_diff`). -/
theorem s5gr_B1_diff {ε : ℝ} {F G : ℂ → ℂ → ℂ}
    (hpair : ∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ) ∧
      volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0)
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc)) (m n : ℕ) :
    DifferentiableOn ℂ (fun τ => B1 (grunsky (F τ) (G τ)) m n) (ball 0 ε) := by
  have hFτ : ∀ z ∈ unitDisc, ∀ τ ∈ ball (0 : ℂ) ε, DifferentiableAt ℂ (fun τ => F τ z) τ := by
    intro z hz τ hτ
    have ha := han (τ, z) ⟨hτ, hz⟩
    have hp : DifferentiableAt ℂ (fun t : ℂ => (t, z)) τ := differentiableAt_id.prodMk (differentiableAt_const z)
    exact ha.differentiableAt.comp τ hp
  have hdz : ∀ z ∈ unitDisc, ∀ t ∈ ball (0 : ℂ) ε,
      HasDerivAt (fun z' => F t z') (fderiv ℂ (fun p : ℂ × ℂ => F p.1 p.2) (t, z) (0, 1)) z := by
    intro z hz t ht
    have h1 := (han (t, z) ⟨ht, hz⟩).differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun z' : ℂ => (t, z')) (0, 1) z := (hasDerivAt_const z t).prodMk (hasDerivAt_id z)
    exact h1.comp_hasDerivAt z h2
  have hdd : ∀ z ∈ unitDisc, DifferentiableOn ℂ (fun t => deriv (F t) z) (ball 0 ε) := by
    intro z hz t ht
    have hfd := han.fderiv (t, z) ⟨ht, hz⟩
    have hp : DifferentiableAt ℂ (fun t' : ℂ => (t', z)) t := differentiableAt_id.prodMk (differentiableAt_const z)
    have h3 : DifferentiableAt ℂ (fun t' => fderiv ℂ (fun p : ℂ × ℂ => F p.1 p.2) (t', z) (0, 1)) t :=
      (hfd.differentiableAt.comp t hp).clm_apply (differentiableAt_const _)
    exact h3.differentiableWithinAt.congr (fun t' ht' => (hdz z hz t' ht').deriv) (hdz z hz t ht).deriv
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hker : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      DifferentiableOn ℂ (fun t => (π : ℂ) * kerK1 (F t) z w) (ball 0 ε) := by
    intro z hz w hw hzw
    have hne : ∀ t ∈ ball (0 : ℂ) ε, (F t z - F t w) ^ 2 ≠ 0 := fun t ht => pow_ne_zero 2 fun h0 =>
      hzw ((hpair t ht).1.2.1 hz hw (sub_eq_zero.mp h0))
    have hFz : DifferentiableOn ℂ (fun t => F t z) (ball 0 ε) := fun t ht =>
      (hFτ z hz t ht).differentiableWithinAt
    have hFw : DifferentiableOn ℂ (fun t => F t w) (ball 0 ε) := fun t ht =>
      (hFτ w hw t ht).differentiableWithinAt
    refine DifferentiableOn.congr (f := fun t => 1 / (z - w) ^ 2 -
      deriv (F t) z * deriv (F t) w / (F t z - F t w) ^ 2) ?_ fun t _ => ?_
    · exact (differentiableOn_const _).sub (((hdd z hz).mul (hdd w hw)).div ((hFz.sub hFw).pow 2) hne)
    · rw [kerK1_of_ne _ hzw, ← mul_assoc, mul_one_div_cancel hπ, one_mul]
  have hbd : ∀ t ∈ ball (0 : ℂ) ε, ∀ p q, ‖B1 (grunsky (F t) (G t)) p q‖ ≤ 1 := by
    intro t ht p q
    obtain ⟨hs, hle⟩ := AppB.b1_finBil_row zero_le_one (s5gr_finBil_B1 (hpair t ht).1 (hpair t ht).2) p
    have h1 : ‖B1 (grunsky (F t) (G t)) p q‖ ^ 2 ≤ 1 := by
      have := (hs.le_tsum q (fun _ _ => sq_nonneg _)).trans hle
      simpa using this
    nlinarith [norm_nonneg (B1 (grunsky (F t) (G t)) p q)]
  have hsq : ∀ p q : ℕ, (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ) *
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ) = (((p + 1) * (q + 1) : ℕ) : ℂ) := by
    intro p q
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  obtain ⟨c, hc⟩ : ∃ c : ℂ → ℕ → ℕ → ℂ, c = fun t p q =>
      B1 (grunsky (F t) (G t)) p q * (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ) := ⟨_, rfl⟩
  have hcd := AppB.b1_df_coeff_diff isOpen_ball (c := c) (L := fun p q => Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)))
    (ρ1 := 1 / 2) (ρ2 := 1 / 4) (by norm_num) (by norm_num) (fun p q => Real.sqrt_nonneg _)
    (AppB.b1_summable_L (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by
      intro t ht p q
      rw [hc]
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ 1 * Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hbd t ht p q) (Real.sqrt_nonneg _)
        _ = _ := one_mul _)
    (by
      intro z w hz hw
      have hz1 : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; norm_num)
      have hw1 : w ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hw]; norm_num)
      have hzw : z ≠ w := by
        intro he; rw [he] at hz; rw [hz] at hw; norm_num at hw
      refine (hker z hz1 w hw1 hzw).congr (fun t ht => ?_)
      have hs := (s2c_kernels_K1 (hpair t ht).1 z hz1 w hw1 hzw).mul_left (π : ℂ)
      refine (HasSum.tsum_eq ?_)
      convert hs using 1
      funext p
      have hB : B1 (grunsky (F t) (G t)) p.1 p.2 = (Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) : ℂ) *
          grunsky (F t) (G t) (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ)) := rfl
      rw [hc]
      simp only
      rw [hB, mul_comm (Real.sqrt _ : ℂ) (grunsky _ _ _ _), mul_assoc (grunsky _ _ _ _), hsq]
      field_simp)
    m n
  have hne : ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hcd.div_const ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ)).congr (fun t _ => ?_)
  rw [hc]
  field_simp

/-- **Stub W7.** For a holomorphic family of normalized null pairs with `F_0 = id` and `log|G_τ'(∞)|²` bounded:
in `ℓ²`, `c_-(τ) = τ ċ + O(|τ|²)`, and `‖B₁(τ)‖ = O(|τ|)` (Schwarz on the finite bilinear forms). -/
theorem s5gr_family_bounds {ε : ℝ} (hε : 0 < ε) {F G : ℂ → ℂ → ℂ}
    (hpair : ∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ) ∧
      volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0)
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc))
    (h0 : ∀ z ∈ unitDisc, F 0 z = z) {M : ℝ}
    (hM : ∀ τ ∈ ball (0 : ℂ) ε, Real.log (‖derivAtInfty (G τ)‖ ^ 2) ≤ M) :
    let cm : ℂ → ℕ → ℂ := fun τ j => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, Summable (fun j => ‖deriv (fun τ => cm τ j) 0‖ ^ 2) ∧
      ∀ τ ∈ ball (0 : ℂ) r,
        Summable (fun j => ‖cm τ j - τ * deriv (fun τ => cm τ j) 0‖ ^ 2) ∧
        (∑' j, ‖cm τ j - τ * deriv (fun τ => cm τ j) 0‖ ^ 2) ≤ C * ‖τ‖ ^ 4 ∧
        ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
          ∑' m, ‖∑' n, B1 (grunsky (F τ) (G τ)) m n * x n‖ ^ 2 ≤ C * ‖τ‖ ^ 2 * ∑' n, ‖x n‖ ^ 2 := by
  intro cm
  obtain ⟨δ, hδ, hδε, hcd, -⟩ := s5gr_log_family hε (fun τ hτ => (hpair τ hτ).1) han h0
  have hτε : ∀ τ ∈ ball (0 : ℂ) δ, τ ∈ ball (0 : ℂ) ε := fun τ hτ => ball_subset_ball hδε hτ
  -- the coordinates `c_-(τ)_j`
  have hφd : ∀ j, DifferentiableOn ℂ (fun τ => cm τ j) (ball 0 δ) := by
    intro j
    refine ((hcd (j + 1)).const_mul ((Real.sqrt ((j : ℝ) + 1) : ℂ))).congr fun τ _ => ?_
    show (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0 = _
    simp
  have hφ0 : ∀ j, cm 0 j = 0 := by
    intro j
    show (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F 0) (G 0) (-((j : ℤ) + 1)) 0 = 0
    rw [s5gr_axis_zero (hpair 0 (mem_ball_self hε)).1 h0 j, mul_zero]
  have hφb : ∀ σ ∈ ball (0 : ℂ) δ, ∀ N, ∑ j ∈ Finset.range N, ‖cm σ j‖ ^ 2 ≤ M := by
    intro σ hσ N
    obtain ⟨hs1, hs2, hsum⟩ := r22_sum (hpair σ (hτε σ hσ)).1 (hpair σ (hτε σ hσ)).2
    have e : ∀ j, ‖cm σ j‖ ^ 2 = ((j + 1 : ℕ) : ℝ) * ‖grunsky (F σ) (G σ) (-((j : ℤ) + 1)) 0‖ ^ 2 := by
      intro j
      show ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F σ) (G σ) (-((j : ℤ) + 1)) 0‖ ^ 2 = _
      rw [s5gr_sqrt_norm_sq]; push_cast; ring
    simp only [e]
    calc ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * ‖grunsky (F σ) (G σ) (-((j : ℤ) + 1)) 0‖ ^ 2
        ≤ ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky (F σ) (G σ) (-((j : ℤ) + 1)) 0‖ ^ 2 :=
          hs1.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ Real.log (‖derivAtInfty (G σ)‖ ^ 2) := by
          rw [← hsum]; exact le_add_of_nonneg_right (tsum_nonneg fun _ => by positivity)
      _ ≤ M := hM σ (hτε σ hσ)
  have hM0 : 0 ≤ M := by simpa using hφb 0 (mem_ball_self hδ) 0
  have hT := s5gr_trunc (φ := fun j τ => cm τ j) hδ hM0 hφd hφ0 hφb
  -- `ċ ∈ ℓ²`
  obtain ⟨cd, hcd'⟩ : ∃ cd : ℕ → ℂ, cd = fun j => deriv (fun τ => cm τ j) 0 := ⟨_, rfl⟩
  have hcdN : ∀ N, ∑ j ∈ Finset.range N, ‖cd j‖ ^ 2 ≤ M / δ ^ 2 := by
    intro N
    have h1 := (hT cd N).1
    have e : ∑ j ∈ Finset.range N, conj (cd j) * deriv (fun τ => cm τ j) 0 =
        ((∑ j ∈ Finset.range N, ‖cd j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => by rw [hcd']; exact_mod_cast k23_conj_mul _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
    have h2 := s5gr_sq_of_le_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity : 0 ≤ Real.sqrt M / δ) (le_of_le_of_eq h1 (by ring))
    rw [div_pow, Real.sq_sqrt hM0] at h2
    exact h2
  have hcds : Summable (fun j => ‖cd j‖ ^ 2) := summable_of_sum_range_le (fun _ => sq_nonneg _) hcdN
  -- `B₁` along the family
  have hBd : ∀ m n, DifferentiableOn ℂ (fun τ => B1 (grunsky (F τ) (G τ)) m n) (ball 0 δ) := fun m n =>
    (s5gr_B1_diff hpair han m n).mono (ball_subset_ball hδε)
  have hB0 : ∀ m n, B1 (grunsky (F 0) (G 0)) m n = 0 := s5gr_B1_zero (hpair 0 (mem_ball_self hε)).1 h0
  refine ⟨δ, hδ, max (4 * M / δ ^ 4) (1 / δ ^ 2), ?_, fun τ hτ => ?_⟩
  · rw [hcd'] at hcds; exact hcds
  -- the second-order bound
  have hτn : ‖τ‖ < δ := mem_ball_zero_iff.mp hτ
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℂ, v = fun j => cm τ j - τ * cd j := ⟨_, rfl⟩
  have hvN : ∀ N, ∑ j ∈ Finset.range N, ‖v j‖ ^ 2 ≤ 4 * M / δ ^ 4 * ‖τ‖ ^ 4 := by
    intro N
    have h1 := (hT v N).2 τ hτ
    have e : ∑ j ∈ Finset.range N, conj (v j) * (cm τ j - τ * deriv (fun τ => cm τ j) 0) =
        ((∑ j ∈ Finset.range N, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have : cm τ j - τ * deriv (fun τ => cm τ j) 0 = v j := by rw [hv, hcd']
      rw [this]; exact_mod_cast k23_conj_mul _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
    have h2 := s5gr_sq_of_le_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity : 0 ≤ 2 * Real.sqrt M * (‖τ‖ / δ) ^ 2) (le_of_le_of_eq h1 (by ring))
    calc _ ≤ (2 * Real.sqrt M * (‖τ‖ / δ) ^ 2) ^ 2 := h2
      _ = 4 * M / δ ^ 4 * ‖τ‖ ^ 4 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hM0, div_pow]; field_simp; ring
  have hvs : Summable (fun j => ‖v j‖ ^ 2) := summable_of_sum_range_le (fun _ => sq_nonneg _) hvN
  have hvt : (∑' j, ‖v j‖ ^ 2) ≤ 4 * M / δ ^ 4 * ‖τ‖ ^ 4 :=
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hvN
  have hC1 : 4 * M / δ ^ 4 ≤ max (4 * M / δ ^ 4) (1 / δ ^ 2) := le_max_left _ _
  have hC2 : 1 / δ ^ 2 ≤ max (4 * M / δ ^ 4) (1 / δ ^ 2) := le_max_right _ _
  rw [hv] at hvs hvt
  rw [hcd'] at hvs hvt
  refine ⟨hvs, hvt.trans (mul_le_mul_of_nonneg_right hC1 (by positivity)), fun x hx => ?_⟩
  -- the Schwarz lemma for the finite bilinear forms of `B₁`
  have hbil : AppB.FinBil (B1 (grunsky (F τ) (G τ))) (‖τ‖ / δ) := by
    intro X Y x y
    obtain ⟨β, hβ⟩ : ∃ β : ℂ → ℂ, β = fun t => ∑ m ∈ Y, ∑ n ∈ X, y m * B1 (grunsky (F t) (G t)) m n * x n :=
      ⟨_, rfl⟩
    have hβd : DifferentiableOn ℂ β (ball 0 δ) := by
      rw [hβ]
      apply DifferentiableOn.fun_sum
      intro m _
      apply DifferentiableOn.fun_sum
      intro n _
      exact ((hBd m n).const_mul (y m)).mul_const (x n)
    have hβ0 : β 0 = 0 := by rw [hβ]; simp [hB0]
    have hmaps : MapsTo β (ball 0 δ)
        (closedBall (β 0) (Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2))) := by
      intro t ht
      rw [hβ0, mem_closedBall_zero_iff, hβ]
      have h := s5gr_finBil_B1 (hpair t (hτε t ht)).1 (hpair t (hτε t ht)).2 X Y x y
      rwa [one_mul] at h
    have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hβd hmaps hτ
    rw [hβ0, dist_zero_right, dist_zero_right] at hs
    have he : β τ = ∑ m ∈ Y, ∑ n ∈ X, y m * B1 (grunsky (F τ) (G τ)) m n * x n := by rw [hβ]
    rw [← he]
    refine hs.trans (le_of_eq ?_)
    ring
  have h := (AppB.b1_finBil_apply (by positivity) hbil hx).2
  have h' : (∑' m, ‖∑' n, B1 (grunsky (F τ) (G τ)) m n * x n‖ ^ 2) ≤ (‖τ‖ / δ) ^ 2 * ∑' n, ‖x n‖ ^ 2 := h
  refine h'.trans (mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun _ => sq_nonneg _))
  rw [div_pow, div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_right hC2 (by positivity)

/-- **Stub W8.** The `τ`-derivative of `c_-`: if `∂_τ F_τ|₀ = Σ ȧ_n z^{n+2}`, then `∂_τ b_{-(j+1),0}|₀ = -ȧ_j`
(`log(F_τ(z)/z) = -Σ b_{-k,0} z^k`), so `ċ_j = -√(j+1) ȧ_j`. -/
theorem s5gr_cdot {ε : ℝ} (hε : 0 < ε) {F G : ℂ → ℂ → ℂ}
    (hpair : ∀ τ ∈ ball (0 : ℂ) ε, IsNormalizedDisjointPair (F τ) (G τ))
    (han : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε ×ˢ unitDisc))
    (h0 : ∀ z ∈ unitDisc, F 0 z = z) {a : ℕ → ℂ}
    (hjet : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => a n * z ^ (n + 2)) (deriv (fun τ => F τ z) 0)) (j : ℕ) :
    deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0 =
      -((Real.sqrt ((j : ℝ) + 1) : ℂ) * a j) := by
  obtain ⟨δ, hδ, hδε, -, hS⟩ := s5gr_log_family hε hpair han h0
  -- the jet: `-Ḟ(z)/z = Σ_n e_n zⁿ`, `e_{n+1} = -ȧ_n`
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℂ, e = fun n => if n = 0 then 0 else -a (n - 1) := ⟨_, rfl⟩
  obtain ⟨f0, hf0⟩ : ∃ f0 : ℂ → ℂ, f0 = fun z => if z = 0 then 0 else -(deriv (fun τ => F τ z) 0 / z) :=
    ⟨_, rfl⟩
  have hL : ∀ z ∈ ball (0 : ℂ) (1 / 4), HasSum (fun n : ℕ =>
      deriv (fun τ => if n = 0 then 0 else grunsky (F τ) (G τ) (-(n : ℤ)) 0) 0 * z ^ n) (f0 z) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have e0 : (fun n : ℕ => deriv (fun τ => if n = 0 then (0 : ℂ) else grunsky (F τ) (G τ) (-(n : ℤ)) 0) 0 *
          (0 : ℂ) ^ n) = fun _ => 0 := by
        funext n
        by_cases hn : n = 0
        · subst hn; simp
        · simp [zero_pow hn]
      rw [e0, show f0 0 = 0 by simp [hf0]]
      exact hasSum_zero
    · rw [show f0 z = -(deriv (fun τ => F τ z) 0 / z) by simp [hf0, hz0]]
      exact hS z hz hz0
  have hR : ∀ z ∈ ball (0 : ℂ) (1 / 4), HasSum (fun n => e n * z ^ n) (f0 z) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have e0 : (fun n => e n * (0 : ℂ) ^ n) = fun _ => 0 := by
        funext n
        by_cases hn : n = 0
        · subst hn; simp [he]
        · simp [zero_pow hn]
      rw [e0, show f0 0 = 0 by simp [hf0]]
      exact hasSum_zero
    · have hz1 : z ∈ unitDisc := ball_subset_ball (by norm_num) hz
      have h1 := ((hjet z hz1).div_const z).neg
      have h2 : HasSum (fun n => e (n + 1) * z ^ (n + 1)) (-(deriv (fun τ => F τ z) 0 / z)) := by
        convert h1 using 1
        funext n
        simp only [he, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
        field_simp
        ring
      refine (hasSum_nat_add_iff' 1).mp ?_
      rw [show f0 z - ∑ i ∈ Finset.range 1, e i * z ^ i = -(deriv (fun τ => F τ z) 0 / z) by
        simp [hf0, hz0, he]]
      exact h2
  have hU := s5gr_coeff_unique (by norm_num : (0 : ℝ) < 1 / 4) hL hR
  have hj := congrFun hU (j + 1)
  beta_reduce at hj
  have hej : e (j + 1) = -a j := by simp [he]
  rw [hej] at hj
  have hfun : (fun τ => grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) =
      fun τ => if j + 1 = 0 then (0 : ℂ) else grunsky (F τ) (G τ) (-((j + 1 : ℕ) : ℤ)) 0 := by
    funext τ
    simp
  rw [deriv_const_mul_field, hfun, hj, mul_neg]

/-- **The scalar estimate behind W9.** With `A = ‖u‖`, `|A - t d| ≤ s t²`, `‖x‖ ∈ [A(1 - st), A(1 + st)]` and
`‖x‖² ≤ P ≤ ‖x‖²/(1 - s²t²)`, `st ≤ 1/2`: `|A² + P - 2t²d²| ≤ (2s(2d + s) + 4s(d + s)²) t³` for `t ≤ 1`. -/
theorem s5gr_scalar_est {A X P d s t : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (hd : 0 ≤ d) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (hst : s * t ≤ 1 / 2) (hAt : |A - t * d| ≤ s * t ^ 2)
    (hX1 : A * (1 - s * t) ≤ X) (hX2 : X ≤ A * (1 + s * t))
    (hP1 : X ^ 2 ≤ P) (hP2 : (1 - (s * t) ^ 2) * P ≤ X ^ 2) :
    |A ^ 2 + P - 2 * t ^ 2 * d ^ 2| ≤ (2 * s * (2 * d + s) + 4 * s * (d + s) ^ 2) * t ^ 3 := by
  have hst0 : 0 ≤ s * t := mul_nonneg hs ht
  obtain ⟨hAt1, hAt2⟩ := abs_le.mp hAt
  have hAu : A ≤ t * (d + s) := by nlinarith
  have hA2 : A ^ 2 ≤ t ^ 2 * (d + s) ^ 2 := by
    have := pow_le_pow_left₀ hA hAu 2
    nlinarith
  -- `|A² - t²d²| ≤ s t³ (2d + s)`
  have h1 : |A ^ 2 - t ^ 2 * d ^ 2| ≤ s * t ^ 3 * (2 * d + s) := by
    have e : A ^ 2 - t ^ 2 * d ^ 2 = (A - t * d) * (A + t * d) := by ring
    rw [e, abs_mul]
    have hAp : |A + t * d| ≤ t * (2 * d + s) := by
      rw [abs_of_nonneg (by positivity)]; nlinarith
    calc |A - t * d| * |A + t * d| ≤ (s * t ^ 2) * (t * (2 * d + s)) :=
          mul_le_mul hAt hAp (abs_nonneg _) (by positivity)
      _ = s * t ^ 3 * (2 * d + s) := by ring
  -- `P - A²` from both sides
  have hden : 0 < 1 - (s * t) ^ 2 := by nlinarith
  have hPu : P ≤ A ^ 2 * (1 + 4 * (s * t)) := by
    have hX2' : X ^ 2 ≤ A ^ 2 * (1 + s * t) ^ 2 := by
      have := pow_le_pow_left₀ hX hX2 2; nlinarith
    have key : (1 - (s * t) ^ 2) * P ≤ (1 - (s * t) ^ 2) * (A ^ 2 * (1 + 4 * (s * t))) := by
      have : A ^ 2 * (1 + s * t) ^ 2 ≤ (1 - (s * t) ^ 2) * (A ^ 2 * (1 + 4 * (s * t))) := by
        have hA2' : 0 ≤ A ^ 2 := sq_nonneg A
        nlinarith [mul_nonneg hA2' hst0, mul_nonneg hA2' (mul_nonneg hst0 hst0),
          mul_nonneg (mul_nonneg hA2' hst0) (mul_nonneg hst0 hst0)]
      linarith
    exact le_of_mul_le_mul_left key hden
  have hPl : A ^ 2 * (1 - 2 * (s * t)) ≤ P := by
    have hX1' : (A * (1 - s * t)) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by nlinarith) hX1 2
    nlinarith [sq_nonneg (s * t), sq_nonneg A]
  have h2 : |P - A ^ 2| ≤ 4 * s * t ^ 3 * (d + s) ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sq_nonneg A) hst0, mul_le_mul_of_nonneg_left hA2 (by positivity : 0 ≤ 2 * (s * t))]
    · nlinarith [mul_le_mul_of_nonneg_left hA2 (by positivity : 0 ≤ 4 * (s * t))]
  have e : A ^ 2 + P - 2 * t ^ 2 * d ^ 2 = 2 * (A ^ 2 - t ^ 2 * d ^ 2) + (P - A ^ 2) := by ring
  rw [e]
  calc |2 * (A ^ 2 - t ^ 2 * d ^ 2) + (P - A ^ 2)| ≤ |2 * (A ^ 2 - t ^ 2 * d ^ 2)| + |P - A ^ 2| :=
        abs_add_le _ _
    _ ≤ 2 * (s * t ^ 3 * (2 * d + s)) + 4 * s * t ^ 3 * (d + s) ^ 2 := by
        rw [abs_mul, abs_two]; linarith
    _ = (2 * s * (2 * d + s) + 4 * s * (d + s) ^ 2) * t ^ 3 := by ring

/-- **Stub W9.** `K(τ Y) = ‖Y‖²_VK |τ|² + o(|τ|²)` (W1–W8 with `r22_sum` and the continuity of `K`). -/
theorem s5gr_K_quadratic (Y : AInf unitDisc × ℂ) :
    (fun τ : ℂ => potentialK (tcCoordHInv (τ • Y)) - vkNormSqCoordOrigin Y * ‖τ‖ ^ 2) =o[𝓝 0]
      (fun τ : ℂ => ‖τ‖ ^ 2) := by
  obtain ⟨ε, hε, F, G, hFG, han, h0, hjet⟩ := s5gr_curve_pair Y
  set k : ℂ → ℝ := fun τ => potentialK (tcCoordHInv (τ • Y)) with hkdef
  -- continuity of `K` along the line
  have hkc : ContinuousAt k 0 := by
    have hx0 : tcCoordH tOrigin = 0 := by
      rw [← Prod.mk_zero_zero]
      exact s5t53_tcCoordH_origin
    have hreg := s5l54_regular s5rh_tOrigin_mem
    rw [hx0] at hreg
    have ha : ContDiffAt ℝ 2 (fun t : ℂ => t • Y) 0 := (contDiff_id.smul contDiff_const).contDiffAt
    have hg' : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
        ((fun t : ℂ => t • Y) 0) := by
      simpa using hreg
    have hc : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (t • Y))) 0 :=
      ContDiffAt.comp (g := fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
        (f := fun t : ℂ => t • Y) 0 hg' ha
    exact ((hc.div_const 2).sub contDiffAt_const).continuousAt
  obtain ⟨ε1, hε1, hk1⟩ := Metric.continuousAt_iff.mp hkc 1 one_pos
  set ε2 := min ε ε1 with hε2
  have hε2p : 0 < ε2 := lt_min hε hε1
  have hsub : ∀ τ ∈ ball (0 : ℂ) ε2, τ ∈ ball (0 : ℂ) ε ∧ dist τ 0 < ε1 := fun τ hτ =>
    ⟨ball_subset_ball (min_le_left _ _) hτ, lt_of_lt_of_le (mem_ball.mp hτ) (min_le_right _ _)⟩
  have hM : ∀ τ ∈ ball (0 : ℂ) ε2, Real.log (‖derivAtInfty (G τ)‖ ^ 2) ≤ 2 * (|k 0| + 1) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hsub τ hτ
    rw [Real.log_pow, ← (hFG τ h1).2.2.1]
    have h3 := hk1 h2
    rw [Real.dist_eq] at h3
    push_cast
    have : k τ ≤ |k 0| + 1 := by
      have := abs_lt.mp h3
      linarith [le_abs_self (k 0)]
    show 2 * k τ ≤ _
    linarith
  have hpair2 : ∀ τ ∈ ball (0 : ℂ) ε2, IsNormalizedDisjointPair (F τ) (G τ) ∧
      volume ((F τ '' unitDisc ∪ G τ '' unitDiscExterior)ᶜ) = 0 :=
    fun τ hτ => ⟨(hFG τ (hsub τ hτ).1).1, (hFG τ (hsub τ hτ).1).2.1⟩
  have han2 : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (ball 0 ε2 ×ˢ unitDisc) :=
    han.mono (prod_mono (ball_subset_ball (min_le_left _ _)) subset_rfl)
  obtain ⟨r, hr, C, hcs, hW⟩ := s5gr_family_bounds hε2p hpair2 han2 h0 hM
  -- the derivative vector and the VK norm
  set a : ℕ → ℂ := fun n => if n = 0 then Y.2 else I * tangentCoeff Y.1 (n + 1) with ha
  have hcd : ∀ j : ℕ, deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0 =
      -((Real.sqrt ((j : ℝ) + 1) : ℂ) * a j) :=
    s5gr_cdot hε2p (fun τ hτ => (hpair2 τ hτ).1) han2 h0 hjet
  set w : ell2 := ⟨_, gop_mem_of_summable hcs⟩ with hw
  have hV : ‖w‖ ^ 2 = vkNormSqCoordOrigin Y := by
    rw [gop_norm_sq]
    have e1 : ∀ j : ℕ, ‖w j‖ ^ 2 = ((j : ℝ) + 1) * ‖a j‖ ^ 2 := by
      intro j
      show ‖deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0‖ ^ 2 = _
      rw [hcd j, norm_neg, s5gr_sqrt_norm_sq]
    have hs : Summable (fun j : ℕ => ((j : ℝ) + 1) * ‖a j‖ ^ 2) := (gop_l2_summable w).congr e1
    rw [tsum_congr e1, hs.tsum_eq_zero_add]
    unfold vkNormSqCoordOrigin
    simp only [ha, Nat.cast_zero, zero_add, one_mul, if_true, Nat.succ_ne_zero, if_false, norm_mul,
      Complex.norm_I, mul_pow, one_pow]
    rw [add_comm]
    congr 1
    refine tsum_congr fun n => ?_
    push_cast
    ring
  -- the cubic bound
  set C' := max C 0 with hC'
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = C' := Real.sq_sqrt (le_max_right _ _)
  set d := ‖w‖ with hd
  set K0 := (2 * s * (2 * d + s) + 4 * s * (d + s) ^ 2) / 2 with hK0
  set r' := min (min r ε2) (min 1 (1 / (2 * (s + 1)))) with hr'
  have hr'p : 0 < r' := lt_min (lt_min hr hε2p) (lt_min one_pos (by positivity))
  have hbound : ∀ τ ∈ ball (0 : ℂ) r', |k τ - vkNormSqCoordOrigin Y * ‖τ‖ ^ 2| ≤ K0 * ‖τ‖ ^ 3 := by
    intro τ hτ
    have hτn : ‖τ‖ < r' := mem_ball_zero_iff.mp hτ
    have hτr : τ ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr (lt_of_lt_of_le hτn
      ((min_le_left _ _).trans (min_le_left _ _)))
    have hτ2 : τ ∈ ball (0 : ℂ) ε2 := mem_ball_zero_iff.mpr (lt_of_lt_of_le hτn
      ((min_le_left _ _).trans (min_le_right _ _)))
    have ht1 : ‖τ‖ ≤ 1 := (lt_of_lt_of_le hτn ((min_le_right _ _).trans (min_le_left _ _))).le
    have hst : s * ‖τ‖ ≤ 1 / 2 := by
      have h1 : ‖τ‖ ≤ 1 / (2 * (s + 1)) := (lt_of_lt_of_le hτn ((min_le_right _ _).trans (min_le_right _ _))).le
      have h2 : ‖τ‖ * (2 * (s + 1)) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at h1; exact h1
      nlinarith [norm_nonneg τ]
    obtain ⟨hp, hn, hK, hU⟩ := hFG τ (hsub τ hτ2).1
    obtain ⟨hsd, hle4, hB1⟩ := hW τ hτr
    obtain ⟨hs1, hs2, hsum⟩ := r22_sum hp hn
    set cmτ : ℕ → ℂ := fun j : ℕ => (Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0
      with hcmτ
    have hcm : Summable (fun j : ℕ => ‖cmτ j‖ ^ 2) := by
      refine hs1.congr fun j => ?_
      rw [hcmτ, s5gr_sqrt_norm_sq]; push_cast; ring
    set u : ell2 := ⟨cmτ, gop_mem_of_summable hcm⟩ with hu
    -- `‖u - τ w‖ ≤ s t²`
    have hdiff : ‖u - τ • w‖ ≤ s * ‖τ‖ ^ 2 := by
      have e : ‖u - τ • w‖ ^ 2 = ∑' j : ℕ, ‖cmτ j - τ * deriv (fun τ => (Real.sqrt ((j : ℝ) + 1) : ℂ) *
          grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0) 0‖ ^ 2 := by
        rw [gop_norm_sq]; rfl
      have h1 : ‖u - τ • w‖ ^ 2 ≤ (s * ‖τ‖ ^ 2) ^ 2 := by
        rw [e, mul_pow, hss, ← pow_mul]
        exact hle4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
    have hAt : |‖u‖ - ‖τ‖ * d| ≤ s * ‖τ‖ ^ 2 := by
      have h1 := abs_norm_sub_norm_le u (τ • w)
      rw [norm_smul] at h1
      exact h1.trans hdiff
    -- W3
    have hB1' : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
        ∑' m, ‖∑' n, B1 (grunsky (F τ) (G τ)) m n * x n‖ ^ 2 ≤ (s * ‖τ‖) ^ 2 * ∑' n, ‖x n‖ ^ 2 := by
      intro x hx
      rw [mul_pow, hss]
      exact (hB1 x hx).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (tsum_nonneg fun _ => by positivity))
    have hW3 := s5gr_two_sided hp hn hU (mul_nonneg hs0 (norm_nonneg τ)) (by linarith) hB1'
    obtain ⟨hxs, hcps, hlo, hhi⟩ := hW3
    set xv : ell2 := ⟨_, gop_mem_of_summable hxs⟩ with hxv
    -- `‖x - u‖ ≤ s t ‖u‖`
    have hxu : ‖xv - u‖ ≤ s * ‖τ‖ * ‖u‖ := by
      have hsym := (grunsky_unitary hp hn).1
      have e : ‖xv - u‖ ^ 2 = ∑' l, ‖∑' k, B1 (grunsky (F τ) (G τ)) l k * conj (cmτ k)‖ ^ 2 := by
        rw [gop_norm_sq]
        refine tsum_congr fun l => ?_
        show ‖(cmτ l - ∑' k, conj (cmτ k) * B1 (grunsky (F τ) (G τ)) k l) - cmτ l‖ ^ 2 = _
        rw [sub_sub_cancel_left, norm_neg]
        congr 2
        refine tsum_congr fun k => ?_
        rw [(hsym k l).1, mul_comm]
      have hcj : Summable (fun n => ‖conj (cmτ n)‖ ^ 2) := by simpa only [Complex.norm_conj] using hcm
      have h1 := hB1' (fun n => conj (cmτ n)) hcj
      simp only [Complex.norm_conj] at h1
      have h2 : ‖xv - u‖ ^ 2 ≤ (s * ‖τ‖ * ‖u‖) ^ 2 := by
        rw [e, mul_pow, gop_norm_sq u]
        exact h1
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    have hX1 : ‖u‖ * (1 - s * ‖τ‖) ≤ ‖xv‖ := by
      have := norm_sub_norm_le u xv
      rw [norm_sub_rev] at this
      nlinarith
    have hX2 : ‖xv‖ ≤ ‖u‖ * (1 + s * ‖τ‖) := by
      have := norm_sub_norm_le xv u
      nlinarith
    have hP1 : ‖xv‖ ^ 2 ≤ ∑' j : ℕ, ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2 := by
      rw [gop_norm_sq]; exact hlo
    have hP2 : (1 - (s * ‖τ‖) ^ 2) *
        ∑' j : ℕ, ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2 ≤ ‖xv‖ ^ 2 := by
      rw [gop_norm_sq]; exact hhi
    have hest := s5gr_scalar_est (norm_nonneg u) (norm_nonneg xv) (norm_nonneg w) hs0 (norm_nonneg τ) ht1 hst
      hAt hX1 hX2 hP1 hP2
    -- `A² + P = 2K`
    have hAP : ‖u‖ ^ 2 + ∑' j : ℕ, ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2 =
        2 * k τ := by
      rw [gop_norm_sq]
      have e1 : (∑' j : ℕ, ‖u j‖ ^ 2) = ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky (F τ) (G τ) (-((j : ℤ) + 1)) 0‖ ^ 2 :=
        tsum_congr fun j => by
          show ‖cmτ j‖ ^ 2 = _
          rw [hcmτ, s5gr_sqrt_norm_sq]; push_cast; ring
      have e2 : (∑' j : ℕ, ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2) =
          ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2 :=
        tsum_congr fun j => by rw [s5gr_sqrt_norm_sq]; push_cast; ring
      rw [e1, e2, hsum, Real.log_pow, ← hK]
      push_cast
      ring
    rw [← hV]
    have e : k τ - ‖w‖ ^ 2 * ‖τ‖ ^ 2 =
        (‖u‖ ^ 2 + ∑' j : ℕ, ‖(Real.sqrt ((j : ℝ) + 1) : ℂ) * grunsky (F τ) (G τ) ((j : ℤ) + 1) 0‖ ^ 2 -
          2 * ‖τ‖ ^ 2 * d ^ 2) / 2 := by
      rw [hAP]; ring
    rw [e, abs_div, abs_two, hK0]
    have := div_le_div_of_nonneg_right hest (zero_le_two : (0 : ℝ) ≤ 2)
    calc _ ≤ (2 * s * (2 * d + s) + 4 * s * (d + s) ^ 2) * ‖τ‖ ^ 3 / 2 := this
      _ = _ := by ring
  -- `O(t³) = o(t²)`
  have hO : (fun τ : ℂ => k τ - vkNormSqCoordOrigin Y * ‖τ‖ ^ 2) =O[𝓝 0] (fun τ : ℂ => ‖τ‖ ^ 3) := by
    refine Asymptotics.IsBigO.of_bound K0 ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) hr'p] with τ hτ
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    exact hbound τ hτ
  exact hO.trans_isLittleO (isLittleO_norm_pow_norm_pow (by norm_num : 2 < 3))

/-- **The origin identity.** `Levi_{(0,∞)} K(Y) = ‖Y‖²_VK` for all `Y ∈ A∞(𝔻) × ℂ`. -/
theorem s5gr_origin_identity (Y : AInf unitDisc × ℂ) :
    leviTC potentialK tOrigin Y = vkNormSqCoordOrigin Y := by
  have hx0 : tcCoordH tOrigin = 0 := by
    rw [← Prod.mk_zero_zero]
    exact s5t53_tcCoordH_origin
  have hreg := s5l54_regular s5rh_tOrigin_mem
  rw [hx0] at hreg
  have ha : ContDiffAt ℝ 2 (fun t : ℂ => t • Y) 0 := (contDiff_id.smul contDiff_const).contDiffAt
  have hg' : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
      ((fun t : ℂ => t • Y) 0) := by
    simpa using hreg
  have hc : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (t • Y))) 0 :=
    ContDiffAt.comp (g := fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
      (f := fun t : ℂ => t • Y) 0 hg' ha
  have hk : ContDiffAt ℝ 2 (fun t : ℂ => potentialK (tcCoordHInv (t • Y))) 0 := by
    have h1 : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (t • Y)) / 2 - Real.log 2) 0 :=
      (hc.div_const 2).sub contDiffAt_const
    exact h1
  unfold leviTC
  rw [hx0]
  simp only [zero_add]
  rw [s5gr_levi_of_isLittleO hk (s5gr_K_quadratic Y)]
  simp

/-- **Theorem 5.3** (TT:2288–2294), proved: `c₁(V) = -(2/π) ω_VK` on `𝒯(1)`, and `K` is a Kähler potential of the
Velling–Kirillov metric. -/
theorem s5gr_thm_5_3 :
    (∀ q ∈ TCurve, ∀ X, chernForm q X = -(2 / π) * omegaVK q X) ∧
      ∀ q ∈ TCurve, ∀ X, leviTC potentialK q X = vkNormSq q X := by
  have hii := s5t53_ii_of_origin s5gr_origin_identity
  exact ⟨s5t53_i_of_ii hii, hii⟩

/-- **Theorem 5.3** (TT:2288–2294). `c₁(V) = -(2/π) ω_VK` on `𝒯(1)`. Equivalently, `K` is a Kähler potential of the
Velling–Kirillov metric: `∂∂̄K(X, X̄) = ‖X‖²_VK`. -/
theorem thm_5_3 :
    (∀ q ∈ TCurve, ∀ X, chernForm q X = -(2 / π) * omegaVK q X) ∧
      ∀ q ∈ TCurve, ∀ X, leviTC potentialK q X = vkNormSq q X := by
  exact s5gr_thm_5_3

end TakhtajanTeo
