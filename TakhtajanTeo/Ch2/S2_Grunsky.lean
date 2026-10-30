import TakhtajanTeo.Ch2.S1_UnivalentFunctions

/-!
# Chapter 2, §2 — Grunsky operators for `T₀(1)` (TT:3798–4580)

* §2.1 normalized disjoint pairs, generalized Grunsky coefficients, Theorem 2.1 (Hummel), Remark 2.2, (2.1), the
  matrices `B₁, …, B₄`, (2.2), (2.3), symmetry and unitarity of `𝐁`, Remark 2.3, the kernels `K₁, …, K₄`, Remark 2.4,
  the bases `e_n`, `f_n`, (2.4), Lemma 2.5, Theorem 2.6, Lemma 2.7 with (2.6)–(2.9), Remark 2.8, Corollary 2.9, the map
  `𝒫` and Theorem 2.10, Remark 2.11
* §2.2 conjugations, Lemma 2.12 (Schur), Corollary 2.13, (2.12), the Fredholm determinant, Definition 2.15, (2.13)
* §2.3 Faber polynomials, the bases `α_n`, `β_n`, the period matrices, Corollary 2.16

**Modelling.**
- Operators on `ℓ²` are their matrices (indices `m, n ≥ 1` written `m + 1`, `n + 1` with `m, n : ℕ`).
  - Operator identities such as (2.2) are stated entrywise.
  - Boundedness and Hilbert–Schmidt conditions are stated through square-summability.
- The abstract Lemma 2.12 is stated for compact operators on `ℓ² = lp (fun _ : ℕ => ℂ) 2`, with the standard conjugation
  `star` (2.3).
- The Fredholm determinant `Det_F(𝒞) = ∏ ρ_n²` (TT:4481) is defined as `∏ (1 - λ_n²)` over the singular values `λ_n`
  of `B₁`. The singular values are taken from a chosen diagonalization `B₁B₁* = U diag(λ²) U*`, so the product does not
  depend on the choice.
- The welding pair of `[μ]` is `(𝖿^μ, 𝗀_μ) = (fsans μ, gsans μ)`.
- [CORRECTION] `K₁` and `K₄` use the removable diagonal value
  `-𝒮(f)(z)/(6π)`, not the zero produced by totalized division in the raw
  quotient. This agrees with the holomorphic expansions at TT:3949–3961 and
  the explicit `K₄(u,u)` formula at TT:4657. The off-diagonal formulas and
  one-variable area integrals are unchanged.

**Not stated.**
- Remark 2.14 (TT:4466) cites [Sch81]. Its claim that `B₁, B₄` are compact iff `[μ] ∈ S` is Appendix B.
- "`±λ_n⁻¹` are Fredholm eigenvalues" (TT:4464) is Schiffer's definition through (2.12), which is stated.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- A normalized disjoint pair (TT:3800): `f` univalent on `𝔻` with `f(0) = 0`, `f'(0) = 1`; `g` univalent on `𝔻*` with
`g(∞) = ∞`; `f(𝔻) ∩ g(𝔻*) = ∅`. -/
def IsNormalizedDisjointPair (f g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧ IsUnivalentAtInfty g ∧
    Disjoint (f '' unitDisc) (g '' unitDiscExterior)

/-- The generalized Grunsky coefficients `b_{nm}` (`n, m ∈ ℤ`) of a normalized disjoint pair (TT:3803–3814).
Written with exponentials, so that no branch of `log` is involved:
- `(g(z) - g(ζ))/(z - ζ) = exp(b₀₀ - Σ_{m,n ≥ 1} b_{mn} z^{-m} ζ^{-n})`;
- `(g(z) - f(ζ))/(b z) = exp(-Σ_{m ≥ 1, n ≥ 0} b_{m,-n} z^{-m} ζⁿ)`;
- `(f(z) - f(ζ))/(z - ζ) = exp(b₀₀ - Σ_{m,n ≥ 0} b_{-m,-n} z^m ζⁿ)`.

Here `e^{b₀₀} = b = g'(∞)`, and `b_{-n,m} = b_{m,-n}` (`n ≥ 0`, `m ≥ 1`). -/
def IsGrunskyCoeff (f g : ℂ → ℂ) (b : ℤ → ℤ → ℂ) : Prop :=
  exp (b 0 0) = derivAtInfty g ∧
    (∀ z ∈ unitDiscExterior, ∀ ζ ∈ unitDiscExterior, z ≠ ζ → ∃ S,
      HasSum (fun p : ℕ × ℕ => b (p.1 + 1) (p.2 + 1) * z ^ (-(p.1 + 1 : ℤ)) * ζ ^ (-(p.2 + 1 : ℤ))) S ∧
      (g z - g ζ) / (z - ζ) = exp (b 0 0 - S)) ∧
    (∀ z ∈ unitDiscExterior, ∀ ζ ∈ unitDisc, ∃ S,
      HasSum (fun p : ℕ × ℕ => b (p.1 + 1) (-(p.2 : ℤ)) * z ^ (-(p.1 + 1 : ℤ)) * ζ ^ p.2) S ∧
      (g z - f ζ) / (derivAtInfty g * z) = exp (-S)) ∧
    (∀ z ∈ unitDisc, ∀ ζ ∈ unitDisc, z ≠ ζ → ∃ S,
      HasSum (fun p : ℕ × ℕ => b (-(p.1 : ℤ)) (-(p.2 : ℤ)) * z ^ p.1 * ζ ^ p.2) S ∧
      (f z - f ζ) / (z - ζ) = exp (b 0 0 - S)) ∧
    ∀ n : ℕ, ∀ m : ℕ, b (-(n : ℤ)) (m + 1) = b (m + 1) (-(n : ℤ))

/-- The Grunsky coefficients of a pair (chosen; junk `0` if none). -/
def grunsky (f g : ℂ → ℂ) : ℤ → ℤ → ℂ := if h : ∃ b, IsGrunskyCoeff f g b then h.choose else fun _ _ => 0

/-- Scalar power-series uniqueness after removing the constant exponential ambiguity. -/
theorem powerSeries_nonconstant_unique_of_exp {a b : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, Summable (fun n => a n * z ^ n))
    (hb : ∀ z ∈ unitDisc, Summable (fun n => b n * z ^ n))
    (he : ∀ z ∈ unitDisc, z ≠ 0 →
      exp (a 0 - ∑' n, a n * z ^ n) = exp (b 0 - ∑' n, b n * z ^ n)) :
    ∀ n : ℕ, n ≠ 0 → a n = b n := by
  let F : ℂ → ℂ := fun z => ∑' n, a n * z ^ n
  let G : ℂ → ℂ := fun z => ∑' n, b n * z ^ n
  have hF : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using (ha z hz).hasSum
  have hG : HasFPowerSeriesAt G (FormalMultilinearSeries.ofScalars ℂ b) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using (hb z hz).hasSum
  have hF0 : F 0 = a 0 := by simp [F, zero_pow_eq]
  have hG0 : G 0 = b 0 := by simp [G, zero_pow_eq]
  have hAF := (hasFPowerSeriesAt_const (c := a 0) (e := (0 : ℂ)) (𝕜 := ℂ)).sub hF
  have hBG := (hasFPowerSeriesAt_const (c := b 0) (e := (0 : ℂ)) (𝕜 := ℂ)).sub hG
  have hAFc : ContinuousAt (fun z => a 0 - F z) 0 := hAF.continuousAt
  have hBGc : ContinuousAt (fun z => b 0 - G z) 0 := hBG.continuousAt
  have hstrip : Ioo (-π) π ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  have hAe : ∀ᶠ z in 𝓝 (0 : ℂ), (a 0 - F z).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hAFc).tendsto
    simp only [Function.comp_apply, hF0, sub_self, zero_im] at ht
    exact ht.eventually hstrip
  have hBe : ∀ᶠ z in 𝓝 (0 : ℂ), (b 0 - G z).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hBGc).tendsto
    simp only [Function.comp_apply, hG0, sub_self, zero_im] at ht
    exact ht.eventually hstrip
  have heq : (fun z => a 0 - F z) =ᶠ[𝓝 (0 : ℂ)] (fun z => b 0 - G z) := by
    filter_upwards [hAe, hBe, ball_mem_nhds (0 : ℂ) one_pos] with z hAz hBz hz
    by_cases hz0 : z = 0
    · simp [hz0, hF0, hG0]
    · exact exp_inj_of_neg_pi_lt_of_le_pi hAz.1 hAz.2.le hBz.1 hBz.2.le (he z hz hz0)
  have hp := hAF.eq_formalMultilinearSeries_of_eventually hBG heq
  intro n hn
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) hp
  simpa [constFormalMultilinearSeries_apply_of_nonzero hn, FormalMultilinearSeries.ofScalars] using hc

/-- Restriction of an absolutely summable double power series to the second axis zero. -/
theorem hasSum_double_axis_right {c : ℕ → ℕ → ℂ} {z S : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * (0 : ℂ) ^ p.2) S) :
    HasSum (fun n => c n 0 * z ^ n) S := by
  apply h.prod_fiberwise
  intro n
  apply (hasSum_ite_eq (0 : ℕ) (c n 0 * z ^ n)).congr_fun
  intro m
  by_cases hm : m = 0 <;> simp [hm]

/-- Restriction of a double power series to the first axis zero. -/
theorem hasSum_double_axis_left {c : ℕ → ℕ → ℂ} {z S : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => c p.1 p.2 * (0 : ℂ) ^ p.1 * z ^ p.2) S) :
    HasSum (fun n => c 0 n * z ^ n) S := by
  have hh := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h
  apply hasSum_double_axis_right (c := fun m n => c n m)
  simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.swap, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The negative first-axis logarithmic expansion follows directly from IsGrunskyCoeff. -/
theorem IsGrunskyCoeff.negative_axis_right {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    ∃ S : ℂ, HasSum (fun n : ℕ => b (-(n : ℤ)) 0 * z ^ n) S ∧
      (f z - f 0) / z = exp (b 0 0 - S) := by
  obtain ⟨S, hS, he⟩ := hb.2.2.2.1 z hz 0 (by simp [unitDisc]) hz0
  refine ⟨S, ?_, by simpa only [sub_zero] using he⟩
  simpa only [Nat.cast_zero, neg_zero] using
    hasSum_double_axis_right (c := fun m n => b (-(m : ℤ)) (-(n : ℤ))) hS

/-- The other negative-axis expansion has the same normalized difference quotient. -/
theorem IsGrunskyCoeff.negative_axis_left {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    ∃ S : ℂ, HasSum (fun n : ℕ => b 0 (-(n : ℤ)) * z ^ n) S ∧
      (f z - f 0) / z = exp (b 0 0 - S) := by
  obtain ⟨S, hS, he⟩ := hb.2.2.2.1 0 (by simp [unitDisc]) z hz hz0.symm
  refine ⟨S, ?_, ?_⟩
  · simpa only [Nat.cast_zero, neg_zero] using
      hasSum_double_axis_left (c := fun m n => b (-(m : ℤ)) (-(n : ℤ))) hS
  · convert he using 1 <;> field_simp <;> ring

/-- The first negative-axis series converges throughout the disk, including zero. -/
theorem IsGrunskyCoeff.negative_axis_right_summable {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) {z : ℂ} (hz : z ∈ unitDisc) :
    Summable (fun n : ℕ => b (-(n : ℤ)) 0 * z ^ n) := by
  by_cases hz0 : z = 0
  · subst z
    simp only [zero_pow_eq, mul_ite, mul_one, mul_zero]
    apply (hasSum_ite_eq (0 : ℕ) (b 0 0)).summable.congr
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  · obtain ⟨S, hS, _⟩ := hb.negative_axis_right hz hz0
    exact hS.summable

/-- The other negative-axis series also converges throughout the disk. -/
theorem IsGrunskyCoeff.negative_axis_left_summable {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) {z : ℂ} (hz : z ∈ unitDisc) :
    Summable (fun n : ℕ => b 0 (-(n : ℤ)) * z ^ n) := by
  by_cases hz0 : z = 0
  · subst z
    simp only [zero_pow_eq, mul_ite, mul_one, mul_zero]
    apply (hasSum_ite_eq (0 : ℕ) (b 0 0)).summable.congr
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  · obtain ⟨S, hS, _⟩ := hb.negative_axis_left hz hz0
    exact hS.summable

/-- The negative-axis symmetry follows from the defining exponentials, without grunsky_spec. -/
theorem IsGrunskyCoeff.negative_axis_symm {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) (n : ℕ) : b (-(n : ℤ)) 0 = b 0 (-(n : ℤ)) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply powerSeries_nonconstant_unique_of_exp
      (fun z hz => hb.negative_axis_right_summable hz)
      (fun z hz => hb.negative_axis_left_summable hz) _ n hn
    intro z hz hz0
    obtain ⟨S, hS, heS⟩ := hb.negative_axis_right hz hz0
    obtain ⟨T, hT, heT⟩ := hb.negative_axis_left hz hz0
    simpa only [Nat.cast_zero, neg_zero, hS.tsum_eq, hT.tsum_eq] using heS.symm.trans heT

/-- Every nonconstant negative-axis coefficient is independent of the chosen coefficient witness. -/
theorem IsGrunskyCoeff.negative_axis_unique {f g : ℂ → ℂ} {b c : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) (hc : IsGrunskyCoeff f g c) {n : ℕ} (hn : n ≠ 0) :
    b (-(n : ℤ)) 0 = c (-(n : ℤ)) 0 ∧ b 0 (-(n : ℤ)) = c 0 (-(n : ℤ)) := by
  have hright : b (-(n : ℤ)) 0 = c (-(n : ℤ)) 0 := by
    apply powerSeries_nonconstant_unique_of_exp
      (fun z hz => hb.negative_axis_right_summable hz)
      (fun z hz => hc.negative_axis_right_summable hz) _ n hn
    intro z hz hz0
    obtain ⟨S, hS, heS⟩ := hb.negative_axis_right hz hz0
    obtain ⟨T, hT, heT⟩ := hc.negative_axis_right hz hz0
    simpa only [Nat.cast_zero, neg_zero, hS.tsum_eq, hT.tsum_eq] using heS.symm.trans heT
  exact ⟨hright, (hb.negative_axis_symm n).symm.trans (hright.trans (hc.negative_axis_symm n))⟩

/-- A continuous logarithmic lift of a nonvanishing holomorphic function is holomorphic. -/
theorem differentiableOn_of_continuous_exp_lift {U : Set ℂ} (hU : IsOpen U)
    {G L : ℂ → ℂ} (hG : DifferentiableOn ℂ G U) (hL : ContinuousOn L U)
    (he : ∀ z ∈ U, exp (L z) = G z) : DifferentiableOn ℂ L U := by
  intro x hx
  have hGx := hG.differentiableAt (hU.mem_nhds hx)
  have hLx := hL.continuousAt (hU.mem_nhds hx)
  have hG0 : G x ≠ 0 := (he x hx) ▸ exp_ne_zero (L x)
  let A : ℂ → ℂ := fun y => L y - L x
  let B : ℂ → ℂ := fun y => log (G y / G x)
  have hA0 : A x = 0 := by simp [A]
  have hB0 : B x = 0 := by simp [B, hG0]
  have hBd : DifferentiableAt ℂ B x := by
    apply (differentiableAt_log (by simp [hG0])).comp x (hGx.div_const (G x))
  have hstrip : Ioo (-π) π ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  have hAc : ContinuousAt A x := hLx.sub continuousAt_const
  have hAe : ∀ᶠ y in 𝓝 x, (A y).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hAc).tendsto
    simp only [Function.comp_apply, hA0, zero_im] at ht
    exact ht.eventually hstrip
  have hBe : ∀ᶠ y in 𝓝 x, (B y).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hBd.continuousAt).tendsto
    simp only [Function.comp_apply, hB0, zero_im] at ht
    exact ht.eventually hstrip
  have hAB : A =ᶠ[𝓝 x] B := by
    filter_upwards [hAe, hBe, hU.mem_nhds hx] with y hyA hyB hy
    apply exp_inj_of_neg_pi_lt_of_le_pi hyA.1 hyA.2.le hyB.1 hyB.2.le
    dsimp [A, B]
    rw [exp_sub, he y hy, he x hx, exp_log]
    exact div_ne_zero ((he y hy) ▸ exp_ne_zero (L y)) hG0
  have hAd : DifferentiableAt ℂ A x := hBd.congr_of_eventuallyEq hAB
  simpa only [A, sub_add_cancel] using (hAd.add_const (L x)).differentiableWithinAt

/-- A normalized nonvanishing holomorphic disk function has a normalized holomorphic logarithm. -/
theorem exists_normalized_disk_log {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G unitDisc)
    (hGne : ∀ z ∈ unitDisc, G z ≠ 0) (hG0 : G 0 = 1) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ L 0 = 0 ∧ ∀ z ∈ unitDisc, exp (L z) = G z := by
  letI : ContractibleSpace unitDisc :=
    (show Convex ℝ unitDisc from convex_ball 0 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  have hsim : IsSimplyConnected unitDisc := by
    change SimplyConnectedSpace unitDisc
    infer_instance
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim
    (show IsOpen unitDisc from isOpen_ball) hG.continuousOn (by
      rintro ⟨z, hz, he⟩
      exact hGne z hz he)
  change EqOn (fun z => exp (L z)) G unitDisc at hLe
  have hLd := differentiableOn_of_continuous_exp_lift (show IsOpen unitDisc from isOpen_ball)
    hG hLc hLe
  refine ⟨fun z => L z - L 0, hLd.sub_const _, sub_self _, ?_⟩
  intro z hz
  have hlez : exp (L z) = G z := hLe hz
  have hle0 : exp (L 0) = G 0 := hLe (mem_ball_self one_pos)
  rw [exp_sub, hlez, hle0, hG0, div_one]

/-- Actual existence of the normalized disk-axis logarithmic coefficients, for any
chosen constant b00. This is an axis construction, not the full two-variable array. -/
theorem disk_axis_coefficients_exist {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1) (b00 : ℂ) :
    ∃ a : ℕ → ℂ, a 0 = b00 ∧ ∀ z ∈ unitDisc, ∃ S : ℂ,
      HasSum (fun n => a n * z ^ n) S ∧ exp (b00 - S) = dslope f 0 z := by
  have hq : DifferentiableOn ℂ (dslope f 0) unitDisc :=
    (differentiableOn_dslope (ball_mem_nhds (0 : ℂ) one_pos)).mpr hf
  have hq0 : dslope f 0 0 = 1 := by rw [dslope_same, hf0]
  have hqne : ∀ z ∈ unitDisc, dslope f 0 z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simpa only [hz0, hq0] using (one_ne_zero : (1 : ℂ) ≠ 0)
    · rw [dslope_of_ne f hz0, slope_def_field, sub_zero]
      exact div_ne_zero (sub_ne_zero.mpr (fun he => hz0 (hi hz (mem_ball_self one_pos) he))) hz0
  obtain ⟨L, hLd, hL0, he⟩ := exists_normalized_disk_log hq hqne hq0
  let F : ℂ → ℂ := fun z => b00 - L z
  let a : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0
  refine ⟨a, ?_, ?_⟩
  · simp [a, F, hL0]
  · intro z hz
    refine ⟨F z, ?_, ?_⟩
    · have hh := Complex.hasSum_taylorSeries_on_ball
        (show DifferentiableOn ℂ F unitDisc from (differentiableOn_const b00).sub hLd) hz
      simpa only [a, smul_eq_mul, sub_zero, mul_assoc, mul_comm, mul_left_comm] using hh
    · simpa [F] using he z hz

/-- Equality of scalar power-series sums determines every coefficient. -/
theorem powerSeries_coeff_unique {a b : ℕ → ℂ} {F : ℂ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (F z))
    (hb : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ n) (F z)) : a = b := by
  have hFa : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using ha z hz
  have hFb : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ b) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using hb z hz
  have hp := hFa.eq_formalMultilinearSeries hFb
  funext n
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hp
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc

/-- Every row of a convergent double disk series is a convergent scalar series. -/
theorem double_powerSeries_row_summable {a : ℕ → ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      Summable (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2))
    {w : ℂ} (hw : w ∈ unitDisc) (m : ℕ) : Summable (fun n => a m n * w ^ n) := by
  have hhalf : (1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, mem_ball, dist_zero_right]
  have hh := (ha (1 / 2) hhalf w hw).prod_factor m
  have hmul : Summable (fun n => (a m n * w ^ n) * (1 / 2 : ℂ) ^ m) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  exact (summable_mul_right_iff (pow_ne_zero m (by norm_num : (1 / 2 : ℂ) ≠ 0))).mp hmul

/-- Genuine two-variable coefficient uniqueness, by justified fiberwise summation
and scalar uniqueness twice. No Grunsky specification is used. -/
theorem double_powerSeries_coeff_unique {a b : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (ha : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    (hb : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => b p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w)) : a = b := by
  have hAr {w : ℂ} (hw : w ∈ unitDisc) (m : ℕ) : Summable (fun n => a m n * w ^ n) :=
    double_powerSeries_row_summable (fun z hz w hw => (ha z hz w hw).summable) hw m
  have hBr {w : ℂ} (hw : w ∈ unitDisc) (m : ℕ) : Summable (fun n => b m n * w ^ n) :=
    double_powerSeries_row_summable (fun z hz w hw => (hb z hz w hw).summable) hw m
  have hrows (w : ℂ) (hw : w ∈ unitDisc) :
      (fun m => ∑' n, a m n * w ^ n) = (fun m => ∑' n, b m n * w ^ n) := by
    apply powerSeries_coeff_unique (F := fun z => F z w)
    · intro z hz
      apply (ha z hz w hw).prod_fiberwise
      intro m
      apply ((hAr hw m).hasSum.mul_right (z ^ m)).congr_fun
      intro n
      ring
    · intro z hz
      apply (hb z hz w hw).prod_fiberwise
      intro m
      apply ((hBr hw m).hasSum.mul_right (z ^ m)).congr_fun
      intro n
      ring
  funext m
  apply powerSeries_coeff_unique (F := fun w => ∑' n, a m n * w ^ n)
  · intro w hw
    exact (hAr hw m).hasSum
  · intro w hw
    rw [congrFun (hrows w hw) m]
    exact (hBr hw m).hasSum

/-- A symmetric two-variable sum has symmetric coefficients. -/
theorem double_powerSeries_symm {a : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (ha : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    (hsymm : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, F z w = F w z) :
    ∀ m n, a m n = a n m := by
  have ht : a = (fun m n => a n m) := by
    apply double_powerSeries_coeff_unique ha
    intro z hz w hw
    have hh := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (ha w hw z hz)
    rw [hsymm w hw z hz] at hh
    simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.swap, mul_assoc, mul_comm, mul_left_comm] using hh
  exact fun m n => congrFun (congrFun ht m) n

/-- The present disk expansion itself forces derivative one at the origin.
This is a necessary condition for an IsGrunskyCoeff witness, not an assumed normalization. -/
theorem IsGrunskyCoeff.hasDerivAt_zero {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ}
    (hb : IsGrunskyCoeff f g b) : HasDerivAt f 1 0 := by
  let F : ℂ → ℂ := fun z => ∑' n : ℕ, b (-(n : ℤ)) 0 * z ^ n
  have hF : HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => b (-(n : ℤ)) 0)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
    simpa only [F, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm, zero_add] using
      (hb.negative_axis_right_summable hz).hasSum
  have hF0 : F 0 = b 0 0 := by simp [F, zero_pow_eq]
  have ht : Tendsto (fun z => exp (b 0 0 - F z)) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have hc := Complex.continuous_exp.continuousAt.comp
      ((continuousAt_const (y := b 0 0)).sub hF.continuousAt)
    simpa only [Function.comp_def, Pi.sub_apply, hF0, sub_self, exp_zero] using hc.tendsto
  have heq : (fun z => exp (b 0 0 - F z)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => (f z - f 0) / z) := by
    have hnear : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ unitDisc :=
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hz0
    obtain ⟨S, hS, hquot⟩ := hb.negative_axis_right hz hz0
    dsimp [F]
    rw [hS.tsum_eq]
    exact hquot.symm
  have hquot := (ht.mono_left nhdsWithin_le_nhds).congr' heq
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hquot

/-- Non-unit common scaling has no witness under the currently encoded normalization.
This does not by itself assert a counterexample to the full scaling conclusion. -/
theorem not_IsGrunskyCoeff_scaled {f g : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (hf0 : deriv f 0 = 1) {r : ℂ} (hr : r ≠ 1) (b : ℤ → ℤ → ℂ) :
    ¬ IsGrunskyCoeff (fun z => r * f z) (fun z => r * g z) b := by
  intro hb
  have hder := hb.hasDerivAt_zero.deriv
  rw [(hf.hasDerivAt.const_mul r).deriv, hf0, mul_one] at hder
  exact hr hder

/-- The removable divided difference is symmetric, including the diagonal. -/
theorem dslope_swap (f : ℂ → ℂ) (z w : ℂ) : dslope f z w = dslope f w z := by
  by_cases hzw : z = w
  · simp [hzw]
  · rw [dslope_of_ne f (Ne.symm hzw), dslope_of_ne f hzw, slope_comm]

/-- Univalence makes the diagonal-filled divided difference nonzero on the bidisk. -/
theorem univalent_dslope_ne_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hi : InjOn f unitDisc) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    dslope f z w ≠ 0 := by
  by_cases hwz : w = z
  · rw [hwz, dslope_same]
    exact deriv_ne_zero_of_injOn (show IsOpen unitDisc from isOpen_ball) hf hi hz
  · rw [dslope_of_ne f hwz, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => hwz (hi hw hz he))) (sub_ne_zero.mpr hwz)

/-- Each variable slice of the removable divided difference is holomorphic.
Joint holomorphy and the double expansion are separate construction steps. -/
theorem holomorphic_dslope_slices {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    DifferentiableOn ℂ (dslope f z) unitDisc ∧
      DifferentiableOn ℂ (fun w => dslope f w z) unitDisc := by
  have hd := (differentiableOn_dslope ((show IsOpen unitDisc from isOpen_ball).mem_nhds hz)).mpr hf
  refine ⟨hd, ?_⟩
  have he : (fun w => dslope f w z) = dslope f z := by funext w; exact dslope_swap f w z
  rw [he]
  exact hd

/-- Complex-linear interpolation in two endpoints, with real interpolation time. -/
def grunskySegmentCLM (t : ℝ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (1 - (t : ℂ)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ

theorem grunskySegmentCLM_apply (t : ℝ) (p : ℂ × ℂ) :
    grunskySegmentCLM t p = (1 - (t : ℂ)) * p.1 + (t : ℂ) * p.2 := by
  simp [grunskySegmentCLM]

/-- Interpolation is contractive in the maximum norm on the two endpoints. -/
theorem grunskySegmentCLM_norm_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖grunskySegmentCLM t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (grunskySegmentCLM t) (by norm_num)
  intro p
  rw [grunskySegmentCLM_apply, one_mul]
  have hn := norm_add_le ((1 - (t : ℂ)) * p.1) ((t : ℂ) * p.2)
  rw [norm_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1] at hn
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at hn
  have h1 := mul_le_mul_of_nonneg_left (norm_fst_le p) (show 0 ≤ 1 - t by linarith [ht.2])
  have h2 := mul_le_mul_of_nonneg_left (norm_snd_le p) ht.1
  nlinarith

theorem grunskySegmentCLM_norm_apply_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : ℂ × ℂ) :
    ‖grunskySegmentCLM t p‖ ≤ ‖p‖ := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_of_le_one_left (norm_nonneg p) (grunskySegmentCLM_norm_le ht))

theorem grunskySegmentCLM_continuous : Continuous grunskySegmentCLM := by
  unfold grunskySegmentCLM
  fun_prop

/-- A genuine parameter-integral proof of joint complex differentiability.
The integrable derivative bound is uniform in interpolation time. -/
theorem holomorphic_segment_integral {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => ∫ t in Icc (0 : ℝ) 1, g (grunskySegmentCLM t p))
      (unitDisc ×ˢ unitDisc) := by
  intro p hp
  have hp1 : ‖p‖ < 1 := by
    rw [Prod.norm_def]
    exact max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)
  obtain ⟨R, hpR, hR1⟩ := exists_between hp1
  have hR0 : 0 < R := (norm_nonneg p).trans_lt hpR
  let s : Set (ℂ × ℂ) := ball 0 R
  have hs : s ∈ 𝓝 p := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hpR)
  have hpath (q : ℂ × ℂ) (hq : q ∈ s) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      grunskySegmentCLM t q ∈ unitDisc :=
    mem_ball_zero_iff.mpr ((grunskySegmentCLM_norm_apply_le ht q).trans_lt
      ((mem_ball_zero_iff.mp hq).trans hR1))
  have hgp := hg.deriv (show IsOpen unitDisc from isOpen_ball)
  have hclosed : closedBall (0 : ℂ) R ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR1)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hgp.continuousOn.mono hclosed)
  let F : (ℂ × ℂ) → ℝ → ℂ := fun q t => g (grunskySegmentCLM t q)
  let F' : (ℂ × ℂ) → ℝ → (ℂ × ℂ) →L[ℂ] ℂ :=
    fun q t => deriv g (grunskySegmentCLM t q) • grunskySegmentCLM t
  have hFc (q : ℂ × ℂ) (hq : q ∈ s) : ContinuousOn (F q) (Icc (0 : ℝ) 1) := by
    exact hg.continuousOn.comp
      ((grunskySegmentCLM_continuous.clm_apply continuous_const).continuousOn) (hpath q hq)
  have hFpc (q : ℂ × ℂ) (hq : q ∈ s) : ContinuousOn (F' q) (Icc (0 : ℝ) 1) := by
    exact (hgp.continuousOn.comp
      ((grunskySegmentCLM_continuous.clm_apply continuous_const).continuousOn) (hpath q hq)).smul
        grunskySegmentCLM_continuous.continuousOn
  have hpS : p ∈ s := mem_ball_zero_iff.mpr hpR
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (F := F) (F' := F') (bound := fun _ => max C 0) hs
    (by filter_upwards [hs] with q hq; exact (hFc q hq).aestronglyMeasurable measurableSet_Icc)
    ((hFc p hpS).integrableOn_compact isCompact_Icc)
    ((hFpc p hpS).aestronglyMeasurable measurableSet_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      intro q hq
      have hqR : grunskySegmentCLM t q ∈ closedBall (0 : ℂ) R :=
        mem_closedBall_zero_iff.mpr ((grunskySegmentCLM_norm_apply_le ht q).trans
          (mem_ball_zero_iff.mp hq).le)
      have hCq : ‖deriv g (grunskySegmentCLM t q)‖ ≤ max C 0 := (hC _ hqR).trans (le_max_left _ _)
      change ‖deriv g (grunskySegmentCLM t q) • grunskySegmentCLM t‖ ≤ max C 0
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (grunskySegmentCLM_norm_le ht)).trans hCq)
    (integrableOn_const (show volume (Icc (0 : ℝ) 1) ≠ ∞ from measure_Icc_lt_top.ne))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      intro q hq
      have hga := hg.differentiableAt ((show IsOpen unitDisc from isOpen_ball).mem_nhds (hpath q hq t ht))
      exact hga.hasDerivAt.comp_hasFDerivAt q (grunskySegmentCLM t).hasFDerivAt)
  exact hd.differentiableAt.differentiableWithinAt

/-- The removable divided difference equals the integral of the derivative along
the line segment, including coincident endpoints. -/
theorem dslope_eq_integral_segment {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    dslope f z w = ∫ t in Icc (0 : ℝ) 1, deriv f (grunskySegmentCLM t (z, w)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hwz : w = z
  · subst w
    rw [dslope_same]
    have he : (fun t : ℝ => deriv f (grunskySegmentCLM t (z, z))) = fun _ => deriv f z := by
      funext t
      rw [grunskySegmentCLM_apply]
      congr 1
      ring
    rw [he]
    simp
  · have hp1 : ‖(z, w)‖ < 1 := by
      rw [Prod.norm_def]
      exact max_lt (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
    have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : grunskySegmentCLM t (z, w) ∈ unitDisc :=
      mem_ball_zero_iff.mpr ((grunskySegmentCLM_norm_apply_le ht (z, w)).trans_lt hp1)
    have hline (t : ℝ) : HasDerivAt (fun s : ℝ => grunskySegmentCLM s (z, w)) (w - z) t := by
      have he : (fun s : ℝ => grunskySegmentCLM s (z, w)) = AffineMap.lineMap z w := by
        funext s
        simp only [grunskySegmentCLM_apply, AffineMap.lineMap_apply_module, Complex.real_smul,
          Complex.ofReal_sub, Complex.ofReal_one]
      rw [he]
      exact AffineMap.hasDerivAt_lineMap
    have hder (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ => f (grunskySegmentCLM s (z, w)))
          ((w - z) * deriv f (grunskySegmentCLM t (z, w))) t := by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      have hfa := hf.differentiableAt ((show IsOpen unitDisc from isOpen_ball).mem_nhds (hpath t ht'))
      have hd := (hfa.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hline t)
      simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hd
    have hcont : ContinuousOn (fun t : ℝ => (w - z) * deriv f (grunskySegmentCLM t (z, w))) (Icc 0 1) := by
      apply continuousOn_const.mul
      exact ((hf.deriv (show IsOpen unitDisc from isOpen_ball)).continuousOn).comp
        (grunskySegmentCLM_continuous.clm_apply continuous_const).continuousOn hpath
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (hcont.intervalIntegrable_of_Icc zero_le_one)
    rw [intervalIntegral.integral_const_mul] at hFTC
    simp only [grunskySegmentCLM_apply, Complex.ofReal_one, Complex.ofReal_zero,
      sub_self, zero_mul, one_mul, sub_zero, zero_add, add_zero] at hFTC
    rw [dslope_of_ne f hwz, slope_def_field]
    apply (div_eq_iff (sub_ne_zero.mpr hwz)).mpr
    simpa only [grunskySegmentCLM_apply, mul_comm] using hFTC.symm

/-- Joint complex differentiability on the entire bidisk, including the diagonal.
It follows from the parameter integral, not from separate holomorphy. -/
theorem holomorphic_dslope_joint {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => dslope f p.1 p.2) (unitDisc ×ˢ unitDisc) := by
  apply (holomorphic_segment_integral (hf.deriv (show IsOpen unitDisc from isOpen_ball))).congr
  intro p hp
  exact dslope_eq_integral_segment hf hp.1 hp.2

theorem continuousOn_dslope_joint {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (unitDisc ×ˢ unitDisc) :=
  (holomorphic_dslope_joint hf).continuousOn

/-- The local logarithm argument for a genuinely joint holomorphic map on a product domain. -/
theorem differentiableOn_exp_lift_prod {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {G L : (ℂ × ℂ) → ℂ} (hG : DifferentiableOn ℂ G U) (hL : ContinuousOn L U)
    (he : ∀ p ∈ U, exp (L p) = G p) : DifferentiableOn ℂ L U := by
  intro p hp
  have hGp := hG.differentiableAt (hU.mem_nhds hp)
  have hLp := hL.continuousAt (hU.mem_nhds hp)
  have hG0 : G p ≠ 0 := (he p hp) ▸ exp_ne_zero (L p)
  let A : (ℂ × ℂ) → ℂ := fun q => L q - L p
  let B : (ℂ × ℂ) → ℂ := fun q => log (G q / G p)
  have hA0 : A p = 0 := by simp [A]
  have hB0 : B p = 0 := by simp [B, hG0]
  have hBd : DifferentiableAt ℂ B p := by
    apply (differentiableAt_log (by simp [hG0])).comp p
    simpa only [div_eq_mul_inv] using hGp.mul_const (G p)⁻¹
  have hstrip : Ioo (-π) π ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  have hAc : ContinuousAt A p := hLp.sub continuousAt_const
  have hAe : ∀ᶠ q in 𝓝 p, (A q).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hAc).tendsto
    simp only [Function.comp_apply, hA0, zero_im] at ht
    exact ht.eventually hstrip
  have hBe : ∀ᶠ q in 𝓝 p, (B q).im ∈ Ioo (-π) π := by
    have ht := (Complex.continuous_im.continuousAt.comp hBd.continuousAt).tendsto
    simp only [Function.comp_apply, hB0, zero_im] at ht
    exact ht.eventually hstrip
  have hAB : A =ᶠ[𝓝 p] B := by
    filter_upwards [hAe, hBe, hU.mem_nhds hp] with q hqA hqB hq
    apply exp_inj_of_neg_pi_lt_of_le_pi hqA.1 hqA.2.le hqB.1 hqB.2.le
    dsimp [A, B]
    rw [exp_sub, he q hq, he p hp, exp_log]
    exact div_ne_zero ((he q hq) ▸ exp_ne_zero (L q)) hG0
  have hAd : DifferentiableAt ℂ A p := hBd.congr_of_eventuallyEq hAB
  simpa only [A, sub_add_cancel] using (hAd.add_const (L p)).differentiableWithinAt

/-- A normalized jointly holomorphic logarithm of the divided difference on the
whole bidisk. No separate-to-joint holomorphy inference is used. -/
theorem exists_bidisk_divided_difference_log {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1) :
    ∃ L : (ℂ × ℂ) → ℂ, DifferentiableOn ℂ L (unitDisc ×ˢ unitDisc) ∧
      L (0, 0) = 0 ∧ ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = dslope f p.1 p.2 := by
  let U := unitDisc ×ˢ unitDisc
  have hUo : IsOpen U := isOpen_ball.prod isOpen_ball
  have hUc : Convex ℝ U := (convex_ball (0 : ℂ) 1).prod (convex_ball (0 : ℂ) 1)
  have hzero : (0, 0) ∈ U := ⟨mem_ball_self one_pos, mem_ball_self one_pos⟩
  letI : ContractibleSpace U := hUc.contractibleSpace ⟨(0, 0), hzero⟩
  have hsim : IsSimplyConnected U := by change SimplyConnectedSpace U; infer_instance
  have hQ := holomorphic_dslope_joint hf
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim hUo hQ.continuousOn (by
    rintro ⟨p, hp, he⟩
    exact univalent_dslope_ne_zero hf hi hp.1 hp.2 he)
  have hLd := differentiableOn_exp_lift_prod hUo hQ hLc (fun p hp => hLe hp)
  refine ⟨fun p => L p - L (0, 0), hLd.sub_const _, sub_self _, ?_⟩
  intro p hp
  have hep : exp (L p) = dslope f p.1 p.2 := hLe hp
  have he0 : exp (L (0, 0)) = 1 := by simpa only [Function.comp_def, dslope_same, hf0] using hLe hzero
  rw [exp_sub, hep, he0, div_one]

/-- Continuous exponential lifts on a connected space are determined by one value. -/
theorem continuous_exp_lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {L M : X → ℂ} (hL : Continuous L) (hM : Continuous M)
    (he : ∀ x, exp (L x) = exp (M x)) {x₀ : X} (h0 : L x₀ = M x₀) : L = M := by
  let D : X → ℂ := fun x => L x - M x
  have hDc : Continuous D := hL.sub hM
  have hDe (x : X) : exp (D x) = 1 := by
    dsimp [D]
    rw [exp_sub, he x, div_self (exp_ne_zero _)]
  have hloc : IsLocallyConstant D := by
    apply (IsLocallyConstant.iff_eventually_eq D).mpr
    intro x
    have hcont : ContinuousAt (fun y => (D y - D x).im) x := by fun_prop
    have hstrip : Ioo (-π) π ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
    have ht : Tendsto (fun y => (D y - D x).im) (𝓝 x) (𝓝 0) := by simpa using hcont.tendsto
    filter_upwards [ht.eventually hstrip] with y hy
    have hz : D y - D x = 0 := by
      apply exp_inj_of_neg_pi_lt_of_le_pi hy.1 hy.2.le (by simpa using neg_neg_of_pos Real.pi_pos)
        (by simpa using Real.pi_pos.le)
      rw [exp_sub, hDe y, hDe x, div_one, exp_zero]
    exact sub_eq_zero.mp hz
  funext x
  have hdx := hloc.apply_eq_of_preconnectedSpace x x₀
  dsimp [D] at hdx
  rw [h0, sub_self] at hdx
  exact sub_eq_zero.mp hdx

/-- The normalized logarithm is symmetric in its two endpoints. -/
theorem bidisk_divided_difference_log_symm {f : ℂ → ℂ} {L : (ℂ × ℂ) → ℂ}
    (hL : ContinuousOn L (unitDisc ×ˢ unitDisc))
    (he : ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = dslope f p.1 p.2) :
    ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, L (z, w) = L (w, z) := by
  let U := unitDisc ×ˢ unitDisc
  have hUc : Convex ℝ U := (convex_ball (0 : ℂ) 1).prod (convex_ball (0 : ℂ) 1)
  have hzero : (0, 0) ∈ U := ⟨mem_ball_self one_pos, mem_ball_self one_pos⟩
  letI : ContractibleSpace U := hUc.contractibleSpace ⟨(0, 0), hzero⟩
  have hLc : Continuous (fun p : U => L p) := hL.comp_continuous continuous_subtype_val (fun p => p.property)
  have hMc : Continuous (fun p : U => L (p.val.2, p.val.1)) :=
    hL.comp_continuous (by fun_prop) (fun p => ⟨p.property.2, p.property.1⟩)
  have heq := continuous_exp_lift_unique hLc hMc (fun p => by
    rw [he p p.property, he (p.val.2, p.val.1) ⟨p.property.2, p.property.1⟩]
    exact dslope_swap f p.val.1 p.val.2) (x₀ := ⟨(0, 0), hzero⟩) rfl
  intro z hz w hw
  exact congrFun heq ⟨(z, w), hz, hw⟩

/-- Interchanging a circle average and an absolutely uniformly dominated series. -/
theorem circleAverage_hasSum_of_bound {ι : Type*} [Countable ι]
    {T : ι → ℂ → ℂ} {K : ℂ → ℂ} {B : ι → ℝ} {R : ℝ}
    (hT : ∀ i, CircleIntegrable (T i) 0 R) (hB : Summable B)
    (hbound : ∀ i, ∀ u ∈ sphere (0 : ℂ) |R|, ‖T i u‖ ≤ B i)
    (hpoint : ∀ u ∈ sphere (0 : ℂ) |R|, HasSum (fun i => T i u) (K u)) :
    HasSum (fun i => Real.circleAverage (T i) 0 R) (Real.circleAverage K 0 R) := by
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun i (_ : ℝ) => B i) (fun i => (hT i).def'.1)
    (fun i => Eventually.of_forall fun θ _ => hbound i _ (circleMap_mem_sphere' 0 R θ))
    (Eventually.of_forall fun _ _ => hB) intervalIntegrable_const
    (Eventually.of_forall fun θ _ => hpoint _ (circleMap_mem_sphere' 0 R θ))
  simpa only [Real.circleAverage_def] using hi.const_smul ((2 * π)⁻¹ : ℝ)

/-- Two circle averages can be interchanged with a uniformly dominated double series. -/
theorem double_circleAverage_hasSum_of_bound {ι : Type*} [Countable ι]
    {T : ι → ℂ × ℂ → ℂ} {K : ℂ × ℂ → ℂ} {B : ι → ℝ} {R : ℝ}
    (hin : ∀ i, ∀ u ∈ sphere (0 : ℂ) |R|, CircleIntegrable (fun v => T i (u, v)) 0 R)
    (hout : ∀ i, CircleIntegrable (fun u => Real.circleAverage (fun v => T i (u, v)) 0 R) 0 R)
    (hB : Summable B)
    (hbound : ∀ i, ∀ u ∈ sphere (0 : ℂ) |R|, ∀ v ∈ sphere (0 : ℂ) |R|, ‖T i (u, v)‖ ≤ B i)
    (hpoint : ∀ u ∈ sphere (0 : ℂ) |R|, ∀ v ∈ sphere (0 : ℂ) |R|,
      HasSum (fun i => T i (u, v)) (K (u, v))) :
    HasSum (fun i => Real.circleAverage (fun u => Real.circleAverage (fun v => T i (u, v)) 0 R) 0 R)
      (Real.circleAverage (fun u => Real.circleAverage (fun v => K (u, v)) 0 R) 0 R) := by
  apply circleAverage_hasSum_of_bound hout hB
  · intro i u hu
    exact Real.norm_circleAverage_le_circleAverage_norm.trans
      (Real.circleAverage_mono_on_of_le_circle (hin i u hu).norm (hbound i u hu))
  · intro u hu
    exact circleAverage_hasSum_of_bound (fun i => hin i u hu) hB
      (fun i => hbound i u hu) (hpoint u hu)

/-- Continuous data on a product of circles have integrable inner and outer means. -/
theorem circleAverage_iterated_integrable {T : ℂ × ℂ → ℂ} {R : ℝ}
    (hT : ContinuousOn T (sphere (0 : ℂ) |R| ×ˢ sphere (0 : ℂ) |R|)) :
    (∀ u ∈ sphere (0 : ℂ) |R|, CircleIntegrable (fun v => T (u, v)) 0 R) ∧
      CircleIntegrable (fun u => Real.circleAverage (fun v => T (u, v)) 0 R) 0 R := by
  have hc : Continuous (fun p : ℝ × ℝ => T (circleMap 0 R p.1, circleMap 0 R p.2)) :=
    hT.comp_continuous (by fun_prop) (fun p => ⟨circleMap_mem_sphere' 0 R p.1, circleMap_mem_sphere' 0 R p.2⟩)
  constructor
  · intro u hu
    have hcu : Continuous (fun θ : ℝ => T (u, circleMap 0 R θ)) :=
      hT.comp_continuous (by fun_prop) (fun θ => ⟨hu, circleMap_mem_sphere' 0 R θ⟩)
    exact hcu.intervalIntegrable _ _
  · have hmean := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun θ η : ℝ => T (circleMap 0 R θ, circleMap 0 R η)) hc 0 (2 * π)).const_smul ((2 * π)⁻¹ : ℝ)
    exact hmean.intervalIntegrable _ _

/-- Double Cauchy coefficients, defined by genuine iterated circle averages. -/
def bidiskCauchyCoeff (F : ℂ × ℂ → ℂ) (R : ℝ) (m n : ℕ) : ℂ :=
  Real.circleAverage (fun u => Real.circleAverage (fun v => F (u, v) / (u ^ m * v ^ n)) 0 R) 0 R

/-- Iterated Cauchy means reconstruct a jointly holomorphic function inside a smaller bidisk. -/
theorem bidiskCauchy_reproduces {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc)) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R) :
    Real.circleAverage (fun u => Real.circleAverage
      (fun v => (u / (u - z)) * (v / (v - w)) * F (u, v)) 0 R) 0 R = F (z, w) := by
  have hsub : closedBall (0 : ℂ) R ⊆ unitDisc := fun u hu =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hR1)
  have hs1 (v : ℂ) (hv : v ∈ unitDisc) :
      DiffContOnCl ℂ (fun u => F (u, v)) (ball 0 |R|) := by
    have hd : DifferentiableOn ℂ (fun u => F (u, v)) unitDisc :=
      hF.comp (differentiableOn_id.prodMk (differentiableOn_const v)) (fun u hu => ⟨hu, hv⟩)
    rw [abs_of_pos hR0]
    refine ⟨hd.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball 0 hR0.ne']
    exact hd.continuousOn.mono hsub
  have hs2 (u : ℂ) (hu : u ∈ unitDisc) :
      DiffContOnCl ℂ (fun v => F (u, v)) (ball 0 |R|) := by
    have hd : DifferentiableOn ℂ (fun v => F (u, v)) unitDisc :=
      hF.comp ((differentiableOn_const u).prodMk differentiableOn_id) (fun v hv => ⟨hu, hv⟩)
    rw [abs_of_pos hR0]
    refine ⟨hd.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball 0 hR0.ne']
    exact hd.continuousOn.mono hsub
  have hin (u : ℂ) (hu : u ∈ sphere (0 : ℂ) |R|) :
      Real.circleAverage (fun v => (u / (u - z)) * (v / (v - w)) * F (u, v)) 0 R =
        (u / (u - z)) * F (u, w) := by
    have huD : u ∈ unitDisc := hsub (by simpa [abs_of_pos hR0] using sphere_subset_closedBall hu)
    have hm := (hs2 u huD).circleAverage_smul_div
      (show w ∈ ball (0 : ℂ) |R| by simpa [abs_of_pos hR0] using mem_ball_zero_iff.mpr hw)
    simp only [sub_zero, smul_eq_mul] at hm
    have heq : (fun v => (u / (u - z)) * (v / (v - w)) * F (u, v)) =
        (fun v => (u / (u - z)) • ((v / (v - w)) * F (u, v))) := by funext v; simp only [smul_eq_mul]; ring
    rw [heq, Real.circleAverage_fun_smul, hm]
    rfl
  calc
    _ = Real.circleAverage (fun u => (u / (u - z)) * F (u, w)) 0 R := Real.circleAverage_congr_sphere hin
    _ = F (z, w) := by
      have hm := (hs1 w (mem_ball_zero_iff.mpr (hw.trans hR1))).circleAverage_smul_div
        (show z ∈ ball (0 : ℂ) |R| by simpa [abs_of_pos hR0] using mem_ball_zero_iff.mpr hz)
      simpa only [sub_zero, smul_eq_mul] using hm

/-- Actual double-series convergence to a holomorphic function on every smaller
bidisk, with explicit Cauchy coefficients and a summable geometric majorant. -/
theorem hasSum_bidiskCauchyCoeff {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc)) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R) :
    HasSum (fun p : ℕ × ℕ => bidiskCauchyCoeff F R p.1 p.2 * z ^ p.1 * w ^ p.2) (F (z, w)) := by
  let S := sphere (0 : ℂ) |R| ×ˢ sphere (0 : ℂ) |R|
  have hsub : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ⊆ unitDisc ×ˢ unitDisc := by
    intro p hp
    exact ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.1).trans_lt hR1),
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.2).trans_lt hR1)⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
    (hF.continuousOn.mono hsub)
  have hN (u : ℂ) (hu : u ∈ sphere (0 : ℂ) |R|) : ‖u‖ = R := by
    simpa [mem_sphere, dist_zero_right, abs_of_pos hR0] using hu
  have hne (u : ℂ) (hu : u ∈ sphere (0 : ℂ) |R|) : u ≠ 0 := norm_pos_iff.mp ((hN u hu) ▸ hR0)
  have hSS : S ⊆ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := by
    intro p hp
    exact ⟨mem_closedBall_zero_iff.mpr (hN p.1 hp.1).le, mem_closedBall_zero_iff.mpr (hN p.2 hp.2).le⟩
  let T : (ℕ × ℕ) → ℂ × ℂ → ℂ := fun i p => F p * (z / p.1) ^ i.1 * (w / p.2) ^ i.2
  let K : ℂ × ℂ → ℂ := fun p => (p.1 / (p.1 - z)) * (p.2 / (p.2 - w)) * F p
  let B : (ℕ × ℕ) → ℝ := fun i => max C 0 * (‖z‖ / R) ^ i.1 * (‖w‖ / R) ^ i.2
  have hTc (i : ℕ × ℕ) : ContinuousOn (T i) S := by
    apply ((hF.continuousOn.mono (hSS.trans hsub)).mul
      ((continuousOn_const.div continuousOn_fst (fun p hp => hne p.1 hp.1)).pow i.1)).mul
    exact (continuousOn_const.div continuousOn_snd (fun p hp => hne p.2 hp.2)).pow i.2
  have hBsum : Summable B := by
    have hzs := summable_geometric_of_lt_one (div_nonneg (norm_nonneg z) hR0.le) ((div_lt_one hR0).mpr hz)
    have hws := summable_geometric_of_lt_one (div_nonneg (norm_nonneg w) hR0.le) ((div_lt_one hR0).mpr hw)
    have hh := hzs.mul_of_nonneg hws (fun _ => by positivity) (fun _ => by positivity)
    simpa only [B, mul_assoc] using hh.mul_left (max C 0)
  have hbound (i : ℕ × ℕ) (u : ℂ) (hu : u ∈ sphere (0 : ℂ) |R|)
      (v : ℂ) (hv : v ∈ sphere (0 : ℂ) |R|) : ‖T i (u, v)‖ ≤ B i := by
    dsimp [T, B]
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, norm_div, hN u hu, hN v hv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hC (u, v) (hSS ⟨hu, hv⟩)).trans (le_max_left _ _)) (by positivity)) (by positivity)
  have hpoint (u : ℂ) (hu : u ∈ sphere (0 : ℂ) |R|)
      (v : ℂ) (hv : v ∈ sphere (0 : ℂ) |R|) : HasSum (fun i => T i (u, v)) (K (u, v)) := by
    have hzu : ‖z / u‖ < 1 := by rw [norm_div, hN u hu]; exact (div_lt_one hR0).mpr hz
    have hwv : ‖w / v‖ < 1 := by rw [norm_div, hN v hv]; exact (div_lt_one hR0).mpr hw
    have hzg := hasSum_geometric_of_norm_lt_one hzu
    have hwg := hasSum_geometric_of_norm_lt_one hwv
    have hprod := hzg.mul hwg (summable_mul_of_summable_norm hzg.summable.norm hwg.summable.norm)
    have hku : (1 - z / u)⁻¹ = u / (u - z) := by rw [one_sub_div (hne u hu), inv_div]
    have hkv : (1 - w / v)⁻¹ = v / (v - w) := by rw [one_sub_div (hne v hv), inv_div]
    simpa only [T, K, hku, hkv, mul_assoc, mul_comm, mul_left_comm] using hprod.mul_left (F (u, v))
  have hseries := double_circleAverage_hasSum_of_bound
    (fun i => (circleAverage_iterated_integrable (hTc i)).1)
    (fun i => (circleAverage_iterated_integrable (hTc i)).2) hBsum hbound hpoint
  have hcoeff (i : ℕ × ℕ) :
      Real.circleAverage (fun u => Real.circleAverage (fun v => T i (u, v)) 0 R) 0 R =
        bidiskCauchyCoeff F R i.1 i.2 * z ^ i.1 * w ^ i.2 := by
    have hp (u v : ℂ) : T i (u, v) = (z ^ i.1 * w ^ i.2) • (F (u, v) / (u ^ i.1 * v ^ i.2)) := by
      simp only [T, div_pow, div_eq_mul_inv, mul_inv, smul_eq_mul]
      ring
    simp_rw [hp, Real.circleAverage_fun_smul]
    change (z ^ i.1 * w ^ i.2) • bidiskCauchyCoeff F R i.1 i.2 = _
    simp only [smul_eq_mul]
    ring
  simp_rw [hcoeff] at hseries
  have hvalue : Real.circleAverage (fun u => Real.circleAverage (fun v => K (u, v)) 0 R) 0 R = F (z, w) :=
    bidiskCauchy_reproduces hF hR0 hR1 hz hw
  rwa [hvalue] at hseries

/-- The constructed double coefficients do not depend on the smaller integration radius. -/
theorem bidiskCauchyCoeff_radius_independent {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc)) {R S : ℝ}
    (hR0 : 0 < R) (hR1 : R < 1) (hS0 : 0 < S) (hS1 : S < 1) :
    bidiskCauchyCoeff F R = bidiskCauchyCoeff F S := by
  let ρ : ℝ := min R S / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρR : ρ < R := by dsimp [ρ]; linarith [min_le_left R S]
  have hρS : ρ < S := by dsimp [ρ]; linarith [min_le_right R S]
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hsum (T : ℝ) (hT0 : 0 < T) (hT1 : T < 1) (hρT : ρ < T)
      (z : ℂ) (hz : z ∈ unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      HasSum (fun p : ℕ × ℕ =>
        (bidiskCauchyCoeff F T p.1 p.2 * (ρ : ℂ) ^ p.1 * (ρ : ℂ) ^ p.2) * z ^ p.1 * w ^ p.2)
        (F ((ρ : ℂ) * z, (ρ : ℂ) * w)) := by
    have hscale (v : ℂ) (hv : v ∈ unitDisc) : ‖(ρ : ℂ) * v‖ < T := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
      exact (mul_lt_of_lt_one_right hρ0 (mem_ball_zero_iff.mp hv)).trans hρT
    have hh := hasSum_bidiskCauchyCoeff hF hT0 hT1 (hscale z hz) (hscale w hw)
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh
  have heq : (fun m n => bidiskCauchyCoeff F R m n * (ρ : ℂ) ^ m * (ρ : ℂ) ^ n) =
      (fun m n => bidiskCauchyCoeff F S m n * (ρ : ℂ) ^ m * (ρ : ℂ) ^ n) :=
    double_powerSeries_coeff_unique (F := fun z w => F ((ρ : ℂ) * z, (ρ : ℂ) * w))
      (hsum R hR0 hR1 hρR) (hsum S hS0 hS1 hρS)
  funext m n
  have hh : bidiskCauchyCoeff F R m n * (ρ : ℂ) ^ m * (ρ : ℂ) ^ n =
      bidiskCauchyCoeff F S m n * (ρ : ℂ) ^ m * (ρ : ℂ) ^ n := congrFun (congrFun heq m) n
  have hh' : bidiskCauchyCoeff F R m n * (ρ : ℂ) ^ m = bidiskCauchyCoeff F S m n * (ρ : ℂ) ^ m :=
    mul_right_cancel₀ (pow_ne_zero n hρC) hh
  exact mul_right_cancel₀ (pow_ne_zero m hρC) hh'

/-- One coefficient array, fixed at radius 1/2, expands the function on the entire bidisk. -/
theorem hasSum_bidiskCauchyCoeff_unitDisc {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun p : ℕ × ℕ => bidiskCauchyCoeff F (1 / 2) p.1 p.2 * z ^ p.1 * w ^ p.2) (F (z, w)) := by
  have hmax : max ‖z‖ ‖w‖ < 1 := max_lt (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)
  obtain ⟨R, hRlow, hR1⟩ := exists_between hmax
  have hR0 : 0 < R := (norm_nonneg z).trans_lt ((le_max_left _ _).trans_lt hRlow)
  rw [bidiskCauchyCoeff_radius_independent hF (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hR0 hR1]
  exact hasSum_bidiskCauchyCoeff hF hR0 hR1 ((le_max_left _ _).trans_lt hRlow)
    ((le_max_right _ _).trans_lt hRlow)

theorem bidiskCauchyCoeff_zero_zero {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc)) :
    bidiskCauchyCoeff F (1 / 2) 0 0 = F (0, 0) := by
  have hh := hasSum_bidiskCauchyCoeff_unitDisc hF (mem_ball_self one_pos) (mem_ball_self one_pos)
  have hs := hasSum_double_axis_right (c := bidiskCauchyCoeff F (1 / 2)) hh
  simpa [zero_pow_eq] using hs.tsum_eq

/-- Actual existence and symmetry of the complete negative-index Grunsky block.
The exterior and mixed blocks are not asserted here. -/
theorem grunsky_negative_block_exists {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1) (b00 : ℂ) :
    ∃ a : ℕ → ℕ → ℂ, a 0 0 = b00 ∧ (∀ m n, a m n = a n m) ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
        HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
          (f z - f w) / (z - w) = exp (b00 - S) := by
  obtain ⟨L, hLd, hL0, hLe⟩ := exists_bidisk_divided_difference_log hf hi hf0
  let F : ℂ × ℂ → ℂ := fun p => b00 - L p
  have hFd : DifferentiableOn ℂ F (unitDisc ×ˢ unitDisc) := (differentiableOn_const b00).sub hLd
  have hseries (z : ℂ) (hz : z ∈ unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :=
    hasSum_bidiskCauchyCoeff_unitDisc hFd hz hw
  refine ⟨bidiskCauchyCoeff F (1 / 2), ?_, ?_, ?_⟩
  · rw [bidiskCauchyCoeff_zero_zero hFd]
    simp [F, hL0]
  · apply double_powerSeries_symm hseries
    intro z hz w hw
    dsimp [F]
    rw [bidisk_divided_difference_log_symm hLd.continuousOn hLe z hz w hw]
  · intro z hz w hw hzw
    refine ⟨F (z, w), hseries z hz w hw, ?_⟩
    have he := hLe (z, w) ⟨hz, hw⟩
    rw [dslope_swap f z w, dslope_of_ne f hzw, slope_def_field] at he
    simpa [F] using he.symm

/-- A power series `Σ dₙ zⁿ` that converges at points of every modulus `x < 1` converges on the open disk,
and its sum is continuous there. -/
theorem g1_series_disk {d : ℕ → ℂ}
    (h : ∀ x : ℝ, 0 < x → x < 1 → ∃ s : ℂ, ‖s‖ = x ∧ Summable (fun n => d n * s ^ n)) :
    (∀ z ∈ unitDisc, HasSum (fun n => d n * z ^ n) (∑' n, d n * z ^ n)) ∧
      ContinuousOn (fun z => ∑' n, d n * z ^ n) unitDisc := by
  -- geometric domination on every smaller closed disk
  have key : ∀ r : ℝ, 0 < r → r < 1 → ∃ (C : ℝ) (x : ℝ), 0 < x ∧ r < x ∧ x < 1 ∧
      ∀ n, ‖d n‖ * x ^ n ≤ C := by
    intro r hr0 hr1
    obtain ⟨x, hrx, hx1⟩ := exists_between hr1
    have hx0 : 0 < x := hr0.trans hrx
    obtain ⟨s, hs, hsum⟩ := h x hx0 hx1
    have hbdd := hsum.tendsto_atTop_zero.norm.bddAbove_range
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨C, x, hx0, hrx, hx1, fun n => ?_⟩
    have := hC ⟨n, rfl⟩
    simpa [norm_mul, norm_pow, hs] using this
  have hsum_ball : ∀ r : ℝ, 0 < r → r < 1 → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n, ∀ z : ℂ, ‖z‖ ≤ r → ‖d n * z ^ n‖ ≤ u n := by
    intro r hr0 hr1
    obtain ⟨C, x, hx0, hrx, hx1, hC⟩ := key r hr0 hr1
    refine ⟨fun n => C * (r / x) ^ n, ?_, ?_⟩
    · exact (summable_geometric_of_lt_one (div_nonneg hr0.le hx0.le) ((div_lt_one hx0).mpr hrx)).mul_left C
    · intro n z hz
      have hxn : 0 < x ^ n := pow_pos hx0 n
      calc ‖d n * z ^ n‖ = ‖d n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
        _ ≤ ‖d n‖ * r ^ n := by gcongr
        _ = (‖d n‖ * x ^ n) * (r / x) ^ n := by
          rw [div_pow]; field_simp
        _ ≤ C * (r / x) ^ n := by
          gcongr
          exact hC n
  constructor
  · intro z hz
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨r, hzr, hr1⟩ := exists_between hzn
    have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
    obtain ⟨u, hu, hb⟩ := hsum_ball r hr0 hr1
    exact (Summable.of_norm_bounded hu (fun n => hb n z hzr.le)).hasSum
  · intro z hz
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨r, hzr, hr1⟩ := exists_between hzn
    have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
    obtain ⟨u, hu, hb⟩ := hsum_ball r hr0 hr1
    have hcont : ContinuousOn (fun z => ∑' n, d n * z ^ n) (closedBall (0 : ℂ) r) := by
      apply continuousOn_tsum (u := u) (fun n => by fun_prop) hu
      intro n w hw
      exact hb n w (mem_closedBall_zero_iff.mp hw)
    exact (hcont.continuousAt (closedBall_mem_nhds_of_mem (by simpa using hzr))).continuousWithinAt

/-- Symmetry of the coefficients of a double power series whose exponential is symmetric. -/
theorem g1_double_sym_of_exp {a : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ} {c0 : ℂ}
    (hS : ∀ s ∈ unitDisc, s ≠ 0 → ∀ t ∈ unitDisc, t ≠ 0 → s ≠ t → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * s ^ p.1 * t ^ p.2) S ∧ K s t = exp (c0 - S))
    (hK : ∀ s t, K s t = K t s) : ∀ m n, a m n = a n m := by
  let d : ℕ → ℕ → ℂ := fun p q => a p q - a q p
  let D' : Set ℂ := unitDisc \ {0}
  have hD'dense : ∀ F : Set ℂ, F.Finite → unitDisc ⊆ closure (unitDisc \ F) := by
    intro F hF z hz
    have hd : Dense Fᶜ := hF.countable.dense_compl ℝ
    have := hd.open_subset_closure_inter (show IsOpen unitDisc from isOpen_ball) hz
    exact closure_mono (by intro w hw; exact ⟨hw.1, hw.2⟩) this
  -- Step A
  have hA : ∀ s ∈ unitDisc, s ≠ 0 → ∀ t ∈ unitDisc, t ≠ 0 → s ≠ t → ∃ E : ℂ,
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * s ^ p.1 * t ^ p.2) E ∧ exp E = 1 := by
    intro s hs hs0 t ht ht0 hst
    obtain ⟨S1, h1, k1⟩ := hS s hs hs0 t ht ht0 hst
    obtain ⟨S2, h2, k2⟩ := hS t ht ht0 s hs hs0 (Ne.symm hst)
    have h2' : HasSum (fun p : ℕ × ℕ => a p.2 p.1 * s ^ p.1 * t ^ p.2) S2 := by
      refine ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h2).congr_fun ?_
      intro p
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      ring
    refine ⟨S1 - S2, ?_, ?_⟩
    · refine (h1.sub h2').congr_fun ?_
      intro p
      simp only [d]
      ring
    · have hk : exp (c0 - S1) = exp (c0 - S2) := by rw [← k1, ← k2, hK]
      rw [exp_sub, exp_sub] at hk
      have hc : exp c0 ≠ 0 := exp_ne_zero _
      have h1' : exp S1 ≠ 0 := exp_ne_zero _
      have h2'' : exp S2 ≠ 0 := exp_ne_zero _
      rw [div_eq_div_iff h1' h2''] at hk
      have hS12 : exp S1 = exp S2 := (mul_left_cancel₀ hc hk).symm
      rw [exp_sub, hS12, div_self h2'']
  let Ev : ℂ → ℂ → ℂ := fun s t => ∑' p : ℕ × ℕ, d p.1 p.2 * s ^ p.1 * t ^ p.2
  let e : ℂ → ℕ → ℂ := fun t p => ∑' q : ℕ, d p q * t ^ q
  let Φ : ℂ → ℂ → ℂ := fun t s => ∑' p : ℕ, e t p * s ^ p
  have hconn : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  haveI : PreconnectedSpace unitDisc := isPreconnected_iff_preconnectedSpace.mp hconn
  have hmemD' : ∀ z, z ∈ D' ↔ z ∈ unitDisc ∧ z ≠ 0 := fun z => by simp [D']
  -- F1
  have F1 : ∀ s ∈ D', ∀ t ∈ D', s ≠ t →
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * s ^ p.1 * t ^ p.2) (Ev s t) ∧ exp (Ev s t) = 1 := by
    intro s hs t ht hst
    obtain ⟨hs1, hs0⟩ := (hmemD' s).mp hs
    obtain ⟨ht1, ht0⟩ := (hmemD' t).mp ht
    obtain ⟨E, hE, hexp⟩ := hA s hs1 hs0 t ht1 ht0 hst
    have : Ev s t = E := hE.tsum_eq
    rw [this]
    exact ⟨hE, hexp⟩
  -- F2
  have F2 : ∀ s ∈ D', ∀ t ∈ D', s ≠ t →
      (∀ p, Summable (fun q => d p q * t ^ q)) ∧ HasSum (fun p => e t p * s ^ p) (Ev s t) := by
    intro s hs t ht hst
    obtain ⟨hE, -⟩ := F1 s hs t ht hst
    obtain ⟨hs1, hs0⟩ := (hmemD' s).mp hs
    have hrs : ∀ p, Summable (fun q => d p q * t ^ q) := by
      intro p
      have h1 := hE.summable.prod_factor p
      have hsp : s ^ p ≠ 0 := pow_ne_zero p hs0
      have h2 : Summable (fun q => s ^ p * (d p q * t ^ q)) :=
        h1.congr (fun q => by simp only; ring)
      exact (summable_mul_left_iff hsp).mp h2
    refine ⟨hrs, ?_⟩
    apply hE.prod_fiberwise
    intro p
    have := (hrs p).hasSum.mul_right (s ^ p)
    convert this using 1
    funext q
    simp only
    ring
  -- F3
  have F3 : ∀ t ∈ D', (∀ s ∈ unitDisc, HasSum (fun p => e t p * s ^ p) (Φ t s)) ∧
      ContinuousOn (Φ t) unitDisc := by
    intro t ht
    apply g1_series_disk (d := e t)
    intro x hx0 hx1
    by_cases hxt : ((x : ℝ) : ℂ) = t
    · refine ⟨-(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : (-(x : ℂ)) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        simpa using hx0.ne'
      have hne : (-(x : ℂ)) ≠ t := by
        intro h
        have : (x : ℂ) = 0 := by rw [← hxt] at h; linear_combination -h / 2
        exact hx0.ne' (by exact_mod_cast this)
      exact (F2 _ hs t ht hne).2.summable
    · refine ⟨(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : ((x : ℝ) : ℂ) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        exact_mod_cast hx0.ne'
      exact (F2 _ hs t ht hxt).2.summable
  -- F4
  have F4 : ∀ t ∈ D', ∀ s ∈ D', s ≠ t → Φ t s = Ev s t := by
    intro t ht s hs hst
    exact ((F3 t ht).1 s ((hmemD' s).mp hs).1).unique (F2 s hs t ht hst).2
  -- F5
  have F5 : ∀ t ∈ D', ∀ s ∈ unitDisc, exp (Φ t s) = 1 := by
    intro t ht s hs
    have hcl := hD'dense {0, t} (Set.toFinite _)
    have hEq : EqOn (fun s => exp (Φ t s)) (fun _ => (1 : ℂ)) unitDisc := by
      apply Set.EqOn.of_subset_closure (s := unitDisc \ {0, t}) (t := unitDisc) _
        (Complex.continuous_exp.comp_continuousOn (F3 t ht).2) continuousOn_const diff_subset hcl
      intro w hw
      have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
      have hwt : w ≠ t := fun h => hw.2 (by simp [h])
      have hwD' : w ∈ D' := (hmemD' w).mpr ⟨hw.1, hw0⟩
      show exp (Φ t w) = 1
      rw [F4 t ht w hwD' hwt]
      exact (F1 w hwD' t ht hwt).2
    exact hEq hs
  -- F6
  have F6 : ∀ t ∈ D', ∀ s ∈ unitDisc, Φ t s = Φ t 0 := by
    intro t ht s hs
    have hc : Continuous (fun x : unitDisc => Φ t (x : ℂ)) :=
      (F3 t ht).2.comp_continuous continuous_subtype_val (fun x => x.2)
    have := continuous_exp_lift_unique (X := unitDisc) (L := fun x => Φ t (x : ℂ))
      (M := fun _ => Φ t 0) hc continuous_const
      (fun x => by rw [F5 t ht _ x.2, F5 t ht 0 (mem_ball_self one_pos)])
      (x₀ := ⟨0, mem_ball_self one_pos⟩) rfl
    exact congrFun this ⟨s, hs⟩
  -- F7, F8
  have F7 : ∀ t ∈ D', ∀ s ∈ D', s ≠ t → Ev s t = Φ t 0 := by
    intro t ht s hs hst
    rw [← F4 t ht s hs hst, F6 t ht s ((hmemD' s).mp hs).1]
  have F8 : ∀ s ∈ D', ∀ t ∈ D', s ≠ t → Ev s t = - Ev t s := by
    intro s hs t ht hst
    have h1 := (F1 t ht s hs (Ne.symm hst)).1
    have h2 := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr h1
    have h3 : HasSum (fun p : ℕ × ℕ => -(d p.1 p.2 * s ^ p.1 * t ^ p.2)) (Ev t s) := by
      refine h2.congr_fun ?_
      intro p
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, d]
      ring
    have h4 := h3.neg
    simp only [neg_neg] at h4
    exact ((F1 s hs t ht hst).1).unique h4
  -- F9
  have hp1 : ((1 : ℂ) / 2) ∈ D' :=
    (hmemD' _).mpr ⟨by simp [unitDisc, mem_ball_zero_iff, norm_div]; norm_num, by norm_num⟩
  have hp2 : ((1 : ℂ) / 3) ∈ D' :=
    (hmemD' _).mpr ⟨by simp [unitDisc, mem_ball_zero_iff, norm_div]; norm_num, by norm_num⟩
  have hp3 : ((1 : ℂ) / 4) ∈ D' :=
    (hmemD' _).mpr ⟨by simp [unitDisc, mem_ball_zero_iff, norm_div]; norm_num, by norm_num⟩
  have hrel : ∀ u ∈ D', ∀ v ∈ D', u ≠ v → Φ v 0 = - Φ u 0 := by
    intro u hu v hv huv
    rw [← F7 v hv u hu huv, ← F7 u hu v hv (Ne.symm huv)]
    exact F8 u hu v hv huv
  have hne12 : ((1 : ℂ) / 2) ≠ 1 / 3 := by norm_num
  have hne13 : ((1 : ℂ) / 2) ≠ 1 / 4 := by norm_num
  have hne23 : ((1 : ℂ) / 3) ≠ 1 / 4 := by norm_num
  have hz1 : Φ (1 / 2) 0 = 0 := by
    have a1 := hrel _ hp1 _ hp2 hne12
    have a2 := hrel _ hp1 _ hp3 hne13
    have a3 := hrel _ hp2 _ hp3 hne23
    linear_combination (a1 + a2 - a3) / 2
  have hz : ∀ t ∈ D', Φ t 0 = 0 := by
    intro t ht
    by_cases h : t = 1 / 2
    · rw [h]; exact hz1
    · rw [hrel _ hp1 t ht (Ne.symm h), hz1, neg_zero]
  -- F10, F11
  have F10 : ∀ t ∈ D', ∀ s ∈ unitDisc, Φ t s = 0 := fun t ht s hs => by rw [F6 t ht s hs, hz t ht]
  have F11 : ∀ t ∈ D', ∀ p, e t p = 0 := by
    intro t ht
    have := powerSeries_coeff_unique (a := e t) (b := fun _ => 0) (F := fun _ => 0)
      (fun z hz => by simpa [F10 t ht z hz] using (F3 t ht).1 z hz)
      (fun z _ => by simpa using hasSum_zero)
    exact fun p => congrFun this p
  have hrowsum : ∀ t ∈ D', ∀ p, Summable (fun q => d p q * t ^ q) := by
    intro t ht p
    by_cases h : t = 1 / 2
    · exact (F2 (1 / 3) hp2 t ht (by rw [h]; norm_num)).1 p
    · exact (F2 (1 / 2) hp1 t ht (Ne.symm h)).1 p
  -- F12
  have F12 : ∀ p q, d p q = 0 := by
    intro p
    have hpr := g1_series_disk (d := fun q => d p q) (by
      intro x hx0 hx1
      refine ⟨(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : ((x : ℝ) : ℂ) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        exact_mod_cast hx0.ne'
      exact hrowsum _ hs p)
    have hcl := hD'dense {0} (Set.toFinite _)
    have hG0 : EqOn (fun z => ∑' q, d p q * z ^ q) (fun _ => (0 : ℂ)) unitDisc := by
      apply Set.EqOn.of_subset_closure (s := unitDisc \ {0}) (t := unitDisc) _ hpr.2 continuousOn_const
        diff_subset hcl
      intro w hw
      have hwD' : w ∈ D' := hw
      show ∑' q, d p q * w ^ q = 0
      exact F11 w hwD' p
    have := powerSeries_coeff_unique (a := fun q => d p q) (b := fun _ => 0) (F := fun _ => 0)
      (fun z hz => by simpa [hG0 hz] using hpr.1 z hz)
      (fun z _ => by simpa using hasSum_zero)
    exact fun q => congrFun this q
  intro m n
  have := F12 m n
  simp only [d] at this
  exact sub_eq_zero.mp this


/-- Inversion of an exterior univalent function: `φ(s) = b / g(1/s)` is normalized univalent on `𝔻`. -/
theorem g1_inverted_exterior {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ φ : ℂ → ℂ, ∃ b : ℂ, DifferentiableOn ℂ φ unitDisc ∧ InjOn φ unitDisc ∧ φ 0 = 0 ∧ deriv φ 0 = 1 ∧
      b ≠ 0 ∧ derivAtInfty g = b ∧ ∀ s ∈ unitDisc, s ≠ 0 → g (1 / s) = b / φ s := by
  obtain ⟨hfd, hfi, hf0, hf1, ⟨hgd, hgi, hgt⟩, hdisj⟩ := h
  have hext : ∀ s ∈ unitDisc, s ≠ 0 → 1 / s ∈ unitDiscExterior := by
    intro s hs hs0
    have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    show 1 < ‖1 / s‖
    rw [norm_div, norm_one, lt_div_iff₀ hpos]
    linarith
  have hgne : ∀ z ∈ unitDiscExterior, g z ≠ 0 := by
    intro z hz hgz
    have h0 : (0 : ℂ) ∈ f '' unitDisc := ⟨0, mem_ball_self one_pos, hf0⟩
    have h1 : (0 : ℂ) ∈ g '' unitDiscExterior := ⟨z, hz, hgz⟩
    exact Set.disjoint_left.mp hdisj h0 h1
  -- ψ(s) = 1 / g(1/s) on the punctured disc, tending to 0
  let ψ : ℂ → ℂ := fun s => (g (1 / s))⁻¹
  have hψd : DifferentiableOn ℂ ψ (unitDisc \ {0}) := by
    intro s hs
    have hs' : s ∈ unitDisc := hs.1
    have hs0 : s ≠ 0 := hs.2
    have hgd' : DifferentiableAt ℂ g (1 / s) :=
      hgd.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds (hext s hs' hs0))
    have : DifferentiableAt ℂ (fun s => g (1 / s)) s := by
      apply DifferentiableAt.comp s (g := g) (f := fun s => 1 / s) hgd'
      exact (differentiableAt_const _).div differentiableAt_id hs0
    exact (this.inv (hgne _ (hext s hs' hs0))).differentiableWithinAt
  have hψt : Tendsto ψ (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => 1 / s) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      simpa only [one_div] using tendsto_inv₀_nhdsNE_zero (α := ℂ)
    have h2 : Tendsto (fun s : ℂ => g (1 / s)) (𝓝[≠] 0) (cocompact ℂ) := hgt.comp h1
    rw [← Metric.cobounded_eq_cocompact] at h2
    exact (tendsto_inv₀_cobounded (α := ℂ)).comp h2
  let φ0 : ℂ → ℂ := Function.update ψ 0 0
  have hφ0d : DifferentiableOn ℂ φ0 unitDisc := by
    refine (differentiableOn_compl_singleton_and_continuousAt_iff (c := (0 : ℂ)) (s := unitDisc)
      (ball_mem_nhds (0 : ℂ) one_pos)).mp ⟨hψd.congr ?_, continuousAt_update_same.mpr hψt⟩
    intro s hs
    exact Function.update_of_ne hs.2 _ _
  have hφ0ne : ∀ s ∈ unitDisc, s ≠ 0 → φ0 s = (g (1 / s))⁻¹ := by
    intro s _ hs0
    exact Function.update_of_ne hs0 _ _
  have hφ0nz : ∀ s ∈ unitDisc, s ≠ 0 → φ0 s ≠ 0 := by
    intro s hs hs0
    rw [hφ0ne s hs hs0]
    exact inv_ne_zero (hgne _ (hext s hs hs0))
  have hφ00 : φ0 0 = 0 := Function.update_self _ _ _
  have hφ0i : InjOn φ0 unitDisc := by
    intro s hs t ht hst
    by_cases hs0 : s = 0
    · by_cases ht0 : t = 0
      · rw [hs0, ht0]
      · exfalso
        exact hφ0nz t ht ht0 (by rw [← hst, hs0, hφ00])
    · by_cases ht0 : t = 0
      · exfalso
        exact hφ0nz s hs hs0 (by rw [hst, ht0, hφ00])
      · rw [hφ0ne s hs hs0, hφ0ne t ht ht0] at hst
        have hg1 : g (1 / s) = g (1 / t) := inv_injective hst
        have := hgi (hext s hs hs0) (hext t ht ht0) hg1
        simpa using this
  have hder0 : deriv φ0 0 ≠ 0 :=
    deriv_ne_zero_of_injOn (show IsOpen unitDisc from isOpen_ball) hφ0d hφ0i (mem_ball_self one_pos)
  set c : ℂ := (deriv φ0 0)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hder0
  refine ⟨fun s => c * φ0 s, c, hφ0d.const_mul c, ?_, by simp [hφ00], ?_, hc0, ?_, ?_⟩
  · intro s hs t ht hst
    exact hφ0i hs ht (mul_left_cancel₀ hc0 hst)
  · rw [deriv_const_mul _ ((hφ0d.differentiableAt (ball_mem_nhds (0 : ℂ) one_pos)))]
    rw [hc, inv_mul_cancel₀ hder0]
  · -- the derivative at infinity
    have hφd0 : HasDerivAt (fun s => c * φ0 s) 1 0 := by
      have h1 := ((hφ0d.differentiableAt (ball_mem_nhds (0 : ℂ) one_pos)).hasDerivAt.const_mul c)
      have : c * deriv φ0 0 = 1 := by rw [hc, inv_mul_cancel₀ hder0]
      rwa [this] at h1
    have hsl := hasDerivAt_iff_tendsto_slope.mp hφd0
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · rw [← Metric.cobounded_eq_cocompact]; exact tendsto_inv₀_cobounded (α := ℂ)
      · filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
        exact inv_ne_zero (by simpa using hz)
    have hslT : Tendsto (fun z : ℂ => slope (fun s => c * φ0 s) 0 z⁻¹) (cocompact ℂ) (𝓝 1) :=
      hsl.comp hinv
    have hfin : Tendsto (fun z : ℂ => c / slope (fun s => c * φ0 s) 0 z⁻¹) (cocompact ℂ) (𝓝 (c / 1)) :=
      tendsto_const_nhds.div hslT one_ne_zero
    rw [div_one] at hfin
    have hev : (fun z : ℂ => c / slope (fun s => c * φ0 s) 0 z⁻¹) =ᶠ[cocompact ℂ] fun z => g z / z := by
      filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
      have hz1 : 1 < ‖z‖ := by simpa using hz
      have hz0 : z ≠ 0 := by intro h0; subst h0; norm_num at hz1
      have hzi : z⁻¹ ∈ unitDisc := by
        apply mem_ball_zero_iff.mpr
        rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1
      have hzi0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
      rw [slope_def_field, hφ00, mul_zero, sub_zero, sub_zero, hφ0ne _ hzi hzi0]
      simp only [one_div, inv_inv, inv_inv]
      have hgz : g z ≠ 0 := hgne z hz1
      field_simp
    exact (hfin.congr' hev).limUnder_eq
  · intro s hs hs0
    show g (1 / s) = c / (c * φ0 s)
    have h1 := hφ0nz s hs hs0
    have h2 := hφ0ne s hs hs0
    have h3 : g (1 / s) = (φ0 s)⁻¹ := by rw [h2, inv_inv]
    rw [h3]
    field_simp


/-- A nonvanishing holomorphic function on the bidisk with value `1` at the origin has a normalized
holomorphic logarithm with a double power series on the whole bidisk. -/
theorem g1_bidisk_log_series {M : ℂ × ℂ → ℂ} (hM : DifferentiableOn ℂ M (unitDisc ×ˢ unitDisc))
    (hne : ∀ p ∈ unitDisc ×ˢ unitDisc, M p ≠ 0) (h0 : M (0, 0) = 1) :
    ∃ L : ℂ × ℂ → ℂ, DifferentiableOn ℂ L (unitDisc ×ˢ unitDisc) ∧ L (0, 0) = 0 ∧
      (∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = M p) ∧
      ∃ c : ℕ → ℕ → ℂ, ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
        HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (L (z, w)) := by
  let U := unitDisc ×ˢ unitDisc
  have hUo : IsOpen U := isOpen_ball.prod isOpen_ball
  have hUc : Convex ℝ U := (convex_ball (0 : ℂ) 1).prod (convex_ball (0 : ℂ) 1)
  have hzero : ((0 : ℂ), (0 : ℂ)) ∈ U := ⟨mem_ball_self one_pos, mem_ball_self one_pos⟩
  letI : ContractibleSpace U := hUc.contractibleSpace ⟨(0, 0), hzero⟩
  have hsim : IsSimplyConnected U := by change SimplyConnectedSpace U; infer_instance
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim hUo hM.continuousOn (by
    rintro ⟨p, hp, he⟩
    exact hne p hp he)
  have hLd := differentiableOn_exp_lift_prod hUo hM hLc (fun p hp => hLe hp)
  have hL1 : DifferentiableOn ℂ (fun p => L p - L (0, 0)) U := hLd.sub_const _
  have he0 : exp (L (0, 0)) = 1 := by
    have := hLe hzero
    simpa only [Function.comp_def, h0] using this
  refine ⟨fun p => L p - L (0, 0), hL1, sub_self _, ?_, bidiskCauchyCoeff (fun p => L p - L (0, 0)) (1 / 2), ?_⟩
  · intro p hp
    have hep : exp (L p) = M p := hLe hp
    show exp (L p - L (0, 0)) = M p
    rw [exp_sub, hep, he0, div_one]
  · intro z hz w hw
    exact hasSum_bidiskCauchyCoeff_unitDisc hL1 hz hw

/-- If the series coefficients of `L` come from a double expansion and `L` vanishes on the second axis,
then the second-axis coefficients vanish. -/
theorem g1_axis_right_zero {c : ℕ → ℕ → ℂ} {L : ℂ × ℂ → ℂ}
    (hL : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (L (z, w)))
    (hax : ∀ z ∈ unitDisc, L (z, 0) = 0) : ∀ n, c n 0 = 0 := by
  have h1 : ∀ z ∈ unitDisc, HasSum (fun n => c n 0 * z ^ n) (0 : ℂ) := by
    intro z hz
    have := hasSum_double_axis_right (c := c) (z := z) (S := L (z, 0)) (by
      simpa using hL z hz 0 (mem_ball_self one_pos))
    rwa [hax z hz] at this
  have h2 : ∀ z ∈ unitDisc, HasSum (fun n => (fun _ : ℕ => (0 : ℂ)) n * z ^ n) (0 : ℂ) := by
    intro z _
    simpa using hasSum_zero
  have := powerSeries_coeff_unique (F := fun _ => (0 : ℂ)) h1 h2
  intro n
  exact congrFun this n

/-- Same for the first axis. -/
theorem g1_axis_left_zero {c : ℕ → ℕ → ℂ} {L : ℂ × ℂ → ℂ}
    (hL : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) (L (z, w)))
    (hax : ∀ w ∈ unitDisc, L (0, w) = 0) : ∀ n, c 0 n = 0 := by
  have h1 : ∀ z ∈ unitDisc, HasSum (fun n => c 0 n * z ^ n) (0 : ℂ) := by
    intro z hz
    have := hasSum_double_axis_left (c := c) (z := z) (S := L (0, z)) (by
      simpa using hL 0 (mem_ball_self one_pos) z hz)
    rwa [hax z hz] at this
  have h2 : ∀ z ∈ unitDisc, HasSum (fun n => (fun _ : ℕ => (0 : ℂ)) n * z ^ n) (0 : ℂ) := by
    intro z _
    simpa using hasSum_zero
  have := powerSeries_coeff_unique (F := fun _ => (0 : ℂ)) h1 h2
  intro n
  exact congrFun this n

/-- A normalized logarithm of a function equal to `1` on an axis vanishes on that axis. -/
theorem g1_log_axis_zero_right {L : ℂ × ℂ → ℂ} {M : ℂ × ℂ → ℂ}
    (hLc : ContinuousOn L (unitDisc ×ˢ unitDisc)) (hL0 : L (0, 0) = 0)
    (hLe : ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = M p) (hax : ∀ z ∈ unitDisc, M (z, 0) = 1) :
    ∀ z ∈ unitDisc, L (z, 0) = 0 := by
  have hconv : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  haveI : PreconnectedSpace unitDisc := isPreconnected_iff_preconnectedSpace.mp hconv
  have hc : Continuous (fun x : unitDisc => L ((x : ℂ), 0)) := by
    apply hLc.comp_continuous (by fun_prop)
    intro x
    exact ⟨x.2, mem_ball_self one_pos⟩
  have := continuous_exp_lift_unique (X := unitDisc) (L := fun x => L ((x : ℂ), 0)) (M := fun _ => 0) hc
    continuous_const (by
      intro x
      rw [exp_zero, hLe _ ⟨x.2, mem_ball_self one_pos⟩, hax _ x.2])
    (x₀ := ⟨0, mem_ball_self one_pos⟩) (by simpa using hL0)
  intro z hz
  exact congrFun this ⟨z, hz⟩

/-- Same for the first axis. -/
theorem g1_log_axis_zero_left {L : ℂ × ℂ → ℂ} {M : ℂ × ℂ → ℂ}
    (hLc : ContinuousOn L (unitDisc ×ˢ unitDisc)) (hL0 : L (0, 0) = 0)
    (hLe : ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = M p) (hax : ∀ w ∈ unitDisc, M (0, w) = 1) :
    ∀ w ∈ unitDisc, L (0, w) = 0 := by
  have hconv : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  haveI : PreconnectedSpace unitDisc := isPreconnected_iff_preconnectedSpace.mp hconv
  have hc : Continuous (fun x : unitDisc => L (0, (x : ℂ))) := by
    apply hLc.comp_continuous (by fun_prop)
    intro x
    exact ⟨mem_ball_self one_pos, x.2⟩
  have := continuous_exp_lift_unique (X := unitDisc) (L := fun x => L (0, (x : ℂ))) (M := fun _ => 0) hc
    continuous_const (by
      intro x
      rw [exp_zero, hLe _ ⟨mem_ball_self one_pos, x.2⟩, hax _ x.2])
    (x₀ := ⟨0, mem_ball_self one_pos⟩) (by simpa using hL0)
  intro w hw
  exact congrFun this ⟨w, hw⟩

/-- Drop the vanishing zero-index rows and columns of a double series. -/
theorem g1_hasSum_shift_both {c : ℕ → ℕ → ℂ} {z w S : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) S)
    (h1 : ∀ n, c n 0 = 0) (h2 : ∀ n, c 0 n = 0) :
    HasSum (fun p : ℕ × ℕ => c (p.1 + 1) (p.2 + 1) * z ^ (p.1 + 1) * w ^ (p.2 + 1)) S := by
  let g : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2 + 1)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq, add_left_inj] at hpq
    exact Prod.ext hpq.1 hpq.2
  have hz : ∀ x ∉ Set.range g, (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) x = 0 := by
    rintro ⟨a, b⟩ hx
    simp only
    rcases a with _ | a
    · simp [h2]
    · rcases b with _ | b
      · simp [h1]
      · exact absurd ⟨(a, b), rfl⟩ hx
  exact (hg.hasSum_iff hz).mpr h

/-- Drop only the vanishing zero-index first row. -/
theorem g1_hasSum_shift_first {c : ℕ → ℕ → ℂ} {z w S : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) S)
    (h2 : ∀ n, c 0 n = 0) :
    HasSum (fun p : ℕ × ℕ => c (p.1 + 1) p.2 * z ^ (p.1 + 1) * w ^ p.2) S := by
  let g : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq, add_left_inj] at hpq
    exact Prod.ext hpq.1 hpq.2
  have hz : ∀ x ∉ Set.range g, (fun p : ℕ × ℕ => c p.1 p.2 * z ^ p.1 * w ^ p.2) x = 0 := by
    rintro ⟨a, b⟩ hx
    simp only
    rcases a with _ | a
    · simp [h2]
    · exact absurd ⟨(a, b), rfl⟩ hx
  exact (hg.hasSum_iff hz).mpr h

theorem g1_zpow_neg_succ (z : ℂ) (n : ℕ) : z ^ (-((n : ℤ) + 1)) = z⁻¹ ^ (n + 1) := by
  have h : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [zpow_neg, h, zpow_natCast, inv_pow]

theorem g1_dslope_zero_ne {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc)
    {s : ℂ} (hs : s ∈ unitDisc) : dslope φ 0 s ≠ 0 :=
  univalent_dslope_ne_zero hφd hφi (mem_ball_self one_pos) hs

/-- The exterior block: a double expansion of the logarithm of
`(s/φ(s)) (t/φ(t)) (φ(s) - φ(t))/(s - t)` with no axis terms. -/
theorem g1_ext_block {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc)
    (hφ1 : deriv φ 0 = 1) :
    ∃ C : ℕ → ℕ → ℂ, ∀ s ∈ unitDisc, ∀ t ∈ unitDisc, ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => C p.1 p.2 * s ^ (p.1 + 1) * t ^ (p.2 + 1)) S ∧
        exp (-S) = (dslope φ 0 s)⁻¹ * (dslope φ 0 t)⁻¹ * dslope φ s t := by
  let U := unitDisc ×ˢ unitDisc
  have hdsl : DifferentiableOn ℂ (dslope φ 0) unitDisc :=
    (differentiableOn_dslope (ball_mem_nhds (0 : ℂ) one_pos)).mpr hφd
  have hE1 : DifferentiableOn ℂ (fun s => (dslope φ 0 s)⁻¹) unitDisc :=
    hdsl.inv (fun s hs => g1_dslope_zero_ne hφd hφi hs)
  let M : ℂ × ℂ → ℂ := fun p => (dslope φ 0 p.1)⁻¹ * (dslope φ 0 p.2)⁻¹ * dslope φ p.1 p.2
  have hMd : DifferentiableOn ℂ M U := by
    have h1 : DifferentiableOn ℂ (fun p : ℂ × ℂ => (dslope φ 0 p.1)⁻¹) U :=
      hE1.comp differentiableOn_fst (fun p hp => hp.1)
    have h2 : DifferentiableOn ℂ (fun p : ℂ × ℂ => (dslope φ 0 p.2)⁻¹) U :=
      hE1.comp differentiableOn_snd (fun p hp => hp.2)
    exact (h1.mul h2).mul (holomorphic_dslope_joint hφd)
  have hMne : ∀ p ∈ U, M p ≠ 0 := by
    intro p hp
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (g1_dslope_zero_ne hφd hφi hp.1))
      (inv_ne_zero (g1_dslope_zero_ne hφd hφi hp.2))) (univalent_dslope_ne_zero hφd hφi hp.1 hp.2)
  have hdz : dslope φ 0 0 = 1 := by rw [dslope_same, hφ1]
  have hM0 : M (0, 0) = 1 := by
    show (dslope φ 0 0)⁻¹ * (dslope φ 0 0)⁻¹ * dslope φ 0 0 = 1
    rw [hdz]; norm_num
  have hax1 : ∀ z ∈ unitDisc, M (z, 0) = 1 := by
    intro z hz
    simp only [M, hdz, inv_one, mul_one]
    rw [dslope_swap φ z 0]
    exact inv_mul_cancel₀ (g1_dslope_zero_ne hφd hφi hz)
  have hax2 : ∀ w ∈ unitDisc, M (0, w) = 1 := by
    intro w hw
    simp only [M, hdz, inv_one, one_mul]
    exact inv_mul_cancel₀ (g1_dslope_zero_ne hφd hφi hw)
  obtain ⟨L, hLd, hL0, hLe, c, hc⟩ := g1_bidisk_log_series hMd hMne hM0
  have hz1 := g1_log_axis_zero_right hLd.continuousOn hL0 hLe hax1
  have hz2 := g1_log_axis_zero_left hLd.continuousOn hL0 hLe hax2
  have hc1 := g1_axis_right_zero hc hz1
  have hc2 := g1_axis_left_zero hc hz2
  refine ⟨fun p q => -c (p + 1) (q + 1), ?_⟩
  intro s hs t ht
  refine ⟨-L (s, t), ?_, ?_⟩
  · have := (g1_hasSum_shift_both (hc s hs t ht) hc1 hc2).neg
    refine this.congr_fun ?_
    intro p
    simp only [neg_mul]
  · rw [neg_neg]
    exact hLe (s, t) ⟨hs, ht⟩

/-- The mixed block: logarithm of `(s/φ(s)) (1 - f(ζ) φ(s)/b)`, no `s⁰` terms. -/
theorem g1_mix_block {f φ : ℂ → ℂ} {b : ℂ} (hb : b ≠ 0) (hfd : DifferentiableOn ℂ f unitDisc)
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hφ1 : deriv φ 0 = 1)
    (hdisj : ∀ s ∈ unitDisc, s ≠ 0 → ∀ ζ ∈ unitDisc, f ζ ≠ b / φ s) :
    ∃ C : ℕ → ℕ → ℂ, ∀ s ∈ unitDisc, ∀ ζ ∈ unitDisc, ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => C p.1 p.2 * s ^ (p.1 + 1) * ζ ^ p.2) S ∧
        exp (-S) = (dslope φ 0 s)⁻¹ * (1 - f ζ * φ s / b) := by
  let U := unitDisc ×ˢ unitDisc
  have hdsl : DifferentiableOn ℂ (dslope φ 0) unitDisc :=
    (differentiableOn_dslope (ball_mem_nhds (0 : ℂ) one_pos)).mpr hφd
  have hE1 : DifferentiableOn ℂ (fun s => (dslope φ 0 s)⁻¹) unitDisc :=
    hdsl.inv (fun s hs => g1_dslope_zero_ne hφd hφi hs)
  let M : ℂ × ℂ → ℂ := fun p => (dslope φ 0 p.1)⁻¹ * (1 - f p.2 * φ p.1 / b)
  have hMd : DifferentiableOn ℂ M U := by
    have h1 : DifferentiableOn ℂ (fun p : ℂ × ℂ => (dslope φ 0 p.1)⁻¹) U :=
      hE1.comp differentiableOn_fst (fun p hp => hp.1)
    have h2 : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.2) U :=
      hfd.comp differentiableOn_snd (fun p hp => hp.2)
    have h3 : DifferentiableOn ℂ (fun p : ℂ × ℂ => φ p.1) U :=
      hφd.comp differentiableOn_fst (fun p hp => hp.1)
    have h4 : DifferentiableOn ℂ (fun p : ℂ × ℂ => f p.2 * φ p.1 / b) U :=
      ((h2.mul h3).mul_const b⁻¹).congr (fun p _ => by simp [div_eq_mul_inv])
    exact h1.mul ((differentiableOn_const (1 : ℂ)).sub h4)
  have hMne : ∀ p ∈ U, M p ≠ 0 := by
    intro p hp
    refine mul_ne_zero (inv_ne_zero (g1_dslope_zero_ne hφd hφi hp.1)) ?_
    intro h0
    by_cases hs0 : p.1 = 0
    · simp [hs0, hφ0] at h0
    · have hφne : φ p.1 ≠ 0 := by
        intro h
        exact hs0 (hφi hp.1 (mem_ball_self one_pos) (by rw [h, hφ0]))
      apply hdisj p.1 hp.1 hs0 p.2 hp.2
      field_simp at h0 ⊢
      linear_combination -h0
  have hdz : dslope φ 0 0 = 1 := by rw [dslope_same, hφ1]
  have hM0 : M (0, 0) = 1 := by simp [M, hφ0, hφ1]
  have hax2 : ∀ w ∈ unitDisc, M (0, w) = 1 := by
    intro w _
    simp [M, hφ0, hφ1]
  obtain ⟨L, hLd, hL0, hLe, c, hc⟩ := g1_bidisk_log_series hMd hMne hM0
  have hz2 := g1_log_axis_zero_left hLd.continuousOn hL0 hLe hax2
  have hc2 := g1_axis_left_zero hc hz2
  refine ⟨fun p q => -c (p + 1) q, ?_⟩
  intro s hs t ht
  refine ⟨-L (s, t), ?_, ?_⟩
  · have := (g1_hasSum_shift_first (hc s hs t ht) hc2).neg
    refine this.congr_fun ?_
    intro p
    simp only [neg_mul]
  · rw [neg_neg]
    exact hLe (s, t) ⟨hs, ht⟩


-- G1c: assembly of `isGrunskyCoeff_exists`; to be appended after G1a (g1_inverted_exterior) and G1b.

theorem g1_alg_ext (b φs φt s t : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s ≠ t) (hφs : φs ≠ 0)
    (hφt : φt ≠ 0) :
    (b / φs - b / φt) / (s⁻¹ - t⁻¹) = b * ((φs / s)⁻¹ * (φt / t)⁻¹ * ((φt - φs) / (t - s))) := by
  have h1 : s⁻¹ - t⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_injective.ne hst)
  have h2 : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
  have h3 : t * s ≠ 0 := mul_ne_zero ht hs
  have h4 : s⁻¹ - t⁻¹ = (t - s) / (s * t) := by field_simp
  rw [h4]
  field_simp

theorem g1_alg_mix (b φs fz s : ℂ) (hb : b ≠ 0) (hs : s ≠ 0) (hφs : φs ≠ 0) :
    (b / φs - fz) / (b * s⁻¹) = (φs / s)⁻¹ * (1 - fz * φs / b) := by
  field_simp

/-- (G1) A normalized disjoint pair has Grunsky coefficients. -/
theorem isGrunskyCoeff_exists {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ b, IsGrunskyCoeff f g b := by
  obtain ⟨φ, b, hφd, hφi, hφ0, hφ1, hb0, hbinf, hgφ⟩ := g1_inverted_exterior h
  obtain ⟨hfd, hfi, hf0, hf1, hgU, hdisj⟩ := h
  have hext : ∀ s ∈ unitDisc, s ≠ 0 → s⁻¹ ∈ unitDiscExterior := by
    intro s hs hs0
    have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    show 1 < ‖s⁻¹‖
    rw [norm_inv]
    exact one_lt_inv₀ hpos |>.mpr hsn
  have hinvD : ∀ z ∈ unitDiscExterior, z⁻¹ ∈ unitDisc ∧ z⁻¹ ≠ 0 := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := by intro h0; subst h0; norm_num at hz1
    refine ⟨?_, inv_ne_zero hz0⟩
    apply mem_ball_zero_iff.mpr
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  have hgz : ∀ z ∈ unitDiscExterior, g z = b / φ z⁻¹ := by
    intro z hz
    obtain ⟨hs, hs0⟩ := hinvD z hz
    have := hgφ z⁻¹ hs hs0
    rwa [one_div, inv_inv] at this
  have hφne : ∀ s ∈ unitDisc, s ≠ 0 → φ s ≠ 0 := by
    intro s hs hs0 h0
    exact hs0 (hφi hs (mem_ball_self one_pos) (by rw [h0, hφ0]))
  obtain ⟨a, ha00, -, hexpA⟩ := grunsky_negative_block_exists hfd hfi hf1 (Complex.log b)
  obtain ⟨C, hC⟩ := g1_ext_block hφd hφi hφ1
  obtain ⟨Cm, hCm⟩ := g1_mix_block hb0 hfd hφd hφi hφ0 hφ1 (by
    intro s hs hs0 ζ hζ hfz
    have hmem : f ζ ∈ g '' unitDiscExterior := ⟨s⁻¹, hext s hs hs0, by rw [hgz _ (hext s hs hs0), inv_inv, hfz]⟩
    exact Set.disjoint_left.mp hdisj ⟨ζ, hζ, rfl⟩ hmem)
  let B : ℤ → ℤ → ℂ := fun i j =>
    if 1 ≤ i then (if 1 ≤ j then C (i - 1).toNat (j - 1).toNat else Cm (i - 1).toNat (-j).toNat)
    else (if 1 ≤ j then Cm (j - 1).toNat (-i).toNat else a (-i).toNat (-j).toNat)
  have hB1 : ∀ p q : ℕ, B ((p : ℤ) + 1) ((q : ℤ) + 1) = C p q := by
    intro p q
    have h1 : (1 : ℤ) ≤ (p : ℤ) + 1 := by omega
    have h2 : (1 : ℤ) ≤ (q : ℤ) + 1 := by omega
    simp [B, h1, h2]
  have hB2 : ∀ p q : ℕ, B ((p : ℤ) + 1) (-(q : ℤ)) = Cm p q := by
    intro p q
    have h1 : (1 : ℤ) ≤ (p : ℤ) + 1 := by omega
    have h2 : ¬ (1 : ℤ) ≤ -(q : ℤ) := by omega
    simp [B, h1, h2]
  have hB3 : ∀ n m : ℕ, B (-(n : ℤ)) ((m : ℤ) + 1) = Cm m n := by
    intro n m
    have h1 : ¬ (1 : ℤ) ≤ -(n : ℤ) := by omega
    have h2 : (1 : ℤ) ≤ (m : ℤ) + 1 := by omega
    simp [B, h1, h2]
  have hB4 : ∀ p q : ℕ, B (-(p : ℤ)) (-(q : ℤ)) = a p q := by
    intro p q
    have h1 : ¬ (1 : ℤ) ≤ -(p : ℤ) := by omega
    have h2 : ¬ (1 : ℤ) ≤ -(q : ℤ) := by omega
    simp [B, h1, h2]
  have hB00 : B 0 0 = Complex.log b := by
    have := hB4 0 0
    simp only [Nat.cast_zero, neg_zero] at this
    rw [this, ha00]
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB00, exp_log hb0, hbinf]
  · intro z hz ζ hζ hzζ
    obtain ⟨hs, hs0⟩ := hinvD z hz
    obtain ⟨ht, ht0⟩ := hinvD ζ hζ
    obtain ⟨S, hS, hexp⟩ := hC z⁻¹ hs ζ⁻¹ ht
    refine ⟨S, ?_, ?_⟩
    · refine hS.congr_fun ?_
      intro p
      rw [g1_zpow_neg_succ, g1_zpow_neg_succ, hB1]
    · have hq : b / cexp S = b * cexp (-S) := by rw [exp_neg, div_eq_mul_inv]
      rw [hB00, exp_sub, exp_log hb0, hq, hexp, hgz z hz, hgz ζ hζ]
      have hφs := hφne _ hs hs0
      have hφt := hφne _ ht ht0
      have hst : z⁻¹ ≠ ζ⁻¹ := fun h' => hzζ (inv_injective h')
      have hz0 : z ≠ 0 := (fun h' => hs0 (by rw [h', inv_zero]))
      have hζ0 : ζ ≠ 0 := (fun h' => ht0 (by rw [h', inv_zero]))
      rw [dslope_of_ne φ hs0, dslope_of_ne φ ht0, dslope_of_ne φ hst.symm, slope_def_field,
        slope_def_field, slope_def_field, hφ0, sub_zero, sub_zero, sub_zero, sub_zero]
      have := g1_alg_ext b (φ z⁻¹) (φ ζ⁻¹) z⁻¹ ζ⁻¹ hs0 ht0 hst hφs hφt
      rw [inv_inv, inv_inv] at this
      exact this
  · intro z hz ζ hζ
    obtain ⟨hs, hs0⟩ := hinvD z hz
    obtain ⟨S, hS, hexp⟩ := hCm z⁻¹ hs ζ hζ
    refine ⟨S, ?_, ?_⟩
    · refine hS.congr_fun ?_
      intro p
      rw [g1_zpow_neg_succ, hB2]
    · rw [hbinf, hexp, hgz z hz, dslope_of_ne φ hs0, slope_def_field, hφ0, sub_zero, sub_zero]
      have hφs := hφne _ hs hs0
      have := g1_alg_mix b (φ z⁻¹) (f ζ) z⁻¹ hb0 hs0 hφs
      rw [inv_inv] at this
      exact this
  · intro z hz ζ hζ hzζ
    obtain ⟨S, hS, hexp⟩ := hexpA z hz ζ hζ hzζ
    refine ⟨S, ?_, ?_⟩
    · refine hS.congr_fun ?_
      intro p
      rw [hB4]
    · rw [hB00]
      exact hexp
  · intro n m
    rw [hB3, hB2]

/-- (TT:3814) The Grunsky coefficients of a normalized disjoint pair exist, are unique up to the choice of
`b₀₀ ∈ log b`, and are symmetric (`b_{nm} = b_{mn}` for `n, m ≥ 1` or `n, m ≤ 0`).

[CORRECTION 2026-10-25] The dilation-invariance clause is dropped. `IsGrunskyCoeff` forces `f'(0) = 1`, so the dilated
pair `(rf, rg)` has no coefficients, and `grunsky` returns its junk value `0` (下属4: `f = id`, `g = 3z + 3/(2z)`,
`b₁₁ = 1/2`). TT's remark (TT:3814) concerns a renormalized definition that is not used here. -/
theorem grunsky_spec {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    IsGrunskyCoeff f g (grunsky f g) ∧
      ∀ n m : ℕ, grunsky f g (n + 1) (m + 1) = grunsky f g (m + 1) (n + 1) ∧
        grunsky f g (-(n : ℤ)) (-(m : ℤ)) = grunsky f g (-(m : ℤ)) (-(n : ℤ)) := by
  have hex := isGrunskyCoeff_exists h
  have hb : IsGrunskyCoeff f g (grunsky f g) := by
    show IsGrunskyCoeff f g (if h : ∃ b, IsGrunskyCoeff f g b then h.choose else fun _ _ => 0)
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hb, ?_⟩
  intro n m
  constructor
  · -- exterior block
    have hinv : ∀ s ∈ unitDisc, s ≠ 0 → s⁻¹ ∈ unitDiscExterior := by
      intro s hs hs0
      have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
      have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
      show 1 < ‖s⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr hsn
    let ã : ℕ → ℕ → ℂ := fun p q => if p = 0 ∨ q = 0 then 0 else grunsky f g (p : ℤ) (q : ℤ)
    have hsym := g1_double_sym_of_exp (a := ã)
      (K := fun s t => (g s⁻¹ - g t⁻¹) / (s⁻¹ - t⁻¹)) (c0 := grunsky f g 0 0)
      (by
        intro s hs hs0 t ht ht0 hst
        obtain ⟨S, hS, he⟩ := hb.2.1 s⁻¹ (hinv s hs hs0) t⁻¹ (hinv t ht ht0) (inv_injective.ne hst)
        refine ⟨S, ?_, he⟩
        have hshift : HasSum (fun p : ℕ × ℕ => ã (p.1 + 1) (p.2 + 1) * s ^ (p.1 + 1) * t ^ (p.2 + 1)) S := by
          refine hS.congr_fun ?_
          intro p
          simp only [ã, g1_zpow_neg_succ, inv_inv]
          simp
        let gg : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2 + 1)
        have hg : Function.Injective gg := by
          intro p q hpq
          simp only [gg, Prod.mk.injEq, add_left_inj] at hpq
          exact Prod.ext hpq.1 hpq.2
        have hz : ∀ x ∉ Set.range gg, (fun p : ℕ × ℕ => ã p.1 p.2 * s ^ p.1 * t ^ p.2) x = 0 := by
          rintro ⟨a, b⟩ hx
          rcases a with _ | a
          · simp [ã]
          · rcases b with _ | b
            · simp [ã]
            · exact absurd ⟨(a, b), rfl⟩ hx
        exact (hg.hasSum_iff hz).mp hshift)
      (by
        intro s t
        show (g s⁻¹ - g t⁻¹) / (s⁻¹ - t⁻¹) = (g t⁻¹ - g s⁻¹) / (t⁻¹ - s⁻¹)
        rw [← neg_sub (g s⁻¹) (g t⁻¹), ← neg_sub s⁻¹ t⁻¹, neg_div_neg_eq])
      (n + 1) (m + 1)
    simpa [ã] using hsym
  · -- interior block
    exact g1_double_sym_of_exp (a := fun p q => grunsky f g (-(p : ℤ)) (-(q : ℤ)))
      (K := fun s t => (f s - f t) / (s - t)) (c0 := grunsky f g 0 0)
      (by
        intro s hs _ t ht _ hst
        exact hb.2.2.2.1 s hs t ht hst)
      (by
        intro s t
        show (f s - f t) / (s - t) = (f t - f s) / (t - s)
        rw [← neg_sub (f s) (f t), ← neg_sub s t, neg_div_neg_eq])
      n m

-- `thm_2_1` moved to `Ch2/S2_Thm21.lean` (2026-10-26).

-- `remark_2_2` moved to `Ch2/S2_Remark22.lean` (2026-10-26).

-- `eq_2_1` moved to `Ch2/S2_Mixed.lean` (2026-10-26).

/-- `(B₁)_{mn} = √(mn) b_{-m,-n}` (TT:3871), indices `m + 1`, `n + 1`. -/
def B1 (b : ℤ → ℤ → ℂ) (m n : ℕ) : ℂ := Real.sqrt ((m + 1) * (n + 1) : ℝ) * b (-(m + 1 : ℤ)) (-(n + 1 : ℤ))
/-- `(B₂)_{mn} = √(mn) b_{-m,n}`. -/
def B2 (b : ℤ → ℤ → ℂ) (m n : ℕ) : ℂ := Real.sqrt ((m + 1) * (n + 1) : ℝ) * b (-(m + 1 : ℤ)) (n + 1)
/-- `(B₃)_{mn} = √(mn) b_{m,-n}`. -/
def B3 (b : ℤ → ℤ → ℂ) (m n : ℕ) : ℂ := Real.sqrt ((m + 1) * (n + 1) : ℝ) * b (m + 1) (-(n + 1 : ℤ))
/-- `(B₄)_{mn} = √(mn) b_{mn}`. -/
def B4 (b : ℤ → ℤ → ℂ) (m n : ℕ) : ℂ := Real.sqrt ((m + 1) * (n + 1) : ℝ) * b (m + 1) (n + 1)

/-- The entry `(A A'*)_{mn} = Σ_k A_{mk} \overline{A'_{nk}}` of a product with an adjoint. -/
def mulAdj (A A' : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ := ∑' k, A m k * conj (A' n k)

/-- `δ_{mn}`. -/
def kron (m n : ℕ) : ℂ := if m = n then 1 else 0

-- `eq_2_2` moved to `Ch2/S2_MixedHook.lean` (2026-10-26).

-- `grunsky_unitary` moved to `Ch2/S2_MixedHook.lean` (2026-10-26).

-- `remark_2_3` moved to `Ch2/S2_Remark23.lean` (2026-10-27).

/-- `K₁(z, w) = (1/π)(1/(z - w)² - f'(z)f'(w)/(f(z) - f(w))²)` off the diagonal
(TT:3949). [CORRECTION] On the diagonal use the removable value `-𝒮(f)/(6π)`,
as required by the holomorphic series and the same-sign formula at TT:4657. -/
def kerK1 (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  if z = w then -schwarzianHol f z / (6 * π)
  else 1 / π * (1 / (z - w) ^ 2 - deriv f z * deriv f w / (f z - f w) ^ 2)
/-- `K₂(z, w) = (1/π) f'(z)g'(w)/(f(z) - g(w))²` (TT:3953). -/
def kerK2 (f g : ℂ → ℂ) (z w : ℂ) : ℂ := 1 / π * (deriv f z * deriv g w / (f z - g w) ^ 2)
/-- `K₃(z, w) = (1/π) g'(z)f'(w)/(g(z) - f(w))²` (TT:3957). -/
def kerK3 (f g : ℂ → ℂ) (z w : ℂ) : ℂ := 1 / π * (deriv g z * deriv f w / (g z - f w) ^ 2)
/-- `K₄(z, w) = (1/π)(1/(z - w)² - g'(z)g'(w)/(g(z) - g(w))²)` off the diagonal
(TT:3961). [CORRECTION] `K₄(z,z) = -𝒮(g)(z)/(6π)` is explicit at TT:4657. -/
def kerK4 (g : ℂ → ℂ) (z w : ℂ) : ℂ :=
  if z = w then -schwarzianHol g z / (6 * π)
  else 1 / π * (1 / (z - w) ^ 2 - deriv g z * deriv g w / (g z - g w) ^ 2)

/-- The removable diagonal value of K1 (TT:3949, 4657). -/
theorem kerK1_diag (f : ℂ → ℂ) (z : ℂ) :
    kerK1 f z z = -schwarzianHol f z / (6 * π) := by simp [kerK1]

/-- The removable diagonal value of K4 (TT:4657). -/
theorem kerK4_diag (g : ℂ → ℂ) (z : ℂ) :
    kerK4 g z z = -schwarzianHol g z / (6 * π) := by simp [kerK4]

/-- The original K1 quotient holds away from the diagonal (TT:3949). -/
theorem kerK1_of_ne (f : ℂ → ℂ) {z w : ℂ} (h : z ≠ w) :
    kerK1 f z w = 1 / π * (1 / (z - w) ^ 2 -
      deriv f z * deriv f w / (f z - f w) ^ 2) := by simp [kerK1, h]

/-- The original K4 quotient holds away from the diagonal (TT:3961). -/
theorem kerK4_of_ne (g : ℂ → ℂ) {z w : ℂ} (h : z ≠ w) :
    kerK4 g z w = 1 / π * (1 / (z - w) ^ 2 -
      deriv g z * deriv g w / (g z - g w) ^ 2) := by simp [kerK4, h]

/-- Changing the K1 diagonal preserves area-integral formulas (TT:3949–3970). -/
theorem kerK1_ae_eq_quotient (f : ℂ → ℂ) (z : ℂ)
    (μ : Measure ℂ) [NullSingletonClass μ] :
    kerK1 f z =ᵐ[μ] (fun w => 1 / π * (1 / (z - w) ^ 2 -
      deriv f z * deriv f w / (f z - f w) ^ 2)) := by
  filter_upwards [μ.ae_ne z] with w hw
  exact kerK1_of_ne f hw.symm

/-- Changing the K4 diagonal preserves area-integral formulas (TT:3961–3976). -/
theorem kerK4_ae_eq_quotient (g : ℂ → ℂ) (z : ℂ)
    (μ : Measure ℂ) [NullSingletonClass μ] :
    kerK4 g z =ᵐ[μ] (fun w => 1 / π * (1 / (z - w) ^ 2 -
      deriv g z * deriv g w / (g z - g w) ^ 2)) := by
  filter_upwards [μ.ae_ne z] with w hw
  exact kerK4_of_ne g hw.symm

/-- The K1 extension also preserves almost-everywhere values in its first variable (TT:3949). -/
theorem kerK1_ae_eq_quotient_left (f : ℂ → ℂ) (w : ℂ)
    (μ : Measure ℂ) [NullSingletonClass μ] :
    (fun z => kerK1 f z w) =ᵐ[μ] (fun z => 1 / π * (1 / (z - w) ^ 2 -
      deriv f z * deriv f w / (f z - f w) ^ 2)) := by
  filter_upwards [μ.ae_ne w] with z hz
  exact kerK1_of_ne f hz

/-- The orthonormal basis `e_n(z) = √(n/π) z^{n-1}` of `A₂¹(𝔻)` (TT:3997), `n = k + 1`. -/
def basisE (k : ℕ) (z : ℂ) : ℂ := Real.sqrt ((k + 1 : ℝ) / π) * z ^ k
/-- The orthonormal basis `f_n(z) = √(n/π) z^{-n-1}` of `A₂¹(𝔻*)` (TT:3997), `n = k + 1`. -/
def basisF (k : ℕ) (z : ℂ) : ℂ := Real.sqrt ((k + 1 : ℝ) / π) * z ^ (-(k : ℤ) - 2)

-- `kernels_spec` moved to `Ch2/S2_Completed.lean` (2026-10-26).

/-- A21 functions on the finite-area disk are genuinely integrable. -/
theorem a21_disk_integrable {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc) :
    IntegrableOn φ unitDisc := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (show volume unitDisc ≠ ∞ from measure_ball_lt_top.ne)
  exact MemLp.integrable (by norm_num) (a21_memLp_two measurableSet_ball hφ)

/-- The punctured kernel in Remark 2.4 is integrable for every positive hole radius. -/
theorem remark_2_4_truncated_integrable {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun w => conj (φ w) / (z - w) ^ 2) (unitDisc \ ball z δ) := by
  have hmeas : MeasurableSet (unitDisc \ ball z δ) := measurableSet_ball.diff measurableSet_ball
  have hden (w : ℂ) (hw : w ∈ unitDisc \ ball z δ) : δ ≤ ‖z - w‖ := by
    simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hw.2
  have hc : ContinuousOn (fun w => conj (φ w) / (z - w) ^ 2) (unitDisc \ ball z δ) := by
    apply (Complex.continuous_conj.comp_continuousOn (hφ.1.continuousOn.mono Set.sdiff_subset)).div
      (by fun_prop)
    intro w hw
    exact pow_ne_zero 2 (norm_pos_iff.mp (hδ.trans_le (hden w hw)))
  have hiφ : IntegrableOn (fun w => ‖φ w‖) unitDisc := (a21_disk_integrable hφ).norm
  apply ((hiφ.mono_set Set.sdiff_subset).const_mul (δ ^ 2)⁻¹).mono'
    (hc.aestronglyMeasurable hmeas)
  filter_upwards [ae_restrict_mem hmeas] with w hw
  change ‖conj (φ w) / (z - w) ^ 2‖ ≤ (δ ^ 2)⁻¹ * ‖φ w‖
  rw [norm_div, norm_pow, norm_conj, ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ)
  exact pow_le_pow_left₀ hδ.le (hden w hw) 2

/-- Exact circle cancellation for the antiholomorphic kernel about its pole. -/
theorem remark_2_4_circle_zero {φ : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (closedBall c r)) :
    Real.circleAverage (fun w => conj (φ w) / (c - w) ^ 2) c r = 0 := by
  let F : ℂ → ℂ := fun w => (w - c) ^ 2 * φ w
  have hF : DifferentiableOn ℂ F (closedBall c r) :=
    ((differentiableOn_id.sub_const c).pow 2).mul hφ
  have hFC : DiffContOnCl ℂ F (ball c |r|) := by
    rw [abs_of_pos hr]
    refine ⟨hF.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball c hr.ne']
    exact hF.continuousOn
  have hmean : Real.circleAverage F c r = 0 := by
    simpa [F] using hFC.circleAverage
  have hconj : Real.circleAverage (fun w => conj (F w)) c r = 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm
      (hF.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hr.le)
    simpa [Function.comp_def, hmean] using hh
  have heq : Real.circleAverage (fun w => conj (φ w) / (c - w) ^ 2) c r =
      Real.circleAverage (fun w => ((r : ℂ) ^ 4)⁻¹ * conj (F w)) c r := by
    apply Real.circleAverage_congr_sphere
    intro w hw
    have hn : ‖w - c‖ = r := by simpa [mem_sphere, dist_eq_norm, abs_of_pos hr] using hw
    have hw0 : w - c ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hmul : (w - c) * conj (w - c) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_cast
    have hpow := congrArg (fun v : ℂ => v ^ 2) hmul
    dsimp [F]
    rw [map_mul, map_pow, show c - w = -(w - c) by ring, neg_sq]
    field_simp
    linear_combination -conj (φ w) * hpow
  rw [heq]
  change Real.circleAverage (fun w => ((r : ℂ) ^ 4)⁻¹ • conj (F w)) c r = 0
  rw [Real.circleAverage_fun_smul, hconj, smul_zero]

/-- Polar integration turns exact circle-average cancellation into area cancellation. -/
theorem disk_integral_zero_of_circleAverage_zero {G : ℂ → ℂ} (hGm : Measurable G)
    (hGi : IntegrableOn G unitDisc)
    (hcircle : ∀ r : ℝ, 0 < r → r < 1 → Real.circleAverage G 0 r = 0) :
    ∫ w in unitDisc, G w = 0 := by
  have hpolar := integrableOn_polar_of_integrableOn_ball hGm hGi
  rw [show unitDisc = ball (0 : ℂ) 1 from rfl, setIntegral_ball_eq_polar' 0 zero_le_one
    (by simpa only [add_zero] using hpolar)]
  calc
    _ = ∫ r in (0 : ℝ)..1, (0 : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (1 : ℝ)] with r hrne hr
      have hr' : r ∈ Ioc (0 : ℝ) 1 := by simpa using hr
      have havg := hcircle r hr'.1 (lt_of_le_of_ne hr'.2 hrne)
      rw [Real.circleAverage_def] at havg
      have hint : (∫ θ in (0 : ℝ)..2 * π, G (circleMap 0 r θ)) = 0 :=
        (smul_eq_zero.mp havg).resolve_left (by positivity)
      rw [intervalIntegral.integral_const_mul, hint, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

/-- Exact cancellation at the disk center for every positive truncation radius.
This is a center subcase of Remark 2.4, not the general-center statement. -/
theorem remark_2_4_center_truncated_zero {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ w in unitDisc \ ball (0 : ℂ) δ, conj (φ w) / (0 - w) ^ 2) = 0 := by
  let S : Set ℂ := unitDisc \ ball (0 : ℂ) δ
  let K : ℂ → ℂ := fun w => conj (φ w) / (0 - w) ^ 2
  let G : ℂ → ℂ := S.indicator K
  have hSm : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  have hKc : ContinuousOn K S := by
    apply (Complex.continuous_conj.comp_continuousOn (hφ.1.continuousOn.mono Set.sdiff_subset)).div
      (by fun_prop)
    intro w hw
    have hn : δ ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw.2
    exact pow_ne_zero 2 (sub_ne_zero.mpr (norm_pos_iff.mp (hδ.trans_le hn)).symm)
  have hGm : Measurable G := by
    have hh := hKc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hSm
    have he : G = S.piecewise K (fun _ => 0) := by
      ext w
      by_cases hw : w ∈ S <;> simp [G, Set.piecewise, hw]
    rwa [he]
  have hGglobal : Integrable G := (integrable_indicator_iff hSm).mpr
    (remark_2_4_truncated_integrable hφ 0 hδ)
  have hcircle (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : Real.circleAverage G 0 r = 0 := by
    by_cases hrδ : r < δ
    · calc
        _ = Real.circleAverage (fun _ : ℂ => (0 : ℂ)) 0 r := by
          apply Real.circleAverage_congr_sphere
          intro w hw
          have hn : ‖w‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hw
          have hwS : w ∉ S := by
            intro hs
            exact hs.2 (mem_ball_zero_iff.mpr (hn ▸ hrδ))
          exact Set.indicator_of_notMem hwS K
        _ = 0 := Real.circleAverage_const 0 0 r
    · have heq : Real.circleAverage G 0 r = Real.circleAverage K 0 r := by
        apply Real.circleAverage_congr_sphere
        intro w hw
        have hn : ‖w‖ = r := by simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hw
        have hwS : w ∈ S := ⟨mem_ball_zero_iff.mpr (hn ▸ hr1), by
          simpa [mem_ball, dist_zero_right, hn] using hrδ⟩
        exact Set.indicator_of_mem hwS K
      rw [heq]
      apply remark_2_4_circle_zero hr0
      apply hφ.1.mono
      intro w hw
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hr1)
  have hzero := disk_integral_zero_of_circleAverage_zero hGm hGglobal.integrableOn hcircle
  change (∫ w in unitDisc, S.indicator K w) = 0 at hzero
  rw [setIntegral_indicator hSm, inter_eq_right.mpr (show S ⊆ unitDisc from Set.sdiff_subset)] at hzero
  exact hzero

/-- The principal-value assertion of Remark 2.4 at z=0. -/
theorem remark_2_4_center {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc) :
    Tendsto (fun δ : ℝ => ∫ w in unitDisc \ ball (0 : ℂ) δ, conj (φ w) / (0 - w) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (remark_2_4_center_truncated_zero hφ hδ).symm

/-- The same polar cancellation criterion on an arbitrary disk. -/
theorem ball_integral_zero_of_circleAverage_zero {G : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hGm : Measurable G) (hGi : IntegrableOn G (ball c R))
    (hcircle : ∀ r : ℝ, 0 < r → r < R → Real.circleAverage G c r = 0) :
    ∫ w in ball c R, G w = 0 := by
  have hpre : (fun w : ℂ => w + c) ⁻¹' ball c R = ball 0 R := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have htr := (measurePreserving_add_right volume c).integrableOn_comp_preimage
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding |>.mpr hGi
  have hGic : IntegrableOn (fun w => G (w + c)) (ball 0 R) := by
    simpa only [hpre, Function.comp_def] using htr
  have hpolar := integrableOn_polar_of_integrableOn_ball
    (hGm.comp (measurable_id.add_const c)) hGic
  rw [setIntegral_ball_eq_polar' c hR.le hpolar]
  calc
    _ = ∫ r in (0 : ℝ)..R, (0 : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne R] with r hrne hr
      have hr' : r ∈ Ioc (0 : ℝ) R := by simpa [Set.uIoc_of_le hR.le] using hr
      have havg := hcircle r hr'.1 (lt_of_le_of_ne hr'.2 hrne)
      rw [Real.circleAverage_def] at havg
      have hint : (∫ θ in (0 : ℝ)..2 * π, G (circleMap c r θ)) = 0 :=
        (smul_eq_zero.mp havg).resolve_left (by positivity)
      rw [intervalIntegral.integral_const_mul, hint, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

/-- Exact local annulus cancellation around any pole strictly inside the disk. -/
theorem remark_2_4_local_annulus_zero {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {c : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hsub : closedBall c R ⊆ unitDisc) :
    (∫ w in ball c R \ ball c δ, conj (φ w) / (c - w) ^ 2) = 0 := by
  let S : Set ℂ := ball c R \ ball c δ
  let K : ℂ → ℂ := fun w => conj (φ w) / (c - w) ^ 2
  let G : ℂ → ℂ := S.indicator K
  have hSm : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  have hSD : S ⊆ unitDisc \ ball c δ := fun w hw => ⟨hsub (ball_subset_closedBall hw.1), hw.2⟩
  have hKc : ContinuousOn K S := by
    apply (Complex.continuous_conj.comp_continuousOn (hφ.1.continuousOn.mono
      (hSD.trans Set.sdiff_subset))).div (by fun_prop)
    intro w hw
    have hn : δ ≤ ‖c - w‖ := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hw.2
    exact pow_ne_zero 2 (norm_pos_iff.mp (hδ.trans_le hn))
  have hGm : Measurable G := by
    have hh := hKc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hSm
    have he : G = S.piecewise K (fun _ => 0) := by
      ext w
      by_cases hw : w ∈ S <;> simp [G, Set.piecewise, hw]
    rwa [he]
  have hGglobal : Integrable G := (integrable_indicator_iff hSm).mpr
    ((remark_2_4_truncated_integrable hφ c hδ).mono_set hSD)
  have hcircle (r : ℝ) (hr0 : 0 < r) (hrR : r < R) : Real.circleAverage G c r = 0 := by
    by_cases hrδ : r < δ
    · calc
        _ = Real.circleAverage (fun _ : ℂ => (0 : ℂ)) c r := by
          apply Real.circleAverage_congr_sphere
          intro w hw
          have hn : ‖w - c‖ = r := by simpa [mem_sphere, dist_eq_norm, abs_of_pos hr0] using hw
          have hwS : w ∉ S := by
            intro hs
            exact hs.2 (by simpa [mem_ball, dist_eq_norm, hn] using hrδ)
          exact Set.indicator_of_notMem hwS K
        _ = 0 := Real.circleAverage_const 0 c r
    · have heq : Real.circleAverage G c r = Real.circleAverage K c r := by
        apply Real.circleAverage_congr_sphere
        intro w hw
        have hn : ‖w - c‖ = r := by simpa [mem_sphere, dist_eq_norm, abs_of_pos hr0] using hw
        have hwS : w ∈ S := ⟨by simpa [mem_ball, dist_eq_norm, hn] using hrR,
          by simpa [mem_ball, dist_eq_norm, hn] using hrδ⟩
        exact Set.indicator_of_mem hwS K
      rw [heq]
      apply remark_2_4_circle_zero hr0
      exact hφ.1.mono ((closedBall_subset_closedBall hrR.le).trans hsub)
  have hzero := ball_integral_zero_of_circleAverage_zero hR hGm hGglobal.integrableOn hcircle
  change (∫ w in ball c R, S.indicator K w) = 0 at hzero
  rw [setIntegral_indicator hSm, inter_eq_right.mpr (show S ⊆ ball c R from Set.sdiff_subset)] at hzero
  exact hzero

/-- Once both holes lie in the disk, changing the positive hole radius leaves
the truncated integral unchanged, by exact local annulus cancellation. -/
theorem remark_2_4_truncation_stable {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {z : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hδR : δ ≤ R)
    (hsub : closedBall z R ⊆ unitDisc) :
    (∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2) =
      ∫ w in unitDisc \ ball z R, conj (φ w) / (z - w) ^ 2 := by
  have hR : 0 < R := hδ.trans_le hδR
  have hlocal := remark_2_4_local_annulus_zero hφ hδ hR hsub
  have hs : ball z R \ ball z δ ⊆ unitDisc \ ball z δ :=
    fun w hw => ⟨hsub (ball_subset_closedBall hw.1), hw.2⟩
  have hdiff : (unitDisc \ ball z δ) \ (ball z R \ ball z δ) = unitDisc \ ball z R := by
    ext w
    constructor
    · intro hw
      exact ⟨hw.1.1, fun hwr => hw.2 ⟨hwr, hw.1.2⟩⟩
    · intro hw
      exact ⟨⟨hw.1, fun hwd => hw.2 (ball_subset_ball hδR hwd)⟩, fun hwl => hw.2 hwl.1⟩
  have hsplit := setIntegral_diff (measurableSet_ball.diff measurableSet_ball)
    (remark_2_4_truncated_integrable hφ z hδ) hs
  rw [hdiff, hlocal, sub_zero] at hsplit
  exact hsplit.symm

/-- The general-center principal value exists and equals any sufficiently small
fixed truncation. Vanishing of this value is a separate step of Remark 2.4. -/
theorem remark_2_4_pv_eq_fixed_truncation {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {z : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall z R ⊆ unitDisc) :
    Tendsto (fun δ : ℝ => ∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2)
      (𝓝[>] 0) (𝓝 (∫ w in unitDisc \ ball z R, conj (φ w) / (z - w) ^ 2)) := by
  apply tendsto_const_nhds.congr'
  have hnear : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < R :=
    (gt_mem_nhds hR).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with δ hδ hδR
  exact (remark_2_4_truncation_stable hφ hδ hδR.le hsub).symm

/-- Principal-value existence at every interior point, without asserting its value. -/
theorem remark_2_4_pv_exists {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ L : ℂ, Tendsto (fun δ : ℝ => ∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hR, hsub⟩ := a21_boundary_ball_subset (Or.inl rfl) hz
  exact ⟨_, remark_2_4_pv_eq_fixed_truncation hφ hR hsub⟩

/-- Quantitative fixed-hole control used to transfer approximations in Remark 2.4. -/
theorem remark_2_4_truncated_norm_le {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2‖ ≤
      (δ ^ 2)⁻¹ * ∫ w in unitDisc, ‖φ w‖ := by
  have hmeas : MeasurableSet (unitDisc \ ball z δ) := measurableSet_ball.diff measurableSet_ball
  have hi := remark_2_4_truncated_integrable hφ z hδ
  have hiφ : IntegrableOn (fun w => ‖φ w‖) unitDisc := (a21_disk_integrable hφ).norm
  have hlocal := hiφ.mono_set (show unitDisc \ ball z δ ⊆ unitDisc from Set.sdiff_subset)
  have hbound : (∫ w in unitDisc \ ball z δ, ‖conj (φ w) / (z - w) ^ 2‖) ≤
      ∫ w in unitDisc \ ball z δ, (δ ^ 2)⁻¹ * ‖φ w‖ := by
    apply integral_mono_ae hi.norm (hlocal.const_mul (δ ^ 2)⁻¹)
    filter_upwards [ae_restrict_mem hmeas] with w hw
    have hn : δ ≤ ‖z - w‖ := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hw.2
    rw [norm_div, norm_pow, norm_conj, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ)
      (pow_le_pow_left₀ hδ.le hn 2)
  have hmass := setIntegral_mono_set hiφ (Eventually.of_forall fun w => norm_nonneg (φ w))
    (Eventually.of_forall (show unitDisc \ ball z δ ⊆ unitDisc from Set.sdiff_subset))
  rw [integral_const_mul] at hbound
  exact (norm_integral_le_integral_norm _).trans (hbound.trans
    (mul_le_mul_of_nonneg_left hmass (by positivity)))

/-- The outer Green boundary integral vanishes even when its pole is off-center. -/
theorem remark_2_4_outer_boundary_zero {φ : ℂ → ℂ} {z : ℂ} {R : ℝ}
    (hzR : ‖z‖ < R) (hφ : DifferentiableOn ℂ φ (closedBall 0 R)) :
    (∫ θ in (0 : ℝ)..2 * π, conj (φ (circleMap 0 R θ)) / (circleMap 0 R θ - z) *
      conj (deriv (circleMap 0 R) θ)) = 0 := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hzR
  have hden (w : ℂ) (hw : w ∈ closedBall 0 R) : (R : ℂ) ^ 2 - conj z * w ≠ 0 := by
    have hwR : ‖w‖ ≤ R := mem_closedBall_zero_iff.mp hw
    have hlt : ‖conj z * w‖ < ‖(R : ℂ) ^ 2‖ := by
      rw [norm_mul, norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith [mul_le_mul_of_nonneg_left hwR (norm_nonneg z)]
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    linarith
  let Q : ℂ → ℂ := fun w => w ^ 2 * φ w / ((R : ℂ) ^ 2 - conj z * w)
  have hQ : DifferentiableOn ℂ Q (closedBall 0 R) :=
    ((differentiableOn_id.pow 2).mul hφ).div (by fun_prop) hden
  have hQC : DiffContOnCl ℂ Q (ball 0 |R|) := by
    rw [abs_of_pos hR]
    refine ⟨hQ.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball 0 hR.ne']
    exact hQ.continuousOn
  have hmean : Real.circleAverage Q 0 R = 0 := by simpa [Q] using hQC.circleAverage
  have hconj : Real.circleAverage (fun w => conj (Q w)) 0 R = 0 := by
    have hh := Complex.conjCLE.toContinuousLinearMap.circleAverage_comp_comm
      (hQ.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR.le)
    simpa [Function.comp_def, hmean] using hh
  rw [Real.circleAverage_def] at hconj
  have hint : (∫ θ in (0 : ℝ)..2 * π, conj (Q (circleMap 0 R θ))) = 0 :=
    (smul_eq_zero.mp hconj).resolve_left (by positivity)
  have heq (θ : ℝ) : conj (φ (circleMap 0 R θ)) / (circleMap 0 R θ - z) *
      conj (deriv (circleMap 0 R) θ) = -I * conj (Q (circleMap 0 R θ)) := by
    let w := circleMap 0 R θ
    have hwN : ‖w‖ = R := by simp [w, norm_circleMap_zero, abs_of_pos hR]
    have hw : w ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr hwN.le
    have hwz : w - z ≠ 0 := by
      intro he
      have := congrArg norm (sub_eq_zero.mp he)
      linarith
    have hmul : w * conj w = (R : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwN]
      norm_cast
    have hd := hden w hw
    have hdc : (R : ℂ) ^ 2 - z * conj w ≠ 0 := by
      intro he
      apply hd
      have hh := congrArg (starRingEnd ℂ) he
      simpa using hh
    rw [deriv_circleMap]
    change conj (φ w) / (w - z) * conj (w * I) = -I * conj (Q w)
    simp only [Q, map_div₀, map_mul, map_sub, map_pow, conj_ofReal, conj_conj, conj_I]
    field_simp
    linear_combination conj (φ w) * conj w * hmul
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, hint, mul_zero]

/-- The inner Green boundary term is zero, using the proved circle cancellation. -/
theorem remark_2_4_inner_boundary_zero {φ : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (closedBall z r)) :
    (∫ θ in (0 : ℝ)..2 * π, conj (φ (circleMap z r θ)) / (circleMap z r θ - z) *
      conj (deriv (circleMap z r) θ)) = 0 := by
  have hmean := remark_2_4_circle_zero hr hφ
  rw [Real.circleAverage_def] at hmean
  have hint : (∫ θ in (0 : ℝ)..2 * π, conj (φ (circleMap z r θ)) /
      (z - circleMap z r θ) ^ 2) = 0 := (smul_eq_zero.mp hmean).resolve_left (by positivity)
  have heq (θ : ℝ) : conj (φ (circleMap z r θ)) / (circleMap z r θ - z) *
      conj (deriv (circleMap z r) θ) = (-I * (r : ℂ) ^ 2) *
        (conj (φ (circleMap z r θ)) / (z - circleMap z r θ) ^ 2) := by
    let w := circleMap z r θ
    have hn : ‖w - z‖ = r := by simp [w, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    have hwz : w - z ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
    have hmul : (w - z) * conj (w - z) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_cast
    rw [deriv_circleMap, show circleMap 0 r θ = w - z by simp [w, circleMap_sub_center]]
    change conj (φ w) / (w - z) * conj ((w - z) * I) = _
    rw [show z - circleMap z r θ = -(w - z) by dsimp [w]; ring, neg_sq]
    rw [map_mul, conj_I]
    field_simp
    linear_combination -conj (φ w) * hmul
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, hint, mul_zero]

/-- Green's formula on an eccentric punctured disk: both boundary integrals vanish. -/
theorem remark_2_4_inner_disk_zero {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {z : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hfit : ‖z‖ + δ < R) (hR1 : R < 1) :
    (∫ w in ball (0 : ℂ) R \ ball z δ, conj (φ w) / (z - w) ^ 2) = 0 := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hzR : ‖z‖ < R := by linarith
  have houterSub : closedBall (0 : ℂ) R ⊆ unitDisc := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hR1)
  have hinnerSub : closedBall z δ ⊆ ball (0 : ℂ) R := by
    intro w hw
    have hn := norm_add_le (w - z) z
    rw [sub_add_cancel] at hn
    have hd : ‖w - z‖ ≤ δ := by simpa [mem_closedBall, dist_eq_norm] using hw
    apply mem_ball_zero_iff.mpr
    linarith
  obtain ⟨χ, _, _, hχ1, hkernel⟩ := exists_kernel_cutoff z hδ
  let u : ℂ → ℂ := fun w => (χ w * (w - z)⁻¹) * conj (φ w)
  have hφC : ContDiffOn ℝ 1 φ unitDisc :=
    (hφ.contDiffOn (show IsOpen unitDisc from isOpen_ball)).restrict_scalars ℝ
  have huC : ContDiffOn ℝ 1 u unitDisc := hkernel.contDiffOn.mul
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφC)
  have hUouter := green_disc_dz_closedBall hR (huC.mono houterSub)
  have hUinner := green_disc_dz_closedBall hδ
    (huC.mono (hinnerSub.trans (ball_subset_closedBall.trans houterSub)))
  have huc (w : ℂ) (hw : δ ≤ ‖w - z‖) : u w = conj (φ w) / (w - z) := by
    dsimp [u]
    rw [hχ1 w hw, one_mul]
    ring
  have hout (θ : ℝ) : u (circleMap 0 R θ) = conj (φ (circleMap 0 R θ)) / (circleMap 0 R θ - z) := by
    apply huc
    have hn := norm_add_le (circleMap 0 R θ - z) z
    rw [sub_add_cancel, norm_circleMap_zero, abs_of_pos hR] at hn
    linarith
  have hin (θ : ℝ) : u (circleMap z δ θ) = conj (φ (circleMap z δ θ)) / (circleMap z δ θ - z) := by
    apply huc
    simp [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]
  simp only [hout] at hUouter
  rw [remark_2_4_outer_boundary_zero hzR (hφ.mono houterSub)] at hUouter
  simp only [hin] at hUinner
  rw [remark_2_4_inner_boundary_zero hδ
    (hφ.mono (hinnerSub.trans (ball_subset_closedBall.trans houterSub)))] at hUinner
  have hcoef : (-2 * I : ℂ) ≠ 0 := by simp
  have hio : (∫ w in ball (0 : ℂ) R, dz u w) = 0 :=
    (mul_eq_zero.mp hUouter.symm).resolve_left hcoef
  have hii : (∫ w in ball z δ, dz u w) = 0 :=
    (mul_eq_zero.mp hUinner.symm).resolve_left hcoef
  have hidz : IntegrableOn (dz u) (ball (0 : ℂ) R) :=
    (((continuousOn_dz_dzbar huC (show IsOpen unitDisc from isOpen_ball)).1.mono houterSub).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) R)).mono_set ball_subset_closedBall
  have hdiff : (∫ w in ball (0 : ℂ) R \ ball z δ, dz u w) = 0 := by
    rw [setIntegral_sdiff measurableSet_ball hidz (ball_subset_closedBall.trans hinnerSub), hio, hii, sub_self]
  have hcongr : (∫ w in ball (0 : ℂ) R \ ball z δ, dz u w) =
      -(∫ w in ball (0 : ℂ) R \ ball z δ, conj (φ w) / (z - w) ^ 2) := by
    rw [← integral_neg]
    apply setIntegral_congr_ae (measurableSet_ball.diff measurableSet_ball)
    have hs : ∀ᵐ w : ℂ, w ∉ sphere z δ := by
      rw [ae_iff]
      exact measure_mono_null (fun w hw => not_not.mp hw) (Measure.addHaar_sphere volume z δ)
    filter_upwards [hs] with w hws hw
    have hwD := houterSub (ball_subset_closedBall hw.1)
    have hge : δ ≤ ‖w - z‖ := by simpa [mem_ball, dist_eq_norm] using hw.2
    have hgt : δ < ‖w - z‖ := lt_of_le_of_ne hge (fun he => hws (by
      rw [mem_sphere, dist_eq_norm]
      exact he.symm))
    have hwz : w ≠ z := by intro he; simp [he] at hgt; linarith
    have hev : u =ᶠ[𝓝 w] (fun v => (v - z)⁻¹ * conj (φ v)) := by
      have ho : IsOpen {v : ℂ | δ < ‖v - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [ho.mem_nhds hgt] with v hv
      dsimp [u]
      rw [hχ1 v hv.le, one_mul]
    have hφat := hφ.differentiableAt ((show IsOpen unitDisc from isOpen_ball).mem_nhds hwD)
    have hφreal := hφat.restrictScalars ℝ
    rw [show dz u w = dz (fun v => (v - z)⁻¹ * conj (φ v)) w by simp only [dz, hev.fderiv_eq],
      dz_mul (differentiableAt_inv_sub hwz) (differentiableAt_conj hφreal), dz_inv_sub hwz,
      dz_conj hφreal, (cauchyRiemann_iff.mp hφat).2, map_zero]
    rw [show z - w = -(w - z) by ring, neg_sq]
    ring
  exact neg_eq_zero.mp (hcongr.symm.trans hdiff)

/-- Fixed-hole cancellation on the full unit disk, by integrable exhaustion in
the outer radius. The positive hole keeps the singular kernel L1-dominated. -/
theorem remark_2_4_truncated_zero {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc)
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hfit : ‖z‖ + δ < 1) :
    (∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2) = 0 := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  let S : ℕ → Set ℂ := fun n => ball 0 (r n) \ ball z δ
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hrmono : Monotone r := by
    intro m n hmn
    dsimp [r]
    apply sub_le_sub_left
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hrlim : Tendsto r atTop (𝓝 1) := by
    simpa only [r, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hUnion : unitDisc \ ball z δ = ⋃ n, S n := by
    ext w
    constructor
    · intro hw
      have he := hrlim.eventually (lt_mem_nhds (mem_ball_zero_iff.mp hw.1))
      obtain ⟨n, hn⟩ := he.exists
      exact mem_iUnion.mpr ⟨n, mem_ball_zero_iff.mpr hn, hw.2⟩
    · intro hw
      obtain ⟨n, hn⟩ := mem_iUnion.mp hw
      exact ⟨(ball_subset_ball (hr1 n).le) hn.1, hn.2⟩
  have hSm : ∀ n, MeasurableSet (S n) := fun _ => measurableSet_ball.diff measurableSet_ball
  have hSmono : Monotone S := by
    intro m n hmn
    exact Set.sdiff_subset_sdiff_left (ball_subset_ball (hrmono hmn))
  have hi : IntegrableOn (fun w => conj (φ w) / (z - w) ^ 2) (⋃ n, S n) := by
    rw [← hUnion]
    exact remark_2_4_truncated_integrable hφ z hδ
  have hlim := tendsto_setIntegral_of_monotone hSm hSmono hi
  rw [← hUnion] at hlim
  have hzero : Tendsto (fun n => ∫ w in S n, conj (φ w) / (z - w) ^ 2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hrlim.eventually (lt_mem_nhds hfit)] with n hn
    exact (remark_2_4_inner_disk_zero hφ.1 hδ hn (hr1 n)).symm
  exact tendsto_nhds_unique hlim hzero

/-- **Remark 2.4** (TT:3982–3986). For `φ` holomorphic on `𝔻` (and `∬_𝔻 |φ|² < ∞`), `∬_𝔻 \overline{φ(w)}/(z - w)² d²w = 0`
in the principal value sense, `z ∈ 𝔻`. -/
theorem remark_2_4 {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun δ : ℝ => ∫ w in unitDisc \ ball z δ, conj (φ w) / (z - w) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hR, hsub⟩ := a21_boundary_ball_subset (Or.inl rfl) hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfit : ‖z‖ + |‖z‖ - 1| / 2 < 1 := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hzero := remark_2_4_truncated_zero hφ hR hfit
  simpa only [hzero] using remark_2_4_pv_eq_fixed_truncation hφ hR hsub

/-- The kernel `𝖪_l(z, w) = ∬ K_l(z, u) \overline{K_l(w, u)} d²u` of `𝖪_l = K_l K_l*`, for `l = 1` (on `𝔻`). -/
def kerKK1 (f : ℂ → ℂ) (z w : ℂ) : ℂ := ∫ u in unitDisc, kerK1 f z u * conj (kerK1 f w u)
/-- `𝖪₂(z, w)` (on `𝔻`; the `u`-integral over `𝔻*`). -/
def kerKK2 (f g : ℂ → ℂ) (z w : ℂ) : ℂ := ∫ u in unitDiscExterior, kerK2 f g z u * conj (kerK2 f g w u)
/-- `𝖪₃(z, w)` (on `𝔻*`; the `u`-integral over `𝔻`). -/
def kerKK3 (f g : ℂ → ℂ) (z w : ℂ) : ℂ := ∫ u in unitDisc, kerK3 f g z u * conj (kerK3 f g w u)
/-- `𝖪₄(z, w)` (on `𝔻*`). -/
def kerKK4 (g : ℂ → ℂ) (z w : ℂ) : ℂ := ∫ u in unitDiscExterior, kerK4 g z u * conj (kerK4 g w u)

-- `eq_2_4` moved to `Ch2/S2_Completed6.lean` (2026-10-26).

-- `lemma_2_5` moved to `Ch2/S2_Completed.lean` (2026-10-26).

-- `thm_2_6` moved to `Ch2/S2_Thm26.lean` (2026-10-27).

-- `eq_2_8` moved to `Ch2/S2_Completed5.lean` (2026-10-26).

-- `remark_2_8` moved to `Ch2/S2_Remark28.lean` (2026-10-27).

-- `lemma_2_7` moved to `Ch2/S2_Lemma27.lean` (2026-10-27).

-- `eq_2_9` moved to `Ch2/S2_Completed4.lean` (2026-10-26).

-- `cor_2_9` moved to `Ch2/S2_Cor29.lean` (2026-10-27).

/-- The map `𝒫 : T₀(1) → 𝒮₂`, `[μ] ↦ B₁(𝖿^μ)` (TT:4199), as a matrix. -/
def periodP (p : T1) : ℕ → ℕ → ℂ :=
  B1 (grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)))

-- `periodP_injective` moved to `Ch2/S2_Completed2.lean` (2026-10-26).

-- `thm_2_10` moved to `Ch2/S2Thm210.lean` (2026-10-28).

/-! ## §2.2 Fredholm eigenvalues and Fredholm determinant -/

/-- `ℓ²`. -/
abbrev ell2 : Type := lp (fun _ : ℕ => ℂ) 2

/-- The transpose `Tᵗ = J T* J` with respect to the standard conjugation `J = star` of `ℓ²` (TT:4287, (2.3)). -/
def transposeOp (T : ell2 →L[ℂ] ell2) (x : ell2) : ell2 := star (ContinuousLinearMap.adjoint T (star x))

-- `lemma_2_12` moved to `Ch2/S2_Completed3.lean` (2026-10-26).

/-- **Corollary 2.13** (TT:4374). In Lemma 2.12, the nonzero entries `d_n` are singular values of `T`: `d_n²` is an
eigenvalue of `T T*`. -/
theorem cor_2_13 {T U D : ell2 →L[ℂ] ell2} {d : ℕ → ℝ} (hU : U ∈ unitary (ell2 →L[ℂ] ell2))
    (hD : ∀ x n, D x n = d n * x n) (hT : ∀ x, T x = U (D (transposeOp U x))) {n : ℕ} (hn : d n ≠ 0) :
    ∃ x : ell2, x ≠ 0 ∧ T (ContinuousLinearMap.adjoint T x) = ((d n ^ 2 : ℝ) : ℂ) • x := by
  let e : ell2 := lp.single 2 n 1
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun x : ell2 => x n) h
    simp [e] at this
  have heStar : star e = e := by
    ext k
    by_cases hk : k = n
    · subst k; simp [e, lp.star_apply]
    · simp [e, lp.star_apply, lp.single_apply, hk]
  have hUU (x : ell2) : ContinuousLinearMap.adjoint U (U x) = x := by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A x)
      (Unitary.star_mul_self_of_mem hU)
    simpa [ContinuousLinearMap.star_eq_adjoint] using h
  have hDe : D e = (d n : ℂ) • e := by
    ext k
    rw [hD]
    change (d k : ℂ) * e k = (d n : ℂ) * e k
    by_cases hk : k = n
    · subst k; simp [e]
    · simp [e, lp.single_apply, hk]
  have hconj (x y : ell2) : inner ℂ x (star y) = inner ℂ y (star x) := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro k
    simp [lp.star_apply, RCLike.inner_apply, mul_comm]
  have hAdj : ContinuousLinearMap.adjoint T (U e) = (d n : ℂ) • star (U e) := by
    apply ext_inner_left ℂ
    intro y
    calc
      inner ℂ y (ContinuousLinearMap.adjoint T (U e)) = inner ℂ (T y) (U e) :=
        ContinuousLinearMap.adjoint_inner_right T y (U e)
      _ = inner ℂ (D (transposeOp U y)) e := by
        rw [hT, ContinuousLinearMap.inner_map_map_of_mem_unitary hU]
      _ = (d n : ℂ) * (ContinuousLinearMap.adjoint U (star y)) n := by
        rw [lp.inner_single_right]
        simp [hD, transposeOp, lp.star_apply, RCLike.inner_apply]
      _ = (d n : ℂ) * inner ℂ e (ContinuousLinearMap.adjoint U (star y)) := by
        rw [lp.inner_single_left]
        simp [RCLike.inner_apply]
      _ = (d n : ℂ) * inner ℂ (U e) (star y) := by
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ y ((d n : ℂ) • star (U e)) := by
        rw [inner_smul_right, hconj]
  have hTstar : T (star (U e)) = (d n : ℂ) • U e := by
    rw [hT]
    simp only [transposeOp, star_star, hUU, heStar, hDe, map_smul]
  refine ⟨U e, ?_, ?_⟩
  · intro h
    apply he
    simpa [h] using (hUU e).symm
  · rw [hAdj, map_smul, hTstar, smul_smul]
    simp only [pow_two, Complex.ofReal_mul]

/-- A singular value sequence of `B₁`: `λ_n ≥ 0` with an orthonormal basis `(u_n)` of `ℓ²` (columns of a unitary `U`)
such that `B₁B₁* u_n = λ_n² u_n` entrywise. -/
def IsSingularSeq (A : ℕ → ℕ → ℂ) (lam : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ lam n) ∧ ∃ U : ℕ → ℕ → ℂ, (∀ m n, mulAdj U U m n = kron m n) ∧
    (∀ m n, (∑' k, conj (U k m) * U k n) = kron m n) ∧
    ∀ m n, (∑' k, mulAdj A A m k * U k n) = ((lam n ^ 2 : ℝ) : ℂ) * U m n

-- `eq_2_12` moved to `Ch2/S2_Eq212.lean` (2026-10-27).

/-- The Fredholm determinant `Det_F(𝒞) = ∏ ρ_n² = ∏ (1 - λ_n²) = det(I - 𝖪₁)` of the quasicircle `𝒞 = 𝖿^μ(S¹)`
(TT:4478–4481), over a chosen singular value sequence of `B₁` (junk `1` if none). -/
def detF (μ : LinfStar) : ℝ :=
  let A := B1 (grunsky (fsans μ) (gsans μ))
  if h : ∃ lam, IsSingularSeq A lam then ∏' n, (1 - h.choose n ^ 2) else 1

-- `detF_spec` moved to `Ch2/S2_DetF.lean` (2026-10-27).

/-- **Definition 2.15** (TT:4486–4490). `S₂([μ]) = log Det_F(𝖿^μ(S¹))` on `T₀(1)`. -/
def liouvilleS2 (p : T1) : ℝ := Real.log (detF (Quotient.out p : LinfStarBall))

-- `eq_2_13` moved to `Ch2/S2_DetF.lean` (2026-10-27).

/-! ## §2.3 Period matrix of 1-forms -/

/-- The generalized Faber polynomials (TT:4506–4524), characterized by:
- `log((g(z) - w)/(b z)) = -Σ_{n ≥ 1} P_n(w)/n · z^{-n}`;
- `log((w - f(z))/w) = log(f(z)/z) - Σ_{n ≥ 1} Q_n(w)/n · zⁿ`;
- `P_n` is a polynomial of degree `n` in `w`, `Q_n` a polynomial of degree `n` in `1/w`.

The defining relations are written with exponentials and the Grunsky expansions they imply (TT:4535):
`P_n(g(z)) = zⁿ + n Σ_{m ≥ 1} b_{nm} z^{-m}` and `Q_n(f(z)) = z^{-n} + n Σ_{m ≥ 1} b_{-n,-m} z^m`. -/
def IsFaber (f g : ℂ → ℂ) (P Q : ℕ → Polynomial ℂ) : Prop :=
  (∀ n, (P (n + 1)).natDegree = n + 1 ∧ (Q (n + 1)).natDegree = n + 1) ∧
    (∀ n, ∀ z ∈ unitDiscExterior, HasSum (fun m : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) (m + 1) * z ^ (-(m + 1 : ℤ)))
      ((P (n + 1)).eval (g z) - z ^ (n + 1))) ∧
    ∀ n, ∀ z ∈ unitDisc, z ≠ 0 → HasSum (fun m : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (-(n + 1 : ℤ)) (-(m + 1 : ℤ)) * z ^ (m + 1))
      ((Q (n + 1)).eval (f z)⁻¹ - z ^ (-(n + 1 : ℤ)))



end Ch2

end TakhtajanTeo
