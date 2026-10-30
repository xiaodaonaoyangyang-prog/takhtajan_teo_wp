import TakhtajanTeo.Ch1.L613

/-!
# (1.24)–(1.25) at general `ε` (`e124_`, 下属3) — DRAFT interface

Host: new module `Ch1/Eq124General.lean`. It imports `Ch1/WRegFoundation` (W-REG, frozen `WR_INTERFACE` 547f19d7:
`wr_joint_contDiff_U` (E2), `wr_jacobian_pos_U` (E3)). `e124_eq_1_24` and `e124_eq_1_25` are byte-identical copies of
the ORIGINAL `eq_1_24` and `eq_1_25` (S1_5, unchanged).

Notation in the stubs: `f = w_{εμ}` (hypothesis `hf`), `κ = μ_f(z)`, `m(v) = μ(v) f_v(v)²`,
`ẇ(y) = ∂_ε w_{εμ}(y)`, given by `eq_1_21` as `-(1/π) ∬_𝕌 R(f y, f v) m(v)`, and
`R₁(ζ, η) = ∂_ζ R(ζ, η) = 1/(η - ζ)² + 1/η - 1/(η - 1)`.

Route (the `∂_ε` parts; the `∂_ε̄` parts carry no principal value at `v = z`):
1. `e124_mixed`: `∂_ε (f_z)(y) = ∂_y ẇ(y)`, by symmetry of second derivatives (W-REG E2: `C³` jointly).
2. `e124_K_dz`, `e124_K_dzbar`, `e124_Kbar_dz`, `e124_Kbar_dzbar`: the Wirtinger quotient rule for
   `K = f_z(z) f_z(u)/(f z - f u)²` (resp. `K(z, ū)`), with `∂_ε f = ẇ` (`eq_1_21`) and step 1.
3. `∂_z ẇ(z)` is a principal value in the **v-plane** with no extra term. This is the cancellation of two local
   terms of the same value `μ(z) f_z(z) κ̄/(1 - |κ|²)`:
   * `e124_chain`: `ẇ = G ∘ f` with `G(ζ) = -(1/π) ∬ R(ζ, f v) m(v)`, whose `∂_ζ̄ G = m ∘ f⁻¹ / J_f ∘ f⁻¹` (Cauchy
     transform). The chain rule `(G ∘ f)_z = G_ζ f_z + G_ζ̄ \overline{f_z̄}` gives the image-plane principal
     value plus the term `μ(z) f_z(z) κ̄/(1 - |κ|²)`.
   * `e124_shape`: excising `f⁻¹(B(f z, δ))` (≈ an ellipse) instead of `B(z, δ)` changes the principal value of
     the `α²/(αh + βh̄)²` singularity by `π κ̄/(1 - |κ|²)`, and `e124_pv_convert` turns this into
     `PV_v = PV_image - π μ(z) f_z(z) κ̄/(1 - |κ|²)`.
   * `e124_dz_wdot`: the two cancel.
4. `e124_dz_wdotbar`: `∂_z ∂_ε̄ w(z)` by differentiating under the integral (the kernel `R(ζ, \overline{f v})`
   is regular for `ζ ∈ 𝕌`).
5. Assembly: partial fractions of `1/((η - a)²(η - b)²)`, the `1/η - 1/(η - 1)` terms cancel, and the
   one-point principal values combine into `pv2` (a one-point PV at `z` plus a function integrable near `u`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### The local cancellation -/

/-- `∫_{-π}^{π} e^{imθ} dθ = 2π [m = 0]`. -/
theorem e124s_int_exp (m : ℤ) :
    (∫ θ in (-π)..π, Complex.exp ((m : ℂ) * (θ : ℂ) * I)) = if m = 0 then 2 * π else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [Complex.real_smul]
    try ring
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]
    have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hm) I_ne_zero
    have h := integral_exp_mul_complex (a := -π) (b := π) hc
    have heq : (fun θ : ℝ => Complex.exp ((m : ℂ) * (θ : ℂ) * I)) = fun θ : ℝ => Complex.exp ((m : ℂ) * I * θ) := by
      funext θ
      ring_nf
    rw [heq, h]
    have hper : Complex.exp ((m : ℂ) * I * (π : ℂ)) = Complex.exp ((m : ℂ) * I * ((-π : ℝ) : ℂ)) := by
      have h2 : (m : ℂ) * I * (π : ℂ) = (m : ℂ) * I * ((-π : ℝ) : ℂ) + (m : ℂ) * (2 * π * I) := by
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]
    simp

/-- **Fourier coefficient.** `∫_{-π}^{π} e^{-2iθ} log|1 - κ e^{-2iθ}| dθ = -π κ̄` for `|κ| < 1`. -/
theorem e124s_fourier {κ : ℂ} (hκ : ‖κ‖ < 1) :
    (∫ θ in (-π)..π, Complex.exp (-2 * (θ : ℂ) * I) *
        (Real.log ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ : ℂ)) = -(π * conj κ) := by
  set E : ℝ → ℂ := fun θ => Complex.exp (-2 * (θ : ℂ) * I) with hEd
  have hEn : ∀ θ : ℝ, ‖E θ‖ = 1 := by
    intro θ
    rw [hEd]
    dsimp only
    rw [Complex.norm_exp]
    simp
  have hEc : ∀ θ : ℝ, conj (E θ) = Complex.exp (2 * (θ : ℂ) * I) := by
    intro θ
    rw [hEd]
    dsimp only
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hxn : ∀ θ : ℝ, ‖κ * E θ‖ < 1 := by
    intro θ
    rw [norm_mul, hEn, mul_one]
    exact hκ
  -- the terms
  set F : ℕ → ℝ → ℂ := fun n θ =>
    E θ * (-(1 / 2 : ℂ) * ((κ * E θ) ^ n / n + conj ((κ * E θ) ^ n / n))) with hFd
  have hlim : ∀ θ : ℝ, HasSum (fun n => F n θ) (E θ * (Real.log ‖1 - κ * E θ‖ : ℂ)) := by
    intro θ
    have h1 := hasSum_taylorSeries_neg_log (hxn θ)
    have h2 := (h1.add (Complex.hasSum_conj'.mpr h1)).mul_left (E θ * (-(1 / 2 : ℂ)))
    have hre : (Real.log ‖1 - κ * E θ‖ : ℂ) = -(1 / 2 : ℂ) * (-Complex.log (1 - κ * E θ) +
        conj (-Complex.log (1 - κ * E θ))) := by
      rw [← Complex.log_re]
      apply Complex.ext <;> simp <;> ring
    rw [hre]
    convert h2 using 1
    · funext n
      rw [hFd]
      dsimp only
      ring
    · ring
  have hbound : ∀ n θ, ‖F n θ‖ ≤ ‖κ‖ ^ n := by
    intro n θ
    rw [hFd]
    dsimp only
    rw [norm_mul, hEn, one_mul, norm_mul]
    have h1 : ‖(κ * E θ) ^ n / n‖ ≤ ‖κ‖ ^ n := by
      rw [norm_div, norm_pow, norm_mul, hEn, mul_one]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · apply div_le_self (by positivity)
        rw [Complex.norm_natCast]
        exact_mod_cast hn
    calc ‖-(1 / 2 : ℂ)‖ * ‖(κ * E θ) ^ n / n + conj ((κ * E θ) ^ n / n)‖
        ≤ (1 / 2) * (‖(κ * E θ) ^ n / n‖ + ‖conj ((κ * E θ) ^ n / n)‖) := by
          gcongr
          · simp
          · exact norm_add_le _ _
      _ ≤ (1 / 2) * (‖κ‖ ^ n + ‖κ‖ ^ n) := by
          rw [Complex.norm_conj]
          gcongr
      _ = ‖κ‖ ^ n := by ring
  have hEcont : Continuous E := by
    rw [hEd]
    fun_prop
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    rw [hFd]
    dsimp only
    fun_prop
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (fun n _ => ‖κ‖ ^ n) (fun n => (hFcont n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun θ _ => hbound n θ)
    (Eventually.of_forall fun _ _ => summable_geometric_of_lt_one (norm_nonneg _) hκ)
    intervalIntegrable_const (Eventually.of_forall fun θ _ => hlim θ)
  -- each term
  have hterm : ∀ n, (∫ θ in (-π)..π, F n θ) = if n = 1 then -(π * conj κ) else 0 := by
    intro n
    have hF : F n = fun θ : ℝ => -(1 / 2 : ℂ) * (κ ^ n / n) * Complex.exp (((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) * (θ : ℂ) * I) +
        -(1 / 2 : ℂ) * (conj κ ^ n / n) * Complex.exp (((2 * ((n : ℤ) - 1) : ℤ) : ℂ) * (θ : ℂ) * I) := by
      funext θ
      rw [hFd]
      dsimp only
      rw [map_div₀, map_pow, map_mul, hEc, map_natCast, mul_pow, mul_pow]
      rw [hEd]
      dsimp only
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      have k1 : Complex.exp (-2 * (θ : ℂ) * I) * Complex.exp ((n : ℂ) * (-2 * (θ : ℂ) * I)) =
          Complex.exp (((-2 * ((n : ℤ) + 1) : ℤ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have k2 : Complex.exp (-2 * (θ : ℂ) * I) * Complex.exp ((n : ℂ) * (2 * (θ : ℂ) * I)) =
          Complex.exp (((2 * ((n : ℤ) - 1) : ℤ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← k1, ← k2]
      ring
    rw [hF, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      e124s_int_exp, e124s_int_exp]
    · have h1 : ((-2 * ((n : ℤ) + 1) : ℤ)) ≠ 0 := by omega
      simp only [h1, if_false, Complex.ofReal_zero, mul_zero, zero_add]
      by_cases hn : n = 1
      · subst hn
        norm_num
        try ring
      · have h2 : ((2 * ((n : ℤ) - 1) : ℤ)) ≠ 0 := by omega
        simp only [h2, hn, if_false, Complex.ofReal_zero, mul_zero]
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hsum' : HasSum (fun n => ∫ θ in (-π)..π, F n θ) (-(π * conj κ)) := by
    rw [show (fun n => ∫ θ in (-π)..π, F n θ) = fun n => if n = 1 then -(π * conj κ) else 0 from
      funext hterm]
    exact hasSum_ite_eq 1 _
  exact hsum.unique hsum'

/-- `∫_{r > 0} 1_{[a, b)}(r) r⁻¹ dr = [a ≤ b] log(b/a)` for `a, b > 0`. -/
theorem e124s_radial_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ r in Ioi (0 : ℝ), (Ico a b).indicator (fun r : ℝ => r⁻¹) r) = if a ≤ b then Real.log (b / a) else 0 := by
  rw [setIntegral_indicator measurableSet_Ico]
  have hs : Ioi (0 : ℝ) ∩ Ico a b = Ico a b := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Ico]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le ha h.1, h⟩
  rw [hs]
  by_cases hab : a ≤ b
  · rw [if_pos hab, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb]
  · rw [if_neg hab, Ico_eq_empty (not_lt.mpr (le_of_lt (not_le.mp hab))), Measure.restrict_empty, integral_zero_measure]

/-- The radial integral of the signed region between the circle `r = 1` and the curve `r = 1/q`. -/
theorem e124s_radial {q : ℝ} (hq : 0 < q) :
    (∫ r in Ioi (0 : ℝ), (Ico (1 / q) 1).indicator (fun r : ℝ => r⁻¹) r) -
        (∫ r in Ioi (0 : ℝ), (Ico 1 (1 / q)).indicator (fun r : ℝ => r⁻¹) r) = Real.log q := by
  have hq' : 0 < 1 / q := by positivity
  rw [e124s_radial_one hq' one_pos, e124s_radial_one one_pos hq']
  have e1 : (1 : ℝ) / (1 / q) = q := by field_simp
  have e2 : (1 / q) / (1 : ℝ) = q⁻¹ := by field_simp
  rw [e1, e2, Real.log_inv]
  by_cases h1 : 1 / q ≤ 1
  · rw [if_pos h1]
    by_cases h2 : (1 : ℝ) ≤ 1 / q
    · have : q = 1 := by
        have h3 : 1 / q = 1 := le_antisymm h1 h2
        field_simp at h3
        linarith
      rw [if_pos h2, this, Real.log_one]
      ring
    · rw [if_neg h2, sub_zero]
  · rw [if_neg h1, if_pos (le_of_lt (not_le.mp h1)), zero_sub, neg_neg]

/-- On a polar point `η = r e^{iθ}`, `‖L⁻¹ η‖ = r q(θ)` with `q(θ) = |1 - κ e^{-2iθ}|/(1 - |κ|²)`. -/
theorem e124s_inv_norm {κ : ℂ} (hκ : ‖κ‖ < 1) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖((r : ℂ) * Complex.exp ((θ : ℂ) * I) - κ * conj ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) /
        ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ)‖ =
      r * (‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2)) := by
  have hd : (0 : ℝ) < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hc : conj ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) = (r : ℂ) * Complex.exp (-(θ : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp
  have hfac : (r : ℂ) * Complex.exp ((θ : ℂ) * I) - κ * ((r : ℂ) * Complex.exp (-(θ : ℂ) * I)) =
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) * (1 - κ * Complex.exp (-2 * (θ : ℂ) * I)) := by
    have : Complex.exp (-(θ : ℂ) * I) = Complex.exp ((θ : ℂ) * I) * Complex.exp (-2 * (θ : ℂ) * I) := by
      rw [← Complex.exp_add]
      ring_nf
    rw [this]
    ring
  rw [hc, hfac, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  ring

/-- Bounds for `q(θ) = |1 - κ e^{-2iθ}|/(1 - |κ|²)`: `1/(1 + |κ|) ≤ q ≤ 1/(1 - |κ|)`. -/
theorem e124s_q_bounds {κ : ℂ} (hκ : ‖κ‖ < 1) (θ : ℝ) :
    1 / (1 + ‖κ‖) ≤ ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2) ∧
      ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2) ≤ 1 / (1 - ‖κ‖) := by
  have hk0 := norm_nonneg κ
  have hd : (0 : ℝ) < 1 - ‖κ‖ ^ 2 := by nlinarith
  have hE : ‖κ * Complex.exp (-2 * (θ : ℂ) * I)‖ = ‖κ‖ := by
    rw [norm_mul, show (-2 * (θ : ℂ) * I) = ((-2 * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have h1 : 1 - ‖κ‖ ≤ ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (κ * Complex.exp (-2 * (θ : ℂ) * I))
    rw [norm_one, hE] at this
    exact this
  have h2 : ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ ≤ 1 + ‖κ‖ := by
    have := norm_sub_le (1 : ℂ) (κ * Complex.exp (-2 * (θ : ℂ) * I))
    rw [norm_one, hE] at this
    exact this
  have hf : 1 - ‖κ‖ ^ 2 = (1 - ‖κ‖) * (1 + ‖κ‖) := by ring
  have ha : 0 < 1 - ‖κ‖ := by linarith
  have hb : 0 < 1 + ‖κ‖ := by linarith
  constructor
  · rw [div_le_div_iff₀ hb hd, hf]
    nlinarith
  · rw [div_le_div_iff₀ hd ha, hf]
    nlinarith

/-- The polar form of the signed integrand. -/
theorem e124s_pointwise {κ : ℂ} (hκ : ‖κ‖ < 1) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (r : ℂ) • (({η : ℂ | 1 ≤ ‖(η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ)‖ ∧ ‖η‖ < 1}.indicator
          (fun η : ℂ => (η ^ 2)⁻¹) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) -
        ({η : ℂ | ‖(η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ)‖ < 1 ∧ 1 ≤ ‖η‖}.indicator
          (fun η : ℂ => (η ^ 2)⁻¹) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) =
      Complex.exp (-2 * (θ : ℂ) * I) *
        (((Ico (1 / (‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2))) 1).indicator
            (fun r : ℝ => r⁻¹) r -
          (Ico 1 (1 / (‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2)))).indicator
            (fun r : ℝ => r⁻¹) r : ℝ) : ℂ) := by
  set q : ℝ := ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2) with hqd
  have hq : 0 < q := lt_of_lt_of_le (by have := norm_nonneg κ; positivity) (e124s_q_bounds hκ θ).1
  have hn : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hi := e124s_inv_norm hκ hr θ
  rw [← hqd] at hi
  have hG : (r : ℂ) • (((r : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ 2)⁻¹ =
      Complex.exp (-2 * (θ : ℂ) * I) * ((r⁻¹ : ℝ) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    rw [smul_eq_mul, mul_pow, ← Complex.exp_nat_mul, mul_inv, ← Complex.exp_neg]
    push_cast
    field_simp
    try ring_nf
  have hiff1 : (1 ≤ r * q ∧ r < 1) ↔ r ∈ Ico (1 / q) 1 := by
    rw [mem_Ico, div_le_iff₀ hq, mul_comm]
  have hiff2 : (r * q < 1 ∧ 1 ≤ r) ↔ r ∈ Ico 1 (1 / q) := by
    rw [mem_Ico, lt_div_iff₀ hq]
    exact And.comm
  simp only [indicator_apply, mem_ofPred_eq, hi, hn]
  by_cases h1 : r ∈ Ico (1 / q) 1
  · have h1' := hiff1.mpr h1
    have h2 : r ∉ Ico 1 (1 / q) := fun h => by
      have := hiff2.mpr h
      linarith [h1'.1, this.1]
    have h2' : ¬ (r * q < 1 ∧ 1 ≤ r) := fun h => h2 (hiff2.mp h)
    simp only [h1', h1, h2, h2', and_self, ite_true, ite_false, sub_zero]
    exact hG
  · have h1' : ¬ (1 ≤ r * q ∧ r < 1) := fun h => h1 (hiff1.mp h)
    by_cases h2 : r ∈ Ico 1 (1 / q)
    · have h2' := hiff2.mpr h2
      simp only [h1', h1, h2, h2', and_self, ite_true, ite_false, zero_sub, smul_neg]
      rw [hG]
      push_cast
      ring
    · have h2' : ¬ (r * q < 1 ∧ 1 ≤ r) := fun h => h2 (hiff2.mp h)
      simp only [h1', h1, h2, h2', ite_false, sub_zero, smul_zero]
      push_cast
      ring

/-- `r ↦ 1_{[a,b)}(r) r⁻¹` is integrable for `a > 0`. -/
theorem e124s_ind_int {a b : ℝ} (ha : 0 < a) : Integrable ((Ico a b).indicator fun r : ℝ => r⁻¹) := by
  have hc : ContinuousOn (fun r : ℝ => r⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1))
  exact ((hc.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self).integrable_indicator measurableSet_Ico

/-- `|1_{[1/q,1)}(r) r⁻¹ - 1_{[1,1/q)}(r) r⁻¹| ≤ (2/(1-|κ|)) 1_{[1-|κ|, 1+|κ|]}(r)` for `q` as in `e124s_q_bounds`. -/
theorem e124s_R_bound {κ : ℂ} (hκ : ‖κ‖ < 1) {q : ℝ} (hq1 : 1 / (1 + ‖κ‖) ≤ q) (hq2 : q ≤ 1 / (1 - ‖κ‖)) (r : ℝ) :
    ‖(Ico (1 / q) 1).indicator (fun r : ℝ => r⁻¹) r - (Ico 1 (1 / q)).indicator (fun r : ℝ => r⁻¹) r‖ ≤
      (Icc (1 - ‖κ‖) (1 + ‖κ‖)).indicator (fun _ => 2 / (1 - ‖κ‖)) r := by
  have hk0 := norm_nonneg κ
  have ha : 0 < 1 - ‖κ‖ := by linarith
  have hb : 0 < 1 + ‖κ‖ := by linarith
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hiq1 : 1 / q ≤ 1 + ‖κ‖ := by
    rw [div_le_iff₀ hqpos]
    have := (div_le_iff₀ hb).mp hq1
    linarith
  have hiq2 : 1 - ‖κ‖ ≤ 1 / q := by
    rw [le_div_iff₀ hqpos]
    have := (le_div_iff₀ ha).mp hq2
    linarith
  by_cases hr : r ∈ Icc (1 - ‖κ‖) (1 + ‖κ‖)
  · rw [indicator_of_mem hr]
    have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
    have hinv : r⁻¹ ≤ 1 / (1 - ‖κ‖) := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le ha hr.1
    have hA : ‖(Ico (1 / q) 1).indicator (fun r : ℝ => r⁻¹) r‖ ≤ 1 / (1 - ‖κ‖) := by
      rw [Real.norm_eq_abs]
      by_cases h : r ∈ Ico (1 / q) 1
      · rw [indicator_of_mem h, abs_of_pos (inv_pos.mpr hr0)]
        exact hinv
      · rw [indicator_of_notMem h, abs_zero]
        positivity
    have hB : ‖(Ico 1 (1 / q)).indicator (fun r : ℝ => r⁻¹) r‖ ≤ 1 / (1 - ‖κ‖) := by
      rw [Real.norm_eq_abs]
      by_cases h : r ∈ Ico 1 (1 / q)
      · rw [indicator_of_mem h, abs_of_pos (inv_pos.mpr hr0)]
        exact hinv
      · rw [indicator_of_notMem h, abs_zero]
        positivity
    calc _ ≤ ‖(Ico (1 / q) 1).indicator (fun r : ℝ => r⁻¹) r‖ + ‖(Ico 1 (1 / q)).indicator (fun r : ℝ => r⁻¹) r‖ :=
          norm_sub_le _ _
      _ ≤ 1 / (1 - ‖κ‖) + 1 / (1 - ‖κ‖) := add_le_add hA hB
      _ = 2 / (1 - ‖κ‖) := by ring
  · rw [indicator_of_notMem hr]
    have h1 : r ∉ Ico (1 / q) 1 := fun h => hr ⟨hiq2.trans h.1, by linarith [h.2]⟩
    have h2 : r ∉ Ico 1 (1 / q) := fun h => hr ⟨by linarith [h.1], (le_of_lt h.2).trans hiq1⟩
    rw [indicator_of_notMem h1, indicator_of_notMem h2, sub_zero, norm_zero]

/-- **Polar step.** In the image plane, `∫_{B₁} η⁻² - ∫_{B₂} η⁻² = -π κ̄`, where `B₁, B₂` are the two lunes between the
unit circle and the ellipse `{|L⁻¹ η| = 1}`. -/
theorem e124s_polar {κ : ℂ} (hκ : ‖κ‖ < 1) :
    (∫ η in {η : ℂ | 1 ≤ ‖(η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ)‖ ∧ ‖η‖ < 1}, (η ^ 2)⁻¹) -
        (∫ η in {η : ℂ | ‖(η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ)‖ < 1 ∧ 1 ≤ ‖η‖}, (η ^ 2)⁻¹) =
      -(π * conj κ) := by
  have hk0 := norm_nonneg κ
  have hd : (0 : ℝ) < 1 - ‖κ‖ ^ 2 := by nlinarith
  have ha : 0 < 1 - ‖κ‖ := by linarith
  have hb : 0 < 1 + ‖κ‖ := by linarith
  set Li : ℂ → ℂ := fun η => (η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ) with hLid
  have hdC : ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hLic : Continuous Li :=
    (continuous_id.sub (continuous_const.mul Complex.continuous_conj)).div_const _
  have hLi_le : ∀ η, ‖Li η‖ ≤ ‖η‖ / (1 - ‖κ‖) := by
    intro η
    rw [hLid]
    dsimp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have h1 : ‖η - κ * conj η‖ ≤ ‖η‖ * (1 + ‖κ‖) := by
      calc ‖η - κ * conj η‖ ≤ ‖η‖ + ‖κ * conj η‖ := norm_sub_le _ _
        _ = ‖η‖ * (1 + ‖κ‖) := by rw [norm_mul, Complex.norm_conj]; ring
    rw [div_le_div_iff₀ hd ha]
    have hf : 1 - ‖κ‖ ^ 2 = (1 - ‖κ‖) * (1 + ‖κ‖) := by ring
    rw [hf]
    nlinarith [norm_nonneg η]
  have hL : ∀ η, η = Li η + κ * conj (Li η) := by
    intro η
    rw [hLid]
    dsimp only
    rw [map_div₀, Complex.conj_ofReal, map_sub, map_mul, Complex.conj_conj]
    field_simp
    have hn : κ * conj κ = ((‖κ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast at hn ⊢
    linear_combination η * hn
  have hLge : ∀ η, ‖η‖ ≤ (1 + ‖κ‖) * ‖Li η‖ := by
    intro η
    calc ‖η‖ = ‖Li η + κ * conj (Li η)‖ := by rw [← hL η]
      _ ≤ ‖Li η‖ + ‖κ * conj (Li η)‖ := norm_add_le _ _
      _ = (1 + ‖κ‖) * ‖Li η‖ := by rw [norm_mul, Complex.norm_conj]; ring
  set B1 : Set ℂ := {η : ℂ | 1 ≤ ‖Li η‖ ∧ ‖η‖ < 1} with hB1
  set B2 : Set ℂ := {η : ℂ | ‖Li η‖ < 1 ∧ 1 ≤ ‖η‖} with hB2
  have hm1 : MeasurableSet B1 :=
    (measurableSet_le measurable_const hLic.measurable.norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hm2 : MeasurableSet B2 :=
    (measurableSet_lt hLic.measurable.norm measurable_const).inter (measurableSet_le measurable_const measurable_norm)
  set K : Set ℂ := closedBall (0 : ℂ) (1 + ‖κ‖) ∩ {η : ℂ | 1 - ‖κ‖ ≤ ‖η‖} with hKd
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hGK : IntegrableOn (fun η : ℂ => (η ^ 2)⁻¹) K := by
    refine ContinuousOn.integrableOn_compact hKc ?_
    refine (continuousOn_id.pow 2).inv₀ (fun η hη => pow_ne_zero 2 ?_)
    intro h
    have h0 : η = 0 := h
    have h' : 1 - ‖κ‖ ≤ ‖η‖ := hη.2
    rw [h0, norm_zero] at h'
    linarith
  have h1K : B1 ⊆ K := by
    intro η hη
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      linarith [hη.2]
    · show 1 - ‖κ‖ ≤ ‖η‖
      have h := (hη.1).trans (hLi_le η)
      rwa [le_div_iff₀ ha, one_mul] at h
  have h2K : B2 ⊆ K := by
    intro η hη
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      have := hLge η
      nlinarith [hη.1, norm_nonneg (Li η)]
    · show 1 - ‖κ‖ ≤ ‖η‖
      linarith [hη.2]
  have hI1 := (hGK.mono_set h1K).integrable_indicator hm1
  have hI2 := (hGK.mono_set h2K).integrable_indicator hm2
  rw [← integral_indicator hm1, ← integral_indicator hm2, ← integral_sub hI1 hI2,
    ← Complex.integral_comp_polarCoord_symm]
  -- the polar integrand
  set q : ℝ → ℝ := fun θ => ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ / (1 - ‖κ‖ ^ 2) with hqd
  set H : ℝ × ℝ → ℂ := fun p => Complex.exp (-2 * (p.2 : ℂ) * I) *
    (((Ico (1 / q p.2) 1).indicator (fun r : ℝ => r⁻¹) p.1 -
      (Ico 1 (1 / q p.2)).indicator (fun r : ℝ => r⁻¹) p.1 : ℝ) : ℂ) with hHd
  have hpt : ∀ p ∈ polarCoord.target,
      p.1 • (B1.indicator (fun η : ℂ => (η ^ 2)⁻¹) (Complex.polarCoord.symm p) -
        B2.indicator (fun η : ℂ => (η ^ 2)⁻¹) (Complex.polarCoord.symm p)) = H p := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hps : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hps, Complex.real_smul, ← smul_eq_mul]
    exact e124s_pointwise hκ hr p.2
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  -- integrability on the product
  have hqc : Continuous q := by
    rw [hqd]
    fun_prop
  have hqb : ∀ θ, 1 / (1 + ‖κ‖) ≤ q θ ∧ q θ ≤ 1 / (1 - ‖κ‖) := fun θ => e124s_q_bounds hκ θ
  have hqpos : ∀ θ, 0 < q θ := fun θ => lt_of_lt_of_le (by positivity) (hqb θ).1
  have hHm : Measurable H := by
    have hS1 : MeasurableSet {p : ℝ × ℝ | 1 / q p.2 ≤ p.1 ∧ p.1 < 1} :=
      (measurableSet_le (measurable_const.div (hqc.measurable.comp measurable_snd)) measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const)
    have hS2 : MeasurableSet {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 < 1 / q p.2} :=
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst (measurable_const.div (hqc.measurable.comp measurable_snd)))
    have hR : (fun p : ℝ × ℝ => (Ico (1 / q p.2) 1).indicator (fun r : ℝ => r⁻¹) p.1 -
        (Ico 1 (1 / q p.2)).indicator (fun r : ℝ => r⁻¹) p.1) =
        fun p => {p : ℝ × ℝ | 1 / q p.2 ≤ p.1 ∧ p.1 < 1}.indicator (fun p : ℝ × ℝ => p.1⁻¹) p -
          {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 < 1 / q p.2}.indicator (fun p : ℝ × ℝ => p.1⁻¹) p := by
      funext p
      simp only [indicator_apply, mem_Ico, mem_ofPred_eq]
    have hRm : Measurable (fun p : ℝ × ℝ => (Ico (1 / q p.2) 1).indicator (fun r : ℝ => r⁻¹) p.1 -
        (Ico 1 (1 / q p.2)).indicator (fun r : ℝ => r⁻¹) p.1) := by
      rw [hR]
      exact ((measurable_fst.inv).indicator hS1).sub ((measurable_fst.inv).indicator hS2)
    rw [hHd]
    exact (Complex.measurable_exp.comp ((measurable_const.mul
      (Complex.measurable_ofReal.comp measurable_snd)).mul measurable_const)).mul
      (Complex.measurable_ofReal.comp hRm)
  have hHint : Integrable H ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    set C : ℝ := 2 / (1 - ‖κ‖)
    have hg : Integrable ((Icc (1 - ‖κ‖) (1 + ‖κ‖) ×ˢ (univ : Set ℝ)).indicator (fun _ => C))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rw [integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)]
      refine integrableOn_const ?_
      rw [Measure.prod_prod]
      refine ENNReal.mul_ne_top ?_ ?_
      · exact ((Measure.restrict_apply_le _ _).trans_lt measure_Icc_lt_top).ne
      · rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact measure_Ioo_lt_top.ne
    refine Integrable.mono' hg hHm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [hHd]
    dsimp only
    rw [norm_mul, show (-2 * ((p.2 : ℝ) : ℂ) * I) = ((-2 * p.2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
    have h := e124s_R_bound hκ (hqb p.2).1 (hqb p.2).2 p.1
    calc _ ≤ (Icc (1 - ‖κ‖) (1 + ‖κ‖)).indicator (fun _ => 2 / (1 - ‖κ‖)) p.1 := h
      _ = (Icc (1 - ‖κ‖) (1 + ‖κ‖) ×ˢ (univ : Set ℝ)).indicator (fun _ => C) p := by
          simp only [indicator_apply, mem_prod, mem_univ, and_true] <;> rfl
  rw [ht, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm H hHint]
  -- the radial integral
  have hin : ∀ θ : ℝ, (∫ r, H (r, θ) ∂(volume.restrict (Ioi (0 : ℝ)))) =
      Complex.exp (-2 * (θ : ℂ) * I) * ((Real.log (q θ) : ℝ) : ℂ) := by
    intro θ
    rw [hHd]
    dsimp only
    rw [integral_const_mul, integral_complex_ofReal,
      integral_sub (e124s_ind_int (by have := hqpos θ; positivity)).integrableOn
        (e124s_ind_int one_pos).integrableOn, e124s_radial (hqpos θ)]
  rw [integral_congr_ae (Eventually.of_forall hin)]
  -- the angular integral
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hfun : (fun θ : ℝ => Complex.exp (-2 * (θ : ℂ) * I) * ((Real.log (q θ) : ℝ) : ℂ)) =
      fun θ : ℝ => Complex.exp (-2 * (θ : ℂ) * I) * (Real.log ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ : ℂ) -
        ((Real.log (1 - ‖κ‖ ^ 2) : ℝ) : ℂ) * Complex.exp (((-2 : ℤ) : ℂ) * (θ : ℂ) * I) := by
    funext θ
    have hne : ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ ≠ 0 := by
      have := hqpos θ
      rw [hqd] at this
      exact (div_pos_iff_of_pos_right hd |>.mp this).ne'
    rw [hqd]
    dsimp only
    rw [Real.log_div hne hd.ne']
    push_cast
    ring
  have hne' : ∀ θ : ℝ, ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ ≠ 0 := by
    intro θ
    have := hqpos θ
    rw [hqd] at this
    exact (div_pos_iff_of_pos_right hd |>.mp this).ne'
  have hlogc : Continuous fun θ : ℝ => Real.log ‖1 - κ * Complex.exp (-2 * (θ : ℂ) * I)‖ :=
    (continuous_norm.comp (by fun_prop)).log hne'
  rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, e124s_fourier hκ, e124s_int_exp]
  · simp
  · exact (Continuous.intervalIntegrable ((by fun_prop : Continuous fun θ : ℝ => Complex.exp (-2 * (θ : ℂ) * I)).mul
      (Complex.continuous_ofReal.comp hlogc)) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The real-linear map `h ↦ h + κ h̄` has determinant `1 - |κ|²`. -/
theorem e124s_det (κ : ℂ) :
    LinearMap.det ((ContinuousLinearMap.id ℝ ℂ + (ContinuousLinearMap.mul ℝ ℂ κ).comp
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = 1 - ‖κ‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Shape term.** For `|κ| < 1` the principal value of `(h + κh̄)⁻²` over the complement of the ellipse
`{|h + κh̄| < 1}` and over the complement of the unit disc differ by `-π κ̄/(1 - |κ|²)`. -/
theorem e124_shape {κ : ℂ} (hκ : ‖κ‖ < 1) :
    (∫ h in {h : ℂ | 1 ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < 1}, ((h + κ * conj h) ^ 2)⁻¹) -
        (∫ h in {h : ℂ | ‖h‖ < 1 ∧ 1 ≤ ‖h + κ * conj h‖}, ((h + κ * conj h) ^ 2)⁻¹) =
      -(π * conj κ) / (1 - ‖κ‖ ^ 2) := by
  have hk0 := norm_nonneg κ
  have hd : (0 : ℝ) < 1 - ‖κ‖ ^ 2 := by nlinarith
  set L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.id ℝ ℂ + (ContinuousLinearMap.mul ℝ ℂ κ).comp
    (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hLd
  have hLa : ∀ h, L h = h + κ * conj h := by
    intro h
    rw [hLd]
    simp
  set Li : ℂ → ℂ := fun η => (η - κ * conj η) / ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ) with hLid
  have hdC : ((1 - ‖κ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hn : κ * conj κ = ((‖κ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hLiL : ∀ h, Li (L h) = h := by
    intro h
    rw [hLa, hLid]
    dsimp only
    rw [map_add, map_mul, Complex.conj_conj]
    field_simp
    push_cast at hn ⊢
    linear_combination (-h) * hn
  have hLLi : ∀ η, L (Li η) = η := by
    intro η
    rw [hLa, hLid]
    dsimp only
    rw [map_div₀, Complex.conj_ofReal, map_sub, map_mul, Complex.conj_conj]
    field_simp
    push_cast at hn ⊢
    linear_combination (-η) * hn
  have hLinj : Function.Injective L := fun a b hab => by rw [← hLiL a, ← hLiL b, hab]
  have hdet : |LinearMap.det (L : ℂ →ₗ[ℝ] ℂ)| = 1 - ‖κ‖ ^ 2 := by
    rw [hLd, e124s_det, abs_of_pos hd]
  -- change of variables `η = L h`
  have hcv : ∀ {s : Set ℂ}, MeasurableSet s →
      (∫ h in s, ((h + κ * conj h) ^ 2)⁻¹) = (1 - ‖κ‖ ^ 2)⁻¹ • ∫ η in L '' s, (η ^ 2)⁻¹ := by
    intro s hs
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun x _ => L.hasFDerivAt.hasFDerivWithinAt) hLinj.injOn, hdet, integral_smul, smul_smul,
      inv_mul_cancel₀ hd.ne', one_smul]
    simp only [hLa]
  have hLc : Continuous fun h : ℂ => h + κ * conj h := continuous_id.add (continuous_const.mul Complex.continuous_conj)
  have hA1 : MeasurableSet {h : ℂ | 1 ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < 1} :=
    (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt hLc.measurable.norm measurable_const)
  have hA2 : MeasurableSet {h : ℂ | ‖h‖ < 1 ∧ 1 ≤ ‖h + κ * conj h‖} :=
    (measurableSet_lt measurable_norm measurable_const).inter (measurableSet_le measurable_const hLc.measurable.norm)
  have himg : ∀ {P : ℝ → ℝ → Prop},
      L '' {h : ℂ | P ‖h‖ ‖h + κ * conj h‖} = {η : ℂ | P ‖Li η‖ ‖η‖} := by
    intro P
    ext η
    constructor
    · rintro ⟨h, hh, rfl⟩
      show P ‖Li (L h)‖ ‖L h‖
      rw [hLiL, hLa]
      exact hh
    · intro hη
      refine ⟨Li η, ?_, hLLi η⟩
      show P ‖Li η‖ ‖Li η + κ * conj (Li η)‖
      rw [← hLa, hLLi]
      exact hη
  rw [hcv hA1, hcv hA2,
    himg (P := fun a b => 1 ≤ a ∧ b < 1), himg (P := fun a b => a < 1 ∧ 1 ≤ b), ← smul_sub]
  have hpol := e124s_polar hκ
  rw [hLid]
  rw [hpol, Complex.real_smul]
  push_cast
  field_simp

/-! ### `e124_chain`: regularity of `f = w_{εμ}` and of its inverse -/

/-- `extU (ε μ)` is a Beltrami coefficient on `ℂ` with bound `‖ε‖ k`. -/
theorem e124c_extU_beltrami {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) (ε : ℂ) :
    IsBeltramiCoeff (extU fun y => ε * μ y) univ (‖ε‖ * k) := by
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  have hmL : MeasurableSet {z : ℂ | z.im < 0} := measurableSet_lt Complex.measurable_im measurable_const
  have hpre : conj ⁻¹' upperHalf = {z : ℂ | z.im < 0} := by
    ext z
    simp [upperHalf, Complex.conj_im]
  have hmp : MeasurePreserving conj (volume.restrict {z : ℂ | z.im < 0}) (volume.restrict upperHalf) := by
    have := gzE_conj_measurePreserving.restrict_preimage hmU
    rwa [hpre] at this
  have hsplit : extU (fun y => ε * μ y) =
      fun u => upperHalf.indicator (fun y => ε * μ y) u +
        {z : ℂ | z.im < 0}.indicator (fun y => conj (ε * μ (conj y))) u := by
    funext u
    by_cases h1 : 0 < u.im
    · have h2 : ¬ u.im < 0 := not_lt.2 h1.le
      have h1' : u ∈ upperHalf := h1
      simp [extU, h1, h2, h1', indicator_of_notMem (show u ∉ {z : ℂ | z.im < 0} from h2)]
    · have h1' : u ∉ upperHalf := h1
      by_cases h2 : u.im < 0
      · have h2' : u ∈ {z : ℂ | z.im < 0} := h2
        simp [extU, h1, h2, indicator_of_notMem h1', indicator_of_mem h2']
      · have h2' : u ∉ {z : ℂ | z.im < 0} := h2
        simp [extU, h1, h2, indicator_of_notMem h1', indicator_of_notMem h2']
  have hA : AEStronglyMeasurable (fun y => ε * μ y) (volume.restrict upperHalf) := hμ.1.const_mul ε
  have hB : AEStronglyMeasurable (fun y => conj (ε * μ (conj y))) (volume.restrict {z : ℂ | z.im < 0}) :=
    Complex.continuous_conj.comp_aestronglyMeasurable (hA.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving)
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_univ, hsplit]
    exact ((aestronglyMeasurable_indicator_iff hmU).2 hA).add ((aestronglyMeasurable_indicator_iff hmL).2 hB)
  · rw [Measure.restrict_univ]
    have hU := (ae_restrict_iff' hmU).1 hμ.2
    have hL : ∀ᵐ u, u ∈ {z : ℂ | z.im < 0} → ‖μ (conj u)‖ ≤ k :=
      (ae_restrict_iff' hmL).1 (hmp.quasiMeasurePreserving.ae hμ.2)
    filter_upwards [hU, hL] with u hu hl
    show ‖extU (fun y => ε * μ y) u‖ ≤ ‖ε‖ * k
    unfold extU
    by_cases h1 : 0 < u.im
    · rw [if_pos h1, norm_mul]
      exact mul_le_mul_of_nonneg_left (hu h1) (norm_nonneg _)
    · rw [if_neg h1]
      by_cases h2 : u.im < 0
      · rw [if_pos h2, Complex.norm_conj, norm_mul]
        exact mul_le_mul_of_nonneg_left (hl h2) (norm_nonneg _)
      · rw [if_neg h2, norm_zero]
        positivity

/-- Facts about `f = w_{εμ}` used below. -/
theorem e124c_setup {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) :
    IsNormalizedSolution f (extU fun y => ε * μ y) ∧ ContDiffOn ℝ 3 f upperHalf ∧
      (∀ y ∈ upperHalf, 0 < jacobian f y) ∧ ∀ y ∈ upperHalf, complexDilatation f y = ε * μ y := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hns : IsNormalizedSolution f (extU fun y => ε * μ y) := by
    rw [hf]
    exact QCV.qcv_ns_spec (by positivity) hε (e124c_extU_beltrami hk hμ ε)
  have hμs' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ upperHalf := hμs
  have hC : ContDiffOn ℝ 3 f upperHalf := by
    have h := (wr_joint_contDiff_U hk hμ hμs').comp (s := upperHalf) (g := fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2)
      (f := fun y : ℂ => (ε, y)) (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨hε, hy⟩)
    rw [hf]
    exact h
  have hJ : ∀ y ∈ upperHalf, 0 < jacobian f y := by
    intro y hy
    rw [hf]
    exact wr_jacobian_pos_U hk hμ hμs' hε hy
  refine ⟨hns, hC, hJ, ?_⟩
  -- the dilatation is `εμ` everywhere on `𝕌`, by continuity
  have hd1 : ∀ y ∈ upperHalf, DifferentiableAt ℝ f y := fun y hy =>
    (hC.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdz0 : ∀ y ∈ upperHalf, dz f y ≠ 0 := by
    intro y hy h0
    have := hJ y hy
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f y)]
  have hfd : ContinuousOn (fderiv ℝ f) upperHalf := hC.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdzc : ContinuousOn (dz f) upperHalf := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hdzbc : ContinuousOn (dzbar f) upperHalf := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const)))).div_const _
  have hcd : ContinuousOn (complexDilatation f) upperHalf := hdzbc.div hdzc hdz0
  have hcμ : ContinuousOn (fun y => ε * μ y) upperHalf := continuousOn_const.mul hμs.continuousOn
  have hae : complexDilatation f =ᵐ[volume.restrict upperHalf] fun y => ε * μ y := by
    have hmU : MeasurableSet upperHalf := hU.measurableSet
    filter_upwards [ae_restrict_of_ae hns.2.2.2.2, ae_restrict_mem hmU] with y hy hyU
    rw [hy]
    unfold extU
    rw [if_pos (show 0 < y.im from hyU)]
  exact Measure.eqOn_open_of_ae_eq hae hU hcd hcμ

/-- The inverse of `f` is `C²` near `f y`, `y ∈ 𝕌` (inverse function theorem, `J_f > 0`). -/
theorem e124c_inv {f g₀ : ℂ → ℂ} (hns : IsNormalizedSolution f g₀) (hC : ContDiffOn ℝ 3 f upperHalf)
    (hJ : ∀ y ∈ upperHalf, 0 < jacobian f y) {y : ℂ} (hy : y ∈ upperHalf) :
    ContDiffAt ℝ 2 (Function.invFunOn f univ) (f y) := by
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hns
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hinv : Function.invFunOn f univ = e.symm := by
    funext η
    have hex : ∃ a ∈ (univ : Set ℂ), f a = η := ⟨e.symm η, mem_univ _, by rw [← he]; exact e.apply_symm_apply η⟩
    apply e.injective
    rw [he, Function.invFunOn_eq hex, ← he, e.apply_symm_apply]
  have hCy : ContDiffAt ℝ 3 f y := hC.contDiffAt (hU.mem_nhds hy)
  have hdet : (fderiv ℝ f y).det ≠ 0 := by
    have h := det_fderiv_eq_jacobian (hCy.differentiableAt (by norm_num))
    show LinearMap.det (fderiv ℝ f y : ℂ →ₗ[ℝ] ℂ) ≠ 0
    rw [h]
    exact (hJ y hy).ne'
  set L : ℂ ≃L[ℝ] ℂ := (fderiv ℝ f y).toContinuousLinearEquivOfDetNeZero hdet with hLd
  have hsy : e.symm (f y) = y := by rw [← he, e.symm_apply_apply]
  have hL : HasFDerivAt e (L : ℂ →L[ℝ] ℂ) (e.toOpenPartialHomeomorph.symm (f y)) := by
    have h1 : (L : ℂ →L[ℝ] ℂ) = fderiv ℝ f y := by
      ext x
      rw [hLd]
      exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply _ hdet x
    show HasFDerivAt e (L : ℂ →L[ℝ] ℂ) (e.symm (f y))
    rw [hsy, h1, he]
    exact (hCy.differentiableAt (by norm_num)).hasFDerivAt
  have hCe : ContDiffAt ℝ 2 e (e.toOpenPartialHomeomorph.symm (f y)) := by
    show ContDiffAt ℝ 2 e (e.symm (f y))
    rw [hsy, he]
    exact hCy.of_le (by norm_num)
  have h := e.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ (f y)) hL hCe
  rw [hinv]
  exact h

/-- The pushforward coefficient `ν̇ = (μ/(1 - |εμ|²) · f_z/\overline{f_z}) ∘ f⁻¹` is `C¹` near `f y`, `y ∈ 𝕌`. -/
theorem e124c_nudot_cdAt {μ : ℂ → ℂ} {ε : ℂ} {f : ℂ → ℂ} (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    (hns : IsNormalizedSolution f (extU fun y => ε * μ y)) (hC : ContDiffOn ℝ 3 f upperHalf)
    (hJ : ∀ y ∈ upperHalf, 0 < jacobian f y) (hdil : ∀ y ∈ upperHalf, complexDilatation f y = ε * μ y)
    {y : ℂ} (hy : y ∈ upperHalf) :
    ContDiffAt ℝ 1 (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f) (f y) := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set inv := Function.invFunOn f univ with hinvd
  have hinj : InjOn f univ := hns.1.choose_spec.2.2.1.2.1
  have hiy : inv (f y) = y := hinj.leftInvOn_invFunOn (mem_univ y)
  have hinvC : ContDiffAt ℝ 2 inv (f y) := e124c_inv hns hC hJ hy
  -- the source-side expression
  have hdz0 : ∀ x ∈ upperHalf, dz f x ≠ 0 := by
    intro x hx h0
    have := hJ x hx
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f x)]
  have hlt : ∀ x ∈ upperHalf, ‖ε * μ x‖ < 1 := by
    intro x hx
    have hJx := hJ x hx
    unfold jacobian at hJx
    rw [← hdil x hx]
    show ‖dzbar f x / dz f x‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hdz0 x hx))]
    nlinarith [norm_nonneg (dzbar f x), norm_nonneg (dz f x)]
  set Φ : ℂ → ℂ := fun x => μ x / (1 - conj (ε * μ x) * (ε * μ x)) * (dz f x / conj (dz f x)) with hΦd
  have hΦ : ContDiffAt ℝ 1 Φ y := by
    have hμy : ContDiffAt ℝ 1 μ y := (hμs.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast le_top)
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) y := (hC.contDiffAt (hU.mem_nhds hy)).fderiv_right (by norm_num)
    have hdz : ContDiffAt ℝ 1 (dz f) y := by
      show ContDiffAt ℝ 1 (fun x => (fderiv ℝ f x 1 - I * fderiv ℝ f x I) / 2) y
      exact ((hfd.clm_apply contDiffAt_const).sub (contDiffAt_const.mul (hfd.clm_apply contDiffAt_const))).div_const _
    have hcj : ∀ {g : ℂ → ℂ}, ContDiffAt ℝ 1 g y → ContDiffAt ℝ 1 (fun x => conj (g x)) y := fun hg =>
      (Complex.conjCLE.contDiff.contDiffAt).comp y hg
    have hεμ : ContDiffAt ℝ 1 (fun x => ε * μ x) y := contDiffAt_const.mul hμy
    have hden1 : 1 - conj (ε * μ y) * (ε * μ y) ≠ 0 := by
      intro h0
      have h1 : conj (ε * μ y) * (ε * μ y) = 1 := by linear_combination -h0
      have h2 := hlt y hy
      have : ‖conj (ε * μ y) * (ε * μ y)‖ = ‖ε * μ y‖ ^ 2 := by rw [norm_mul, Complex.norm_conj]; ring
      rw [h1, norm_one] at this
      nlinarith [norm_nonneg (ε * μ y)]
    have hden2 : conj (dz f y) ≠ 0 := (map_ne_zero _).2 (hdz0 y hy)
    have hdiv : ∀ {g h : ℂ → ℂ}, ContDiffAt ℝ 1 g y → ContDiffAt ℝ 1 h y → h y ≠ 0 →
        ContDiffAt ℝ 1 (fun x => g x / h x) y := by
      intro g h hg hh hne
      simp only [div_eq_mul_inv]
      exact hg.mul (hh.inv hne)
    exact (hdiv hμy (contDiffAt_const.sub ((hcj hεμ).mul hεμ)) hden1).mul (hdiv hdz (hcj hdz) hden2)
  have hcomp : ContDiffAt ℝ 1 (Φ ∘ inv) (f y) := by
    rw [← hiy] at hΦ
    exact hΦ.comp (f y) (hinvC.of_le (by norm_num))
  refine hcomp.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ η in 𝓝 (f y), inv η ∈ upperHalf := by
    have hc : ContinuousAt inv (f y) := hinvC.continuousAt
    exact hc.preimage_mem_nhds (by rw [hiy]; exact hU.mem_nhds hy)
  filter_upwards [hev] with η hη
  show (upperHalf.indicator μ) (inv η) / (1 - conj ((extU fun y => ε * μ y) (inv η)) *
      (extU fun y => ε * μ y) (inv η)) * (dz f (inv η) / conj (dz f (inv η))) = Φ (inv η)
  have he : (extU fun y => ε * μ y) (inv η) = ε * μ (inv η) := by
    unfold extU
    rw [if_pos (show 0 < (inv η).im from hη)]
  rw [indicator_of_mem hη, he]

/-- The cutoff: `ω = χ ν̇` is `C¹` with compact support, and `χ = 1` near `f z`. -/
theorem e124c_cutoff {μ : ℂ → ℂ} {ε : ℂ} {f : ℂ → ℂ} (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf)
    (hns : IsNormalizedSolution f (extU fun y => ε * μ y)) (hC : ContDiffOn ℝ 3 f upperHalf)
    (hJ : ∀ y ∈ upperHalf, 0 < jacobian f y) (hdil : ∀ y ∈ upperHalf, complexDilatation f y = ε * μ y)
    {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ R > 0, ∃ χ : ℂ → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧ (∀ η, 0 ≤ χ η ∧ χ η ≤ 1) ∧
      (∀ η ∈ ball (f z) R, χ η = 1) ∧
      tsupport χ ⊆ f '' upperHalf ∧
      ContDiff ℝ 1 (fun η => (χ η : ℂ) * ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f η) := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hns' := hns
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hns'
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hO : IsOpen (f '' upperHalf) := by
    rw [← he]
    exact e.isOpenMap _ hU
  obtain ⟨R0, hR0, hball⟩ := Metric.isOpen_iff.mp hO (f z) ⟨z, hz, rfl⟩
  set R : ℝ := R0 / 3 with hRd
  have hR : 0 < R := by positivity
  let c : ContDiffBump (f z) := ⟨R, 2 * R, hR, by linarith⟩
  refine ⟨R, hR, c, c.contDiff, c.hasCompactSupport, fun η => ⟨c.nonneg, c.le_one⟩, fun η hη =>
    c.one_of_mem_closedBall (ball_subset_closedBall hη), ?_, ?_⟩
  · rw [c.tsupport_eq]
    exact (closedBall_subset_ball (by show 2 * R < R0; linarith)).trans hball
  · rw [contDiff_iff_contDiffAt]
    intro η
    by_cases hη : η ∈ ball (f z) R0
    · obtain ⟨y, hy, rfl⟩ := hball hη
      have hn := e124c_nudot_cdAt hμs hns hC hJ hdil hy
      exact ((Complex.ofRealCLM.contDiff.comp c.contDiff).contDiffAt).mul hn
    · have hfar : ∀ᶠ x in 𝓝 η, (c x : ℂ) * ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f x = 0 := by
        have hcl : (closedBall (f z) (2 * R))ᶜ ∈ 𝓝 η := isClosed_closedBall.isOpen_compl.mem_nhds (by
          intro h
          apply hη
          exact closedBall_subset_ball (by show 2 * R < R0; linarith) h)
        filter_upwards [hcl] with x hx
        have : c x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          rw [c.tsupport_eq]
          exact hx
        rw [this, Complex.ofReal_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hfar

/-- Truncating an integrable function off a shrinking disc does not change the limit. -/
theorem e124c_trunc_tendsto {g : ℂ → ℂ} (hg : Integrable g) (a : ℂ) :
    Tendsto (fun δ : ℝ => ∫ η in {η : ℂ | δ < ‖η - a‖}, g η) (𝓝[>] 0) (𝓝 (∫ η, g η)) := by
  have hm : ∀ δ : ℝ, MeasurableSet {η : ℂ | δ < ‖η - a‖} := fun δ =>
    measurableSet_lt measurable_const (measurable_id.sub_const a).norm
  have e : ∀ δ : ℝ, (∫ η in {η : ℂ | δ < ‖η - a‖}, g η) = ∫ η, {η : ℂ | δ < ‖η - a‖}.indicator g η :=
    fun δ => (integral_indicator (hm δ)).symm
  simp only [e]
  apply tendsto_integral_filter_of_dominated_convergence (fun η => ‖g η‖)
  · exact Eventually.of_forall fun δ => hg.aestronglyMeasurable.indicator (hm δ)
  · exact Eventually.of_forall fun δ => Eventually.of_forall fun η => norm_indicator_le_norm_self _ _
  · exact hg.norm
  · filter_upwards [Measure.ae_ne volume a] with η hη
    have hpos : 0 < ‖η - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hη)
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    exact (indicator_of_mem (show η ∈ {η : ℂ | δ < ‖η - a‖} from hδ.2) g).symm

/-- **Derivatives of `G = V[ν]` at `a`.** If `ν` is bounded and `χ ν` is `C¹` for a cutoff `χ` equal to `1`
near `a`, then `V[ν]` is real-differentiable at `a`, `∂_{z̄} V[ν](a) = ν(a)`, and `∂_z V[ν](a)` is the
round principal value of `-(1/π) ∫ ν(η) (1/(η-a)² + 1/η - 1/(η-1))`. -/
theorem e124c_G {ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hν : IsBeltramiCoeff ν univ k) {a : ℂ} {R : ℝ}
    (hR : 0 < R) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ η, 0 ≤ χ η ∧ χ η ≤ 1) (hχ1 : ∀ η ∈ ball a R, χ η = 1)
    (hω : ContDiff ℝ 1 (fun η => (χ η : ℂ) * ν η)) :
    DifferentiableAt ℝ (ahVar ν) a ∧ dzbar (ahVar ν) a = ν a ∧
      Tendsto (fun δ : ℝ => -(1 / π : ℂ) * ∫ η in {η : ℂ | δ < ‖η - a‖}, ν η * QCV.kerD1 a η)
        (𝓝[>] 0) (𝓝 (dz (ahVar ν) a)) := by
  set ω : ℂ → ℂ := fun η => (χ η : ℂ) * ν η with hωd
  set ν₂ : ℂ → ℂ := fun η => (1 - (χ η : ℂ)) * ν η with hν₂d
  have hχn : ∀ η, ‖(χ η : ℂ)‖ ≤ 1 := fun η => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ01 η).1]
    exact (hχ01 η).2
  have hχn2 : ∀ η, ‖1 - (χ η : ℂ)‖ ≤ 1 := fun η => by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(hχ01 η).2])]
    linarith [(hχ01 η).1]
  have hνm : AEStronglyMeasurable ν volume := by simpa using hν.1
  have hνb : ∀ᵐ u : ℂ, ‖ν u‖ ≤ k := by simpa using hν.2
  have hχC : Continuous fun η => (χ η : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hωB : IsBeltramiCoeff ω univ k := by
    refine ⟨by rw [Measure.restrict_univ]; exact hω.continuous.aestronglyMeasurable, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [hνb] with u hu
    show ‖(χ u : ℂ) * ν u‖ ≤ k
    rw [norm_mul]
    calc _ ≤ 1 * k := mul_le_mul (hχn u) hu (norm_nonneg _) zero_le_one
      _ = k := one_mul k
  have hν₂B : IsBeltramiCoeff ν₂ univ k := by
    refine ⟨by rw [Measure.restrict_univ]; exact (continuous_const.sub hχC).aestronglyMeasurable.mul hνm, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [hνb] with u hu
    show ‖(1 - (χ u : ℂ)) * ν u‖ ≤ k
    rw [norm_mul]
    calc _ ≤ 1 * k := mul_le_mul (hχn2 u) hu (norm_nonneg _) zero_le_one
      _ = k := one_mul k
  have hsplit : ∀ w, ahVar ν w = ahVar ω w + ahVar ν₂ w := by
    intro w
    have e : ν = fun ζ => (1 : ℂ) * ω ζ + ν₂ ζ := by
      funext ζ
      show ν ζ = 1 * ((χ ζ : ℂ) * ν ζ) + (1 - (χ ζ : ℂ)) * ν ζ
      ring
    calc ahVar ν w = ahVar (fun ζ => (1 : ℂ) * ω ζ + ν₂ ζ) w := congrArg (fun q => ahVar q w) e
      _ = _ := by simpa using ah_var_linear hωB hν₂B 1 w
  -- the compactly supported part is a Cauchy transform up to an affine function
  have hωc : HasCompactSupport ω :=
    show HasCompactSupport ((fun η => (χ η : ℂ)) * ν) from (hχc.comp_left Complex.ofReal_zero).mul_right
  obtain ⟨R', hR'⟩ := hωc.isCompact.isBounded.subset_closedBall 0
  have hR1 : (0 : ℝ) < max R' 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hωR : ∀ z : ℂ, max R' 1 < ‖z‖ → ω z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have h1 := mem_closedBall.1 (hR' hm)
    rw [dist_zero_right] at h1
    linarith [le_max_left R' 1]
  have hωp : MemLp ω (ENNReal.ofReal 4) volume := hω.continuous.memLp_of_hasCompactSupport hωc
  have hωi : ∀ z, Integrable (fun ζ => ω ζ / (ζ - z)) :=
    integrable_cauchyT_kernel (by norm_num : (2 : ℝ) < 4) hR1 hωp hωR
  have hahω : ∀ w, ahVar ω w = cauchyT ω w - cauchyT ω 0 - w * (cauchyT ω 1 - cauchyT ω 0) :=
    ahC_ahVar_eq (by norm_num : (2 : ℝ) < 4) hR1 hωp hωR
  -- the part vanishing near `a` is holomorphic there
  have hν₂0 : ∀ u ∈ ball a R, ν₂ u = 0 := by
    intro u hu
    show (1 - (χ u : ℂ)) * ν u = 0
    rw [hχ1 u hu]
    simp
  have hD := (QCV.qcv_ahVar_kernel_derivatives hk hν₂B isOpen_ball hν₂0 (mem_ball_self hR)).1
  set L₂ : ℂ := ∫ u, ν₂ u * QCV.kerD1 a u with hL₂d
  set c : ℂ := cauchyT ω 1 - cauchyT ω 0 with hcd
  set P : ℂ → ℂ := fun w => -cauchyT ω 0 - w * c + ahVar ν₂ w with hPd
  have hP : HasDerivAt P (-c + -(1 / π : ℂ) * L₂) a := by
    have h1 := ((hasDerivAt_id' a).mul_const c).const_sub (-cauchyT ω 0)
    rw [one_mul] at h1
    exact h1.add (hD.const_mul (-(1 / π : ℂ)))
  have hPc : DifferentiableAt ℂ P a := hP.differentiableAt
  have hPR := cauchyRiemann_iff.1 hPc
  have hPdz : dz P a = -c + -(1 / π : ℂ) * L₂ := by rw [dz_eq_deriv hPc, hP.deriv]
  have hTd : DifferentiableAt ℝ (cauchyT ω) a :=
    ((contDiff_cauchyT hω hωc).contDiffAt).differentiableAt (by norm_num)
  have hG : ahVar ν = fun w => cauchyT ω w + P w := by
    funext w
    rw [hsplit, hahω]
    show _ = cauchyT ω w + (-cauchyT ω 0 - w * (cauchyT ω 1 - cauchyT ω 0) + ahVar ν₂ w)
    ring
  have hadd := l613_dz_add hTd hPR.1
  have hdzbar : dzbar (ahVar ν) a = ν a := by
    rw [hG, hadd.2, hPR.2, add_zero, dzbar_cauchyT hω hωc, cauchyT_dzbar_eq hω hωc]
    show (χ a : ℂ) * ν a = ν a
    rw [hχ1 a (mem_ball_self hR)]
    simp
  have hdz : dz (ahVar ν) a = cauchyT (dz ω) a + (-c + -(1 / π : ℂ) * L₂) := by
    rw [hG, hadd.1, hPdz, dz_cauchyT hω hωc]
  refine ⟨by rw [hG]; exact hTd.add hPR.1, hdzbar, ?_⟩
  -- the three truncated pieces
  have hA := tendsto_truncated_cauchyT_dz hω hωc a
  set g : ℂ → ℂ := fun ζ => ω ζ / (ζ - 0) - ω ζ / (ζ - 1) with hgd
  have hgi : Integrable g := (hωi 0).sub (hωi 1)
  have hB := (e124c_trunc_tendsto hgi a).const_mul (-(1 / π : ℂ))
  have hBv : -(1 / π : ℂ) * ∫ η, g η = -c := by
    show -(1 / π : ℂ) * ∫ η, (ω η / (η - 0) - ω η / (η - 1)) = -(cauchyT ω 1 - cauchyT ω 0)
    rw [integral_sub (hωi 0) (hωi 1)]
    simp only [cauchyT]
    ring
  have hν₂i : Integrable (fun u => ν₂ u * QCV.kerD1 a u) := by
    obtain ⟨C, hC, hmaj⟩ := QCV.qcv_kernel_ball_majorant (y := a) (r := R / 8) (by positivity)
    have hm1 : Measurable (QCV.kerD1 a) := by unfold QCV.kerD1; fun_prop
    have hν₂m : AEStronglyMeasurable ν₂ volume := by simpa using hν₂B.1
    have hν₂b : ∀ᵐ u : ℂ, ‖ν₂ u‖ ≤ k := by simpa using hν₂B.2
    refine (((ah_ker_integrable I).norm.const_mul C).const_mul k).mono'
      (hν₂m.mul hm1.aestronglyMeasurable) ?_
    filter_upwards [hν₂b, Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume (1 : ℂ),
      Measure.ae_ne volume I] with u hu h0 h1 hI
    by_cases hz : ν₂ u = 0
    · rw [hz, zero_mul, norm_zero]
      positivity
    · have hfar : 8 * (R / 8) ≤ ‖u - a‖ := by
        by_contra hlt
        push_neg at hlt
        exact hz (hν₂0 u (by rw [mem_ball, dist_eq_norm]; linarith))
      rw [norm_mul]
      exact mul_le_mul hu (hmaj u h0 h1 hI hfar a (mem_ball_self (by positivity))).2.1 (norm_nonneg _) hk
  have hωI : Integrable ω := hω.continuous.integrable_of_hasCompactSupport hωc
  have hωm : Measurable ω := hω.continuous.measurable
  have hs : ∀ δ : ℝ, MeasurableSet {η : ℂ | δ < ‖η - a‖} := fun δ =>
    measurableSet_lt measurable_const (measurable_id.sub_const a).norm
  have hωi2 : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun ζ => ω ζ / (ζ - a) ^ 2) {ζ : ℂ | δ < ‖ζ - a‖} := by
    intro δ hδ
    have hb : Integrable (fun ζ => ‖ω ζ‖ * (δ ^ 2)⁻¹) (volume.restrict {ζ : ℂ | δ < ‖ζ - a‖}) :=
      (hωI.norm.mul_const _).restrict
    refine hb.mono' (by fun_prop : Measurable fun ζ => ω ζ / (ζ - a) ^ 2).aestronglyMeasurable ?_
    rw [ae_restrict_iff' (hs δ)]
    refine Eventually.of_forall fun ζ hζ => ?_
    have hζ' : δ < ‖ζ - a‖ := hζ
    rw [norm_div, norm_pow, div_eq_mul_inv]
    gcongr
  have hgoal : cauchyT (dz ω) a + (-c + -(1 / π : ℂ) * L₂) =
      (cauchyT (dz ω) a + -(1 / π : ℂ) * ∫ η, g η) + -(1 / π : ℂ) * L₂ := by
    rw [hBv]
    ring
  rw [hdz, hgoal]
  refine ((hA.add hB).add tendsto_const_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with δ hδ
  have hL₂ : ∫ η in {η : ℂ | δ < ‖η - a‖}, ν₂ η * QCV.kerD1 a η = L₂ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hu' : ¬ δ < ‖u - a‖ := hu
    push_neg at hu'
    rw [hν₂0 u (by rw [mem_ball, dist_eq_norm]; linarith [hδ.2]), zero_mul]
  have hpt : ∀ᵐ η : ℂ, ν η * QCV.kerD1 a η = ω η / (η - a) ^ 2 + g η + ν₂ η * QCV.kerD1 a η := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume (1 : ℂ),
      Measure.ae_ne volume a] with η h0 h1 ha
    have h1' : η - 1 ≠ 0 := sub_ne_zero.2 h1
    have ha' : η - a ≠ 0 := sub_ne_zero.2 ha
    show ν η * QCV.kerD1 a η = (χ η : ℂ) * ν η / (η - a) ^ 2 +
      ((χ η : ℂ) * ν η / (η - 0) - (χ η : ℂ) * ν η / (η - 1)) + (1 - (χ η : ℂ)) * ν η * QCV.kerD1 a η
    unfold QCV.kerD1
    rw [sub_zero]
    field_simp
    ring
  have hi1 : IntegrableOn (fun ζ => ω ζ / (ζ - a) ^ 2 + g ζ) {ζ : ℂ | δ < ‖ζ - a‖} :=
    (hωi2 δ hδ.1).add hgi.integrableOn
  rw [← hL₂, ← mul_add, ← mul_add, ← integral_add (hωi2 δ hδ.1) hgi.integrableOn,
    ← integral_add hi1 hν₂i.integrableOn]
  congr 1
  refine setIntegral_congr_ae (hs δ) ?_
  filter_upwards [hpt] with η hη _
  exact hη.symm

/-- Change of variables for the pushforward coefficient against a general measurable kernel `K`
(the pattern of `QCV.qcv_var_source`, with `ahKer w` replaced by `K`). -/
theorem e124c_cov {g₀ f₀ h K : ℂ → ℂ} {k ε : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hg₀ : IsBeltramiCoeff g₀ univ k) (hf₀ : IsNormalizedSolution f₀ g₀)
    (hh : IsBeltramiCoeff h univ ε) (hKm : Measurable K) :
    ∫ w, ahT_dot h g₀ f₀ w * K w = ∫ u, h u * K (f₀ u) * dz f₀ u ^ 2 := by
  obtain ⟨⟨K₀, hK⟩, himg, -, -, hdil⟩ := hf₀
  have hq : IsQuasiconformal f₀ univ := ⟨K₀, hK⟩
  have hdot := QCV.qcv_dot_beltrami hk₀ hk hg₀ hq himg hh
  have hmeasG : AEStronglyMeasurable (fun ζ => ahT_dot h g₀ f₀ ζ * K ζ) volume := by
    have h1 : AEStronglyMeasurable (ahT_dot h g₀ f₀) volume := by
      simpa [Measure.restrict_univ] using hdot.1
    exact h1.mul hKm.aestronglyMeasurable
  rw [QCV.qcv_cov_integral hK himg _ hmeasG]
  refine integral_congr_ae ?_
  have hJ := thm9_6_cor2_jacobian_pos hK
  rw [Measure.restrict_univ] at hJ
  have hg0b := hg₀.2
  rw [Measure.restrict_univ] at hg0b
  have hinj : InjOn f₀ univ := hK.2.2.1.2.1
  filter_upwards [hJ, hdil, hg0b] with u hJu hdu hgu
  have hφ : Function.invFunOn f₀ univ (f₀ u) = u := hinj.leftInvOn_invFunOn (mem_univ u)
  have hdzne : dz f₀ u ≠ 0 := by
    intro h0
    have : jacobian f₀ u ≤ 0 := by
      unfold jacobian
      rw [h0]
      simp
    linarith
  have hdzbar : dzbar f₀ u = g₀ u * dz f₀ u := by
    unfold complexDilatation at hdu
    rw [div_eq_iff hdzne] at hdu
    rw [hdu]
  have hA : (1 : ℂ) - conj (g₀ u) * g₀ u ≠ 0 := by
    have : ‖conj (g₀ u) * g₀ u‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg (g₀ u)]
    intro h0
    have h1 : conj (g₀ u) * g₀ u = 1 := by linear_combination -h0
    rw [h1] at this; simp at this
  have hJc : (jacobian f₀ u : ℂ) = dz f₀ u * conj (dz f₀ u) * (1 - conj (g₀ u) * g₀ u) := by
    unfold jacobian
    rw [hdzbar, norm_mul]
    push_cast
    rw [Complex.mul_conj, mul_comm (conj (g₀ u)) (g₀ u), Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    push_cast
    ring
  have hcne : conj (dz f₀ u) ≠ 0 := (map_ne_zero _).2 hdzne
  simp only [ahT_dot, hφ]
  rw [ENNReal.toReal_ofReal hJu.le, Complex.real_smul, hJc]
  field_simp

/-- The image-plane truncated integral of `ν̇ · K₁` is the `v`-plane integral over `𝕌 ∖ f⁻¹(B(f z, δ))`. -/
theorem e124c_pv_image {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ} (hns : IsNormalizedSolution f (extU fun y => ε * μ y))
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    ∫ η in {η : ℂ | δ < ‖η - f z‖},
        ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f η * QCV.kerD1 (f z) η =
      ∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
        (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2 := by
  set a := f z with had
  set g₀ : ℂ → ℂ := extU fun y => ε * μ y with hg₀d
  have hg₀ : IsBeltramiCoeff g₀ univ (‖ε‖ * k) := e124c_extU_beltrami hk hμ ε
  have hk0 : 0 ≤ ‖ε‖ * k := by positivity
  obtain ⟨⟨K₀, hK⟩, himg, hf0, hf1, hdl⟩ := hns
  have hfc : Continuous f := continuousOn_univ.1 hK.2.2.1.1
  have hinj : InjOn f univ := hK.2.2.1.2.1
  have hsurj : ∀ η, f (Function.invFunOn f univ η) = η := by
    intro η
    have hex : ∃ x ∈ (univ : Set ℂ), f x = η := by
      have : η ∈ f '' univ := by rw [himg]; exact mem_univ η
      obtain ⟨x, -, hx⟩ := this
      exact ⟨x, mem_univ x, hx⟩
    exact Function.invFunOn_eq hex
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  have hmB : MeasurableSet (f ⁻¹' ball a δ) := (isOpen_ball.preimage hfc).measurableSet
  set h' : ℂ → ℂ := (f ⁻¹' ball a δ)ᶜ.indicator (upperHalf.indicator μ) with hh'd
  have hh' : IsBeltramiCoeff h' univ k :=
    vf_indicator_coeff hk (vf_zero_extension_coeff hk hμ) hmB.compl
  have hKm : Measurable (QCV.kerD1 a) := by unfold QCV.kerD1; fun_prop
  -- sphere is null: strict vs non-strict truncation
  have hS : {η : ℂ | δ < ‖η - a‖} =ᵐ[volume] (ball a δ)ᶜ := by
    have hsph : volume (sphere a δ) = 0 := Measure.addHaar_sphere volume a δ
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsph] with η hη
    have hη' : ‖η - a‖ ≠ δ := by
      intro he
      exact hη (show dist η a = δ by rw [dist_eq_norm]; exact he)
    apply propext
    show δ < ‖η - a‖ ↔ η ∉ ball a δ
    rw [mem_ball, dist_eq_norm, not_lt]
    constructor
    · exact fun h => h.le
    · exact fun h => lt_of_le_of_ne h (Ne.symm hη')
  rw [setIntegral_congr_set hS, ← integral_indicator measurableSet_ball.compl]
  have hpt : ∀ η, (ball a δ)ᶜ.indicator
      (fun η => ahT_dot (upperHalf.indicator μ) g₀ f η * QCV.kerD1 a η) η =
      ahT_dot h' g₀ f η * QCV.kerD1 a η := by
    intro η
    have hfi := hsurj η
    by_cases hη : η ∈ (ball a δ)ᶜ
    · rw [indicator_of_mem hη]
      have hm : Function.invFunOn f univ η ∈ (f ⁻¹' ball a δ)ᶜ := by
        show f (Function.invFunOn f univ η) ∉ ball a δ
        rw [hfi]
        exact hη
      simp only [ahT_dot, hh'd, indicator_of_mem hm]
    · rw [indicator_of_notMem hη]
      have hm : Function.invFunOn f univ η ∉ (f ⁻¹' ball a δ)ᶜ := by
        intro h0
        apply hη
        have h1 : f (Function.invFunOn f univ η) ∉ ball a δ := h0
        rw [hfi] at h1
        exact h1
      simp only [ahT_dot, hh'd, indicator_of_notMem hm, zero_div, zero_mul]
  simp only [hpt]
  rw [e124c_cov hk0 hε hg₀ ⟨⟨K₀, hK⟩, himg, hf0, hf1, hdl⟩ hh' hKm,
    ← integral_indicator (hmU.diff hmB)]
  congr 1
  funext v
  by_cases hv : v ∈ upperHalf \ f ⁻¹' ball a δ
  · rw [indicator_of_mem hv]
    have hc : v ∈ (f ⁻¹' ball a δ)ᶜ := hv.2
    rw [hh'd, indicator_of_mem hc, indicator_of_mem hv.1]
    have hv0 : f v ≠ 0 := by
      intro h0
      have : v = 0 := hinj (mem_univ v) (mem_univ 0) (by rw [h0, hf0])
      have hvi : 0 < v.im := hv.1
      rw [this, Complex.zero_im] at hvi
      exact lt_irrefl 0 hvi
    have hv1 : f v - 1 ≠ 0 := by
      intro h0
      have : v = 1 := hinj (mem_univ v) (mem_univ 1) (by rw [hf1]; linear_combination h0)
      have hvi : 0 < v.im := hv.1
      rw [this, Complex.one_im] at hvi
      exact lt_irrefl 0 hvi
    unfold QCV.kerD1
    field_simp
    ring
  · rw [indicator_of_notMem hv]
    have h0 : h' v = 0 := by
      rw [hh'd]
      by_cases hc : v ∈ (f ⁻¹' ball a δ)ᶜ
      · rw [indicator_of_mem hc, indicator_of_notMem (fun hu => hv ⟨hu, hc⟩)]
      · rw [indicator_of_notMem hc]
    rw [h0, zero_mul, zero_mul]

/-- **Chain term.** `∂_z ẇ(z)` is the image-plane principal value plus the local term from `G_ζ̄`. -/
theorem e124_chain {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun y => -(1 / π) * ∫ v in upperHalf, kernelRU (f y) (f v) * μ v * dz f v ^ 2) z =
      -(1 / π) * limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
          dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) +
        μ z * dz f z * conj (complexDilatation f z) / (1 - ‖complexDilatation f z‖ ^ 2) := by
  obtain ⟨hns, hC, hJ, hdil⟩ := e124c_setup hk hμ hμs hε hf
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hmU : MeasurableSet upperHalf := hU.measurableSet
  set g₀ : ℂ → ℂ := extU fun y => ε * μ y with hg₀d
  set ν : ℂ → ℂ := ahT_dot (upperHalf.indicator μ) g₀ f with hνd
  have hg₀ : IsBeltramiCoeff g₀ univ (‖ε‖ * k) := e124c_extU_beltrami hk hμ ε
  have hk0 : 0 ≤ ‖ε‖ * k := by positivity
  have hh := vf_zero_extension_coeff hk hμ
  have hνB : IsBeltramiCoeff ν univ (k / (1 - (‖ε‖ * k) ^ 2)) :=
    QCV.qcv_dot_beltrami hk0 hε hg₀ hns.1 hns.2.1 hh
  have hk' : 0 ≤ k / (1 - (‖ε‖ * k) ^ 2) := div_nonneg hk (by nlinarith)
  -- `ẇ = V[ν̇] ∘ f`
  have hW : (fun y => -(1 / π) * ∫ v in upperHalf, kernelRU (f y) (f v) * μ v * dz f v ^ 2) =
      ahVar ν ∘ f := by
    funext y
    rw [Function.comp_apply, QCV.qcv_var_source hk0 hε hg₀ hns hh (f y), ← integral_indicator hmU]
    congr 1
    congr 1
    funext v
    by_cases hv : v ∈ upperHalf
    · rw [indicator_of_mem hv, indicator_of_mem hv]
      simp only [kernelRU, ahKer]
      ring
    · rw [indicator_of_notMem hv, indicator_of_notMem hv]
      ring
  obtain ⟨R, hR, χ, hχ, hχc, hχ01, hχ1, -, hω⟩ := e124c_cutoff hμs hns hC hJ hdil hz
  obtain ⟨hGd, hGbar, hGlim⟩ := e124c_G hk' hνB hR hχ hχc hχ01 hχ1 hω
  have hfd : DifferentiableAt ℝ f z := (hC.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  rw [hW, eq6_2_dz_comp hfd hGd, ← (eq6_3 hfd).2, hGbar]
  -- the local term
  have hinj : InjOn f univ := hns.1.choose_spec.2.2.1.2.1
  have hiz : Function.invFunOn f univ (f z) = z := hinj.leftInvOn_invFunOn (mem_univ z)
  have hdz0 : dz f z ≠ 0 := by
    intro h0
    have := hJ z hz
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f z)]
  set κ := complexDilatation f z with hκd
  have hlt : ‖κ‖ < 1 := by
    have hJz := hJ z hz
    unfold jacobian at hJz
    show ‖dzbar f z / dz f z‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hdz0)]
    nlinarith [norm_nonneg (dzbar f z), norm_nonneg (dz f z)]
  have hloc : ν (f z) * conj (dzbar f z) = μ z * dz f z * conj κ / (1 - (‖κ‖ : ℂ) ^ 2) := by
    have hdzbar : dzbar f z = κ * dz f z := by
      show dzbar f z = dzbar f z / dz f z * dz f z
      field_simp
    have hg : g₀ z = κ := by
      rw [hκd, hdil z hz, hg₀d]
      unfold extU
      rw [if_pos (show 0 < z.im from hz)]
    show upperHalf.indicator μ (Function.invFunOn f univ (f z)) /
        (1 - conj (g₀ (Function.invFunOn f univ (f z))) * g₀ (Function.invFunOn f univ (f z))) *
        (dz f (Function.invFunOn f univ (f z)) / conj (dz f (Function.invFunOn f univ (f z)))) *
        conj (dzbar f z) = _
    rw [hiz, indicator_of_mem hz, hg, hdzbar, map_mul, Complex.conj_mul']
    have hd1 : (1 : ℂ) - (‖κ‖ : ℂ) ^ 2 ≠ 0 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.2 (by nlinarith [norm_nonneg κ])
    have hcd : conj (dz f z) ≠ 0 := (map_ne_zero _).2 hdz0
    field_simp
  -- the principal-value term
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hI : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
      (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * dz (ahVar ν) (f z))) := by
    refine (hGlim.const_mul (-(π : ℂ))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← e124c_pv_image hk hμ hε hns (show (0 : ℝ) < δ from hδ)]
    field_simp
    rfl
  have hlim : limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
      dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) =
      dz f z * (-(π : ℂ) * dz (ahVar ν) (f z)) := by
    apply Tendsto.limUnder_eq
    refine (hI.const_mul (dz f z)).congr' (Eventually.of_forall fun δ => ?_)
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [hlim, hloc]
  have he : -(1 / π : ℂ) * (dz f z * (-(π : ℂ) * dz (ahVar ν) (f z))) = dz (ahVar ν) (f z) * dz f z := by
    field_simp
  rw [he]

/-- The image-plane kernel `K(ζ) = (ζ - a)⁻² + ζ⁻¹ - (ζ - 1)⁻¹ = ((2a - 1)ζ - a²)/((ζ - a)² ζ (ζ - 1))` is integrable
off every disc around `a`: there it is dominated by a multiple of `|ζ|⁻¹|ζ - 1|⁻¹(1 + |ζ|)⁻¹`. -/
theorem e124p_kernel_int (a : ℂ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun ζ : ℂ => 1 / (ζ - a) ^ 2 + 1 / ζ - 1 / (ζ - 1)) (ball a η)ᶜ := by
  set B1 : ℝ := ‖2 * a - 1‖ * (1 + ‖a‖) + ‖a‖ ^ 2 with hB1
  set C : ℝ := B1 * (1 + ‖a‖) * (1 / η + 1) ^ 2 with hCd
  have hM := (phiKernel_majorant_integrable.const_mul C).integrableOn (s := (ball a η)ᶜ)
  have hKm : Measurable fun ζ : ℂ => 1 / (ζ - a) ^ 2 + 1 / ζ - 1 / (ζ - 1) := by fun_prop
  refine hM.mono' hKm.aestronglyMeasurable ?_
  have h0 : ∀ᵐ ζ : ℂ, ζ ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have h1 : ∀ᵐ ζ : ℂ, ζ ≠ 1 := compl_mem_ae_iff.mpr (measure_singleton 1)
  filter_upwards [ae_restrict_mem measurableSet_ball.compl, ae_restrict_of_ae h0, ae_restrict_of_ae h1]
    with ζ hζ hz0 hz1
  have hsη : η ≤ ‖ζ - a‖ := by
    rw [← dist_eq_norm]; exact not_lt.mp hζ
  set s := ‖ζ - a‖ with hsd
  have hs0 : 0 < s := hη.trans_le hsη
  have hza : ζ - a ≠ 0 := norm_pos_iff.mp hs0
  have hz1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hn0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hz0
  have hn1 : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr hz1'
  have hK : 1 / (ζ - a) ^ 2 + 1 / ζ - 1 / (ζ - 1) = ((2 * a - 1) * ζ - a ^ 2) / ((ζ - a) ^ 2 * ζ * (ζ - 1)) := by
    field_simp; ring
  -- `|num| (1 + |ζ|) ≤ C s²`
  have hN : ‖(2 * a - 1) * ζ - a ^ 2‖ ≤ B1 * (1 + s) := by
    have hz : ‖ζ‖ ≤ ‖a‖ + s := by
      have := norm_add_le (ζ - a) a
      rw [sub_add_cancel] at this; linarith
    have := norm_sub_le ((2 * a - 1) * ζ) (a ^ 2)
    rw [norm_mul, norm_pow] at this
    have h2 := mul_le_mul_of_nonneg_left hz (norm_nonneg (2 * a - 1))
    have h3 : 0 ≤ ‖2 * a - 1‖ * (1 + ‖a‖ * s) := by positivity
    have h4 : 0 ≤ ‖a‖ ^ 2 * s := by positivity
    rw [hB1]
    nlinarith
  have hZ : 1 + ‖ζ‖ ≤ (1 + ‖a‖) * (1 + s) := by
    have := norm_add_le (ζ - a) a
    rw [sub_add_cancel] at this
    nlinarith [norm_nonneg a, hs0.le]
  have hs1 : 1 + s ≤ (1 / η + 1) * s := by
    have : 1 ≤ s / η := (one_le_div hη).mpr hsη
    have e : (1 / η + 1) * s = s / η + s := by ring
    linarith
  have hcore : ‖(2 * a - 1) * ζ - a ^ 2‖ * (1 + ‖ζ‖) ≤ C * s ^ 2 := by
    calc _ ≤ (B1 * (1 + s)) * ((1 + ‖a‖) * (1 + s)) :=
          mul_le_mul hN hZ (by positivity) (by positivity)
      _ = B1 * (1 + ‖a‖) * (1 + s) ^ 2 := by ring
      _ ≤ B1 * (1 + ‖a‖) * ((1 / η + 1) * s) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs1 2) (by positivity)
      _ = C * s ^ 2 := by rw [hCd]; ring
  rw [hK, norm_div, norm_mul, norm_mul, norm_pow, ← hsd]
  have hpos : 0 < s ^ 2 * ‖ζ‖ * ‖ζ - 1‖ := mul_pos (mul_pos (pow_pos hs0 2) hn0) hn1
  rw [div_le_iff₀ hpos]
  have hz2 : 0 < 1 + ‖ζ‖ := by positivity
  have e : C * (‖ζ‖⁻¹ * ‖ζ - 1‖⁻¹ * (1 + ‖ζ‖)⁻¹) * (s ^ 2 * ‖ζ‖ * ‖ζ - 1‖) = C * s ^ 2 / (1 + ‖ζ‖) := by
    field_simp
  rw [e, le_div_iff₀ hz2]
  exact hcore

/-- The `v`-plane integrand is integrable on every measurable `S ⊆ 𝕌` whose image stays a fixed distance away
from `f z` (change of variables `ζ = f v`, `|μ| |f_v|² ≤ k J_f/(1 - (|ε|k)²)`, and `e124p_kernel_int`). -/
theorem e124p_int_on {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ upperHalf)
    {η : ℝ} (hη : 0 < η) (hav : ∀ v ∈ S, η ≤ ‖f v - f z‖) :
    IntegrableOn (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) S := by
  obtain ⟨hns, hC, hJ, hcd⟩ := e124c_setup hk hμ hμs hε hf
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨⟨K, hK⟩, hs, h0, h1, -⟩ := hns
  have hi : Function.Injective f := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hfc : Continuous f := he ▸ e.continuous
  have hd : ∀ v ∈ upperHalf, DifferentiableAt ℝ f v := fun v hv =>
    (hC.contDiffAt (hU.mem_nhds hv)).differentiableAt (by norm_num)
  -- the image-plane kernel is integrable on `f '' S`
  have hKi : IntegrableOn (fun ζ : ℂ => 1 / (ζ - f z) ^ 2 + 1 / ζ - 1 / (ζ - 1)) (f '' S) := by
    refine (e124p_kernel_int (f z) hη).mono_set ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
    exact hav v hv
  have hder : ∀ v ∈ S, HasFDerivWithinAt f (fderiv ℝ f v) S v := fun v hv =>
    (hd v (hSU hv)).hasFDerivAt.hasFDerivWithinAt
  have hcv := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hder hi.injOn _).mp hKi
  -- continuity of the integrand on `S`
  have hne : ∀ v ∈ S, f v - f z ≠ 0 := fun v hv h => by
    have := hav v hv
    rw [h, norm_zero] at this
    linarith
  have him : ∀ v ∈ S, v ≠ 0 ∧ v ≠ 1 := fun v hv => by
    have h' : 0 < v.im := hSU hv
    exact ⟨fun h => by rw [h, Complex.zero_im] at h'; exact lt_irrefl _ h',
      fun h => by rw [h, Complex.one_im] at h'; exact lt_irrefl _ h'⟩
  have hf0 : ∀ v ∈ S, f v ≠ 0 := fun v hv h => (him v hv).1 (hi (h.trans h0.symm))
  have hf1 : ∀ v ∈ S, f v - 1 ≠ 0 := fun v hv h => (him v hv).2 (hi ((sub_eq_zero.mp h).trans h1.symm))
  have hfd : ContinuousOn (fderiv ℝ f) upperHalf := hC.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdzc : ContinuousOn (dz f) upperHalf := by
    have e1 : dz f = fun y => (fderiv ℝ f y 1 - I * fderiv ℝ f y I) / 2 := rfl
    rw [e1]
    exact ((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hfd.clm_apply continuousOn_const))).div_const _
  have hKc : ContinuousOn (fun v => 1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) S :=
    ((continuousOn_const.div ((hfc.continuousOn.sub continuousOn_const).pow 2)
      (fun v hv => pow_ne_zero 2 (hne v hv))).add (continuousOn_const.div hfc.continuousOn hf0)).sub
      (continuousOn_const.div (hfc.continuousOn.sub continuousOn_const) hf1)
  have hgc : ContinuousOn (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) S :=
    ((continuousOn_const.mul hKc).mul (hμs.continuousOn.mono hSU)).mul ((hdzc.mono hSU).pow 2)
  -- the pointwise bound
  set q : ℝ := ‖ε‖ * k with hqd
  have hq0 : 0 ≤ q := by positivity
  have hq : 0 < 1 - q ^ 2 := by nlinarith
  refine (hcv.norm.const_mul (‖dz f z‖ * (k / (1 - q ^ 2)))).mono' (hgc.aestronglyMeasurable hS) ?_
  filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae_restrict_of_subset hSU hμ.2] with v hv hμv
  have hvU := hSU hv
  have hJv : 0 < jacobian f v := hJ v hvU
  have hdet : |(fderiv ℝ f v).det| = jacobian f v := by
    rw [show (fderiv ℝ f v).det = jacobian f v from det_fderiv_eq_jacobian (hd v hvU), abs_of_pos hJv]
  have hdz0 : dz f v ≠ 0 := by
    intro h
    have := hJv
    unfold jacobian at this
    rw [h, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f v)]
  have hdzb : ‖dzbar f v‖ ≤ q * ‖dz f v‖ := by
    have e2 : dzbar f v = complexDilatation f v * dz f v := (div_mul_cancel₀ _ hdz0).symm
    rw [e2, hcd v hvU, norm_mul, norm_mul, hqd]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμv (norm_nonneg _)) (norm_nonneg _)
  have hJb : (1 - q ^ 2) * ‖dz f v‖ ^ 2 ≤ jacobian f v := by
    unfold jacobian
    have := pow_le_pow_left₀ (norm_nonneg _) hdzb 2
    nlinarith
  have hdz2 : ‖dz f v‖ ^ 2 ≤ jacobian f v / (1 - q ^ 2) := by
    rw [le_div_iff₀ hq]; linarith
  rw [norm_smul, hdet, Real.norm_of_nonneg hJv.le, norm_mul, norm_mul, norm_mul, norm_pow]
  calc ‖dz f z‖ * ‖1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)‖ * ‖μ v‖ * ‖dz f v‖ ^ 2
      ≤ ‖dz f z‖ * ‖1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)‖ * k * (jacobian f v / (1 - q ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hμv (by positivity)) hdz2 (by positivity)
          (mul_nonneg (by positivity) hk)
    _ = ‖dz f z‖ * (k / (1 - q ^ 2)) * (jacobian f v * ‖1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)‖) := by
        ring

/-- The `v`-plane integrand is integrable on `𝕌` minus a disc around `z`, and minus a preimage disc around `f z`. -/
theorem e124p_integrable {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2)
        (upperHalf \ ball z δ) ∧
      IntegrableOn (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2)
        (upperHalf \ f ⁻¹' ball (f z) δ) := by
  obtain ⟨hns, -, -, -⟩ := e124c_setup hk hμ hμs hε hf
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hns
  have hi : Function.Injective f := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hfc : Continuous f := he ▸ e.continuous
  refine ⟨?_, ?_⟩
  · -- `f(B(z, δ))` is an open neighbourhood of `f z`
    have hopen : IsOpen (f '' ball z δ) := by
      rw [← he]; exact e.isOpenMap _ isOpen_ball
    obtain ⟨η, hη, hb⟩ := Metric.isOpen_iff.mp hopen (f z) ⟨z, mem_ball_self hδ, rfl⟩
    refine e124p_int_on hk hμ hμs hε hf z (hU.measurableSet.diff measurableSet_ball) diff_subset hη ?_
    intro v hv
    by_contra hlt
    rw [not_le, ← dist_eq_norm] at hlt
    obtain ⟨w, hw, hwv⟩ := hb hlt
    exact hv.2 (hi hwv ▸ hw)
  · refine e124p_int_on hk hμ hμs hε hf z (hU.measurableSet.diff (hfc.measurable measurableSet_ball))
      diff_subset hδ ?_
    intro v hv
    have := hv.2
    rw [mem_preimage, mem_ball, dist_eq_norm, not_lt] at this
    exact this

/-- A function `C¹` at `z` is Lipschitz on a ball around `z`. -/
theorem e124p_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℂ → E} {z : ℂ}
    (hF : ContDiffAt ℝ 1 F z) :
    ∃ ρ > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ball z ρ, ∀ y ∈ ball z ρ, ‖F x - F y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨K, t, ht, hL⟩ := hF.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨ρ, hρ, K, K.2, fun x hx y hy => ?_⟩
  have := hL.dist_le_mul x (hb hx) y (hb hy)
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- First-order Taylor bound from a Lipschitz derivative. -/
theorem e124p_taylor {f : ℂ → ℂ} {z : ℂ} {ρ L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x ∈ ball z ρ, DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ ball z ρ, ‖fderiv ℝ f x - fderiv ℝ f z‖ ≤ L * ‖x - z‖) {h : ℂ} (hh : ‖h‖ < ρ) :
    ‖f (z + h) - f z - fderiv ℝ f z h‖ ≤ L * ‖h‖ ^ 2 := by
  have hs : closedBall z ‖h‖ ⊆ ball z ρ := closedBall_subset_ball hh
  have hder : ∀ x ∈ closedBall z ‖h‖, HasFDerivWithinAt (fun y => f y - fderiv ℝ f z y)
      (fderiv ℝ f x - fderiv ℝ f z) (closedBall z ‖h‖) x := fun x hx =>
    ((hd x (hs hx)).hasFDerivAt.sub (fderiv ℝ f z).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ x ∈ closedBall z ‖h‖, ‖fderiv ℝ f x - fderiv ℝ f z‖ ≤ L * ‖h‖ := fun x hx =>
    (hl x (hs hx)).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hx) hL)
  have hm : z + h ∈ closedBall z ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := (convex_closedBall z ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd
    (mem_closedBall_self (norm_nonneg h)) hm
  have e : f (z + h) - f z - fderiv ℝ f z h =
      (f (z + h) - fderiv ℝ f z (z + h)) - (f z - fderiv ℝ f z z) := by
    rw [map_add]; abel
  rw [e]
  rw [add_sub_cancel_left] at this
  calc _ ≤ L * ‖h‖ * ‖h‖ := this
    _ = L * ‖h‖ ^ 2 := by ring

/-- Wirtinger form of a real-linear map of `ℂ`. -/
theorem e124p_wirt (L : ℂ →L[ℝ] ℂ) (h : ℂ) :
    L h = (L 1 - I * L I) / 2 * h + (L 1 + I * L I) / 2 * conj h := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, h = a + b * I := ⟨h.re, h.im, (Complex.re_add_im h).symm⟩
  have e : (a : ℂ) + b * I = a • (1 : ℂ) + b • I := by simp [Complex.real_smul]
  rw [e, map_add, map_smul, map_smul]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, mul_one]
  linear_combination (b * L I) * Complex.I_sq

/-- `|D⁻² - M⁻²| = |M - D||M + D|/(|D|²|M|²)`, with lower bounds on `|D|`, `|M|`. -/
theorem e124p_inv_sq {D M : ℂ} {t c e A : ℝ} (ht : 0 < t) (hc : 0 < c) (hD : c / 2 * t ≤ ‖D‖)
    (hM : c * t ≤ ‖M‖) (hE : ‖M - D‖ ≤ e) (hS : ‖M + D‖ ≤ A) :
    ‖1 / D ^ 2 - 1 / M ^ 2‖ ≤ e * A / ((c / 2 * t) ^ 2 * (c * t) ^ 2) := by
  have h1 : 0 < c / 2 * t := by positivity
  have h2 : 0 < c * t := by positivity
  have hD0 : D ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le h1 hD)
  have hM0 : M ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le h2 hM)
  have e1 : 1 / D ^ 2 - 1 / M ^ 2 = (M - D) * (M + D) / (D ^ 2 * M ^ 2) := by
    field_simp; ring
  rw [e1, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  exact div_le_div₀ (mul_nonneg ((norm_nonneg _).trans hE) ((norm_nonneg _).trans hS)) (mul_le_mul hE hS (norm_nonneg _) ((norm_nonneg _).trans hE))
    (by positivity) (mul_le_mul (pow_le_pow_left₀ h1.le hD 2) (pow_le_pow_left₀ h2.le hM 2)
      (by positivity) (by positivity))

/-- The model-singularity estimate of `e124p_local` at one point `z + h`: with `F = f(z+h)`, `F₀ = f z`,
`P = μ(z+h) f_z(z+h)²`, the integrand minus `μ(z)α/(h + κh̄)²` is `O(1/|h|)`. -/
theorem e124p_model_bound {α κ h F F0 μ0 μ1 a1 : ℂ} {L1 L2 Rz r c0 : ℝ}
    (hα : α ≠ 0) (hκ : ‖κ‖ < 1) (hc0d : c0 = ‖α‖ * (1 - ‖κ‖)) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hRz : 0 ≤ Rz)
    (hh0 : 0 < ‖h‖) (hhr : ‖h‖ < r) (h4 : L1 * ‖h‖ ≤ c0 / 2)
    (hEt : ‖F - F0 - α * (h + κ * conj h)‖ ≤ L1 * ‖h‖ ^ 2)
    (hP : ‖μ1 * a1 ^ 2 - μ0 * α ^ 2‖ ≤ L2 * ‖h‖)
    (hRb : ‖1 / F - 1 / (F - 1)‖ ≤ Rz + 1) :
    ‖α * (1 / (F - F0) ^ 2 + 1 / F - 1 / (F - 1)) * μ1 * a1 ^ 2 - μ0 * α * ((h + κ * conj h) ^ 2)⁻¹‖ ≤
      (L1 + ‖α‖ * (4 * L2 / c0 ^ 2) + ‖α‖ * ‖μ0 * α ^ 2‖ * (20 * L1 * ‖α‖ / c0 ^ 4) +
        ‖α‖ * (Rz + 1) * (‖μ0 * α ^ 2‖ + L2 * r) * r) / ‖h‖ := by
  have hαp : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hc0 : 0 < c0 := by rw [hc0d]; exact mul_pos hαp (by linarith)
  have hc0α : c0 ≤ ‖α‖ := by rw [hc0d]; nlinarith [norm_nonneg κ]
  have hc0ne : c0 ≠ 0 := hc0.ne'
  have ht0 : ‖h‖ ≠ 0 := hh0.ne'
  have hr : 0 < r := hh0.trans hhr
  set t := ‖h‖ with htd
  set Lh := h + κ * conj h with hLhd
  set D := F - F0 with hDd
  set M := α * Lh with hMd
  set Pz := ‖μ0 * α ^ 2‖ with hPzd
  have hLlo : (1 - ‖κ‖) * t ≤ ‖Lh‖ := by
    have := norm_sub_norm_le h (-(κ * conj h))
    rw [norm_neg, norm_mul, Complex.norm_conj, sub_neg_eq_add] at this
    nlinarith
  have hLhi : ‖Lh‖ ≤ 2 * t := by
    have := norm_add_le h (κ * conj h)
    rw [norm_mul, Complex.norm_conj] at this
    nlinarith [norm_nonneg κ]
  have hLh0 : Lh ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (by linarith) hh0) hLlo)
  have hMlo : c0 * t ≤ ‖M‖ := by
    rw [hMd, norm_mul, hc0d, mul_assoc]
    exact mul_le_mul_of_nonneg_left hLlo (norm_nonneg _)
  have hMhi : ‖M‖ ≤ 2 * ‖α‖ * t := by
    calc ‖M‖ = ‖α‖ * ‖Lh‖ := by rw [hMd, norm_mul]
      _ ≤ ‖α‖ * (2 * t) := mul_le_mul_of_nonneg_left hLhi (norm_nonneg _)
      _ = 2 * ‖α‖ * t := by ring
  have hEs : ‖D - M‖ ≤ c0 / 2 * t :=
    hEt.trans (by rw [pow_two, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 hh0.le)
  have hDlo : c0 / 2 * t ≤ ‖D‖ := by
    have := norm_sub_le D (D - M)
    rw [sub_sub_cancel] at this
    linarith
  have hS : ‖M + D‖ ≤ 5 * ‖α‖ * t := by
    have := norm_add_le (2 * M) (D - M)
    rw [show 2 * M + (D - M) = M + D by ring, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    have h3 : c0 / 2 * t ≤ ‖α‖ * t := mul_le_mul_of_nonneg_right (by linarith) hh0.le
    linarith
  have hinv := e124p_inv_sq (e := L1 * t ^ 2) (A := 5 * ‖α‖ * t) hh0 hc0 hDlo hMlo
    (by rw [norm_sub_rev]; exact hEt) hS
  have hinv' : ‖1 / D ^ 2 - 1 / M ^ 2‖ ≤ 20 * L1 * ‖α‖ / c0 ^ 4 / t := by
    refine hinv.trans (le_of_eq ?_)
    field_simp
    ring
  have hPb : ‖μ1 * a1 ^ 2‖ ≤ Pz + L2 * r := by
    have := norm_le_insert' (μ1 * a1 ^ 2) (μ0 * α ^ 2)
    linarith [mul_le_mul_of_nonneg_left hhr.le hL2]
  have hh1 : 0 < c0 / 2 * t := mul_pos (half_pos hc0) hh0
  have hXb : ‖1 / D ^ 2‖ ≤ 1 / (c0 / 2 * t) ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (pow_pos hh1 2) (pow_le_pow_left₀ hh1.le hDlo 2)
  have hmod : μ0 * α * (Lh ^ 2)⁻¹ = α * (μ0 * α ^ 2) * (1 / M ^ 2) := by
    rw [hMd]; field_simp
  have hdec : α * (1 / D ^ 2 + 1 / F - 1 / (F - 1)) * μ1 * a1 ^ 2 - μ0 * α * (Lh ^ 2)⁻¹ =
      α * (1 / D ^ 2) * (μ1 * a1 ^ 2 - μ0 * α ^ 2) + α * (μ0 * α ^ 2) * (1 / D ^ 2 - 1 / M ^ 2) +
        α * (1 / F - 1 / (F - 1)) * (μ1 * a1 ^ 2) := by
    rw [hmod]; ring
  rw [hdec]
  have hT1 : ‖α * (1 / D ^ 2) * (μ1 * a1 ^ 2 - μ0 * α ^ 2)‖ ≤ ‖α‖ * (4 * L2 / c0 ^ 2) / t := by
    rw [norm_mul, norm_mul]
    calc _ ≤ ‖α‖ * (1 / (c0 / 2 * t) ^ 2) * (L2 * t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hXb (norm_nonneg _)) hP (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (by positivity))
      _ = ‖α‖ * (4 * L2 / c0 ^ 2) / t := by field_simp; ring
  have hT2 : ‖α * (μ0 * α ^ 2) * (1 / D ^ 2 - 1 / M ^ 2)‖ ≤ ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4) / t := by
    rw [norm_mul, norm_mul]
    calc _ ≤ ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4 / t) :=
          mul_le_mul_of_nonneg_left hinv' (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4) / t := by ring
  have hK3 : 0 ≤ ‖α‖ * (Rz + 1) * (Pz + L2 * r) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (by linarith)) (add_nonneg (norm_nonneg _) (mul_nonneg hL2 hr.le))
  have hT3 : ‖α * (1 / F - 1 / (F - 1)) * (μ1 * a1 ^ 2)‖ ≤ ‖α‖ * (Rz + 1) * (Pz + L2 * r) * r / t := by
    rw [norm_mul, norm_mul]
    have hK : ‖α‖ * ‖1 / F - 1 / (F - 1)‖ * ‖μ1 * a1 ^ 2‖ ≤ ‖α‖ * (Rz + 1) * (Pz + L2 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hRb (norm_nonneg _)) hPb (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (by linarith))
    refine hK.trans ?_
    rw [le_div_iff₀ hh0]
    exact mul_le_mul_of_nonneg_left hhr.le hK3
  have hsum := (norm_add₃_le (a := α * (1 / D ^ 2) * (μ1 * a1 ^ 2 - μ0 * α ^ 2))
    (b := α * (μ0 * α ^ 2) * (1 / D ^ 2 - 1 / M ^ 2)) (c := α * (1 / F - 1 / (F - 1)) * (μ1 * a1 ^ 2)))
  have hL1t : 0 ≤ L1 / t := div_nonneg hL1 hh0.le
  have he : (L1 + ‖α‖ * (4 * L2 / c0 ^ 2) + ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4) +
      ‖α‖ * (Rz + 1) * (Pz + L2 * r) * r) / t = L1 / t + ‖α‖ * (4 * L2 / c0 ^ 2) / t +
        ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4) / t + ‖α‖ * (Rz + 1) * (Pz + L2 * r) * r / t := by ring
  rw [he]
  linarith

/-- `C²` expansion at `z`: the linearization `α(h + κh̄)` of `f` and the model singularity `αμ(z)/(h + κh̄)²` of the
integrand, with `α ≠ 0` and `|κ| < 1` (W-REG E2/E3). -/
theorem e124p_local {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    dz f z ≠ 0 ∧ ‖complexDilatation f z‖ < 1 ∧ ∃ r > 0, ∃ C : ℝ, ball z r ⊆ upperHalf ∧
      ∀ h : ℂ, 0 < ‖h‖ → ‖h‖ < r →
        ‖f (z + h) - f z - dz f z * (h + complexDilatation f z * conj h)‖ ≤ C * ‖h‖ ^ 2 ∧
        ‖dz f z * (1 / (f (z + h) - f z) ^ 2 + 1 / f (z + h) - 1 / (f (z + h) - 1)) * μ (z + h) *
            dz f (z + h) ^ 2 - μ z * dz f z * ((h + complexDilatation f z * conj h) ^ 2)⁻¹‖ ≤ C / ‖h‖ := by
  obtain ⟨hns, hC, hJ, -⟩ := e124c_setup hk hμ hμs hε hf
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hJz : 0 < ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := hJ z hz
  have hα : dz f z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hJz
    nlinarith [norm_nonneg (dzbar f z)]
  have hαp : 0 < ‖dz f z‖ := norm_pos_iff.mpr hα
  have hdzb : dzbar f z = complexDilatation f z * dz f z := (div_mul_cancel₀ _ hα).symm
  have hκ : ‖complexDilatation f z‖ < 1 := by
    have h1 : ‖dzbar f z‖ < ‖dz f z‖ := by nlinarith [norm_nonneg (dzbar f z), norm_nonneg (dz f z)]
    rw [show complexDilatation f z = dzbar f z / dz f z from rfl, norm_div]
    exact (div_lt_one hαp).mpr h1
  refine ⟨hα, hκ, ?_⟩
  -- `f z ∉ {0, 1}` (injectivity and normalization)
  obtain ⟨⟨K, hK⟩, -, h0, h1, -⟩ := hns
  have hi : Function.Injective f := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  have hzim : 0 < z.im := hz
  have hz0 : f z ≠ 0 := fun he => by
    have := hi (he.trans h0.symm)
    rw [this, Complex.zero_im] at hzim
    exact lt_irrefl _ hzim
  have hz1 : f z ≠ 1 := fun he => by
    have := hi (he.trans h1.symm)
    rw [this, Complex.one_im] at hzim
    exact lt_irrefl _ hzim
  -- regularity at `z`
  have hCz : ContDiffAt ℝ 3 f z := hC.contDiffAt (hU.mem_nhds hz)
  have hD1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := hCz.fderiv_right (by norm_num)
  have hdz1 : ContDiffAt ℝ 1 (dz f) z := by
    have e : dz f = fun y => (fderiv ℝ f y 1 - I * fderiv ℝ f y I) / 2 := rfl
    rw [e]
    exact ((hD1.clm_apply contDiffAt_const).sub (contDiffAt_const.mul (hD1.clm_apply contDiffAt_const))).div_const 2
  have hμ1 : ContDiffAt ℝ 1 μ z := (hμs.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  have hP1 : ContDiffAt ℝ 1 (fun y => μ y * dz f y ^ 2) z := hμ1.mul (hdz1.pow 2)
  obtain ⟨ρ1, hρ1, L1, hL1, hl1⟩ := e124p_lip hD1
  obtain ⟨ρ2, hρ2, L2, hL2, hl2⟩ := e124p_lip hP1
  have hfc : ContinuousAt f z := hCz.continuousAt
  have hRc : ContinuousAt (fun y => 1 / f y - 1 / (f y - 1)) z :=
    (continuousAt_const.div hfc hz0).sub
      (continuousAt_const.div (hfc.sub continuousAt_const) (sub_ne_zero.mpr hz1))
  obtain ⟨ρ3, hρ3, hl3⟩ := Metric.continuousAt_iff.mp hRc 1 one_pos
  obtain ⟨ρ0, hρ0, hb0⟩ := Metric.isOpen_iff.mp hU z hz
  -- constants
  set α := dz f z with hαd
  set κ := complexDilatation f z with hκd
  set c0 : ℝ := ‖α‖ * (1 - ‖κ‖) with hc0d
  have hc0 : 0 < c0 := mul_pos hαp (by linarith)
  have hc0α : c0 ≤ ‖α‖ := by nlinarith [norm_nonneg κ]
  set Pz : ℝ := ‖μ z * α ^ 2‖ with hPzd
  set Rz : ℝ := ‖1 / f z - 1 / (f z - 1)‖ with hRzd
  set r : ℝ := min (min ρ0 ρ1) (min (min ρ2 ρ3) (c0 / (2 * (L1 + 1)))) with hrd
  have hr : 0 < r := by positivity
  set A1 : ℝ := ‖α‖ * (4 * L2 / c0 ^ 2) with hA1d
  set A2 : ℝ := ‖α‖ * Pz * (20 * L1 * ‖α‖ / c0 ^ 4) with hA2d
  set K3 : ℝ := ‖α‖ * (Rz + 1) * (Pz + L2 * r)
  have hK3 : 0 ≤ K3 := by positivity
  refine ⟨r, hr, L1 + A1 + A2 + K3 * r,
    (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))).trans hb0, ?_⟩
  intro h hh0 hhr
  have hr0 : ‖h‖ < ρ0 := lt_of_lt_of_le hhr ((min_le_left _ _).trans (min_le_left _ _))
  have hr1 : ‖h‖ < ρ1 := lt_of_lt_of_le hhr ((min_le_left _ _).trans (min_le_right _ _))
  have hr2 : ‖h‖ < ρ2 :=
    lt_of_lt_of_le hhr ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hr3 : ‖h‖ < ρ3 :=
    lt_of_lt_of_le hhr ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hrc : ‖h‖ < c0 / (2 * (L1 + 1)) := lt_of_lt_of_le hhr ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : ∀ ρ : ℝ, ‖h‖ < ρ → z + h ∈ ball z ρ := fun ρ hρ => by
    rwa [mem_ball, dist_eq_norm, add_sub_cancel_left]
  -- the linearization
  have hdiff : ∀ x ∈ ball z (min ρ0 ρ1), DifferentiableAt ℝ f x := fun x hx =>
    (hC.contDiffAt (hU.mem_nhds (hb0 (ball_subset_ball (min_le_left _ _) hx)))).differentiableAt (by norm_num)
  have hlip : ∀ x ∈ ball z (min ρ0 ρ1), ‖fderiv ℝ f x - fderiv ℝ f z‖ ≤ L1 * ‖x - z‖ := fun x hx =>
    hl1 x (ball_subset_ball (min_le_right _ _) hx) z (mem_ball_self hρ1)
  have hT := e124p_taylor hL1 hdiff hlip (lt_min hr0 hr1)
  have hlin : fderiv ℝ f z h = α * (h + κ * conj h) := by
    rw [e124p_wirt (fderiv ℝ f z) h]
    show dz f z * h + dzbar f z * conj h = _
    rw [hdzb]; ring
  rw [hlin] at hT
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨hT.trans (mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hK3 hr.le]) (by positivity)), ?_⟩
  have h2 : ‖h‖ * (2 * (L1 + 1)) < c0 := (lt_div_iff₀ (by positivity)).mp hrc
  have h4 : L1 * ‖h‖ ≤ c0 / 2 := by nlinarith
  have hP : ‖μ (z + h) * dz f (z + h) ^ 2 - μ z * α ^ 2‖ ≤ L2 * ‖h‖ := by
    have := hl2 (z + h) (hmem ρ2 hr2) z (mem_ball_self hρ2)
    rwa [add_sub_cancel_left] at this
  have hRb : ‖1 / f (z + h) - 1 / (f (z + h) - 1)‖ ≤ Rz + 1 := by
    have := hl3 (show dist (z + h) z < ρ3 by rw [dist_eq_norm, add_sub_cancel_left]; exact hr3)
    rw [dist_eq_norm] at this
    have := norm_sub_norm_le (1 / f (z + h) - 1 / (f (z + h) - 1)) (1 / f z - 1 / (f z - 1))
    linarith
  exact e124p_model_bound hα hκ hc0d hL1 hL2 (norm_nonneg _) hh0 hhr h4 hT hP hRb

/-- The angular factor of `(h + κh̄)⁻²` in polar coordinates, `e^{2iθ}/(e^{2iθ} + κ)²`, has zero mean: it is the
derivative of the `2π`-periodic `(i/2)(e^{2iθ} + κ)⁻¹`. -/
theorem e124p_angular {κ : ℂ} (hκ : ‖κ‖ < 1) :
    (∫ θ in (-π)..π, Complex.exp ((θ : ℂ) * I) ^ 2 / (Complex.exp ((θ : ℂ) * I) ^ 2 + κ) ^ 2) = 0 := by
  have hv : ∀ w : ℂ, ‖Complex.exp (w * I) ^ 2‖ = 1 → Complex.exp (w * I) ^ 2 + κ ≠ 0 := by
    intro w hw h
    have : ‖κ‖ = 1 := by rw [show κ = -(Complex.exp (w * I) ^ 2) by linear_combination h, norm_neg, hw]
    linarith
  have hn : ∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * I) ^ 2‖ = 1 := fun θ => by
    rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hd : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => I / 2 * (Complex.exp ((t : ℂ) * I) ^ 2 + κ)⁻¹)
      (Complex.exp ((θ : ℂ) * I) ^ 2 / (Complex.exp ((θ : ℂ) * I) ^ 2 + κ) ^ 2) θ := by
    intro θ
    have h1 : HasDerivAt (fun w : ℂ => w * I) I (θ : ℂ) := by
      simpa using (hasDerivAt_id (θ : ℂ)).mul_const I
    have h3 := ((h1.cexp.pow 2).add_const κ).inv (hv _ (hn θ))
    have h4 := (h3.const_mul (I / 2)).comp_ofReal
    convert h4 using 1
    simp only [Pi.pow_apply]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hc : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * I) ^ 2 / (Complex.exp ((θ : ℂ) * I) ^ 2 + κ) ^ 2 :=
    Continuous.div (by fun_prop) (by fun_prop) (fun θ => pow_ne_zero 2 (hv _ (hn θ)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ) (hc.intervalIntegrable _ _)]
  have e1 : Complex.exp ((π : ℂ) * I) ^ 2 = 1 := by rw [Complex.exp_pi_mul_I]; norm_num
  have e2 : Complex.exp (((-π : ℝ) : ℂ) * I) ^ 2 = 1 := by
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  simp only [e1, e2, sub_self]

/-- `(h + κh̄)⁻²` at `h = r e^{iθ}`, times the polar Jacobian `r`, is `r⁻¹ e^{2iθ}/(e^{2iθ} + κ)²`. -/
theorem e124p_annulus_pt {κ : ℂ} (hκ : ‖κ‖ < 1) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (r : ℂ) * ((((r : ℂ) * Complex.exp ((θ : ℂ) * I)) + κ * conj ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) ^ 2)⁻¹ =
      ((r⁻¹ : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * I) ^ 2 / (Complex.exp ((θ : ℂ) * I) ^ 2 + κ) ^ 2) := by
  set E := Complex.exp ((θ : ℂ) * I) with hEd
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have hc : conj E = E⁻¹ := by
    rw [hEd, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.exp_neg]
  have hw : E ^ 2 + κ ≠ 0 := by
    intro h
    have h1 : ‖E ^ 2‖ = 1 := by rw [hEd, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
    have : ‖κ‖ = 1 := by rw [show κ = -(E ^ 2) by linear_combination h, norm_neg, h1]
    linarith
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [map_mul, Complex.conj_ofReal, hc,
    show (r : ℂ) * E + κ * ((r : ℂ) * E⁻¹) = (r : ℂ) * E⁻¹ * (E ^ 2 + κ) by field_simp]
  push_cast
  field_simp

/-- The model kernel `(h + κh̄)⁻²` has zero integral over every annulus. -/
theorem e124p_annulus {κ : ℂ} (hκ : ‖κ‖ < 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ h in ball (0 : ℂ) b \ ball (0 : ℂ) a, ((h + κ * conj h) ^ 2)⁻¹ = 0 := by
  -- `0 < a ≤ b` are not needed: the identity holds for every annulus (empty when `b ≤ a`)
  have _ha := ha
  have _hab := hab
  set S : Set ℂ := ball (0 : ℂ) b \ ball (0 : ℂ) a with hSd
  have hSm : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  set ψ : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I) ^ 2 / (Complex.exp ((θ : ℂ) * I) ^ 2 + κ) ^ 2 with hψd
  set H : ℝ × ℝ → ℂ := fun p => (((Ico a b).indicator (fun r : ℝ => r⁻¹) p.1 : ℝ) : ℂ) * ψ p.2 with hHd
  rw [← integral_indicator hSm, ← Complex.integral_comp_polarCoord_symm]
  have hpt : ∀ p ∈ polarCoord.target,
      p.1 • S.indicator (fun h : ℂ => ((h + κ * conj h) ^ 2)⁻¹) (Complex.polarCoord.symm p) = H p := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hps : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hnorm : ‖(p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)‖ = p.1 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hmem : (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) ∈ S ↔ p.1 ∈ Ico a b := by
      rw [hSd, Set.mem_sdiff, mem_ball_zero_iff, mem_ball_zero_iff, hnorm, mem_Ico, not_lt, and_comm]
    rw [hps, Complex.real_smul, hHd]
    dsimp only
    by_cases h : p.1 ∈ Ico a b
    · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h, e124p_annulus_pt hκ hr]
    · rw [indicator_of_notMem (fun h' => h (hmem.mp h')), indicator_of_notMem h]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [ht, Measure.volume_eq_prod, ← Measure.prod_restrict, hHd]
  rw [integral_prod_mul (fun r : ℝ => (((Ico a b).indicator (fun r : ℝ => r⁻¹) r : ℝ) : ℂ)) ψ]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    hψd, e124p_angular hκ, mul_zero]

open scoped Pointwise in
/-- Scale invariance of the model kernel `(h + κh̄)⁻² d²h` on a set and its dilate, together with the dilation of
the two `e124_shape` sets. -/
theorem e124p_shape_scale {κ : ℂ} {s : ℝ} (hs : 0 < s) :
    (∫ h in {h : ℂ | s ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < s}, ((h + κ * conj h) ^ 2)⁻¹) =
        (∫ h in {h : ℂ | 1 ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < 1}, ((h + κ * conj h) ^ 2)⁻¹) ∧
      (∫ h in {h : ℂ | ‖h‖ < s ∧ s ≤ ‖h + κ * conj h‖}, ((h + κ * conj h) ^ 2)⁻¹) =
        (∫ h in {h : ℂ | ‖h‖ < 1 ∧ 1 ≤ ‖h + κ * conj h‖}, ((h + κ * conj h) ^ 2)⁻¹) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hF : ∀ x : ℂ, ((s • x + κ * conj (s • x)) ^ 2)⁻¹ = ((s : ℂ) ^ 2)⁻¹ * ((x + κ * conj x) ^ 2)⁻¹ := by
    intro x
    rw [Complex.real_smul, map_mul, Complex.conj_ofReal,
      show (s : ℂ) * x + κ * ((s : ℂ) * conj x) = (s : ℂ) * (x + κ * conj x) by ring, mul_pow, mul_inv]
  have key : ∀ A : Set ℂ, ∫ h in s • A, ((h + κ * conj h) ^ 2)⁻¹ = ∫ h in A, ((h + κ * conj h) ^ 2)⁻¹ := by
    intro A
    have h1 := Measure.setIntegral_comp_smul_of_pos volume (fun h : ℂ => ((h + κ * conj h) ^ 2)⁻¹) A hs
    simp only [hF, integral_const_mul, Complex.finrank_real_complex] at h1
    rw [Complex.real_smul] at h1
    push_cast at h1
    have h2 : ((s : ℂ) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hsC)
    exact (mul_left_cancel₀ h2 h1).symm
  have hnorm : ∀ h : ℂ, ‖s⁻¹ • h‖ = s⁻¹ * ‖h‖ := fun h => by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
  have hL : ∀ h : ℂ, s⁻¹ • h + κ * conj (s⁻¹ • h) = s⁻¹ • (h + κ * conj h) := fun h => by
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  have hle : ∀ t : ℝ, (1 ≤ s⁻¹ * t ↔ s ≤ t) := fun t => by
    rw [← div_eq_inv_mul, one_le_div hs]
  have hlt : ∀ t : ℝ, (s⁻¹ * t < 1 ↔ t < s) := fun t => by
    rw [← div_eq_inv_mul, div_lt_one hs]
  have hA : {h : ℂ | s ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < s} = s • {h : ℂ | 1 ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < 1} := by
    ext h
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne']
    simp only [mem_ofPred_eq, hL, hnorm, hle, hlt]
  have hB : {h : ℂ | ‖h‖ < s ∧ s ≤ ‖h + κ * conj h‖} = s • {h : ℂ | ‖h‖ < 1 ∧ 1 ≤ ‖h + κ * conj h‖} := by
    ext h
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne']
    simp only [mem_ofPred_eq, hL, hnorm, hle, hlt]
  exact ⟨by rw [hA, key], by rw [hB, key]⟩

/-- `e124_shape` at scale `s > 0` (the kernel `(h + κh̄)⁻² d²h` is scale invariant). -/
theorem e124p_shape_scaled {κ : ℂ} (hκ : ‖κ‖ < 1) {s : ℝ} (hs : 0 < s) :
    (∫ h in {h : ℂ | s ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < s}, ((h + κ * conj h) ^ 2)⁻¹) -
        (∫ h in {h : ℂ | ‖h‖ < s ∧ s ≤ ‖h + κ * conj h‖}, ((h + κ * conj h) ^ 2)⁻¹) =
      -(π * conj κ) / (1 - ‖κ‖ ^ 2) := by
  obtain ⟨hA, hB⟩ := e124p_shape_scale (κ := κ) hs
  rw [hA, hB]
  exact e124_shape hκ

/-- `|v - z|⁻¹` is integrable on every disc around `z`. -/
theorem e124p_invnorm_int (z : ℂ) (r : ℝ) : IntegrableOn (fun v : ℂ => ‖v - z‖⁻¹) (ball z r) := by
  have hfin : (Module.finrank ℝ ℂ : ℝ) = 2 := by simp
  have h0 : IntegrableOn (fun u : ℂ => ‖u‖⁻¹) (ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1) (by simp)
      (by rw [hfin]; norm_num) ?_ (measurable_norm.inv).aestronglyMeasurable
    refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun x _ => ?_)
    rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]
  have h1 := ((integrable_indicator_iff measurableSet_ball).mpr h0).comp_sub_right z
  rw [← integrable_indicator_iff measurableSet_ball]
  refine h1.congr (ae_of_all _ fun v => ?_)
  by_cases hv : v ∈ ball z r
  · have hv' : v - z ∈ ball (0 : ℂ) r := by rwa [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    simp only [indicator_of_mem hv, indicator_of_mem hv']
  · have hv' : v - z ∉ ball (0 : ℂ) r := by rwa [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    simp only [indicator_of_notMem hv, indicator_of_notMem hv']

/-- The model term `c (h + κh̄)⁻²`, `h = v - z`, is integrable with integral `0` on every annulus around `z`
(`e124p_annulus`, translated). -/
theorem e124p_model_zero (c κ z : ℂ) (hκ : ‖κ‖ < 1) {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) :
    IntegrableOn (fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) (ball z r \ ball z δ) ∧
      ∫ v in ball z r \ ball z δ, c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹ = 0 := by
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hm : Measurable fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹ := by fun_prop
  have hA : MeasurableSet (ball z r \ ball z δ) := measurableSet_ball.diff measurableSet_ball
  refine ⟨Measure.integrableOn_of_bounded (M := ‖c‖ / ((1 - ‖κ‖) * δ) ^ 2)
    ((measure_mono diff_subset).trans_lt measure_ball_lt_top).ne hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [ae_restrict_mem hA] with v hv
    have hvδ : δ ≤ ‖v - z‖ := by
      have := hv.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
    have hlo : (1 - ‖κ‖) * δ ≤ ‖v - z + κ * conj (v - z)‖ := by
      have := norm_sub_norm_le (v - z) (-(κ * conj (v - z)))
      rw [norm_neg, norm_mul, Complex.norm_conj, sub_neg_eq_add] at this
      nlinarith
    have hp : 0 < (1 - ‖κ‖) * δ := mul_pos (by linarith) hδ
    rw [norm_mul, norm_inv, norm_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le hlo 2)) (norm_nonneg _)
  · rw [← integral_indicator hA]
    have e : ∀ v, (ball z r \ ball z δ).indicator (fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) v =
        (ball (0 : ℂ) r \ ball 0 δ).indicator (fun h => c * ((h + κ * conj h) ^ 2)⁻¹) (v - z) := by
      intro v
      have hiff : v ∈ ball z r \ ball z δ ↔ v - z ∈ ball (0 : ℂ) r \ ball 0 δ := by
        simp only [mem_diff, mem_ball, dist_eq_norm, sub_zero]
      by_cases hv : v ∈ ball z r \ ball z δ
      · rw [indicator_of_mem hv, indicator_of_mem (hiff.mp hv)]
      · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv (hiff.mpr h))]
    simp only [e]
    rw [integral_sub_right_eq_self (fun h => (ball (0 : ℂ) r \ ball 0 δ).indicator
        (fun h => c * ((h + κ * conj h) ^ 2)⁻¹) h) z,
      integral_indicator (measurableSet_ball.diff measurableSet_ball), integral_const_mul,
      e124p_annulus hκ hδ hδr, mul_zero]

/-- Dominated convergence for excisions shrinking to `z`: `∫_{B \ X_δ} F → ∫_B F`. -/
theorem e124p_rem_tendsto {F : ℂ → ℂ} {B : Set ℂ} {z : ℂ} (hF : IntegrableOn F B) {X : ℝ → Set ℂ}
    (hXm : ∀ δ, MeasurableSet (X δ)) (hX : ∀ v, v ≠ z → ∀ᶠ δ in 𝓝[>] (0 : ℝ), v ∉ X δ) :
    Tendsto (fun δ => ∫ v in B \ X δ, F v) (𝓝[>] (0 : ℝ)) (𝓝 (∫ v in B, F v)) := by
  have e : ∀ δ, ∫ v in B \ X δ, F v = ∫ v in B, (X δ)ᶜ.indicator F v := fun δ => by
    rw [setIntegral_indicator (hXm δ).compl, diff_eq]
  simp only [e]
  refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖F v‖)
    (Eventually.of_forall fun δ => hF.aestronglyMeasurable.indicator (hXm δ).compl)
    (Eventually.of_forall fun δ => Eventually.of_forall fun v => norm_indicator_le_norm_self _ _) hF.norm ?_
  have hne : ∀ᵐ v ∂(volume.restrict B), v ≠ z :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))
  filter_upwards [hne] with v hv
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hX v hv] with δ hδ
  rw [indicator_of_mem (show v ∈ (X δ)ᶜ from hδ)]

/-- The remainder `g - (model)` is integrable on the disc of `e124p_local`. -/
theorem e124p_rem_int {μ : ℂ → ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ upperHalf k) {f : ℂ → ℂ} (hfc : Continuous f)
    {z κ : ℂ} {r C : ℝ} (hball : ball z r ⊆ upperHalf)
    (hloc : ∀ h : ℂ, 0 < ‖h‖ → ‖h‖ < r →
      ‖dz f z * (1 / (f (z + h) - f z) ^ 2 + 1 / f (z + h) - 1 / (f (z + h) - 1)) * μ (z + h) *
          dz f (z + h) ^ 2 - μ z * dz f z * ((h + κ * conj h) ^ 2)⁻¹‖ ≤ C / ‖h‖) :
    IntegrableOn (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2 -
      μ z * dz f z * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) (ball z r) := by
  have hfm : Measurable f := hfc.measurable
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hμm : AEStronglyMeasurable μ (volume.restrict (ball z r)) :=
    hμ.1.mono_measure (Measure.restrict_mono hball le_rfl)
  have hK : Measurable fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) := by fun_prop
  have hg : AEStronglyMeasurable (fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v *
      dz f v ^ 2) (volume.restrict (ball z r)) :=
    (hK.aestronglyMeasurable.mul hμm).mul ((measurable_dz f).pow_const 2).aestronglyMeasurable
  have hm : Measurable fun v => μ z * dz f z * ((v - z + κ * conj (v - z)) ^ 2)⁻¹ := by fun_prop
  refine ((e124p_invnorm_int z r).const_mul C).mono' (hg.sub hm.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))] with v hv hvz
  have hvz' : v - z ≠ 0 := sub_ne_zero.mpr hvz
  have hvr : ‖v - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hv
  have := hloc (v - z) (norm_pos_iff.mpr hvz') hvr
  rw [add_sub_cancel] at this
  rw [← div_eq_mul_inv]
  exact this

/-- The `v`-plane principal value exists. -/
theorem e124p_v_limit {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    ∃ L : ℂ, Tendsto (fun δ => ∫ v in upperHalf \ ball z δ,
      dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨-, hκ, r, hr, C, hball, hloc⟩ := e124p_local hk hμ hμs hε hf hz
  obtain ⟨hns, -, -, -⟩ := e124c_setup hk hμ hμs hε hf
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hns
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hfc : Continuous f := he ▸ e.continuous
  have hrem := e124p_rem_int hμ hfc hball (fun h h0 h1 => (hloc h h0 h1).2)
  -- `I(δ) = I(r) + ∫_{B_r \ B_δ} (g - model)` for `0 < δ < r`
  refine ⟨(∫ v in upperHalf \ ball z r, dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v *
      dz f v ^ 2) + ∫ v in ball z r, (dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v *
      dz f v ^ 2 - μ z * dz f z * ((v - z + complexDilatation f z * conj (v - z)) ^ 2)⁻¹), ?_⟩
  have hT := e124p_rem_tendsto hrem (X := fun δ => ball z δ) (fun δ => measurableSet_ball) (fun v hv => by
    have hp : 0 < ‖v - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
    filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
    rw [mem_ball, dist_eq_norm, not_lt]
    exact hδ.2.le)
  refine (tendsto_const_nhds.add hT).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
  have hI := (e124p_integrable hk hμ hμs hε hf hz hδ.1).1
  have hsplit : upperHalf \ ball z δ = (upperHalf \ ball z r) ∪ (ball z r \ ball z δ) := by
    ext v
    constructor
    · rintro ⟨hvU, hvδ⟩
      by_cases hvr : v ∈ ball z r
      · exact Or.inr ⟨hvr, hvδ⟩
      · exact Or.inl ⟨hvU, hvr⟩
    · rintro (⟨hvU, hvr⟩ | ⟨hvr, hvδ⟩)
      · exact ⟨hvU, fun h => hvr (ball_subset_ball hδ.2.le h)⟩
      · exact ⟨hball hvr, hvδ⟩
  have hdisj : Disjoint (upperHalf \ ball z r) (ball z r \ ball z δ) :=
    disjoint_left.mpr fun v h1 h2 => h1.2 h2.1
  rw [hsplit] at hI
  obtain ⟨hmi, hm0⟩ := e124p_model_zero (μ z * dz f z) (complexDilatation f z) z hκ hδ.1 hδ.2.le
  show _ = ∫ v in upperHalf \ ball z δ, _
  rw [hsplit, setIntegral_union hdisj (measurableSet_ball.diff measurableSet_ball)
      (hI.mono_set subset_union_left) (hI.mono_set subset_union_right),
    integral_sub (hI.mono_set subset_union_right) hmi, hm0, sub_zero]

/-- `(1 - |κ|)|h| ≤ |h + κh̄| ≤ 2|h|`. -/
theorem e124p_Lb {κ : ℂ} (hκ : ‖κ‖ < 1) (h : ℂ) :
    (1 - ‖κ‖) * ‖h‖ ≤ ‖h + κ * conj h‖ ∧ ‖h + κ * conj h‖ ≤ 2 * ‖h‖ := by
  have h1 := norm_sub_norm_le h (-(κ * conj h))
  have h2 := norm_add_le h (κ * conj h)
  rw [norm_neg, norm_mul, Complex.norm_conj, sub_neg_eq_add] at h1
  rw [norm_mul, Complex.norm_conj] at h2
  constructor <;> nlinarith [norm_nonneg κ, norm_nonneg h]

/-- Translation of a set integral: `∫_{z + S₀} F(v - z) = ∫_{S₀} F`. -/
theorem e124p_translate (z : ℂ) (F : ℂ → ℂ) {S0 : Set ℂ} (hS0 : MeasurableSet S0) :
    ∫ v in {v : ℂ | v - z ∈ S0}, F (v - z) = ∫ h in S0, F h := by
  have hm : MeasurableSet {v : ℂ | v - z ∈ S0} := hS0.preimage (measurable_id.sub_const z)
  rw [← integral_indicator hm, ← integral_indicator hS0]
  have e : (fun v => {v : ℂ | v - z ∈ S0}.indicator (fun v => F (v - z)) v) = fun v => S0.indicator F (v - z) := by
    funext v
    simp only [indicator_apply, mem_ofPred_eq]
  rw [e, integral_sub_right_eq_self (fun h => S0.indicator F h) z]

/-- The elliptic discs `{|L(v - z)| < s}` have volume `s² V₁`. -/
theorem e124p_ell_vol (κ z : ℂ) (hκ : ‖κ‖ < 1) {s : ℝ} (hs : 0 < s) :
    volume.real {v : ℂ | ‖v - z + κ * conj (v - z)‖ < s} =
      s ^ 2 * volume.real {h : ℂ | ‖h + κ * conj h‖ < 1} := by
  have hP : {v : ℂ | ‖v - z + κ * conj (v - z)‖ < s} =
      (fun v => v + -z) ⁻¹' (open scoped Pointwise in s • {h : ℂ | ‖h + κ * conj h‖ < 1}) := by
    ext v
    rw [mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne', ← sub_eq_add_neg]
    simp only [mem_ofPred_eq, Complex.real_smul, map_mul, Complex.conj_ofReal]
    rw [show ((s⁻¹ : ℝ) : ℂ) * (v - z) + κ * (((s⁻¹ : ℝ) : ℂ) * conj (v - z)) =
        ((s⁻¹ : ℝ) : ℂ) * (v - z + κ * conj (v - z)) by ring, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul, div_lt_one hs]
  rw [hP, measureReal_def, measure_preimage_add_right, Measure.addHaar_smul_of_nonneg volume hs.le,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Complex.finrank_real_complex, measureReal_def]

/-- The elliptic shell `{A ≤ |L(v - z)| < B}` has volume `(B² - A²) V₁`. -/
theorem e124p_shell_vol (κ z : ℂ) (hκ : ‖κ‖ < 1) {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    volume.real {v : ℂ | A ≤ ‖v - z + κ * conj (v - z)‖ ∧ ‖v - z + κ * conj (v - z)‖ < B} =
      (B ^ 2 - A ^ 2) * volume.real {h : ℂ | ‖h + κ * conj h‖ < 1} := by
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hm : Measurable fun v : ℂ => ‖v - z + κ * conj (v - z)‖ := by fun_prop
  have he : {v : ℂ | A ≤ ‖v - z + κ * conj (v - z)‖ ∧ ‖v - z + κ * conj (v - z)‖ < B} =
      {v : ℂ | ‖v - z + κ * conj (v - z)‖ < B} \ {v : ℂ | ‖v - z + κ * conj (v - z)‖ < A} := by
    ext v
    simp only [mem_ofPred_eq, Set.mem_sdiff, not_lt]
    exact and_comm
  have hsub : {v : ℂ | ‖v - z + κ * conj (v - z)‖ < A} ⊆ {v : ℂ | ‖v - z + κ * conj (v - z)‖ < B} :=
    fun v hv => lt_of_lt_of_le hv hAB
  have hfin : volume {v : ℂ | ‖v - z + κ * conj (v - z)‖ < B} ≠ ⊤ := by
    refine ((measure_mono (fun v (hv : ‖v - z + κ * conj (v - z)‖ < B) => ?_)).trans_lt
      (measure_ball_lt_top (x := z) (r := B / (1 - ‖κ‖)))).ne
    rw [mem_ball, dist_eq_norm, lt_div_iff₀ (by linarith), mul_comm]
    exact lt_of_le_of_lt (e124p_Lb hκ (v - z)).1 hv
  rw [he, measureReal_sdiff hsub (measurableSet_lt hm measurable_const) hfin, e124p_ell_vol κ z hκ (hA.trans_le hAB),
    e124p_ell_vol κ z hκ hA]
  ring

/-- Comparing two excisions: `|∫_{B \ X} m - ∫_{B \ Y} m| ≤ M |S|` when the symmetric difference lies in `S` (off `z`)
and `|m| ≤ M` on `S`. -/
theorem e124p_compare {m : ℂ → ℂ} {B X Y S : Set ℂ} {z : ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hS : MeasurableSet S) (hSf : volume S ≠ ⊤)
    (hBX : IntegrableOn m (B \ X)) (hBY : IntegrableOn m (B \ Y)) (hBm : MeasurableSet B)
    (hsd : ∀ v ∈ B, v ≠ z → ¬(v ∈ X ↔ v ∈ Y) → v ∈ S) (hb : ∀ v ∈ S, ‖m v‖ ≤ M) :
    ‖(∫ v in B \ X, m v) - ∫ v in B \ Y, m v‖ ≤ volume.real S * M := by
  rw [← integral_indicator (hBm.diff hX), ← integral_indicator (hBm.diff hY),
    ← integral_sub ((integrable_indicator_iff (hBm.diff hX)).mpr hBX)
      ((integrable_indicator_iff (hBm.diff hY)).mpr hBY), ← smul_eq_mul, ← integral_indicator_const M hS]
  refine norm_integral_le_of_norm_le ((integrable_indicator_iff hS).mpr (integrableOn_const hSf)) ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton z)] with v hvz
  have hvz' : v ≠ z := hvz
  by_cases hvB : v ∈ B
  · by_cases hxy : (v ∈ X ↔ v ∈ Y)
    · have : (B \ X).indicator m v = (B \ Y).indicator m v := by
        simp only [indicator_apply, Set.mem_sdiff, hxy]
      rw [this, sub_self, norm_zero]
      exact indicator_nonneg (fun _ _ => hM0) v
    · have hvS := hsd v hvB hvz' hxy
      rw [indicator_of_mem hvS]
      by_cases hvX : v ∈ X
      · have hvY : v ∉ Y := fun h => hxy ⟨fun _ => h, fun _ => hvX⟩
        rw [indicator_of_notMem (show v ∉ B \ X from fun h => h.2 hvX), indicator_of_mem (show v ∈ B \ Y from ⟨hvB, hvY⟩), zero_sub, norm_neg]
        exact hb v hvS
      · have hvY : v ∈ Y := by by_contra h; exact hxy ⟨fun h' => absurd h' hvX, fun h' => absurd h' h⟩
        rw [indicator_of_mem (show v ∈ B \ X from ⟨hvB, hvX⟩), indicator_of_notMem (show v ∉ B \ Y from fun h => h.2 hvY), sub_zero]
        exact hb v hvS
  · rw [indicator_of_notMem (show v ∉ B \ X from fun h => hvB h.1),
      indicator_of_notMem (show v ∉ B \ Y from fun h => hvB h.1), sub_self, norm_zero]
    exact indicator_nonneg (fun _ _ => hM0) v

/-- Splitting `𝕌 \ X = (𝕌 \ B) ∪ (B \ X)` for `X ⊆ B ⊆ 𝕌`. -/
theorem e124p_split {g : ℂ → ℂ} {B X : Set ℂ} (hB : B ⊆ upperHalf) (hBm : MeasurableSet B)
    (hXm : MeasurableSet X) (hX : X ⊆ B) (hint : IntegrableOn g (upperHalf \ X)) :
    ∫ v in upperHalf \ X, g v = (∫ v in upperHalf \ B, g v) + ∫ v in B \ X, g v := by
  have hsplit : upperHalf \ X = (upperHalf \ B) ∪ (B \ X) := by
    ext v
    constructor
    · rintro ⟨hvU, hvX⟩
      by_cases hvB : v ∈ B
      · exact Or.inr ⟨hvB, hvX⟩
      · exact Or.inl ⟨hvU, hvB⟩
    · rintro (⟨hvU, hvB⟩ | ⟨hvB, hvX⟩)
      · exact ⟨hvU, fun h => hvB (hX h)⟩
      · exact ⟨hB hvB, hvX⟩
  rw [hsplit] at hint ⊢
  exact setIntegral_union (disjoint_left.mpr fun v h1 h2 => h1.2 h2.1) (hBm.diff hXm)
    (hint.mono_set subset_union_left) (hint.mono_set subset_union_right)

/-- The model term on `B_r` minus the elliptic disc `Q_ρ = {|L(v - z)| < ρ}` (`e124p_shape_scaled`, translated). -/
theorem e124p_model_Q (c κ z : ℂ) (hκ : ‖κ‖ < 1) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ / (1 - ‖κ‖) ≤ r) :
    IntegrableOn (fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)
        (ball z r \ {v : ℂ | ‖v - z + κ * conj (v - z)‖ < ρ}) ∧
      ∫ v in ball z r \ {v : ℂ | ‖v - z + κ * conj (v - z)‖ < ρ}, c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹ =
        π * (c * conj κ / (1 - ‖κ‖ ^ 2)) := by
  have hκ1 : 0 < 1 - ‖κ‖ := by linarith
  have hρr' : ρ ≤ r := le_trans (le_div_self hρ.le hκ1 (by linarith [norm_nonneg κ])) hρr
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hLm : Measurable fun v : ℂ => ‖v - z + κ * conj (v - z)‖ := by fun_prop
  set Q := {v : ℂ | ‖v - z + κ * conj (v - z)‖ < ρ} with hQd
  have hQm : MeasurableSet Q := measurableSet_lt hLm measurable_const
  set F : ℂ → ℂ := fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹ with hFd
  have hQB : Q ⊆ ball z r := fun v hv => by
    rw [mem_ball, dist_eq_norm]
    have h1 := (e124p_Lb hκ (v - z)).1
    have hv' : ‖v - z + κ * conj (v - z)‖ < ρ := hv
    have : ‖v - z‖ < ρ / (1 - ‖κ‖) := by rw [lt_div_iff₀ hκ1]; linarith
    linarith
  have hhalf : ball z (ρ / 2) ⊆ Q := fun v hv => by
    rw [mem_ball, dist_eq_norm] at hv
    show ‖v - z + κ * conj (v - z)‖ < ρ
    linarith [(e124p_Lb hκ (v - z)).2]
  have hmi : IntegrableOn F (ball z r \ ball z (ρ / 2)) := (e124p_model_zero c κ z hκ (half_pos hρ) (by linarith)).1
  have hsub : ∀ T : Set ℂ, T ⊆ ball z r → (∀ v ∈ T, v ∉ ball z (ρ / 2)) → IntegrableOn F T :=
    fun T hT hT' => hmi.mono_set fun v hv => ⟨hT hv, hT' v hv⟩
  have i1 : IntegrableOn F (ball z r \ Q) := hsub _ sdiff_subset fun v hv h => hv.2 (hhalf h)
  have i2 : IntegrableOn F (ball z r \ ball z ρ) :=
    hsub _ sdiff_subset fun v hv h => hv.2 (ball_subset_ball (by linarith) h)
  have i3 : IntegrableOn F (ball z ρ \ Q) :=
    hsub _ (sdiff_subset.trans (ball_subset_ball hρr')) fun v hv h => hv.2 (hhalf h)
  have i4 : IntegrableOn F (Q \ ball z ρ) :=
    hsub _ (sdiff_subset.trans hQB) fun v hv h => hv.2 (ball_subset_ball (by linarith) h)
  refine ⟨i1, ?_⟩
  -- `1_{B∖Q} - 1_{B∖B_ρ} = 1_{B_ρ∖Q} - 1_{Q∖B_ρ}`
  have hid : (∫ v in ball z r \ Q, F v) - (∫ v in ball z r \ ball z ρ, F v) =
      (∫ v in ball z ρ \ Q, F v) - ∫ v in Q \ ball z ρ, F v := by
    have hBm : MeasurableSet (ball z r) := measurableSet_ball
    rw [← integral_indicator (hBm.diff hQm), ← integral_indicator (hBm.diff measurableSet_ball),
      ← integral_indicator (measurableSet_ball.diff hQm), ← integral_indicator (hQm.diff measurableSet_ball),
      ← integral_sub ((integrable_indicator_iff (hBm.diff hQm)).mpr i1)
        ((integrable_indicator_iff (hBm.diff measurableSet_ball)).mpr i2),
      ← integral_sub ((integrable_indicator_iff (measurableSet_ball.diff hQm)).mpr i3)
        ((integrable_indicator_iff (hQm.diff measurableSet_ball)).mpr i4)]
    congr 1
    funext v
    by_cases hvB : v ∈ ball z r
    · by_cases hvQ : v ∈ Q <;> by_cases hvR : v ∈ ball z ρ <;>
        simp [indicator_apply, Set.mem_sdiff, hvB, hvQ, hvR]
    · have hvQ : v ∉ Q := fun h => hvB (hQB h)
      have hvR : v ∉ ball z ρ := fun h => hvB (ball_subset_ball hρr' h)
      simp [indicator_apply, Set.mem_sdiff, hvB, hvQ, hvR]
  have h0 : ∫ v in ball z r \ ball z ρ, F v = 0 := (e124p_model_zero c κ z hκ hρ hρr').2
  have t1 : ∫ v in ball z ρ \ Q, F v = c * ∫ h in {h : ℂ | ‖h‖ < ρ ∧ ρ ≤ ‖h + κ * conj h‖}, ((h + κ * conj h) ^ 2)⁻¹ := by
    have hS : ball z ρ \ Q = {v : ℂ | v - z ∈ {h : ℂ | ‖h‖ < ρ ∧ ρ ≤ ‖h + κ * conj h‖}} := by
      ext v; simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, hQd, mem_ofPred_eq, not_lt]
    have hm0 : MeasurableSet {h : ℂ | ‖h‖ < ρ ∧ ρ ≤ ‖h + κ * conj h‖} :=
      (measurableSet_lt measurable_norm measurable_const).inter (measurableSet_le measurable_const (show Measurable fun h : ℂ => ‖h + κ * conj h‖ by fun_prop))
    rw [hS]
    have h2 := e124p_translate z (fun h => c * ((h + κ * conj h) ^ 2)⁻¹) hm0
    beta_reduce at h2
    exact h2.trans (integral_const_mul c _)
  have t2 : ∫ v in Q \ ball z ρ, F v = c * ∫ h in {h : ℂ | ρ ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < ρ}, ((h + κ * conj h) ^ 2)⁻¹ := by
    have hS : Q \ ball z ρ = {v : ℂ | v - z ∈ {h : ℂ | ρ ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < ρ}} := by
      ext v; simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, hQd, mem_ofPred_eq, not_lt]; exact and_comm
    have hm0 : MeasurableSet {h : ℂ | ρ ≤ ‖h‖ ∧ ‖h + κ * conj h‖ < ρ} :=
      (measurableSet_le measurable_const measurable_norm).inter (measurableSet_lt (show Measurable fun h : ℂ => ‖h + κ * conj h‖ by fun_prop) measurable_const)
    rw [hS]
    have h2 := e124p_translate z (fun h => c * ((h + κ * conj h) ^ 2)⁻¹) hm0
    beta_reduce at h2
    exact h2.trans (integral_const_mul c _)
  have hsh := e124p_shape_scaled hκ hρ
  rw [h0, sub_zero, t1, t2] at hid
  rw [hid]
  linear_combination (-c) * hsh

/-- Real-variable core of the shell inclusion: with `t = |h|`, `N = |α||Lh|`, `Dn = |f(z+h) - f z|`,
`|Dn - N| ≤ Ct²`, `c₀t ≤ N`, and `t < c₀/(2(C+1))` on `{Dn < δ}`, a point in exactly one of `{Dn < δ}`, `{N < δ}`
has `δ - wδ² ≤ N < δ + wδ²`, `w = 4C/c₀²`. -/
theorem e124p_shell_mem {t N Dn δ C c0 w : ℝ} (ht0 : 0 < t) (hc0 : 0 < c0) (hC0 : 0 ≤ C)
    (hlo : c0 * t ≤ N) (i1 : Dn ≤ N + C * t ^ 2) (i2 : N ≤ Dn + C * t ^ 2)
    (hE : Dn < δ → t * (2 * (C + 1)) < c0) (hwd : w = 4 * C / c0 ^ 2) (hxy : ¬(Dn < δ ↔ N < δ)) :
    δ - w * δ ^ 2 ≤ N ∧ N < δ + w * δ ^ 2 := by
  have hsmall : t * c0 ≤ 2 * δ := by
    by_cases hD : Dn < δ
    · have h2 := hE hD
      have h3 : C * t ≤ c0 / 2 := by nlinarith
      have h4 : C * t ^ 2 ≤ c0 / 2 * t := by
        rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 ht0.le
      nlinarith
    · have hN : N < δ := by by_contra h; exact hxy ⟨fun h' => absurd h' hD, fun h' => absurd h' h⟩
      nlinarith
  have hCw : C * t ^ 2 ≤ w * δ ^ 2 := by
    have ht : t ≤ 2 * δ / c0 := by rw [le_div_iff₀ hc0]; exact hsmall
    calc C * t ^ 2 ≤ C * (2 * δ / c0) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0.le ht 2) hC0
      _ = w * δ ^ 2 := by rw [hwd]; field_simp; ring
  have hw0 : 0 ≤ w * δ ^ 2 := le_trans (by positivity) hCw
  by_cases hD : Dn < δ
  · have hN : ¬ N < δ := fun h => hxy ⟨fun _ => h, fun _ => hD⟩
    push_neg at hN
    constructor <;> linarith
  · have hN : N < δ := by by_contra h; exact hxy ⟨fun h' => absurd h' hD, fun h' => absurd h' h⟩
    push_neg at hD
    constructor <;> linarith

/-- The model term on `B_r` minus the preimage disc `E_δ = f⁻¹B(f z, δ)` is within `16|c| w V₁ δ` of `π c κ̄/(1 - |κ|²)`:
`E_δ` and `Q_{δ/|α|}` differ inside the shell `{δ - wδ² ≤ |α||L(v - z)| < δ + wδ²}` (`e124p_shell_mem`), whose volume is
`O(δ³)` (`e124p_shell_vol`), while `|m| = O(δ⁻²)` there (`e124p_compare`). -/
theorem e124p_modelE {f : ℂ → ℂ} {z α κ : ℂ} (c : ℂ) (hκ : ‖κ‖ < 1) (ha : 0 < ‖α‖) {r r1 C c0 w δ : ℝ}
    (hc0d : c0 = ‖α‖ * (1 - ‖κ‖)) (hC0 : 0 ≤ C)
    (hloc : ∀ h : ℂ, 0 < ‖h‖ → ‖h‖ < r → ‖f (z + h) - f z - α * (h + κ * conj h)‖ ≤ C * ‖h‖ ^ 2)
    (hr1r : r1 ≤ r) (hr1c : r1 ≤ c0 / (2 * (C + 1))) (hEs : f ⁻¹' ball (f z) δ ⊆ ball z r1)
    (hwd : w = 4 * C / c0 ^ 2) (hw0 : 0 ≤ w) (hδp : 0 < δ) (hwδ : w * δ ≤ 1 / 2)
    (hρr : δ / ‖α‖ / (1 - ‖κ‖) ≤ r) (hEm : MeasurableSet (f ⁻¹' ball (f z) δ))
    (hmE : IntegrableOn (fun v => c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) (ball z r \ f ⁻¹' ball (f z) δ)) :
    ‖(∫ v in ball z r \ f ⁻¹' ball (f z) δ, c * ((v - z + κ * conj (v - z)) ^ 2)⁻¹) -
        π * (c * conj κ / (1 - ‖κ‖ ^ 2))‖ ≤
      16 * ‖c‖ * w * volume.real {h : ℂ | ‖h + κ * conj h‖ < 1} * δ := by
  have hκ1 : 0 < 1 - ‖κ‖ := by linarith
  have hc0 : 0 < c0 := by rw [hc0d]; exact mul_pos ha hκ1
  have hρ : 0 < δ / ‖α‖ := div_pos hδp ha
  obtain ⟨hmQ, hQv⟩ := e124p_model_Q c κ z hκ hρ hρr
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hLm : Measurable fun v : ℂ => ‖v - z + κ * conj (v - z)‖ := by fun_prop
  obtain ⟨As, hAsd⟩ : ∃ As : ℝ, As = (δ - w * δ ^ 2) / ‖α‖ := ⟨_, rfl⟩
  obtain ⟨Bs, hBsd⟩ : ∃ Bs : ℝ, Bs = (δ + w * δ ^ 2) / ‖α‖ := ⟨_, rfl⟩
  have hAs : δ / (2 * ‖α‖) ≤ As := by
    have h := mul_nonneg (mul_nonneg ha.le hδp.le) (by linarith : (0 : ℝ) ≤ 1 - 2 * (w * δ))
    rw [hAsd, div_le_div_iff₀ (by positivity) ha]; nlinarith [h]
  have hAs0 : 0 < As := lt_of_lt_of_le (by positivity) hAs
  have hAB : As ≤ Bs := by
    rw [hAsd, hBsd]; exact div_le_div_of_nonneg_right (by nlinarith) ha.le
  have hShm : MeasurableSet {v : ℂ | As ≤ ‖v - z + κ * conj (v - z)‖ ∧ ‖v - z + κ * conj (v - z)‖ < Bs} :=
    (measurableSet_le measurable_const hLm).inter (measurableSet_lt hLm measurable_const)
  have hShf : volume {v : ℂ | As ≤ ‖v - z + κ * conj (v - z)‖ ∧ ‖v - z + κ * conj (v - z)‖ < Bs} ≠ ⊤ := by
    refine ((measure_mono (fun v (hv : As ≤ ‖v - z + κ * conj (v - z)‖ ∧ ‖v - z + κ * conj (v - z)‖ < Bs) => ?_)).trans_lt
      (measure_ball_lt_top (x := z) (r := Bs / (1 - ‖κ‖)))).ne
    rw [mem_ball, dist_eq_norm, lt_div_iff₀ hκ1, mul_comm]
    exact lt_of_le_of_lt (e124p_Lb hκ (v - z)).1 hv.2
  have hM0 : 0 ≤ ‖c‖ * (2 * ‖α‖ / δ) ^ 2 := by positivity
  have hcmp := e124p_compare (B := ball z r) (z := z) hM0 hEm (measurableSet_lt hLm measurable_const) hShm hShf
    hmE hmQ measurableSet_ball ?_ ?_
  · rw [hQv] at hcmp
    refine hcmp.trans (le_of_eq ?_)
    rw [e124p_shell_vol κ z hκ hAs0 hAB, hAsd, hBsd]
    field_simp
    ring
  · intro v hvB hvz hxy
    have hvr : ‖v - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hvB
    have ht0 : 0 < ‖v - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvz)
    have hD := hloc (v - z) ht0 hvr
    rw [add_sub_cancel] at hD
    have hnL : ‖α * (v - z + κ * conj (v - z))‖ = ‖α‖ * ‖v - z + κ * conj (v - z)‖ := norm_mul _ _
    have hlo : c0 * ‖v - z‖ ≤ ‖α‖ * ‖v - z + κ * conj (v - z)‖ := by
      rw [hc0d, mul_assoc]; exact mul_le_mul_of_nonneg_left (e124p_Lb hκ (v - z)).1 ha.le
    have i1 := norm_le_insert' (f v - f z) (α * (v - z + κ * conj (v - z)))
    have i2 := norm_le_insert' (α * (v - z + κ * conj (v - z))) (f v - f z)
    rw [norm_sub_rev (α * (v - z + κ * conj (v - z))) (f v - f z)] at i2
    rw [hnL] at i1 i2
    have hmE' : v ∈ f ⁻¹' ball (f z) δ ↔ ‖f v - f z‖ < δ := by rw [mem_preimage, mem_ball, dist_eq_norm]
    have hmQ' : v ∈ {v : ℂ | ‖v - z + κ * conj (v - z)‖ < δ / ‖α‖} ↔
        ‖α‖ * ‖v - z + κ * conj (v - z)‖ < δ := by
      rw [mem_ofPred_eq, lt_div_iff₀ ha, mul_comm]
    have hE : ‖f v - f z‖ < δ → ‖v - z‖ * (2 * (C + 1)) < c0 := fun h => by
      have := hEs (hmE'.mpr h)
      rw [mem_ball, dist_eq_norm] at this
      have := lt_of_lt_of_le this hr1c
      rwa [lt_div_iff₀ (by positivity)] at this
    have hxy' : ¬(‖f v - f z‖ < δ ↔ ‖α‖ * ‖v - z + κ * conj (v - z)‖ < δ) := by
      rwa [← hmE', ← hmQ']
    obtain ⟨h1, h2⟩ := e124p_shell_mem ht0 hc0 hC0 hlo (i1.trans (by linarith [hD])) (i2.trans (by linarith [hD]))
      hE hwd hxy'
    refine ⟨?_, ?_⟩
    · rw [hAsd, div_le_iff₀ ha]; linarith [h1]
    · rw [hBsd, lt_div_iff₀ ha]; linarith [h2]
  · intro v hv
    have hL : δ / (2 * ‖α‖) ≤ ‖v - z + κ * conj (v - z)‖ := hAs.trans hv.1
    have hp : 0 < δ / (2 * ‖α‖) := by positivity
    rw [norm_mul, norm_inv, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc (‖v - z + κ * conj (v - z)‖ ^ 2)⁻¹ ≤ ((δ / (2 * ‖α‖)) ^ 2)⁻¹ :=
          inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le hL 2)
      _ = (2 * ‖α‖ / δ) ^ 2 := by field_simp

/-- Image-plane minus `v`-plane truncations (at matched radii) tend to `π c`. -/
theorem e124p_diff_limit {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun δ => (∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
        dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) -
      ∫ v in upperHalf \ ball z (δ / ‖dz f z‖),
        dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (π * (μ z * dz f z * conj (complexDilatation f z) / (1 - ‖complexDilatation f z‖ ^ 2)))) := by
  obtain ⟨hα, hκ, r, hr, C, hball, hloc⟩ := e124p_local hk hμ hμs hε hf hz
  obtain ⟨hns, -, -, -⟩ := e124c_setup hk hμ hμs hε hf
  obtain ⟨⟨K, hK⟩, hs, -⟩ := hns
  have hi : Function.Injective f := fun x y he => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) he
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hfc : Continuous f := he ▸ e.continuous
  have hrem := e124p_rem_int hμ hfc hball (fun h h0 h1 => (hloc h h0 h1).2)
  set α := dz f z with hαd
  set κ := complexDilatation f z with hκd
  have ha : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hκ1 : 0 < 1 - ‖κ‖ := by linarith
  obtain ⟨c0, hc0d⟩ : ∃ c0 : ℝ, c0 = ‖α‖ * (1 - ‖κ‖) := ⟨_, rfl⟩
  have hc0 : 0 < c0 := by rw [hc0d]; exact mul_pos ha hκ1
  have hC0 : 0 ≤ C := by
    have hr2 : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1 := (hloc ((r / 2 : ℝ) : ℂ) (by rw [hr2]; linarith) (by rw [hr2]; linarith)).1
    by_contra hneg
    have : C * ‖((r / 2 : ℝ) : ℂ)‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (by rw [hr2]; positivity)
    linarith [norm_nonneg (f (z + ((r / 2 : ℝ) : ℂ)) - f z - α * (((r / 2 : ℝ) : ℂ) + κ * conj ((r / 2 : ℝ) : ℂ)))]
  obtain ⟨r1, hr1d⟩ : ∃ r1 : ℝ, r1 = min r (c0 / (2 * (C + 1))) := ⟨_, rfl⟩
  have hr1 : 0 < r1 := by rw [hr1d]; exact lt_min hr (by positivity)
  have hr1r : r1 ≤ r := by rw [hr1d]; exact min_le_left _ _
  have hr1c : r1 ≤ c0 / (2 * (C + 1)) := by rw [hr1d]; exact min_le_right _ _
  have hopen : IsOpen (f '' ball z r1) := by rw [← he]; exact e.isOpenMap _ isOpen_ball
  obtain ⟨η1, hη1, hb1⟩ := Metric.isOpen_iff.mp hopen (f z) ⟨z, mem_ball_self hr1, rfl⟩
  have hEs : ∀ δ ≤ η1, f ⁻¹' ball (f z) δ ⊆ ball z r1 := fun δ hδ v hv => by
    obtain ⟨w, hw, hwv⟩ := hb1 (ball_subset_ball hδ hv)
    exact hi hwv ▸ hw
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = 4 * C / c0 ^ 2 := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hwd]; positivity
  obtain ⟨δ0, hδ0d⟩ : ∃ δ0 : ℝ, δ0 = min (min η1 (c0 * r)) (1 / (2 * (w + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ0 := by rw [hδ0d]; exact lt_min (lt_min hη1 (mul_pos hc0 hr)) (by positivity)
  have hδη : δ0 ≤ η1 := by rw [hδ0d]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδr : δ0 ≤ c0 * r := by rw [hδ0d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδw : δ0 ≤ 1 / (2 * (w + 1)) := by rw [hδ0d]; exact min_le_right _ _
  set V1 := volume.real {h : ℂ | ‖h + κ * conj h‖ < 1} with hV1d
  have hV1 : 0 ≤ V1 := measureReal_nonneg
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hLm : Measurable fun v : ℂ => ‖v - z + κ * conj (v - z)‖ := by fun_prop
  -- the model term: `|∫_{B_r \ E_δ} m - π c| ≤ 16 |μ(z) α| w V₁ δ`
  have hT0 : Tendsto (fun δ => ∫ v in ball z r \ f ⁻¹' ball (f z) δ, μ z * α * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (π * (μ z * α * conj κ / (1 - ‖κ‖ ^ 2)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg0 : Tendsto (fun δ : ℝ => 16 * ‖μ z * α‖ * w * V1 * δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (16 * ‖μ z * α‖ * w * V1)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg0
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
    have hδp := hδ.1
    have hwδ : w * δ ≤ 1 / 2 := by
      have h1 : δ * (2 * (w + 1)) ≤ 1 := by
        have := hδ.2.le.trans hδw; rwa [le_div_iff₀ (by positivity)] at this
      nlinarith
    have hρ : 0 < δ / ‖α‖ := div_pos hδp ha
    have hρr : δ / ‖α‖ / (1 - ‖κ‖) ≤ r := by
      rw [div_div, ← hc0d, div_le_iff₀ hc0, mul_comm]; exact hδ.2.le.trans hδr
    have hEm : MeasurableSet (f ⁻¹' ball (f z) δ) := hfc.measurable measurableSet_ball
    have hEB : f ⁻¹' ball (f z) δ ⊆ ball z r :=
      (hEs δ (hδ.2.le.trans hδη)).trans (ball_subset_ball hr1r)
    have hgE := ((e124p_integrable hk hμ hμs hε hf hz hδp).2).mono_set (sdiff_subset_sdiff_left hball)
    have hmE : IntegrableOn (fun v => μ z * α * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)
        (ball z r \ f ⁻¹' ball (f z) δ) :=
      (hgE.sub (hrem.mono_set sdiff_subset)).congr_fun (fun v _ => by simp only [Pi.sub_apply]; exact sub_sub_cancel _ _) (measurableSet_ball.diff hEm)
    exact e124p_modelE (μ z * α) hκ ha hc0d hC0 (fun h h0 h1 => (hloc h h0 h1).1) hr1r hr1c
      (hEs δ (hδ.2.le.trans hδη)) hwd hw0 hδp hwδ hρr hEm hmE
  -- the remainder terms
  have hT1 := e124p_rem_tendsto hrem (X := fun δ => f ⁻¹' ball (f z) δ)
    (fun δ => hfc.measurable measurableSet_ball) (fun v hv => by
      have hp : 0 < ‖f v - f z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hv (hi h))
      filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
      rw [mem_preimage, mem_ball, dist_eq_norm, not_lt]
      exact hδ.2.le)
  have hT2 := e124p_rem_tendsto hrem (X := fun δ => ball z (δ / ‖α‖)) (fun δ => measurableSet_ball)
    (fun v hv => by
      have hp : 0 < ‖α‖ * ‖v - z‖ := mul_pos ha (norm_pos_iff.mpr (sub_ne_zero.mpr hv))
      filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
      rw [mem_ball, dist_eq_norm, not_lt, div_le_iff₀ ha, mul_comm]
      exact hδ.2.le)
  have hlim := hT0.add (hT1.sub hT2)
  rw [sub_self, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
  have hδp := hδ.1
  have hρ : 0 < δ / ‖α‖ := div_pos hδp ha
  have hρr : δ / ‖α‖ ≤ r := by
    rw [div_le_iff₀ ha]
    have : c0 ≤ ‖α‖ := by rw [hc0d]; nlinarith [norm_nonneg κ]
    nlinarith [hδ.2.le.trans hδr]
  have hEm : MeasurableSet (f ⁻¹' ball (f z) δ) := hfc.measurable measurableSet_ball
  have hEB : f ⁻¹' ball (f z) δ ⊆ ball z r := (hEs δ (hδ.2.le.trans hδη)).trans (ball_subset_ball hr1r)
  have hIE := (e124p_integrable hk hμ hμs hε hf hz hδp).2
  have hIρ := (e124p_integrable hk hμ hμs hε hf hz hρ).1
  have hgE := hIE.mono_set (sdiff_subset_sdiff_left hball)
  have hgρ := hIρ.mono_set (sdiff_subset_sdiff_left hball)
  have hmE : IntegrableOn (fun v => μ z * α * ((v - z + κ * conj (v - z)) ^ 2)⁻¹)
      (ball z r \ f ⁻¹' ball (f z) δ) :=
    (hgE.sub (hrem.mono_set sdiff_subset)).congr_fun (fun v _ => by simp only [Pi.sub_apply]; exact sub_sub_cancel _ _) (measurableSet_ball.diff hEm)
  obtain ⟨hmρ, hm0⟩ := e124p_model_zero (μ z * α) κ z hκ hρ hρr
  show _ + (_ - _) = _ - _
  rw [e124p_split hball measurableSet_ball hEm hEB hIE,
    e124p_split hball measurableSet_ball measurableSet_ball (ball_subset_ball hρr) hIρ,
    integral_sub hgE hmE, integral_sub hgρ hmρ, hm0]
  ring

/-- **PV conversion** (from `e124_shape`): the image-plane and `v`-plane principal values differ by the shape
term. -/
theorem e124_pv_convert {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ ball z δ,
        dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) =
      limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ f ⁻¹' ball (f z) δ,
          dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) -
        π * (μ z * dz f z * conj (complexDilatation f z) / (1 - ‖complexDilatation f z‖ ^ 2)) := by
  obtain ⟨L, hL⟩ := e124p_v_limit hk hμ hμs hε hf hz
  have hD := e124p_diff_limit hk hμ hμs hε hf hz
  have hα : 0 < ‖dz f z‖ := norm_pos_iff.mpr (e124p_local hk hμ hμs hε hf hz).1
  -- `δ ↦ δ/|α|` maps `𝓝[>] 0` to itself
  have hsc : Tendsto (fun δ : ℝ => δ / ‖dz f z‖) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := ((continuous_id.div_const ‖dz f z‖).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ hα
  have hJ := (hD.add (hL.comp hsc))
  simp only [Function.comp_def, sub_add_cancel] at hJ
  rw [hL.limUnder_eq, hJ.limUnder_eq]
  ring

/-- **Cancellation** (`e124_chain` + `e124_pv_convert`): `∂_z ẇ(z)` is the `v`-plane principal value, with no
extra term. -/
theorem e124_dz_wdot {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun y => -(1 / π) * ∫ v in upperHalf, kernelRU (f y) (f v) * μ v * dz f v ^ 2) z =
      -(1 / π) * limUnder (𝓝[>] (0 : ℝ)) (fun δ => ∫ v in upperHalf \ ball z δ,
        dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) := by
  rw [e124_chain hk hμ hμs hε hf hz, e124_pv_convert hk hμ hμs hε hf hz]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

/-! ### Wirtinger algebra and the `ε`-regularity from W-REG (下属4) -/

/-- `∂` of a function that is locally constant near the point vanishes. -/
theorem e124_dz_eventuallyConst {g : ℂ → ℂ} {ε c : ℂ} (h : g =ᶠ[𝓝 ε] fun _ => c) :
    dz g ε = 0 ∧ dzbar g ε = 0 := by
  unfold dz dzbar
  rw [h.fderiv_eq]
  simp

/-- `∂̄` of a difference. -/
theorem e124_dzbar_sub {φ ψ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z) (hψ : DifferentiableAt ℝ ψ z) :
    dzbar (fun w => φ w - ψ w) z = dzbar φ z - dzbar ψ z := by
  unfold dzbar
  rw [fderiv_fun_sub hφ hψ]
  simp only [sub_apply]
  ring

/-- `∂(1/h) = -∂h/h²`. -/
theorem e124_dz_inv {h : ℂ → ℂ} {ε : ℂ} (hh : DifferentiableAt ℝ h ε) (h0 : h ε ≠ 0) :
    dz (fun e => (h e)⁻¹) ε = -dz h ε / h ε ^ 2 := by
  have hi : DifferentiableAt ℝ (fun e => (h e)⁻¹) ε := hh.inv h0
  have hm := dz_mul hh hi
  have hev : (fun e => h e * (h e)⁻¹) =ᶠ[𝓝 ε] fun _ => (1 : ℂ) := by
    filter_upwards [hh.continuousAt.eventually_ne h0] with e he using mul_inv_cancel₀ he
  rw [(e124_dz_eventuallyConst hev).1] at hm
  have h2 : h ε * dz (fun e => (h e)⁻¹) ε = -((h ε)⁻¹ * dz h ε) := by linear_combination (-1 : ℂ) * hm
  have h3 : dz (fun e => (h e)⁻¹) ε = -((h ε)⁻¹ * dz h ε) * (h ε)⁻¹ := by
    rw [← h2, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  rw [h3]
  ring

/-- `∂̄(1/h) = -∂̄h/h²`. -/
theorem e124_dzbar_inv {h : ℂ → ℂ} {ε : ℂ} (hh : DifferentiableAt ℝ h ε) (h0 : h ε ≠ 0) :
    dzbar (fun e => (h e)⁻¹) ε = -dzbar h ε / h ε ^ 2 := by
  have hi : DifferentiableAt ℝ (fun e => (h e)⁻¹) ε := hh.inv h0
  have hm := dzbar_mul hh hi
  have hev : (fun e => h e * (h e)⁻¹) =ᶠ[𝓝 ε] fun _ => (1 : ℂ) := by
    filter_upwards [hh.continuousAt.eventually_ne h0] with e he using mul_inv_cancel₀ he
  rw [(e124_dz_eventuallyConst hev).2] at hm
  have h2 : h ε * dzbar (fun e => (h e)⁻¹) ε = -((h ε)⁻¹ * dzbar h ε) := by linear_combination (-1 : ℂ) * hm
  have h3 : dzbar (fun e => (h e)⁻¹) ε = -((h ε)⁻¹ * dzbar h ε) * (h ε)⁻¹ := by
    rw [← h2, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
  rw [h3]
  ring

/-- Wirtinger quotient rule for `∂` of `A B / N²`. -/
theorem e124_dz_quot {A B N : ℂ → ℂ} {ε : ℂ} (hA : DifferentiableAt ℝ A ε) (hB : DifferentiableAt ℝ B ε)
    (hN : DifferentiableAt ℝ N ε) (hN0 : N ε ≠ 0) :
    dz (fun e => A e * B e / N e ^ 2) ε =
      (dz A ε * B ε + A ε * dz B ε) / N ε ^ 2 - 2 * A ε * B ε * dz N ε / N ε ^ 3 := by
  have hN2 : DifferentiableAt ℝ (fun e => N e ^ 2) ε := hN.pow 2
  have hN20 : N ε ^ 2 ≠ 0 := pow_ne_zero 2 hN0
  have hinv := e124_dz_inv hN2 hN20
  have hsq : dz (fun e => N e ^ 2) ε = 2 * N ε * dz N ε := by
    rw [show (fun e => N e ^ 2) = fun e => N e * N e by funext e; ring, dz_mul hN hN]
    ring
  have hAB := dz_mul hA hB
  have hfun : (fun e => A e * B e / N e ^ 2) = fun e => (A e * B e) * (N e ^ 2)⁻¹ := by
    funext e
    rw [div_eq_mul_inv]
  have hAB' : DifferentiableAt ℝ (fun e => A e * B e) ε := hA.mul hB
  have hNi : DifferentiableAt ℝ (fun e => (N e ^ 2)⁻¹) ε := hN2.inv hN20
  rw [hfun, dz_mul hAB' hNi, hinv, hsq, hAB]
  field_simp
  ring

/-- Wirtinger quotient rule for `∂̄` of `A B / N²`. -/
theorem e124_dzbar_quot {A B N : ℂ → ℂ} {ε : ℂ} (hA : DifferentiableAt ℝ A ε) (hB : DifferentiableAt ℝ B ε)
    (hN : DifferentiableAt ℝ N ε) (hN0 : N ε ≠ 0) :
    dzbar (fun e => A e * B e / N e ^ 2) ε =
      (dzbar A ε * B ε + A ε * dzbar B ε) / N ε ^ 2 - 2 * A ε * B ε * dzbar N ε / N ε ^ 3 := by
  have hN2 : DifferentiableAt ℝ (fun e => N e ^ 2) ε := hN.pow 2
  have hN20 : N ε ^ 2 ≠ 0 := pow_ne_zero 2 hN0
  have hinv := e124_dzbar_inv hN2 hN20
  have hsq : dzbar (fun e => N e ^ 2) ε = 2 * N ε * dzbar N ε := by
    rw [show (fun e => N e ^ 2) = fun e => N e * N e by funext e; ring, dzbar_mul hN hN]
    ring
  have hAB := dzbar_mul hA hB
  have hfun : (fun e => A e * B e / N e ^ 2) = fun e => (A e * B e) * (N e ^ 2)⁻¹ := by
    funext e
    rw [div_eq_mul_inv]
  have hAB' : DifferentiableAt ℝ (fun e => A e * B e) ε := hA.mul hB
  have hNi : DifferentiableAt ℝ (fun e => (N e ^ 2)⁻¹) ε := hN2.inv hN20
  rw [hfun, dzbar_mul hAB' hNi, hinv, hsq, hAB]
  field_simp
  ring

/-- `ε`-regularity from W-REG E2: `ε ↦ w_{εμ}(z)` and `ε ↦ ∂_z w_{εμ}(z)` are real differentiable. -/
theorem e124_E2_diff {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    DifferentiableAt ℝ (fun e => wU (fun x => e * μ x) z) ε ∧
      DifferentiableAt ℝ (fun e => dz (wU fun y => e * μ y) z) ε := by
  have hC := wr_joint_contDiff_U hk hμ hμs
  have hS : IsOpen {e : ℂ | ‖e‖ * k < 1} := isOpen_lt (continuous_norm.mul continuous_const) continuous_const
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hA : ∀ p ∈ {e : ℂ | ‖e‖ * k < 1} ×ˢ upperHalf,
      ContDiffAt ℝ 3 (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) p :=
    fun p hp => hC.contDiffAt ((hS.prod hU).mem_nhds hp)
  have hpair : DifferentiableAt ℝ (fun e : ℂ => (e, z)) ε := differentiableAt_id.prodMk (differentiableAt_const z)
  constructor
  · have hd := (hA (ε, z) ⟨hε, hz⟩).differentiableAt (by norm_num)
    exact hd.comp ε hpair
  · have hev : ∀ᶠ e in 𝓝 ε, dz (wU fun y => e * μ y) z =
        (2 : ℂ)⁻¹ * (fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z) (0, 1) -
          I * fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z) (0, I)) := by
      filter_upwards [hS.mem_nhds hε] with e he
      have hd : DifferentiableAt ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z) :=
        (hA (e, z) ⟨he, hz⟩).differentiableAt (by norm_num)
      have hcomp : HasFDerivAt (fun y => wU (fun u => e * μ u) y)
          ((fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z)).comp
            (ContinuousLinearMap.inr ℝ ℂ ℂ)) z :=
        hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right e z)
      unfold dz
      rw [hcomp.fderiv, div_eq_inv_mul]
      rfl
    have hf' := (hA (ε, z) ⟨hε, hz⟩).fderiv_right (m := 2) (by norm_num)
    have hd' : DifferentiableAt ℝ
        (fun e : ℂ => fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z)) ε :=
      (hf'.differentiableAt (by norm_num)).comp ε hpair
    have h1 := hd'.clm_apply (differentiableAt_const ((0 : ℂ), (1 : ℂ)))
    have h2 := hd'.clm_apply (differentiableAt_const ((0 : ℂ), I))
    have hsum : DifferentiableAt ℝ (fun e : ℂ =>
        fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z) (0, 1) -
          I * fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (e, z) (0, I)) ε :=
      h1.sub ((differentiableAt_const I).mul h2)
    exact (hsum.const_mul ((2 : ℂ)⁻¹)).congr_of_eventuallyEq hev

/-- `w_{εμ}` is injective. -/
theorem e124_inj {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) : Function.Injective f := by
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf
  obtain ⟨K, hK⟩ := hns.1
  obtain ⟨e, he⟩ := t1_homeomorph hK hns.2.1
  rw [← he]
  exact e.injective

/-- `w_{εμ}` is the symmetric-extension normalized solution `fMuSym (εμ)` of LiZhongQC S33 (the coefficients
`extU` and `symmetricExtension` agree off the real axis). -/
theorem e124_wU_eq_fMuSym {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) : wU (fun y => ε * μ y) = fMuSym (fun y => ε * μ y) := by
  have hν : IsBeltramiCoeff (fun y => ε * μ y) upperHalf (‖ε‖ * k) :=
    ⟨hμ.1.const_mul ε, hμ.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  obtain ⟨-, hN, -, -⟩ := bg_sym_spec (by positivity) hε hν
  have hreal : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    simpa using gzE_volume_im_eq_zero
  have hN' : IsNormalizedSolution (fMuSym (fun y => ε * μ y)) (extU fun y => ε * μ y) := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hN
    refine ⟨h1, h2, h3, h4, ?_⟩
    filter_upwards [h5, hreal] with z hz hz0
    rw [hz]
    by_cases h1 : 0 < z.im
    · simp [symmetricExtension, extU, h1, not_lt.mpr h1.le]
    · have h2 : z.im < 0 := lt_of_le_of_ne (not_lt.mp h1) hz0
      simp [symmetricExtension, extU, h1, h2]
  exact QCV.qcv_ns_eq (by positivity) hε (e124c_extU_beltrami hk hμ ε) hN'

/-- `w_{εμ}` maps `𝕌` into `𝕌`. -/
theorem e124_wU_upper {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) : wU (fun y => ε * μ y) z ∈ upperHalf := by
  have hν : IsBeltramiCoeff (fun y => ε * μ y) upperHalf (‖ε‖ * k) :=
    ⟨hμ.1.const_mul ε, hμ.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  rw [e124_wU_eq_fMuSym hk hμ hε, ← (fMuSym_upperHalf (by positivity) hε hν).1]
  exact mem_image_of_mem _ hz

/-- `f z - \overline{f u} ≠ 0` for `z, u ∈ 𝕌`. -/
theorem e124_ne_conj {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) {ε : ℂ}
    (hε : ‖ε‖ * k < 1) {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    wU (fun y => ε * μ y) z - conj (wU (fun y => ε * μ y) u) ≠ 0 := by
  have h1 : 0 < (wU (fun y => ε * μ y) z).im := e124_wU_upper hk hμ hε hz
  have h2 : 0 < (wU (fun y => ε * μ y) u).im := e124_wU_upper hk hμ hε hu
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at this
  linarith

/-! ### `e124_dz_wdotbar` helpers (下属4) -/

/-- `∂̄` of a holomorphic function vanishes. -/
theorem e124_dzbar_holo {G : ℂ → ℂ} {ζ : ℂ} (hG : DifferentiableAt ℂ G ζ) : dzbar G ζ = 0 := by
  have e : ∀ x, fderiv ℝ G ζ x = fderiv ℂ G ζ x := fun x => by
    rw [hG.fderiv_restrictScalars ℝ]
    rfl
  have hI : fderiv ℂ G ζ I = I * fderiv ℂ G ζ 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [dzbar, e, e, hI]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The `𝕌`-supported source `1_𝕌 μ` is a Beltrami coefficient on `ℂ`. -/
theorem e124_indicator_beltrami {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k) :
    IsBeltramiCoeff (upperHalf.indicator μ) univ k := by
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_univ]
    exact (aestronglyMeasurable_indicator_iff hU).mpr hμ.1
  · rw [Measure.restrict_univ]
    filter_upwards [(ae_restrict_iff' hU).mp hμ.2] with v hv
    by_cases hvU : v ∈ upperHalf
    · rw [indicator_of_mem hvU]
      exact hv hvU
    · rw [indicator_of_notMem hvU, norm_zero]
      exact hk

/-- **Change of variables to the image plane.** With `T = ahT_dot (1_𝕌 μ) (extU εμ) f` and
`κ(u) = \overline{T(ū)}`: `∬_𝕌 K(\overline{f v}) \overline{μ(v) f_v(v)²} = ∬ κ(u) K(u)`. -/
theorem e124_cov_conj {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {K : ℂ → ℂ} (hKm : Measurable K) :
    (∫ v in upperHalf, K (conj (f v)) * conj (μ v * dz f v ^ 2)) =
      ∫ u, conj (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (conj u)) * K u := by
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf
  have hK'm : Measurable (fun w => conj (K (conj w))) :=
    Complex.continuous_conj.measurable.comp (hKm.comp Complex.continuous_conj.measurable)
  have hcov := e124c_cov (by positivity) hε (e124c_extU_beltrami hk hμ ε) hns
    (e124_indicator_beltrami hk hμ) hK'm
  have hemb : MeasurableEmbedding (fun z : ℂ => conj z) := Complex.conjCLE.toHomeomorph.measurableEmbedding
  calc (∫ v in upperHalf, K (conj (f v)) * conj (μ v * dz f v ^ 2))
      = ∫ v, conj (upperHalf.indicator μ v * conj (K (conj (f v))) * dz f v ^ 2) := by
        rw [← integral_indicator hU]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        by_cases hv : v ∈ upperHalf
        · simp only [indicator_of_mem hv, map_mul, map_pow, Complex.conj_conj]
          ring
        · simp [indicator_of_notMem hv]
    _ = conj (∫ v, upperHalf.indicator μ v * conj (K (conj (f v))) * dz f v ^ 2) := integral_conj
    _ = conj (∫ w, ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f w * conj (K (conj w))) := by
        rw [hcov]
    _ = ∫ w, conj (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f w) * K (conj w) := by
        rw [← integral_conj]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [map_mul, Complex.conj_conj]
    _ = ∫ u, conj (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (conj u)) * K u := by
        have h := gzE_conj_measurePreserving.integral_comp hemb
          (fun u => conj (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (conj u)) * K u)
        simp only [Complex.conj_conj] at h
        exact h

/-- `∂_z` of `∂_ε̄ w_{εμ}`: the kernel `R(ζ, \overline{f v})` is regular for `ζ ∈ 𝕌`, so no principal value. -/
theorem e124_dz_wdotbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun y => -(1 / π) * ∫ v in upperHalf, kernelRU (f y) (conj (f v)) * conj (μ v * dz f v ^ 2)) z =
      -(1 / π) * ∫ v in upperHalf, dz f z *
        (1 / (conj (f v) - f z) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) * conj (μ v * dz f v ^ 2) := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hns, hC3, -, -⟩ := e124c_setup hk hμ hμs hε hf
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ → ℂ,
      κ = fun u => conj (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (conj u)) := ⟨_, rfl⟩
  -- `κ` is bounded and vanishes on `𝕌`
  have hTb : IsBeltramiCoeff (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f) univ
      (k / (1 - (‖ε‖ * k) ^ 2)) := by
    obtain ⟨⟨K₀, hK₀⟩, himg, -⟩ := hns
    exact QCV.qcv_dot_beltrami (by positivity) hε (e124c_extU_beltrami hk hμ ε) ⟨K₀, hK₀⟩ himg
      (e124_indicator_beltrami hk hμ)
  have hκb : IsBeltramiCoeff κ univ (k / (1 - (‖ε‖ * k) ^ 2)) := by
    have hmp := gzE_conj_measurePreserving
    obtain ⟨hT1, hT2⟩ := hTb
    rw [Measure.restrict_univ] at hT1 hT2
    rw [hκ]
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ]
      exact Complex.continuous_conj.comp_aestronglyMeasurable (hT1.comp_measurePreserving hmp)
    · rw [Measure.restrict_univ]
      filter_upwards [hmp.quasiMeasurePreserving.ae hT2] with u hu
      simpa using hu
  have hk' : 0 ≤ k / (1 - (‖ε‖ * k) ^ 2) := by
    have : (‖ε‖ * k) ^ 2 < 1 := by nlinarith [mul_nonneg (norm_nonneg ε) hk]
    exact div_nonneg hk (by linarith)
  have hsurj : ∀ w, f (Function.invFunOn f univ w) = w := by
    intro w
    have hw : w ∈ f '' univ := by rw [hns.2.1]; exact mem_univ w
    exact Function.invFunOn_eq hw
  have hzero : ∀ u ∈ upperHalf, κ u = 0 := by
    intro u hu
    have hnot : Function.invFunOn f univ (conj u) ∉ upperHalf := by
      intro hin
      have h1 : wU (fun y => ε * μ y) (Function.invFunOn f univ (conj u)) ∈ upperHalf :=
        e124_wU_upper hk hμ hε hin
      rw [← hf, hsurj] at h1
      have h2 : 0 < (conj u).im := h1
      rw [Complex.conj_im] at h2
      have h3 : 0 < u.im := hu
      linarith
    rw [hκ]
    simp only [ahT_dot, indicator_of_notMem hnot, zero_div, zero_mul, map_zero]
  -- the holomorphic outer function
  have hfz : f z ∈ upperHalf := by rw [hf]; exact e124_wU_upper hk hμ hε hz
  have hG : ∀ ζ, (∫ v in upperHalf, kernelRU ζ (conj (f v)) * conj (μ v * dz f v ^ 2)) =
      ∫ u, κ u * ahKer ζ u := by
    intro ζ
    have hkr : ∀ u, kernelRU ζ u = ahKer ζ u := by
      intro u
      unfold kernelRU ahKer
      ring
    simp only [hkr]
    rw [e124_cov_conj hk hμ hμs hε hf (ahK_measurable ζ), hκ]
  have hD := (QCV.qcv_ahVar_kernel_derivatives hk' hκb hU hzero hfz).1
  have hGd : HasDerivAt (fun ζ => -(1 / π) * ∫ v in upperHalf, kernelRU ζ (conj (f v)) *
      conj (μ v * dz f v ^ 2)) (-(1 / π) * ∫ u, κ u * QCV.kerD1 (f z) u) (f z) := by
    have h := hD.const_mul (-(1 / π) : ℂ)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
    show -(1 / π) * (∫ v in upperHalf, kernelRU ζ (conj (f v)) * conj (μ v * dz f v ^ 2)) =
      -(1 / π) * ∫ u, κ u * ahKer ζ u
    rw [hG ζ]
  have hfd : DifferentiableAt ℝ f z :=
    (hC3.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
  have hcomp := eq6_2_dz_comp hfd (hGd.differentiableAt.restrictScalars ℝ)
  rw [e124_dzbar_holo hGd.differentiableAt, zero_mul, add_zero, dz_eq_deriv hGd.differentiableAt,
    hGd.deriv] at hcomp
  change dz ((fun ζ => -(1 / π) * ∫ v in upperHalf, kernelRU ζ (conj (f v)) *
    conj (μ v * dz f v ^ 2)) ∘ f) z = _
  rw [hcomp]
  -- back to the `v`-plane
  have hm1 : Measurable (QCV.kerD1 (f z)) := by unfold QCV.kerD1; fun_prop
  have hback : (∫ u, κ u * QCV.kerD1 (f z) u) =
      ∫ v in upperHalf, QCV.kerD1 (f z) (conj (f v)) * conj (μ v * dz f v ^ 2) := by
    rw [e124_cov_conj hk hμ hμs hε hf hm1, hκ]
  rw [hback, mul_assoc, ← integral_mul_const]
  congr 1
  refine setIntegral_congr_fun measurableSet_upperHalf_aux fun v hv => ?_
  have hfv : 0 < (f v).im := by
    have : f v ∈ upperHalf := by rw [hf]; exact e124_wU_upper hk hμ hε hv
    exact this
  have h0 : conj (f v) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im, Complex.zero_im] at this
    linarith
  have h1 : conj (f v) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.one_im, Complex.zero_im] at this
    linarith
  show QCV.kerD1 (f z) (conj (f v)) * conj (μ v * dz f v ^ 2) * dz f z = _
  unfold QCV.kerD1
  field_simp
  ring

/-! ### Mixed partials and the quotient rule -/

/-- `∂_ε` and `∂_ε̄` of `(w_{εμ})_z` are `∂_z` of `∂_ε w` and `∂_ε̄ w` (W-REG E2: joint `C³`). -/
theorem e124_mixed {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun e => dz (wU fun y => e * μ y) z) ε = dz (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) z ∧
      dzbar (fun e => dz (wU fun y => e * μ y) z) ε = dz (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) z := by
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hE2 := wr_joint_contDiff_U hk hμ hμs
  have hSo : IsOpen ({ε : ℂ | ‖ε‖ * k < 1} ×ˢ upperHalf) :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod hUo
  have hW : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (ε, z) :=
    (hE2.contDiffAt (hSo.mem_nhds (show (ε, z) ∈ {ε : ℂ | ‖ε‖ * k < 1} ×ˢ upperHalf from ⟨hε, hz⟩))).of_le (by norm_num)
  obtain ⟨-, h1, h2⟩ := l613_wirt_comm hW
  exact ⟨h1, h2⟩

/-- Quotient rule for `∂_ε K_{εμ}(z, u)`. -/
theorem e124_K_dz {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dz (fun e => kernelK (fun y => e * μ y) z u) ε =
      (dz (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) z * dz f u +
          dz f z * dz (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) u) / (f z - f u) ^ 2 -
        2 * dz f z * dz f u * (dz (fun e => wU (fun x => e * μ x) z) ε - dz (fun e => wU (fun x => e * μ x) u) ε) /
          (f z - f u) ^ 3 := by
  have hinj := e124_inj hk hμ hμs hε hf
  have hN0 : f z - f u ≠ 0 := sub_ne_zero.mpr (hinj.ne hzu)
  obtain ⟨hwz, hdz⟩ := e124_E2_diff hk hμ hμs hε hz
  obtain ⟨hwu, hdu⟩ := e124_E2_diff hk hμ hμs hε hu
  have hmz := (e124_mixed hk hμ hμs hε hz).1
  have hmu := (e124_mixed hk hμ hμs hε hu).1
  subst hf
  unfold kernelK
  have hN : DifferentiableAt ℝ
      (fun e => wU (fun x => e * μ x) z - wU (fun x => e * μ x) u) ε := hwz.sub hwu
  rw [e124_dz_quot hdz hdu hN hN0, dz_sub_pointwise hwz hwu, hmz, hmu]

/-- Quotient rule for `∂_ε̄ K_{εμ}(z, u)`. -/
theorem e124_K_dzbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dzbar (fun e => kernelK (fun y => e * μ y) z u) ε =
      (dz (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) z * dz f u +
          dz f z * dz (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) u) / (f z - f u) ^ 2 -
        2 * dz f z * dz f u *
          (dzbar (fun e => wU (fun x => e * μ x) z) ε - dzbar (fun e => wU (fun x => e * μ x) u) ε) /
          (f z - f u) ^ 3 := by
  have hinj := e124_inj hk hμ hμs hε hf
  have hN0 : f z - f u ≠ 0 := sub_ne_zero.mpr (hinj.ne hzu)
  obtain ⟨hwz, hdz⟩ := e124_E2_diff hk hμ hμs hε hz
  obtain ⟨hwu, hdu⟩ := e124_E2_diff hk hμ hμs hε hu
  have hmz := (e124_mixed hk hμ hμs hε hz).2
  have hmu := (e124_mixed hk hμ hμs hε hu).2
  subst hf
  unfold kernelK
  have hN : DifferentiableAt ℝ
      (fun e => wU (fun x => e * μ x) z - wU (fun x => e * μ x) u) ε := hwz.sub hwu
  rw [e124_dzbar_quot hdz hdu hN hN0, e124_dzbar_sub hwz hwu, hmz, hmu]

/-- Quotient rule for `∂_ε K_{εμ}(z, ū)` (`∂_ε \overline{g} = \overline{∂_ε̄ g}`). -/
theorem e124_Kbar_dz {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dz (fun e => kernelKbar (fun y => e * μ y) z u) ε =
      (dz (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) z * conj (dz f u) +
          dz f z * conj (dz (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) u)) / (f z - conj (f u)) ^ 2 -
        2 * dz f z * conj (dz f u) *
          (dz (fun e => wU (fun x => e * μ x) z) ε - conj (dzbar (fun e => wU (fun x => e * μ x) u) ε)) /
          (f z - conj (f u)) ^ 3 := by
  have hN0 := e124_ne_conj hk hμ hε hz hu
  obtain ⟨hwz, hdz⟩ := e124_E2_diff hk hμ hμs hε hz
  obtain ⟨hwu, hdu⟩ := e124_E2_diff hk hμ hμs hε hu
  have hmz := (e124_mixed hk hμ hμs hε hz).1
  have hmu := (e124_mixed hk hμ hμs hε hu).2
  have hdu' : DifferentiableAt ℝ (fun e => conj (dz (wU fun y => e * μ y) u)) ε :=
    Complex.conjCLE.differentiableAt.comp ε hdu
  have hwu' : DifferentiableAt ℝ (fun e => conj (wU (fun x => e * μ x) u)) ε :=
    Complex.conjCLE.differentiableAt.comp ε hwu
  have hN : DifferentiableAt ℝ
      (fun e => wU (fun x => e * μ x) z - conj (wU (fun x => e * μ x) u)) ε := hwz.sub hwu'
  subst hf
  unfold kernelKbar
  rw [e124_dz_quot hdz hdu' hN hN0, dz_sub_pointwise hwz hwu', dz_conj hdu, dz_conj hwu, hmz, hmu]

/-- Quotient rule for `∂_ε̄ K_{εμ}(z, ū)`. -/
theorem e124_Kbar_dzbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dzbar (fun e => kernelKbar (fun y => e * μ y) z u) ε =
      (dz (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) z * conj (dz f u) +
          dz f z * conj (dz (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) u)) / (f z - conj (f u)) ^ 2 -
        2 * dz f z * conj (dz f u) *
          (dzbar (fun e => wU (fun x => e * μ x) z) ε - conj (dz (fun e => wU (fun x => e * μ x) u) ε)) /
          (f z - conj (f u)) ^ 3 := by
  have hN0 := e124_ne_conj hk hμ hε hz hu
  obtain ⟨hwz, hdz⟩ := e124_E2_diff hk hμ hμs hε hz
  obtain ⟨hwu, hdu⟩ := e124_E2_diff hk hμ hμs hε hu
  have hmz := (e124_mixed hk hμ hμs hε hz).2
  have hmu := (e124_mixed hk hμ hμs hε hu).1
  have hdu' : DifferentiableAt ℝ (fun e => conj (dz (wU fun y => e * μ y) u)) ε :=
    Complex.conjCLE.differentiableAt.comp ε hdu
  have hwu' : DifferentiableAt ℝ (fun e => conj (wU (fun x => e * μ x) u)) ε :=
    Complex.conjCLE.differentiableAt.comp ε hwu
  have hN : DifferentiableAt ℝ
      (fun e => wU (fun x => e * μ x) z - conj (wU (fun x => e * μ x) u)) ε := hwz.sub hwu'
  subst hf
  unfold kernelKbar
  rw [e124_dzbar_quot hdz hdu' hN hN0, e124_dzbar_sub hwz hwu', dzbar_conj hdu, dzbar_conj hwu, hmz, hmu]

/-! ### The original statements (byte-identical copies) -/

/-! ### Assembly of (1.24)–(1.25): generic principal-value bookkeeping -/

/-- Dominated convergence for truncations by a family of measurable sets. -/
theorem e124a_dct {g φ : ℂ → ℂ} {S : Set ℂ} (hg : IntegrableOn g S) {B : ℝ → Set ℂ}
    (hB : ∀ δ, MeasurableSet (B δ)) (hφ : ∀ x, φ x = g x ∨ φ x = 0)
    (hpt : ∀ᵐ x ∂(volume.restrict S), ∀ᶠ δ in 𝓝[>] (0 : ℝ), (B δ).indicator g x = φ x) :
    Tendsto (fun δ : ℝ => ∫ x in S, (B δ).indicator g x) (𝓝[>] 0) (𝓝 (∫ x in S, φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖)
  · exact Eventually.of_forall fun δ => hg.aestronglyMeasurable.indicator (hB δ)
  · exact Eventually.of_forall fun δ => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _
  · exact hg.norm
  · filter_upwards [hpt] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun δ h => h.symm)

/-- A point `x ≠ p` eventually leaves the shrinking disc `B(p, δ)`. -/
theorem e124a_far {x p : ℂ} (h : x ≠ p) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), x ∉ ball p δ := by
  filter_upwards [Ioo_mem_nhdsGT (dist_pos.2 h)] with δ hδ hm
  exact lt_asymm (mem_ball.1 hm) hδ.2

/-- One-point principal value at `z`, restricted to the two-point truncation `𝕌 ∖ (B(z,δ) ∪ B(u,δ))`. -/
theorem e124a_pv1 {F : ℂ → ℂ} {z u : ℂ} (hzu : z ≠ u) {L : ℂ}
    (h : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, F v) (𝓝[>] 0) (𝓝 L))
    (hi : ∀ δ : ℝ, 0 < δ → IntegrableOn F (upperHalf \ ball z δ)) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), F v) (𝓝[>] 0) (𝓝 L) := by
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  set δ₀ := dist z u / 2 with hδ₀d
  have hδ₀ : 0 < δ₀ := by have := dist_pos.2 hzu; positivity
  set S₀ := upperHalf \ ball z δ₀ with hS₀d
  have hsh : Tendsto (fun δ : ℝ => ∫ v in S₀, (ball u δ).indicator F v) (𝓝[>] 0) (𝓝 (∫ v in S₀, (0 : ℂ))) := by
    refine e124a_dct (hi δ₀ hδ₀) (fun δ => measurableSet_ball) (fun x => Or.inr rfl) ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume u)] with x hx
    filter_upwards [e124a_far hx] with δ hδ
    exact indicator_of_notMem hδ F
  rw [integral_zero] at hsh
  have hlim := h.sub hsh
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  have hsub : (upperHalf \ ball z δ) ∩ ball u δ ⊆ upperHalf \ ball z δ := inter_subset_left
  have hset : (upperHalf \ ball z δ) ∩ ball u δ = S₀ ∩ ball u δ := by
    ext v
    simp only [mem_inter_iff, mem_diff, mem_ball, hS₀d]
    constructor
    · rintro ⟨⟨hv, -⟩, hvu⟩
      refine ⟨⟨hv, ?_⟩, hvu⟩
      intro hvz
      have := dist_triangle z v u
      rw [dist_comm z v] at this
      linarith [hδ.2]
    · rintro ⟨⟨hv, -⟩, hvu⟩
      refine ⟨⟨hv, ?_⟩, hvu⟩
      intro hvz
      have := dist_triangle z v u
      rw [dist_comm z v] at this
      linarith [hδ.2]
  have e1 : upperHalf \ (ball z δ ∪ ball u δ) = (upperHalf \ ball z δ) \ ((upperHalf \ ball z δ) ∩ ball u δ) := by
    rw [diff_self_inter, diff_diff]
  show (∫ v in upperHalf \ ball z δ, F v) - (∫ v in S₀, (ball u δ).indicator F v) = _
  rw [setIntegral_indicator measurableSet_ball, ← hset, e1,
    integral_diff ((hmU.diff measurableSet_ball).inter measurableSet_ball) (hi δ hδ.1) hsub]

/-- An `L¹(𝕌)` function: two-point truncations converge to the full integral. -/
theorem e124a_reg2 {G : ℂ → ℂ} (z u : ℂ) (hG : IntegrableOn G upperHalf) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), G v) (𝓝[>] 0)
      (𝓝 (∫ v in upperHalf, G v)) := by
  have hd := e124a_dct hG (B := fun δ => (ball z δ ∪ ball u δ)ᶜ)
    (fun δ => (measurableSet_ball.union measurableSet_ball).compl) (φ := G) (fun x => Or.inl rfl) ?_
  · refine hd.congr' (Eventually.of_forall fun δ => ?_)
    dsimp only
    rw [setIntegral_indicator (measurableSet_ball.union measurableSet_ball).compl, diff_eq]
  · filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume z), ae_restrict_of_ae (Measure.ae_ne volume u)]
      with x hxz hxu
    filter_upwards [e124a_far hxz, e124a_far hxu] with δ h1 h2
    exact indicator_of_mem (show x ∉ ball z δ ∪ ball u δ from fun h => h.elim h1 h2) G

/-- One-point principal value at `z` along two-point truncations, `z = u` allowed. -/
theorem e124a_pv1g {F : ℂ → ℂ} {z u : ℂ} {L : ℂ}
    (h : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, F v) (𝓝[>] 0) (𝓝 L))
    (hi : ∀ δ : ℝ, 0 < δ → IntegrableOn F (upperHalf \ ball z δ)) :
    Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), F v) (𝓝[>] 0) (𝓝 L) := by
  by_cases hzu : z = u
  · subst hzu
    simpa only [union_self] using h
  · exact e124a_pv1 hzu h hi

/-- **Generic two-point assembly.** If `F = c₁F₁ + c₂F₂ + c₃G` on `𝕌 ∖ {z, u}`, the two-point truncations of
`F₁`, `F₂` converge to `L₁`, `L₂` and `G ∈ L¹(𝕌)`, then `pv2 F z u = c₁L₁ + c₂L₂ + c₃∫G`. -/
theorem e124a_pv2core {F F₁ F₂ G : ℂ → ℂ} {z u : ℂ} {L₁ L₂ c₁ c₂ c₃ : ℂ}
    (t₁ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), F₁ v) (𝓝[>] 0) (𝓝 L₁))
    (t₂ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), F₂ v) (𝓝[>] 0) (𝓝 L₂))
    (i₁ : ∀ δ : ℝ, 0 < δ → IntegrableOn F₁ (upperHalf \ (ball z δ ∪ ball u δ)))
    (i₂ : ∀ δ : ℝ, 0 < δ → IntegrableOn F₂ (upperHalf \ (ball z δ ∪ ball u δ)))
    (hG : IntegrableOn G upperHalf)
    (hF : ∀ v ∈ upperHalf, v ≠ z → v ≠ u → F v = c₁ * F₁ v + c₂ * F₂ v + c₃ * G v) :
    pv2 F z u = c₁ * L₁ + c₂ * L₂ + c₃ * ∫ v in upperHalf, G v := by
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  have hT : ∀ δ : ℝ, MeasurableSet (upperHalf \ (ball z δ ∪ ball u δ)) := fun δ =>
    hmU.diff (measurableSet_ball.union measurableSet_ball)
  apply Tendsto.limUnder_eq
  refine (((t₁.const_mul c₁).add (t₂.const_mul c₂)).add ((e124a_reg2 z u hG).const_mul c₃)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have j₁ : IntegrableOn (fun v => c₁ * F₁ v) (upperHalf \ (ball z δ ∪ ball u δ)) := (i₁ δ hδ').const_mul c₁
  have j₂ : IntegrableOn (fun v => c₂ * F₂ v) (upperHalf \ (ball z δ ∪ ball u δ)) := (i₂ δ hδ').const_mul c₂
  have jG : IntegrableOn (fun v => c₃ * G v) (upperHalf \ (ball z δ ∪ ball u δ)) :=
    (hG.mono_set sdiff_subset).const_mul c₃
  have j12 : IntegrableOn (fun v => c₁ * F₁ v + c₂ * F₂ v) (upperHalf \ (ball z δ ∪ ball u δ)) :=
    j₁.add j₂
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add j₁ j₂,
    ← integral_add j12 jG]
  refine setIntegral_congr_fun (hT δ) (fun v hv => ?_)
  have hvz : v ≠ z := fun h => hv.2 (Or.inl (by rw [h]; exact mem_ball_self hδ'))
  have hvu : v ≠ u := fun h => hv.2 (Or.inr (by rw [h]; exact mem_ball_self hδ'))
  exact (hF v hv.1 hvz hvu).symm

/-- The two-point assembly with one-point principal values at `z` (for `F₁`) and at `u` (for `F₂`). -/
theorem e124a_pv2 {F F₁ F₂ G : ℂ → ℂ} {z u : ℂ} (hzu : z ≠ u) {L₁ L₂ c₁ c₂ c₃ : ℂ}
    (h₁ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball z δ, F₁ v) (𝓝[>] 0) (𝓝 L₁))
    (h₂ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball u δ, F₂ v) (𝓝[>] 0) (𝓝 L₂))
    (i₁ : ∀ δ : ℝ, 0 < δ → IntegrableOn F₁ (upperHalf \ ball z δ))
    (i₂ : ∀ δ : ℝ, 0 < δ → IntegrableOn F₂ (upperHalf \ ball u δ))
    (hG : IntegrableOn G upperHalf)
    (hF : ∀ v ∈ upperHalf, v ≠ z → v ≠ u → F v = c₁ * F₁ v + c₂ * F₂ v + c₃ * G v) :
    pv2 F z u = c₁ * L₁ + c₂ * L₂ + c₃ * ∫ v in upperHalf, G v := by
  have t₂ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ), F₂ v) (𝓝[>] 0) (𝓝 L₂) := by
    refine (e124a_pv1 (Ne.symm hzu) h₂ i₂).congr' (Eventually.of_forall fun δ => ?_)
    rw [union_comm]
  exact e124a_pv2core (e124a_pv1 hzu h₁ i₁) t₂
    (fun δ hδ => (i₁ δ hδ).mono_set (diff_subset_diff_right subset_union_left))
    (fun δ hδ => (i₂ δ hδ).mono_set (diff_subset_diff_right subset_union_right)) hG hF

/-- Partial fractions: `1/((η-a)²(η-b)²) = (R₁(a,η) + R₁(b,η))/(a-b)² - 2(R(a,η) - R(b,η))/(a-b)³`. -/
theorem e124a_pf {a b η : ℂ} (hab : a ≠ b) (ha : η ≠ a) (hb : η ≠ b) (h0 : η ≠ 0) (h1 : η ≠ 1) :
    1 / ((η - a) ^ 2 * (η - b) ^ 2) =
      ((1 / (η - a) ^ 2 + 1 / η - 1 / (η - 1)) + (1 / (η - b) ^ 2 + 1 / η - 1 / (η - 1))) / (a - b) ^ 2 -
        2 * (kernelRU a η - kernelRU b η) / (a - b) ^ 3 := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have ha' : η - a ≠ 0 := sub_ne_zero.2 ha
  have hb' : η - b ≠ 0 := sub_ne_zero.2 hb
  have h1' : η - 1 ≠ 0 := sub_ne_zero.2 h1
  have ha'' : a - η ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hb'' : b - η ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  unfold kernelRU
  field_simp
  ring

/-- Pointwise Jacobian identity: `J_f(v) ν̇(f v) = μ(v) f_v(v)²` on `𝕌`. -/
theorem e124a_Jpt {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {v : ℂ} (hv : v ∈ upperHalf) :
    (jacobian f v : ℂ) * ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (f v) =
      μ v * dz f v ^ 2 := by
  obtain ⟨hns, -, hJ, hdil⟩ := e124c_setup hk hμ hμs hε hf
  have hinj : InjOn f univ := hns.1.choose_spec.2.2.1.2.1
  have hφ : Function.invFunOn f univ (f v) = v := hinj.leftInvOn_invFunOn (mem_univ v)
  have hdzne : dz f v ≠ 0 := by
    intro h0
    have := hJ v hv
    unfold jacobian at this
    rw [h0, norm_zero] at this
    nlinarith [norm_nonneg (dzbar f v)]
  have hg : (extU fun y => ε * μ y) v = complexDilatation f v := by
    rw [hdil v hv]
    unfold extU
    rw [if_pos (show 0 < v.im from hv)]
  have hdzbar : dzbar f v = complexDilatation f v * dz f v := by
    show dzbar f v = dzbar f v / dz f v * dz f v
    field_simp
  set κ := complexDilatation f v with hκd
  have hlt : ‖κ‖ < 1 := by
    have hJv := hJ v hv
    unfold jacobian at hJv
    rw [hdzbar, norm_mul] at hJv
    by_contra hge
    push_neg at hge
    have h2 : ‖dz f v‖ ≤ ‖κ‖ * ‖dz f v‖ := le_mul_of_one_le_left (norm_nonneg _) hge
    nlinarith [norm_nonneg (dz f v)]
  have hA : (1 : ℂ) - conj κ * κ ≠ 0 := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (by nlinarith [norm_nonneg κ])
  have hJc : (jacobian f v : ℂ) = dz f v * conj (dz f v) * (1 - conj κ * κ) := by
    unfold jacobian
    rw [hdzbar, norm_mul]
    push_cast
    rw [Complex.mul_conj, mul_comm (conj κ) κ, Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    push_cast
    ring
  have hcne : conj (dz f v) ≠ 0 := (map_ne_zero _).2 hdzne
  simp only [ahT_dot, hφ, hg, indicator_of_mem hv]
  rw [hJc]
  field_simp

/-- **Integrability transfer** to the `v`-plane: `ν̇ K ∈ L¹(ℂ)` gives `K(f v) μ(v) f_v(v)² ∈ L¹(𝕌)`. -/
theorem e124a_transfer {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {K : ℂ → ℂ}
    (hK : Integrable (fun η => ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f η * K η)) :
    IntegrableOn (fun v => K (f v) * μ v * dz f v ^ 2) upperHalf := by
  obtain ⟨hns, hC, hJ, -⟩ := e124c_setup hk hμ hμs hε hf
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hmU : MeasurableSet upperHalf := hU.measurableSet
  have hinj : InjOn f univ := hns.1.choose_spec.2.2.1.2.1
  have hd : ∀ x ∈ upperHalf, DifferentiableAt ℝ f x := fun x hx =>
    (hC.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume) hmU
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) (hinj.mono (subset_univ _))
    (fun η => ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f η * K η)).1 hK.integrableOn
  refine h.congr_fun (fun v hv => ?_) hmU
  have hdet : (fderiv ℝ f v).det = jacobian f v := det_fderiv_eq_jacobian (hd v hv)
  show |(fderiv ℝ f v).det| • (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f (f v) * K (f v)) =
    K (f v) * μ v * dz f v ^ 2
  rw [hdet, abs_of_pos (hJ v hv), Complex.real_smul, ← mul_assoc, e124a_Jpt hk hμ hμs hε hf hv]
  ring

/-- `ν K₀` and `ν K₁` are integrable for bounded `ν` vanishing on `B(c, R)`. -/
theorem e124a_nuK_int {ν : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hν : IsBeltramiCoeff ν univ k) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hzero : ∀ u ∈ ball c R, ν u = 0) :
    Integrable (fun u => ν u * ahKer c u) ∧ Integrable (fun u => ν u * QCV.kerD1 c u) := by
  have hνm : AEStronglyMeasurable ν volume := by simpa using hν.1
  have hνb : ∀ᵐ u : ℂ, ‖ν u‖ ≤ k := by simpa using hν.2
  obtain ⟨C, hC, hmaj⟩ := QCV.qcv_kernel_ball_majorant (y := c) (r := R / 8) (by positivity)
  have hm1 : Measurable (QCV.kerD1 c) := by unfold QCV.kerD1; fun_prop
  have hdom : Integrable (fun u => k * (C * ‖ahKer I u‖)) := ((ah_ker_integrable I).norm.const_mul C).const_mul k
  have hb : ∀ {K : ℂ → ℂ}, AEStronglyMeasurable K volume →
      (∀ u : ℂ, u ≠ 0 → u ≠ 1 → u ≠ I → 8 * (R / 8) ≤ ‖u - c‖ → ‖K u‖ ≤ C * ‖ahKer I u‖) →
      Integrable (fun u => ν u * K u) := by
    intro K hKm hK
    refine hdom.mono' (hνm.mul hKm) ?_
    filter_upwards [hνb, Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume (1 : ℂ),
      Measure.ae_ne volume I] with u hu h0 h1 hI
    by_cases hz : ν u = 0
    · rw [hz, zero_mul, norm_zero]
      positivity
    · have hfar : 8 * (R / 8) ≤ ‖u - c‖ := by
        by_contra hlt
        push_neg at hlt
        exact hz (hzero u (by rw [mem_ball, dist_eq_norm]; linarith))
      rw [norm_mul]
      exact mul_le_mul hu (hK u h0 h1 hI hfar) (norm_nonneg _) hk
  exact ⟨hb (ahK_measurable c).aestronglyMeasurable
      (fun u h0 h1 hI hfar => (hmaj u h0 h1 hI hfar c (mem_ball_self (by positivity))).1),
    hb hm1.aestronglyMeasurable
      (fun u h0 h1 hI hfar => (hmaj u h0 h1 hI hfar c (mem_ball_self (by positivity))).2.1)⟩

/-- `R(w, f v) μ(v) f_v(v)² ∈ L¹(𝕌)` for every `w`. -/
theorem e124a_R_int {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) (w : ℂ) :
    IntegrableOn (fun v => kernelRU w (f v) * μ v * dz f v ^ 2) upperHalf := by
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf
  have hk0 : 0 ≤ ‖ε‖ * k := by positivity
  have hνB := QCV.qcv_dot_beltrami hk0 hε (e124c_extU_beltrami hk hμ ε) hns.1 hns.2.1
    (vf_zero_extension_coeff hk hμ)
  have hνm : AEStronglyMeasurable (ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f) volume := by
    simpa using hνB.1
  have hνb : ∀ᵐ x : ℂ, ‖ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f x‖ ≤
      k / (1 - (‖ε‖ * k) ^ 2) := by simpa using hνB.2
  have h := e124a_transfer hk hμ hμs hε hf ((ah_ker_integrable w).bdd_mul hνm hνb)
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  refine h.congr_fun (fun v _ => ?_) hmU
  simp only [kernelRU, ahKer]
  ring

/-- **(1.24), `∂_ε` part.** -/
theorem e124a_24dz {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dz (fun e => kernelK (fun y => e * μ y) z u) ε =
      -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelK (fun y => ε * μ y) v u) z u := by
  rw [e124_K_dz hk hμ hμs hε rfl hz hu hzu]
  have hW := fun y => (eq_1_21 hk hμ hε y).1
  have hfun : (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (wU (fun y => ε * μ y) v) * μ v *
        dz (wU fun y => ε * μ y) v ^ 2 := funext hW
  rw [hfun, e124_dz_wdot hk hμ hμs hε rfl hz, e124_dz_wdot hk hμ hμs hε rfl hu, hW z, hW u]
  obtain ⟨Lz, hLz⟩ := e124p_v_limit hk hμ hμs hε rfl hz
  obtain ⟨Lu, hLu⟩ := e124p_v_limit hk hμ hμs hε rfl hu
  rw [hLz.limUnder_eq, hLu.limUnder_eq]
  unfold kernelK
  generalize hf : wU (fun y => ε * μ y) = f at hLz hLu ⊢
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf.symm
  have hinj := e124_inj hk hμ hμs hε hf.symm
  have hf0 : f 0 = 0 := hns.2.2.1
  have hf1 : f 1 = 1 := hns.2.2.2.1
  have hab : f z ≠ f u := fun h => hzu (hinj h)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hab' : f z - f u ≠ 0 := sub_ne_zero.2 hab
  have hRz := e124a_R_int hk hμ hμs hε hf.symm (f z)
  have hRu := e124a_R_int hk hμ hμs hε hf.symm (f u)
  rw [e124a_pv2 (F₁ := fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2)
    (F₂ := fun v => dz f u * (1 / (f v - f u) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2)
    (G := fun v => kernelRU (f z) (f v) * μ v * dz f v ^ 2 - kernelRU (f u) (f v) * μ v * dz f v ^ 2)
    (c₁ := dz f u / (f z - f u) ^ 2) (c₂ := dz f z / (f z - f u) ^ 2)
    (c₃ := -2 * dz f z * dz f u / (f z - f u) ^ 3) hzu hLz hLu
    (fun δ hδ => (e124p_integrable hk hμ hμs hε hf.symm hz hδ).1)
    (fun δ hδ => (e124p_integrable hk hμ hμs hε hf.symm hu hδ).1) (hRz.sub hRu) ?_,
    integral_sub hRz hRu]
  · field_simp
    ring
  · intro v hv hvz hvu
    have hv0 : f v ≠ 0 := fun h => by
      have := hinj (h.trans hf0.symm)
      rw [this] at hv
      have h' : (0 : ℝ) < (0 : ℂ).im := hv
      simp at h'
    have hv1 : f v ≠ 1 := fun h => by
      have := hinj (h.trans hf1.symm)
      rw [this] at hv
      have h' : (0 : ℝ) < (1 : ℂ).im := hv
      simp at h'
    have hvz' : f v ≠ f z := fun h => hvz (hinj h)
    have hvu' : f v ≠ f u := fun h => hvu (hinj h)
    have hpf := e124a_pf hab hvz' hvu' hv0 hv1
    have hz' : f z - f v ≠ 0 := sub_ne_zero.2 (Ne.symm hvz')
    have hu' : f v - f u ≠ 0 := sub_ne_zero.2 hvu'
    have hz'' : f v - f z ≠ 0 := sub_ne_zero.2 hvz'
    have e1 : μ v * (dz f z * dz f v / (f z - f v) ^ 2) * (dz f v * dz f u / (f v - f u) ^ 2) =
        dz f z * dz f u * (μ v * dz f v ^ 2) * (1 / ((f v - f z) ^ 2 * (f v - f u) ^ 2)) := by
      field_simp
      ring
    rw [e1, hpf]
    ring

/-- Conjugation preserves integrability. -/
theorem e124a_conj_int {g : ℂ → ℂ} {s : Set ℂ} (h : IntegrableOn g s) :
    IntegrableOn (fun v => conj (g v)) s :=
  Integrable.mono' h.norm (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (Eventually.of_forall fun v => (Complex.norm_conj _).le)

/-- `\overline{R(w, x)} = R(w̄, x̄)`. -/
theorem e124a_conjRU (w x : ℂ) : conj (kernelRU w x) = kernelRU (conj w) (conj x) := by
  unfold kernelRU
  simp only [map_div₀, map_mul, map_sub, map_one]

/-- `\overline{R₁(w, x)} = R₁(w̄, x̄)`. -/
theorem e124a_conjR1 (w x : ℂ) :
    conj (1 / (x - w) ^ 2 + 1 / x - 1 / (x - 1)) = 1 / (conj x - conj w) ^ 2 + 1 / conj x - 1 / (conj x - 1) := by
  simp only [map_div₀, map_add, map_sub, map_pow, map_one]

/-- `R₁(c, f v) μ(v) f_v(v)² ∈ L¹(𝕌)` for `c` in the lower half-plane (`f(𝕌) ⊆ 𝕌`, so `ν̇ = 0` near `c`). -/
theorem e124a_R1c_int {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) {c : ℂ} (hc : c.im < 0) :
    IntegrableOn (fun v => (1 / (f v - c) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2) upperHalf := by
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf
  have hk0 : 0 ≤ ‖ε‖ * k := by positivity
  have hνB := QCV.qcv_dot_beltrami hk0 hε (e124c_extU_beltrami hk hμ ε) hns.1 hns.2.1
    (vf_zero_extension_coeff hk hμ)
  have hk' : 0 ≤ k / (1 - (‖ε‖ * k) ^ 2) := div_nonneg hk (by nlinarith)
  have hup : ∀ v ∈ upperHalf, f v ∈ upperHalf := fun v hv => by
    rw [hf]
    exact e124_wU_upper hk hμ hε hv
  have hsurj : ∀ η, f (Function.invFunOn f univ η) = η := by
    intro η
    have hm : η ∈ f '' univ := by rw [hns.2.1]; exact mem_univ η
    obtain ⟨x, -, hx⟩ := hm
    exact Function.invFunOn_eq ⟨x, mem_univ x, hx⟩
  have hzero : ∀ η ∈ ball c (-c.im), ahT_dot (upperHalf.indicator μ) (extU fun y => ε * μ y) f η = 0 := by
    intro η hη
    have hnot : Function.invFunOn f univ η ∉ upperHalf := by
      intro hm
      have h1 := hup _ hm
      rw [hsurj] at h1
      have h2 : |η.im - c.im| ≤ ‖η - c‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      rw [mem_ball, dist_eq_norm] at hη
      have h3 : 0 < η.im := h1
      have h4 := (abs_lt.1 (lt_of_le_of_lt h2 hη)).2
      linarith
    simp only [ahT_dot, indicator_of_notMem hnot, zero_div, zero_mul]
  have h := e124a_transfer hk hμ hμs hε hf (e124a_nuK_int hk' hνB (by linarith) hzero).2
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  refine h.congr_fun (fun v hv => ?_) hmU
  have hfv : 0 < (f v).im := hup v hv
  have h0 : f v ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hfv; exact lt_irrefl 0 hfv
  have h1 : f v - 1 ≠ 0 := fun h0 => by
    rw [sub_eq_zero] at h0
    rw [h0, Complex.one_im] at hfv
    exact lt_irrefl 0 hfv
  show QCV.kerD1 c (f v) * μ v * dz f v ^ 2 = _
  unfold QCV.kerD1
  field_simp
  ring

/-- The regular kernels of the `∂_ε̄` parts are in `L¹(𝕌)`. -/
theorem e124a_bar_int {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1) {f : ℂ → ℂ}
    (hf : f = wU (fun y => ε * μ y)) (d w : ℂ) {a : ℂ} (ha : a ∈ upperHalf) :
    IntegrableOn (fun v => d * (1 / (conj (f v) - a) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) *
        conj (μ v * dz f v ^ 2)) upperHalf ∧
      IntegrableOn (fun v => kernelRU w (conj (f v)) * conj (μ v * dz f v ^ 2)) upperHalf := by
  have hmU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  have hc : (conj a).im < 0 := by
    rw [Complex.conj_im]
    have : 0 < a.im := ha
    linarith
  constructor
  · have h := e124a_conj_int ((e124a_R1c_int hk hμ hμs hε hf hc).const_mul (conj d))
    refine h.congr_fun (fun v _ => ?_) hmU
    simp only [map_mul, map_pow, Complex.conj_conj, e124a_conjR1]
    ring
  · have h := e124a_conj_int (e124a_R_int hk hμ hμs hε hf (conj w))
    refine h.congr_fun (fun v _ => ?_) hmU
    simp only [map_mul, map_pow, e124a_conjRU, Complex.conj_conj]
    ring

/-- **(1.24), `∂_ε̄` part** (no singularity: `\overline{f v}` lies in the lower half-plane). -/
theorem e124a_24dzbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dzbar (fun e => kernelK (fun y => e * μ y) z u) ε =
      -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
        kernelKbar (fun y => ε * μ y) u v) z u := by
  rw [e124_K_dzbar hk hμ hμs hε rfl hz hu hzu]
  have hW := fun y => (eq_1_21 hk hμ hε y).2
  have hfun : (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (conj (wU (fun y => ε * μ y) v)) *
        conj (μ v * dz (wU fun y => ε * μ y) v ^ 2) := funext hW
  rw [hfun, e124_dz_wdotbar hk hμ hμs hε rfl hz, e124_dz_wdotbar hk hμ hμs hε rfl hu, hW z, hW u]
  have hza := e124_wU_upper hk hμ hε hz
  have hub := e124_wU_upper hk hμ hε hu
  unfold kernelKbar
  generalize hf : wU (fun y => ε * μ y) = f at hza hub ⊢
  have hinj := e124_inj hk hμ hμs hε hf.symm
  have hup : ∀ v ∈ upperHalf, f v ∈ upperHalf := fun v hv => by
    rw [← hf]
    exact e124_wU_upper hk hμ hε hv
  have hab : f z - f u ≠ 0 := sub_ne_zero.2 (fun h => hzu (hinj h))
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨hF1, hRz⟩ := e124a_bar_int hk hμ hμs hε hf.symm (dz f z) (f z) hza
  obtain ⟨hF2, hRu⟩ := e124a_bar_int hk hμ hμs hε hf.symm (dz f u) (f u) hub
  rw [e124a_pv2core
    (F₁ := fun v => dz f z * (1 / (conj (f v) - f z) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) *
      conj (μ v * dz f v ^ 2))
    (F₂ := fun v => dz f u * (1 / (conj (f v) - f u) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) *
      conj (μ v * dz f v ^ 2))
    (G := fun v => kernelRU (f z) (conj (f v)) * conj (μ v * dz f v ^ 2) -
      kernelRU (f u) (conj (f v)) * conj (μ v * dz f v ^ 2))
    (c₁ := dz f u / (f z - f u) ^ 2) (c₂ := dz f z / (f z - f u) ^ 2)
    (c₃ := -2 * dz f z * dz f u / (f z - f u) ^ 3) (e124a_reg2 z u hF1) (e124a_reg2 z u hF2)
    (fun δ _ => hF1.mono_set sdiff_subset) (fun δ _ => hF2.mono_set sdiff_subset) (hRz.sub hRu) ?_,
    integral_sub hRz hRu]
  · field_simp
    ring
  · intro v hv _ _
    have hfv : 0 < (f v).im := hup v hv
    have hza' : 0 < (f z).im := hza
    have hub' : 0 < (f u).im := hub
    have hc : (conj (f v)).im < 0 := by rw [Complex.conj_im]; linarith
    have n1 : conj (f v) - f z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.zero_im] at this
      linarith
    have n2 : conj (f v) - f u ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.zero_im] at this
      linarith
    have n3 : f z - conj (f v) ≠ 0 := fun h => n1 (by linear_combination -h)
    have n4 : f u - conj (f v) ≠ 0 := fun h => n2 (by linear_combination -h)
    have n5 : conj (f v) ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.zero_im] at this
      linarith
    have n6 : conj (f v) - 1 ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.one_im, Complex.zero_im] at this
      linarith
    unfold kernelRU
    simp only [map_mul, map_pow]
    field_simp
    ring

/-- **(1.25), `∂_ε` part** (principal value at `v = z` only; `\overline{f u}` is off `f(𝕌)`). -/
theorem e124a_25dz {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dz (fun e => kernelKbar (fun y => e * μ y) z u) ε =
      -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelKbar (fun y => ε * μ y) v u) z u := by
  rw [e124_Kbar_dz hk hμ hμs hε rfl hz hu]
  have hW1 := fun y => (eq_1_21 hk hμ hε y).1
  have hW2 := fun y => (eq_1_21 hk hμ hε y).2
  have hfun1 : (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (wU (fun y => ε * μ y) v) * μ v *
        dz (wU fun y => ε * μ y) v ^ 2 := funext hW1
  have hfun2 : (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (conj (wU (fun y => ε * μ y) v)) *
        conj (μ v * dz (wU fun y => ε * μ y) v ^ 2) := funext hW2
  rw [hfun1, hfun2, e124_dz_wdot hk hμ hμs hε rfl hz, e124_dz_wdotbar hk hμ hμs hε rfl hu, hW1 z, hW2 u]
  obtain ⟨Lz, hLz⟩ := e124p_v_limit hk hμ hμs hε rfl hz
  rw [hLz.limUnder_eq]
  have hza := e124_wU_upper hk hμ hε hz
  have hub := e124_wU_upper hk hμ hε hu
  unfold kernelK kernelKbar
  generalize hf : wU (fun y => ε * μ y) = f at hLz hza hub ⊢
  obtain ⟨hns, -⟩ := e124c_setup hk hμ hμs hε hf.symm
  have hinj := e124_inj hk hμ hμs hε hf.symm
  have hup : ∀ v ∈ upperHalf, f v ∈ upperHalf := fun v hv => by
    rw [← hf]
    exact e124_wU_upper hk hμ hε hv
  have hza' : 0 < (f z).im := hza
  have hub' : 0 < (f u).im := hub
  have hab : f z - conj (f u) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨hX, -⟩ := e124a_bar_int hk hμ hμs hε hf.symm (dz f u) 0 hub
  obtain ⟨-, hY⟩ := e124a_bar_int hk hμ hμs hε hf.symm 0 (f u) hub
  have hRz := e124a_R_int hk hμ hμs hε hf.symm (f z)
  have hF2 := e124a_conj_int hX
  have hYc := e124a_conj_int hY
  rw [e124a_pv2core
    (F₁ := fun v => dz f z * (1 / (f v - f z) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2)
    (F₂ := fun v => conj (dz f u * (1 / (conj (f v) - f u) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) *
      conj (μ v * dz f v ^ 2)))
    (G := fun v => kernelRU (f z) (f v) * μ v * dz f v ^ 2 -
      conj (kernelRU (f u) (conj (f v)) * conj (μ v * dz f v ^ 2)))
    (c₁ := conj (dz f u) / (f z - conj (f u)) ^ 2) (c₂ := dz f z / (f z - conj (f u)) ^ 2)
    (c₃ := -2 * dz f z * conj (dz f u) / (f z - conj (f u)) ^ 3)
    (e124a_pv1g hLz (fun δ hδ => (e124p_integrable hk hμ hμs hε hf.symm hz hδ).1))
    (e124a_reg2 z u hF2)
    (fun δ hδ => (e124p_integrable hk hμ hμs hε hf.symm hz hδ).1.mono_set
      (diff_subset_diff_right subset_union_left))
    (fun δ _ => hF2.mono_set sdiff_subset) (hRz.sub hYc) ?_,
    integral_sub hRz hYc, integral_conj, integral_conj]
  · simp only [map_mul, map_neg, map_div₀, map_one, Complex.conj_ofReal]
    field_simp
    ring
  · intro v hv hvz _
    have hfv : 0 < (f v).im := hup v hv
    have n0 : f v ≠ 0 := fun h => by rw [h, Complex.zero_im] at hfv; exact lt_irrefl 0 hfv
    have n1 : f v - 1 ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.one_im, Complex.zero_im] at this
      linarith
    have n2 : f v - f z ≠ 0 := sub_ne_zero.2 (fun h => hvz (hinj h))
    have n3 : f z - f v ≠ 0 := fun h => n2 (by linear_combination -h)
    have n4 : f v - conj (f u) ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have n5 : conj (f u) - f v ≠ 0 := fun h => n4 (by linear_combination -h)
    unfold kernelRU
    simp only [map_mul, map_pow, map_div₀, map_add, map_sub, map_one, Complex.conj_conj]
    field_simp
    ring

/-- **(1.25), `∂_ε̄` part** (principal value at `v = u` only). -/
theorem e124a_25dzbar {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dzbar (fun e => kernelKbar (fun y => e * μ y) z u) ε =
      -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
        kernelKbarbar (fun y => ε * μ y) v u) z u := by
  rw [e124_Kbar_dzbar hk hμ hμs hε rfl hz hu]
  have hW1 := fun y => (eq_1_21 hk hμ hε y).1
  have hW2 := fun y => (eq_1_21 hk hμ hε y).2
  have hfun1 : (fun y => dz (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (wU (fun y => ε * μ y) v) * μ v *
        dz (wU fun y => ε * μ y) v ^ 2 := funext hW1
  have hfun2 : (fun y => dzbar (fun e => wU (fun x => e * μ x) y) ε) = fun y =>
      -(1 / π) * ∫ v in upperHalf, kernelRU (wU (fun y => ε * μ y) y) (conj (wU (fun y => ε * μ y) v)) *
        conj (μ v * dz (wU fun y => ε * μ y) v ^ 2) := funext hW2
  rw [hfun2, hfun1, e124_dz_wdotbar hk hμ hμs hε rfl hz, e124_dz_wdot hk hμ hμs hε rfl hu, hW2 z, hW1 u]
  obtain ⟨Lu, hLu⟩ := e124p_v_limit hk hμ hμs hε rfl hu
  rw [hLu.limUnder_eq]
  have hza := e124_wU_upper hk hμ hε hz
  have hub := e124_wU_upper hk hμ hε hu
  unfold kernelKbar kernelKbarbar kernelK
  generalize hf : wU (fun y => ε * μ y) = f at hLu hza hub ⊢
  have hinj := e124_inj hk hμ hμs hε hf.symm
  have hup : ∀ v ∈ upperHalf, f v ∈ upperHalf := fun v hv => by
    rw [← hf]
    exact e124_wU_upper hk hμ hε hv
  have hza' : 0 < (f z).im := hza
  have hub' : 0 < (f u).im := hub
  have hab : f z - conj (f u) ≠ 0 := fun h => by
    have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  obtain ⟨hF1, hRz⟩ := e124a_bar_int hk hμ hμs hε hf.symm (dz f z) (f z) hza
  have hRu := e124a_conj_int (e124a_R_int hk hμ hμs hε hf.symm (f u))
  have hi : ∀ δ : ℝ, 0 < δ → IntegrableOn
      (fun v => conj (dz f u * (1 / (f v - f u) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2))
      (upperHalf \ ball u δ) := fun δ hδ =>
    e124a_conj_int (e124p_integrable hk hμ hμs hε hf.symm hu hδ).1
  have hLc : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ ball u δ,
      conj (dz f u * (1 / (f v - f u) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2))
      (𝓝[>] 0) (𝓝 (conj Lu)) := by
    refine ((Complex.continuous_conj.tendsto Lu).comp hLu).congr' (Eventually.of_forall fun δ => ?_)
    exact integral_conj.symm
  have t₂ : Tendsto (fun δ : ℝ => ∫ v in upperHalf \ (ball z δ ∪ ball u δ),
      conj (dz f u * (1 / (f v - f u) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2))
      (𝓝[>] 0) (𝓝 (conj Lu)) := by
    refine (e124a_pv1g (u := z) hLc hi).congr' (Eventually.of_forall fun δ => ?_)
    rw [union_comm]
  rw [e124a_pv2core
    (F₁ := fun v => dz f z * (1 / (conj (f v) - f z) ^ 2 + 1 / conj (f v) - 1 / (conj (f v) - 1)) *
      conj (μ v * dz f v ^ 2))
    (F₂ := fun v => conj (dz f u * (1 / (f v - f u) ^ 2 + 1 / f v - 1 / (f v - 1)) * μ v * dz f v ^ 2))
    (G := fun v => kernelRU (f z) (conj (f v)) * conj (μ v * dz f v ^ 2) -
      conj (kernelRU (f u) (f v) * μ v * dz f v ^ 2))
    (c₁ := conj (dz f u) / (f z - conj (f u)) ^ 2) (c₂ := dz f z / (f z - conj (f u)) ^ 2)
    (c₃ := -2 * dz f z * conj (dz f u) / (f z - conj (f u)) ^ 3)
    (e124a_reg2 z u hF1) t₂ (fun δ _ => hF1.mono_set sdiff_subset)
    (fun δ hδ => (hi δ hδ).mono_set (diff_subset_diff_right subset_union_right)) (hRz.sub hRu) ?_,
    integral_sub hRz hRu, integral_conj]
  · simp only [map_mul, map_neg, map_div₀, map_one, Complex.conj_ofReal]
    field_simp
    ring
  · intro v hv _ hvu
    have hfv : 0 < (f v).im := hup v hv
    have n0 : f v ≠ 0 := fun h => by rw [h, Complex.zero_im] at hfv; exact lt_irrefl 0 hfv
    have n1 : f v - 1 ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.one_im, Complex.zero_im] at this
      linarith
    have n2 : f v - f u ≠ 0 := sub_ne_zero.2 (fun h => hvu (hinj h))
    have n3 : conj (f v) - f z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith
    have n4 : f z - conj (f v) ≠ 0 := fun h => n3 (by linear_combination -h)
    have n5 : conj (f v) ≠ 0 := (map_ne_zero _).2 n0
    have n6 : conj (f v) - 1 ≠ 0 := fun h => n1 (by
      have := congrArg conj h
      simpa using this)
    have n7 : conj (f v) - conj (f u) ≠ 0 := fun h => n2 (by
      have := congrArg conj h
      simpa using this)
    have n8 : conj (f u) - conj (f v) ≠ 0 := fun h => n7 (by linear_combination -h)
    unfold kernelRU
    simp only [map_mul, map_pow, map_div₀, map_add, map_sub, map_one, Complex.conj_conj]
    field_simp
    ring

/-- **(1.24)** (TT:1301–1305), [Ahl62]. For `z, u ∈ 𝕌`, in the principal value sense:
`∂/∂ε K_{εμ}(z, u) = -(1/π) ∬_𝕌 μ(v) K_{εμ}(z, v) K_{εμ}(v, u) d²v`,
`∂/∂ε̄ K_{εμ}(z, u) = -(1/π) ∬_𝕌 \overline{μ(v)} K_{εμ}(z, v̄) K_{εμ}(v̄, u) d²v`.

[CORRECTION 2026-10-25, user-approved] `μ` is assumed `C^∞` on `𝕌`. For merely measurable `μ`, the derivative
`(w_{εμ})_z` at a fixed point and the principal value at `v = z, u` need not exist (found by 下属3). TT applies the
formula to harmonic Beltrami differentials, which are smooth. -/
theorem e124_eq_1_24 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dz (fun e => kernelK (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelK (fun y => ε * μ y) v u) z u ∧
      dzbar (fun e => kernelK (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
          kernelKbar (fun y => ε * μ y) u v) z u := by
  exact ⟨e124a_24dz hk hμ hμs hε hz hu hzu, e124a_24dzbar hk hμ hμs hε hz hu hzu⟩

/-- **(1.25)** (TT:1314–1320). For `z, u ∈ 𝕌`, in the principal value sense:
`∂/∂ε K_{εμ}(z, ū) = -(1/π) ∬_𝕌 μ(v) K_{εμ}(z, v) K_{εμ}(v, ū) d²v`,
`∂/∂ε̄ K_{εμ}(z, ū) = -(1/π) ∬_𝕌 \overline{μ(v)} K_{εμ}(z, v̄) K_{εμ}(v̄, ū) d²v`.

[CORRECTION 2026-10-25, user-approved] `μ` is assumed `C^∞` on `𝕌`, as in (1.24). -/
theorem e124_eq_1_25 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dz (fun e => kernelKbar (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelKbar (fun y => ε * μ y) v u) z u ∧
      dzbar (fun e => kernelKbar (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
          kernelKbarbar (fun y => ε * μ y) v u) z u := by
  exact ⟨e124a_25dz hk hμ hμs hε hz hu, e124a_25dzbar hk hμ hμs hε hz hu⟩

/-- **(1.24)** (TT:1301–1305), [Ahl62]. For `z, u ∈ 𝕌`, in the principal value sense:
`∂/∂ε K_{εμ}(z, u) = -(1/π) ∬_𝕌 μ(v) K_{εμ}(z, v) K_{εμ}(v, u) d²v`,
`∂/∂ε̄ K_{εμ}(z, u) = -(1/π) ∬_𝕌 \overline{μ(v)} K_{εμ}(z, v̄) K_{εμ}(v̄, u) d²v`.

[CORRECTION 2026-10-25, user-approved] `μ` is assumed `C^∞` on `𝕌`. For merely measurable `μ`, the derivative
`(w_{εμ})_z` at a fixed point and the principal value at `v = z, u` need not exist (found by 下属3). TT applies the
formula to harmonic Beltrami differentials, which are smooth. -/
theorem eq_1_24 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) (hzu : z ≠ u) :
    dz (fun e => kernelK (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelK (fun y => ε * μ y) v u) z u ∧
      dzbar (fun e => kernelK (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
          kernelKbar (fun y => ε * μ y) u v) z u :=
  e124_eq_1_24 hk hμ hμs hε hz hu hzu

/-- **(1.25)** (TT:1314–1320). For `z, u ∈ 𝕌`, in the principal value sense:
`∂/∂ε K_{εμ}(z, ū) = -(1/π) ∬_𝕌 μ(v) K_{εμ}(z, v) K_{εμ}(v, ū) d²v`,
`∂/∂ε̄ K_{εμ}(z, ū) = -(1/π) ∬_𝕌 \overline{μ(v)} K_{εμ}(z, v̄) K_{εμ}(v̄, ū) d²v`.

[CORRECTION 2026-10-25, user-approved] `μ` is assumed `C^∞` on `𝕌`, as in (1.24). -/
theorem eq_1_25 {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hμ : IsBeltramiCoeff μ upperHalf k)
    (hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ upperHalf) {ε : ℂ} (hε : ‖ε‖ * k < 1)
    {z u : ℂ} (hz : z ∈ upperHalf) (hu : u ∈ upperHalf) :
    dz (fun e => kernelKbar (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => μ v * kernelK (fun y => ε * μ y) z v * kernelKbar (fun y => ε * μ y) v u) z u ∧
      dzbar (fun e => kernelKbar (fun y => e * μ y) z u) ε =
        -(1 / π) * pv2 (fun v => conj (μ v) * kernelKbar (fun y => ε * μ y) z v *
          kernelKbarbar (fun y => ε * μ y) v u) z u :=
  e124_eq_1_25 hk hμ hμs hε hz hu

end TakhtajanTeo
