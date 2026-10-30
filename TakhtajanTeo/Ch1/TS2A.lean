import TakhtajanTeo.Ch1.TS2

/-!
# TS2, first conjunct: Zygmund ⇒ `u₊‴ ∈ A∞` (Littlewood–Paley route) — INTERFACE (stubs)
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo
namespace TS2A

open LiZhongQC

/-- Fourier coefficient of a real function. -/
abbrev cf (u : ℝ → ℝ) (n : ℤ) : ℂ := fourierCoeff (fun θ => (u θ : ℂ)) n

/-! ### A. Dyadic piecewise-linear partition of unity on `n ≥ 1` -/

/-- Hat function with vertices `2^k/2, 2^k, 2^(k+1)`. -/
def hatK (k : ℕ) (n : ℤ) : ℝ :=
  max 0 (min (((n : ℝ) - 2 ^ k / 2) / (2 ^ k / 2)) ((2 ^ (k + 1) - (n : ℝ)) / 2 ^ k))

theorem hatK_nonneg (k : ℕ) (n : ℤ) : 0 ≤ hatK k n := le_max_left _ _

theorem hatK_le_one (k : ℕ) (n : ℤ) : hatK k n ≤ 1 := by
  unfold hatK
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  refine max_le zero_le_one ?_
  by_cases hn : (n : ℝ) ≤ 2 ^ k
  · refine (min_le_left _ _).trans ?_
    rw [div_le_one (by positivity)]
    linarith
  · refine (min_le_right _ _).trans ?_
    rw [div_le_one hN]
    rw [pow_succ]
    linarith

theorem hatK_support {k : ℕ} {n : ℤ} (h : hatK k n ≠ 0) : 2 ^ k / 2 < (n : ℝ) ∧ (n : ℝ) < 2 ^ (k + 1) := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  unfold hatK at h
  have hpos : 0 < min (((n : ℝ) - 2 ^ k / 2) / (2 ^ k / 2)) ((2 ^ (k + 1) - (n : ℝ)) / 2 ^ k) := by
    by_contra hneg
    exact h (max_eq_left (not_lt.1 hneg))
  obtain ⟨h1, h2⟩ := lt_min_iff.1 hpos
  refine ⟨?_, ?_⟩
  · have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ k / 2)).1 h1
    linarith
  · have := (div_pos_iff_of_pos_right hN).1 h2
    linarith

/-- `Σ_k hat_k(n) = 1` for `n ≥ 1` (at most two nonzero terms). -/
theorem hatK_partition {n : ℤ} (hn : 1 ≤ n) : HasSum (fun k : ℕ => hatK k n) 1 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  have hm : 1 ≤ m := by omega
  set k0 := Nat.log 2 m with hk0
  have h1 : 2 ^ k0 ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : m < 2 ^ (k0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h1' : (2 : ℝ) ^ k0 ≤ m := by exact_mod_cast h1
  have h2' : (m : ℝ) < 2 ^ (k0 + 1) := by exact_mod_cast h2
  have hcast : (((m : ℕ) : ℤ) : ℝ) = (m : ℝ) := by simp
  have hzero : ∀ k ∉ ({k0, k0 + 1} : Finset ℕ), hatK k (m : ℤ) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    unfold hatK
    rw [hcast]
    rcases lt_or_gt_of_ne hk.1 with hlt | hgt
    · have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ k0 := pow_le_pow_right₀ (by norm_num) (by omega)
      refine max_eq_left ((min_le_right _ _).trans ?_)
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · have : (2 : ℝ) ^ (k0 + 2) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (2 : ℝ) ^ (k0 + 1) * 2 = 2 ^ (k0 + 2) := by ring
      refine max_eq_left ((min_le_left _ _).trans ?_)
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hsum : HasSum (fun k : ℕ => hatK k (m : ℤ)) (∑ k ∈ ({k0, k0 + 1} : Finset ℕ), hatK k (m : ℤ)) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hne : k0 ≠ k0 + 1 := by omega
  rw [Finset.sum_pair hne] at hsum
  have hN : (0 : ℝ) < 2 ^ k0 := by positivity
  have e0 : hatK k0 (m : ℤ) = (2 ^ (k0 + 1) - (m : ℝ)) / 2 ^ k0 := by
    unfold hatK
    rw [hcast]
    have ha : 1 ≤ ((m : ℝ) - 2 ^ k0 / 2) / (2 ^ k0 / 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hb1 : (2 ^ (k0 + 1) - (m : ℝ)) / 2 ^ k0 ≤ 1 := by
      rw [div_le_one hN, pow_succ]; linarith
    have hb0 : 0 ≤ (2 ^ (k0 + 1) - (m : ℝ)) / 2 ^ k0 := div_nonneg (by linarith) hN.le
    rw [min_eq_right (hb1.trans ha), max_eq_right hb0]
  have e1 : hatK (k0 + 1) (m : ℤ) = ((m : ℝ) - 2 ^ k0) / 2 ^ k0 := by
    unfold hatK
    rw [hcast]
    have hN1 : (0 : ℝ) < 2 ^ (k0 + 1) := by positivity
    have ha0 : 0 ≤ ((m : ℝ) - 2 ^ (k0 + 1) / 2) / (2 ^ (k0 + 1) / 2) := by
      apply div_nonneg _ (by positivity)
      rw [pow_succ]; linarith
    have ha1 : ((m : ℝ) - 2 ^ (k0 + 1) / 2) / (2 ^ (k0 + 1) / 2) ≤
        (2 ^ (k0 + 1 + 1) - (m : ℝ)) / 2 ^ (k0 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hN1]
      rw [pow_succ, pow_succ]
      have h2'' : (m : ℝ) < 2 ^ k0 * 2 := by rw [pow_succ] at h2'; exact h2'
      nlinarith [mul_pos hN (sub_pos.2 h2'')]
    rw [min_eq_left ha1, max_eq_right ha0]
    rw [pow_succ]
    field_simp
  rw [e0, e1] at hsum
  convert hsum using 1
  field_simp
  rw [pow_succ]
  ring

/-! ### B. `L¹` bound for the kernel of a smooth, finitely supported multiplier -/

theorem kl_norm_exp (n : ℤ) (t : ℝ) : ‖exp ((n : ℂ) * (t : ℂ) * I)‖ = 1 := by
  have : (n : ℂ) * (t : ℂ) * I = (((n : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

/-- Shifting the index of a finitely supported sequence multiplies the kernel by a phase. -/
theorem kl_shift {a b : ℤ} {ν : ℤ → ℂ} (hν : ∀ n, n < a ∨ b < n → ν n = 0) (t : ℝ) (c : ℤ)
    (hc : |c| ≤ 1) :
    ∑ n ∈ Finset.Icc (a - 1) (b + 1), ν (n + c) * exp ((n : ℂ) * (t : ℂ) * I) =
      exp (-(c : ℂ) * (t : ℂ) * I) * ∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I) := by
  have h1 : ∑ n ∈ Finset.Icc (a - 1) (b + 1), ν (n + c) * exp ((n : ℂ) * (t : ℂ) * I) =
      ∑ m ∈ Finset.Icc (a - 1 + c) (b + 1 + c), ν m * exp (((m : ℂ) - c) * (t : ℂ) * I) := by
    rw [← Finset.map_add_right_Icc, Finset.sum_map]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [addRightEmbedding_apply]
    push_cast
    ring_nf
  rw [h1]
  have hsub : Finset.Icc a b ⊆ Finset.Icc (a - 1 + c) (b + 1 + c) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    have := abs_le.1 hc
    omega
  rw [← Finset.sum_subset hsub (fun x _ hx => by
    have : x < a ∨ b < x := by simp only [Finset.mem_Icc, not_and_or, not_le] at hx; exact hx
    simp [hν x this]), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- Pointwise bounds for the kernel `K(t) = Σ ν_n e^{int}`. -/
theorem kl_pointwise {a b : ℤ} {ν : ℤ → ℂ} (hν : ∀ n, n < a ∨ b < n → ν n = 0) {S B : ℝ}
    (hS : ∑ n ∈ Finset.Icc a b, ‖ν n‖ ≤ S)
    (hB : ∑ n ∈ Finset.Icc (a - 1) (b + 1), ‖ν (n + 1) - 2 * ν n + ν (n - 1)‖ ≤ B) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖ ≤ S ∧
      ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖ * (2 - 2 * Real.cos t) ≤ B := by
  set K : ℂ := ∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I) with hK
  refine ⟨?_, ?_⟩
  · refine (norm_sum_le _ _).trans (le_trans ?_ hS)
    refine Finset.sum_le_sum (fun n _ => ?_)
    rw [norm_mul, kl_norm_exp, mul_one]
  · have h1 := kl_shift hν t 1 (by norm_num)
    have h2 := kl_shift hν t (-1) (by norm_num)
    have h0 := kl_shift hν t 0 (by norm_num)
    have key : ∑ n ∈ Finset.Icc (a - 1) (b + 1), (ν (n + 1) - 2 * ν n + ν (n - 1)) *
        exp ((n : ℂ) * (t : ℂ) * I) = (exp (-(t : ℂ) * I) + exp ((t : ℂ) * I) - 2) * K := by
      have e : ∀ n : ℤ, (ν (n + 1) - 2 * ν n + ν (n - 1)) * exp ((n : ℂ) * (t : ℂ) * I) =
          ν (n + 1) * exp ((n : ℂ) * (t : ℂ) * I) - 2 * (ν (n + 0) * exp ((n : ℂ) * (t : ℂ) * I)) +
            ν (n + -1) * exp ((n : ℂ) * (t : ℂ) * I) := by
        intro n; simp only [add_zero, sub_eq_add_neg]; ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h0, h2]
      simp only [Int.cast_one, Int.cast_zero, Int.cast_neg, neg_zero, zero_mul, Complex.exp_zero,
        one_mul, neg_neg]
      rw [← hK]; ring
    have hcos : exp (-(t : ℂ) * I) + exp ((t : ℂ) * I) - 2 = ((2 * Real.cos t - 2 : ℝ) : ℂ) := by
      have : exp (-(t : ℂ) * I) + exp ((t : ℂ) * I) = 2 * Complex.cos t := by
        rw [Complex.cos]; ring_nf
      rw [this]; push_cast; rfl
    rw [hcos] at key
    have hn := congrArg norm key
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
    have hab : |2 * Real.cos t - 2| = 2 - 2 * Real.cos t := by
      rw [abs_of_nonpos (by linarith [Real.cos_le_one t])]; ring
    rw [hab] at hn
    calc ‖K‖ * (2 - 2 * Real.cos t) = (2 - 2 * Real.cos t) * ‖K‖ := mul_comm _ _
      _ = ‖∑ n ∈ Finset.Icc (a - 1) (b + 1), (ν (n + 1) - 2 * ν n + ν (n - 1)) *
            exp ((n : ℂ) * (t : ℂ) * I)‖ := hn.symm
      _ ≤ ∑ n ∈ Finset.Icc (a - 1) (b + 1), ‖(ν (n + 1) - 2 * ν n + ν (n - 1)) *
            exp ((n : ℂ) * (t : ℂ) * I)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc (a - 1) (b + 1), ‖ν (n + 1) - 2 * ν n + ν (n - 1)‖ := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, kl_norm_exp, mul_one]
      _ ≤ B := hB

theorem kl_cos_lower (s : ℝ) (hs : |s| ≤ π) : 4 * s ^ 2 / π ^ 2 ≤ 2 - 2 * Real.cos s := by
  have h1 : 2 - 2 * Real.cos s = 4 * Real.sin (s / 2) ^ 2 := by
    have h : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 := by
      have := Real.cos_two_mul (s / 2)
      rw [show 2 * (s / 2) = s by ring, Real.cos_sq'] at this
      linarith
    rw [h]; ring
  have h2 : |s| / π ≤ Real.sin (|s| / 2) := by
    have := Real.mul_le_sin (x := |s| / 2) (by positivity) (by linarith)
    have e : 2 / π * (|s| / 2) = |s| / π := by field_simp
    rwa [e] at this
  have h3 : Real.sin (s / 2) ^ 2 = Real.sin (|s| / 2) ^ 2 := by
    rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg, neg_sq]
  rw [h1, h3]
  have h4 : (|s| / π) ^ 2 ≤ Real.sin (|s| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have e2 : (|s| / π) ^ 2 = s ^ 2 / π ^ 2 := by rw [div_pow, sq_abs]
  rw [e2] at h4
  have : 4 * s ^ 2 / π ^ 2 = 4 * (s ^ 2 / π ^ 2) := by ring
  rw [this]; linarith

/-- Pure real-variable integral estimate. -/
theorem kl_int_bound {f : ℝ → ℝ} (hc : Continuous f) {S c : ℝ} (hS0 : 0 ≤ S) (hc0 : 0 ≤ c)
    (hf0 : ∀ t, 0 ≤ f t) (hfS : ∀ t, f t ≤ S)
    (hfc : ∀ t, 0 < |t| → |t| ≤ π → f t ≤ c / t ^ 2) :
    ∫ t in (-π)..π, f t ≤ 4 * Real.sqrt (S * c) := by
  have hδ : ∀ δ : ℝ, 0 < δ → ∫ t in (-π)..π, f t ≤ 2 * δ * S + 2 * c / δ := by
    intro δ hδ0
    set m := min δ π with hm
    have hm0 : 0 < m := lt_min hδ0 Real.pi_pos
    have hmπ : m ≤ π := min_le_right _ _
    have hmδ : m ≤ δ := min_le_left _ _
    have hI1 : IntervalIntegrable f volume (-π) (-m) := hc.intervalIntegrable _ _
    have hI2 : IntervalIntegrable f volume (-m) m := hc.intervalIntegrable _ _
    have hI3 : IntervalIntegrable f volume m π := hc.intervalIntegrable _ _
    have hsplit : ∫ t in (-π)..π, f t =
        (∫ t in (-π)..(-m), f t) + (∫ t in (-m)..m, f t) + ∫ t in m..π, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hI1 (hI2.trans hI3),
        ← intervalIntegral.integral_add_adjacent_intervals hI2 hI3]
      ring
    -- the tail integral of `c / t²`
    have hg : ∀ t ∈ Set.Icc m π, c / t ^ 2 = c * t ^ (-2 : ℤ) := by
      intro t _
      rw [zpow_neg, zpow_two, div_eq_mul_inv]; simp [sq]
    have hgc : ContinuousOn (fun t : ℝ => c * t ^ (-2 : ℤ)) (Set.Icc m π) :=
      continuousOn_const.mul (continuousOn_id.zpow₀ _ (fun t ht => Or.inl (by
        exact (lt_of_lt_of_le hm0 ht.1).ne')))
    have htail : ∫ t in m..π, c * t ^ (-2 : ℤ) = c * (1 / m - 1 / π) := by
      rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, by
        rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> linarith⟩)]
      simp only [show (-2 : ℤ) + 1 = -1 by norm_num, zpow_neg, zpow_one]
      field_simp
      ring
    have hright : ∫ t in m..π, f t ≤ c * (1 / m - 1 / π) := by
      rw [← htail]
      refine intervalIntegral.integral_mono_on hmπ hI3 (hgc.intervalIntegrable_of_Icc hmπ) (fun t ht => ?_)
      rw [← hg t ht]
      exact hfc t (by rw [abs_of_pos (lt_of_lt_of_le hm0 ht.1)]; exact lt_of_lt_of_le hm0 ht.1)
        (by rw [abs_of_pos (lt_of_lt_of_le hm0 ht.1)]; exact ht.2)
    have hleft : ∫ t in (-π)..(-m), f t ≤ c * (1 / m - 1 / π) := by
      have := intervalIntegral.integral_comp_neg (a := m) (b := π) (f := f)
      rw [show (-π) = -π from rfl] at this
      rw [← this, ← htail]
      refine intervalIntegral.integral_mono_on hmπ (by
        exact (hc.comp continuous_neg).intervalIntegrable _ _) (hgc.intervalIntegrable_of_Icc hmπ) (fun t ht => ?_)
      rw [← hg t ht]
      have hp : 0 < t := lt_of_lt_of_le hm0 ht.1
      have := hfc (-t) (by rw [abs_neg, abs_of_pos hp]; exact hp) (by rw [abs_neg, abs_of_pos hp]; exact ht.2)
      simpa [neg_sq] using this
    have hmid : ∫ t in (-m)..m, f t ≤ 2 * m * S := by
      have := intervalIntegral.integral_mono_on (a := -m) (b := m) (by linarith) hI2
        (intervalIntegrable_const (c := S)) (fun t _ => hfS t)
      rw [intervalIntegral.integral_const] at this
      simp only [smul_eq_mul] at this
      linarith
    have hcm : 1 / m - 1 / π ≤ 1 / δ := by
      rcases le_total δ π with h | h
      · rw [hm, min_eq_left h]
        have : 0 ≤ 1 / π := by positivity
        linarith
      · rw [hm, min_eq_right h]
        have : 0 < 1 / δ := by positivity
        linarith
    rw [hsplit]
    have hc1 : c * (1 / m - 1 / π) ≤ c * (1 / δ) := mul_le_mul_of_nonneg_left hcm hc0
    have hm2 : 2 * m * S ≤ 2 * δ * S := by nlinarith
    calc _ ≤ c * (1 / m - 1 / π) + 2 * m * S + c * (1 / m - 1 / π) := by linarith
      _ ≤ c * (1 / δ) + 2 * δ * S + c * (1 / δ) := by linarith
      _ = 2 * δ * S + 2 * c / δ := by ring
  -- optimisation in `δ`
  have hε : ∀ ε : ℝ, 0 < ε → ∫ t in (-π)..π, f t ≤ 4 * Real.sqrt ((S + ε) * (c + ε)) := by
    intro ε hε0
    set δ := Real.sqrt ((c + ε) / (S + ε)) with hδdef
    have hSe : 0 < S + ε := by linarith
    have hce : 0 < c + ε := by linarith
    have hδ0 : 0 < δ := Real.sqrt_pos.2 (div_pos hce hSe)
    have h := hδ δ hδ0
    have hsq : δ ^ 2 = (c + ε) / (S + ε) := Real.sq_sqrt (div_pos hce hSe).le
    have hsq' : δ ^ 2 * (S + ε) = c + ε := by rw [hsq]; field_simp
    have e1 : δ * (S + ε) = Real.sqrt ((S + ε) * (c + ε)) := by
      refine (Real.sqrt_sq (by positivity : 0 ≤ δ * (S + ε))).symm.trans ?_
      congr 1
      nlinarith [hsq']
    have e2 : (c + ε) / δ = Real.sqrt ((S + ε) * (c + ε)) := by
      rw [← e1, div_eq_iff hδ0.ne']
      nlinarith [hsq']
    calc _ ≤ 2 * δ * S + 2 * c / δ := h
      _ ≤ 2 * δ * (S + ε) + 2 * (c + ε) / δ := by
          have : 0 < δ := hδ0
          have h1 : 2 * δ * S ≤ 2 * δ * (S + ε) := by nlinarith
          have h2 : 2 * c / δ ≤ 2 * (c + ε) / δ := by
            apply div_le_div_of_nonneg_right _ hδ0.le; linarith
          linarith
      _ = 4 * Real.sqrt ((S + ε) * (c + ε)) := by
          have : 2 * (c + ε) / δ = 2 * ((c + ε) / δ) := by ring
          rw [this, e2, show 2 * δ * (S + ε) = 2 * (δ * (S + ε)) by ring, e1]; ring
  have hlim : Tendsto (fun ε : ℝ => 4 * Real.sqrt ((S + ε) * (c + ε))) (𝓝[>] 0) (𝓝 (4 * Real.sqrt (S * c))) := by
    have : Continuous fun ε : ℝ => 4 * Real.sqrt ((S + ε) * (c + ε)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun ε hε0 => hε ε hε0))

/-- `∫_{-π}^{π} |Σ ν_n e^{int}| dt ≤ 2π √(S B)` where `S ≥ Σ|ν_n|` and `B ≥ Σ|Δ²ν_n|`
(double Abel summation: `|K(t)| (2 - 2 cos t) ≤ B`, `|K| ≤ S`). -/
theorem kernel_L1 {a b : ℤ} {ν : ℤ → ℂ} (hν : ∀ n, n < a ∨ b < n → ν n = 0) {S B : ℝ}
    (hS : ∑ n ∈ Finset.Icc a b, ‖ν n‖ ≤ S)
    (hB : ∑ n ∈ Finset.Icc (a - 1) (b + 1), ‖ν (n + 1) - 2 * ν n + ν (n - 1)‖ ≤ B) :
    ∫ t in (-π)..π, ‖∑ n ∈ Finset.Icc a b, ν n * exp (n * t * I)‖ ≤ 2 * π * Real.sqrt (S * B) := by
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hS
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hB
  have hcont : Continuous fun t : ℝ => ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖ := by
    fun_prop
  have key := kl_int_bound (f := fun t : ℝ => ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖)
    hcont hS0 (c := π ^ 2 * B / 4) (by positivity) (fun t => norm_nonneg _)
    (fun t => (kl_pointwise hν hS hB t).1) (by
      intro t ht0 htπ
      have h2 := (kl_pointwise hν hS hB t).2
      have h3 := kl_cos_lower t htπ
      have ht2 : 0 < t ^ 2 := by
        have : t ≠ 0 := abs_pos.1 ht0
        positivity
      have hπ : 0 < π ^ 2 := by positivity
      set F := ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖
      have hF : 0 ≤ F := norm_nonneg _
      show F ≤ π ^ 2 * B / 4 / t ^ 2
      rw [le_div_iff₀ ht2]
      have h4 : F * (4 * t ^ 2 / π ^ 2) ≤ B := le_trans (mul_le_mul_of_nonneg_left h3 hF) h2
      have h5 : F * (4 * t ^ 2) ≤ B * π ^ 2 := by
        have := mul_le_mul_of_nonneg_right h4 hπ.le
        calc F * (4 * t ^ 2) = F * (4 * t ^ 2 / π ^ 2) * π ^ 2 := by field_simp
          _ ≤ B * π ^ 2 := this
      nlinarith)
  refine key.trans (le_of_eq ?_)
  have : Real.sqrt (S * (π ^ 2 * B / 4)) = π / 2 * Real.sqrt (S * B) := by
    rw [show S * (π ^ 2 * B / 4) = (π / 2) ^ 2 * (S * B) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [this]; ring

/-! ### C. A Zygmund function: multiplier bound through second differences -/

theorem mb_periodic_g {u : ℝ → ℝ} (hp : ∀ θ, u (θ + 2 * π) = u θ) (n : ℤ) :
    Function.Periodic (fun s : ℝ => (u s : ℂ) * exp (-((n : ℂ) * (s : ℂ) * I))) (2 * π) := by
  intro s
  show (u (s + 2 * π) : ℂ) * exp (-((n : ℂ) * ((s + 2 * π : ℝ) : ℂ) * I)) =
    (u s : ℂ) * exp (-((n : ℂ) * (s : ℂ) * I))
  rw [hp s]
  congr 1
  rw [show -((n : ℂ) * ((s + 2 * π : ℝ) : ℂ) * I) =
      -((n : ℂ) * (s : ℂ) * I) + ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem mb_fc_shift {u : ℝ → ℝ} (hp : ∀ θ, u (θ + 2 * π) = u θ) (n : ℤ) (h : ℝ) :
    fourierCoeff (fun s => (u (s + h) : ℂ)) n =
      exp ((n : ℂ) * (h : ℂ) * I) * fourierCoeff (fun θ => (u θ : ℂ)) n := by
  unfold fourierCoeff
  have hg := mb_periodic_g hp n
  have e1 : ∀ s : ℝ, (u (s + h) : ℂ) * exp (-((n : ℂ) * (s : ℂ) * I)) =
      exp ((n : ℂ) * (h : ℂ) * I) * ((u (s + h) : ℂ) * exp (-((n : ℂ) * ((s + h : ℝ) : ℂ) * I))) := by
    intro s
    have : exp (-((n : ℂ) * (s : ℂ) * I)) =
        exp ((n : ℂ) * (h : ℂ) * I) * exp (-((n : ℂ) * ((s + h : ℝ) : ℂ) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  have h2 : ∫ s in (0:ℝ)..2 * π, (u (s + h) : ℂ) * exp (-((n : ℂ) * ((s + h : ℝ) : ℂ) * I)) =
      ∫ s in (0:ℝ)..2 * π, (u s : ℂ) * exp (-((n : ℂ) * (s : ℂ) * I)) := by
    have := intervalIntegral.integral_comp_add_right
      (fun s : ℝ => (u s : ℂ) * exp (-((n : ℂ) * (s : ℂ) * I))) (a := 0) (b := 2 * π) h
    refine this.trans ?_
    rw [show 2 * π + h = h + 2 * π by ring, show (0:ℝ) + h = h by ring]
    have := hg.intervalIntegral_add_eq h 0
    rw [this]; simp
  rw [intervalIntegral.integral_congr (fun s _ => e1 s), intervalIntegral.integral_const_mul, h2]
  ring

theorem mb_fc_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeff (fun s => f s + g s) n = fourierCoeff f n + fourierCoeff g n := by
  unfold fourierCoeff
  have hi : ∀ k : ℝ → ℂ, Continuous k →
      IntervalIntegrable (fun θ => k θ * exp (-((n : ℂ) * (θ : ℂ) * I))) volume 0 (2 * π) := by
    intro k hk
    exact (hk.mul (by fun_prop)).intervalIntegrable _ _
  simp only [add_mul]
  rw [intervalIntegral.integral_add (hi f hf) (hi g hg)]
  ring

theorem mb_fc_smul {g : ℝ → ℂ} (c : ℂ) (n : ℤ) :
    fourierCoeff (fun s => c * g s) n = c * fourierCoeff g n := by
  unfold fourierCoeff
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul]; ring

theorem mb_fc_D {u : ℝ → ℝ} (hc : Continuous u) (hp : ∀ θ, u (θ + 2 * π) = u θ) (n : ℤ) (h : ℝ) :
    fourierCoeff (fun s => (u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ))) n =
      fourierCoeff (fun θ => (u θ : ℂ)) n * (2 * Real.cos (n * h) - 2) := by
  have hcu : Continuous fun s : ℝ => (u s : ℂ) := Complex.continuous_ofReal.comp hc
  have c1 : Continuous fun s : ℝ => (u (s + h) : ℂ) := hcu.comp (continuous_id.add continuous_const)
  have c2 : Continuous fun s : ℝ => (u (s + -h) : ℂ) := hcu.comp (continuous_id.add continuous_const)
  have c3 : Continuous fun s : ℝ => (u (s + -h) : ℂ) + (-2) * (u s : ℂ) :=
    c2.add (continuous_const.mul hcu)
  rw [mb_fc_add (f := fun s => (u (s + h) : ℂ)) (g := fun s => (u (s + -h) : ℂ) + (-2) * (u s : ℂ)) c1 c3 n,
    mb_fc_add (f := fun s => (u (s + -h) : ℂ)) (g := fun s => (-2) * (u s : ℂ)) c2
      (continuous_const.mul hcu) n,
    mb_fc_smul (g := fun s => (u s : ℂ)) (-2) n, mb_fc_shift hp n h, mb_fc_shift hp n (-h)]
  have hcos : exp ((n : ℂ) * (h : ℂ) * I) + exp ((n : ℂ) * ((-h : ℝ) : ℂ) * I) =
      2 * Complex.cos ((n : ℂ) * (h : ℂ)) := by
    rw [Complex.two_cos, show (n : ℂ) * ((-h : ℝ) : ℂ) * I = -((n : ℂ) * (h : ℂ)) * I by push_cast; ring]
  push_cast at hcos ⊢
  linear_combination (fourierCoeff (fun θ => (u θ : ℂ)) n) * hcos

theorem mb_sum_eq {D : ℝ → ℂ} (hD : Continuous D) (a b : ℤ) (ν : ℤ → ℂ) (θ : ℝ) :
    ∑ n ∈ Finset.Icc a b, ν n * fourierCoeff D n * exp ((n : ℂ) * (θ : ℂ) * I) =
      (1 / (2 * (π : ℂ))) * ∫ s in (0:ℝ)..2 * π,
        D s * ∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I) := by
  have hint : ∀ n ∈ Finset.Icc a b, IntervalIntegrable
      (fun s : ℝ => D s * (ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I))) volume 0 (2 * π) := by
    intro n _
    exact (hD.mul (continuous_const.mul (by fun_prop))).intervalIntegrable _ _
  simp only [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold fourierCoeff
  have hs : ∀ s : ℝ, D s * (ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I)) =
      (ν n * exp ((n : ℂ) * (θ : ℂ) * I)) * (D s * exp (-((n : ℂ) * (s : ℂ) * I))) := by
    intro s
    have : exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I) =
        exp ((n : ℂ) * (θ : ℂ) * I) * exp (-((n : ℂ) * (s : ℂ) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [intervalIntegral.integral_congr (fun s _ => hs s), intervalIntegral.integral_const_mul]
  ring

/-- `‖Σ ν_n c_n (2 cos(nh) - 2) e^{inθ}‖ ≤ C |h| √(S B)`: the sum is `(1/2π) ∫ D_h u(θ - t) K_ν(t) dt` with
`D_h u(θ) = u(θ + h) + u(θ - h) - 2 u(θ)`, `|D_h u| ≤ C|h|`. -/
theorem mult_bound {u : ℝ → ℝ} (hc : Continuous u) (hp : ∀ θ, u (θ + 2 * π) = u θ) {C : ℝ}
    (hC : ∀ θ t, |u (θ + t) + u (θ - t) - 2 * u θ| ≤ C * |t|)
    {a b : ℤ} {ν : ℤ → ℂ} (hν : ∀ n, n < a ∨ b < n → ν n = 0) {S B : ℝ}
    (hS : ∑ n ∈ Finset.Icc a b, ‖ν n‖ ≤ S)
    (hB : ∑ n ∈ Finset.Icc (a - 1) (b + 1), ‖ν (n + 1) - 2 * ν n + ν (n - 1)‖ ≤ B) (h θ : ℝ) :
    ‖∑ n ∈ Finset.Icc a b, ν n * (cf u n * (2 * Real.cos (n * h) - 2)) * exp (n * θ * I)‖ ≤
      C * |h| * Real.sqrt (S * B) := by
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0 1)
  have hcu : Continuous fun s : ℝ => (u s : ℂ) := Complex.continuous_ofReal.comp hc
  have c1 : Continuous fun s : ℝ => (u (s + h) : ℂ) := hcu.comp (continuous_id.add continuous_const)
  have c2 : Continuous fun s : ℝ => (u (s + -h) : ℂ) := hcu.comp (continuous_id.add continuous_const)
  have hDcont : Continuous fun s : ℝ => (u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ)) :=
    c1.add (c2.add (continuous_const.mul hcu))
  have e : (∑ n ∈ Finset.Icc a b, ν n * (cf u n * (2 * Real.cos (n * h) - 2)) * exp (n * θ * I)) =
      ∑ n ∈ Finset.Icc a b, ν n * fourierCoeff
        (fun s => (u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ))) n *
          exp ((n : ℂ) * (θ : ℂ) * I) :=
    Finset.sum_congr rfl (fun n _ => by rw [mb_fc_D hc hp n h])
  rw [e, mb_sum_eq hDcont a b ν θ]
  have hD_le : ∀ s : ℝ, ‖(u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ))‖ ≤ C * |h| := by
    intro s
    have e2 : (u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ)) =
        ((u (s + h) + u (s - h) - 2 * u s : ℝ) : ℂ) := by
      push_cast; rw [← sub_eq_add_neg]; ring
    rw [e2, Complex.norm_real, Real.norm_eq_abs]
    exact hC s h
  have hkk : Continuous fun t : ℝ => ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖ := by
    fun_prop
  have hper : Function.Periodic
      (fun t : ℝ => ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖) (2 * π) := by
    intro t
    show ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((t + 2 * π : ℝ) : ℂ) * I)‖ = _
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    rw [show (n : ℂ) * ((t + 2 * π : ℝ) : ℂ) * I = (n : ℂ) * (t : ℂ) * I + ((n : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hint : ‖∫ s in (0:ℝ)..2 * π, ((u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ))) *
        ∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I)‖ ≤
      ∫ s in (0:ℝ)..2 * π, C * |h| *
        ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I)‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by positivity)
      (Filter.Eventually.of_forall (fun s _ => ?_)) ?_
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD_le s) (norm_nonneg _)
    · exact (continuous_const.mul (hkk.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul] at hint
  have hflip : ∫ s in (0:ℝ)..2 * π, ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I)‖ =
      ∫ t in (-π)..π, ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖ := by
    have h1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π)
      (fun t : ℝ => ‖∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * (t : ℂ) * I)‖) θ
    have h2 := hper.intervalIntegral_add_eq (θ - 2 * π) (-π)
    beta_reduce at h1 h2
    rw [h1, show θ - 0 = θ - 2 * π + 2 * π by ring, h2, show -π + 2 * π = π by ring]
  rw [hflip] at hint
  have hL1 := kernel_L1 hν hS hB
  have hn : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]
    simp [abs_of_pos Real.pi_pos]
  have hS0 : 0 ≤ S := le_trans (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hS
  rw [norm_mul, hn]
  have hCh : 0 ≤ C * |h| := by positivity
  have hpi : 0 < 2 * π := by positivity
  calc 1 / (2 * π) * ‖∫ s in (0:ℝ)..2 * π, ((u (s + h) : ℂ) + ((u (s + -h) : ℂ) + (-2) * (u s : ℂ))) *
        ∑ n ∈ Finset.Icc a b, ν n * exp ((n : ℂ) * ((θ - s : ℝ) : ℂ) * I)‖
      ≤ 1 / (2 * π) * (C * |h| * (2 * π * Real.sqrt (S * B))) :=
        mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hL1 hCh)) (by positivity)
    _ = C * |h| * Real.sqrt (S * B) := by field_simp

/-! ### D. The block multipliers and their discrete second differences -/

/-- Scale `h_k = π/2^(k+1)`: on the support of `hat_k`, `n h_k ∈ [π/4, π]`, so `2 cos(n h_k) - 2` stays away from `0`. -/
def hk (k : ℕ) : ℝ := π / 2 ^ (k + 1)

/-- The block multiplier `ν^k_n = n(n-1) r^{n-2} hat_k(n) / (2 cos(n h_k) - 2)`. -/
def nuK (r : ℝ) (k : ℕ) (n : ℤ) : ℝ :=
  ((n : ℝ) * (n - 1) * r ^ (n - 2)) * hatK k n / (2 * Real.cos (n * hk k) - 2)

theorem nb_ell (k : ℕ) :
    (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) ≤ 2 ^ k / 2 ∧ (2 : ℝ) ^ k / 2 < (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) + 1 := by
  have h := Nat.div_add_mod (2 ^ k) 2
  have h2 : (2 ^ k) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h3 : (2 : ℝ) ^ k = 2 * ((2 ^ k / 2 : ℕ) : ℝ) + ((2 ^ k % 2 : ℕ) : ℝ) := by
    exact_mod_cast h.symm
  have h4 : ((2 ^ k % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast h2
  have h5 : (0 : ℝ) ≤ ((2 ^ k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Int.cast_natCast]
  constructor <;> linarith

theorem nb_hat_left (k : ℕ) (m : ℤ) (h1 : (2 : ℝ) ^ k / 2 ≤ m) (h2 : (m : ℝ) ≤ 2 ^ k) :
    hatK k m = ((m : ℝ) - 2 ^ k / 2) / (2 ^ k / 2) := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hA0 : 0 ≤ ((m : ℝ) - 2 ^ k / 2) / (2 ^ k / 2) := div_nonneg (by linarith) (by positivity)
  have hAB : ((m : ℝ) - 2 ^ k / 2) / (2 ^ k / 2) ≤ (2 ^ (k + 1) - (m : ℝ)) / 2 ^ k := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right h2 hN.le]
  unfold hatK
  rw [min_eq_left hAB, max_eq_right hA0]

theorem nb_hat_right (k : ℕ) (m : ℤ) (h1 : (2 : ℝ) ^ k ≤ m) (h2 : (m : ℝ) ≤ 2 ^ (k + 1)) :
    hatK k m = (2 ^ (k + 1) - (m : ℝ)) / 2 ^ k := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hB0 : 0 ≤ (2 ^ (k + 1) - (m : ℝ)) / 2 ^ k := div_nonneg (by linarith) hN.le
  have hBA : (2 ^ (k + 1) - (m : ℝ)) / 2 ^ k ≤ ((m : ℝ) - 2 ^ k / 2) / (2 ^ k / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right h1 hN.le]
  unfold hatK
  rw [min_eq_right hBA, max_eq_right hB0]

theorem nb_hat_lip (k : ℕ) (m : ℤ) : |hatK k (m + 1) - hatK k m| ≤ 2 / 2 ^ k := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  unfold hatK
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by rw [sub_self, abs_zero]; positivity) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · have e : ∀ x : ℝ, (x + 1 - 2 ^ k / 2) / (2 ^ k / 2) - (x - 2 ^ k / 2) / (2 ^ k / 2) = 2 / 2 ^ k := by
      intro x; field_simp; ring
    push_cast
    rw [e, abs_of_pos (by positivity)]
  · have e : ∀ x : ℝ, (2 ^ (k + 1) - (x + 1)) / 2 ^ k - (2 ^ (k + 1) - x) / 2 ^ k = -(1 / 2 ^ k) := by
      intro x; field_simp; ring
    push_cast
    rw [e, abs_neg, abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_right (by norm_num) hN.le

theorem nb_hat_small_left (k : ℕ) (m : ℤ) (h : (m : ℝ) ≤ 2 ^ k / 2 + 3) : hatK k m ≤ 6 / 2 ^ k := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  unfold hatK
  refine max_le (by positivity) (min_le_of_left_le ?_)
  rw [div_le_div_iff₀ (by positivity) hN]
  nlinarith [mul_le_mul_of_nonneg_right (show (m : ℝ) - 2 ^ k / 2 ≤ 3 by linarith) hN.le]

theorem nb_hat_small_right (k : ℕ) (m : ℤ) (h : (2 : ℝ) ^ (k + 1) - 2 ≤ m) : hatK k m ≤ 2 / 2 ^ k := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  unfold hatK
  refine max_le (by positivity) (min_le_of_right_le ?_)
  exact div_le_div_of_nonneg_right (by linarith) hN.le

theorem nb_den_le (k : ℕ) (m : ℤ) (h1 : (2 : ℝ) ^ k / 2 ≤ m) (h2 : (m : ℝ) ≤ 2 ^ (k + 1)) :
    2 * Real.cos (m * hk k) - 2 ≤ -(1 / 2) := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  have hhk : hk k = π / (2 ^ k * 2) := by unfold hk; rw [pow_succ]
  have e1 : π / 4 ≤ (m : ℝ) * hk k := by
    rw [hhk, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]
  have e2 : (m : ℝ) * hk k ≤ π := by
    rw [hhk, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    rw [pow_succ] at h2
    nlinarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := π / 4) (y := (m : ℝ) * hk k)
    (by positivity) e2 e1
  rw [Real.cos_pi_div_four] at hc
  have hs : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  linarith

theorem nb_nu_abs (r : ℝ) (k : ℕ) (m : ℤ) :
    |nuK r k m| ≤ 2 * |(m : ℝ) * (m - 1) * r ^ (m - 2)| * hatK k m := by
  by_cases h0 : hatK k m = 0
  · unfold nuK; rw [h0]; simp
  · obtain ⟨hs1, hs2⟩ := hatK_support h0
    have hd := nb_den_le k m hs1.le hs2.le
    have hH := hatK_nonneg k m
    unfold nuK
    rw [abs_div, abs_mul, abs_of_nonneg hH]
    have hden : 1 / 2 ≤ |2 * Real.cos ((m : ℝ) * hk k) - 2| := by
      rw [abs_of_neg (by linarith)]; linarith
    have hnn : 0 ≤ |(m : ℝ) * (m - 1) * r ^ (m - 2)| * hatK k m := by positivity
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hnn (sub_nonneg.2 hden)]

theorem nb_inv_diff {a b : ℝ} (ha : a ≤ -(1 / 2)) (hb : b ≤ -(1 / 2)) :
    |1 / b - 1 / a| ≤ 4 * |b - a| := by
  have ha' : 1 / 2 ≤ |a| := by rw [abs_of_neg (by linarith)]; linarith
  have hb' : 1 / 2 ≤ |b| := by rw [abs_of_neg (by linarith)]; linarith
  have hane : a ≠ 0 := by intro h; rw [h] at ha; norm_num at ha
  have hbne : b ≠ 0 := by intro h; rw [h] at hb; norm_num at hb
  have e : 1 / b - 1 / a = (a - b) / (a * b) := by
    rw [div_sub_div _ _ hbne hane]; ring
  have h14 : 1 / 4 ≤ |a| * |b| := by
    have := mul_le_mul ha' hb' (by norm_num) (abs_nonneg _)
    linarith
  rw [e, abs_div, abs_mul, div_le_iff₀ (by linarith), abs_sub_comm a b]
  nlinarith [mul_nonneg (abs_nonneg (b - a)) (sub_nonneg.2 h14)]

theorem nb_inv_abs {a : ℝ} (ha : a ≤ -(1 / 2)) : |1 / a| ≤ 2 := by
  have ha' : 1 / 2 ≤ |a| := by rw [abs_of_neg (by linarith)]; linarith
  rw [abs_div, abs_one, div_le_iff₀ (by linarith)]
  linarith

theorem nb_inv_diff2 {a0 ap am E F : ℝ} (h0 : a0 ≤ -(1 / 2)) (hp : ap ≤ -(1 / 2))
    (hm : am ≤ -(1 / 2)) (ha0 : -4 ≤ a0) (hE : |ap + am - 2 * a0| ≤ E) (hFp : |ap - a0| ≤ F)
    (hFm : |am - a0| ≤ F) :
    |1 / ap + 1 / am - 2 / a0| ≤ 8 * (4 * E + 2 * F ^ 2) := by
  have hane : a0 ≠ 0 := by intro h; rw [h] at h0; norm_num at h0
  have hpne : ap ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have hmne : am ≠ 0 := by intro h; rw [h] at hm; norm_num at hm
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hFp
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have e : 1 / ap + 1 / am - 2 / a0 =
      -(a0 * ((ap - a0) + (am - a0)) + 2 * (ap - a0) * (am - a0)) / (a0 * ap * am) := by
    field_simp; ring
  have hs : (ap - a0) + (am - a0) = ap + am - 2 * a0 := by ring
  have h1 : 1 / 2 ≤ |a0| := by rw [abs_of_neg (by linarith)]; linarith
  have h2 : 1 / 2 ≤ |ap| := by rw [abs_of_neg (by linarith)]; linarith
  have h3 : 1 / 2 ≤ |am| := by rw [abs_of_neg (by linarith)]; linarith
  have hden : 1 / 8 ≤ |a0 * ap * am| := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul (mul_le_mul h1 h2 (by norm_num) (abs_nonneg _)) h3 (by norm_num)
      (by positivity)
    linarith
  have hn : |a0 * ((ap - a0) + (am - a0)) + 2 * (ap - a0) * (am - a0)| ≤ 4 * E + 2 * F ^ 2 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, hs]
      have : |a0| ≤ 4 := by rw [abs_of_neg (by linarith)]; linarith
      exact mul_le_mul this hE (abs_nonneg _) (by norm_num)
    · rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul hFp hFm (abs_nonneg _) hF0
      nlinarith
  rw [e, abs_div, abs_neg, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * E + 2 * F ^ 2) (sub_nonneg.2 hden)]

theorem nb_cos_diff (x h : ℝ) (hh : 0 ≤ h) :
    |2 * Real.cos (x + h) - 2 * Real.cos x| ≤ 2 * h ∧
      |2 * Real.cos (x - h) - 2 * Real.cos x| ≤ 2 * h ∧
      |(2 * Real.cos (x + h) - 2) + (2 * Real.cos (x - h) - 2) - 2 * (2 * Real.cos x - 2)| ≤
        2 * h ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have := Real.abs_cos_sub_cos_le (x + h) x
    rw [show x + h - x = h by ring, abs_of_nonneg hh] at this
    rw [show 2 * Real.cos (x + h) - 2 * Real.cos x = 2 * (Real.cos (x + h) - Real.cos x) by ring,
      abs_mul, abs_two]
    linarith
  · have := Real.abs_cos_sub_cos_le (x - h) x
    rw [show x - h - x = -h by ring, abs_neg, abs_of_nonneg hh] at this
    rw [show 2 * Real.cos (x - h) - 2 * Real.cos x = 2 * (Real.cos (x - h) - Real.cos x) by ring,
      abs_mul, abs_two]
    linarith
  · have e : (2 * Real.cos (x + h) - 2) + (2 * Real.cos (x - h) - 2) - 2 * (2 * Real.cos x - 2) =
        -(4 * Real.cos x * (1 - Real.cos h)) := by
      rw [Real.cos_add, Real.cos_sub]; ring
    have hc : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
    have hd0 : 0 ≤ 1 - Real.cos h := by linarith [Real.cos_le_one h]
    have hd : 1 - Real.cos h ≤ h ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hd0, show |(4 : ℝ)| = 4 by norm_num]
    nlinarith [abs_nonneg (Real.cos x), mul_nonneg (abs_nonneg (Real.cos x)) hd0]

theorem nb_prod2 {fp f0 fm gp g0 gm F0 G0 F1 G1 F2 G2 : ℝ} (hf0 : |f0| ≤ F0) (hg0 : |g0| ≤ G0)
    (hf1p : |fp - f0| ≤ F1) (hf1m : |fm - f0| ≤ F1) (hg1p : |gp - g0| ≤ G1)
    (hg1m : |gm - g0| ≤ G1) (hf2 : |fp + fm - 2 * f0| ≤ F2) (hg2 : |gp + gm - 2 * g0| ≤ G2) :
    |fp * gp + fm * gm - 2 * (f0 * g0)| ≤ F2 * G0 + F0 * G2 + 2 * (F1 * G1) := by
  have e : fp * gp + fm * gm - 2 * (f0 * g0) = (fp + fm - 2 * f0) * g0 + f0 * (gp + gm - 2 * g0) +
      (fp - f0) * (gp - g0) + (fm - f0) * (gm - g0) := by ring
  have h1 : |(fp + fm - 2 * f0) * g0| ≤ F2 * G0 := by
    rw [abs_mul]; exact mul_le_mul hf2 hg0 (abs_nonneg _) ((abs_nonneg _).trans hf2)
  have h2 : |f0 * (gp + gm - 2 * g0)| ≤ F0 * G2 := by
    rw [abs_mul]; exact mul_le_mul hf0 hg2 (abs_nonneg _) ((abs_nonneg _).trans hf0)
  have h3 : |(fp - f0) * (gp - g0)| ≤ F1 * G1 := by
    rw [abs_mul]; exact mul_le_mul hf1p hg1p (abs_nonneg _) ((abs_nonneg _).trans hf1p)
  have h4 : |(fm - f0) * (gm - g0)| ≤ F1 * G1 := by
    rw [abs_mul]; exact mul_le_mul hf1m hg1m (abs_nonneg _) ((abs_nonneg _).trans hf1m)
  rw [e, abs_le]
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  have a4 := abs_le.1 h4
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

theorem nb_combine {Pp P0 Pm Hp H0 Hm Qp Q0 Qm q a d e f p δ ε : ℝ} (hH0 : |H0| ≤ 1)
    (hQp : |Qp| ≤ q) (hQ0 : |Q0| ≤ q) (hQm : |Qm| ≤ q)
    (hHp : |Hp - H0| ≤ a) (hHm : |Hm - H0| ≤ a) (hH2 : |Hp + Hm - 2 * H0| ≤ d)
    (hQp1 : |Qp - Q0| ≤ e) (hQm1 : |Qm - Q0| ≤ e) (hQ2 : |Qp + Qm - 2 * Q0| ≤ f)
    (hP0 : |P0| ≤ p) (hPp : |Pp - P0| ≤ δ) (hPm : |Pm - P0| ≤ δ) (hP2 : |Pp + Pm - 2 * P0| ≤ ε) :
    |Pp * (Hp * Qp) + Pm * (Hm * Qm) - 2 * (P0 * (H0 * Q0))| ≤
      ε * q + p * (d * q + 1 * f + 2 * (a * e)) + 2 * (δ * (a * q + e)) := by
  have hq0 : 0 ≤ q := (abs_nonneg _).trans hQ0
  have hW0 : |H0 * Q0| ≤ 1 * q := by
    rw [abs_mul]; exact mul_le_mul hH0 hQ0 (abs_nonneg _) zero_le_one
  have hWp : |Hp * Qp - H0 * Q0| ≤ a * q + e := by
    have : Hp * Qp - H0 * Q0 = (Hp - H0) * Qp + H0 * (Qp - Q0) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul hHp hQp (abs_nonneg _) ((abs_nonneg _).trans hHp)
    · rw [abs_mul]
      calc |H0| * |Qp - Q0| ≤ 1 * e := mul_le_mul hH0 hQp1 (abs_nonneg _) zero_le_one
        _ = e := one_mul e
  have hWm : |Hm * Qm - H0 * Q0| ≤ a * q + e := by
    have : Hm * Qm - H0 * Q0 = (Hm - H0) * Qm + H0 * (Qm - Q0) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul hHm hQm (abs_nonneg _) ((abs_nonneg _).trans hHm)
    · rw [abs_mul]
      calc |H0| * |Qm - Q0| ≤ 1 * e := mul_le_mul hH0 hQm1 (abs_nonneg _) zero_le_one
        _ = e := one_mul e
  have hW2 := nb_prod2 (fp := Hp) (f0 := H0) (fm := Hm) (gp := Qp) (g0 := Q0) (gm := Qm)
    hH0 hQ0 hHp hHm hQp1 hQm1 hH2 hQ2
  have key := nb_prod2 (fp := Pp) (f0 := P0) (fm := Pm) (gp := Hp * Qp) (g0 := H0 * Q0)
    (gm := Hm * Qm) hP0 hW0 hPp hPm hWp hWm hP2 hW2
  linarith

theorem nb_P_step (r : ℝ) (hr : r ≠ 0) (n : ℤ) :
    ((n + 1 : ℤ) : ℝ) * (((n + 1 : ℤ) : ℝ) - 1) * r ^ (n + 1 - 2) -
        (n : ℝ) * ((n : ℝ) - 1) * r ^ (n - 2) =
      (n : ℝ) * r ^ (n - 3) * (r * (2 - ((n : ℝ) + 1) * (1 - r))) := by
  have e1 : r ^ (n + 1 - 2) = r * r * r ^ (n - 3) := by
    rw [show n + 1 - 2 = 2 + (n - 3) by ring, zpow_add₀ hr, zpow_two]
  have e2 : r ^ (n - 2) = r * r ^ (n - 3) := by
    rw [show n - 2 = 1 + (n - 3) by ring, zpow_add₀ hr, zpow_one]
  rw [e1, e2]; push_cast; ring

theorem nb_P_stepm (r : ℝ) (hr : r ≠ 0) (n : ℤ) :
    ((n - 1 : ℤ) : ℝ) * (((n - 1 : ℤ) : ℝ) - 1) * r ^ (n - 1 - 2) -
        (n : ℝ) * ((n : ℝ) - 1) * r ^ (n - 2) =
      ((n : ℝ) - 1) * r ^ (n - 3) * ((n : ℝ) * (1 - r) - 2) := by
  have e1 : r ^ (n - 1 - 2) = r ^ (n - 3) := by rw [show n - 1 - 2 = n - 3 by ring]
  have e2 : r ^ (n - 2) = r * r ^ (n - 3) := by
    rw [show n - 2 = 1 + (n - 3) by ring, zpow_add₀ hr, zpow_one]
  rw [e1, e2]; push_cast; ring

theorem nb_P_step2 (r : ℝ) (hr : r ≠ 0) (n : ℤ) :
    ((n + 1 : ℤ) : ℝ) * (((n + 1 : ℤ) : ℝ) - 1) * r ^ (n + 1 - 2) +
        ((n - 1 : ℤ) : ℝ) * (((n - 1 : ℤ) : ℝ) - 1) * r ^ (n - 1 - 2) -
        2 * ((n : ℝ) * ((n : ℝ) - 1) * r ^ (n - 2)) =
      r ^ (n - 3) * ((n : ℝ) ^ 2 * (1 - r) ^ 2 - (n : ℝ) * (1 - r) * (4 - (1 - r)) + 2) := by
  have e1 : r ^ (n + 1 - 2) = r * r * r ^ (n - 3) := by
    rw [show n + 1 - 2 = 2 + (n - 3) by ring, zpow_add₀ hr, zpow_two]
  have e2 : r ^ (n - 2) = r * r ^ (n - 3) := by
    rw [show n - 2 = 1 + (n - 3) by ring, zpow_add₀ hr, zpow_one]
  have e3 : r ^ (n - 1 - 2) = r ^ (n - 3) := by rw [show n - 1 - 2 = n - 3 by ring]
  rw [e1, e2, e3]; push_cast; ring

theorem nb_den_steps (k : ℕ) (n : ℤ) :
    |(2 * Real.cos (((n + 1 : ℤ) : ℝ) * hk k) - 2) - (2 * Real.cos ((n : ℝ) * hk k) - 2)| ≤ 2 * hk k ∧
    |(2 * Real.cos (((n - 1 : ℤ) : ℝ) * hk k) - 2) - (2 * Real.cos ((n : ℝ) * hk k) - 2)| ≤ 2 * hk k ∧
    |(2 * Real.cos (((n + 1 : ℤ) : ℝ) * hk k) - 2) + (2 * Real.cos (((n - 1 : ℤ) : ℝ) * hk k) - 2) -
        2 * (2 * Real.cos ((n : ℝ) * hk k) - 2)| ≤ 2 * hk k ^ 2 := by
  have hh : 0 ≤ hk k := by unfold hk; positivity
  obtain ⟨c1, c2, c3⟩ := nb_cos_diff ((n : ℝ) * hk k) (hk k) hh
  have ep : ((n + 1 : ℤ) : ℝ) * hk k = (n : ℝ) * hk k + hk k := by push_cast; ring
  have em : ((n - 1 : ℤ) : ℝ) * hk k = (n : ℝ) * hk k - hk k := by push_cast; ring
  rw [ep, em]
  refine ⟨?_, ?_, c3⟩
  · rw [show (2 * Real.cos ((n : ℝ) * hk k + hk k) - 2) - (2 * Real.cos ((n : ℝ) * hk k) - 2) =
      2 * Real.cos ((n : ℝ) * hk k + hk k) - 2 * Real.cos ((n : ℝ) * hk k) by ring]
    exact c1
  · rw [show (2 * Real.cos ((n : ℝ) * hk k - hk k) - 2) - (2 * Real.cos ((n : ℝ) * hk k) - 2) =
      2 * Real.cos ((n : ℝ) * hk k - hk k) - 2 * Real.cos ((n : ℝ) * hk k) by ring]
    exact c2

theorem nb_hk_le (k : ℕ) : 0 ≤ hk k ∧ hk k ≤ 2 / 2 ^ k := by
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨by unfold hk; positivity, ?_⟩
  unfold hk
  rw [pow_succ, div_le_div_iff₀ (by positivity) hN]
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four hN.le]

theorem nb_nu_eq (r : ℝ) (k : ℕ) (m : ℤ) :
    nuK r k m = ((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2)) *
      (hatK k m * (1 / (2 * Real.cos ((m : ℝ) * hk k) - 2))) := by
  unfold nuK; ring

set_option maxHeartbeats 1000000 in
theorem nb_reg_abs {r N s T n d hk Hp H0 Hm Dp D0 Dm Pp P0 Pm : ℝ}
    (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (hs : s = 1 - r) (hN : 1 ≤ N) (hn1 : 1 ≤ n)
    (hn2 : n + 1 ≤ 2 * N) (hT : 0 ≤ T)
    (hPs : Pp - P0 = n * T * (r * (2 - (n + 1) * s))) (hPm : Pm - P0 = (n - 1) * T * (n * s - 2))
    (hP2 : Pp + Pm - 2 * P0 = T * (n ^ 2 * s ^ 2 - n * s * (4 - s) + 2))
    (hP0 : P0 = n * (n - 1) * (r * T))
    (hH0 : 0 ≤ H0) (hH1 : H0 ≤ 1) (hHp : |Hp - H0| ≤ 2 / N) (hHm : |Hm - H0| ≤ 2 / N)
    (hH2 : |Hp + Hm - 2 * H0| ≤ d)
    (hDp : Dp ≤ -(1 / 2)) (hD0 : D0 ≤ -(1 / 2)) (hDm : Dm ≤ -(1 / 2)) (hD0' : -4 ≤ D0)
    (hDp1 : |Dp - D0| ≤ 2 * hk) (hDm1 : |Dm - D0| ≤ 2 * hk)
    (hD2 : |Dp + Dm - 2 * D0| ≤ 2 * hk ^ 2) (hk0 : 0 ≤ hk) (hk1 : hk ≤ 2 / N) :
    |Pp * (Hp * (1 / Dp)) + Pm * (Hm * (1 / Dm)) - 2 * (P0 * (H0 * (1 / D0)))| ≤
      T * (8 * (N * s) ^ 2 + 176 * (N * s) + 2468 + 8 * N ^ 2 * d) := by
  have hN0 : 0 < N := by linarith
  have hr0 : 0 < r := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s ≤ 1 / 2 := by rw [hs]; linarith
  have hnN : n ≤ 2 * N := by linarith
  -- bounds for the reciprocal denominators
  have hQp : |1 / Dp| ≤ 2 := nb_inv_abs hDp
  have hQ0 : |1 / D0| ≤ 2 := nb_inv_abs hD0
  have hQm : |1 / Dm| ≤ 2 := nb_inv_abs hDm
  have e16 : 16 / N = 8 * (2 / N) := by ring
  have hQp1 : |1 / Dp - 1 / D0| ≤ 16 / N := by
    have := nb_inv_diff hD0 hDp
    linarith
  have hQm1 : |1 / Dm - 1 / D0| ≤ 16 / N := by
    have := nb_inv_diff hD0 hDm
    linarith
  have hk2 : hk ^ 2 ≤ (2 / N) ^ 2 := pow_le_pow_left₀ hk0 hk1 2
  have e512 : 512 / N ^ 2 = 128 * (2 / N) ^ 2 := by field_simp; ring
  have hQ2 : |1 / Dp + 1 / Dm - 2 * (1 / D0)| ≤ 512 / N ^ 2 := by
    have := nb_inv_diff2 hD0 hDp hDm hD0' hD2 hDp1 hDm1
    rw [show 2 * (1 / D0) = 2 / D0 by ring, e512]
    linarith
  -- bounds for P
  have hnn : 0 ≤ n := by linarith
  have hNs : 0 ≤ N * s := mul_nonneg hN0.le hs0
  have hu : n * s ≤ 2 * (N * s) := by
    have := mul_le_mul_of_nonneg_right hnN hs0; linarith
  have hus : (n + 1) * s ≤ 2 * (N * s) := by
    have := mul_le_mul_of_nonneg_right hn2 hs0; linarith
  have hu0 : 0 ≤ n * s := mul_nonneg hnn hs0
  have hn1' : 0 ≤ n - 1 := by linarith
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]; exact mul_nonneg (mul_nonneg hnn hn1') (mul_nonneg hr0.le hT)
  have hp : |P0| ≤ 4 * N ^ 2 * T := by
    rw [abs_of_nonneg hP0nn, hP0]
    have h1 : n * (n - 1) ≤ n ^ 2 := by
      have : n ^ 2 - n * (n - 1) = n := by ring
      linarith
    have h2 : r * T ≤ T := mul_le_of_le_one_left hT hr2.le
    have h3 : n * (n - 1) * (r * T) ≤ n ^ 2 * T :=
      mul_le_mul h1 h2 (mul_nonneg hr0.le hT) (sq_nonneg n)
    have h4 : n ^ 2 ≤ 4 * N ^ 2 := by
      have := pow_le_pow_left₀ hnn hnN 2
      calc n ^ 2 ≤ (2 * N) ^ 2 := this
        _ = 4 * N ^ 2 := by ring
    linarith [mul_le_mul_of_nonneg_right h4 hT]
  have hAr : n * r ≤ 2 * N := by
    have := mul_le_mul hnN hr2.le hr0.le (by linarith : (0 : ℝ) ≤ 2 * N)
    linarith
  have hPp : |Pp - P0| ≤ 2 * N * T * (2 + 2 * (N * s)) := by
    rw [hPs]
    have e : n * T * (r * (2 - (n + 1) * s)) = (T * (n * r)) * (2 - (n + 1) * s) := by ring
    rw [e, abs_mul, abs_of_nonneg (mul_nonneg hT (mul_nonneg hnn hr0.le))]
    have h1 : |2 - (n + 1) * s| ≤ 2 + 2 * (N * s) := by
      rw [abs_le]; constructor <;> linarith
    have h2 : T * (n * r) ≤ T * (2 * N) := mul_le_mul_of_nonneg_left hAr hT
    calc _ ≤ T * (2 * N) * (2 + 2 * (N * s)) :=
          mul_le_mul h2 h1 (abs_nonneg _) (mul_nonneg hT (by linarith))
      _ = _ := by ring
  have hPm' : |Pm - P0| ≤ 2 * N * T * (2 + 2 * (N * s)) := by
    rw [hPm]
    have e : (n - 1) * T * (n * s - 2) = (T * (n - 1)) * (n * s - 2) := by ring
    rw [e, abs_mul, abs_of_nonneg (mul_nonneg hT hn1')]
    have h1 : |n * s - 2| ≤ 2 + 2 * (N * s) := by
      rw [abs_le]; constructor <;> linarith
    have h2 : T * (n - 1) ≤ T * (2 * N) := mul_le_mul_of_nonneg_left (by linarith) hT
    calc _ ≤ T * (2 * N) * (2 + 2 * (N * s)) :=
          mul_le_mul h2 h1 (abs_nonneg _) (mul_nonneg hT (by linarith))
      _ = _ := by ring
  have hε : |Pp + Pm - 2 * P0| ≤ T * (4 * (N * s) ^ 2 + 8 * (N * s) + 2) := by
    rw [hP2, abs_mul, abs_of_nonneg hT]
    have h1 : |n ^ 2 * s ^ 2 - n * s * (4 - s) + 2| ≤ 4 * (N * s) ^ 2 + 8 * (N * s) + 2 := by
      have hsq : (n * s) ^ 2 ≤ (2 * (N * s)) ^ 2 := pow_le_pow_left₀ hu0 hu 2
      have hq1 : 0 ≤ n ^ 2 * s ^ 2 := by positivity
      have hq2 : n * s * s ≤ n * s * (1 / 2) := mul_le_mul_of_nonneg_left hs1 hu0
      have hq3 : 0 ≤ n * s * s := mul_nonneg hu0 hs0
      have hq4 : 0 ≤ (N * s) ^ 2 := sq_nonneg _
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul_of_nonneg_left h1 hT
  have hc := nb_combine (Pp := Pp) (P0 := P0) (Pm := Pm) (Hp := Hp) (H0 := H0) (Hm := Hm)
    (Qp := 1 / Dp) (Q0 := 1 / D0) (Qm := 1 / Dm) (q := 2) (a := 2 / N) (d := d)
    (e := 16 / N) (f := 512 / N ^ 2) (p := 4 * N ^ 2 * T) (δ := 2 * N * T * (2 + 2 * (N * s)))
    (ε := T * (4 * (N * s) ^ 2 + 8 * (N * s) + 2))
    (by rw [abs_of_nonneg hH0]; exact hH1) hQp hQ0 hQm hHp hHm hH2 hQp1 hQm1 hQ2 hp hPp hPm' hε
  refine hc.trans (le_of_eq ?_)
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem nb_reg {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (n : ℤ)
    (hn1 : (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) + 3 ≤ n) (hn2 : (n : ℝ) ≤ 2 ^ (k + 1) - 2) {d : ℝ}
    (hd : |hatK k (n + 1) + hatK k (n - 1) - 2 * hatK k n| ≤ d) :
    |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤
      r ^ (n - 3) * (8 * (2 ^ k * (1 - r)) ^ 2 + 176 * (2 ^ k * (1 - r)) + 2468 +
        8 * (2 ^ k) ^ 2 * d) := by
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hr0 : 0 < r := by linarith
  obtain ⟨he1, he2⟩ := nb_ell k
  rw [Int.cast_natCast] at hn1
  have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hn2' : (n : ℝ) + 1 ≤ 2 * 2 ^ k := by rw [hN2] at hn2; linarith
  have hnlo : (2 : ℝ) ^ k / 2 + 2 ≤ n := by
    have : (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) = ((2 ^ k / 2 : ℕ) : ℝ) := Int.cast_natCast _
    linarith
  have hDp := nb_den_le k (n + 1) (by push_cast; linarith) (by push_cast; rw [hN2]; linarith)
  have hD0 := nb_den_le k n (by linarith) (by rw [hN2]; linarith)
  have hDm := nb_den_le k (n - 1) (by push_cast; linarith) (by push_cast; rw [hN2]; linarith)
  have hD0' : -4 ≤ 2 * Real.cos ((n : ℝ) * hk k) - 2 := by
    linarith [Real.neg_one_le_cos ((n : ℝ) * hk k)]
  obtain ⟨s1, s2, s3⟩ := nb_den_steps k n
  obtain ⟨hk0, hk1⟩ := nb_hk_le k
  have hHm : |hatK k (n - 1) - hatK k n| ≤ 2 / 2 ^ k := by
    have := nb_hat_lip k (n - 1)
    rw [sub_add_cancel, abs_sub_comm] at this
    exact this
  have hP0 : (n : ℝ) * ((n : ℝ) - 1) * r ^ (n - 2) = (n : ℝ) * ((n : ℝ) - 1) * (r * r ^ (n - 3)) := by
    rw [show r ^ (n - 2) = r * r ^ (n - 3) by
      rw [show n - 2 = 1 + (n - 3) by ring, zpow_add₀ hr0.ne', zpow_one]]
  have key := nb_reg_abs (r := r) (N := 2 ^ k) (s := 1 - r) (T := r ^ (n - 3)) (n := (n : ℝ))
    (d := d) (hk := hk k) hr1 hr2 rfl hN1 (by linarith) hn2' (zpow_nonneg hr0.le _)
    (nb_P_step r hr0.ne' n) (nb_P_stepm r hr0.ne' n) (nb_P_step2 r hr0.ne' n) hP0
    (hatK_nonneg k n) (hatK_le_one k n) (nb_hat_lip k n) hHm hd hDp hD0 hDm hD0' s1 s2 s3 hk0 hk1
  refine le_trans (le_of_eq ?_) key
  congr 1
  rw [nb_nu_eq r k (n + 1), nb_nu_eq r k n, nb_nu_eq r k (n - 1)]
  ring

theorem nb_nu_zero {r : ℝ} {k : ℕ} {n : ℤ}
    (h : n < ((2 ^ k / 2 : ℕ) : ℤ) ∨ 2 ^ (k + 1) < n) : nuK r k n = 0 := by
  have h0 : hatK k n = 0 := by
    by_contra hne
    obtain ⟨h1, h2⟩ := hatK_support hne
    obtain ⟨he1, he2⟩ := nb_ell k
    rcases h with h | h
    · have : (n : ℝ) < (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h
      linarith
    · have : (2 : ℝ) ^ (k + 1) < n := by exact_mod_cast h
      linarith
  unfold nuK; rw [h0]; simp

theorem nb_nu_edge {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (m : ℤ)
    (hm : (m : ℝ) ≤ 2 ^ (k + 1) + 2) (hH : hatK k m ≤ 6 / 2 ^ k) :
    |nuK r k m| ≤ 768 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) := by
  have hr0 : 0 < r := by linarith
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hN0 : (0 : ℝ) < 2 ^ k := by linarith
  have hrl : 0 ≤ r ^ (2 ^ k / 2 : ℕ) := by positivity
  by_cases hlt : m < ((2 ^ k / 2 : ℕ) : ℤ)
  · rw [nb_nu_zero (Or.inl hlt), abs_zero]; positivity
  · have hlt' : ((2 ^ k / 2 : ℕ) : ℤ) ≤ m := not_lt.1 hlt
    have hm0z : (0 : ℤ) ≤ m := le_trans (Int.natCast_nonneg _) hlt'
    have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast hm0z
    have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    refine (nb_nu_abs r k m).trans ?_
    have hpow : r ^ (m - 2) ≤ 4 * r ^ (2 ^ k / 2 : ℕ) := by
      have h1 : r ^ (m - 2) ≤ r ^ (((2 ^ k / 2 : ℕ) : ℤ) - 2) :=
        zpow_le_zpow_right_of_le_one₀ hr0 hr2.le (by linarith)
      have h2 : r ^ (((2 ^ k / 2 : ℕ) : ℤ) - 2) = r ^ (2 ^ k / 2 : ℕ) / (r * r) := by
        rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_two]
      rw [h2] at h1
      refine h1.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hrl (show (0 : ℝ) ≤ r * r - 1 / 4 by nlinarith)]
    have hmm : |(m : ℝ) * ((m : ℝ) - 1)| ≤ 16 * (2 ^ k) ^ 2 := by
      have hcase : (m : ℝ) = 0 ∨ 1 ≤ (m : ℝ) := by
        rcases eq_or_lt_of_le hm0z with h | h
        · left; rw [← h]; simp
        · right; exact_mod_cast h
      have hm4 : (m : ℝ) ≤ 4 * 2 ^ k := by rw [hN2] at hm; linarith
      rcases hcase with h | h
      · rw [h]; simp
      · rw [abs_of_nonneg (mul_nonneg hm0 (by linarith))]
        nlinarith
    have hPb : |(m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2)| ≤ 64 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ) := by
      rw [abs_mul, abs_of_nonneg (zpow_nonneg hr0.le _)]
      calc |(m : ℝ) * ((m : ℝ) - 1)| * r ^ (m - 2) ≤ 16 * (2 ^ k) ^ 2 * (4 * r ^ (2 ^ k / 2 : ℕ)) :=
            mul_le_mul hmm hpow (zpow_nonneg hr0.le _) (by positivity)
        _ = _ := by ring
    calc 2 * |(m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2)| * hatK k m ≤
          2 * (64 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ)) * (6 / 2 ^ k) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hPb (by norm_num)) hH (hatK_nonneg k m)
            (by positivity)
      _ = _ := by field_simp; ring

theorem nb_pw_left {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (n : ℤ)
    (hn2 : n ≤ ((2 ^ k / 2 : ℕ) : ℤ) + 2) :
    |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤ 3072 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) := by
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  obtain ⟨he1, he2⟩ := nb_ell k
  have hn2' : (n : ℝ) ≤ (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) + 2 := by exact_mod_cast hn2
  have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have key : ∀ m : ℤ, m ≤ n + 1 → (m : ℝ) ≤ 2 ^ k / 2 + 3 →
      |nuK r k m| ≤ 768 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) := by
    intro m hm1 hm2
    refine nb_nu_edge hr1 hr2 k m ?_ (nb_hat_small_left k m hm2)
    have : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm1
    rw [hN2]; linarith
  have h1 := abs_le.1 (key (n + 1) le_rfl (by push_cast; linarith))
  have h0 := abs_le.1 (key n (by omega) (by linarith))
  have hm := abs_le.1 (key (n - 1) (by omega) (by push_cast; linarith))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h0.1, h0.2, hm.1, hm.2]

theorem nb_pw_right {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (n : ℤ)
    (hn1 : (2 : ℤ) ^ (k + 1) - 1 ≤ n) (hn2 : n ≤ (2 : ℤ) ^ (k + 1) + 1) :
    |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤ 3072 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) := by
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hn1' : (2 : ℝ) ^ (k + 1) - 1 ≤ n := by exact_mod_cast hn1
  have hn2' : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) + 1 := by exact_mod_cast hn2
  have key : ∀ m : ℤ, n - 1 ≤ m → m ≤ n + 1 →
      |nuK r k m| ≤ 768 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) := by
    intro m hm1 hm2
    have a1 : (n : ℝ) - 1 ≤ m := by exact_mod_cast hm1
    have a2 : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hm2
    refine nb_nu_edge hr1 hr2 k m (by linarith) ?_
    have := nb_hat_small_right k m (by linarith)
    have h6 : 2 / (2 : ℝ) ^ k ≤ 6 / 2 ^ k :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have h1 := abs_le.1 (key (n + 1) (by omega) le_rfl)
  have h0 := abs_le.1 (key n (by omega) (by omega))
  have hm := abs_le.1 (key (n - 1) (by omega) (by omega))
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h0.1, h0.2, hm.1, hm.2]

theorem nb_pw_mid {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (n : ℤ)
    (hn1 : ((2 ^ k / 2 : ℕ) : ℤ) + 3 ≤ n) (hn2 : n ≤ (2 : ℤ) ^ (k + 1) - 2) {d : ℝ}
    (hd : |hatK k (n + 1) + hatK k (n - 1) - 2 * hatK k n| ≤ d) (hd0 : 0 ≤ d) :
    |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤
      r ^ (2 ^ k / 2 : ℕ) * (8 * (2 ^ k * (1 - r)) ^ 2 + 176 * (2 ^ k * (1 - r)) + 2468 +
        8 * (2 ^ k) ^ 2 * d) := by
  have hr0 : 0 < r := by linarith
  have hn1' : (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) + 3 ≤ n := by exact_mod_cast hn1
  have hn2' : (n : ℝ) ≤ 2 ^ (k + 1) - 2 := by exact_mod_cast hn2
  have h := nb_reg hr1 hr2 k n hn1' hn2' hd
  have hT : r ^ (n - 3) ≤ r ^ (2 ^ k / 2 : ℕ) := by
    have := zpow_le_zpow_right_of_le_one₀ hr0 hr2.le (show (((2 ^ k / 2 : ℕ) : ℤ)) ≤ n - 3 by omega)
    rwa [zpow_natCast] at this
  have hx : 0 ≤ (2 : ℝ) ^ k * (1 - r) := mul_nonneg (by positivity) (by linarith)
  have hbr : 0 ≤ 8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468 +
      8 * ((2 : ℝ) ^ k) ^ 2 * d := by positivity
  exact h.trans (mul_le_mul_of_nonneg_right hT hbr)

theorem nb_pw {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (n : ℤ)
    (hn1 : ((2 ^ k / 2 : ℕ) : ℤ) - 1 ≤ n) (hn2 : n ≤ (2 : ℤ) ^ (k + 1) + 1) :
    |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤
      r ^ (2 ^ k / 2 : ℕ) * (8 * (2 ^ k * (1 - r)) ^ 2 + 176 * (2 ^ k * (1 - r)) + 2468) +
        (if n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) then
          3104 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) else 0) := by
  have hr0 : 0 < r := by linarith
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hrl : 0 ≤ r ^ (2 ^ k / 2 : ℕ) := by positivity
  have hx : 0 ≤ (2 : ℝ) ^ k * (1 - r) := mul_nonneg (by positivity) (by linarith)
  have hP0 : 0 ≤ 8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468 := by
    positivity
  have hA0 : 0 ≤ r ^ (2 ^ k / 2 : ℕ) * (8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 +
      176 * ((2 : ℝ) ^ k * (1 - r)) + 2468) := mul_nonneg hrl hP0
  have hK0 : 0 ≤ 3104 * (2 : ℝ) ^ k * r ^ (2 ^ k / 2 : ℕ) := by positivity
  have hN2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  by_cases hA : n ≤ ((2 ^ k / 2 : ℕ) : ℤ) + 2
  · have hmem : n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) := by
      simp only [Finset.mem_union, Finset.mem_Icc]
      left; left; exact ⟨hn1, hA⟩
    rw [if_pos hmem]
    have := nb_pw_left hr1 hr2 k n hA
    linarith
  · by_cases hB : (2 : ℤ) ^ (k + 1) - 1 ≤ n
    · have hmem : n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) := by
        simp only [Finset.mem_union, Finset.mem_Icc]
        right; exact ⟨hB, hn2⟩
      rw [if_pos hmem]
      have := nb_pw_right hr1 hr2 k n hB hn2
      linarith
    · have hm1 : ((2 ^ k / 2 : ℕ) : ℤ) + 3 ≤ n := by omega
      have hm2 : n ≤ (2 : ℤ) ^ (k + 1) - 2 := by omega
      by_cases hK : n = (2 : ℤ) ^ k
      · have hmem : n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) := by
          simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
          left; right; exact hK
        rw [if_pos hmem]
        have hd : |hatK k (n + 1) + hatK k (n - 1) - 2 * hatK k n| ≤ 4 / 2 ^ k := by
          have a1 := abs_le.1 (nb_hat_lip k n)
          have a2 := abs_le.1 (show |hatK k (n - 1) - hatK k n| ≤ 2 / 2 ^ k by
            have := nb_hat_lip k (n - 1)
            rw [sub_add_cancel, abs_sub_comm] at this
            exact this)
          have e : (4 : ℝ) / 2 ^ k = 2 / 2 ^ k + 2 / 2 ^ k := by ring
          rw [abs_le, e]
          constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
        have h := nb_pw_mid hr1 hr2 k n hm1 hm2 hd (by positivity)
        have e : 8 * ((2 : ℝ) ^ k) ^ 2 * (4 / 2 ^ k) = 32 * 2 ^ k := by field_simp; ring
        rw [e] at h
        nlinarith [h, hA0, hK0, mul_nonneg hrl (by positivity : (0 : ℝ) ≤ 32 * 2 ^ k)]
      · have hite : 0 ≤ (if n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) then
            3104 * (2 : ℝ) ^ k * r ^ (2 ^ k / 2 : ℕ) else 0) := by
          split_ifs
          · exact hK0
          · exact le_rfl
        have hflat : (n : ℝ) + 1 ≤ 2 ^ k ∨ (2 : ℝ) ^ k ≤ (n : ℝ) - 1 := by
          rcases lt_or_gt_of_ne hK with h | h
          · left
            have : n + 1 ≤ (2 : ℤ) ^ k := by omega
            exact_mod_cast this
          · right
            have : (2 : ℤ) ^ k ≤ n - 1 := by omega
            exact_mod_cast this
        obtain ⟨he1, he2⟩ := nb_ell k
        have hn1r : (((2 ^ k / 2 : ℕ) : ℤ) : ℝ) + 3 ≤ n := by exact_mod_cast hm1
        have hn2r : (n : ℝ) ≤ 2 ^ (k + 1) - 2 := by exact_mod_cast hm2
        have hz : hatK k (n + 1) + hatK k (n - 1) - 2 * hatK k n = 0 := by
          rcases hflat with hf | hf
          · rw [nb_hat_left k (n + 1) (by push_cast; linarith) (by push_cast; linarith),
              nb_hat_left k (n - 1) (by push_cast; linarith) (by push_cast; linarith),
              nb_hat_left k n (by linarith) (by linarith)]
            push_cast; ring
          · rw [nb_hat_right k (n + 1) (by push_cast; linarith) (by push_cast; linarith),
              nb_hat_right k (n - 1) (by push_cast; linarith) (by push_cast; linarith),
              nb_hat_right k n (by linarith) (by linarith)]
            push_cast; ring
        have h := nb_pw_mid hr1 hr2 k n hm1 hm2 (d := 0) (by rw [hz]; simp) le_rfl
        have h' : |nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1)| ≤
            r ^ (2 ^ k / 2 : ℕ) * (8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468) := by
          simpa using h
        linarith

theorem nb_nat_div (a : ℕ) :
    a / 2 = a / 4 + (a / 2 - a / 4) ∧ a / 4 ≤ a / 2 - a / 4 ∧ a ≤ 4 * (a / 4 + 1) := by
  omega

theorem nb_div_mono (a : ℕ) : a / 4 ≤ a / 2 := by omega

theorem nb_ell_le (k : ℕ) : ((2 ^ k / 2 : ℕ) : ℤ) ≤ (2 : ℤ) ^ (k + 1) := by
  have h1 : 2 ^ k / 2 ≤ 2 ^ k := Nat.div_le_self _ _
  have h2 : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h1.trans h2

theorem nb_absorb {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) :
    (8 * (2 ^ k * (1 - r)) ^ 2 + 176 * (2 ^ k * (1 - r)) + 2468) * r ^ (2 ^ k / 2 : ℕ) ≤
      4356 * r ^ (2 ^ k / 4 : ℕ) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hj, hMj, hNb⟩ := nb_nat_div (2 ^ k)
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = 2 ^ k / 2 - 2 ^ k / 4 := ⟨_, rfl⟩
  rw [← hjdef] at hj hMj
  have hNr : (2 : ℝ) ^ k ≤ 4 * (((2 ^ k / 4 : ℕ) : ℝ) + 1) := by exact_mod_cast hNb
  have hMjr : ((2 ^ k / 4 : ℕ) : ℝ) ≤ j := by exact_mod_cast hMj
  have hs0 : 0 ≤ 1 - r := by linarith
  have hs1 : 1 - r ≤ 1 / 2 := by linarith
  set y : ℝ := (j : ℝ) * (1 - r) with hy
  have hy0 : 0 ≤ y := mul_nonneg (Nat.cast_nonneg _) hs0
  have hx0 : 0 ≤ (2 : ℝ) ^ k * (1 - r) := mul_nonneg (by positivity) hs0
  have hx : (2 : ℝ) ^ k * (1 - r) ≤ 4 * y + 2 := by
    have h1 := mul_le_mul_of_nonneg_right hNr hs0
    have h2 := mul_le_mul_of_nonneg_right hMjr hs0
    nlinarith
  have hrpow : r ^ (2 ^ k / 2 : ℕ) = r ^ (2 ^ k / 4 : ℕ) * r ^ j := by rw [hj, pow_add]
  have hrj : r ^ j ≤ Real.exp (-y) := by
    have h1 : r ≤ Real.exp (-(1 - r)) := by
      have := Real.one_sub_le_exp_neg (1 - r); linarith
    have h2 := pow_le_pow_left₀ hr0.le h1 j
    rw [← Real.exp_nat_mul] at h2
    have e : (j : ℝ) * -(1 - r) = -y := by rw [hy]; ring
    rwa [e] at h2
  have hy2 : y ^ 2 ≤ 2 * Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy0 2
    norm_num [Nat.factorial] at this
    linarith
  have e1 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hyexp : y ^ 2 * Real.exp (-y) ≤ 2 := by
    have := mul_le_mul_of_nonneg_right hy2 (Real.exp_pos (-y)).le
    nlinarith [e1]
  have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hepos : 0 < Real.exp (-y) := Real.exp_pos _
  have hpoly : 8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468 ≤
      544 * y ^ 2 + 3268 := by
    have hsq : ((2 : ℝ) ^ k * (1 - r)) ^ 2 ≤ (4 * y + 2) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    nlinarith [sq_nonneg (y - 1)]
  have hP0 : 0 ≤ 8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468 := by
    positivity
  have hmain : (8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468) * r ^ j ≤
      4356 := by
    calc _ ≤ (544 * y ^ 2 + 3268) * Real.exp (-y) :=
          mul_le_mul hpoly hrj (by positivity) (by positivity)
      _ = 544 * (y ^ 2 * Real.exp (-y)) + 3268 * Real.exp (-y) := by ring
      _ ≤ 4356 := by nlinarith
  rw [hrpow]
  have hrM : 0 ≤ r ^ (2 ^ k / 4 : ℕ) := by positivity
  calc _ = r ^ (2 ^ k / 4 : ℕ) *
        ((8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468) * r ^ j) := by ring
    _ ≤ r ^ (2 ^ k / 4 : ℕ) * 4356 := mul_le_mul_of_nonneg_left hmain hrM
    _ = _ := by ring

theorem nb_card_eq (a b : ℤ) (h : a ≤ b + 1) : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
  have := Int.card_Icc_of_le a b h
  have h2 : (((Finset.Icc a b).card : ℤ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by rw [this]
  push_cast at h2
  exact h2

theorem nb_P_abs {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (m : ℤ)
    (hlt : ((2 ^ k / 2 : ℕ) : ℤ) ≤ m) (hm : (m : ℝ) ≤ 2 ^ (k + 1) + 2) :
    |(m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2)| ≤ 64 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ) := by
  have hr0 : 0 < r := by linarith
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hrl : 0 ≤ r ^ (2 ^ k / 2 : ℕ) := by positivity
  have hm0z : (0 : ℤ) ≤ m := le_trans (Int.natCast_nonneg _) hlt
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast hm0z
  have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hpow : r ^ (m - 2) ≤ 4 * r ^ (2 ^ k / 2 : ℕ) := by
    have h1 : r ^ (m - 2) ≤ r ^ (((2 ^ k / 2 : ℕ) : ℤ) - 2) :=
      zpow_le_zpow_right_of_le_one₀ hr0 hr2.le (by linarith)
    have h2 : r ^ (((2 ^ k / 2 : ℕ) : ℤ) - 2) = r ^ (2 ^ k / 2 : ℕ) / (r * r) := by
      rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_two]
    rw [h2] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hrl (show (0 : ℝ) ≤ r * r - 1 / 4 by nlinarith)]
  have hmm : |(m : ℝ) * ((m : ℝ) - 1)| ≤ 16 * (2 ^ k) ^ 2 := by
    have hcase : (m : ℝ) = 0 ∨ 1 ≤ (m : ℝ) := by
      rcases eq_or_lt_of_le hm0z with h | h
      · left; rw [← h]; simp
      · right; exact_mod_cast h
    have hm4 : (m : ℝ) ≤ 4 * 2 ^ k := by rw [hN2] at hm; linarith
    rcases hcase with h | h
    · rw [h]; simp
    · rw [abs_of_nonneg (mul_nonneg hm0 (by linarith))]
      nlinarith
  rw [abs_mul, abs_of_nonneg (zpow_nonneg hr0.le _)]
  calc |(m : ℝ) * ((m : ℝ) - 1)| * r ^ (m - 2) ≤ 16 * (2 ^ k) ^ 2 * (4 * r ^ (2 ^ k / 2 : ℕ)) :=
        mul_le_mul hmm hpow (zpow_nonneg hr0.le _) (by positivity)
    _ = _ := by ring

theorem nb_nu_all {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) (m : ℤ)
    (hm : (m : ℝ) ≤ 2 ^ (k + 1) + 2) : |nuK r k m| ≤ 128 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ) := by
  have hr0 : 0 < r := by linarith
  have hrl : 0 ≤ r ^ (2 ^ k / 2 : ℕ) := by positivity
  by_cases hlt : m < ((2 ^ k / 2 : ℕ) : ℤ)
  · rw [nb_nu_zero (Or.inl hlt), abs_zero]; positivity
  · have hlt' : ((2 ^ k / 2 : ℕ) : ℤ) ≤ m := not_lt.1 hlt
    refine (nb_nu_abs r k m).trans ?_
    have hP := nb_P_abs hr1 hr2 k m hlt' hm
    have hH := hatK_le_one k m
    have hH0 := hatK_nonneg k m
    calc 2 * |(m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2)| * hatK k m ≤
          2 * (64 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num)) hH hH0 (by positivity)
      _ = _ := by ring

theorem nb_sum1 {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) :
    ∑ n ∈ Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)), ‖(nuK r k n : ℂ)‖ ≤
      384 * 8 ^ k * r ^ (2 ^ k / 4 : ℕ) := by
  have hr0 : 0 < r := by linarith
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have h8 : (8 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 3 := by
    rw [← pow_mul, show k * 3 = 3 * k by ring, pow_mul]; norm_num
  have hrM : r ^ (2 ^ k / 2 : ℕ) ≤ r ^ (2 ^ k / 4 : ℕ) :=
    pow_le_pow_of_le_one hr0.le hr2.le (nb_div_mono (2 ^ k))
  have hterm : ∀ n ∈ Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)),
      ‖(nuK r k n : ℂ)‖ ≤ 128 * (2 ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine nb_nu_all hr1 hr2 k n ?_
    have : (n : ℝ) ≤ ((2 : ℤ) ^ (k + 1) : ℤ) := by exact_mod_cast hn.2
    push_cast at this
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := nb_card_eq ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)) (by linarith [nb_ell_le k])
  simp only [Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at hcard
  have hl0 : (0 : ℝ) ≤ ((2 ^ k / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc3 : ((Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1))).card : ℝ) ≤ 3 * 2 ^ k := by
    rw [hcard, hN2]; linarith
  have hpos : 0 ≤ 128 * ((2 : ℝ) ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ) := by positivity
  calc _ ≤ 3 * 2 ^ k * (128 * ((2 : ℝ) ^ k) ^ 2 * r ^ (2 ^ k / 2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hc3 hpos
    _ ≤ 3 * 2 ^ k * (128 * ((2 : ℝ) ^ k) ^ 2 * r ^ (2 ^ k / 4 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hrM (by positivity)
    _ = 384 * 8 ^ k * r ^ (2 ^ k / 4 : ℕ) := by rw [h8]; ring

theorem nb_sum2 {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r < 1) (k : ℕ) :
    ∑ n ∈ Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1),
      ‖(nuK r k (n + 1) : ℂ) - 2 * (nuK r k n : ℂ) + (nuK r k (n - 1) : ℂ)‖ ≤
      50000 * 2 ^ k * r ^ (2 ^ k / 4 : ℕ) := by
  have hr0 : 0 < r := by linarith
  have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hN2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hrM : r ^ (2 ^ k / 2 : ℕ) ≤ r ^ (2 ^ k / 4 : ℕ) :=
    pow_le_pow_of_le_one hr0.le hr2.le (nb_div_mono (2 ^ k))
  have hterm : ∀ n ∈ Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1),
      ‖(nuK r k (n + 1) : ℂ) - 2 * (nuK r k n : ℂ) + (nuK r k (n - 1) : ℂ)‖ ≤
        r ^ (2 ^ k / 2 : ℕ) * (8 * (2 ^ k * (1 - r)) ^ 2 + 176 * (2 ^ k * (1 - r)) + 2468) +
          (if n ∈ (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)) then
          3104 * 2 ^ k * r ^ (2 ^ k / 2 : ℕ) else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have e : (nuK r k (n + 1) : ℂ) - 2 * (nuK r k n : ℂ) + (nuK r k (n - 1) : ℂ) =
        ((nuK r k (n + 1) - 2 * nuK r k n + nuK r k (n - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact nb_pw hr1 hr2 k n hn.1 hn.2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem, Finset.sum_const,
    nsmul_eq_mul]
  have hcard := nb_card_eq (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1)
    (by linarith [nb_ell_le k, (2 : ℤ) ^ (k + 1)])
  simp only [Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, Int.cast_add, Int.cast_sub,
    Int.cast_one] at hcard
  have hl0 : (0 : ℝ) ≤ ((2 ^ k / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc : ((Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1)).card : ℝ) ≤ 5 * 2 ^ k := by
    rw [hcard, hN2]; linarith
  have hE : ((Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1) ∩
      (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1))).card : ℝ) ≤ 8 := by
    have c1 : ∀ c : ℤ, (Finset.Icc (c - 1) (c + 2)).card = 4 := fun c => by
      rw [Int.card_Icc]; omega
    have c3 : ∀ c : ℤ, (Finset.Icc (c - 1) (c + 1)).card = 3 := fun c => by
      rw [Int.card_Icc]; omega
    have h1 := Finset.card_union_le (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2))
      {(2 : ℤ) ^ k}
    have h2 := Finset.card_union_le (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
      {(2 : ℤ) ^ k}) (Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1))
    have h3 := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1))
      (s₂ := Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1)))
    rw [c1, Finset.card_singleton] at h1
    rw [c3] at h2
    have : (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1) ∩
      (Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (((2 ^ k / 2 : ℕ) : ℤ) + 2) ∪
            {(2 : ℤ) ^ k} ∪ Finset.Icc ((2 : ℤ) ^ (k + 1) - 1) ((2 : ℤ) ^ (k + 1) + 1))).card ≤ 8 := by
      omega
    exact_mod_cast this
  have hab := nb_absorb hr1 hr2 k
  have hP0 : 0 ≤ 8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468 := by
    have : 0 ≤ (2 : ℝ) ^ k * (1 - r) := mul_nonneg (by positivity) (by linarith)
    positivity
  have hrl : 0 ≤ r ^ (2 ^ k / 2 : ℕ) := by positivity
  have hA : 0 ≤ r ^ (2 ^ k / 2 : ℕ) *
      (8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468) := mul_nonneg hrl hP0
  have hK : 0 ≤ 3104 * (2 : ℝ) ^ k * r ^ (2 ^ k / 2 : ℕ) := by positivity
  calc _ ≤ 5 * 2 ^ k * (r ^ (2 ^ k / 2 : ℕ) *
        (8 * ((2 : ℝ) ^ k * (1 - r)) ^ 2 + 176 * ((2 : ℝ) ^ k * (1 - r)) + 2468)) +
        8 * (3104 * (2 : ℝ) ^ k * r ^ (2 ^ k / 2 : ℕ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hc hA) (mul_le_mul_of_nonneg_right hE hK)
    _ ≤ 5 * 2 ^ k * (4356 * r ^ (2 ^ k / 4 : ℕ)) + 8 * (3104 * (2 : ℝ) ^ k * r ^ (2 ^ k / 4 : ℕ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) ?_
        · rw [mul_comm]; exact hab
        · apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hrM (by positivity)
    _ ≤ 50000 * 2 ^ k * r ^ (2 ^ k / 4 : ℕ) := by
        have : 0 ≤ (2 : ℝ) ^ k * r ^ (2 ^ k / 4 : ℕ) := by positivity
        nlinarith

theorem ds_tele (h : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), h m =
      ∑ m ∈ Finset.Ico 1 (2 ^ J), h m := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_consecutive _ Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))]

theorem ds_term {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    (2 : ℝ) ^ (j + 1) * r ^ (2 ^ (j + 1)) ≤ 2 * ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), r ^ m := by
  have hle : ∀ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), r ^ (2 ^ (j + 1)) ≤ r ^ m := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact pow_le_pow_of_le_one hr0 hr1.le hm.2.le
  have := Finset.card_nsmul_le_sum _ _ _ hle
  rw [Nat.card_Ico, nsmul_eq_mul] at this
  have hc : ((2 ^ (j + 1) - 2 ^ j : ℕ) : ℝ) = 2 ^ j := by
    have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [h2, show 2 * 2 ^ j - 2 ^ j = 2 ^ j by omega]
    push_cast; ring
  rw [hc] at this
  calc (2 : ℝ) ^ (j + 1) * r ^ (2 ^ (j + 1)) = 2 * (2 ^ j * r ^ (2 ^ (j + 1))) := by ring
    _ ≤ _ := by linarith

theorem ds_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.Ico 1 M, r ^ m ≤ 1 / (1 - r) := by
  have := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (Finset.Ico 1 M) (fun i _ => pow_nonneg hr0 i)
  rw [tsum_geometric_of_lt_one hr0 hr1] at this
  rwa [← one_div] at this

theorem ds_partial {F : ℕ → ℝ} {r : ℝ} (hF : ∀ k, F k = (2 : ℝ) ^ k * r ^ (2 ^ k / 4))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) : ∑ k ∈ Finset.range K, F k ≤ 15 / (1 - r) := by
  have hs : 0 < 1 - r := by linarith
  have hFnn : ∀ k, 0 ≤ F k := fun k => by rw [hF]; positivity
  have h2 : ∀ j, F (j + 2) = 4 * ((2 : ℝ) ^ j * r ^ (2 ^ j)) := by
    intro j
    rw [hF]
    have : 2 ^ (j + 2) / 4 = 2 ^ j := by
      have : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [this]; ring
  have h0 : F 0 = 1 := by rw [hF]; simp
  have h1 : F 1 = 2 := by rw [hF]; norm_num
  have hmono : ∑ k ∈ Finset.range K, F k ≤ ∑ k ∈ Finset.range (K + 2), F k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => hFnn i)
  have hsplit : ∑ k ∈ Finset.range (K + 2), F k =
      3 + 4 * ∑ j ∈ Finset.range K, (2 : ℝ) ^ j * r ^ (2 ^ j) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', h0, zero_add, h1,
      Finset.mul_sum]
    have : ∑ i ∈ Finset.range K, F (i + 1 + 1) =
        ∑ i ∈ Finset.range K, 4 * ((2 : ℝ) ^ i * r ^ (2 ^ i)) :=
      Finset.sum_congr rfl (fun i _ => h2 i)
    rw [this]; ring
  set g : ℕ → ℝ := fun j => (2 : ℝ) ^ j * r ^ (2 ^ j) with hg
  have hgnn : ∀ j, 0 ≤ g j := fun j => by simp only [hg]; positivity
  have hg0 : g 0 ≤ 1 := by
    simp only [hg]; simp; exact hr1.le
  have hS1 : ∑ j ∈ Finset.range K, g j ≤ ∑ j ∈ Finset.range (K + 1), g j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => hgnn i)
  rw [Finset.sum_range_succ'] at hS1
  have hS2 : ∑ j ∈ Finset.range K, g (j + 1) ≤ 2 * (1 / (1 - r)) := by
    calc ∑ j ∈ Finset.range K, g (j + 1) ≤
          ∑ j ∈ Finset.range K, 2 * ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), r ^ m :=
          Finset.sum_le_sum (fun j _ => ds_term hr0 hr1 j)
      _ = 2 * ∑ m ∈ Finset.Ico 1 (2 ^ K), r ^ m := by
          rw [← Finset.mul_sum, ds_tele (fun m => r ^ m) K]
      _ ≤ 2 * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (ds_geom hr0 hr1 _) (by norm_num)
  have hinv : 1 ≤ 1 / (1 - r) := by rw [le_div_iff₀ hs]; linarith
  have e15 : 15 / (1 - r) = 15 * (1 / (1 - r)) := by ring
  rw [e15]
  have := hsplit
  linarith

/-- Size and total second variation of `ν^k`, for `1/2 ≤ r < 1`:
`Σ|ν^k| ≲ 8^k r^{2^k/4}`, `Σ|Δ²ν^k| ≲ 2^k r^{2^k/4}` (the exponent loses a factor 2 to absorb `(1-r)²N²`). -/
theorem nuK_bounds : ∃ A : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ k : ℕ,
    (∑ n ∈ Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)), ‖(nuK r k n : ℂ)‖ ≤ A * 8 ^ k * r ^ (2 ^ k / 4)) ∧
      (∑ n ∈ Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1),
        ‖(nuK r k (n + 1) : ℂ) - 2 * (nuK r k n : ℂ) + (nuK r k (n - 1) : ℂ)‖ ≤ A * 2 ^ k * r ^ (2 ^ k / 4)) := by
  refine ⟨60000, fun r hr1 hr2 k => ⟨?_, ?_⟩⟩
  · refine (nb_sum1 hr1 hr2 k).trans ?_
    have : 0 ≤ (8 : ℝ) ^ k * r ^ (2 ^ k / 4) := by
      have : 0 < r := by linarith
      positivity
    nlinarith
  · refine (nb_sum2 hr1 hr2 k).trans ?_
    have : 0 ≤ (2 : ℝ) ^ k * r ^ (2 ^ k / 4) := by
      have : 0 < r := by linarith
      positivity
    nlinarith

theorem nuK_zero {r : ℝ} {k : ℕ} {n : ℤ} (h : n < ((2 ^ k / 2 : ℕ) : ℤ) ∨ 2 ^ (k + 1) < n) : nuK r k n = 0 := by
  exact nb_nu_zero h

/-- `Σ_k 2^k r^{2^k/4} ≤ A/(1-r)`. -/
theorem dyadic_sum : ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r → r < 1 →
    Summable (fun k : ℕ => (2 : ℝ) ^ k * r ^ (2 ^ k / 4)) ∧ ∑' k : ℕ, (2 : ℝ) ^ k * r ^ (2 ^ k / 4) ≤ A / (1 - r) := by
  refine ⟨15, fun r hr0 hr1 => ?_⟩
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) ^ k * r ^ (2 ^ k / 4) := fun k => by positivity
  have hp : ∀ K : ℕ, ∑ k ∈ Finset.range K, (2 : ℝ) ^ k * r ^ (2 ^ k / 4) ≤ 15 / (1 - r) :=
    fun K => ds_partial (F := fun k : ℕ => (2 : ℝ) ^ k * r ^ (2 ^ k / 4)) (fun k => rfl) hr0 hr1 K
  exact ⟨summable_of_sum_range_le hnn hp, Real.tsum_le_of_sum_range_le hnn hp⟩

/-! ### E. Bloch-type bound for `g'' = Σ_{n ≥ 2} n(n-1) c_n z^{n-2}` -/

theorem zb_blockeq (u : ℝ → ℝ) (r : ℝ) (k : ℕ) (φ : ℝ) (m : ℤ) :
    (hatK k m : ℂ) * (if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) * cf u m *
        exp ((m : ℂ) * (φ : ℂ) * I) else 0) =
      (nuK r k m : ℂ) * (cf u m * (2 * Real.cos (m * hk k) - 2)) * exp ((m : ℂ) * (φ : ℂ) * I) := by
  by_cases hH : hatK k m = 0
  · have hν : nuK r k m = 0 := by unfold nuK; rw [hH]; simp
    rw [hν, hH]; simp
  · obtain ⟨hs1, hs2⟩ := hatK_support hH
    have hN1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hd := nb_den_le k m hs1.le hs2.le
    have hden : (2 * Real.cos ((m : ℝ) * hk k) - 2) ≠ 0 := (by linarith : 2 * Real.cos ((m : ℝ) * hk k) - 2 < 0).ne
    have hm0 : (0 : ℝ) < m := by linarith
    have hm1 : 1 ≤ m := by
      have : (0 : ℤ) < m := by exact_mod_cast hm0
      omega
    by_cases h2 : 2 ≤ m
    · rw [if_pos h2]
      have key : nuK r k m * (2 * Real.cos ((m : ℝ) * hk k) - 2) =
          (m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) * hatK k m := by
        unfold nuK; exact div_mul_cancel₀ _ hden
      have key' := congrArg (fun x : ℝ => (x : ℂ)) key
      push_cast at key' ⊢
      linear_combination (cf u m * exp ((m : ℂ) * (φ : ℂ) * I)) * key'.symm
    · have hm : m = 1 := by omega
      have hν : nuK r k m = 0 := by unfold nuK; rw [hm]; simp
      rw [if_neg h2, hν]; simp

theorem zb_block {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ φ : ℝ, ∀ k : ℕ,
      ‖∑' m : ℤ, (hatK k m : ℂ) * (if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) *
          cf u m * exp ((m : ℂ) * (φ : ℂ) * I) else 0)‖ ≤ K₀ * 2 ^ k * r ^ (2 ^ k / 4) := by
  obtain ⟨hc, hp, C, hC⟩ := hu.1
  obtain ⟨A, hA⟩ := nuK_bounds
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0 1)
  refine ⟨C * π * |A| / 2, by positivity, fun r hr1 hr2 φ k => ?_⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨hS, hB⟩ := hA r hr1 hr2 k
  have hR : 0 ≤ r ^ (2 ^ k / 4) := by positivity
  have hS' : ∑ n ∈ Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)), ‖(nuK r k n : ℂ)‖ ≤
      |A| * 8 ^ k * r ^ (2 ^ k / 4) :=
    hS.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) hR)
  have hB' : ∑ n ∈ Finset.Icc (((2 ^ k / 2 : ℕ) : ℤ) - 1) (2 ^ (k + 1) + 1),
      ‖(nuK r k (n + 1) : ℂ) - 2 * (nuK r k n : ℂ) + (nuK r k (n - 1) : ℂ)‖ ≤
      |A| * 2 ^ k * r ^ (2 ^ k / 4) :=
    hB.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) hR)
  have hmb := mult_bound (ν := fun n => (nuK r k n : ℂ)) hc hp hC
    (fun n hn => by show (nuK r k n : ℂ) = 0; rw [nuK_zero hn]; simp) hS' hB' (hk k) φ
  have e : ∑' m : ℤ, (hatK k m : ℂ) * (if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) *
          cf u m * exp ((m : ℂ) * (φ : ℂ) * I) else 0) =
      ∑ n ∈ Finset.Icc ((2 ^ k / 2 : ℕ) : ℤ) (2 ^ (k + 1)),
        (nuK r k n : ℂ) * (cf u n * (2 * Real.cos (n * hk k) - 2)) * exp ((n : ℂ) * (φ : ℂ) * I) := by
    rw [tsum_congr (fun m => zb_blockeq u r k φ m)]
    refine tsum_eq_sum (fun m hm => ?_)
    have : m < ((2 ^ k / 2 : ℕ) : ℤ) ∨ (2 : ℤ) ^ (k + 1) < m := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm; exact hm
    rw [nuK_zero this]; simp
  rw [e]
  refine hmb.trans ?_
  have hh0 : 0 ≤ hk k := by unfold hk; positivity
  rw [abs_of_nonneg hh0]
  have h8 : (8 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 3 := by
    rw [← pow_mul, show k * 3 = 3 * k by ring, pow_mul]; norm_num
  have hSB : |A| * 8 ^ k * r ^ (2 ^ k / 4) * (|A| * 2 ^ k * r ^ (2 ^ k / 4)) =
      (|A| * ((2 : ℝ) ^ k) ^ 2 * r ^ (2 ^ k / 4)) ^ 2 := by rw [h8]; ring
  rw [hSB, Real.sqrt_sq (by positivity)]
  have hN : (0 : ℝ) < 2 ^ k := by positivity
  unfold hk
  rw [pow_succ]
  apply le_of_eq
  field_simp

theorem zb_Ubound {u : ℝ → ℝ} (hu : u ∈ tangentQS) : ∃ U : ℝ, 0 ≤ U ∧ ∀ m : ℤ, ‖cf u m‖ ≤ U := by
  have hs : Summable fun n : ℤ => ‖cf u n‖ := tangentQS_fourier_summable hu
  exact ⟨∑' n : ℤ, ‖cf u n‖, tsum_nonneg (fun _ => norm_nonneg _),
    fun m => hs.le_tsum m (fun j _ => norm_nonneg _)⟩

theorem zb_polygeom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) * ((n : ℝ) + 1) * r ^ n) := by
  have h : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 h
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 h
  have h0 := summable_geometric_of_lt_one hr0 hr1
  have := (h2.add (h1.mul_left 3)).add (h0.mul_left 2)
  refine this.congr (fun n => ?_)
  ring

theorem zb_P_nat (r : ℝ) (n : ℕ) :
    (((n : ℤ) + 2 : ℤ) : ℝ) * ((((n : ℤ) + 2 : ℤ) : ℝ) - 1) * r ^ ((n : ℤ) + 2 - 2) =
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * r ^ n := by
  rw [show (n : ℤ) + 2 - 2 = (n : ℤ) by ring, zpow_natCast]
  push_cast; ring

theorem zb_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {U : ℝ} {c : ℤ → ℂ} (hU : ∀ m, ‖c m‖ ≤ U)
    (φ : ℝ) (f : ℤ → ℂ)
    (hf : ∀ m, f m = if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) * c m *
        exp ((m : ℂ) * (φ : ℂ) * I) else 0) :
    Summable fun m => ‖f m‖ := by
  have hnat : ∀ n : ℕ, ‖f ((n : ℤ) + 2)‖ = ((n : ℝ) + 2) * ((n : ℝ) + 1) * r ^ n * ‖c ((n : ℤ) + 2)‖ := by
    intro n
    rw [hf, if_pos (by omega), norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ((((n : ℤ) + 2 : ℤ) : ℂ)) = (((n : ℤ) + 2 : ℤ) : ℂ) from rfl, kl_norm_exp, mul_one,
      zb_P_nat, abs_of_nonneg (by positivity)]
  have hbd : Summable fun n : ℕ => ‖f ((n : ℤ) + 2)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((zb_polygeom hr0 hr1).mul_left U)
    rw [hnat]
    have := hU ((n : ℤ) + 2)
    have h0 : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * r ^ n := by positivity
    nlinarith
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) + 2 := fun a b h => by simpa using h
  refine (Function.Injective.summable_iff hinj (fun x hx => ?_)).1 hbd
  have : x < 2 := by
    by_contra h
    exact hx ⟨(x - 2).toNat, by simp only []; omega⟩
  rw [hf, if_neg (by omega), norm_zero]

theorem zb_swap {f : ℤ → ℂ} (hf0 : ∀ m, m < 2 → f m = 0) (hsum : Summable fun m => ‖f m‖) :
    ∑' m : ℤ, f m = ∑' k : ℕ, ∑' m : ℤ, (hatK k m : ℂ) * f m := by
  have hm : ∀ m : ℤ, HasSum (fun k : ℕ => (hatK k m : ℂ) * f m) (f m) := by
    intro m
    by_cases h1 : 1 ≤ m
    · have := (Complex.hasSum_ofReal.2 (hatK_partition h1)).mul_right (f m)
      simpa using this
    · have : f m = 0 := hf0 m (by omega)
      rw [this]
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have hnorm : ∀ m : ℤ, HasSum (fun k : ℕ => ‖(hatK k m : ℂ) * f m‖) ‖f m‖ := by
    intro m
    by_cases h1 : 1 ≤ m
    · have := (hatK_partition h1).mul_right ‖f m‖
      rw [one_mul] at this
      have e : (fun k : ℕ => ‖(hatK k m : ℂ) * f m‖) = fun k : ℕ => hatK k m * ‖f m‖ := by
        funext k
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hatK_nonneg k m)]
      rw [e]; exact this
    · have : f m = 0 := hf0 m (by omega)
      rw [this]
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have hg : Summable (fun p : ℤ × ℕ => ‖(hatK p.2 p.1 : ℂ) * f p.1‖) := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun m => (hnorm m).summable, ?_⟩
    exact (summable_congr fun m => (hnorm m).tsum_eq).2 hsum
  have hF : Summable (Function.uncurry fun (m : ℤ) (k : ℕ) => (hatK k m : ℂ) * f m) :=
    Summable.of_norm hg
  calc ∑' m, f m = ∑' m : ℤ, ∑' k : ℕ, (hatK k m : ℂ) * f m := tsum_congr (fun m => (hm m).tsum_eq.symm)
    _ = ∑' k : ℕ, ∑' m : ℤ, (hatK k m : ℂ) * f m := (Summable.tsum_comm hF).symm

theorem zb_total {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    ∃ K₁ : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ φ : ℝ, ∀ f : ℤ → ℂ,
      (∀ m, f m = if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) * cf u m *
        exp ((m : ℂ) * (φ : ℂ) * I) else 0) → ‖∑' m, f m‖ ≤ K₁ / (1 - r) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := zb_block hu
  obtain ⟨A, hA⟩ := dyadic_sum
  obtain ⟨U, hU0, hU⟩ := zb_Ubound hu
  refine ⟨K₀ * A, fun r hr1 hr2 φ f hf => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have hf0 : ∀ m, m < 2 → f m = 0 := fun m hm => by rw [hf, if_neg (by omega)]
  have hsum := zb_summable hr0 hr2 hU φ f hf
  rw [zb_swap hf0 hsum]
  obtain ⟨hAs, hAle⟩ := hA r hr0 hr2
  have hb : ∀ k : ℕ, ‖∑' m : ℤ, (hatK k m : ℂ) * f m‖ ≤ K₀ * ((2 : ℝ) ^ k * r ^ (2 ^ k / 4)) := by
    intro k
    calc ‖∑' m : ℤ, (hatK k m : ℂ) * f m‖ =
        ‖∑' m : ℤ, (hatK k m : ℂ) * (if 2 ≤ m then (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) *
          cf u m * exp ((m : ℂ) * (φ : ℂ) * I) else 0)‖ := by
          congr 1; exact tsum_congr (fun m => by rw [hf m])
      _ ≤ K₀ * 2 ^ k * r ^ (2 ^ k / 4) := hK₀ r hr1 hr2 φ k
      _ = _ := by ring
  refine (tsum_of_norm_bounded (hAs.hasSum.mul_left K₀) hb).trans ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← hAs.hasSum.tsum_eq] at *; exact hAle) hK₀0

theorem zyg_bloch {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    ∃ M : ℝ, ∀ z ∈ unitDisc, ‖∑' n : ℕ, (((n : ℂ) + 2) * ((n : ℂ) + 1)) * cf u ((n : ℤ) + 2) * z ^ n‖ ≤
      M / (1 - ‖z‖) := by
  obtain ⟨K₁, hK₁⟩ := zb_total hu
  obtain ⟨U, hU0, hU⟩ := zb_Ubound hu
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑' n : ℕ, ((n : ℝ) + 2) * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact tsum_nonneg (fun n => by positivity)
  refine ⟨max (max K₁ (U * T)) 0, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hs : 0 < 1 - ‖z‖ := by linarith
  have hM0 : 0 ≤ max (max K₁ (U * T)) 0 := le_max_right _ _
  by_cases hsmall : ‖z‖ < 1 / 2
  · have hg : HasSum (fun n : ℕ => U * (((n : ℝ) + 2) * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n)) (U * T) := by
      rw [hT]; exact ((zb_polygeom (by norm_num) (by norm_num)).hasSum).mul_left U
    have hbd := tsum_of_norm_bounded hg (f := fun n : ℕ => (((n : ℂ) + 2) * ((n : ℂ) + 1)) *
        cf u ((n : ℤ) + 2) * z ^ n) (fun n => by
      have e : (((n : ℂ) + 2) * ((n : ℂ) + 1)) = ((((n : ℝ) + 2) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_pow]
      have h1 := hU ((n : ℤ) + 2)
      have h2 : ‖z‖ ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) hsmall.le n
      have h0 : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
      calc ((n : ℝ) + 2) * ((n : ℝ) + 1) * ‖cf u ((n : ℤ) + 2)‖ * ‖z‖ ^ n ≤
          ((n : ℝ) + 2) * ((n : ℝ) + 1) * U * (1 / 2 : ℝ) ^ n :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 (pow_nonneg (norm_nonneg _) _)
              (mul_nonneg h0 hU0)
        _ = _ := by ring)
    refine hbd.trans ?_
    have hUT : U * T ≤ max (max K₁ (U * T)) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [le_div_iff₀ hs]
    have := mul_nonneg (mul_nonneg hU0 hT0) (norm_nonneg z)
    nlinarith
  · have hr1 : 1 / 2 ≤ ‖z‖ := not_lt.1 hsmall
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖z‖ := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Complex.arg z := ⟨_, rfl⟩
    have hz' : z = (r : ℂ) * exp ((φ : ℂ) * I) := by
      rw [hr, hφ]; exact (Complex.norm_mul_exp_arg_mul_I z).symm
    obtain ⟨f, hf⟩ : ∃ f : ℤ → ℂ, ∀ m, f m = if 2 ≤ m then
        (((m : ℝ) * ((m : ℝ) - 1) * r ^ (m - 2) : ℝ) : ℂ) * cf u m *
          exp ((m : ℂ) * (φ : ℂ) * I) else 0 := ⟨fun m => _, fun m => rfl⟩
    have h1 := hK₁ r (by rw [hr]; exact hr1) (by rw [hr]; exact hz1) φ f hf
    have hinj : Function.Injective fun n : ℕ => (n : ℤ) + 2 := fun a b h => by simpa using h
    have hsup : Function.support f ⊆ Set.range fun n : ℕ => (n : ℤ) + 2 := by
      intro m hm
      by_contra hne
      apply hm
      rw [hf, if_neg]
      intro h2
      exact hne ⟨(m - 2).toNat, by simp only []; omega⟩
    have hre : ∑' n : ℕ, f ((n : ℤ) + 2) = ∑' m, f m := Function.Injective.tsum_eq hinj hsup
    have hterm : ∀ n : ℕ, f ((n : ℤ) + 2) = exp (2 * (φ : ℂ) * I) *
        ((((n : ℂ) + 2) * ((n : ℂ) + 1)) * cf u ((n : ℤ) + 2) * z ^ n) := by
      intro n
      rw [hf, if_pos (by omega), zb_P_nat]
      have hzn : z ^ n = (r : ℂ) ^ n * exp ((n : ℂ) * (φ : ℂ) * I) := by
        rw [hz', mul_pow, ← Complex.exp_nat_mul]; congr 2; ring
      have hex : exp ((((n : ℤ) + 2 : ℤ) : ℂ) * (φ : ℂ) * I) =
          exp (2 * (φ : ℂ) * I) * exp ((n : ℂ) * (φ : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hzn, hex]; push_cast; ring
    have hS : ∑' m, f m = exp (2 * (φ : ℂ) * I) *
        ∑' n : ℕ, (((n : ℂ) + 2) * ((n : ℂ) + 1)) * cf u ((n : ℤ) + 2) * z ^ n := by
      rw [← hre, tsum_congr hterm, tsum_mul_left]
    have hexp : ‖exp (2 * (φ : ℂ) * I)‖ = 1 := by
      have := Complex.norm_exp_ofReal_mul_I (2 * φ)
      rw [show (2 * (φ : ℂ) * I) = (((2 * φ : ℝ) : ℂ)) * I by push_cast; ring]
      exact this
    rw [hS, norm_mul, hexp, one_mul] at h1
    rw [← hr]
    refine h1.trans ?_
    have hK : K₁ ≤ max (max K₁ (U * T)) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    exact div_le_div_of_nonneg_right hK (by rw [hr] at *; linarith)

/-! ### F. Cauchy estimate and packaging in `A∞` -/

theorem ps_shift {b : ℕ → ℂ} (hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖b n‖ * ρ ^ n) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n : ℕ => ‖((n : ℂ) + 1) * b (n + 1)‖ * ρ ^ n := by
  intro ρ hρ0 hρ1
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = (1 + ρ) / 2 := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρρ : ρ < ρ' := by rw [hρ']; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ρ / ρ' := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg hρ0 hρ'0.le
  have hq1 : q < 1 := by rw [hq]; exact (div_lt_one hρ'0).2 hρρ
  have hρeq : ρ = q * ρ' := by rw [hq]; field_simp
  have hsq : Summable fun n : ℕ => ((n : ℝ) + 1) * q ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
    have h0 := summable_geometric_of_lt_one hq0 hq1
    exact (h1.add h0).congr (fun n => by simp only [pow_one]; ring)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) * q ^ n ≤ C :=
    ⟨∑' n : ℕ, ((n : ℝ) + 1) * q ^ n, fun n => hsq.le_tsum n (fun j _ => by positivity)⟩
  have hs := (summable_nat_add_iff 1).2 (hb ρ' hρ'0.le hρ'1)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left (C / ρ'))
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, hnorm]
  have h1 : ((n : ℝ) + 1) * ρ ^ n ≤ C * ρ' ^ n := by
    rw [hρeq, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hρ'0.le n)
  have h2 : ‖b (n + 1)‖ * (((n : ℝ) + 1) * ρ ^ n) ≤ ‖b (n + 1)‖ * (C * ρ' ^ n) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  calc ((n : ℝ) + 1) * ‖b (n + 1)‖ * ρ ^ n = ‖b (n + 1)‖ * (((n : ℝ) + 1) * ρ ^ n) := by ring
    _ ≤ ‖b (n + 1)‖ * (C * ρ' ^ n) := h2
    _ = C / ρ' * (‖b (n + 1)‖ * ρ' ^ (n + 1)) := by field_simp; ring

theorem ps_summable {b : ℕ → ℂ} (hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖b n‖ * ρ ^ n)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable fun n : ℕ => b n * z ^ n := by
  refine Summable.of_norm ?_
  simpa only [norm_mul, norm_pow] using hb ‖z‖ (norm_nonneg _) hz

theorem ps_hasDeriv {b : ℕ → ℂ} (hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖b n‖ * ρ ^ n)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : ℂ => ∑' n : ℕ, b n * w ^ n)
      (∑' n : ℕ, ((n : ℂ) + 1) * b (n + 1) * z ^ n) z := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (‖z‖ + 1) / 2 := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρz : ‖z‖ < ρ := by rw [hρ]; linarith
  have hρ0 : 0 ≤ ρ := by have := norm_nonneg z; linarith
  have hu := hb ρ hρ0 hρ1
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => b n * w ^ n) (Metric.ball (0 : ℂ) ρ) :=
    fun n => ((differentiable_id.pow n).const_mul (b n)).differentiableOn
  have hzU : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρz
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) ρ → ‖b n * w ^ n‖ ≤ ‖b n‖ * ρ ^ n := by
    intro n w hw
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.1 hw).le n) (norm_nonneg _)
  have hsum := hasSum_deriv_of_summable_norm hu hdiff Metric.isOpen_ball hbound hzU
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n, b n * w ^ n) (Metric.ball 0 ρ) :=
    differentiableOn_tsum_of_summable_norm hu hdiff Metric.isOpen_ball hbound
  have hat : DifferentiableAt ℂ (fun w : ℂ => ∑' n, b n * w ^ n) z :=
    hD.differentiableAt (Metric.isOpen_ball.mem_nhds hzU)
  have hdz : ∀ n : ℕ, deriv (fun w : ℂ => b n * w ^ n) z = b n * ((n : ℂ) * z ^ (n - 1)) := by
    intro n
    exact ((hasDerivAt_pow n z).const_mul (b n)).deriv
  have h1 := (hasSum_nat_add_iff' 1).2 hsum
  simp only [Finset.sum_range_one, hdz, Nat.cast_zero, zero_mul, mul_zero, sub_zero] at h1
  have hs2 : HasSum (fun n : ℕ => ((n : ℂ) + 1) * b (n + 1) * z ^ n)
      (deriv (fun w : ℂ => ∑' n, b n * w ^ n) z) := by
    convert h1 using 1
    funext n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [hs2.tsum_eq]
  exact hat.hasDerivAt

theorem bt_chain {P G0 G1 G2 : ℂ → ℂ} (hE : ∀ w : ℂ, ‖w‖ < 1 → P w = I * (w * G0 w))
    (h0 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt G0 (G1 w) w)
    (h1 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt G1 (G2 w) w)
    (h2 : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℂ G2 w) {w : ℂ} (hw : ‖w‖ < 1) :
    iteratedDeriv 3 P w = I * (3 * G2 w + w * deriv G2 w) := by
  have hev : ∀ {w : ℂ}, ‖w‖ < 1 → ∀ᶠ x in nhds w, ‖x‖ < 1 := fun {w} hw =>
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hw))
      (fun x hx => mem_ball_zero_iff.1 hx)
  have D1 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt P (I * (G0 w + w * G1 w)) w := by
    intro w hw
    have h := ((hasDerivAt_id w).mul (h0 w hw)).const_mul I
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq ?_
    filter_upwards [hev hw] with x hx
    exact hE x hx
  have D2 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt (deriv P) (I * (2 * G1 w + w * G2 w)) w := by
    intro w hw
    have h := ((h0 w hw).add ((hasDerivAt_id w).mul (h1 w hw))).const_mul I
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
    filter_upwards [hev hw] with x hx
    exact (D1 x hx).deriv
  have D3 : HasDerivAt (deriv (deriv P)) (I * (3 * G2 w + w * deriv G2 w)) w := by
    have h := (((h1 w hw).const_mul 2).add
      ((hasDerivAt_id w).mul (h2 w hw).hasDerivAt)).const_mul I
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq ?_
    filter_upwards [hev hw] with x hx
    exact (D2 x hx).deriv
  rw [iteratedDeriv_eq_iterate]
  exact D3.deriv

theorem bt_cauchy {G2 : ℂ → ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hd : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℂ G2 w)
    (hb : ∀ w : ℂ, ‖w‖ < 1 → ‖G2 w‖ ≤ M / (1 - ‖w‖)) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv G2 z‖ ≤ 4 * M / (1 - ‖z‖) ^ 2 := by
  have ht : 0 < 1 - ‖z‖ := by linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hsub : ∀ w : ℂ, ‖w - z‖ ≤ R → ‖w‖ < 1 := by
    intro w hw
    have := norm_le_norm_add_norm_sub' w z
    rw [hRdef] at hw
    linarith
  have hdc : DiffContOnCl ℂ G2 (Metric.ball z R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hR.ne']
    exact fun w hw => (hd w (hsub w (mem_closedBall_iff_norm.1 hw))).differentiableWithinAt
  have hC : ∀ w ∈ Metric.sphere z R, ‖G2 w‖ ≤ 2 * M / (1 - ‖z‖) := by
    intro w hw
    have hwz : ‖w - z‖ = R := mem_sphere_iff_norm.1 hw
    have hw1 := hsub w hwz.le
    have h1 : R ≤ 1 - ‖w‖ := by
      have := norm_le_norm_add_norm_sub' w z
      rw [hRdef] at hwz ⊢
      linarith
    calc ‖G2 w‖ ≤ M / (1 - ‖w‖) := hb w hw1
      _ ≤ M / R := div_le_div_of_nonneg_left hM0 hR h1
      _ = 2 * M / (1 - ‖z‖) := by rw [hRdef]; field_simp
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc hC
  refine this.trans (le_of_eq ?_)
  rw [hRdef]; field_simp; ring

theorem bloch_third_aux {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ < 1 → ‖iteratedDeriv 3 (uPlus u) z‖ ≤ M / (1 - ‖z‖) ^ 2 := by
  obtain ⟨M, hM⟩ := zyg_bloch hu
  obtain ⟨U, hU0, hU⟩ := zb_Ubound hu
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_zero_iff.2 (by simp)
  have hM0 : 0 ≤ M := by
    have := hM 0 h0
    simp only [norm_zero, sub_zero, div_one] at this
    exact (norm_nonneg _).trans this
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, ∀ n, g n = if n = 0 then 0 else cf u (n : ℤ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Dg, hDg⟩ : ∃ Dg : ℕ → ℂ, ∀ n, Dg n = ((n : ℂ) + 1) * g (n + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨D2g, hD2g⟩ : ∃ D2g : ℕ → ℂ, ∀ n, D2g n = ((n : ℂ) + 1) * Dg (n + 1) := ⟨_, fun _ => rfl⟩
  have hb0 : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖g n‖ * ρ ^ n := by
    intro ρ hρ0 hρ1
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left U)
    have : ‖g n‖ ≤ U := by
      rw [hg]; split_ifs
      · simpa using hU0
      · exact hU _
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hρ0 n)
  have hb1 : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖Dg n‖ * ρ ^ n := by
    simpa only [hDg] using ps_shift hb0
  have hb2 : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => ‖D2g n‖ * ρ ^ n := by
    simpa only [hD2g] using ps_shift hb1
  have hd0 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt (fun x : ℂ => ∑' n, g n * x ^ n)
      (∑' n, Dg n * w ^ n) w := fun w hw => by simpa only [hDg] using ps_hasDeriv hb0 hw
  have hd1 : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt (fun x : ℂ => ∑' n, Dg n * x ^ n)
      (∑' n, D2g n * w ^ n) w := fun w hw => by simpa only [hD2g] using ps_hasDeriv hb1 hw
  have hd2 : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℂ (fun x : ℂ => ∑' n, D2g n * x ^ n) w :=
    fun w hw => (ps_hasDeriv hb2 hw).differentiableAt
  have hE : ∀ w : ℂ, ‖w‖ < 1 → uPlus u w = I * (w * ∑' n, g n * w ^ n) := by
    intro w hw
    have hs := (ts2_uPlus_props hu).2 w (mem_ball_zero_iff.2 hw)
    have h1 := (hasSum_nat_add_iff' 1).2 hs
    simp only [Finset.sum_range_one, pow_zero, mul_one] at h1
    have h2 : HasSum (fun n : ℕ => I * (w * (g n * w ^ n))) (I * (w * ∑' n, g n * w ^ n)) :=
      ((ps_summable hb0 hw).hasSum.mul_left w).mul_left I
    have e : (fun n : ℕ => (if n + 1 < 2 then (0 : ℂ) else I * fourierCoeff (fun θ => (u θ : ℂ))
        (((n + 1 : ℕ) : ℤ) - 1)) * w ^ (n + 1)) = fun n : ℕ => I * (w * (g n * w ^ n)) := by
      funext n
      rcases n with _ | k
      · simp [hg]
      · have : ¬ (k + 1 + 1 < 2) := by omega
        simp only [if_neg this, hg, if_neg (Nat.succ_ne_zero k)]
        push_cast
        ring_nf
    rw [e] at h1
    have := h1.unique h2
    simpa using this
  have hbd : ∀ w : ℂ, ‖w‖ < 1 → ‖∑' n, D2g n * w ^ n‖ ≤ M / (1 - ‖w‖) := by
    intro w hw
    have := hM w (mem_ball_zero_iff.2 hw)
    refine le_trans (le_of_eq ?_) this
    congr 1
    refine tsum_congr (fun n => ?_)
    have e1 : g (n + 1 + 1) = cf u ((n : ℤ) + 2) := by
      rw [hg, if_neg (Nat.succ_ne_zero _)]; congr 1
    rw [hD2g, hDg, e1]; push_cast; ring
  refine ⟨7 * M, by positivity, fun z hz => ?_⟩
  rw [bt_chain hE hd0 hd1 hd2 hz, norm_mul, Complex.norm_I, one_mul]
  have hc := bt_cauchy hM0 hd2 hbd hz
  have ht : 0 < 1 - ‖z‖ := by linarith
  have h3 := hbd z hz
  have hz0 := norm_nonneg z
  have hdz : ‖z * deriv (fun x : ℂ => ∑' n, D2g n * x ^ n) z‖ ≤ 4 * M / (1 - ‖z‖) ^ 2 := by
    rw [norm_mul]
    calc ‖z‖ * ‖deriv (fun x : ℂ => ∑' n, D2g n * x ^ n) z‖ ≤ 1 * (4 * M / (1 - ‖z‖) ^ 2) :=
          mul_le_mul hz.le hc (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h4 : ‖(3 : ℂ) * ∑' n, D2g n * z ^ n‖ ≤ 3 * M / (1 - ‖z‖) := by
    rw [norm_mul]
    have : ‖(3 : ℂ)‖ = 3 := by simp
    rw [this, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have h5 : 3 * M / (1 - ‖z‖) ≤ 3 * M / (1 - ‖z‖) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc _ ≤ ‖(3 : ℂ) * ∑' n, D2g n * z ^ n‖ + ‖z * deriv (fun x : ℂ => ∑' n, D2g n * x ^ n) z‖ :=
        norm_add_le _ _
    _ ≤ 3 * M / (1 - ‖z‖) ^ 2 + 4 * M / (1 - ‖z‖) ^ 2 := add_le_add (h4.trans h5) hdz
    _ = 7 * M / (1 - ‖z‖) ^ 2 := by ring

theorem bloch_third {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    ∃ M : ℝ, ∀ z ∈ unitDisc, ‖iteratedDeriv 3 (uPlus u) z‖ ≤ M / (1 - ‖z‖) ^ 2 := by
  obtain ⟨M, -, hM⟩ := bloch_third_aux hu
  exact ⟨M, fun z hz => hM z (mem_ball_zero_iff.1 hz)⟩

theorem pack_AInf {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G unitDisc) {M : ℝ}
    (hM : ∀ z ∈ unitDisc, ‖G z‖ ≤ M / (1 - ‖z‖) ^ 2) :
    ∃ phi : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun phi z = G z := by
  have hw : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2 := by fun_prop
  have hcont : Continuous fun z : unitDisc => (((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * G z := by
    have h : ContinuousOn (fun z : ℂ => (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) * G z) unitDisc :=
      (Complex.continuous_ofReal.comp hw).continuousOn.mul hG.continuousOn
    exact h.restrict
  have hbd : ∀ z : unitDisc, ‖(((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * G z‖ ≤ 4 * |M| := by
    intro z
    have hz : ‖(z : ℂ)‖ < 1 := mem_ball_zero_iff.1 z.2
    have hz0 := norm_nonneg (z : ℂ)
    have ht : 0 < 1 - ‖(z : ℂ)‖ := by linarith
    have h1 := hM (z : ℂ) z.2
    have h2 : 0 ≤ (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 := sq_nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h2]
    calc (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * ‖G z‖ ≤ (1 - ‖(z : ℂ)‖ ^ 2) ^ 2 * (M / (1 - ‖(z : ℂ)‖) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (1 + ‖(z : ℂ)‖) ^ 2 * M := by field_simp; ring
      _ ≤ (1 + ‖(z : ℂ)‖) ^ 2 * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) (by positivity)
      _ ≤ 4 * |M| := mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg M)
  let ψ : BoundedContinuousFunction unitDisc ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : unitDisc => (((1 - ‖(z : ℂ)‖ ^ 2) ^ 2 : ℝ) : ℂ) * G z) hcont (4 * |M|) hbd
  have hun : ∀ z ∈ unitDisc, unweight unitDisc ψ z = G z := by
    intro z hz
    have ht : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hne1 : (1 - (‖z‖ : ℂ) ^ 2) ≠ 0 := by
      have : (1 - (‖z‖ : ℂ) ^ 2) = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [this]
      have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact Complex.ofReal_ne_zero.2 this.ne'
    have hne : (1 - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hne1
    simp only [unweight, dif_pos hz]
    show (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) * G z / (1 - (‖z‖ : ℂ) ^ 2) ^ 2 = G z
    push_cast
    field_simp
  have hmem : ψ ∈ AInf unitDisc := by
    show DifferentiableOn ℂ (unweight unitDisc ψ) unitDisc
    exact hG.congr hun
  exact ⟨⟨ψ, hmem⟩, fun z hz => hun z hz⟩

theorem x5_TS2_a :
    ∀ u ∈ tangentQS, (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) →
      ∃ phi : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun phi z = iteratedDeriv 3 (uPlus u) z := by
  intro u hu _
  obtain ⟨M, hM⟩ := bloch_third hu
  have hd : DifferentiableOn ℂ (iteratedDeriv 3 (uPlus u)) unitDisc := by
    have hA : AnalyticOnNhd ℂ (uPlus u) unitDisc :=
      (ts2_uPlus_props hu).1.analyticOnNhd (show IsOpen unitDisc from isOpen_ball)
    rw [iteratedDeriv_eq_iterate]
    exact (hA.iterated_deriv 3).differentiableOn
  exact pack_AInf hd hM

end TS2A

open LiZhongQC

/-- **TS2** (TT:982–990). The `ℝ`-linear isomorphism `T₀^ℝ Möb(S¹)\Homeo_qs(S¹) ≅ T₀T(1) → A∞(𝔻)` is
`u ↦ d³u₊/dz³ = i Σ_{n ≥ 2} (n³ - n) c_n z^{n-2}`.
- Stated for `u` with `c_{-1} = c_0 = c_1 = 0`.
- `d³u₊/dz³` lies in `A∞(𝔻)`.
- The map is a bijection onto `A∞(𝔻)`. -/
theorem TS2 :
    (∀ u ∈ tangentQS, (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) →
        ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = iteratedDeriv 3 (uPlus u) z) ∧
      ∀ φ : AInf unitDisc, ∃! u, u ∈ tangentQS ∧
        (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) ∧
        ∀ z ∈ unitDisc, AInf.toFun φ z = iteratedDeriv 3 (uPlus u) z :=
  ⟨TS2A.x5_TS2_a, ts2_second⟩

end TakhtajanTeo
