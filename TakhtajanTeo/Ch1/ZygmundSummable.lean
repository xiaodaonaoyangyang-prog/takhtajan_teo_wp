import TakhtajanTeo.Ch1.S1_2_Homogeneous

/-! Zygmund functions have `Σ n |c_n|² < ∞` (TS4 with `s = 1/2`, TT:2136): a dyadic-block argument from the
second-difference Parseval estimate `zygmund_fourier_energy`. -/

open Real Complex Filter Set Topology MeasureTheory
noncomputable section
namespace TakhtajanTeo
set_option autoImplicit false

theorem zygmund_dyadic_multiplier_ge {k m : ℕ} (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) :
    1 ≤ ‖exp (((m : ℤ) : ℂ) * ((π / (3 * 2 ^ k) : ℝ) : ℂ) * I) +
        exp (-(((m : ℤ) : ℂ) * ((π / (3 * 2 ^ k) : ℝ) : ℂ) * I)) - 2‖ := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hm1 : (2 : ℝ) ^ k ≤ m := by exact_mod_cast h1
  have hm2 : (m : ℝ) < 2 * 2 ^ k := by
    have : (m : ℝ) < 2 ^ (k + 1) := by exact_mod_cast h2
    rwa [pow_succ, mul_comm] at this
  set x : ℝ := (m : ℝ) * (π / (3 * 2 ^ k)) with hx
  have hxlo : π / 3 ≤ x := by
    rw [hx, show (m : ℝ) * (π / (3 * 2 ^ k)) = (m / 2 ^ k) * (π / 3) by field_simp]
    have : (1 : ℝ) ≤ m / 2 ^ k := by rw [le_div_iff₀ hk]; linarith
    nlinarith [Real.pi_pos]
  have hxhi : x ≤ π := by
    rw [hx, show (m : ℝ) * (π / (3 * 2 ^ k)) = (m / 2 ^ k) * (π / 3) by field_simp]
    have : (m : ℝ) / 2 ^ k ≤ 2 := by rw [div_le_iff₀ hk]; linarith
    nlinarith [Real.pi_pos]
  have hcos : Real.cos x ≤ 1 / 2 := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hxhi hxlo
    rwa [Real.cos_pi_div_three] at this
  have he : exp (((m : ℤ) : ℂ) * ((π / (3 * 2 ^ k) : ℝ) : ℂ) * I) +
        exp (-(((m : ℤ) : ℂ) * ((π / (3 * 2 ^ k) : ℝ) : ℂ) * I)) - 2 =
      ((2 * Real.cos x - 2 : ℝ) : ℂ) := by
    have h : exp ((x : ℂ) * I) + exp (-((x : ℂ) * I)) = 2 * (Real.cos x : ℂ) := by
      rw [Complex.ofReal_cos, Complex.two_cos, neg_mul]
    have hxc : (x : ℂ) = ((m : ℤ) : ℂ) * ((π / (3 * 2 ^ k) : ℝ) : ℂ) := by
      rw [hx]; push_cast; ring
    rw [← hxc, h]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem zygmund_block_energy {u : ℝ → ℝ} (hu : IsZygmund u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
        ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 ≤ C ^ 2 * (π / (3 * 2 ^ k)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := zygmund_fourier_energy hu
  refine ⟨C, hC, fun k => ?_⟩
  have hs := h (π / (3 * 2 ^ k)) ((Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1))).image (fun m : ℕ => (m : ℤ)))
  rw [Finset.sum_image (fun a _ b _ hab => by exact_mod_cast hab)] at hs
  refine le_trans (Finset.sum_le_sum fun m hm => ?_) hs
  rw [Finset.mem_Ico] at hm
  have hge := zygmund_dyadic_multiplier_ge hm.1 hm.2
  rw [norm_mul, mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hge)

theorem zygmund_weighted_block_energy {u : ℝ → ℝ} (hu : IsZygmund u) :
    ∃ B : ℝ, ∀ k : ℕ,
      ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
        (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 ≤ B * (1 / 2) ^ k := by
  obtain ⟨C, hC, h⟩ := zygmund_block_energy hu
  refine ⟨2 * C ^ 2 * π ^ 2 / 9, fun k => ?_⟩
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)), (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2
      ≤ ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)), (2 : ℝ) ^ (k + 1) *
          ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Ico] at hm
        have : (m : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hm.2.le
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ = (2 : ℝ) ^ (k + 1) * ∑ m ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
          ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (k + 1) * (C ^ 2 * (π / (3 * 2 ^ k)) ^ 2) :=
        mul_le_mul_of_nonneg_left (h k) (by positivity)
    _ = 2 * C ^ 2 * π ^ 2 / 9 * (1 / 2) ^ k := by
        rw [pow_succ, div_pow, one_div, inv_pow]
        field_simp
        ring

theorem zygmund_summable_aux {u : ℝ → ℝ} (hu : IsZygmund u) :
    Summable fun m : ℕ => (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 := by
  obtain ⟨B, hB⟩ := zygmund_weighted_block_energy hu
  have hnn : ∀ m : ℕ, 0 ≤ (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 :=
    fun m => mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)
  have hB0 : 0 ≤ B := by
    have h0 : 0 ≤ ∑ m ∈ Finset.Ico (2 ^ 0 : ℕ) (2 ^ (0 + 1)),
        (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 :=
      Finset.sum_nonneg fun m _ => hnn m
    simpa using le_trans h0 (hB 0)
  have hS : ∀ K : ℕ, ∑ m ∈ Finset.range (2 ^ K),
      (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 ≤
        B * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)),
        Finset.sum_range_succ, mul_add]
      exact add_le_add ih (hB K)
  apply summable_of_sum_range_le hnn (c := B * 2)
  intro n
  calc ∑ m ∈ Finset.range n, (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2
      ≤ ∑ m ∈ Finset.range (2 ^ n), (m : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (m : ℤ)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.lt_two_pow_self).le) (fun m _ _ => hnn m)
    _ ≤ B * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := hS n
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hB0

/-- (TT:2136) The series (4.1) converges for a Zygmund tangent vector. -/
theorem zygmund_vk_summable {u : ℝ → ℝ} (hu : IsZygmund u) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (n + 1)‖ ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (zygmund_summable_aux hu)
  refine h.congr fun n => ?_
  push_cast
  rfl

end TakhtajanTeo
