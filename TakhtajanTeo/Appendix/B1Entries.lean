import TakhtajanTeo.Ch2.S5_PeriodMapping
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch1.QCVariationBers

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo
open LiZhongQC Ch2 QCV
namespace AppB


/-- Second-difference bound for a bounded holomorphic function on a disc. -/
theorem b1_dslope_bound {f : ℂ → ℂ} {t0 : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball t0 (2 * r)))
    (hM : ∀ s ∈ closedBall t0 r, ‖f s‖ ≤ M) {t : ℂ} (ht : t ∈ closedBall t0 r) :
    ‖dslope f t0 t - deriv f t0‖ ≤ 3 * M * ‖t - t0‖ / r ^ 2 := by
  have hnhds : ball t0 (2 * r) ∈ 𝓝 t0 := ball_mem_nhds _ (by linarith)
  have hd1 : DifferentiableOn ℂ (dslope f t0) (ball t0 (2 * r)) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf
  have hd2 : DifferentiableOn ℂ (dslope (dslope f t0) t0) (ball t0 (2 * r)) :=
    (Complex.differentiableOn_dslope hnhds).mpr hd1
  have hcl : closure (ball t0 r) = closedBall t0 r := closure_ball t0 hr.ne'
  have hsub : closedBall t0 r ⊆ ball t0 (2 * r) := closedBall_subset_ball (by linarith)
  have hdc : DiffContOnCl ℂ (dslope (dslope f t0) t0) (ball t0 r) :=
    (hd2.mono (hcl ▸ hsub)).diffContOnCl
  have hfc : DiffContOnCl ℂ f (ball t0 r) := (hf.mono (hcl ▸ hsub)).diffContOnCl
  have hder : ‖deriv f t0‖ ≤ M / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hfc
      (fun z hz => hM z (sphere_subset_closedBall hz))
  have hsph : ∀ s ∈ sphere t0 r, ‖dslope (dslope f t0) t0 s‖ ≤ 3 * M / r ^ 2 := by
    intro s hs
    have hsr : ‖s - t0‖ = r := by simpa [dist_eq_norm] using hs
    have hne : s ≠ t0 := by
      intro h
      rw [h, sub_self, norm_zero] at hsr
      exact hr.ne hsr
    have hsne : s - t0 ≠ 0 := sub_ne_zero.mpr hne
    have e1 : dslope f t0 s = (f s - f t0) / (s - t0) := by
      rw [dslope_of_ne _ hne, slope_def_field]
    have e2 : dslope (dslope f t0) t0 s = (dslope f t0 s - deriv f t0) / (s - t0) := by
      rw [dslope_of_ne _ hne, slope_def_field, dslope_same]
    have hfs : ‖f s‖ ≤ M := hM s (sphere_subset_closedBall hs)
    have hf0 : ‖f t0‖ ≤ M := hM t0 (mem_closedBall_self hr.le)
    have h1 : ‖dslope f t0 s‖ ≤ 2 * M / r := by
      rw [e1, norm_div, hsr, div_le_div_iff_of_pos_right hr]
      calc ‖f s - f t0‖ ≤ ‖f s‖ + ‖f t0‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    rw [e2, norm_div, hsr]
    have h2 : ‖dslope f t0 s - deriv f t0‖ ≤ 3 * M / r :=
      calc ‖dslope f t0 s - deriv f t0‖ ≤ ‖dslope f t0 s‖ + ‖deriv f t0‖ := norm_sub_le _ _
        _ ≤ 2 * M / r + M / r := add_le_add h1 hder
        _ = 3 * M / r := by ring
    calc ‖dslope f t0 s - deriv f t0‖ / r ≤ (3 * M / r) / r :=
          div_le_div_of_nonneg_right h2 hr.le
      _ = 3 * M / r ^ 2 := by ring
  have hbnd : ‖dslope (dslope f t0) t0 t‖ ≤ 3 * M / r ^ 2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc
    · intro z hz
      rw [frontier_ball _ hr.ne'] at hz
      exact hsph z hz
    · rw [hcl]; exact ht
  by_cases hte : t = t0
  · subst hte
    simp [dslope_same]
  · have hsne : t - t0 ≠ 0 := sub_ne_zero.mpr hte
    have e2 : dslope (dslope f t0) t0 t = (dslope f t0 t - deriv f t0) / (t - t0) := by
      rw [dslope_of_ne _ hte, slope_def_field, dslope_same]
    rw [e2, norm_div] at hbnd
    have hpos : 0 < ‖t - t0‖ := norm_pos_iff.mpr hsne
    rw [div_le_iff₀ hpos] at hbnd
    calc ‖dslope f t0 t - deriv f t0‖ ≤ 3 * M / r ^ 2 * ‖t - t0‖ := hbnd
      _ = 3 * M * ‖t - t0‖ / r ^ 2 := by ring

/-- `Z` is bounded by `K` on finitely supported vectors, as a bilinear form. -/
def FinBil (Z : ℕ → ℕ → ℂ) (K : ℝ) : Prop :=
  ∀ (X Y : Finset ℕ) (x y : ℕ → ℂ),
    ‖∑ m ∈ Y, ∑ n ∈ X, y m * Z m n * x n‖ ≤
      K * Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2)

theorem b1_finBil_row {Z : ℕ → ℕ → ℂ} {K : ℝ} (_hK : 0 ≤ K) (h : FinBil Z K) (m : ℕ) :
    Summable (fun n => ‖Z m n‖ ^ 2) ∧ (∑' n, ‖Z m n‖ ^ 2) ≤ K ^ 2 := by
  have key : ∀ X : Finset ℕ, ∑ n ∈ X, ‖Z m n‖ ^ 2 ≤ K ^ 2 := by
    intro X
    have hb := h X {m} (fun n => conj (Z m n)) (fun _ => 1)
    have e : ∑ k ∈ ({m} : Finset ℕ), ∑ n ∈ X, (fun _ => (1 : ℂ)) k * Z k n * conj (Z m n) =
        ((∑ n ∈ X, ‖Z m n‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Finset.sum_singleton, one_mul]
      push_cast
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_comm, Complex.conj_mul']
    rw [e, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hb
    have hx : ∑ n ∈ X, ‖conj (Z m n)‖ ^ 2 = ∑ n ∈ X, ‖Z m n‖ ^ 2 := by simp
    simp only [Finset.sum_singleton, norm_one, one_pow, Real.sqrt_one, mul_one, hx] at hb
    set S := ∑ n ∈ X, ‖Z m n‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    by_cases h0 : S = 0
    · rw [h0]; positivity
    · have hpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr (lt_of_le_of_ne hS0 (Ne.symm h0))
      have : Real.sqrt S ≤ K := by
        have h2 : S = Real.sqrt S * Real.sqrt S := (Real.mul_self_sqrt hS0).symm
        nlinarith [hb]
      calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
        _ ≤ K ^ 2 := pow_le_pow_left₀ hpos.le this 2
  have hs : Summable (fun n => ‖Z m n‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

theorem b1_summable_mul_l2 {a b : ℕ → ℂ} (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2) : Summable fun n => a n * b n := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((ha.add hb).mul_left (1 / 2 : ℝ))
  intro n
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]

/-- Truncated application agrees with a finite sum. -/
theorem b1_matApply_trunc (Z : ℕ → ℕ → ℂ) (x : ℕ → ℂ) (J m : ℕ) :
    matApply Z (fun n => if n < J then x n else 0) m = ∑ n ∈ Finset.range J, Z m n * x n := by
  unfold matApply
  rw [tsum_eq_sum (s := Finset.range J)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [Finset.mem_range.mp hn]
  · intro n hn
    simp [Finset.mem_range.not.mp hn]

theorem b1_finBil_apply {Z : ℕ → ℕ → ℂ} {K : ℝ} (hK : 0 ≤ K) (h : FinBil Z K) {x : ℕ → ℂ}
    (hx : IsL2 x) :
    Summable (fun m => ‖matApply Z x m‖ ^ 2) ∧ sqSum (matApply Z x) ≤ K ^ 2 * sqSum x := by
  have hx0 : 0 ≤ sqSum x := tsum_nonneg (fun _ => sq_nonneg _)
  have hlim : ∀ m, Tendsto (fun J : ℕ => ∑ n ∈ Finset.range J, Z m n * x n) atTop
      (𝓝 (matApply Z x m)) := by
    intro m
    exact (b1_summable_mul_l2 (b1_finBil_row hK h m).1 hx).hasSum.tendsto_sum_nat
  have hfin : ∀ N J : ℕ, ∑ m ∈ Finset.range N, ‖∑ n ∈ Finset.range J, Z m n * x n‖ ^ 2 ≤
      K ^ 2 * sqSum x := by
    intro N J
    set v : ℕ → ℂ := fun m => ∑ n ∈ Finset.range J, Z m n * x n with hv
    have hb := h (Finset.range J) (Finset.range N) x (fun m => conj (v m))
    have e : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range J, conj (v m) * Z m n * x n =
        ((∑ m ∈ Finset.range N, ‖v m‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro m _
      have : ∑ n ∈ Finset.range J, conj (v m) * Z m n * x n = conj (v m) * v m := by
        rw [hv]; simp only [Finset.mul_sum, mul_assoc]
      rw [this, Complex.conj_mul']
    rw [e, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hb
    have hy : ∑ m ∈ Finset.range N, ‖conj (v m)‖ ^ 2 = ∑ m ∈ Finset.range N, ‖v m‖ ^ 2 := by simp
    rw [hy] at hb
    set S := ∑ m ∈ Finset.range N, ‖v m‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hX : ∑ n ∈ Finset.range J, ‖x n‖ ^ 2 ≤ sqSum x := hx.sum_le_tsum _ (fun _ _ => sq_nonneg _)
    have hXn : 0 ≤ ∑ n ∈ Finset.range J, ‖x n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    by_cases h0 : S = 0
    · rw [h0]; positivity
    · have hpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr (lt_of_le_of_ne hS0 (Ne.symm h0))
      have h1 : Real.sqrt S ≤ K * Real.sqrt (∑ n ∈ Finset.range J, ‖x n‖ ^ 2) := by
        have h2 : S = Real.sqrt S * Real.sqrt S := (Real.mul_self_sqrt hS0).symm
        nlinarith [hb]
      calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
        _ ≤ (K * Real.sqrt (∑ n ∈ Finset.range J, ‖x n‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ hpos.le h1 2
        _ = K ^ 2 * ∑ n ∈ Finset.range J, ‖x n‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hXn]
        _ ≤ K ^ 2 * sqSum x := mul_le_mul_of_nonneg_left hX (sq_nonneg K)
  have hN : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖matApply Z x m‖ ^ 2 ≤ K ^ 2 * sqSum x := by
    intro N
    have ht : Tendsto (fun J : ℕ => ∑ m ∈ Finset.range N,
        ‖∑ n ∈ Finset.range J, Z m n * x n‖ ^ 2) atTop
        (𝓝 (∑ m ∈ Finset.range N, ‖matApply Z x m‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro m _
      exact ((hlim m).norm).pow 2
    exact le_of_tendsto' ht (fun J => hfin N J)
  have hs : Summable (fun m => ‖matApply Z x m‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hN
  exact ⟨hs, Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hN⟩

theorem b1_df_geom (N : ℕ) {ω : ℂ} (hω : IsPrimitiveRoot ω N) (m : ℤ) :
    ∑ j ∈ Finset.range N, (ω ^ m) ^ j = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  split_ifs with h
  · have : ω ^ m = 1 := (hω.zpow_eq_one_iff_dvd m).mpr h
    simp [this]
  · have hne : ω ^ m ≠ 1 := fun h1 => h ((hω.zpow_eq_one_iff_dvd m).mp h1)
    have hN1 : (ω ^ m) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hN1]; simp

/-- Discrete Fourier extraction of one coefficient of a double power series on two circles. -/
theorem b1_df_alias {c : ℕ → ℕ → ℂ} {ρ1 ρ2 : ℝ} (h1 : 0 < ρ1) (h2 : 0 < ρ2)
    (hS : Summable fun q : ℕ × ℕ => ‖c q.1 q.2‖ * ρ1 ^ q.1 * ρ2 ^ q.2)
    (N : ℕ) (hN : 0 < N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) (p q : ℕ) :
    ((N : ℂ)⁻¹) ^ 2 * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        (((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
          ∑' r : ℕ × ℕ, c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) =
      ∑' r : ℕ × ℕ, c r.1 r.2 * ((ρ1 : ℂ) ^ ((r.1 : ℤ) - p) * (ρ2 : ℂ) ^ ((r.2 : ℤ) - q)) *
        ((if (N : ℤ) ∣ (r.1 : ℤ) - p then (1 : ℂ) else 0) *
          (if (N : ℤ) ∣ (r.2 : ℤ) - q then (1 : ℂ) else 0)) := by
  have hωn : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hz : ∀ j : ℕ, ‖(ρ1 : ℂ) * ω ^ j‖ = ρ1 := by
    intro j; simp [norm_mul, hωn, abs_of_pos h1]
  have hw : ∀ k : ℕ, ‖(ρ2 : ℂ) * ω ^ k‖ = ρ2 := by
    intro k; simp [norm_mul, hωn, abs_of_pos h2]
  have hz0 : ∀ j : ℕ, (ρ1 : ℂ) * ω ^ j ≠ 0 := by
    intro j h
    have := hz j
    rw [h, norm_zero] at this
    exact h1.ne this
  have hw0 : ∀ k : ℕ, (ρ2 : ℂ) * ω ^ k ≠ 0 := by
    intro k h
    have := hw k
    rw [h, norm_zero] at this
    exact h2.ne this
  have hsum : ∀ j k : ℕ, Summable fun r : ℕ × ℕ =>
      c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2 := by
    intro j k
    apply Summable.of_norm
    refine hS.congr (fun r => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hz, hw]
  -- pointwise identity
  have key : ∀ (j k : ℕ) (r : ℕ × ℕ),
      ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
        (c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) =
      c r.1 r.2 * ((ρ1 : ℂ) ^ ((r.1 : ℤ) - p) * (ρ2 : ℂ) ^ ((r.2 : ℤ) - q)) *
        ((ω ^ ((r.1 : ℤ) - p)) ^ j * (ω ^ ((r.2 : ℤ) - q)) ^ k) := by
    intro j k r
    have e1 : ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * ((ρ1 : ℂ) * ω ^ j) ^ r.1 =
        (ρ1 : ℂ) ^ ((r.1 : ℤ) - p) * (ω ^ ((r.1 : ℤ) - p)) ^ j := by
      have h' : ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * ((ρ1 : ℂ) * ω ^ j) ^ (r.1 : ℤ) =
          ((ρ1 : ℂ) * ω ^ j) ^ ((r.1 : ℤ) - p) := by
        rw [← zpow_add₀ (hz0 j)]; congr 1; ring
      rw [← zpow_natCast _ r.1, h', mul_zpow, ← zpow_natCast ω j, ← zpow_mul, ← zpow_natCast (ω ^ ((r.1 : ℤ) - p)) j,
        ← zpow_mul, mul_comm]
      rw [mul_comm (j : ℤ)]; exact mul_comm _ _
    have e2 : ((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) * ((ρ2 : ℂ) * ω ^ k) ^ r.2 =
        (ρ2 : ℂ) ^ ((r.2 : ℤ) - q) * (ω ^ ((r.2 : ℤ) - q)) ^ k := by
      have h' : ((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) * ((ρ2 : ℂ) * ω ^ k) ^ (r.2 : ℤ) =
          ((ρ2 : ℂ) * ω ^ k) ^ ((r.2 : ℤ) - q) := by
        rw [← zpow_add₀ (hw0 k)]; congr 1; ring
      rw [← zpow_natCast _ r.2, h', mul_zpow, ← zpow_natCast ω k, ← zpow_mul, ← zpow_natCast (ω ^ ((r.2 : ℤ) - q)) k,
        ← zpow_mul, mul_comm]
      rw [mul_comm (k : ℤ)]; exact mul_comm _ _
    calc _ = c r.1 r.2 * (((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * ((ρ1 : ℂ) * ω ^ j) ^ r.1) *
          (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) * ((ρ2 : ℂ) * ω ^ k) ^ r.2) := by ring
      _ = _ := by rw [e1, e2]; ring
  have hG : ∀ j k : ℕ, Summable fun r : ℕ × ℕ =>
      ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
        (c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) :=
    fun j k => ((hsum j k).mul_left _).mul_left _
  have hL : ∀ j k : ℕ, ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
          ∑' r : ℕ × ℕ, c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2) =
      ∑' r : ℕ × ℕ, ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
        (c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) := by
    intro j k
    rw [tsum_mul_left, tsum_mul_left]
  simp only [hL]
  have hswap : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑' r : ℕ × ℕ,
        ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
          (c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) =
      ∑' r : ℕ × ℕ, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((ρ1 : ℂ) * ω ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω ^ k) ^ (-(q : ℤ)) *
          (c r.1 r.2 * ((ρ1 : ℂ) * ω ^ j) ^ r.1 * ((ρ2 : ℂ) * ω ^ k) ^ r.2)) := by
    rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => hG j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [Summable.tsum_finsetSum (fun k _ => hG j k)]
  rw [hswap, ← tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [key]
  have e : ∀ A : ℂ, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      A * ((ω ^ ((r.1 : ℤ) - p)) ^ j * (ω ^ ((r.2 : ℤ) - q)) ^ k) =
      A * ((∑ j ∈ Finset.range N, (ω ^ ((r.1 : ℤ) - p)) ^ j) *
        ∑ k ∈ Finset.range N, (ω ^ ((r.2 : ℤ) - q)) ^ k) := by
    intro A
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  rw [e, b1_df_geom N hω, b1_df_geom N hω]
  split_ifs <;> simp <;> field_simp


theorem b1_df_div_max {N p q a b : ℕ} (hp : p < N) (hq : q < N) (hne : (a, b) ≠ (p, q))
    (ha : (N : ℤ) ∣ (a : ℤ) - p) (hb : (N : ℤ) ∣ (b : ℤ) - q) : N ≤ max a b := by
  by_cases hap : a = p
  · subst hap
    have hbq : b ≠ q := fun h => hne (by rw [h])
    have hne' : (b : ℤ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hbq)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have h2 : (N : ℤ) ∣ (q : ℤ) - b := by
        have := dvd_neg.mpr hb; simpa using this
      have := Int.le_of_dvd (by omega) h2
      omega
    · have := Int.le_of_dvd hgt hb
      omega
  · have hne' : (a : ℤ) - p ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hap)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have h2 : (N : ℤ) ∣ (p : ℤ) - a := by
        have := dvd_neg.mpr ha; simpa using this
      have := Int.le_of_dvd (by omega) h2
      omega
    · have := Int.le_of_dvd hgt ha
      omega

theorem b1_df_coeff_diff {U : Set ℂ} (hU : IsOpen U) {c : ℂ → ℕ → ℕ → ℂ} {L : ℕ → ℕ → ℝ}
    {ρ1 ρ2 : ℝ} (h1 : 0 < ρ1) (h2 : 0 < ρ2) (hL0 : ∀ p q, 0 ≤ L p q)
    (hLs : Summable fun r : ℕ × ℕ => L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2)
    (hb : ∀ t ∈ U, ∀ p q, ‖c t p q‖ ≤ L p q)
    (hdiff : ∀ z w : ℂ, ‖z‖ = ρ1 → ‖w‖ = ρ2 →
      DifferentiableOn ℂ (fun t => ∑' r : ℕ × ℕ, c t r.1 r.2 * z ^ r.1 * w ^ r.2) U)
    (p q : ℕ) : DifferentiableOn ℂ (fun t => c t p q) U := by
  let ω : ℕ → ℂ := fun N => Complex.exp (2 * π * I / N)
  let A : ℕ → ℂ → ℂ := fun N t => ((N : ℂ)⁻¹) ^ 2 * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    (((ρ1 : ℂ) * ω N ^ j) ^ (-(p : ℤ)) * (((ρ2 : ℂ) * ω N ^ k) ^ (-(q : ℤ)) *
      ∑' r : ℕ × ℕ, c t r.1 r.2 * ((ρ1 : ℂ) * ω N ^ j) ^ r.1 * ((ρ2 : ℂ) * ω N ^ k) ^ r.2))
  have hωn : ∀ N : ℕ, 0 < N → IsPrimitiveRoot (ω N) N := fun N hN =>
    Complex.isPrimitiveRoot_exp N hN.ne'
  have hnorm : ∀ N : ℕ, 0 < N → ‖ω N‖ = 1 := fun N hN => (hωn N hN).norm'_eq_one hN.ne'
  have hAd : ∀ N : ℕ, 0 < N → DifferentiableOn ℂ (A N) U := by
    intro N hN
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro j _
    apply DifferentiableOn.fun_sum
    intro k _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.const_mul
    apply hdiff
    · simp [hnorm N hN, abs_of_pos h1]
    · simp [hnorm N hN, abs_of_pos h2]
  have hS : ∀ t ∈ U, Summable fun r : ℕ × ℕ => ‖c t r.1 r.2‖ * ρ1 ^ r.1 * ρ2 ^ r.2 := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) hLs
    gcongr
    exact hb t ht _ _
  let T : ℕ → ℕ × ℕ → ℝ := fun N r =>
    if N ≤ max r.1 r.2 then L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2 else 0
  have hTpos : ∀ N (r : ℕ × ℕ), N ≤ max r.1 r.2 → T N r = L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2 :=
    fun N r h => if_pos h
  have hTneg : ∀ N (r : ℕ × ℕ), ¬ N ≤ max r.1 r.2 → T N r = 0 := fun N r h => if_neg h
  have hLr : ∀ r : ℕ × ℕ, 0 ≤ L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2 := fun r => by
    have := hL0 r.1 r.2; positivity
  have hT0 : ∀ N r, 0 ≤ T N r := by
    intro N r
    by_cases h : N ≤ max r.1 r.2
    · rw [hTpos N r h]; exact hLr r
    · rw [hTneg N r h]
  have hTle : ∀ N r, T N r ≤ L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2 := by
    intro N r
    by_cases h : N ≤ max r.1 r.2
    · rw [hTpos N r h]
    · rw [hTneg N r h]; exact hLr r
  have hTs : ∀ N, Summable (T N) := fun N =>
    Summable.of_nonneg_of_le (hT0 N) (hTle N) hLs
  have hTlim : Tendsto (fun N => ∑' r, T N r) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := T) (g := fun _ => (0 : ℝ))
      (bound := fun r : ℕ × ℕ => L r.1 r.2 * ρ1 ^ r.1 * ρ2 ^ r.2) hLs
      (fun r => tendsto_const_nhds.congr' ((eventually_gt_atTop (max r.1 r.2)).mono
        (fun N hN => (hTneg N r (not_le.mpr hN)).symm)))
      (Eventually.of_forall fun N r => by
        rw [Real.norm_of_nonneg (hT0 N r)]; exact hTle N r)
    simpa using this
  have hbound : ∀ t ∈ U, ∀ N : ℕ, 0 < N → p < N → q < N →
      ‖A N t - c t p q‖ ≤ (ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹ * ∑' r, T N r := by
    intro t ht N hN hpN hqN
    have hal := b1_df_alias h1 h2 (hS t ht) N hN (hωn N hN) p q
    set f : ℕ × ℕ → ℂ := fun r => c t r.1 r.2 * ((ρ1 : ℂ) ^ ((r.1 : ℤ) - p) * (ρ2 : ℂ) ^ ((r.2 : ℤ) - q)) *
      ((if (N : ℤ) ∣ (r.1 : ℤ) - p then (1 : ℂ) else 0) *
        (if (N : ℤ) ∣ (r.2 : ℤ) - q then (1 : ℂ) else 0)) with hf
    have hAeq : A N t = ∑' r, f r := hal
    have ha0 : 0 ≤ (ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹ := by positivity
    have hfb : ∀ r : ℕ × ℕ, r ≠ (p, q) → ‖f r‖ ≤ (ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹ * T N r := by
      intro r hr
      by_cases hd : (N : ℤ) ∣ (r.1 : ℤ) - p ∧ (N : ℤ) ∣ (r.2 : ℤ) - q
      · have hm : N ≤ max r.1 r.2 := b1_df_div_max hpN hqN hr hd.1 hd.2
        rw [hTpos N r hm]
        have e1 : ‖(ρ1 : ℂ) ^ ((r.1 : ℤ) - p)‖ = ρ1 ^ r.1 * (ρ1 ^ p)⁻¹ := by
          rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg h1.le, zpow_sub₀ h1.ne']
          simp [div_eq_mul_inv]
        have e2 : ‖(ρ2 : ℂ) ^ ((r.2 : ℤ) - q)‖ = ρ2 ^ r.2 * (ρ2 ^ q)⁻¹ := by
          rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg h2.le, zpow_sub₀ h2.ne']
          simp [div_eq_mul_inv]
        simp only [hf, hd.1, hd.2, if_true, mul_one, norm_mul, e1, e2]
        have hcb := hb t ht r.1 r.2
        have hp1 : 0 ≤ ρ1 ^ r.1 * (ρ1 ^ p)⁻¹ := by positivity
        have hp2 : 0 ≤ ρ2 ^ r.2 * (ρ2 ^ q)⁻¹ := by positivity
        calc ‖c t r.1 r.2‖ * (ρ1 ^ r.1 * (ρ1 ^ p)⁻¹ * (ρ2 ^ r.2 * (ρ2 ^ q)⁻¹))
            ≤ L r.1 r.2 * (ρ1 ^ r.1 * (ρ1 ^ p)⁻¹ * (ρ2 ^ r.2 * (ρ2 ^ q)⁻¹)) :=
              mul_le_mul_of_nonneg_right hcb (mul_nonneg hp1 hp2)
          _ = _ := by ring
      · have h0 : f r = 0 := by
          rw [not_and_or] at hd
          rcases hd with hd | hd <;> simp [hf, hd]
        rw [h0, norm_zero]
        exact mul_nonneg ha0 (hT0 N r)
    have hfpq : f (p, q) = c t p q := by simp [hf]
    have hsf : Summable f := by
      refine Summable.of_norm_bounded_eventually
        ((hTs N).mul_left ((ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹)) ?_
      have : ({(p, q)} : Set (ℕ × ℕ))ᶜ ∈ (cofinite : Filter (ℕ × ℕ)) :=
        Set.Finite.compl_mem_cofinite (Set.finite_singleton _)
      filter_upwards [this] with r hr
      exact hfb r hr
    rw [hAeq, hsf.tsum_eq_add_tsum_ite (p, q), hfpq, add_sub_cancel_left]
    refine tsum_of_norm_bounded ((hTs N).hasSum.mul_left ((ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹)) (fun r => ?_)
    by_cases hr : r = (p, q)
    · simp only [hr, if_true, norm_zero]
      exact mul_nonneg ha0 (hT0 N _)
    · simp only [hr, if_false]
      exact hfb r hr
  have hE : Tendsto (fun N => (ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹ * ∑' r, T N r) atTop (𝓝 0) := by
    simpa using hTlim.const_mul ((ρ1 ^ p)⁻¹ * (ρ2 ^ q)⁻¹)
  have hlimA : TendstoUniformlyOn A (fun t => c t p q) atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hE.eventually (gt_mem_nhds hε), eventually_gt_atTop (max p q)] with N hN1 hN2
    intro t ht
    have hpN : p < N := lt_of_le_of_lt (le_max_left _ _) hN2
    have hqN : q < N := lt_of_le_of_lt (le_max_right _ _) hN2
    rw [dist_eq_norm, norm_sub_rev]
    exact (hbound t ht N (by omega) hpN hqN).trans_lt hN1
  exact hlimA.tendstoLocallyUniformlyOn.differentiableOn
    ((eventually_gt_atTop 0).mono fun N hN => hAd N hN) hU



theorem b1_fsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : fsans μ = fB μ := by
  ext z; simp [fsans, b8_weldConst_zero hμ, lambdaW]

/-- Möbius invariance of the Grunsky kernel `K₁` (off the diagonal). -/
theorem b1_kerK1_fB_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ unitDisc)
    (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    kerK1 (fB μ) z w = kerK1 (normalizedSolution (extB μ)) z w := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  obtain ⟨-, hhol, hinj, -⟩ := qcv_W_props hk
  obtain ⟨M, hM, W, hW, hfinite, -, f, hf, -⟩ := (wB_spec hμ).1
  have hWeq : normalizedSolution (extB μ) = W := qcv_ns_eq (norm_nonneg μ) hk (extB_isBeltramiCoeff μ) hW
  obtain ⟨a, b, c, d, hdet, rfl⟩ := hM
  have hden : ∀ z ∈ unitDisc, c * W z + d ≠ 0 := by
    intro z hz he
    have hfin := (hfinite z).symm.trans (hf z hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin
    exact OnePoint.infty_ne_coe _ hfin
  have hrep : EqOn (fB μ) (fun z => (a * W z + b) / (c * W z + d)) unitDisc := by
    intro z hz
    rw [fB, hfinite z, mobiusExt_coe (hden z hz)]
    rfl
  have hWd : ∀ x ∈ unitDisc, HasDerivAt W (deriv W x) x := by
    intro x hx
    rw [← hWeq]
    exact (hhol.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  have hderiv : ∀ x ∈ unitDisc, deriv (fB μ) x =
      (a * d - b * c) * deriv W x / (c * W x + d) ^ 2 := by
    intro x hx
    have h := (((hWd x hx).const_mul a).add_const b).div (((hWd x hx).const_mul c).add_const d)
      (hden x hx)
    have hev : fB μ =ᶠ[𝓝 x] fun v => (a * W v + b) / (c * W v + d) :=
      eventually_of_mem (isOpen_ball.mem_nhds hx) hrep
    have h2 : deriv (fun v => (a * W v + b) / (c * W v + d)) x =
        (a * deriv W x * (c * W x + d) - (a * W x + b) * (c * deriv W x)) / (c * W x + d) ^ 2 :=
      h.deriv
    rw [hev.deriv_eq, h2]
    have := hden x hx
    field_simp
    ring
  have hWinj : W z ≠ W w := by
    intro he
    rw [← hWeq] at he
    exact hzw (hinj (mem_univ z) (mem_univ w) he)
  have hdz := hden z hz
  have hdw := hden w hw
  have hdet' : a * d - b * c ≠ 0 := hdet
  have hWsub : W z - W w ≠ 0 := sub_ne_zero.mpr hWinj
  have hfsub : fB μ z - fB μ w = (a * d - b * c) * (W z - W w) / ((c * W z + d) * (c * W w + d)) := by
    rw [hrep hz, hrep hw, div_sub_div _ _ hdz hdw]
    congr 1
    ring
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  unfold kerK1
  simp only [hzw, ite_false]
  rw [hderiv z hz, hderiv w hw, hfsub, hWeq]
  congr 2
  field_simp

theorem b1_W_family_diff {ρ μ : LinfStar} (hρ : ρ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    DifferentiableAt ℂ (fun s : ℂ => normalizedSolution (extB (ρ + s • μ)) z) 0 ∧
      DifferentiableAt ℂ (fun s : ℂ => deriv (normalizedSolution (extB (ρ + s • μ))) z) 0 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hρn : ‖ρ‖ < 1 := by simpa [LinfStarBall] using hρ
  set r₀ : ℝ := (1 - ‖ρ‖) / (‖μ‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := by have := sub_pos.2 hρn; positivity
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hnorm : ∀ s ∈ ball (0 : ℂ) r₀, ‖ρ + s • μ‖ < 1 := by
    intro s hs
    have hsn : ‖s‖ < r₀ := by simpa using hs
    have h1 : ‖s‖ * (‖μ‖ + 1) < 1 - ‖ρ‖ := by
      rw [hr₀, lt_div_iff₀ (by positivity)] at hsn; exact hsn
    calc ‖ρ + s • μ‖ ≤ ‖ρ‖ + ‖s • μ‖ := norm_add_le _ _
      _ = ‖ρ‖ + ‖s‖ * ‖μ‖ := by rw [norm_smul]
      _ < 1 := by nlinarith [norm_nonneg μ, norm_nonneg s]
  have hball : ∀ s ∈ ball (0 : ℂ) r₀, ρ + s • μ ∈ LinfStarBall := fun s hs => by
    simpa [LinfStarBall] using hnorm s hs
  let W : ℂ → ℂ → ℂ := fun s ζ => normalizedSolution (extB (ρ + s • μ)) ζ
  have hWt : ∀ ζ, DifferentiableOn ℂ (fun s => W s ζ) (ball (0 : ℂ) r₀) := by
    intro ζ
    have hc : DifferentiableOn ℂ (fun s : ℂ => ρ + s • μ) (ball (0 : ℂ) r₀) :=
      (differentiableOn_id.smul_const μ).const_add ρ
    exact (qcv_planeB_differentiableOn ζ).comp hc hball
  refine ⟨((hWt z).differentiableAt (ball_mem_nhds _ hr₀pos)), ?_⟩
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ := by
    intro t ht
    simp only [mem_closedBall, dist_zero_right, mem_ball] at ht ⊢
    linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ closedBall (0 : ℂ) r, ‖W t 2‖ ≤ B :=
    (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hrpos.le))
  set R : ℝ := (1 - ‖z‖) / 2 with hRdef
  have hRpos : 0 < R := by have := sub_pos.2 hz1; positivity
  set ρ' : ℝ := (1 + ‖z‖) / 2 with hρdef
  have hρ1 : ρ' < 1 := by rw [hρdef]; linarith
  have hballsub : ball z R ⊆ unitDisc := by
    intro p hp
    simp only [mem_ball, dist_eq_norm] at hp
    refine mem_ball_zero_iff.mpr ?_
    have := norm_le_norm_add_norm_sub' p z
    linarith
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball z R, ‖W t ζ‖ ≤ 4 * B * (ρ' / (1 - ρ') ^ 2) := by
    intro t ht ζ hζ
    have htr₀ : t ∈ ball (0 : ℂ) r₀ := hrsub (ball_subset_closedBall ht)
    have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp (hballsub hζ)
    have hζρ : ‖ζ‖ ≤ ρ' := by
      simp only [mem_ball, dist_eq_norm] at hζ
      have := norm_le_norm_add_norm_sub' ζ z
      rw [hρdef]; linarith
    refine (qcv_W_koebe (hnorm t htr₀) hζ1).trans ?_
    have hm := qcv_mono_koebe (norm_nonneg ζ) hζρ hρ1
    have hBt := hB t (ball_subset_closedBall ht)
    calc 4 * ‖normalizedSolution (extB (ρ + t • μ)) 2‖ * (‖ζ‖ / (1 - ‖ζ‖) ^ 2)
        ≤ 4 * B * (‖ζ‖ / (1 - ‖ζ‖) ^ 2) := by gcongr
      _ ≤ 4 * B * (ρ' / (1 - ρ') ^ 2) := by gcongr
  have hζdiff : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (W t) (ball z R) := fun t ht =>
    (qcv_W_props (hnorm t (hrsub (ball_subset_closedBall ht)))).2.1.mono hballsub
  have htdiff : ∀ ζ ∈ ball z R, DifferentiableOn ℂ (fun t => W t ζ) (ball (0 : ℂ) r) := fun ζ _ =>
    (hWt ζ).mono (ball_subset_ball (by linarith))
  have hj := qcv_param_hasDerivAt_iter 1 (F := W) (c := z) (r := r) (R := R)
    (M := 4 * B * (ρ' / (1 - ρ') ^ 2)) hrpos hRpos hζdiff htdiff hM
  simpa [iteratedDeriv_one] using hj.differentiableAt

theorem b1_shift_diff {f : LinfStar → ℂ} {ν μ : LinfStar} {t1 : ℂ}
    (h : DifferentiableAt ℂ (fun s : ℂ => f ((ν + t1 • μ) + s • μ)) 0) :
    DifferentiableAt ℂ (fun t : ℂ => f (ν + t • μ)) t1 := by
  have e : (fun t : ℂ => f (ν + t • μ)) = (fun s : ℂ => f ((ν + t1 • μ) + s • μ)) ∘ (fun t => t - t1) := by
    funext t
    simp only [Function.comp_apply]
    congr 1
    rw [sub_smul]; abel
  rw [e]
  have h' : DifferentiableAt ℂ (fun s : ℂ => f ((ν + t1 • μ) + s • μ)) (t1 - t1) := by
    rwa [sub_self]
  exact DifferentiableAt.comp (f := fun t : ℂ => t - t1) t1 h' (differentiableAt_id.sub_const t1)

theorem b1_kernel_diffAt {ν μ : LinfStar} {t1 : ℂ} (h1 : ν + t1 • μ ∈ LinfStarBall) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    DifferentiableAt ℂ (fun t : ℂ =>
      (π : ℂ) * kerK1 (normalizedSolution (extB (ν + t • μ))) z w) t1 := by
  have hk1 : ‖ν + t1 • μ‖ < 1 := by simpa [LinfStarBall] using h1
  obtain ⟨hz0, hz1⟩ := b1_W_family_diff (μ := μ) h1 hz
  obtain ⟨hw0, hw1⟩ := b1_W_family_diff (μ := μ) h1 hw
  have dWz := b1_shift_diff (f := fun ρ => normalizedSolution (extB ρ) z) hz0
  have dWw := b1_shift_diff (f := fun ρ => normalizedSolution (extB ρ) w) hw0
  have dDz := b1_shift_diff (f := fun ρ => deriv (normalizedSolution (extB ρ)) z) hz1
  have dDw := b1_shift_diff (f := fun ρ => deriv (normalizedSolution (extB ρ)) w) hw1
  obtain ⟨-, hhol, hinj, -⟩ := qcv_W_props hk1
  have hne : normalizedSolution (extB (ν + t1 • μ)) z - normalizedSolution (extB (ν + t1 • μ)) w ≠ 0 :=
    sub_ne_zero.mpr (fun he => hzw (hinj (mem_univ z) (mem_univ w) he))
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hform : (fun t : ℂ => (π : ℂ) * kerK1 (normalizedSolution (extB (ν + t • μ))) z w) =
      fun t : ℂ => 1 / (z - w) ^ 2 - deriv (normalizedSolution (extB (ν + t • μ))) z *
        deriv (normalizedSolution (extB (ν + t • μ))) w /
          (normalizedSolution (extB (ν + t • μ)) z - normalizedSolution (extB (ν + t • μ)) w) ^ 2 := by
    funext t
    unfold kerK1
    simp only [hzw, ite_false]
    field_simp
  rw [hform]
  have hsub := dWz.sub dWw
  exact (differentiableAt_const _).sub ((dDz.mul dDw).div (hsub.pow 2) (pow_ne_zero 2 hne))


theorem b1_finBil_of_contractive {B : ℕ → ℕ → ℂ} (hB : B7Contractive B) : FinBil B 1 := by
  intro X Y x y
  let x' : ℕ → ℂ := fun n => if n ∈ X then x n else 0
  have hx' : Summable (fun n => ‖x' n‖ ^ 2) :=
    summable_of_ne_finset_zero (s := X) (by intro n hn; simp [x', hn])
  obtain ⟨hs, hle⟩ := hB x' hx'
  have hv : ∀ m, b7Apply B x' m = ∑ n ∈ X, B m n * x n := by
    intro m
    unfold b7Apply
    rw [tsum_eq_sum (s := X) (by intro n hn; simp [x', hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [x', hn]
  have hsq : ∑' n, ‖x' n‖ ^ 2 = ∑ n ∈ X, ‖x n‖ ^ 2 := by
    rw [tsum_eq_sum (s := X) (by intro n hn; simp [x', hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [x', hn]
  have e : ∑ m ∈ Y, ∑ n ∈ X, y m * B m n * x n = ∑ m ∈ Y, y m * b7Apply B x' m := by
    apply Finset.sum_congr rfl
    intro m _
    rw [hv m, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [e]
  have hY : ∑ m ∈ Y, ‖b7Apply B x' m‖ ^ 2 ≤ ∑ n ∈ X, ‖x n‖ ^ 2 :=
    calc _ ≤ ∑' m, ‖b7Apply B x' m‖ ^ 2 := hs.sum_le_tsum _ (fun _ _ => sq_nonneg _)
      _ ≤ _ := hsq ▸ hle
  calc ‖∑ m ∈ Y, y m * b7Apply B x' m‖ ≤ ∑ m ∈ Y, ‖y m‖ * ‖b7Apply B x' m‖ :=
        (norm_sum_le _ _).trans (by simp [norm_mul])
    _ ≤ Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖b7Apply B x' m‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2) * Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
    _ = 1 * Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2) := by ring

theorem b1_basis_weight (p q : ℕ) (z w : ℂ) :
    (π : ℂ) * (basisE p z * basisE q w) =
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ) * z ^ p * w ^ q := by
  have hr : Real.sqrt (((p : ℝ) + 1) / π) * Real.sqrt (((q : ℝ) + 1) / π) * π =
      Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) := by
    rw [← Real.sqrt_mul (by positivity)]
    have h1 : (((p : ℝ) + 1) / π) * (((q : ℝ) + 1) / π) = (((p : ℝ) + 1) * ((q : ℝ) + 1)) / π ^ 2 := by
      field_simp
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq Real.pi_pos.le]
    field_simp
  unfold basisE
  have hc : ((Real.sqrt (((p : ℝ) + 1) / π) * Real.sqrt (((q : ℝ) + 1) / π) * π : ℝ) : ℂ) =
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ) := by rw [hr]
  push_cast at hc
  calc (π : ℂ) * ((Real.sqrt ((((p : ℕ) : ℝ) + 1) / π) : ℂ) * z ^ p * ((Real.sqrt ((((q : ℕ) : ℝ) + 1) / π) : ℂ) * w ^ q))
      = ((Real.sqrt (((p : ℝ) + 1) / π) : ℂ) * (Real.sqrt (((q : ℝ) + 1) / π) : ℂ) * π) * z ^ p * w ^ q := by ring
    _ = _ := by rw [hc]

theorem b1_summable_L (ρ1 ρ2 : ℝ) (h1 : 0 < ρ1) (h1' : ρ1 < 1) (h2 : 0 < ρ2) (h2' : ρ2 < 1) :
    Summable fun r : ℕ × ℕ =>
      Real.sqrt (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1)) * ρ1 ^ r.1 * ρ2 ^ r.2 := by
  have hs : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → Summable fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n := by
    intro ρ h0 h1
    have a := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ) (by rwa [Real.norm_of_nonneg h0.le])
    have b := summable_geometric_of_lt_one h0.le h1
    refine (a.add b).congr (fun n => ?_)
    simp only [pow_one]; ring
  have hprod := Summable.mul_of_nonneg (hs ρ1 h1 h1') (hs ρ2 h2 h2')
    (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) hprod
  have hx : 1 ≤ ((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) r.1
    have := Nat.cast_nonneg (α := ℝ) r.2
    nlinarith
  have hsq : Real.sqrt (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1)) ≤ ((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1) := by
    calc _ ≤ Real.sqrt (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1)) ^ 2 := by
          have := Real.one_le_sqrt.mpr hx
          nlinarith [Real.sqrt_nonneg (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1))]
      _ = _ := Real.sq_sqrt (by positivity)
  calc Real.sqrt (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1)) * ρ1 ^ r.1 * ρ2 ^ r.2
      ≤ (((r.1 : ℝ) + 1) * ((r.2 : ℝ) + 1)) * ρ1 ^ r.1 * ρ2 ^ r.2 := by gcongr
    _ = _ := by ring

theorem b1_entries {ν μ : LinfStar} {t0 : ℂ} (h : ν + t0 • μ ∈ LinfStarBall) :
    ∃ r : ℝ, 0 < r ∧ (∀ t ∈ ball t0 (2 * r), ν + t • μ ∈ LinfStarBall) ∧
      ∀ m n, DifferentiableOn ℂ
        (fun t => B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) m n) (ball t0 (2 * r)) := by
  have hρn : ‖ν + t0 • μ‖ < 1 := by simpa [LinfStarBall] using h
  set r₀ : ℝ := (1 - ‖ν + t0 • μ‖) / (‖μ‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := by have := sub_pos.2 hρn; positivity
  refine ⟨r₀ / 2, by positivity, ?_⟩
  have h2r : 2 * (r₀ / 2) = r₀ := by ring
  rw [h2r]
  have hball : ∀ t ∈ ball t0 r₀, ν + t • μ ∈ LinfStarBall := by
    intro t ht
    have htn : ‖t - t0‖ < r₀ := by simpa [dist_eq_norm] using ht
    have h1 : ‖t - t0‖ * (‖μ‖ + 1) < 1 - ‖ν + t0 • μ‖ := by
      rw [hr₀, lt_div_iff₀ (by positivity)] at htn; exact htn
    have e : ν + t • μ = (ν + t0 • μ) + (t - t0) • μ := by rw [sub_smul]; abel
    simp only [LinfStarBall, mem_ball_zero_iff]
    rw [e]
    calc ‖(ν + t0 • μ) + (t - t0) • μ‖ ≤ ‖ν + t0 • μ‖ + ‖(t - t0) • μ‖ := norm_add_le _ _
      _ = ‖ν + t0 • μ‖ + ‖t - t0‖ * ‖μ‖ := by rw [norm_smul]
      _ < 1 := by nlinarith [norm_nonneg μ, norm_nonneg (t - t0)]
  refine ⟨hball, ?_⟩
  have hU : IsOpen (ball t0 r₀) := isOpen_ball
  -- data from the Bergman model, for each admissible `t`
  have hpm := fun t (ht : t ∈ ball t0 r₀) =>
    b8_pair_model (b8_welding_normalized_pair (hball t ht))
  have hbd : ∀ t ∈ ball t0 r₀, ∀ m n,
      ‖B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) m n‖ ≤ 1 := by
    intro t ht m n
    obtain ⟨hs, hle⟩ := (hpm t ht).2.1 m
    have h1 : ‖B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) m n‖ ^ 2 ≤ 1 :=
      (hs.le_tsum n (fun _ _ => sq_nonneg _)).trans hle
    nlinarith [norm_nonneg (B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) m n)]
  intro m n
  let c : ℂ → ℕ → ℕ → ℂ := fun t p q =>
    B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) p q *
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ)
  have hc := b1_df_coeff_diff hU (c := c) (L := fun p q => Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)))
    (ρ1 := 1 / 2) (ρ2 := 1 / 4) (by norm_num) (by norm_num) (fun p q => Real.sqrt_nonneg _)
    (b1_summable_L (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by
      intro t ht p q
      simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ 1 * Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hbd t ht p q) (Real.sqrt_nonneg _)
        _ = _ := one_mul _)
    (by
      intro z w hz hw
      have hz1 : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; norm_num)
      have hw1 : w ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hw]; norm_num)
      have hzw : z ≠ w := by
        intro he; rw [he] at hz; rw [hz] at hw; norm_num at hw
      have hdiffK : DifferentiableOn ℂ (fun t : ℂ =>
          (π : ℂ) * kerK1 (normalizedSolution (extB (ν + t • μ))) z w) (ball t0 r₀) :=
        fun t ht => (b1_kernel_diffAt (hball t ht) hz1 hw1 hzw).differentiableWithinAt
      refine hdiffK.congr (fun t ht => ?_)
      have hs := ((hpm t ht).2.2.2 z hz1 w hw1 hzw).mul_left (π : ℂ)
      have hk : kerK1 (fsans (ν + t • μ)) z w = kerK1 (normalizedSolution (extB (ν + t • μ))) z w := by
        rw [b1_fsans_eq (hball t ht)]; exact b1_kerK1_fB_eq (hball t ht) hz1 hw1 hzw
      rw [← hk]
      refine (HasSum.tsum_eq ?_)
      refine hs.congr_fun (fun p => ?_)
      have e := b1_basis_weight p.1 p.2 z w
      calc c t p.1 p.2 * z ^ p.1 * w ^ p.2
          = B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) p.1 p.2 *
            ((Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) : ℂ) * z ^ p.1 * w ^ p.2) := by
            simp only [c]; ring
        _ = B1 (grunsky (fsans (ν + t • μ)) (gsans (ν + t • μ))) p.1 p.2 *
            ((π : ℂ) * (basisE p.1 z * basisE p.2 w)) := by rw [e]
        _ = _ := by ring) m n
  have hne : ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hc.div_const ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ)).congr (fun t ht => ?_)
  simp only [c]
  field_simp

end AppB
end TakhtajanTeo
