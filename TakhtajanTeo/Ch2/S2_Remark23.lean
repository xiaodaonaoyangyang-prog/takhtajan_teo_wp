import TakhtajanTeo.Appendix.B1Entries
import TakhtajanTeo.Ch2.S2_Thm26
import TakhtajanTeo.Ch2.S2_Remark22
import TakhtajanTeo.Ch2.FaberBoundary
import TakhtajanTeo.Ch2.S2_MixedHook

/-!
# Ch2 §2: Remark 2.3 (`k23_` copy)

`remark_2_3` is proved here as `k23_remark_2_3`, with the statement byte-identical. Route:
* `k23_B1_bound` (下属3, with `k23_B1_origin`): `‖B₁(μ)x‖ ≤ c‖x‖` with `0 ≤ c < 1`, by the Schwarz lemma in `t` for the bilinear form
  `Σ y_m B₁(tμ)_{mn} x_n` (holomorphy `AppB.b1_entries`, contraction `‖B₁‖ ≤ 1` on the ball).
* `k23_B4_bound`: from `k23_B1_bound` at `μ⁻¹`, since `B₁(μ⁻¹) = conj B₄(μ)` entrywise (`fb_inv_block`).
* `k23_col_isometry`: if the columns of `(A; A')` are orthonormal and the rows of `A`, `A'` are in `ℓ²`, then
  `‖Ax‖² + ‖A'x‖² = ‖x‖²` on `ℓ²` (finite supports, then truncation and Fatou).
* `k23_B2_below`, `k23_B3_below`: `(1 - c²)‖x‖² ≤ ‖B₂x‖²` (columns of `(B₂; B₄)`), and the same for `B₃` (columns of
  `(B₁; B₃)`), by `grunsky_unitary`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `B₁ = 0` at the origin: `f^0 = id`, so `K₁ = 0`, and Lemma 2.5 (Parseval) kills every Grunsky coefficient. -/
theorem k23_B1_origin (m n : ℕ) : B1 (grunsky (fsans (0 : LinfStar)) (gsans (0 : LinfStar))) m n = 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have L := s2c_lemma_2_5 (AppB.b8_welding_normalized_pair h0) (r22_complement_null h0)
  have hK : (∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (0 : LinfStar)) p.1 p.2‖₊ : ℝ≥0∞) ^ 2) = 0 := by
    rw [gk_fsans_zero]
    simp [AppB.kerK1_id]
  have hfin : (∫⁻ p in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (0 : LinfStar)) p.1 p.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
    rw [hK]
    exact ENNReal.zero_lt_top
  have hsumm := L.1.mp hfin
  have heq := (L.2.1 hfin).1
  rw [hK, ENNReal.ofReal_eq_zero] at heq
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ ((p.1 + 1) * (p.2 + 1) : ℝ) *
      ‖grunsky (fsans (0 : LinfStar)) (gsans (0 : LinfStar)) (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2 :=
    fun p => by positivity
  have htsum : (∑' p : ℕ × ℕ, ((p.1 + 1) * (p.2 + 1) : ℝ) *
      ‖grunsky (fsans (0 : LinfStar)) (gsans (0 : LinfStar)) (-(p.1 + 1 : ℤ)) (-(p.2 + 1 : ℤ))‖ ^ 2) = 0 :=
    le_antisymm heq (tsum_nonneg hnn)
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp (htsum ▸ hsumm.hasSum)) (m, n)
  have hpos : (0 : ℝ) < ((m : ℝ) + 1) * ((n : ℝ) + 1) := by positivity
  have hb : ‖grunsky (fsans (0 : LinfStar)) (gsans (0 : LinfStar)) (-(m + 1 : ℤ)) (-(n + 1 : ℤ))‖ = 0 := by
    have h2 : ‖grunsky (fsans (0 : LinfStar)) (gsans (0 : LinfStar)) (-(m + 1 : ℤ)) (-(n + 1 : ℤ))‖ ^ 2 = 0 := by
      have := hz
      simp only [Pi.zero_apply] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · exact h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  unfold B1
  rw [norm_eq_zero.mp hb, mul_zero]

/-- (下属3) Strict Grunsky bound for `B₁`: there is `0 ≤ c < 1` with `‖B₁x‖ ≤ c‖x‖` on `ℓ²`. -/
theorem k23_B1_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    let b := grunsky (fsans μ) (gsans μ)
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 := by
  intro b
  have hn : ‖μ‖ < 1 := mem_ball_zero_iff.mp hμ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 / (1 + ‖μ‖) := ⟨_, rfl⟩
  have hμ0 : 0 < 1 + ‖μ‖ := by positivity
  have hR1 : 1 < R := by rw [hR, lt_div_iff₀ hμ0]; linarith
  have hRμ : R * ‖μ‖ < 1 := by rw [hR, div_mul_eq_mul_div, div_lt_one hμ0]; linarith
  have hmem : ∀ t ∈ ball (0 : ℂ) R, (0 : LinfStar) + t • μ ∈ LinfStarBall := by
    intro t ht
    rw [zero_add]
    show t • μ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    have h1 : ‖t‖ < R := mem_ball_zero_iff.mp ht
    calc ‖t‖ * ‖μ‖ ≤ R * ‖μ‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
      _ < 1 := hRμ
  obtain ⟨Bt, hBt⟩ : ∃ Bt : ℂ → ℕ → ℕ → ℂ,
      Bt = fun t => B1 (grunsky (fsans ((0 : LinfStar) + t • μ)) (gsans ((0 : LinfStar) + t • μ))) := ⟨_, rfl⟩
  have hdiff : ∀ m n, DifferentiableOn ℂ (fun t => Bt t m n) (ball 0 R) := by
    intro m n t ht
    obtain ⟨r, hr, -, hd⟩ := AppB.b1_entries (hmem t ht)
    rw [hBt]
    exact ((hd m n).differentiableAt (ball_mem_nhds t (by linarith))).differentiableWithinAt
  have hbil : ∀ t ∈ ball (0 : ℂ) R, AppB.FinBil (Bt t) 1 := by
    intro t ht
    rw [hBt]
    exact AppB.b1_finBil_of_contractive (AppB.b8_pair_model (AppB.b8_welding_normalized_pair (hmem t ht))).2.2.1
  have h0 : ∀ m n, Bt 0 m n = 0 := by
    intro m n
    rw [hBt]
    show B1 (grunsky (fsans ((0 : LinfStar) + (0 : ℂ) • μ)) (gsans ((0 : LinfStar) + (0 : ℂ) • μ))) m n = 0
    rw [zero_smul, add_zero]
    exact k23_B1_origin m n
  -- the Schwarz lemma for each finite bilinear form
  have hc : AppB.FinBil (Bt 1) ((1 + ‖μ‖) / 2) := by
    intro X Y x y
    obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, φ = fun t => ∑ m ∈ Y, ∑ n ∈ X, y m * Bt t m n * x n := ⟨_, rfl⟩
    have hφd : DifferentiableOn ℂ φ (ball 0 R) := by
      rw [hφ]
      apply DifferentiableOn.fun_sum
      intro m _
      apply DifferentiableOn.fun_sum
      intro n _
      exact ((hdiff m n).const_mul (y m)).mul_const (x n)
    have hφ0 : φ 0 = 0 := by
      rw [hφ]
      simp [h0]
    have hmaps : MapsTo φ (ball 0 R)
        (closedBall (φ 0) (Real.sqrt (∑ n ∈ X, ‖x n‖ ^ 2) * Real.sqrt (∑ m ∈ Y, ‖y m‖ ^ 2))) := by
      intro t ht
      rw [hφ0, mem_closedBall_zero_iff, hφ]
      have h := hbil t ht X Y x y
      rwa [one_mul] at h
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, norm_one]; exact hR1
    have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφd hmaps h1
    rw [hφ0, dist_zero_right, dist_zero_right, norm_one, mul_one] at hs
    have he : φ 1 = ∑ m ∈ Y, ∑ n ∈ X, y m * Bt 1 m n * x n := by rw [hφ]
    rw [← he]
    refine hs.trans (le_of_eq ?_)
    rw [hR, div_div_eq_mul_div]
    ring
  refine ⟨(1 + ‖μ‖) / 2, by positivity, by linarith, fun x hx => ?_⟩
  have hb1 : Bt 1 = B1 b := by
    rw [hBt]
    show B1 (grunsky (fsans ((0 : LinfStar) + (1 : ℂ) • μ)) (gsans ((0 : LinfStar) + (1 : ℂ) • μ))) =
      B1 (grunsky (fsans μ) (gsans μ))
    rw [one_smul, zero_add]
  have h := (AppB.b1_finBil_apply (by positivity) hc hx).2
  rw [hb1] at h
  exact h

/-- Strict Grunsky bound for `B₄`, from `k23_B1_bound` at `μ⁻¹` (`B₁(μ⁻¹) = conj B₄(μ)`, `fb_inv_block`). -/
theorem k23_B4_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    let b := grunsky (fsans μ) (gsans μ)
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B4 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 := by
  intro b
  have hν := bc_beltramiInv_mem_ball hμ
  obtain ⟨c, hc0, hc1, hc⟩ := k23_B1_bound hν
  refine ⟨c, hc0, hc1, fun x hx => ?_⟩
  -- `B₄(μ) = conj B₁(μ⁻¹)` entrywise
  have hent : ∀ m n, B4 b m n =
      conj (B1 (grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ))) m n) := by
    intro m n
    have h := FB.fb_inv_block hμ (m + 1) (n + 1) (by omega) (by omega)
    push_cast at h
    unfold B1 B4
    rw [map_mul, h, Complex.conj_conj, Complex.conj_ofReal]
  have hx' : Summable (fun n => ‖conj (x n)‖ ^ 2) := by
    simpa only [Complex.norm_conj] using hx
  have h := hc (fun n => conj (x n)) hx'
  have hrow : ∀ m, ‖∑' n, B4 b m n * x n‖ =
      ‖∑' n, B1 (grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ))) m n * conj (x n)‖ := by
    intro m
    have he : (fun n => B4 b m n * x n) = fun n =>
        conj (B1 (grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ))) m n * conj (x n)) := by
      funext n
      rw [hent, map_mul, Complex.conj_conj]
    rw [he, ← Complex.conj_tsum, Complex.norm_conj]
  calc ∑' m, ‖∑' n, B4 b m n * x n‖ ^ 2
      = ∑' m, ‖∑' n, B1 (grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ))) m n * conj (x n)‖ ^ 2 :=
        tsum_congr (fun m => by rw [hrow])
    _ ≤ c ^ 2 * ∑' n, ‖conj (x n)‖ ^ 2 := h
    _ = c ^ 2 * ∑' n, ‖x n‖ ^ 2 := by simp only [Complex.norm_conj]

/-- `conj z * z = ‖z‖²` as a complex number. -/
theorem k23_conj_mul (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Products of two square-summable sequences are summable. -/
theorem k23_summable_mul {a b : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖ ^ 2))
    (hb : Summable (fun n => ‖b n‖ ^ 2)) : Summable (fun n => a n * b n) := by
  refine Summable.of_norm_bounded ((ha.add hb).div_const 2) fun n => ?_
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]

/-- The diagonal of the column identity forces square-summable columns. -/
theorem k23_col_summable {A A' : ℕ → ℕ → ℂ}
    (hcol : ∀ m n, (∑' k, (conj (A k m) * A k n + conj (A' k m) * A' k n)) = kron m n) (n : ℕ) :
    Summable (fun k => ‖A k n‖ ^ 2) ∧ Summable (fun k => ‖A' k n‖ ^ 2) := by
  have h := hcol n n
  simp only [kron, if_true, k23_conj_mul, ← Complex.ofReal_add] at h
  have hs : Summable (fun k => ‖A k n‖ ^ 2 + ‖A' k n‖ ^ 2) := by
    by_contra hns
    have h0 : (∑' k, (((‖A k n‖ ^ 2 + ‖A' k n‖ ^ 2 : ℝ)) : ℂ)) = 0 := by
      rw [tsum_eq_zero_of_not_summable]
      rwa [Complex.summable_ofReal]
    rw [h0] at h
    exact zero_ne_one h
  exact ⟨hs.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖A' k n‖]),
    hs.of_nonneg_of_le (fun _ => by positivity) (fun k => by nlinarith [sq_nonneg ‖A k n‖])⟩

/-- The column identity for finitely supported vectors. -/
theorem k23_col_finite {A A' : ℕ → ℕ → ℂ}
    (hcol : ∀ m n, (∑' k, (conj (A k m) * A k n + conj (A' k m) * A' k n)) = kron m n)
    {x : ℕ → ℂ} {N : ℕ} (hx : ∀ n, N ≤ n → x n = 0) :
    Summable (fun m => ‖∑' n, A m n * x n‖ ^ 2 + ‖∑' n, A' m n * x n‖ ^ 2) ∧
      (∑' m, (‖∑' n, A m n * x n‖ ^ 2 + ‖∑' n, A' m n * x n‖ ^ 2)) = ∑' n, ‖x n‖ ^ 2 := by
  have hsupp : ∀ (B : ℕ → ℕ → ℂ) (m : ℕ), (∑' n, B m n * x n) = ∑ n ∈ Finset.range N, B m n * x n := by
    intro B m
    apply tsum_eq_sum
    intro n hn
    rw [hx n (by simpa using hn), mul_zero]
  have hxs : (∑' n, ‖x n‖ ^ 2) = ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 := by
    apply tsum_eq_sum
    intro n hn
    rw [hx n (by simpa using hn), norm_zero]
    norm_num
  have hcs := k23_col_summable hcol
  -- the complex-valued terms
  let F : ℕ → ℕ → ℕ → ℂ := fun n n' m =>
    conj (x n) * x n' * (conj (A m n) * A m n' + conj (A' m n) * A' m n')
  have hF : ∀ n n', Summable (F n n') := by
    intro n n'
    have h1 := k23_summable_mul (a := fun m => conj (A m n)) (b := fun m => A m n')
      (by simpa using (hcs n).1) (hcs n').1
    have h2 := k23_summable_mul (a := fun m => conj (A' m n)) (b := fun m => A' m n')
      (by simpa using (hcs n).2) (hcs n').2
    exact (h1.add h2).mul_left _
  have hterm : ∀ m, ((‖∑' n, A m n * x n‖ ^ 2 + ‖∑' n, A' m n * x n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N, F n n' m := by
    intro m
    rw [Complex.ofReal_add, ← k23_conj_mul, ← k23_conj_mul, hsupp A m, hsupp A' m, map_sum, map_sum,
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [F, map_mul]
    ring
  have hsumC : Summable (fun m => ∑ n ∈ Finset.range N, ∑ n' ∈ Finset.range N, F n n' m) :=
    summable_sum fun n _ => summable_sum fun n' _ => hF n n'
  have hsumR : Summable (fun m => ‖∑' n, A m n * x n‖ ^ 2 + ‖∑' n, A' m n * x n‖ ^ 2) := by
    rw [← Complex.summable_ofReal]
    simpa only [hterm] using hsumC
  refine ⟨hsumR, ?_⟩
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  simp only [hterm]
  rw [Summable.tsum_finsetSum (fun n _ => summable_sum fun n' _ => hF n n')]
  simp_rw [Summable.tsum_finsetSum (fun n' _ => hF _ n')]
  have hin : ∀ n n', (∑' m, F n n' m) = conj (x n) * x n' * kron n n' := by
    intro n n'
    simp only [F]
    rw [tsum_mul_left, hcol n n']
  simp only [hin, kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [hxs, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (Finset.mem_range.mp hn), k23_conj_mul]

/-- Truncation of a vector. -/
theorem k23_trunc_tendsto {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {u : ℕ → E} (hu : Summable u) :
    Tendsto (fun N => ∑' n, (if n < N then u n else 0)) atTop (𝓝 (∑' n, u n)) := by
  have he : ∀ N, (∑' n, (if n < N then u n else 0)) = ∑ n ∈ Finset.range N, u n := by
    intro N
    rw [tsum_eq_sum (s := Finset.range N)]
    · exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn)
    · intro n hn
      rw [if_neg (by simpa using hn)]
  simp only [he]
  exact hu.hasSum.tendsto_sum_nat

/-- The contraction bound for arbitrary `ℓ²` vectors (by truncation). -/
theorem k23_col_le {A A' : ℕ → ℕ → ℂ}
    (hcol : ∀ m n, (∑' k, (conj (A k m) * A k n + conj (A' k m) * A' k n)) = kron m n)
    (hrow : ∀ m, Summable (fun n => ‖A m n‖ ^ 2)) (hrow' : ∀ m, Summable (fun n => ‖A' m n‖ ^ 2))
    {y : ℕ → ℂ} (hy : Summable (fun n => ‖y n‖ ^ 2)) :
    Summable (fun m => ‖∑' n, A m n * y n‖ ^ 2 + ‖∑' n, A' m n * y n‖ ^ 2) ∧
      (∑' m, (‖∑' n, A m n * y n‖ ^ 2 + ‖∑' n, A' m n * y n‖ ^ 2)) ≤ ∑' n, ‖y n‖ ^ 2 := by
  let yN : ℕ → ℕ → ℂ := fun N n => if n < N then y n else 0
  have hyN : ∀ N n, N ≤ n → yN N n = 0 := fun N n h => if_neg (by omega)
  have hfin := fun N => k23_col_finite hcol (hyN N)
  have hyNle : ∀ N, (∑' n, ‖yN N n‖ ^ 2) ≤ ∑' n, ‖y n‖ ^ 2 := by
    intro N
    refine (hy.of_nonneg_of_le (fun _ => by positivity) fun n => ?_).tsum_le_tsum (fun n => ?_) hy
    · simp only [yN]; split_ifs <;> simp
    · simp only [yN]; split_ifs <;> simp
  have hconv : ∀ (B : ℕ → ℕ → ℂ), (∀ m, Summable (fun n => ‖B m n‖ ^ 2)) → ∀ m,
      Tendsto (fun N => ∑' n, B m n * yN N n) atTop (𝓝 (∑' n, B m n * y n)) := by
    intro B hB m
    have h := k23_trunc_tendsto (k23_summable_mul (hB m) hy)
    refine h.congr fun N => ?_
    refine tsum_congr fun n => ?_
    simp only [yN]
    split_ifs <;> simp
  have hF : ∀ s : Finset ℕ, (∑ m ∈ s, (‖∑' n, A m n * y n‖ ^ 2 + ‖∑' n, A' m n * y n‖ ^ 2)) ≤
      ∑' n, ‖y n‖ ^ 2 := by
    intro s
    have hlim : Tendsto (fun N => ∑ m ∈ s, (‖∑' n, A m n * yN N n‖ ^ 2 + ‖∑' n, A' m n * yN N n‖ ^ 2))
        atTop (𝓝 (∑ m ∈ s, (‖∑' n, A m n * y n‖ ^ 2 + ‖∑' n, A' m n * y n‖ ^ 2))) :=
      tendsto_finsetSum _ fun m _ =>
        (((hconv A hrow m).norm).pow 2).add (((hconv A' hrow' m).norm).pow 2)
    refine le_of_tendsto' hlim fun N => ?_
    have h1 := (hfin N).1.sum_le_tsum s (fun _ _ => by positivity)
    rw [(hfin N).2] at h1
    exact h1.trans (hyNle N)
  exact ⟨summable_of_sum_le (fun _ => by positivity) hF,
    Real.tsum_le_of_sum_le (fun _ => by positivity) hF⟩

/-- A square-summable sequence as an element of `ℓ²`. -/
theorem k23_memℓp {u : ℕ → ℂ} (hu : Summable (fun n => ‖u n‖ ^ 2)) : Memℓp u 2 := by
  apply memℓp_gen
  simpa using hu

/-- `‖u‖²_{ℓ²} = Σ |u_n|²`. -/
theorem k23_lp_norm_sq {u : ℕ → ℂ} (hu : Summable (fun n => ‖u n‖ ^ 2)) :
    ‖(⟨u, k23_memℓp hu⟩ : lp (fun _ : ℕ => ℂ) 2)‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  simp only [h2]
  have hs : (∑' n, ‖(⟨u, k23_memℓp hu⟩ : lp (fun _ : ℕ => ℂ) 2) n‖ ^ (2 : ℝ)) = ∑' n, ‖u n‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [Real.rpow_two]
  rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (tsum_nonneg fun _ => by positivity)]
  norm_num

/-- Column isometry: orthonormal columns of the stacked matrix `(A; A')` with rows in `ℓ²` give
`‖Ax‖² + ‖A'x‖² = ‖x‖²` on `ℓ²` (including summability of both row series). -/
theorem k23_col_isometry {A A' : ℕ → ℕ → ℂ}
    (hcol : ∀ m n, (∑' k, (conj (A k m) * A k n + conj (A' k m) * A' k n)) = kron m n)
    (hrow : ∀ m, Summable (fun n => ‖A m n‖ ^ 2)) (hrow' : ∀ m, Summable (fun n => ‖A' m n‖ ^ 2))
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Summable (fun m => ‖∑' n, A m n * x n‖ ^ 2) ∧ Summable (fun m => ‖∑' n, A' m n * x n‖ ^ 2) ∧
      (∑' m, ‖∑' n, A m n * x n‖ ^ 2) + (∑' m, ‖∑' n, A' m n * x n‖ ^ 2) = ∑' n, ‖x n‖ ^ 2 := by
  -- summability of both row series
  have hsum : ∀ {y : ℕ → ℂ}, Summable (fun n => ‖y n‖ ^ 2) →
      Summable (fun m => ‖∑' n, A m n * y n‖ ^ 2) ∧ Summable (fun m => ‖∑' n, A' m n * y n‖ ^ 2) := by
    intro y hy
    have h := (k23_col_le hcol hrow hrow' hy).1
    exact ⟨h.of_nonneg_of_le (fun _ => by positivity) (fun m => by nlinarith [sq_nonneg ‖∑' n, A' m n * y n‖]),
      h.of_nonneg_of_le (fun _ => by positivity) (fun m => by nlinarith [sq_nonneg ‖∑' n, A m n * y n‖])⟩
  obtain ⟨hA, hA'⟩ := hsum hx
  refine ⟨hA, hA', ?_⟩
  let xN : ℕ → ℕ → ℂ := fun N n => if n < N then x n else 0
  have hxN : ∀ N, Summable (fun n => ‖xN N n‖ ^ 2) := fun N =>
    hx.of_nonneg_of_le (fun _ => by positivity) fun n => by simp only [xN]; split_ifs <;> simp
  have hdiff : ∀ N, Summable (fun n => ‖x n - xN N n‖ ^ 2) := fun N =>
    hx.of_nonneg_of_le (fun _ => by positivity) fun n => by simp only [xN]; split_ifs <;> simp
  -- linearity of the row series
  have hlin : ∀ (B : ℕ → ℕ → ℂ), (∀ m, Summable (fun n => ‖B m n‖ ^ 2)) → ∀ N m,
      (∑' n, B m n * x n) - (∑' n, B m n * xN N n) = ∑' n, B m n * (x n - xN N n) := by
    intro B hB N m
    rw [← Summable.tsum_sub (k23_summable_mul (hB m) hx) (k23_summable_mul (hB m) (hxN N))]
    exact tsum_congr fun n => by ring
  -- the tail tends to zero
  have htail : Tendsto (fun N => ∑' n, ‖x n - xN N n‖ ^ 2) atTop (𝓝 0) := by
    have h := k23_trunc_tendsto hx
    have he : ∀ N, (∑' n, ‖x n - xN N n‖ ^ 2) = (∑' n, ‖x n‖ ^ 2) - ∑' n, (if n < N then ‖x n‖ ^ 2 else 0) := by
      intro N
      rw [← Summable.tsum_sub hx (hx.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        fun n => by split_ifs <;> simp)]
      refine tsum_congr fun n => ?_
      simp only [xN]
      split_ifs <;> simp
    simp only [he]
    have h2 := h.const_sub (∑' n, ‖x n‖ ^ 2)
    rw [sub_self] at h2
    exact h2
  -- convergence of the norms in `ℓ²`
  have hnorm : ∀ (B : ℕ → ℕ → ℂ) (hB : ∀ m, Summable (fun n => ‖B m n‖ ^ 2))
      (hBs : ∀ {y : ℕ → ℂ}, Summable (fun n => ‖y n‖ ^ 2) → Summable (fun m => ‖∑' n, B m n * y n‖ ^ 2))
      (hBle : ∀ {y : ℕ → ℂ}, Summable (fun n => ‖y n‖ ^ 2) →
        (∑' m, ‖∑' n, B m n * y n‖ ^ 2) ≤ ∑' n, ‖y n‖ ^ 2),
      Tendsto (fun N => ∑' m, ‖∑' n, B m n * xN N n‖ ^ 2) atTop (𝓝 (∑' m, ‖∑' n, B m n * x n‖ ^ 2)) := by
    intro B hB hBs hBle
    let U : lp (fun _ : ℕ => ℂ) 2 := ⟨fun m => ∑' n, B m n * x n, k23_memℓp (hBs hx)⟩
    let UN : ℕ → lp (fun _ : ℕ => ℂ) 2 := fun N => ⟨fun m => ∑' n, B m n * xN N n, k23_memℓp (hBs (hxN N))⟩
    have hU : ‖U‖ ^ 2 = ∑' m, ‖∑' n, B m n * x n‖ ^ 2 := k23_lp_norm_sq (hBs hx)
    have hUN : ∀ N, ‖UN N‖ ^ 2 = ∑' m, ‖∑' n, B m n * xN N n‖ ^ 2 := fun N => k23_lp_norm_sq (hBs (hxN N))
    have hsub : ∀ N, ‖U - UN N‖ ^ 2 ≤ ∑' n, ‖x n - xN N n‖ ^ 2 := by
      intro N
      have hm : Summable (fun m => ‖∑' n, B m n * (x n - xN N n)‖ ^ 2) := hBs (hdiff N)
      have he : U - UN N = ⟨fun m => ∑' n, B m n * (x n - xN N n), k23_memℓp hm⟩ := by
        ext m
        simp only [U, UN, lp.coeFn_sub, Pi.sub_apply]
        exact hlin B hB N m
      rw [he, k23_lp_norm_sq hm]
      exact hBle (hdiff N)
    have hconv : Tendsto (fun N => ‖U - UN N‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N => Real.sqrt (∑' n, ‖x n - xN N n‖ ^ 2)) atTop (𝓝 0) := by
        have h0' := (Real.continuous_sqrt.tendsto 0).comp htail
        rw [Real.sqrt_zero] at h0'
        exact h0'
      refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) h0
      rw [← Real.sqrt_sq (norm_nonneg (U - UN N))]
      exact Real.sqrt_le_sqrt (hsub N)
    have hUNt : Tendsto UN atTop (𝓝 U) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine hconv.congr fun N => ?_
      rw [norm_sub_rev]
    have h2 := ((continuous_norm.tendsto U).comp hUNt).pow 2
    simp only [Function.comp_def, hUN, hU] at h2
    exact h2
  have hAle : ∀ {y : ℕ → ℂ}, Summable (fun n => ‖y n‖ ^ 2) →
      (∑' m, ‖∑' n, A m n * y n‖ ^ 2) ≤ ∑' n, ‖y n‖ ^ 2 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsum hy
    have h := (k23_col_le hcol hrow hrow' hy).2
    rw [Summable.tsum_add h1 h2] at h
    have h0 : (0 : ℝ) ≤ ∑' m, ‖∑' n, A' m n * y n‖ ^ 2 := tsum_nonneg fun m => sq_nonneg _
    linarith
  have hA'le : ∀ {y : ℕ → ℂ}, Summable (fun n => ‖y n‖ ^ 2) →
      (∑' m, ‖∑' n, A' m n * y n‖ ^ 2) ≤ ∑' n, ‖y n‖ ^ 2 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsum hy
    have h := (k23_col_le hcol hrow hrow' hy).2
    rw [Summable.tsum_add h1 h2] at h
    have h0 : (0 : ℝ) ≤ ∑' m, ‖∑' n, A m n * y n‖ ^ 2 := tsum_nonneg fun m => sq_nonneg _
    linarith
  have hlimA := hnorm A hrow (fun hy => (hsum hy).1) hAle
  have hlimA' := hnorm A' hrow' (fun hy => (hsum hy).2) hA'le
  have hlimx : Tendsto (fun N => ∑' n, ‖xN N n‖ ^ 2) atTop (𝓝 (∑' n, ‖x n‖ ^ 2)) := by
    have h := k23_trunc_tendsto hx
    refine h.congr fun N => tsum_congr fun n => ?_
    simp only [xN]
    split_ifs <;> simp
  have heq : ∀ N, (∑' m, ‖∑' n, A m n * xN N n‖ ^ 2) + (∑' m, ‖∑' n, A' m n * xN N n‖ ^ 2) =
      ∑' n, ‖xN N n‖ ^ 2 := by
    intro N
    obtain ⟨h1, h2⟩ := hsum (hxN N)
    rw [← Summable.tsum_add h1 h2]
    exact (k23_col_finite hcol (N := N) (fun n hn => if_neg (by omega))).2
  exact tendsto_nhds_unique ((hlimA.add hlimA').congr heq) hlimx

/-- `B₂` is bounded below: a bound `‖B₄x‖ ≤ c‖x‖` gives `(1 - c²)‖x‖² ≤ ‖B₂x‖²` (columns of `(B₂; B₄)`). -/
theorem k23_B2_below {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {c : ℝ}
    (hc : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B4 (grunsky (fsans μ) (gsans μ)) m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    (1 - c ^ 2) * ∑' n, ‖x n‖ ^ 2 ≤ ∑' m, ‖∑' n, B2 (grunsky (fsans μ) (gsans μ)) m n * x n‖ ^ 2 := by
  obtain ⟨hpair, hnull, -⟩ := remark_2_2 hμ
  obtain ⟨hsym, h13, h24, -⟩ := grunsky_unitary hpair hnull
  have hrow2 : ∀ m, Summable (fun n => ‖B2 (grunsky (fsans μ) (gsans μ)) m n‖ ^ 2) := by
    intro m
    refine ((k23_col_summable h13 m).2).congr fun n => ?_
    rw [(hsym n m).2.2]
  have hrow4 : ∀ m, Summable (fun n => ‖B4 (grunsky (fsans μ) (gsans μ)) m n‖ ^ 2) := by
    intro m
    refine ((k23_col_summable h24 m).2).congr fun n => ?_
    rw [(hsym n m).2.1]
  have hiso := (k23_col_isometry h24 hrow2 hrow4 hx).2.2
  have h4 := hc x hx
  nlinarith

/-- `B₃` is bounded below: a bound `‖B₁x‖ ≤ c‖x‖` gives `(1 - c²)‖x‖² ≤ ‖B₃x‖²` (columns of `(B₁; B₃)`). -/
theorem k23_B3_below {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {c : ℝ}
    (hc : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 (grunsky (fsans μ) (gsans μ)) m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    (1 - c ^ 2) * ∑' n, ‖x n‖ ^ 2 ≤ ∑' m, ‖∑' n, B3 (grunsky (fsans μ) (gsans μ)) m n * x n‖ ^ 2 := by
  obtain ⟨hpair, hnull, -⟩ := remark_2_2 hμ
  obtain ⟨hsym, h13, h24, -⟩ := grunsky_unitary hpair hnull
  have hrow1 : ∀ m, Summable (fun n => ‖B1 (grunsky (fsans μ) (gsans μ)) m n‖ ^ 2) := by
    intro m
    refine ((k23_col_summable h13 m).1).congr fun n => ?_
    rw [(hsym n m).1]
  have hrow3 : ∀ m, Summable (fun n => ‖B3 (grunsky (fsans μ) (gsans μ)) m n‖ ^ 2) := by
    intro m
    refine ((k23_col_summable h24 m).1).congr fun n => ?_
    rw [(hsym m n).2.2]
  have hiso := (k23_col_isometry h13 hrow1 hrow3 hx).2.2
  have h1 := hc x hx
  nlinarith

/-- **Remark 2.3** (TT:3896). For the welding pair of `[μ] ∈ T(1)`:
- `I - B₁B₁*` and `I - B₄B₄*` are positive definite, so `‖B₁‖, ‖B₄‖ < 1` (Grunsky's inequality, strict);
- `B₂`, `B₃` are topological isomorphisms of `ℓ²` (bounded below).

Stated: there is `0 ≤ c < 1` with `‖B₁x‖, ‖B₄x‖ ≤ c‖x‖`, and `C` with `‖x‖ ≤ C‖B₂x‖`, `‖x‖ ≤ C‖B₃x‖`, for `x ∈ ℓ²`. -/
theorem k23_remark_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    let b := grunsky (fsans μ) (gsans μ)
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∃ C, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 ∧
      ∑' m, ‖∑' n, B4 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 ∧
      ∑' n, ‖x n‖ ^ 2 ≤ C * ∑' m, ‖∑' n, B2 b m n * x n‖ ^ 2 ∧
      ∑' n, ‖x n‖ ^ 2 ≤ C * ∑' m, ‖∑' n, B3 b m n * x n‖ ^ 2 := by
  intro b
  obtain ⟨c₁, hc₁0, hc₁1, h₁⟩ := k23_B1_bound hμ
  obtain ⟨c₄, hc₄0, hc₄1, h₄⟩ := k23_B4_bound hμ
  set c := max c₁ c₄ with hc
  have hc0 : 0 ≤ c := le_max_of_le_left hc₁0
  have hc1 : c < 1 := max_lt hc₁1 hc₄1
  have hpos : 0 < 1 - c ^ 2 := by nlinarith
  have hsq₁ : c₁ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hc₁0 (le_max_left _ _) 2
  have hsq₄ : c₄ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hc₄0 (le_max_right _ _) 2
  have hB1 : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 := fun x hx =>
    (h₁ x hx).trans (mul_le_mul_of_nonneg_right hsq₁ (tsum_nonneg fun _ => by positivity))
  have hB4 : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B4 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 := fun x hx =>
    (h₄ x hx).trans (mul_le_mul_of_nonneg_right hsq₄ (tsum_nonneg fun _ => by positivity))
  refine ⟨c, hc0, hc1, 1 / (1 - c ^ 2), fun x hx => ⟨hB1 x hx, hB4 x hx, ?_, ?_⟩⟩
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos, mul_comm]
    exact k23_B2_below hμ hB4 hx
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos, mul_comm]
    exact k23_B3_below hμ hB1 hx

/-- **Remark 2.3** (TT:3896). For the welding pair of `[μ] ∈ T(1)`:
- `I - B₁B₁*` and `I - B₄B₄*` are positive definite, so `‖B₁‖, ‖B₄‖ < 1` (Grunsky's inequality, strict);
- `B₂`, `B₃` are topological isomorphisms of `ℓ²` (bounded below).

Stated: there is `0 ≤ c < 1` with `‖B₁x‖, ‖B₄x‖ ≤ c‖x‖`, and `C` with `‖x‖ ≤ C‖B₂x‖`, `‖x‖ ≤ C‖B₃x‖`, for `x ∈ ℓ²`. -/
theorem remark_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    let b := grunsky (fsans μ) (gsans μ)
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∃ C, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∑' m, ‖∑' n, B1 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 ∧
      ∑' m, ‖∑' n, B4 b m n * x n‖ ^ 2 ≤ c ^ 2 * ∑' n, ‖x n‖ ^ 2 ∧
      ∑' n, ‖x n‖ ^ 2 ≤ C * ∑' m, ‖∑' n, B2 b m n * x n‖ ^ 2 ∧
      ∑' n, ‖x n‖ ^ 2 ≤ C * ∑' m, ‖∑' n, B3 b m n * x n‖ ^ 2 :=
  k23_remark_2_3 hμ

end Ch2
end TakhtajanTeo
