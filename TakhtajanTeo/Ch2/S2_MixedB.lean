import TakhtajanTeo.Ch2.S2_Mixed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-! ## `eq_2_2`: row identities from the Grunsky equality -/

/-- Symmetry `b_{kl} = b_{lk}` for nonzero indices of every sign. -/
theorem mg_gsym {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) (k l : ℤ) (hk : k ≠ 0) (hl : l ≠ 0) :
    grunsky f g k l = grunsky f g l k := by
  have hspec := grunsky_spec h
  have hc : ∀ k : ℤ, k ≠ 0 → ∃ j : ℕ, k = (j : ℤ) + 1 ∨ k = -((j : ℤ) + 1) := by
    intro k hk
    rcases lt_or_gt_of_ne hk with hl | hl
    · exact ⟨(-k - 1).toNat, Or.inr (by omega)⟩
    · exact ⟨(k - 1).toNat, Or.inl (by omega)⟩
  obtain ⟨j, hj⟩ := hc k hk
  obtain ⟨j', hj'⟩ := hc l hl
  rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact (hspec.2 j j').1
  · have h1 := hspec.1.2.2.2.2 (j' + 1) j
    push_cast at h1
    exact h1.symm
  · have h1 := hspec.1.2.2.2.2 (j + 1) j'
    push_cast at h1
    exact h1
  · have h1 := (hspec.2 (j + 1) (j' + 1)).2
    push_cast at h1
    exact h1

/-- Splitting a `ℤ`-indexed sum with vanishing `0`-term into its positive and negative parts. -/
theorem mg_int_split {G : ℤ → ℂ} {a : ℂ} (hG : HasSum G a) (h0 : G 0 = 0) :
    ((∑' j : ℕ, G ((j : ℤ) + 1)) + ∑' j : ℕ, G (-((j : ℤ) + 1))) = a ∧
      Summable (fun j : ℕ => G ((j : ℤ) + 1)) ∧ Summable (fun j : ℕ => G (-((j : ℤ) + 1))) := by
  have hs := hG.summable
  have h1 : Summable (fun n : ℕ => G (n : ℤ)) := hs.comp_injective Nat.cast_injective
  have h2 : Summable (fun n : ℕ => G (-((n : ℤ) + 1))) :=
    hs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) (fun x y hxy => by
      simp only [neg_inj, add_left_inj] at hxy
      exact_mod_cast hxy)
  have h3 : Summable (fun j : ℕ => G ((j : ℤ) + 1)) :=
    hs.comp_injective (i := fun j : ℕ => (j : ℤ) + 1) (fun x y hxy => by
      simp only [add_left_inj] at hxy
      exact_mod_cast hxy)
  refine ⟨?_, h3, h2⟩
  have h4 := h1.tsum_eq_zero_add
  simp only [Nat.cast_zero, h0, zero_add, Nat.cast_add, Nat.cast_one] at h4
  rw [← hG.tsum_eq, tsum_of_nat_of_neg_add_one h1 h2, h4]

/-- The row sums of the Grunsky equality. `R l₀ k = √|l₀ k| b_{l₀ k}`. -/
theorem mg_row_hasSum {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0)
    {R : ℤ → ℤ → ℂ} (hR : ∀ l0 k, R l0 k = (Real.sqrt |((l0 : ℝ) * k)| : ℂ) * grunsky f g l0 k)
    (l0 l0' : ℤ) (h0 : l0 ≠ 0) (h0' : l0' ≠ 0) :
    HasSum (fun k : ℤ => if k = 0 then 0 else R l0 k * conj (R l0' k)) (if l0 = l0' then 1 else 0) := by
  set M : ℕ := l0.natAbs ⊔ l0'.natAbs with hM
  have hJ : ∀ l : ℤ, l ≠ 0 → l.natAbs ≤ M → l ∈ (Finset.Icc (-(M : ℤ)) M).erase 0 := by
    intro l hl hlM
    simp only [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨hl, ?_, ?_⟩ <;> omega
  have hJ0 : l0 ∈ (Finset.Icc (-(M : ℤ)) M).erase 0 := hJ l0 h0 (le_sup_left)
  have hJ0' : l0' ∈ (Finset.Icc (-(M : ℤ)) M).erase 0 := hJ l0' h0' (le_sup_right)
  have key := mg_eq_2_1_hasSum h hF M (fun l => if l = l0 then (1 : ℂ) else 0)
    (fun l => if l = l0' then (1 : ℂ) else 0)
  have hrhs : (∑ k ∈ (Finset.Icc (-(M : ℤ)) M).erase 0,
      (fun l => if l = l0 then (1 : ℂ) else 0) k * conj ((fun l => if l = l0' then (1 : ℂ) else 0) k)) =
      if l0 = l0' then 1 else 0 := by
    rw [Finset.sum_eq_single l0 (fun k _ hk => by simp [hk]) (fun hh => absurd hJ0 hh)]
    by_cases hh : l0 = l0' <;> simp [hh]
  rw [hrhs] at key
  have hfun : (fun k : ℤ => if k = 0 then (0 : ℂ) else R l0 k * conj (R l0' k)) =
      (fun k : ℤ => if k = 0 then 0 else
        ∑ l ∈ (Finset.Icc (-(M : ℤ)) M).erase 0, ∑ l' ∈ (Finset.Icc (-(M : ℤ)) M).erase 0,
          (Real.sqrt |(k * l : ℝ)| : ℂ) * grunsky f g k l * Real.sqrt |(k * l' : ℝ)| *
            conj (grunsky f g k l') *
            (fun l => if l = l0 then (1 : ℂ) else 0) l *
            conj ((fun l => if l = l0' then (1 : ℂ) else 0) l')) := by
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
      rw [Finset.sum_eq_single l0 (fun l _ hl => Finset.sum_eq_zero (fun l' _ => by simp [hl]))
        (fun hh => absurd hJ0 hh)]
      rw [Finset.sum_eq_single l0' (fun l' _ hl' => by simp [hl']) (fun hh => absurd hJ0' hh)]
      have e1 : (k : ℝ) * l0 = l0 * k := mul_comm _ _
      have e2 : (k : ℝ) * l0' = l0' * k := mul_comm _ _
      simp only [hR, e1, e2, mg_gsym h k l0 hk h0, mg_gsym h k l0' hk h0', if_true, map_one, mul_one,
        map_mul, Complex.conj_ofReal]
      ring
  rw [hfun]
  exact key

/-- Row identity: the positive and negative parts of the row sum add up to `δ`. -/
theorem mg_row_identity {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0)
    {R : ℤ → ℤ → ℂ} (hR : ∀ l0 k, R l0 k = (Real.sqrt |((l0 : ℝ) * k)| : ℂ) * grunsky f g l0 k)
    (l0 l0' : ℤ) (h0 : l0 ≠ 0) (h0' : l0' ≠ 0) :
    ((∑' j : ℕ, R l0 ((j : ℤ) + 1) * conj (R l0' ((j : ℤ) + 1))) +
        ∑' j : ℕ, R l0 (-((j : ℤ) + 1)) * conj (R l0' (-((j : ℤ) + 1)))) =
      if l0 = l0' then 1 else 0 := by
  have hs := mg_int_split (mg_row_hasSum h hF hR l0 l0' h0 h0') (by simp)
  have e1 : ∀ j : ℕ, ((j : ℤ) + 1 ≠ 0) := fun j => by omega
  have e2 : ∀ j : ℕ, (-((j : ℤ) + 1) ≠ 0) := fun j => by omega
  simpa only [if_neg (e1 _), if_neg (e2 _)] using hs.1

/-- Square summability of the rows. -/
theorem mg_row_summable {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0)
    {R : ℤ → ℤ → ℂ} (hR : ∀ l0 k, R l0 k = (Real.sqrt |((l0 : ℝ) * k)| : ℂ) * grunsky f g l0 k)
    (l0 : ℤ) (h0 : l0 ≠ 0) :
    Summable (fun j : ℕ => ‖R l0 ((j : ℤ) + 1)‖ ^ 2) ∧ Summable (fun j : ℕ => ‖R l0 (-((j : ℤ) + 1))‖ ^ 2) := by
  have hs := mg_int_split (mg_row_hasSum h hF hR l0 l0 h0 h0) (by simp)
  have e1 : ∀ j : ℕ, ((j : ℤ) + 1 ≠ 0) := fun j => by omega
  have e2 : ∀ j : ℕ, (-((j : ℤ) + 1) ≠ 0) := fun j => by omega
  have e : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.sq_norm]
  refine ⟨?_, ?_⟩
  · have := hs.2.1
    simp only [if_neg (e1 _), e] at this
    exact Complex.summable_ofReal.mp this
  · have := hs.2.2
    simp only [if_neg (e2 _), e] at this
    exact Complex.summable_ofReal.mp this

/-- The product of two square-summable sequences is summable. -/
theorem mg_sq_mul_summable {u v : ℕ → ℂ} (hu : Summable (fun n => ‖u n‖ ^ 2))
    (hv : Summable (fun n => ‖v n‖ ^ 2)) : Summable (fun n => u n * v n) := by
  refine Summable.of_norm_bounded ((hu.add hv).div_const 2) (fun n => ?_)
  rw [norm_mul]
  show ‖u n‖ * ‖v n‖ ≤ (‖u n‖ ^ 2 + ‖v n‖ ^ 2) / 2
  nlinarith [sq_nonneg (‖u n‖ - ‖v n‖)]

/-- A pair of row-square-summable matrices with `A A* + C C* = I` has `‖A‖ ≤ 1`. -/
theorem mg_row_bound {A C : ℕ → ℕ → ℂ} (hA : ∀ m, Summable (fun n => ‖A m n‖ ^ 2))
    (hC : ∀ m, Summable (fun n => ‖C m n‖ ^ 2))
    (hI : ∀ m n, (∑' k, A m k * conj (A n k)) + (∑' k, C m k * conj (C n k)) = if m = n then 1 else 0)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    ∑' m, ‖∑' n, A m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 := by
  have hnc : ∀ z : ℂ, ‖conj z‖ = ‖z‖ := fun z => Complex.norm_conj z
  have hmc : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.sq_norm]
  have hAc : ∀ m, Summable (fun n => ‖conj (A m n)‖ ^ 2) := fun m => by
    simpa only [hnc] using hA m
  have hCc : ∀ m, Summable (fun n => ‖conj (C m n)‖ ^ 2) := fun m => by
    simpa only [hnc] using hC m
  refine Real.tsum_le_of_sum_range_le (fun m => by positivity) (fun M => ?_)
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℂ, ∀ m, y m = ∑' n, A m n * x n := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ m, c m = conj (y m) := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℂ, ∀ n, w n = ∑ m ∈ Finset.range M, c m * A m n := ⟨_, fun _ => rfl⟩
  obtain ⟨wC, hwC⟩ : ∃ wC : ℕ → ℂ, ∀ n, wC n = ∑ m ∈ Finset.range M, c m * C m n := ⟨_, fun _ => rfl⟩
  have hyy : ∀ m, ∑' n, A m n * x n = y m := fun m => (hy m).symm
  simp only [hyy]
  -- (1) the pairing `∑ x w = ∑ ‖y‖²`
  have hcy : ∀ m, c m * y m = ((‖y m‖ ^ 2 : ℝ) : ℂ) := fun m => by
    rw [hc, mul_comm, hmc]
  have h1 : HasSum (fun n => w n * x n) (((∑ m ∈ Finset.range M, ‖y m‖ ^ 2 : ℝ)) : ℂ) := by
    have := hasSum_sum (s := Finset.range M) (f := fun m n => c m * (A m n * x n))
      (a := fun m => c m * y m)
      (fun m _ => by
        have h' := (mg_sq_mul_summable (hA m) hx).hasSum.mul_left (c m)
        rw [← hy m] at h'
        exact h')
    have hfun : (fun n => ∑ m ∈ Finset.range M, c m * (A m n * x n)) = fun n => w n * x n := by
      funext n
      rw [hw n, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hfun] at this
    convert this using 1
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun m _ => (hcy m).symm)
  -- (2) the Gram identity
  have h2 : ∀ (B : ℕ → ℕ → ℂ), (∀ m, Summable (fun n => ‖B m n‖ ^ 2)) →
      (∀ m, Summable (fun n => ‖conj (B m n)‖ ^ 2)) → ∀ v : ℕ → ℂ,
      (∀ n, v n = ∑ m ∈ Finset.range M, c m * B m n) →
      HasSum (fun n => v n * conj (v n))
        (∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, B m k * conj (B m' k)) := by
    intro B hB hBc v hv
    have hterm : ∀ m m', HasSum (fun n => c m * conj (c m') * (B m n * conj (B m' n)))
        (c m * conj (c m') * ∑' k, B m k * conj (B m' k)) := fun m m' =>
      (mg_sq_mul_summable (hB m) (hBc m')).hasSum.mul_left _
    have := hasSum_sum (s := Finset.range M)
      (f := fun m n => ∑ m' ∈ Finset.range M, c m * conj (c m') * (B m n * conj (B m' n)))
      (a := fun m => ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, B m k * conj (B m' k))
      (fun m _ => hasSum_sum (fun m' _ => hterm m m'))
    have hfun : (fun n => v n * conj (v n)) = fun n => ∑ m ∈ Finset.range M,
        ∑ m' ∈ Finset.range M, c m * conj (c m') * (B m n * conj (B m' n)) := by
      funext n
      rw [hv n, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
      rw [map_mul]
      ring
    rw [hfun]
    exact this
  have hVA := h2 A hA hAc w hw
  have hVC := h2 C hC hCc wC hwC
  have hV : (∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, A m k * conj (A m' k)) +
      (∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, C m k * conj (C m' k)) =
      (((∑ m ∈ Finset.range M, ‖y m‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [← Finset.sum_add_distrib]
    have : ∀ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, A m k * conj (A m' k) +
        c m * conj (c m') * ∑' k, C m k * conj (C m' k) =
        if m = m' then c m * conj (c m) else 0 := by
      intro m' _
      rw [← mul_add, hI m m']
      by_cases h : m = m'
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hm, hmc (c m), hc m, hnc]
  have hre : ∀ z : ℂ, (z * conj z).re = ‖z‖ ^ 2 := fun z => by rw [hmc]; exact Complex.ofReal_re _
  generalize (∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, A m k * conj (A m' k)) = VA
    at hVA hV
  generalize (∑ m ∈ Finset.range M, ∑ m' ∈ Finset.range M, c m * conj (c m') * ∑' k, C m k * conj (C m' k)) = VC
    at hVC hV
  generalize hSdef : (∑ m ∈ Finset.range M, ‖y m‖ ^ 2 : ℝ) = S at h1 hV ⊢
  have hWA : HasSum (fun n => ‖w n‖ ^ 2) VA.re := by
    have := Complex.reCLM.hasSum hVA
    simpa only [Complex.reCLM_apply, hre] using this
  have hWC : HasSum (fun n => ‖wC n‖ ^ 2) VC.re := by
    have := Complex.reCLM.hasSum hVC
    simpa only [Complex.reCLM_apply, hre] using this
  have hWsum : VA.re + VC.re = S := by
    have := congrArg Complex.re hV
    simpa using this
  have hWCnn : 0 ≤ VC.re := hWC.nonneg (fun n => by positivity)
  have hxw : HasSum (fun n => (w n * x n).re) S := by
    have := Complex.reCLM.hasSum h1
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using this
  have hp : ∀ n, ‖x n - conj (w n)‖ ^ 2 = ‖x n‖ ^ 2 + ‖w n‖ ^ 2 - 2 * (w n * x n).re := fun n => by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, Complex.mul_re]
    ring
  have hH := (hx.hasSum.add hWA).sub (hxw.mul_left 2)
  have hfun : (fun n => ‖x n - conj (w n)‖ ^ 2) = fun n => ‖x n‖ ^ 2 + ‖w n‖ ^ 2 - 2 * (w n * x n).re :=
    funext hp
  have hnn : 0 ≤ (∑' n, ‖x n‖ ^ 2) + VA.re - 2 * S := by
    have h5 : HasSum (fun n => ‖x n - conj (w n)‖ ^ 2) ((∑' n, ‖x n‖ ^ 2) + VA.re - 2 * S) := by
      rw [hfun]; exact hH
    exact h5.nonneg (fun n => by positivity)
  linarith

/-- (M5) Core of `eq_2_2`, stated for matrices given by the formulas of `B1 … B4`
(so that `eq_2_2` follows by `fun m n => rfl`). -/
theorem mg_eq_2_2_core {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {B1 B2 B3 B4 : ℕ → ℕ → ℂ}
    (e1 : ∀ m n : ℕ, B1 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (-(m + 1 : ℤ)) (-(n + 1 : ℤ)))
    (e2 : ∀ m n : ℕ, B2 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (-(m + 1 : ℤ)) (n + 1))
    (e3 : ∀ m n : ℕ, B3 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (m + 1) (-(n + 1 : ℤ)))
    (e4 : ∀ m n : ℕ, B4 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (m + 1) (n + 1)) :
    (∀ m n : ℕ, (∑' k, B1 m k * conj (B1 n k)) + (∑' k, B2 m k * conj (B2 n k)) = if m = n then 1 else 0) ∧
      (∀ m n : ℕ, (∑' k, B3 m k * conj (B1 n k)) + (∑' k, B4 m k * conj (B2 n k)) = 0) ∧
      (∀ m n : ℕ, (∑' k, B1 m k * conj (B3 n k)) + (∑' k, B2 m k * conj (B4 n k)) = 0) ∧
      (∀ m n : ℕ, (∑' k, B3 m k * conj (B3 n k)) + (∑' k, B4 m k * conj (B4 n k)) = if m = n then 1 else 0) ∧
      (∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
        ∑' m, ‖∑' n, B1 m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 ∧
        ∑' m, ‖∑' n, B2 m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 ∧
        ∑' m, ‖∑' n, B3 m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 ∧
        ∑' m, ‖∑' n, B4 m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2) ∧
      (∀ m : ℕ, Summable (fun j : ℕ => ‖B1 m j‖ ^ 2)) ∧ (∀ m : ℕ, Summable (fun j : ℕ => ‖B2 m j‖ ^ 2)) ∧
      (∀ m : ℕ, Summable (fun j : ℕ => ‖B3 m j‖ ^ 2)) ∧ (∀ m : ℕ, Summable (fun j : ℕ => ‖B4 m j‖ ^ 2)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℤ → ℤ → ℂ, ∀ l0 k,
      R l0 k = (Real.sqrt |((l0 : ℝ) * k)| : ℂ) * grunsky f g l0 k := ⟨_, fun _ _ => rfl⟩
  have habs : ∀ (a : ℕ) (s : ℤ), (s = (a : ℤ) + 1 ∨ s = -((a : ℤ) + 1)) → |(s : ℝ)| = (a : ℝ) + 1 := by
    intro a s hs
    rcases hs with rfl | rfl
    · push_cast; exact abs_of_nonneg (by positivity)
    · push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
  have hrel : ∀ (m j : ℕ) (s t : ℤ), (s = (m : ℤ) + 1 ∨ s = -((m : ℤ) + 1)) →
      (t = (j : ℤ) + 1 ∨ t = -((j : ℤ) + 1)) →
      (Real.sqrt ((m + 1) * (j + 1) : ℝ) : ℂ) * grunsky f g s t = R s t := by
    intro m j s t hs ht
    rw [hR, abs_mul, habs m s hs, habs j t ht]
  have hB1 : ∀ m j : ℕ, B1 m j = R (-((m : ℤ) + 1)) (-((j : ℤ) + 1)) := fun m j => by
    rw [e1]; exact hrel m j _ _ (Or.inr rfl) (Or.inr rfl)
  have hB2 : ∀ m j : ℕ, B2 m j = R (-((m : ℤ) + 1)) ((j : ℤ) + 1) := fun m j => by
    rw [e2]; exact hrel m j _ _ (Or.inr rfl) (Or.inl rfl)
  have hB3 : ∀ m j : ℕ, B3 m j = R ((m : ℤ) + 1) (-((j : ℤ) + 1)) := fun m j => by
    rw [e3]; exact hrel m j _ _ (Or.inl rfl) (Or.inr rfl)
  have hB4 : ∀ m j : ℕ, B4 m j = R ((m : ℤ) + 1) ((j : ℤ) + 1) := fun m j => by
    rw [e4]; exact hrel m j _ _ (Or.inl rfl) (Or.inl rfl)
  have hp : ∀ m : ℕ, ((m : ℤ) + 1 ≠ 0) := fun m => by omega
  have hn : ∀ m : ℕ, (-((m : ℤ) + 1) ≠ 0) := fun m => by omega
  have hkp : ∀ m n : ℕ, ((m : ℤ) + 1 = (n : ℤ) + 1) ↔ m = n := fun m n => by omega
  have hkn : ∀ m n : ℕ, (-((m : ℤ) + 1) = -((n : ℤ) + 1)) ↔ m = n := fun m n => by omega
  have hpn : ∀ m n : ℕ, ¬ ((m : ℤ) + 1 = -((n : ℤ) + 1)) := fun m n => by omega
  have hnp : ∀ m n : ℕ, ¬ (-((m : ℤ) + 1) = (n : ℤ) + 1) := fun m n => by omega
  -- the four identities
  have id1 : ∀ m n : ℕ, (∑' k, B1 m k * conj (B1 n k)) + (∑' k, B2 m k * conj (B2 n k)) =
      if m = n then 1 else 0 := by
    intro m n
    have key := mg_row_identity h hF hR (-((m : ℤ) + 1)) (-((n : ℤ) + 1)) (hn m) (hn n)
    simp only [hB1, hB2]
    rw [add_comm, key]
    simp only [hkn]
  have id2 : ∀ m n : ℕ, (∑' k, B3 m k * conj (B1 n k)) + (∑' k, B4 m k * conj (B2 n k)) = 0 := by
    intro m n
    have key := mg_row_identity h hF hR ((m : ℤ) + 1) (-((n : ℤ) + 1)) (hp m) (hn n)
    simp only [hB1, hB2, hB3, hB4]
    rw [add_comm, key, if_neg (hpn m n)]
  have id3 : ∀ m n : ℕ, (∑' k, B1 m k * conj (B3 n k)) + (∑' k, B2 m k * conj (B4 n k)) = 0 := by
    intro m n
    have key := mg_row_identity h hF hR (-((m : ℤ) + 1)) ((n : ℤ) + 1) (hn m) (hp n)
    simp only [hB1, hB2, hB3, hB4]
    rw [add_comm, key, if_neg (hnp m n)]
  have id4 : ∀ m n : ℕ, (∑' k, B3 m k * conj (B3 n k)) + (∑' k, B4 m k * conj (B4 n k)) =
      if m = n then 1 else 0 := by
    intro m n
    have key := mg_row_identity h hF hR ((m : ℤ) + 1) ((n : ℤ) + 1) (hp m) (hp n)
    simp only [hB3, hB4]
    rw [add_comm, key]
    simp only [hkp]
  -- rows are square summable
  have hA1 : ∀ m : ℕ, Summable (fun j : ℕ => ‖B1 m j‖ ^ 2) := fun m => by
    simpa only [hB1] using (mg_row_summable h hF hR (-((m : ℤ) + 1)) (hn m)).2
  have hA2 : ∀ m : ℕ, Summable (fun j : ℕ => ‖B2 m j‖ ^ 2) := fun m => by
    simpa only [hB2] using (mg_row_summable h hF hR (-((m : ℤ) + 1)) (hn m)).1
  have hA3 : ∀ m : ℕ, Summable (fun j : ℕ => ‖B3 m j‖ ^ 2) := fun m => by
    simpa only [hB3] using (mg_row_summable h hF hR ((m : ℤ) + 1) (hp m)).2
  have hA4 : ∀ m : ℕ, Summable (fun j : ℕ => ‖B4 m j‖ ^ 2) := fun m => by
    simpa only [hB4] using (mg_row_summable h hF hR ((m : ℤ) + 1) (hp m)).1
  refine ⟨id1, id2, id3, id4, fun x hx => ⟨?_, ?_, ?_, ?_⟩, hA1, hA2, hA3, hA4⟩
  · exact mg_row_bound hA1 hA2 id1 hx
  · exact mg_row_bound hA2 hA1 (fun m n => by rw [add_comm]; exact id1 m n) hx
  · exact mg_row_bound hA3 hA4 id4 hx
  · exact mg_row_bound hA4 hA3 (fun m n => by rw [add_comm]; exact id4 m n) hx

/-- (M6) Core of `grunsky_unitary` (formulas of `B1 … B4` as hypotheses). -/
theorem mg_unitary_core {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) {B1 B2 B3 B4 : ℕ → ℕ → ℂ}
    (e1 : ∀ m n : ℕ, B1 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (-(m + 1 : ℤ)) (-(n + 1 : ℤ)))
    (e2 : ∀ m n : ℕ, B2 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (-(m + 1 : ℤ)) (n + 1))
    (e3 : ∀ m n : ℕ, B3 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (m + 1) (-(n + 1 : ℤ)))
    (e4 : ∀ m n : ℕ, B4 m n = (Real.sqrt ((m + 1) * (n + 1) : ℝ) : ℂ) * grunsky f g (m + 1) (n + 1)) :
    (∀ m n : ℕ, B1 m n = B1 n m ∧ B4 m n = B4 n m ∧ B3 m n = B2 n m) ∧
      (∀ m n : ℕ, (∑' k, (conj (B1 k m) * B1 k n + conj (B3 k m) * B3 k n)) = if m = n then 1 else 0) ∧
      (∀ m n : ℕ, (∑' k, (conj (B2 k m) * B2 k n + conj (B4 k m) * B4 k n)) = if m = n then 1 else 0) ∧
      ∀ m n : ℕ, (∑' k, (conj (B1 k m) * B2 k n + conj (B3 k m) * B4 k n)) = 0 := by
  obtain ⟨id1, id2, id3, id4, -, hA1, hA2, hA3, hA4⟩ := mg_eq_2_2_core h hF e1 e2 e3 e4
  have hn : ∀ m : ℕ, (-((m : ℤ) + 1) ≠ 0) := fun m => by omega
  have hp : ∀ m : ℕ, ((m : ℤ) + 1 ≠ 0) := fun m => by omega
  have hs1 : ∀ m n : ℕ, B1 m n = B1 n m := fun m n => by
    rw [e1, e1, mg_gsym h (-((m : ℤ) + 1)) (-((n : ℤ) + 1)) (hn m) (hn n), mul_comm ((m : ℝ) + 1) ((n : ℝ) + 1)]
  have hs4 : ∀ m n : ℕ, B4 m n = B4 n m := fun m n => by
    rw [e4, e4, mg_gsym h ((m : ℤ) + 1) ((n : ℤ) + 1) (hp m) (hp n), mul_comm ((m : ℝ) + 1) ((n : ℝ) + 1)]
  have hs32 : ∀ m n : ℕ, B3 m n = B2 n m := fun m n => by
    rw [e3, e2, mg_gsym h ((m : ℤ) + 1) (-((n : ℤ) + 1)) (hp m) (hn n), mul_comm ((m : ℝ) + 1) ((n : ℝ) + 1)]
  have hconj : ∀ A : ℕ → ℕ → ℂ, (∀ m, Summable (fun j : ℕ => ‖A m j‖ ^ 2)) →
      ∀ m, Summable (fun j : ℕ => ‖conj (A m j)‖ ^ 2) := fun A hA m => by
    simpa only [Complex.norm_conj] using hA m
  have hprod : ∀ A C : ℕ → ℕ → ℂ, (∀ m, Summable (fun j : ℕ => ‖A m j‖ ^ 2)) →
      (∀ m, Summable (fun j : ℕ => ‖C m j‖ ^ 2)) → ∀ m n : ℕ,
      Summable (fun k => A n k * conj (C m k)) := fun A C hA hC m n =>
    mg_sq_mul_summable (hA n) (hconj C hC m)
  have hk : ∀ m n : ℕ, (if n = m then (1 : ℂ) else 0) = if m = n then 1 else 0 := fun m n => by
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [hmn, Ne.symm hmn]
  refine ⟨fun m n => ⟨hs1 m n, hs4 m n, hs32 m n⟩, fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · have hfun : ∀ k, conj (B1 k m) * B1 k n + conj (B3 k m) * B3 k n =
        B1 n k * conj (B1 m k) + B2 n k * conj (B2 m k) := fun k => by
      rw [hs1 k m, hs1 k n, hs32 k m, hs32 k n]; ring
    rw [tsum_congr hfun, Summable.tsum_add (hprod B1 B1 hA1 hA1 m n) (hprod B2 B2 hA2 hA2 m n),
      id1 n m, hk]
  · have hfun : ∀ k, conj (B2 k m) * B2 k n + conj (B4 k m) * B4 k n =
        B3 n k * conj (B3 m k) + B4 n k * conj (B4 m k) := fun k => by
      rw [← hs32 m k, ← hs32 n k, hs4 k m, hs4 k n]; ring
    rw [tsum_congr hfun, Summable.tsum_add (hprod B3 B3 hA3 hA3 m n) (hprod B4 B4 hA4 hA4 m n),
      id4 n m, hk]
  · have hfun : ∀ k, conj (B1 k m) * B2 k n + conj (B3 k m) * B4 k n =
        B3 n k * conj (B1 m k) + B4 n k * conj (B2 m k) := fun k => by
      rw [hs1 k m, ← hs32 n k, hs32 k m, hs4 k n]; ring
    rw [tsum_congr hfun, Summable.tsum_add (hprod B3 B1 hA3 hA1 m n) (hprod B4 B2 hA4 hA2 m n),
      id2 n m]

end Ch2

end TakhtajanTeo
