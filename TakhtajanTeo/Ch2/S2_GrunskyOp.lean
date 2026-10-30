import TakhtajanTeo.Ch2.S2_MixedHook

/-!
# Matrices as operators on `ℓ²` (host `Ch2/S2_GrunskyOp.lean`, prefix `gop_`)

Shared by `Ch2/S2_DetF` (`detF_spec`, `eq_2_13`) and `Ch2/S2_Eq212` (`eq_2_12`).
- `gopOp A`: the operator `x ↦ (m ↦ Σ_n A m n x n)`. It is defined when the rows of `A` are in `ℓ²` and the partial
  Bessel sums are uniformly bounded (junk `0` otherwise). It is the only new definition (leader-approved).
- API: `gop_apply`, `gop_adjoint_apply`, `gop_transposeOp_apply`, `gop_symm` (symmetric matrix ⇒ `T = Tᵗ`).
- Grunsky blocks: `gop_grunsky_bounds`, `gop_blocks` (`eq_2_2` and `grunsky_unitary` as operator identities, plus the
  symmetries `B₁ᵗ = B₁`, `B₄ᵗ = B₄`, `B₃ = B₂ᵗ`).
- `gop_singular_basis` / `gop_basis_singular`: `IsSingularSeq A λ` ⇔ a Hilbert basis of eigenvectors of `T T*`.
- `gop_compact_of_HS`: a Hilbert–Schmidt matrix gives a compact operator (for `lemma_2_12`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real InnerProductSpace
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-! ### `ℓ²` basics -/

theorem gop_l2_summable (x : ell2) : Summable fun n => ‖x n‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem gop_norm_sq (x : ell2) : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem gop_mem_of_summable {y : ℕ → ℂ} (hy : Summable fun n => ‖y n‖ ^ 2) : Memℓp y 2 :=
  memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hy)

theorem gop_inner_apply (a b : ℂ) : inner ℂ a b = conj a * b := by
  rw [RCLike.inner_apply, mul_comm]

theorem gop_inner_single_left (n : ℕ) (y : ell2) : inner ℂ (lp.single 2 n 1 : ell2) y = y n := by
  rw [lp.inner_single_left, gop_inner_apply, map_one, one_mul]

theorem gop_single_apply (n m : ℕ) : (lp.single 2 n 1 : ell2) m = if m = n then 1 else 0 := by
  rw [lp.single_apply, Pi.single_apply]

/-- Every operator on `ℓ²` acts by its matrix `S e_k`. -/
theorem gop_clm_apply (S : ell2 →L[ℂ] ell2) (y : ell2) (m : ℕ) :
    S y m = ∑' k, S (lp.single 2 k 1 : ell2) m * y k := by
  rw [← gop_inner_single_left m (S y), ← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  have h : (ContinuousLinearMap.adjoint S (lp.single 2 m 1 : ell2)) k =
      conj (S (lp.single 2 k 1 : ell2) m) := by
    rw [← gop_inner_single_left k, ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right,
      gop_inner_apply, mul_one]
  rw [gop_inner_apply, h, Complex.conj_conj]

/-- Operators on `ℓ²` with the same matrix are equal. -/
theorem gop_ext {S S' : ell2 →L[ℂ] ell2}
    (h : ∀ m n, S (lp.single 2 n 1 : ell2) m = S' (lp.single 2 n 1 : ell2) m) : S = S' := by
  ext y m
  rw [gop_clm_apply S y m, gop_clm_apply S' y m]
  exact tsum_congr fun k => by rw [h m k]

/-! ### The operator of a matrix -/

/-- A matrix with `ℓ²` rows and uniformly bounded partial Bessel sums is a bounded operator on `ℓ²`. -/
theorem gop_exists {A : ℕ → ℕ → ℂ}
    (h : (∀ m, Summable fun n => ‖A m n‖ ^ 2) ∧ ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2) :
    ∃ T : ell2 →L[ℂ] ell2, ∀ (x : ell2) (m : ℕ), T x m = ∑' n, A m n * x n := by
  obtain ⟨hrow, C, hC⟩ := h
  have hsum : ∀ x : ell2, Summable fun m => ‖∑' n, A m n * x n‖ ^ 2 := fun x =>
    summable_of_sum_range_le (fun m => by positivity) (hC x (gop_l2_summable x))
  have hle : ∀ x : ell2, ∑' m, ‖∑' n, A m n * x n‖ ^ 2 ≤ max C 0 * ‖x‖ ^ 2 := by
    intro x
    rw [gop_norm_sq x]
    refine (Real.tsum_le_of_sum_range_le (fun m => by positivity) (hC x (gop_l2_summable x))).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (tsum_nonneg fun n => by positivity)
  have hprod : ∀ (x : ell2) m, Summable fun n => A m n * x n := fun x m =>
    mg_sq_mul_summable (hrow m) (gop_l2_summable x)
  let L : ell2 →ₗ[ℂ] ell2 :=
    { toFun := fun x => ⟨fun m => ∑' n, A m n * x n, gop_mem_of_summable (hsum x)⟩
      map_add' := by
        intro x y
        ext m
        show ∑' n, A m n * (x + y) n = (∑' n, A m n * x n) + ∑' n, A m n * y n
        rw [← (hprod x m).tsum_add (hprod y m)]
        exact tsum_congr fun n => by rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro c x
        ext m
        show ∑' n, A m n * (c • x) n = c • ∑' n, A m n * x n
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun n => by rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring }
  have hL : ∀ x, ‖L x‖ ≤ Real.sqrt (max C 0) * ‖x‖ := by
    intro x
    have h1 : ‖L x‖ ^ 2 ≤ max C 0 * ‖x‖ ^ 2 := by
      rw [gop_norm_sq]
      exact hle x
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (norm_nonneg _)] at h2
  exact ⟨L.mkContinuous _ hL, fun x m => rfl⟩

/-- The operator `x ↦ (m ↦ Σ_n A m n x n)` on `ℓ²`, for a matrix with `ℓ²` rows and uniformly bounded partial Bessel
sums (junk `0` otherwise). -/
def gopOp (A : ℕ → ℕ → ℂ) : ell2 →L[ℂ] ell2 :=
  if h : (∀ m, Summable fun n => ‖A m n‖ ^ 2) ∧ ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2
  then (gop_exists h).choose else 0

theorem gop_apply {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (x : ell2) (m : ℕ) : gopOp A x m = ∑' n, A m n * x n := by
  unfold gopOp
  rw [dif_pos ⟨hrow, hbd⟩]
  exact (gop_exists ⟨hrow, hbd⟩).choose_spec x m

theorem gop_tsum_single (a : ℕ → ℂ) (n : ℕ) : ∑' k, a k * (lp.single 2 n 1 : ell2) k = a n := by
  rw [tsum_eq_single n (fun k hk => by rw [gop_single_apply, if_neg hk, mul_zero]), gop_single_apply, if_pos rfl,
    mul_one]

theorem gop_single_entry {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (m n : ℕ) : gopOp A (lp.single 2 n 1 : ell2) m = A m n := by
  rw [gop_apply hrow hbd, gop_tsum_single (A m) n]

/-- The adjoint is the conjugate transpose. -/
theorem gop_adjoint_apply {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (x : ell2) (n : ℕ) : ContinuousLinearMap.adjoint (gopOp A) x n = ∑' m, conj (A m n) * x m := by
  rw [← gop_inner_single_left n, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  refine tsum_congr fun m => ?_
  rw [gop_single_entry hrow hbd, gop_inner_apply]

/-- The transpose `Tᵗ = J T* J` is the transposed matrix. -/
theorem gop_transposeOp_apply {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (x : ell2) (m : ℕ) : transposeOp (gopOp A) x m = ∑' n, A n m * x n := by
  show star (ContinuousLinearMap.adjoint (gopOp A) (star x) m) = _
  rw [gop_adjoint_apply hrow hbd, RCLike.star_def, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [lp.star_apply, map_mul, Complex.conj_conj, RCLike.star_def, Complex.conj_conj]

/-- A symmetric matrix gives a `J`-symmetric operator, `T = Tᵗ`. -/
theorem gop_symm {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (hsym : ∀ m n, A m n = A n m) (x : ell2) : gopOp A x = transposeOp (gopOp A) x := by
  ext m
  rw [gop_apply hrow hbd, gop_transposeOp_apply hrow hbd]
  exact tsum_congr fun n => by rw [hsym]

/-- The matrix of `S T*`. -/
theorem gop_mul_adjoint_entry {A A' : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (hrow' : ∀ m, Summable fun n => ‖A' m n‖ ^ 2)
    (hbd' : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A' m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2) (m n : ℕ) :
    (gopOp A * ContinuousLinearMap.adjoint (gopOp A')) (lp.single 2 n 1 : ell2) m = mulAdj A A' m n := by
  rw [ContinuousLinearMap.mul_apply, gop_apply hrow hbd, mulAdj]
  refine tsum_congr fun k => ?_
  rw [gop_adjoint_apply hrow' hbd', gop_tsum_single (fun j => conj (A' j k)) n]

/-- The matrix of `S* T`. -/
theorem gop_adjoint_mul_entry {A A' : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (hrow' : ∀ m, Summable fun n => ‖A' m n‖ ^ 2)
    (hbd' : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A' m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2) (m n : ℕ) :
    (ContinuousLinearMap.adjoint (gopOp A) * gopOp A') (lp.single 2 n 1 : ell2) m =
      ∑' k, conj (A k m) * A' k n := by
  rw [ContinuousLinearMap.mul_apply, gop_adjoint_apply hrow hbd]
  exact tsum_congr fun k => by rw [gop_single_entry hrow' hbd']

/-- Partial-sum form of `mg_row_bound` (copy of its body): the first `M` output entries obey Bessel's bound. -/
theorem gop_row_partial {A C : ℕ → ℕ → ℂ} (hA : ∀ m, Summable (fun n => ‖A m n‖ ^ 2))
    (hC : ∀ m, Summable (fun n => ‖C m n‖ ^ 2))
    (hI : ∀ m n, (∑' k, A m k * conj (A n k)) + (∑' k, C m k * conj (C n k)) = if m = n then 1 else 0)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) (M : ℕ) :
    ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 := by
  have hnc : ∀ z : ℂ, ‖conj z‖ = ‖z‖ := fun z => Complex.norm_conj z
  have hmc : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.sq_norm]
  have hAc : ∀ m, Summable (fun n => ‖conj (A m n)‖ ^ 2) := fun m => by
    simpa only [hnc] using hA m
  have hCc : ∀ m, Summable (fun n => ‖conj (C m n)‖ ^ 2) := fun m => by
    simpa only [hnc] using hC m
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

/-- The Grunsky blocks have `ℓ²` rows and Bessel bound `1`. -/
theorem gop_grunsky_bounds {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    ∀ A ∈ ({B1 b, B2 b, B3 b, B4 b} : Set (ℕ → ℕ → ℂ)), (∀ m, Summable fun n => ‖A m n‖ ^ 2) ∧
      ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
        ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2 := by
  intro b A hA
  obtain ⟨i1, -, -, i4, -, r1, r2, r3, r4⟩ :=
    mg_eq_2_2_core h hF (B1 := B1 b) (B2 := B2 b) (B3 := B3 b) (B4 := B4 b)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have i1' : ∀ m n, (∑' k, B2 b m k * conj (B2 b n k)) + (∑' k, B1 b m k * conj (B1 b n k)) =
      if m = n then 1 else 0 := fun m n => by rw [add_comm]; exact i1 m n
  have i4' : ∀ m n, (∑' k, B4 b m k * conj (B4 b n k)) + (∑' k, B3 b m k * conj (B3 b n k)) =
      if m = n then 1 else 0 := fun m n => by rw [add_comm]; exact i4 m n
  rcases hA with rfl | rfl | rfl | rfl
  · exact ⟨r1, 1, fun x hx M => by rw [one_mul]; exact gop_row_partial r1 r2 i1 hx M⟩
  · exact ⟨r2, 1, fun x hx M => by rw [one_mul]; exact gop_row_partial r2 r1 i1' hx M⟩
  · exact ⟨r3, 1, fun x hx M => by rw [one_mul]; exact gop_row_partial r3 r4 i4 hx M⟩
  · exact ⟨r4, 1, fun x hx M => by rw [one_mul]; exact gop_row_partial r4 r3 i4' hx M⟩

/-- (2.2) and the unitarity of `𝐁` as operator identities, with `B₁ᵗ = B₁`, `B₄ᵗ = B₄`, `B₃ = B₂ᵗ`. -/
theorem gop_blocks {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    (hF : volume ((f '' unitDisc ∪ g '' unitDiscExterior)ᶜ) = 0) :
    let b := grunsky f g
    gopOp (B1 b) * ContinuousLinearMap.adjoint (gopOp (B1 b)) +
        gopOp (B2 b) * ContinuousLinearMap.adjoint (gopOp (B2 b)) = 1 ∧
      gopOp (B3 b) * ContinuousLinearMap.adjoint (gopOp (B3 b)) +
        gopOp (B4 b) * ContinuousLinearMap.adjoint (gopOp (B4 b)) = 1 ∧
      gopOp (B1 b) * ContinuousLinearMap.adjoint (gopOp (B3 b)) +
        gopOp (B2 b) * ContinuousLinearMap.adjoint (gopOp (B4 b)) = 0 ∧
      ContinuousLinearMap.adjoint (gopOp (B1 b)) * gopOp (B1 b) +
        ContinuousLinearMap.adjoint (gopOp (B3 b)) * gopOp (B3 b) = 1 ∧
      ContinuousLinearMap.adjoint (gopOp (B2 b)) * gopOp (B2 b) +
        ContinuousLinearMap.adjoint (gopOp (B4 b)) * gopOp (B4 b) = 1 ∧
      ContinuousLinearMap.adjoint (gopOp (B1 b)) * gopOp (B2 b) +
        ContinuousLinearMap.adjoint (gopOp (B3 b)) * gopOp (B4 b) = 0 ∧
      (∀ x, gopOp (B1 b) x = transposeOp (gopOp (B1 b)) x) ∧ (∀ x, gopOp (B4 b) x = transposeOp (gopOp (B4 b)) x) ∧
      ∀ x, gopOp (B3 b) x = transposeOp (gopOp (B2 b)) x := by
  intro b
  have hB := gop_grunsky_bounds h hF
  obtain ⟨r1, b1⟩ := hB (B1 b) (Set.mem_insert _ _)
  obtain ⟨r2, b2⟩ := hB (B2 b) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r3, b3⟩ := hB (B3 b) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  obtain ⟨r4, b4⟩ := hB (B4 b)
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  obtain ⟨i1, -, i3, i4, -⟩ := hook_eq_2_2 h hF
  obtain ⟨hsym, u1, u2, u3⟩ := hook_unitary h hF
  -- columns are rows of the symmetric partner
  have c1 : ∀ m, Summable fun k => ‖B1 b k m‖ ^ 2 := fun m =>
    (r1 m).congr fun k => by rw [(hsym k m).1]
  have c2 : ∀ m, Summable fun k => ‖B2 b k m‖ ^ 2 := fun m =>
    (r3 m).congr fun k => by rw [(hsym m k).2.2]
  have c3 : ∀ m, Summable fun k => ‖B3 b k m‖ ^ 2 := fun m =>
    (r2 m).congr fun k => by rw [(hsym k m).2.2]
  have c4 : ∀ m, Summable fun k => ‖B4 b k m‖ ^ 2 := fun m =>
    (r4 m).congr fun k => by rw [(hsym k m).2.1]
  have cc : ∀ {A : ℕ → ℕ → ℂ}, (∀ m, Summable fun k => ‖A k m‖ ^ 2) →
      ∀ m, Summable fun k => ‖conj (A k m)‖ ^ 2 := fun hA m =>
    (hA m).congr fun k => by rw [Complex.norm_conj]
  have hcol : ∀ {A A' : ℕ → ℕ → ℂ}, (∀ m, Summable fun k => ‖A k m‖ ^ 2) →
      (∀ m, Summable fun k => ‖A' k m‖ ^ 2) → ∀ m n, Summable fun k => conj (A k m) * A' k n :=
    fun hA hA' m n => mg_sq_mul_summable (cc hA m) (hA' n)
  have hone : ∀ m n, (1 : ell2 →L[ℂ] ell2) (lp.single 2 n 1 : ell2) m = kron m n := fun m n => by
    rw [ContinuousLinearMap.one_apply, gop_single_apply, kron]
  have hzero : ∀ m n, (0 : ell2 →L[ℂ] ell2) (lp.single 2 n 1 : ell2) m = 0 := fun m n => rfl
  refine ⟨gop_ext fun m n => ?_, gop_ext fun m n => ?_, gop_ext fun m n => ?_, gop_ext fun m n => ?_,
    gop_ext fun m n => ?_, gop_ext fun m n => ?_, gop_symm r1 b1 (fun m n => (hsym m n).1),
    gop_symm r4 b4 (fun m n => (hsym m n).2.1), fun x => ?_⟩
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_mul_adjoint_entry r1 b1 r1 b1,
      gop_mul_adjoint_entry r2 b2 r2 b2, i1 m n, hone]
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_mul_adjoint_entry r3 b3 r3 b3,
      gop_mul_adjoint_entry r4 b4 r4 b4, i4 m n, hone]
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_mul_adjoint_entry r1 b1 r3 b3,
      gop_mul_adjoint_entry r2 b2 r4 b4, i3 m n, hzero]
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_adjoint_mul_entry r1 b1 r1 b1,
      gop_adjoint_mul_entry r3 b3 r3 b3, ← (hcol c1 c1 m n).tsum_add (hcol c3 c3 m n), u1 m n, hone]
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_adjoint_mul_entry r2 b2 r2 b2,
      gop_adjoint_mul_entry r4 b4 r4 b4, ← (hcol c2 c2 m n).tsum_add (hcol c4 c4 m n), u2 m n, hone]
  · rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, gop_adjoint_mul_entry r1 b1 r2 b2,
      gop_adjoint_mul_entry r3 b3 r4 b4, ← (hcol c1 c2 m n).tsum_add (hcol c3 c4 m n), u3 m n, hzero]
  · ext m
    rw [gop_apply r3 b3, gop_transposeOp_apply r2 b2]
    exact tsum_congr fun n => by rw [(hsym m n).2.2]

theorem gop_tsum_normSq {a : ℕ → ℂ} (h : (∑' k, conj (a k) * a k) = 1) : Summable fun k => ‖a k‖ ^ 2 := by
  by_contra hs
  have hs' : ¬ Summable fun k => conj (a k) * a k := by
    intro hc
    apply hs
    have := (Complex.reCLM.summable hc)
    refine this.congr fun k => ?_
    rw [Complex.reCLM_apply, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [tsum_eq_zero_of_not_summable hs'] at h
  exact zero_ne_one h

/-- Bessel with an extra unit vector: if `Σ_n |⟪u_n, e⟫|² = ‖e‖²` for an orthonormal `u` and `y ⊥ u`, then `y ⊥ e`. -/
theorem gop_orth_of_parseval {u : ℕ → ell2} (hu : Orthonormal ℂ u) {y e : ell2} (hy : ∀ n, inner ℂ (u n) y = 0)
    (hp : ∑' n, ‖inner ℂ (u n) e‖ ^ 2 = ‖e‖ ^ 2) : inner ℂ y e = 0 := by
  by_cases hy0 : y = 0
  · rw [hy0, inner_zero_left]
  set z : ell2 := (‖y‖⁻¹ : ℂ) • y
  have hz : ‖z‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  let v : ℕ → ell2 := fun k => Nat.casesOn k z u
  have hv : Orthonormal ℂ v := by
    refine ⟨fun k => ?_, fun i j hij => ?_⟩
    · cases k with
      | zero => exact hz
      | succ n => exact hu.1 n
    · cases i with
      | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ n =>
          show inner ℂ z (u n) = 0
          rw [inner_smul_left, ← inner_conj_symm, hy n, map_zero, mul_zero]
      | succ n =>
        cases j with
        | zero =>
          show inner ℂ (u n) z = 0
          rw [inner_smul_right, hy n, mul_zero]
        | succ m => exact hu.2 (fun h => hij (by rw [h]))
  have hB := hv.tsum_inner_products_le e
  have hsum : Summable fun k => ‖inner ℂ (v k) e‖ ^ 2 := by
    refine summable_of_sum_le (fun k => by positivity) (fun s => hv.sum_inner_products_le e)
  rw [hsum.tsum_eq_zero_add] at hB
  have h0 : ‖inner ℂ z e‖ ^ 2 ≤ 0 := by
    have : ∑' n, ‖inner ℂ (v (n + 1)) e‖ ^ 2 = ‖e‖ ^ 2 := hp
    show ‖inner ℂ (v 0) e‖ ^ 2 ≤ 0
    linarith
  have h1 : inner ℂ z e = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h0 (by positivity))
    exact norm_eq_zero.mp this
  rw [inner_smul_left, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by simpa using h1) (norm_ne_zero_iff.mpr hy0)
  · exact h1

/-- A singular value sequence gives a Hilbert basis of eigenvectors of `T T*`. -/
theorem gop_singular_basis {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    {lam : ℕ → ℝ} (hl : IsSingularSeq A lam) :
    ∃ u : HilbertBasis ℕ ℂ ell2,
      ∀ n, gopOp A (ContinuousLinearMap.adjoint (gopOp A) (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n := by
  obtain ⟨-, U, hrowU, hcolU, heig⟩ := hl
  -- the columns
  have hcs : ∀ n, Summable fun k => ‖U k n‖ ^ 2 := fun n => gop_tsum_normSq (by rw [hcolU n n, kron, if_pos rfl])
  let u : ℕ → ell2 := fun n => ⟨fun k => U k n, gop_mem_of_summable (hcs n)⟩
  have hu : ∀ n k, u n k = U k n := fun n k => rfl
  have huo : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [lp.inner_eq_tsum]
    have := hcolU i j
    rw [kron] at this
    rw [← this]
    exact tsum_congr fun k => by rw [gop_inner_apply, hu, hu]
  -- completeness, from the rows
  have hrs : ∀ m, Summable fun n => ‖U m n‖ ^ 2 := fun m => by
    have h := gop_tsum_normSq (a := fun n => conj (U m n)) (by
      have := hrowU m m
      rw [mulAdj, kron, if_pos rfl] at this
      rw [← this]
      exact tsum_congr fun n => by rw [Complex.conj_conj, mul_comm])
    exact h.congr fun n => by rw [Complex.norm_conj]
  have hpar : ∀ m, ∑' n, ‖inner ℂ (u n) (lp.single 2 m 1 : ell2)‖ ^ 2 = ‖(lp.single 2 m 1 : ell2)‖ ^ 2 := by
    intro m
    have hnorm : ‖(lp.single 2 m 1 : ell2)‖ = 1 := by
      rw [lp.norm_single (by norm_num), norm_one]
    rw [hnorm, one_pow]
    have h := hrowU m m
    rw [mulAdj, kron, if_pos rfl] at h
    have h' : ((∑' n, ‖U m n‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h, Complex.ofReal_tsum]
      exact tsum_congr fun n => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h'' : ∑' n, ‖U m n‖ ^ 2 = 1 := by exact_mod_cast h'
    rw [← h'']
    exact tsum_congr fun n => by rw [lp.inner_single_right, gop_inner_apply, mul_one, hu, Complex.norm_conj]
  have htot : (Submodule.span ℂ (Set.range u))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ n, inner ℂ (u n) y = 0 := fun n =>
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self n)) hy
    ext m
    have := gop_orth_of_parseval huo hy' (hpar m)
    rw [lp.inner_single_right, gop_inner_apply, mul_one] at this
    rw [lp.coeFn_zero, Pi.zero_apply]
    simpa using this
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot huo htot, fun n => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  ext m
  rw [← ContinuousLinearMap.mul_apply, gop_clm_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hu, ← heig m n]
  exact tsum_congr fun k => by rw [gop_mul_adjoint_entry hrow hbd hrow hbd, hu]

/-- A Hilbert basis of eigenvectors of `T T*` gives a singular value sequence. -/
theorem gop_basis_singular {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (u : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, gopOp A (ContinuousLinearMap.adjoint (gopOp A) (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n) :
    IsSingularSeq A lam := by
  refine ⟨h0, fun m n => u n m, fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · -- rows: Parseval for `e_m`, `e_n`
    have h := u.tsum_inner_mul_inner (lp.single 2 m 1 : ell2) (lp.single 2 n 1 : ell2)
    rw [mulAdj, kron]
    rw [gop_inner_single_left, gop_single_apply] at h
    rw [← h]
    refine tsum_congr fun k => ?_
    rw [gop_inner_single_left, ← inner_conj_symm (u k) (lp.single 2 n 1 : ell2), gop_inner_single_left]
  · have h := orthonormal_iff_ite.mp u.orthonormal m n
    rw [lp.inner_eq_tsum] at h
    rw [kron, ← h]
    exact tsum_congr fun k => by rw [gop_inner_apply]
  · have h := congrArg (fun y : ell2 => y m) (hu n)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h
    rw [← h, ← ContinuousLinearMap.mul_apply, gop_clm_apply]
    exact tsum_congr fun k => by rw [gop_mul_adjoint_entry hrow hbd hrow hbd]

/-- The operator `x ↦ (⟪r_m, x⟫)_m` of a square-summable family of rows, with its Hilbert–Schmidt bound
(after 下属2's `e212_mk`). -/
theorem gop_rows_mk (r : ℕ → ell2) (hr : Summable fun m => ‖r m‖ ^ 2) :
    ∃ T : ell2 →L[ℂ] ell2, (∀ x m, T x m = inner ℂ (r m) x) ∧ ‖T‖ ≤ Real.sqrt (∑' m, ‖r m‖ ^ 2) := by
  have hb : ∀ x : ell2, ∀ m, ‖inner ℂ (r m) x‖ ^ 2 ≤ ‖r m‖ ^ 2 * ‖x‖ ^ 2 := fun x m => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hs : ∀ x : ell2, Summable fun m => ‖inner ℂ (r m) x‖ ^ 2 := fun x =>
    (hr.mul_right (‖x‖ ^ 2)).of_nonneg_of_le (fun m => by positivity) (hb x)
  let L : ell2 →ₗ[ℂ] ell2 :=
    { toFun := fun x => ⟨fun m => inner ℂ (r m) x, gop_mem_of_summable (hs x)⟩
      map_add' := fun x y => by
        ext m
        show inner ℂ (r m) (x + y) = inner ℂ (r m) x + inner ℂ (r m) y
        exact inner_add_right _ _ _
      map_smul' := fun c x => by
        ext m
        show inner ℂ (r m) (c • x) = c • inner ℂ (r m) x
        rw [inner_smul_right, smul_eq_mul] }
  have hbound : ∀ x, ‖L x‖ ≤ Real.sqrt (∑' m, ‖r m‖ ^ 2) * ‖x‖ := fun x => by
    have h1 : ‖L x‖ ^ 2 = ∑' m, ‖inner ℂ (r m) x‖ ^ 2 := gop_norm_sq (L x)
    have h2 : ∑' m, ‖inner ℂ (r m) x‖ ^ 2 ≤ (∑' m, ‖r m‖ ^ 2) * ‖x‖ ^ 2 := by
      rw [← tsum_mul_right]
      exact (hs x).tsum_le_tsum (hb x) (hr.mul_right _)
    have h3 : 0 ≤ Real.sqrt (∑' m, ‖r m‖ ^ 2) * ‖x‖ := by positivity
    have h4 : ‖L x‖ ^ 2 ≤ (Real.sqrt (∑' m, ‖r m‖ ^ 2) * ‖x‖) ^ 2 := by
      rw [h1, mul_pow, Real.sq_sqrt (tsum_nonneg fun m => by positivity)]
      exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h3 (by norm_num : (2 : ℕ) ≠ 0)).1 h4
  exact ⟨L.mkContinuous _ hbound, fun x m => rfl, L.mkContinuous_norm_le (Real.sqrt_nonneg _) hbound⟩

/-- Row truncation: the operator of a square-summable family of rows is compact (after 下属2's `e212_mk_compact`). -/
theorem gop_rows_compact (r : ℕ → ell2) (hr : Summable fun m => ‖r m‖ ^ 2) {T : ell2 →L[ℂ] ell2}
    (hT : ∀ x m, T x m = inner ℂ (r m) x) : IsCompactOperator T := by
  classical
  let TN : ℕ → ell2 →L[ℂ] ell2 := fun N => ∑ j ∈ Finset.range N,
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 j 1 : ell2)).comp (innerSL ℂ (r j))
  have hTN : ∀ N x m, TN N x m = if m < N then inner ℂ (r m) x else 0 := by
    intro N x m
    simp only [TN, ContinuousLinearMap.coe_sum', Finset.sum_apply, lp.coeFn_sum, ContinuousLinearMap.coe_comp',
      Function.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, lp.coeFn_smul,
      Pi.smul_apply, lp.coeFn_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
  have hcomp : ∀ N, IsCompactOperator (TN N) := by
    intro N
    induction N with
    | zero =>
      have h0 : TN 0 = 0 := Finset.sum_range_zero _
      rw [h0]
      exact isCompactOperator_zero
    | succ N ih =>
      have hs : TN (N + 1) = TN N +
          (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 N 1 : ell2)).comp (innerSL ℂ (r N)) :=
        Finset.sum_range_succ _ _
      rw [hs, ContinuousLinearMap.coe_add']
      refine ih.add ?_
      rw [ContinuousLinearMap.coe_comp']
      exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ (r N))).clm_comp _
  have htail : ∀ N, ∃ S : ell2 →L[ℂ] ell2, (∀ x m, S x m = inner ℂ (if m < N then 0 else r m) x) ∧
      ‖S‖ ≤ Real.sqrt (∑' k, ‖r (k + N)‖ ^ 2) := by
    intro N
    have hg : Summable fun m => ‖(if m < N then 0 else r m : ell2)‖ ^ 2 :=
      hr.of_nonneg_of_le (fun m => by positivity) (fun m => by split_ifs <;> simp)
    obtain ⟨S, hS, hSn⟩ := gop_rows_mk _ hg
    refine ⟨S, hS, hSn.trans (Real.sqrt_le_sqrt (le_of_eq ?_))⟩
    rw [← hg.sum_add_tsum_nat_add N]
    have h0 : ∑ i ∈ Finset.range N, ‖(if i < N then 0 else r i : ell2)‖ ^ 2 = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [Finset.mem_range.1 hi]
    rw [h0, zero_add]
    exact tsum_congr fun k => by simp
  have hlim : Tendsto TN atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hz : Tendsto (fun N => Real.sqrt (∑' k, ‖r (k + N)‖ ^ 2)) atTop (𝓝 0) := by
      have := (tendsto_sum_nat_add fun k => ‖r k‖ ^ 2).sqrt
      simpa only [Real.sqrt_zero] using this
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hz
    obtain ⟨S, hS, hSn⟩ := htail N
    have hE : TN N - T = -S := by
      ext x m
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, lp.coeFn_sub, lp.coeFn_neg,
        Pi.sub_apply, Pi.neg_apply, hTN, hT, hS]
      split_ifs <;> simp
    rw [hE, norm_neg]
    exact hSn
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall hcomp)

/-- A Hilbert–Schmidt matrix gives a compact operator. -/
theorem gop_compact_of_HS {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (hHS : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖ ^ 2) : IsCompactOperator (gopOp A) := by
  let r : ℕ → ell2 := fun m => ⟨fun k => conj (A m k),
    gop_mem_of_summable ((hrow m).congr fun k => by rw [Complex.norm_conj])⟩
  have hrn : ∀ m, ‖r m‖ ^ 2 = ∑' k, ‖A m k‖ ^ 2 := fun m => by
    rw [gop_norm_sq]
    exact tsum_congr fun k => by
      show ‖conj (A m k)‖ ^ 2 = _
      rw [Complex.norm_conj]
  have hr : Summable fun m => ‖r m‖ ^ 2 := by
    simp only [hrn]
    exact hHS.prod
  obtain ⟨T, hT, -⟩ := gop_rows_mk r hr
  have hTA : gopOp A = T := by
    ext x m
    rw [gop_apply hrow hbd, hT, lp.inner_eq_tsum]
    exact tsum_congr fun k => by
      show A m k * x k = inner ℂ (conj (A m k)) (x k)
      rw [gop_inner_apply, Complex.conj_conj]
  rw [hTA]
  exact gop_rows_compact r hr hT

end Ch2
end TakhtajanTeo
