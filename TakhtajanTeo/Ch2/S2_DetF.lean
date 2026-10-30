import TakhtajanTeo.Ch2.S2_Cor29
import TakhtajanTeo.Ch2.S2_GrunskyOp
import TakhtajanTeo.Ch2.S2_Remark23
import TakhtajanTeo.Ch2.S2_Remark22

/-!
# `detF_spec` and `(2.13)` (host `Ch2/S2_DetF.lean`, prefix `dF_`)

Route (TT:4478–4495), at the operator level on `ℓ²`:
1–2. Shared module `Ch2/S2_GrunskyOp` (`gop_`): `gopOp`, `gop_blocks` (unitarity + symmetries),
   `gop_singular_basis` / `gop_basis_singular` (`IsSingularSeq A λ` ⇔ a Hilbert basis of eigenvectors of `T T*`).
3. `dF_lam_lt_one_op`: `λ_n < 1` once `T₃` is bounded below. `dF_transfer`: the vectors `T₃ ū_n / √(1 - λ_n²)` form a
   Hilbert basis of eigenvectors of `T₄T₄*` with the same `λ_n²` (TT's `Vᵗ B₄ V = -D`). Completeness uses that `T₃*`
   is injective, i.e. `T₂` is injective.
4. `dF_sq_summable`: `Σ λ_n² = ‖B₁‖²_HS < ∞` (Parseval twice). `dF_tprod_indep`: two singular sequences have the same
   positive values with the same finite multiplicities, so the products agree (`tprod_eq_tprod_of_ne_one_bij`).
5. `dF_multipliable`, `dF_tprod_pos`: `Real.multipliable_one_add_of_summable` and `Real.rexp_tsum_eq_tprod`.
6. `dF_remark23_ops` (**held** until `remark_2_3` closes): `T₂`, `T₃` are bounded below. This is the only use of
   `remark_2_3`, through its clauses 3 and 4 only.
7. Assembly `dF_detF_spec`; `dF_eq_2_13` from `fb_clause3` (`B₁([μ]⁻¹) = \overline{B₄([μ])}`), `dF_singular_conj`,
   `lemma_3_4` and `grp_invT_invT`.

[NOTE] The frozen `remark_2_3` has `∃ c < 1` with bounds `c²‖x‖²`. A negative `c` is allowed, so clauses 1 and 2 hold
trivially with `c = -1` (`‖B₁‖ ≤ 1` by `eq_2_2`). They are vacuous. This route does not use them.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real InnerProductSpace
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem dF_inner_mul_adjoint (T : ell2 →L[ℂ] ell2) (u : ell2) :
    RCLike.re (inner ℂ u ((T * ContinuousLinearMap.adjoint T) u)) = ‖ContinuousLinearMap.adjoint T u‖ ^ 2 := by
  rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]

/-- `‖T* u‖² = s ‖u‖²` for an eigenvector `T T* u = s u`. -/
theorem dF_norm_adjoint_sq {T : ell2 →L[ℂ] ell2} {u : ell2} {s : ℝ}
    (h : T (ContinuousLinearMap.adjoint T u) = (s : ℂ) • u) :
    ‖ContinuousLinearMap.adjoint T u‖ ^ 2 = s * ‖u‖ ^ 2 := by
  have h1 := dF_inner_mul_adjoint T u
  rw [ContinuousLinearMap.mul_apply, h, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul,
    ← RCLike.re_to_complex, inner_self_eq_norm_sq] at h1
  exact h1.symm

/-- (3) If `T₁T₁* + T₂T₂* = 1` and `T₃ = T₂ᵗ` is injective, `T₁T₁*` has no unit eigenvalue. -/
theorem dF_lam_lt_one_op {T₁ T₂ T₃ : ell2 →L[ℂ] ell2}
    (hR1 : T₁ * ContinuousLinearMap.adjoint T₁ + T₂ * ContinuousLinearMap.adjoint T₂ = 1)
    (hT3 : ∀ x, T₃ x = transposeOp T₂ x) (hinj : Function.Injective T₃) {u : ell2} (hu : u ≠ 0) {s : ℝ}
    (h : T₁ (ContinuousLinearMap.adjoint T₁ u) = (s : ℂ) • u) : s < 1 := by
  by_contra hs
  push_neg at hs
  have e1 : (T₁ * ContinuousLinearMap.adjoint T₁) u + (T₂ * ContinuousLinearMap.adjoint T₂) u = u := by
    rw [← ContinuousLinearMap.add_apply, hR1, ContinuousLinearMap.one_apply]
  have e2 := congrArg (fun v => RCLike.re (inner ℂ u v)) e1
  have e3 : ‖ContinuousLinearMap.adjoint T₁ u‖ ^ 2 + ‖ContinuousLinearMap.adjoint T₂ u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp only [inner_add_right, map_add, dF_inner_mul_adjoint, inner_self_eq_norm_sq] at e2
    exact e2
  rw [dF_norm_adjoint_sq h] at e3
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  have h0 : ‖ContinuousLinearMap.adjoint T₂ u‖ ^ 2 ≤ 0 := by nlinarith
  have h00 : ContinuousLinearMap.adjoint T₂ u = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h0 (by positivity)))
  have h3 : T₃ (star u) = 0 := by
    rw [hT3]
    show star (ContinuousLinearMap.adjoint T₂ (star (star u))) = 0
    rw [star_star, h00, star_zero]
  have h4 : star u = 0 := hinj (h3.trans (map_zero T₃).symm)
  exact hu (by simpa using congrArg star h4)

theorem dF_inner_star (a b : ell2) : inner ℂ (star a) (star b) = inner ℂ b a := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [lp.star_apply, lp.star_apply, gop_inner_apply, gop_inner_apply]
  simp only [RCLike.star_def, Complex.conj_conj]
  ring

/-- For `T₃ = T₂ᵗ`: `T₃* y = \overline{T₂ ȳ}`. -/
theorem dF_adjoint_transpose {T₂ T₃ : ell2 →L[ℂ] ell2} (hT3 : ∀ x, T₃ x = transposeOp T₂ x) (y : ell2) :
    ContinuousLinearMap.adjoint T₃ y = star (T₂ (star y)) := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, hT3]
  show inner ℂ (star (ContinuousLinearMap.adjoint T₂ (star x))) y = inner ℂ x (star (T₂ (star y)))
  calc inner ℂ (star (ContinuousLinearMap.adjoint T₂ (star x))) y
      = inner ℂ (star (ContinuousLinearMap.adjoint T₂ (star x))) (star (star y)) := by rw [star_star]
    _ = inner ℂ (star y) (ContinuousLinearMap.adjoint T₂ (star x)) := dF_inner_star _ _
    _ = inner ℂ (T₂ (star y)) (star x) := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ (star (star x)) (star (T₂ (star y))) := (dF_inner_star _ _).symm
    _ = inner ℂ x (star (T₂ (star y))) := by rw [star_star]

/-- An element orthogonal to a Hilbert basis is zero. -/
theorem dF_eq_zero_of_orth (u : HilbertBasis ℕ ℂ ell2) {z : ell2} (hz : ∀ n, inner ℂ (u n) z = 0) : z = 0 := by
  have h := u.tsum_inner_mul_inner z z
  have h0 : ∀ n, inner ℂ z (u n) = 0 := fun n => by rw [← inner_conj_symm, hz n, map_zero]
  simp only [h0, zero_mul, tsum_zero] at h
  exact inner_self_eq_zero.mp h.symm

/-- (3) Transfer of singular vectors from `B₁` to `B₄` (TT's `Vᵗ B₄ V = -D`). -/
theorem dF_transfer {T₁ T₂ T₃ T₄ : ell2 →L[ℂ] ell2}
    (hR4 : T₃ * ContinuousLinearMap.adjoint T₃ + T₄ * ContinuousLinearMap.adjoint T₄ = 1)
    (hC1 : ContinuousLinearMap.adjoint T₁ * T₁ + ContinuousLinearMap.adjoint T₃ * T₃ = 1)
    (hsym : ∀ x, T₁ x = transposeOp T₁ x) (hT3 : ∀ x, T₃ x = transposeOp T₂ x) (hinj : Function.Injective T₂)
    {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1) (u : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, T₁ (ContinuousLinearMap.adjoint T₁ (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n) :
    ∃ w : HilbertBasis ℕ ℂ ell2, ∀ n, T₄ (ContinuousLinearMap.adjoint T₄ (w n)) = ((lam n ^ 2 : ℝ) : ℂ) • w n := by
  -- `T₁* y = \overline{T₁ ȳ}`
  have hadj1 : ∀ y, ContinuousLinearMap.adjoint T₁ y = star (T₁ (star y)) := dF_adjoint_transpose hsym
  have hadj3 : ∀ y, ContinuousLinearMap.adjoint T₃ y = star (T₂ (star y)) := dF_adjoint_transpose hT3
  -- `v_n = ū_n` are eigenvectors of `T₁*T₁`
  have hv : ∀ n, ContinuousLinearMap.adjoint T₁ (T₁ (star (u n))) = ((lam n ^ 2 : ℝ) : ℂ) • star (u n) := by
    intro n
    have e : T₁ (star (u n)) = star (ContinuousLinearMap.adjoint T₁ (u n)) := by
      rw [hadj1, star_star]
    rw [e, hadj1, star_star, hu n, star_smul, RCLike.star_def, Complex.conj_ofReal]
  have hC1' : ∀ x, ContinuousLinearMap.adjoint T₃ (T₃ x) = x - ContinuousLinearMap.adjoint T₁ (T₁ x) := by
    intro x
    have := congrArg (fun S : ell2 →L[ℂ] ell2 => S x) hC1
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    rw [eq_sub_iff_add_eq, add_comm]; exact this
  have hR4' : ∀ y, T₄ (ContinuousLinearMap.adjoint T₄ y) = y - T₃ (ContinuousLinearMap.adjoint T₃ y) := by
    intro y
    have := congrArg (fun S : ell2 →L[ℂ] ell2 => S y) hR4
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    rw [eq_sub_iff_add_eq, add_comm]; exact this
  -- `T₃*T₃ v_n = (1 - λ_n²) v_n`
  have h33 : ∀ n, ContinuousLinearMap.adjoint T₃ (T₃ (star (u n))) =
      ((1 - lam n ^ 2 : ℝ) : ℂ) • star (u n) := by
    intro n
    rw [hC1', hv n, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hpos : ∀ n, 0 < 1 - lam n ^ 2 := fun n => by nlinarith [h0 n, h1 n]
  let c : ℕ → ℂ := fun n => ((Real.sqrt (1 - lam n ^ 2))⁻¹ : ℝ)
  let w : ℕ → ell2 := fun n => c n • T₃ (star (u n))
  have hww : ∀ m n, inner ℂ (w m) (w n) = if m = n then 1 else 0 := by
    intro m n
    have hin : inner ℂ (T₃ (star (u m))) (T₃ (star (u n))) =
        ((1 - lam n ^ 2 : ℝ) : ℂ) * (if m = n then 1 else 0) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, h33 n, inner_smul_right, dF_inner_star,
        orthonormal_iff_ite.mp u.orthonormal n m]
      by_cases h : m = n
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [w, inner_smul_left, inner_smul_right, hin, c]
    by_cases h : m = n
    · subst h
      simp only [ite_true, mul_one, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_eq_one, ← mul_assoc, ← mul_inv,
        Real.mul_self_sqrt (hpos m).le, inv_mul_cancel₀ (hpos m).ne']
    · simp [h]
  have hwo : Orthonormal ℂ w := orthonormal_iff_ite.mpr hww
  have htot : (Submodule.span ℂ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hy' : ∀ n, inner ℂ (w n) y = 0 := fun n =>
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self n)) hy
    -- `⟪v_n, T₃* y⟫ = 0`
    have h2 : ∀ n, inner ℂ (u n) (star (ContinuousLinearMap.adjoint T₃ y)) = 0 := by
      intro n
      have hn := hy' n
      simp only [w, inner_smul_left, mul_eq_zero, map_eq_zero, c] at hn
      rcases hn with hn | hn
      · exact absurd hn (by
          have := Real.sqrt_pos.mpr (hpos n)
          exact_mod_cast (inv_pos.mpr this).ne')
      · rw [← ContinuousLinearMap.adjoint_inner_right] at hn
        rw [← dF_inner_star, star_star, ← inner_conj_symm, hn, map_zero]
    have h3 := dF_eq_zero_of_orth u h2
    rw [star_eq_zero, hadj3, star_eq_zero] at h3
    have h4 : star y = 0 := hinj (h3.trans (map_zero T₂).symm)
    simpa using congrArg star h4
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot hwo htot, fun n => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  show T₄ (ContinuousLinearMap.adjoint T₄ (c n • T₃ (star (u n)))) = _ • (c n • T₃ (star (u n)))
  rw [hR4', map_smul, map_smul, h33 n, map_smul]
  simp only [smul_smul]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

/-- (4) `Σ λ_n² = ‖A‖²_HS` is finite for a Hilbert–Schmidt matrix. -/
theorem dF_sq_summable {A : ℕ → ℕ → ℂ} (hrow : ∀ m, Summable fun n => ‖A m n‖ ^ 2)
    (hbd : ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤ C * ∑' n, ‖x n‖ ^ 2)
    (hHS : Summable fun q : ℕ × ℕ => ‖A q.1 q.2‖ ^ 2) {lam : ℕ → ℝ} (u : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, gopOp A (ContinuousLinearMap.adjoint (gopOp A) (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n) :
    Summable fun n => lam n ^ 2 := by
  have hl : ∀ n, lam n ^ 2 = ‖ContinuousLinearMap.adjoint (gopOp A) (u n)‖ ^ 2 := fun n => by
    rw [dF_norm_adjoint_sq (hu n), u.orthonormal.1 n, one_pow, mul_one]
  have hent : ∀ n k, ‖(ContinuousLinearMap.adjoint (gopOp A) (u n)) k‖ ^ 2 =
      ‖inner ℂ (u n) (gopOp A (lp.single 2 k 1 : ell2))‖ ^ 2 := fun n k => by
    rw [← gop_inner_single_left k, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.norm_conj]
  have hcol : ∀ k, ‖gopOp A (lp.single 2 k 1 : ell2)‖ ^ 2 = ∑' m, ‖A m k‖ ^ 2 := fun k => by
    rw [gop_norm_sq]
    exact tsum_congr fun m => by rw [gop_single_entry hrow hbd]
  have hcs : Summable fun k => ∑' m, ‖A m k‖ ^ 2 := by
    have h' : Summable fun q : ℕ × ℕ => ‖A q.2 q.1‖ ^ 2 := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hHS
    exact h'.prod
  have hcs' : Summable fun k => ‖gopOp A (lp.single 2 k 1 : ell2)‖ ^ 2 := hcs.congr fun k => (hcol k).symm
  have hsn : ∀ n, Summable fun k => ‖inner ℂ (u n) (gopOp A (lp.single 2 k 1 : ell2))‖ ^ 2 := fun n =>
    (gop_l2_summable (ContinuousLinearMap.adjoint (gopOp A) (u n))).congr fun k => hent n k
  refine summable_of_sum_le (c := ∑' k, ‖gopOp A (lp.single 2 k 1 : ell2)‖ ^ 2) (fun n => by positivity)
    (fun s => ?_)
  calc ∑ n ∈ s, lam n ^ 2 = ∑ n ∈ s, ∑' k, ‖inner ℂ (u n) (gopOp A (lp.single 2 k 1 : ell2))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hl, gop_norm_sq]
        exact tsum_congr fun k => hent n k
    _ = ∑' k, ∑ n ∈ s, ‖inner ℂ (u n) (gopOp A (lp.single 2 k 1 : ell2))‖ ^ 2 :=
        (Summable.tsum_finsetSum fun n _ => hsn n).symm
    _ ≤ ∑' k, ‖gopOp A (lp.single 2 k 1 : ell2)‖ ^ 2 :=
        Summable.tsum_le_tsum (fun k => u.orthonormal.sum_inner_products_le _)
          (summable_sum fun n _ => hsn n) hcs'

/-- Eigenvectors of the self-adjoint `T T*` for different eigenvalues are orthogonal. -/
theorem dF_orth_eig {T : ell2 →L[ℂ] ell2} {a b : ell2} {α β : ℝ} (hab : α ≠ β)
    (ha : T (ContinuousLinearMap.adjoint T a) = (α : ℂ) • a) (hb : T (ContinuousLinearMap.adjoint T b) = (β : ℂ) • b) :
    inner ℂ a b = 0 := by
  have h1 : inner ℂ (T (ContinuousLinearMap.adjoint T a)) b = inner ℂ a (T (ContinuousLinearMap.adjoint T b)) :=
    (ContinuousLinearMap.adjoint_inner_right T (ContinuousLinearMap.adjoint T a) b).symm.trans
      (ContinuousLinearMap.adjoint_inner_left T (ContinuousLinearMap.adjoint T b) a)
  rw [ha, hb, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((α - β : ℝ) : ℂ) * inner ℂ a b = 0 := by push_cast; linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp (by exact_mod_cast h)) hab
  · exact h

/-- The fibre `{n | λ_n² = s}`, `s > 0`, is finite for square-summable `λ`. -/
theorem dF_fiber_finite {lam : ℕ → ℝ} (hs : Summable fun n => lam n ^ 2) {s : ℝ} (hs0 : 0 < s) :
    {n | lam n ^ 2 = s}.Finite := by
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hs0)
  refine (Filter.eventually_cofinite.mp h).subset fun n hn => ?_
  show ¬ lam n ^ 2 < s
  rw [Set.mem_setOf_eq.mp hn]
  exact lt_irrefl s

/-- Parseval over the eigenvalue-`s` vectors: a vector of the `s`-eigenspace sees only the `s`-fibre. -/
theorem dF_fiber_parseval {T : ell2 →L[ℂ] ell2} {lam : ℕ → ℝ} (u : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, T (ContinuousLinearMap.adjoint T (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n) {s : ℝ}
    (F : Finset ℕ) (hF : ∀ n, n ∈ F ↔ lam n ^ 2 = s) {x : ell2}
    (hx : T (ContinuousLinearMap.adjoint T x) = (s : ℂ) • x) :
    ∑ n ∈ F, ‖inner ℂ (u n) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := u.tsum_inner_mul_inner x x
  have hterm : ∀ n, inner ℂ x (u n) * inner ℂ (u n) x = ((‖inner ℂ (u n) x‖ ^ 2 : ℝ) : ℂ) := fun n => by
    rw [← inner_conj_symm, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hterm] at h
  have hz : ∀ n ∉ F, ‖inner ℂ (u n) x‖ ^ 2 = 0 := fun n hn => by
    rw [dF_orth_eig (fun he => hn ((hF n).mpr he)) (hu n) hx, norm_zero]; ring
  rw [← Complex.ofReal_tsum, tsum_eq_sum hz] at h
  have h' := congrArg RCLike.re h
  rw [inner_self_eq_norm_sq, RCLike.re_to_complex, Complex.ofReal_re] at h'
  exact h'

/-- Two eigenbases of `T T*` have the same multiplicity of each positive eigenvalue. -/
theorem dF_card_fiber {T : ell2 →L[ℂ] ell2} {lam lam' : ℕ → ℝ} (u u' : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, T (ContinuousLinearMap.adjoint T (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n)
    (hu' : ∀ n, T (ContinuousLinearMap.adjoint T (u' n)) = ((lam' n ^ 2 : ℝ) : ℂ) • u' n) {s : ℝ}
    (F F' : Finset ℕ) (hF : ∀ n, n ∈ F ↔ lam n ^ 2 = s) (hF' : ∀ n, n ∈ F' ↔ lam' n ^ 2 = s) :
    F.card = F'.card := by
  have hsx : ∀ n ∈ F, T (ContinuousLinearMap.adjoint T (u n)) = (s : ℂ) • u n := fun n hn => by
    rw [hu n, (hF n).mp hn]
  have hsx' : ∀ n ∈ F', T (ContinuousLinearMap.adjoint T (u' n)) = (s : ℂ) • u' n := fun n hn => by
    rw [hu' n, (hF' n).mp hn]
  have c1 : (F.card : ℝ) = ∑ n ∈ F, ∑ m ∈ F', ‖inner ℂ (u' m) (u n)‖ ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [dF_fiber_parseval u' hu' F' hF' (hsx n hn), u.orthonormal.1 n, one_pow]
  have c2 : (F'.card : ℝ) = ∑ m ∈ F', ∑ n ∈ F, ‖inner ℂ (u n) (u' m)‖ ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [dF_fiber_parseval u hu F hF (hsx' m hm), u'.orthonormal.1 m, one_pow]
  have c3 : ∑ n ∈ F, ∑ m ∈ F', ‖inner ℂ (u' m) (u n)‖ ^ 2 = ∑ m ∈ F', ∑ n ∈ F, ‖inner ℂ (u n) (u' m)‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [← inner_conj_symm, Complex.norm_conj]
  exact_mod_cast c1.trans (c3.trans c2.symm)

/-- (4) Two eigenbases of `T T*` with square-summable eigenvalues give the same Fredholm product. -/
theorem dF_tprod_indep {T : ell2 →L[ℂ] ell2} {lam lam' : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h0' : ∀ n, 0 ≤ lam' n)
    (hs : Summable fun n => lam n ^ 2) (hs' : Summable fun n => lam' n ^ 2) (u u' : HilbertBasis ℕ ℂ ell2)
    (hu : ∀ n, T (ContinuousLinearMap.adjoint T (u n)) = ((lam n ^ 2 : ℝ) : ℂ) • u n)
    (hu' : ∀ n, T (ContinuousLinearMap.adjoint T (u' n)) = ((lam' n ^ 2 : ℝ) : ℂ) • u' n) :
    ∏' n, (1 - lam n ^ 2) = ∏' n, (1 - lam' n ^ 2) := by
  classical
  -- `λ_n ≥ 0` is not needed: only the values `λ_n²` enter
  have _h0 := h0
  have _h0' := h0'
  -- the nonzero indices, fibred by the eigenvalue
  let α := {n : ℕ // lam n ^ 2 ≠ 0}
  let α' := {n : ℕ // lam' n ^ 2 ≠ 0}
  let f : α → ℝ := fun x => lam x.1 ^ 2
  let f' : α' → ℝ := fun x => lam' x.1 ^ 2
  have hfib : ∀ y : ℝ, Nonempty ({x : α // f x = y} ≃ {x : α' // f' x = y}) := by
    intro y
    by_cases hy : 0 < y
    · have hfin := dF_fiber_finite hs hy
      have hfin' := dF_fiber_finite hs' hy
      have hc := dF_card_fiber (s := y) u u' hu hu' hfin.toFinset hfin'.toFinset (fun n => by simp)
        (fun n => by simp)
      have e1 : {x : α // f x = y} ≃ {n : ℕ // lam n ^ 2 = y} :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun n => ⟨⟨n.1, by rw [n.2]; exact hy.ne'⟩, n.2⟩
          left_inv := fun x => rfl
          right_inv := fun n => rfl }
      have e2 : {x : α' // f' x = y} ≃ {n : ℕ // lam' n ^ 2 = y} :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun n => ⟨⟨n.1, by rw [n.2]; exact hy.ne'⟩, n.2⟩
          left_inv := fun x => rfl
          right_inv := fun n => rfl }
      haveI : Finite {n : ℕ // lam n ^ 2 = y} := hfin.to_subtype
      haveI : Finite {n : ℕ // lam' n ^ 2 = y} := hfin'.to_subtype
      have hcard : Nat.card {n : ℕ // lam n ^ 2 = y} = Nat.card {n : ℕ // lam' n ^ 2 = y} := by
        have c1 : Nat.card {n : ℕ // lam n ^ 2 = y} = hfin.toFinset.card := by
          rw [← Set.ncard_eq_toFinset_card _ hfin]; exact Nat.card_coe_set_eq _
        have c2 : Nat.card {n : ℕ // lam' n ^ 2 = y} = hfin'.toFinset.card := by
          rw [← Set.ncard_eq_toFinset_card _ hfin']; exact Nat.card_coe_set_eq _
        rw [c1, c2, hc]
      obtain ⟨e⟩ := Finite.card_eq.mp hcard
      exact ⟨e1.trans (e.trans e2.symm)⟩
    · haveI : IsEmpty {x : α // f x = y} :=
        ⟨fun x => hy (x.2 ▸ lt_of_le_of_ne (sq_nonneg _) (Ne.symm x.1.2))⟩
      haveI : IsEmpty {x : α' // f' x = y} :=
        ⟨fun x => hy (x.2 ▸ lt_of_le_of_ne (sq_nonneg _) (Ne.symm x.1.2))⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
  let E : α ≃ α' := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun y => (hfib y).some).trans (Equiv.sigmaFiberEquiv f'))
  have hE : ∀ x, f' (E x) = f x := by
    intro x
    simp only [E, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
    exact ((hfib (f x)).some ⟨x, rfl⟩).2
  have hsupp : ∀ n, (1 - lam n ^ 2 ≠ 1) ↔ lam n ^ 2 ≠ 0 := fun n => by
    constructor <;> intro h <;> contrapose! h <;> linarith
  have hsupp' : ∀ n, (1 - lam' n ^ 2 ≠ 1) ↔ lam' n ^ 2 ≠ 0 := fun n => by
    constructor <;> intro h <;> contrapose! h <;> linarith
  symm
  refine tprod_eq_tprod_of_ne_one_bij (fun x => (E ⟨x.1, (hsupp x.1).mp x.2⟩).1) ?_ ?_ ?_
  · intro x y hxy
    have := E.injective (Subtype.ext hxy)
    have h2 : x.1 = y.1 := congrArg (fun z : α => z.1) this
    exact Subtype.ext h2
  · intro n hn
    have hn' : lam' n ^ 2 ≠ 0 := (hsupp' n).mp hn
    obtain ⟨x, hx⟩ := E.surjective ⟨n, hn'⟩
    refine ⟨⟨x.1, (hsupp x.1).mpr x.2⟩, ?_⟩
    show (E ⟨x.1, _⟩).1 = n
    rw [show (⟨x.1, (hsupp x.1).mp ((hsupp x.1).mpr x.2)⟩ : α) = x from rfl, hx]
  · intro x
    exact congrArg (fun t => 1 - t) (hE ⟨x.1, (hsupp x.1).mp x.2⟩)

/-- (5) The Fredholm product converges. -/
theorem dF_multipliable {lam : ℕ → ℝ} (hs : Summable fun n => lam n ^ 2) :
    Multipliable fun n => 1 - lam n ^ 2 := by
  have := Real.multipliable_one_add_of_summable (f := fun n => -(lam n ^ 2)) hs.neg
  simpa only [sub_eq_add_neg] using this

/-- (5) The Fredholm product is positive when every `λ_n < 1`. -/
theorem dF_tprod_pos {lam : ℕ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (h1 : ∀ n, lam n < 1) (hs : Summable fun n => lam n ^ 2) :
    0 < ∏' n, (1 - lam n ^ 2) := by
  have hpos : ∀ n, 0 < 1 - lam n ^ 2 := fun n => by nlinarith [h0 n, h1 n]
  have hl : Summable fun n => Real.log (1 - lam n ^ 2) := by
    have := Real.summable_log_one_add_of_summable (f := fun n => -(lam n ^ 2)) hs.neg
    simpa only [sub_eq_add_neg] using this
  rw [← Real.rexp_tsum_eq_tprod hpos hl]
  exact Real.exp_pos _

/-- (6, held: uses `remark_2_3`) `T₂` and `T₃` are injective. -/
theorem dF_remark23_ops {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Injective (gopOp (B2 (grunsky (fsans μ) (gsans μ)))) ∧
      Function.Injective (gopOp (B3 (grunsky (fsans μ) (gsans μ)))) := by
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnull := r22_complement_null hμ
  obtain ⟨c, -, -, C, hC⟩ := remark_2_3 hμ
  have hB := gop_grunsky_bounds hpair hnull
  obtain ⟨r2, b2⟩ := hB (B2 (grunsky (fsans μ) (gsans μ))) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  obtain ⟨r3, b3⟩ := hB (B3 (grunsky (fsans μ) (gsans μ)))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have key : ∀ {T : ell2 →L[ℂ] ell2}, (∀ x : ell2, ∑' n, ‖x n‖ ^ 2 ≤ C * ∑' m, ‖T x m‖ ^ 2) →
      Function.Injective T := by
    intro T hT
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 := hT x
    rw [hx] at h1
    simp only [lp.coeFn_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, tsum_zero, mul_zero] at h1
    have h2 : ‖x‖ ^ 2 ≤ 0 := by rw [gop_norm_sq]; exact h1
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (by positivity)))
  refine ⟨key fun x => ?_, key fun x => ?_⟩
  · have h := (hC x (gop_l2_summable x)).2.2.1
    simpa only [gop_apply r2 b2] using h
  · have h := (hC x (gop_l2_summable x)).2.2.2
    simpa only [gop_apply r3 b3] using h

theorem dF_kron_conj (m n : ℕ) : conj (kron m n) = kron m n := by
  unfold kron
  split_ifs <;> simp

/-- (7) Singular value sequences of the conjugate matrix. -/
theorem dF_singular_conj {A : ℕ → ℕ → ℂ} {lam : ℕ → ℝ} (h : IsSingularSeq A lam) :
    IsSingularSeq (fun m n => conj (A m n)) lam := by
  obtain ⟨h0, U, hr, hc, he⟩ := h
  have hm : ∀ m k, mulAdj (fun m n => conj (A m n)) (fun m n => conj (A m n)) m k = conj (mulAdj A A m k) := by
    intro m k
    rw [mulAdj, mulAdj, Complex.conj_tsum]
    exact tsum_congr fun j => by rw [map_mul]
  refine ⟨h0, fun m n => conj (U m n), fun m n => ?_, fun m n => ?_, fun m n => ?_⟩
  · rw [← dF_kron_conj, ← hr m n, mulAdj, mulAdj, Complex.conj_tsum]
    exact tsum_congr fun k => by rw [map_mul]
  · rw [← dF_kron_conj, ← hc m n, Complex.conj_tsum]
    exact tsum_congr fun k => by rw [map_mul]
  · calc (∑' k, mulAdj (fun m n => conj (A m n)) (fun m n => conj (A m n)) m k * conj (U k n))
        = conj (∑' k, mulAdj A A m k * U k n) := by
          rw [Complex.conj_tsum]
          exact tsum_congr fun k => by rw [hm, map_mul]
      _ = ((lam n ^ 2 : ℝ) : ℂ) * conj (U m n) := by rw [he m n, map_mul, Complex.conj_ofReal]

/-- **detF_spec** (TT:4481), byte-identical copy of `detF_spec`. -/
theorem dF_detF_spec {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    (∀ lam, IsSingularSeq (B1 b) lam → IsSingularSeq (B4 b) lam) ∧
      (∀ lam, IsSingularSeq (B1 b) lam → Multipliable (fun n => 1 - lam n ^ 2) ∧ ∏' n, (1 - lam n ^ 2) = detF μ) ∧
      0 < detF μ := by
  intro μ b
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hnull := r22_complement_null hμ
  obtain ⟨hR1, hR4, -, hC1, -, -, hs1, -, hs3⟩ := gop_blocks hpair hnull
  obtain ⟨hr1, hb1⟩ := gop_grunsky_bounds hpair hnull (B1 b) (Set.mem_insert _ _)
  obtain ⟨hr4, hb4⟩ := gop_grunsky_bounds hpair hnull (B4 b)
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  obtain ⟨hi2, hi3⟩ := dF_remark23_ops hμ
  have hHS : Summable fun q : ℕ × ℕ => ‖B1 b q.1 q.2‖ ^ 2 := ((cor_2_9 p).1).mp hp
  have hlt : ∀ lam, IsSingularSeq (B1 b) lam → ∀ n, lam n < 1 := by
    intro lam hl n
    obtain ⟨u, hu⟩ := gop_singular_basis hr1 hb1 hl
    have hsq := dF_lam_lt_one_op hR1 hs3 hi3 (u.orthonormal.ne_zero n) (hu n)
    nlinarith [hl.1 n]
  have hprod : ∀ lam, IsSingularSeq (B1 b) lam → ∏' n, (1 - lam n ^ 2) = detF μ := by
    intro lam hl
    have hex : ∃ lam, IsSingularSeq (B1 b) lam := ⟨lam, hl⟩
    show _ = (if h : ∃ lam, IsSingularSeq (B1 b) lam then ∏' n, (1 - h.choose n ^ 2) else 1)
    rw [dif_pos hex]
    obtain ⟨u, hu⟩ := gop_singular_basis hr1 hb1 hl
    obtain ⟨u', hu'⟩ := gop_singular_basis hr1 hb1 hex.choose_spec
    exact dF_tprod_indep hl.1 hex.choose_spec.1 (dF_sq_summable hr1 hb1 hHS u hu)
      (dF_sq_summable hr1 hb1 hHS u' hu') u u' hu hu'
  refine ⟨fun lam hl => ?_, fun lam hl => ⟨?_, hprod lam hl⟩, ?_⟩
  · obtain ⟨u, hu⟩ := gop_singular_basis hr1 hb1 hl
    obtain ⟨w, hw⟩ := dF_transfer hR4 hC1 hs1 hs3 hi2 hl.1 (hlt lam hl) u hu
    exact gop_basis_singular hr4 hb4 hl.1 w hw
  · obtain ⟨u, hu⟩ := gop_singular_basis hr1 hb1 hl
    exact dF_multipliable (dF_sq_summable hr1 hb1 hHS u hu)
  · by_cases hex : ∃ lam, IsSingularSeq (B1 b) lam
    · obtain ⟨lam, hl⟩ := hex
      rw [← hprod lam hl]
      obtain ⟨u, hu⟩ := gop_singular_basis hr1 hb1 hl
      exact dF_tprod_pos hl.1 (hlt lam hl) (dF_sq_summable hr1 hb1 hHS u hu)
    · show 0 < (if h : ∃ lam, IsSingularSeq (B1 b) lam then ∏' n, (1 - h.choose n ^ 2) else 1)
      rw [dif_neg hex]
      exact one_pos

/-- **(2.13)** (TT:4495), byte-identical copy of `eq_2_13`. -/
theorem dF_eq_2_13 {p : T1} (hp : p ∈ T01) : liouvilleS2 p = liouvilleS2 (invT p) := by
  have hq : invT p ∈ T01 := TakhtajanTeo.lemma_3_4.2.2 p hp
  -- `B₁([μ]⁻¹) = \overline{B₄([μ])}` and `B₁([μ]) = \overline{B₄([μ]⁻¹)}`
  have e1 : B1 (grunsky (fsans (Quotient.out (invT p) : LinfStarBall)) (gsans (Quotient.out (invT p) : LinfStarBall))) =
      fun m n => conj (B4 (grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))) m n) := by
    funext m n
    rw [FB.fb_clause3 p m n, Complex.conj_conj]
    simp only [periodP]
  have e2 : B1 (grunsky (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall))) =
      fun m n => conj (B4 (grunsky (fsans (Quotient.out (invT p) : LinfStarBall))
        (gsans (Quotient.out (invT p) : LinfStarBall))) m n) := by
    funext m n
    rw [FB.fb_clause3 (invT p) m n, Complex.conj_conj]
    show periodP p m n = periodP (invT (invT p)) m n
    rw [grp_invT_invT]
  suffices h : detF (Quotient.out p : LinfStarBall) = detF (Quotient.out (invT p) : LinfStarBall) by
    unfold liouvilleS2; rw [h]
  by_cases hex : ∃ lam, IsSingularSeq (B1 (grunsky (fsans (Quotient.out p : LinfStarBall))
      (gsans (Quotient.out p : LinfStarBall)))) lam
  · obtain ⟨lam, hl⟩ := hex
    have hA := (dF_detF_spec hp).2.1 lam hl
    have hB : IsSingularSeq (B1 (grunsky (fsans (Quotient.out (invT p) : LinfStarBall))
        (gsans (Quotient.out (invT p) : LinfStarBall)))) lam := by
      rw [e1]; exact dF_singular_conj ((dF_detF_spec hp).1 lam hl)
    rw [← hA.2, ← ((dF_detF_spec hq).2.1 lam hB).2]
  · have hex' : ¬ ∃ lam, IsSingularSeq (B1 (grunsky (fsans (Quotient.out (invT p) : LinfStarBall))
        (gsans (Quotient.out (invT p) : LinfStarBall)))) lam := by
      rintro ⟨lam, hl⟩
      apply hex
      refine ⟨lam, ?_⟩
      rw [e2]; exact dF_singular_conj ((dF_detF_spec hq).1 lam hl)
    have h1 : detF (Quotient.out p : LinfStarBall) = 1 := dif_neg hex
    have h2 : detF (Quotient.out (invT p) : LinfStarBall) = 1 := dif_neg hex'
    rw [h1, h2]

/-- (TT:4481) For `[μ] ∈ T₀(1)`:
- `det(I - 𝖪₁) = det(I - 𝖪₄)`, i.e. `B₁` and `B₄` have the same singular values (`Vᵗ B₄ V = -D`);
- the product `∏ (1 - λ_n²)` converges to a positive number;
- it does not depend on the singular value sequence. -/
theorem detF_spec {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    (∀ lam, IsSingularSeq (B1 b) lam → IsSingularSeq (B4 b) lam) ∧
      (∀ lam, IsSingularSeq (B1 b) lam → Multipliable (fun n => 1 - lam n ^ 2) ∧ ∏' n, (1 - lam n ^ 2) = detF μ) ∧
      0 < detF μ :=
  dF_detF_spec hp

/-- **(2.13)** (TT:4495). `S₂([μ]) = S₂([μ]⁻¹)` on `T₀(1)`. -/
theorem eq_2_13 {p : T1} (hp : p ∈ T01) : liouvilleS2 p = liouvilleS2 (invT p) :=
  dF_eq_2_13 hp

end Ch2
end TakhtajanTeo
