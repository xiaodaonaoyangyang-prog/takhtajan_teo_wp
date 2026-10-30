import TakhtajanTeo.Ch2.S2_Grunsky

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real InnerProductSpace
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

namespace S2cL212

theorem inner_star_right (x y : ell2) : inner ℂ x (star y) = inner ℂ y (star x) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp [lp.star_apply, RCLike.inner_apply, mul_comm]

section
variable {T : ell2 →L[ℂ] ell2} (hsym : ∀ x, T x = transposeOp T x)
include hsym

theorem hstar (y : ell2) : star (T y) = ContinuousLinearMap.adjoint T (star y) := by
  have h := hsym y
  unfold transposeOp at h
  rw [h, star_star]

theorem a_eq (u : ell2) : T (star u) = star (ContinuousLinearMap.adjoint T u) := by
  have h := hstar hsym (star u)
  rw [star_star] at h
  rw [← h, star_star]

theorem a_a (u : ell2) : T (star (T (star u))) = T (ContinuousLinearMap.adjoint T u) := by
  rw [a_eq hsym u, star_star]

theorem inner_a (u v : ell2) : inner ℂ (T (star u)) v = inner ℂ (T (star v)) u := by
  rw [a_eq hsym u]
  have h := inner_star_right (star (ContinuousLinearMap.adjoint T u)) (star v)
  rw [star_star, star_star] at h
  rw [h, ContinuousLinearMap.adjoint_inner_right]

theorem norm_a (u : ell2) : ‖T (star u)‖ = ‖ContinuousLinearMap.adjoint T u‖ := by
  rw [a_eq hsym u, norm_star]

theorem inner_P (u : ell2) :
    inner ℂ u (T (ContinuousLinearMap.adjoint T u)) = ((‖T (star u)‖ ^ 2 : ℝ) : ℂ) := by
  rw [← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, norm_a hsym]
  simp

end

theorem a_smul_real (T : ell2 →L[ℂ] ell2) (r : ℝ) (y : ell2) :
    T (star ((r : ℂ) • y)) = (r : ℂ) • T (star y) := by
  rw [star_smul, map_smul]
  simp

theorem a_smul_I (T : ell2 →L[ℂ] ell2) (y : ell2) :
    T (star (Complex.I • y)) = -Complex.I • T (star y) := by
  rw [star_smul, map_smul]
  simp

theorem exists_fixed {T : ell2 →L[ℂ] ell2} (hsym : ∀ x, T x = transposeOp T x)
    (hT : IsCompactOperator T) (W : Submodule ℂ ell2) (hWc : IsClosed (W : Set ell2))
    (hinv : ∀ w ∈ W, T (star w) ∈ W) (hne : ∃ w ∈ W, w ≠ 0) :
    ∃ f ∈ W, f ≠ 0 ∧ ∃ s : ℝ, 0 ≤ s ∧ T (star f) = (s : ℂ) • f := by
  by_cases h0 : ∃ w ∈ W, w ≠ 0 ∧ T (star w) = 0
  · obtain ⟨w, hw, hw0, hwa⟩ := h0
    exact ⟨w, hw, hw0, 0, le_rfl, by simp [hwa]⟩
  push Not at h0
  have : CompleteSpace W := hWc.completeSpace_coe
  set P : ell2 →L[ℂ] ell2 := T * ContinuousLinearMap.adjoint T with hP
  have hPsa : IsSelfAdjoint P := by
    simpa [hP, ContinuousLinearMap.star_eq_adjoint] using IsSelfAdjoint.mul_star_self T
  have hPsym : (P : ell2 →ₗ[ℂ] ell2).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 hPsa
  have hPc : IsCompactOperator P := by
    have := hT.comp_clm (ContinuousLinearMap.adjoint T)
    exact this
  have hPa : ∀ w, P w = T (star (T (star w))) := fun w => (a_a hsym w).symm
  have hPinv : ∀ w ∈ W, P w ∈ W := fun w hw => by
    rw [hPa]; exact hinv _ (hinv w hw)
  let S : W →L[ℂ] W := P.restrict hPinv
  have hSc : IsCompactOperator S := hPc.restrict' hPinv
  have hSs : (S : W →ₗ[ℂ] W).IsSymmetric := hPsym.restrict_invariant hPinv
  have hSne : S ≠ 0 := by
    obtain ⟨w, hw, hw0⟩ := hne
    intro hS0
    have h1 : P w = 0 := by
      have := congrArg (fun A : W →L[ℂ] W => (A ⟨w, hw⟩ : ell2)) hS0
      simpa [S] using this
    have h2 := inner_P hsym w
    have h3 : (P w) = T (ContinuousLinearMap.adjoint T w) := rfl
    rw [← h3, h1, inner_zero_right] at h2
    have h4 : ‖T (star w)‖ ^ 2 = 0 := by exact_mod_cast h2.symm
    have h5 : T (star w) = 0 := by simpa using h4
    exact h0 w hw hw0 h5
  have hex : ∃ μ, Module.End.HasEigenvalue (S : Module.End ℂ W) μ ∧ μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hSne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hSc hSs).1 hcon)
  obtain ⟨μ, hμ, hμ0⟩ := hex
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hSv : S v = μ • v := hv.apply_eq_smul
  have hv0 : (v : ell2) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  set x : ell2 := (v : ell2) with hx
  have hxW : x ∈ W := v.2
  have hPx : P x = μ • x := by
    have := congrArg (fun y : W => (y : ell2)) hSv
    simpa [S] using this
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hv0
  have hn : (((‖T (star x)‖ ^ 2 : ℝ)) : ℂ) = μ * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have h1 := inner_P hsym x
    have h3 : T (ContinuousLinearMap.adjoint T x) = P x := rfl
    rw [h3, hPx, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
    rw [← h1]
    simp
  set s : ℝ := ‖T (star x)‖ / ‖x‖ with hs
  have hμs : μ = (s : ℂ) ^ 2 := by
    have hxc : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hnx 2).ne'
    have : μ = (((‖T (star x)‖ ^ 2 : ℝ)) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      field_simp
      rw [hn]
    rw [this, hs]
    push_cast
    ring
  have hs0 : s ≠ 0 := by
    intro h
    apply hμ0
    rw [hμs, h]
    simp
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsnn : 0 ≤ s := div_nonneg (norm_nonneg _) hnx.le
  have haxW : T (star x) ∈ W := hinv x hxW
  have haax : T (star (T (star x))) = μ • x := by rw [← hPa, hPx]
  have hu : T (star ((s : ℂ) • x + T (star x))) = (s : ℂ) • ((s : ℂ) • x + T (star x)) := by
    rw [star_add, map_add, a_smul_real, haax, hμs]
    module
  have hu' : T (star (Complex.I • ((s : ℂ) • x - T (star x)))) =
      (s : ℂ) • (Complex.I • ((s : ℂ) • x - T (star x))) := by
    rw [a_smul_I, star_sub, map_sub, a_smul_real, haax, hμs]
    module
  have hmem1 : (s : ℂ) • x + T (star x) ∈ W := W.add_mem (W.smul_mem _ hxW) haxW
  have hmem2 : Complex.I • ((s : ℂ) • x - T (star x)) ∈ W :=
    W.smul_mem _ (W.sub_mem (W.smul_mem _ hxW) haxW)
  by_cases h1 : (s : ℂ) • x + T (star x) = 0
  · refine ⟨_, hmem2, ?_, s, hsnn, hu'⟩
    have h2 : T (star x) = -((s : ℂ) • x) := eq_neg_of_add_eq_zero_right h1
    rw [h2]
    intro h3
    have h4 : ((2 * s : ℂ)) • x = 0 := by
      have h5 : (s : ℂ) • x - -((s : ℂ) • x) = 0 := by
        rcases smul_eq_zero.1 h3 with h | h
        · exact absurd h Complex.I_ne_zero
        · exact h
      rw [← h5]; module
    rcases smul_eq_zero.1 h4 with h | h
    · apply hsC
      have : (2 : ℂ) ≠ 0 := two_ne_zero
      simpa [this] using h
    · exact hv0 h
  · exact ⟨_, hmem1, h1, s, hsnn, hu⟩

theorem exists_hilbertBasis_fixed {T : ell2 →L[ℂ] ell2} (hsym : ∀ x, T x = transposeOp T x)
    (hT : IsCompactOperator T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℂ ell2) (s : ι → ℝ), (∀ i, 0 ≤ s i) ∧
      ∀ i, T (star (b i)) = (s i : ℂ) • b i := by
  classical
  let Fix : Set ell2 := {f | ‖f‖ = 1 ∧ ∃ s : ℝ, 0 ≤ s ∧ T (star f) = (s : ℂ) • f}
  have hz := zorn_subset_nonempty
    {S : Set ell2 | S ⊆ Fix ∧ Orthonormal ℂ (Subtype.val : S → ell2)}
    (fun c hc cc _ => ⟨⋃₀ c, ⟨Set.sUnion_subset fun x xc => (hc xc).1,
      orthonormal_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2⟩,
      fun _ => Set.subset_sUnion_of_mem⟩) (∅ : Set ell2)
    ⟨Set.empty_subset _, orthonormal_empty ℂ ell2⟩
  obtain ⟨S, -, hS⟩ := hz
  obtain ⟨⟨hSF, hSo⟩, hSmax⟩ := hS
  have hSmax' : ∀ S' : Set ell2, S' ⊆ Fix → Orthonormal ℂ (Subtype.val : S' → ell2) → S ⊆ S' →
      S' ⊆ S := fun S' h1 h2 h3 => hSmax ⟨h1, h2⟩ h3
  have hOrth : (Submodule.span ℂ (Set.range (Subtype.val : S → ell2)))ᗮ = ⊥ := by
    by_contra hne
    set W := (Submodule.span ℂ (Set.range (Subtype.val : S → ell2)))ᗮ with hW
    have hmemW : ∀ w ∈ W, ∀ f ∈ S, inner ℂ f w = 0 := fun w hw f hf =>
      (Submodule.mem_orthogonal _ _).1 hw f (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)
    have hinv : ∀ w ∈ W, T (star w) ∈ W := by
      intro w hw
      rw [hW, Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨⟨f, hf⟩, rfl⟩ := hu
        obtain ⟨-, s, -, hs⟩ := hSF hf
        have h1 : inner ℂ f (T (star w)) = conj (inner ℂ (T (star w)) f) := (inner_conj_symm _ _).symm
        rw [h1, inner_a hsym w f, hs, inner_smul_left, hmemW w hw f hf]
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hne
    obtain ⟨f, hfW, hf0, s, hs0, hfs⟩ := exists_fixed hsym hT W
      (Submodule.isClosed_orthogonal _) hinv ⟨w, hw, hw0⟩
    have hfn : 0 < ‖f‖ := norm_pos_iff.2 hf0
    set g : ell2 := ((‖f‖⁻¹ : ℝ) : ℂ) • f with hg
    have hgW : g ∈ W := W.smul_mem _ hfW
    have hgn : ‖g‖ = 1 := by
      rw [hg, norm_smul]
      simp [hfn.ne']
    have hgF : g ∈ Fix := by
      refine ⟨hgn, s, hs0, ?_⟩
      rw [hg, a_smul_real, hfs, smul_comm]
    have hgS : g ∉ S := by
      intro hgS
      have h1 := hmemW g hgW g hgS
      rw [inner_self_eq_norm_sq_to_K, hgn] at h1
      simp at h1
    have hins : Orthonormal ℂ (Subtype.val : ↥(insert g S) → ell2) := by
      rw [orthonormal_subtype_iff_ite]
      intro v hv w hw'
      rcases hv with hv | hv <;> rcases hw' with hw' | hw'
      · rw [hv, hw']
        simp [inner_self_eq_norm_sq_to_K, hgn]
      · have h := hmemW g hgW w hw'
        have hne : v ≠ w := fun h' => hgS (hv ▸ h' ▸ hw')
        rw [show (if v = w then (1 : ℂ) else 0) = 0 by simp [hne], hv, ← inner_conj_symm, h, map_zero]
      · have h := hmemW g hgW v hv
        have hne : v ≠ w := fun h' => hgS (hw' ▸ h' ▸ hv)
        rw [show (if v = w then (1 : ℂ) else 0) = 0 by simp [hne], hw', h]
      · exact orthonormal_subtype_iff_ite.1 hSo v hv w hw'
    have := hSmax' (insert g S) (Set.insert_subset hgF hSF) hins (Set.subset_insert _ _)
    exact hgS (this (Set.mem_insert _ _))
  exact ⟨S, HilbertBasis.mkOfOrthogonalEqBot hSo hOrth, fun i => Classical.choose (hSF i.2).2,
    fun i => (Classical.choose_spec (hSF i.2).2).1, fun i => by
      rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
      exact (Classical.choose_spec (hSF i.2).2).2⟩

theorem equiv_nat_of_hilbertBasis {ι : Type} (b : HilbertBasis ι ℂ ell2) : Nonempty (ι ≃ ℕ) := by
  classical
  have hcount : Countable ι := by
    have h2 : ∀ n : ℕ, {i : ι | b i n ≠ 0}.Countable := by
      intro n
      have hs : Summable fun i : ι => ‖inner ℂ (b i) (lp.single 2 n (1 : ℂ))‖ ^ 2 :=
        b.orthonormal.inner_products_summable _
      have := hs.countable_support
      convert this using 1
      ext i
      simp [Function.mem_support, lp.inner_single_right]
    have h3 : (Set.univ : Set ι) ⊆ ⋃ n, {i : ι | b i n ≠ 0} := by
      intro i _
      by_contra hcon
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hcon
      have h0 : b i = 0 := by
        ext n
        simp [hcon n]
      have h1 := b.orthonormal.norm_eq_one i
      rw [h0] at h1
      simp at h1
    exact Set.countable_univ_iff.1 ((Set.countable_iUnion h2).mono h3)
  have hinf : Infinite ι := by
    by_contra hfin
    have hfin' : Finite ι := not_infinite_iff_finite.1 hfin
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have hc : IsClosed (Submodule.span ℂ (Set.range b) : Set ell2) :=
      Submodule.closed_of_finiteDimensional _
    have hspan : Submodule.span ℂ (Set.range b) = ⊤ := by
      have := b.dense_span
      rwa [hc.submodule_topologicalClosure_eq] at this
    have hfd2 : FiniteDimensional ℂ ell2 := by
      have : FiniteDimensional ℂ (⊤ : Submodule ℂ ell2) := by rw [← hspan]; exact hfd
      exact Module.Finite.equiv (Submodule.topEquiv (R := ℂ) (M := ell2))
    have hon : Orthonormal ℂ (fun n : ℕ => (lp.single 2 n (1 : ℂ) : ell2)) := by
      rw [orthonormal_iff_ite]
      intro n m
      rw [lp.inner_single_left]
      by_cases h : n = m
      · subst h; simp
      · simp [lp.single_apply, h]
    have := hon.linearIndependent.finite
    exact not_finite ℕ
  exact nonempty_equiv_of_countable

def transposeCLM (V : ell2 →L[ℂ] ell2) : ell2 →L[ℂ] ell2 :=
  LinearMap.mkContinuous
    { toFun := transposeOp V
      map_add' := fun x y => by simp [transposeOp, star_add]
      map_smul' := fun c x => by simp [transposeOp, star_smul] }
    ‖ContinuousLinearMap.adjoint V‖
    (fun x => by
      show ‖star (ContinuousLinearMap.adjoint V (star x))‖ ≤ _
      rw [norm_star]
      simpa using (ContinuousLinearMap.adjoint V).le_opNorm (star x))

theorem transposeCLM_apply (V : ell2 →L[ℂ] ell2) (x : ell2) :
    transposeCLM V x = transposeOp V x := rfl

theorem lemma_2_12_aux {T : ell2 →L[ℂ] ell2} (hT : IsCompactOperator T)
    (hsym : ∀ x, T x = transposeOp T x) :
    ∃ U : ell2 →L[ℂ] ell2, U ∈ unitary (ell2 →L[ℂ] ell2) ∧ ∃ D : ell2 →L[ℂ] ell2, ∃ d : ℕ → ℝ,
      (∀ n, 0 ≤ d n) ∧ (∀ x n, D x n = d n * x n) ∧ ∀ x, T x = U (D (transposeOp U x)) := by
  classical
  obtain ⟨ι, b, s, hs0, hs⟩ := exists_hilbertBasis_fixed hsym hT
  obtain ⟨e⟩ := equiv_nat_of_hilbertBasis b
  let v : ℕ → ell2 := fun n => b (e.symm n)
  have hv : Orthonormal ℂ v := b.orthonormal.comp _ e.symm.injective
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    have : Set.range v = Set.range b := e.symm.surjective.range_comp _
    rw [this]
    exact b.dense_span.ge
  let b' : HilbertBasis ℕ ℂ ell2 := HilbertBasis.mk hv hsp
  have hb' : ∀ n, b' n = v n := fun n => by rw [HilbertBasis.coe_mk]
  let Ue : ell2 ≃ₗᵢ[ℂ] ell2 := b'.repr.symm
  have hUe : ∀ n, Ue (lp.single 2 n (1 : ℂ)) = v n := fun n => by
    rw [← hb']
    exact b'.repr_symm_single n
  have hUu : (Ue : ell2 →L[ℂ] ell2) ∈ unitary (ell2 →L[ℂ] ell2) :=
    (Unitary.linearIsometryEquiv.symm Ue).2
  set U : ell2 →L[ℂ] ell2 := (Ue : ell2 →L[ℂ] ell2) with hU
  have hUU : ∀ y, U (ContinuousLinearMap.adjoint U y) = y := fun y => by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A y) (Unitary.mul_star_self_of_mem hUu)
    simpa [ContinuousLinearMap.star_eq_adjoint] using h
  have hUU' : ∀ y, ContinuousLinearMap.adjoint U (U y) = y := fun y => by
    have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A y) (Unitary.star_mul_self_of_mem hUu)
    simpa [ContinuousLinearMap.star_eq_adjoint] using h
  let Vt : ell2 →L[ℂ] ell2 := transposeCLM (ContinuousLinearMap.adjoint U)
  have hVt : ∀ y, Vt y = star (U (star y)) := fun y => by
    simp [Vt, transposeCLM_apply, transposeOp]
  let D : ell2 →L[ℂ] ell2 := (ContinuousLinearMap.adjoint U).comp (T.comp Vt)
  refine ⟨U, hUu, D, fun n => s (e.symm n), fun n => hs0 _, ?_, ?_⟩
  · intro x n
    have hn : ∀ y : ell2, y n = inner ℂ (lp.single 2 n (1 : ℂ)) y := fun y => by
      rw [lp.inner_single_left]; simp
    have hfn : T (star (v n)) = (s (e.symm n) : ℂ) • v n := hs (e.symm n)
    set y : ell2 := U (star x) with hy
    have hD : D x = ContinuousLinearMap.adjoint U (T (star y)) := by
      show ContinuousLinearMap.adjoint U (T (Vt x)) = _
      rw [hVt]
    have h2 : inner ℂ y (v n) = x n := by
      rw [← hUe n, hy]
      show inner ℂ (U (star x)) (U (lp.single 2 n 1)) = x n
      rw [ContinuousLinearMap.inner_map_map_of_mem_unitary hUu, lp.inner_single_right]
      simp [lp.star_apply]
    have h3 : U (lp.single 2 n (1 : ℂ)) = v n := hUe n
    rw [hn (D x), hD, ContinuousLinearMap.adjoint_inner_right, h3]
    calc inner ℂ (v n) (T (star y)) = conj (inner ℂ (T (star y)) (v n)) := (inner_conj_symm _ _).symm
      _ = conj (inner ℂ (T (star (v n))) y) := by rw [inner_a hsym y (v n)]
      _ = ((s (e.symm n) : ℝ) : ℂ) * x n := by
        rw [hfn, inner_smul_left, ← h2]
        simp
  · intro x
    have h1 : Vt (transposeOp U x) = x := by
      rw [hVt]
      simp only [transposeOp, star_star, hUU, star_star]
    show T x = U (ContinuousLinearMap.adjoint U (T (Vt (transposeOp U x))))
    rw [h1, hUU]

end S2cL212

/-- **Lemma 2.12** (Schur, TT:4298–4302). A compact operator `T` on `ℓ²`, symmetric with respect to `J` (`T = Tᵗ`),
can be written as `T = U D Uᵗ`. Here `U` is unitary and `D ≥ 0` is diagonal in the standard basis
(`(Dx)_n = d_n x_n`, `d_n ≥ 0`). 
Proved here as `s2c_lemma_2_12`; statement identical to `lemma_2_12`. -/
theorem s2c_lemma_2_12 {T : ell2 →L[ℂ] ell2} (hT : IsCompactOperator T) (hsym : ∀ x, T x = transposeOp T x) :
    ∃ U : ell2 →L[ℂ] ell2, U ∈ unitary (ell2 →L[ℂ] ell2) ∧ ∃ D : ell2 →L[ℂ] ell2, ∃ d : ℕ → ℝ, (∀ n, 0 ≤ d n) ∧
      (∀ x n, D x n = d n * x n) ∧ ∀ x, T x = U (D (transposeOp U x)) := by
  exact S2cL212.lemma_2_12_aux hT hsym

/-! ### Original relocated (2026-10-26) -/

/-- **Lemma 2.12** (Schur, TT:4298–4302). A compact operator `T` on `ℓ²`, symmetric with respect to `J` (`T = Tᵗ`),
can be written as `T = U D Uᵗ`. Here `U` is unitary and `D ≥ 0` is diagonal in the standard basis
(`(Dx)_n = d_n x_n`, `d_n ≥ 0`). -/
theorem lemma_2_12 {T : ell2 →L[ℂ] ell2} (hT : IsCompactOperator T) (hsym : ∀ x, T x = transposeOp T x) :
    ∃ U : ell2 →L[ℂ] ell2, U ∈ unitary (ell2 →L[ℂ] ell2) ∧ ∃ D : ell2 →L[ℂ] ell2, ∃ d : ℕ → ℝ, (∀ n, 0 ≤ d n) ∧
      (∀ x n, D x n = d n * x n) ∧ ∀ x, T x = U (D (transposeOp U x)) :=
  s2c_lemma_2_12 hT hsym

end Ch2

end TakhtajanTeo
