import TakhtajanTeo.Ch2.S3FredholmVariation

/-! # The actual Hilbert--Schmidt ideal and trace calculus -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- The Hilbert space of square-summable matrices. -/
abbrev s3tc_HS := lp (fun _ : ℕ × ℕ => ℂ) 2

theorem s3tc_summable (A : s3tc_HS) : Summable (fun q : ℕ × ℕ => ‖A q‖^2) :=
  s3fv_sum_hs (lp.memℓp A)

/-- An actual column in ℓ², with its membership proof. -/
def s3tc_col (A : s3tc_HS) (n : ℕ) : ell2 :=
  ⟨fun m => A (m,n),gop_mem_of_summable ((s3tc_summable A).prod_symm.prod_factor n)⟩

theorem s3tc_col_apply (A : s3tc_HS) (m n : ℕ) : s3tc_col A n m = A (m,n) := rfl

theorem s3tc_col_add (A B : s3tc_HS) (n : ℕ) : s3tc_col (A+B) n = s3tc_col A n+s3tc_col B n := by
  ext m
  rfl

theorem s3tc_col_smul (c : ℂ) (A : s3tc_HS) (n : ℕ) : s3tc_col (c • A) n = c • s3tc_col A n := by
  ext m
  rfl

theorem s3tc_columns (A : s3tc_HS) : Summable (fun n => ‖s3tc_col A n‖^2) ∧
    (∑' n, ‖s3tc_col A n‖^2) = ‖A‖^2 := by
  have he (n : ℕ) : ‖s3tc_col A n‖^2 = ∑' m, ‖A (m,n)‖^2 := gop_norm_sq _
  have hs := (s3tc_summable A).prod_symm
  refine ⟨hs.prod.congr (fun n => (he n).symm),?_⟩
  rw [s3fv_lp_norm_sq]
  calc
    _ = ∑' n, ∑' m, ‖A (m,n)‖^2 := tsum_congr he
    _ = ∑' m, ∑' n, ‖A (m,n)‖^2 := (s3tc_summable A).tsum_comm
    _ = _ := (s3tc_summable A).tsum_prod.symm

theorem s3tc_left_summable (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    Summable (fun q : ℕ × ℕ => ‖T (s3tc_col A q.2) q.1‖^2) := by
  have hb (n : ℕ) : ‖T (s3tc_col A n)‖^2 ≤ ‖T‖^2*‖s3tc_col A n‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
  have hn : Summable (fun n => ‖T (s3tc_col A n)‖^2) :=
    ((s3tc_columns A).1.mul_left (‖T‖^2)).of_nonneg_of_le (fun _ => sq_nonneg _) hb
  have hs : Summable (fun q : ℕ × ℕ => ‖T (s3tc_col A q.1) q.2‖^2) := by
    have hnonneg : (0 : ℕ × ℕ → ℝ) ≤ (fun q : ℕ × ℕ => ‖T (s3tc_col A q.1) q.2‖^2) :=
      fun q => sq_nonneg _
    apply (summable_prod_of_nonneg hnonneg).mpr
    exact ⟨fun n => gop_l2_summable (T (s3tc_col A n)),hn.congr (fun n => gop_norm_sq (T (s3tc_col A n)))⟩
  exact hs.prod_symm

/-- Bounded left multiplication, defined on genuine columns. -/
def s3tc_left (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) : s3tc_HS :=
  ⟨fun q => T (s3tc_col A q.2) q.1,s3fv_mem_hs (s3tc_left_summable T A)⟩

theorem s3tc_left_apply (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) (m n : ℕ) :
    s3tc_left T A (m,n) = T (s3tc_col A n) m := rfl

theorem s3tc_left_norm (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) : ‖s3tc_left T A‖ ≤ ‖T‖*‖A‖ := by
  have hc (n : ℕ) : s3tc_col (s3tc_left T A) n = T (s3tc_col A n) := by ext m; rfl
  have hnorm : ‖s3tc_left T A‖^2 ≤ ‖T‖^2*‖A‖^2 := by
    rw [← (s3tc_columns (s3tc_left T A)).2,← (s3tc_columns A).2,← tsum_mul_left]
    apply (s3tc_columns (s3tc_left T A)).1.tsum_le_tsum _ ((s3tc_columns A).1.mul_left _)
    intro n
    rw [hc]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
  nlinarith [norm_nonneg (s3tc_left T A),mul_nonneg (norm_nonneg T) (norm_nonneg A)]

/-- Left multiplication as a continuous linear operator on HS matrices. -/
def s3tc_leftCLM (T : ell2 →L[ℂ] ell2) : s3tc_HS →L[ℂ] s3tc_HS :=
  LinearMap.mkContinuous
    { toFun := s3tc_left T
      map_add' := fun A B => by
        ext q
        simp only [s3tc_left,s3tc_col_add,map_add,lp.coeFn_add,Pi.add_apply]
      map_smul' := fun c A => by
        ext q
        simp only [s3tc_left,s3tc_col_smul,map_smul,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply] }
    ‖T‖ (s3tc_left_norm T)

theorem s3tc_leftCLM_apply (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) : s3tc_leftCLM T A = s3tc_left T A := rfl

theorem s3tc_leftCLM_norm (T : ell2 →L[ℂ] ell2) : ‖s3tc_leftCLM T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (s3tc_left_norm T)

/-- The continuous bilinear left action of bounded operators on the HS ideal. -/
def s3tc_leftAction : (ell2 →L[ℂ] ell2) →L[ℂ] s3tc_HS →L[ℂ] s3tc_HS :=
  LinearMap.mkContinuous
    { toFun := s3tc_leftCLM
      map_add' := fun S T => by ext A q; rfl
      map_smul' := fun c T => by ext A q; rfl }
    1 (fun T => by simpa only [one_mul] using! s3tc_leftCLM_norm T)

theorem s3tc_leftAction_apply (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_leftAction T A = s3tc_left T A := rfl

theorem s3tc_bounded (A : s3tc_HS) : IsBoundedMat (fun m n => A (m,n)) :=
  (s3fv_hs_operator (A := fun m n => A (m,n)) (s3tc_summable A)).1

theorem s3tc_op_norm (A : s3tc_HS) : ‖gopOp (fun m n => A (m,n))‖ ≤ ‖A‖ := by
  have h := (s3fv_hs_operator (A := fun m n => A (m,n)) (s3tc_summable A)).2
  rw [← s3fv_lp_norm_sq,Real.sqrt_sq (norm_nonneg A)] at h
  exact h

/-- The canonical inclusion of HS matrices into bounded operators. -/
def s3tc_toOperator : s3tc_HS →L[ℂ] (ell2 →L[ℂ] ell2) :=
  LinearMap.mkContinuous
    { toFun := fun A => gopOp (fun m n => A (m,n))
      map_add' := fun A B => by
        apply gop_ext
        intro m n
        rw [pmb_entry (s3tc_bounded (A+B))]
        simp only [ContinuousLinearMap.add_apply,lp.coeFn_add,Pi.add_apply,
          pmb_entry (s3tc_bounded A),pmb_entry (s3tc_bounded B)]
      map_smul' := fun c A => by
        apply gop_ext
        intro m n
        rw [pmb_entry (s3tc_bounded (c • A))]
        simp only [ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply,
          pmb_entry (s3tc_bounded A)] }
    1 (fun A => by simpa only [one_mul] using! s3tc_op_norm A)

theorem s3tc_toOperator_apply (A : s3tc_HS) : s3tc_toOperator A = gopOp (fun m n => A (m,n)) := rfl

theorem s3tc_toOperator_entry (A : s3tc_HS) (m n : ℕ) :
    s3tc_toOperator A (lp.single 2 n 1 : ell2) m = A (m,n) := pmb_entry (s3tc_bounded A) m n

theorem s3tc_toOperator_col (A : s3tc_HS) (n : ℕ) :
    s3tc_toOperator A (lp.single 2 n 1 : ell2) = s3tc_col A n := by
  ext m
  exact s3tc_toOperator_entry A m n

theorem s3tc_toOperator_injective : Function.Injective s3tc_toOperator := by
  intro A B h
  ext q
  rw [← s3tc_toOperator_entry A q.1 q.2,← s3tc_toOperator_entry B q.1 q.2,h]

theorem s3tc_left_operator (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_toOperator (s3tc_left T A) = T*s3tc_toOperator A := by
  apply gop_ext
  intro m n
  rw [s3tc_toOperator_entry,ContinuousLinearMap.mul_apply,s3tc_toOperator_col]
  rfl

/-- Transposition is a complex-linear Hilbert isometry on HS matrices. -/
def s3tc_transpose : s3tc_HS ≃ₗᵢ[ℂ] s3tc_HS :=
  { toFun := fun A => ⟨fun q => A (q.2,q.1),s3fv_mem_hs (s3tc_summable A).prod_symm⟩
    invFun := fun A => ⟨fun q => A (q.2,q.1),s3fv_mem_hs (s3tc_summable A).prod_symm⟩
    left_inv := fun A => by ext q; rfl
    right_inv := fun A => by ext q; rfl
    map_add' := fun A B => by ext q; rfl
    map_smul' := fun c A => by ext q; rfl
    norm_map' := fun A => by
      have h : ‖(⟨fun q => A (q.2,q.1),s3fv_mem_hs (s3tc_summable A).prod_symm⟩ : s3tc_HS)‖^2 = ‖A‖^2 := by
        rw [s3fv_lp_norm_sq,s3fv_lp_norm_sq]
        exact (Equiv.prodComm ℕ ℕ).tsum_eq (fun q => ‖A q‖^2)
      change ‖(⟨fun q => A (q.2,q.1),s3fv_mem_hs (s3tc_summable A).prod_symm⟩ : s3tc_HS)‖ = ‖A‖
      nlinarith [norm_nonneg A,norm_nonneg (⟨fun q => A (q.2,q.1),s3fv_mem_hs (s3tc_summable A).prod_symm⟩ : s3tc_HS)] }

theorem s3tc_transpose_apply (A : s3tc_HS) (m n : ℕ) : s3tc_transpose A (m,n) = A (n,m) := rfl

theorem s3tc_transposeOp_entry (T : ell2 →L[ℂ] ell2) (m n : ℕ) :
    S2cL212.transposeCLM T (lp.single 2 n 1 : ell2) m = T (lp.single 2 m 1 : ell2) n := by
  have hs : star (lp.single 2 n 1 : ell2) = lp.single 2 n 1 := by
    ext k
    simp [lp.star_apply,lp.single_apply,Pi.single_apply]
  have ha : ContinuousLinearMap.adjoint T (lp.single 2 n 1 : ell2) m =
      conj (T (lp.single 2 m 1 : ell2) n) := by
    rw [← gop_inner_single_left,ContinuousLinearMap.adjoint_inner_right,lp.inner_single_right,
      gop_inner_apply,mul_one]
  rw [S2cL212.transposeCLM_apply,transposeOp,hs]
  change conj (ContinuousLinearMap.adjoint T (lp.single 2 n 1 : ell2) m) = _
  rw [ha,Complex.conj_conj]

theorem s3tc_transposeOp_norm (T : ell2 →L[ℂ] ell2) : ‖S2cL212.transposeCLM T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖star (ContinuousLinearMap.adjoint T (star x))‖ ≤ _
  rw [norm_star]
  have h := (ContinuousLinearMap.adjoint T).le_opNorm (star x)
  simpa only [norm_star,LinearIsometryEquiv.norm_map] using h

/-- Transposition of bounded operators, as an actual continuous linear map. -/
def s3tc_transposeOperator : (ell2 →L[ℂ] ell2) →L[ℂ] (ell2 →L[ℂ] ell2) :=
  LinearMap.mkContinuous
    { toFun := S2cL212.transposeCLM
      map_add' := fun T U => by
        apply gop_ext
        intro m n
        simp only [s3tc_transposeOp_entry,ContinuousLinearMap.add_apply,lp.coeFn_add,Pi.add_apply]
      map_smul' := fun c T => by
        apply gop_ext
        intro m n
        simp only [s3tc_transposeOp_entry,ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply] }
    1 (fun T => by simpa only [one_mul] using! s3tc_transposeOp_norm T)

theorem s3tc_transposeOperator_entry (T : ell2 →L[ℂ] ell2) (m n : ℕ) :
    s3tc_transposeOperator T (lp.single 2 n 1 : ell2) m = T (lp.single 2 m 1 : ell2) n := s3tc_transposeOp_entry T m n

/-- Right multiplication on the actual HS matrix space. -/
def s3tc_rightCLM (T : ell2 →L[ℂ] ell2) : s3tc_HS →L[ℂ] s3tc_HS :=
  (s3tc_transpose : s3tc_HS →L[ℂ] s3tc_HS).comp
    ((s3tc_leftAction (s3tc_transposeOperator T)).comp (s3tc_transpose : s3tc_HS →L[ℂ] s3tc_HS))

theorem s3tc_right_apply (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) (m n : ℕ) :
    s3tc_rightCLM T A (m,n) = s3tc_transposeOperator T (s3tc_col (s3tc_transpose A) m) n := rfl

theorem s3tc_right_norm (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) : ‖s3tc_rightCLM T A‖ ≤ ‖T‖*‖A‖ := by
  change ‖s3tc_transpose (s3tc_left (s3tc_transposeOperator T) (s3tc_transpose A))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply (s3tc_left_norm _ _).trans
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right (s3tc_transposeOp_norm T) (norm_nonneg A)

/-- The continuous bilinear right action, curried in the bounded-operator factor. -/
def s3tc_rightAction : (ell2 →L[ℂ] ell2) →L[ℂ] s3tc_HS →L[ℂ] s3tc_HS :=
  LinearMap.mkContinuous
    { toFun := s3tc_rightCLM
      map_add' := fun T U => by
        ext A q
        rcases q with ⟨m,n⟩
        simp only [s3tc_right_apply,map_add,ContinuousLinearMap.add_apply,lp.coeFn_add,Pi.add_apply]
      map_smul' := fun c T => by
        ext A q
        rcases q with ⟨m,n⟩
        simp only [s3tc_right_apply,map_smul,ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply] }
    1 (fun T => by
      change ‖s3tc_rightCLM T‖ ≤ 1*‖T‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (s3tc_right_norm T))

theorem s3tc_rightAction_apply (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_rightAction T A = s3tc_rightCLM T A := rfl

theorem s3tc_right_operator (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_toOperator (s3tc_rightCLM T A) = s3tc_toOperator A*T := by
  apply gop_ext
  intro m n
  rw [s3tc_toOperator_entry,s3tc_right_apply,ContinuousLinearMap.mul_apply,
    gop_clm_apply (s3tc_transposeOperator T),gop_clm_apply (s3tc_toOperator A)]
  simp_rw [s3tc_transposeOperator_entry,s3tc_col_apply,s3tc_transpose_apply,s3tc_toOperator_entry]
  exact tsum_congr (fun k => mul_comm _ _)

/-- The left and right HS actions commute, as their actual operator products do. -/
theorem s3tc_left_right (T U : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left T (s3tc_rightCLM U A) = s3tc_rightCLM U (s3tc_left T A) := by
  apply s3tc_toOperator_injective
  rw [s3tc_left_operator,s3tc_right_operator,s3tc_right_operator,s3tc_left_operator,mul_assoc]

theorem s3tc_left_mul (T U : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_left (T*U) A = s3tc_left T (s3tc_left U A) := by
  apply s3tc_toOperator_injective
  rw [s3tc_left_operator,s3tc_left_operator,s3tc_left_operator,mul_assoc]

theorem s3tc_right_mul (T U : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_rightCLM (T*U) A = s3tc_rightCLM U (s3tc_rightCLM T A) := by
  apply s3tc_toOperator_injective
  rw [s3tc_right_operator,s3tc_right_operator,s3tc_right_operator,mul_assoc]

theorem s3tc_col_left (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) (n : ℕ) :
    s3tc_col (s3tc_left T A) n = T (s3tc_col A n) := by ext m; rfl

theorem s3tc_inner_columns (A B : s3tc_HS) :
    inner ℂ A B = ∑' n, inner ℂ (s3tc_col A n) (s3tc_col B n) := by
  have hs := lp.summable_inner (𝕜 := ℂ) A B
  rw [lp.inner_eq_tsum]
  calc
    _ = ∑' m, ∑' n, inner ℂ (A (m,n)) (B (m,n)) := hs.tsum_prod
    _ = ∑' n, ∑' m, inner ℂ (A (m,n)) (B (m,n)) :=
      (Summable.tsum_comm (f := fun m n => inner ℂ (A (m,n)) (B (m,n))) hs).symm
    _ = _ := tsum_congr (fun n => (lp.inner_eq_tsum (s3tc_col A n) (s3tc_col B n)).symm)

theorem s3tc_left_inner (T : ell2 →L[ℂ] ell2) (A B : s3tc_HS) :
    inner ℂ B (s3tc_left T A) = inner ℂ (s3tc_left (star T) B) A := by
  rw [s3tc_inner_columns,s3tc_inner_columns]
  apply tsum_congr
  intro n
  rw [s3tc_col_left,s3tc_col_left]
  exact (ContinuousLinearMap.adjoint_inner_left T _ _).symm

/-- Conjugate transposition in the actual matrix Hilbert space. -/
def s3tc_adjoint (A : s3tc_HS) : s3tc_HS := star (s3tc_transpose A)

theorem s3tc_adjoint_apply (A : s3tc_HS) (m n : ℕ) : s3tc_adjoint A (m,n) = conj (A (n,m)) := rfl

theorem s3tc_adjoint_norm (A : s3tc_HS) : ‖s3tc_adjoint A‖ = ‖A‖ := by
  rw [s3tc_adjoint,norm_star,LinearIsometryEquiv.norm_map]

theorem s3tc_adjoint_operator (A : s3tc_HS) : s3tc_toOperator (s3tc_adjoint A) = star (s3tc_toOperator A) := by
  apply gop_ext
  intro m n
  rw [s3tc_toOperator_entry,s3tc_adjoint_apply]
  change _ = ContinuousLinearMap.adjoint (gopOp (fun i j => A (i,j))) (lp.single 2 n 1 : ell2) m
  rw [gop_adjoint_apply (isBoundedMat_row_isL2 (s3tc_bounded A)) (pmb_partial_bound (s3tc_bounded A)),gop_tsum_single]

theorem s3tc_adjoint_adjoint (A : s3tc_HS) : s3tc_adjoint (s3tc_adjoint A) = A := by
  ext q
  rcases q with ⟨m,n⟩
  rw [s3tc_adjoint_apply,s3tc_adjoint_apply,Complex.conj_conj]

theorem s3tc_adjoint_right (T : ell2 →L[ℂ] ell2) (A : s3tc_HS) :
    s3tc_adjoint (s3tc_rightCLM T A) = s3tc_left (star T) (s3tc_adjoint A) := by
  apply s3tc_toOperator_injective
  rw [s3tc_adjoint_operator,s3tc_right_operator,star_mul,s3tc_left_operator,s3tc_adjoint_operator]

/-- Trace of a product of two HS matrices, represented by the Hilbert pairing. -/
def s3tc_trace (A B : s3tc_HS) : ℂ := inner ℂ (s3tc_adjoint B) A

theorem s3tc_trace_eq_sum (A B : s3tc_HS) : s3tc_trace A B = ∑' q : ℕ × ℕ, B (q.2,q.1)*A q := by
  rw [s3tc_trace,lp.inner_eq_tsum]
  apply tsum_congr
  rintro ⟨m,n⟩
  rw [gop_inner_apply,s3tc_adjoint_apply,Complex.conj_conj]

theorem s3tc_trace_norm (A B : s3tc_HS) : ‖s3tc_trace A B‖ ≤ ‖A‖*‖B‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (s3tc_adjoint B) A
  rw [s3tc_adjoint_norm,mul_comm] at h
  exact h

/-- This Hilbert pairing is the absolutely convergent actual operator diagonal trace. -/
theorem s3tc_trace_diagonal (A B : s3tc_HS) :
    Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2)
      ((s3tc_toOperator A*s3tc_toOperator B) (lp.single 2 m 1))) ∧
      (∑' m, inner ℂ (lp.single 2 m 1 : ell2)
        ((s3tc_toOperator A*s3tc_toOperator B) (lp.single 2 m 1))) = s3tc_trace A B := by
  have h := s3fv_trace_pair (A := fun m n => A (m,n)) (B := fun m n => s3tc_adjoint B (m,n))
    (s3tc_summable A) (s3tc_summable (s3tc_adjoint B))
  change Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2)
      ((s3tc_toOperator A*star (s3tc_toOperator (s3tc_adjoint B))) (lp.single 2 m 1))) ∧ _ at h
  rw [s3tc_adjoint_operator,star_star] at h
  refine ⟨h.1,?_⟩
  have he := h.2.1
  change (∑' m, inner ℂ (lp.single 2 m 1 : ell2)
    ((s3tc_toOperator A*star (s3tc_toOperator (s3tc_adjoint B))) (lp.single 2 m 1))) = _ at he
  rw [s3tc_adjoint_operator,star_star] at he
  rw [he,s3tc_trace,lp.inner_eq_tsum]
  exact tsum_congr (fun q => (gop_inner_apply _ _).symm)

theorem s3tc_trace_cyclic (A B : s3tc_HS) : s3tc_trace A B = s3tc_trace B A := by
  rw [s3tc_trace_eq_sum,s3tc_trace_eq_sum]
  calc
    _ = ∑' q : ℕ × ℕ, B q*A (q.2,q.1) :=
      ((Equiv.prodComm ℕ ℕ).tsum_eq (fun q : ℕ × ℕ => B (q.2,q.1)*A q)).symm
    _ = _ := tsum_congr (fun q => mul_comm _ _)

/-- Cyclicity with a bounded factor, proved through the HS adjoint identity. -/
theorem s3tc_trace_left_right (T : ell2 →L[ℂ] ell2) (A B : s3tc_HS) :
    s3tc_trace (s3tc_left T A) B = s3tc_trace A (s3tc_rightCLM T B) := by
  rw [s3tc_trace,s3tc_trace,s3tc_left_inner,s3tc_adjoint_right]

theorem s3tc_trace_add_left (A B C : s3tc_HS) : s3tc_trace (A+B) C = s3tc_trace A C+s3tc_trace B C :=
  inner_add_right _ _ _

theorem s3tc_trace_smul_left (c : ℂ) (A B : s3tc_HS) : s3tc_trace (c • A) B = c*s3tc_trace A B :=
  inner_smul_right _ _ _

theorem s3tc_trace_add_right (A B C : s3tc_HS) : s3tc_trace A (B+C) = s3tc_trace A B+s3tc_trace A C := by
  rw [s3tc_trace_cyclic,s3tc_trace_add_left,s3tc_trace_cyclic B A,s3tc_trace_cyclic C A]

theorem s3tc_trace_smul_right (c : ℂ) (A B : s3tc_HS) : s3tc_trace A (c • B) = c*s3tc_trace A B := by
  rw [s3tc_trace_cyclic,s3tc_trace_smul_left,s3tc_trace_cyclic B A]

def s3tc_traceCLM (A : s3tc_HS) : s3tc_HS →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := s3tc_trace A
      map_add' := s3tc_trace_add_right A
      map_smul' := fun c B => s3tc_trace_smul_right c A B }
    ‖A‖ (s3tc_trace_norm A)

/-- The continuous bilinear trace pairing on two HS factors. -/
def s3tc_tracePair : s3tc_HS →L[ℂ] s3tc_HS →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := s3tc_traceCLM
      map_add' := fun A B => by ext C; exact s3tc_trace_add_left A B C
      map_smul' := fun c A => by ext B; exact s3tc_trace_smul_left c A B }
    1 (fun A => by
      change ‖s3tc_traceCLM A‖ ≤ 1*‖A‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (s3tc_trace_norm A))

theorem s3tc_tracePair_apply (A B : s3tc_HS) : s3tc_tracePair A B = s3tc_trace A B := rfl

theorem s3tc_trace_gram_pair (A B : s3tc_HS) : s3tc_trace A (s3tc_adjoint B) = inner ℂ B A := by
  rw [s3tc_trace,s3tc_adjoint_adjoint]

/-- Every positive Gram power has a genuinely summable diagonal trace,
expressed through the bounded left action on the HS factor. -/
theorem s3tc_gram_power_trace (A : s3tc_HS) (N : ℕ) :
    let K := s3tc_toOperator A*star (s3tc_toOperator A)
    Summable (fun m => inner ℂ (lp.single 2 m 1 : ell2) ((K^(N+1)) (lp.single 2 m 1))) ∧
      (∑' m, inner ℂ (lp.single 2 m 1 : ell2) ((K^(N+1)) (lp.single 2 m 1))) =
        inner ℂ A (s3tc_left (K^N) A) := by
  intro K
  have he : s3tc_toOperator (s3tc_left (K^N) A)*s3tc_toOperator (s3tc_adjoint A) = K^(N+1) := by
    rw [s3tc_left_operator,s3tc_adjoint_operator,mul_assoc,← pow_succ]
  have h := s3tc_trace_diagonal (s3tc_left (K^N) A) (s3tc_adjoint A)
  rw [he,s3tc_trace_gram_pair] at h
  exact h

/-- Uniform spectral-gap majorant for every Gram trace moment. -/
theorem s3tc_gram_moment_bound (A : s3tc_HS) {c : ℝ} (hc : 0 ≤ c)
    (hA : ‖s3tc_toOperator A‖ ≤ c) (N : ℕ) :
    ‖inner ℂ A (s3tc_left ((s3tc_toOperator A*star (s3tc_toOperator A))^N) A)‖ ≤
      ‖A‖^2*(c^2)^N := by
  let K := s3tc_toOperator A*star (s3tc_toOperator A)
  have hstar : ‖star (s3tc_toOperator A)‖ = ‖s3tc_toOperator A‖ := by
    change ‖ContinuousLinearMap.adjoint (s3tc_toOperator A)‖ = _
    exact LinearIsometryEquiv.norm_map _ _
  have hk : ‖K‖ ≤ c^2 := by
    have h := norm_mul_le (s3tc_toOperator A) (star (s3tc_toOperator A))
    rw [hstar] at h
    dsimp only [K]
    nlinarith [norm_nonneg (s3tc_toOperator A)]
  have hp : ∀ n : ℕ, ‖K^n‖ ≤ (c^2)^n := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using! (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := ell2))
    | succ n ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hk (norm_nonneg _) (pow_nonneg (sq_nonneg c) n))
  calc
    ‖inner ℂ A (s3tc_left (K^N) A)‖ ≤ ‖A‖*‖s3tc_left (K^N) A‖ := norm_inner_le_norm _ _
    _ ≤ ‖A‖*(‖K^N‖*‖A‖) := mul_le_mul_of_nonneg_left (s3tc_left_norm _ _) (norm_nonneg A)
    _ ≤ ‖A‖*((c^2)^N*‖A‖) := by gcongr; exact hp N
    _ = ‖A‖^2*(c^2)^N := by ring

theorem s3tc_right_one (A : s3tc_HS) : s3tc_rightCLM 1 A = A := by
  apply s3tc_toOperator_injective
  rw [s3tc_right_operator,mul_one]

/-- The actual diagonal trace of two HS factors is unchanged in any Hilbert basis. -/
theorem s3tc_trace_basis (A B : s3tc_HS) (u : HilbertBasis ℕ ℂ ell2) :
    Summable (fun n => inner ℂ (u n) ((s3tc_toOperator A*s3tc_toOperator B) (u n))) ∧
      (∑' n, inner ℂ (u n) ((s3tc_toOperator A*s3tc_toOperator B) (u n))) = s3tc_trace A B := by
  let U : ell2 →L[ℂ] ell2 := (u.repr.symm : ell2 →L[ℂ] ell2)
  have hUe (n : ℕ) : U (lp.single 2 n 1 : ell2) = u n := u.repr_symm_single n
  have hUu : U ∈ unitary (ell2 →L[ℂ] ell2) := (Unitary.linearIsometryEquiv.symm u.repr.symm).2
  have hUU : U*star U = 1 := Unitary.mul_star_self_of_mem hUu
  let A' := s3tc_left (star U) A
  let B' := s3tc_rightCLM U B
  have hop : s3tc_toOperator A'*s3tc_toOperator B' =
      star U*((s3tc_toOperator A*s3tc_toOperator B)*U) := by
    dsimp only [A',B']
    rw [s3tc_left_operator,s3tc_right_operator]
    simp only [mul_assoc]
  have he (n : ℕ) : inner ℂ (lp.single 2 n 1 : ell2)
      ((s3tc_toOperator A'*s3tc_toOperator B') (lp.single 2 n 1)) =
      inner ℂ (u n) ((s3tc_toOperator A*s3tc_toOperator B) (u n)) := by
    rw [hop,ContinuousLinearMap.mul_apply,ContinuousLinearMap.mul_apply,hUe]
    exact ContinuousLinearMap.adjoint_inner_right U _ _ |>.trans (by rw [hUe])
  have ht : s3tc_trace A' B' = s3tc_trace A B := by
    dsimp only [A',B']
    rw [s3tc_trace_left_right,← s3tc_right_mul,hUU,s3tc_right_one]
  have h := s3tc_trace_diagonal A' B'
  exact ⟨h.1.congr he,(tsum_congr (fun n => (he n).symm)).trans (h.2.trans ht)⟩

/-- In a genuine eigenbasis, the Gram trace moment is the corresponding
spectral power sum, with summability supplied by the HS trace theorem. -/
theorem s3tc_gram_spectral (A : s3tc_HS) (u : HilbertBasis ℕ ℂ ell2) (lam : ℕ → ℝ)
    (heig : ∀ n, (s3tc_toOperator A*star (s3tc_toOperator A)) (u n) = ((lam n^2 : ℝ) : ℂ) • u n)
    (N : ℕ) :
    let K := s3tc_toOperator A*star (s3tc_toOperator A)
    Summable (fun n => ((lam n^2 : ℝ) : ℂ)^(N+1)) ∧
      inner ℂ A (s3tc_left (K^N) A) = ∑' n, ((lam n^2 : ℝ) : ℂ)^(N+1) := by
  intro K
  have hp (n j : ℕ) : (K^j) (u n) = (((lam n^2 : ℝ) : ℂ)^j) • u n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ,ContinuousLinearMap.mul_apply,heig,map_smul,ih,smul_smul]
      congr 1
      ring
  have hop : s3tc_toOperator (s3tc_left (K^N) A)*s3tc_toOperator (s3tc_adjoint A) = K^(N+1) := by
    rw [s3tc_left_operator,s3tc_adjoint_operator,mul_assoc,← pow_succ]
  have h := s3tc_trace_basis (s3tc_left (K^N) A) (s3tc_adjoint A) u
  rw [hop,s3tc_trace_gram_pair] at h
  have hd (n : ℕ) : inner ℂ (u n) ((K^(N+1)) (u n)) = ((lam n^2 : ℝ) : ℂ)^(N+1) := by
    rw [hp,inner_smul_right,inner_self_eq_norm_sq_to_K,u.orthonormal.1 n]
    simp
  exact ⟨h.1.congr hd,h.2.symm.trans (tsum_congr hd)⟩

/-- Absolute convergence of the trace logarithm series from a genuine operator gap. -/
theorem s3tc_gram_log_summable (A : s3tc_HS) (hA : ‖s3tc_toOperator A‖ < 1) :
    Summable (fun N : ℕ => inner ℂ A
      (s3tc_left ((s3tc_toOperator A*star (s3tc_toOperator A))^N) A) / (N+1)) := by
  have hc2 : ‖s3tc_toOperator A‖^2 < 1 := by nlinarith [norm_nonneg (s3tc_toOperator A)]
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg ‖s3tc_toOperator A‖) hc2).mul_left (‖A‖^2))
  intro N
  rw [norm_div]
  have hden : ‖((N : ℂ)+1)‖ = (N : ℝ)+1 := by norm_cast
  rw [hden]
  apply (div_le_self (norm_nonneg _) (le_add_of_nonneg_left (Nat.cast_nonneg N) : (1 : ℝ) ≤ (N : ℝ)+1)).trans
  exact s3tc_gram_moment_bound A (norm_nonneg _) le_rfl N

end Ch2
end TakhtajanTeo
