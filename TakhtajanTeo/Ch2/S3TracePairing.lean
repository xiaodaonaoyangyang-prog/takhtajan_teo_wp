import TakhtajanTeo.Ch2.S3DiagonalL2

/-! # The actual continuous HS pairing with a harmonic exterior tangent -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

def s3tp_eval (z : ℂ) : s3tc_HS →L[ℂ] ℂ :=
  (innerSL ℂ (star (s3st_vector z))).comp
    ((ContinuousLinearMap.apply ℂ ell2 (s3st_vector z)).comp s3tc_toOperator)

theorem s3tp_eval_apply (A : s3tc_HS) (z : ℂ) :
    s3tp_eval z A = s3st_kernel (s3tc_toOperator A) z z := rfl

theorem s3tp_diagonal_A2 (A : s3tc_HS) : (fun z => s3tp_eval z A) ∈ A2fun unitDiscExterior := by
  have h := wp_inverted_disk_A2 (s3dl_diagonal_A2 A)
  have he : EqOn (fun z => s3tp_eval z A) (fun z => s3kv_eval z⁻¹ z⁻¹ A/z^4) unitDiscExterior :=
    fun z hz => s3dl_exterior_diagonal A hz
  refine ⟨h.1.congr he,?_⟩
  rw [normA2_congr wp_exterior_isOpen.measurableSet he]
  exact h.2

theorem s3tp_integrable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (A : s3tc_HS) :
    IntegrableOn (fun z => s3tp_eval z A*μ z) unitDiscExterior :=
  s3st_pair_integrable (s3tp_diagonal_A2 A) hμ

/-- The actual area pairing, initially as a linear map on genuine HS matrices. -/
def s3tp_pair {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : s3tc_HS →ₗ[ℂ] ℂ where
  toFun A := ∫ z in unitDiscExterior, s3tp_eval z A*μ z
  map_add' A B := by
    simp_rw [map_add,add_mul]
    exact integral_add (s3tp_integrable hμ A) (s3tp_integrable hμ B)
  map_smul' c A := by
    change (∫ z in unitDiscExterior, s3tp_eval z (c • A)*μ z) =
      c*(∫ z in unitDiscExterior, s3tp_eval z A*μ z)
    simp_rw [map_smul,smul_eq_mul,mul_assoc]
    exact integral_const_mul _ _

theorem s3tp_pair_quadratic {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (A : s3tc_HS) :
    ‖s3tp_pair hμ A‖ ≤ ‖A‖^2/(2*π)+(∫ z in unitDiscExterior, ‖μ z‖^2*rho z) := by
  have hi := s3tp_integrable hμ A
  have hD := (s3dl_exterior_bound A).1
  have hM := wp_integrable_sq hμ
  calc
    ‖s3tp_pair hμ A‖ ≤ ∫ z in unitDiscExterior, ‖s3tp_eval z A*μ z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in unitDiscExterior, ‖s3tp_eval z A‖^2*(rho z)⁻¹+‖μ z‖^2*rho z := by
      apply integral_mono_ae hi.norm (hD.add hM)
      filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
      change ‖s3tp_eval z A*μ z‖ ≤ ‖s3tp_eval z A‖^2*(rho z)⁻¹+‖μ z‖^2*rho z
      rw [norm_mul]
      exact s3st_weighted_pair_bound _ _ (wp_rho_pos hz)
    _ = (∫ z in unitDiscExterior, ‖s3tp_eval z A‖^2*(rho z)⁻¹)+
        (∫ z in unitDiscExterior, ‖μ z‖^2*rho z) := integral_add hD hM
    _ ≤ _ := add_le_add (s3dl_exterior_bound A).2 le_rfl

theorem s3tp_pair_bound {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (A : s3tc_HS) :
    ‖s3tp_pair hμ A‖ ≤ (1/(2*π)+(∫ z in unitDiscExterior, ‖μ z‖^2*rho z))*‖A‖ := by
  by_cases hA : A = 0
  · simp [hA]
  have hAn : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  let V := ((‖A‖ : ℂ)⁻¹) • A
  have hn : ‖V‖ = 1 := by
    simp only [V,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg A),inv_mul_cancel₀ hAn]
  have hP : ‖s3tp_pair hμ V‖ = ‖A‖⁻¹*‖s3tp_pair hμ A‖ := by
    simp only [V,map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg A)]
  have h := s3tp_pair_quadratic hμ V
  rw [hn,hP,one_pow] at h
  have hm := mul_le_mul_of_nonneg_left h (norm_nonneg A)
  rw [← mul_assoc,mul_inv_cancel₀ hAn,one_mul] at hm
  simpa only [mul_comm] using hm

/-- The weighted-L2 diagonal estimate makes the actual area pairing continuous. -/
def s3tp_pairCLM {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : s3tc_HS →L[ℂ] ℂ :=
  (s3tp_pair hμ).mkContinuous (1/(2*π)+(∫ z in unitDiscExterior, ‖μ z‖^2*rho z)) (s3tp_pair_bound hμ)

/-- Riesz representation constructs an actual HS matrix for the harmonic pairing. -/
def s3tp_symbol {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : s3tc_HS :=
  s3tc_adjoint ((InnerProductSpace.toDual ℂ s3tc_HS).symm (s3tp_pairCLM hμ))

/-- A genuine trace/area identity for every HS test matrix, derived from the
continuous diagonal pairing and Riesz representation. -/
theorem s3tp_trace_integral {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (A : s3tc_HS) :
    s3tc_trace A (s3tp_symbol hμ) = ∫ z in unitDiscExterior, s3st_kernel (s3tc_toOperator A) z z*μ z := by
  rw [s3tc_trace,s3tp_symbol,s3tc_adjoint_adjoint,InnerProductSpace.toDual_symm_apply]
  rfl

def s3tp_bilinear (x y : ell2) : ℂ := inner ℂ (star x) y

theorem s3tp_bilinear_sum (x y : ell2) : s3tp_bilinear x y = ∑' n, x n*y n := by
  rw [s3tp_bilinear,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [gop_inner_apply]
  change conj (conj (x n))*y n = _
  rw [Complex.conj_conj]

theorem s3tp_bilinear_symm (x y : ell2) : s3tp_bilinear x y = s3tp_bilinear y x := by
  rw [s3tp_bilinear_sum,s3tp_bilinear_sum]
  exact tsum_congr (fun n => mul_comm _ _)

theorem s3tp_bilinear_transpose (T : ell2 →L[ℂ] ell2) (x y : ell2) :
    s3tp_bilinear x (T y) = s3tp_bilinear (transposeOp T x) y := by
  change inner ℂ (star x) (T y) = inner ℂ (star (star (ContinuousLinearMap.adjoint T (star x)))) y
  rw [star_star]
  exact (ContinuousLinearMap.adjoint_inner_left T y (star x)).symm

theorem s3tp_bilinear_single (x : ell2) (n : ℕ) :
    s3tp_bilinear x (lp.single 2 n 1) = x n := by
  rw [s3tp_bilinear,lp.inner_single_right,gop_inner_apply]
  change conj (conj (x n))*1 = _
  rw [Complex.conj_conj,mul_one]

/-- A genuine HS rank-one matrix, with bilinear rather than sesquilinear entries. -/
def s3tp_rank (x y : ell2) : s3tc_HS :=
  ⟨fun q => x q.1*y q.2,s3fv_mem_hs (by
    simpa only [norm_mul,mul_pow] using
      (gop_l2_summable x).mul_of_nonneg (gop_l2_summable y)
        (fun _ => sq_nonneg _) (fun _ => sq_nonneg _))⟩

theorem s3tp_rank_apply (x y : ell2) (m n : ℕ) : s3tp_rank x y (m,n) = x m*y n := rfl

theorem s3tp_rank_operator (x y v : ell2) :
    s3tc_toOperator (s3tp_rank x y) v = s3tp_bilinear y v • x := by
  change gopOp (fun m n => x m*y n) v = _
  have hB : IsBoundedMat (fun m n => x m*y n) := s3tc_bounded (s3tp_rank x y)
  ext m
  rw [pmb_apply hB]
  change (∑' n, x m*y n*v n) = s3tp_bilinear y v*x m
  rw [s3tp_bilinear_sum,← tsum_mul_right]
  exact tsum_congr (fun n => by ring)

/-- Rank-one tests recover the actual operator bilinear form from the HS trace. -/
theorem s3tp_trace_rank (x y : ell2) (H : s3tc_HS) :
    s3tc_trace (s3tp_rank x y) H = s3tp_bilinear y (s3tc_toOperator H x) := by
  rw [← (s3tc_trace_diagonal (s3tp_rank x y) H).2,
    s3tp_bilinear_transpose,s3tp_bilinear_sum]
  apply tsum_congr
  intro n
  rw [ContinuousLinearMap.mul_apply,s3tp_rank_operator,gop_inner_single_left]
  change s3tp_bilinear y (s3tc_toOperator H (lp.single 2 n 1))*x n = _
  rw [s3tp_bilinear_transpose,s3tp_bilinear_single]

theorem s3tp_rank_diagonal (x y : ell2) (z : ℂ) :
    s3st_kernel (s3tc_toOperator (s3tp_rank x y)) z z =
      s3tp_bilinear (s3st_vector z) x*s3tp_bilinear (s3st_vector z) y := by
  rw [s3st_kernel,s3tp_rank_operator,inner_smul_right]
  change s3tp_bilinear y (s3st_vector z)*s3tp_bilinear (s3st_vector z) x = _
  rw [s3tp_bilinear_symm y (s3st_vector z),mul_comm]

/-- The constructed HS symbol represents the actual exterior product pairing
for arbitrary ell2 coefficient vectors, not merely polynomial tests. -/
theorem s3tp_symbol_pair {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (x y : ell2) :
    s3tp_bilinear x (s3tc_toOperator (s3tp_symbol hμ) y) =
      ∫ u in unitDiscExterior, μ u*s3tp_bilinear (s3st_vector u) x*s3tp_bilinear (s3st_vector u) y := by
  rw [← s3tp_trace_rank y x,s3tp_trace_integral]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [s3tp_rank_diagonal]
  ring

end Ch2
end TakhtajanTeo
