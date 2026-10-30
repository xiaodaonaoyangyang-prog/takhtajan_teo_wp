import TakhtajanTeo.Ch2.S3KernelVariation
import Mathlib.Data.Finset.NatAntidiagonal

/-! # Weighted L2 control of the diagonal of a genuine HS Bergman kernel

The finite coefficient estimate and Fatou passage provide the control
needed for the subsequent trace/integral interchange.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

theorem s3dl_group {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ × ℕ → E} (hf : Summable f) :
    Summable (fun n => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q) ∧
      (∑' n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q) = ∑' q, f q := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hs : Summable (fun q : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n => f q.2) := e.summable_iff.mpr hf
  have hfin (n : ℕ) : Summable (fun q : Finset.HasAntidiagonal.antidiagonal n => f q) := (hasSum_fintype _).summable
  constructor
  · simpa only [tsum_fintype,Finset.sum_coe_sort] using hs.sigma' hfin
  · have ht := hs.tsum_sigma' hfin
    have he := e.tsum_eq f
    simpa only [tsum_fintype,Finset.sum_coe_sort] using ht.symm.trans he

def s3dl_weight (q : ℕ × ℕ) : ℝ :=
  Real.sqrt ((q.1+1 : ℝ)/π)*Real.sqrt ((q.2+1 : ℝ)/π)

def s3dl_coeff (A : s3tc_HS) (n : ℕ) : ℂ :=
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, A q*(s3dl_weight q : ℂ)

def s3dl_den (n : ℕ) : ℝ := ((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3)

theorem s3dl_weight_nonneg (q : ℕ × ℕ) : 0 ≤ s3dl_weight q := by unfold s3dl_weight; positivity

theorem s3dl_weight_sq (q : ℕ × ℕ) :
    (s3dl_weight q)^2 = ((q.1 : ℝ)+1)*((q.2 : ℝ)+1)/π^2 := by
  rw [s3dl_weight,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
  ring

theorem s3dl_weight_sum (n : ℕ) :
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, (s3dl_weight q)^2) ≤ s3dl_den n/π^2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    _ ≤ ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, ((n : ℝ)+1)^2/π^2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hsum : q.1+q.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have h1 : (q.1 : ℝ) ≤ n := by exact_mod_cast Nat.le.intro hsum
      have h2 : (q.2 : ℝ) ≤ n := by exact_mod_cast (show q.2 ≤ n by omega)
      rw [s3dl_weight_sq]
      apply div_le_div_of_nonneg_right _ (sq_nonneg π)
      nlinarith [Nat.cast_nonneg (α := ℝ) q.1,Nat.cast_nonneg (α := ℝ) q.2]
    _ = ((n : ℝ)+1)^3/π^2 := by simp; ring
    _ ≤ s3dl_den n/π^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg π)
      unfold s3dl_den
      nlinarith [sq_nonneg (n : ℝ)]

/-- Cauchy--Schwarz on each finite antidiagonal, with a uniform energy constant. -/
theorem s3dl_coeff_bound (A : s3tc_HS) (n : ℕ) :
    ‖s3dl_coeff A n‖^2/s3dl_den n ≤
      π⁻¹^2*(∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, ‖A q‖^2) := by
  have hnorm : ‖s3dl_coeff A n‖ ≤ ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, ‖A q‖*s3dl_weight q := by
    simpa only [s3dl_coeff,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (s3dl_weight_nonneg _)] using norm_sum_le (Finset.HasAntidiagonal.antidiagonal n)
        (fun q => A q*(s3dl_weight q : ℂ))
  have hsq : ‖s3dl_coeff A n‖^2 ≤
      (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, ‖A q‖^2)*(∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, (s3dl_weight q)^2) := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.HasAntidiagonal.antidiagonal n) (fun q => ‖A q‖) s3dl_weight)
  have hb := hsq.trans (mul_le_mul_of_nonneg_left (s3dl_weight_sum n)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hd : 0 < s3dl_den n := by unfold s3dl_den; positivity
  apply (div_le_iff₀ hd).mpr
  convert hb using 1 <;> field_simp <;> ring

theorem s3dl_energy_summable (A : s3tc_HS) :
    Summable (fun n => ‖s3dl_coeff A n‖^2/s3dl_den n) ∧
      (∑' n, ‖s3dl_coeff A n‖^2/s3dl_den n) ≤ π⁻¹^2*‖A‖^2 := by
  obtain ⟨hs,he⟩ := s3dl_group (s3tc_summable A)
  have hm := hs.mul_left (π⁻¹^2)
  have hn (n : ℕ) : 0 ≤ ‖s3dl_coeff A n‖^2/s3dl_den n := by unfold s3dl_den; positivity
  have hf := hm.of_nonneg_of_le hn (s3dl_coeff_bound A)
  refine ⟨hf,?_⟩
  have h := hf.tsum_le_tsum (s3dl_coeff_bound A) hm
  rw [hs.tsum_mul_left,he,← s3fv_lp_norm_sq] at h
  exact h

theorem s3dl_kernel_summable (A : s3tc_HS) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    Summable (fun q : ℕ × ℕ => A q*basisE q.1 z*basisE q.2 w) := by
  have hm := ((basisE_norm_summable hz).mul_norm (basisE_norm_summable hw)).mul_left ‖A‖
  apply Summable.of_norm_bounded hm
  intro q
  simp only [norm_mul]
  have h := mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) A q)
    (mul_nonneg (norm_nonneg (basisE q.1 z)) (norm_nonneg (basisE q.2 w)))
  simpa only [mul_assoc] using h

theorem s3dl_kernel_sum (A : s3tc_HS) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    s3kv_eval z w A = ∑' q : ℕ × ℕ, A q*basisE q.1 z*basisE q.2 w := by
  rw [s3kv_eval_apply,s3kv_kernel_series _ hz w,(s3dl_kernel_summable A hz hw).tsum_prod]
  apply tsum_congr
  intro m
  change (gopOp (fun i j => A (i,j)) (s3kv_vector w)) m*basisE m z = _
  rw [pmb_apply (s3tc_bounded A)]
  change (∑' n, A (m,n)*s3kv_vector w n)*basisE m z = _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [s3kv_vector_apply hw]
  ring

/-- The scalar diagonal series is the actual bounded HS kernel evaluation. -/
theorem s3dl_diagonal_series (A : s3tc_HS) {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun n => s3dl_coeff A n*z^n) (s3kv_eval z z A) := by
  obtain ⟨hs,ht⟩ := s3dl_group (s3dl_kernel_summable A hz hz)
  have he (n : ℕ) : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, A q*basisE q.1 z*basisE q.2 z) =
      s3dl_coeff A n*z^n := by
    rw [s3dl_coeff,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqn : q.1+q.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    rw [basisE,basisE,s3dl_weight,Complex.ofReal_mul,← hqn,pow_add]
    ring
  have hf := hs.congr he
  have hfSum : (∑' n, s3dl_coeff A n*z^n) = s3kv_eval z z A := by
    rw [s3dl_kernel_sum A hz hz,← ht]
    exact tsum_congr (fun n => (he n).symm)
  exact hfSum ▸ hf.hasSum

/-- Fatou passes finite weighted Parseval to the actual HS diagonal. -/
theorem s3dl_diagonal_lintegral (A : s3tc_HS) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖s3kv_eval z z A‖^2*(rho z)⁻¹)) ≤
      ENNReal.ofReal (‖A‖^2/(2*π)) := by
  let P := wp_scalarSeriesPolynomial (s3dl_coeff A)
  let F : ℕ → ℂ → ℝ≥0∞ := fun N z => ENNReal.ofReal (‖(P N).eval z‖^2*(rho z)⁻¹)
  have hc := (s3dl_energy_summable A).1
  have hm (N : ℕ) : Measurable (F N) := by dsimp [F,rho]; fun_prop
  have ht (z : ℂ) (hz : z ∈ unitDisc) : Tendsto (fun N => F N z) atTop
      (𝓝 (ENNReal.ofReal (‖s3kv_eval z z A‖^2*(rho z)⁻¹))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    have hp : Tendsto (fun N => (P N).eval z) atTop (𝓝 (s3kv_eval z z A)) := by
      simpa only [P,wp_scalarSeriesPolynomial_eval] using (s3dl_diagonal_series A hz).tendsto_sum_nat
    exact (hp.norm.pow 2).mul_const _
  have hI (N : ℕ) : (∫⁻ z in unitDisc, F N z) =
      ENNReal.ofReal ((π/2)*∑ n ∈ Finset.range N, ‖s3dl_coeff A n‖^2/s3dl_den n) := by
    dsimp only [F]
    rw [← ofReal_integral_eq_lintegral_ofReal (A21_disk_weighted_integrable (polynomial_mem_A21 (P N)))
      (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (by unfold rho; positivity)))]
    rw [wp_scalarSeriesPolynomial_area]
    rfl
  have hlim : Tendsto (fun N => ∫⁻ z in unitDisc, F N z) atTop
      (𝓝 (ENNReal.ofReal ((π/2)*(∑' n, ‖s3dl_coeff A n‖^2/s3dl_den n)))) := by
    simp only [hI]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hc.hasSum.tendsto_sum_nat.const_mul (π/2))
  calc
    _ = ∫⁻ z in unitDisc, liminf (fun N => F N z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
      exact (ht z hz).liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ z in unitDisc, F N z) atTop := lintegral_liminf_le hm
    _ = _ := hlim.liminf_eq
    _ ≤ ENNReal.ofReal (‖A‖^2/(2*π)) := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left (s3dl_energy_summable A).2 (by positivity : 0 ≤ π/2)
      convert h using 1 <;> field_simp <;> ring

/-- Actual weighted L2 integrability and a uniform quadratic norm bound on
the diagonal restriction, without any assumed trace/integral interchange. -/
theorem s3dl_diagonal_bound (A : s3tc_HS) :
    IntegrableOn (fun z => ‖s3kv_eval z z A‖^2*(rho z)⁻¹) unitDisc ∧
      (∫ z in unitDisc, ‖s3kv_eval z z A‖^2*(rho z)⁻¹) ≤ ‖A‖^2/(2*π) := by
  have hd := differentiableOn_of_powerSeries (fun z hz => s3dl_diagonal_series A hz)
  have hm : AEStronglyMeasurable (fun z => ‖s3kv_eval z z A‖^2*(rho z)⁻¹) (volume.restrict unitDisc) := by
    apply ((hd.continuousOn.norm.pow 2).mul _).aestronglyMeasurable measurableSet_ball
    simp only [rho,inv_div]
    fun_prop
  have hn (z : ℂ) : 0 ≤ ‖s3kv_eval z z A‖^2*(rho z)⁻¹ := by unfold rho; positivity
  have hi : IntegrableOn (fun z => ‖s3kv_eval z z A‖^2*(rho z)⁻¹) unitDisc := by
    refine ⟨hm,?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
    exact (s3dl_diagonal_lintegral A).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  have h := s3dl_diagonal_lintegral A
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ‖A‖^2/(2*π))).mp h

theorem s3dl_diagonal_A2 (A : s3tc_HS) : (fun z => s3kv_eval z z A) ∈ A2fun unitDisc :=
  ⟨differentiableOn_of_powerSeries (fun z hz => s3dl_diagonal_series A hz),
    normA2_lt_top_of_integrable_weighted_sq (s3dl_diagonal_bound A).1⟩

theorem s3dl_vector_inv {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s3st_vector z = (z⁻¹)^2 • s3kv_vector z⁻¹ := by
  have hz0 := resolvent_exterior_ne_zero hz
  have hi : z⁻¹ ∈ unitDisc := (a21_inv_exterior hz).1
  ext n
  rw [lp.coeFn_smul,Pi.smul_apply,s3st_vector_apply hz,s3kv_vector_apply hi]
  have h := e24_basisF_inv n (inv_ne_zero hz0)
  simpa only [inv_inv,smul_eq_mul] using h

theorem s3dl_exterior_diagonal (A : s3tc_HS) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    s3st_kernel (s3tc_toOperator A) z z = s3kv_eval z⁻¹ z⁻¹ A/z^4 := by
  rw [s3st_kernel,s3dl_vector_inv hz,s3kv_eval_apply,s3kv_kernel,
    star_smul,map_smul,inner_smul_left,inner_smul_right]
  simp only [div_eq_mul_inv,inv_pow,starRingEnd_apply,star_star]
  ring

/-- The same genuine diagonal bound in the exterior coordinate. -/
theorem s3dl_exterior_bound (A : s3tc_HS) :
    IntegrableOn (fun z => ‖s3st_kernel (s3tc_toOperator A) z z‖^2*(rho z)⁻¹) unitDiscExterior ∧
      (∫ z in unitDiscExterior, ‖s3st_kernel (s3tc_toOperator A) z z‖^2*(rho z)⁻¹) ≤
        ‖A‖^2/(2*π) := by
  let f : ℂ → ℂ := fun z => s3kv_eval z z A
  let g : ℂ → ℂ := fun z => f z⁻¹/z^4
  have he : EqOn (fun z => s3st_kernel (s3tc_toOperator A) z z) g unitDiscExterior :=
    fun z hz => s3dl_exterior_diagonal A hz
  have hi : IntegrableOn (fun z => ‖g z‖^2*(rho z)⁻¹) unitDiscExterior :=
    wp_inverted_disk_A2_integrable (s3dl_diagonal_A2 A)
  have hweight : EqOn (fun z => ‖s3st_kernel (s3tc_toOperator A) z z‖^2*(rho z)⁻¹)
      (fun z => ‖g z‖^2*(rho z)⁻¹) unitDiscExterior := fun z hz => by
        dsimp only
        have hze : s3st_kernel (s3tc_toOperator A) z z = g z := he hz
        rw [hze]
  refine ⟨hi.congr_fun hweight.symm wp_exterior_isOpen.measurableSet,?_⟩
  rw [setIntegral_congr_fun wp_exterior_isOpen.measurableSet hweight,
    ← inverted_quadratic_weighted_integral g]
  have hginv : EqOn (fun z => ‖g z⁻¹/z^4‖^2*(rho z)⁻¹)
      (fun z => ‖f z‖^2*(rho z)⁻¹) (unitDisc \ {0}) := by
    intro z hz
    dsimp only [g]
    rw [wp_quadratic_inversion_involutive f hz.2]
  have hset : MeasurableSet (unitDisc \ {(0 : ℂ)}) := measurableSet_ball.diff (measurableSet_singleton 0)
  have hchange : (∫ z in unitDisc \ {0}, ‖g z⁻¹/z^4‖^2*(rho z)⁻¹) =
      ∫ z in unitDisc \ {0}, ‖f z‖^2*(rho z)⁻¹ := setIntegral_congr_fun hset hginv
  rw [hchange]
  have hdel : volume.restrict (unitDisc \ {(0 : ℂ)}) = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [hz]
  rw [hdel]
  exact (s3dl_diagonal_bound A).2

end Ch2
end TakhtajanTeo
