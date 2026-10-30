import TakhtajanTeo.Ch1.S1_3_Fuchsian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem pat_discExteriorR_eq {r : ℝ} (hr : 1 < r) :
    discExteriorR r = {z : ℂ | r ≤ ‖z‖} := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hr h, h⟩⟩

theorem pat_discExteriorR_measurable (r : ℝ) : MeasurableSet (discExteriorR r) := by
  exact (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_const continuous_norm).measurableSet

theorem pat_exterior_radial_integral {r : ℝ} (hr : 1 < r) (f : ℝ → ℝ) :
    (∫ z in discExteriorR r, f ‖z‖) = 2 * π * ∫ t in Ici r, t * f t := by
  have hi := integral_fun_norm_addHaar (volume : Measure ℂ) ((Ici r).indicator f)
  have he : (fun z : ℂ => (Ici r).indicator f ‖z‖) =
      (discExteriorR r).indicator (fun z => f ‖z‖) := by
    funext z
    rw [pat_discExteriorR_eq hr]
    simp only [indicator, mem_Ici, mem_setOf_eq]
  rw [he, integral_indicator (pat_discExteriorR_measurable r)] at hi
  have hunit : (volume : Measure ℂ).real (ball 0 1) = π := by simp [Measure.real]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, nsmul_eq_mul, smul_eq_mul] at hi
  rw [hunit] at hi
  have he' : (fun t : ℝ => t * (Ici r).indicator f t) =
      (Ici r).indicator (fun t => t * f t) := by
    funext t
    by_cases ht : r ≤ t <;> simp [indicator, ht]
  rw [he', setIntegral_indicator measurableSet_Ici] at hi
  have hs : Ioi (0 : ℝ) ∩ Ici r = Ici r :=
    inter_eq_right.mpr (fun t ht => lt_of_lt_of_le (lt_trans zero_lt_one hr) ht)
  rw [hs] at hi
  simpa only [Nat.cast_ofNat, mul_assoc] using hi

theorem pat_exterior_radial_integrable {r : ℝ} (hr : 1 < r) (f : ℝ → ℝ) :
    IntegrableOn (fun z : ℂ => f ‖z‖) (discExteriorR r) ↔
      IntegrableOn (fun t => t * f t) (Ici r) := by
  rw [← integrable_indicator_iff (pat_discExteriorR_measurable r)]
  have he : (discExteriorR r).indicator (fun z : ℂ => f ‖z‖) =
      fun z : ℂ => (Ici r).indicator f ‖z‖ := by
    funext z
    rw [pat_discExteriorR_eq hr]
    simp only [indicator, mem_Ici, mem_setOf_eq]
  rw [he, integrable_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  have he' : (fun t : ℝ => t * (Ici r).indicator f t) =
      (Ici r).indicator (fun t => t * f t) := by
    funext t
    by_cases ht : r ≤ t <;> simp [indicator, ht]
  rw [he', integrableOn_indicator_iff measurableSet_Ici]
  rw [inter_eq_left.mpr (show Ici r ⊆ Ioi (0 : ℝ) from
    fun t ht => lt_of_lt_of_le (lt_trans zero_lt_one hr) ht)]

theorem pat_radial_primitive {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => 2 / (1 - s ^ 2)) (t * (4 / (1 - t ^ 2) ^ 2)) t := by
  have hne : 1 - t ^ 2 ≠ 0 := by nlinarith
  convert (hasDerivAt_const t (2 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)) hne using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    ring

theorem pat_radial_primitive_limit :
    Tendsto (fun t : ℝ => 2 / (1 - t ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t ^ 2 + (-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop (by norm_num))
  have hh := ht.inv_tendsto_atTop.const_mul (-2 : ℝ)
  convert hh using 1
  · funext t
    change 2 / (1 - t ^ 2) = -2 * (t ^ 2 + -1)⁻¹
    rw [show 1 - t ^ 2 = -(t ^ 2 + -1) by ring]
    rw [div_neg, div_eq_mul_inv]
    ring
  · ring

theorem pat_radial_density_integrable {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun t : ℝ => t * (4 / (1 - t ^ 2) ^ 2)) (Ici r) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => pat_radial_primitive (lt_of_lt_of_le hr ht))
    (fun t ht => mul_nonneg (le_of_lt (lt_trans zero_lt_one (hr.trans ht))) (by positivity))
    pat_radial_primitive_limit

theorem pat_radial_density_integral {r : ℝ} (hr : 1 < r) :
    (∫ t in Ici r, t * (4 / (1 - t ^ 2) ^ 2)) = 2 / (r ^ 2 - 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => pat_radial_primitive (lt_of_lt_of_le hr ht))
    (fun t ht => mul_nonneg (le_of_lt (lt_trans zero_lt_one (hr.trans ht))) (by positivity))
    pat_radial_primitive_limit
  rw [hh, zero_sub, ← div_neg]
  congr 1
  ring

theorem pat_rho_integrable {r : ℝ} (hr : 1 < r) :
    IntegrableOn rho (discExteriorR r) := by
  exact (pat_exterior_radial_integrable hr (fun t => 4 / (1 - t ^ 2) ^ 2)).mpr
    (pat_radial_density_integrable hr)

theorem pat_rho_integral {r : ℝ} (hr : 1 < r) :
    (∫ z in discExteriorR r, rho z) = 4 * π / (r ^ 2 - 1) := by
  calc _ = 2 * π * ∫ t in Ici r, t * (4 / (1 - t ^ 2) ^ 2) :=
      pat_exterior_radial_integral hr (fun t => 4 / (1 - t ^ 2) ^ 2)
    _ = _ := by rw [pat_radial_density_integral hr]; ring

theorem pat_rho_integral_pos {r : ℝ} (hr : 1 < r) :
    0 < ∫ z in discExteriorR r, rho z := by
  rw [pat_rho_integral hr]
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (by nlinarith)

theorem pat_rho_fundDomain (Γ : Subgroup SL2C) :
    (∫ z in fundDomain Γ, rho z) = (hypArea Γ).toReal := by
  have hm : Measurable rho := by unfold rho; fun_prop
  exact integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun z => div_nonneg (by norm_num) (sq_nonneg _))
    hm.aestronglyMeasurable

theorem pat_quotient_constant (Γ : Subgroup SL2C) (c : ℂ) :
    quotientIntegral Γ (fun z => c * rho z) = c * (hypArea Γ).toReal := by
  unfold quotientIntegral
  rw [integral_const_mul, integral_complex_ofReal, pat_rho_fundDomain]

theorem pat_constant_average (Γ : Subgroup SL2C) (c : ℂ) {r : ℝ} (hr : 1 < r) :
    ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
      (∫ z in discExteriorR r, c * (rho z : ℂ)) = quotientIntegral Γ (fun z => c * rho z) := by
  rw [integral_const_mul, integral_complex_ofReal, pat_quotient_constant]
  have hn : ((∫ z in discExteriorR r, rho z : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pat_rho_integral_pos hr).ne'
  field_simp

/-- The constant-function case of Patterson averaging. This is not the
general automorphic-function averaging theorem. -/
theorem pat_constant_limit (Γ : Subgroup SL2C) (c : ℂ) :
    Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
      ∫ z in discExteriorR r, c * (rho z : ℂ)) (𝓝[>] 1)
      (𝓝 (quotientIntegral Γ (fun z => c * rho z))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (pat_constant_average Γ c hr).symm

theorem pat_normalizing_factor_limit (Γ : Subgroup SL2C) :
    Tendsto (fun r : ℝ => (hypArea Γ).toReal / (∫ z in discExteriorR r, rho z))
      (𝓝[>] 1) (𝓝 0) := by
  have hh : Tendsto (fun r : ℝ => (hypArea Γ).toReal * (r ^ 2 - 1) / (4 * π))
      (𝓝[>] 1) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => (hypArea Γ).toReal * (r ^ 2 - 1) / (4 * π)) := by fun_prop
    simpa using (hc.continuousAt (x := 1)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [pat_rho_integral hr, div_div_eq_mul_div]

theorem pat_bounded_integrable {r : ℝ} (hr : 1 < r) {h : ℂ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ z ∂volume.restrict unitDiscExterior, ‖h z‖ ≤ C) :
    IntegrableOn (fun z => h z * (rho z : ℂ)) (discExteriorR r) := by
  have hs : discExteriorR r ⊆ unitDiscExterior := fun _ hz => hz.1
  have hρ := pat_rho_integrable hr
  apply (hρ.const_mul C).mono' ((hm.mono_set hs).mul hρ.ofReal.aestronglyMeasurable)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hb] with z hz
  change ‖h z * (rho z : ℂ)‖ ≤ C * rho z
  have hn : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
  simpa only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hn] using
    mul_le_mul_of_nonneg_right hz hn

theorem pat_weighted_integral_norm_le {r : ℝ} (hr : 1 < r) {h : ℂ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ z ∂volume.restrict unitDiscExterior, ‖h z‖ ≤ C) :
    ‖∫ z in discExteriorR r, h z * (rho z : ℂ)‖ ≤
      C * (∫ z in discExteriorR r, rho z) := by
  have hi := pat_bounded_integrable hr hm hb
  have hρ := pat_rho_integrable hr
  calc _ ≤ ∫ z in discExteriorR r, ‖h z * (rho z : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in discExteriorR r, C * rho z := by
      apply integral_mono_ae hi.norm (hρ.const_mul C)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (show discExteriorR r ⊆ unitDiscExterior from fun _ hz => hz.1) hb] with z hz
      have hn : 0 ≤ rho z := div_nonneg (by norm_num) (sq_nonneg _)
      simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn] using
        mul_le_mul_of_nonneg_right hz hn
    _ = _ := integral_const_mul C rho

theorem pat_normalized_average_norm_le (Γ : Subgroup SL2C) {r : ℝ} (hr : 1 < r)
    {h : ℂ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ z ∂volume.restrict unitDiscExterior, ‖h z‖ ≤ C) :
    ‖((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
      ∫ z in discExteriorR r, h z * (rho z : ℂ)‖ ≤ (hypArea Γ).toReal * C := by
  have hpos := pat_rho_integral_pos hr
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg hpos.le]
  calc _ ≤ ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z)) *
        (C * (∫ z in discExteriorR r, rho z)) :=
      mul_le_mul_of_nonneg_left (pat_weighted_integral_norm_le hr hm hb)
        (div_nonneg ENNReal.toReal_nonneg hpos.le)
    _ = _ := by field_simp

end TakhtajanTeo
