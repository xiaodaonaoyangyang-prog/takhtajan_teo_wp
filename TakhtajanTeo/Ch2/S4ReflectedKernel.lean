import TakhtajanTeo.Ch2.S4Variation
import TakhtajanTeo.Ch1.QCVariationLocalKernel

/-! # Reflected coefficient and the antiholomorphic infinitesimal kernel -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- L5
theorem s4v_integral_reflection (F : ℂ → ℂ) :
    (∫ u in unitDisc, F u) =
      ∫ w in unitDiscExterior, (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) * F (refl w) := by
  have hc := resolvent_inv_exterior_conformal
  have hi := ahP_integral_image wp_exterior_isOpen hc.1 hc.2.1 F
  rw [hc.2.2] at hi
  have hpre : (fun w : ℂ => conj w) ⁻¹' unitDiscExterior = unitDiscExterior := by
    ext w
    simp [unitDiscExterior]
  calc
    _ = ∫ u in unitDisc \ {0}, F u :=
      (setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))).symm
    _ = ∫ w in unitDiscExterior, (‖deriv (fun u : ℂ => u⁻¹) w‖ ^ 2 : ℝ) • F w⁻¹ := hi
    _ = ∫ w in unitDiscExterior, (‖deriv (fun u : ℂ => u⁻¹) (conj w)‖ ^ 2 : ℝ) • F (conj w)⁻¹ := by
      rw [← gzE_conj_measurePreserving.setIntegral_preimage_emb
        Complex.conjLIE.toHomeomorph.measurableEmbedding _ _, hpre]
    _ = _ := by
      apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
      intro w hw
      have hw0 : conj w ≠ 0 := by simpa using resolvent_exterior_ne_zero hw
      dsimp only
      rw [(hasDerivAt_inv hw0).deriv]
      simp only [norm_neg, norm_inv, norm_pow, norm_conj, ← pow_mul,
        show 2 * 2 = 4 from rfl, Complex.real_smul, refl, inv_pow]

-- L6
theorem s4v_reflected_kernel (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ u, unitDisc.indicator (extA ν) u / (u - z) ^ 4) =
      ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
  have he : (fun u => unitDisc.indicator (extA ν) u / (u - z) ^ 4) =
      unitDisc.indicator (fun u => extA ν u / (u - z) ^ 4) := by
    funext u
    by_cases hu : u ∈ unitDisc <;> simp [hu]
  have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
  rw [he, integral_indicator hD, s4v_integral_reflection]
  apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
  intro w hw
  dsimp only
  have hw0 := resolvent_exterior_ne_zero hw
  have hwc : conj w ≠ 0 := by simpa using hw0
  have hnorm : ‖refl w‖ < 1 := by
    rw [refl, norm_inv, norm_conj]
    exact inv_lt_one_of_one_lt₀ hw
  have hrr : refl (refl w) = w := by simp [refl]
  have hJ : (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((w * conj w) ^ 2)⁻¹ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
    congr 1
    ring
  have hd := s4v_kernel_den_ne_zero hz hw
  have hcoef : extA ν (refl w) = conj (ν w) * (refl w) ^ 2 / conj (refl w) ^ 2 := by
    unfold extA
    rw [ite_eq_right (not_lt.mpr hnorm.le), ite_eq_left hnorm, hrr]
  rw [hcoef, hJ]
  simp only [refl, map_inv₀, conj_conj]
  field_simp
  <;> ring

-- L7
theorem s4v_reflected_ahVar_iter3 (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    iteratedDeriv 3 (ahVar (unitDisc.indicator (extA ν))) z =
      -(6 / π : ℂ) * ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
  have hb : IsBeltramiCoeff (unitDisc.indicator (extA ν)) univ ‖ν‖ := by
    have hm := (extA_isBeltramiCoeff ν).1
    rw [Measure.restrict_univ] at hm
    have hD : MeasurableSet unitDisc := isOpen_ball.measurableSet
    refine ⟨by simpa only [Measure.restrict_univ] using hm.indicator hD, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [extA_ae_norm_le ν] with u hu
    by_cases h : u ∈ unitDisc
    · simpa only [indicator_of_mem h] using hu
    · simp only [indicator_of_notMem h, norm_zero]
      exact norm_nonneg ν
  have hzero : ∀ u ∈ unitDiscExterior, unitDisc.indicator (extA ν) u = 0 := by
    intro u hu
    exact indicator_of_notMem (fun h => (not_lt_of_ge hu.le) (mem_ball_zero_iff.mp h)) _
  rw [QCV.qcv_ahVar_iter3 (norm_nonneg ν) hb wp_exterior_isOpen hzero hz,
    s4v_reflected_kernel ν hz]

end Ch2
end TakhtajanTeo
