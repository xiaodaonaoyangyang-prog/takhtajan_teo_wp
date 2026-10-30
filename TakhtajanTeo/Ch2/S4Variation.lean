import TakhtajanTeo.Ch2.S4Eq41
import TakhtajanTeo.Ch1.QCVariationBergman

/-! # Analytic ingredients for the Weil–Petersson variation

The reflected fourth-order kernel has genuine integrable representatives.
Its harmonic reproduction and pairing are proved independently of the open
variation statement and of the first variation of the Liouville action.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- L1
theorem s4v_kernel_den_ne_zero {z w : ℂ} (hz : z ∈ unitDiscExterior)
    (hw : w ∈ unitDiscExterior) : 1 - conj w * z ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one, norm_mul, norm_conj] at he
  change 1 < ‖z‖ at hz
  change 1 < ‖w‖ at hw
  nlinarith

-- L2
theorem s4v_kernel_integrable_bound {ν : ℂ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hm : AEStronglyMeasurable ν (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖ν w‖ ≤ M)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    IntegrableOn (fun w => conj (ν w) / (1 - conj w * z) ^ 4) unitDiscExterior := by
  have hδ : 0 < ‖z‖ - 1 := sub_pos.mpr hz
  have hden : AEStronglyMeasurable (fun w : ℂ => (1 - conj w * z) ^ 4)
      (volume.restrict unitDiscExterior) := by fun_prop
  apply (QCV.qcv_hB_int.const_mul (M / (‖z‖ - 1) ^ 4)).mono' (hm.star.div₀ hden)
  filter_upwards [hb, ae_restrict_mem wp_exterior_isOpen.measurableSet] with w hw hwD
  have hwpos : 0 < ‖w‖ := lt_trans zero_lt_one hwD
  have hlow : (‖z‖ - 1) * ‖w‖ ≤ ‖1 - conj w * z‖ := by
    have h := norm_sub_norm_le (conj w * z) 1
    rw [norm_mul, norm_conj, norm_one, norm_sub_rev] at h
    nlinarith [show 1 < ‖w‖ from hwD]
  have hlowpos : 0 < (‖z‖ - 1) * ‖w‖ := mul_pos hδ hwpos
  have hpow : ((‖z‖ - 1) * ‖w‖) ^ 4 ≤ ‖1 - conj w * z‖ ^ 4 :=
    pow_le_pow_left₀ hlowpos.le hlow 4
  calc
    ‖conj (ν w) / (1 - conj w * z) ^ 4‖ = ‖ν w‖ / ‖1 - conj w * z‖ ^ 4 := by
      rw [norm_div, norm_conj, norm_pow]
    _ ≤ M / (((‖z‖ - 1) * ‖w‖) ^ 4) :=
      div_le_div₀ hM hw (pow_pos hlowpos 4) hpow
    _ = (M / (‖z‖ - 1) ^ 4) * (‖w‖ ^ 4)⁻¹ := by
      simp only [mul_pow, div_eq_mul_inv, mul_inv, mul_assoc]
    _ ≤ (M / (‖z‖ - 1) ^ 4) * (16 * (1 + ‖w‖) ^ (-4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (QCV.qcv_inv4 hwD) (by positivity)

-- L3
theorem s4v_kernel_reproduce {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (6 / π : ℂ) * (∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4) =
      conj (ν z) * (rho z : ℂ) / 2 := by
  have h := congrArg (starRingEnd ℂ) (wp_harmonic_projection_raw hν hz)
  have hi : conj (∫ w in unitDiscExterior, ν w / (1 - w * conj z) ^ 4) =
      ∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4 := by
    rw [← integral_conj]
    simp only [map_div₀, map_pow, map_sub, map_one, map_mul, conj_conj]
  simp only [map_mul, map_div₀, conj_ofReal, map_ofNat, hi] at h
  generalize hJ : (∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4) = J at h ⊢
  have hn : (1 - ‖z‖ ^ 2 : ℝ) ≠ 0 := by
    have hz' : 1 < ‖z‖ := hz
    nlinarith [norm_nonneg z]
  have hnC : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  rw [← h]
  simp only [rho, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp
  ring

-- L4
theorem s4v_kernel_pairing {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => 2 * μ z * ((6 / π : ℂ) *
      (∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4))) unitDiscExterior ∧
    (∫ z in unitDiscExterior, 2 * μ z * ((6 / π : ℂ) *
      (∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4))) = wpInner μ ν := by
  have he : (fun z => 2 * μ z * ((6 / π : ℂ) *
      (∫ w in unitDiscExterior, conj (ν w) / (1 - conj w * z) ^ 4))) =ᵐ[volume.restrict unitDiscExterior]
      (fun z => μ z * conj (ν z) * rho z) := by
    filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
    rw [s4v_kernel_reproduce hν hz]
    ring
  exact ⟨(wpInner_integrable hμ hν).congr he.symm, integral_congr_ae he⟩

end Ch2
end TakhtajanTeo
