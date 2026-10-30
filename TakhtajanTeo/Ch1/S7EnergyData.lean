import TakhtajanTeo.Ch1.S7Prop71

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Multiplication by an essentially bounded coefficient preserves weighted L2.
This supplies the forcing term in the energy argument for Proposition 7.2. -/
theorem s7ed_product_finite {D : Set ℂ} {f g : ℂ → ℂ} {M : ℝ}
    (hf : normL2 D f < ∞)
    (hg : ∀ᵐ z ∂(volume.restrict D), ‖g z‖ ≤ M) :
    normL2 D (fun z => f z * conj (g z)) < ∞ := by
  have hi : (∫⁻ z in D, (‖f z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho z)) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mp hf
  have hb : (∫⁻ z in D, (‖f z * conj (g z)‖₊ : ℝ≥0∞)^2 *
      ENNReal.ofReal (rho z)) ≤
      ENNReal.ofReal M ^ 2 * ∫⁻ z in D, (‖f z‖₊ : ℝ≥0∞)^2 *
        ENNReal.ofReal (rho z) := by
    calc
      _ ≤ ∫⁻ z in D, ENNReal.ofReal M ^ 2 *
          ((‖f z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho z)) := by
        apply lintegral_mono_ae
        filter_upwards [hg] with z hz
        have hn : (‖g z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
          simpa only [← coe_nnnorm, ENNReal.ofReal_coe_nnreal] using
            ENNReal.ofReal_le_ofReal hz
        have hc : ‖conj (g z)‖₊ = ‖g z‖₊ := Subtype.ext (Complex.norm_conj _)
        simp only [nnnorm_mul, hc, ENNReal.coe_mul, mul_pow]
        calc
          _ ≤ (‖f z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal M ^ 2 *
              ENNReal.ofReal (rho z) := by gcongr
          _ = _ := by ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mpr
    (hb.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hi))

/-- The actual harmonic forcing term has finite weighted energy. -/
theorem s7ed_forcing_finite {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (ν : LinfStar) :
    normL2 unitDiscExterior (fun z => μ z * conj (ν z)) < ∞ := by
  obtain ⟨φ, hφ, hrep, hn⟩ := hμ
  exact s7ed_product_finite hn (LinfStar_ae_norm_le ν)

/-- The actual first variation is expressed using the raw harmonic L2 input,
not a pointwise equality with the arbitrarily chosen L-infinity representative. -/
theorem s7ed_Qdot_raw {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    Qdot (toLinf μ) ν z = -2 * dzbar (fun y => (rho y : ℂ)⁻¹ *
      dzbar (resolventStar fun u => μ u * conj (ν u)) y) z := by
  have hm : toLinf μ ∈ harmonicBeltrami :=
    (harmonicL2_subset_harmonic.choose_spec μ hμ).1
  have he : resolventStar (fun u => (toLinf μ) u * conj (ν u)) =
      resolventStar (fun u => μ u * conj (ν u)) := by
    funext w
    apply integral_congr_ae
    filter_upwards [wp_harmonic_toLinf_ae hμ] with u hu
    simp only [hu]
  rw [← he]
  exact (p71_prop_7_1 hm hν hz).2

end TakhtajanTeo
