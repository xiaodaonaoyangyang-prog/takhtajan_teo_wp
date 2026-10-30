import TakhtajanTeo.Ch1.PattersonNormalization
import TakhtajanTeo.Ch1.HilbertBersSurjection

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The exterior core includes infinity, but its hyperbolic area is finite.
Consequently any essentially bounded coefficient has finite energy there. -/
theorem cce_core_finite {a : ℂ → ℂ} {R M : ℝ} (hR : 1 < R)
    (hb : ∀ᵐ z ∂(volume.restrict (discExteriorR R)), ‖a z‖ ≤ M) :
    normL2 (discExteriorR R) a < ∞ := by
  have hmass : (∫⁻ z in discExteriorR R, ENNReal.ofReal (rho z)) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (pat_rho_integrable hR)
      (Eventually.of_forall fun z => div_nonneg (by norm_num) (sq_nonneg _))]
    exact ENNReal.ofReal_lt_top
  have hle : (∫⁻ z in discExteriorR R,
      (‖a z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho z)) ≤
      ENNReal.ofReal M ^ 2 * ∫⁻ z in discExteriorR R, ENNReal.ofReal (rho z) := by
    calc _ ≤ ∫⁻ z in discExteriorR R,
        ENNReal.ofReal M ^ 2 * ENNReal.ofReal (rho z) := by
          apply lintegral_mono_ae
          filter_upwards [hb] with z hz
          have hn : (‖a z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
            have hh := ENNReal.ofReal_le_ofReal hz
            rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal] at hh
            exact hh
          gcongr
      _ = _ := by rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mpr
  exact hle.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hmass)

/-- Finite collar energy survives arbitrary bounded filling of the exterior
core. This proves only the energy step, not existence or injectivity of a fill. -/
theorem cce_finite_of_collar {a : ℂ → ℂ} {R M : ℝ} (hR : 1 < R)
    (hb : ∀ᵐ z ∂(volume.restrict (discExteriorR R)), ‖a z‖ ≤ M)
    (hc : normL2 (unitDiscExterior \ discExteriorR R) a < ∞) :
    normL2 unitDiscExterior a < ∞ := by
  have hcore := cce_core_finite hR hb
  have he : unitDiscExterior =
      (unitDiscExterior \ discExteriorR R) ∪ discExteriorR R := by
    exact (sdiff_union_of_subset (fun z hz => hz.1)).symm
  have hi := lintegral_union_le (μ := volume)
    (fun z => (‖a z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho z))
    (unitDiscExterior \ discExteriorR R) (discExteriorR R)
  rw [← he] at hi
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mpr
  exact hi.trans_lt (ENNReal.add_lt_top.mpr ⟨
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mp hc,
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mp hcore⟩)

end TakhtajanTeo
