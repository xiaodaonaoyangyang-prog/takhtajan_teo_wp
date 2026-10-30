import TakhtajanTeo.Ch1.ComponentRelativeSchwarzian
import TakhtajanTeo.Ch1.ComponentCoreEnergy

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The nonlinear reflection coefficient expression includes its denominator.
Its identification with an extension's dilatation is a separate geometric step. -/
def crn_coefficient (q h : ℂ → ℂ) (u : ℂ) : ℂ :=
  hbPre_reflected q h u / (1 + (u - h u)^2 * (q (h u) / 2) * dz h u)

/-- Finite raw energy for the SAME specified reflection, not another
existentially chosen reflection. -/
theorem crn_raw_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {q h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (hq : (∫⁻ v in fsans μ '' unitDisc,
      ENNReal.ofReal (‖q v‖^2 / poincareDensity (fsans μ '' unitDisc) v^2)) < ∞) :
    normL2 unitDiscExterior (hbPre_pullback (hbPre_reflected q h) (gsans μ)) < ∞ := by
  have hf := S2C.s2c_conf_f hμ
  have hg := S2C.s2c_conf_g hμ
  have hΩ := hf.isOpen isOpen_ball
  have hE := hg.isOpen resolvent_exterior_isOpen
  obtain ⟨C, hC, hprod⟩ := hr6_reflection_density_product hμ hh
  obtain ⟨K, hK⟩ := hh.1
  have hρ : ∀ v ∈ fsans μ '' unitDisc,
      0 < poincareDensity (fsans μ '' unitDisc) v ^ 2 := by
    intro v hv
    exact sq_pos_of_pos (s20l_a2_density_pos hΩ (hf.symm isOpen_ball) hv)
  have hm := hbPre_reflected_mass (q := q) hK hh.2.1 hρ hC.le
    (fun u hu => (hprod u hu).2)
  have hfin := hm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hq)
  have he : (∫⁻ w in unitDiscExterior,
      (‖hbPre_pullback (hbPre_reflected q h) (gsans μ) w‖₊ : ℝ≥0∞)^2 *
        ENNReal.ofReal (rho w)) =
      ∫⁻ u in gsans μ '' unitDiscExterior,
        ENNReal.ofReal (‖hbPre_reflected q h u‖^2 *
          poincareDensityNearInfty (gsans μ '' unitDiscExterior) u^2) := by
    calc _ = ∫⁻ w in unitDiscExterior,
        ENNReal.ofReal (‖hbPre_pullback (hbPre_reflected q h) (gsans μ) w‖^2) *
          ENNReal.ofReal (rho w) := by
            simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
      _ = _ := (hbPre_pullback_mass resolvent_exterior_isOpen hg).trans (by
        apply setLIntegral_congr_fun hE.measurableSet
        intro u hu
        dsimp only
        rw [← hbSurj_exterior_density hμ hu, ENNReal.ofReal_mul (sq_nonneg _)])
  unfold normL2
  rw [he]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

theorem crn_norm_le {q h : ℂ → ℂ} {u : ℂ}
    (hd : (1 / 2 : ℝ) ≤ ‖1 + (u - h u)^2 * (q (h u) / 2) * dz h u‖) :
    ‖crn_coefficient q h u‖ ≤ 2 * ‖hbPre_reflected q h u‖ := by
  rw [crn_coefficient, norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + (u - h u)^2 * (q (h u) / 2) * dz h u‖)).mpr
  nlinarith [norm_nonneg (hbPre_reflected q h u)]

/-- On any measurable collar with the actual denominator bounded below,
the nonlinear quotient has finite energy from the true relative Schwarzian. -/
theorem crn_schwarzian_collar_finite {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {S : Set ℂ} (hS : MeasurableSet S) (hSE : S ⊆ unitDiscExterior)
    (hd : ∀ w ∈ S, (1 / 2 : ℝ) ≤
      ‖1 + (gsans μ w - h (gsans μ w))^2 *
        (schwarzianHol (crs_transition μ ν) (h (gsans μ w)) / 2) * dz h (gsans μ w)‖) :
    normL2 S (hbPre_pullback (crn_coefficient (schwarzianHol (crs_transition μ ν)) h)
      (gsans μ)) < ∞ := by
  let q := schwarzianHol (crs_transition μ ν)
  let a := hbPre_pullback (crn_coefficient q h) (gsans μ)
  let b := hbPre_pullback (hbPre_reflected q h) (gsans μ)
  have hb := crn_raw_finite hμ hh (crs_schwarzian_energy hμ hν hP)
  have hpt : ∀ w ∈ S, ‖a w‖ ≤ 2 * ‖b w‖ := by
    intro w hw
    have hg := S2C.s2c_conf_g hμ
    have hder := deriv_ne_zero_of_injOn resolvent_exterior_isOpen hg.1 hg.2.1 (hSE hw)
    dsimp only [a, b]
    rw [hbPre_pullback_norm hder, hbPre_pullback_norm hder]
    exact crn_norm_le (hd w hw)
  have hi : (∫⁻ w in S, (‖a w‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w)) ≤
      4 * ∫⁻ w in unitDiscExterior, (‖b w‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w) := by
    calc _ ≤ ∫⁻ w in S, (4 : ℝ≥0∞) * ((‖b w‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS] with w hw
          have hn := ENNReal.ofReal_le_ofReal (hpt w hw)
          simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ofReal_norm, enorm_eq_nnnorm] at hn
          norm_num at hn
          calc _ ≤ (2 * (‖b w‖₊ : ℝ≥0∞))^2 * ENNReal.ofReal (rho w) := by gcongr
            _ = _ := by ring
      _ = 4 * ∫⁻ w in S, (‖b w‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho w) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ _ := by gcongr
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mpr
  exact hi.trans_lt (ENNReal.mul_lt_top (by norm_num)
    ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1/2)).mp hb))

end TakhtajanTeo
