import TakhtajanTeo.Ch1.S7ResolventProbability

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Weighted Tonelli and symmetry preserve the integral of a nonnegative input. -/
theorem s7rl_mass_swap {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {a : ℂ → ℝ≥0∞} (ha : AEMeasurable a (volume.restrict D)) :
    (∫⁻ z in D, (∫⁻ w in D, ENNReal.ofReal (resolventKernel z w * rho w) * a w) *
      ENNReal.ofReal (rho z)) = ∫⁻ w in D, a w * ENNReal.ofReal (rho w) := by
  have hr : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by unfold rho; fun_prop
  have hr0 (z : ℂ) : 0 ≤ rho z := by unfold rho; positivity
  have hm : AEMeasurable (Function.uncurry fun z w : ℂ =>
      (a w * ENNReal.ofReal (rho w)) *
        (ENNReal.ofReal (resolventKernel z w) * ENNReal.ofReal (rho z)))
      ((volume.restrict D).prod (volume.restrict D)) :=
    (ha.comp_snd.mul hr.aemeasurable.comp_snd).mul
      (measurable_resolventKernel.ennreal_ofReal.aemeasurable.mul hr.aemeasurable.comp_fst)
  calc
    _ = ∫⁻ z in D, ∫⁻ w in D, (a w * ENNReal.ofReal (rho w)) *
        (ENNReal.ofReal (resolventKernel z w) * ENNReal.ofReal (rho z)) := by
      apply lintegral_congr
      intro z
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_mul' (hr0 w)]
      ring
    _ = ∫⁻ w in D, ∫⁻ z in D, (a w * ENNReal.ofReal (rho w)) *
        (ENNReal.ofReal (resolventKernel z w) * ENNReal.ofReal (rho z)) :=
      lintegral_lintegral_swap hm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
      have hk : Measurable (fun z => ENNReal.ofReal (resolventKernel z w) *
          ENNReal.ofReal (rho z)) :=
        (measurable_resolventKernel.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal.mul hr
      rw [lintegral_const_mul _ hk]
      have hmass : (∫⁻ z in D, ENNReal.ofReal (resolventKernel z w) *
          ENNReal.ofReal (rho z)) = 1 := by
        simp_rw [← ENNReal.ofReal_mul' (hr0 _), resolventKernel_symm _ w]
        rw [← ofReal_integral_eq_lintegral_ofReal (resolvent_mass_integrable hD hw)
          (resolvent_mass_nonneg_ae hD hw), RK4 hD hw]
        norm_num
      rw [hmass, mul_one]

/-- ENNReal form of the actual pointwise Jensen bound, suitable for Tonelli. -/
theorem s7rl_square_lintegral {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {z : ℂ} (hz : z ∈ D) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict D)) {C : ℝ}
    (hb : ∀ᵐ w ∂(volume.restrict D), ‖f w‖ ≤ C) :
    ENNReal.ofReal (‖resolventOp D f z‖ ^ 2) ≤
      ∫⁻ w in D, ENNReal.ofReal (resolventKernel z w * rho w) *
        ENNReal.ofReal (‖f w‖ ^ 2) := by
  have hbq : ∀ᵐ w ∂(volume.restrict D), ‖‖f w‖ ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [hb] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hi : Integrable (fun w => resolventKernel z w * ‖f w‖ ^ 2 * rho w)
      (volume.restrict D) := by
    apply ((resolvent_mass_integrable hD hz).mul_bdd (hf.norm.pow 2) hbq).congr
    exact Eventually.of_forall fun w => by dsimp; ring
  have hn : ∀ᵐ w ∂(volume.restrict D),
      0 ≤ resolventKernel z w * ‖f w‖ ^ 2 * rho w := by
    filter_upwards [resolvent_mass_nonneg_ae hD hz] with w hw
    nlinarith [sq_nonneg ‖f w‖, mul_nonneg hw (sq_nonneg ‖f w‖)]
  have hj := ENNReal.ofReal_le_ofReal (s7rp_square_bound hD hz hf hb)
  rw [ofReal_integral_eq_lintegral_ofReal hi hn] at hj
  refine hj.trans_eq ?_
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul' (sq_nonneg ‖f w‖)]
  congr 1
  ring

/-- The actual resolvent is a contraction for the hyperbolic L2 norm.
Boundedness is an input class condition, not an assumed bound on the output. -/
theorem s7rl_contraction {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D)) {C : ℝ}
    (hb : ∀ᵐ w ∂(volume.restrict D), ‖f w‖ ≤ C) :
    normL2 D (resolventOp D f) ≤ normL2 D f := by
  have ha : AEMeasurable (fun w => ENNReal.ofReal (‖f w‖ ^ 2)) (volume.restrict D) :=
    (hf.norm.pow 2).aemeasurable.ennreal_ofReal
  have hnorm (v : ℂ) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, enorm_eq_nnnorm]
  unfold normL2
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  simp_rw [hnorm]
  calc
    _ ≤ ∫⁻ z in D, (∫⁻ w in D, ENNReal.ofReal (resolventKernel z w * rho w) *
        ENNReal.ofReal (‖f w‖ ^ 2)) * ENNReal.ofReal (rho z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with z hz
      exact mul_le_mul' (s7rl_square_lintegral hD hz hf hb) le_rfl
    _ = _ := s7rl_mass_swap hD ha

/-- In particular, the smooth bounded forcing supplied for Proposition 7.2
has a potential of finite hyperbolic energy. -/
theorem s7rl_finite {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℂ} (hf : f ∈ BCinf D) (hn : normL2 D f < ∞) :
    normL2 D (resolventOp D f) < ∞ := by
  obtain ⟨C, hb⟩ := hf.2
  have hae : ∀ᵐ w ∂(volume.restrict D), ‖f w‖ ≤ C := by
    filter_upwards [ae_restrict_mem (resolvent_domain_isOpen hD).measurableSet] with w hw
    exact hb w hw
  exact (s7rl_contraction hD
    (hf.1.continuousOn.aestronglyMeasurable (resolvent_domain_isOpen hD).measurableSet) hae).trans_lt hn

end TakhtajanTeo
