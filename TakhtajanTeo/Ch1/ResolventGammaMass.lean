import TakhtajanTeo.Ch1.ResolventGamma

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem gam_mob_deriv {g : SL2C} {w : ℂ}
    (hD : g 1 0 * w + g 1 1 ≠ 0) :
    deriv (mob g) w = 1 / (g 1 0 * w + g 1 1) ^ 2 := by
  have h := hasDerivAt_mobius (a := g 0 0) (b := g 0 1) hD
  rw [fd_det g] at h
  exact h.deriv

theorem gam_rho_mob_jacobian {g : SL2C} (hg : IsSU11 g) {w : ℂ}
    (hD : g 1 0 * w + g 1 1 ≠ 0) :
    rho (mob g w) * ‖deriv (mob g) w‖ ^ 2 = rho w := by
  have hn : ‖g 1 0 * w + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  rw [gam_mob_deriv hD, norm_div, norm_one, norm_pow]
  unfold rho
  rw [su11_one_sub_norm_mob g hg w hD]
  field_simp

theorem gam_tile_weighted_kernel {g : SL2C} (hg : IsSU11 g)
    (F : Set ℂ) (z : ℂ) :
    (∫⁻ w in F, ENNReal.ofReal (resolventKernel z (mob g w) * rho w)) =
      ∫⁻ w in F, ENNReal.ofReal (‖deriv (mob g) w‖ ^ 2) *
        ENNReal.ofReal (resolventKernel z (mob g w) * rho (mob g w)) := by
  have hnull := (fd_denom_finite g).measure_zero volume
  have hgen : ∀ᵐ w : ℂ ∂volume, g 1 0 * w + g 1 1 ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hgen] with w hw
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  calc resolventKernel z (mob g w) * rho w =
      resolventKernel z (mob g w) * (rho (mob g w) * ‖deriv (mob g) w‖ ^ 2) := by
        rw [gam_rho_mob_jacobian hg hw]
    _ = _ := by ring

/-- Unfolding gives a finite mass before any real-valued series is assumed
summable; the sum here takes values in the extended nonnegative reals. -/
theorem gam_sum_tile_kernel_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∫⁻ w in F, ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) = 1 := by
  have hm : (∫⁻ w in unitDiscExterior,
      ENNReal.ofReal (resolventKernel z w * rho w)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (resolvent_mass_integrable (Or.inr rfl) hz)
      (resolvent_mass_nonneg_ae (Or.inr rfl) hz), RK4 (Or.inr rfl) hz]
    simp
  rw [← hm, fd_unfold hΓ hF]
  apply tsum_congr
  rintro ⟨_, g, hg, rfl⟩
  exact gam_tile_weighted_kernel (hΓ.1 g hg) F z

theorem gam_action_measurable (Γ : Subgroup SL2C)
    (a : (fun g : SL2C => mob g) '' (Γ : Set SL2C)) :
    Measurable (a : ℂ → ℂ) := by
  obtain ⟨g, hg, heq⟩ := a.property
  rw [← heq]
  exact fd_measurable_mob g

theorem gam_rho_measurable : Measurable rho :=
  measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)

theorem gam_kernel_comp_measurable (f : ℂ → ℂ) (hf : Measurable f) (z : ℂ) :
    Measurable (fun w => resolventKernel z (f w)) := by
  have hp : Measurable (fun w => pointPair z (f w)) := by
    unfold pointPair
    fun_prop
  unfold resolventKernel
  fun_prop

theorem gam_weighted_comp_measurable (f : ℂ → ℂ) (hf : Measurable f) (z : ℂ) :
    Measurable (fun w => ENNReal.ofReal (resolventKernel z (f w) * rho w)) :=
  ((gam_kernel_comp_measurable f hf z).mul gam_rho_measurable).ennreal_ofReal

theorem gam_weighted_action_measurable (Γ : Subgroup SL2C)
    (a : (fun g : SL2C => mob g) '' (Γ : Set SL2C)) (z : ℂ) :
    Measurable (fun w => ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) :=
  gam_weighted_comp_measurable (a : ℂ → ℂ) (gam_action_measurable Γ a) z

theorem gam_weighted_series_measurable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    (z : ℂ) : Measurable (fun w =>
      ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  exact Measurable.ennreal_tsum (fun a => gam_weighted_action_measurable Γ a z)

theorem gam_weighted_series_integral {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫⁻ w in F, ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) = 1 := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  rw [lintegral_tsum (fun a => (gam_weighted_action_measurable Γ a z).aemeasurable)]
  exact gam_sum_tile_kernel_mass hΓ hF hz

theorem gam_weighted_series_finite_ae {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∀ᵐ w ∂(volume.restrict F),
      (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) < ∞ := by
  apply ae_lt_top (gam_weighted_series_measurable hΓ z)
  rw [gam_weighted_series_integral hΓ hF hz]
  exact ENNReal.one_ne_top

theorem gam_mob_fiber_finite (g : SL2C) {z : ℂ} (hz : z ≠ 0) :
    {w : ℂ | mob g w = z}.Finite := by
  apply (Set.finite_singleton (mob g⁻¹ z)).subset
  intro w hw
  have hD : g 1 0 * w + g 1 1 ≠ 0 := by
    intro hzero
    have heq : mob g w = 0 := by simp [mob, hzero]
    exact hz (hw.symm.trans heq)
  have hback := (fd_inv_step g hD).2
  rw [hw] at hback
  exact hback.symm

theorem gam_ae_off_orbit {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ w : ℂ ∂volume, ∀ g ∈ Γ, mob g w ≠ z := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable Γ := (fd_countable (Γ := Γ)).to_subtype
  have heach : ∀ g : Γ, ∀ᵐ w : ℂ ∂volume, mob g.val w ≠ z := by
    intro g
    exact measure_eq_zero_iff_ae_notMem.mp ((gam_mob_fiber_finite g.val hz).measure_zero volume)
  filter_upwards [ae_all_iff.mpr heach] with w hw
  intro g hg
  exact hw ⟨g, hg⟩

theorem gam_series_summable_of_weighted_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖)
    (hoff : ∀ g ∈ Γ, mob g w ≠ z)
    (hfinite : (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) < ∞) :
    Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) w)) := by
  have hρ : 0 < rho w := by
    unfold rho
    apply div_pos (by norm_num)
    apply sq_pos_of_ne_zero
    nlinarith
  apply (summable_mul_right_iff hρ.ne').mp
  apply (ENNReal.summable_toReal hfinite.ne).congr
  rintro ⟨_, g, hg, rfl⟩
  apply ENNReal.toReal_ofReal
  apply mul_nonneg _ hρ.le
  apply (gam_K_pos hz _ (hoff g hg)).le
  by_cases hD : g 1 0 * w + g 1 1 = 0
  · exact Or.inr (by simp [mob, hD])
  · exact Or.inl (fd_mob_exterior (hΓ.1 g hg) hw hD)

theorem gam_series_summable_ae_fundDomain {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∀ᵐ w ∂(volume.restrict F),
      Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        resolventKernel z ((a : ℂ → ℂ) w)) := by
  have hz0 : z ≠ 0 := by intro hzero; norm_num [hzero, unitDiscExterior] at hz
  filter_upwards [gam_weighted_series_finite_ae hΓ hF hz,
    ae_restrict_of_ae (gam_ae_off_orbit hΓ hz0), ae_restrict_mem hF.1] with w hf hoff hw
  exact gam_series_summable_of_weighted_finite hΓ hz (hF.2.1 hw) hoff hf

theorem gam_weighted_series_toReal_ae {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (fun w => resolventKernelGamma Γ z w * rho w) =ᵐ[volume.restrict F]
      (fun w => (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)).toReal) := by
  have hz0 : z ≠ 0 := by intro hzero; norm_num [hzero, unitDiscExterior] at hz
  filter_upwards [gam_series_summable_ae_fundDomain hΓ hF hz,
    ae_restrict_of_ae (gam_ae_off_orbit hΓ hz0), ae_restrict_mem hF.1] with w hs hoff hw
  have hnonneg : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      0 ≤ resolventKernel z ((a : ℂ → ℂ) w) * rho w := by
    rintro ⟨_, g, hg, rfl⟩
    apply mul_nonneg _ (by unfold rho; positivity)
    apply (gam_K_pos hz _ (hoff g hg)).le
    by_cases hD : g 1 0 * w + g 1 1 = 0
    · exact Or.inr (by simp [mob, hD])
    · exact Or.inl (fd_mob_exterior (hΓ.1 g hg) (hF.2.1 hw) hD)
  have heq := congrArg ENNReal.toReal
    (ENNReal.ofReal_tsum_of_nonneg hnonneg (hs.mul_right (rho w)))
  rw [ENNReal.toReal_ofReal (tsum_nonneg hnonneg), tsum_mul_right] at heq
  exact heq

theorem gam_kernel_integral_fundDomain {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundDomain Γ F) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ w in F, resolventKernelGamma Γ z w * rho w) = 1 := by
  rw [integral_congr_ae (gam_weighted_series_toReal_ae hΓ hF hz)]
  rw [integral_toReal (gam_weighted_series_measurable hΓ z).aemeasurable
    (gam_weighted_series_finite_ae hΓ hF hz), gam_weighted_series_integral hΓ hF hz]
  simp

/-- The quotient mass clause of (1.20), with the original kernel and chosen
fundamental domain. No pointwise convergence is assumed. -/
theorem gam_quotient_kernel_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    quotientIntegral Γ (fun w => resolventKernelGamma Γ z w * rho w) = 1 := by
  unfold quotientIntegral
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  rw [gam_kernel_integral_fundDomain hΓ (isFundDomain_fundDomain hΓ) hz]
  simp

end TakhtajanTeo
