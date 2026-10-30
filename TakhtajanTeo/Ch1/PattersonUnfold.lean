import TakhtajanTeo.Ch1.PattersonCounting

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem pat_orbit_real_integrable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun w => (patOrbitDensity Γ r w).toReal) (fundDomain Γ) := by
  apply integrable_toReal_of_lintegral_ne_top (pat_orbit_density_measurable hΓ r).aemeasurable
  rw [pat_orbit_density_mass hΓ hr]
  exact ENNReal.ofReal_ne_top

theorem pat_nonneg_real_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {h : ℂ → ℝ} (hm : Measurable h) (hn : ∀ w, 0 ≤ h w)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫ w in discExteriorR r, h w * rho w) =
      ∫ w in fundDomain Γ, h w * (patOrbitDensity Γ r w).toReal := by
  have he := pat_orbit_test_unfold hΓ r hm.ennreal_ofReal (fun g hg =>
    (ha g hg).mono fun w hw => congrArg ENNReal.ofReal hw)
  have hl : (∫ w in discExteriorR r, h w * rho w) =
      (∫⁻ w in discExteriorR r, ENNReal.ofReal (h w) * ENNReal.ofReal (rho w)).toReal := by
    have hnn : ∀ᵐ w ∂volume.restrict (discExteriorR r), 0 ≤ h w * rho w :=
      Eventually.of_forall fun w => mul_nonneg (hn w) (div_nonneg (by norm_num) (sq_nonneg _))
    calc _ = (∫⁻ w in discExteriorR r, ENNReal.ofReal (h w * rho w)).toReal :=
        integral_eq_lintegral_of_nonneg_ae hnn (hm.mul gam_rho_measurable).aestronglyMeasurable
      _ = _ := by
        congr 1
        apply lintegral_congr_ae
        exact Eventually.of_forall fun w => ENNReal.ofReal_mul (hn w)
  have hmprod := hm.ennreal_ofReal.mul (pat_orbit_density_measurable hΓ r)
  have ht : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      ENNReal.ofReal (h w) * patOrbitDensity Γ r w < ∞ := by
    filter_upwards [pat_orbit_density_finite_ae hΓ hr] with w hw
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw
  have hi := integral_toReal hmprod.aemeasurable ht
  change (∫ w in fundDomain Γ, (ENNReal.ofReal (h w) * patOrbitDensity Γ r w).toReal) =
    (∫⁻ w in fundDomain Γ, ENNReal.ofReal (h w) * patOrbitDensity Γ r w).toReal at hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hn _)] at hi
  exact hl.trans ((congrArg ENNReal.toReal he).trans hi.symm)

theorem pat_real_bounded_weight_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {h f : α → ℝ} {C : ℝ} (hf : Integrable f μ)
    (hm : AEStronglyMeasurable h μ) (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ C) :
    Integrable (fun x => h x * f x) μ := by
  apply (hf.norm.const_mul C).mono' (hm.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖h x * f x‖ ≤ C * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem pat_pos_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; ring

theorem pat_real_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {r : ℝ} (hr : 1 < r)
    {h : ℂ → ℝ} {C : ℝ} (hm : Measurable h)
    (hb : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖h w‖ ≤ C)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫ w in discExteriorR r, h w * rho w) =
      ∫ w in fundDomain Γ, h w * (patOrbitDensity Γ r w).toReal := by
  let hp : ℂ → ℝ := fun w => max (h w) 0
  let hn : ℂ → ℝ := fun w => max (-h w) 0
  have hpm : Measurable hp := hm.max measurable_const
  have hnm : Measurable hn := hm.neg.max measurable_const
  have hpbd : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖hp w‖ ≤ C := by
    filter_upwards [hb] with w hw
    change ‖max (h w) 0‖ ≤ C
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact (max_le (le_abs_self _) (abs_nonneg _)).trans hw
  have hnbd : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖hn w‖ ≤ C := by
    filter_upwards [hb] with w hw
    change ‖max (-h w) 0‖ ≤ C
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    have hh := max_le (le_abs_self (-h w)) (abs_nonneg (-h w))
    rw [abs_neg] at hh
    exact hh.trans hw
  have hpaut : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, hp (mob g w) = hp w := by
    intro g hg
    filter_upwards [ha g hg] with w hw
    simp only [hp, hw]
  have hnaut : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, hn (mob g w) = hn w := by
    intro g hg
    filter_upwards [ha g hg] with w hw
    simp only [hn, hw]
  have hep := pat_nonneg_real_unfold hΓ hr hpm (fun _ => le_max_right _ _) hpaut
  have hen := pat_nonneg_real_unfold hΓ hr hnm (fun _ => le_max_right _ _) hnaut
  have hsplit (w : ℂ) : hp w - hn w = h w := pat_pos_neg _
  have hRS : discExteriorR r ⊆ unitDiscExterior := fun _ hw => hw.1
  have hpR := pat_real_bounded_weight_integrable (pat_rho_integrable hr)
    hpm.aestronglyMeasurable (ae_restrict_of_ae_restrict_of_subset hRS hpbd)
  have hnR := pat_real_bounded_weight_integrable (pat_rho_integrable hr)
    hnm.aestronglyMeasurable (ae_restrict_of_ae_restrict_of_subset hRS hnbd)
  have hpF := pat_real_bounded_weight_integrable (pat_orbit_real_integrable hΓ hr)
    hpm.aestronglyMeasurable (ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) hpbd)
  have hnF := pat_real_bounded_weight_integrable (pat_orbit_real_integrable hΓ hr)
    hnm.aestronglyMeasurable (ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) hnbd)
  calc _ = ∫ w in discExteriorR r, hp w * rho w - hn w * rho w := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          change h w * rho w = hp w * rho w - hn w * rho w
          rw [← sub_mul, hsplit]
    _ = (∫ w in discExteriorR r, hp w * rho w) -
        (∫ w in discExteriorR r, hn w * rho w) := integral_sub hpR hnR
    _ = (∫ w in fundDomain Γ, hp w * (patOrbitDensity Γ r w).toReal) -
        (∫ w in fundDomain Γ, hn w * (patOrbitDensity Γ r w).toReal) := by rw [hep, hen]
    _ = _ := by
      rw [← integral_sub hpF hnF]
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        change hp w * (patOrbitDensity Γ r w).toReal - hn w * (patOrbitDensity Γ r w).toReal =
          h w * (patOrbitDensity Γ r w).toReal
        rw [← sub_mul, hsplit]

theorem pat_complex_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {r : ℝ} (hr : 1 < r)
    {h : ℂ → ℂ} {C : ℝ} (hm : Measurable h)
    (hb : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖h w‖ ≤ C)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫ w in discExteriorR r, h w * (rho w : ℂ)) =
      ∫ w in fundDomain Γ, h w * ((patOrbitDensity Γ r w).toReal : ℂ) := by
  have hR := pat_bounded_integrable hr hm.aestronglyMeasurable hb
  have hF := pat_bounded_weight_integrable (pat_orbit_real_integrable hΓ hr)
    hm.aestronglyMeasurable (ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) hb)
  have hbr : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖(h w).re‖ ≤ C := by
    filter_upwards [hb] with w hw
    exact (Complex.abs_re_le_norm _).trans hw
  have hbi : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖(h w).im‖ ≤ C := by
    filter_upwards [hb] with w hw
    exact (Complex.abs_im_le_norm _).trans hw
  have har : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, (h (mob g w)).re = (h w).re := by
    intro g hg
    exact (ha g hg).mono fun _ he => congrArg Complex.re he
  have hai : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, (h (mob g w)).im = (h w).im := by
    intro g hg
    exact (ha g hg).mono fun _ he => congrArg Complex.im he
  apply Complex.ext
  · have eR : (∫ w in discExteriorR r, h w * (rho w : ℂ)).re =
        ∫ w in discExteriorR r, (h w * (rho w : ℂ)).re := (integral_re hR).symm
    have eF : (∫ w in fundDomain Γ, h w * ((patOrbitDensity Γ r w).toReal : ℂ)).re =
        ∫ w in fundDomain Γ, (h w * ((patOrbitDensity Γ r w).toReal : ℂ)).re := (integral_re hF).symm
    rw [eR, eF]
    simpa only [Function.comp_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      pat_real_unfold hΓ hr (Complex.measurable_re.comp hm) hbr har
  · have eR : (∫ w in discExteriorR r, h w * (rho w : ℂ)).im =
        ∫ w in discExteriorR r, (h w * (rho w : ℂ)).im := (integral_im hR).symm
    have eF : (∫ w in fundDomain Γ, h w * ((patOrbitDensity Γ r w).toReal : ℂ)).im =
        ∫ w in fundDomain Γ, (h w * ((patOrbitDensity Γ r w).toReal : ℂ)).im := (integral_im hF).symm
    rw [eR, eF]
    simpa only [Function.comp_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using
      pat_real_unfold hΓ hr (Complex.measurable_im.comp hm) hbi hai

theorem pat_complex_probability_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {h : ℂ → ℂ} {C : ℝ} (hm : Measurable h)
    (hb : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖h w‖ ≤ C)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫ w in discExteriorR r, h w * (rho w : ℂ)) / (4 * π / (r ^ 2 - 1) : ℝ) =
      ∫ w in fundDomain Γ, h w * ((patProbabilityDensity Γ r w).toReal : ℂ) := by
  rw [pat_complex_unfold hΓ hr hm hb ha, ← integral_div]
  have hA : 0 ≤ 4 * π / (r ^ 2 - 1) :=
    le_of_lt (div_pos (mul_pos (by norm_num) Real.pi_pos) (by nlinarith))
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change (h w * ((patOrbitDensity Γ r w).toReal : ℂ)) / (4 * π / (r ^ 2 - 1) : ℝ) =
      h w * ((patProbabilityDensity Γ r w).toReal : ℂ)
    rw [patProbabilityDensity, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hA]
    push_cast
    ring

theorem pat_measurable_automorphic_representative {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {h : ℂ → ℂ} (hm : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    ∃ k : ℂ → ℂ, Measurable k ∧ k =ᵐ[volume.restrict unitDiscExterior] h ∧
      ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, k (mob g w) = k w := by
  let k := hm.mk h
  have he : k =ᵐ[volume.restrict unitDiscExterior] h := hm.ae_eq_mk.symm
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hall : ∀ᵐ w ∂volume, w ∈ unitDiscExterior → k w = h w :=
    (ae_restrict_iff' hext).mp he
  refine ⟨k, hm.stronglyMeasurable_mk.measurable, he, ?_⟩
  intro g hg
  filter_upwards [he, ha g hg, ae_restrict_of_ae (qf_mob_ae_pullback g hall),
    ae_restrict_of_ae (compl_mem_ae_iff.mpr ((fd_denom_finite g).measure_zero volume)),
    ae_restrict_mem hext] with w hew haw hpull hd hw
  have hD : g 1 0 * w + g 1 1 ≠ 0 := hd
  have hgw := (qf_mob_exterior_iff (hΓ.1 g hg) hD).mpr hw
  exact (hpull hgw).trans (haw.trans hew.symm)

theorem pat_complex_probability_unfold_ae {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {h : ℂ → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hb : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖h w‖ ≤ C)
    (ha : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w) :
    (∫ w in discExteriorR r, h w * (rho w : ℂ)) / (4 * π / (r ^ 2 - 1) : ℝ) =
      ∫ w in fundDomain Γ, h w * ((patProbabilityDensity Γ r w).toReal : ℂ) := by
  obtain ⟨k, hkm, he, hka⟩ := pat_measurable_automorphic_representative hΓ hm ha
  have hkb : ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖k w‖ ≤ C := by
    filter_upwards [he, hb] with w hew hbw
    simpa only [hew] using hbw
  have hk := pat_complex_probability_unfold hΓ hr hkm hkb hka
  have eR : (∫ w in discExteriorR r, k w * (rho w : ℂ)) =
      ∫ w in discExteriorR r, h w * (rho w : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (show discExteriorR r ⊆ unitDiscExterior from fun _ hw => hw.1) he] with w hew
    exact congrArg (fun v : ℂ => v * (rho w : ℂ)) hew
  have eF : (∫ w in fundDomain Γ, k w * ((patProbabilityDensity Γ r w).toReal : ℂ)) =
      ∫ w in fundDomain Γ, h w * ((patProbabilityDensity Γ r w).toReal : ℂ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (fundDomain_subset Γ) he] with w hew
    exact congrArg (fun v : ℂ => v * ((patProbabilityDensity Γ r w).toReal : ℂ)) hew
  rwa [eR, eF] at hk

/-- The exact original Patterson average, conditional on the actual orbit-count
asymptotic. This extra premise has not been proved and is not an axiom. -/
theorem pat_average_limit_of_counting_asymptotic {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    {h : ℂ → ℂ} (hmeas : AEStronglyMeasurable h (volume.restrict unitDiscExterior))
    (hbdd : ∃ C, ∀ᵐ w ∂volume.restrict unitDiscExterior, ‖h w‖ ≤ C)
    (haut : ∀ g ∈ Γ, ∀ᵐ w ∂volume.restrict unitDiscExterior, h (mob g w) = h w)
    (hcount : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patOrbitCount Γ r w : ℝ) / (4 * π / (r ^ 2 - 1)))
        (𝓝[>] 1) (𝓝 ((hypArea Γ).toReal)⁻¹)) :
    Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ w in discExteriorR r, rho w) : ℂ) *
        ∫ w in discExteriorR r, h w * rho w)
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ (fun w => h w * rho w))) := by
  have ht := pat_orbit_test_limit_of_ae_limit hΓ hmeas hbdd
    (pat_density_limit_of_counting_asymptotic hΓ hcount)
  have hA : ((hypArea Γ).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pat_hypArea_toReal_pos hΓ).ne'
  have ht' : Tendsto (fun r : ℝ => ((hypArea Γ).toReal : ℂ) *
      ∫ w in fundDomain Γ, h w * ((patProbabilityDensity Γ r w).toReal : ℂ))
      (𝓝[>] 1) (𝓝 (quotientIntegral Γ (fun w => h w * rho w))) := by
    have hh := ht.const_mul ((hypArea Γ).toReal : ℂ)
    convert hh using 1
    field_simp
  apply ht'.congr'
  obtain ⟨C, hC⟩ := hbdd
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [pat_rho_integral hr, ← pat_complex_probability_unfold_ae hΓ.1 hr hmeas hC haut]
  push_cast
  ring

end TakhtajanTeo
