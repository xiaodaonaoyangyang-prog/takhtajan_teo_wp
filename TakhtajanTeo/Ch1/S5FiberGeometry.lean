import TakhtajanTeo.Ch1.S5WeldingRegularity
import TakhtajanTeo.Ch1.GroupOrigin
import TakhtajanTeo.Ch1.TCurveTopGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Actual fixed-fiber regularity, including the reciprocal coordinate at infinity. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem s5fg_uniformizer_analytic_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    AnalyticAt ℂ (fiberUniformizer μ) (gMu μ w)⁻¹ := by
  have hg : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨hI, hdI⟩ := RMT.differentiableOn_invFunOn_of_injOn hO hg.1 hg.2.1
  have hg0 := gMu_exterior_ne_zero hμ hw
  have hw0 : w ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hw
  have hi : Function.invFunOn (gMu μ) unitDiscExterior (gMu μ w) = w := hg.2.1.leftInvOn_invFunOn hw
  have hA : AnalyticAt ℂ (Function.invFunOn (gMu μ) unitDiscExterior) (gMu μ w)⁻¹⁻¹ := by
    simpa only [inv_inv] using hdI.analyticAt (hI.mem_nhds ⟨w, hw, rfl⟩)
  have hB := (hA.comp (analyticAt_id.inv (inv_ne_zero hg0))).inv
    (by simpa only [Function.comp_apply, inv_inv, hi] using hw0)
  apply hB.congr
  filter_upwards [eventually_ne_nhds (inv_ne_zero hg0)] with z hz
  simp [fiberUniformizer, hz]

theorem s5fg_uniformizer_analytic_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℂ (fiberUniformizer μ) 0 ∧ fiberUniformizer μ 0 = 0 ∧
      deriv (fiberUniformizer μ) 0 ≠ 0 := by
  let g := normalizedWeldingExterior μ
  have hbij : Function.Bijective g := normalizedWeldingExterior_bijective hμ
  have hproper : IsProperMap g := isProperMap_iff_tendsto_cocompact.mpr
    (normalizedWeldingExterior_continuous_proper hμ)
  let e : ℂ ≃ₜ ℂ := (Equiv.ofBijective g hbij).toHomeomorphOfContinuousClosed
    hproper.continuous hproper.isClosedMap
  have he : (e : ℂ → ℂ) = g := rfl
  have hO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hed : DifferentiableOn ℂ e unitDiscExterior := normalizedWeldingExterior_differentiableOn hμ
  obtain ⟨hI, hdI⟩ := RMT.differentiableOn_invFunOn_of_injOn hO hed e.injective.injOn
  have hsym : EqOn e.symm (Function.invFunOn e unitDiscExterior) (e '' unitDiscExterior) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [e.symm_apply_apply, e.injective.injOn.leftInvOn_invFunOn hz]
  have hc : IsConformalOnto e.symm (e '' unitDiscExterior) ((Homeomorph.refl ℂ) '' unitDiscExterior) := by
    refine ⟨hdI.congr hsym, e.symm.injective.injOn, ?_⟩
    rw [show ((Homeomorph.refl ℂ) : ℂ → ℂ) = id from rfl, image_id]
    simp only [← image_comp, Homeomorph.symm_comp_self, image_id]
  obtain ⟨ξ, hξa, hξ0, hξd, hξ⟩ := grp25z_transition_chart e (Homeomorph.refl ℂ) hc (fun z _ => by simp)
  have hInv : Tendsto (fun t : ℂ => t⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have hE : unitDiscExterior ∈ cocompact ℂ := by
    have heE : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by ext z; simp [unitDiscExterior]
    rw [heE]
    exact (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact
  have hs := ((isProperMap_iff_tendsto_cocompact.mp e.symm.isProperMap).2.comp hInv).eventually hE
  have hs' : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → e.symm t⁻¹ ∈ unitDiscExterior := by
    filter_upwards [eventually_nhdsWithin_iff.mp hs] with t ht
    exact ht
  have hEq : ξ =ᶠ[𝓝 (0 : ℂ)] fiberUniformizer μ := by
    filter_upwards [hs'] with t ht
    by_cases h0 : t = 0
    · subst t; simp [hξ0, fiberUniformizer]
    · rw [hξ t h0]
      have hv : gMu μ (e.symm t⁻¹) = t⁻¹ := by
        rw [gMu_eq_normalizedWeldingExterior hμ (ht h0)]
        exact e.apply_symm_apply _
      have hg : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
      have hi : Function.invFunOn (gMu μ) unitDiscExterior t⁻¹ = e.symm t⁻¹ := by
        conv_lhs => rw [← hv]
        exact hg.2.1.leftInvOn_invFunOn (ht h0)
      simp [fiberUniformizer, h0, hi]
  exact ⟨hξa.congr hEq, by simp [fiberUniformizer], hEq.deriv_eq ▸ hξd⟩

theorem s5fg_uniformizer_regular {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ζ : ℂ}
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    AnalyticAt ℂ (fiberUniformizer μ) ζ ∧ ‖fiberUniformizer μ ζ‖ < 1 ∧
      deriv (fiberUniformizer μ) ζ ≠ 0 := by
  rcases hζ with rfl | ⟨w, hw, rfl⟩
  · obtain ⟨ha, hv, hd⟩ := s5fg_uniformizer_analytic_zero hμ
    exact ⟨ha, by simp [hv], hd⟩
  · obtain ⟨hv, hd⟩ := s5wr_uniformizer_jet hμ hw
    have hg : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
    have hgd := RMT.deriv_ne_zero_of_injOn (isOpen_lt continuous_const continuous_norm) hg.1 hg.2.1 hw
    have hw0 : w ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hw
    refine ⟨s5fg_uniformizer_analytic_finite hμ hw, ?_, ?_⟩
    · rw [hv, norm_inv]
      exact inv_lt_one_of_one_lt₀ hw
    · rw [hd.deriv]
      exact div_ne_zero (pow_ne_zero _ (gMu_exterior_ne_zero hμ hw)) (mul_ne_zero (pow_ne_zero _ hw0) hgd)

theorem s5fg_norm_sq_analytic {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℝ (fun t => ‖f t‖ ^ 2) z := by
  have hre := (Complex.reCLM.analyticAt (f z)).comp hf.restrictScalars
  have him := (Complex.imCLM.analyticAt (f z)).comp hf.restrictScalars
  convert! (hre.mul hre).add (him.mul him) using 1
  funext t
  exact Complex.sq_norm (f t)

theorem s5fg_metric_realAnalytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ζ : ℂ}
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    AnalyticAt ℝ (fun t => Real.log (4 * ‖deriv (fiberUniformizer μ) t‖ ^ 2 /
      (1 - ‖fiberUniformizer μ t‖ ^ 2) ^ 2)) ζ := by
  obtain ⟨ha, hv, hd⟩ := s5fg_uniformizer_regular hμ hζ
  have hsq : 0 < 1 - ‖fiberUniformizer μ ζ‖ ^ 2 := by nlinarith [norm_nonneg (fiberUniformizer μ ζ)]
  have hn := s5fg_norm_sq_analytic ha.deriv
  have hb := s5fg_norm_sq_analytic ha
  have hnum : AnalyticAt ℝ (fun t => 4 * ‖deriv (fiberUniformizer μ) t‖ ^ 2) ζ := analyticAt_const.mul hn
  have hden : AnalyticAt ℝ (fun t => (1 - ‖fiberUniformizer μ t‖ ^ 2) ^ 2) ζ := (analyticAt_const.sub hb).pow 2
  have hrat := hnum.div hden (pow_ne_zero 2 hsq.ne')
  have hp : 0 < 4 * ‖deriv (fiberUniformizer μ) ζ‖ ^ 2 / (1 - ‖fiberUniformizer μ ζ‖ ^ 2) ^ 2 :=
    div_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hd) _)) (pow_pos hsq _)
  convert! (analyticAt_log hp).comp_of_eq hrat rfl using 1

theorem s5fg_actual_fiber_condition {p : T1} {z : ExtPlane} (hq : (p, z) ∈ TCurve) :
    finPart (inversion z) = 0 ∨ ∃ w ∈ unitDiscExterior,
      finPart (inversion z) = (gMu (Quotient.out p : LinfStarBall) w)⁻¹ := by
  let μ : LinfStar := (Quotient.out p : LinfStarBall)
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  change z ∈ wB μ '' extDiscExterior at hq
  rw [← tcg_welding_image hμ] at hq
  obtain ⟨u, hu, rfl⟩ := hq
  rcases hu with ⟨w, hw, rfl⟩ | hu
  · right
    refine ⟨w, hw, ?_⟩
    have hg := gMu_exterior_ne_zero hμ hw
    rw [← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw]
    simp [inversion, mobiusExt, hg, finPart]
    rfl
  · have hu' : u = extInf := hu
    subst u
    left
    rw [normalizedWeldingSphere_infty hμ]
    simp [inversion, mobiusExt, finPart, extInf]

theorem s5fg_logNormSq_fiber_analytic {p : T1} {z : ExtPlane} (hq : (p, z) ∈ TCurve) :
    AnalyticAt ℝ (fun ζ : ℂ => logNormSq (p, inversion (ζ : ExtPlane))) (finPart (inversion z)) := by
  have he : (fun ζ : ℂ => logNormSq (p, inversion (ζ : ExtPlane))) = fun ζ =>
      Real.log (4 * ‖deriv (fiberUniformizer (Quotient.out p : LinfStarBall)) ζ‖ ^ 2 /
        (1 - ‖fiberUniformizer (Quotient.out p : LinfStarBall) ζ‖ ^ 2) ^ 2) := by
    funext ζ
    unfold logNormSq
    rw [tcc_inversion_invol]
    rfl
  rw [he]
  exact s5fg_metric_realAnalytic (Quotient.out p : LinfStarBall).2 (s5fg_actual_fiber_condition hq)

theorem s5fg_coordInv_fiber {p : T1} {ζ : ℂ} (hx : (bers p, ζ) ∈ tcCoord '' TCurve) :
    tcCoordInv (bers p, ζ) = (p, inversion (ζ : ExtPlane)) := by
  obtain ⟨q, hq, hcoord⟩ := hx
  have hp : q.1 = p := by
    apply bers_isOpenEmbedding.injective
    exact congrArg Prod.fst hcoord
  have hz : finPart (inversion q.2) = ζ := congrArg Prod.snd hcoord
  have hzero : q.2 ≠ ((0 : ℂ) : ExtPlane) := by
    intro hh
    have hm : q.2 ∈ wB (Quotient.out q.1 : LinfStarBall) '' extDiscExterior := hq
    rw [hh] at hm
    exact tcc_zero_not_mem (Quotient.out q.1 : LinfStarBall).2 hm
  have hback : inversion ((finPart (inversion q.2) : ℂ) : ExtPlane) = q.2 := by
    rw [coe_finPart_of_ne ((tcc_inversion_eq_inf_iff q.2).not.mpr hzero), tcc_inversion_invol]
  have hi : tcCoordInv (tcCoord q) = q := tcCoord_chart.1.leftInvOn_invFunOn hq
  rw [← hcoord, hi]
  apply Prod.ext
  · exact hp
  · rw [← hz, hback]

theorem s5fg_logNormSq_chart_fiber_analytic {p : T1} {z : ExtPlane} (hq : (p, z) ∈ TCurve) :
    AnalyticAt ℝ (fun ζ : ℂ => logNormSq (tcCoordInv (bers p, ζ))) (finPart (inversion z)) := by
  have hx : (bers p, finPart (inversion z)) ∈ tcCoord '' TCurve := ⟨(p, z), hq, rfl⟩
  have hc : ContinuousAt (fun ζ : ℂ => (bers p, ζ)) (finPart (inversion z)) := by fun_prop
  have hev := hc (tcCoord_chart.2.mem_nhds hx)
  apply (s5fg_logNormSq_fiber_analytic hq).congr
  filter_upwards [hev] with ζ hζ
  rw [s5fg_coordInv_fiber hζ]

end TakhtajanTeo
