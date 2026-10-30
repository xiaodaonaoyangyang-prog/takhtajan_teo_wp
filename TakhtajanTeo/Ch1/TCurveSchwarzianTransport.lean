import TakhtajanTeo.Ch1.TCurveCoefficientTransport
import TakhtajanTeo.Ch1.TCurveMobiusAction

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Holomorphy on the disk upgrades the exterior coefficient to its actual
zero extension on the plane; the circle has area zero. -/
theorem tcg_plane_extB {μ : LinfStar} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisc)
    (hae : complexDilatation F =ᵐ[volume.restrict unitDiscExterior] (μ : ℂ → ℂ)) :
    complexDilatation F =ᵐ[volume] extB μ := by
  have hE := (ae_restrict_iff' bc_hEo.measurableSet).mp hae
  have hC : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 1)
  filter_upwards [hE, hC] with z he hc
  rcases lt_trichotomy ‖z‖ 1 with hz | hz | hz
  · have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz
    have hzE : z ∉ unitDiscExterior := fun h => (not_lt_of_ge hz.le) h
    rw [complexDilatation_eq_zero_of_diffAt (hF.differentiableAt (isOpen_ball.mem_nhds hzD)),
      extB, indicator_of_notMem hzE]
  · exact (hc (mem_sphere_zero_iff_norm.mpr hz)).elim
  · rw [he hz, extB, indicator_of_mem (show z ∈ unitDiscExterior from hz)]

/-- Any genuine plane solution gives the same Bers Schwarzian. -/
theorem tcg_bers_of_plane {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hFs : F '' univ = univ)
    (hFd : DifferentiableOn ℂ F unitDisc)
    (hFe : complexDilatation F =ᵐ[volume.restrict unitDiscExterior] (μ : ℂ → ℂ))
    {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (bersPhi μ) z = schwarzianHol F z := by
  have hN := AppA.acc_ns_spec hμ
  have hNae : complexDilatation (normalizedSolution (extB μ)) =ᵐ[volume] extB μ := hN.2.2.2.2
  obtain ⟨T, hT, he⟩ := uq_conformal_auto isOpen_univ ⟨K, hF⟩ hN.1 hFs hN.2.1 (by
    rw [Measure.restrict_univ]
    exact (tcg_plane_extB hFd hFe).trans hNae.symm)
  obtain ⟨a, b, ha, hab⟩ := nx_entire_affine hT
  have heq : normalizedSolution (extB μ) = fun w => a * F w + b := by
    funext w
    rw [he w (mem_univ w), hab]
  rw [(bersPhi_spec hμ).1 z hz, QCV.qcv_schwarzian_fB_eq hμ hz, heq]
  have hFa : AnalyticAt ℂ F z := hFd.analyticAt (isOpen_ball.mem_nhds hz)
  have hF' : deriv F z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hFd
    (hF.2.2.1.2.1.mono (subset_univ _)) hz
  have hpost := schwarzian_mobius_comp_of_ne hFa hF'
    (a := a) (b := b) (c := 0) (d := 1) (by simpa using ha) (by simp)
  have hAf : AnalyticAt ℂ (fun w => a * F w + b) z :=
    (analyticAt_const.mul hFa).add analyticAt_const
  simp only [zero_mul, zero_add, div_one] at hpost
  rw [schwarzian_of_analyticAt hAf, schwarzian_of_analyticAt hFa] at hpost
  exact hpost

/-- Every disk conformal automorphism has zero Schwarzian. -/
theorem tcg_disk_schwarzian_zero {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) : schwarzianHol S z = 0 := by
  obtain ⟨c, a, hc, ha, he⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hS
  have hg : S =ᶠ[𝓝 z] (fun w => c * blaschke a w) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => he hw)
  have hm : (fun w => c * blaschke a w) =
      (fun w => (c * w + -(c * a)) / (-conj a * w + 1)) := by
    funext w
    simp only [blaschke]
    ring
  have hd : c * 1 - -(c * a) * -conj a ≠ 0 := by
    have hne : (1 - ‖a‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg a]
    rw [show c * 1 - -(c * a) * -conj a = c * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) by
      push_cast; rw [← Complex.mul_conj']; ring]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hc]; norm_num))
      (Complex.ofReal_ne_zero.mpr hne)
  rw [← schwarzian_of_analyticAt (hS.1.analyticAt (isOpen_ball.mem_nhds hz)),
    schwarzian_congr (hg.filter_mono nhdsWithin_le_nhds), hm, schwarzian_mobius hd]

/-- Exact Bers pullback for the actual tcurve coefficient of a disk conformal extension. -/
theorem tcg_lambda_bers {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC (⇑e) univ K)
    (heE : e '' unitDiscExterior = unitDiscExterior)
    (hS : IsConformalOnto (⇑e.symm) unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (bersPhi (tcurveLambda ν e)) z =
      AInf.toFun (bersPhi ν) (e.symm z) * deriv (⇑e.symm) z ^ 2 := by
  have hN := AppA.acc_ns_spec hν
  obtain ⟨KN, hKN⟩ := hN.1
  have hes : e '' univ = univ := image_univ.trans e.surjective.range_eq
  have hLam := (tmi_lambda_props hν he hes heE).1
  have hNd : DifferentiableOn ℂ (normalizedSolution (extB ν)) unitDisc :=
    (QCV.qcv_planeSolution_conformal hν).1
  have hNe : complexDilatation (normalizedSolution (extB ν)) =ᵐ[volume.restrict unitDiscExterior]
      (ν : ℂ → ℂ) := by
    filter_upwards [ae_restrict_of_ae hN.2.2.2.2, ae_restrict_mem bc_hEo.measurableSet]
      with w hw hwE
    rw [hw]
    simp [extB, indicator_of_mem hwE]
  have hFd : DifferentiableOn ℂ (normalizedSolution (extB ν) ∘ e.symm) unitDisc :=
    hNd.comp hS.1 hS.mapsTo
  have hFK := thm7_1_comp (homeomorph_inverse_isKQC e he) hKN (subset_univ _)
  have hFs : (normalizedSolution (extB ν) ∘ e.symm) '' univ = univ := by
    rw [image_comp, image_univ.trans e.symm.surjective.range_eq, hN.2.1]
  rw [tcg_bers_of_plane hLam hFK hFs hFd
    (tcg_lambda_is_dilatation hν hKN hNe e he heE).symm hz]
  have hSa : AnalyticAt ℂ (⇑e.symm) z := hS.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hNa : AnalyticAt ℂ (normalizedSolution (extB ν)) (e.symm z) :=
    hNd.analyticAt (isOpen_ball.mem_nhds (hS.mapsTo hz))
  have hS' : deriv (⇑e.symm) z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hS.1 hS.2.1 hz
  have hN' : deriv (normalizedSolution (extB ν)) (e.symm z) ≠ 0 :=
    deriv_ne_zero_of_injOn isOpen_ball hNd
      (hKN.2.2.1.2.1.mono (subset_univ _)) (hS.mapsTo hz)
  have hchain := eq19_1_chain_rule hSa hS' hNa hN'
  rw [schwarzian_of_analyticAt (AnalyticAt.comp (f := (⇑e.symm)) hNa hSa),
    schwarzian_of_analyticAt hNa, schwarzian_of_analyticAt hSa,
    tcg_disk_schwarzian_zero hS hz, add_zero] at hchain
  rw [hchain, (bersPhi_spec hν).1 _ (hS.mapsTo hz), QCV.qcv_schwarzian_fB_eq hν (hS.mapsTo hz)]

/-- In particular the operation preserves the actual A2 norm of the Bers differential. -/
theorem tcg_lambda_bers_norm {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC (⇑e) univ K)
    (heE : e '' unitDiscExterior = unitDiscExterior)
    (hS : IsConformalOnto (⇑e.symm) unitDisc unitDisc) :
    normA2 unitDisc (AInf.toFun (bersPhi (tcurveLambda ν e))) =
      normA2 unitDisc (AInf.toFun (bersPhi ν)) := by
  exact (normA2_congr (D := unitDisc) isOpen_ball.measurableSet
    (fun z hz => tcg_lambda_bers hν e he heE hS hz)).trans (tcg_normA2_pullback hS _)

#print axioms tcg_bers_of_plane
#print axioms tcg_lambda_bers
#print axioms tcg_lambda_bers_norm
end TakhtajanTeo
