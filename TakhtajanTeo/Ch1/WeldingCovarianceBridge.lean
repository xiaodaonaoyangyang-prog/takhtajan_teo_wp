import TakhtajanTeo.Ch1.NormalizedWelding

/-! # Local factorization and Wirtinger identities for the actual welding

Only the at-most-one finite pole of Model A is excluded. The derivative
identity is pointwise elsewhere in the exterior, using the holomorphic local
inverse of the exterior welding function, hence also holds almost everywhere.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wAS_finite_ae (μ : LinfStar) : ∀ᵐ z : ℂ, wAS μ (z : ExtPlane) ≠ extInf := by
  have hp : {z : ℂ | wAS μ (z : ExtPlane) = extInf}.Subsingleton := by
    intro z hz w hw
    exact OnePoint.coe_injective ((wAS_bijective μ).1 (hz.trans hw.symm))
  simpa only [ae_iff, not_not] using hp.finite.measure_zero volume

theorem wA_finite_domain_open {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsOpen {z : ℂ | wAS μ (z : ExtPlane) ≠ extInf} :=
  isOpen_compl_singleton.preimage ((wAS_continuous hμ).comp OnePoint.continuous_coe)

theorem wA_continuousOn_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ContinuousOn (wA μ) {z : ℂ | wAS μ (z : ExtPlane) ≠ extInf} := by
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_iff]
  apply ((wAS_continuous hμ).comp OnePoint.continuous_coe).continuousOn.congr
  intro z hz
  exact coe_finPart_of_ne hz

theorem normalizedWelding_factorization {μ : LinfStar} {z : ℂ}
    (hz : wAS μ (z : ExtPlane) ≠ extInf) :
    fB μ z = normalizedWeldingExterior μ (wA μ z) := by
  have he : (wA μ z : ExtPlane) = wAS μ z := coe_finPart_of_ne hz
  unfold normalizedWeldingExterior normalizedWeldingSphere
  rw [Function.comp_apply, he, Function.leftInverse_invFun (wAS_bijective μ).1]
  rfl

theorem normalizedWelding_factorization_germ {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : wAS μ (z : ExtPlane) ≠ extInf) :
    fB μ =ᶠ[𝓝 z] normalizedWeldingExterior μ ∘ wA μ := by
  filter_upwards [(wA_finite_domain_open hμ).mem_nhds hz] with w hw
  exact normalizedWelding_factorization hw

theorem normalizedWelding_factorization_germ_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      fB μ =ᶠ[𝓝 z] normalizedWeldingExterior μ ∘ wA μ := by
  filter_upwards [ae_restrict_of_ae (wAS_finite_ae μ)] with z hz
  exact normalizedWelding_factorization_germ hμ hz

theorem normalizedWelding_wirtinger {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ unitDiscExterior) (hfinite : wAS μ (z : ExtPlane) ≠ extInf) :
    dz (fB μ) z = deriv (normalizedWeldingExterior μ) (wA μ z) * dz (wA μ) z ∧
      dzbar (fB μ) z = deriv (normalizedWeldingExterior μ) (wA μ z) * dzbar (wA μ) z := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hAz : wA μ z ∈ unitDiscExterior := by
    rcases wAS_maps_ext hμ hz with h | ⟨u, hu, he⟩
    · exact (hfinite h).elim
    · change 1 < ‖finPart (wAS μ (z : ExtPlane))‖
      rw [he]
      exact hu
  have hAc : ContinuousAt (wA μ) z :=
    (wA_continuousOn_finite hμ).continuousAt ((wA_finite_domain_open hμ).mem_nhds hfinite)
  have hG : IsConformalOnto (normalizedWeldingExterior μ) unitDiscExterior
      (normalizedWeldingExterior μ '' unitDiscExterior) :=
    ⟨normalizedWeldingExterior_differentiableOn hμ,
      (normalizedWeldingExterior_bijective hμ).1.injOn, rfl⟩
  have hGo := isOpen_image_of_isKQC (isKQC_one_of_conformal hE hG)
  have hInv := hG.symm hE
  have hleft : ∀ᶠ w in 𝓝 (wA μ z),
      Function.invFunOn (normalizedWeldingExterior μ) unitDiscExterior
        (normalizedWeldingExterior μ w) = w := by
    filter_upwards [hE.mem_nhds hAz] with w hw
    exact hG.2.1.leftInvOn_invFunOn hw
  have hc := s23_wirtinger_comp_left hAc (hG.1.differentiableAt (hE.mem_nhds hAz))
    (hInv.1.differentiableAt (hGo.mem_nhds ⟨wA μ z, hAz, rfl⟩)) hleft
  have he := normalizedWelding_factorization_germ hμ hfinite
  have hdz : dz (fB μ) z = dz (normalizedWeldingExterior μ ∘ wA μ) z := by
    unfold dz
    rw [he.fderiv_eq]
  have hdzbar : dzbar (fB μ) z = dzbar (normalizedWeldingExterior μ ∘ wA μ) z := by
    unfold dzbar
    rw [he.fderiv_eq]
  rw [hdz, hdzbar]
  exact hc

theorem normalizedWelding_wirtinger_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      dz (fB μ) z = deriv (normalizedWeldingExterior μ) (wA μ z) * dz (wA μ) z ∧
        dzbar (fB μ) z = deriv (normalizedWeldingExterior μ) (wA μ z) * dzbar (wA μ) z := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  filter_upwards [ae_restrict_of_ae (wAS_finite_ae μ), ae_restrict_mem hE.measurableSet] with z hz hze
  exact normalizedWelding_wirtinger hμ hze hz

end TakhtajanTeo
