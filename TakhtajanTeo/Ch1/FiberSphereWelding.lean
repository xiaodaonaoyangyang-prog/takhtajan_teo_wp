import TakhtajanTeo.Ch1.SphereWeldingTransport

/-! Candidate spherical fiber welding. This module does not alter the frozen
original `fiber_welding` statement. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def fiberWeldingSphere (μ : LinfStar) (w : ℂ) : ExtPlane → ExtPlane :=
  mobiusExt 1 0 (-1 / gMu μ w) 1 ∘ normalizedWeldingSphere μ ∘ sigmaInvSphere (w : ExtPlane)

def fiberWeldingExterior (μ : LinfStar) (w z : ℂ) : ℂ :=
  finPart (fiberWeldingSphere μ w (z : ExtPlane))

theorem sigmaSphere_isMobius {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsMobius (sigmaSphere (w : ExtPlane)) :=
  ⟨_, _, _, _, sigmaSphere_det hw, rfl⟩

theorem sigmaInvSphere_isMobius {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsMobius (sigmaInvSphere (w : ExtPlane)) := by
  refine ⟨_, _, _, _, ?_, rfl⟩
  convert sigmaSphere_det hw using 1 <;> ring

theorem sigmaInvSphere_apply_sigma {w : ℂ} (hw : w ∈ unitDiscExterior) (p : ExtPlane) :
    sigmaInvSphere (w : ExtPlane) (sigmaSphere (w : ExtPlane) p) = p :=
  (mobiusHomeomorph _ _ _ _ (sigmaSphere_det hw)).left_inv p

theorem sigmaInvSphere_infty {w : ℂ} (hw : w ∈ unitDiscExterior) :
    sigmaInvSphere (w : ExtPlane) extInf = (w : ExtPlane) := by
  rw [← sigmaSphere_pole (w : ExtPlane), sigmaInvSphere_apply_sigma hw]

theorem gMu_exterior_ne_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) : gMu μ w ≠ 0 := by
  obtain ⟨u, hu, he⟩ := wAS_maps_disc hμ (z := 0) (by norm_num)
  have hau : wA μ 0 = u := congrArg finPart he
  have hG0 : normalizedWeldingExterior μ (wA μ 0) = 0 := by
    rw [normalizedWeldingExterior_closedDisk hμ (by simp), (fB_normalization μ).1]
  intro hn
  rw [gMu_eq_normalizedWeldingExterior hμ hw] at hn
  have hw0 := (normalizedWeldingExterior_bijective hμ).1 (hn.trans hG0.symm)
  rw [hau] at hw0
  subst w
  exact (not_lt.mpr hu.le) hw

theorem fiberWeldingSphere_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) : fiberWeldingSphere μ w extInf = extInf := by
  change mobiusExt 1 0 (-1 / gMu μ w) 1
    (normalizedWeldingSphere μ (sigmaInvSphere (w : ExtPlane) extInf)) = _
  rw [sigmaInvSphere_infty hw, ← normalizedWeldingExterior_coe hμ,
    ← gMu_eq_normalizedWeldingExterior hμ hw]
  apply mobiusExt_coe_of_eq_zero
  field_simp [gMu_exterior_ne_zero hμ hw]
  norm_num

theorem fiberWeldingSphere_continuous_bijective {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    Continuous (fiberWeldingSphere μ w) ∧ Function.Bijective (fiberWeldingSphere μ w) := by
  have hL : IsMobius (mobiusExt 1 0 (-1 / gMu μ w) 1) := ⟨1, 0, _, 1, by simp, rfl⟩
  have hLc := mobius_sphere_continuous_bijective hL
  have hSc := mobius_sphere_continuous_bijective (sigmaInvSphere_isMobius hw)
  exact ⟨hLc.1.comp ((normalizedWeldingSphere_continuous hμ).comp hSc.1),
    hLc.2.comp ((normalizedWeldingSphere_bijective μ).comp hSc.2)⟩

theorem fiberWeldingExterior_coe {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) (z : ℂ) :
    (fiberWeldingExterior μ w z : ExtPlane) = fiberWeldingSphere μ w (z : ExtPlane) :=
  sphereFinite_coe (fiberWeldingSphere_continuous_bijective hμ hw).2
    (fiberWeldingSphere_infty hμ hw) z

theorem fiberWeldingExterior_quasiconformal {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsQuasiconformal (fiberWeldingExterior μ w) univ := by
  obtain ⟨K, hK⟩ := normalizedWeldingExterior_quasiconformal hμ
  exact ⟨K, sphereTransport_isKQC (normalizedWeldingSphere_bijective μ)
    (normalizedWeldingSphere_continuous hμ) (fun z => (normalizedWeldingExterior_coe hμ z).symm)
    hK (sigmaInvSphere_isMobius hw) ⟨1, 0, _, 1, by simp, rfl⟩
    (fiberWeldingSphere_infty hμ hw)⟩

theorem fiberWeldingExterior_isUnivalentAtInfty {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsUnivalentAtInfty (fiberWeldingExterior μ w) := by
  have hsc := fiberWeldingSphere_continuous_bijective hμ hw
  have hsi := fiberWeldingSphere_infty hμ hw
  refine ⟨?_, (sphereFinite_bijective hsc.2 hsi).1.injOn,
    (sphereFinite_continuous_proper hsc.2 hsc.1 hsi).2⟩
  exact sphereTransport_differentiableOn (normalizedWeldingSphere_bijective μ)
    (normalizedWeldingSphere_continuous hμ) (fun z => (normalizedWeldingExterior_coe hμ z).symm)
    (normalizedWeldingExterior_differentiableOn hμ) (sigmaInvSphere_isMobius hw)
    ⟨1, 0, _, 1, by simp, rfl⟩ (sigmaSphere_mapsTo (Or.inl ⟨w, hw, rfl⟩)).2 hsi

theorem fiberWeldingExterior_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w z u : ℂ} (hw : w ∈ unitDiscExterior) (hz : z ∈ unitDiscExterior)
    (hu : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = (u : ExtPlane)) :
    fiberWeldingExterior μ w z = lambdaW (-1 / gMu μ w) (gMu μ u) := by
  have huE : u ∈ unitDiscExterior := by
    have he := (sigmaSphere_mapsTo (Or.inl ⟨w, hw, rfl⟩)).2 (Or.inl ⟨z, hz, rfl⟩)
    rw [hu] at he
    simpa [extDiscExterior, toExt] using he
  have hval : fiberWeldingSphere μ w (z : ExtPlane) =
      mobiusExt 1 0 (-1 / gMu μ w) 1 (gMu μ u : ExtPlane) := by
    change mobiusExt _ _ _ _ (normalizedWeldingSphere μ _) = _
    rw [hu, ← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ huE]
  have hden : (-1 / gMu μ w) * gMu μ u + 1 ≠ 0 := by
    intro hd
    rw [mobiusExt_coe_of_eq_zero hd] at hval
    exact OnePoint.coe_ne_infty _ ((fiberWeldingExterior_coe hμ hw z).trans hval)
  unfold fiberWeldingExterior
  rw [hval, mobiusExt_coe hden]
  simp [finPart, mobiusFn, lambdaW]

theorem sigmaW_invFun_of_finite_inverse {w z u : ℂ} (hw : w ∈ unitDiscExterior)
    (hz : z ∈ unitDiscExterior)
    (hu : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = (u : ExtPlane)) :
    Function.invFun (sigmaW w) z = u := by
  have hsz := sigmaSphere_inv_apply (Or.inl ⟨w, hw, rfl⟩) (z : ExtPlane)
  rw [hu] at hsz
  have huw : u ≠ w := by
    intro hh
    rw [hh, sigmaSphere_pole] at hsz
    exact OnePoint.coe_ne_infty z hsz.symm
  have he : sigmaW w u = z := by
    rw [sigmaSphere_coe_eq hw huw] at hsz
    exact OnePoint.coe_injective hsz
  have hi := Function.invFun_eq (f := sigmaW w) ⟨u, he⟩
  have hqw : Function.invFun (sigmaW w) z ≠ w := by
    intro hh
    rw [hh] at hi
    have hwzero : sigmaW w w = 0 := by simp [sigmaW]
    rw [hwzero] at hi
    rw [← hi] at hz
    norm_num [unitDiscExterior] at hz
  apply OnePoint.coe_injective
  apply isMobius_injective (sigmaSphere_isMobius hw)
  rw [sigmaSphere_coe_eq hw hqw, sigmaSphere_coe_eq hw huw, hi, he]

theorem fiberWeldingExterior_original_coordinates {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w z : ℂ} (hw : w ∈ unitDiscExterior) (hz : z ∈ unitDiscExterior)
    (hp : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) ≠ extInf) :
    fiberWeldingExterior μ w z =
      lambdaW (-1 / gMu μ w) (gMu μ (Function.invFun (sigmaW w) z)) := by
  have hu := (coe_finPart_of_ne hp).symm
  rw [sigmaW_invFun_of_finite_inverse hw hz hu]
  exact fiberWeldingExterior_finite hμ hw hz hu

theorem fiberWeldingExterior_at_inverse_pole {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w z : ℂ} (hw : w ∈ unitDiscExterior)
    (hz : sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = extInf) :
    fiberWeldingExterior μ w z = -gMu μ w := by
  have hc : (-1 : ℂ) / gMu μ w ≠ 0 := div_ne_zero (by norm_num) (gMu_exterior_ne_zero hμ hw)
  change finPart (mobiusExt 1 0 (-1 / gMu μ w) 1
    (normalizedWeldingSphere μ (sigmaInvSphere (w : ExtPlane) (z : ExtPlane)))) = _
  rw [hz, normalizedWeldingSphere_infty hμ, mobiusExt_infty_of_ne hc]
  simp [finPart, div_neg]

theorem sigmaW_blaschke_closed {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧
      EqOn (sigmaW w) (fun z => c * blaschke a z) (closedBall (0 : ℂ) 1) := by
  obtain ⟨u, v, hs, -, huv⟩ := sigmaSphere_positive_matrix (Or.inl ⟨w, hw, rfl⟩)
  have hnorm : ‖v‖ < ‖u‖ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm] at huv
    nlinarith [norm_nonneg u, norm_nonneg v]
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (by linarith [norm_nonneg v])
  have hcu : conj u ≠ 0 := by
    intro hh
    apply hu
    simpa using congrArg (starRingEnd ℂ) hh
  let a : ℂ := -v / u
  let c : ℂ := u / conj u
  have ha : ‖a‖ < 1 := by
    dsimp [a]
    rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hu)]
    exact hnorm
  have hc : ‖c‖ = 1 := by simp [c, norm_div, hu]
  have he : EqOn (sigmaW w) (fun z => c * blaschke a z) (closedBall (0 : ℂ) 1) := by
    intro z hz
    have hzw : z ≠ w := by
      intro hh
      have hz1 := mem_closedBall_zero_iff.mp hz
      rw [hh] at hz1
      exact (not_lt.mpr hz1) hw
    have hdenB := blaschke_den_closed ha (mem_closedBall_zero_iff.mp hz)
    have hden : conj v * z + conj u ≠ 0 := by
      have heq : conj v * z + conj u = conj u * (1 - conj a * z) := by
        dsimp [a]
        simp only [map_div₀, map_neg]
        field_simp
        <;> ring
      rw [heq]
      exact mul_ne_zero hcu hdenB
    have hval := sigmaSphere_coe_eq hw hzw
    rw [hs, mobiusExt_coe hden] at hval
    have hzval := OnePoint.coe_injective hval
    rw [← hzval]
    dsimp [mobiusFn, c, a, blaschke]
    simp only [map_div₀, map_neg]
    field_simp
    <;> ring
  exact ⟨c, a, hc, ha, he⟩

theorem sigmaW_closed_extension {w : ℂ} (hw : w ∈ unitDiscExterior) :
    HasQCExtension (sigmaW w) (closedBall (0 : ℂ) 1) := by
  obtain ⟨c, a, hc, ha, he⟩ := sigmaW_blaschke_closed hw
  let R := radialDiskExtension (fun z => c * blaschke a z)
  exact ⟨R, ⟨_, radialRotationBlaschke_isKQC hc ha⟩,
    (radialRotationBlaschke_homeomorph hc ha).2.2.1,
    fun z hz => (radialDiskExtension_eq_closed hz).trans (he hz).symm⟩

theorem fiberWeldingExterior_closed_identity {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w z : ℂ} (hw : w ∈ unitDiscExterior) (hz : z ∈ closedBall (0 : ℂ) 1) :
    fiberWeldingExterior μ w (sigmaW w (wA μ z)) = lambdaW (-1 / gMu μ w) (fB μ z) ∧
      (-1 / gMu μ w) * fB μ z + 1 ≠ 0 := by
  obtain ⟨u, hu, he⟩ := (wAS_closed_iff hμ (z : ExtPlane)).mp ⟨z, hz, rfl⟩
  have hau : wA μ z = u := congrArg finPart he.symm
  have haz : wA μ z ∈ closedBall (0 : ℂ) 1 := by rwa [hau]
  have hn : wA μ z ≠ w := by
    intro hh
    have hb := mem_closedBall_zero_iff.mp haz
    rw [hh] at hb
    exact (not_lt.mpr hb) hw
  have hvalue : fiberWeldingSphere μ w (sigmaW w (wA μ z) : ExtPlane) =
      mobiusExt 1 0 (-1 / gMu μ w) 1 (fB μ z : ExtPlane) := by
    change mobiusExt _ _ _ _ (normalizedWeldingSphere μ
      (sigmaInvSphere (w : ExtPlane) (sigmaW w (wA μ z) : ExtPlane))) = _
    rw [← sigmaSphere_coe_eq hw hn, sigmaInvSphere_apply_sigma hw,
      ← normalizedWeldingExterior_coe hμ, normalizedWeldingExterior_closedDisk hμ hz]
  have hd : (-1 / gMu μ w) * fB μ z + 1 ≠ 0 := by
    intro hh
    rw [mobiusExt_coe_of_eq_zero hh] at hvalue
    exact OnePoint.coe_ne_infty _ ((fiberWeldingExterior_coe hμ hw _).trans hvalue)
  refine ⟨?_, hd⟩
  unfold fiberWeldingExterior
  rw [hvalue, mobiusExt_coe hd]
  simp [finPart, mobiusFn, lambdaW]

theorem fiberWeldingPrime_sphere {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsWeldingPrime (fun z => sigmaW w (finPart (gammaMu μ z)))
      (fun z => lambdaW (-1 / gMu μ w) (fB μ z)) (fiberWeldingExterior μ w) := by
  let c : ℂ := -1 / gMu μ w
  have hL : IsMobius (mobiusExt 1 0 c 1) := ⟨1, 0, c, 1, by simp, rfl⟩
  have hden : ∀ z ∈ unitDisc, c * fB μ z + 1 ≠ 0 :=
    fun z hz => (fiberWeldingExterior_closed_identity hμ hw (ball_subset_closedBall hz)).2
  have hlambda : ∀ z ∈ unitDisc,
      finPart (mobiusExt 1 0 c 1 (fB μ z : ExtPlane)) = lambdaW c (fB μ z) := by
    intro z hz
    rw [mobiusExt_coe (hden z hz)]
    simp [finPart, mobiusFn, lambdaW]
  have hdf : DifferentiableOn ℂ (fun z => lambdaW c (fB μ z)) unitDisc := by
    have hh := (mobius_finite_conformal hL).1.comp (fB_holomorphic_injective hμ).1
      (fun z hz => by
        change mobiusExt 1 0 c 1 (fB μ z : ExtPlane) ≠ extInf
        rw [mobiusExt_coe (hden z hz)]
        exact OnePoint.coe_ne_infty _)
    exact hh.congr (fun z hz => (hlambda z hz).symm)
  have hif : InjOn (fun z => lambdaW c (fB μ z)) unitDisc := by
    intro z hz v hv he
    apply (fB_holomorphic_injective hμ).2 hz hv
    apply OnePoint.coe_injective
    apply isMobius_injective hL
    rw [mobiusExt_coe (hden z hz), mobiusExt_coe (hden v hv)]
    exact congrArg (fun x : ℂ => (x : ExtPlane)) (by simpa [mobiusFn, lambdaW] using he)
  have hjet := lambdaW_comp_jets
    ((fB_holomorphic_injective hμ).1.analyticOnNhd isOpen_ball 0 (by simp [unitDisc]))
    (fB_normalization μ).1 (fB_normalization μ).2.1 c
  refine ⟨?_, hdf, hif, ?_, hjet.1, fiberWeldingExterior_isUnivalentAtInfty hμ hw⟩
  · obtain ⟨H, ⟨KH, hKH⟩, hHs, hHa⟩ := wA_hasQCExtension_closed hμ
    obtain ⟨R, ⟨KR, hKR⟩, hRs, hRa⟩ := sigmaW_closed_extension hw
    obtain ⟨KG, hKG⟩ := fiberWeldingExterior_quasiconformal hμ hw
    let G := fiberWeldingExterior μ w
    have hsc := fiberWeldingSphere_continuous_bijective hμ hw
    have hGs : G '' univ = univ :=
      (sphereFinite_homeomorph hsc.2 hsc.1 (fiberWeldingSphere_infty hμ hw)).2.2.1
    have hAclosed : ∀ z ∈ closedBall (0 : ℂ) 1, wA μ z ∈ closedBall (0 : ℂ) 1 := by
      intro z hz
      obtain ⟨u, hu, he⟩ := (wAS_closed_iff hμ (z : ExtPlane)).mp ⟨z, hz, rfl⟩
      have ha : wA μ z = u := congrArg finPart he.symm
      rwa [ha]
    refine ⟨G ∘ R ∘ H, G,
      ⟨(KH * KR) * KG, thm7_1_comp (thm7_1_comp hKH hKR (subset_univ _)) hKG (subset_univ _)⟩,
      ?_, ?_, ⟨KG, hKG⟩, hGs, (fun _ _ => rfl), ?_⟩
    · rw [image_comp, image_comp, hHs, hRs, hGs]
    · intro z hz
      have hzcl := ball_subset_closedBall hz
      change G (R (H z)) = _
      rw [hHa hzcl, hRa (hAclosed z hzcl)]
      exact (fiberWeldingExterior_closed_identity hμ hw hzcl).1
    · intro z hz
      have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (show ‖z‖ = 1 from hz).le
      change G (sigmaW w (finPart (gammaMu μ z))) = G (R (H z))
      rw [hHa hzcl, hRa (hAclosed z hzcl)]
      simp only [gammaMu, alphaMu_eq_id, id_eq]
      rfl
  · simp [lambdaW, (fB_normalization μ).1]

end TakhtajanTeo

#print axioms TakhtajanTeo.fiberWeldingExterior_quasiconformal
#print axioms TakhtajanTeo.fiberWeldingExterior_isUnivalentAtInfty
#print axioms TakhtajanTeo.fiberWeldingExterior_finite
#print axioms TakhtajanTeo.fiberWeldingExterior_at_inverse_pole
#print axioms TakhtajanTeo.fiberWeldingExterior_original_coordinates
#print axioms TakhtajanTeo.fiberWeldingPrime_sphere
