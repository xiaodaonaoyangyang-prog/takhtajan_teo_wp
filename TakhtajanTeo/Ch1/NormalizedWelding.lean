import TakhtajanTeo.Ch1.S1_2_Homogeneous
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# The exterior function of the normalized welding

Construct the actual sphere transition `wB μ ∘ (wAS μ)⁻¹`, before identifying
its finite part with the choice-based `gMu`. No welding existence theorem is
used here. The exterior map is a global quasiconformal plane homeomorphism.
A quasiconformal plane extension of `wA μ` from the closed disk is the explicit
remaining premise in the constructed `IsWelding` and `IsWeldingPrime` interfaces.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def normalizedWeldingSphere (μ : LinfStar) : ExtPlane → ExtPlane :=
  wB μ ∘ Function.invFun (wAS μ)

def normalizedWeldingExterior (μ : LinfStar) (z : ℂ) : ℂ :=
  finPart (normalizedWeldingSphere μ z)

theorem normalizedWeldingSphere_bijective (μ : LinfStar) :
    Function.Bijective (normalizedWeldingSphere μ) := by
  apply (wB_bijective μ).comp
  refine ⟨?_, Function.invFun_surjective (wAS_bijective μ).1⟩
  intro p q hpq
  have h := congrArg (wAS μ) hpq
  simpa only [Function.invFun_eq ((wAS_bijective μ).2 _)] using h

theorem normalizedWeldingSphere_continuous {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Continuous (normalizedWeldingSphere μ) :=
  (wB_continuous hμ).comp (wAS_invFun_continuous hμ)

theorem normalizedWeldingSphere_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    normalizedWeldingSphere μ extInf = extInf :=
  (fB_normalization μ).2.2 ⟨wB μ, (wB_spec hμ).1⟩

theorem normalizedWeldingExterior_coe {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (z : ℂ) :
    (normalizedWeldingExterior μ z : ExtPlane) = normalizedWeldingSphere μ z := by
  apply coe_finPart_of_ne
  intro h
  exact OnePoint.coe_ne_infty z ((normalizedWeldingSphere_bijective μ).1
    (h.trans (normalizedWeldingSphere_infty hμ).symm))

theorem normalizedWeldingExterior_map {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    OnePoint.map (normalizedWeldingExterior μ) = normalizedWeldingSphere μ := by
  funext p
  induction p using OnePoint.rec with
  | infty => exact (normalizedWeldingSphere_infty hμ).symm
  | coe z => exact normalizedWeldingExterior_coe hμ z

theorem normalizedWeldingExterior_continuous_proper {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) :
    Continuous (normalizedWeldingExterior μ) ∧
      Tendsto (normalizedWeldingExterior μ) (cocompact ℂ) (cocompact ℂ) := by
  have h := OnePoint.continuous_map_iff.mp
    ((normalizedWeldingExterior_map hμ).symm ▸ normalizedWeldingSphere_continuous hμ)
  simpa only [coclosedCompact_eq_cocompact] using h

theorem normalizedWeldingExterior_bijective {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Bijective (normalizedWeldingExterior μ) := by
  constructor
  · intro z w h
    have hc := congrArg (fun x : ℂ => (x : ExtPlane)) h
    rw [normalizedWeldingExterior_coe hμ, normalizedWeldingExterior_coe hμ] at hc
    exact OnePoint.coe_injective ((normalizedWeldingSphere_bijective μ).1 hc)
  · intro w
    obtain ⟨p, hp⟩ := (normalizedWeldingSphere_bijective μ).2 (w : ExtPlane)
    induction p using OnePoint.rec with
    | infty =>
      rw [normalizedWeldingSphere_infty hμ] at hp
      exact (OnePoint.coe_ne_infty w hp.symm).elim
    | coe z =>
      refine ⟨z, ?_⟩
      exact OnePoint.coe_injective ((normalizedWeldingExterior_coe hμ z).trans hp)

theorem normalizedWeldingExterior_boundary {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ unitCircle) :
    normalizedWeldingExterior μ (wA μ z) = fB μ z := by
  obtain ⟨u, -, hu⟩ := wAS_maps_circle hμ hz
  have he : (wA μ z : ExtPlane) = wAS μ z := by
    unfold wA
    rw [hu]
    rfl
  unfold normalizedWeldingExterior normalizedWeldingSphere
  rw [Function.comp_apply, he, Function.leftInverse_invFun (wAS_bijective μ).1]
  rfl

/-- The exterior transition is holomorphic. The plane chart of the inverse
Model A map has at most one exceptional point; continuity removes it. -/
theorem normalizedWeldingExterior_differentiableOn {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (normalizedWeldingExterior μ) unitDiscExterior := by
  obtain ⟨M, hM, W, hW, hwf, hwi, -, -, -⟩ := wA_spec hμ
  obtain ⟨N, hN, V, hV, hvf, hvi, -⟩ := (wB_spec hμ).1
  obtain ⟨Minv, hMinv, hMl, -⟩ := isMobius_inverse hM
  let P : ℂ → ℂ := fun z => finPart (Minv (z : ExtPlane))
  let ψ : ℂ → ℂ := V ∘ Function.invFunOn W {u : ℂ | 1 < ‖u‖}
  let Q : ℂ → ℂ := fun z => finPart (N (z : ExtPlane))
  let Ω : Set ℂ := {z | z ∈ unitDiscExterior ∧ Minv (z : ExtPlane) ≠ extInf}
  have hψ : IsConformalOnto ψ {u : ℂ | 1 < ‖u‖} (V '' {u : ℂ | 1 < ‖u‖}) :=
    (transition_conformal hW hV).1
  have hinv : ∀ p, wAS μ (Function.invFun (wAS μ) p) = p :=
    fun p => Function.invFun_eq ((wAS_bijective μ).2 p)
  have hdata : ∀ z ∈ Ω, ∃ u : ℂ,
      Function.invFun (wAS μ) (z : ExtPlane) = (u : ExtPlane) ∧ W u = P z ∧ 1 < ‖u‖ := by
    intro z hz
    have hnot : Function.invFun (wAS μ) (z : ExtPlane) ∉
        toExt (closedBall (0 : ℂ) 1) := by
      rw [wAS_closed_iff hμ, hinv, coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hz.1
    exact finite_preimage_data hwf hwi hMl (hinv _) hnot
      (coe_finPart_of_ne hz.2).symm
  have hPmem : ∀ z ∈ Ω, P z ∈ {u : ℂ | 1 < ‖u‖} := by
    intro z hz
    obtain ⟨u, -, hu, hU⟩ := hdata z hz
    rw [← hu]
    exact normalized_solution_exterior hW hU
  have hvalues : ∀ z ∈ Ω,
      normalizedWeldingExterior μ z = Q (ψ (P z)) ∧ N (ψ (P z) : ExtPlane) ≠ extInf := by
    intro z hz
    obtain ⟨u, hu, hWu, hU⟩ := hdata z hz
    have heψ : ψ (P z) = V u := by
      dsimp [ψ]
      rw [← hWu, (normalized_solution_injective hW).injOn.leftInvOn_invFunOn hU]
    have he : normalizedWeldingSphere μ z = N (ψ (P z) : ExtPlane) := by
      dsimp [normalizedWeldingSphere]
      rw [hu, hvf, heψ]
    refine ⟨?_, ?_⟩
    · change finPart (normalizedWeldingSphere μ z) = _
      rw [he]
    · rw [← he, ← normalizedWeldingExterior_coe hμ]
      exact OnePoint.coe_ne_infty _
  have hdiff : DifferentiableOn ℂ (normalizedWeldingExterior μ) Ω := by
    have hPd : DifferentiableOn ℂ P Ω :=
      (mobius_finite_conformal hMinv).1.mono (fun _ hz => hz.2)
    have h1 : DifferentiableOn ℂ (ψ ∘ P) Ω := hψ.1.comp hPd hPmem
    have h2 : DifferentiableOn ℂ (Q ∘ ψ ∘ P) Ω :=
      (mobius_finite_conformal hN).1.comp h1 (fun z hz => (hvalues z hz).2)
    exact h2.congr (fun z hz => (hvalues z hz).1)
  have hE : (unitDiscExterior \ Ω).Subsingleton := by
    intro z hz w hw
    have hz' : Minv (z : ExtPlane) = extInf := by
      by_contra hn
      exact hz.2 ⟨hz.1, hn⟩
    have hw' : Minv (w : ExtPlane) = extInf := by
      by_contra hn
      exact hw.2 ⟨hw.1, hn⟩
    exact OnePoint.coe_injective (isMobius_injective hMinv (hz'.trans hw'.symm))
  refine differentiableOn_of_finite_exceptional
    (show IsOpen unitDiscExterior from isOpen_lt continuous_const continuous_norm)
    hE.finite (normalizedWeldingExterior_continuous_proper hμ).1.continuousOn ?_
  apply hdiff.mono
  intro z hz
  by_contra hn
  exact hz.2 ⟨hz.1, hn⟩

theorem normalizedWeldingExterior_isUnivalentAtInfty {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) : IsUnivalentAtInfty (normalizedWeldingExterior μ) :=
  ⟨normalizedWeldingExterior_differentiableOn hμ,
    (normalizedWeldingExterior_bijective hμ).1.injOn,
    (normalizedWeldingExterior_continuous_proper hμ).2⟩

theorem normalizedWeldingExterior_homeomorph {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsHomeomorphOnto (normalizedWeldingExterior μ) univ univ := by
  let g := normalizedWeldingExterior μ
  have hb : Function.Bijective g := normalizedWeldingExterior_bijective hμ
  have hp : IsProperMap g := isProperMap_iff_tendsto_cocompact.mpr
    (normalizedWeldingExterior_continuous_proper hμ)
  let e : ℂ ≃ₜ ℂ := (Equiv.ofBijective g hb).toHomeomorphOfContinuousClosed
    hp.continuous hp.isClosedMap
  have he : Function.invFunOn g univ = e.symm := by
    funext y
    obtain ⟨x, rfl⟩ := hb.2 y
    rw [hb.1.injOn.leftInvOn_invFunOn (mem_univ x)]
    exact (e.symm_apply_apply x).symm
  refine ⟨hp.continuous.continuousOn, hb.1.injOn, image_univ.trans hb.2.range_eq, ?_⟩
  rw [he]
  exact e.symm.continuous.continuousOn

theorem normalizedWeldingExterior_quasiconformal {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsQuasiconformal (normalizedWeldingExterior μ) univ := by
  obtain ⟨M, hM, W, hW, hwf, hwi, -, -, -⟩ := wA_spec hμ
  obtain ⟨N, hN, V, hV, hvf, hvi, -⟩ := (wB_spec hμ).1
  obtain ⟨Minv, hMinv, hMl, -⟩ := isMobius_inverse hM
  obtain ⟨KW, hKW⟩ := hW.1
  obtain ⟨KV, hKV⟩ := hV.1
  let P : ℂ → ℂ := fun z => finPart (Minv (z : ExtPlane))
  let ψ : ℂ → ℂ := V ∘ Function.invFunOn W univ
  let Q : ℂ → ℂ := fun z => finPart (N (z : ExtPlane))
  let Ω : Set ℂ := {z | Minv (z : ExtPlane) ≠ extInf}
  have hiW : IsKQC (Function.invFunOn W univ) univ KW := by
    have hi := thm7_2_inv hKW
    rwa [hW.2.1] at hi
  have hψ : IsKQC ψ univ (KW * KV) := thm7_1_comp hiW hKV (subset_univ _)
  have hP : IsKQC P Ω 1 :=
    isKQC_one_of_conformal (mobius_finite_open hMinv) (mobius_finite_conformal hMinv)
  have hinv : ∀ p, wAS μ (Function.invFun (wAS μ) p) = p :=
    fun p => Function.invFun_eq ((wAS_bijective μ).2 p)
  have hdata : ∀ z ∈ Ω, ∃ u : ℂ,
      Function.invFun (wAS μ) (z : ExtPlane) = (u : ExtPlane) ∧ W u = P z := by
    intro z hz
    have hi := hinv (z : ExtPlane)
    generalize hq : Function.invFun (wAS μ) (z : ExtPlane) = q at hi
    induction q using OnePoint.rec with
    | infty =>
      exfalso
      apply hz
      rw [hwi] at hi
      rw [← hi, hMl]
    | coe u =>
      refine ⟨u, rfl, ?_⟩
      rw [hwf] at hi
      have h := congrArg Minv hi
      rw [hMl] at h
      exact congrArg finPart h
  have hv : ∀ z ∈ Ω,
      normalizedWeldingExterior μ z = Q (ψ (P z)) ∧ N (ψ (P z) : ExtPlane) ≠ extInf := by
    intro z hz
    obtain ⟨u, hu, hWu⟩ := hdata z hz
    have heψ : ψ (P z) = V u := by
      dsimp [ψ]
      rw [← hWu, (normalized_solution_injective hW).injOn.leftInvOn_invFunOn (mem_univ u)]
    have he : normalizedWeldingSphere μ z = N (ψ (P z) : ExtPlane) := by
      dsimp [normalizedWeldingSphere]
      rw [hu, hvf, heψ]
    refine ⟨?_, ?_⟩
    · change finPart (normalizedWeldingSphere μ z) = _
      rw [he]
    · rw [← he, ← normalizedWeldingExterior_coe hμ]
      exact OnePoint.coe_ne_infty _
  have h1 : IsKQC (ψ ∘ P) Ω (KW * KV) := by
    simpa only [one_mul] using thm7_1_comp hP hψ (subset_univ _)
  have h2 : IsKQC (Q ∘ ψ ∘ P) Ω (KW * KV) :=
    (bg_comp_conformal h1 (mobius_finite_open hN) (mobius_finite_conformal hN)
      (by rintro _ ⟨z, hz, rfl⟩; exact (hv z hz).2)).1
  have hg : IsKQC (normalizedWeldingExterior μ) Ω (KW * KV) :=
    ad_isKQC_congr h2 (fun z hz => (hv z hz).1)
  refine ⟨KW * KV, ?_⟩
  have hhome := normalizedWeldingExterior_homeomorph hμ
  have himage : normalizedWeldingExterior μ '' univ = univ := hhome.2.2.1
  apply iskqc_of_subsingleton_exceptional (P := fun z => Minv (z : ExtPlane) ≠ extInf)
    isOpen_univ (by rwa [himage]) (one_le_mul_of_one_le_of_one_le hKW.2.1 hKV.2.1)
    (subset_univ _) ?_ hg
  intro z hz w hw
  have hz' : Minv (z : ExtPlane) = extInf := not_not.mp hz.2
  have hw' : Minv (w : ExtPlane) = extInf := not_not.mp hw.2
  exact OnePoint.coe_injective (isMobius_injective hMinv (hz'.trans hw'.symm))

theorem normalizedWeldingExterior_closedDisk {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    normalizedWeldingExterior μ (wA μ z) = fB μ z := by
  obtain ⟨u, -, hu⟩ := (wAS_closed_iff hμ (z : ExtPlane)).mp ⟨z, hz, rfl⟩
  have he : (wA μ z : ExtPlane) = wAS μ z := by
    unfold wA
    rw [← hu]
    rfl
  unfold normalizedWeldingExterior normalizedWeldingSphere
  rw [Function.comp_apply, he, Function.leftInverse_invFun (wAS_bijective μ).1]
  rfl

/-- Exact remaining extension premise for the actual normalized welding.
The exterior function and both normalization conditions are already established. -/
theorem normalizedWeldingPrime_of_modelA_extension {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hExt : HasQCExtension (wA μ) (closedBall (0 : ℂ) 1)) :
    IsWeldingPrime (wA μ) (fB μ) (normalizedWeldingExterior μ) := by
  obtain ⟨H, ⟨KH, hKH⟩, hHsurj, hHagree⟩ := hExt
  obtain ⟨KG, hKG⟩ := normalizedWeldingExterior_quasiconformal hμ
  have hGsurj := (normalizedWeldingExterior_homeomorph hμ).2.2.1
  refine ⟨?_, (fB_holomorphic_injective hμ).1, (fB_holomorphic_injective hμ).2,
    (fB_normalization μ).1, (fB_normalization μ).2.1,
    normalizedWeldingExterior_isUnivalentAtInfty hμ⟩
  refine ⟨normalizedWeldingExterior μ ∘ H, normalizedWeldingExterior μ,
    ⟨KH * KG, thm7_1_comp hKH hKG (subset_univ _)⟩, ?_, ?_,
    ⟨KG, hKG⟩, hGsurj, (fun _ _ => rfl), ?_⟩
  · rw [image_comp, hHsurj, hGsurj]
  · intro z hz
    have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr
      (mem_ball_zero_iff.mp hz).le
    rw [Function.comp_apply, hHagree hzcl]
    exact normalizedWeldingExterior_closedDisk hμ hzcl
  · intro z hz
    have hzcl : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr
      (show ‖z‖ = 1 from hz).le
    rw [Function.comp_apply, hHagree hzcl]

theorem normalizedWelding_of_modelA_extension {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hExt : HasQCExtension (wA μ) (closedBall (0 : ℂ) 1)) :
    IsWelding (wA μ) id (fB μ) (normalizedWeldingExterior μ) := by
  obtain ⟨⟨F, G, hF, hFs, hFf, hG, hGs, hGg, hboundary⟩, hrest⟩ :=
    normalizedWeldingPrime_of_modelA_extension hμ hExt
  refine ⟨rfl, ⟨F, G, hF, hFs, hFf, hG, hGs, hGg, ?_⟩, hrest⟩
  intro z hz
  change (G (wA μ z) : ExtPlane) = (F z : ExtPlane)
  exact congrArg (fun x : ℂ => (x : ExtPlane)) (hboundary z hz)


end TakhtajanTeo
