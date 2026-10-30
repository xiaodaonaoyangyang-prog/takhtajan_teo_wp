import TakhtajanTeo.Ch1.TCurveSchwarzianTransport

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Conformal-disk transport is an actual Mobius transition of the Model B
sphere maps, obtained from global Beltrami uniqueness. -/
theorem tcg_transport_mobius {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (R : ℂ ≃ₜ ℂ) {K : ℝ} (hR : IsKQC (⇑R) univ K)
    (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc) :
    ∃ B : ExtPlane → ExtPlane, IsMobius B ∧
      ∀ p, wB (tcurveLambda ν R) (OnePoint.map R p) = B (wB ν p) := by
  have hRs : R '' univ = univ := image_univ.trans R.surjective.range_eq
  have hl := (tmi_lambda_props hν hR hRs hRE).1
  obtain ⟨M, hM, W, hW, hwf, hwi, hrest⟩ := (wB_spec hν).1
  obtain ⟨N, hN, V, hV, hvf, hvi, hrest'⟩ := (wB_spec hl).1
  obtain ⟨KW, hKW⟩ := hW.1
  have hWe : complexDilatation W =ᵐ[volume.restrict unitDiscExterior] (ν : ℂ → ℂ) := by
    filter_upwards [ae_restrict_of_ae hW.2.2.2.2, ae_restrict_mem bc_hEo.measurableSet]
      with z hz hzE
    rw [hz]
    simp [extB, indicator_of_mem hzE]
  have hFK : IsKQC (W ∘ R.symm) univ (K * KW) :=
    thm7_1_comp (homeomorph_inverse_isKQC R hR) hKW (subset_univ _)
  have hFs : (W ∘ R.symm) '' univ = univ := by
    rw [image_comp, image_univ.trans R.symm.surjective.range_eq, hW.2.1]
  have hFd : DifferentiableOn ℂ (W ∘ R.symm) unitDisc :=
    (extB_solution_holomorphic hW).comp hRD.1 hRD.mapsTo
  have hFae := tcg_plane_extB hFd (tcg_lambda_is_dilatation hν hKW hWe R hR hRE).symm
  have hVae : complexDilatation V =ᵐ[volume] extB (tcurveLambda ν R) := hV.2.2.2.2
  obtain ⟨A, hA, hVA⟩ := uq_conformal_auto isOpen_univ ⟨K * KW, hFK⟩ hV.1 hFs hV.2.1 (by
    rw [Measure.restrict_univ]
    exact hFae.trans hVae.symm)
  obtain ⟨a, b, ha, hab⟩ := nx_entire_affine hA
  have hVR : ∀ z, V (R z) = a * W z + b := by
    intro z
    rw [hVA (R z) (mem_univ _), hab, Function.comp_apply, R.symm_apply_apply]
  obtain ⟨Mi, hMi, hMil, hMir⟩ := isMobius_inverse hM
  let B : ExtPlane → ExtPlane := fun p => N (mobiusExt a b 0 1 (Mi p))
  have hAff : IsMobius (mobiusExt a b 0 1) := ⟨a, b, 0, 1, by simpa using ha, rfl⟩
  refine ⟨B, isMobius_comp (isMobius_comp hMi hAff) hN, ?_⟩
  intro p
  induction p using OnePoint.rec with
  | infty =>
    change wB (tcurveLambda ν R) extInf = N (mobiusExt a b 0 1 (Mi (wB ν extInf)))
    rw [hvi, hwi, hMil]
    simp [mobiusExt]
  | coe z =>
    change wB (tcurveLambda ν R) ((R z : ℂ) : ExtPlane) =
      N (mobiusExt a b 0 1 (Mi (wB ν (z : ExtPlane))))
    rw [hvf, hwf, hMil, mobiusExt_coe (by simp), hVR]
    simp [mobiusFn]

/-- Exact normalized base-quotient fibre transport on genuine exterior fibres. -/
theorem tcg_normalized_fibre_quotient {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC (⇑e) univ K)
    (heC : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hm1 : e (-1) = -1) (hmI : e (-I) = -I) (h1 : e 1 = 1)
    (hae : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] complexDilatation (⇑e))
    {ζ : ExtPlane} (hζ : ζ ∈ wB ν '' extDiscExterior) :
    tcurveZ ν e (beltramiMul ν (beltramiInv μ)) ζ =
      normalizedWeldingSphere (beltramiMul ν (beltramiInv μ))
        (Function.invFun (normalizedWeldingSphere ν) ζ) := by
  obtain ⟨p, hp, rfl⟩ := hζ
  have hi : Function.invFun (normalizedWeldingSphere ν) (wB ν p) = wAS ν p := by
    apply (normalizedWeldingSphere_bijective ν).1
    rw [Function.invFun_eq ((normalizedWeldingSphere_bijective ν).2 (wB ν p))]
    dsimp only [normalizedWeldingSphere, Function.comp_apply]
    rw [Function.leftInverse_invFun (wAS_bijective ν).1 p]
  have hmap : wAS (beltramiMul ν (beltramiInv μ)) (OnePoint.map e p) = wAS ν p := by
    rw [← tcg_modelA_exterior hμ e he heC hm1 hmI h1 hae hp,
      grp_wAS_mul hν (grp_inv_mem hμ)]
    change wAS ν (wAS (beltramiInv μ) (wAS μ p)) = wAS ν p
    exact congrArg (wAS ν) (congrFun (grp_wAS_inv_right hμ) p)
  rw [hi]
  dsimp only [tcurveZ, normalizedWeldingSphere, Function.comp_apply]
  rw [Function.leftInverse_invFun (wB_bijective ν).1 p, ← hmap,
    Function.leftInverse_invFun (wAS_bijective (beltramiMul ν (beltramiInv μ))).1]

#print axioms tcg_transport_mobius
#print axioms tcg_normalized_fibre_quotient
end TakhtajanTeo
