import TakhtajanTeo.Ch1.GeneralWeldingUniqueness

/-! Construct a normalized welding from an actual plane QC extension of its
circle map. The only remaining hypothesis is the extension itself. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem weldingPrime_exists_of_plane_extension {h H : ℂ → ℂ}
    (hH : IsQuasiconformal H univ) (hHs : H '' univ = univ)
    (hHcircle : H '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1)
    (hHh : EqOn H h unitCircle) : ∃ f g, IsWeldingPrime h f g := by
  obtain ⟨K, hK⟩ := hH
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hHs
  have hV : IsKQC e.symm univ K := homeomorph_inverse_isKQC e hK
  have hKD : 1 ≤ K := hK.2.1
  let k : ℝ := (K - 1) / (K + 1)
  have hk0 : 0 ≤ k := div_nonneg (sub_nonneg.mpr hKD) (by linarith)
  have hk1 : k < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  let μ : ℂ → ℂ := unitDisc.indicator (complexDilatation e.symm)
  have hvbc := (thm10_2_genHomeoSolution_of_isKQC hV).1
  have hμ : IsBeltramiCoeff μ univ k := by
    rw [IsBeltramiCoeff, Measure.restrict_univ] at hvbc ⊢
    refine ⟨hvbc.1.indicator isOpen_ball.measurableSet, ?_⟩
    filter_upwards [hvbc.2] with z hz
    by_cases hzD : z ∈ unitDisc
    · simpa only [μ, indicator_of_mem hzD] using hz
    · simpa only [μ, indicator_of_notMem hzD, norm_zero] using hk0
  obtain ⟨W, hWn, hWK, -⟩ := thm13_7_normalized_existence hk0 hk1 hμ
  obtain ⟨hWq, hWs, -, -, hWdil⟩ := hWn
  obtain ⟨eW, rfl⟩ := t1_homeomorph hWK hWs
  have hD : IsOpen unitDisc := isOpen_ball
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hregions := planeHomeomorph_circle_regions e hHcircle
  have hvimg : e.symm '' unitDisc = unitDisc := by
    calc
      e.symm '' unitDisc = e.symm '' (e '' unitDisc) :=
        congrArg (fun s : Set ℂ => e.symm '' s) hregions.2.1.symm
      _ = unitDisc := e.toEquiv.symm_image_image _
  have hemap : MapsTo e unitDisc unitDisc := image_subset_iff.mp hregions.2.1.subset
  have hcoeff : ∀ᵐ z ∂(volume.restrict unitDisc),
      complexDilatation eW z = complexDilatation e.symm z := by
    filter_upwards [ae_restrict_of_ae hWdil, ae_restrict_mem hD.measurableSet] with z hz hzD
    simpa only [μ, indicator_of_mem hzD] using hz
  have hconf := bg_conformal_of_dilatation_eq
    (nx_isKQC_restrict hV hD (subset_univ _)) (nx_isKQC_restrict hWK hD (subset_univ _)) hcoeff
  rw [hvimg] at hconf
  have hi : EqOn (Function.invFunOn (e.symm : ℂ → ℂ) unitDisc) e unitDisc := by
    intro z hz
    have hh := e.symm.injective.injOn.leftInvOn_invFunOn (hemap hz)
    simpa only [e.symm_apply_apply] using hh
  let f₀ : ℂ → ℂ := eW ∘ e
  have hf₀d : DifferentiableOn ℂ f₀ unitDisc :=
    hconf.1.congr (fun z hz => congrArg eW (hi hz).symm)
  have hf₀i : InjOn f₀ unitDisc := (eW.injective.comp e.injective).injOn
  have hz0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  let a := deriv f₀ 0
  let b := f₀ 0
  have ha : a ≠ 0 := deriv_ne_zero_of_injOn hD hf₀d hf₀i hz0
  let L : ℂ → ℂ := fun u => (u - b) / a
  have hL : IsConformalOnto L univ univ := nxE_affine_isConformalOnto ha
  let G : ℂ → ℂ := L ∘ eW
  let F : ℂ → ℂ := G ∘ e
  have hG : IsKQC G univ ((1 + k) / (1 - k)) :=
    (bg_comp_conformal hWK isOpen_univ hL (subset_univ _)).1
  have hF : IsKQC F univ (K * ((1 + k) / (1 - k))) := thm7_1_comp hK hG (subset_univ _)
  have hGs : G '' univ = univ := by
    rw [image_comp, hWs, hL.2.2]
  have hFs : F '' univ = univ := by
    rw [image_comp, hHs, hGs]
  have hFd : DifferentiableOn ℂ F unitDisc :=
    (hf₀d.sub_const b).div_const a
  have hFi : InjOn F unitDisc := by
    intro z hz v hv hfv
    apply hf₀i hz hv
    exact hL.2.1 (mem_univ _) (mem_univ _) hfv
  have hF0 : F 0 = 0 := by simp [F, G, L, b, f₀]
  have hF1 : deriv F 0 = 1 := by
    have hd := (((hf₀d.differentiableAt (hD.mem_nhds hz0)).hasDerivAt).sub_const b).div_const a
    change deriv (fun z => (f₀ z - b) / a) 0 = 1
    rw [hd.deriv]
    exact div_self ha
  have hWE : DifferentiableOn ℂ eW unitDiscExterior := by
    apply nx_differentiableOn_of_dilatation_zero (nx_isKQC_restrict hWK hE (subset_univ _))
    filter_upwards [ae_restrict_of_ae hWdil, ae_restrict_mem hE.measurableSet] with z hz hzE
    have hzD : z ∉ unitDisc := by
      intro hh
      exact (not_lt.mpr (mem_ball_zero_iff.mp hh).le) hzE
    simpa only [μ, indicator_of_notMem hzD] using hz
  have hGd : DifferentiableOn ℂ G unitDiscExterior := (hWE.sub_const b).div_const a
  have hGi : InjOn G unitDiscExterior := by
    intro z hz v hv heq
    exact eW.injective (hL.2.1 (mem_univ _) (mem_univ _) heq)
  have hGinf : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    obtain ⟨eg, he⟩ := t1_homeomorph hG hGs
    rw [← he]
    exact (isProperMap_iff_tendsto_cocompact.mp eg.isProperMap).2
  refine ⟨F, G, ⟨F, G, ⟨_, hF⟩, hFs, (fun _ _ => rfl),
    ⟨_, hG⟩, hGs, (fun _ _ => rfl), ?_⟩, hFd, hFi, hF0, hF1, hGd, hGi, hGinf⟩
  intro z hz
  change G (h z) = G (e z)
  rw [hHh hz]

end TakhtajanTeo

#print axioms TakhtajanTeo.weldingPrime_exists_of_plane_extension
