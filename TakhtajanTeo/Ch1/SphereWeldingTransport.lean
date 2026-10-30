import TakhtajanTeo.Ch1.WeldingUniqueness

/-! Möbius transport of a plane quasiconformal map, composed on the sphere
before taking the finite part. The normalization at infinity removes the
apparent finite-coordinate pole of the intermediate inverse map. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem sphereFinite_coe {F : ExtPlane → ExtPlane}
    (hb : Function.Bijective F) (hi : F extInf = extInf) (z : ℂ) :
    (finPart (F (z : ExtPlane)) : ExtPlane) = F (z : ExtPlane) := by
  apply coe_finPart_of_ne
  intro h
  exact OnePoint.coe_ne_infty z (hb.1 (h.trans hi.symm))

theorem sphereFinite_bijective {F : ExtPlane → ExtPlane}
    (hb : Function.Bijective F) (hi : F extInf = extInf) :
    Function.Bijective (fun z : ℂ => finPart (F (z : ExtPlane))) := by
  constructor
  · intro z w h
    have he := congrArg (fun x : ℂ => (x : ExtPlane)) h
    rw [sphereFinite_coe hb hi, sphereFinite_coe hb hi] at he
    exact OnePoint.coe_injective (hb.1 he)
  · intro w
    obtain ⟨p, hp⟩ := hb.2 (w : ExtPlane)
    induction p using OnePoint.rec with
    | infty => exact (OnePoint.coe_ne_infty w (hi.symm.trans hp).symm).elim
    | coe z => exact ⟨z, congrArg finPart hp⟩

theorem sphereFinite_continuous_proper {F : ExtPlane → ExtPlane}
    (hb : Function.Bijective F) (hc : Continuous F) (hi : F extInf = extInf) :
    Continuous (fun z : ℂ => finPart (F (z : ExtPlane))) ∧
      Tendsto (fun z : ℂ => finPart (F (z : ExtPlane))) (cocompact ℂ) (cocompact ℂ) := by
  have he : OnePoint.map (fun z : ℂ => finPart (F (z : ExtPlane))) = F := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact hi.symm
    | coe z => exact sphereFinite_coe hb hi z
  have h := OnePoint.continuous_map_iff.mp (he.symm ▸ hc)
  simpa only [coclosedCompact_eq_cocompact] using h

theorem sphereFinite_homeomorph {F : ExtPlane → ExtPlane}
    (hb : Function.Bijective F) (hc : Continuous F) (hi : F extInf = extInf) :
    IsHomeomorphOnto (fun z : ℂ => finPart (F (z : ExtPlane))) univ univ := by
  let g : ℂ → ℂ := fun z => finPart (F (z : ExtPlane))
  have hgb : Function.Bijective g := sphereFinite_bijective hb hi
  have hp : IsProperMap g := isProperMap_iff_tendsto_cocompact.mpr
    (sphereFinite_continuous_proper hb hc hi)
  let e : ℂ ≃ₜ ℂ := (Equiv.ofBijective g hgb).toHomeomorphOfContinuousClosed
    hp.continuous hp.isClosedMap
  have he : Function.invFunOn g univ = e.symm := by
    funext y
    obtain ⟨x, rfl⟩ := hgb.2 y
    rw [hgb.1.injOn.leftInvOn_invFunOn (mem_univ x)]
    exact (e.symm_apply_apply x).symm
  refine ⟨hp.continuous.continuousOn, hgb.1.injOn,
    image_univ.trans hgb.2.range_eq, ?_⟩
  rw [he]
  exact e.symm.continuous.continuousOn

theorem mobius_sphere_continuous_bijective {M : ExtPlane → ExtPlane} (hM : IsMobius M) :
    Continuous M ∧ Function.Bijective M := by
  obtain ⟨a, b, c, d, hd, rfl⟩ := hM
  exact ⟨(mobiusHomeomorph a b c d hd).continuous,
    (mobiusHomeomorph a b c d hd).bijective⟩

theorem sphereTransport_isKQC {G M N : ExtPlane → ExtPlane} {g : ℂ → ℂ} {K : ℝ}
    (hGb : Function.Bijective G) (hGc : Continuous G)
    (hg : ∀ z : ℂ, G (z : ExtPlane) = (g z : ExtPlane))
    (hgq : IsKQC g univ K) (hM : IsMobius M) (hN : IsMobius N)
    (hi : N (G (M extInf)) = extInf) :
    IsKQC (fun z : ℂ => finPart (N (G (M (z : ExtPlane))))) univ K := by
  let F : ExtPlane → ExtPlane := N ∘ G ∘ M
  let f : ℂ → ℂ := fun z => finPart (F (z : ExtPlane))
  let P : ℂ → ℂ := fun z => finPart (M (z : ExtPlane))
  let Q : ℂ → ℂ := fun z => finPart (N (z : ExtPlane))
  let Ω : Set ℂ := {z | M (z : ExtPlane) ≠ extInf}
  have hMc := mobius_sphere_continuous_bijective hM
  have hNc := mobius_sphere_continuous_bijective hN
  have hFb : Function.Bijective F := hNc.2.comp (hGb.comp hMc.2)
  have hFc : Continuous F := hNc.1.comp (hGc.comp hMc.1)
  have hFi : F extInf = extInf := hi
  have hval : ∀ z ∈ Ω, f z = Q (g (P z)) ∧ N (g (P z) : ExtPlane) ≠ extInf := by
    intro z hz
    have he : F (z : ExtPlane) = N (g (P z) : ExtPlane) := by
      change N (G (M (z : ExtPlane))) = _
      rw [← coe_finPart_of_ne hz, hg]
    constructor
    · exact congrArg finPart he
    · rw [← he, ← sphereFinite_coe hFb hFi]
      exact OnePoint.coe_ne_infty _
  have hP : IsKQC P Ω 1 :=
    isKQC_one_of_conformal (mobius_finite_open hM) (mobius_finite_conformal hM)
  have h1 : IsKQC (g ∘ P) Ω K := by
    simpa only [one_mul] using thm7_1_comp hP hgq (subset_univ _)
  have h2 : IsKQC (Q ∘ g ∘ P) Ω K :=
    (bg_comp_conformal h1 (mobius_finite_open hN) (mobius_finite_conformal hN)
      (by rintro _ ⟨z, hz, rfl⟩; exact (hval z hz).2)).1
  have hlocal : IsKQC f Ω K := ad_isKQC_congr h2 (fun z hz => (hval z hz).1)
  have hhome := sphereFinite_homeomorph hFb hFc hFi
  have himage : f '' univ = univ := hhome.2.2.1
  apply iskqc_of_subsingleton_exceptional (P := fun z => M (z : ExtPlane) ≠ extInf)
    isOpen_univ (by rwa [himage]) hgq.2.1 (subset_univ _) ?_ hlocal
  intro z hz w hw
  exact OnePoint.coe_injective (hMc.2.1 ((not_not.mp hz.2).trans (not_not.mp hw.2).symm))

theorem sphereTransport_differentiableOn {G M N : ExtPlane → ExtPlane} {g : ℂ → ℂ}
    (hGb : Function.Bijective G) (hGc : Continuous G)
    (hg : ∀ z : ℂ, G (z : ExtPlane) = (g z : ExtPlane))
    (hgd : DifferentiableOn ℂ g unitDiscExterior) (hM : IsMobius M) (hN : IsMobius N)
    (hME : MapsTo M extDiscExterior extDiscExterior)
    (hi : N (G (M extInf)) = extInf) :
    DifferentiableOn ℂ (fun z : ℂ => finPart (N (G (M (z : ExtPlane))))) unitDiscExterior := by
  let F : ExtPlane → ExtPlane := N ∘ G ∘ M
  let f : ℂ → ℂ := fun z => finPart (F (z : ExtPlane))
  let P : ℂ → ℂ := fun z => finPart (M (z : ExtPlane))
  let Q : ℂ → ℂ := fun z => finPart (N (z : ExtPlane))
  let Ω : Set ℂ := {z | z ∈ unitDiscExterior ∧ M (z : ExtPlane) ≠ extInf}
  have hMc := mobius_sphere_continuous_bijective hM
  have hNc := mobius_sphere_continuous_bijective hN
  have hFb : Function.Bijective F := hNc.2.comp (hGb.comp hMc.2)
  have hFc : Continuous F := hNc.1.comp (hGc.comp hMc.1)
  have hFi : F extInf = extInf := hi
  have hval : ∀ z ∈ Ω, f z = Q (g (P z)) ∧ N (g (P z) : ExtPlane) ≠ extInf := by
    intro z hz
    have he : F (z : ExtPlane) = N (g (P z) : ExtPlane) := by
      change N (G (M (z : ExtPlane))) = _
      rw [← coe_finPart_of_ne hz.2, hg]
    constructor
    · exact congrArg finPart he
    · rw [← he, ← sphereFinite_coe hFb hFi]
      exact OnePoint.coe_ne_infty _
  have hPmem : MapsTo P Ω unitDiscExterior := by
    intro z hz
    have he := hME (show (z : ExtPlane) ∈ extDiscExterior from Or.inl ⟨z, hz.1, rfl⟩)
    rw [← coe_finPart_of_ne hz.2] at he
    rcases he with he | he
    · exact coe_mem_toExt_iff.mp he
    · exact (OnePoint.coe_ne_infty _ he).elim
  have hdiff : DifferentiableOn ℂ f Ω := by
    have hPd := (mobius_finite_conformal hM).1.mono (fun z (hz : z ∈ Ω) => hz.2)
    have h1 : DifferentiableOn ℂ (g ∘ P) Ω := hgd.comp hPd hPmem
    have h2 : DifferentiableOn ℂ (Q ∘ g ∘ P) Ω :=
      (mobius_finite_conformal hN).1.comp h1 (fun z hz => (hval z hz).2)
    exact h2.congr (fun z hz => (hval z hz).1)
  have hex : (unitDiscExterior \ Ω).Subsingleton := by
    intro z hz w hw
    have hz' : M (z : ExtPlane) = extInf := by
      by_contra hn
      exact hz.2 ⟨hz.1, hn⟩
    have hw' : M (w : ExtPlane) = extInf := by
      by_contra hn
      exact hw.2 ⟨hw.1, hn⟩
    exact OnePoint.coe_injective (hMc.2.1 (hz'.trans hw'.symm))
  refine differentiableOn_of_finite_exceptional
    (show IsOpen unitDiscExterior from isOpen_lt continuous_const continuous_norm)
    hex.finite (sphereFinite_continuous_proper hFb hFc hFi).1.continuousOn ?_
  apply hdiff.mono
  intro z hz
  by_contra hn
  exact hz.2 ⟨hz.1, hn⟩

end TakhtajanTeo

#print axioms TakhtajanTeo.sphereTransport_isKQC
#print axioms TakhtajanTeo.sphereTransport_differentiableOn
