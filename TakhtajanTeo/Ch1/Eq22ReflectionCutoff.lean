import TakhtajanTeo.Ch1.Eq22ReflectionImage
import TakhtajanTeo.Ch1.Eq22PullbackSupport

open Complex Set Filter Topology
open scoped ComplexConjugate
namespace TakhtajanTeo
open LiZhongQC

theorem eq22_reflection_inverse {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∃ H : ℂ → ℂ, ContinuousOn H ((fsans μ '' unitDisc) \ {a}) ∧
        MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior) ∧
        (∀ u ∈ gsans μ '' unitDiscExterior, H (h u) = u) ∧
        (∀ v ∈ (fsans μ '' unitDisc) \ {a}, h (H v) = v) := by
  obtain ⟨a,ha,ht,himg⟩ := eq22_reflection_image hμ hh
  obtain ⟨K,hK⟩ := hh.1
  let E := gsans μ '' unitDiscExterior
  let g : ℂ → ℂ := fun u => conj (h u)
  let H : ℂ → ℂ := fun v => Function.invFunOn g E (conj v)
  have hleft : ∀ u ∈ E, H (h u) = u := by
    intro u hu
    exact hK.2.2.1.2.1.leftInvOn_invFunOn hu
  have hc : ContinuousOn H ((fsans μ '' unitDisc) \ {a}) := by
    apply hK.2.2.1.2.2.2.comp continuous_conj.continuousOn
    intro v hv
    rw [← himg] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact ⟨u,hu,rfl⟩
  refine ⟨a,ha,ht,H,hc,?_,hleft,?_⟩
  · intro v hv
    rw [← himg] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    rw [hleft u hu]
    exact hu
  · intro v hv
    rw [← himg] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    rw [hleft u hu]

theorem eq22_reflection_cutoff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∀ χ : ℂ → ℂ, Continuous χ → HasCompactSupport χ →
        tsupport χ ⊆ (fsans μ '' unitDisc) \ {a} →
        HasCompactSupport ((gsans μ '' unitDiscExterior).indicator (χ ∘ h)) ∧
        tsupport ((gsans μ '' unitDiscExterior).indicator (χ ∘ h)) ⊆
          gsans μ '' unitDiscExterior ∧
        Continuous ((gsans μ '' unitDiscExterior).indicator (χ ∘ h)) := by
  obtain ⟨a,ha,ht,H,hH,hm,hi,_⟩ := eq22_reflection_inverse hμ hh
  obtain ⟨K,hK⟩ := hh.1
  have hc : ContinuousOn h (gsans μ '' unitDiscExterior) := by
    simpa only [Function.comp_def, conj_conj] using
      continuous_conj.comp_continuousOn hK.2.2.1.1
  refine ⟨a,ha,ht,fun χ hχ hχc hs => ?_⟩
  have hHm := hH.mono hs
  have hmap : MapsTo H (tsupport χ) (gsans μ '' unitDiscExterior) :=
    fun _ hx => hm (hs hx)
  obtain ⟨hcompact,hsub⟩ := eq22_pullback_support hχc hHm hmap hi
  exact ⟨hcompact,hsub,eq22_pullback_continuous hK.1 hc hχ hχc hHm hmap hi⟩

end TakhtajanTeo
