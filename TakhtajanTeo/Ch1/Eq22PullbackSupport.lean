import Mathlib

open Complex Set
namespace TakhtajanTeo

theorem eq22_pullback_support {E : Set ℂ} {h H χ : ℂ → ℂ}
    (hc : HasCompactSupport χ) (hH : ContinuousOn H (tsupport χ))
    (hm : MapsTo H (tsupport χ) E) (hi : ∀ u ∈ E, H (h u) = u) :
    HasCompactSupport (E.indicator (χ ∘ h)) ∧
      tsupport (E.indicator (χ ∘ h)) ⊆ E := by
  have hK : IsCompact (H '' tsupport χ) := hc.isCompact.image_of_continuousOn hH
  have hs : Function.support (E.indicator (χ ∘ h)) ⊆ H '' tsupport χ := by
    intro u hu
    have hup : u ∈ E ∧ χ (h u) ≠ 0 := by
      simpa [Function.mem_support, Function.comp_def] using hu
    exact ⟨h u, subset_tsupport _ (Function.mem_support.mpr hup.2), hi u hup.1⟩
  have ht : tsupport (E.indicator (χ ∘ h)) ⊆ H '' tsupport χ :=
    closure_minimal hs hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure ht, ht.trans ?_⟩
  rintro _ ⟨v,hv,rfl⟩
  exact hm hv

theorem eq22_pullback_continuous {E : Set ℂ} {h H χ : ℂ → ℂ}
    (hE : IsOpen E) (hh : ContinuousOn h E) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hH : ContinuousOn H (tsupport χ))
    (hm : MapsTo H (tsupport χ) E) (hi : ∀ u ∈ E, H (h u) = u) :
    Continuous (E.indicator (χ ∘ h)) := by
  have ht := (eq22_pullback_support hc hH hm hi).2
  have hOn : ContinuousOn (E.indicator (χ ∘ h)) E :=
    (hχ.comp_continuousOn hh).congr (fun u hu => indicator_of_mem hu _)
  exact hOn.continuous_of_tsupport_subset hE ht

end TakhtajanTeo
