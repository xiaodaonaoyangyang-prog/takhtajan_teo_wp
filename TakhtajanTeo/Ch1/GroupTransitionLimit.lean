import TakhtajanTeo.Ch1.GroupInverseLimit
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Convergence of the plane transition and its reciprocal chart in the S3 argument. -/
open Set Filter Topology
namespace TakhtajanTeo

/-- The two independently normalized plane maps induce an identity-convergent transition. -/
theorem grp_transition_tendsto {F W : ℕ → (ℂ ≃ₜ ℂ)}
    (hF : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) id atTop)
    (hW : TendstoLocallyUniformly (fun n => (W n : ℂ → ℂ)) id atTop) :
    TendstoLocallyUniformly (fun n z => W n ((F n).symm z)) id atTop := by
  have hi := kn6_inverse_locallyUniform (F := Homeomorph.refl ℂ) hF
  have hFi : Tendsto (fun n => (⟨(F n).symm, (F n).symm.continuous⟩ : C(ℂ, ℂ))) atTop
      (𝓝 (ContinuousMap.id ℂ)) := ContinuousMap.tendsto_of_tendstoLocallyUniformly hi
  have hWi : Tendsto (fun n => (⟨W n, (W n).continuous⟩ : C(ℂ, ℂ))) atTop
      (𝓝 (ContinuousMap.id ℂ)) := ContinuousMap.tendsto_of_tendstoLocallyUniformly hW
  have hc := ContinuousMap.continuous_comp'.tendsto
    (ContinuousMap.id ℂ, ContinuousMap.id ℂ) |>.comp (hFi.prodMk_nhds hWi)
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hc

/-- Reciprocal transition charts converge off zero; analyticity at zero is a separate input. -/
theorem grp_transition_reciprocal_tendsto {F W : ℕ → (ℂ ≃ₜ ℂ)}
    (hF : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) id atTop)
    (hW : TendstoLocallyUniformly (fun n => (W n : ℂ → ℂ)) id atTop) :
    TendstoLocallyUniformlyOn (fun n t => (W n ((F n).symm t⁻¹))⁻¹)
      id atTop ({0}ᶜ : Set ℂ) := by
  have hc := (grp_transition_tendsto hF hW).tendstoLocallyUniformlyOn
    |>.comp (fun t : ℂ => t⁻¹) (mapsTo_univ _ _) continuousOn_inv₀
  have hh := hc.inv₀ continuousOn_inv₀ (fun t ht => inv_ne_zero ht)
  convert hh using 1 <;> simp [Function.comp_def, Pi.inv_def] <;> rfl

end TakhtajanTeo
