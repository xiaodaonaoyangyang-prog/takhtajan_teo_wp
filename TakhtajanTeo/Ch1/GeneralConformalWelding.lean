import TakhtajanTeo.Ch1.CircleQCPlaneExtension
import TakhtajanTeo.Ch1.WeldingFromExtension

/-! Complete general welding candidates, preserving the original heads. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem general_weldingPrime_exists {h : ℂ → ℂ} (hh : IsQSCircleHomeo h) :
    ∃ f g, IsWeldingPrime h f g := by
  obtain ⟨H, hH, hHs, hHc, hHh⟩ := circle_quasisymmetric_plane_extension hh
  exact weldingPrime_exists_of_plane_extension hH hHs hHc hHh

theorem welding_of_weldingPrime {h f g : ℂ → ℂ} (hw : IsWeldingPrime h f g) :
    IsWelding h id f g := by
  obtain ⟨⟨F, G, hF, hFs, hFf, hG, hGs, hGg, hb⟩, hrest⟩ := hw
  refine ⟨rfl, ⟨F, G, hF, hFs, hFf, hG, hGs, hGg, ?_⟩, hrest⟩
  intro z hz
  exact congrArg (fun z : ℂ => (z : ExtPlane)) (hb z hz)

theorem conformal_welding_prime_complete {h : ℂ → ℂ} (hh : IsOneFixedQS h) :
    (∃ f g, IsWeldingPrime h f g) ∧
      ∀ f₁ f₂ g₁ g₂, IsWeldingPrime h f₁ g₁ → IsWeldingPrime h f₂ g₂ →
        EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior := by
  exact ⟨general_weldingPrime_exists hh.1, fun _ _ _ _ => conformal_welding_prime_unique hh⟩

theorem conformal_welding_complete {h : ℂ → ℂ} (hh : IsNormalizedQS h) :
    (∃ α f g, IsWelding h α f g) ∧ ∀ f₁ f₂ g₁ g₂, IsWelding h id f₁ g₁ → IsWelding h id f₂ g₂ →
      EqOn f₁ f₂ unitDisc ∧ EqOn g₁ g₂ unitDiscExterior := by
  refine ⟨?_, fun _ _ _ _ => conformal_welding_unique hh⟩
  obtain ⟨f, g, hw⟩ := general_weldingPrime_exists hh.1
  exact ⟨id, f, g, welding_of_weldingPrime hw⟩

end TakhtajanTeo

#print axioms TakhtajanTeo.conformal_welding_complete
#print axioms TakhtajanTeo.conformal_welding_prime_complete
