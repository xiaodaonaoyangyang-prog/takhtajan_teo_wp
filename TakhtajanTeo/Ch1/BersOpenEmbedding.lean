import TakhtajanTeo.Ch1.BersInjective
import TakhtajanTeo.Ch1.BanachHolomorphic
import TakhtajanTeo.Ch1.QCVariation

/-! # The Bers embedding is an open embedding, given surjective differentials

`bers_isOpenEmbedding_of_submersion`: if `D_μ bersPhi` is onto for every `μ ∈ L∞(𝔻*)₁` (the first conjunct of
`phi_submersion`), then `bers` is an open embedding of `T(1)`. Injectivity is `bers_injective`; openness is the
Banach implicit-function theorem applied to `bersPhi` (strictly differentiable by `bh_hasStrictFDerivAt`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem bers_isOpenEmbedding_of_submersion
    (hsub : ∀ μ ∈ LinfStarBall,
      LinearMap.range (fderiv ℂ bersPhi μ : LinfStar →ₗ[ℂ] AInf unitDisc) = ⊤) :
    Topology.IsOpenEmbedding bers := by
  haveI : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  have hball : IsOpen (LinfStarBall : Set LinfStar) := isOpen_ball
  have hopen : ∀ V : Set LinfStar, IsOpen V → V ⊆ LinfStarBall → IsOpen (bersPhi '' V) := by
    intro V hV hVb
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨μ, hμV, rfl⟩
    have hs := bh_hasStrictFDerivAt hball bersPhi_differentiableOn (hVb hμV)
    have hmap := hs.map_nhds_eq_of_surj (hsub μ (hVb hμV))
    rw [← hmap]
    exact Filter.image_mem_map (hV.mem_nhds hμV)
  have hquot : Topology.IsQuotientMap (Phi : LinfStarBall → T1) := isQuotientMap_quotient_mk'
  have hPhi : Continuous (Phi : LinfStarBall → T1) := hquot.continuous
  have hbPhi : (bers ∘ Phi : LinfStarBall → AInf unitDisc) = fun μ : LinfStarBall => bersPhi (μ : LinfStar) := by
    funext μ
    exact bers_Phi μ
  have hcont : Continuous bers := by
    rw [hquot.continuous_iff, hbPhi]
    exact bersPhi_differentiableOn.continuousOn.comp_continuous continuous_subtype_val
      (fun μ => μ.2)
  have hbo : IsOpenMap bers := by
    intro U hU
    have hV : IsOpen (Subtype.val '' (Phi ⁻¹' U : Set LinfStarBall)) :=
      hball.isOpenMap_subtype_val _ (hU.preimage hPhi)
    have himg : bers '' U = bersPhi '' (Subtype.val '' (Phi ⁻¹' U : Set LinfStarBall)) := by
      ext q
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨μ, rfl⟩ := Quotient.exists_rep p
        refine ⟨μ.1, ⟨μ, hp, rfl⟩, ?_⟩
        exact (bers_Phi μ).symm
      · rintro ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
        exact ⟨Phi μ, hμ, bers_Phi μ⟩
    rw [himg]
    exact hopen _ hV (by rintro _ ⟨μ, -, rfl⟩; exact μ.2)
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont bers_injective hbo

end TakhtajanTeo

