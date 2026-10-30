import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.GeneralWeldingUniqueness

/-! A genuine global QC witness for the relative interior conformal map.
This supplies ambient and boundary compatibility, with no L2 claim. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The interior welding map has an actual global plane QC extension. -/
theorem cra_welding_extension {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (e : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC e univ K ∧ EqOn e (fsans μ) unitDisc := by
  obtain ⟨F, G, ⟨K, hK⟩, hFs, hFf, -⟩ := (gMu_isWelding hμ).2.1
  obtain ⟨e, he⟩ := t203_pack_homeo hK hFs
  refine ⟨e, K, by rwa [he], ?_⟩
  intro w hw
  rw [he, S2C.s2c_fsans_eq hμ]
  exact hFf hw

/-- Compose the two independently provided ambient welding extensions. -/
theorem cra_ambient_exists {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∃ (H : ℂ ≃ₜ ℂ) (K : ℝ), IsKQC H univ K ∧
      ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w := by
  obtain ⟨eμ, Kμ, hKμ, heμ⟩ := cra_welding_extension hμ
  obtain ⟨eν, Kν, hKν, heν⟩ := cra_welding_extension hν
  let H := eμ.symm.trans eν
  have hHK : IsKQC H univ (Kμ*Kν) := by
    change IsKQC ((eν : ℂ → ℂ) ∘ (eμ.symm : ℂ → ℂ)) univ _
    exact thm7_1_comp (homeomorph_inverse_isKQC eμ hKμ) hKν (subset_univ _)
  refine ⟨H, Kμ*Kν, hHK, ?_⟩
  intro w hw
  change eν (eμ.symm (fsans μ w)) = fsans ν w
  rw [← heμ hw, eμ.symm_apply_apply]
  exact heν hw

/-- The ambient witness agrees with the actual relative conformal map on
the interior; no value of invFunOn outside its domain is used. -/
theorem cra_relative_eqOn {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    {H : ℂ ≃ₜ ℂ} (he : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) :
    EqOn H (fsans ν ∘ Function.invFunOn (fsans μ) unitDisc) (fsans μ '' unitDisc) := by
  rintro z ⟨w, hw, rfl⟩
  dsimp only [Function.comp_apply]
  rw [(S2C.s2c_conf_f hμ).2.1.leftInvOn_invFunOn hw]
  exact he w hw

/-- Exact images of the interior, its closure and boundary, and the exterior. -/
theorem cra_ambient_images {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {H : ℂ ≃ₜ ℂ} (he : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) :
    H '' (fsans μ '' unitDisc) = fsans ν '' unitDisc ∧
      H '' closure (fsans μ '' unitDisc) = closure (fsans ν '' unitDisc) ∧
      H '' frontier (fsans μ '' unitDisc) = frontier (fsans ν '' unitDisc) ∧
      H '' (gsans μ '' unitDiscExterior) = gsans ν '' unitDiscExterior := by
  have hΩ : H '' (fsans μ '' unitDisc) = fsans ν '' unitDisc := by
    rw [image_image]
    exact image_congr he
  have hc : H '' closure (fsans μ '' unitDisc) = closure (fsans ν '' unitDisc) := by
    rw [H.image_closure, hΩ]
  refine ⟨hΩ, hc, ?_, ?_⟩
  · rw [H.image_frontier, hΩ]
  · obtain ⟨_, _, _, _, hEμ⟩ := hc6_welding_quasidisc hμ
    obtain ⟨_, _, _, _, hEν⟩ := hc6_welding_quasidisc hν
    rw [hEμ, hEν, H.image_compl, hc]

theorem cra_relative_conformal {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {H : ℂ ≃ₜ ℂ} (he : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) :
    IsConformalOnto H (fsans μ '' unitDisc) (fsans ν '' unitDisc) := by
  have hfμ := S2C.s2c_conf_f hμ
  have hfν := S2C.s2c_conf_f hν
  have hi := hfμ.symm isOpen_ball
  have hdiff : DifferentiableOn ℂ (fsans ν ∘ Function.invFunOn (fsans μ) unitDisc)
      (fsans μ '' unitDisc) := hfν.1.comp hi.1 hi.mapsTo
  exact ⟨hdiff.congr (cra_relative_eqOn hμ he), H.injective.injOn,
    (cra_ambient_images hμ hν he).1⟩

/-- The relative interior map extends continuously to every boundary point,
with trace equal to the actual global QC witness. -/
theorem cra_relative_boundary_limit {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    {H : ℂ ≃ₜ ℂ} (he : ∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) (z : ℂ) :
    Tendsto (fsans ν ∘ Function.invFunOn (fsans μ) unitDisc)
      (𝓝[fsans μ '' unitDisc] z) (𝓝 (H z)) := by
  apply (H.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  exact eventually_nhdsWithin_of_forall (fun w hw => cra_relative_eqOn hμ he hw)

/-- Concrete global witness with domain, boundary and extension interfaces.
Only the two original admissible coefficients are inputs. -/
theorem cra_relative_ambient {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∃ (H : ℂ ≃ₜ ℂ) (K : ℝ), 1 ≤ K ∧ IsKQC H univ K ∧
      (∀ w ∈ unitDisc, H (fsans μ w) = fsans ν w) ∧
      IsConformalOnto H (fsans μ '' unitDisc) (fsans ν '' unitDisc) ∧
      EqOn H (fsans ν ∘ Function.invFunOn (fsans μ) unitDisc) (fsans μ '' unitDisc) ∧
      H '' closure (fsans μ '' unitDisc) = closure (fsans ν '' unitDisc) ∧
      H '' frontier (fsans μ '' unitDisc) = frontier (fsans ν '' unitDisc) ∧
      H '' (gsans μ '' unitDiscExterior) = gsans ν '' unitDiscExterior ∧
      ∀ z ∈ frontier (fsans μ '' unitDisc),
        Tendsto (fsans ν ∘ Function.invFunOn (fsans μ) unitDisc)
          (𝓝[fsans μ '' unitDisc] z) (𝓝 (H z)) := by
  obtain ⟨H, K, hK, he⟩ := cra_ambient_exists hμ hν
  obtain ⟨hΩ, hc, hf, hE⟩ := cra_ambient_images hμ hν he
  exact ⟨H, K, hK.2.1, hK, he, cra_relative_conformal hμ hν he,
    cra_relative_eqOn hμ he, hc, hf, hE, fun z _ => cra_relative_boundary_limit hμ he z⟩

#print axioms cra_welding_extension
#print axioms cra_ambient_exists
#print axioms cra_relative_eqOn
#print axioms cra_ambient_images
#print axioms cra_relative_conformal
#print axioms cra_relative_boundary_limit
#print axioms cra_relative_ambient
end TakhtajanTeo
