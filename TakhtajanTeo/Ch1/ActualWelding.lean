import TakhtajanTeo.Ch1.RadialMobiusDistortion
import TakhtajanTeo.Ch1.NormalizedWelding
/-! # Actual normalized welding from the Model A closed-disk extension

The explicit radial extension of the disk Möbius factor supplies a global
QC plane extension of Model A. This removes the extension premise from the
normalized welding construction and verifies the choice-based `gMu` witness.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem radial_normalized_solution_disk_images {μ : LinfStar} {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extA μ)) :
    W '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 ∧ W '' unitDisc = unitDisc := by
  have hsurj : Function.Surjective W := by
    intro w
    have hw : w ∈ W '' univ := by rw [hW.2.1]; trivial
    obtain ⟨z, -, hz⟩ := hw
    exact ⟨z, hz⟩
  constructor
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with h | h
      · exact mem_closedBall_zero_iff.mpr (normalized_solution_disc hW h).le
      · exact mem_closedBall_zero_iff.mpr (normalized_solution_circle hW h).le
    · intro hw
      obtain ⟨z, rfl⟩ := hsurj w
      refine ⟨z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff] at hw ⊢
      by_contra hz
      exact (not_lt.mpr hw) (normalized_solution_exterior hW (not_le.mp hz))
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.mpr (normalized_solution_disc hW (mem_ball_zero_iff.mp hz))
    · intro hw
      obtain ⟨z, rfl⟩ := hsurj w
      refine ⟨z, ?_, rfl⟩
      rw [unitDisc, mem_ball_zero_iff] at hw ⊢
      by_contra hz
      rcases (not_lt.mp hz).lt_or_eq with h | h
      · have := normalized_solution_exterior hW h
        linarith
      · have := normalized_solution_circle hW h.symm
        linarith

theorem wA_hasQCExtension_closed {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    HasQCExtension (wA μ) (closedBall (0 : ℂ) 1) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, -, -, -⟩ := wA_spec hμ
  obtain ⟨hWcl, hWD⟩ := radial_normalized_solution_disk_images hW
  let m : ℂ → ℂ := fun z => finPart (M (z : ExtPlane))
  have hMfin : ∀ z ∈ closedBall (0 : ℂ) 1, M (z : ExtPlane) ≠ extInf := by
    intro z hz
    have hz' : z ∈ W '' closedBall (0 : ℂ) 1 := by rw [hWcl]; exact hz
    obtain ⟨u, hu, rfl⟩ := hz'
    have hmem := (wAS_closed_iff hμ (u : ExtPlane)).mp ⟨u, hu, rfl⟩
    rw [hwf] at hmem
    intro he
    rw [he] at hmem
    exact infty_notMem_toExt _ hmem
  have hmc : ContinuousOn m (closedBall (0 : ℂ) 1) :=
    (mobius_finite_conformal hM).1.continuousOn.mono hMfin
  have hMD : IsConformalOnto m unitDisc unitDisc := by
    refine ⟨(mobius_finite_conformal hM).1.mono (fun z hz => hMfin z (ball_subset_closedBall hz)),
      (mobius_finite_conformal hM).2.1.mono (fun z hz => hMfin z (ball_subset_closedBall hz)), ?_⟩
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ W '' unitDisc := by rw [hWD]; exact hz
      obtain ⟨u, hu, rfl⟩ := hz'
      obtain ⟨v, hv, he⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hu)
      change finPart (M (W u : ExtPlane)) ∈ unitDisc
      rw [← hwf, he]
      exact mem_ball_zero_iff.mpr hv
    · intro hw
      have hw' : (w : ExtPlane) ∈ wAS μ '' toExt unitDisc := by
        rw [(wA_mapsTo hμ).1]
        exact ⟨w, hw, rfl⟩
      obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := hw'
      refine ⟨W u, mem_ball_zero_iff.mpr (normalized_solution_disc hW (mem_ball_zero_iff.mp hu)), ?_⟩
      change finPart (M (W u : ExtPlane)) = w
      rw [← hwf, he]
      rfl
  obtain ⟨G, ⟨KG, hKG⟩, hGs, hGm⟩ := conformal_disk_hasQCExtension_closed hMD hmc
  obtain ⟨KW, hKW⟩ := hW.1
  refine ⟨G ∘ W, ⟨KW * KG, thm7_1_comp hKW hKG (subset_univ _)⟩, ?_, ?_⟩
  · rw [image_comp, hW.2.1, hGs]
  · intro z hz
    have hWz : W z ∈ closedBall (0 : ℂ) 1 := by
      rw [← hWcl]
      exact mem_image_of_mem W hz
    rw [Function.comp_apply, hGm hWz]
    change finPart (M (W z : ExtPlane)) = finPart (wAS μ (z : ExtPlane))
    rw [hwf]

theorem normalizedWelding_actual {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsWelding (wA μ) id (fB μ) (normalizedWeldingExterior μ) :=
  normalizedWelding_of_modelA_extension hμ (wA_hasQCExtension_closed hμ)

theorem normalizedWeldingPrime_actual {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsWeldingPrime (wA μ) (fB μ) (normalizedWeldingExterior μ) :=
  normalizedWeldingPrime_of_modelA_extension hμ (wA_hasQCExtension_closed hμ)

theorem alphaMu_eq_id (μ : LinfStar) : alphaMu μ = id := by
  unfold alphaMu
  split_ifs with h
  · obtain ⟨g, hg⟩ := h.choose_spec
    exact hg.1
  · rfl

theorem gMu_isWelding {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsWelding (wA μ) (alphaMu μ) (fB μ) (gMu μ) := by
  have hex : ∃ g, IsWelding (wA μ) (alphaMu μ) (fB μ) g :=
    ⟨normalizedWeldingExterior μ, by rw [alphaMu_eq_id]; exact normalizedWelding_actual hμ⟩
  unfold gMu
  rw [dif_pos hex]
  exact hex.choose_spec

theorem fB_hasQCExtension_closed {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    HasQCExtension (fB μ) (closedBall (0 : ℂ) 1) := by
  obtain ⟨H, ⟨KH, hKH⟩, hHs, hHa⟩ := wA_hasQCExtension_closed hμ
  obtain ⟨KG, hKG⟩ := normalizedWeldingExterior_quasiconformal hμ
  have hGs := (normalizedWeldingExterior_homeomorph hμ).2.2.1
  refine ⟨normalizedWeldingExterior μ ∘ H,
    ⟨KH * KG, thm7_1_comp hKH hKG (subset_univ _)⟩, ?_, ?_⟩
  · rw [image_comp, hHs, hGs]
  · intro z hz
    rw [Function.comp_apply, hHa hz]
    exact normalizedWeldingExterior_closedDisk hμ hz

end TakhtajanTeo
