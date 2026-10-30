import TakhtajanTeo.Ch1.QCVariationBergman
import TakhtajanTeo.Ch1.S1_1_Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem hp_toLinf_congr {f g : ℂ → ℂ} (h : EqOn f g unitDiscExterior) : toLinf f = toLinf g := by
  have hmeas : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hae : f =ᵐ[volume.restrict unitDiscExterior] g := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hmeas]
    exact Filter.Eventually.of_forall h
  unfold toLinf
  by_cases hf : MemLp f ∞ (volume.restrict unitDiscExterior)
  · have hg : MemLp g ∞ (volume.restrict unitDiscExterior) := hf.ae_eq hae
    rw [dif_pos hf, dif_pos hg]
    exact MemLp.toLp_congr hf hg hae
  · have hg : ¬ MemLp g ∞ (volume.restrict unitDiscExterior) := fun hg => hf (hg.ae_eq hae.symm)
    rw [dif_neg hf, dif_neg hg]

theorem hp_eq_Lambda (μ : LinfStar) : harmonicProj μ = Lambda (fderiv ℂ bersPhi 0 μ) := by
  unfold harmonicProj Lambda
  apply hp_toLinf_congr
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num [unitDiscExterior] at hz
  have hc : conj z ≠ 0 := (map_ne_zero conj).2 hz0
  have hw : refl z ∈ unitDisc := (refl_mem_disc_iff hz0).2 hz
  have h14 := eq_1_4 μ (refl z) hw
  show 3 * (1 - (‖z‖ : ℂ) ^ 2) ^ 2 / π * ∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4 =
    -(1 / 2) * (1 - (‖z‖ : ℂ) ^ 2) ^ 2 * AInf.toFun (fderiv ℂ bersPhi 0 μ) (refl z) / conj z ^ 4
  rw [h14]
  have hint : ∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4 =
      ((conj z)⁻¹) ^ 4 * ∫ ζ in unitDiscExterior, μ ζ / (ζ - refl z) ^ 4 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show μ ζ / (1 - ζ * conj z) ^ 4 = ((conj z)⁻¹) ^ 4 * (μ ζ / (ζ - refl z) ^ 4)
    have h1 : 1 - ζ * conj z = -conj z * (ζ - (conj z)⁻¹) := by
      field_simp
      ring
    unfold refl
    rw [h1, show (-conj z * (ζ - (conj z)⁻¹)) ^ 4 = conj z ^ 4 * (ζ - (conj z)⁻¹) ^ 4 by ring]
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  rw [hint]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

theorem harmonicProj_isProjection_cand :
    (∀ (a : ℂ) μ ν, harmonicProj (a • μ + ν) = a • harmonicProj μ + harmonicProj ν) ∧
      (∀ μ, harmonicProj (harmonicProj μ) = harmonicProj μ) ∧
      range harmonicProj = harmonicBeltrami ∧ harmonicProj ⁻¹' {0} = trivialBeltrami := by
  obtain ⟨h1, h2, h3⟩ := lambda_inverse_D0bers
  refine ⟨fun a μ ν => ?_, fun μ => ?_, ?_, ?_⟩
  · rw [hp_eq_Lambda, hp_eq_Lambda, hp_eq_Lambda, map_add, map_smul, Lambda_add, Lambda_smul]
  · rw [hp_eq_Lambda, hp_eq_Lambda, h2]
  · ext ν
    simp only [mem_range, SetLike.mem_coe]
    constructor
    · rintro ⟨μ, rfl⟩
      rw [hp_eq_Lambda]
      exact h1 _
    · intro hν
      refine ⟨ν, ?_⟩
      rw [hp_eq_Lambda]
      exact h3 ν hν
  · ext μ
    simp only [mem_preimage, mem_singleton_iff, SetLike.mem_coe]
    rw [← ker_D0Phi, LinearMap.mem_ker, hp_eq_Lambda]
    constructor
    · intro h
      have := h2 (fderiv ℂ bersPhi 0 μ)
      rw [h, map_zero] at this
      exact this.symm
    · intro h
      rw [show (fderiv ℂ bersPhi 0 : LinfStar →L[ℂ] AInf unitDisc) μ = 0 from h]
      have := Lambda_smul 0 (0 : AInf unitDisc)
      simpa using this

/-! ### Original relocated from `S1_1` (2026-10-26) -/

/-- (TT:548–551) `P` is the projection of `L∞(𝔻*)` onto `Ω^{-1,1}(𝔻*)` along `𝓝(𝔻*)`, defined by the decomposition
(1.3): `P` is linear, idempotent, with image `Ω^{-1,1}(𝔻*)` and kernel `𝓝(𝔻*)`. -/
theorem harmonicProj_isProjection :
    (∀ (a : ℂ) μ ν, harmonicProj (a • μ + ν) = a • harmonicProj μ + harmonicProj ν) ∧
      (∀ μ, harmonicProj (harmonicProj μ) = harmonicProj μ) ∧
      range harmonicProj = harmonicBeltrami ∧ harmonicProj ⁻¹' {0} = trivialBeltrami :=
  harmonicProj_isProjection_cand

end TakhtajanTeo
