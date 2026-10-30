import TakhtajanTeo.Ch1.Eq22ReflectionSphere
import TakhtajanTeo.Ch1.QuasidiskKernel

open Complex Set Metric Filter Topology

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem hr6_exterior_density_chart {E : Set ℂ} {φ : ℂ → ℂ} {p u : ℂ}
    (h0 : ∀ z ∈ E, z ≠ 0) (hp : p ∉ E)
    (hDo : IsOpen ((fun z : ℂ => z⁻¹) '' E ∪ {0}))
    (hφ : IsConformalOnto φ ((fun z : ℂ => z⁻¹) '' E ∪ {0}) unitDisc) (hu : u ∈ E) :
    poincareDensity (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' E)) (u - p)⁻¹ *
      ‖(u - p)⁻¹‖ ^ 2 = poincareDensityNearInfty E u := by
  let T : ℂ → ℂ := fun w => w / (1 - p * w)
  have hden : ∀ w ∈ (fun z : ℂ => z⁻¹) '' E ∪ {0}, 1 - p * w ≠ 0 := by
    rintro w (⟨v, hv, rfl⟩ | hw)
    · have hv0 := h0 v hv
      have hvp : v - p ≠ 0 := sub_ne_zero.mpr (fun he => hp (he ▸ hv))
      have he : 1 - p * v⁻¹ = (v - p) / v := by field_simp <;> ring
      rw [he]
      exact div_ne_zero hvp hv0
    · have hw0 : w = 0 := hw
      simp [hw0]
  have hTval : ∀ v ∈ E, T v⁻¹ = (v - p)⁻¹ := by
    intro v hv
    have hv0 := h0 v hv
    have hvp : v - p ≠ 0 := sub_ne_zero.mpr (fun he => hp (he ▸ hv))
    have he : 1 - p * v⁻¹ = (v - p) / v := by field_simp <;> ring
    dsimp only [T]
    rw [he]
    field_simp
  have hT : IsConformalOnto T ((fun z : ℂ => z⁻¹) '' E ∪ {0})
      (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' E)) := by
    refine ⟨fun w hw => ?_, ?_, ?_⟩
    · exact (differentiableAt_id.div
        ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const p).mul differentiableAt_id))
        (hden w hw)).differentiableWithinAt
    · intro x hx y hy hxy
      have he := (div_eq_div_iff (hden x hx) (hden y hy)).mp hxy
      linear_combination he
    · ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with ⟨v, hv, rfl⟩ | hw
        · exact Or.inr ⟨v, hv, (hTval v hv).symm⟩
        · have hw0 : w = 0 := hw
          simp [T, hw0]
      · rintro (rfl | ⟨v, hv, rfl⟩)
        · exact ⟨0, Or.inr rfl, by simp [T]⟩
        · exact ⟨v⁻¹, Or.inl ⟨v, hv, rfl⟩, hTval v hv⟩
  have hu0 := h0 u hu
  have hup : u - p ≠ 0 := sub_ne_zero.mpr (fun he => hp (he ▸ hu))
  have huid : u⁻¹ ∈ (fun z : ℂ => z⁻¹) '' E ∪ {0} := Or.inl ⟨u, hu, rfl⟩
  have hDT : HasDerivAt T (1 / (1 - p * u⁻¹) ^ 2) u⁻¹ := by
    convert (hasDerivAt_id u⁻¹).div
      ((hasDerivAt_const u⁻¹ (1 : ℂ)).sub ((hasDerivAt_id u⁻¹).const_mul p))
      (hden u⁻¹ huid) using 1
    · rfl
    · change 1 / (1 - p * u⁻¹) ^ 2 =
        (1 * (1 - p * u⁻¹) - u⁻¹ * (0 - p * 1)) / (1 - p * u⁻¹) ^ 2
      congr 1
      ring
  have hdeneq : 1 - p * u⁻¹ = (u - p) / u := by field_simp <;> ring
  have hdnorm : ‖deriv T u⁻¹‖ = ‖u‖ ^ 2 / ‖u - p‖ ^ 2 := by
    rw [hDT.deriv, hdeneq, norm_div, norm_one, norm_pow, norm_div]
    field_simp
  have hcov := aw_tr_density_conformal hDo hT hφ huid
  rw [hTval u hu, hdnorm] at hcov
  unfold poincareDensityNearInfty
  rw [← hcov, norm_inv]
  field_simp

-- L2
theorem hr6_welding_exterior_density_chart {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {p u : ℂ} (hp : p ∈ frontier (fsans μ '' unitDisc))
    (hu : u ∈ gsans μ '' unitDiscExterior) :
    poincareDensity (insert 0 ((fun z : ℂ => (z - p)⁻¹) '' (gsans μ '' unitDiscExterior))) (u - p)⁻¹ *
      ‖(u - p)⁻¹‖ ^ 2 = poincareDensityNearInfty (gsans μ '' unitDiscExterior) u := by
  let E := gsans μ '' unitDiscExterior
  let H : ℂ → ℂ := fun w => if w = 0 then 0 else (gsans μ w⁻¹)⁻¹
  obtain ⟨hHd, hHi, hg0⟩ := r24_inversion hμ
  have hHimg : H '' unitDisc = (fun z : ℂ => z⁻¹) '' E ∪ {0} := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hw0 : w = 0
      · simp [H, hw0]
      · exact Or.inl ⟨gsans μ w⁻¹, ⟨w⁻¹, QCV.qcv_inv_mem_exterior ⟨hw, hw0⟩, rfl⟩,
          by simp [H, hw0]⟩
    · rintro (⟨v, hv, rfl⟩ | hy)
      · obtain ⟨x, hx, rfl⟩ := hv
        have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by have : 1 < ‖x‖ := hx; linarith)
        have hxi : x⁻¹ ∈ unitDisc := by
          rw [unitDisc, mem_ball_zero_iff, norm_inv]
          exact inv_lt_one_of_one_lt₀ hx
        exact ⟨x⁻¹, hxi, by simp [H, inv_ne_zero hx0]⟩
      · have hy0 : y = 0 := hy
        exact ⟨0, mem_ball_self one_pos, by simp [H, hy0]⟩
  have hH : IsConformalOnto H unitDisc ((fun z : ℂ => z⁻¹) '' E ∪ {0}) :=
    ⟨hHd, hHi, hHimg⟩
  have h0 : ∀ z ∈ E, z ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg0 x hx
  have hpn : p ∉ E := by
    intro hpE
    exact Set.disjoint_left.mp (s16p_basic (eq22_welding_components hμ)).2.2.2.2.1
      (Or.inl ⟨p, hpE, rfl⟩) ⟨p, hp, rfl⟩
  exact hr6_exterior_density_chart h0 hpn (hH.isOpen isOpen_ball) (hH.symm isOpen_ball) hu

end TakhtajanTeo
