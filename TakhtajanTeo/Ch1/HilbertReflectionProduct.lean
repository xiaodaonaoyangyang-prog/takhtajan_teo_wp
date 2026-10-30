import TakhtajanTeo.Ch1.HilbertReflectionDensity
import TakhtajanTeo.Ch1.HilbertExteriorDensity
import TakhtajanTeo.Ch1.Eq22ReflectionTransport

open Complex Set Metric Filter Topology

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem hr6_reflection_density_product {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ gsans μ '' unitDiscExterior,
      1 / C ≤ ‖u - h u‖ ^ 4 * poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 *
        poincareDensityNearInfty (gsans μ '' unitDiscExterior) u ^ 2 ∧
      ‖u - h u‖ ^ 4 * poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 *
        poincareDensityNearInfty (gsans μ '' unitDiscExterior) u ^ 2 ≤ C := by
  let Ω := fsans μ '' unitDisc
  let E := gsans μ '' unitDiscExterior
  have hΩ : IsOpen Ω := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hφ := (S2C.s2c_conf_f hμ).symm isOpen_ball
  have hcomp := eq22_welding_components hμ
  obtain ⟨a, ha, F, hFc, hF, hFa, hagree⟩ := eq22_reflection_sphere hμ hh
  obtain ⟨e0, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  let p : ℂ := e0 1
  have hp : p ∈ frontier Ω := by
    change p ∈ frontier (fsans μ '' unitDisc)
    rw [hfimg, ← e0.image_frontier]
    refine ⟨1, ?_, rfl⟩
    simp [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hpΩ : p ∉ Ω := fun hpI => hp.2 (hΩ.interior_eq.symm ▸ hpI)
  have hEp : ∀ u ∈ E, u ≠ p := by
    intro u hu hup
    have hpE : p ∈ E := hup ▸ hu
    exact disjoint_left.mp (s16p_basic hcomp).2.2.2.2.1
      (Or.inl ⟨p, hpE, rfl⟩) ⟨p, hp, rfl⟩
  let γ : ℂ → ℂ := fun z => (z - p)⁻¹
  let e : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph 0 1 1 (-p) (uq_j_inv_det p)
  have hep : e (p : ExtPlane) = extInf := uq_j_mobiusInv_apply_self p
  have heinf : e extInf = ((0 : ℂ) : ExtPlane) := by
    change mobiusHomeomorph 0 1 1 (-p) (uq_j_inv_det p) extInf = _
    rw [mobiusHomeomorph_apply, mobiusExt_infty_of_ne one_ne_zero, zero_div]
  have hez : ∀ z : ℂ, z ≠ p → e (z : ExtPlane) = ((γ z : ℂ) : ExtPlane) := by
    intro z hz
    change mobiusHomeomorph 0 1 1 (-p) (uq_j_inv_det p) (z : ExtPlane) = _
    rw [uq_j_mobiusInv_coe hz]
    congr 1
    simp [γ, mobiusFn, sub_eq_add_neg, one_div]
  have himage : ∀ S : Set ℂ, (∀ z ∈ S, z ≠ p) → e '' toExt S = toExt (γ '' S) := by
    intro S hS
    unfold toExt
    rw [image_image, image_image]
    exact image_congr (fun z hz => hez z (hS z hz))
  let A : Set ℂ := insert 0 (γ '' E)
  let B : Set ℂ := γ '' Ω
  let Ccurve : Set ExtPlane := e '' toExt (frontier Ω)
  have hA : e '' (toExt E ∪ {extInf}) = toExt A := by
    rw [image_union, image_singleton, heinf, himage E hEp]
    simp only [A, toExt, image_insert_eq, union_singleton]
  have hB : e '' toExt Ω = toExt B := himage Ω (fun z hz he => hpΩ (he ▸ hz))
  have hcomp' : AreComplementaryComponents Ccurve (toExt A) (toExt B) := by
    have hct := s16p_areComplementaryComponents_image hcomp e
    rw [hA, hB] at hct
    exact hct
  have hF' : LiZhongQC.IsQCReflection Ccurve (toExt A) (toExt B) (e ∘ F ∘ e.symm) := by
    have hft := s16p_refl_transport hcomp hF e (α := 0) (β := 1) (q := p) one_ne_zero hep
      (fun z hz => by simpa only [zero_add, one_mul] using hez z hz)
    rw [hA, hB] at hft
    exact hft
  have hinf : extInf ∈ Ccurve := ⟨p, ⟨p, hp, rfl⟩, hep⟩
  have hq : IsQuasicircle Ccurve := (LiZhongQC.thm16_2 hcomp').mpr ⟨_, hF'⟩
  let g : ℂ → ℂ := fun z => extToC (e (F (e.symm (z : ExtPlane))))
  obtain ⟨K, hK, hR⟩ := eq22_transport_sphere_planar hcomp' hinf hF'
  obtain ⟨C, hC, hprod⟩ := hr6_planar_density_product hcomp' hinf hq hR
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hv : h u ∈ Ω := hh.2.1 hu
  have hvp : h u ≠ p := fun he => hpΩ (he ▸ hv)
  have hvn : ‖h u - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvp)
  have hun : ‖u - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hEp u hu))
  have hg : g (γ u) = γ (h u) := by
    change extToC (e (F (e.symm ((γ u : ℂ) : ExtPlane)))) = γ (h u)
    rw [← hez u (hEp u hu), e.symm_apply_apply, hagree u hu, hez (h u) hvp]
    rfl
  have hIn := s20l_density_mobius hΩ hφ hpΩ hv
  change poincareDensity B (γ (h u)) * ‖γ (h u)‖ ^ 2 = poincareDensity Ω (h u) at hIn
  have hOut := hr6_welding_exterior_density_chart hμ hp hu
  change poincareDensity A (γ u) * ‖γ u‖ ^ 2 = poincareDensityNearInfty E u at hOut
  have hd := s20l_a3_norm_sub (inv_ne_zero (sub_ne_zero.mpr hvp)) (hEp u hu)
  have hdist : ‖u - h u‖ = ‖γ (h u) - γ u‖ * ‖h u - p‖ * ‖u - p‖ := by
    calc ‖u - h u‖ = ‖h u - u‖ := norm_sub_rev _ _
      _ = _ := by simpa only [γ, inv_inv, add_sub_cancel] using hd
  have hcov : ‖u - h u‖ ^ 4 * poincareDensity Ω (h u) ^ 2 *
      poincareDensityNearInfty E u ^ 2 =
      ‖γ u - g (γ u)‖ ^ 4 * poincareDensity B (g (γ u)) ^ 2 * poincareDensity A (γ u) ^ 2 := by
    rw [hg, norm_sub_rev (γ u) (γ (h u)), hdist, ← hIn, ← hOut]
    simp only [γ, norm_inv]
    field_simp [hvn, hun]
    <;> ring
  change 1 / C ≤ ‖u - h u‖ ^ 4 * poincareDensity Ω (h u) ^ 2 *
    poincareDensityNearInfty E u ^ 2 ∧
    ‖u - h u‖ ^ 4 * poincareDensity Ω (h u) ^ 2 * poincareDensityNearInfty E u ^ 2 ≤ C
  rw [hcov]
  exact hprod (γ u) (Or.inr ⟨u, hu, rfl⟩)

end TakhtajanTeo
