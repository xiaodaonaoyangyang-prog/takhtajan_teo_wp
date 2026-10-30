import LiZhongQC.Ch05.S20_SchwarzDomains

open Complex Set Metric Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem eq22_transport_sphere_planar {C : Set ExtPlane} {A B : Set ℂ}
    {F : ExtPlane → ExtPlane} (hC : AreComplementaryComponents C (toExt A) (toExt B))
    (hinf : extInf ∈ C) (hF : LiZhongQC.IsQCReflection C (toExt A) (toExt B) F) :
    ∃ K : ℝ, 1 ≤ K ∧ IsPlanarQCReflection A B (fun z : ℂ => extToC (F (z : ExtPlane))) K := by
  obtain ⟨hFc, hFi, hFA, hFC, K, hK⟩ := hF
  have hAo : IsOpen A := OnePoint.isOpen_image_coe.mp (s16p_basic hC).2.1
  have hm : ∀ z ∈ A, F (z : ExtPlane) ∈ toExt B := fun z hz =>
    hFA ▸ mem_image_of_mem F (show (z : ExtPlane) ∈ toExt A from ⟨z, hz, rfl⟩)
  have hfinite : ∀ z ∈ A, ((extToC (F (z : ExtPlane)) : ℂ) : ExtPlane) = F (z : ExtPlane) := by
    intro z hz
    obtain ⟨w, -, hw⟩ := hm z hz
    rw [← hw]
    rfl
  have hne : ∀ z ∈ A, F (z : ExtPlane) ≠ extInf := by
    intro z hz
    rw [← hfinite z hz]
    simp
  have hdom : {z : ℂ | (z : ExtPlane) ∈ toExt A ∧ F (z : ExtPlane) ≠ extInf} = A := by
    ext z
    simp only [mem_setOf_eq, coe_mem_toExt_iff]
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, hne z hz⟩⟩
  rw [hdom] at hK
  refine ⟨K, hK.2.1, ?_, ?_, hK, ?_⟩
  · intro z hz w hw he
    dsimp only at he
    apply OnePoint.coe_injective
    apply hFi (Or.inl ⟨z, hz, rfl⟩) (Or.inl ⟨w, hw, rfl⟩)
    rw [← hfinite z hz, ← hfinite w hw, he]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      dsimp only
      obtain ⟨v, hv, he⟩ := hm z hz
      rw [← he]
      exact hv
    · intro hw
      have hh : (w : ExtPlane) ∈ F '' toExt A := hFA.symm ▸ (show (w : ExtPlane) ∈ toExt B from ⟨w, hw, rfl⟩)
      obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := hh
      exact ⟨z, hz, by dsimp only; rw [he]; rfl⟩
  · intro z hz
    have hzC : (z : ExtPlane) ∈ C := by
      rw [← s16p_frontier_eq hC hinf]
      exact (s20l_g_mem_frontier_iff hAo z).mp hz.1
    have hc : ContinuousWithinAt (fun w : ℂ => F (w : ExtPlane)) A z :=
      (hFc _ (Or.inr hzC)).comp OnePoint.continuous_coe.continuousWithinAt
        (fun w hw => Or.inl ⟨w, hw, rfl⟩)
    have hec : ContinuousAt extToC (F (z : ExtPlane)) := by
      rw [hFC _ hzC]
      exact s16p_continuousAt_extToC z
    have hh := ContinuousAt.comp_continuousWithinAt
      (f := fun w : ℂ => F (w : ExtPlane)) hec hc
    change Tendsto (fun w : ℂ => extToC (F (w : ExtPlane))) (𝓝[A] z)
      (𝓝 (extToC (F (z : ExtPlane)))) at hh
    rw [hFC _ hzC] at hh
    exact hh

-- L2: exact interface from lean6's sphere-reflection packaging lane.
theorem eq22_chart_gap_bound {Ω E : Set ℂ} {h φ : ℂ → ℂ} {F : ExtPlane → ExtPlane} {p : ℂ}
    (hΩ : IsOpen Ω) (hφ : IsConformalOnto φ Ω unitDisc)
    (hcomp : AreComplementaryComponents (toExt (frontier Ω))
      (toExt E ∪ {extInf}) (toExt Ω))
    (hF : LiZhongQC.IsQCReflection (toExt (frontier Ω))
      (toExt E ∪ {extInf}) (toExt Ω) F)
    (hagree : ∀ u ∈ E, F (u : ExtPlane) = (h u : ExtPlane))
    (hp : p ∈ frontier Ω) :
    ∃ M : ℝ, 0 < M ∧ ∀ u ∈ E,
      ‖u - h u‖ * poincareDensity Ω (h u) * ‖h u - p‖ ≤ M * ‖u - p‖ := by
  obtain ⟨-, -, -, -, hEC, -, -⟩ := s16p_basic hcomp
  have hpΩ : p ∉ Ω := fun hpI => hp.2 (hΩ.interior_eq.symm ▸ hpI)
  have hEp : ∀ u ∈ E, u ≠ p := by
    rintro u hu rfl
    exact disjoint_left.mp hEC (Or.inl ⟨u, hu, rfl⟩) ⟨u, hp, rfl⟩
  have hm : ∀ u ∈ E, h u ∈ Ω := by
    intro u hu
    have hh : (h u : ExtPlane) ∈ toExt Ω := by
      rw [← hagree u hu, ← hF.2.2.1]
      exact ⟨u, Or.inl ⟨u, hu, rfl⟩, rfl⟩
    exact coe_mem_toExt_iff.mp hh
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
  let C : Set ExtPlane := e '' toExt (frontier Ω)
  have hA : e '' (toExt E ∪ {extInf}) = toExt A := by
    rw [image_union, image_singleton, heinf, himage E hEp]
    simp only [A, toExt, image_insert_eq, union_singleton]
  have hB : e '' toExt Ω = toExt B := himage Ω (fun z hz he => hpΩ (he ▸ hz))
  have hcomp' : AreComplementaryComponents C (toExt A) (toExt B) := by
    have hh := s16p_areComplementaryComponents_image hcomp e
    rw [hA, hB] at hh
    exact hh
  have hF' : LiZhongQC.IsQCReflection C (toExt A) (toExt B) (e ∘ F ∘ e.symm) := by
    have hh := s16p_refl_transport hcomp hF e (α := 0) (β := 1) (q := p) one_ne_zero hep
      (fun z hz => by simpa only [zero_add, one_mul] using hez z hz)
    rw [hA, hB] at hh
    exact hh
  have hinf : extInf ∈ C := ⟨p, ⟨p, hp, rfl⟩, hep⟩
  obtain ⟨Kc, hKc⟩ := (LiZhongQC.thm16_2 hcomp').mpr ⟨_, hF'⟩
  let g : ℂ → ℂ := fun z => extToC (e (F (e.symm (z : ExtPlane))))
  obtain ⟨K, hK, hR⟩ := eq22_transport_sphere_planar hcomp' hinf hF'
  obtain ⟨M, hM⟩ := lemma20_2 hK
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro u hu
  have hv : h u ∈ Ω := hm u hu
  have hvp : h u ≠ p := fun he => hpΩ (he ▸ hv)
  have hvn : ‖h u - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvp)
  have hg : g (γ u) = γ (h u) := by
    change extToC (e (F (e.symm ((γ u : ℂ) : ExtPlane)))) = γ (h u)
    rw [← hez u (hEp u hu), e.symm_apply_apply, hagree u hu, hez (h u) hvp]
    rfl
  have hζ : γ u ∈ A := Or.inr ⟨u, hu, rfl⟩
  have hgap := hM C A B Kc g hKc hinf hcomp' hR (γ u) hζ
  rw [hg] at hgap
  have hP := s20l_density_mobius hΩ hφ hpΩ hv
  change poincareDensity B (γ (h u)) * ‖γ (h u)‖ ^ 2 = poincareDensity Ω (h u) at hP
  have hηΩ := s20l_a2_density_pos hΩ hφ hv
  have hη : 0 < poincareDensity B (γ (h u)) := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (sq_nonneg ‖γ (h u)‖)
    rw [hP] at hh
    linarith
  have hprod := (le_div_iff₀ hη).mp hgap
  have hd := s20l_a3_norm_sub (inv_ne_zero (sub_ne_zero.mpr hvp)) (hEp u hu)
  have hdist : ‖u - h u‖ = ‖γ (h u) - γ u‖ * ‖h u - p‖ * ‖u - p‖ := by
    calc ‖u - h u‖ = ‖h u - u‖ := norm_sub_rev _ _
      _ = _ := by simpa only [γ, inv_inv, add_sub_cancel] using hd
  calc ‖u - h u‖ * poincareDensity Ω (h u) * ‖h u - p‖ =
        (‖γ (h u) - γ u‖ * poincareDensity B (γ (h u))) * ‖u - p‖ := by
          rw [hdist, ← hP]
          simp only [γ, norm_inv]
          field_simp [hvn]
          <;> ring
    _ ≤ M * ‖u - p‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ ≤ max M 1 * ‖u - p‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

end TakhtajanTeo
