import LiZhongQC.Ch05.S20_SchwarzDomains

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem hr6_source_gap {G g φ : ℂ → ℂ} {K : ℝ} {A₁ A₂ : Set ℂ}
    (hG : IsKQC G univ K) (hGs : G '' univ = univ)
    (hGU : G '' upperHalf = A₁) (hGL : G '' lowerHalf = A₂)
    (hsym : ∀ ζ ∈ upperHalf, G (conj ζ) = g (G ζ))
    (hφ : IsConformalOnto φ A₁ upperHalf) {z : ℂ} (hz : z ∈ A₁) :
    ‖g z - z‖ ≤ 2 * (1 + lambdaInv K) / poincareDensity A₁ z := by
  classical
  have hGi : Function.Injective G := fun x y h => hG.2.2.1.2.1 (mem_univ x) (mem_univ y) h
  have hgi : InjOn g A₁ := by
    intro x hx y hy hxy
    rw [← hGU] at hx hy
    obtain ⟨ξ, hξ, rfl⟩ := hx
    obtain ⟨η, hη, rfl⟩ := hy
    have hconj := hGi ((hsym ξ hξ).trans (hxy.trans (hsym η hη).symm))
    have he : ξ = η := by simpa only [conj_conj] using congrArg conj hconj
    exact congrArg G he
  have hgm : MapsTo g A₁ A₂ := by
    intro x hx
    rw [← hGU] at hx
    obtain ⟨ξ, hξ, rfl⟩ := hx
    rw [← hGL]
    exact ⟨conj ξ, by simpa [upperHalf, lowerHalf, conj_im] using hξ, hsym ξ hξ⟩
  have hnU : (fun w : ℂ => -w) '' upperHalf = lowerHalf :=
    wd_n_neg_image (fun w => by simp [upperHalf, lowerHalf])
  have hnL : (fun w : ℂ => -w) '' lowerHalf = upperHalf :=
    wd_n_neg_image (fun w => by simp [upperHalf, lowerHalf])
  have hnall : (fun w : ℂ => -w) '' univ = univ :=
    image_univ_of_surjective (Homeomorph.neg ℂ).surjective
  have hnq : IsKQC (fun w : ℂ => -w) univ 1 :=
    isKQC_one_of_conformal isOpen_univ
      ⟨differentiable_id.neg.differentiableOn, neg_injective.injOn, hnall⟩
  have hGm : IsKQC (fun w => G (-w)) univ K := by
    simpa only [one_mul, Function.comp_def] using thm7_1_comp hnq hG (subset_univ _)
  have hGms : (fun w => G (-w)) '' univ = univ := by
    change (G ∘ fun w : ℂ => -w) '' univ = univ
    rw [image_comp, hnall, hGs]
  have hGmU : (fun w => G (-w)) '' upperHalf = A₂ := by
    change (G ∘ fun w : ℂ => -w) '' upperHalf = A₂
    rw [image_comp, hnU, hGL]
  have hGmL : (fun w => G (-w)) '' lowerHalf = A₁ := by
    change (G ∘ fun w : ℂ => -w) '' lowerHalf = A₁
    rw [image_comp, hnL, hGU]
  have hφm : IsConformalOnto (fun w => -φ w) A₁ lowerHalf := by
    refine ⟨hφ.1.neg, fun x hx y hy hxy => hφ.2.1 hx hy (neg_injective hxy), ?_⟩
    change ((fun w : ℂ => -w) ∘ φ) '' A₁ = lowerHalf
    rw [image_comp, hφ.2.2, hnU]
  have hsm : ∀ ξ ∈ upperHalf,
      G (-conj ξ) = Function.invFunOn g A₁ (G (-ξ)) := by
    intro ξ hξ
    have hη : -conj ξ ∈ upperHalf := by simpa [upperHalf] using hξ
    have hx : G (-conj ξ) ∈ A₁ := hGU ▸ mem_image_of_mem G hη
    have he : g (G (-conj ξ)) = G (-ξ) := by
      simpa only [map_neg, conj_conj] using (hsym (-conj ξ) hη).symm
    rw [← he]
    exact (hgi.leftInvOn_invFunOn hx).symm
  have hrev := s20l_a2_core hGm hGms hGmU hGmL hsm hφm (hgm hz)
  rw [hgi.leftInvOn_invFunOn hz] at hrev
  simpa only [norm_sub_rev z (g z)] using hrev

-- L2
theorem hr6_planar_density_product {C : Set ExtPlane} {A₁ A₂ : Set ℂ}
    {g : ℂ → ℂ} {K : ℝ}
    (hcomp : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hinf : extInf ∈ C)
    (hq : IsQuasicircle C) (hR : IsPlanarQCReflection A₁ A₂ g K) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ A₁,
      1 / B ≤ ‖z - g z‖ ^ 4 * poincareDensity A₂ (g z) ^ 2 * poincareDensity A₁ z ^ 2 ∧
      ‖z - g z‖ ^ 4 * poincareDensity A₂ (g z) ^ 2 * poincareDensity A₁ z ^ 2 ≤ B := by
  obtain ⟨G, hG, hGs, hGU, hGL, -, hsym⟩ := s20l_glue hinf hcomp hq hR
  obtain ⟨⟨φ, hφ, Φ, hΦ, hΦinf⟩, ψ, hψ, Ψ, hΨ, hΨinf⟩ :=
    s20l_uniformizers hinf hcomp hq
  have hAo : IsOpen A₁ := OnePoint.isOpen_image_coe.mp (s16p_basic hcomp).2.1
  have hBo : IsOpen A₂ := OnePoint.isOpen_image_coe.mp (s16p_basic hcomp).2.2.1
  have hsep : Disjoint A₁ A₂ := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (s16p_basic hcomp).2.2.2.2.2.2
      ⟨x, hx, rfl⟩ ⟨x, hy, rfl⟩
  have hφD := isConformalOnto_cayley.comp hφ
  have hψD := s20l_a2_disc_of_lower hψ
  let T := max (2 * (1 + lambdaInv K)) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨max (T ^ 4) 16, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro z hz
  have hgz : g z ∈ A₂ := hR.2.1 ▸ mem_image_of_mem g hz
  have hzn : z ∉ A₂ := fun h => Set.disjoint_left.mp hsep hz h
  have hgzn : g z ∉ A₁ := fun h => Set.disjoint_left.mp hsep h hgz
  have hd : 0 < ‖g z - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hzn (he ▸ hgz)))
  have hη1 := s20l_a2_density_pos hAo hφD hz
  have hη2 := s20l_a2_density_pos hBo hψD hgz
  have hup1 : ‖g z - z‖ * poincareDensity A₁ z ≤ T :=
    ((le_div_iff₀ hη1).mp (hr6_source_gap hG hGs hGU hGL hsym hφ hz)).trans (le_max_left _ _)
  have hup2 : ‖g z - z‖ * poincareDensity A₂ (g z) ≤ T :=
    ((le_div_iff₀ hη2).mp (s20l_a2_core hG hGs hGU hGL hsym hψ hz)).trans (le_max_left _ _)
  have hlo1 := t203_density_ge hAo hφD hz hgzn
  have hlo2 := t203_density_ge hBo hψD hgz hzn
  rw [norm_sub_rev z (g z)] at hlo2
  have hlo1' : (1 / 2 : ℝ) ≤ ‖g z - z‖ * poincareDensity A₁ z := by
    have h := (div_le_iff₀ (mul_pos two_pos hd)).mp hlo1
    linarith
  have hlo2' : (1 / 2 : ℝ) ≤ ‖g z - z‖ * poincareDensity A₂ (g z) := by
    have h := (div_le_iff₀ (mul_pos two_pos hd)).mp hlo2
    linarith
  let P := (‖g z - z‖ * poincareDensity A₁ z) *
    (‖g z - z‖ * poincareDensity A₂ (g z))
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hPlow : (1 / 4 : ℝ) ≤ P := by
    have h := mul_le_mul hlo1' hlo2' (by norm_num) (by positivity)
    norm_num at h
    exact h
  have hPup : P ≤ T ^ 2 := by
    simpa only [pow_two] using mul_le_mul hup1 hup2 (by positivity) hT.le
  have hsqlow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hPlow 2
  have hsqup := pow_le_pow_left₀ hP0 hPup 2
  have hPeq : ‖z - g z‖ ^ 4 * poincareDensity A₂ (g z) ^ 2 * poincareDensity A₁ z ^ 2 = P ^ 2 := by
    rw [norm_sub_rev z (g z)]
    dsimp [P]
    ring
  rw [hPeq]
  constructor
  · exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 16) (le_max_right _ _)).trans
      (by norm_num at hsqlow; exact hsqlow)
  · have hpow : (T ^ 2) ^ 2 = T ^ 4 := by ring
    exact (hsqup.trans_eq hpow).trans (le_max_left _ _)

end TakhtajanTeo
