import TakhtajanTeo.Ch1.S2Core
import LiZhongQC.Lemmas.LV81PunctureRemovable

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem eq22_antiquasi_puncture_limit {G Ω : Set ℂ} {h : ℂ → ℂ} {r : ℝ}
    (hq : IsQuasiconformal (fun z => conj (h z)) G) (hm : MapsTo h G Ω)
    (hb : Bornology.IsBounded Ω) (hreg : interior (closure Ω) ⊆ Ω)
    (hr : 0 < r) (hsub : ball (0 : ℂ) r \ {0} ⊆ G) (h0 : (0 : ℂ) ∉ G) :
    ∃ a ∈ Ω, Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 a) ∧ a ∉ h '' G := by
  classical
  obtain ⟨K, hK⟩ := hq
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hbconj : Bornology.IsBounded
      ((fun z => conj (h z)) '' (ball (0 : ℂ) r \ {0})) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simpa only [norm_conj] using hC (h x) (hm (hsub hx))
  obtain ⟨b, ht, hnot, hext⟩ := lv81_puncture_removable hK hr hsub h0 hbconj
  let H : ℂ → ℂ := fun z => conj (Function.update (fun w => conj (h w)) 0 b z)
  have hH0 : H 0 = conj b := by simp [H]
  have hHG : EqOn H h G := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx
    simp [H, Function.update_of_ne hx0]
  have hlim : Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 (conj b)) := by
    simpa only [Function.comp_def, conj_conj] using
      continuous_conj.continuousAt.tendsto.comp ht
  have hGe : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ∈ G := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds 0 hr), self_mem_nhdsWithin]
      with x hx hx0
    exact hsub ⟨hx, hx0⟩
  have hcl : conj b ∈ closure Ω :=
    mem_closure_of_tendsto hlim (hGe.mono fun x hx => hm hx)
  have hHo : IsOpen (H '' insert 0 G) := by
    apply isOpen_image_of_continuousOn_injOn hext.1
    · exact continuous_conj.comp_continuousOn hext.2.2.1.1
    · intro x hx y hy hxy
      apply hext.2.2.1.2.1 hx hy
      simpa only [H, conj_conj] using congrArg conj hxy
  have hHcl : H '' insert 0 G ⊆ closure Ω := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · rwa [hH0]
    · rw [hHG hx]
      exact subset_closure (hm hx)
  refine ⟨conj b, hreg ((interior_maximal hHcl hHo)
    ⟨0, mem_insert 0 G, hH0⟩), hlim, ?_⟩
  rintro ⟨x, hx, hxa⟩
  apply hnot
  exact ⟨x, hx, by simpa only [conj_conj] using congrArg conj hxa⟩

-- L2
theorem eq22_antiquasi_infty_limit {E Ω : Set ℂ} {h : ℂ → ℂ}
    (hE : E ∈ cocompact ℂ) (h0 : (0 : ℂ) ∉ E)
    (hq : IsQuasiconformal (fun z => conj (h z)) E) (hm : MapsTo h E Ω)
    (hb : Bornology.IsBounded Ω) (hreg : interior (closure Ω) ⊆ Ω) :
    ∃ a ∈ Ω, Tendsto h (cocompact ℂ) (𝓝 a) ∧ a ∉ h '' E := by
  classical
  obtain ⟨K, hK⟩ := hq
  let G : Set ℂ := {0}ᶜ ∩ (fun w : ℂ => w⁻¹) ⁻¹' E
  have hGo : IsOpen G :=
    continuousOn_inv₀.isOpen_inter_preimage isOpen_compl_singleton hK.1
  have hconf : IsConformalOnto (fun w : ℂ => w⁻¹) G
      ((fun w : ℂ => w⁻¹) '' G) := by
    refine ⟨fun w hw => (differentiableAt_inv hw.1).differentiableWithinAt,
      inv_injective.injOn, rfl⟩
  have hqi := isKQC_one_of_conformal hGo hconf
  have hcomp : IsQuasiconformal (fun w => conj (h w⁻¹)) G := by
    refine ⟨K, ?_⟩
    have hqcomp := thm7_1_comp hqi hK (by
      rintro _ ⟨w, hw, rfl⟩
      exact hw.2)
    simpa only [one_mul, Function.comp_def] using hqcomp
  have hit : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have hGe : G ∈ 𝓝[≠] (0 : ℂ) := by
    filter_upwards [hit hE, self_mem_nhdsWithin] with w hw hw0
    exact ⟨hw0, hw⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hGe
  obtain ⟨a, ha, ht, hnot⟩ := eq22_antiquasi_puncture_limit hcomp
    (fun w hw => hm hw.2) hb hreg hr hsub (by simp [G])
  have hback : Tendsto (fun u : ℂ => u⁻¹) (cocompact ℂ) (𝓝[≠] (0 : ℂ)) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded'
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [Function.comp_def, inv_inv] using ht.comp hback
  · rintro ⟨u, hu, hua⟩
    apply hnot
    have hu0 : u ≠ 0 := by rintro rfl; exact h0 hu
    exact ⟨u⁻¹, ⟨inv_ne_zero hu0, by simpa using hu⟩, by simpa using hua⟩

-- L3
theorem eq22_reflection_infty_limit {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      a ∉ h '' (gsans μ '' unitDiscExterior) := by
  obtain ⟨F, G, ⟨KF, hKF⟩, hFs, hFf, ⟨KG, hKG⟩, hGs, hGg, -⟩ :=
    (gMu_isWelding hμ).2.1
  obtain ⟨eF, heF⟩ := t203_pack_homeo hKF hFs
  obtain ⟨eG, heG⟩ := t203_pack_homeo hKG hGs
  have hFimg : fsans μ '' unitDisc = eF '' unitDisc := by
    rw [S2C.s2c_fsans_eq hμ, ← hFf.image_eq, ← heF]
  have hGimg : gsans μ '' unitDiscExterior = eG '' unitDiscExterior := by
    rw [S2C.s2c_gsans_eq hμ, ← hGg.image_eq, ← heG]
  have hb : Bornology.IsBounded (fsans μ '' unitDisc) := by
    rw [hFimg]
    exact ((isCompact_closedBall (0 : ℂ) 1).image eF.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hreg : interior (closure (fsans μ '' unitDisc)) ⊆ fsans μ '' unitDisc := by
    rw [hFimg, ← eF.image_closure, ← eF.image_interior]
    simp only [unitDisc, closure_ball (0 : ℂ) one_ne_zero,
      interior_closedBall (0 : ℂ) one_ne_zero]
    exact Subset.rfl
  have hE : gsans μ '' unitDiscExterior ∈ cocompact ℂ := by
    have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
      ext z
      simp [unitDiscExterior, mem_closedBall, not_le]
    rw [hGimg, hDc, eG.image_compl]
    exact ((isCompact_closedBall (0 : ℂ) 1).image eG.continuous).compl_mem_cocompact
  have h0 : (0 : ℂ) ∉ gsans μ '' unitDiscExterior := by
    have hf0 : fsans μ 0 = 0 := by
      rw [S2C.s2c_fsans_eq hμ]
      exact (fB_normalization μ).1
    exact Set.disjoint_left.mp (AppB.b8_welding_normalized_pair hμ).2.2.2.2.2
      ⟨0, mem_ball_self one_pos, hf0⟩
  exact eq22_antiquasi_infty_limit hE h0 hh.1 hh.2.1 hb hreg

end TakhtajanTeo
