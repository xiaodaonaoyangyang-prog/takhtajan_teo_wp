import TakhtajanTeo.Ch1.Eq22ReflectionImage

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem eq22_sphere_of_planar_data {E Ω : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (hE : E ∈ cocompact ℂ) (hΩ : IsOpen Ω) (hfr : frontier E = frontier Ω)
    (hq : IsQuasiconformal (fun z => conj (h z)) E) (ha : a ∈ Ω)
    (himg : h '' E = Ω \ {a}) (ht : Tendsto h (cocompact ℂ) (𝓝 a))
    (hb : ∀ z ∈ frontier Ω, Tendsto h (𝓝[E] z) (𝓝 z)) :
    ∃ F : ExtPlane → ExtPlane, Continuous F ∧
      LiZhongQC.IsQCReflection (toExt (frontier Ω)) (toExt E ∪ {extInf}) (toExt Ω) F ∧
      F extInf = (a : ExtPlane) ∧ ∀ u ∈ E, F (u : ExtPlane) = (h u : ExtPlane) := by
  classical
  obtain ⟨K, hK⟩ := hq
  have hc : ContinuousOn h E := by
    simpa only [Function.comp_def, conj_conj] using
      continuous_conj.comp_continuousOn hK.2.2.1.1
  have hi : InjOn h E := fun x hx y hy hxy => hK.2.2.1.2.1 hx hy (congrArg conj hxy)
  have hm : MapsTo h E Ω := fun x hx => (himg ▸ mem_image_of_mem h hx).1
  have hna : a ∉ h '' E := by rw [himg]; simp
  have hnoΩ : ∀ x ∈ frontier Ω, x ∉ Ω :=
    fun x hx hxΩ => hx.2 (hΩ.interior_eq.symm ▸ hxΩ)
  have hnoE : ∀ x ∈ frontier Ω, x ∉ E := by
    intro x hx hxE
    have hxfr : x ∈ frontier E := hfr.symm ▸ hx
    exact hxfr.2 (hK.1.interior_eq.symm ▸ hxE)
  let k : ℂ → ℂ := fun x => if x ∈ E then h x else x
  have hkc : Continuous k := by
    apply continuous_if'
    · intro x hx
      have hxfr : x ∈ frontier Ω := hfr ▸ hx
      simpa [hnoE x hxfr] using hb x hxfr
    · intro x hx
      have hxfr : x ∈ frontier Ω := hfr ▸ hx
      rw [ite_eq_right (hnoE x hxfr)]
      change Tendsto (id : ℂ → ℂ) (𝓝[Eᶜ] x) (𝓝 x)
      exact tendsto_id.mono_left nhdsWithin_le_nhds
    · exact hc
    · exact continuous_id.continuousOn
  have hkt : Tendsto k (cocompact ℂ) (𝓝 a) := by
    apply ht.congr'
    filter_upwards [hE] with x hx
    simp [k, hx]
  have hki : InjOn k (E ∪ frontier Ω) := by
    intro x hx y hy hxy
    by_cases hxE : x ∈ E <;> by_cases hyE : y ∈ E
    · exact hi hxE hyE (by simpa only [k, ite_eq_left hxE, ite_eq_left hyE] using hxy)
    · have he : h x = y := by simpa only [k, ite_eq_left hxE, ite_eq_right hyE] using hxy
      exact False.elim (hnoΩ y (hy.resolve_left hyE) (he ▸ hm hxE))
    · have he : x = h y := by simpa only [k, ite_eq_right hxE, ite_eq_left hyE] using hxy
      exact False.elim (hnoΩ x (hx.resolve_left hxE) (he.symm ▸ hm hyE))
    · simpa only [k, ite_eq_right hxE, ite_eq_right hyE] using hxy
  have hnak : a ∉ k '' (E ∪ frontier Ω) := by
    rintro ⟨x, hx, hxa⟩
    by_cases hxE : x ∈ E
    · exact hna ⟨x, hxE, by simpa only [k, ite_eq_left hxE] using hxa⟩
    · have he : x = a := by simpa only [k, ite_eq_right hxE] using hxa
      exact hnoΩ x (hx.resolve_left hxE) (he.symm ▸ ha)
  let F : ExtPlane → ExtPlane := fun p => OnePoint.elim p (a : ExtPlane) (fun x => (k x : ExtPlane))
  have hFc : Continuous F := by
    rw [OnePoint.continuous_iff]
    constructor
    · change Tendsto (fun x => (k x : ExtPlane)) (coclosedCompact ℂ) (𝓝 (a : ExtPlane))
      rw [coclosedCompact_eq_cocompact]
      exact OnePoint.continuous_coe.continuousAt.tendsto.comp hkt
    · exact OnePoint.continuous_coe.comp hkc
  have hmem : ∀ x : ℂ,
      (x : ExtPlane) ∈ (toExt E ∪ {extInf}) ∪ toExt (frontier Ω) ↔ x ∈ E ∪ frontier Ω := by
    intro x
    simp [toExt]
  have hFi : InjOn F ((toExt E ∪ {extInf}) ∪ toExt (frontier Ω)) := by
    intro p hp q hq heq
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe y =>
        have he : a = k y := OnePoint.coe_injective heq
        exact False.elim (hnak ⟨y, (hmem y).mp hq, he.symm⟩)
    | coe x =>
      induction q using OnePoint.rec with
      | infty =>
        have he : k x = a := OnePoint.coe_injective heq
        exact False.elim (hnak ⟨x, (hmem x).mp hp, he⟩)
      | coe y =>
        exact congrArg (fun z : ℂ => (z : ExtPlane))
          (hki ((hmem x).mp hp) ((hmem y).mp hq) (OnePoint.coe_injective heq))
  have hFA : F '' (toExt E ∪ {extInf}) = toExt Ω := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rcases hp with hp | hp
      · obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨h x, hm hx, by simp [F, k, hx]⟩
      · have hp' : p = extInf := mem_singleton_iff.mp hp
        subst p
        exact ⟨a, ha, rfl⟩
    · rintro _ ⟨v, hv, rfl⟩
      by_cases hva : v = a
      · exact ⟨extInf, Or.inr rfl, by simp [F, hva]⟩
      · have hvim : v ∈ h '' E := by rw [himg]; exact ⟨hv, hva⟩
        obtain ⟨x, hx, hxe⟩ := hvim
        exact ⟨(x : ExtPlane), Or.inl ⟨x, hx, rfl⟩, by simp [F, k, hx, hxe]⟩
  have hFC : ∀ p ∈ toExt (frontier Ω), F p = p := by
    rintro _ ⟨x, hx, rfl⟩
    simp [F, k, hnoE x hx]
  have hdom : {z : ℂ | (z : ExtPlane) ∈ toExt E ∪ {extInf} ∧ F z ≠ extInf} = E := by
    ext z
    simp [F, toExt]
  refine ⟨F, hFc, ⟨hFc.continuousOn, hFi, hFA, hFC, K, ?_⟩, rfl, ?_⟩
  · rw [hdom]
    apply ad_isKQC_congr hK
    intro z hz
    simp [F, k, hz, extToC]
  · intro u hu
    simp [F, k, hu]

-- L2
theorem eq22_reflection_sphere {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, ∃ F : ExtPlane → ExtPlane, Continuous F ∧
      LiZhongQC.IsQCReflection (toExt (frontier (fsans μ '' unitDisc)))
        (toExt (gsans μ '' unitDiscExterior) ∪ {extInf}) (toExt (fsans μ '' unitDisc)) F ∧
      F extInf = (a : ExtPlane) ∧
      ∀ u ∈ gsans μ '' unitDiscExterior, F (u : ExtPlane) = (h u : ExtPlane) := by
  obtain ⟨a, ha, ht, himg⟩ := eq22_reflection_image hμ hh
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp [unitDiscExterior, mem_closedBall, not_le]
  have hE : gsans μ '' unitDiscExterior ∈ cocompact ℂ := by
    rw [hgimg, hDc, e.image_compl]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).compl_mem_cocompact
  have hfr : frontier (gsans μ '' unitDiscExterior) = frontier (fsans μ '' unitDisc) := by
    rw [hgimg, hfimg, ← e.image_frontier, ← e.image_frontier, hDc, frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  exact ⟨a, ha, eq22_sphere_of_planar_data hE ((S2C.s2c_conf_f hμ).isOpen isOpen_ball)
    hfr hh.1 ha himg ht hh.2.2⟩

-- L3
theorem eq22_disk_components :
    AreComplementaryComponents (toExt (sphere (0 : ℂ) 1))
      (toExt unitDiscExterior ∪ {extInf}) (toExt unitDisc) := by
  have hS : (toExt (sphere (0 : ℂ) 1))ᶜ =
      (toExt unitDiscExterior ∪ {extInf}) ∪ toExt unitDisc := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [toExt]
    | coe z =>
      simp only [mem_compl_iff, coe_mem_toExt_iff, mem_union, mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false, unitDiscExterior, mem_setOf_eq,
        unitDisc, mem_sphere, mem_ball, dist_zero_right]
      exact (ne_iff_lt_or_gt).trans (or_comm)
  have hUeq : toExt unitDiscExterior ∪ {extInf} =
      (toExt (closedBall (0 : ℂ) 1))ᶜ := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [toExt]
    | coe z => simp [toExt, unitDiscExterior, mem_closedBall, not_le]
  have hUo : IsOpen (toExt unitDiscExterior ∪ {extInf}) := by
    rw [hUeq]
    exact (OnePoint.isClosed_image_coe.mpr
      ⟨isClosed_closedBall, isCompact_closedBall (0 : ℂ) 1⟩).isOpen_compl
  have hVo : IsOpen (toExt unitDisc) := OnePoint.isOpen_image_coe.mpr isOpen_ball
  have hdis : Disjoint (toExt unitDiscExterior ∪ {extInf}) (toExt unitDisc) := by
    apply Set.disjoint_left.mpr
    rintro _ hp ⟨z, hz, rfl⟩
    have hzE : z ∈ unitDiscExterior := by simpa [toExt] using hp
    exact (not_lt_of_ge (le_of_lt hzE)) (mem_ball_zero_iff.mp hz)
  have hUc : IsPreconnected (toExt unitDiscExterior ∪ {extInf}) :=
    aqc_isPreconnected_toExt_normGT_insert (show (0 : ℝ) ≤ 1 by norm_num)
  have hVc : IsPreconnected (toExt unitDisc) :=
    isPreconnected_ball.image _ OnePoint.continuous_coe.continuousOn
  have hUmem : extInf ∈ toExt unitDiscExterior ∪ {extInf} := Or.inr rfl
  have hVmem : ((0 : ℂ) : ExtPlane) ∈ toExt unitDisc := ⟨0, mem_ball_self one_pos, rfl⟩
  refine ⟨isJordanCurve_toExt_unitCircle, extInf, ?_, ((0 : ℂ) : ExtPlane), ?_,
    (wd_n_component_eq hS hUo hVo hdis hUc hUmem).symm,
    (wd_n_component_eq (hS.trans (union_comm _ _)) hVo hUo hdis.symm hVc hVmem).symm, ?_⟩
  · rw [hS]
    exact Or.inl hUmem
  · rw [hS]
    exact Or.inr hVmem
  · intro heq
    have hin : extInf ∈ toExt unitDisc := heq ▸ hUmem
    simp [toExt] at hin

-- L4
theorem eq22_welding_components {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AreComplementaryComponents (toExt (frontier (fsans μ '' unitDisc)))
      (toExt (gsans μ '' unitDiscExterior) ∪ {extInf}) (toExt (fsans μ '' unitDisc)) := by
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  have hC : e '' sphere (0 : ℂ) 1 = frontier (fsans μ '' unitDisc) := by
    rw [hfimg, ← e.image_frontier]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hc := s16p_areComplementaryComponents_image eq22_disk_components e.onePointCongr
  rw [s13x_de_image_toExt, image_union, s13x_de_image_toExt, image_singleton,
    s13x_de_image_toExt] at hc
  have hinf : e.onePointCongr extInf = extInf := rfl
  rw [hinf, hC, ← hfimg, ← hgimg] at hc
  exact hc

end TakhtajanTeo
