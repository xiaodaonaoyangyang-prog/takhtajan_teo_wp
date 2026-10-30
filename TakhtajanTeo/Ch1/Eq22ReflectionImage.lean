import TakhtajanTeo.Ch1.Eq22ReflectionInfinity

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem eq22_welding_common_chart {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ e : ℂ ≃ₜ ℂ, fsans μ '' unitDisc = e '' unitDisc ∧
      gsans μ '' unitDiscExterior = e '' unitDiscExterior := by
  have hwA : wA μ '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, he⟩ := wAS_maps_disc hμ (mem_ball_zero_iff.mp hz)
      have hw : wA μ z = u := by unfold wA; rw [he]; rfl
      rw [hw]
      exact mem_ball_zero_iff.mpr hu
    · intro z hz
      have hz' : (z : ExtPlane) ∈ wAS μ '' toExt unitDisc := by
        rw [(wA_mapsTo hμ).1]
        exact ⟨z, hz, rfl⟩
      obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := hz'
      exact ⟨u, hu, congrArg finPart he⟩
  obtain ⟨K, hK⟩ := normalizedWeldingExterior_quasiconformal hμ
  obtain ⟨e, he⟩ := t203_pack_homeo hK (normalizedWeldingExterior_homeomorph hμ).2.2.1
  refine ⟨e, ?_, ?_⟩
  · have heq : EqOn (normalizedWeldingExterior μ ∘ wA μ) (fB μ) unitDisc :=
      fun z hz => normalizedWeldingExterior_closedDisk hμ (ball_subset_closedBall hz)
    rw [S2C.s2c_fsans_eq hμ, ← heq.image_eq, image_comp, hwA, ← he]
  · rw [S2C.s2c_gsans_eq hμ, (gMu_eq_normalizedWeldingExterior hμ).image_eq, ← he]

-- L2
theorem eq22_filled_image_isOpen {E : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (hE : E ∈ cocompact ℂ) (hEo : IsOpen E) (hc : ContinuousOn h E) (hi : InjOn h E)
    (ht : Tendsto h (cocompact ℂ) (𝓝 a)) (ha : a ∉ h '' E) :
    IsOpen (insert a (h '' E)) := by
  classical
  have hinv : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp (hinv hE)
  let F := Function.update (fun w : ℂ => h w⁻¹) 0 a
  have hF0 : F 0 = a := by simp [F]
  have hFc : ContinuousOn F (ball (0 : ℂ) r) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    by_cases hx0 : x = 0
    · subst x
      exact continuousAt_update_same.mpr (ht.comp hinv)
    · have hxe : x⁻¹ ∈ E := hsub ⟨hx, hx0⟩
      have hc' := ((hc x⁻¹ hxe).continuousAt (hEo.mem_nhds hxe)).comp
        (continuousAt_inv₀ hx0)
      apply hc'.congr
      filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
      exact (Function.update_of_ne hy a (fun w : ℂ => h w⁻¹)).symm
  have hFi : InjOn F (ball (0 : ℂ) r) := by
    intro x hx y hy heq
    by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0
    · exact hx0.trans hy0.symm
    · subst x
      have hey : F y = h y⁻¹ := Function.update_of_ne hy0 _ _
      rw [hF0, hey] at heq
      exact False.elim (ha ⟨y⁻¹, hsub ⟨hy, hy0⟩, heq.symm⟩)
    · subst y
      have hex : F x = h x⁻¹ := Function.update_of_ne hx0 _ _
      rw [hF0, hex] at heq
      exact False.elim (ha ⟨x⁻¹, hsub ⟨hx, hx0⟩, heq⟩)
    · simp only [F, Function.update_of_ne hx0, Function.update_of_ne hy0] at heq
      exact inv_injective (hi (hsub ⟨hx, hx0⟩) (hsub ⟨hy, hy0⟩) heq)
  have hFo := isOpen_image_of_continuousOn_injOn isOpen_ball hFc hFi
  have hFs : F '' ball (0 : ℂ) r ⊆ insert a (h '' E) := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · simp [hx0, hF0]
    · exact Or.inr ⟨x⁻¹, hsub ⟨hx, hx0⟩,
        (Function.update_of_ne hx0 a (fun w : ℂ => h w⁻¹)).symm⟩
  apply isOpen_iff_mem_nhds.mpr
  rintro x (rfl | hx)
  · exact mem_of_superset (hFo.mem_nhds ⟨0, mem_ball_self hr, hF0⟩) hFs
  · exact mem_of_superset ((isOpen_image_of_continuousOn_injOn hEo hc hi).mem_nhds hx)
      (subset_insert a _)

-- L3
theorem eq22_image_eq_punctured_of_boundary {E Ω : Set ℂ} {h : ℂ → ℂ} {a : ℂ}
    (hE : E ∈ cocompact ℂ) (hEo : IsOpen E) (hΩo : IsOpen Ω) (hΩ : IsConnected Ω)
    (hm : MapsTo h E Ω) (hc : ContinuousOn h E) (hi : InjOn h E)
    (hfr : frontier E ⊆ frontier Ω)
    (hb : ∀ x ∈ frontier Ω, Tendsto h (𝓝[E] x) (𝓝 x))
    (ha : a ∈ Ω) (ht : Tendsto h (cocompact ℂ) (𝓝 a)) (hna : a ∉ h '' E) :
    h '' E = Ω \ {a} := by
  classical
  have hclosed : closure (h '' E) ∩ Ω ⊆ insert a (h '' E) := by
    rintro v ⟨hvcl, hvΩ⟩
    by_cases hva : v = a
    · exact Or.inl hva
    obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp hvcl
    choose u hu heu using hs
    have hlim : Tendsto (fun n => h (u n)) atTop (𝓝 v) := by
      simpa only [heu] using hst
    have hd : 0 < dist v a / 3 := div_pos (dist_pos.mpr hva) (by norm_num)
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp (ht (ball_mem_nhds a hd))
    have hKe : ∀ᶠ n in atTop, u n ∈ K := by
      filter_upwards [hlim (ball_mem_nhds v hd)] with n hn
      by_contra hnK
      have hnA : dist (h (u n)) a < dist v a / 3 := hKs hnK
      have hnV : dist v (h (u n)) < dist v a / 3 := by simpa [mem_ball, dist_comm] using hn
      have htri := dist_triangle v (h (u n)) a
      linarith
    obtain ⟨x, -, σ, hσ, hxlim⟩ := hK.tendsto_subseq' hKe.frequently
    have hxcl : x ∈ closure E := mem_closure_of_tendsto hxlim
      (Eventually.of_forall fun n => hu (σ n))
    have hxwithin : Tendsto (u ∘ σ) atTop (𝓝[E] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxlim, Eventually.of_forall fun n => hu (σ n)⟩
    have hvlim : Tendsto (fun n => h (u (σ n))) atTop (𝓝 v) :=
      hlim.comp hσ.tendsto_atTop
    by_cases hxE : x ∈ E
    · have hhv : v = h x := tendsto_nhds_unique hvlim ((hc x hxE).tendsto.comp hxwithin)
      exact Or.inr ⟨x, hxE, hhv.symm⟩
    · have hxfr : x ∈ frontier Ω := hfr ⟨hxcl, fun hx => hxE (interior_subset hx)⟩
      have hvx : v = x := tendsto_nhds_unique hvlim ((hb x hxfr).comp hxwithin)
      have hxΩ : x ∈ Ω := hvx ▸ hvΩ
      exact False.elim (hxfr.2 (hΩo.interior_eq.symm ▸ hxΩ))
  have hfilled := eq22_filled_image_isOpen hE hEo hc hi ht hna
  have hsub : Ω ⊆ insert a (h '' E) :=
    hΩ.isPreconnected.subset_of_closure_inter_subset hfilled
      ⟨a, ha, mem_insert a _⟩ (by
        rw [insert_eq, closure_union, closure_singleton]
        rintro x ⟨rfl | hx, hxΩ⟩
        · exact mem_insert _ _
        · exact hclosed ⟨hx, hxΩ⟩)
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨hm hx, ?_⟩
    intro heq
    exact hna ⟨x, hx, mem_singleton_iff.mp heq⟩
  · rintro y ⟨hy, hya⟩
    rcases hsub hy with heq | hyim
    · exact False.elim (hya heq)
    · exact hyim

-- L4
theorem eq22_reflection_image {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      h '' (gsans μ '' unitDiscExterior) = (fsans μ '' unitDisc) \ {a} := by
  obtain ⟨a, ha, ht, hna⟩ := eq22_reflection_infty_limit hμ hh
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  obtain ⟨K, hK⟩ := hh.1
  have hc : ContinuousOn h (gsans μ '' unitDiscExterior) := by
    simpa only [Function.comp_def, conj_conj] using
      continuous_conj.comp_continuousOn hK.2.2.1.1
  have hi : InjOn h (gsans μ '' unitDiscExterior) := by
    intro x hx y hy hxy
    exact hK.2.2.1.2.1 hx hy (congrArg conj hxy)
  have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp [unitDiscExterior, mem_closedBall, not_le]
  have hE : gsans μ '' unitDiscExterior ∈ cocompact ℂ := by
    rw [hgimg, hDc, e.image_compl]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).compl_mem_cocompact
  have hΩo : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hΩc : IsConnected (fsans μ '' unitDisc) := by
    rw [hfimg]
    exact (isConnected_ball (show (0 : ℝ) < 1 by norm_num)).image e e.continuous.continuousOn
  have hfr : frontier (gsans μ '' unitDiscExterior) ⊆ frontier (fsans μ '' unitDisc) := by
    rw [hgimg, hfimg, ← e.image_frontier, ← e.image_frontier, hDc, frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
    exact Subset.rfl
  exact ⟨a, ha, ht, eq22_image_eq_punctured_of_boundary hE hK.1 hΩo hΩc hh.2.1
    hc hi hfr hh.2.2 ha ht hna⟩

/-- The original weak reflection satisfies the full planar reflection package
onto the punctured interior domain; the puncture is its limit at infinity. -/
theorem eq22_reflection_planar {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∃ K : ℝ, IsPlanarQCReflection (gsans μ '' unitDiscExterior)
        ((fsans μ '' unitDisc) \ {a}) h K := by
  obtain ⟨a, ha, ht, himg⟩ := eq22_reflection_image hμ hh
  obtain ⟨K, hK⟩ := hh.1
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp [unitDiscExterior, mem_closedBall, not_le]
  have hfr : frontier (gsans μ '' unitDiscExterior) = frontier (fsans μ '' unitDisc) := by
    rw [hgimg, hfimg, ← e.image_frontier, ← e.image_frontier, hDc, frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  refine ⟨a, ha, ht, K, ?_, himg, hK, ?_⟩
  · intro x hx y hy hxy
    exact hK.2.2.1.2.1 hx hy (congrArg conj hxy)
  · intro x hx
    exact hh.2.2 x (hfr ▸ hx.1)

end TakhtajanTeo
