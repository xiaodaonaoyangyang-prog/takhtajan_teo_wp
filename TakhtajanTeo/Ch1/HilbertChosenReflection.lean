import TakhtajanTeo.Ch1.Eq22ReflectionSphere
import TakhtajanTeo.Ch1.HilbertReflectionPreimage

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate

namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem hc6_welding_quasidisc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ K : ℝ, 1 ≤ K ∧ IsKQuasidisc (fsans μ '' unitDisc) K ∧
      Bornology.IsBounded (fsans μ '' unitDisc) ∧
      gsans μ '' unitDiscExterior = (closure (fsans μ '' unitDisc))ᶜ := by
  obtain ⟨F, G, ⟨K, hK⟩, hFs, hFf, -⟩ := (gMu_isWelding hμ).2.1
  obtain ⟨e, he⟩ := t203_pack_homeo hK hFs
  have heK : IsKQC (e : ℂ → ℂ) univ K := by rwa [he]
  have himg : fsans μ '' unitDisc = e '' unitDisc := by
    rw [S2C.s2c_fsans_eq hμ, ← hFf.image_eq, ← he]
  have hb : Bornology.IsBounded (fsans μ '' unitDisc) := by
    rw [himg]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hΩo : IsOpen (fsans μ '' unitDisc) := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hΩc : IsConnected (fsans μ '' unitDisc) := by
    rw [himg]
    exact (isConnected_ball one_pos).image e e.continuous.continuousOn
  have hfr : frontier (toExt (fsans μ '' unitDisc)) = toExt (e '' sphere (0 : ℂ) 1) := by
    rw [frontier_toExt_of_isBounded' hb hΩo, himg, ← e.image_frontier]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hQ : IsKQuasicircle (frontier (toExt (fsans μ '' unitDisc))) K := by
    refine ⟨e, heK, image_univ_of_surjective e.surjective, mobiusExt 1 0 0 1,
      ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
    have hId : mobiusExt 1 0 0 1 = id := funext t203_pack_mobius_id
    rw [hId, image_id, hfr]
    exact (s13x_de_image_toExt e (sphere (0 : ℂ) 1)).symm
  refine ⟨K, hK.2.1, ⟨⟨hΩo, hΩc, n18_isJordanCurve hQ⟩, hQ⟩, hb, ?_⟩
  obtain ⟨e', hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  rw [hgimg, hfimg, ← e'.image_closure, ← e'.image_compl, unitDisc,
    closure_ball (0 : ℂ) one_ne_zero]
  congr 1
  ext z
  simp [unitDiscExterior, mem_closedBall, not_le]

-- L2
theorem hc6_chosen_reflection {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (h : ℂ → ℂ) (K : ℝ) (p : ℂ) (C : ℝ), 0 ≤ C ∧ p ∈ fsans μ '' unitDisc ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧
      IsPlanarQCReflection (gsans μ '' unitDiscExterior) ((fsans μ '' unitDisc) \ {p}) h K ∧
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      Tendsto h (cocompact ℂ ⊓ 𝓟 (gsans μ '' unitDiscExterior)) (𝓝 p) ∧
      (∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
        poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C) ∧
      (∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖dzbar h u‖ *
        poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C) := by
  obtain ⟨K0, hK0, hD, hbD, hEeq⟩ := hc6_welding_quasidisc hμ
  obtain ⟨C, hC, hconstruct⟩ := t203_reflection hK0
  obtain ⟨h, K, p, hp, hC1, hR, ht, hbound⟩ := hconstruct _ hD hbD
  rw [← hEeq] at hC1 hR ht hbound
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp [unitDiscExterior, mem_closedBall, not_le]
  have hfr : frontier (gsans μ '' unitDiscExterior) = frontier (fsans μ '' unitDisc) := by
    rw [hgimg, hfimg, ← e.image_frontier, ← e.image_frontier, hDc, frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hweak : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h := by
    refine ⟨⟨K, hR.2.2.1⟩, fun u hu => ?_, ?_⟩
    · exact (hR.2.1 ▸ mem_image_of_mem h hu).1
    · intro x hx
      have hxn : x ∉ fsans μ '' unitDisc :=
        fun hxin => hx.2 (hD.1.1.interior_eq.symm ▸ hxin)
      have hxp : x ∉ closure ({p} : Set ℂ) := by
        rw [closure_singleton]
        intro hxp
        exact hxn ((mem_singleton_iff.mp hxp).symm ▸ hp)
      have hxfr : x ∈ frontier ((fsans μ '' unitDisc) \ {p}) :=
        ⟨closure_sdiff ⟨hx.1, hxp⟩, fun hxi => hxn (interior_subset hxi).1⟩
      exact hR.2.2.2 x ⟨hfr.symm ▸ hx, hxfr⟩
  have hop : ∀ u ∈ gsans μ '' unitDiscExterior, ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ *
      poincareDensity (fsans μ '' unitDisc) (h u) ^ 2 ≤ C := by
    intro u hu
    simpa only [norm_sub_rev (h u) u] using hbound u hu
  refine ⟨h, K, p, C, hC, hp, hC1, hR, hweak, ht, hop, ?_⟩
  intro u hu
  have hdz : ‖dzbar h u‖ ≤ ‖fderiv ℝ h u‖ := by
    linarith [t203_norm_dz_add_dzbar_le (g := h) (z := u), norm_nonneg (dz h u)]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdz (sq_nonneg _))
    (sq_nonneg _)).trans (hop u hu)

-- L3
theorem hc6_chosen_raw_coefficient {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (h : ℂ → ℂ) (C : ℝ), 0 ≤ C ∧
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧
      ∀ (q : ℂ → ℂ) (M : ℝ), 0 ≤ M → DifferentiableOn ℂ q (fsans μ '' unitDisc) →
        (∀ v ∈ fsans μ '' unitDisc, ‖q v‖ ≤ M * poincareDensity (fsans μ '' unitDisc) v ^ 2) →
        MemLp (hbPre_reflected q h) ⊤ (volume.restrict (gsans μ '' unitDiscExterior)) ∧
          ∀ u ∈ gsans μ '' unitDiscExterior, ‖hbPre_reflected q h u‖ ≤ M * C / 2 := by
  obtain ⟨h, K, p, C, hC, hp, hC1, hR, hh, ht, hop, hgeom⟩ := hc6_chosen_reflection hμ
  refine ⟨h, C, hC, hh, hC1, ?_⟩
  intro q M hM hq hqbound
  have hbound := hbPre_reflected_bound hh.2.1 hM hqbound hgeom
  have hEo : IsOpen (gsans μ '' unitDiscExterior) := hR.2.2.1.1
  have hc : ContinuousOn (hbPre_reflected q h) (gsans μ '' unitDiscExterior) := by
    unfold hbPre_reflected
    exact ((continuousOn_const.mul (hq.continuousOn.comp hC1.continuousOn hh.2.1)).mul
      ((continuousOn_id.sub hC1.continuousOn).pow 2)).mul
      (continuousOn_dz_dzbar hC1 hEo).2
  refine ⟨memLp_top_of_bound (hc.aestronglyMeasurable hEo.measurableSet) (M * C / 2) ?_, hbound⟩
  filter_upwards [ae_restrict_mem hEo.measurableSet] with u hu
  exact hbound u hu

end TakhtajanTeo
