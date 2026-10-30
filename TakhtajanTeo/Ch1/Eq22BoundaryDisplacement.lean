import TakhtajanTeo.Ch1.Eq22ReflectionSphere
import TakhtajanTeo.Ch1.Eq22ReflectionTransport
import TakhtajanTeo.Ch1.Eq22BoundaryDomain
import TakhtajanTeo.Ch1.Eq22ReflectionCutoff

open Complex Set Metric Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1: density and distance both refer to the complete physical inner domain.
theorem eq22_density_distance_lower {Ω : Set ℂ} {φ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hφ : IsConformalOnto φ Ω unitDisc) (hne : Ωᶜ.Nonempty) {v : ℂ} (hv : v ∈ Ω) :
    1 ≤ 2 * poincareDensity Ω v * Metric.infDist v Ωᶜ := by
  have hd : 0 < Metric.infDist v Ωᶜ :=
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hne).mp (fun hv' => hv' hv)
  have h := (div_le_iff₀ (mul_pos two_pos hd)).mp (t203_density_ge_infDist hΩ hφ hv hne)
  calc 1 ≤ poincareDensity Ω v * (2 * Metric.infDist v Ωᶜ) := h
    _ = _ := by ring

-- L2
theorem eq22_displacement_of_density_bound {Ω : Set ℂ} {φ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hφ : IsConformalOnto φ Ω unitDisc) (hne : Ωᶜ.Nonempty) {u v : ℂ} (hv : v ∈ Ω)
    {D : ℝ} (hgap : ‖u - v‖ * poincareDensity Ω v ≤ D) :
    ‖u - v‖ ≤ 2 * D * Metric.infDist v Ωᶜ := by
  have hlow := eq22_density_distance_lower hΩ hφ hne hv
  calc ‖u - v‖ = ‖u - v‖ * 1 := (mul_one _).symm
    _ ≤ ‖u - v‖ * (2 * poincareDensity Ω v * Metric.infDist v Ωᶜ) :=
      mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = 2 * (‖u - v‖ * poincareDensity Ω v) * Metric.infDist v Ωᶜ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2)) Metric.infDist_nonneg

-- L3: use two poles, not the weaker squared-displacement G1 consequence.
theorem eq22_two_pole_bounded_gap {u v a b : ℂ} {ρ M R : ℝ}
    (hab : a ≠ b) (hρ : 0 ≤ ρ) (hM : 0 < M) (hR : 0 ≤ R) (hu : ‖u‖ ≤ R)
    (ha : ‖u - v‖ * ρ * ‖v - a‖ ≤ M * ‖u - a‖)
    (hb : ‖u - v‖ * ρ * ‖v - b‖ ≤ M * ‖u - b‖) :
    ‖u - v‖ * ρ ≤ M * (2 * R + ‖a‖ + ‖b‖ + 1) / ‖a - b‖ := by
  have hab0 : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hdelta : ‖a - b‖ ≤ ‖v - a‖ + ‖v - b‖ := by
    calc ‖a - b‖ ≤ ‖a - v‖ + ‖v - b‖ := norm_sub_le_norm_sub_add_norm_sub a v b
      _ = _ := by rw [norm_sub_rev a v]
  have hrad : ‖u - a‖ + ‖u - b‖ ≤ 2 * R + ‖a‖ + ‖b‖ + 1 := by
    linarith [norm_sub_le u a, norm_sub_le u b]
  apply (le_div_iff₀ hab0).mpr
  calc ‖u - v‖ * ρ * ‖a - b‖ ≤ ‖u - v‖ * ρ * (‖v - a‖ + ‖v - b‖) :=
      mul_le_mul_of_nonneg_left hdelta (mul_nonneg (norm_nonneg _) hρ)
    _ = ‖u - v‖ * ρ * ‖v - a‖ + ‖u - v‖ * ρ * ‖v - b‖ := by ring
    _ ≤ M * ‖u - a‖ + M * ‖u - b‖ := add_le_add ha hb
    _ = M * (‖u - a‖ + ‖u - b‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad hM.le

-- L4: no extra regularity hypothesis on the original reflection.
theorem eq22_reflection_bounded_displacement {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ gsans μ '' unitDiscExterior, ‖u‖ ≤ R →
      ‖u - h u‖ * poincareDensity (fsans μ '' unitDisc) (h u) ≤ D ∧
      ‖u - h u‖ ≤ 2 * D * Metric.infDist (h u) (fsans μ '' unitDisc)ᶜ := by
  obtain ⟨_, _, F, _, hFs, _, hagree⟩ := eq22_reflection_sphere hμ hh
  obtain ⟨e, hΩimg, -⟩ := eq22_welding_common_chart hμ
  have hΩ := (S2C.s2c_conf_f hμ).isOpen isOpen_ball
  have hφ := (S2C.s2c_conf_f hμ).symm isOpen_ball
  have ha : e 1 ∈ frontier (fsans μ '' unitDisc) := by
    rw [hΩimg, ← e.image_frontier]
    apply mem_image_of_mem
    simp [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hb : e (-1) ∈ frontier (fsans μ '' unitDisc) := by
    rw [hΩimg, ← e.image_frontier]
    apply mem_image_of_mem
    simp [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hab : e 1 ≠ e (-1) := fun he => (by norm_num : (1 : ℂ) ≠ -1) (e.injective he)
  have hab0 : 0 < ‖e 1 - e (-1)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  obtain ⟨M1, hM1, h1⟩ := eq22_chart_gap_bound hΩ hφ (eq22_welding_components hμ) hFs hagree ha
  obtain ⟨M2, -, h2⟩ := eq22_chart_gap_bound hΩ hφ (eq22_welding_components hμ) hFs hagree hb
  let M := max M1 M2
  have hM : 0 < M := hM1.trans_le (le_max_left _ _)
  let D := M * (2 * R + ‖e 1‖ + ‖e (-1)‖ + 1) / ‖e 1 - e (-1)‖
  have hD : 0 < D := by dsimp only [D]; positivity
  have hne : (fsans μ '' unitDisc)ᶜ.Nonempty :=
    ⟨e 1, fun hv => ha.2 (hΩ.interior_eq.symm ▸ hv)⟩
  refine ⟨D, hD, fun u hu huR => ?_⟩
  have hv := hh.2.1 hu
  have hρ := (s20l_a2_density_pos hΩ hφ hv).le
  have hgap : ‖u - h u‖ * poincareDensity (fsans μ '' unitDisc) (h u) ≤ D :=
    eq22_two_pole_bounded_gap hab hρ hM hR huR
      ((h1 u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      ((h2 u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
  exact ⟨hgap, eq22_displacement_of_density_bound hΩ hφ hne hv hgap⟩

-- L5: inputs supplied by eq22_reflection_inverse; hgeom matches eq22_boundary_tail.
theorem eq22_inverse_collar_displacement {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (fsans μ '' unitDisc))
    {a : ℂ} (ha : a ∈ fsans μ '' unitDisc) (ht : Tendsto h (cocompact ℂ) (𝓝 a))
    {H : ℂ → ℂ} (hH : MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior))
    (hinv : ∀ v ∈ (fsans μ '' unitDisc) \ {a}, h (H v) = v) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ D : ℝ, 0 < D ∧
      ∀ w ∈ unitDisc, r ≤ ‖w‖ ^ 2 →
        ‖H (f w) - f w‖ * poincareDensity (fsans μ '' unitDisc) (f w) ≤ D ∧
        ‖H (f w) - f w‖ ≤ 2 * D * Metric.infDist (f w) (fsans μ '' unitDisc)ᶜ := by
  obtain ⟨η, hη, r, hr0, hr1, hsep⟩ := eq22_conformal_collar_separation hf ha
  obtain ⟨R, hR⟩ := Metric.closedBall_compl_subset_of_mem_cocompact
    (ht (ball_mem_nhds a hη)) (0 : ℂ)
  obtain ⟨D, hD, hBD⟩ := eq22_reflection_bounded_displacement hμ hh (max R 0) (le_max_right _ _)
  refine ⟨r, hr0, hr1, D, hD, fun w hw hwr => ?_⟩
  have hneq : f w ≠ a := by
    intro he
    have hsep' := hsep w hw hwr
    rw [he, sub_self, norm_zero] at hsep'
    exact (not_le_of_gt hη) hsep'
  have hv : f w ∈ (fsans μ '' unitDisc) \ {a} := ⟨hf.mapsTo hw, hneq⟩
  have hbound : ‖H (f w)‖ ≤ max R 0 := by
    by_contra hn
    have hbig : R < ‖H (f w)‖ := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hn)
    have hout : H (f w) ∈ (closedBall (0 : ℂ) R)ᶜ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hbig
    have hhB := hR hout
    change h (H (f w)) ∈ ball a η at hhB
    rw [hinv _ hv] at hhB
    have hlt : ‖f w - a‖ < η := by simpa only [mem_ball, dist_eq_norm] using hhB
    exact (not_lt_of_ge (hsep w hw hwr)) hlt
  have hresult := hBD (H (f w)) (hH hv) hbound
  rwa [hinv _ hv] at hresult

-- L6: original hh supplies all the inverse data used by L5.
theorem eq22_reflection_collar_geometry {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ} (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (fsans μ '' unitDisc)) :
    ∃ a ∈ fsans μ '' unitDisc, Tendsto h (cocompact ℂ) (𝓝 a) ∧
      ∃ H : ℂ → ℂ, ContinuousOn H ((fsans μ '' unitDisc) \ {a}) ∧
        MapsTo H ((fsans μ '' unitDisc) \ {a}) (gsans μ '' unitDiscExterior) ∧
        (∀ u ∈ gsans μ '' unitDiscExterior, H (h u) = u) ∧
        (∀ v ∈ (fsans μ '' unitDisc) \ {a}, h (H v) = v) ∧
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ D : ℝ, 0 < D ∧
          ∀ w ∈ unitDisc, r ≤ ‖w‖ ^ 2 →
            ‖H (f w) - f w‖ * poincareDensity (fsans μ '' unitDisc) (f w) ≤ D ∧
            ‖H (f w) - f w‖ ≤ 2 * D * Metric.infDist (f w) (fsans μ '' unitDisc)ᶜ := by
  obtain ⟨a, ha, ht, H, hH, hm, hleft, hright⟩ := eq22_reflection_inverse hμ hh
  exact ⟨a, ha, ht, H, hH, hm, hleft, hright,
    eq22_inverse_collar_displacement hμ hh hf ha ht hm hright⟩

end TakhtajanTeo
