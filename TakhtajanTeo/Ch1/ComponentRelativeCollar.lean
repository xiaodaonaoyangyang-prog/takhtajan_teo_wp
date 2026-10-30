import TakhtajanTeo.Ch1.ComponentRelativeBoundary
import TakhtajanTeo.Ch1.ComponentRelativeAmbient

/-! Actual exterior parameter collars for the reflected relative Schwarzian.
Only the existing reflection is used in the boundary geometry; no nonlinear
injectivity or quasiconformal gluing conclusion is asserted. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section

namespace TakhtajanTeo
open LiZhongQC

def crc_exteriorBoundary : Filter ℂ :=
  comap (fun w : ℂ => ‖w‖) (𝓝 1) ⊓ 𝓟 unitDiscExterior

-- L1
theorem crc_radial_le_nhds_circle :
    comap (fun w : ℂ => ‖w‖) (𝓝 1) ≤ 𝓝ˢ (sphere (0 : ℂ) 1) := by
  let L := comap (fun w : ℂ => ‖w‖) (𝓝 1)
  have hn : Tendsto (fun w : ℂ => ‖w‖) L (𝓝 1) := tendsto_comap
  have hm : closedBall (0 : ℂ) 2 ∈ L := by
    filter_upwards [hn (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with w hw
    exact mem_closedBall_zero_iff.mpr (le_of_lt hw)
  apply (isCompact_closedBall (0 : ℂ) 2).le_nhdsSet_of_clusterPt hm
  intro z _ hz
  let : NeBot (𝓝 z ⊓ L) := hz
  have he : ‖z‖ = 1 := tendsto_nhds_unique
    (continuous_norm.continuousAt.tendsto.mono_left (show 𝓝 z ⊓ L ≤ 𝓝 z from inf_le_left))
    (hn.mono_left inf_le_right)
  exact mem_sphere_zero_iff_norm.mpr he

-- L2
theorem crc_boundary_uniform {a : ℂ → ℝ}
    (ha : ∀ ζ : ℂ, ‖ζ‖ = 1 → Tendsto a (𝓝[unitDiscExterior] ζ) (𝓝 1)) :
    Tendsto a crc_exteriorBoundary (𝓝 1) := by
  intro s hs
  have hmem : a ⁻¹' s ∈ 𝓝ˢ (sphere (0 : ℂ) 1) ⊓ 𝓟 unitDiscExterior :=
    (isCompact_sphere (0 : ℂ) 1).mem_nhdsSet_inf_of_forall
      (fun ζ hζ => ha ζ (mem_sphere_zero_iff_norm.mp hζ) hs)
  exact (inf_le_inf crc_radial_le_nhds_circle le_rfl) hmem

-- L3
theorem crc_inverse_reflection_boundary {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Tendsto (fun w => ‖Function.invFunOn (fsans μ) unitDisc (h (gsans μ w))‖)
      (𝓝[unitDiscExterior] ζ) (𝓝 1) := by
  obtain ⟨eF, KF, hKF, heF⟩ := cra_welding_extension hμ
  obtain ⟨KG, hKG⟩ := normalizedWeldingExterior_quasiconformal hμ
  obtain ⟨eG, heG⟩ := t203_pack_homeo hKG (normalizedWeldingExterior_homeomorph hμ).2.2.1
  have hG : EqOn eG (gsans μ) unitDiscExterior := by
    intro w hw
    rw [heG, S2C.s2c_gsans_eq hμ]
    exact (gMu_eq_normalizedWeldingExterior hμ hw).symm
  have hEi : gsans μ '' unitDiscExterior = eG '' unitDiscExterior := hG.image_eq.symm
  obtain ⟨e, hfimg, hgimg⟩ := eq22_welding_common_chart hμ
  have hDc : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    simp [unitDiscExterior, mem_closedBall, not_le]
  have hfr : frontier (gsans μ '' unitDiscExterior) = frontier (fsans μ '' unitDisc) := by
    rw [hgimg, hfimg, ← e.image_frontier, ← e.image_frontier, hDc, frontier_compl,
      frontier_closedBall (0 : ℂ) one_ne_zero]
    simp only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero]
  have hζfr : ζ ∈ frontier unitDiscExterior := by
    rw [hDc, frontier_compl, frontier_closedBall (0 : ℂ) one_ne_zero]
    exact mem_sphere_zero_iff_norm.mpr hζ
  have hx : eG ζ ∈ frontier (fsans μ '' unitDisc) := by
    rw [← hfr, hEi, ← eG.image_frontier]
    exact ⟨ζ, hζfr, rfl⟩
  have hunit : ‖eF.symm (eG ζ)‖ = 1 := by
    have hi : eF '' unitDisc = fsans μ '' unitDisc := heF.image_eq
    rw [← hi, ← eF.image_frontier] at hx
    obtain ⟨v, hv, hvx⟩ := hx
    rw [← hvx, eF.symm_apply_apply]
    simpa only [unitDisc, frontier_ball (0 : ℂ) one_ne_zero, mem_sphere, dist_zero_right] using hv
  have hgs : Tendsto (gsans μ) (𝓝[unitDiscExterior] ζ) (𝓝 (eG ζ)) := by
    apply (eG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    exact eventually_nhdsWithin_of_forall (fun w hw => hG hw)
  have hgsE : Tendsto (gsans μ) (𝓝[unitDiscExterior] ζ)
      (𝓝[gsans μ '' unitDiscExterior] (eG ζ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hgs,
      eventually_nhdsWithin_of_forall (fun w hw => mem_image_of_mem (gsans μ) hw)⟩
  have ht := (eF.symm.continuous.continuousAt.tendsto.comp ((hh.2.2 _ hx).comp hgsE)).norm
  rw [hunit] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨v, hv, hvf⟩ := hh.2.1 (mem_image_of_mem (gsans μ) hw)
  dsimp only [Function.comp_def]
  rw [← hvf, (S2C.s2c_conf_f hμ).2.1.leftInvOn_invFunOn hv, ← heF hv, eF.symm_apply_apply]

-- L4
theorem crc_reflection_tendsto {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) :
    Tendsto (gsans μ) crc_exteriorBoundary (crb_reflectionBoundary μ h) := by
  have hw : ∀ᶠ w in crc_exteriorBoundary, w ∈ unitDiscExterior :=
    (eventually_principal.mpr (fun w hw => hw)).filter_mono inf_le_right
  apply tendsto_inf.mpr
  constructor
  · apply tendsto_comap_iff.mpr
    apply tendsto_inf.mpr
    constructor
    · apply tendsto_comap_iff.mpr
      exact crc_boundary_uniform (fun ζ hζ => crc_inverse_reflection_boundary hμ hh hζ)
    · apply tendsto_principal.mpr
      filter_upwards [hw] with w hw
      exact ((S2C.s2c_conf_f hμ).symm isOpen_ball).mapsTo
        (hh.2.1 (mem_image_of_mem (gsans μ) hw))
  · apply tendsto_principal.mpr
    filter_upwards [hw] with w hw
    exact mem_image_of_mem (gsans μ) hw

-- L5
theorem crc_eventually_collar {p : ℂ → Prop}
    (hp : ∀ᶠ w in crc_exteriorBoundary, p w) :
    ∃ R : ℝ, 1 < R ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < R → p w := by
  rw [crc_exteriorBoundary, eventually_inf_principal] at hp
  obtain ⟨s, hs, hsub⟩ := mem_comap.mp hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨1 + ε, by linarith, fun w hw1 hwR => ?_⟩
  apply hsub (hball ?_) hw1
  rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < ‖w‖ - 1)]
  linarith

-- L6
theorem crc_denominator_collar {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {q h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h)
    (ht : Tendsto (fun u => ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖)
      (crb_reflectionBoundary μ h) (𝓝 0))
    {k : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < R →
      let u := gsans μ w
      ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * k ∧
      ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ < k ∧
      1 - k ≤ ‖1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ ∧
      1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u ≠ 0 := by
  apply crc_eventually_collar
  exact (crc_reflection_tendsto hμ hh) (crb_denominator_eventually ht hk hk1)

-- L7
theorem crc_schwarzian_chosen_collar {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hν : ν ∈ LinfStarBall)
    (hP : AInf.toFun (bersPhi ν - bersPhi μ) ∈ A2fun unitDisc) :
    ∃ h : ℂ → ℂ,
      IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧
      ContDiffOn ℝ 1 h (gsans μ '' unitDiscExterior) ∧
      ∀ k : ℝ, 0 < k → k < 1 → ∃ R : ℝ, 1 < R ∧
        ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < R →
        let u := gsans μ w
        let q := schwarzianHol (crs_transition μ ν)
        ‖q (h u)‖ * ‖u - h u‖ ^ 2 * ‖fderiv ℝ h u‖ < 2 * k ∧
        ‖(u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ < k ∧
        1 - k ≤ ‖1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u‖ ∧
        1 + (u - h u) ^ 2 * (q (h u) / 2) * dz h u ≠ 0 := by
  obtain ⟨h, hh, hC1, ht, _⟩ := crb_schwarzian_chosen_reflection hμ hν hP
  exact ⟨h, hh, hC1, fun k hk hk1 => crc_denominator_collar hμ hh ht hk hk1⟩

end TakhtajanTeo
