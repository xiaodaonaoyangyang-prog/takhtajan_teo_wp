import TakhtajanTeo.Ch1.Eq22PunctureTail

/-! Measurability and genuine local boundedness of the paired remainder at the
omitted target point. No boundedness of the inverse reflection is assumed. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem eq22_remainder_measurable {H q : ℂ → ℂ} {Ω : Set ℂ} {p z : ℂ}
    (hΩ : MeasurableSet Ω) (hH : ContinuousOn H (Ω \ {p})) (hq : ContinuousOn q Ω) :
    AEStronglyMeasurable (fun v => q v*(H v-v)^3/((H v-z)^3*(v-z)))
      (volume.restrict Ω) := by
  have he : volume.restrict (Ω \ {p}) = volume.restrict Ω :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton p))
  have hHm := hH.aestronglyMeasurable (μ := volume) (hΩ.diff (measurableSet_singleton p))
  rw [he] at hHm
  have hqm := hq.aestronglyMeasurable (μ := volume) hΩ
  exact ((hqm.aemeasurable.mul ((hHm.aemeasurable.sub measurable_id.aemeasurable).pow_const 3)).div
    (((hHm.aemeasurable.sub_const z).pow_const 3).mul (measurable_id.sub_const z).aemeasurable)).aestronglyMeasurable

-- L2
theorem eq22_remainder_locally_bounded {H q : ℂ → ℂ} {Ω E : Set ℂ} {p z : ℂ}
    (hΩ : IsOpen Ω) (hp : p ∈ Ω) (hpz : p ≠ z) (hq : ContinuousAt q p)
    (hH : MapsTo H (Ω \ {p}) E) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ u ∈ E, η ≤ ‖u-z‖) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ Ω ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ v ∈ ball p r, ‖q v*(H v-v)^3/((H v-z)^3*(v-z))‖ ≤ B := by
  let R : ℂ → ℂ := fun v => q v*(H v-v)^3/((H v-z)^3*(v-z))
  let d := ‖p-z‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hpz)
  obtain ⟨rΩ,hrΩ,hballΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  obtain ⟨rq,hrq,hballq⟩ := Metric.mem_nhds_iff.mp
    (hq.norm.eventually (gt_mem_nhds (lt_add_one ‖q p‖)))
  let r := min rΩ (min rq (d/2))
  have hr : 0 < r := lt_min hrΩ (lt_min hrq (half_pos hd))
  have hrΩ' : r ≤ rΩ := min_le_left _ _
  have hrq' : r ≤ rq := (min_le_right _ _).trans (min_le_left _ _)
  have hrd : r ≤ d/2 := (min_le_right _ _).trans (min_le_right _ _)
  let B₀ := (‖q p‖+1)*(1+(2*d)/η)^3/(d/2)
  refine ⟨r,hr,(ball_subset_ball hrΩ').trans hballΩ,max B₀ ‖R p‖,
    (norm_nonneg _).trans (le_max_right _ _),fun v hv => ?_⟩
  by_cases hvp : v = p
  · subst v
    exact le_max_right _ _
  · have hvr : ‖v-p‖ < r := by simpa only [mem_ball,dist_eq_norm] using hv
    have hqv : ‖q v‖ ≤ ‖q p‖+1 := (hballq (ball_subset_ball hrq' hv)).le
    have hupper : ‖v-z‖ ≤ 2*d := by
      have htri := norm_sub_le_norm_sub_add_norm_sub v p z
      change ‖v-z‖ ≤ ‖v-p‖+d at htri
      linarith
    have hlower : d/2 ≤ ‖v-z‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub p v z
      rw [norm_sub_rev p v] at htri
      change d ≤ ‖v-p‖+‖v-z‖ at htri
      linarith
    have hHv : H v ∈ E := hH ⟨hballΩ (ball_subset_ball hrΩ' hv),hvp⟩
    exact (eq22_remainder_uniform_bound (by positivity) (by positivity) hη (half_pos hd)
      hqv hupper (hsep (H v) hHv) hlower).trans (le_max_left _ _)

end TakhtajanTeo
