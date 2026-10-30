import TakhtajanTeo.Ch1.ResolventGamma

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem gam_orbit_numerator_pos {g : SL2C} (hg : IsSU11 g)
    {z w : ℂ} (hw : 1 < ‖w‖) (hne : mob g w ≠ z) :
    0 < ‖(g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have heq := sub_eq_zero.mp hzero
  by_cases hD : g 1 0 * w + g 1 1 = 0
  · have hid := fd_su11_identity hg w
    rw [hD, mul_zero] at heq
    rw [heq, hD] at hid
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add] at hid
    nlinarith
  · apply hne
    exact (div_eq_iff hD).mpr heq

private theorem gam_finite_positive_lower_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hpos : ∀ i ∈ s, 0 < f i) :
    ∃ δ > 0, ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (f a), lt_min hδ (hpos a (Finset.mem_insert_self a s)), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound i hi)

/-- Discreteness gives a uniform positive numerator separation from an orbit,
including group elements whose totalized Möbius map has a pole at `w`. -/
theorem gam_orbit_uniform_separation {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖)
    (hoff : ∀ g ∈ Γ, mob g w ≠ z) :
    ∃ δ > 0, ∀ g ∈ Γ,
      δ ≤ ‖(g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)‖ := by
  classical
  let f : SL2C → ℝ := fun g =>
    ‖(g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)‖
  have hfin := gam_sublevel_finite hΓ hz hw 1
  obtain ⟨δ, hδ, hbound⟩ := gam_finite_positive_lower_bound hfin.toFinset f (by
    intro g hg
    have hg' := hfin.mem_toFinset.mp hg
    exact gam_orbit_numerator_pos (hΓ.1 g hg'.1) hw (hoff g hg'.1))
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro g hg
  by_cases hsmall : f g ≤ 1
  · exact (min_le_left _ _).trans (hbound g (hfin.mem_toFinset.mpr ⟨hg, hsmall⟩))
  · exact (min_le_right _ _).trans (le_of_lt (lt_of_not_ge hsmall))

theorem gam_pointPair_orbit_numerator {g : SL2C} (hg : IsSU11 g)
    {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖)
    (hD : g 1 0 * w + g 1 1 ≠ 0) :
    pointPair z (mob g w) =
      ‖(g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)‖ ^ 2 /
        ((‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1)) := by
  have hn : ‖g 1 0 * w + g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hD
  have hzden : ‖z‖ ^ 2 - 1 ≠ 0 := by nlinarith
  have hwden : ‖w‖ ^ 2 - 1 ≠ 0 := by nlinarith
  have heq : z - mob g w =
      -((g 0 0 * w + g 0 1) - z * (g 1 0 * w + g 1 1)) /
        (g 1 0 * w + g 1 1) := by
    unfold mob
    apply (eq_div_iff hD).2
    rw [sub_mul, div_mul_cancel₀ _ hD]
    ring
  rw [gam_pp_eq, fd_mob_norm hg hw hD, heq, norm_div, norm_neg, div_pow]
  field_simp [hn, hzden, hwden]
  exact mul_div_cancel_right₀ _ (by simpa only [mul_comm w (g 1 0)] using hn)

theorem gam_pointPair_uniform_separation {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖)
    (hoff : ∀ g ∈ Γ, mob g w ≠ z) :
    ∃ δ > 0, ∀ g ∈ Γ, g 1 0 * w + g 1 1 ≠ 0 → δ ≤ pointPair z (mob g w) := by
  obtain ⟨ε, hε, hbound⟩ := gam_orbit_uniform_separation hΓ hz hw hoff
  have hden : 0 < (‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1) :=
    mul_pos (by nlinarith) (by nlinarith)
  refine ⟨ε ^ 2 / ((‖z‖ ^ 2 - 1) * (‖w‖ ^ 2 - 1)), div_pos (by positivity) hden, ?_⟩
  intro g hg hD
  rw [gam_pointPair_orbit_numerator (hΓ.1 g hg) hz hw hD]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hε.le (hbound g hg) 2) hden.le

/-- Only finitely many distinct group actions have a coordinate pole at a
fixed exterior point. They can be omitted in cofinite summability comparisons. -/
theorem gam_action_poles_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {w : ℂ} (hw : 1 < ‖w‖) :
    {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) | (a : ℂ → ℂ) w = 0}.Finite := by
  classical
  have hfinite := gam_sublevel_finite hΓ hw hw ‖w‖
  have hpoles : {g : Γ | g.val 1 0 * w + g.val 1 1 = 0}.Finite := by
    apply (hfinite.preimage (f := fun g : Γ => g.val)
      (fun _ _ _ _ heq => Subtype.ext heq)).subset
    intro g hg
    refine ⟨g.property, ?_⟩
    have hid := fd_su11_identity (hΓ.1 g.val g.property) w
    change g.val 1 0 * w + g.val 1 1 = 0 at hg
    rw [hg, mul_zero, sub_zero]
    rw [hg] at hid
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hid
    nlinarith [norm_nonneg (g.val 0 0 * w + g.val 0 1), norm_nonneg w]
  let act : Γ → (fun g : SL2C => mob g) '' (Γ : Set SL2C) :=
    fun g => ⟨mob g.val, g.val, g.property, rfl⟩
  apply (hpoles.image act).subset
  intro a ha
  obtain ⟨g, hg, heq⟩ := a.property
  change mob g = (a : ℂ → ℂ) at heq
  have hzero : mob g w = 0 := by rw [heq]; exact ha
  have hD : g 1 0 * w + g 1 1 = 0 := by
    rcases (div_eq_zero_iff.mp hzero) with hN | hD
    · have hid := fd_su11_identity (hΓ.1 g hg) w
      rw [hN] at hid
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hid
      nlinarith [sq_nonneg ‖g 1 0 * w + g 1 1‖]
    · exact hD
  exact ⟨⟨g, hg⟩, hD, Subtype.ext heq⟩

end TakhtajanTeo
