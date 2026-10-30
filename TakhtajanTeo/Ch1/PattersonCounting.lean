import TakhtajanTeo.Ch1.PattersonScheffe
import TakhtajanTeo.Ch1.ResolventGammaSeparation
import Mathlib.Data.Set.Card

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem pat_cutoff_matrices_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    {g : SL2C | g ∈ Γ ∧ mob g w ∈ discExteriorR r}.Finite := by
  letI : DiscreteTopology Γ := hΓ.2
  let δ : ℝ := r ^ 2 - 1
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  let C := (√((‖w‖ ^ 2 - 1) / δ) +
    √((‖w‖ ^ 2 - 1) / δ + (‖w‖ ^ 2 - 1))) * (‖w‖ + 1) / (‖w‖ ^ 2 - 1)
  apply (fd_bounded_finite (Γ := Γ) C).subset
  rintro g ⟨hg, hcut⟩
  have hd : g 1 0 * w + g 1 1 ≠ 0 := by
    intro hz
    have he : mob g w = 0 := by simp [mob, hz]
    have hgt : 1 < ‖mob g w‖ := hcut.1
    norm_num [he] at hgt
  have hs : δ ≤ ‖mob g w‖ ^ 2 - 1 := by
    have hle : r ≤ ‖mob g w‖ := hcut.2
    dsimp [δ]
    nlinarith [norm_nonneg (mob g w)]
  exact ⟨hg, fd_entries_bound (hΓ.1 g hg) hw hδ hd hs⟩

theorem pat_cutoff_actions_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) |
      (a : ℂ → ℂ) w ∈ discExteriorR r}.Finite := by
  have hf := (pat_cutoff_matrices_finite hΓ hr hw).image (fun g => mob g)
  apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
  apply hf.subset
  rintro f ⟨a, ha, rfl⟩
  change (a : ℂ → ℂ) w ∈ discExteriorR r at ha
  obtain ⟨g, hg, he⟩ := a.property
  exact ⟨g, ⟨hg, by simpa only [he] using ha⟩, he⟩

/-- Counts distinct transformations, not SL2 matrices, so the central sign
does not spuriously double the lattice count. Finite-chart poles are excluded. -/
def patOrbitCount (Γ : Subgroup SL2C) (r : ℝ) (w : ℂ) : ℕ :=
  {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) |
    (a : ℂ → ℂ) w ∈ discExteriorR r}.ncard

theorem pat_indicator_sum_eq_count {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      (discExteriorR r).indicator (fun _ => (1 : ℝ≥0∞)) ((a : ℂ → ℂ) w)) =
      (patOrbitCount Γ r w : ℝ≥0∞) := by
  let S := {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) |
    (a : ℂ → ℂ) w ∈ discExteriorR r}
  have hf : S.Finite := pat_cutoff_actions_finite hΓ hr hw
  rw [tsum_eq_sum (s := hf.toFinset)]
  · have he : ∀ a ∈ hf.toFinset,
        (discExteriorR r).indicator (fun _ => (1 : ℝ≥0∞)) ((a : ℂ → ℂ) w) = 1 := by
      intro a ha
      have ha' : (a : ℂ → ℂ) w ∈ discExteriorR r := hf.mem_toFinset.mp ha
      exact indicator_of_mem ha' (fun _ : ℂ => (1 : ℝ≥0∞))
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [patOrbitCount, Set.ncard_eq_toFinset_card _ hf]
  · intro a ha
    have ha' : (a : ℂ → ℂ) w ∉ discExteriorR r :=
      fun he => ha (hf.mem_toFinset.mpr he)
    exact indicator_of_notMem ha' (fun _ : ℂ => (1 : ℝ≥0∞))

theorem pat_orbit_density_eq_count {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    patOrbitDensity Γ r w = ENNReal.ofReal (rho w) * (patOrbitCount Γ r w : ℝ≥0∞) := by
  unfold patOrbitDensity
  rw [ENNReal.tsum_mul_left, pat_indicator_sum_eq_count hΓ hr hw]

theorem pat_orbit_density_finite {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    patOrbitDensity Γ r w < ∞ := by
  rw [pat_orbit_density_eq_count hΓ hr hw]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

theorem pat_probability_real_eq_count {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (patProbabilityDensity Γ r w).toReal =
      rho w * (patOrbitCount Γ r w : ℝ) / (4 * π / (r ^ 2 - 1)) := by
  have hρ : 0 ≤ rho w := div_nonneg (by norm_num) (sq_nonneg _)
  have hA : 0 ≤ 4 * π / (r ^ 2 - 1) := le_of_lt
    (div_pos (mul_pos (by norm_num) Real.pi_pos) (by nlinarith))
  rw [patProbabilityDensity, pat_orbit_density_eq_count hΓ hr hw]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hρ,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_natCast]
  ring

theorem pat_orbit_count_antitone {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r s : ℝ} (hr : 1 < r) (hrs : r ≤ s) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    patOrbitCount Γ s w ≤ patOrbitCount Γ r w := by
  apply Set.ncard_le_ncard _ (pat_cutoff_actions_finite hΓ hr hw)
  intro a ha
  exact ⟨ha.1, hrs.trans ha.2⟩

theorem pat_mob_zero_iff_pole {g : SL2C} (hg : IsSU11 g) {w : ℂ}
    (hw : w ∈ unitDiscExterior) :
    mob g w = 0 ↔ g 1 0 * w + g 1 1 = 0 := by
  constructor
  · intro hz
    rcases (div_eq_zero_iff.mp hz) with hn | hd
    · have hi := fd_su11_identity hg w
      rw [hn] at hi
      have hw' : 1 < ‖w‖ := hw
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)] at hi
      nlinarith [sq_nonneg ‖g 1 0 * w + g 1 1‖]
    · exact hd
  · intro hd
    simp [mob, hd]

theorem pat_sphere_cutoff_iff {g : SL2C} (hg : IsSU11 g) {w : ℂ}
    (hw : w ∈ unitDiscExterior) (r : ℝ) :
    mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) (w : ExtPlane) ∈
      toExt (discExteriorR r) ∪ {extInf} ↔ mob g w = 0 ∨ mob g w ∈ discExteriorR r := by
  by_cases hd : g 1 0 * w + g 1 1 = 0
  · rw [mobiusExt_coe_of_eq_zero hd]
    simp [(pat_mob_zero_iff_pole hg hw).mpr hd]
  · rw [mobiusExt_coe hd]
    have hz : mob g w ≠ 0 := mt (pat_mob_zero_iff_pole hg hw).mp hd
    change ((mob g w : ℂ) : ExtPlane) ∈ toExt (discExteriorR r) ∪ {extInf} ↔ _
    simp [toExt, hz]

def patPoleCount (Γ : Subgroup SL2C) (w : ℂ) : ℕ :=
  {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) | (a : ℂ → ℂ) w = 0}.ncard

def patPoleCompletedCount (Γ : Subgroup SL2C) (r : ℝ) (w : ℂ) : ℕ :=
  ({a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) | (a : ℂ → ℂ) w = 0} ∪
    {a | (a : ℂ → ℂ) w ∈ discExteriorR r}).ncard

theorem pat_pole_completed_count_eq {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {r : ℝ} (hr : 1 < r) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    patPoleCompletedCount Γ r w = patPoleCount Γ w + patOrbitCount Γ r w := by
  apply Set.ncard_union_eq _ (gam_action_poles_finite hΓ hw) (pat_cutoff_actions_finite hΓ hr hw)
  rw [Set.disjoint_left]
  intro a ha hb
  change (a : ℂ → ℂ) w = 0 at ha
  have he : 1 < ‖(a : ℂ → ℂ) w‖ := hb.1
  norm_num [ha] at he

/-- The finitely many sphere-pole terms have vanishing normalized contribution.
This does not assume, or prove, the lattice-count asymptotic. -/
theorem pat_pole_normalized_limit (Γ : Subgroup SL2C) (w : ℂ) :
    Tendsto (fun r : ℝ => (patPoleCount Γ w : ℝ) / (4 * π / (r ^ 2 - 1)))
      (𝓝[>] 1) (𝓝 0) := by
  have hc : Continuous (fun r : ℝ => (patPoleCount Γ w : ℝ) * (r ^ 2 - 1) / (4 * π)) := by
    fun_prop
  have ht := (hc.continuousAt (x := 1)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  simpa only [div_div_eq_mul_div, one_pow, sub_self, mul_zero, zero_div] using ht

theorem pat_density_limit_of_counting_asymptotic {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hcount : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patOrbitCount Γ r w : ℝ) / (4 * π / (r ^ 2 - 1)))
        (𝓝[>] 1) (𝓝 ((hypArea Γ).toReal)⁻¹)) :
    ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patProbabilityDensity Γ r w).toReal) (𝓝[>] 1)
        (𝓝 (rho w / (hypArea Γ).toReal)) := by
  filter_upwards [hcount, ae_restrict_mem (fundDomain_measurable Γ)] with w hc hw
  have ht := hc.const_mul (rho w)
  have ht' : Tendsto (fun r : ℝ => rho w *
      ((patOrbitCount Γ r w : ℝ) / (4 * π / (r ^ 2 - 1)))) (𝓝[>] 1)
      (𝓝 (rho w / (hypArea Γ).toReal)) := by
    simpa only [div_eq_mul_inv] using ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa only [← mul_div_assoc] using
    (pat_probability_real_eq_count hΓ.1 hr (fundDomain_subset Γ hw)).symm

/-- Conditional transfer from the actual numeric orbit-count asymptotic.
The asymptotic is an explicit hypothesis, not an additional project axiom. -/
theorem pat_L1_of_counting_asymptotic {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hcount : ∀ᵐ w ∂volume.restrict (fundDomain Γ),
      Tendsto (fun r : ℝ => (patOrbitCount Γ r w : ℝ) / (4 * π / (r ^ 2 - 1)))
        (𝓝[>] 1) (𝓝 ((hypArea Γ).toReal)⁻¹)) :
    Tendsto (fun r : ℝ => ∫ w in fundDomain Γ,
      ‖(patProbabilityDensity Γ r w).toReal - rho w / (hypArea Γ).toReal‖)
      (𝓝[>] 1) (𝓝 0) :=
  pat_orbit_L1_of_ae_limit hΓ (pat_density_limit_of_counting_asymptotic hΓ hcount)

end TakhtajanTeo
