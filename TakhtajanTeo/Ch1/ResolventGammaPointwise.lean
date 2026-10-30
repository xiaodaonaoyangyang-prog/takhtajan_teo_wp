import TakhtajanTeo.Ch1.ResolventGammaTransport
import TakhtajanTeo.Ch1.ResolventGammaSeparation

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

theorem gam_ae_good_first {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∀ᵐ v ∂(volume.restrict unitDiscExterior),
      (∀ g ∈ Γ, mob g w ≠ v) ∧
      Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        resolventKernel v ((a : ℂ → ℂ) w)) := by
  haveI : DiscreteTopology Γ := hΓ.2
  have hc : ((fun g : SL2C => mob g w) '' (Γ : Set SL2C)).Countable :=
    (fd_countable (Γ := Γ)).image _
  have havoid : ∀ᵐ v : ℂ ∂volume, v ∉ (fun g : SL2C => mob g w) '' (Γ : Set SL2C) :=
    measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero volume)
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [gam_series_summable_ae_exterior hΓ hw, ae_restrict_of_ae havoid,
    ae_restrict_mem hext] with v hsum hav hv
  exact ⟨fun g hg heq => hav ⟨g, hg, heq⟩, (gam_summable_symm hΓ hw hv).mp hsum⟩

theorem gam_exists_nearby_summable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v ∈ unitDiscExterior, pointPair z v < δ ∧ (∀ g ∈ Γ, mob g w ≠ v) ∧
      Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        resolventKernel v ((a : ℂ → ℂ) w)) := by
  have hz' : 1 < ‖z‖ := hz
  have hden : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
  have hcont : ContinuousAt (fun v : ℂ => pointPair z v) z :=
    (pointPair_continuousAt z z hden hden).comp₂
      (g := fun _ : ℂ => z) (h := fun v : ℂ => v) continuousAt_const continuousAt_id
  have hnear : {v : ℂ | v ∈ unitDiscExterior ∧ pointPair z v < δ} ∈ 𝓝 z := by
    have hsmall := hcont.eventually (Iio_mem_nhds (by simpa [pointPair] using hδ))
    exact inter_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz) hsmall
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hgood := ae_restrict_of_ae_restrict_of_subset
    (fun v (hv : v ∈ Metric.ball z r) => (hball hv).1) (gam_ae_good_first hΓ hw)
  obtain ⟨v, hv, hvgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume z hr).ne' hgood
  exact ⟨v, (hball hv).1, (hball hv).2, hvgood⟩

/-- Every off-orbit point has a summable automorphic kernel series. The
comparison is only required outside the finite set of coordinate poles. -/
theorem gam_series_summable {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior)
    (hoff : ∀ g ∈ Γ, mob g w ≠ z) :
    Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) w)) := by
  obtain ⟨δ, hδ, hsep⟩ := gam_pointPair_uniform_separation hΓ hz hw hoff
  obtain ⟨v, hv, hsmall, hvoff, hsum⟩ :=
    gam_exists_nearby_summable hΓ hz hw (lt_min zero_lt_one hδ)
  apply (hsum.norm.mul_left (64 : ℝ)).of_norm_bounded_eventually
  filter_upwards [(gam_action_poles_finite hΓ hw).eventually_cofinite_notMem] with a ha
  obtain ⟨g, hg, heq⟩ := a.property
  change mob g = (a : ℂ → ℂ) at heq
  have hzero : mob g w ≠ 0 := by rw [heq]; exact ha
  have hD : g 1 0 * w + g 1 1 ≠ 0 := by
    intro hD
    apply hzero
    simp [mob, hD]
  have hu : 1 < ‖mob g w‖ := fd_mob_exterior (hΓ.1 g hg) hw hD
  have hlocal : pointPair z v ≤ pointPair (mob g w) z := by
    rw [pointPair_symm (mob g w) z]
    exact (le_of_lt (lt_of_lt_of_le hsmall (min_le_right _ _))).trans (hsep g hg hD)
  have hcomp := gam_kernel_local_comparison hu hz hv (hoff g hg) (hvoff g hg)
    (le_of_lt (lt_of_lt_of_le hsmall (min_le_left _ _))) hlocal
  rw [(RK1 (mob g w) z).1, (RK1 (mob g w) v).1] at hcomp
  rw [← heq]
  rw [Real.norm_eq_abs, abs_of_pos (gam_K_pos hz (Or.inl hu) (hoff g hg))]
  exact hcomp.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))

theorem gam_kernel_strict_pos {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior)
    (hoff : ∀ g ∈ Γ, mob g w ≠ z) : 0 < resolventKernelGamma Γ z w := by
  have hs := gam_series_summable hΓ hz hw hoff
  have hnonneg : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      0 ≤ resolventKernel z ((a : ℂ → ℂ) w) := by
    rintro ⟨_, g, hg, rfl⟩
    apply (gam_K_pos hz _ (hoff g hg)).le
    by_cases hD : g 1 0 * w + g 1 1 = 0
    · exact Or.inr (by simp [mob, hD])
    · exact Or.inl (fd_mob_exterior (hΓ.1 g hg) hw hD)
  let a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) := ⟨mob 1, 1, Γ.one_mem, rfl⟩
  have hpos : 0 < resolventKernel z ((a : ℂ → ℂ) w) := by
    have hne := hoff 1 Γ.one_mem
    simp only [gam_mob_one] at hne
    change 0 < resolventKernel z (mob 1 w)
    rw [gam_mob_one]
    exact gam_K_pos hz (Or.inl hw) hne
  exact hs.tsum_pos hnonneg a hpos

end TakhtajanTeo
