import TakhtajanTeo.Ch1.ResolventGammaMass

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real Matrix
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option autoImplicit false

private theorem gam_summable_reindex {ι : Type*} (e : ι ≃ ι) (f g : ι → ℝ)
    (h : ∀ i, f i = g (e i)) : Summable f ↔ Summable g := by
  have heq : f = g ∘ e := funext h
  rw [heq]
  exact e.summable_iff (f := g)

theorem gam_summable_symm {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) :
    Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) w)) ↔
    Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
      resolventKernel w ((a : ℂ → ℂ) z)) := by
  obtain ⟨e, he⟩ := gam_equiv_inv Γ
  apply gam_summable_reindex e
    (fun a => resolventKernel z ((a : ℂ → ℂ) w))
    (fun a => resolventKernel w ((a : ℂ → ℂ) z))
  intro a
  obtain ⟨g, hg, hga⟩ := a.property
  rw [he a g hg hga, ← hga]
  have hm := gam_master (hΓ.1 g hg) (hΓ.1 1 Γ.one_mem) (z := w) (w := z) hw hz
  rw [gam_mob_one, mul_one] at hm
  rw [(RK1 z (mob g w)).1, hm]

theorem gam_summable_left {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {g : SL2C} (hg : g ∈ Γ) {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) :
    Summable (fun a : (fun k : SL2C => mob k) '' (Γ : Set SL2C) =>
      resolventKernel (mob g z) ((a : ℂ → ℂ) w)) ↔
    Summable (fun a : (fun k : SL2C => mob k) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) w)) := by
  obtain ⟨e, he⟩ := gam_equiv_mul Γ (Γ.inv_mem hg)
  apply gam_summable_reindex e
    (fun a => resolventKernel (mob g z) ((a : ℂ → ℂ) w))
    (fun a => resolventKernel z ((a : ℂ → ℂ) w))
  intro a
  obtain ⟨k, hk, hka⟩ := a.property
  rw [he a k hk hka, ← hka]
  exact gam_master (hΓ.1 g hg) (hΓ.1 k hk) hz hw

theorem gam_summable_right {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {g : SL2C} (hg : g ∈ Γ) {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖)
    (hgw : 1 < ‖mob g w‖) :
    Summable (fun a : (fun k : SL2C => mob k) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) (mob g w))) ↔
    Summable (fun a : (fun k : SL2C => mob k) '' (Γ : Set SL2C) =>
      resolventKernel z ((a : ℂ → ℂ) w)) := by
  exact (gam_summable_symm hΓ hz hgw).trans
    ((gam_summable_left hΓ hg hw hz).trans (gam_summable_symm hΓ hw hz))

/-- The totalized finite Möbius coordinate preserves a.e. statements: its
single possible pole can be discarded as an area-null set. -/
theorem gam_mob_ae_pullback (g : SL2C) {P : ℂ → Prop}
    (hP : ∀ᵐ u : ℂ ∂volume, P u) : ∀ᵐ w : ℂ ∂volume, P (mob g w) := by
  let U : Set ℂ := {w | g 1 0 * w + g 1 1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  have hinj : InjOn (mob g) U := by
    intro x hx y hy heq
    rw [← (fd_inv_step g hx).2, ← (fd_inv_step g hy).2, heq]
  have hqc : IsKQC (mob g) U 1 := isKQC_one_of_conformal hU
    ⟨fun w hw => (fd_mob_differentiableAt g hw).differentiableWithinAt, hinj, rfl⟩
  have hpull : ∀ᵐ w ∂(volume.restrict U), P (mob g w) :=
    s23_c2_ae_pullback hqc (Set.subset_univ _) (by simpa using hP)
  have hmem : ∀ᵐ w : ℂ ∂volume, w ∈ U :=
    measure_eq_zero_iff_ae_notMem.mp ((fd_denom_finite g).measure_zero volume)
  filter_upwards [hmem, (ae_restrict_iff' hU.measurableSet).mp hpull] with w hw hp
  exact hp hw

/-- A.e. summability on a fundamental domain transports to the entire exterior.
Only countably many nonsingular pullbacks and the actual summability reindexing
are used; divergent real `tsum` values are never used to infer convergence. -/
theorem gam_series_summable_ae_exterior {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        resolventKernel z ((a : ℂ → ℂ) w)) := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable Γ := (fd_countable (Γ := Γ)).to_subtype
  have hF := isFundDomain_fundDomain hΓ
  have hgood : ∀ᵐ u : ℂ ∂volume, u ∈ fundDomain Γ →
      Summable (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        resolventKernel z ((a : ℂ → ℂ) u)) :=
    (ae_restrict_iff' hF.1).mp (gam_series_summable_ae_fundDomain hΓ hF hz)
  have heach : ∀ g : Γ, ∀ᵐ w : ℂ ∂volume, mob g.val w ∈ fundDomain Γ →
      Summable (fun a : (fun k : SL2C => mob k) '' (Γ : Set SL2C) =>
        resolventKernel z ((a : ℂ → ℂ) (mob g.val w))) :=
    fun g => gam_mob_ae_pullback g.val hgood
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  filter_upwards [hF.2.2.1, ae_restrict_of_ae (ae_all_iff.mpr heach),
    ae_restrict_mem hext] with w hcover hall hw
  obtain ⟨g, hg, hgw⟩ := hcover
  exact (gam_summable_right hΓ hg hz hw (hF.2.1 hgw)).mp (hall ⟨g, hg⟩ hgw)

end TakhtajanTeo
