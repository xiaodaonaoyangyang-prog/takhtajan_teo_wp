import TakhtajanTeo.Ch1.S1_3_Fuchsian

/-!
# Fundamental domains in the disk model

Disk-model mirror of the exterior unfolding and fundamental-domain comparison of `S1_3_Fuchsian`
(`fd_unfold`, `fdq_integral_independent`): the `SU(1,1)` action preserves `𝔻`, so the same tile
decomposition works with `‖z‖ < 1` in place of `1 < ‖z‖`. `IsFundDomainD Γ F` is `IsFundDomainOn Γ unitDisc F`
of `S8_FiniteDimensional` (which cannot be imported here).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- A measurable fundamental domain of `Γ` in the unit disk (the disk analogue of `IsFundDomain`). -/
def IsFundDomainD (Γ : Subgroup SL2C) (F : Set ℂ) : Prop :=
  MeasurableSet F ∧ F ⊆ unitDisc ∧ (∀ᵐ z ∂(volume.restrict unitDisc), ∃ g ∈ Γ, mob g z ∈ F) ∧
    ∀ g ∈ Γ, ∀ h ∈ Γ, mob g ≠ mob h → volume (mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ unitDisc) = 0

/-- `SU(1,1)` matrices have nonvanishing denominator on the disk. -/
theorem fdD_denom_ne {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : ‖z‖ < 1) :
    g 1 0 * z + g 1 1 ≠ 0 := by
  intro h0
  have h := fd_su11_identity hg z
  rw [h0, norm_zero] at h
  nlinarith [sq_nonneg ‖g 0 0 * z + g 0 1‖, norm_nonneg z]

/-- `SU(1,1)` preserves the disk. -/
theorem fdD_mob_lt {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz : ‖z‖ < 1) : ‖mob g z‖ < 1 := by
  have hD := fdD_denom_ne hg hz
  have h := fd_su11_identity hg z
  have hn : 0 < ‖g 1 0 * z + g 1 1‖ := norm_pos_iff.mpr hD
  unfold mob
  rw [norm_div, div_lt_one hn]
  by_contra hcon
  have h1 : ‖g 1 0 * z + g 1 1‖ ≤ ‖g 0 0 * z + g 0 1‖ := not_lt.mp hcon
  nlinarith [mul_self_le_mul_self hn.le h1, norm_nonneg z]

/-- Change of variables for the tile `{z ∈ 𝔻* | mob g z ∈ F}` of the action of `g`. -/
theorem fdD_tile_lintegral {F : Set ℂ} (hFm : MeasurableSet F) (hFe : F ⊆ unitDisc)
    (g : SL2C) (hg : IsSU11 g) (ψ : ℂ → ℝ≥0∞) :
    ∫⁻ z in {z : ℂ | ‖z‖ < 1 ∧ mob g z ∈ F}, ψ z =
      ∫⁻ w in F, ENNReal.ofReal (‖deriv (mob g⁻¹) w‖ ^ 2) * ψ (mob g⁻¹ w) := by
  set s : Set ℂ := F ∩ {w | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0} with hs
  have hsm : MeasurableSet s := hFm.inter (fd_measurableSet_gen g⁻¹)
  have hgen : ∀ w ∈ s, (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0 := fun w hw => hw.2
  have hleft : ∀ w ∈ s, mob g (mob g⁻¹ w) = w ∧ (g : SL2C) 1 0 * mob g⁻¹ w + g 1 1 ≠ 0 := by
    intro w hw
    have := fd_inv_step g⁻¹ (hgen w hw)
    rw [inv_inv] at this
    exact ⟨this.2, this.1⟩
  have hinj : InjOn (mob g⁻¹) s := fun w1 h1 w2 h2 h => by
    rw [← (hleft w1 h1).1, ← (hleft w2 h2).1, h]
  have himg : mob g⁻¹ '' s = {z : ℂ | ‖z‖ < 1 ∧ mob g z ∈ F} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hFe hw.1)
      refine ⟨?_, by rw [(hleft w hw).1]; exact hw.1⟩
      exact fdD_mob_lt (isSU11_inv hg) hw1
    · rintro ⟨hz, hzF⟩
      have hDg : g 1 0 * z + g 1 1 ≠ 0 := fdD_denom_ne hg hz
      obtain ⟨hDi, hback⟩ := fd_inv_step g hDg
      exact ⟨mob g z, ⟨hzF, hDi⟩, hback⟩
  rw [← himg, fd_lintegral_image g⁻¹ hsm hgen hinj ψ]
  refine setLIntegral_congr ?_
  have hnull : volume {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} = 0 :=
    (fd_denom_finite g⁻¹).measure_zero volume
  have : ∀ᵐ w ∂volume, w ∉ {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  refine eventuallyEqSet_iff.mpr ?_
  filter_upwards [this] with w hw
  have hw' : (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0 := hw
  exact ⟨fun h => h.1, fun h => ⟨h, hw'⟩⟩


/-- **Unfolding over a fundamental domain** (lower integrals): the integral over `𝔻*` is the sum over the
distinct actions `a ∈ Γ/±1` of the integrals over `F` of the pulled-back density. -/
theorem fdD_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundDomainD Γ F)
    (ψ : ℂ → ℝ≥0∞) :
    ∫⁻ w in unitDisc, ψ w =
      ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) := by
  classical
  haveI : DiscreteTopology Γ := hΓ.2
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hext : MeasurableSet unitDisc := measurableSet_ball
  let S : A → Set ℂ := fun b => {z | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ F}
  have hSm : ∀ b, MeasurableSet (S b) := by
    rintro ⟨_, g, hg, rfl⟩
    exact (measurableSet_lt measurable_norm measurable_const).inter ((fd_measurable_mob g) hF.1)
  have hcover : unitDisc =ᵐ[volume] ⋃ b, S b := by
    refine eventuallyEqSet_iff.mpr ?_
    filter_upwards [(ae_restrict_iff' hext).mp hF.2.2.1] with z hz
    constructor
    · intro hz1
      obtain ⟨g, hg, hF'⟩ := hz hz1
      exact mem_iUnion.mpr ⟨⟨mob g, g, hg, rfl⟩, mem_ball_zero_iff.mp hz1, hF'⟩
    · intro h
      obtain ⟨b, hb⟩ := mem_iUnion.mp h
      exact mem_ball_zero_iff.mpr hb.1
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) S) := by
    rintro ⟨_, g, hg, rfl⟩ ⟨_, h, hh, rfl⟩ hne
    have : mob g ≠ mob h := fun e => hne (Subtype.ext e)
    refine measure_mono_null (t := mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ unitDisc) ?_ (hF.2.2.2 g hg h hh this)
    intro z hz
    exact ⟨⟨hz.1.2, hz.2.2⟩, mem_ball_zero_iff.mpr hz.1.1⟩
  let rep : A → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : A, rep b ∈ Γ ∧ mob (rep b) = b.1 := fun b => Classical.choose_spec b.2
  let ι : A → A := fun b => ⟨mob (rep b)⁻¹, (rep b)⁻¹, Γ.inv_mem (hrep b).1, rfl⟩
  have hιι : Function.Involutive ι := by
    intro b
    apply Subtype.ext
    show mob (rep (ι b))⁻¹ = b.1
    have h1 : mob (rep b)⁻¹ = mob (rep (ι b)) := ((hrep (ι b)).2).symm
    rcases fd_mob_eq h1 with h | h
    · rw [h, inv_inv]; exact (hrep b).2
    · rw [h, fd_inv_neg, inv_inv, fd_mob_neg]; exact (hrep b).2
  let e : A ≃ A := hιι.toPerm
  calc ∫⁻ w in unitDisc, ψ w = ∫⁻ w in ⋃ b, S b, ψ w := setLIntegral_congr hcover
    _ = ∑' b, ∫⁻ w in S b, ψ w :=
        lintegral_iUnion₀ (fun b => (hSm b).nullMeasurableSet) hdisj ψ
    _ = ∑' b : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv ((ι b : A) : ℂ → ℂ) w‖ ^ 2) *
          ψ (((ι b : A) : ℂ → ℂ) w) := by
        refine tsum_congr fun b => ?_
        have hS : S b = {z : ℂ | ‖z‖ < 1 ∧ mob (rep b) z ∈ F} := by
          ext z; simp only [S, mem_setOf_eq, (hrep b).2]
        rw [hS]
        exact fdD_tile_lintegral hF.1 hF.2.1 (rep b) (hΓ.1 _ (hrep b).1) ψ
    _ = ∑' a : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) :=
        e.tsum_eq (fun a : A => ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w))


theorem fdqD_tile_image (g : SL2C) (hg : IsSU11 g) {F G : Set ℂ}
    (hF : F ⊆ unitDisc) (hG : G ⊆ unitDisc) :
    mob g '' (F ∩ mob g ⁻¹' G) = G ∩ mob g⁻¹ ⁻¹' F := by
  ext y
  constructor
  · rintro ⟨w, ⟨hwF, hwG⟩, rfl⟩
    have hback := (fd_inv_step g (fdD_denom_ne hg (mem_ball_zero_iff.mp (hF hwF)))).2
    exact ⟨hwG, by simpa only [mem_preimage, hback] using hwF⟩
  · rintro ⟨hyG, hyF⟩
    have hback := (fd_inv_step g⁻¹ (fdD_denom_ne (isSU11_inv hg) (mem_ball_zero_iff.mp (hG hyG)))).2
    rw [inv_inv] at hback
    exact ⟨mob g⁻¹ y, ⟨hyF, by simpa only [mem_preimage, hback] using hyG⟩, hback⟩


theorem fdqD_partition_cover {ι : Type*} {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFe : F ⊆ unitDisc) (hG : IsFundDomainD Γ G) (r : ι → SL2C)
    (hsurj : ∀ g ∈ Γ, ∃ i, mob (r i) = mob g) :
    F =ᵐ[volume] ⋃ i, F ∩ mob (r i) ⁻¹' G := by
  have hext : MeasurableSet unitDisc :=
    measurableSet_ball
  apply eventuallyEqSet_iff.mpr
  filter_upwards [(ae_restrict_iff' hext).mp hG.2.2.1] with w hw
  constructor
  · intro hwF
    obtain ⟨g, hg, hgw⟩ := hw (hFe hwF)
    obtain ⟨i, hi⟩ := hsurj g hg
    exact mem_iUnion.mpr ⟨i, hwF, by simpa only [mem_preimage, hi] using hgw⟩
  · intro hwU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hwU
    exact hi.1

theorem fdqD_partition_disjoint {ι : Type*} {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFe : F ⊆ unitDisc) (hG : IsFundDomainD Γ G) (r : ι → SL2C)
    (hr : ∀ i, r i ∈ Γ) (hinj : Function.Injective (fun i => mob (r i))) :
    Pairwise (Function.onFun (AEDisjoint volume) (fun i => F ∩ mob (r i) ⁻¹' G)) := by
  intro i j hij
  have hne : mob (r i) ≠ mob (r j) := fun heq => hij (hinj heq)
  apply measure_mono_null (t := mob (r i) ⁻¹' G ∩ mob (r j) ⁻¹' G ∩ unitDisc)
    _ (hG.2.2.2 (r i) (hr i) (r j) (hr j) hne)
  intro w hw
  exact ⟨⟨hw.1.2, hw.2.2⟩, hFe hw.1.1⟩

theorem fdqD_partition_measure {ι : Type*} [Countable ι] {Γ : Subgroup SL2C} {F G : Set ℂ}
    (hFm : MeasurableSet F) (hFe : F ⊆ unitDisc) (hG : IsFundDomainD Γ G)
    (r : ι → SL2C) (hr : ∀ i, r i ∈ Γ)
    (hsurj : ∀ g ∈ Γ, ∃ i, mob (r i) = mob g)
    (hinj : Function.Injective (fun i => mob (r i))) :
    volume.restrict F = Measure.sum (fun i => volume.restrict (F ∩ mob (r i) ⁻¹' G)) := by
  exact (Measure.restrict_congr_set (fdqD_partition_cover hFe hG r hsurj)).trans
    (Measure.restrict_iUnion_ae (fdqD_partition_disjoint hFe hG r hr hinj)
      (fun i => (hFm.inter ((fd_measurable_mob (r i)) hG.1)).nullMeasurableSet))

theorem fdqD_tile_compare {F G : Set ℂ}
    (hFm : MeasurableSet F) (hGm : MeasurableSet G)
    (hFe : F ⊆ unitDisc) (hGe : G ⊆ unitDisc)
    {g : SL2C} (hg : IsSU11 g) (f : ℂ → ℂ)
    (hinv : ∀ᵐ w ∂(volume.restrict unitDisc),
      (‖deriv (mob g) w‖ ^ 2) • f (mob g w) = f w) :
    (IntegrableOn f (G ∩ mob g⁻¹ ⁻¹' F) ↔ IntegrableOn f (F ∩ mob g ⁻¹' G)) ∧
    (∫ w in G ∩ mob g⁻¹ ⁻¹' F, f w) = (∫ w in F ∩ mob g ⁻¹' G, f w) ∧
    (∫ w in G ∩ mob g⁻¹ ⁻¹' F, ‖f w‖) = (∫ w in F ∩ mob g ⁻¹' G, ‖f w‖) := by
  have hs : MeasurableSet (F ∩ mob g ⁻¹' G) := hFm.inter ((fd_measurable_mob g) hGm)
  have hD : ∀ w ∈ F ∩ mob g ⁻¹' G, g 1 0 * w + g 1 1 ≠ 0 :=
    fun w hw => fdD_denom_ne hg (mem_ball_zero_iff.mp (hFe hw.1))
  have heq : (fun w => (‖deriv (mob g) w‖ ^ 2) • f (mob g w)) =ᵐ[
      volume.restrict (F ∩ mob g ⁻¹' G)] f :=
    ae_restrict_of_ae_restrict_of_subset (fun w hw => hFe hw.1) hinv
  have hnorm : (fun w => (‖deriv (mob g) w‖ ^ 2) • ‖f (mob g w)‖) =ᵐ[
      volume.restrict (F ∩ mob g ⁻¹' G)] (fun w => ‖f w‖) := by
    filter_upwards [heq] with w hw
    have hn := congrArg norm hw
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖deriv (mob g) w‖),
      smul_eq_mul] using hn
  rw [← fdqD_tile_image g hg hFe hGe]
  exact ⟨(fdq_mob_integrable_image g hs hD f).trans (integrableOn_congr_fun_ae heq),
    (fdq_mob_integral_image g hs hD f).trans (integral_congr_ae heq),
    (fdq_mob_integral_image g hs hD (fun w => ‖f w‖)).trans (integral_congr_ae hnorm)⟩

theorem fdqD_integral_independent {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    {F G : Set ℂ} (hF : IsFundDomainD Γ F) (hG : IsFundDomainD Γ G)
    (f : ℂ → ℂ)
    (hinv : ∀ g ∈ Γ, ∀ᵐ w ∂(volume.restrict unitDisc),
      (‖deriv (mob g) w‖ ^ 2) • f (mob g w) = f w) :
    (∫ w in F, f w) = ∫ w in G, f w := by
  classical
  haveI : DiscreteTopology Γ := hΓ.2
  let A := (fun g : SL2C => mob g) '' (Γ : Set SL2C)
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  let r : A → SL2C := fun a => Classical.choose a.property
  have hr : ∀ a : A, r a ∈ Γ ∧ mob (r a) = a.val :=
    fun a => Classical.choose_spec a.property
  have hi : Function.Injective (fun a : A => mob (r a)) := by
    intro a b hab
    apply Subtype.ext
    exact (hr a).2.symm.trans (hab.trans (hr b).2)
  have ho : ∀ g ∈ Γ, ∃ a : A, mob (r a) = mob g := by
    intro g hg
    exact ⟨⟨mob g, g, hg, rfl⟩, (hr ⟨mob g, g, hg, rfl⟩).2⟩
  have hii : Function.Injective (fun a : A => mob (r a)⁻¹) := by
    intro a b hab
    apply hi
    simpa only [inv_inv] using fdq_inv_action_congr hab
  have hoi : ∀ g ∈ Γ, ∃ a : A, mob (r a)⁻¹ = mob g := by
    intro g hg
    obtain ⟨a, ha⟩ := ho g⁻¹ (Γ.inv_mem hg)
    exact ⟨a, by simpa only [inv_inv] using fdq_inv_action_congr ha⟩
  have hμ := fdqD_partition_measure hF.1 hF.2.1 hG r (fun a => (hr a).1) ho hi
  have hν := fdqD_partition_measure hG.1 hG.2.1 hF
    (fun a : A => (r a)⁻¹) (fun a => Γ.inv_mem (hr a).1) hoi hii
  change (∫ w, f w ∂volume.restrict F) = ∫ w, f w ∂volume.restrict G
  rw [hμ, hν]
  apply fdq_integral_sum_compare _ _ f
  · intro a
    exact (fdqD_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 (hΓ.1 _ (hr a).1) f (hinv (r a) (hr a).1)).1.symm
  · intro a
    exact (fdqD_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 (hΓ.1 _ (hr a).1) f (hinv (r a) (hr a).1)).2.2.symm
  · intro a
    exact (fdqD_tile_compare hF.1 hG.1 hF.2.1 hG.2.1 (hΓ.1 _ (hr a).1) f (hinv (r a) (hr a).1)).2.1.symm

end TakhtajanTeo
