import TakhtajanTeo.Ch1.FundDomainReflect

/-!
# Unfolding of Bochner integrals over a disk fundamental domain

* `fdD_hasSum_integral_unfold`: for integrable `h` on `𝔻`, `∫_𝔻 h = Σ_a ∫_F |a'|² h(a w)`.
* `fdD_sum_tile_kernel_mass_act`: `Σ_a ∬_F G(a z, w) ρ(w) = 1` (RK4 unfolded).
* `fdD_term_one`: `∬_𝔻 f(z) ∬_F G(z, w) ρ(w) = ∬_F f` for a `Γ`-invariant density `f` (identity term of (8.1)).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Bochner change of variables for the tile `{z ∈ 𝔻* | mob g z ∈ F}` of the action of `g`. -/
theorem fdD_tile_integral {F : Set ℂ} (hFm : MeasurableSet F) (hFe : F ⊆ unitDisc)
    (g : SL2C) (hg : IsSU11 g) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : ℂ → E) :
    ∫ z in {z : ℂ | ‖z‖ < 1 ∧ mob g z ∈ F}, ψ z =
      ∫ w in F, (‖deriv (mob g⁻¹) w‖ ^ 2) • ψ (mob g⁻¹ w) := by
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
  rw [← himg, fdq_mob_integral_image g⁻¹ hsm hgen ψ]
  refine setIntegral_congr_set ?_
  have hnull : volume {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} = 0 :=
    (fd_denom_finite g⁻¹).measure_zero volume
  have : ∀ᵐ w ∂volume, w ∉ {w : ℂ | (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 = 0} :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  refine eventuallyEqSet_iff.mpr ?_
  filter_upwards [this] with w hw
  have hw' : (g⁻¹ : SL2C) 1 0 * w + (g⁻¹ : SL2C) 1 1 ≠ 0 := hw
  exact ⟨fun h => h.1, fun h => ⟨h, hw'⟩⟩



/-- The tiles `{z ∈ 𝔻 | γ z ∈ F}` cover `𝔻` almost disjointly. -/
theorem fdD_restrict_eq_sum {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundDomainD Γ F) :
    volume.restrict unitDisc =
      Measure.sum (fun b : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        volume.restrict {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ F}) := by
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
  exact (Measure.restrict_congr_set hcover).trans
    (Measure.restrict_iUnion_ae hdisj (fun b => (hSm b).nullMeasurableSet))

/-- **Unfolding of Bochner integrals** over a disk fundamental domain. -/
theorem fdD_hasSum_integral_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundDomainD Γ F) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℂ → E}
    (hh : IntegrableOn h unitDisc) :
    HasSum (fun a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
      ∫ w in F, (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)) (∫ w in unitDisc, h w) := by
  classical
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
  have hsum := hasSum_integral_measure (μ := fun b : A =>
    volume.restrict {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ F}) (f := h)
    (by rw [← fdD_restrict_eq_sum hΓ hF]; exact hh)
  rw [← fdD_restrict_eq_sum hΓ hF] at hsum
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
  have hterm : ∀ b : A, (∫ z in {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ F}, h z) =
      ∫ w in F, (‖deriv ((ι b : A) : ℂ → ℂ) w‖ ^ 2) • h (((ι b : A) : ℂ → ℂ) w) := by
    intro b
    have hS : {z : ℂ | ‖z‖ < 1 ∧ (b : ℂ → ℂ) z ∈ F} = {z : ℂ | ‖z‖ < 1 ∧ mob (rep b) z ∈ F} := by
      ext z; simp only [mem_setOf_eq, (hrep b).2]
    rw [hS]
    exact fdD_tile_integral hF.1 hF.2.1 (rep b) (hΓ.1 _ (hrep b).1) h
  have hsum' : HasSum (fun b : A => ∫ w in F, (‖deriv ((ι b : A) : ℂ → ℂ) w‖ ^ 2) •
      h (((ι b : A) : ℂ → ℂ) w)) (∫ w in unitDisc, h w) := by
    convert hsum using 1
    funext b
    exact (hterm b).symm
  exact (e.hasSum_iff (f := fun a : A => ∫ w in F, (‖deriv (a : ℂ → ℂ) w‖ ^ 2) •
    h ((a : ℂ → ℂ) w))).mp hsum'


/-- `SU(1,1)` point-pair invariance on the disk, in the form `G(γz, w) = G(z, γ⁻¹w)`. -/
theorem fdD_kernel_act {g : SL2C} (hg : IsSU11 g) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    resolventKernel (mob g z) w = resolventKernel z (mob g⁻¹ w) := by
  have hw' : mob g⁻¹ w ∈ unitDisc :=
    mem_ball_zero_iff.mpr (fdD_mob_lt (isSU11_inv hg) (mem_ball_zero_iff.mp hw))
  have hback := (fd_inv_step g⁻¹ (fdD_denom_ne (isSU11_inv hg) (mem_ball_zero_iff.mp hw))).2
  rw [inv_inv] at hback
  calc resolventKernel (mob g z) w = resolventKernel (mob g z) (mob g (mob g⁻¹ w)) := by rw [hback]
    _ = resolventKernel z (mob g⁻¹ w) := (RK1 z (mob g⁻¹ w)).2 g hg (Or.inl ⟨hz, hw'⟩)

/-- The inversion permutation of the set of actions. -/
theorem fdD_inv_perm (Γ : Subgroup SL2C) :
    ∃ e : ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) ≃ ((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ∀ a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∃ g ∈ Γ, (a : ℂ → ℂ) = mob g ∧
        ((e a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) : ℂ → ℂ) = mob g⁻¹ := by
  classical
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
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
  exact ⟨hιι.toPerm, fun b => ⟨rep b, (hrep b).1, (hrep b).2.symm, rfl⟩⟩

/-- Total mass of the kernel over the tiles (disk version of `gam_sum_tile_kernel_mass`). -/
theorem fdD_sum_tile_kernel_mass {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundDomainD Γ F) {z : ℂ} (hz : z ∈ unitDisc) :
    (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∫⁻ w in F, ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w)) = 1 := by
  have hm : (∫⁻ w in unitDisc, ENNReal.ofReal (resolventKernel z w * rho w)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (resolvent_mass_integrable (Or.inl rfl) hz)
      (resolvent_mass_nonneg_ae (Or.inl rfl) hz), RK4 (Or.inl rfl) hz]
    simp
  rw [← hm, fdD_unfold hΓ hF]
  apply tsum_congr
  rintro ⟨_, g, hg, rfl⟩
  exact gam_tile_weighted_kernel (hΓ.1 g hg) F z

/-- The same with the action moved onto the first argument of the kernel. -/
theorem fdD_sum_tile_kernel_mass_act {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundDomainD Γ F) {z : ℂ} (hz : z ∈ unitDisc) :
    (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∫⁻ w in F, ENNReal.ofReal (resolventKernel ((a : ℂ → ℂ) z) w * rho w)) = 1 := by
  obtain ⟨e, he⟩ := fdD_inv_perm Γ
  rw [← fdD_sum_tile_kernel_mass hΓ hF hz]
  calc _ = ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ∫⁻ w in F, ENNReal.ofReal (resolventKernel z (((e a : (fun g : SL2C => mob g) '' (Γ : Set SL2C)) : ℂ → ℂ) w) * rho w) := by
        refine tsum_congr fun a => ?_
        obtain ⟨g, hg, ha, hea⟩ := he a
        refine setLIntegral_congr_fun hF.1 fun w hw => ?_
        rw [ha, hea]
        congr 2
        exact fdD_kernel_act (hΓ.1 g hg) hz (hF.2.1 hw)
    _ = _ := e.tsum_eq (fun b : (fun g : SL2C => mob g) '' (Γ : Set SL2C) =>
        ∫⁻ w in F, ENNReal.ofReal (resolventKernel z ((b : ℂ → ℂ) w) * rho w))

theorem fdD_action_mem {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ)
    (a : (fun g : SL2C => mob g) '' (Γ : Set SL2C)) {z : ℂ} (hz : z ∈ unitDisc) :
    (a : ℂ → ℂ) z ∈ unitDisc := by
  obtain ⟨_, g, hg, rfl⟩ := a
  exact mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1 g hg) (mem_ball_zero_iff.mp hz))

/-- **Term 1 of `identity_contribution`**: unfolding `∬_𝔻 f(z) ∬_F G(z,w) ρ(w)` for an invariant density `f`. -/
theorem fdD_term_one {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundDomainD Γ F)
    {f : ℂ → ℂ} (hfm : Measurable f)
    (hinv : ∀ g ∈ Γ, ∀ w ∈ unitDisc, f (mob g w) * ((‖deriv (mob g) w‖ ^ 2 : ℝ) : ℂ) = f w)
    (hfi : IntegrableOn f F) :
    IntegrableOn (fun z => f z * ((∫ w in F, resolventKernel z w * rho w : ℝ) : ℂ)) unitDisc ∧
      ∫ z in unitDisc, f z * ((∫ w in F, resolventKernel z w * rho w : ℝ) : ℂ) = ∫ z in F, f z := by
  classical
  set A := (fun g : SL2C => mob g) '' (Γ : Set SL2C) with hA
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable A := (fd_countable (Γ := Γ)).image _ |>.to_subtype
  set J : ℂ → ℝ := fun z => ∫ w in F, resolventKernel z w * rho w with hJ
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hJmeas : Measurable J := by
    have hm : Measurable (fun p : ℂ × ℂ => resolventKernel p.1 p.2 * rho p.2) :=
      measurable_resolventKernel.mul (gam_rho_measurable.comp measurable_snd)
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict F)).measurable
  have hJint : ∀ z ∈ unitDisc, IntegrableOn (fun w => resolventKernel z w * rho w) F := fun z hz =>
    (resolvent_mass_integrable (Or.inl rfl) hz).mono_set hF.2.1
  have hJae : ∀ z ∈ unitDisc, 0 ≤ᵐ[volume.restrict F] fun w => resolventKernel z w * rho w :=
    fun z hz => ae_restrict_of_ae_restrict_of_subset hF.2.1 (resolvent_mass_nonneg_ae (Or.inl rfl) hz)
  have hJnn : ∀ z ∈ unitDisc, 0 ≤ J z := fun z hz => integral_nonneg_of_ae (hJae z hz)
  have hJenn : ∀ z ∈ unitDisc, ENNReal.ofReal (J z) =
      ∫⁻ w in F, ENNReal.ofReal (resolventKernel z w * rho w) :=
    fun z hz => ofReal_integral_eq_lintegral_ofReal (hJint z hz) (hJae z hz)
  have hJsum : ∀ z ∈ unitDisc, ∑' a : A, ENNReal.ofReal (J ((a : ℂ → ℂ) z)) = 1 := by
    intro z hz
    rw [← fdD_sum_tile_kernel_mass_act hΓ hF hz]
    exact tsum_congr fun a => hJenn _ (fdD_action_mem hΓ a hz)
  have hJle : ∀ a : A, ∀ z ∈ unitDisc, J ((a : ℂ → ℂ) z) ≤ 1 := by
    intro a z hz
    have h1 : ENNReal.ofReal (J ((a : ℂ → ℂ) z)) ≤ 1 := by
      rw [← hJsum z hz]
      exact ENNReal.le_tsum (f := fun a : A => ENNReal.ofReal (J ((a : ℂ → ℂ) z))) a
    have := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rwa [ENNReal.toReal_ofReal (hJnn _ (fdD_action_mem hΓ a hz)), ENNReal.toReal_one] at this
  have hJreal : ∀ z ∈ unitDisc, HasSum (fun a : A => J ((a : ℂ → ℂ) z)) 1 := by
    intro z hz
    have hne : ∑' a : A, ENNReal.ofReal (J ((a : ℂ → ℂ) z)) ≠ ⊤ := by
      rw [hJsum z hz]; exact ENNReal.one_ne_top
    have hs : Summable (fun a : A => J ((a : ℂ → ℂ) z)) :=
      (ENNReal.summable_toReal hne).congr fun a =>
        ENNReal.toReal_ofReal (hJnn _ (fdD_action_mem hΓ a hz))
    have ht := ENNReal.tsum_toReal_eq (fun a : A => ENNReal.ofReal_ne_top (r := J ((a : ℂ → ℂ) z)))
    rw [hJsum z hz, ENNReal.toReal_one] at ht
    have ht' : ∑' a : A, J ((a : ℂ → ℂ) z) = 1 :=
      (tsum_congr fun a => (ENNReal.toReal_ofReal (hJnn _ (fdD_action_mem hΓ a hz))).symm).trans ht.symm
    rw [← ht']
    exact hs.hasSum
  have hJa_meas : ∀ a : A, Measurable (fun w => J ((a : ℂ → ℂ) w)) := fun a =>
    hJmeas.comp (gam_action_measurable Γ a)
  have hinvA : ∀ a : A, ∀ w ∈ unitDisc,
      f ((a : ℂ → ℂ) w) * ((‖deriv (a : ℂ → ℂ) w‖ ^ 2 : ℝ) : ℂ) = f w := by
    rintro ⟨_, g, hg, rfl⟩ w hw
    exact hinv g hg w hw
  set h : ℂ → ℂ := fun z => f z * (J z : ℂ) with hh
  have hhmeas : Measurable h := hfm.mul (Complex.measurable_ofReal.comp hJmeas)
  have hnorm : ∀ a : A, ∀ w ∈ F,
      ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ENNReal.ofReal ‖h ((a : ℂ → ℂ) w)‖ =
        ENNReal.ofReal ‖f w‖ * ENNReal.ofReal (J ((a : ℂ → ℂ) w)) := by
    intro a w hw
    have hwD := hF.2.1 hw
    have hJn := hJnn _ (fdD_action_mem hΓ a hwD)
    have hf := hinvA a w hwD
    have hfn : ‖f w‖ = ‖f ((a : ℂ → ℂ) w)‖ * ‖deriv (a : ℂ → ℂ) w‖ ^ 2 := by
      rw [← hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [hh, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJn]
    rw [hfn, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
    ring
  have hS : (∑' a : A, ∫⁻ w in F, ENNReal.ofReal ‖f w‖ * ENNReal.ofReal (J ((a : ℂ → ℂ) w))) =
      ∫⁻ w in F, ENNReal.ofReal ‖f w‖ := by
    calc _ = ∫⁻ w in F, ∑' a : A, ENNReal.ofReal ‖f w‖ * ENNReal.ofReal (J ((a : ℂ → ℂ) w)) :=
          (lintegral_tsum fun a => (hfm.norm.ennreal_ofReal.mul
            (hJa_meas a).ennreal_ofReal).aemeasurable).symm
      _ = _ := setLIntegral_congr_fun hF.1 fun w hw => by
          rw [ENNReal.tsum_mul_left, hJsum w (hF.2.1 hw), mul_one]
  have hfin : ∫⁻ w in F, ENNReal.ofReal ‖f w‖ < ⊤ := (hasFiniteIntegral_iff_norm _).mp hfi.2
  have hint : IntegrableOn h unitDisc := by
    refine ⟨hhmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hu := fdD_unfold hΓ hF (fun z => ENNReal.ofReal ‖h z‖)
    rw [hu]
    calc _ = ∑' a : A, ∫⁻ w in F, ENNReal.ofReal ‖f w‖ * ENNReal.ofReal (J ((a : ℂ → ℂ) w)) :=
          tsum_congr fun a => setLIntegral_congr_fun hF.1 (hnorm a)
      _ < ⊤ := by rw [hS]; exact hfin
  have hsum := fdD_hasSum_integral_unfold hΓ hF hint
  have hterm : ∀ a : A, (∫ w in F, (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)) =
      ∫ w in F, f w * (J ((a : ℂ → ℂ) w) : ℂ) := by
    intro a
    refine setIntegral_congr_fun hF.1 fun w hw => ?_
    have hf := hinvA a w (hF.2.1 hw)
    simp only [hh, Complex.real_smul]
    rw [← hf]
    ring
  have hsum' : HasSum (fun a : A => ∫ w in F, f w * (J ((a : ℂ → ℂ) w) : ℂ))
      (∫ w in unitDisc, h w) := by
    convert hsum using 1
    funext a
    exact (hterm a).symm
  have hFint : ∀ a : A, Integrable (fun w => f w * (J ((a : ℂ → ℂ) w) : ℂ)) (volume.restrict F) := by
    intro a
    have hb : ∀ᵐ w ∂(volume.restrict F), ‖(J ((a : ℂ → ℂ) w) : ℂ)‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem hF.1] with w hw
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJnn _ (fdD_action_mem hΓ a (hF.2.1 hw)))]
      exact hJle a w (hF.2.1 hw)
    exact Integrable.mul_bdd (c := 1) hfi
      (Complex.measurable_ofReal.comp (hJa_meas a)).aestronglyMeasurable hb
  have hFsum : Summable (fun a : A => ∫ w in F, ‖f w * (J ((a : ℂ → ℂ) w) : ℂ)‖) := by
    have hne : (∑' a : A, ∫⁻ w in F, ENNReal.ofReal ‖f w * (J ((a : ℂ → ℂ) w) : ℂ)‖) ≠ ⊤ := by
      have : (∑' a : A, ∫⁻ w in F, ENNReal.ofReal ‖f w * (J ((a : ℂ → ℂ) w) : ℂ)‖) =
          ∑' a : A, ∫⁻ w in F, ENNReal.ofReal ‖f w‖ * ENNReal.ofReal (J ((a : ℂ → ℂ) w)) := by
        refine tsum_congr fun a => setLIntegral_congr_fun hF.1 fun w hw => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hJnn _ (fdD_action_mem hΓ a (hF.2.1 hw))),
          ENNReal.ofReal_mul (norm_nonneg _)]
      rw [this, hS]
      exact hfin.ne
    have hs := ENNReal.summable_toReal hne
    refine hs.congr fun a => ?_
    rw [integral_norm_eq_lintegral_enorm (hFint a).aestronglyMeasurable]
    simp only [ofReal_norm_eq_enorm]
  have hsum2 := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hcongr : ∫ w in F, ∑' a : A, f w * (J ((a : ℂ → ℂ) w) : ℂ) = ∫ w in F, f w := by
    refine setIntegral_congr_fun hF.1 fun w hw => ?_
    rw [tsum_mul_left]
    have := (hJreal w (hF.2.1 hw)).tsum_eq
    rw [← Complex.ofReal_tsum, this]
    simp
  refine ⟨hint, ?_⟩
  have := hsum'.unique hsum2
  rw [this, hcongr]

end TakhtajanTeo
