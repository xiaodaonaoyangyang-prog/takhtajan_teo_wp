import TakhtajanTeo.Ch1.FundDomainDisc
import TakhtajanTeo.Ch1.S1_4_ResolventCore
import TakhtajanTeo.Ch1.ResolventGammaMass

/-!
# Reflection transport of fundamental domains

The reflection `z ↦ 1/z̄` commutes with the `SU(1,1)` action and carries a fundamental domain of `Γ` in `𝔻*`
to one in `𝔻` (`fdr_isFundDomainD_refl`); it preserves hyperbolic area (`fdr_lintegral_rho_refl`), and the
hyperbolic area of a disk fundamental domain is independent of the domain (`fdD_lintegral_rho_independent`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem fdr_measurable_refl : Measurable refl :=
  measurable_inv.comp Complex.continuous_conj.measurable

/-- Reflection in the unit circle commutes with the `SU(1,1)` action (away from the origin). -/
theorem fdr_mob_refl {g : SL2C} (hg : IsSU11 g) {z : ℂ} (hz0 : z ≠ 0) :
    mob g (refl z) = refl (mob g z) := by
  obtain ⟨h1, h2⟩ := hg
  have hzc : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  have n1 : conj z * (g 0 0 * (conj z)⁻¹ + g 0 1) = g 0 0 + g 0 1 * conj z := by
    field_simp
  have n2 : conj z * (g 1 0 * (conj z)⁻¹ + g 1 1) = g 1 0 + g 1 1 * conj z := by
    field_simp
  have e1 : mob g (refl z) = (g 0 0 + g 0 1 * conj z) / (g 1 0 + g 1 1 * conj z) := by
    unfold mob refl
    rw [← mul_div_mul_left _ _ hzc, n1, n2]
  have e2 : refl (mob g z) = conj (g 1 0 * z + g 1 1) / conj (g 0 0 * z + g 0 1) := by
    unfold mob refl
    rw [map_div₀, inv_div]
  rw [e1, e2]
  simp only [map_add, map_mul, h1, h2, conj_conj]
  congr 1 <;> ring

theorem fdr_ne_zero_of_exterior {z : ℂ} (hz : z ∈ unitDiscExterior) : z ≠ 0 := by
  rintro rfl
  norm_num [unitDiscExterior] at hz

theorem fdr_ne_zero_of_disc_ne {z : ℂ} (hz : z ≠ 0) : (conj z)⁻¹ ≠ 0 :=
  inv_ne_zero ((map_ne_zero _).mpr hz)

/-- Reflection carries a fundamental domain in the exterior to one in the disk. -/
theorem fdr_isFundDomainD_refl {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundDomain Γ F) : IsFundDomainD Γ (refl '' F) := by
  have himg : refl '' F = refl ⁻¹' F :=
    congrFun (Set.image_eq_preimage_of_inverse refl_involutive refl_involutive) F
  have hext : MeasurableSet unitDiscExterior :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)
    filter_upwards [this] with z hz
    simpa using hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [himg]; exact fdr_measurable_refl hF.1
  · rintro _ ⟨w, hw, rfl⟩
    exact (refl_mem_disc_iff (fdr_ne_zero_of_exterior (hF.2.1 hw))).mpr (hF.2.1 hw)
  · have hcov := (ae_restrict_iff' hext).mp hF.2.2.1
    have hDm : MeasurableSet unitDisc := measurableSet_ball
    rw [ae_restrict_iff' hDm]
    filter_upwards [ae_refl hcov, h0] with z hz hz0 hzD
    have hzE : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).mpr hzD
    obtain ⟨g, hg, hgF⟩ := hz hzE
    refine ⟨g, hg, ?_⟩
    have hrz : refl z ≠ 0 := fdr_ne_zero_of_disc_ne hz0
    have := fdr_mob_refl (hΓ.1 g hg) hrz
    rw [refl_involutive z] at this
    rw [himg, mem_preimage, this, refl_involutive]
    exact hgF
  · intro g hg h hh hne
    have hN := hF.2.2.2 g hg h hh hne
    have hae : ∀ᵐ w : ℂ, w ∉ mob g ⁻¹' F ∩ mob h ⁻¹' F ∩ unitDiscExterior :=
      measure_eq_zero_iff_ae_notMem.mp hN
    have hae' := ae_refl hae
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae', h0] with z hz hz0 hzS
    apply hz
    obtain ⟨⟨hg1, hh1⟩, hzD⟩ := hzS
    rw [himg] at hg1 hh1
    refine ⟨⟨?_, ?_⟩, (refl_mem_exterior_iff hz0).mpr hzD⟩
    · have := fdr_mob_refl (hΓ.1 g hg) hz0
      rw [mem_preimage, this]; exact hg1
    · have := fdr_mob_refl (hΓ.1 h hh) hz0
      rw [mem_preimage, this]; exact hh1


/-- Inversion is the Möbius map of an `SL(2, ℂ)` matrix with nonvanishing denominator off the origin. -/
theorem fdr_exists_inv : ∃ g : SL2C, (∀ z, mob g z = z⁻¹) ∧ ∀ w : ℂ, w ≠ 0 → g 1 0 * w + g 1 1 ≠ 0 := by
  refine ⟨⟨!![0, I; I, 0], by simp [Matrix.det_fin_two]⟩, ?_, ?_⟩
  · intro z
    by_cases hz : z = 0
    · simp [mob, hz]
    · simp [mob]
      field_simp
  · intro w hw
    simp [hw]

/-- Change of variables for inversion (lower integrals). -/
theorem fdr_lintegral_inv {S : Set ℂ} (hS : MeasurableSet S) (hS0 : ∀ z ∈ S, z ≠ 0) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in (fun z : ℂ => z⁻¹) '' S, φ w =
      ∫⁻ z in S, ENNReal.ofReal (‖deriv (fun z : ℂ => z⁻¹) z‖ ^ 2) * φ z⁻¹ := by
  obtain ⟨g, hg, hgd⟩ := fdr_exists_inv
  have hfun : mob g = fun z : ℂ => z⁻¹ := funext hg
  have hinj : InjOn (mob g) S := by
    intro x _ y _ h
    simpa [hfun] using h
  have h := fd_lintegral_image g hS (fun w hw => hgd w (hS0 w hw)) hinj φ
  rw [hfun] at h
  simpa using h

/-- Change of variables for complex conjugation. -/
theorem fdr_lintegral_conj {T : Set ℂ} (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in conj '' T, φ w = ∫⁻ y in T, φ (conj y) := by
  have himg : conj '' T = (fun z : ℂ => conj z) ⁻¹' T :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun z : ℂ => conj z)
      Complex.conj_conj Complex.conj_conj) T
  rw [himg, ← gzE_conj_measurePreserving.setLIntegral_comp_preimage_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding (fun y => φ (conj y)) T]
  simp only [Complex.conj_conj]

/-- Change of variables for the reflection `z ↦ 1/z̄` (lower integrals). -/
theorem fdr_lintegral_refl {S : Set ℂ} (hS : MeasurableSet S) (hS0 : ∀ z ∈ S, z ≠ 0) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in refl '' S, φ w =
      ∫⁻ z in S, ENNReal.ofReal (‖deriv (fun z : ℂ => z⁻¹) z‖ ^ 2) * φ (refl z) := by
  have hf : refl = fun z : ℂ => conj (z⁻¹) := funext fun z => by simp [refl]
  calc ∫⁻ w in refl '' S, φ w
      = ∫⁻ w in conj '' ((fun z : ℂ => z⁻¹) '' S), φ w := by rw [hf, Set.image_image]
    _ = ∫⁻ y in (fun z : ℂ => z⁻¹) '' S, φ (conj y) := fdr_lintegral_conj φ
    _ = _ := by
      rw [fdr_lintegral_inv hS hS0 (fun y => φ (conj y))]
      simp only [hf]

/-- Reflection preserves the hyperbolic area of subsets of the punctured exterior or disk. -/
theorem fdr_lintegral_rho_refl {S : Set ℂ} (hS : MeasurableSet S) (hS0 : ∀ z ∈ S, z ≠ 0) :
    ∫⁻ w in refl '' S, ENNReal.ofReal (rho w) = ∫⁻ z in S, ENNReal.ofReal (rho z) := by
  rw [fdr_lintegral_refl hS hS0]
  refine setLIntegral_congr_fun hS fun z hz => ?_
  have hρ : rho (refl z) = rho z⁻¹ := by simp [rho, refl]
  rw [hρ, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm, rho_inv_jacobian (hS0 z hz)]

/-- The hyperbolic area of a disk fundamental domain does not depend on the domain. -/
theorem fdD_lintegral_rho_independent {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F G : Set ℂ}
    (hF : IsFundDomainD Γ F) (hG : IsFundDomainD Γ G) :
    ∫⁻ z in F, ENNReal.ofReal (rho z) = ∫⁻ z in G, ENNReal.ofReal (rho z) := by
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
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  let ψ : ℂ → ℝ≥0∞ := G.indicator fun z => ENNReal.ofReal (rho z)
  have hU := fdD_unfold hΓ hF ψ
  have hL : ∫⁻ w in unitDisc, ψ w = ∫⁻ z in G, ENNReal.ofReal (rho z) := by
    rw [lintegral_indicator hG.1, Measure.restrict_restrict hG.1, inter_eq_left.mpr hG.2.1]
  have hterm : ∀ a : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) =
      ∫⁻ w in F ∩ (a : ℂ → ℂ) ⁻¹' G, ENNReal.ofReal (rho w) := by
    rintro ⟨_, g, hg, rfl⟩
    have hgm : MeasurableSet (mob g ⁻¹' G) := (fd_measurable_mob g) hG.1
    have hpt : ∀ w ∈ F, ENNReal.ofReal (‖deriv (mob g) w‖ ^ 2) * ψ (mob g w) =
        (mob g ⁻¹' G).indicator (fun w => ENNReal.ofReal (rho w)) w := by
      intro w hw
      have hD := fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp (hF.2.1 hw))
      by_cases hwG : mob g w ∈ G
      · have hwG' : w ∈ mob g ⁻¹' G := hwG
        simp only [ψ, indicator_of_mem hwG, indicator_of_mem hwG']
        rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm, gam_rho_mob_jacobian (hΓ.1 g hg) hD]
      · have hwG' : w ∉ mob g ⁻¹' G := hwG
        simp only [ψ, indicator_of_notMem hwG, indicator_of_notMem hwG', mul_zero]
    rw [setLIntegral_congr_fun hF.1 hpt, lintegral_indicator hgm, Measure.restrict_restrict hgm,
      inter_comm]
  have hμ := fdqD_partition_measure hF.1 hF.2.1 hG r (fun a => (hr a).1) ho hi
  calc ∫⁻ z in F, ENNReal.ofReal (rho z)
      = ∫⁻ z, ENNReal.ofReal (rho z) ∂(Measure.sum
          (fun i : A => volume.restrict (F ∩ mob (r i) ⁻¹' G))) := by rw [← hμ]
    _ = ∑' a : A, ∫⁻ z in F ∩ mob (r a) ⁻¹' G, ENNReal.ofReal (rho z) := lintegral_sum_measure _ _
    _ = ∑' a : A, ∫⁻ z in F ∩ (a : ℂ → ℂ) ⁻¹' G, ENNReal.ofReal (rho z) := by
        refine tsum_congr fun a => ?_
        rw [(hr a).2]
    _ = ∑' a : A, ∫⁻ w in F, ENNReal.ofReal (‖deriv (a : ℂ → ℂ) w‖ ^ 2) * ψ ((a : ℂ → ℂ) w) :=
        tsum_congr fun a => (hterm a).symm
    _ = ∫⁻ w in unitDisc, ψ w := hU.symm
    _ = _ := hL

end TakhtajanTeo
