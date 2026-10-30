import TakhtajanTeo.Ch1.S8_FiniteDimensional

/-!
# §8: the Petersson average and Lemma 8.2, conditional on Lemma 1.9 (`s8c_` prefix)

`petersson_average` and `lemma_8_2` (S8) are proved here from the conclusion of `lemma_1_9` (S1_3) for the given
group, taken as the hypothesis `hL`. Once `lemma_1_9` is proved, `hL := fun hm hb ha => lemma_1_9 hΓ hm hb ha`.
The transfer from the model `𝔻*` of Lemma 1.9 to the model `𝔻` of §8 uses the reflection `z ↦ 1/z̄`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **C1.** Change of variables for the reflection `z ↦ 1/z̄`, with the hyperbolic weight `ρ`. -/
theorem s8c_refl_setIntegral {S : Set ℂ} (hS : MeasurableSet S) (hS0 : ∀ z ∈ S, z ≠ 0) (f : ℂ → ℂ) :
    ∫ w in refl '' S, f w * rho w = ∫ z in S, f (refl z) * rho z := by
  have hf : refl = fun z : ℂ => conj (z⁻¹) := funext fun z => by simp [refl]
  obtain ⟨g, hg, hgd⟩ := fdr_exists_inv
  have hfun : mob g = fun z : ℂ => z⁻¹ := funext hg
  have hconj : ∀ (T : Set ℂ) (φ : ℂ → ℂ), ∫ w in conj '' T, φ w = ∫ y in T, φ (conj y) := by
    intro T φ
    have himg : conj '' T = (fun z : ℂ => conj z) ⁻¹' T :=
      congrFun (Set.image_eq_preimage_of_inverse (f := fun z : ℂ => conj z)
        Complex.conj_conj Complex.conj_conj) T
    rw [himg, ← gzE_conj_measurePreserving.setIntegral_preimage_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding (fun y => φ (conj y)) T]
    simp only [Complex.conj_conj]
  calc ∫ w in refl '' S, f w * rho w
      = ∫ w in conj '' ((fun z : ℂ => z⁻¹) '' S), f w * rho w := by rw [hf, Set.image_image]
    _ = ∫ y in (fun z : ℂ => z⁻¹) '' S, f (conj y) * rho (conj y) := hconj _ (fun w => f w * rho w)
    _ = ∫ z in S, f (refl z) * rho z := by
        rw [← hfun, fdq_mob_integral_image g hS (fun w hw => hgd w (hS0 w hw))]
        refine setIntegral_congr_fun hS fun z hz => ?_
        have hz0 := hS0 z hz
        have hJ := rho_inv_jacobian hz0
        rw [← hfun] at hJ
        have hρ : rho (conj (mob g z)) = rho z⁻¹ := by simp [rho, hfun]
        have hr : refl z = conj (mob g z) := by simp [refl, hfun]
        rw [hr, hρ, Complex.real_smul, ← hJ]
        push_cast
        ring

/-- **C2.** The exterior annulus `𝔻*_R` reflects onto the closed disk `𝔻_{1/R}` (up to the null set `{0}`). -/
theorem s8c_exterior_to_disc {R : ℝ} (hR : 1 < R) (f : ℂ → ℂ) :
    ∫ z in discExteriorR R, f (refl z) * rho z = ∫ z in closedDiscR R⁻¹, f z * rho z := by
  have hR0 : 0 < R := by linarith
  have hS : MeasurableSet (discExteriorR R) :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_const measurable_norm)
  have hS0 : ∀ z ∈ discExteriorR R, z ≠ 0 := fun z hz => fdr_ne_zero_of_exterior hz.1
  have hnr : ∀ z : ℂ, ‖refl z‖ = ‖z‖⁻¹ := fun z => by simp [refl]
  have himg : refl '' discExteriorR R = closedDiscR R⁻¹ \ {0} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz0 := hS0 z hz
      refine ⟨?_, ?_⟩
      · show refl z ∈ closedBall 0 R⁻¹
        rw [mem_closedBall_zero_iff, hnr]
        exact inv_anti₀ hR0 hz.2
      · simp [refl, hz0]
    · rintro ⟨hw, hw0⟩
      have hw0' : w ≠ 0 := hw0
      have hwR : ‖w‖ ≤ R⁻¹ := mem_closedBall_zero_iff.mp hw
      have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0'
      have hRw : R ≤ ‖w‖⁻¹ := by
        rw [le_inv_comm₀ hR0 hwpos]
        exact hwR
      refine ⟨refl w, ⟨?_, ?_⟩, refl_involutive w⟩
      · show 1 < ‖refl w‖
        rw [hnr]
        linarith
      · rw [hnr]
        exact hRw
  have hint := s8c_refl_setIntegral hS hS0 f
  rw [← hint, himg]
  exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))

/-- **C3.** For `f` invariant under the Fuchsian group `Γ` on `𝔻`, the quotient integral over `Γ\𝔻*` of `(f ∘ refl) ρ`
is the one over `Γ\𝔻` of `f ρ`, and the two hyperbolic areas agree. -/
theorem s8c_quotient_transfer {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {f : ℂ → ℂ}
    (hinv : ∀ g ∈ Γ, ∀ z ∈ unitDisc, f (mob g z) = f z) :
    quotientIntegral Γ (fun z => f (refl z) * rho z) = quotIntD Γ (fun z => f z * rho z) ∧
      (hypArea Γ).toReal = hypAreaD Γ := by
  have hex : ∃ F, IsFundDomain Γ F := ⟨_, fd_exists_isFundDomain hΓ⟩
  have hFD : IsFundDomain Γ (fundDomain Γ) := by
    unfold fundDomain
    rw [dif_pos hex]
    exact hex.choose_spec
  have hRF : IsFundDomainD Γ (refl '' fundDomain Γ) := fdr_isFundDomainD_refl hΓ hFD
  have hexD : ∃ F, IsFundDomainOn Γ unitDisc F := ⟨_, hRF⟩
  have hG : IsFundDomainD Γ (fundDomainOn Γ unitDisc) := by
    have h : IsFundDomainOn Γ unitDisc (fundDomainOn Γ unitDisc) := by
      unfold fundDomainOn
      rw [dif_pos hexD]
      exact hexD.choose_spec
    exact h
  have hS0 : ∀ z ∈ fundDomain Γ, z ≠ 0 := fun z hz => fdr_ne_zero_of_exterior (hFD.2.1 hz)
  refine ⟨?_, ?_⟩
  · have hinv' : ∀ g ∈ Γ, ∀ᵐ w ∂(volume.restrict unitDisc),
        (‖deriv (mob g) w‖ ^ 2) • (f (mob g w) * (rho (mob g w) : ℂ)) = f w * (rho w : ℂ) := by
      intro g hg
      refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).mpr
        (Eventually.of_forall fun w hw => ?_)
      have hsu := hΓ.1 g hg
      have hD := fdD_denom_ne hsu (mem_ball_zero_iff.mp hw)
      have hJ := gam_rho_mob_jacobian hsu hD
      rw [hinv g hg w hw, Complex.real_smul, ← hJ]
      push_cast
      ring
    unfold quotientIntegral quotIntD
    rw [← s8c_refl_setIntegral hFD.1 hS0 f]
    exact fdqD_integral_independent hΓ hRF hG _ hinv'
  · have h1 := fdr_lintegral_rho_refl hFD.1 hS0
    have h2 := fdD_lintegral_rho_independent hΓ hRF hG
    have hm : AEStronglyMeasurable (fun z : ℂ => rho z) (volume.restrict (fundDomainOn Γ unitDisc)) :=
      (by unfold rho; fun_prop : Measurable fun z : ℂ => rho z).aestronglyMeasurable
    unfold hypArea hypAreaD
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by unfold rho; positivity) hm,
      ← h2, h1]

/-- **C4.** `μ ν̄` is a `Γ`-invariant function on `𝔻` for `Γ`-invariant Beltrami differentials `μ, ν`. -/
theorem s8c_gammaInv_mul_conj {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ ν : ℂ → ℂ}
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∀ g ∈ Γ, ∀ z ∈ unitDisc, μ (mob g z) * conj (ν (mob g z)) = μ z * conj (ν z) := by
  intro g hg z hz
  have hsu := hΓ.1 g hg
  have hD := fdD_denom_ne hsu (mem_ball_zero_iff.mp hz)
  have hd : deriv (mob g) z ≠ 0 := by
    rw [(wp_mob_hasDerivAt g hD).deriv]
    exact one_div_ne_zero (pow_ne_zero 2 hD)
  have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
  have h1 := hμΓ g hg z hz
  have h2 := hνΓ g hg z hz
  rw [← h1, ← h2]
  simp only [map_mul, map_div₀, Complex.conj_conj]
  field_simp

/-- **C5.** `petersson_average`, conditional on the conclusion of `lemma_1_9` for `Γ`. Once `lemma_1_9` is proved, the
original closes by `s8c_petersson_average hΓ (fun hm hb ha => lemma_1_9 hΓ hm hb ha) hμ hν hμΓ hνΓ`
(and `lemma_8_2` likewise by `s8c_lemma_8_2`), i.e. `hL := fun hm hb ha => lemma_1_9 hΓ hm hb ha`. -/
theorem s8c_petersson_average {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hL : ∀ {h : ℂ → ℂ}, AEStronglyMeasurable h (volume.restrict unitDiscExterior) →
      (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C) →
      (∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z) →
      Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
          ∫ z in discExteriorR r, h z * rho z)
        (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)))
    {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (truncR r μ) (truncR r ν)) (𝓝[<] 1)
      (𝓝 (innerGamma Γ μ ν)) := by
  have hF : IsFuchsian Γ := hΓ.1
  set f : ℂ → ℂ := fun z => μ z * conj (ν z) with hf
  have hfinv : ∀ g ∈ Γ, ∀ z ∈ unitDisc, f (mob g z) = f z := s8c_gammaInv_mul_conj hF hμΓ hνΓ
  have hnr : ∀ z : ℂ, ‖refl z‖ = ‖z‖⁻¹ := fun z => by simp [refl]
  have hEm : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hmaps : MapsTo refl unitDiscExterior unitDisc := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    show refl z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hnr]
    exact inv_lt_one_of_one_lt₀ hz1
  have hfc : ContinuousOn f unitDisc :=
    (harmonicD_continuousOn hμ).mul (Complex.continuous_conj.comp_continuousOn (harmonicD_continuousOn hν))
  have hrc : ContinuousOn refl unitDiscExterior := by
    have : refl = fun z : ℂ => (conj z)⁻¹ := rfl
    rw [this]
    exact Complex.continuous_conj.continuousOn.inv₀ fun z hz =>
      (map_ne_zero _).mpr (fdr_ne_zero_of_exterior hz)
  have hmeas : AEStronglyMeasurable (fun z => f (refl z)) (volume.restrict unitDiscExterior) :=
    (hfc.comp hrc hmaps).aestronglyMeasurable hEm
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hbdd : ∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖f (refl z)‖ ≤ C := by
    refine ⟨Cμ * Cν, (ae_restrict_iff' hEm).mpr (Eventually.of_forall fun z hz => ?_)⟩
    have hw := hmaps hz
    show ‖μ (refl z) * conj (ν (refl z))‖ ≤ Cμ * Cν
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCμ _ hw) (hCν _ hw) (norm_nonneg _) ((norm_nonneg _).trans (hCμ _ hw))
  have haut : ∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), f (refl (mob g z)) = f (refl z) := by
    intro g hg
    refine (ae_restrict_iff' hEm).mpr (Eventually.of_forall fun z hz => ?_)
    rw [← fdr_mob_refl (hF.1 g hg) (fdr_ne_zero_of_exterior hz)]
    exact hfinv g hg _ (hmaps hz)
  have hT := hL hmeas hbdd haut
  obtain ⟨hQ, hA⟩ := s8c_quotient_transfer hF hfinv
  rw [hQ, hA] at hT
  have hinv : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun r : ℝ => r⁻¹) (𝓝 1) (𝓝 1⁻¹) := tendsto_inv₀ one_ne_zero
      rw [inv_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact (one_lt_inv₀ hr.1).mpr hr.2
  refine (hT.comp hinv).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hR : 1 < r⁻¹ := (one_lt_inv₀ hr.1).mpr hr.2
  have e1 := s8c_exterior_to_disc hR f
  have e2 := s8c_exterior_to_disc hR (fun _ => 1)
  rw [inv_inv] at e1 e2
  have e3 : l2InnerD (truncR r μ) (truncR r ν) = ∫ z in closedDiscR r, f z * rho z := by
    unfold l2InnerD
    rw [← inter_eq_right.mpr (closedDiscR_subset hr.2),
      ← setIntegral_indicator (show MeasurableSet (closedDiscR r) from measurableSet_closedBall)]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    by_cases hz : z ∈ closedDiscR r <;> simp [truncR, hz, f]
  simp only [Function.comp_apply, one_mul] at e2 ⊢
  rw [e1, e3]
  have e5 : ((∫ z in discExteriorR r⁻¹, rho z : ℝ) : ℂ) = (hypAreaDiscR r : ℂ) := by
    rw [← integral_complex_ofReal, e2, integral_complex_ofReal]
    rfl
  rw [e5]

/-- **C6.** Self-adjointness of `P` against `Ω^{-1,1}(𝔻)`: `∬ μ \overline{P(ν_r)} ρ = ∬ μ_r ν̄_r ρ`. -/
theorem s8c_inner_proj_trunc {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    l2InnerD μ (harmonicProjD (truncR r ν)) = l2InnerD (truncR r μ) (truncR r ν) := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hC0 : 0 ≤ Cμ := (norm_nonneg _).trans (hCμ 0 (by simp [unitDisc]))
  have hD0 : 0 ≤ Cν := (norm_nonneg _).trans (hCν 0 (by simp [unitDisc]))
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  let G : ℂ → ℂ → ℂ := fun z ζ => μ z * conj (truncR r ν ζ) * ((1 - z * conj ζ) ^ 4)⁻¹
  have hden : ∀ z ζ : ℂ, ‖z‖ < 1 → ‖ζ‖ ≤ r → (1 - r) ^ 4 ≤ ‖(1 - z * conj ζ) ^ 4‖ := by
    intro z ζ hz hζ
    have h1 : ‖z * conj ζ‖ ≤ r := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖z‖ * ‖ζ‖ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hz.le (norm_nonneg _)
        _ ≤ r := by linarith
    have h2 : 1 - r ≤ ‖1 - z * conj ζ‖ := by
      have := norm_sub_norm_le (1 : ℂ) (z * conj ζ)
      rw [norm_one] at this
      linarith
    rw [norm_pow]
    exact pow_le_pow_left₀ (by linarith) h2 4
  have hpos : 0 < (1 - r) ^ 4 := pow_pos (by linarith) 4
  set K : ℝ := Cμ * Cν / (1 - r) ^ 4 with hK
  have hbound : ∀ z ∈ unitDisc, ∀ ζ : ℂ, ‖G z ζ‖ ≤ K := by
    intro z hz ζ
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    by_cases hζ : ζ ∈ closedDiscR r
    · have hζ1 : ‖ζ‖ ≤ r := mem_closedBall_zero_iff.mp hζ
      have hζD : ζ ∈ unitDisc := closedDiscR_subset hr1 hζ
      have hd := hden z ζ hz1 hζ1
      simp only [G, truncR, indicator_of_mem hζ]
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_inv, ← div_eq_mul_inv, hK,
        div_le_div_iff₀ (lt_of_lt_of_le hpos hd) hpos]
      calc ‖μ z‖ * ‖ν ζ‖ * (1 - r) ^ 4 ≤ Cμ * Cν * (1 - r) ^ 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hCμ z hz) (hCν ζ hζD) (norm_nonneg _) hC0) hpos.le
        _ ≤ Cμ * Cν * ‖(1 - z * conj ζ) ^ 4‖ := mul_le_mul_of_nonneg_left hd (mul_nonneg hC0 hD0)
    · simp only [G, truncR, indicator_of_notMem hζ, map_zero, mul_zero, zero_mul, norm_zero]
      exact div_nonneg (mul_nonneg hC0 hD0) hpos.le
  have : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hμm : AEStronglyMeasurable μ (volume.restrict unitDisc) :=
    (harmonicD_continuousOn hμ).aestronglyMeasurable hDm
  have hνm : AEStronglyMeasurable (truncR r ν) (volume.restrict unitDisc) :=
    (truncR_aestronglyMeasurable hν hr1).mono_measure Measure.restrict_le_self
  have hGm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => μ p.1)
        ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
      hμm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => conj (truncR r ν p.2))
        ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable hνm).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
    have h3 : Measurable fun p : ℂ × ℂ => ((1 - p.1 * conj p.2) ^ 4)⁻¹ := by fun_prop
    exact (h1.mul h2).mul h3.aestronglyMeasurable
  have hGi : Integrable (Function.uncurry G) ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    refine Integrable.mono' (integrable_const K) hGm ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (hDm.prod hDm)).mpr (Eventually.of_forall fun p hp => ?_)
    exact hbound p.1 hp.1 p.2
  have hrep : ∀ z ∈ unitDisc, μ z * conj (harmonicProjD (truncR r ν) z) * (rho z : ℂ) =
      (12 / π : ℂ) * ∫ ζ in unitDisc, G z ζ := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hI : ∫ ζ in unitDisc, G z ζ =
        μ z * ∫ ζ in unitDisc, conj (truncR r ν ζ) / (1 - z * conj ζ) ^ 4 := by
      rw [← integral_const_mul]
      congr 1
      funext ζ
      simp only [G]
      ring
    have hρ : (rho z : ℂ) ≠ 0 := by
      have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact Complex.ofReal_ne_zero.mpr (by unfold rho; positivity)
    rw [hI, harmonicProjD_trunc_repr hz]
    simp only [map_mul, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
    field_simp
  have hin : ∀ ζ ∈ unitDisc, (12 / π : ℂ) * ∫ z in unitDisc, G z ζ =
      μ ζ * conj (truncR r ν ζ) * (rho ζ : ℂ) := by
    intro ζ hζ
    have hP := harmonicProjD_self hμ hζ
    unfold harmonicProjD at hP
    have hI : ∫ z in unitDisc, G z ζ =
        conj (truncR r ν ζ) * ∫ z in unitDisc, μ z / (1 - z * conj ζ) ^ 4 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      simp only [G]
      ring
    have hs : (1 : ℂ) - (‖ζ‖ : ℂ) ^ 2 ≠ 0 := by
      have : (1 : ℝ) - ‖ζ‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg ζ, mem_ball_zero_iff.mp hζ]
      exact_mod_cast this
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hI]
    rw [← hP]
    generalize (∫ z in unitDisc, μ z / (1 - z * conj ζ) ^ 4) = J
    simp only [rho]
    push_cast
    field_simp
    ring
  have hL : l2InnerD μ (harmonicProjD (truncR r ν)) =
      (12 / π : ℂ) * ∫ z in unitDisc, ∫ ζ in unitDisc, G z ζ := by
    unfold l2InnerD
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hDm hrep
  rw [hL, integral_integral_swap hGi, ← integral_const_mul]
  unfold l2InnerD
  refine setIntegral_congr_fun hDm fun ζ hζ => ?_
  rw [hin ζ hζ]
  by_cases h : ζ ∈ closedDiscR r <;> simp [truncR, h]

/-- **C7.** The inner limit of Lemma 8.2: `lim_{s → 1⁻} ∬ P(μ_s) \overline{P(ν_r)} ρ = ∬ μ_r ν̄_r ρ`. -/
theorem s8c_inner_limit {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    Tendsto (fun s : ℝ => l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν))) (𝓝[<] 1)
      (𝓝 (l2InnerD (truncR r μ) (truncR r ν))) := by
  rw [← s8c_inner_proj_trunc hμ hν hr0 hr1]
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  obtain ⟨-, C, hC⟩ := harmonicProjD_trunc_mem hν hr0 hr1
  have : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hm : AEStronglyMeasurable (fun z => harmonicProjD (truncR r ν) z * (rho z : ℂ))
      (volume.restrict unitDisc) :=
    ((harmonicProjD_trunc_continuousOn hν hr0 hr1).mul resolvent_rho_continuousOn).aestronglyMeasurable
      measurableSet_ball
  have hint : IntegrableOn (fun z => harmonicProjD (truncR r ν) z * rho z) unitDisc := by
    refine Integrable.mono' (integrable_const (4 * C)) hm
      ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_))
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hs : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hρ0 : 0 ≤ rho z := by unfold rho; positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    calc ‖harmonicProjD (truncR r ν) z‖ * rho z ≤ C * (1 - ‖z‖ ^ 2) ^ 2 * rho z :=
          mul_le_mul_of_nonneg_right (hC z hz) hρ0
      _ = 4 * C := by unfold rho; field_simp
  exact lemma_8_1_limit hμ
    ⟨_, fun z hz => harmonicProjD_norm_le (truncR_norm_le r hCν) (mem_ball_zero_iff.mp hz)⟩ hint

/-- **C8.** `lemma_8_2`, conditional on the conclusion of `lemma_1_9` for `Γ`. -/
theorem s8c_lemma_8_2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ)
    (hL : ∀ {h : ℂ → ℂ}, AEStronglyMeasurable h (volume.restrict unitDiscExterior) →
      (∃ C, ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖h z‖ ≤ C) →
      (∀ g ∈ Γ, ∀ᵐ z ∂(volume.restrict unitDiscExterior), h (mob g z) = h z) →
      Tendsto (fun r : ℝ => ((hypArea Γ).toReal / (∫ z in discExteriorR r, rho z) : ℂ) *
          ∫ z in discExteriorR r, h z * rho z)
        (𝓝[>] 1) (𝓝 (quotientIntegral Γ fun z => h z * rho z)))
    {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
        (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν)))
      (𝓝[<] 1) (𝓝 (innerGamma Γ μ ν)) := by
  have hP := s8c_petersson_average hΓ hL hμ hν hμΓ hνΓ
  refine hP.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact ((s8c_inner_limit hμ hν hr.1 hr.2).const_mul _).limUnder_eq.symm

end TakhtajanTeo
