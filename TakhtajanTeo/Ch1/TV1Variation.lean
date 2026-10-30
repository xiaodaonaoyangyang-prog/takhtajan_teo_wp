import TakhtajanTeo.Ch1.Lemma15
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.BeltramiCompose

/-!
# TV1: Model-A first variation and the pullback of harmonic Beltrami differentials  [下属2]

* `tv_local_bound`, `tv_local_bound_gen`: `‖F x - x‖ ≤ C ε ‖x‖^α` near `0` for normalized solutions of coefficients of
  norm `≤ ε` (hydrodynamic solution `f = z + cauchyT ω`, Hölder bound of the Cauchy transform).
* `tv_wAS_first_order`: `(wAS (tμ))⁻¹(0) = t s + o(t)`.
* `tv_wB_form`, `tv_gamma_first_order`, `tv_W_diff`, `tv_Wp_diff`, `tv1_a_diff`: `t ↦ w^{tμ}(z)` is differentiable at `0`.
* `tv_pullback_harmonic`, `tv1_sigma_inv`: `(σ_z⁻¹)^* μ` is harmonic (for `σ_z⁻¹` a Möbius map of `𝔻*` with a pole `a`).

All helpers are public theorems prefixed `tv_` / `tv1_`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem tv_hydroR {nu : ℂ → ℂ} {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hnu : IsBeltramiCoeff nu univ k) {R : ℝ} (hR : 0 < R) (hsupp : ∀ w : ℂ, R < ‖w‖ → nu w = 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => nu z * hilbertH ω z + nu z) :
    IsKQC (fun z => z + cauchyT ω z) univ ((1 + k) / (1 - k)) ∧
      (fun z => z + cauchyT ω z) '' univ = univ ∧
      (∀ᵐ z, complexDilatation (fun z => z + cauchyT ω z) z = nu z) := by
  have hμ : IsCompactBeltramiCoeff nu k := ⟨hnu, R, hsupp⟩
  obtain ⟨hkqc, e', he'⟩ := thm12_1_isKQC hk0 hk1 hμ hp hkp hω hsol
  have himg : (fun z => z + cauchyT ω z) '' univ = univ := by
    rw [← he', Set.image_univ]; exact e'.surjective.range_eq
  refine ⟨hkqc, himg, ?_⟩
  have hgen : IsGenHomeoSolution (fun z => z + cauchyT ω z) nu univ (ENNReal.ofReal p) := by
    refine ⟨hkqc.2.2.1, ?_⟩
    obtain ⟨R', hR', hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → nu z = 0 :=
      ⟨R, hR, hsupp⟩
    set omR : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator ω with homRdef
    have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hRR' hsol
    have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
    have hHT : hilbertH ω = hilbertH omR := hilbertH_congr_ae homs
    have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
    have homRbdd : Bornology.IsBounded (Function.support omR) := t3_isBounded_support_indicator
    obtain ⟨hgp, heqbar, heqz⟩ := thm11_1 hp homRmem homRbdd
    have hgp' := t3_hasGenPartials_add_id hgp
    have hpteq : ∀ z : ℂ, genDzbar (fun z => 1 + (hilbertH omR z + omR z))
        (fun z => I + I * (hilbertH omR z - omR z)) z = omR z := by
      intro z
      have h1 := heqbar z
      rw [genDzbar] at h1 ⊢
      linear_combination h1 + (1 / 2 : ℂ) * I_sq
    have hpteq2 : ∀ z : ℂ, genDz (fun z => 1 + (hilbertH omR z + omR z))
        (fun z => I + I * (hilbertH omR z - omR z)) z = 1 + hilbertH omR z := by
      intro z
      have h2 := heqz z
      rw [genDz] at h2 ⊢
      linear_combination h2 - (1 / 2 : ℂ) * I_sq
    refine ⟨fun z => 1 + (hilbertH omR z + omR z), fun z => I + I * (hilbertH omR z - omR z),
      ?_, ?_⟩
    · rw [show (fun z => z + cauchyT ω z) = (fun z => z + cauchyT omR z) from
        by funext z; rw [hcT]]
      exact hgp'
    · rw [Measure.restrict_univ]
      filter_upwards [hsol, homs] with z hsolz hz
      rw [hpteq z, hpteq2 z, ← hz, hsolz, congrFun hHT z]
      ring
  exact t2_complexDilatation_ae hkqc hp hgen

theorem tv_GformulaR {nu : ℂ → ℂ} {k p : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hnu : IsBeltramiCoeff nu univ k) {R : ℝ} (hR : 0 < R) (hsupp : ∀ w : ℂ, R < ‖w‖ → nu w = 0)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => nu z * hilbertH ω z + nu z)
    {G : ℂ → ℂ} (hG : IsNormalizedSolution G nu) :
    ∃ D : ℂ, D ≠ 0 ∧ ∀ z : ℂ, G z = D⁻¹ * (z + cauchyT ω z - cauchyT ω 0) := by
  obtain ⟨hKqc, himg, hdil⟩ := tv_hydroR hk0 hk1 hp hkp hnu hR hsupp hω hsol
  set r : ℂ → ℂ := cauchyT ω with hr
  set f : ℂ → ℂ := fun z => z + r z with hf
  have hinj : InjOn f univ := hKqc.2.2.1.2.1
  have hD : f 1 - f 0 ≠ 0 := fun h => one_ne_zero (hinj (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  set D := f 1 - f 0 with hDdef
  have hDi : D⁻¹ ≠ 0 := inv_ne_zero hD
  obtain ⟨hq, hsurj⟩ := b4_rat_affine_comp hKqc himg (α := 1) (γ := D⁻¹) 0 (-(D⁻¹ * f 0)) one_ne_zero hDi
  have hfun : (fun z => D⁻¹ * f (1 * z + 0) + -(D⁻¹ * f 0)) = fun z => D⁻¹ * (f z - f 0) := by
    funext z; simp; ring
  rw [hfun] at hq hsurj
  have hdiffae : ∀ᵐ z ∂(volume.restrict (univ : Set ℂ)), DifferentiableAt ℝ f z := thm9_3_differentiable_ae hKqc
  rw [Measure.restrict_univ] at hdiffae
  have hH : IsNormalizedSolution (fun z => D⁻¹ * (f z - f 0)) nu := by
    refine ⟨⟨_, hq⟩, hsurj, by simp, ?_, ?_⟩
    · show D⁻¹ * (f 1 - f 0) = 1
      rw [← hDdef]; exact inv_mul_cancel₀ hD
    · filter_upwards [hdiffae, hdil] with z h1 h2
      have hfz : DifferentiableAt ℝ (fun z => f z - f 0) z := h1.sub_const _
      have hφ : DifferentiableAt ℂ (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) := by fun_prop
      have hφ' : deriv (fun w : ℂ => D⁻¹ * w) ((fun z => f z - f 0) z) ≠ 0 := by simpa using hDi
      have e1 := complexDilatation_comp_conformal_left hfz hφ hφ'
      have e0 : complexDilatation (fun z => f z - f 0) z = complexDilatation f z := by
        unfold complexDilatation dz dzbar
        have : fderiv ℝ (fun z => f z - f 0) z = fderiv ℝ f z := by
          rw [fderiv_sub_const]
        rw [this]
      have hcomp : (fun z => D⁻¹ * (f z - f 0)) = (fun w : ℂ => D⁻¹ * w) ∘ (fun z => f z - f 0) := rfl
      rw [hcomp, e1, e0]; exact h2
  have hGH : G = fun z => D⁻¹ * (f z - f 0) :=
    thm13_5_uniqueness_plane hG.1 hH.1 hG.2.1 hH.2.1
      (by filter_upwards [hG.2.2.2.2, hH.2.2.2.2] with z a b using by rw [a, b]) hG.2.2.1 hG.2.2.2.1
      hH.2.2.1 hH.2.2.2.1
  refine ⟨D, hD, fun z => ?_⟩
  rw [hGH]; simp only [hf]; ring

theorem tv_Lp_bound {ν : ℂ → ℂ} {ε R p : ℝ} (hε : 0 ≤ ε) (hp0 : 0 < p) (hν : IsBeltramiCoeff ν univ ε)
    (hsupp : ∀ ζ : ℂ, R < ‖ζ‖ → ν ζ = 0) :
    MemLp ν (ENNReal.ofReal p) ∧ eLpNorm ν (ENNReal.ofReal p) volume ≤
      volume (closedBall (0 : ℂ) R) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal ε := by
  have hνind : ν = (closedBall (0 : ℂ) R).indicator ν := by
    funext w
    by_cases hw : w ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw, hsupp w]
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw
  have hmeas : AEStronglyMeasurable ν volume := by simpa using hν.1
  have hb : ∀ᵐ w ∂volume, ‖ν w‖ ≤ ε := by simpa using hν.2
  have hνB : eLpNorm ν (ENNReal.ofReal p) volume ≤
      volume (closedBall (0 : ℂ) R) ^ (ENNReal.ofReal p).toReal⁻¹ * ENNReal.ofReal ε := by
    rw [hνind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict (closedBall (0 : ℂ) R)) (p := ENNReal.ofReal p)
      (f := ν) (C := ε) hmeas.restrict (ae_restrict_of_ae hb)
    rwa [Measure.restrict_apply_univ] at this
  refine ⟨?_, hνB⟩
  refine lt_of_le_of_lt hνB ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne)
    ENNReal.ofReal_lt_top

theorem tv_local_bound (R : ℝ) :
    ∃ C ε₀ α : ℝ, 0 < α ∧ 0 < ε₀ ∧ ∀ (ν F : ℂ → ℂ) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ → IsBeltramiCoeff ν univ ε →
      (∀ ζ : ℂ, R < ‖ζ‖ → ν ζ = 0) → IsNormalizedSolution F ν →
        ∀ x : ℂ, ‖x‖ ≤ 1 → ‖F x - x‖ ≤ C * ε * ‖x‖ ^ α := by
  obtain ⟨p, hp, -, hkp⟩ := eq12_1_exists_exponent (k := 1 / 2) (by norm_num) (show (2 : ℝ) < 3 by norm_num)
  obtain ⟨M₂, hM₂⟩ := lemma11_2 hp
  have hp0 : (0 : ℝ) < p := by linarith
  set Λ : ℝ := hilbertNorm p with hΛ
  have hΛ0 : 0 ≤ Λ := hilbertNorm_nonneg p
  set R' : ℝ := max R 1 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Vol : ℝ := (volume (closedBall (0 : ℂ) R')).toReal ^ (1 / p) with hVol
  have hVol0 : 0 ≤ Vol := by positivity
  set α : ℝ := (p - 2) / p with hα
  have hα0 : 0 < α := div_pos (by linarith) hp0
  have hα1 : α ≤ 1 := by rw [hα, div_le_one hp0]; linarith
  set M : ℝ := max M₂ 0 with hM
  -- ‖ω‖_p ≤ 2 Vol ε ; the constant `B = 2 Vol`
  have hc0 : 0 < 1 - Λ / 2 := by linarith
  set c₀ : ℝ := 1 - Λ / 2 with hc₀
  set B : ℝ := Vol / c₀ with hB
  set ε₀ : ℝ := min (1 / 2) (1 / (2 * (M * B + 1))) with hε₀
  have hMB : 0 ≤ M * B := by positivity
  have hε₀0 : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  refine ⟨4 * M * B, ε₀, α, hα0, hε₀0, fun ν F ε hε0 hεε₀ hν hsupp hF x hx => ?_⟩
  have hsupp' : ∀ ζ : ℂ, R' < ‖ζ‖ → ν ζ = 0 := fun ζ hζ => hsupp ζ (lt_of_le_of_lt (le_max_left _ _) hζ)
  have hε12 : ε ≤ 1 / 2 := hεε₀.trans (min_le_left _ _)
  have hk1 : ε < 1 := by linarith
  have hkp' : ε * Λ < 1 := by
    calc ε * Λ ≤ 1 / 2 * Λ := mul_le_mul_of_nonneg_right hε12 hΛ0
      _ < 1 := hkp
  obtain ⟨hνmem, hνB⟩ := tv_Lp_bound hε0 hp0 hν hsupp'
  obtain ⟨ω, hω, hsol, -⟩ := eq12_1_solution hε0 hν hp hkp' hνmem
  have hbound := l15_lp_bound hε0 hp hν hω hsol hνmem
  have hωfin : eLpNorm ω (ENNReal.ofReal p) volume ≠ ⊤ := hω.eLpNorm_ne_top
  have hνfin : eLpNorm ν (ENNReal.ofReal p) volume ≠ ⊤ := hνmem.eLpNorm_ne_top
  set E := (eLpNorm ω (ENNReal.ofReal p) volume).toReal with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hEB : E ≤ (eLpNorm ν (ENNReal.ofReal p) volume).toReal + ε * Λ * E := by
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hνfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin⟩) hbound
    rwa [ENNReal.toReal_add hνfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  have hBle : (eLpNorm ν (ENNReal.ofReal p) volume).toReal ≤ Vol * ε := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top) hνB
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0, ← ENNReal.toReal_rpow] at h1
    have hpt : (ENNReal.ofReal p).toReal⁻¹ = 1 / p := by
      rw [ENNReal.toReal_ofReal hp0.le, one_div]
    rw [hpt] at h1
    exact h1
  have hden : c₀ ≤ 1 - ε * Λ := by
    have : ε * Λ ≤ 1 / 2 * Λ := mul_le_mul_of_nonneg_right hε12 hΛ0
    rw [hc₀]; linarith
  have hden0 : 0 < 1 - ε * Λ := lt_of_lt_of_le hc0 hden
  have hEle : E ≤ B * ε := by
    have h1 : E ≤ Vol * ε / (1 - ε * Λ) := by
      rw [le_div_iff₀ hden0]; nlinarith
    refine h1.trans ?_
    rw [hB, div_mul_eq_mul_div, div_le_div_iff₀ hden0 hc0]
    have := mul_nonneg hVol0 hε0
    nlinarith
  -- the normalized solution
  obtain ⟨D, hD, hGf⟩ := tv_GformulaR hε0 hk1 hp hkp' hν hR'0 hsupp' hω hsol hF
  set r : ℂ → ℂ := cauchyT ω with hr
  have hD1 : D = 1 + r 1 - r 0 := by
    have h1 := hGf 1
    rw [hF.2.2.2.1] at h1
    have : (1 : ℂ) = D⁻¹ * (1 + r 1 - r 0) := h1
    field_simp at this
    exact this
  have hr1 : ‖r 1 - r 0‖ ≤ M₂ * E := by
    have := hM₂ ω hω 1 0
    simp only [sub_zero, norm_one, Real.one_rpow, mul_one] at this
    exact this
  have hr2 : ‖r x - r 0‖ ≤ M₂ * E * ‖x‖ ^ α := by
    have := hM₂ ω hω x 0
    simpa [hE, sub_zero, hα] using this
  have hxα : ‖x‖ ≤ ‖x‖ ^ α := by
    rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
    · rw [← h0]; exact Real.rpow_nonneg le_rfl _
    · calc ‖x‖ = ‖x‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖x‖ ^ α := Real.rpow_le_rpow_of_exponent_ge h0 hx hα1
  have hME : M₂ * E ≤ M * E := mul_le_mul_of_nonneg_right (le_max_left _ _) hE0
  have hMEB : M * E ≤ M * B * ε := by
    calc M * E ≤ M * (B * ε) := mul_le_mul_of_nonneg_left hEle (le_max_right _ _)
      _ = M * B * ε := by ring
  have hεMB : M * B * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (M * B + 1)) := hεε₀.trans (min_le_right _ _)
    have h2 : 0 < 2 * (M * B + 1) := by positivity
    rw [le_div_iff₀ h2] at h1
    nlinarith
  have hDn : (1 / 2 : ℝ) ≤ ‖D‖ := by
    rw [hD1]
    have : ‖(1 : ℂ)‖ - ‖r 1 - r 0‖ ≤ ‖1 + (r 1 - r 0)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(r 1 - r 0))
      rw [sub_neg_eq_add, norm_neg] at this
      exact this
    rw [norm_one] at this
    have e : 1 + r 1 - r 0 = 1 + (r 1 - r 0) := by ring
    rw [e]
    linarith
  have hDi : ‖D⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hDp : 0 < ‖D‖ := lt_of_lt_of_le (by norm_num) hDn
    rw [inv_le_comm₀ hDp (by norm_num)]
    linarith
  have hkey : F x - x = D⁻¹ * ((r x - r 0) - x * (r 1 - r 0)) := by
    rw [hGf x, hD1]
    have hD1' : (1 + r 1 - r 0) ≠ 0 := hD1 ▸ hD
    field_simp
    ring
  rw [hkey, norm_mul]
  have hq : ‖(r x - r 0) - x * (r 1 - r 0)‖ ≤ 2 * (M * E) * ‖x‖ ^ α := by
    calc ‖(r x - r 0) - x * (r 1 - r 0)‖ ≤ ‖r x - r 0‖ + ‖x * (r 1 - r 0)‖ := norm_sub_le _ _
      _ ≤ M₂ * E * ‖x‖ ^ α + ‖x‖ * (M₂ * E) := by
          rw [norm_mul]
          exact add_le_add hr2 (mul_le_mul_of_nonneg_left hr1 (norm_nonneg _))
      _ ≤ M * E * ‖x‖ ^ α + ‖x‖ ^ α * (M * E) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hME (by positivity)) ?_
          calc ‖x‖ * (M₂ * E) ≤ ‖x‖ * (M * E) := mul_le_mul_of_nonneg_left hME (norm_nonneg _)
            _ ≤ ‖x‖ ^ α * (M * E) := mul_le_mul_of_nonneg_right hxα (by positivity)
      _ = 2 * (M * E) * ‖x‖ ^ α := by ring
  calc ‖D⁻¹‖ * ‖(r x - r 0) - x * (r 1 - r 0)‖ ≤ 2 * (2 * (M * E) * ‖x‖ ^ α) :=
        mul_le_mul hDi hq (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (2 * (M * B * ε) * ‖x‖ ^ α) := by gcongr
    _ = 4 * M * B * ε * ‖x‖ ^ α := by ring

theorem tv_local_bound_gen :
    ∃ C ε₀ α : ℝ, 0 < α ∧ 0 < ε₀ ∧ ∀ (ν F : ℂ → ℂ) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ → IsBeltramiCoeff ν univ ε →
      IsNormalizedSolution F ν → ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖F w - w‖ ≤ C * ε * ‖w‖ ^ α := by
  obtain ⟨C₀, δ₀, hδ₀, hout⟩ := ah_outside_uniform
  obtain ⟨C, ε₁, α, hα, hε₁, hloc⟩ := tv_local_bound 2
  set C₁ : ℝ := max C₀ 0 with hC₁
  set ε₀ : ℝ := min (min δ₀ ε₁) (min (1 / 2) (1 / (8 * (C₁ + 1)))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (lt_min hδ₀ hε₁) (lt_min (by norm_num) (by positivity))
  set α' : ℝ := min α 1 with hα'
  have hα'0 : 0 < α' := lt_min hα one_pos
  have hα'1 : α' ≤ 1 := min_le_right _ _
  have hα'α : α' ≤ α := min_le_left _ _
  set C' : ℝ := max C 0 with hC'
  refine ⟨2 * C' + 4 * C₁, ε₀, α', hα'0, hε₀0, fun ν F ε hε0 hεε₀ hν hF w hw => ?_⟩
  have hεδ : ε ≤ δ₀ := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₁ : ε ≤ ε₁ := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε12 : ε ≤ 1 / 2 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε8 : ε ≤ 1 / (8 * (C₁ + 1)) := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hk1 : ε < 1 := by linarith
  have hC1ε : 8 * C₁ * ε ≤ 1 := by
    have h2 : 0 < 8 * (C₁ + 1) := by positivity
    rw [le_div_iff₀ h2] at hε8
    nlinarith [le_max_right C₀ 0]
  -- outer / inner splitting
  have hν2 := ahP_mu2_beltrami hν
  obtain ⟨G₂, hG₂, -, -⟩ := thm13_7_normalized_existence hε0 hk1 hν2
  have hbound2 : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖G₂ z - z‖ ≤ C₀ * ε := fun z hz =>
    hout (nxMu2 ν) G₂ ε hεδ hν2 (ahF_nxMu2_vanish ν) hG₂ z hz
  have hC₀ε : C₀ * ε ≤ C₁ * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε0
  obtain ⟨hc, hh, -, hbd⟩ := ahF_outer hG₂
  -- `G₂` is bounded by 2 on the unit disc
  have hG₂R : ∀ z ∈ unitDisc, ‖G₂ z‖ ≤ 2 := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have := hbound2 z hzn
    have h1 : ‖G₂ z‖ ≤ ‖z‖ + ‖G₂ z - z‖ := by
      calc ‖G₂ z‖ = ‖z + (G₂ z - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖G₂ z - z‖ := norm_add_le _ _
    have h2 : C₁ * ε ≤ 1 := by nlinarith [le_max_right C₀ 0]
    linarith
  have hνpush := ahF_push_beltrami hε0 hν hG₂
  obtain ⟨H, hH, -, -⟩ := thm13_7_normalized_existence hε0 hk1 hνpush
  have hFH : F = H ∘ G₂ := ahF_comp hF hG₂ hH
  have hHsupp : ∀ ζ : ℂ, 2 < ‖ζ‖ → nxPush ν G₂ ζ = 0 := ahF_push_support hG₂R
  -- Cauchy estimate for `g = G₂ - id` on the disc of radius `1/2`
  have hgd : DifferentiableOn ℂ (fun z => G₂ z - z) (ball (0 : ℂ) 1) :=
    hc.1.sub differentiableOn_id
  have hg0 : G₂ 0 - 0 = 0 := by rw [hG₂.2.2.1]; simp
  have hderiv : ∀ u ∈ closedBall (0 : ℂ) (1 / 2), ‖deriv (fun z => G₂ z - z) u‖ ≤ 4 * (C₁ * ε) := by
    intro u hu
    have hun : ‖u‖ ≤ 1 / 2 := mem_closedBall_zero_iff.1 hu
    have hsub : closedBall u (1 / 4) ⊆ ball (0 : ℂ) 1 := by
      intro v hv
      rw [mem_ball_zero_iff]
      have : ‖v - u‖ ≤ 1 / 4 := by rwa [mem_closedBall, dist_eq_norm] at hv
      calc ‖v‖ = ‖(v - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
        _ < 1 := by linarith
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := u) (R := 1 / 4) (C := C₁ * ε)
      (f := fun z => G₂ z - z) (by norm_num)
      (DifferentiableOn.diffContOnCl (by rw [closure_ball _ (by norm_num)]; exact hgd.mono hsub))
      (fun v hv => by
        have hvb : v ∈ ball (0 : ℂ) 1 := hsub (sphere_subset_closedBall hv)
        exact (hbound2 v (mem_ball_zero_iff.1 hvb).le).trans hC₀ε)
    calc ‖deriv (fun z => G₂ z - z) u‖ ≤ C₁ * ε / (1 / 4) := h
      _ = 4 * (C₁ * ε) := by ring
  have hgw : ‖G₂ w - w‖ ≤ 4 * (C₁ * ε) * ‖w‖ := by
    have hconv : Convex ℝ (closedBall (0 : ℂ) (1 / 2)) := convex_closedBall _ _
    have hdiff : ∀ u ∈ closedBall (0 : ℂ) (1 / 2), HasDerivWithinAt (fun z => G₂ z - z)
        (deriv (fun z => G₂ z - z) u) (closedBall (0 : ℂ) (1 / 2)) u := by
      intro u hu
      have hun : ‖u‖ < 1 := by have := mem_closedBall_zero_iff.1 hu; linarith
      exact ((hgd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hun))).hasDerivAt).hasDerivWithinAt
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hdiff hderiv (mem_closedBall_self (by norm_num))
      (mem_closedBall_zero_iff.2 hw)
    rw [hg0, sub_zero] at this
    simpa using this
  -- apply the local bound to `H` at `x = G₂ w`
  set x := G₂ w with hx
  have hwn : 0 ≤ ‖w‖ := norm_nonneg w
  have hxn : ‖x‖ ≤ 2 * ‖w‖ := by
    have h1 : ‖x‖ ≤ ‖w‖ + ‖x - w‖ := by
      calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
        _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
    have h2 : 4 * (C₁ * ε) * ‖w‖ ≤ ‖w‖ := by
      have : 4 * (C₁ * ε) ≤ 1 := by nlinarith [le_max_right C₀ 0]
      nlinarith
    linarith
  have hx1 : ‖x‖ ≤ 1 := by linarith
  have hHx := hloc (nxPush ν G₂) H ε hε0 hεε₁ hνpush hHsupp hH x hx1
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have hxpow : ‖x‖ ^ α ≤ 2 * ‖w‖ ^ α' := by
    have hm : ‖x‖ ^ α ≤ ‖x‖ ^ α' := by
      rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
      · rw [← h0, Real.zero_rpow hα.ne', Real.zero_rpow hα'0.ne']
      · exact Real.rpow_le_rpow_of_exponent_ge h0 hx1 hα'α
    calc ‖x‖ ^ α ≤ ‖x‖ ^ α' := hm
      _ ≤ (2 * ‖w‖) ^ α' := Real.rpow_le_rpow (norm_nonneg _) hxn hα'0.le
      _ = 2 ^ α' * ‖w‖ ^ α' := Real.mul_rpow (by norm_num) hwn
      _ ≤ 2 * ‖w‖ ^ α' := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hwn _)
          calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα'1
            _ = 2 := Real.rpow_one 2
  have hwpow : ‖w‖ ≤ ‖w‖ ^ α' := by
    rcases eq_or_lt_of_le hwn with h0 | h0
    · rw [← h0]; exact Real.rpow_nonneg le_rfl _
    · calc ‖w‖ = ‖w‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ‖w‖ ^ α' := Real.rpow_le_rpow_of_exponent_ge h0 hw1 hα'1
  have hHx' : ‖H x - x‖ ≤ C' * ε * (2 * ‖w‖ ^ α') := by
    calc ‖H x - x‖ ≤ C * ε * ‖x‖ ^ α := hHx
      _ ≤ C' * ε * ‖x‖ ^ α := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hε0) (by positivity)
      _ ≤ C' * ε * (2 * ‖w‖ ^ α') := by
          refine mul_le_mul_of_nonneg_left hxpow (by positivity)
  have hFw : F w = H x := by rw [hFH]; rfl
  rw [hFw]
  calc ‖H x - w‖ ≤ ‖H x - x‖ + ‖x - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C' * ε * (2 * ‖w‖ ^ α') + 4 * (C₁ * ε) * ‖w‖ := add_le_add hHx' hgw
    _ ≤ C' * ε * (2 * ‖w‖ ^ α') + 4 * (C₁ * ε) * ‖w‖ ^ α' := by
        refine add_le_add_right ?_ _
        exact mul_le_mul_of_nonneg_left hwpow (by positivity)
    _ = (2 * C' + 4 * C₁) * ε * ‖w‖ ^ α' := by ring

theorem tv_extA_smul (t : ℝ) (μ : LinfStar) :
    extA ((t : ℂ) • μ) =ᵐ[volume] fun z => (t : ℂ) * extA μ z := by
  have hms : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hs := Lp.coeFn_smul (t : ℂ) μ
  have hP : ∀ᵐ z : ℂ, z ∈ unitDiscExterior → ((t : ℂ) • μ) z = (t : ℂ) * μ z := by
    have := (ae_restrict_iff' hms).1 hs
    filter_upwards [this] with z hz hzm
    simpa using hz hzm
  have hP' := ae_refl hP
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hP, hP', hne] with z h1 h2 hz0
  unfold extA
  by_cases hz1 : 1 < ‖z‖
  · rw [if_pos hz1, if_pos hz1]; exact h1 hz1
  · rw [if_neg hz1, if_neg hz1]
    by_cases hz2 : ‖z‖ < 1
    · rw [if_pos hz2, if_pos hz2]
      have hrz : refl z ∈ unitDiscExterior := (refl_mem_exterior_iff hz0).2 (mem_ball_zero_iff.2 hz2)
      rw [h2 hrz, map_mul, Complex.conj_ofReal]
      ring
    · rw [if_neg hz2, if_neg hz2]; simp

theorem tv_ahVar_smul (t : ℝ) (g : ℂ → ℂ) (w : ℂ) :
    ahVar (fun z => (t : ℂ) * g z) w = (t : ℂ) * ahVar g w := by
  unfold ahVar
  have : (fun ζ => (t : ℂ) * g ζ * ahKer w ζ) = fun ζ => (t : ℂ) * (g ζ * ahKer w ζ) := by
    funext ζ; ring
  rw [this, integral_const_mul]; ring

theorem tv_U_zero (μ : LinfStar) : normalizedSolution (extA (((0 : ℝ) : ℂ) • μ)) = id := by
  have hb := extA_isBeltramiCoeff (((0 : ℝ) : ℂ) • μ)
  have hn : ‖((0 : ℝ) : ℂ) • μ‖ = 0 := by simp
  rw [hn] at hb
  have hae := tv_extA_smul 0 μ
  have h1 := QCV.qcv_ns_congr_ae (le_refl 0) (by norm_num) hb hae
  rw [h1]
  have : (fun z => ((0 : ℝ) : ℂ) * extA μ z) = (0 : ℂ → ℂ) := by funext z; simp
  rw [this]
  exact bB_l_normalizedSolution_zero

theorem tv_U_hasDerivAt (μ : LinfStar) (a : ℂ) :
    HasDerivAt (fun t : ℝ => normalizedSolution (extA ((t : ℂ) • μ)) a) (ahVar (extA μ) a) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro η hη
  have hm : 0 < ‖μ‖ + 1 := by positivity
  obtain ⟨δ, hδ, hfv⟩ := ah_first_variation a (η / (‖μ‖ + 1)) (by positivity)
  have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| < min (δ / (‖μ‖ + 1)) (1 / (‖μ‖ + 1)) := by
    have := Metric.ball_mem_nhds (0 : ℝ) (lt_min (div_pos hδ hm) (by positivity : (0 : ℝ) < 1 / (‖μ‖ + 1)))
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  have hh1 : |h| < δ / (‖μ‖ + 1) := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : |h| < 1 / (‖μ‖ + 1) := lt_of_lt_of_le hh (min_le_right _ _)
  rw [zero_add, Real.norm_eq_abs]
  have hU0 := congrFun (tv_U_zero μ) a
  by_cases hh0 : h = 0
  · subst hh0
    simp
  · have hhp : 0 < |h| := abs_pos.2 hh0
    set ε : ℝ := |h| * (‖μ‖ + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hεδ : ε ≤ δ := by
      have := (lt_div_iff₀ hm).1 hh1
      linarith
    have hnorm : ‖(h : ℂ) • μ‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have := (lt_div_iff₀ hm).1 hh2
      nlinarith [norm_nonneg μ]
    have hb := extA_isBeltramiCoeff ((h : ℂ) • μ)
    have hbε : IsBeltramiCoeff (extA ((h : ℂ) • μ)) univ ε := by
      refine ⟨hb.1, ?_⟩
      filter_upwards [hb.2] with z hz
      refine hz.trans ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hε]
      nlinarith [norm_nonneg μ]
    have hF := QCV.qcv_ns_spec (norm_nonneg _) hnorm hb
    have h1 := hfv (extA ((h : ℂ) • μ)) (normalizedSolution (extA ((h : ℂ) • μ))) ε hε0 hεδ hbε hF
    have hv : ahVar (extA ((h : ℂ) • μ)) a = (h : ℂ) * ahVar (extA μ) a := by
      have hae := tv_extA_smul h μ
      have : ahVar (extA ((h : ℂ) • μ)) a = ahVar (fun z => (h : ℂ) * extA μ z) a := by
        unfold ahVar
        congr 1
        exact integral_congr_ae (by filter_upwards [hae] with z hz; rw [hz])
      rw [this, tv_ahVar_smul]
    rw [hv] at h1
    have h2 : η / (‖μ‖ + 1) * ε = η * |h| := by rw [hε]; field_simp
    rw [h2] at h1
    simp only [hU0, smul_eq_mul]
    simpa using h1

theorem tv_mobius_eq {A B C D u a : ℂ}
    (h : mobiusExt A B C D (u : ExtPlane) = (a : ExtPlane)) : A * u + B = a * (C * u + D) := by
  by_cases hd : C * u + D = 0
  · rw [mobiusExt_coe_of_eq_zero hd] at h
    exact absurd h.symm (OnePoint.coe_ne_infty a)
  · rw [mobiusExt_coe hd] at h
    have h2 : mobiusFn A B C D u = a := OnePoint.coe_injective h
    unfold mobiusFn at h2
    rw [div_eq_iff hd] at h2
    exact h2

theorem tv_pole_point {A B C D u1 u2 u3 l1 l2 l3 m : ℂ} (hdet : A * D - B * C ≠ 0)
    (hden : 2 * I * (u3 - u2) - (1 + I) * (u3 - u1) ≠ 0)
    (h1 : mobiusExt A B C D (u1 : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (h2 : mobiusExt A B C D (u2 : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (h3 : mobiusExt A B C D (u3 : ExtPlane) = ((1 : ℂ) : ExtPlane))
    (hl2 : l2 * (2 * I * (u3 - u2) - (1 + I) * (u3 - u1)) = -(u3 - u1))
    (hl1 : 2 * l1 = 1 - (1 + I) * l2) (hl3 : l3 = l1 + I * l2)
    (hm : m = l1 * u1 + l2 * u2 + l3 * u3) :
    mobiusExt A B C D (m : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
  have e1 := tv_mobius_eq h1
  have e2 := tv_mobius_eq h2
  have e3 := tv_mobius_eq h3
  have hS1 : l1 + l2 + l3 = 1 := by rw [hl3]; linear_combination hl1
  have hS2 : -l1 - I * l2 + l3 = 0 := by rw [hl3]; ring
  have hS3 : -u1 * l1 - I * u2 * l2 + u3 * l3 = 0 := by
    rw [hl3]
    have : (u3 - u1) * l1 + I * (u3 - u2) * l2 = 0 := by
      linear_combination (u3 - u1) / 2 * hl1 + (1 / 2 : ℂ) * hl2
    linear_combination this
  have hAm : A * m + B = 0 := by
    rw [hm]
    linear_combination l1 * e1 + l2 * e2 + l3 * e3 - B * hS1 + C * hS3 + D * hS2
  have hCm : C * m + D ≠ 0 := by
    intro hc
    apply hdet
    have : A * D - B * C = A * (C * m + D) - C * (A * m + B) := by ring
    rw [this, hc, hAm]; ring
  rw [mobiusExt_coe hCm]
  congr 1
  unfold mobiusFn
  rw [hAm, zero_div]

theorem tv_lambdaInv_small :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ K R : ℝ, 1 ≤ K → K ≤ 3 → 0 < R → R ≤ r₀ → lambdaInv (K * quadLambda R) ≤ 1 / 2 := by
  obtain ⟨hmono, hzero, -⟩ := quadLambda_strictMono
  have hL : 0 < quadLambda (1 / 2) := b4_num_quadLambda_pos (by norm_num)
  have hev : ∀ᶠ R in 𝓝[>] (0 : ℝ), quadLambda R < quadLambda (1 / 2) / 3 :=
    hzero.eventually (gt_mem_nhds (by positivity))
  obtain ⟨r₁, hr₁, hr₁'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.1 hev)
  refine ⟨r₁ / 2, by linarith [hr₁.out], fun K R hK1 hK3 hR hRr => ?_⟩
  have hr1pos : 0 < r₁ := by simpa using hr₁
  have hΛR : quadLambda R < quadLambda (1 / 2) / 3 := hr₁' ⟨hR, by linarith⟩
  have hΛpos : 0 < quadLambda R := b4_num_quadLambda_pos hR
  have hy : 0 < K * quadLambda R := by positivity
  have hy2 : K * quadLambda R < quadLambda (1 / 2) := by nlinarith
  obtain ⟨hz, hΛz⟩ := td_quadLambda_lambdaInv hy
  by_contra hcon
  push Not at hcon
  have := hmono (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show lambdaInv (K * quadLambda R) ∈ Ioi 0 from hz) hcon
  rw [hΛz] at this
  linarith

theorem tv_wAS_first_order (μ : LinfStar) :
    ∃ s : ℂ, ∀ η > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∃ q : ℂ,
      wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ ‖q - (t : ℂ) * s‖ ≤ η * |t| := by
  set U : ℝ → ℂ → ℂ := fun t => normalizedSolution (extA ((t : ℂ) • μ)) with hU
  have hU0 : ∀ a, U 0 a = a := fun a => by
    exact congrFun (tv_U_zero μ) a
  have hu1 := tv_U_hasDerivAt μ (-1)
  have hu2 := tv_U_hasDerivAt μ (-I)
  have hu3 := tv_U_hasDerivAt μ 1
  set u1 : ℝ → ℂ := fun t => U t (-1) with hu1def
  set u2 : ℝ → ℂ := fun t => U t (-I) with hu2def
  set u3 : ℝ → ℂ := fun t => U t 1 with hu3def
  set den : ℝ → ℂ := fun t => 2 * I * (u3 t - u2 t) - (1 + I) * (u3 t - u1 t) with hdendef
  have hden0 : den 0 = -4 := by
    simp only [hdendef, hu1def, hu2def, hu3def, hU0]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hu1d : DifferentiableAt ℝ u1 0 := hu1.differentiableAt
  have hu2d : DifferentiableAt ℝ u2 0 := hu2.differentiableAt
  have hu3d : DifferentiableAt ℝ u3 0 := hu3.differentiableAt
  have hdend : DifferentiableAt ℝ den 0 := by
    simp only [hdendef]
    exact ((hu3d.sub hu2d).const_mul _).sub ((hu3d.sub hu1d).const_mul _)
  set l2 : ℝ → ℂ := fun t => -(u3 t - u1 t) / den t with hl2def
  set l1 : ℝ → ℂ := fun t => (1 - (1 + I) * l2 t) / 2 with hl1def
  set l3 : ℝ → ℂ := fun t => l1 t + I * l2 t with hl3def
  set m : ℝ → ℂ := fun t => l1 t * u1 t + l2 t * u2 t + l3 t * u3 t with hmdef
  have hden0' : den 0 ≠ 0 := by rw [hden0]; norm_num
  have hl2d : DifferentiableAt ℝ l2 0 := by
    simp only [hl2def]
    exact (hu3d.sub hu1d).neg.div hdend hden0'
  have hl1d : DifferentiableAt ℝ l1 0 := by
    simp only [hl1def]
    exact ((hl2d.const_mul _).const_sub _).div_const _
  have hl3d : DifferentiableAt ℝ l3 0 := hl1d.add (hl2d.const_mul _)
  have hmd : DifferentiableAt ℝ m 0 := by
    simp only [hmdef]
    exact ((hl1d.mul hu1d).add (hl2d.mul hu2d)).add (hl3d.mul hu3d)
  have hm0 : m 0 = 0 := by
    simp only [hmdef, hl1def, hl2def, hl3def, hdendef, hu1def, hu2def, hu3def, hU0]
    ring_nf
  have hmd' : HasDerivAt m (deriv m 0) 0 := hmd.hasDerivAt
  set s : ℂ := deriv m 0 with hs
  refine ⟨s, fun η hη => ?_⟩
  obtain ⟨C, ε₀, α, hα, hε₀, hloc⟩ := tv_local_bound_gen
  obtain ⟨r₀, hr₀, hlam⟩ := tv_lambdaInv_small
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set μ1 : ℝ := ‖μ‖ + 1 with hμ1def
  have hμ1 : 0 < μ1 := by positivity
  set K₁ : ℝ := ‖s‖ + 1 + C' * μ1 with hK₁def
  have hK₁ : 0 < K₁ := by positivity
  set θ : ℝ := η / (2 * (C' * μ1 + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  set y : ℝ := θ ^ (1 / α) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hθ _
  have hyα : y ^ α = θ := by
    rw [hy, ← Real.rpow_mul hθ.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  set c : ℝ := min (η / 2) 1 with hc
  have hc0 : 0 < c := lt_min (by positivity) one_pos
  have hmest : ∀ᶠ t : ℝ in 𝓝 0, ‖m t - t * s‖ ≤ c * |t| := by
    have h1 := hasDerivAt_iff_isLittleO_nhds_zero.1 hmd'
    have h2 := (Asymptotics.isLittleO_iff.1 h1) hc0
    filter_upwards [h2] with t ht
    simp only [zero_add, hm0, sub_zero, smul_eq_mul, Real.norm_eq_abs] at ht
    simpa using ht
  have hdenev : ∀ᶠ t : ℝ in 𝓝 0, den t ≠ 0 := hdend.continuousAt.eventually_ne hden0'
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < min (min (min (ε₀ / μ1) (1 / (2 * μ1))) (r₀ / (‖s‖ + 1))) (y / K₁) := by
    have : 0 < min (min (min (ε₀ / μ1) (1 / (2 * μ1))) (r₀ / (‖s‖ + 1))) (y / K₁) :=
      lt_min (lt_min (lt_min (by positivity) (by positivity)) (by positivity)) (by positivity)
    have h := Metric.ball_mem_nhds (0 : ℝ) this
    filter_upwards [h] with t ht
    simpa using ht
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 ((hmest.and hdenev).and hsmall)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨⟨hmt, hdt⟩, hst⟩ := hδP (by simpa [Real.dist_eq] using ht)
  have hst' : |t| < min (min (min (ε₀ / μ1) (1 / (2 * μ1))) (r₀ / (‖s‖ + 1))) (y / K₁) := hst
  have ht1 : |t| < ε₀ / μ1 :=
    lt_of_lt_of_le hst' ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have ht2 : |t| < 1 / (2 * μ1) :=
    lt_of_lt_of_le hst' ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have ht3 : |t| < r₀ / (‖s‖ + 1) :=
    lt_of_lt_of_le hst' ((min_le_left _ _).trans (min_le_right _ _))
  have ht4 : |t| < y / K₁ := lt_of_lt_of_le hst' (min_le_right _ _)
  set ν : LinfStar := (t : ℂ) • μ with hν
  set ε : ℝ := |t| * μ1 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεε₀ : ε ≤ ε₀ := ((lt_div_iff₀ hμ1).1 ht1).le
  have hε12 : ε < 1 / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ1)).1 ht2
    linarith
  have hnorm : ‖ν‖ ≤ ε := by
    rw [hν, norm_smul, Complex.norm_real, Real.norm_eq_abs, hε]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
  have hnorm1 : ‖ν‖ < 1 := by linarith
  have hνball : ν ∈ LinfStarBall := by
    simpa [LinfStarBall] using hnorm1
  have hb0 := extA_isBeltramiCoeff ν
  have hb : IsBeltramiCoeff (extA ν) univ ε := by
    refine ⟨hb0.1, ?_⟩
    filter_upwards [hb0.2] with z hz
    exact hz.trans hnorm
  obtain ⟨M, ⟨A, B, Cm, D, hdet, hMeq⟩, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hνball
  subst hMeq
  have hUt : U t = W := QCV.qcv_ns_eq (norm_nonneg _) hnorm1 hb0 hW
  have hu1t : u1 t = W (-1) := by show U t (-1) = W (-1); rw [hUt]
  have hu2t : u2 t = W (-I) := by show U t (-I) = W (-I); rw [hUt]
  have hu3t : u3 t = W 1 := by show U t 1 = W 1; rw [hUt]
  have e1 : mobiusExt A B Cm D ((u1 t : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hu1t]; exact (hwf (-1)).symm.trans hm1
  have e2 : mobiusExt A B Cm D ((u2 t : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) := by
    rw [hu2t]; exact (hwf (-I)).symm.trans hmI
  have e3 : mobiusExt A B Cm D ((u3 t : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    rw [hu3t]; exact (hwf 1).symm.trans hm2
  have hl2' : l2 t * (2 * I * (u3 t - u2 t) - (1 + I) * (u3 t - u1 t)) = -(u3 t - u1 t) := by
    have : l2 t * den t = -(u3 t - u1 t) := by
      simp only [hl2def]; exact div_mul_cancel₀ _ hdt
    exact this
  have hl1' : 2 * l1 t = 1 - (1 + I) * l2 t := by
    simp only [hl1def]; ring
  have hpole := tv_pole_point (u1 := u1 t) (u2 := u2 t) (u3 := u3 t) (l1 := l1 t) (l2 := l2 t)
    (l3 := l3 t) (m := m t) hdet hdt e1 e2 e3 hl2' hl1' rfl rfl
  have hWsurj : m t ∈ W '' univ := by rw [hW.2.1]; exact mem_univ _
  obtain ⟨q, -, hqW⟩ := hWsurj
  refine ⟨q, by rw [hwf q, hqW]; exact hpole, ?_⟩
  -- a priori bound `‖q‖ ≤ 1/2`
  have hε1 : ε < 1 := by linarith
  obtain ⟨f, hf, hKQC, huniq⟩ := thm13_7_normalized_existence hε0 hε1 hb
  have hWf : W = f := huniq W hW
  subst hWf
  have hKN : IsKQCNormalizedPlane W ((1 + ε) / (1 - ε)) := ⟨hKQC, hW.2.1, hW.2.2.1, hW.2.2.2.1⟩
  have hK1 : 1 ≤ (1 + ε) / (1 - ε) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hK3 : (1 + ε) / (1 - ε) ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hmtn : ‖m t‖ ≤ |t| * (‖s‖ + 1) := by
    have h1 := norm_sub_norm_le (m t) ((t : ℂ) * s)
    have h2 : ‖(t : ℂ) * s‖ = |t| * ‖s‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : c ≤ 1 := min_le_right _ _
    nlinarith [abs_nonneg t]
  have hmtr : ‖m t‖ ≤ r₀ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖s‖ + 1)).1 ht3
    linarith
  have hq1 : ‖q‖ ≤ 1 / 2 := by
    by_cases hm0' : m t = 0
    · have hq0 : q = 0 := by
        have h0 : W q = W 0 := by rw [hqW, hm0', hW.2.2.1]
        exact hKQC.2.2.1.2.1 (mem_univ _) (mem_univ _) h0
      rw [hq0]; norm_num
    · have hR : 0 < ‖m t‖ := norm_pos_iff.2 hm0'
      have h1 := t203_lim_nb_lower hKN hR (z := q) (by rw [hqW])
      exact h1.trans (hlam _ _ hK1 hK3 hR hmtr)
  have hlq := hloc (extA ν) W ε hε0 hεε₀ hb hW q hq1
  rw [hqW] at hlq
  have hqm : ‖q - m t‖ ≤ C' * μ1 * |t| * ‖q‖ ^ α := by
    rw [norm_sub_rev]
    refine hlq.trans ?_
    have hC : C ≤ C' := le_max_left _ _
    have : C * ε ≤ C' * ε := mul_le_mul_of_nonneg_right hC hε0
    have h2 := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (norm_nonneg q) α)
    calc C * ε * ‖q‖ ^ α ≤ C' * ε * ‖q‖ ^ α := h2
      _ = C' * μ1 * |t| * ‖q‖ ^ α := by rw [hε]; ring
  have hqα1 : ‖q‖ ^ α ≤ 1 := Real.rpow_le_one (norm_nonneg _) (by linarith) hα.le
  have hqK : ‖q‖ ≤ K₁ * |t| := by
    have h1 := norm_sub_norm_le q (m t)
    have h2 : C' * μ1 * |t| * ‖q‖ ^ α ≤ C' * μ1 * |t| := by
      calc C' * μ1 * |t| * ‖q‖ ^ α ≤ C' * μ1 * |t| * 1 :=
            mul_le_mul_of_nonneg_left hqα1 (by positivity)
        _ = C' * μ1 * |t| := mul_one _
    rw [hK₁def]
    linarith
  have hqy : ‖q‖ ≤ y := by
    have := (lt_div_iff₀ hK₁).1 ht4
    rw [mul_comm] at hqK
    linarith
  have hqθ : ‖q‖ ^ α ≤ θ := by
    rw [← hyα]; exact Real.rpow_le_rpow (norm_nonneg _) hqy hα.le
  have hθe : θ * (C' * μ1 + 1) = η / 2 := by rw [hθdef]; field_simp
  have hCθ : C' * μ1 * θ ≤ η / 2 := by
    have : C' * μ1 * θ = θ * (C' * μ1 + 1) - θ := by ring
    linarith
  have hcη : c ≤ η / 2 := min_le_left _ _
  calc ‖q - (t : ℂ) * s‖ = ‖(q - m t) + (m t - (t : ℂ) * s)‖ := by ring_nf
    _ ≤ ‖q - m t‖ + ‖m t - (t : ℂ) * s‖ := norm_add_le _ _
    _ ≤ C' * μ1 * |t| * θ + c * |t| := by
        refine add_le_add ((hqm.trans (mul_le_mul_of_nonneg_left hqθ (by positivity)))) hmt
    _ ≤ η * |t| := by
        have := mul_le_mul_of_nonneg_left hCθ (abs_nonneg t)
        have := mul_le_mul_of_nonneg_right hcη (abs_nonneg t)
        linarith

theorem tv_wB_form {ν : LinfStar} (hν : ν ∈ LinfStarBall) {q : ℂ}
    (hq : wAS ν (q : ExtPlane) = ((0 : ℂ) : ExtPlane)) :
    ∃ α γ : ℂ, α * deriv (normalizedSolution (extB ν)) 0 = 1 ∧
      γ = -(nxInvConj (normalizedSolution (extB ν)) (conj q)) ∧
      ∀ z : ℂ, 1 + γ * normalizedSolution (extB ν) z ≠ 0 →
        finPart (wB ν (z : ExtPlane)) =
          α * normalizedSolution (extB ν) z / (1 + γ * normalizedSolution (extB ν) z) := by
  have hν1 : ‖ν‖ < 1 := by simpa [LinfStarBall] using hν
  have hF : IsNormalizedSolution (normalizedSolution (extB ν)) (extB ν) :=
    QCV.qcv_ns_spec (norm_nonneg ν) hν1 (extB_isBeltramiCoeff ν)
  obtain ⟨M, ⟨a, b, c, d, hdet, hMeq⟩, W, hW, hwf, hwi, f, hf, hf0, hf1, hfp⟩ := (wB_spec hν).1
  subst hMeq
  obtain rfl : W = normalizedSolution (extB ν) :=
    (QCV.qcv_ns_eq (norm_nonneg ν) hν1 (extB_isBeltramiCoeff ν) hW).symm
  set F : ℂ → ℂ := normalizedSolution (extB ν) with hFdef
  have hF0 : F 0 = 0 := hF.2.2.1
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hd : d ≠ 0 := by
    intro hd0
    have h1 := hf 0 h0mem
    rw [hwf 0, hF0, hf0] at h1
    rw [mobiusExt_coe_of_eq_zero (by rw [hd0]; ring)] at h1
    exact OnePoint.infty_ne_coe _ h1
  have hFan : AnalyticAt ℂ F 0 :=
    (extB_solution_holomorphic hF).analyticAt (isOpen_ball.mem_nhds h0mem)
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), c * F z + d ≠ 0 :=
    (hFan.continuousAt.const_mul c |>.add_const d).eventually_ne (by simpa [hF0] using hd)
  have hfe : f =ᶠ[𝓝 (0 : ℂ)] fun z => mobiusFn a b c d (F z) := by
    filter_upwards [isOpen_ball.mem_nhds h0mem, hnear] with z hz hn
    have h1 := hf z hz
    rw [hwf z, mobiusExt_coe hn] at h1
    exact (OnePoint.coe_injective h1).symm
  have hm0 : mobiusFn a b c d (F 0) = 0 := by
    have := hfe.eq_of_nhds
    rw [hf0] at this
    exact this.symm
  have hb : b = 0 := by
    have he : b / d = 0 := by simpa only [hF0, mobiusFn, mul_zero, zero_add] using hm0
    exact (div_eq_zero_iff.mp he).resolve_right hd
  have hden : c * F 0 + d ≠ 0 := by simpa [hF0] using hd
  have he1 := (mobius_comp_first_second (a := a) (b := b) hFan hden).1
  have hm1 : deriv (fun z => mobiusFn a b c d (F z)) 0 = 1 := hfe.deriv_eq.symm.trans hf1
  rw [hm1, hb, hF0] at he1
  have hαe : (a * d - 0 * c) / (c * 0 + d) ^ 2 = a / d := by
    rw [div_eq_div_iff (pow_ne_zero 2 (by simpa using hd)) hd]; ring
  rw [hαe] at he1
  -- the pole condition
  have hbij := wAS_bijective ν
  have hp : wAS ν (Function.invFun (wAS ν) extInf) = extInf :=
    Function.invFun_eq (hbij.2 extInf)
  have hρp : wAS ν (mobiusExt 0 1 1 0 (OnePoint.map conj (Function.invFun (wAS ν) extInf))) =
      ((0 : ℂ) : ExtPlane) := by
    rw [wAS_refl_comm hν, hp, rho_infty]
  have hρq : mobiusExt 0 1 1 0 (OnePoint.map conj (Function.invFun (wAS ν) extInf)) = (q : ExtPlane) :=
    hbij.1 (hρp.trans hq.symm)
  have hpq : Function.invFun (wAS ν) extInf = mobiusExt 0 1 1 0 (OnePoint.map conj (q : ExtPlane)) := by
    rw [← hρq, rho_invol]
  have hγ : c / d = -(nxInvConj F (conj q)) := by
    by_cases hq0 : q = 0
    · subst hq0
      have h1 := hfp
      rw [hpq, rho_zero, hwi] at h1
      have hc : c = 0 := by
        by_contra hc
        rw [mobiusExt_infty_of_ne hc] at h1
        exact OnePoint.coe_ne_infty _ h1
      simp [hc, nxInvConj, hF0]
    · have h1 := hfp
      rw [hpq, rho_coe hq0, hwf] at h1
      have hz : c * F (refl q) + d = 0 := by
        by_contra hz
        rw [mobiusExt_coe hz] at h1
        exact OnePoint.coe_ne_infty _ h1
      have hc : c ≠ 0 := by
        intro hc0
        rw [hc0, zero_mul, zero_add] at hz
        exact hd hz
      have hFr : F (refl q) ≠ 0 := by
        intro h0
        rw [h0, mul_zero, zero_add] at hz
        exact hd hz
      have hdd : d = -(c * F (refl q)) := by linear_combination hz
      have hnx : nxInvConj F (conj q) = (F (refl q))⁻¹ := rfl
      rw [hnx, hdd]
      field_simp
  refine ⟨a / d, c / d, he1.symm, hγ, fun z hz => ?_⟩
  have hcz : c * F z + d ≠ 0 := by
    intro h0
    apply hz
    have : 1 + c / d * F z = (c * F z + d) / d := by field_simp; ring
    rw [this, h0, zero_div]
  rw [hwf z, mobiusExt_coe hcz, finPart_coe, mobiusFn, hb]
  field_simp
  ring

theorem tv_gamma_first_order (μ : LinfStar) {s : ℂ} (hs : ∀ η > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∃ q : ℂ,
      wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ ‖q - (t : ℂ) * s‖ ≤ η * |t|) :
    ∀ η > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∃ q : ℂ,
      wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
        ‖-(nxInvConj (normalizedSolution (extB ((t : ℂ) • μ))) (conj q)) + (t : ℂ) * conj s‖ ≤ η * |t| := by
  intro η hη
  obtain ⟨C, ε₀, α, hα, hε₀, hloc⟩ := tv_local_bound 1
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set μ1 : ℝ := ‖μ‖ + 1 with hμ1def
  have hμ1 : 0 < μ1 := by positivity
  set K₂ : ℝ := ‖s‖ + 1 with hK₂def
  have hK₂ : 0 < K₂ := by positivity
  set θ : ℝ := η / (2 * (C' * μ1 + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  set y : ℝ := min (θ ^ (1 / α)) 1 with hy
  have hy0 : 0 < y := lt_min (Real.rpow_pos_of_pos hθ _) one_pos
  have hyα : y ^ α ≤ θ := by
    calc y ^ α ≤ (θ ^ (1 / α)) ^ α := Real.rpow_le_rpow hy0.le (min_le_left _ _) hα.le
      _ = θ := by rw [← Real.rpow_mul hθ.le, one_div, inv_mul_cancel₀ hα.ne', Real.rpow_one]
  set η' : ℝ := min (η / 2) 1 with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) one_pos
  obtain ⟨δ', hδ', hsδ⟩ := hs η' hη'0
  refine ⟨min δ' (min (min (ε₀ / μ1) (1 / (2 * μ1))) (y / K₂)),
    lt_min hδ' (lt_min (lt_min (by positivity) (by positivity)) (by positivity)), fun t ht => ?_⟩
  have ht0 : |t| < δ' := lt_of_lt_of_le ht (min_le_left _ _)
  have ht' := lt_of_lt_of_le ht (min_le_right _ _)
  have ht1 : |t| < ε₀ / μ1 := lt_of_lt_of_le ht' ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : |t| < 1 / (2 * μ1) := lt_of_lt_of_le ht' ((min_le_left _ _).trans (min_le_right _ _))
  have ht3 : |t| < y / K₂ := lt_of_lt_of_le ht' (min_le_right _ _)
  obtain ⟨q, hq, hqs⟩ := hsδ t ht0
  refine ⟨q, hq, ?_⟩
  set ν : LinfStar := (t : ℂ) • μ with hν
  set ε : ℝ := |t| * μ1 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεε₀ : ε ≤ ε₀ := ((lt_div_iff₀ hμ1).1 ht1).le
  have hε12 : ε < 1 / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ1)).1 ht2
    linarith
  have hε1 : ε < 1 := by linarith
  have hnorm : ‖ν‖ ≤ ε := by
    rw [hν, norm_smul, Complex.norm_real, Real.norm_eq_abs, hε]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
  have hnorm1 : ‖ν‖ < 1 := by linarith
  have hb0 := extB_isBeltramiCoeff ν
  have hb : IsBeltramiCoeff (extB ν) univ ε := by
    refine ⟨hb0.1, ?_⟩
    filter_upwards [hb0.2] with z hz
    exact hz.trans hnorm
  have hW := QCV.qcv_ns_spec (norm_nonneg ν) hnorm1 hb0
  have hν0 : ∀ ζ : ℂ, ‖ζ‖ < 1 → extB ν ζ = 0 := fun ζ hζ => by
    have hn : ζ ∉ unitDiscExterior := fun h => absurd (show 1 < ‖ζ‖ from h) (not_lt.2 hζ.le)
    exact Set.indicator_of_notMem hn ν
  have hbt : IsBeltramiCoeff (nxMu2t (extB ν)) univ ε := (nx_mu2t_compact hε0 hb).1
  have hFt := ahI_invConj_isNormalizedSolution hε0 hε1 hb hν0 hW
  have hsupp : ∀ ζ : ℂ, 1 < ‖ζ‖ → nxMu2t (extB ν) ζ = 0 := fun ζ hz => by
    have hin : ζ⁻¹ ∈ unitDisc := by
      rw [unitDisc, mem_ball, dist_zero_right, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz
    rw [nxMu2t, nxMu2, indicator_of_notMem (notMem_compl_iff.mpr hin), zero_mul]
  have hxn : ‖conj q‖ ≤ |t| * K₂ := by
    rw [Complex.norm_conj]
    have h1 := norm_sub_norm_le q ((t : ℂ) * s)
    have h2 : ‖(t : ℂ) * s‖ = |t| * ‖s‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : η' ≤ 1 := min_le_right _ _
    have h4 := mul_le_mul_of_nonneg_right h3 (abs_nonneg t)
    rw [hK₂def]
    linarith
  have hxy : ‖conj q‖ ≤ y := by
    have := (lt_div_iff₀ hK₂).1 ht3
    linarith
  have hx1 : ‖conj q‖ ≤ 1 := hxy.trans (min_le_right _ _)
  have hlq := hloc (nxMu2t (extB ν)) (nxInvConj (normalizedSolution (extB ν))) ε hε0 hεε₀ hbt hsupp hFt
    (conj q) hx1
  have hxα : ‖conj q‖ ^ α ≤ θ :=
    (Real.rpow_le_rpow (norm_nonneg _) hxy hα.le).trans hyα
  have hFx : ‖nxInvConj (normalizedSolution (extB ν)) (conj q) - conj q‖ ≤ C' * μ1 * |t| * θ := by
    refine hlq.trans ?_
    have hC : C ≤ C' := le_max_left _ _
    have h1 : C * ε ≤ C' * ε := mul_le_mul_of_nonneg_right hC hε0
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg (conj q)) α)
    calc C * ε * ‖conj q‖ ^ α ≤ C' * ε * ‖conj q‖ ^ α := h2
      _ ≤ C' * ε * θ := mul_le_mul_of_nonneg_left hxα (by positivity)
      _ = C' * μ1 * |t| * θ := by rw [hε]; ring
  have hdiff : ‖conj q - (t : ℂ) * conj s‖ ≤ η' * |t| := by
    have : conj q - (t : ℂ) * conj s = conj (q - (t : ℂ) * s) := by
      simp [map_sub, map_mul, Complex.conj_ofReal]
    rw [this, Complex.norm_conj]; exact hqs
  have hθe : θ * (C' * μ1 + 1) = η / 2 := by rw [hθdef]; field_simp
  have hCθ : C' * μ1 * θ ≤ η / 2 := by
    have : C' * μ1 * θ = θ * (C' * μ1 + 1) - θ := by ring
    linarith
  have hη'2 : η' ≤ η / 2 := min_le_left _ _
  have e : -(nxInvConj (normalizedSolution (extB ν)) (conj q)) + (t : ℂ) * conj s =
      -(nxInvConj (normalizedSolution (extB ν)) (conj q) - conj q) - (conj q - (t : ℂ) * conj s) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have h5 := mul_le_mul_of_nonneg_left hCθ (abs_nonneg t)
  have h6 := mul_le_mul_of_nonneg_right hη'2 (abs_nonneg t)
  linarith

theorem tv_W_diff (μ : LinfStar) (z : ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => normalizedSolution (extB ((t : ℂ) • μ)) z) 0 := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have h1 : DifferentiableAt ℂ (fun μ : LinfStar => normalizedSolution (extB μ) z) 0 :=
    (QCV.qcv_planeB_differentiableOn z).differentiableAt (isOpen_ball.mem_nhds h0)
  have h2 : DifferentiableAt ℂ (fun t : ℂ => t • μ) ((0 : ℝ) : ℂ) :=
    (differentiableAt_id.smul_const μ)
  have e : (fun t : ℂ => t • μ) ((0 : ℝ) : ℂ) = 0 := by simp
  have h1' : DifferentiableAt ℂ (fun μ : LinfStar => normalizedSolution (extB μ) z)
      ((fun t : ℂ => t • μ) ((0 : ℝ) : ℂ)) := by rw [e]; exact h1
  exact (h1'.comp ((0 : ℝ) : ℂ) h2).hasDerivAt.comp_ofReal.differentiableAt

theorem tv_Wp_diff (μ : LinfStar) :
    DifferentiableAt ℝ (fun t : ℝ => deriv (normalizedSolution (extB ((t : ℂ) • μ))) 0) 0 := by
  set ρ : ℝ := ‖μ‖ + 1 with hρdef
  have hρ : 0 < ρ := by positivity
  set k0 : ℝ := ‖μ‖ / ρ with hk0def
  have hk0 : 0 ≤ k0 := by positivity
  have hk01 : k0 < 1 := by rw [hk0def, div_lt_one hρ]; linarith
  set νt : ℂ → LinfStar := fun t => (t / (ρ : ℂ)) • μ with hνt
  have hνn : ∀ t ∈ ball (0 : ℂ) 1, ‖νt t‖ ≤ k0 := by
    intro t ht
    have ht' : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
    simp only [hνt]
    rw [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hk0def, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith [norm_nonneg μ]) hρ.le
  have hνb : ∀ t ∈ ball (0 : ℂ) 1, νt t ∈ LinfStarBall := by
    intro t ht
    simpa [LinfStarBall] using (hνn t ht).trans_lt hk01
  have hbeta : ∀ t ∈ ball (0 : ℂ) 1, IsBeltramiCoeff (extB (νt t)) univ k0 := by
    intro t ht
    have hb0 := extB_isBeltramiCoeff (νt t)
    refine ⟨hb0.1, ?_⟩
    filter_upwards [hb0.2] with z hz
    exact hz.trans (hνn t ht)
  have hsol : ∀ t ∈ ball (0 : ℂ) 1,
      IsNormalizedSolution (normalizedSolution (extB (νt t))) (extB (νt t)) := by
    intro t ht
    have hn : ‖νt t‖ < 1 := (hνn t ht).trans_lt hk01
    exact QCV.qcv_ns_spec (norm_nonneg _) hn (extB_isBeltramiCoeff (νt t))
  set Gf : ℂ → ℂ → ℂ := fun t z => normalizedSolution (extB (νt t)) (z / 4) with hGf
  have hKN : ∀ t ∈ ball (0 : ℂ) 1, IsKQCNormalizedPlane (normalizedSolution (extB (νt t)))
      ((1 + k0) / (1 - k0)) := by
    intro t ht
    obtain ⟨f, hf, hfK, huniq⟩ := thm13_7_normalized_existence hk0 hk01 (hbeta t ht)
    have hg := hsol t ht
    have hgf : normalizedSolution (extB (νt t)) = f := huniq _ hg
    rw [hgf]
    rw [hgf] at hg
    exact ⟨hfK, hg.2.1, hg.2.2.1, hg.2.2.2.1⟩
  have hcont : ∀ t ∈ ball (0 : ℂ) 1, Continuous (Gf t) := by
    intro t ht
    obtain ⟨⟨K, hK⟩, -⟩ := hsol t ht
    have hWc : Continuous (normalizedSolution (extB (νt t))) := continuousOn_univ.mp hK.2.2.1.1
    exact hWc.comp (continuous_id.div_const 4)
  have hdiff : ∀ z : ℂ, DifferentiableOn ℂ (fun t => Gf t z) (ball (0 : ℂ) 1) := by
    intro z
    have h1 := QCV.qcv_planeB_differentiableOn (z / 4)
    have h2 : Differentiable ℂ νt := (differentiable_id.div_const (ρ : ℂ)).smul_const μ
    exact h1.comp h2.differentiableOn hνb
  have hM : ∀ t ∈ ball (0 : ℂ) 1, ∀ z : ℂ, ‖z‖ ≤ 2 →
      ‖Gf t z‖ ≤ lambdaInv ((1 + k0) / (1 - k0) * quadLambda (1 / 2)) := by
    intro t ht z hz
    refine t203_lim_nb_upper (hKN t ht) (by norm_num : (0 : ℝ) < 1 / 2) ?_
    rw [norm_div]
    norm_num
    linarith
  have hQ := l15_param_circle 2 hcont hdiff hM
  have hderiv : ∀ t ∈ ball (0 : ℂ) 1, deriv (normalizedSolution (extB (νt t))) 0 =
      4 * ((2 * π * I)⁻¹ * ∮ z in C(0, 2), Gf t z / z ^ 2) := by
    intro t ht
    have hW := hsol t ht
    have hWd : DifferentiableOn ℂ (normalizedSolution (extB (νt t))) unitDisc :=
      extB_solution_holomorphic hW
    have hhd : DifferentiableOn ℂ (Gf t) (closedBall 0 2) := by
      intro z hz
      have hz' : z / 4 ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff, norm_div]
        rw [mem_closedBall_zero_iff] at hz
        norm_num
        linarith
      have := (hWd.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
        ((differentiableAt_id).div_const (4 : ℂ))
      exact this.differentiableWithinAt
    have hc := hhd.deriv_eq_smul_circleIntegral (by norm_num : (0 : ℝ) < 2)
    have hd0 : deriv (Gf t) 0 = deriv (normalizedSolution (extB (νt t))) 0 / 4 := by
      have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
      have hd := (hWd.differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
      have h4 : HasDerivAt (fun z : ℂ => z / 4) (1 / 4 : ℂ) 0 := (hasDerivAt_id 0).div_const 4
      have h5 : HasDerivAt (normalizedSolution (extB (νt t))) (deriv (normalizedSolution (extB (νt t))) 0)
          ((fun z : ℂ => z / 4) 0) := by
        simpa using hd
      have := h5.comp 0 h4
      rw [show Gf t = (normalizedSolution (extB (νt t))) ∘ (fun z : ℂ => z / 4) from rfl, this.deriv]
      ring
    have hfun : (fun z : ℂ => Gf t z / z ^ 2) = fun z : ℂ => (1 / (z - 0) ^ 2) • Gf t z := by
      funext z; simp only [sub_zero, smul_eq_mul]; ring
    have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [hfun, hc, smul_eq_mul, hd0]
    field_simp
  have hE : DifferentiableAt ℂ (fun τ : ℂ => deriv (normalizedSolution (extB (τ • μ))) 0) ((0 : ℝ) : ℂ) := by
    have hQ0 : DifferentiableAt ℂ (fun t => (2 * π * I)⁻¹ * ∮ z in C(0, 2), Gf t z / z ^ 2)
        ((fun τ : ℂ => (ρ : ℂ) * τ) ((0 : ℝ) : ℂ)) := by
      have : (fun τ : ℂ => (ρ : ℂ) * τ) ((0 : ℝ) : ℂ) = 0 := by simp
      rw [this]
      exact hQ.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
    have hc := (hQ0.comp ((0 : ℝ) : ℂ) ((differentiableAt_id).const_mul (ρ : ℂ))).const_mul 4
    refine hc.congr_of_eventuallyEq ?_
    have hmem : ∀ᶠ τ : ℂ in 𝓝 ((0 : ℝ) : ℂ), (ρ : ℂ) * τ ∈ ball (0 : ℂ) 1 := by
      have : Continuous fun τ : ℂ => (ρ : ℂ) * τ := continuous_const.mul continuous_id
      exact this.continuousAt.eventually_mem (isOpen_ball.mem_nhds (by simp))
    filter_upwards [hmem] with τ hτ
    have hτe : νt ((ρ : ℂ) * τ) = τ • μ := by
      simp only [hνt]
      congr 1
      have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      rw [mul_div_cancel_left₀ _ hρc]
    have := hderiv _ hτ
    rw [hτe] at this
    simpa using this
  exact hE.hasDerivAt.comp_ofReal.differentiableAt

theorem tv1_a_diff (μ : LinfStar) (z : ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => finPart (wB ((t : ℂ) • μ) (z : ExtPlane))) 0 := by
  obtain ⟨s, hs⟩ := tv_wAS_first_order μ
  have hg := tv_gamma_first_order μ hs
  set W : ℝ → ℂ → ℂ := fun t => normalizedSolution (extB ((t : ℂ) • μ)) with hW
  set qf : ℝ → ℂ := fun t => if h : ∃ q : ℂ, wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane)
    then h.choose else 0 with hqf
  have hqf_spec : ∀ t : ℝ, (∃ q : ℂ, wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane)) →
      wAS ((t : ℂ) • μ) (qf t : ExtPlane) = ((0 : ℂ) : ExtPlane) := fun t h => by
    simp only [hqf, dif_pos h]
    exact h.choose_spec
  have hqf_uniq : ∀ (t : ℝ) (q : ℂ), wAS ((t : ℂ) • μ) (q : ExtPlane) = ((0 : ℂ) : ExtPlane) → qf t = q := by
    intro t q hq
    have h1 := hqf_spec t ⟨q, hq⟩
    exact OnePoint.coe_injective ((wAS_bijective _).1 (h1.trans hq.symm))
  set γf : ℝ → ℂ := fun t => -(nxInvConj (W t) (conj (qf t))) with hγf
  have hγ0 : γf 0 = 0 := by
    obtain ⟨δ, hδ, hP⟩ := hg 1 one_pos
    obtain ⟨q, hq, hb⟩ := hP 0 (by simpa using hδ)
    have h1 := hqf_uniq 0 q hq
    have h2 : ‖γf 0‖ ≤ 0 := by
      have : γf 0 = -(nxInvConj (W 0) (conj q)) := by simp only [hγf, h1]
      have hb' : ‖-(nxInvConj (W 0) (conj q)) + (((0 : ℝ) : ℂ)) * conj s‖ ≤ 1 * |(0 : ℝ)| := hb
      rw [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, mul_zero] at hb'
      rw [this]
      exact hb'
    exact norm_le_zero_iff.1 h2
  have hγd : HasDerivAt γf (-(conj s)) 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro η hη
    obtain ⟨δ, hδ, hP⟩ := hg η hη
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa using hh
    obtain ⟨q, hq, hb⟩ := hP h hh'
    have h1 := hqf_uniq h q hq
    have e : γf (0 + h) - γf 0 - h • (-(conj s)) = -(nxInvConj (W h) (conj q)) + (h : ℂ) * conj s := by
      rw [zero_add, hγ0, Complex.real_smul]
      simp only [hγf, h1]
      ring
    rw [e, Real.norm_eq_abs]
    exact hb
  have hA : DifferentiableAt ℝ (fun t : ℝ => deriv (W t) 0) 0 := tv_Wp_diff μ
  have hWz : DifferentiableAt ℝ (fun t : ℝ => W t z) 0 := tv_W_diff μ z
  have hA0 : deriv (W 0) 0 ≠ 0 := by
    have hν : (((0 : ℝ) : ℂ) • μ) ∈ LinfStarBall := by simp [LinfStarBall]
    obtain ⟨δ, hδ, hP⟩ := hg 1 one_pos
    obtain ⟨q, hq, -⟩ := hP 0 (by simpa using hδ)
    obtain ⟨α, γ, hα, -, -⟩ := tv_wB_form hν hq
    have hα' : α * deriv (W 0) 0 = 1 := hα
    intro h0
    rw [h0, mul_zero] at hα'
    exact zero_ne_one hα'
  have hden : DifferentiableAt ℝ (fun t : ℝ => 1 + γf t * W t z) 0 :=
    (hγd.differentiableAt.mul hWz).const_add 1
  have hden0 : (1 : ℂ) + γf 0 * W 0 z ≠ 0 := by rw [hγ0, zero_mul, add_zero]; exact one_ne_zero
  have hgd : DifferentiableAt ℝ (fun t : ℝ => (deriv (W t) 0)⁻¹ * W t z / (1 + γf t * W t z)) 0 :=
    ((hA.inv hA0).mul hWz).div hden hden0
  have hev : (fun t : ℝ => finPart (wB ((t : ℂ) • μ) (z : ExtPlane))) =ᶠ[𝓝 0]
      fun t : ℝ => (deriv (W t) 0)⁻¹ * W t z / (1 + γf t * W t z) := by
    obtain ⟨δ, hδ, hP⟩ := hg 1 one_pos
    have hcD : ∀ᶠ t in 𝓝 (0 : ℝ), 1 + γf t * W t z ≠ 0 := hden.continuousAt.eventually_ne hden0
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < min δ (1 / (‖μ‖ + 1)) :=
      by filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ (by positivity : (0 : ℝ) < 1 / (‖μ‖ + 1)))] with t ht
         simpa using ht
    filter_upwards [hcD, hsmall] with t hD hst
    have hν : ((t : ℂ) • μ) ∈ LinfStarBall := by
      have h1 : |t| < 1 / (‖μ‖ + 1) := lt_of_lt_of_le hst (min_le_right _ _)
      have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖μ‖ + 1)).1 h1
      simp only [LinfStarBall, mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg μ, abs_nonneg t]
    obtain ⟨q, hq, -⟩ := hP t (lt_of_lt_of_le hst (min_le_left _ _))
    obtain ⟨α, γ, hα, hγeq, hform⟩ := tv_wB_form hν hq
    have hqt : qf t = q := hqf_uniq t q hq
    have hγt : γf t = γ := by simp only [hγf, hqt]; exact hγeq.symm
    have hα' : α = (deriv (W t) 0)⁻¹ := eq_inv_of_mul_eq_one_left hα
    have hD' : 1 + γ * normalizedSolution (extB ((t : ℂ) • μ)) z ≠ 0 := by rw [← hγt]; exact hD
    show finPart (wB ((t : ℂ) • μ) (z : ExtPlane)) = (deriv (W t) 0)⁻¹ * W t z / (1 + γf t * W t z)
    rw [hform z hD', hα', hγt]
  exact hgd.congr_of_eventuallyEq hev

theorem tv_pullback_harmonic {μ : LinfStar} (hh : μ ∈ harmonicBeltrami) {T : ℂ → ℂ} {a b : ℂ}
    (ha : a ∈ unitDiscExterior)
    (hT : IsConformalOnto T (unitDiscExterior \ {a}) (unitDiscExterior \ {b}))
    (hw : ∀ u ∈ unitDiscExterior \ {a}, ‖T u‖ ^ 2 - 1 = ‖deriv T u‖ * (‖u‖ ^ 2 - 1)) :
    toLinf (fun u => μ (T u) * (conj (deriv T u) / deriv T u)) ∈ harmonicBeltrami := by
  obtain ⟨φ, hφ⟩ := (mem_harmonicBeltrami_iff μ).1 hh
  have hDo : IsOpen unitDiscExterior := bc_hEo
  have hDm : MeasurableSet unitDiscExterior := hDo.measurableSet
  have hD'o : IsOpen (unitDiscExterior \ {a}) := hDo.sdiff isClosed_singleton
  have hD'm : MeasurableSet (unitDiscExterior \ {a}) := hD'o.measurableSet
  have hrestr : volume.restrict (unitDiscExterior \ {a}) = volume.restrict unitDiscExterior :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton a))
  have hmemE : ∀ u : ℂ, u ∈ unitDiscExterior ↔ 1 < ‖u‖ := fun u => Iff.rfl
  have hTmem : ∀ u ∈ unitDiscExterior \ {a}, T u ∈ unitDiscExterior := by
    intro u hu
    have : T u ∈ T '' (unitDiscExterior \ {a}) := ⟨u, hu, rfl⟩
    rw [hT.2.2] at this
    exact this.1
  have hKQC : IsKQC T (unitDiscExterior \ {a}) 1 := isKQC_one_of_conformal hD'o hT
  have hder0 : ∀ u ∈ unitDiscExterior \ {a}, deriv T u ≠ 0 := by
    intro u hu h0
    have h1 := hw u hu
    have h2 : 1 < ‖T u‖ := (hmemE _).1 (hTmem u hu)
    have h3 : 1 < ‖u‖ := (hmemE _).1 hu.1
    rw [h0, norm_zero, zero_mul] at h1
    nlinarith
  have hTan : AnalyticOnNhd ℂ T (unitDiscExterior \ {a}) := hT.1.analyticOnNhd hD'o
  have hdTd : DifferentiableOn ℂ (deriv T) (unitDiscExterior \ {a}) := hTan.deriv.differentiableOn
  -- the new holomorphic function, away from the pole `a`
  set φ' : ℂ → ℂ := fun u => AInf.toFun φ (T u) * deriv T u ^ 2 with hφ'
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDiscExterior := φ.2
  have hφ'd : DifferentiableOn ℂ φ' (unitDiscExterior \ {a}) :=
    ((hφd.comp hT.1 hTmem)).mul (hdTd.pow 2)
  have hn1 : ∀ x : ℝ, 1 < x → ‖(1 - (x : ℂ) ^ 2) ^ 2‖ = (x ^ 2 - 1) ^ 2 := by
    intro x hx
    have : (1 - (x : ℂ) ^ 2) ^ 2 = (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have hne : ∀ u ∈ unitDiscExterior, (1 - (‖u‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    intro u hu h0
    have h1 : 1 < ‖u‖ := (hmemE _).1 hu
    have h2 := hn1 _ h1
    rw [h0, norm_zero] at h2
    have h3 : 0 < ‖u‖ ^ 2 - 1 := by nlinarith
    have h4 : 0 < (‖u‖ ^ 2 - 1) ^ 2 := by positivity
    linarith
  have hφw : ∀ (u : ℂ) (hu : u ∈ unitDiscExterior),
      φ.1 ⟨u, hu⟩ = (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * AInf.toFun φ u := by
    intro u hu
    simp only [AInf.toFun, unweight, dif_pos hu]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ (hne u hu)).symm
  have key : ∀ (u : ℂ) (hu : u ∈ unitDiscExterior \ {a}),
      ‖(1 - (‖u‖ : ℂ) ^ 2) ^ 2 * φ' u‖ = ‖φ.1 ⟨T u, hTmem u hu⟩‖ := by
    intro u hu
    have h1 : 1 < ‖u‖ := (hmemE _).1 hu.1
    have h2 : 1 < ‖T u‖ := (hmemE _).1 (hTmem u hu)
    have e1 : ‖(1 - (‖u‖ : ℂ) ^ 2) ^ 2 * φ' u‖ =
        (‖u‖ ^ 2 - 1) ^ 2 * (‖AInf.toFun φ (T u)‖ * ‖deriv T u‖ ^ 2) := by
      rw [norm_mul, hn1 _ h1]
      simp only [hφ', norm_mul, norm_pow]
    have e2 : ‖φ.1 ⟨T u, hTmem u hu⟩‖ = (‖T u‖ ^ 2 - 1) ^ 2 * ‖AInf.toFun φ (T u)‖ := by
      rw [hφw (T u) (hTmem u hu), norm_mul, hn1 _ h2]
    rw [e1, e2, hw u hu]
    ring
  have hbound' : ∀ u ∈ unitDiscExterior \ {a}, ‖(1 - (‖u‖ : ℂ) ^ 2) ^ 2 * φ' u‖ ≤ ‖φ.1‖ := by
    intro u hu
    rw [key u hu]
    exact BoundedContinuousFunction.norm_coe_le_norm φ.1 _
  -- removable singularity at `a`
  set r : ℝ := (‖a‖ - 1) / 2 with hr
  have ha1 : 1 < ‖a‖ := (hmemE _).1 ha
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : ∀ u ∈ ball a r, (‖a‖ + 1) / 2 ≤ ‖u‖ := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    have := norm_sub_norm_le a u
    rw [norm_sub_rev] at this
    rw [hr] at hu
    linarith
  have hballD : ball a r ⊆ unitDiscExterior := fun u hu => (hmemE _).2 (by linarith [hball u hu])
  set c₀ : ℝ := ((‖a‖ + 1) ^ 2 / 4 - 1) ^ 2 with hc₀
  have hc₀0 : 0 < c₀ := by
    have : 0 < (‖a‖ + 1) ^ 2 / 4 - 1 := by nlinarith
    rw [hc₀]
    positivity
  have hbdd : BddAbove ((norm ∘ φ') '' (ball a r \ {a})) := by
    refine ⟨‖φ.1‖ / c₀, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ unitDiscExterior \ {a} := ⟨hballD hu.1, hu.2⟩
    have h1 := hbound' u hu'
    rw [norm_mul, hn1 _ ((hmemE _).1 hu'.1)] at h1
    have h2 : c₀ ≤ (‖u‖ ^ 2 - 1) ^ 2 := by
      have hu1 := hball u hu.1
      have h4 : (‖a‖ + 1) ^ 2 / 4 ≤ ‖u‖ ^ 2 := by nlinarith
      have h5 : 0 ≤ (‖a‖ + 1) ^ 2 / 4 - 1 := by nlinarith
      rw [hc₀]
      exact pow_le_pow_left₀ h5 (by linarith) 2
    show ‖φ' u‖ ≤ ‖φ.1‖ / c₀
    rw [le_div_iff₀ hc₀0]
    calc ‖φ' u‖ * c₀ ≤ ‖φ' u‖ * (‖u‖ ^ 2 - 1) ^ 2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (‖u‖ ^ 2 - 1) ^ 2 * ‖φ' u‖ := by ring
      _ ≤ ‖φ.1‖ := h1
  set φ'' : ℂ → ℂ := Function.update φ' a (limUnder (𝓝[≠] a) φ') with hφ''
  have hφ''d : DifferentiableOn ℂ φ'' unitDiscExterior := by
    intro u hu
    by_cases hua : u = a
    · subst hua
      have := Complex.differentiableOn_update_limUnder_of_bddAbove (f := φ') (c := u)
        (s := ball u r) (ball_mem_nhds u hr0) (hφ'd.mono fun v hv => ⟨hballD hv.1, hv.2⟩) hbdd
      exact (this.differentiableAt (ball_mem_nhds u hr0)).differentiableWithinAt
    · have hu' : u ∈ unitDiscExterior \ {a} := ⟨hu, hua⟩
      have h1 : φ'' =ᶠ[𝓝 u] φ' := by
        filter_upwards [hD'o.mem_nhds hu'] with v hv
        rw [hφ'', Function.update_of_ne hv.2]
      exact ((hφ'd.differentiableAt (hD'o.mem_nhds hu')).congr_of_eventuallyEq h1).differentiableWithinAt
  have hφ''eq : ∀ u ∈ unitDiscExterior \ {a}, φ'' u = φ' u := fun u hu => by
    rw [hφ'', Function.update_of_ne hu.2]
  -- boundedness of the weighted function on all of `𝔻*`
  have hbound : ∀ u : unitDiscExterior, ‖(1 - (‖(u : ℂ)‖ : ℂ) ^ 2) ^ 2 * φ'' u‖ ≤ ‖φ.1‖ := by
    rintro ⟨u, hu⟩
    by_cases hua : u = a
    · subst hua
      have hcont : ContinuousAt (fun v : ℂ => ‖(1 - (‖v‖ : ℂ) ^ 2) ^ 2 * φ'' v‖) u :=
        (((continuous_const.sub ((Complex.continuous_ofReal.comp continuous_norm).pow 2)).pow 2).continuousAt.mul
          (hφ''d.continuousOn.continuousAt (hDo.mem_nhds hu))).norm
      have hev : ∀ᶠ v in 𝓝[≠] u, ‖(1 - (‖v‖ : ℂ) ^ 2) ^ 2 * φ'' v‖ ≤ ‖φ.1‖ := by
        have h1 : ∀ᶠ v in 𝓝[≠] u, v ∈ unitDiscExterior :=
          nhdsWithin_le_nhds (hDo.mem_nhds hu)
        filter_upwards [h1, self_mem_nhdsWithin] with v hv hv2
        rw [hφ''eq v ⟨hv, hv2⟩]
        exact hbound' v ⟨hv, hv2⟩
      exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
    · show ‖(1 - (‖u‖ : ℂ) ^ 2) ^ 2 * φ'' u‖ ≤ ‖φ.1‖
      rw [hφ''eq u ⟨hu, hua⟩]
      exact hbound' u ⟨hu, hua⟩
  have hcw : Continuous fun u : unitDiscExterior => (1 - (‖(u : ℂ)‖ : ℂ) ^ 2) ^ 2 * φ'' u :=
    ((continuous_const.sub ((Complex.continuous_ofReal.comp
      (continuous_norm.comp continuous_subtype_val)).pow 2)).pow 2).mul
      (hφ''d.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2))
  set ψ' : unitDiscExterior →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : unitDiscExterior => (1 - (‖(u : ℂ)‖ : ℂ) ^ 2) ^ 2 * φ'' u) hcw ‖φ.1‖ hbound with hψ'
  have hun : ∀ u ∈ unitDiscExterior, unweight unitDiscExterior ψ' u = φ'' u := by
    intro u hu
    have h1 : ψ' ⟨u, hu⟩ = (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * φ'' u := rfl
    simp only [unweight, dif_pos hu, h1]
    exact mul_div_cancel_left₀ _ (hne u hu)
  have hψmem : ψ' ∈ AInf unitDiscExterior := hφ''d.congr hun
  set Φ' : AInf unitDiscExterior := ⟨ψ', hψmem⟩ with hΦ'
  have hΦ : ∀ u ∈ unitDiscExterior, AInf.toFun Φ' u = φ'' u := hun
  -- a.e. identification
  have hpull := s23_c2_ae_pullback hKQC (by rintro _ ⟨y, hy, rfl⟩; exact hTmem y hy) hφ
  have hf_ae' : ∀ᵐ u ∂(volume.restrict (unitDiscExterior \ {a})),
      μ (T u) * (conj (deriv T u) / deriv T u) = (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * conj (φ'' u) := by
    filter_upwards [hpull, ae_restrict_mem hD'm] with u h1 hu
    rw [h1, hφ''eq u hu]
    have hwc : (‖T u‖ : ℂ) ^ 2 - 1 = (‖deriv T u‖ : ℂ) * ((‖u‖ : ℂ) ^ 2 - 1) := by
      exact_mod_cast hw u hu
    have hca : (‖deriv T u‖ : ℂ) ^ 2 = deriv T u * conj (deriv T u) := (Complex.mul_conj' _).symm
    have e1 : (1 - (‖T u‖ : ℂ) ^ 2) ^ 2 = (‖deriv T u‖ : ℂ) ^ 2 * (1 - (‖u‖ : ℂ) ^ 2) ^ 2 := by
      linear_combination ((‖T u‖ : ℂ) ^ 2 - 1 + (‖deriv T u‖ : ℂ) * ((‖u‖ : ℂ) ^ 2 - 1)) * hwc
    have ha0 := hder0 u hu
    rw [hφ', e1, hca, map_mul, map_pow]
    field_simp
  have hf_ae : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      μ (T u) * (conj (deriv T u) / deriv T u) = (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * conj (φ'' u) := by
    have h := hf_ae'
    rwa [hrestr] at h
  have hgc : ContinuousOn (fun u : ℂ => (1 - (‖u‖ : ℂ) ^ 2) ^ 2 * conj (φ'' u)) unitDiscExterior :=
    ((continuous_const.sub ((Complex.continuous_ofReal.comp continuous_norm).pow 2)).pow 2).continuousOn.mul
      (Complex.continuous_conj.comp_continuousOn hφ''d.continuousOn)
  have hAE : AEStronglyMeasurable (fun u => μ (T u) * (conj (deriv T u) / deriv T u))
      (volume.restrict unitDiscExterior) :=
    (hgc.aestronglyMeasurable hDm).congr (by filter_upwards [hf_ae] with u hu; exact hu.symm)
  have hmemLp : MemLp (fun u => μ (T u) * (conj (deriv T u) / deriv T u)) ∞
      (volume.restrict unitDiscExterior) := by
    refine memLp_top_of_bound hAE ‖φ.1‖ ?_
    filter_upwards [hf_ae, ae_restrict_mem hDm] with u h1 hu
    rw [h1, norm_mul, Complex.norm_conj, ← norm_mul]
    exact hbound ⟨u, hu⟩
  refine (mem_harmonicBeltrami_iff _).2 ⟨Φ', ?_⟩
  filter_upwards [bc_toLinf_ae hmemLp, hf_ae, ae_restrict_mem hDm] with u h1 h2 hu
  rw [h1, h2, hΦ u hu]

theorem tv1_norm_identity (k u z : ℂ) (hk : ‖k‖ = 1) :
    ‖k + u * z‖ ^ 2 - ‖u + k * conj z‖ ^ 2 = (‖z‖ ^ 2 - 1) * (‖u‖ ^ 2 - 1) := by
  have hk1 : k.re ^ 2 + k.im ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hk
    simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    nlinarith
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  linear_combination (-(z.re ^ 2 + z.im ^ 2 - 1)) * hk1

theorem tv1_norm_identity' (v z : ℂ) :
    ‖1 - v * conj z‖ ^ 2 - ‖v - z‖ ^ 2 = (‖v‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem tv1_sigma_inv {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (-((1 - z) / (1 - conj z)) * conj z) ∈ unitDiscExterior ∧
    IsConformalOnto
      (Function.invFun fun w : ℂ => (1 - z) / (1 - conj z) * ((1 - w * conj z) / (w - z)))
      (unitDiscExterior \ {-((1 - z) / (1 - conj z)) * conj z}) (unitDiscExterior \ {z}) ∧
    ∀ u ∈ unitDiscExterior \ {-((1 - z) / (1 - conj z)) * conj z},
      ‖Function.invFun (fun w : ℂ => (1 - z) / (1 - conj z) * ((1 - w * conj z) / (w - z))) u‖ ^ 2 - 1 =
        ‖deriv (Function.invFun fun w : ℂ => (1 - z) / (1 - conj z) * ((1 - w * conj z) / (w - z))) u‖ *
          (‖u‖ ^ 2 - 1) := by
  have hz1 : 1 < ‖z‖ := hz
  set k : ℂ := (1 - z) / (1 - conj z) with hkdef
  set σ : ℂ → ℂ := fun w => k * ((1 - w * conj z) / (w - z)) with hσ
  set T : ℂ → ℂ := Function.invFun σ with hT
  set a : ℂ := -k * conj z with hadef
  have h1z : (1 - z) ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz1
    simp at hz1
  have h1zc' : (1 - conj z) = conj (1 - z) := by simp
  have h1zc : (1 - conj z) ≠ 0 := by rw [h1zc']; exact (map_ne_zero _).2 h1z
  have hkn : ‖k‖ = 1 := by
    rw [hkdef, norm_div, h1zc', Complex.norm_conj, div_self (norm_ne_zero_iff.2 h1z)]
  have hk0 : k ≠ 0 := div_ne_zero h1z h1zc
  have hzz : ‖z‖ ^ 2 - 1 > 0 := by nlinarith
  have hzzc : 1 - z * conj z ≠ 0 := by
    intro h
    have h2 : (‖z‖ : ℂ) ^ 2 = 1 := by rw [← Complex.mul_conj']; linear_combination -h
    have h3 : ‖z‖ ^ 2 = 1 := by exact_mod_cast h2
    linarith
  have hD'o : IsOpen (unitDiscExterior \ {a}) := (isOpen_lt continuous_const continuous_norm : IsOpen unitDiscExterior).sdiff isClosed_singleton
  have haD : a ∈ unitDiscExterior := by
    show 1 < ‖a‖
    rw [hadef, norm_mul, norm_neg, hkn, Complex.norm_conj, one_mul]
    exact hz1
  have hden : ∀ u : ℂ, u ≠ a → u + k * conj z ≠ 0 := by
    intro u hu h
    apply hu
    rw [hadef]
    linear_combination h
  set Tf : ℂ → ℂ := fun u => (k + u * z) / (u + k * conj z) with hTf
  have hσTf : ∀ u : ℂ, u ≠ a → σ (Tf u) = u ∧ Tf u ≠ z := by
    intro u hu
    have hd := hden u hu
    have hw1 : Tf u - z = k * (1 - z * conj z) / (u + k * conj z) := by
      simp only [hTf]; field_simp; ring
    have hw2 : 1 - Tf u * conj z = u * (1 - z * conj z) / (u + k * conj z) := by
      simp only [hTf]; field_simp; ring
    have hw1' : Tf u - z ≠ 0 := by
      rw [hw1]; exact div_ne_zero (mul_ne_zero hk0 hzzc) hd
    refine ⟨?_, fun h => hw1' (by rw [h, sub_self])⟩
    show k * ((1 - Tf u * conj z) / (Tf u - z)) = u
    rw [hw1, hw2]
    field_simp
  have hinj : ∀ w₁ w₂ : ℂ, w₁ ≠ z → w₂ ≠ z → σ w₁ = σ w₂ → w₁ = w₂ := by
    intro w₁ w₂ h1 h2 h
    have h1' : w₁ - z ≠ 0 := sub_ne_zero.2 h1
    have h2' : w₂ - z ≠ 0 := sub_ne_zero.2 h2
    have h3 := mul_left_cancel₀ hk0 h
    rw [div_eq_div_iff h1' h2'] at h3
    have h4 : (w₂ - w₁) * (1 - z * conj z) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact (sub_eq_zero.1 h5).symm
    · exact absurd h5 hzzc
  have hσz : σ z = 0 := by simp [hσ]
  have hT_eq : ∀ u ∈ unitDiscExterior, u ≠ a → σ (T u) = u ∧ T u = Tf u := by
    intro u hu hua
    obtain ⟨hs, hne⟩ := hσTf u hua
    have hTu : σ (T u) = u := Function.invFun_eq ⟨Tf u, hs⟩
    have hTz : T u ≠ z := by
      intro h
      rw [h, hσz] at hTu
      have : 1 < ‖u‖ := hu
      rw [← hTu] at this
      norm_num at this
    exact ⟨hTu, hinj _ _ hTz hne (hTu.trans hs.symm)⟩
  have hTfd : ∀ u : ℂ, u ≠ a → HasDerivAt Tf (k * (z * conj z - 1) / (u + k * conj z) ^ 2) u := by
    intro u hu
    have hd := hden u hu
    have := ((hasDerivAt_const u k).add ((hasDerivAt_id u).mul_const z)).div
      ((hasDerivAt_id u).add_const (k * conj z)) hd
    refine HasDerivAt.congr_deriv (f := Tf) this ?_
    simp only [Pi.add_apply, id]
    ring
  have hevT : ∀ u ∈ unitDiscExterior \ {a}, T =ᶠ[𝓝 u] Tf := by
    intro u hu
    filter_upwards [hD'o.mem_nhds hu] with v hv
    exact (hT_eq v hv.1 hv.2).2
  have hderiv : ∀ u ∈ unitDiscExterior \ {a},
      deriv T u = k * (z * conj z - 1) / (u + k * conj z) ^ 2 := by
    intro u hu
    rw [(hevT u hu).deriv_eq]
    exact (hTfd u hu.2).deriv
  have hTfn : ∀ u ∈ unitDiscExterior \ {a},
      ‖Tf u‖ ^ 2 - 1 = (‖z‖ ^ 2 - 1) * (‖u‖ ^ 2 - 1) / ‖u + k * conj z‖ ^ 2 := by
    intro u hu
    have hd := norm_pos_iff.2 (hden u hu.2)
    simp only [hTf, norm_div]
    have := tv1_norm_identity k u z hkn
    field_simp
    linarith
  refine ⟨haD, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    have hdiff : DifferentiableAt ℂ Tf u := (hTfd u hu.2).differentiableAt
    exact ((hdiff.congr_of_eventuallyEq (hevT u hu)).differentiableWithinAt)
  · intro u₁ hu₁ u₂ hu₂ h
    have e1 := (hT_eq u₁ hu₁.1 hu₁.2).1
    have e2 := (hT_eq u₂ hu₂.1 hu₂.2).1
    rw [← e1, ← e2, h]
  · ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hd := norm_pos_iff.2 (hden u hu.2)
      have h1 := hTfn u hu
      have h2 : 0 < (‖z‖ ^ 2 - 1) * (‖u‖ ^ 2 - 1) / ‖u + k * conj z‖ ^ 2 := by
        have : 1 < ‖u‖ := hu.1
        apply div_pos _ (by positivity)
        apply mul_pos hzz
        nlinarith
      rw [(hT_eq u hu.1 hu.2).2]
      refine ⟨?_, ?_⟩
      · show 1 < ‖Tf u‖
        nlinarith [norm_nonneg (Tf u)]
      · exact (hσTf u hu.2).2
    · rintro ⟨hv, hvz⟩
      have hvz' : v ≠ z := hvz
      have hv1 : 1 < ‖v‖ := hv
      have hvz2 : v - z ≠ 0 := sub_ne_zero.2 hvz'
      have hσn : 1 < ‖σ v‖ := by
        have h1 := tv1_norm_identity' v z
        have hnz : 0 < ‖v - z‖ := norm_pos_iff.2 hvz2
        have : ‖σ v‖ = ‖1 - v * conj z‖ / ‖v - z‖ := by
          simp only [hσ, norm_mul, norm_div, hkn, one_mul]
        rw [this, one_lt_div hnz]
        have hpos : 0 < ‖1 - v * conj z‖ ^ 2 - ‖v - z‖ ^ 2 := by
          rw [h1]; apply mul_pos <;> nlinarith
        nlinarith [norm_nonneg (1 - v * conj z), norm_nonneg (v - z)]
      have hσa : σ v ≠ a := by
        intro h
        have h2 : k * ((1 - v * conj z) / (v - z)) = -k * conj z := h
        have h3 : (1 - v * conj z) / (v - z) = -conj z := by
          apply mul_left_cancel₀ hk0
          linear_combination h2
        rw [div_eq_iff hvz2] at h3
        apply hzzc
        linear_combination h3
      refine ⟨σ v, ⟨hσn, hσa⟩, ?_⟩
      obtain ⟨hTu, -⟩ := hT_eq (σ v) hσn hσa
      have hTz : T (σ v) ≠ z := by
        intro h
        rw [h, hσz] at hTu
        have : 1 < ‖σ v‖ := hσn
        rw [← hTu] at this
        norm_num at this
      exact hinj _ _ hTz hvz' hTu
  · intro u hu
    rw [hderiv u hu, (hT_eq u hu.1 hu.2).2, hTfn u hu]
    have hd := norm_pos_iff.2 (hden u hu.2)
    have hn : ‖z * conj z - 1‖ = ‖z‖ ^ 2 - 1 := by
      have : z * conj z - 1 = (((‖z‖ ^ 2 - 1 : ℝ)) : ℂ) := by
        rw [Complex.mul_conj']; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg hzz.le]
    rw [norm_div, norm_mul, norm_pow, hkn, hn, one_mul]
    ring

end TakhtajanTeo
