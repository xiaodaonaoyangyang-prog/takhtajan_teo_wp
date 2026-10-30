import TakhtajanTeo.Ch1.S1_1_TeichmullerTheory

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Toolkit: the map `w_μ` of Model A at finite points (`bc_` prefix) -/

/-- `w_μ|ℂ = mobiusFn ∘ W` for a normalized plane solution `W` of `extA μ`. -/
theorem bc_wA_form {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (a b c d : ℂ) (W : ℂ → ℂ), a * d - b * c ≠ 0 ∧ IsNormalizedSolution W (extA μ) ∧
      (∀ z, wA μ z = mobiusFn a b c d (W z)) ∧
      ∀ z, c * W z + d ≠ 0 → wAS μ (z : ExtPlane) = ((mobiusFn a b c d (W z) : ℂ) : ExtPlane) := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hfin, -⟩ := wA_spec hμ
  refine ⟨a, b, c, d, W, hdet, hW, fun z => ?_, fun z hz => ?_⟩
  swap
  · rw [hfin z, mobiusExt_coe hz]
  unfold wA
  rw [hfin z]
  by_cases h : c * W z + d = 0
  · rw [mobiusExt_coe_of_eq_zero h]
    simp [mobiusFn, h, finPart]
  · rw [mobiusExt_coe h]
    rfl

theorem bc_mobiusFn_hasDerivAt {a b c d z : ℂ} (hz : c * z + d ≠ 0) :
    HasDerivAt (mobiusFn a b c d) ((a * d - b * c) / (c * z + d) ^ 2) z := by
  have h := ((hasDerivAt_id' z).const_mul a |>.add_const b).div
    ((hasDerivAt_id' z).const_mul c |>.add_const d) hz
  refine h.congr_deriv ?_
  field_simp
  ring

/-- Almost everywhere properties of `w_μ` on the plane: differentiable, `dz ≠ 0`, dilatation `extA μ`,
and `‖μ_w‖ < 1`. -/
theorem bc_wA_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (wA μ) z ∧ dz (wA μ) z ≠ 0 ∧ complexDilatation (wA μ) z = extA μ z ∧
      ‖complexDilatation (wA μ) z‖ < 1 := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, hcoe⟩ := bc_wA_form hμ
  obtain ⟨K, hK⟩ := hW.1
  have hgood := s23_c2_ae_good hK
  rw [Measure.restrict_univ] at hgood
  have hinj : Function.Injective W := fun x y h => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hnull : ∀ᵐ z : ℂ, c * W z + d ≠ 0 := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro h; apply hdet; rw [hc, h]; ring
      exact Eventually.of_forall fun z => by rw [hc, zero_mul, zero_add]; exact hd
    · have hsub : {z : ℂ | c * W z + d = 0} ⊆ {z | W z = -d / c} := by
        intro z hz
        simp only [mem_setOf_eq] at hz ⊢
        field_simp
        linear_combination hz
      have : (volume : Measure ℂ) {z : ℂ | c * W z + d = 0} = 0 :=
        measure_mono_null hsub (Set.Subsingleton.measure_zero
          (fun x hx y hy => hinj (hx.trans hy.symm)) volume)
      exact measure_eq_zero_iff_ae_notMem.mp this
  filter_upwards [hgood, hW.2.2.2.2, hnull] with z hz1 hz2 hz3
  obtain ⟨hdiff, hlt, -⟩ := hz1
  have hfun : wA μ = mobiusFn a b c d ∘ W := funext hform
  have hg : DifferentiableAt ℂ (mobiusFn a b c d) (W z) := (bc_mobiusFn_hasDerivAt hz3).differentiableAt
  have hgd : deriv (mobiusFn a b c d) (W z) ≠ 0 := by
    rw [(bc_mobiusFn_hasDerivAt hz3).deriv]
    exact div_ne_zero hdet (pow_ne_zero _ hz3)
  have hdz : dz W z ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg _))
  rw [hfun]
  refine ⟨(hg.restrictScalars ℝ).comp z hdiff, ?_, ?_, ?_⟩
  · rw [(eq6_5 hdiff hg).1]; exact mul_ne_zero hgd hdz
  · rw [complexDilatation_comp_conformal_left hdiff hg hgd, hz2]
  · rw [complexDilatation_comp_conformal_left hdiff hg hgd]
    unfold complexDilatation
    rw [norm_div]
    exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hlt)).2 hlt

theorem bc_mobiusFn_injOn {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {V : Set ℂ} (hV : ∀ z ∈ V, c * z + d ≠ 0) :
    InjOn (mobiusFn a b c d) V := by
  intro x hx y hy h
  have hx' := hV x hx
  have hy' := hV y hy
  unfold mobiusFn at h
  rw [div_eq_div_iff hx' hy'] at h
  have : (a * d - b * c) * (x - y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hdet
  · exact sub_eq_zero.mp h0

/-- On the set `U` of points of `𝔻*` that are not the pole of `w_μ`, `w_μ` is a `K`-q.c. map into `𝔻*`. -/
theorem bc_wA_kqc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (U : Set ℂ) (K : ℝ), IsOpen U ∧ U ⊆ unitDiscExterior ∧ (unitDiscExterior \ U).Subsingleton ∧
      IsKQC (wA μ) U K ∧ wA μ '' U ⊆ unitDiscExterior := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, hcoe⟩ := bc_wA_form hμ
  obtain ⟨K, hK⟩ := hW.1
  have hinj : Function.Injective W := fun x y h => hK.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hWc : Continuous W := by
    have := hK.2.2.1.1
    rwa [continuousOn_univ] at this
  set U : Set ℂ := {z | 1 < ‖z‖ ∧ c * W z + d ≠ 0} with hU
  have hUo : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_norm).inter ?_
    exact isOpen_ne_fun (by fun_prop) continuous_const
  have hUE : U ⊆ unitDiscExterior := fun z hz => by simpa [unitDiscExterior] using hz.1
  have hsub : (unitDiscExterior \ U).Subsingleton := by
    intro x hx y hy
    have hpole : ∀ z ∈ unitDiscExterior \ U, c * W z + d = 0 := by
      intro z hz
      by_contra h
      exact hz.2 ⟨by simpa [unitDiscExterior] using hz.1, h⟩
    have hc : c ≠ 0 := by
      intro hc
      have hd : d ≠ 0 := by intro h; apply hdet; rw [hc, h]; ring
      have := hpole x hx
      rw [hc, zero_mul, zero_add] at this
      exact hd this
    have hx' := hpole x hx
    have hy' := hpole y hy
    apply hinj
    have : W x = -d / c := by field_simp; linear_combination hx'
    have : W y = -d / c := by field_simp; linear_combination hy'
    rw [‹W x = -d / c›, this]
  have hWU : IsKQC W U K := t3b_isKQC_restrict hK hUo (subset_univ _)
  have hVo : IsOpen (W '' U) := isOpen_image_of_isKQC hWU
  have hconf : IsConformalOnto (mobiusFn a b c d) (W '' U) (mobiusFn a b c d '' (W '' U)) := by
    have hVden : ∀ z ∈ W '' U, c * z + d ≠ 0 := by
      rintro _ ⟨x, hx, rfl⟩; exact hx.2
    refine ⟨fun z hz => ?_, bc_mobiusFn_injOn hdet hVden, rfl⟩
    exact (bc_mobiusFn_hasDerivAt (hVden z hz)).differentiableAt.differentiableWithinAt
  have hg : IsKQC (mobiusFn a b c d) (W '' U) 1 := isKQC_one_of_conformal hVo hconf
  have hcomp := thm7_1_comp hWU hg (subset_refl _)
  have hfun : wA μ = mobiusFn a b c d ∘ W := funext hform
  refine ⟨U, K * 1, hUo, hUE, hsub, ?_, ?_⟩
  · rw [hfun]; exact hcomp
  · rintro _ ⟨z, hz, rfl⟩
    have hzE : 1 < ‖z‖ := hz.1
    have h := wAS_maps_ext hμ hzE
    rw [hcoe z hz.2] at h
    rcases h with h | ⟨u, hu, hue⟩
    · exact absurd h (by simp [extInf])
    · have : mobiusFn a b c d (W z) = u := by exact_mod_cast hue
      show wA μ z ∈ unitDiscExterior
      rw [hform z, this]
      simpa [unitDiscExterior] using hu

/-- The composition law (6.8) for `w_ℓ ∘ w_μ`, almost everywhere on `𝔻*`. -/
theorem bc_comp_dilatation_ae {l μ : LinfStar} (hl : l ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation (wA l ∘ wA μ) z =
        (μ z + l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
          (1 + conj (μ z) * l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hP : ∀ᵐ u ∂(volume.restrict unitDiscExterior), DifferentiableAt ℝ (wA l) u ∧ dz (wA l) u ≠ 0 ∧
      complexDilatation (wA l) u = l u ∧ ‖complexDilatation (wA l) u‖ < 1 := by
    filter_upwards [ae_restrict_of_ae (bc_wA_ae hl), ae_restrict_mem hEo.measurableSet] with u hu hE
    obtain ⟨h1, h2, h3, h4⟩ := hu
    refine ⟨h1, h2, ?_, h4⟩
    rw [h3]
    exact extA_eq_on_exterior l hE
  have hpull := s23_c2_ae_pullback hT hTmaps hP
  rw [ae_restrict_iff' hUo.measurableSet] at hpull
  have hnull : ∀ᵐ z : ℂ, z ∉ unitDiscExterior \ U :=
    measure_eq_zero_iff_ae_notMem.mp (Set.Subsingleton.measure_zero hsub volume)
  filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hnull, ae_restrict_of_ae (bc_wA_ae hμ), ae_restrict_mem hEo.measurableSet]
    with z h1 h2 h3 hE
  have hzU : z ∈ U := by
    by_contra h; exact h2 ⟨hE, h⟩
  obtain ⟨hPd, hPz, hPdil, hPlt⟩ := h1 hzU
  obtain ⟨h3d, h3z, h3dil, h3lt⟩ := h3
  have hdilT : complexDilatation (wA μ) z = μ z := by rw [h3dil]; exact extA_eq_on_exterior μ hE
  rw [eq6_8_complexDilatation_comp h3d hPd h3z hPz h3lt hPlt, hdilT, hPdil]

/-! ### Composition with `w_μ` on `L∞(𝔻*)`-classes -/

theorem bc_hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm

/-- Pulling an a.e. statement on `𝔻*` back through `w_μ`. -/
theorem bc_pullback_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {P : ℂ → Prop}
    (h : ∀ᵐ u ∂(volume.restrict unitDiscExterior), P u) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), P (wA μ z) := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  have hpull := s23_c2_ae_pullback hT hTmaps h
  rw [ae_restrict_iff' hUo.measurableSet] at hpull
  have hnull : ∀ᵐ z : ℂ, z ∉ unitDiscExterior \ U :=
    measure_eq_zero_iff_ae_notMem.mp (Set.Subsingleton.measure_zero hsub volume)
  filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hnull, ae_restrict_mem bc_hEo.measurableSet] with z h1 h2 hE
  have hzU : z ∈ U := by
    by_contra h; exact h2 ⟨hE, h⟩
  exact h1 hzU

theorem bc_wA_measurable {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : Measurable (wA μ) := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, -⟩ := bc_wA_form hμ
  obtain ⟨K, hK⟩ := hW.1
  have hWc : Continuous W := by
    have := hK.2.2.1.1
    rwa [continuousOn_univ] at this
  have hfun : wA μ = mobiusFn a b c d ∘ W := funext hform
  rw [hfun]
  unfold mobiusFn
  exact (by fun_prop : Measurable fun z : ℂ => (a * z + b) / (c * z + d)).comp hWc.measurable

theorem bc_wA_qmp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Measure.QuasiMeasurePreserving (wA μ) (volume.restrict unitDiscExterior)
      (volume.restrict unitDiscExterior) := by
  refine ⟨bc_wA_measurable hμ, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply (bc_wA_measurable hμ) hs]
  have h : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ∉ s :=
    measure_eq_zero_iff_ae_notMem.mp hs0
  exact measure_eq_zero_iff_ae_notMem.mpr (bc_pullback_ae hμ h)

theorem bc_comp_aesm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (h : AEStronglyMeasurable ν (volume.restrict unitDiscExterior)) :
    AEStronglyMeasurable (ν ∘ wA μ) (volume.restrict unitDiscExterior) :=
  h.comp_quasiMeasurePreserving (bc_wA_qmp hμ)

/-! ### Pointwise algebra for the composition law -/

theorem bc_alg_lt {m b : ℂ} (hm : ‖m‖ < 1) (hb : ‖b‖ < 1) : ‖(m + b) / (1 + conj m * b)‖ < 1 := by
  have hq : ‖conj m * b‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg m, norm_nonneg b]
  have hden : 1 + conj m * b ≠ 0 := by
    intro h
    have h1 : conj m * b = -1 := by linear_combination h
    rw [h1] at hq; simp at hq
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have key : ‖1 + conj m * b‖ ^ 2 - ‖m + b‖ ^ 2 = (1 - ‖m‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpos : 0 < (1 - ‖m‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg m, norm_nonneg b]
  nlinarith [norm_nonneg (m + b), norm_nonneg (1 + conj m * b)]

theorem bc_alg_taylor {m b : ℂ} {r : ℝ} (hm : ‖m‖ ≤ 1) (hb : ‖b‖ ≤ r) (hmr : ‖m‖ * r ≤ 1 / 2) :
    ‖(m + b) / (1 + conj m * b) - m - (((1 - ‖m‖ ^ 2 : ℝ)) : ℂ) * b‖ ≤ 2 * r ^ 2 := by
  have hq : ‖conj m * b‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_conj]
    have := norm_nonneg m
    calc ‖m‖ * ‖b‖ ≤ ‖m‖ * r := by gcongr
      _ ≤ 1 / 2 := hmr
  have hden : 1 + conj m * b ≠ 0 := by
    intro h
    have h1 : conj m * b = -1 := by linear_combination h
    rw [h1] at hq; simp at hq; norm_num at hq
  have hden_norm : 1 / 2 ≤ ‖1 + conj m * b‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(conj m * b))
    rw [norm_neg, norm_one] at this
    have e : (1 : ℂ) - -(conj m * b) = 1 + conj m * b := by ring
    rw [e] at this
    linarith
  have hmm : m * conj m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  have e : (m + b) / (1 + conj m * b) - m - (((1 - ‖m‖ ^ 2 : ℝ)) : ℂ) * b =
      -((((1 - ‖m‖ ^ 2 : ℝ)) : ℂ) * b * (conj m * b)) / (1 + conj m * b) := by
    rw [eq_div_iff hden, sub_mul, sub_mul, div_mul_cancel₀ _ hden]
    push_cast at hmm ⊢
    linear_combination (-b) * hmm
  rw [e, norm_div, norm_neg]
  have h1 : ‖(((1 - ‖m‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> nlinarith [norm_nonneg m]
  have hbr : 0 ≤ r := (norm_nonneg b).trans hb
  simp only [norm_mul, Complex.norm_conj]
  calc ‖(((1 - ‖m‖ ^ 2 : ℝ)) : ℂ)‖ * ‖b‖ * (‖m‖ * ‖b‖) / ‖1 + conj m * b‖
      ≤ 1 * r * (1 * r) / (1 / 2) := by
        gcongr
    _ = 2 * r ^ 2 := by ring

/-! ### The derivative operator `ν ↦ (1 - |μ|²) (ν ∘ w_μ) τ` on `L∞(𝔻*)` -/

theorem bc_Lp_norm_le (X : LinfStar) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖X z‖ ≤ C) : ‖X‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable X)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound h)).trans_eq (ENNReal.toReal_ofReal hC)

theorem bc_toLinf_ae {f : ℂ → ℂ} (h : MemLp f ∞ (volume.restrict unitDiscExterior)) :
    (toLinf f : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] f := by
  unfold toLinf
  rw [dif_pos h]
  exact h.coeFn_toLp

theorem bc_norm_lt_one {μ : LinfStar} (hμ : μ ∈ LinfStarBall) : ‖μ‖ < 1 := by
  simpa [LinfStarBall] using hμ

theorem bc_g_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖(((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)‖ ≤ ‖ν‖ := by
  have hμ1 := bc_norm_lt_one hμ
  filter_upwards [ae_restrict_of_ae (bc_wA_ae hμ), bc_pullback_ae hμ (LinfStar_ae_norm_le ν),
    LinfStar_ae_norm_le μ] with z hz hν hμz
  obtain ⟨-, hdz, -, -⟩ := hz
  have hτ : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hdz)]
  have hm0 := norm_nonneg (μ z)
  have hc : ‖(((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  rw [norm_mul, norm_mul, hτ, mul_one]
  calc ‖(((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ)‖ * ‖ν (wA μ z)‖ ≤ 1 * ‖ν‖ := by
        gcongr
    _ = ‖ν‖ := one_mul _

theorem bc_g_memLp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    MemLp (fun z => (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) ∞
      (volume.restrict unitDiscExterior) := by
  have h1 : AEStronglyMeasurable (fun z => (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ)) (volume.restrict unitDiscExterior) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.sub ((Lp.aestronglyMeasurable μ).norm.pow 2))
  have h2 : AEStronglyMeasurable (fun z => ν (wA μ z)) (volume.restrict unitDiscExterior) :=
    bc_comp_aesm hμ (Lp.aestronglyMeasurable ν)
  have h3 : AEStronglyMeasurable (fun z => conj (dz (wA μ) z) / dz (wA μ) z)
      (volume.restrict unitDiscExterior) :=
    (((continuous_conj.measurable.comp (measurable_dz (wA μ))).div (measurable_dz (wA μ)))).aestronglyMeasurable
  exact memLp_top_of_bound ((h1.mul h2).mul h3) ‖ν‖ (bc_g_bound hμ ν)

/-- The derivative operator of `l ↦ l * μ` at `0`, as a `ℂ`-linear continuous map on `L∞(𝔻*)`. -/
theorem bc_exists_D {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ D : LinfStar →L[ℂ] LinfStar, ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      D ν z = (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) := by
  let g : LinfStar → ℂ → ℂ := fun ν z =>
    (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)
  let D0 : LinfStar →ₗ[ℂ] LinfStar :=
    { toFun := fun ν => toLinf (g ν)
      map_add' := by
        intro ν₁ ν₂
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (bc_g_memLp hμ (ν₁ + ν₂)), bc_toLinf_ae (bc_g_memLp hμ ν₁),
          bc_toLinf_ae (bc_g_memLp hμ ν₂), Lp.coeFn_add (toLinf (g ν₁)) (toLinf (g ν₂)),
          bc_pullback_ae hμ (Lp.coeFn_add ν₁ ν₂)] with z h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h2, h3]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.add_apply]
        ring
      map_smul' := by
        intro c ν
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (bc_g_memLp hμ (c • ν)), bc_toLinf_ae (bc_g_memLp hμ ν),
          Lp.coeFn_smul c (toLinf (g ν)), bc_pullback_ae hμ (Lp.coeFn_smul c ν)] with z h1 h2 h4 h5
        simp only [RingHom.id_apply]
        rw [h4, Pi.smul_apply, h2]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  refine ⟨D0.mkContinuous 1 (fun ν => ?_), fun ν => ?_⟩
  · rw [one_mul]
    exact norm_toLinf_le_of_ae_bound (norm_nonneg ν) (bc_g_bound hμ ν)
  · exact bc_toLinf_ae (bc_g_memLp hμ ν)

/-! ### The product `l * μ` as an explicit a.e. formula, and its derivative at `0` -/

theorem bc_b_bound {μ l : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)‖ ≤ ‖l‖ := by
  filter_upwards [ae_restrict_of_ae (bc_wA_ae hμ), bc_pullback_ae hμ (LinfStar_ae_norm_le l)]
    with z hz hl
  obtain ⟨-, hdz, -, -⟩ := hz
  have hτ : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hdz)]
  rw [norm_mul, hτ, mul_one]
  exact hl

theorem bc_mul_ae {μ l : LinfStar} (hμ : μ ∈ LinfStarBall) (hl : l ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), beltramiMul l μ z =
      (μ z + l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
        (1 + conj (μ z) * l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) := by
  have hl1 := bc_norm_lt_one hl
  have hF : MemLp (fun z => (μ z + l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
        (1 + conj (μ z) * l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ∞
      (volume.restrict unitDiscExterior) := by
    have h2 : AEStronglyMeasurable (fun z => l (wA μ z)) (volume.restrict unitDiscExterior) :=
      bc_comp_aesm hμ (Lp.aestronglyMeasurable l)
    have h3 : AEStronglyMeasurable (fun z => conj (dz (wA μ) z) / dz (wA μ) z)
        (volume.restrict unitDiscExterior) :=
      (((continuous_conj.measurable.comp (measurable_dz (wA μ))).div (measurable_dz (wA μ)))).aestronglyMeasurable
    have h1 : AEStronglyMeasurable μ (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable μ
    have hb := h2.mul h3
    have hnum : AEMeasurable (fun z => μ z + l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))
        (volume.restrict unitDiscExterior) := (h1.add hb).aemeasurable
    have hcm : AEStronglyMeasurable (fun z => conj (μ z)) (volume.restrict unitDiscExterior) :=
      continuous_conj.comp_aestronglyMeasurable h1
    have hden : AEMeasurable (fun z => 1 + conj (μ z) * l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))
        (volume.restrict unitDiscExterior) := by
      have : AEStronglyMeasurable (fun z => conj (μ z) * l (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))
          (volume.restrict unitDiscExterior) := (hcm.mul h2).mul h3
      exact aemeasurable_const.add this.aemeasurable
    refine memLp_top_of_bound (hnum.div hden).aestronglyMeasurable 1 ?_
    filter_upwards [LinfStar_ae_norm_le μ, bc_b_bound (l := l) hμ] with z hm hb
    rw [mul_assoc]
    exact (bc_alg_lt (hm.trans_lt (bc_norm_lt_one hμ)) (hb.trans_lt hl1)).le
  have hD : MemLp (complexDilatation (wA l ∘ wA μ)) ∞ (volume.restrict unitDiscExterior) :=
    hF.ae_eq (by
      filter_upwards [bc_comp_dilatation_ae hl hμ] with z hz using hz.symm)
  filter_upwards [bc_toLinf_ae hD, bc_comp_dilatation_ae hl hμ] with z h1 h2
  show (toLinf (complexDilatation (wA l ∘ wA μ)) : ℂ → ℂ) z = _
  rw [h1, h2]

theorem bc_remainder {μ l : LinfStar} (hμ : μ ∈ LinfStarBall) (D : LinfStar →L[ℂ] LinfStar)
    (hD : ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      D ν z = (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))
    (hl : ‖l‖ ≤ 1 / 2) :
    ‖beltramiMul l μ - μ - D l‖ ≤ 2 * ‖l‖ ^ 2 := by
  have hlb : l ∈ LinfStarBall := by
    have : ‖l‖ < 1 := by linarith
    simpa [LinfStarBall] using this
  refine bc_Lp_norm_le _ (by positivity) ?_
  filter_upwards [bc_mul_ae hμ hlb, hD l, Lp.coeFn_sub (beltramiMul l μ - μ) (D l),
    Lp.coeFn_sub (beltramiMul l μ) μ, LinfStar_ae_norm_le μ, bc_b_bound (l := l) hμ] with z h1 h2 h3 h4 hm hb
  rw [h3, Pi.sub_apply, h4, Pi.sub_apply, h1, h2]
  have hm1 : ‖μ z‖ ≤ 1 := hm.trans (bc_norm_lt_one hμ).le
  have key := bc_alg_taylor hm1 hb (by
    have := norm_nonneg (μ z)
    calc ‖μ z‖ * ‖l‖ ≤ 1 * (1 / 2) := by gcongr
      _ = 1 / 2 := one_mul _)
  simpa only [mul_assoc] using key

theorem bc_hasFDerivAt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ D : LinfStar →L[ℂ] LinfStar, HasFDerivAt (fun l => beltramiMul l μ) D 0 ∧
      ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
        D ν z = (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) := by
  obtain ⟨D, hD⟩ := bc_exists_D hμ
  have h0 : beltramiMul 0 μ = μ := by
    have := bc_remainder (l := 0) hμ D hD (by simp)
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      map_zero, sub_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  refine ⟨D, ?_, hD⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ h : LinfStar in nhds 0, ‖h‖ < min (1 / 2) (c / 2) := by
    have := Metric.ball_mem_nhds (0 : LinfStar) (lt_min (by norm_num : (0:ℝ) < 1 / 2) (half_pos hc))
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  have h1 : ‖h‖ ≤ 1 / 2 := (lt_min_iff.mp hh).1.le
  have h2 : ‖h‖ ≤ c / 2 := (lt_min_iff.mp hh).2.le
  have := bc_remainder (l := h) hμ D hD h1
  have e : beltramiMul (0 + h) μ - beltramiMul 0 μ - D h = beltramiMul h μ - μ - D h := by
    rw [zero_add, h0]
  rw [e]
  refine this.trans ?_
  nlinarith [norm_nonneg h]

theorem bc_remark_1_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      fderiv ℂ (fun l => beltramiMul l μ) 0 ν z =
        (1 - ‖μ z‖ ^ 2) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) := by
  obtain ⟨D, hd, hD⟩ := bc_hasFDerivAt hμ
  rw [hd.fderiv]
  filter_upwards [hD ν] with z hz
  rw [hz]
  push_cast
  ring

/-! ### The finite-coordinate inverse away from its exceptional points -/

theorem bc_wAS_eq_coe_of_wA_ne_zero {μ : LinfStar} {x : ℂ} (hx : wA μ x ≠ 0) :
    wAS μ (x : ExtPlane) = (wA μ x : ExtPlane) := by
  apply (coe_finPart_of_ne ?_).symm
  intro h
  apply hx
  simp [wA, h, finPart, extInf]

theorem bc_wA_inj_of_ne_zero {μ : LinfStar} {x y : ℂ}
    (h : wA μ x = wA μ y) (hx : wA μ x ≠ 0) : x = y := by
  apply OnePoint.coe_injective
  apply (wAS_bijective μ).1
  rw [bc_wAS_eq_coe_of_wA_ne_zero hx,
    bc_wAS_eq_coe_of_wA_ne_zero (h ▸ hx), h]

theorem bc_invFun_wA {μ : LinfStar} {x : ℂ} (hx : wA μ x ≠ 0) :
    Function.invFun (wA μ) (wA μ x) = x := by
  have he : wA μ (Function.invFun (wA μ) (wA μ x)) = wA μ x :=
    Function.invFun_eq ⟨x, rfl⟩
  exact bc_wA_inj_of_ne_zero he (by rwa [he])

theorem bc_wA_image_compl_finite {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {U : Set ℂ} (hU : (unitDiscExterior \ U).Finite) :
    (unitDiscExterior \ wA μ '' U).Finite := by
  apply ((hU.image (wA μ)).union (finite_singleton (finPart (wAS μ extInf)))).subset
  intro y hy
  by_cases hi : wAS μ extInf = (y : ExtPlane)
  · exact Or.inr (by simpa only [mem_singleton_iff, hi, finPart_coe])
  · have hyS : (y : ExtPlane) ∈ wAS μ '' (toExt unitDiscExterior ∪ {extInf}) := by
      rw [(wA_mapsTo hμ).2.1]
      exact Or.inl ⟨y, hy.1, rfl⟩
    obtain ⟨p, hp, he⟩ := hyS
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · have hf : wA μ x = y := by
        show finPart (wAS μ (x : ExtPlane)) = y
        rw [he, finPart_coe]
      exact Or.inl ⟨x, ⟨hx, fun hxU => hy.2 ⟨x, hxU, hf⟩⟩, hf⟩
    · exact (hi (by simpa only [mem_singleton_iff.mp hp] using he)).elim

/-- The ordinary `invFun` is quasiconformal on a cofinite open subset of the exterior.
Its values there agree with the local inverse of the finite-coordinate map. -/
theorem bc_invFun_kqc {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (V : Set ℂ) (K : ℝ), IsOpen V ∧ V ⊆ unitDiscExterior ∧
      (unitDiscExterior \ V).Finite ∧ IsKQC (Function.invFun (wA μ)) V K ∧
      Function.invFun (wA μ) '' V ⊆ unitDiscExterior := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  have heq : EqOn (Function.invFun (wA μ)) (Function.invFunOn (wA μ) U) (wA μ '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    have hn : wA μ x ≠ 0 := by
      have h := hTmaps ⟨x, hx, rfl⟩
      intro he
      norm_num [he, unitDiscExterior] at h
    rw [bc_invFun_wA hn, hT.2.2.1.2.1.leftInvOn_invFunOn hx]
  refine ⟨wA μ '' U, K, isOpen_image_of_isKQC hT, hTmaps,
    bc_wA_image_compl_finite hμ hsub.finite, ad_isKQC_congr (thm7_2_inv hT) heq, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [heq hy]
  exact hUE (Function.invFunOn_mem hy)

theorem bc_invFun_pullback_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {P : ℂ → Prop}
    (h : ∀ᵐ u ∂(volume.restrict unitDiscExterior), P u) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior), P (Function.invFun (wA μ) z) := by
  obtain ⟨V, K, hVo, hVE, hfin, hT, hTmaps⟩ := bc_invFun_kqc hμ
  have hpull := s23_c2_ae_pullback hT hTmaps h
  rw [ae_restrict_iff' hVo.measurableSet] at hpull
  have hnull : ∀ᵐ z : ℂ, z ∉ unitDiscExterior \ V :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)
  filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hnull,
    ae_restrict_mem bc_hEo.measurableSet] with z hp hn hz
  exact hp (by by_contra hv; exact hn ⟨hz, hv⟩)

theorem bc_invFun_right_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), wA μ (Function.invFun (wA μ) y) = y := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  have hnull : ∀ᵐ y : ℂ, y ∉ unitDiscExterior \ wA μ '' U :=
    measure_eq_zero_iff_ae_notMem.mp ((bc_wA_image_compl_finite hμ hsub.finite).measure_zero volume)
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem bc_hEo.measurableSet] with y hn hy
  have him : y ∈ wA μ '' U := by by_contra h; exact hn ⟨hy, h⟩
  obtain ⟨x, hx, he⟩ := him
  exact Function.invFun_eq ⟨x, he⟩

theorem bc_invFun_good_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      DifferentiableAt ℝ (Function.invFun (wA μ)) y ∧
      dz (Function.invFun (wA μ)) y ≠ 0 ∧
      Function.invFun (wA μ) y ∈ unitDiscExterior := by
  obtain ⟨V, K, hVo, hVE, hfin, hT, hTmaps⟩ := bc_invFun_kqc hμ
  have hg := s23_c2_ae_good hT
  rw [ae_restrict_iff' hVo.measurableSet] at hg
  have hnull : ∀ᵐ y : ℂ, y ∉ unitDiscExterior \ V :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)
  filter_upwards [ae_restrict_of_ae hg, ae_restrict_of_ae hnull,
    ae_restrict_mem bc_hEo.measurableSet] with y hg hn hy
  have hv : y ∈ V := by by_contra h; exact hn ⟨hy, h⟩
  obtain ⟨hd, hlt, -⟩ := hg hv
  refine ⟨hd, ?_, hTmaps ⟨y, hv, rfl⟩⟩
  intro he
  rw [he, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

/-- The inverse coefficient follows from the local left-inverse chain rule. -/
theorem bc_inverse_dilatation {f g : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x))
    (hfz : dz f x ≠ 0) (hgz : dz g (f x) ≠ 0)
    (he : g ∘ f =ᶠ[𝓝 x] id) :
    complexDilatation g (f x) = -complexDilatation f x * (dz f x / conj (dz f x)) := by
  have hc := eq6_2_dzbar_comp hf hg
  rw [← (eq6_3 hf).1, (t203_c1_dz_congr he).2] at hc
  have hid : dzbar (id : ℂ → ℂ) x = 0 := by simp [dzbar]
  rw [hid] at hc
  unfold complexDilatation
  have hcf : conj (dz f x) ≠ 0 := by simpa using hfz
  field_simp
  linear_combination -hc

theorem bc_invFun_dilatation_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      complexDilatation (Function.invFun (wA μ)) y =
        (fun x => -μ x * (dz (wA μ) x / conj (dz (wA μ) x)))
          (Function.invFun (wA μ) y) := by
  filter_upwards [bc_invFun_good_ae hμ, bc_invFun_right_ae hμ,
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ)),
    ae_restrict_mem bc_hEo.measurableSet] with y hg he hf hy
  obtain ⟨hgd, hgz, hxE⟩ := hg
  obtain ⟨hfd, hfz, hfm, -⟩ := hf
  have hyn : y ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hy
  have hfn : wA μ (Function.invFun (wA μ) y) ≠ 0 := by rwa [he]
  have hev : ∀ᶠ x in 𝓝 (Function.invFun (wA μ) y), wA μ x ≠ 0 :=
    hfd.continuousAt (eventually_ne_nhds hfn)
  have hleft : Function.invFun (wA μ) ∘ wA μ =ᶠ[𝓝 (Function.invFun (wA μ) y)] id := by
    filter_upwards [hev] with x hx using bc_invFun_wA hx
  have h := bc_inverse_dilatation hfd (by simpa only [he] using hgd) hfz
    (by simpa only [he] using hgz) hleft
  rw [he, hfm, extA_eq_on_exterior μ hxE] at h
  exact h

theorem bc_invFun_dilatation_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (Function.invFun (wA μ)) y‖ ≤ ‖μ‖ := by
  filter_upwards [bc_invFun_dilatation_ae hμ,
    bc_invFun_pullback_ae hμ (LinfStar_ae_norm_le μ),
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ))] with y he hn hg
  rw [he, norm_mul, norm_neg, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hg.2.1), mul_one]
  exact hn

theorem bc_invFun_dilatation_memLp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    MemLp (complexDilatation (Function.invFun (wA μ))) ∞ (volume.restrict unitDiscExterior) := by
  apply memLp_top_of_bound _ ‖μ‖ (bc_invFun_dilatation_bound hμ)
  exact ((measurable_dzbar _).div (measurable_dz _)).aestronglyMeasurable

theorem bc_beltramiInv_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), beltramiInv μ y =
      (fun x => -μ x * (dz (wA μ) x / conj (dz (wA μ) x))) (Function.invFun (wA μ) y) := by
  filter_upwards [bc_toLinf_ae (bc_invFun_dilatation_memLp hμ),
    bc_invFun_dilatation_ae hμ] with y h1 h2 using h1.trans h2

theorem bc_beltramiInv_norm_le {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ‖beltramiInv μ‖ ≤ ‖μ‖ :=
  norm_toLinf_le_of_ae_bound (norm_nonneg μ) (bc_invFun_dilatation_bound hμ)

/-- The inverse operation stays in the open coefficient ball. -/
theorem bc_beltramiInv_mem_ball {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    beltramiInv μ ∈ LinfStarBall := by
  have h := (bc_beltramiInv_norm_le hμ).trans_lt (bc_norm_lt_one hμ)
  simpa [LinfStarBall] using h

theorem bc_inverse_dz {f g : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x))
    (hj : jacobian f x ≠ 0) (he : g ∘ f =ᶠ[𝓝 x] id) :
    dz g (f x) = conj (dz f x) / (jacobian f x : ℂ) := by
  have hc := eq6_2_dz_comp hf hg
  have hb := eq6_2_dzbar_comp hf hg
  rw [← (eq6_3 hf).2, (t203_c1_dz_congr he).1] at hc
  rw [← (eq6_3 hf).1, (t203_c1_dz_congr he).2] at hb
  have hid : dz (id : ℂ → ℂ) x = 1 := by simp [dz]
  have hidb : dzbar (id : ℂ → ℂ) x = 0 := by simp [dzbar]
  rw [hid] at hc
  rw [hidb] at hb
  have hJ : (jacobian f x : ℂ) = dz f x * conj (dz f x) - dzbar f x * conj (dzbar f x) := by
    simp only [jacobian, Complex.mul_conj', Complex.ofReal_sub, Complex.ofReal_pow]
  apply (eq_div_iff (by exact_mod_cast hj)).mpr
  rw [hJ]
  linear_combination -(conj (dz f x)) * hc + (conj (dzbar f x)) * hb

theorem bc_inverse_phase {f g : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x))
    (hj : jacobian f x ≠ 0) (he : g ∘ f =ᶠ[𝓝 x] id) :
    conj (dz g (f x)) / dz g (f x) = dz f x / conj (dz f x) := by
  rw [bc_inverse_dz hf hg hj he]
  simp only [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  exact div_div_div_cancel_right₀ (show (jacobian f x : ℂ) ≠ 0 by exact_mod_cast hj) _ _

theorem bc_jacobian_pos {f : ℂ → ℂ} {x : ℂ} (hfz : dz f x ≠ 0)
    (hμ : ‖complexDilatation f x‖ < 1) : 0 < jacobian f x := by
  have hlt : ‖dzbar f x‖ < ‖dz f x‖ := by
    simpa only [complexDilatation, norm_div, div_lt_one (norm_pos_iff.mpr hfz)] using hμ
  unfold jacobian
  nlinarith [norm_nonneg (dz f x), norm_nonneg (dzbar f x)]

theorem bc_invFun_phase_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      conj (dz (Function.invFun (wA μ)) y) / dz (Function.invFun (wA μ)) y =
        (fun x => dz (wA μ) x / conj (dz (wA μ) x)) (Function.invFun (wA μ) y) := by
  filter_upwards [bc_invFun_good_ae hμ, bc_invFun_right_ae hμ,
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ)),
    ae_restrict_mem bc_hEo.measurableSet] with y hg he hf hy
  obtain ⟨hgd, -, -⟩ := hg
  obtain ⟨hfd, hfz, -, hflt⟩ := hf
  have hyn : y ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hy
  have hfn : wA μ (Function.invFun (wA μ) y) ≠ 0 := by rwa [he]
  have hev : ∀ᶠ x in 𝓝 (Function.invFun (wA μ) y), wA μ x ≠ 0 :=
    hfd.continuousAt (eventually_ne_nhds hfn)
  have hleft : Function.invFun (wA μ) ∘ wA μ =ᶠ[𝓝 (Function.invFun (wA μ) y)] id := by
    filter_upwards [hev] with x hx using bc_invFun_wA hx
  have h := bc_inverse_phase hfd (by simpa only [he] using hgd)
    (bc_jacobian_pos hfz hflt).ne' hleft
  simpa only [he] using h

theorem bc_inverse_comp_algebra {m v a : ℂ} (ha : a ≠ 0) :
    (-m * (a / conj a) + v * (a / conj a)) /
        (1 + conj (-m * (a / conj a)) * v * (a / conj a)) =
      (v - m) / (1 - conj m * v) * (a / conj a) := by
  have hca : conj a ≠ 0 := by simpa using ha
  have he : conj (-m * (a / conj a)) * v * (a / conj a) = -(conj m * v) := by
    simp only [map_mul, map_neg, map_div₀, Complex.conj_conj]
    field_simp
    <;> ring
  rw [he]
  change _ / (1 - conj m * v) = _
  ring

/-- Exact inverse-composition formula for the actual finite inverse, before identifying it
with the separately chosen normalized solution for `beltramiInv μ`. -/
theorem bc_raw_inv_comp_dilatation_ae {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      complexDilatation (wA ν ∘ Function.invFun (wA μ)) y =
        (fun x => (ν x - μ x) / (1 - conj (μ x) * ν x) *
          (dz (wA μ) x / conj (dz (wA μ) x))) (Function.invFun (wA μ) y) := by
  filter_upwards [bc_invFun_good_ae hμ, bc_invFun_dilatation_ae hμ,
    bc_invFun_dilatation_bound hμ, bc_invFun_phase_ae hμ,
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hν)),
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ))] with y hg hm hb hp hn hf
  obtain ⟨hgd, hgz, hxE⟩ := hg
  obtain ⟨hnd, hnz, hnm, hnlt⟩ := hn
  have he := eq6_8_complexDilatation_comp hgd hnd hgz hnz
    (hb.trans_lt (bc_norm_lt_one hμ)) hnlt
  rw [hm, hp, hnm, extA_eq_on_exterior ν hxE] at he
  rw [he]
  exact bc_inverse_comp_algebra hf.2.1

theorem bc_invFun_aesm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AEStronglyMeasurable (Function.invFun (wA μ)) (volume.restrict unitDiscExterior) := by
  obtain ⟨V, K, hVo, hVE, hfin, hT, -⟩ := bc_invFun_kqc hμ
  have hnull : ∀ᵐ y : ℂ, y ∉ unitDiscExterior \ V :=
    measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)
  have he : V =ᵐ[volume] unitDiscExterior := by
    filter_upwards [hnull] with y hy
    exact propext ⟨fun h => hVE h, fun h => by by_contra hn; exact hy ⟨h, hn⟩⟩
  rw [← Measure.restrict_congr_set he]
  exact hT.2.2.1.1.aestronglyMeasurable hVo.measurableSet

theorem bc_comp_invFun_aesm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : AEStronglyMeasurable ν (volume.restrict unitDiscExterior)) :
    AEStronglyMeasurable (ν ∘ Function.invFun (wA μ)) (volume.restrict unitDiscExterior) := by
  have h := hν.stronglyMeasurable_mk.measurable.comp_aemeasurable (bc_invFun_aesm hμ).aemeasurable
  apply h.aestronglyMeasurable.congr
  filter_upwards [bc_invFun_pullback_ae hμ hν.ae_eq_mk] with y hy using hy.symm

theorem bc_Rnm_integrand_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ x ∂(volume.restrict unitDiscExterior),
      ‖ν x / (1 - ‖μ x‖ ^ 2) * (dz (wA μ) x / conj (dz (wA μ) x))‖ ≤
        (1 / (1 - ‖μ‖ ^ 2)) * ‖ν‖ := by
  filter_upwards [LinfStar_ae_norm_le ν, LinfStar_ae_norm_le μ,
    ae_restrict_of_ae (bc_wA_ae hμ)] with x hn hm hg
  have hμ1 := bc_norm_lt_one hμ
  have hd : 0 < 1 - ‖μ‖ ^ 2 := by nlinarith [norm_nonneg μ]
  have hx : 0 < 1 - ‖μ x‖ ^ 2 := by nlinarith [norm_nonneg (μ x)]
  have hden : 1 - ‖μ‖ ^ 2 ≤ 1 - ‖μ x‖ ^ 2 := by nlinarith [norm_nonneg (μ x)]
  have he : (1 : ℂ) - (‖μ x‖ : ℂ) ^ 2 = ((1 - ‖μ x‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_mul, norm_div, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hg.2.1), mul_one, he, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx]
  calc ‖ν x‖ / (1 - ‖μ x‖ ^ 2) ≤ ‖ν‖ / (1 - ‖μ‖ ^ 2) := by gcongr
       _ = (1 / (1 - ‖μ‖ ^ 2)) * ‖ν‖ := by ring

theorem bc_Rnm_memLp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    MemLp (fun y => (fun x => ν x / (1 - ‖μ x‖ ^ 2) *
      (dz (wA μ) x / conj (dz (wA μ) x))) (Function.invFun (wA μ) y)) ∞
        (volume.restrict unitDiscExterior) := by
  have hc : AEStronglyMeasurable (fun x => (1 : ℂ) - (‖μ x‖ : ℂ) ^ 2)
      (volume.restrict unitDiscExterior) :=
    aestronglyMeasurable_const.sub
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable μ).norm).pow 2)
  have ht : AEStronglyMeasurable (fun x => dz (wA μ) x / conj (dz (wA μ) x))
      (volume.restrict unitDiscExterior) :=
    ((measurable_dz _).div (continuous_conj.measurable.comp (measurable_dz _))).aestronglyMeasurable
  exact memLp_top_of_bound
    (bc_comp_invFun_aesm hμ (((Lp.aestronglyMeasurable ν).div₀ hc).mul ht))
    ((1 / (1 - ‖μ‖ ^ 2)) * ‖ν‖) (bc_invFun_pullback_ae hμ (bc_Rnm_integrand_bound hμ ν))

theorem bc_Rnm_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), Rnm ν μ y =
      (fun x => ν x / (1 - ‖μ x‖ ^ 2) * (dz (wA μ) x / conj (dz (wA μ) x)))
        (Function.invFun (wA μ) y) :=
  bc_toLinf_ae (bc_Rnm_memLp hμ ν)

theorem bc_Rnm_norm_le {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ‖Rnm ν μ‖ ≤ (1 / (1 - ‖μ‖ ^ 2)) * ‖ν‖ := by
  have hd : 0 < 1 - ‖μ‖ ^ 2 := by
    have := bc_norm_lt_one hμ
    nlinarith [norm_nonneg μ]
  exact norm_toLinf_le_of_ae_bound (by positivity)
    (bc_invFun_pullback_ae hμ (bc_Rnm_integrand_bound hμ ν))

/-- `R(·, μ)` is a bounded complex-linear operator on the original `L∞` quotient. -/
theorem bc_exists_RnmCLM {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ R : LinfStar →L[ℂ] LinfStar, ∀ ν, R ν = Rnm ν μ := by
  let R0 : LinfStar →ₗ[ℂ] LinfStar :=
    { toFun := fun ν => Rnm ν μ
      map_add' := by
        intro ν₁ ν₂
        apply Lp.ext
        filter_upwards [bc_Rnm_ae hμ (ν₁ + ν₂), bc_Rnm_ae hμ ν₁, bc_Rnm_ae hμ ν₂,
          Lp.coeFn_add (Rnm ν₁ μ) (Rnm ν₂ μ),
          bc_invFun_pullback_ae hμ (Lp.coeFn_add ν₁ ν₂)] with y h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h1, h2, h3, h5, Pi.add_apply]
        ring
      map_smul' := by
        intro c ν
        apply Lp.ext
        filter_upwards [bc_Rnm_ae hμ (c • ν), bc_Rnm_ae hμ ν,
          Lp.coeFn_smul c (Rnm ν μ), bc_invFun_pullback_ae hμ (Lp.coeFn_smul c ν)]
          with y h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h3, Pi.smul_apply, h1, h2, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  exact ⟨R0.mkContinuous (1 / (1 - ‖μ‖ ^ 2)) (bc_Rnm_norm_le hμ), fun _ => rfl⟩

theorem bc_raw_inv_comp_memLp {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    MemLp (complexDilatation (wA ν ∘ Function.invFun (wA μ))) ∞
      (volume.restrict unitDiscExterior) := by
  refine memLp_top_of_bound
    (((measurable_dzbar _).div (measurable_dz _)).aestronglyMeasurable) 1 ?_
  filter_upwards [bc_invFun_good_ae hμ, bc_invFun_dilatation_bound hμ,
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hν))] with y hg hb hn
  obtain ⟨hgd, hgz, -⟩ := hg
  obtain ⟨hnd, hnz, -, hnlt⟩ := hn
  rw [eq6_8_complexDilatation_comp hgd hnd hgz hnz
    (hb.trans_lt (bc_norm_lt_one hμ)) hnlt, mul_assoc]
  apply (bc_alg_lt (hb.trans_lt (bc_norm_lt_one hμ)) ?_).le
  rwa [norm_mul, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hgz), mul_one]

/-- Only the normalization identification is assumed here; all a.e. inverse calculus,
membership in `L∞`, and the algebraic composition formula have been proved above. -/
theorem bc_beltramiMul_inv_formula_of_inverse_germ {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hInv : ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      wA (beltramiInv μ) =ᶠ[𝓝 y] Function.invFun (wA μ)) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior), beltramiMul ν (beltramiInv μ) y =
      (fun x => (ν x - μ x) / (1 - conj (μ x) * ν x) *
        (dz (wA μ) x / conj (dz (wA μ) x))) (Function.invFun (wA μ) y) := by
  have he : complexDilatation (wA ν ∘ wA (beltramiInv μ)) =ᵐ[volume.restrict unitDiscExterior]
      complexDilatation (wA ν ∘ Function.invFun (wA μ)) := by
    filter_upwards [hInv] with y hy
    obtain ⟨h1, h2⟩ := t203_c1_dz_congr (hy.fun_comp (wA ν))
    simp only [complexDilatation, h1, h2]
  have hm := (bc_raw_inv_comp_memLp hμ hν).ae_eq he.symm
  filter_upwards [bc_toLinf_ae hm, he, bc_raw_inv_comp_dilatation_ae hμ hν]
    with y h1 h2 h3 using h1.trans (h2.trans h3)

theorem bc_inverse_taylor {m b : ℂ} {δ r : ℝ} (hδ : 0 < δ)
    (hm : ‖m‖ ≤ 1) (hd : δ ≤ 1 - ‖m‖ ^ 2) (hb : ‖b‖ ≤ r) (hr : r ≤ δ / 2) :
    ‖b / (1 - conj m * (m + b)) - b / (1 - (‖m‖ : ℂ) ^ 2)‖ ≤
      2 * r ^ 2 / δ ^ 2 := by
  let d : ℝ := 1 - ‖m‖ ^ 2
  have hdpos : 0 < d := hδ.trans_le hd
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hrc : 0 ≤ r := (norm_nonneg b).trans hb
  have hdcast : (d : ℂ) = 1 - (‖m‖ : ℂ) ^ 2 := by simp [d]
  have he : 1 - conj m * (m + b) = (d : ℂ) - conj m * b := by
    rw [hdcast, mul_add, Complex.conj_mul']
    ring
  have hmb : ‖conj m * b‖ ≤ r := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖m‖ * ‖b‖ ≤ 1 * r := by gcongr
         _ = r := one_mul _
  have hdn : ‖(d : ℂ)‖ = d := by simp [abs_of_pos hdpos]
  have heNorm : δ / 2 ≤ ‖(d : ℂ) - conj m * b‖ := by
    have h := norm_sub_norm_le (d : ℂ) (conj m * b)
    rw [hdn] at h
    linarith
  have he0 : (d : ℂ) - conj m * b ≠ 0 :=
    norm_pos_iff.mp ((half_pos hδ).trans_le heNorm)
  rw [he, ← hdcast]
  have hrem : b / ((d : ℂ) - conj m * b) - b / (d : ℂ) =
      conj m * b ^ 2 / ((d : ℂ) * ((d : ℂ) - conj m * b)) := by
    rw [div_sub_div b b he0 hdc]
    congr 1 <;> ring
  rw [hrem, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_conj, hdn]
  calc ‖m‖ * ‖b‖ ^ 2 / (d * ‖(d : ℂ) - conj m * b‖) ≤
        1 * r ^ 2 / (δ * (δ / 2)) := by gcongr
       _ = 2 * r ^ 2 / δ ^ 2 := by field_simp <;> ring

theorem bc_inverse_translation_remainder {μ h : LinfStar} (hμ : μ ∈ LinfStarBall)
    (hInv : ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      wA (beltramiInv μ) =ᶠ[𝓝 y] Function.invFun (wA μ))
    (hh : ‖h‖ ≤ min ((1 - ‖μ‖) / 2) ((1 - ‖μ‖ ^ 2) / 2)) :
    ‖beltramiMul (μ + h) (beltramiInv μ) - Rnm h μ‖ ≤
      2 * ‖h‖ ^ 2 / (1 - ‖μ‖ ^ 2) ^ 2 := by
  have hμ1 := bc_norm_lt_one hμ
  have hd : 0 < 1 - ‖μ‖ ^ 2 := by nlinarith [norm_nonneg μ]
  have hl : μ + h ∈ LinfStarBall := by
    have hbound : ‖μ + h‖ < 1 := (norm_add_le μ h).trans_lt (by
      have := (le_min_iff.mp hh).1
      linarith)
    simpa [LinfStarBall] using hbound
  refine bc_Lp_norm_le _ (by positivity) ?_
  filter_upwards [bc_beltramiMul_inv_formula_of_inverse_germ hμ hl hInv,
    bc_Rnm_ae hμ h, Lp.coeFn_sub (beltramiMul (μ + h) (beltramiInv μ)) (Rnm h μ),
    bc_invFun_pullback_ae hμ (Lp.coeFn_add μ h),
    bc_invFun_pullback_ae hμ (LinfStar_ae_norm_le μ),
    bc_invFun_pullback_ae hμ (LinfStar_ae_norm_le h),
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ))]
      with y h1 h2 h3 h4 hm hb hg
  rw [h3, Pi.sub_apply, h1, h2, h4, Pi.add_apply, add_sub_cancel_left, ← sub_mul, norm_mul]
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hg.2.1), mul_one]
  apply bc_inverse_taylor hd (hm.trans hμ1.le) _ hb (le_min_iff.mp hh).2
  nlinarith [norm_nonneg (μ (Function.invFun (wA μ) y))]

theorem bc_eq_1_5_of_inverse_germ {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar)
    (hInv : ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      wA (beltramiInv μ) =ᶠ[𝓝 y] Function.invFun (wA μ)) :
    fderiv ℂ (fun l => beltramiMul l (beltramiInv μ)) μ ν = Rnm ν μ := by
  obtain ⟨R, hR⟩ := bc_exists_RnmCLM hμ
  have hμ1 := bc_norm_lt_one hμ
  have hgap : 0 < (1 - ‖μ‖) / 2 := half_pos (sub_pos.mpr hμ1)
  have hd : 0 < 1 - ‖μ‖ ^ 2 := by nlinarith [norm_nonneg μ]
  have hbase : beltramiMul μ (beltramiInv μ) = 0 := by
    have h := bc_inverse_translation_remainder (h := 0) hμ hInv
      (by simp only [norm_zero]; exact le_min hgap.le (half_pos hd).le)
    rw [← hR, map_zero] at h
    simpa using h
  have hder : HasFDerivAt (fun l => beltramiMul l (beltramiInv μ)) R μ := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    have hrad : 0 < min (min ((1 - ‖μ‖) / 2) ((1 - ‖μ‖ ^ 2) / 2))
        (c * (1 - ‖μ‖ ^ 2) ^ 2 / 2) := by positivity
    have hev : ∀ᶠ h : LinfStar in 𝓝 0,
        ‖h‖ < min (min ((1 - ‖μ‖) / 2) ((1 - ‖μ‖ ^ 2) / 2))
          (c * (1 - ‖μ‖ ^ 2) ^ 2 / 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : LinfStar) hrad] with h hh
      simpa only [mem_ball, dist_zero_right] using hh
    filter_upwards [hev] with h hh
    rw [hbase, sub_zero, hR]
    refine (bc_inverse_translation_remainder hμ hInv (lt_min_iff.mp hh).1.le).trans ?_
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hh2 := (lt_min_iff.mp hh).2.le
    nlinarith [norm_nonneg h, mul_le_mul_of_nonneg_right hh2 (norm_nonneg h)]
  rw [hder.fderiv, hR]

theorem bc_inverse_left_comp_dilatation_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ x ∂(volume.restrict unitDiscExterior),
      complexDilatation (wA (beltramiInv μ) ∘ wA μ) x = 0 := by
  filter_upwards [bc_comp_dilatation_ae (bc_beltramiInv_mem_ball hμ) hμ,
    bc_pullback_ae hμ (bc_beltramiInv_ae hμ),
    bc_pullback_ae hμ (ae_restrict_mem bc_hEo.measurableSet),
    ae_restrict_of_ae (bc_wA_ae hμ)] with x hc hi hx hg
  have hn : wA μ x ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hx
  rw [bc_invFun_wA hn] at hi
  rw [hc, hi]
  have hz := hg.2.1
  have hcz : conj (dz (wA μ) x) ≠ 0 := by simpa using hz
  have he : -μ x * (dz (wA μ) x / conj (dz (wA μ) x)) *
      (conj (dz (wA μ) x) / dz (wA μ) x) = -μ x := by
    field_simp
  rw [he, add_neg_cancel, zero_div]

theorem bc_comp_kqc {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∃ (U : Set ℂ) (K : ℝ), IsOpen U ∧ U ⊆ unitDiscExterior ∧
      (unitDiscExterior \ U).Finite ∧ IsKQC (wA ν ∘ wA μ) U K ∧
      ∀ x ∈ U, (wA ν ∘ wA μ) x ∈ unitDiscExterior ∧
        wAS ν (wAS μ (x : ExtPlane)) = ((wA ν (wA μ x) : ℂ) : ExtPlane) := by
  obtain ⟨U, K, hUo, hUE, hUf, hT, hTm⟩ := bc_wA_kqc hμ
  obtain ⟨V, L, hVo, hVE, hVf, hS, hSm⟩ := bc_wA_kqc hν
  let W := U ∩ wA μ ⁻¹' V
  have hWo : IsOpen W := hT.2.2.1.1.isOpen_inter_preimage hUo hVo
  have hpre : (wA μ ⁻¹' (unitDiscExterior \ V)).Finite := by
    apply hVf.finite.preimage
    intro x hx y hy he
    apply bc_wA_inj_of_ne_zero he
    intro hz
    have := hx.1
    norm_num [hz, unitDiscExterior] at this
  have hWf : (unitDiscExterior \ W).Finite := by
    apply (hUf.finite.union hpre).subset
    intro x hx
    by_cases hu : x ∈ U
    · exact Or.inr ⟨hTm ⟨x, hu, rfl⟩, fun hv => hx.2 ⟨hu, hv⟩⟩
    · exact Or.inl ⟨hx.1, hu⟩
  have hTW : IsKQC (wA μ) W K := t3b_isKQC_restrict hT hWo inter_subset_left
  have hcomp := thm7_1_comp hTW hS (show wA μ '' W ⊆ V from by
    rintro _ ⟨x, hx, rfl⟩; exact hx.2)
  refine ⟨W, K * L, hWo, fun x hx => hUE hx.1, hWf, hcomp, ?_⟩
  intro x hx
  have hfx := hTm ⟨x, hx.1, rfl⟩
  have hgfx := hSm ⟨wA μ x, hx.2, rfl⟩
  have hfn : wA μ x ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hfx
  have hgn : wA ν (wA μ x) ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at hgfx
  exact ⟨hgfx, by rw [bc_wAS_eq_coe_of_wA_ne_zero hfn, bc_wAS_eq_coe_of_wA_ne_zero hgn]⟩

theorem bc_inverse_left_comp_holomorphic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ U : Set ℂ, IsOpen U ∧ U ⊆ unitDiscExterior ∧ (unitDiscExterior \ U).Finite ∧
      DifferentiableOn ℂ (wA (beltramiInv μ) ∘ wA μ) U ∧
      ∀ x ∈ U, (wA (beltramiInv μ) ∘ wA μ) x ∈ unitDiscExterior ∧
        wAS (beltramiInv μ) (wAS μ (x : ExtPlane)) =
          ((wA (beltramiInv μ) (wA μ x) : ℂ) : ExtPlane) := by
  obtain ⟨U, K, hUo, hUE, hUf, hT, hdata⟩ := bc_comp_kqc hμ (bc_beltramiInv_mem_ball hμ)
  exact ⟨U, hUo, hUE, hUf, nx_differentiableOn_of_dilatation_zero hT
    (ae_restrict_of_ae_restrict_of_subset hUE (bc_inverse_left_comp_dilatation_zero hμ)), hdata⟩

/-- Transfer exterior holomorphy, with finitely many coordinate exceptions, to the disk. -/
theorem bc_sigma_conjugate_holomorphic {F : ExtPlane → ExtPlane} (hFc : Continuous F)
    (hFm : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p ∉ toExt (closedBall (0 : ℂ) 1))
    {f : ℂ → ℂ} {U : Set ℂ} (hUf : (unitDiscExterior \ U).Finite)
    (hf : DifferentiableOn ℂ f U)
    (hdata : ∀ x ∈ U, f x ∈ unitDiscExterior ∧ F (x : ExtPlane) = (f x : ExtPlane)) :
    DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc := by
  let c : ℂ → ℂ := fun w => finPart (mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))))
  have hc : ∀ w ∈ unitDisc, (c w : ExtPlane) =
      mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))) := by
    intro w hw
    obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hFm _ (sigma_not_closed hw))
    simp only [c, hy, finPart_coe]
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hcc : ContinuousOn c unitDisc := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.continuousOn_iff]
    exact (hσc.comp (hFc.comp (hσc.comp OnePoint.continuous_coe))).continuousOn.congr hc
  let Ω : Set ℂ := {w | w ∈ unitDisc ∧ w ≠ 0 ∧ w⁻¹ ∈ U}
  have hΩf : (unitDisc \ Ω).Finite := by
    apply ((finite_singleton (0 : ℂ)).union (hUf.image (fun z : ℂ => z⁻¹))).subset
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    · apply Or.inr
      have hwE : w⁻¹ ∈ unitDiscExterior := by
        show 1 < ‖w⁻¹‖
        rw [norm_inv, inv_eq_one_div, one_lt_div (norm_pos_iff.mpr hw0)]
        exact mem_ball_zero_iff.mp hw.1
      exact ⟨w⁻¹, ⟨hwE, fun hu => hw.2 ⟨hw.1, hw0, hu⟩⟩, inv_inv w⟩
  have hi : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω :=
    differentiableOn_id.inv (fun w hw => hw.2.1)
  have hcf : DifferentiableOn ℂ (fun w : ℂ => (f w⁻¹)⁻¹) Ω :=
    (hf.comp hi (fun w hw => hw.2.2)).inv (by
      intro w hw he
      dsimp only [Function.comp_apply] at he
      have h := (hdata _ hw.2.2).1
      norm_num [he, unitDiscExterior] at h)
  have hdΩ : DifferentiableOn ℂ c Ω := hcf.congr (by
    intro w hw
    have hn : f w⁻¹ ≠ 0 := by
      intro he
      have h := (hdata _ hw.2.2).1
      norm_num [he, unitDiscExterior] at h
    simp only [c, sigma_coe hw.2.1, (hdata _ hw.2.2).2, sigma_coe hn, finPart_coe])
  apply differentiableOn_of_finite_exceptional isOpen_ball hΩf hcc
  exact hdΩ.mono (fun w hw => by by_contra h; exact hw.2 ⟨hw.1, h⟩)

/-- A sphere map conformal on the exterior and fixing the three normalization points
is the identity on the exterior, including infinity. -/
theorem bc_exterior_rigidity {F : ExtPlane → ExtPlane} (hFc : Continuous F)
    (hFi : Function.Injective F)
    (hFm : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p ∉ toExt (closedBall (0 : ℂ) 1))
    (hFs : ∀ q ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), F p = q)
    (hfix1 : F ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane))
    (hfixI : F ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane))
    (hfix2 : F ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane))
    (hdiff : DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc) :
    ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p = p := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  let c : ℂ → ℂ := fun w => finPart (mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))))
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hFm _ (sigma_not_closed hw))
    have hcy : c w = y := by simp only [c, hy, finPart_coe]
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    exact OnePoint.coe_injective (hσi (hFi (hσi (e1.trans e2.symm))))
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hFs _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff, hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    change mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hw).1, mobiusExt_coe hwZ]
    exact congrArg (fun z : ℂ => (z : ExtPlane)) (heq hw)
  have hcl := EqOn.closure hagree (hσc.comp (hFc.comp hσc)) hmc
  have hball : closedBall (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
    have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
      hZd.open_subset_closure_inter isOpen_ball
    have h := closure_minimal hsub isClosed_closure
    rwa [closure_ball _ one_ne_zero] at h
  have hclosed : ∀ w ∈ closedBall (0 : ℂ) 1,
      mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))) = mobiusExt A B C D (w : ExtPlane) := by
    intro w hw
    exact hcl ((image_closure_subset_closure_image OnePoint.continuous_coe) ⟨w, hball hw, rfl⟩)
  have hMid : mobiusExt A B C D = id := by
    refine mobius_fixes_three (p₁ := -1) (p₂ := I) (p₃ := 1) hdet ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; have := congrArg Complex.re h; norm_num at this
    · norm_num
    · intro h; have := congrArg Complex.re h; norm_num at this
    · rw [← hclosed (-1) (by simp), sigma_coe (by norm_num)]
      norm_num only [inv_neg, inv_one]
      rw [hfix1, sigma_coe (by norm_num)]
      norm_num
    · rw [← hclosed I (by simp), sigma_coe Complex.I_ne_zero]
      have hi : (I : ℂ)⁻¹ = -I := by simp
      rw [hi, hfixI, sigma_coe (neg_ne_zero.mpr Complex.I_ne_zero)]
      simp
    · rw [← hclosed 1 (by simp), sigma_coe one_ne_zero, inv_one, hfix2,
        sigma_coe one_ne_zero, inv_one]
  intro p hp
  obtain ⟨w, hwp, hw⟩ := sigma_of_not_closed hp
  have h := hclosed w (mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hw).le)
  rw [hMid] at h
  change mobiusExt 0 1 1 0 (F (mobiusExt 0 1 1 0 (w : ExtPlane))) = (w : ExtPlane) at h
  rw [← hwp, sigma_invol] at h
  exact hσi h

theorem bc_inverse_left_sphere_exterior {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ p ∉ toExt (closedBall (0 : ℂ) 1), wAS (beltramiInv μ) (wAS μ p) = p := by
  have hi := bc_beltramiInv_mem_ball hμ
  let F := wAS (beltramiInv μ) ∘ wAS μ
  have hFc : Continuous F := (wAS_continuous hi).comp (wAS_continuous hμ)
  have hFb : Function.Bijective F := (wAS_bijective (beltramiInv μ)).comp (wAS_bijective μ)
  have hFiff : ∀ p, p ∈ toExt (closedBall (0 : ℂ) 1) ↔ F p ∈ toExt (closedBall (0 : ℂ) 1) :=
    fun p => (wAS_closed_iff hμ p).trans (wAS_closed_iff hi (wAS μ p))
  have hFm : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p ∉ toExt (closedBall (0 : ℂ) 1) :=
    fun p hp => fun h => hp ((hFiff p).mpr h)
  have hFs : ∀ q ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), F p = q := by
    intro q hq
    obtain ⟨p, hp⟩ := hFb.2 q
    exact ⟨p, fun h => hq (hp ▸ (hFiff p).mp h), hp⟩
  obtain ⟨U, hUo, hUE, hUf, hf, hdata⟩ := bc_inverse_left_comp_holomorphic hμ
  have hdiff := bc_sigma_conjugate_holomorphic hFc hFm hUf hf hdata
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  obtain ⟨N, hN, V, hV, hvf, hvi, hn1, hnI, hn2⟩ := wA_spec hi
  exact bc_exterior_rigidity hFc hFb.1 hFm hFs
    (by rw [hm1, hn1]) (by rw [hmI, hnI])
    (by rw [hm2, hn2]) hdiff

/-- The chosen normalized inverse and the ordinary finite inverse have the same germ a.e. -/
theorem bc_inverse_germ {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ᵐ y ∂(volume.restrict unitDiscExterior),
      wA (beltramiInv μ) =ᶠ[𝓝 y] Function.invFun (wA μ) := by
  obtain ⟨U, K, hUo, hUE, hUf, hT, hTm⟩ := bc_wA_kqc hμ
  have hVo : IsOpen (wA μ '' U) := isOpen_image_of_isKQC hT
  have heq : EqOn (wA (beltramiInv μ)) (Function.invFun (wA μ)) (wA μ '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    have hyn : wA μ x ≠ 0 := by
      intro he
      have h := hTm ⟨x, hx, rfl⟩
      norm_num [he, unitDiscExterior] at h
    rw [bc_invFun_wA hyn]
    have hp : (x : ExtPlane) ∉ toExt (closedBall (0 : ℂ) 1) := by
      rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le]
      exact hUE hx
    have h := bc_inverse_left_sphere_exterior hμ (x : ExtPlane) hp
    rw [bc_wAS_eq_coe_of_wA_ne_zero hyn] at h
    exact congrArg finPart h
  have hnull : ∀ᵐ y : ℂ, y ∉ unitDiscExterior \ wA μ '' U :=
    measure_eq_zero_iff_ae_notMem.mp ((bc_wA_image_compl_finite hμ hUf.finite).measure_zero volume)
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem bc_hEo.measurableSet] with y hn hy
  have hv : y ∈ wA μ '' U := by by_contra h; exact hn ⟨hy, h⟩
  exact Filter.eventuallyEq_of_mem (hVo.mem_nhds hv) (fun z hz => heq hz)

theorem bc_beltramiMul_inv_formula {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      beltramiMul ν (beltramiInv μ) z =
        (fun u => (ν u - μ u) / (1 - conj (μ u) * ν u) * (dz (wA μ) u / conj (dz (wA μ) u)))
          (Function.invFun (wA μ) z) :=
  bc_beltramiMul_inv_formula_of_inverse_germ hμ hν (bc_inverse_germ hμ)

theorem bc_eq_1_5 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    fderiv ℂ (fun l => beltramiMul l (beltramiInv μ)) μ ν = Rnm ν μ :=
  bc_eq_1_5_of_inverse_germ hμ ν (bc_inverse_germ hμ)

end TakhtajanTeo
