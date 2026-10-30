import TakhtajanTeo.Ch1.BeltramiCompose

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Group structure of Model A (`bg_` prefix) -/

/-- Off the unit circle, a sphere self-map that commutes with reflection and is the identity on `{|p| > 1} ∪ {∞}`
is the identity. -/
theorem bg_sigma_mem_ext {q : ExtPlane} (hq : q ∈ toExt (ball (0 : ℂ) 1)) :
    mobiusExt 0 1 1 0 (OnePoint.map conj q) ∉ toExt (closedBall (0 : ℂ) 1) := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  by_cases hz0 : z = 0
  · subst hz0
    rw [rho_zero]
    exact infty_notMem_toExt _
  · rw [rho_coe hz0]
    rw [coe_mem_toExt_iff, mem_closedBall_zero_iff, not_le, norm_refl]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1

/-- A continuous sphere self-map commuting with the reflection `z ↦ 1/z̄` and equal to the identity on
`{|p| > 1} ∪ {∞}` is the identity. -/
theorem bg_eq_id_of_exterior {F : ExtPlane → ExtPlane} (hFc : Continuous F)
    (hcomm : ∀ q, F (mobiusExt 0 1 1 0 (OnePoint.map conj q)) =
      mobiusExt 0 1 1 0 (OnePoint.map conj (F q)))
    (hext : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), F p = p) (p : ExtPlane) : F p = p := by
  have hσσ : ∀ q : ExtPlane, mobiusExt 0 1 1 0 (OnePoint.map conj
      (mobiusExt 0 1 1 0 (OnePoint.map conj q))) = q := rho_invol
  have hdisc : ∀ q ∈ toExt (ball (0 : ℂ) 1), F q = q := by
    intro q hq
    have h1 := hext _ (bg_sigma_mem_ext hq)
    have h2 := hcomm (mobiusExt 0 1 1 0 (OnePoint.map conj q))
    rw [hσσ, h1, hσσ] at h2
    exact h2
  have hoff : ∀ q : ExtPlane, q ∉ toExt unitCircle → F q = q := by
    intro q hq
    by_cases hb : q ∈ toExt (closedBall (0 : ℂ) 1)
    · obtain ⟨z, hz, rfl⟩ := hb
      have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      have hz2 : ‖z‖ ≠ 1 := fun h => hq ⟨z, h, rfl⟩
      exact hdisc _ ⟨z, mem_ball_zero_iff.mpr (lt_of_le_of_ne hz1 hz2), rfl⟩
    · exact hext q hb
  by_cases hc : p ∈ toExt unitCircle
  · obtain ⟨z, hz, rfl⟩ := hc
    have hz1 : ‖z‖ = 1 := hz
    let s : ℕ → ℂ := fun n => ((1 : ℂ) + 1 / ((n : ℂ) + 1)) * z
    have hs : Tendsto s atTop (𝓝 z) := by
      have h : Tendsto (fun n : ℕ => (1 : ℂ) + 1 / ((n : ℂ) + 1)) atTop (𝓝 ((1 : ℂ) + 0)) := by
        refine tendsto_const_nhds.add ?_
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa using this
      have h' := h.mul_const z
      show Tendsto (fun n : ℕ => ((1 : ℂ) + 1 / ((n : ℂ) + 1)) * z) atTop (𝓝 z)
      simpa only [add_zero, one_mul] using h'
    have hsE : ∀ n, ((s n : ℂ) : ExtPlane) ∉ toExt unitCircle := by
      intro n hn
      rw [coe_mem_toExt_iff] at hn
      have hn1 : ‖s n‖ = 1 := hn
      have hn2 : ‖s n‖ = ‖(1 : ℂ) + 1 / ((n : ℂ) + 1)‖ := by
        simp only [s, norm_mul, hz1, mul_one]
      have hgt : (1 : ℝ) < ‖(1 : ℂ) + 1 / ((n : ℂ) + 1)‖ := by
        have hr : (1 : ℂ) + 1 / ((n : ℂ) + 1) = (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      linarith
    have hlim : Tendsto (fun n => F ((s n : ℂ) : ExtPlane)) atTop (𝓝 (F (z : ExtPlane))) :=
      (hFc.tendsto _).comp ((OnePoint.continuous_coe.tendsto z).comp hs)
    have hlim' : Tendsto (fun n => F ((s n : ℂ) : ExtPlane)) atTop (𝓝 (z : ExtPlane)) := by
      have : (fun n => F ((s n : ℂ) : ExtPlane)) = fun n => ((s n : ℂ) : ExtPlane) :=
        funext fun n => hoff _ (hsE n)
      rw [this]
      exact (OnePoint.continuous_coe.tendsto z).comp hs
    exact tendsto_nhds_unique hlim hlim'
  · exact hoff p hc

/-- The inverse law on the whole sphere: `w_{μ⁻¹} ∘ w_μ = id`. -/
theorem bg_inverse_left_sphere {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (p : ExtPlane) :
    wAS (beltramiInv μ) (wAS μ p) = p := by
  have hi := bc_beltramiInv_mem_ball hμ
  refine bg_eq_id_of_exterior (F := fun q => wAS (beltramiInv μ) (wAS μ q))
    ((wAS_continuous hi).comp (wAS_continuous hμ)) ?_ (bc_inverse_left_sphere_exterior hμ) p
  intro q
  show wAS (beltramiInv μ) (wAS μ _) = _
  rw [wAS_refl_comm hμ, wAS_refl_comm hi]

/-- The right-inverse law. -/
theorem bg_inverse_right_sphere {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (p : ExtPlane) :
    wAS μ (wAS (beltramiInv μ) p) = p := by
  obtain ⟨q, rfl⟩ := (wAS_bijective μ).2 p
  rw [bg_inverse_left_sphere hμ q]


/-! ### The product stays in the ball, and its coefficient is the dilatation of `w_ν ∘ w_μ` -/

theorem bg_alg_bound {m b : ℂ} {r s : ℝ} (hm : ‖m‖ ≤ r) (hb : ‖b‖ ≤ s) (hr : r < 1) (hs : s < 1) :
    ‖(m + b) / (1 + conj m * b)‖ ^ 2 ≤ 1 - (1 - r ^ 2) * (1 - s ^ 2) / 4 := by
  have hm0 := norm_nonneg m
  have hb0 := norm_nonneg b
  have hm1 : ‖m‖ < 1 := lt_of_le_of_lt hm hr
  have hb1 : ‖b‖ < 1 := lt_of_le_of_lt hb hs
  have hq : ‖conj m * b‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]; nlinarith
  have hden : 1 + conj m * b ≠ 0 := by
    intro h
    have h1 : conj m * b = -1 := by linear_combination h
    rw [h1] at hq; simp at hq
  have key : ‖1 + conj m * b‖ ^ 2 - ‖m + b‖ ^ 2 = (1 - ‖m‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hD : 0 < ‖1 + conj m * b‖ ^ 2 := by
    have := norm_pos_iff.mpr hden
    positivity
  have hD4 : ‖1 + conj m * b‖ ^ 2 ≤ 4 := by
    have h2 : ‖1 + conj m * b‖ ≤ 2 := by
      have := norm_add_le (1 : ℂ) (conj m * b)
      rw [norm_one] at this
      linarith
    nlinarith [norm_nonneg (1 + conj m * b)]
  have hr0 : 0 ≤ r := hm0.trans hm
  have hs0 : 0 ≤ s := hb0.trans hb
  have hY : 0 ≤ (1 - r ^ 2) * (1 - s ^ 2) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  have hX : (1 - r ^ 2) * (1 - s ^ 2) ≤ (1 - ‖m‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    apply mul_le_mul (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  rw [norm_div, div_pow, div_le_iff₀ hD]
  nlinarith [mul_nonneg hY (sub_nonneg.2 hD4)]

theorem bg_mul_bound {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation (wA ν ∘ wA μ) z‖ ≤
        Real.sqrt (1 - (1 - ‖μ‖ ^ 2) * (1 - ‖ν‖ ^ 2) / 4) := by
  have hμ1 := bc_norm_lt_one hμ
  have hν1 := bc_norm_lt_one hν
  filter_upwards [bc_comp_dilatation_ae hν hμ, LinfStar_ae_norm_le μ,
    bc_pullback_ae hμ (LinfStar_ae_norm_le ν), ae_restrict_of_ae (bc_wA_ae hμ)] with z hc hm hn hg
  obtain ⟨-, hdz, -, -⟩ := hg
  have hτ : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hdz)]
  rw [hc, mul_assoc (conj (μ z))]
  have hb : ‖ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)‖ ≤ ‖ν‖ := by
    rw [norm_mul, hτ, mul_one]; exact hn
  have h := bg_alg_bound hm hb hμ1 hν1
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans h)).mpr h

theorem bg_mul_sqrt_lt {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    Real.sqrt (1 - (1 - ‖μ‖ ^ 2) * (1 - ‖ν‖ ^ 2) / 4) < 1 := by
  have hμ1 := bc_norm_lt_one hμ
  have hν1 := bc_norm_lt_one hν
  have hm0 := norm_nonneg μ
  have hn0 := norm_nonneg ν
  have hY : 0 < (1 - ‖μ‖ ^ 2) * (1 - ‖ν‖ ^ 2) := mul_pos (by nlinarith) (by nlinarith)
  rw [Real.sqrt_lt' one_pos]
  linarith

theorem bg_mul_memLp {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    MemLp (complexDilatation (wA ν ∘ wA μ)) ∞ (volume.restrict unitDiscExterior) :=
  memLp_top_of_bound ((measurable_dzbar _).div (measurable_dz _)).aestronglyMeasurable _
    (bg_mul_bound hμ hν)

theorem bg_mul_ae {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      beltramiMul ν μ z = complexDilatation (wA ν ∘ wA μ) z :=
  bc_toLinf_ae (bg_mul_memLp hμ hν)

theorem bg_mul_mem_ball {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    beltramiMul ν μ ∈ LinfStarBall := by
  have h := norm_toLinf_le_of_ae_bound (Real.sqrt_nonneg _) (bg_mul_bound hμ hν)
  have h2 := h.trans_lt (bg_mul_sqrt_lt hμ hν)
  simpa [LinfStarBall, beltramiMul] using h2

/-! ### Cofinite quasiconformal data for sphere maps -/

theorem bg_good_wA {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (U : Set ℂ) (K : ℝ), IsOpen U ∧ U ⊆ unitDiscExterior ∧ (unitDiscExterior \ U).Finite ∧
      IsKQC (wA μ) U K ∧ ∀ x ∈ U, wA μ x ∈ unitDiscExterior ∧
        wAS μ (x : ExtPlane) = ((wA μ x : ℂ) : ExtPlane) := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  refine ⟨U, K, hUo, hUE, hsub.finite, hT, fun x hx => ?_⟩
  have h := hTmaps ⟨x, hx, rfl⟩
  have hn : wA μ x ≠ 0 := by intro he; norm_num [he, unitDiscExterior] at h
  exact ⟨h, bc_wAS_eq_coe_of_wA_ne_zero hn⟩

theorem bg_kqc_comp {f g : ℂ → ℂ} {Sf Sg : ExtPlane → ExtPlane}
    (hf : ∃ (U : Set ℂ) (K : ℝ), IsOpen U ∧ U ⊆ unitDiscExterior ∧ (unitDiscExterior \ U).Finite ∧
      IsKQC f U K ∧ ∀ x ∈ U, f x ∈ unitDiscExterior ∧ Sf (x : ExtPlane) = ((f x : ℂ) : ExtPlane))
    (hg : ∃ (V : Set ℂ) (L : ℝ), IsOpen V ∧ V ⊆ unitDiscExterior ∧ (unitDiscExterior \ V).Finite ∧
      IsKQC g V L ∧ ∀ x ∈ V, g x ∈ unitDiscExterior ∧ Sg (x : ExtPlane) = ((g x : ℂ) : ExtPlane)) :
    ∃ (W : Set ℂ) (M : ℝ), IsOpen W ∧ W ⊆ unitDiscExterior ∧ (unitDiscExterior \ W).Finite ∧
      IsKQC (g ∘ f) W M ∧ ∀ x ∈ W, (g ∘ f) x ∈ unitDiscExterior ∧
        (Sg ∘ Sf) (x : ExtPlane) = (((g ∘ f) x : ℂ) : ExtPlane) := by
  obtain ⟨U, K, hUo, hUE, hUf, hT, hTd⟩ := hf
  obtain ⟨V, L, hVo, hVE, hVf, hS, hSd⟩ := hg
  let W := U ∩ f ⁻¹' V
  have hWo : IsOpen W := hT.2.2.1.1.isOpen_inter_preimage hUo hVo
  have hpre : (U ∩ f ⁻¹' (unitDiscExterior \ V)).Finite := by
    apply Set.Finite.of_finite_image (f := f)
    · apply hVf.subset
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · exact hT.2.2.1.2.1.mono inter_subset_left
  have hWf : (unitDiscExterior \ W).Finite := by
    apply (hUf.union hpre).subset
    intro x hx
    by_cases hu : x ∈ U
    · exact Or.inr ⟨hu, (hTd x hu).1, fun hv => hx.2 ⟨hu, hv⟩⟩
    · exact Or.inl ⟨hx.1, hu⟩
  have hTW : IsKQC f W K := t3b_isKQC_restrict hT hWo inter_subset_left
  have hcomp := thm7_1_comp hTW hS (show f '' W ⊆ V from by
    rintro _ ⟨x, hx, rfl⟩; exact hx.2)
  refine ⟨W, K * L, hWo, fun x hx => hUE hx.1, hWf, hcomp, ?_⟩
  intro x hx
  obtain ⟨hfE, hfS⟩ := hTd x hx.1
  obtain ⟨hgE, hgS⟩ := hSd (f x) hx.2
  exact ⟨hgE, by simp only [Function.comp_apply]; rw [hfS, hgS]⟩

/-- The composition law for `g ∘ w_μ` with an arbitrary outer map known almost everywhere. -/
theorem bg_comp_dilatation_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {g κ : ℂ → ℂ}
    (hP : ∀ᵐ u ∂(volume.restrict unitDiscExterior), DifferentiableAt ℝ g u ∧ dz g u ≠ 0 ∧
      complexDilatation g u = κ u ∧ ‖complexDilatation g u‖ < 1) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation (g ∘ wA μ) z =
        (μ z + κ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
          (1 + conj (μ z) * κ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) := by
  obtain ⟨U, K, hUo, hUE, hsub, hT, hTmaps⟩ := bc_wA_kqc hμ
  have hpull := s23_c2_ae_pullback hT hTmaps hP
  rw [ae_restrict_iff' hUo.measurableSet] at hpull
  have hnull : ∀ᵐ z : ℂ, z ∉ unitDiscExterior \ U :=
    measure_eq_zero_iff_ae_notMem.mp (Set.Subsingleton.measure_zero hsub volume)
  filter_upwards [ae_restrict_of_ae hpull, ae_restrict_of_ae hnull,
    ae_restrict_of_ae (bc_wA_ae hμ), ae_restrict_mem bc_hEo.measurableSet]
    with z h1 h2 h3 hE
  have hzU : z ∈ U := by
    by_contra h; exact h2 ⟨hE, h⟩
  obtain ⟨hPd, hPz, hPdil, hPlt⟩ := h1 hzU
  obtain ⟨h3d, h3z, h3dil, h3lt⟩ := h3
  have hdilT : complexDilatation (wA μ) z = μ z := by rw [h3dil]; exact extA_eq_on_exterior μ hE
  rw [eq6_8_complexDilatation_comp h3d hPd h3z hPz h3lt hPlt, hdilT, hPdil]

theorem bg_outer_data {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ u ∂(volume.restrict unitDiscExterior), DifferentiableAt ℝ (wA ν ∘ wA μ) u ∧
      dz (wA ν ∘ wA μ) u ≠ 0 ∧ complexDilatation (wA ν ∘ wA μ) u = beltramiMul ν μ u ∧
      ‖complexDilatation (wA ν ∘ wA μ) u‖ < 1 := by
  obtain ⟨U, K, hUo, hUE, hUf, hT, -⟩ := bc_comp_kqc hμ hν
  have hg := s23_c2_ae_good hT
  rw [ae_restrict_iff' hUo.measurableSet] at hg
  have hnull : ∀ᵐ z : ℂ, z ∉ unitDiscExterior \ U :=
    measure_eq_zero_iff_ae_notMem.mp (hUf.measure_zero volume)
  filter_upwards [ae_restrict_of_ae hg, ae_restrict_of_ae hnull,
    ae_restrict_mem bc_hEo.measurableSet, bg_mul_ae hμ hν, bg_mul_bound hμ hν]
    with z h1 h2 hE h3 h4
  have hzU : z ∈ U := by by_contra h; exact h2 ⟨hE, h⟩
  obtain ⟨hd, hlt, -⟩ := h1 hzU
  refine ⟨hd, ?_, h3.symm, lt_of_le_of_lt h4 (bg_mul_sqrt_lt hμ hν)⟩
  intro he
  rw [he, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

/-- `(w_ν ∘ w_μ) ∘ w_{(ν*μ)⁻¹}` is conformal almost everywhere on the exterior. -/
theorem bg_F_dilatation_zero {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation ((wA ν ∘ wA μ) ∘ wA (beltramiInv (beltramiMul ν μ))) z = 0 := by
  have hρ := bg_mul_mem_ball hμ hν
  have hι := bc_beltramiInv_mem_ball hρ
  filter_upwards [bg_comp_dilatation_ae hι (bg_outer_data hμ hν), bc_beltramiInv_ae hρ,
    bc_inverse_germ hρ, bc_invFun_phase_ae hρ] with z hc hinv hgerm hph
  have hx : wA (beltramiInv (beltramiMul ν μ)) z = Function.invFun (wA (beltramiMul ν μ)) z :=
    hgerm.self_of_nhds
  have hdz : dz (wA (beltramiInv (beltramiMul ν μ))) z =
      dz (Function.invFun (wA (beltramiMul ν μ))) z := (t203_c1_dz_congr hgerm).1
  rw [hc, hx, hdz, hph, hinv]
  have hz0 : (-(beltramiMul ν μ) (Function.invFun (wA (beltramiMul ν μ)) z) *
        (dz (wA (beltramiMul ν μ)) (Function.invFun (wA (beltramiMul ν μ)) z) /
          conj (dz (wA (beltramiMul ν μ)) (Function.invFun (wA (beltramiMul ν μ)) z))) +
      (beltramiMul ν μ) (Function.invFun (wA (beltramiMul ν μ)) z) *
        (dz (wA (beltramiMul ν μ)) (Function.invFun (wA (beltramiMul ν μ)) z) /
          conj (dz (wA (beltramiMul ν μ)) (Function.invFun (wA (beltramiMul ν μ)) z)))) = 0 := by
    ring
  simp only [hz0, zero_div]

/-- The fixed points `-1, -i, 1` of `w_μ`. -/
theorem bg_fix {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    wAS μ ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      wAS μ ((-I : ℂ) : ExtPlane) = ((-I : ℂ) : ExtPlane) ∧
      wAS μ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
  exact ⟨hm1, hmI, hm2⟩

/-- `w_ν ∘ w_μ ∘ w_{(ν*μ)⁻¹} = id` on the whole sphere. -/
theorem bg_mul_core {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) (p : ExtPlane) :
    wAS ν (wAS μ (wAS (beltramiInv (beltramiMul ν μ)) p)) = p := by
  have hρ := bg_mul_mem_ball hμ hν
  have hι := bc_beltramiInv_mem_ball hρ
  set ι := beltramiInv (beltramiMul ν μ) with hιdef
  let F : ExtPlane → ExtPlane := fun q => wAS ν (wAS μ (wAS ι q))
  have hFc : Continuous F :=
    (wAS_continuous hν).comp ((wAS_continuous hμ).comp (wAS_continuous hι))
  have hFb : Function.Bijective F :=
    (wAS_bijective ν).comp ((wAS_bijective μ).comp (wAS_bijective ι))
  have hFiff : ∀ q, q ∈ toExt (closedBall (0 : ℂ) 1) ↔ F q ∈ toExt (closedBall (0 : ℂ) 1) :=
    fun q => (wAS_closed_iff hι q).trans ((wAS_closed_iff hμ _).trans (wAS_closed_iff hν _))
  have hFm : ∀ q ∉ toExt (closedBall (0 : ℂ) 1), F q ∉ toExt (closedBall (0 : ℂ) 1) :=
    fun q hq h => hq ((hFiff q).mpr h)
  have hFs : ∀ q ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), F p = q := by
    intro q hq
    obtain ⟨p, hp⟩ := hFb.2 q
    exact ⟨p, fun h => hq (hp ▸ (hFiff p).mp h), hp⟩
  obtain ⟨U, K, hUo, hUE, hUf, hT, hdata⟩ := bg_kqc_comp (bg_good_wA hι)
    (bg_kqc_comp (bg_good_wA hμ) (bg_good_wA hν))
  have hdiffU : DifferentiableOn ℂ ((wA ν ∘ wA μ) ∘ wA ι) U :=
    nx_differentiableOn_of_dilatation_zero hT
      (ae_restrict_of_ae_restrict_of_subset hUE (bg_F_dilatation_zero hμ hν))
  have hdiff := bc_sigma_conjugate_holomorphic hFc hFm hUf hdiffU hdata
  obtain ⟨n1, nI, n2⟩ := bg_fix hν
  obtain ⟨m1, mI, m2⟩ := bg_fix hμ
  obtain ⟨i1, iI, i2⟩ := bg_fix hι
  have hext := bc_exterior_rigidity hFc hFb.1 hFm hFs
    (by simp only [F, i1, m1, n1]) (by simp only [F, iI, mI, nI]) (by simp only [F, i2, m2, n2]) hdiff
  refine bg_eq_id_of_exterior hFc ?_ hext p
  intro q
  simp only [F]
  rw [wAS_refl_comm hι, wAS_refl_comm hμ, wAS_refl_comm hν]

/-- **Group law** of Model A (`wA_mul`, sphere form), TT:449. -/
theorem bc_wA_mul {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    beltramiMul ν μ ∈ LinfStarBall ∧ wAS (beltramiMul ν μ) = wAS ν ∘ wAS μ ∧
      beltramiInv μ ∈ LinfStarBall ∧ wAS μ ∘ wAS (beltramiInv μ) = id ∧
        wAS (beltramiInv μ) ∘ wAS μ = id := by
  have hρ := bg_mul_mem_ball hμ hν
  refine ⟨hρ, ?_, bc_beltramiInv_mem_ball hμ, funext (bg_inverse_right_sphere hμ),
    funext (bg_inverse_left_sphere hμ)⟩
  funext p
  have h1 := bg_mul_core hμ hν (wAS (beltramiMul ν μ) p)
  rw [bg_inverse_left_sphere hρ] at h1
  exact h1.symm

/-- On the unit circle `w_μ` is a finite-valued circle map. -/
theorem bg_circle_val {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖wA μ z‖ = 1 ∧ wAS μ (z : ExtPlane) = ((wA μ z : ℂ) : ExtPlane) := by
  obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
  have hw : wA μ z = u := by simp only [wA, he, finPart_coe]
  exact ⟨by rw [hw]; exact hu, by rw [hw]; exact he⟩

/-- **(TT:458)** The group law respects the equivalence relation. -/
theorem bc_beltramiMul_respects {l₁ l₂ μ₁ μ₂ : LinfStarBall} (hl : teichSetoid l₁ l₂)
    (hμ : teichSetoid μ₁ μ₂) :
    ∀ z ∈ unitCircle, wA (beltramiMul l₁ μ₁) z = wA (beltramiMul l₂ μ₂) z := by
  intro z hz
  have hz1 : ‖z‖ = 1 := hz
  have hm1 := μ₁.2
  have hm2 := μ₂.2
  have hl1 := l₁.2
  have hl2 := l₂.2
  obtain ⟨hn1, he1⟩ := bg_circle_val hm1 hz1
  obtain ⟨hn2, he2⟩ := bg_circle_val hm2 hz1
  have hu : wA μ₁ z = wA μ₂ z := hμ z hz
  obtain ⟨hk1, hf1⟩ := bg_circle_val hl1 hn1
  have hk : wA l₁ (wA μ₁ z) = wA l₂ (wA μ₁ z) := hl _ hn1
  have hk2 : wAS l₂ ((wA μ₁ z : ℂ) : ExtPlane) = ((wA l₂ (wA μ₁ z) : ℂ) : ExtPlane) :=
    (bg_circle_val hl2 hn1).2
  have e1 := congrFun (bc_wA_mul hm1 hl1).2.1 (z : ExtPlane)
  have e2 := congrFun (bc_wA_mul hm2 hl2).2.1 (z : ExtPlane)
  simp only [Function.comp_apply] at e1 e2
  unfold wA
  rw [e1, e2, he1, he2, ← hu, hf1, hk2, finPart_coe, finPart_coe, hk]

end TakhtajanTeo
