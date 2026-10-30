import LiZhongQC.Ch02.S11_IntegralOperators

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The Cauchy estimate in the precise exponent needed in dimension two. -/
theorem mp_cauchy_morrey_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℂ → ℂ, MemLp ω 4 → ∀ x y : ℂ,
      ‖cauchyT ω x - cauchyT ω y‖ ≤
        C * (eLpNorm ω 4).toReal * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := lemma11_2 (p := 4) (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun ω hω x y => ?_⟩
  have h := hC ω (by simpa using hω) x y
  norm_num at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 0) ENNReal.toReal_nonneg)
    (Real.rpow_nonneg (norm_nonneg _) _))

theorem mp_dzbar_memLp_four {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (dzbar f) 4 := by
  have hx : Continuous (fun z => fderiv ℝ f z (1 : ℂ)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hy : Continuous (fun z => fderiv ℝ f z I) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hd : Continuous (dzbar f) := (hx.add (continuous_const.mul hy)).div_const 2
  have hs : HasCompactSupport (fun z => fderiv ℝ f z 1 + I * fderiv ℝ f z I) :=
    (hasCompactSupport_fderiv_apply hc 1).add
      (hasCompactSupport_fderiv_apply hc I).mul_left
  have he : dzbar f = fun z => (2 : ℂ)⁻¹ *
      (fderiv ℝ f z 1 + I * fderiv ℝ f z I) := by
    funext z; unfold dzbar; ring
  have hc' : HasCompactSupport (dzbar f) := by rw [he]; exact hs.mul_left
  exact hd.memLp_of_hasCompactSupport hc'

/-- A genuine pointwise Morrey estimate, with no differentiability conclusion
assumed. This is the compact-support ingredient of the local estimate. -/
theorem mp_compact_morrey_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x y : ℂ, ‖f x - f y‖ ≤
        C * (eLpNorm (dzbar f) 4).toReal * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_cauchy_morrey_four
  refine ⟨C, hC, fun f hf hc x y => ?_⟩
  simpa only [cauchyT_dzbar_eq hf hc] using
    hest (dzbar f) (mp_dzbar_memLp_four hf hc) x y

/-- The product rule is used on a cutoff of the affine remainder. -/
theorem mp_dzbar_cutoff_affine {η f : ℂ → ℂ} (hη : Differentiable ℝ η)
    (hf : Differentiable ℝ f) (A : ℂ →L[ℝ] ℂ) (c z : ℂ) :
    dzbar (fun w => η w * (f w - A w - c)) z =
      η z * (dzbar f z - (A 1 + I * A I) / 2) +
        dzbar η z * (f z - A z - c) := by
  have hr : DifferentiableAt ℝ (fun w => f w - A w - c) z :=
    ((hf z).sub A.differentiableAt).sub_const c
  simp only [dzbar, fderiv_fun_mul (hη z) hr,
    fderiv_sub_const, fderiv_fun_sub (hf z) A.differentiableAt,
    A.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Localized oscillation of an affine remainder. The derivative of the cutoff
is displayed explicitly; removing this value term needs the Poincare estimate. -/
theorem mp_cutoff_affine_morrey_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η f : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → ContDiff ℝ 1 f →
      ∀ (A : ℂ →L[ℝ] ℂ) (c x y : ℂ), η x = 1 → η y = 1 →
      ‖f x - f y - A (x - y)‖ ≤ C *
        (eLpNorm (fun z =>
          η z * (dzbar f z - (A 1 + I * A I) / 2) +
            dzbar η z * (f z - A z - c)) 4).toReal *
        ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_compact_morrey_four
  refine ⟨C, hC, fun η f hη hc hf A c x y hx hy => ?_⟩
  have hg : ContDiff ℝ 1 (fun z => η z * (f z - A z - c)) :=
    hη.mul ((hf.sub A.contDiff).sub contDiff_const)
  have hgc : HasCompactSupport (fun z => η z * (f z - A z - c)) := hc.mul_right
  have h := hest _ hg hgc x y
  have he : dzbar (fun z => η z * (f z - A z - c)) = fun z =>
      η z * (dzbar f z - (A 1 + I * A I) / 2) +
        dzbar η z * (f z - A z - c) :=
    funext (mp_dzbar_cutoff_affine (hη.differentiable one_ne_zero)
      (hf.differentiable one_ne_zero) A c)
  rw [he, hx, hy, one_mul, one_mul] at h
  convert h using 1 <;> congr 1
  rw [map_sub]
  abel

theorem mp_l4_add_le {f g : ℂ → ℂ} {μ : Measure ℂ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    (eLpNorm (fun z => f z + g z) 4 μ).toReal ≤
      (eLpNorm f 4 μ).toReal + (eLpNorm g 4 μ).toReal := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
      (eLpNorm_add_le (f := f) (g := g) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 4))
  change (eLpNorm (f + g) 4 μ).toReal ≤ _
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using h

/-- A measurable localized product, with a finite real L4 bound. -/
theorem mp_l4_localized_mul {η u : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hu : MemLp u 4 (volume.restrict s))
    (hm : AEStronglyMeasurable (fun z => η z * u z) volume)
    (hsupp : Function.support η ⊆ s) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, ‖η z‖ ≤ B) :
    MemLp (fun z => η z * u z) 4 ∧
      (eLpNorm (fun z => η z * u z) 4).toReal ≤
        B * (eLpNorm u 4 (volume.restrict s)).toReal := by
  have hui : MemLp (s.indicator u) 4 := (memLp_indicator_iff_restrict hs).mpr hu
  have hle : ∀ z, ‖η z * u z‖ ≤ B * ‖s.indicator u z‖ := by
    intro z
    by_cases hz : z ∈ s
    · rw [indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)
    · have hη : η z = 0 := by
        by_contra hn
        exact hz (hsupp hn)
      simp [hη, indicator_of_notMem hz]
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm
    (Eventually.of_forall hle) 4
  have hfin : ENNReal.ofReal B * eLpNorm (s.indicator u) 4 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hui.eLpNorm_ne_top
  refine ⟨hnorm.trans_lt (lt_top_iff_ne_top.mpr hfin), ?_⟩
  have hreal := ENNReal.toReal_mono hfin hnorm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    eLpNorm_indicator_eq_eLpNorm_restrict hs] using hreal

/-- The local L4 estimate before Poincare: gradient error plus the explicitly
scaled value error. All quantities on the right are restricted to `s`. -/
theorem mp_local_cutoff_remainder_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η f : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → ContDiff ℝ 1 f →
      ∀ (A : ℂ →L[ℝ] ℂ) (c : ℂ) (s : Set ℂ),
      MeasurableSet s → tsupport η ⊆ s →
      MemLp (fun z => dzbar f z - (A 1 + I * A I) / 2) 4 (volume.restrict s) →
      MemLp (fun z => f z - A z - c) 4 (volume.restrict s) →
      (∀ z, ‖η z‖ ≤ 1) → ∀ B : ℝ, 0 ≤ B → (∀ z, ‖dzbar η z‖ ≤ B) →
      ∀ x y : ℂ, η x = 1 → η y = 1 →
      ‖f x - f y - A (x - y)‖ ≤ C *
        ((eLpNorm (fun z => dzbar f z - (A 1 + I * A I) / 2)
            4 (volume.restrict s)).toReal +
          B * (eLpNorm (fun z => f z - A z - c) 4 (volume.restrict s)).toReal) *
        ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_cutoff_affine_morrey_four
  refine ⟨C, hC, fun η f hη hc hf A c s hs hsupport hD hR hηbound B hB hBbound
    x y hx hy => ?_⟩
  have cont_dzbar : ∀ {g : ℂ → ℂ}, ContDiff ℝ 1 g → Continuous (dzbar g) := by
    intro g hg
    exact (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      (continuous_const.mul ((hg.continuous_fderiv one_ne_zero).clm_apply
        continuous_const))).div_const 2
  have hprodD : Continuous (fun z => η z * (dzbar f z - (A 1 + I * A I) / 2)) :=
    hη.continuous.mul ((cont_dzbar hf).sub continuous_const)
  have hprodR : Continuous (fun z => dzbar η z * (f z - A z - c)) :=
    (cont_dzbar hη).mul ((hf.continuous.sub A.continuous).sub continuous_const)
  have hsupportD : Function.support (dzbar η) ⊆ s := by
    intro z hz
    by_contra hzs
    have hn : z ∉ tsupport η := fun hm => hzs (hsupport hm)
    have he : dzbar η z = 0 := by simp [dzbar, fderiv_of_notMem_tsupport ℝ hn]
    exact hz he
  obtain ⟨hMD, hND⟩ := mp_l4_localized_mul hs hD hprodD.aestronglyMeasurable
    ((subset_tsupport η).trans hsupport) (by norm_num : (0 : ℝ) ≤ 1) hηbound
  obtain ⟨hMR, hNR⟩ := mp_l4_localized_mul hs hR hprodR.aestronglyMeasurable
    hsupportD hB hBbound
  have hsum := (mp_l4_add_le hMD hMR).trans (add_le_add hND hNR)
  simp only [one_mul] at hsum
  exact (hest η f hη hc hf A c x y hx hy).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC)
      (Real.rpow_nonneg (norm_nonneg _) _))

/-- Exact algebraic absorption used after a local Poincare inequality has been
proved. This lemma does not assert that inequality as an unproved fact. -/
theorem mp_absorb_poincare {G V K P r : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hPoincare : V ≤ P * r * G) :
    G + (K / r) * V ≤ (1 + K * P) * G := by
  have h := mul_le_mul_of_nonneg_left hPoincare (div_nonneg hK hr.le)
  calc G + (K / r) * V ≤ G + (K / r) * (P * r * G) := by linarith
    _ = (1 + K * P) * G := by field_simp

/-- The antiholomorphic derivative error is controlled by both real partial
errors. In particular it is not confused with the full real gradient. -/
theorem mp_affine_dzbar_l4_le {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (A : ℂ →L[ℝ] ℂ) (μ : Measure ℂ)
    (hx : MemLp (fun z => fderiv ℝ f z 1 - A 1) 4 μ)
    (hy : MemLp (fun z => fderiv ℝ f z I - A I) 4 μ) :
    MemLp (fun z => dzbar f z - (A 1 + I * A I) / 2) 4 μ ∧
      (eLpNorm (fun z => dzbar f z - (A 1 + I * A I) / 2) 4 μ).toReal ≤
        (eLpNorm (fun z => fderiv ℝ f z 1 - A 1) 4 μ).toReal +
          (eLpNorm (fun z => fderiv ℝ f z I - A I) 4 μ).toReal := by
  let X := fun z => fderiv ℝ f z 1 - A 1
  let Y := fun z => fderiv ℝ f z I - A I
  have hY : MemLp (fun z => I * Y z) 4 μ := hy.const_mul I
  have hsum : MemLp (fun z => X z + I * Y z) 4 μ := hx.add hY
  have hcont : Continuous (fun z => dzbar f z - (A 1 + I * A I) / 2) := by
    exact ((((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      (continuous_const.mul ((hf.continuous_fderiv one_ne_zero).clm_apply
        continuous_const))).div_const 2).sub continuous_const
  have hbound : ∀ z, ‖dzbar f z - (A 1 + I * A I) / 2‖ ≤ ‖X z + I * Y z‖ := by
    intro z
    have he : dzbar f z - (A 1 + I * A I) / 2 = (X z + I * Y z) / 2 := by
      dsimp [dzbar, X, Y]; ring
    rw [he, norm_div]
    norm_num
  have hnorm := eLpNorm_mono hcont.aestronglyMeasurable hbound (p := 4) (μ := μ)
  refine ⟨hsum.mono hcont.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  have hI : eLpNorm (fun z => I * Y z) 4 μ = eLpNorm Y 4 μ := by
    change eLpNorm (I • Y) 4 μ = _
    rw [eLpNorm_const_smul]
    rw [← ofReal_norm, norm_I, ENNReal.ofReal_one, one_mul]
  have hadd := mp_l4_add_le hx hY
  rw [hI] at hadd
  exact (ENNReal.toReal_mono hsum.eLpNorm_ne_top hnorm).trans hadd

/-- Conditional local Morrey--Poincare estimate for an affine remainder.
The Poincare inequality is an explicit hypothesis, not an imported axiom.
`G` is the sum of the L4 errors of the two real partial derivatives. -/
theorem mp_local_affine_remainder_of_poincare :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η f : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → ContDiff ℝ 1 f →
      ∀ (A : ℂ →L[ℝ] ℂ) (c : ℂ) (s : Set ℂ),
      MeasurableSet s → tsupport η ⊆ s →
      MemLp (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict s) →
      MemLp (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict s) →
      MemLp (fun z => f z - A z - c) 4 (volume.restrict s) →
      (∀ z, ‖η z‖ ≤ 1) → ∀ r K P : ℝ, 0 < r → 0 ≤ K →
      (∀ z, ‖dzbar η z‖ ≤ K / r) →
      let G := (eLpNorm (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict s)).toReal +
        (eLpNorm (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict s)).toReal
      (eLpNorm (fun z => f z - A z - c) 4 (volume.restrict s)).toReal ≤ P * r * G →
      ∀ x y : ℂ, η x = 1 → η y = 1 →
        ‖f x - f y - A (x - y)‖ ≤
          C * (1 + K * P) * G * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_local_cutoff_remainder_four
  refine ⟨C, hC, fun η f hη hc hf A c s hs hsupport hx hy hR hηbound r K P
    hr hK hderiv => ?_⟩
  dsimp only
  intro hP x y hηx hηy
  obtain ⟨hD, hDnorm⟩ := mp_affine_dzbar_l4_le hf A (volume.restrict s) hx hy
  have h := hest η f hη hc hf A c s hs hsupport hD hR hηbound (K / r)
    (div_nonneg hK hr.le) hderiv x y hηx hηy
  have hbound := mp_absorb_poincare hr hK hP
  have hcombined :
      (eLpNorm (fun z => dzbar f z - (A 1 + I * A I) / 2) 4 (volume.restrict s)).toReal +
        K / r * (eLpNorm (fun z => f z - A z - c) 4 (volume.restrict s)).toReal ≤
      (1 + K * P) *
        ((eLpNorm (fun z => fderiv ℝ f z 1 - A 1) 4 (volume.restrict s)).toReal +
          (eLpNorm (fun z => fderiv ℝ f z I - A I) 4 (volume.restrict s)).toReal) := by
    linarith
  have hfinal := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcombined hC) (Real.rpow_nonneg (norm_nonneg _) _))
  simpa only [mul_assoc] using hfinal

/-- A pointwise Morrey remainder bound gives a genuine Frechet derivative when
the normalized error tends to zero. The normalization is `r⁻¹ r^(1/2) E(r)`. -/
theorem mp_hasFDerivAt_of_morrey_remainder {f : ℂ → ℂ} {x : ℂ}
    (A : ℂ →L[ℝ] ℂ) {E : ℝ → ℝ} {C : ℝ}
    (hest : ∀ᶠ y in 𝓝 x, ‖f y - f x - A (y - x)‖ ≤
      C * E ‖y - x‖ * ‖y - x‖ ^ (1 / 2 : ℝ))
    (hlim : Tendsto (fun y : ℂ =>
      ‖y - x‖⁻¹ * (C * E ‖y - x‖ * ‖y - x‖ ^ (1 / 2 : ℝ))) (𝓝 x) (𝓝 0)) :
    HasFDerivAt f A x := by
  rw [hasFDerivAt_iff_tendsto]
  exact squeeze_zero' (Eventually.of_forall fun y =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (hest.mono fun y hy => mul_le_mul_of_nonneg_left hy
      (inv_nonneg.mpr (norm_nonneg _))) hlim

end TakhtajanTeo

