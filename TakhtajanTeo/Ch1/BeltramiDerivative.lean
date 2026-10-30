import TakhtajanTeo.Ch1.BeltramiCompose

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## The derivative of `l ↦ l * μ` at an arbitrary `l₀` (`bd_` prefix) -/

theorem bd_alg (m c b h : ℂ) (hd1 : 1 + c * b ≠ 0) (hd2 : 1 + c * (b + h) ≠ 0) :
    (m + (b + h)) / (1 + c * (b + h)) - (m + b) / (1 + c * b) - (1 - m * c) * h / (1 + c * b) ^ 2 =
      -((1 - m * c) * c * h ^ 2) / ((1 + c * b) ^ 2 * (1 + c * (b + h))) := by
  rw [div_sub_div _ _ hd2 hd1, div_sub_div _ _ (mul_ne_zero hd2 hd1) (pow_ne_zero 2 hd1),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hd2 hd1) (pow_ne_zero 2 hd1))
      (mul_ne_zero (pow_ne_zero 2 hd1) hd2)]
  ring

/-- Exact second-order remainder of the Möbius map `b ↦ (m + b)/(1 + m̄ b)`. -/
theorem bd_mobius_taylor {m b h : ℂ} {s r : ℝ} (hm : ‖m‖ ≤ 1) (hb : ‖b‖ ≤ s) (hh : ‖h‖ ≤ r)
    (hs : s < 1) (hr : r ≤ (1 - s) / 2) :
    ‖(m + (b + h)) / (1 + conj m * (b + h)) - (m + b) / (1 + conj m * b) -
        (((1 - ‖m‖ ^ 2 : ℝ)) : ℂ) * h / (1 + conj m * b) ^ 2‖ ≤ 2 * ‖h‖ ^ 2 / (1 - s) ^ 3 := by
  have hm0 := norm_nonneg m
  have hb0 := norm_nonneg b
  have hh0 := norm_nonneg h
  have hs0 : 0 ≤ s := hb0.trans hb
  have hr0 : 0 ≤ r := hh0.trans hh
  have hs1 : 0 < 1 - s := by linarith
  have hq1 : ‖conj m * b‖ ≤ s := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖m‖ * ‖b‖ ≤ 1 * s := by gcongr
      _ = s := one_mul _
  have hq2 : ‖conj m * (b + h)‖ ≤ s + r := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖m‖ * ‖b + h‖ ≤ 1 * (s + r) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hb hh)
      _ = s + r := one_mul _
  have hd1n : (1 - s) ≤ ‖1 + conj m * b‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(conj m * b))
    rw [norm_neg, norm_one] at this
    have e : (1 : ℂ) - -(conj m * b) = 1 + conj m * b := by ring
    rw [e] at this
    linarith
  have hd2n : (1 - s) / 2 ≤ ‖1 + conj m * (b + h)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(conj m * (b + h)))
    rw [norm_neg, norm_one] at this
    have e : (1 : ℂ) - -(conj m * (b + h)) = 1 + conj m * (b + h) := by ring
    rw [e] at this
    linarith
  have hd1 : 1 + conj m * b ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hd1n; linarith
  have hd2 : 1 + conj m * (b + h) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hd2n; linarith
  have hmm : m * conj m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  have hcast : (((1 - ‖m‖ ^ 2 : ℝ)) : ℂ) = 1 - m * conj m := by
    rw [hmm]; push_cast; ring
  have e := bd_alg m (conj m) b h hd1 hd2
  rw [hcast, e, norm_div, norm_neg]
  have hc1 : ‖1 - m * conj m‖ ≤ 1 := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  have hnum : ‖(1 - m * conj m) * conj m * h ^ 2‖ ≤ ‖h‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj]
    calc ‖1 - m * conj m‖ * ‖m‖ * ‖h‖ ^ 2 ≤ 1 * 1 * ‖h‖ ^ 2 := by gcongr
      _ = ‖h‖ ^ 2 := by ring
  have hden : (1 - s) ^ 3 / 2 ≤ ‖(1 + conj m * b) ^ 2 * (1 + conj m * (b + h))‖ := by
    rw [norm_mul, norm_pow]
    calc (1 - s) ^ 3 / 2 = (1 - s) ^ 2 * ((1 - s) / 2) := by ring
      _ ≤ ‖1 + conj m * b‖ ^ 2 * ‖1 + conj m * (b + h)‖ :=
        mul_le_mul (pow_le_pow_left₀ hs1.le hd1n 2) hd2n (by positivity) (by positivity)
  have hpos : 0 < (1 - s) ^ 3 / 2 := by positivity
  calc ‖(1 - m * conj m) * conj m * h ^ 2‖ / ‖(1 + conj m * b) ^ 2 * (1 + conj m * (b + h))‖
      ≤ ‖h‖ ^ 2 / ((1 - s) ^ 3 / 2) := div_le_div₀ (sq_nonneg _) hnum hpos hden
    _ = 2 * ‖h‖ ^ 2 / (1 - s) ^ 3 := by field_simp

/-- The operators `ν ↦ w · (ν ∘ w_μ) τ` on `L∞(𝔻*)` for a bounded measurable weight `w`. -/
theorem bd_exists_op {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hw : AEStronglyMeasurable w (volume.restrict unitDiscExterior))
    (hwb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖w z‖ ≤ C) :
    ∃ D : LinfStar →L[ℂ] LinfStar, ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      D ν z = w z * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) := by
  have hbound : ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      ‖w z * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)‖ ≤ C * ‖ν‖ := by
    intro ν
    filter_upwards [ae_restrict_of_ae (bc_wA_ae hμ), bc_pullback_ae hμ (LinfStar_ae_norm_le ν),
      hwb] with z hz hν hwz
    obtain ⟨-, hdz, -, -⟩ := hz
    have hτ : ‖conj (dz (wA μ) z) / dz (wA μ) z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hdz)]
    rw [norm_mul, norm_mul, hτ, mul_one]
    exact mul_le_mul hwz hν (norm_nonneg _) hC
  have hmemLp : ∀ ν : LinfStar, MemLp (fun z => w z * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) ∞
      (volume.restrict unitDiscExterior) := by
    intro ν
    have h2 : AEStronglyMeasurable (fun z => ν (wA μ z)) (volume.restrict unitDiscExterior) :=
      bc_comp_aesm hμ (Lp.aestronglyMeasurable ν)
    have h3 : AEStronglyMeasurable (fun z => conj (dz (wA μ) z) / dz (wA μ) z)
        (volume.restrict unitDiscExterior) :=
      (((continuous_conj.measurable.comp (measurable_dz (wA μ))).div
        (measurable_dz (wA μ)))).aestronglyMeasurable
    exact memLp_top_of_bound ((hw.mul h2).mul h3) (C * ‖ν‖) (hbound ν)
  let g : LinfStar → ℂ → ℂ := fun ν z =>
    w z * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)
  let D0 : LinfStar →ₗ[ℂ] LinfStar :=
    { toFun := fun ν => toLinf (g ν)
      map_add' := by
        intro ν₁ ν₂
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (hmemLp (ν₁ + ν₂)), bc_toLinf_ae (hmemLp ν₁),
          bc_toLinf_ae (hmemLp ν₂), Lp.coeFn_add (toLinf (g ν₁)) (toLinf (g ν₂)),
          bc_pullback_ae hμ (Lp.coeFn_add ν₁ ν₂)] with z h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h2, h3]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.add_apply]
        ring
      map_smul' := by
        intro c ν
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (hmemLp (c • ν)), bc_toLinf_ae (hmemLp ν),
          Lp.coeFn_smul c (toLinf (g ν)), bc_pullback_ae hμ (Lp.coeFn_smul c ν)] with z h1 h2 h4 h5
        simp only [RingHom.id_apply]
        rw [h4, Pi.smul_apply, h2]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  refine ⟨D0.mkContinuous C (fun ν => ?_), fun ν => ?_⟩
  · exact norm_toLinf_le_of_ae_bound (mul_nonneg hC (norm_nonneg ν)) (hbound ν)
  · exact bc_toLinf_ae (hmemLp ν)

/-- Denominator of the derivative of the product at `l₀`. -/
theorem bd_den_ne {m b : ℂ} {s : ℝ} (hm : ‖m‖ ≤ 1) (hb : ‖b‖ ≤ s) :
    1 - s ≤ ‖1 + conj m * b‖ := by
  have hq : ‖conj m * b‖ ≤ s := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖m‖ * ‖b‖ ≤ 1 * s := by gcongr
      _ = s := one_mul _
  have := norm_sub_norm_le (1 : ℂ) (-(conj m * b))
  rw [norm_neg, norm_one] at this
  have e : (1 : ℂ) - -(conj m * b) = 1 + conj m * b := by ring
  rw [e] at this
  linarith

/-- The derivative of `l ↦ l * μ` at an arbitrary `l₀` in the ball. -/
theorem bd_hasFDerivAt {μ l₀ : LinfStar} (hμ : μ ∈ LinfStarBall) (hl₀ : l₀ ∈ LinfStarBall) :
    ∃ D : LinfStar →L[ℂ] LinfStar, HasFDerivAt (fun l => beltramiMul l μ) D l₀ ∧
      ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
        D ν z = (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) /
          (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2 := by
  have hs1 := bc_norm_lt_one hl₀
  set s := ‖l₀‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg l₀
  have hs2 : 0 < 1 - s := by linarith
  -- the weight
  let w : ℂ → ℂ := fun z => (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) /
    (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2
  have hwm : AEStronglyMeasurable w (volume.restrict unitDiscExterior) := by
    have h1 : AEStronglyMeasurable μ (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable μ
    have h2 : AEStronglyMeasurable (fun z => l₀ (wA μ z)) (volume.restrict unitDiscExterior) :=
      bc_comp_aesm hμ (Lp.aestronglyMeasurable l₀)
    have h3 : AEStronglyMeasurable (fun z => conj (dz (wA μ) z) / dz (wA μ) z)
        (volume.restrict unitDiscExterior) :=
      (((continuous_conj.measurable.comp (measurable_dz (wA μ))).div
        (measurable_dz (wA μ)))).aestronglyMeasurable
    have hcm : AEStronglyMeasurable (fun z => conj (μ z)) (volume.restrict unitDiscExterior) :=
      continuous_conj.comp_aestronglyMeasurable h1
    have hnum : AEStronglyMeasurable (fun z => (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ))
        (volume.restrict unitDiscExterior) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_const.sub (h1.norm.pow 2))
    have hden : AEStronglyMeasurable (fun z => (1 + conj (μ z) * (l₀ (wA μ z) *
        (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2) (volume.restrict unitDiscExterior) :=
      ((aestronglyMeasurable_const.add (hcm.mul (h2.mul h3)))).pow 2
    exact (hnum.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  have hwb : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖w z‖ ≤ 1 / (1 - s) ^ 2 := by
    filter_upwards [LinfStar_ae_norm_le μ, bc_b_bound (l := l₀) hμ] with z hm hb
    have hm1 : ‖μ z‖ ≤ 1 := hm.trans (bc_norm_lt_one hμ).le
    have hd := bd_den_ne hm1 hb
    have hnum : ‖(((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [norm_nonneg (μ z)]
    simp only [w]
    rw [norm_div, norm_pow]
    exact div_le_div₀ zero_le_one hnum (by positivity) (pow_le_pow_left₀ hs2.le hd 2)
  obtain ⟨D, hD⟩ := bd_exists_op hμ (by positivity) hwm hwb
  have hDf : ∀ ν : LinfStar, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      D ν z = (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) /
          (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2 := by
    intro ν
    filter_upwards [hD ν] with z hz
    rw [hz]
    simp only [w]
    ring
  refine ⟨D, ?_, hDf⟩
  -- remainder estimate
  have hrem : ∀ h : LinfStar, ‖h‖ ≤ (1 - s) / 2 →
      ‖beltramiMul (l₀ + h) μ - beltramiMul l₀ μ - D h‖ ≤ 2 * ‖h‖ ^ 2 / (1 - s) ^ 3 := by
    intro h hh
    have hlh : l₀ + h ∈ LinfStarBall := by
      have : ‖l₀ + h‖ < 1 := by
        have := norm_add_le l₀ h
        linarith
      simpa [LinfStarBall] using this
    refine bc_Lp_norm_le _ (by positivity) ?_
    filter_upwards [bc_mul_ae hμ hlh, bc_mul_ae hμ hl₀, hDf h,
      Lp.coeFn_sub (beltramiMul (l₀ + h) μ - beltramiMul l₀ μ) (D h),
      Lp.coeFn_sub (beltramiMul (l₀ + h) μ) (beltramiMul l₀ μ),
      bc_pullback_ae hμ (Lp.coeFn_add l₀ h), LinfStar_ae_norm_le μ,
      bc_b_bound (l := l₀) hμ, bc_b_bound (l := h) hμ] with z h1 h2 h3 h4 h5 h6 hm hb hbh
    rw [h4, Pi.sub_apply, h5, Pi.sub_apply, h1, h2, h3, h6, Pi.add_apply]
    have hm1 : ‖μ z‖ ≤ 1 := hm.trans (bc_norm_lt_one hμ).le
    have key := bd_mobius_taylor (m := μ z)
      (b := l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))
      (h := h (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) hm1 hb hbh hs1 hh
    have hnum : μ z + (l₀ (wA μ z) + h (wA μ z)) * (conj (dz (wA μ) z) / dz (wA μ) z) =
        μ z + (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) +
          h (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) := by ring
    have hden : 1 + conj (μ z) * (l₀ (wA μ z) + h (wA μ z)) * (conj (dz (wA μ) z) / dz (wA μ) z) =
        1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) +
          h (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) := by ring
    have hlast : (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * h (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) /
          (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2 =
        (((1 - ‖μ z‖ ^ 2 : ℝ)) : ℂ) * (h (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z)) /
          (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2 := by ring
    rw [hnum, hden, hlast, mul_assoc (conj (μ z)) (l₀ (wA μ z))]
    refine key.trans ?_
    gcongr
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ h : LinfStar in nhds 0, ‖h‖ < min ((1 - s) / 2) (c * (1 - s) ^ 3 / 2) := by
    have := Metric.ball_mem_nhds (0 : LinfStar)
      (lt_min (half_pos hs2) (by positivity : 0 < c * (1 - s) ^ 3 / 2))
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  have h1 : ‖h‖ ≤ (1 - s) / 2 := (lt_min_iff.mp hh).1.le
  have h2 : ‖h‖ ≤ c * (1 - s) ^ 3 / 2 := (lt_min_iff.mp hh).2.le
  have hr := hrem h h1
  have e : beltramiMul (l₀ + h) μ - beltramiMul l₀ μ - D h = beltramiMul (l₀ + h) μ - beltramiMul l₀ μ - D h :=
    rfl
  show ‖beltramiMul (l₀ + h) μ - beltramiMul l₀ μ - D h‖ ≤ c * ‖h‖
  refine hr.trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg h]

/-- Explicit a.e. formula for `D_{l₀}R_μ ν` (the general-base-point version of `remark_1_3`). -/
theorem bd_fderiv_ae {μ l₀ : LinfStar} (hμ : μ ∈ LinfStarBall) (hl₀ : l₀ ∈ LinfStarBall)
    (ν : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      fderiv ℂ (fun l => beltramiMul l μ) l₀ ν z =
        (1 - ‖μ z‖ ^ 2) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) /
          (1 + conj (μ z) * (l₀ (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z))) ^ 2 := by
  obtain ⟨D, hd, hD⟩ := bd_hasFDerivAt hμ hl₀
  rw [hd.fderiv]
  filter_upwards [hD ν] with z hz
  rw [hz]
  push_cast
  ring

/-- Complex differentiability of `l ↦ l * μ` on the whole ball. -/
theorem bd_differentiableOn {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fun l => beltramiMul l μ) LinfStarBall := fun l₀ hl₀ =>
  (bd_hasFDerivAt hμ hl₀).choose_spec.1.differentiableAt.differentiableWithinAt

end TakhtajanTeo
