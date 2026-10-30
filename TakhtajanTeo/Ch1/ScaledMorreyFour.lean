import TakhtajanTeo.Ch1.GenPartialsMorreyFour

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
set_option maxHeartbeats 800000

def mp_squareCenter : ℂ := (1 / 2 : ℂ) + I / 2

theorem mp_mem_complexSquare (z : ℂ) : z ∈ mp_complexSquare ↔
    z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    refine ⟨(z.re, z.im), hz, ?_⟩
    exact Complex.ext rfl rfl

theorem mp_closedBall_subset_square :
    closedBall mp_squareCenter (1 / 4 : ℝ) ⊆ mp_complexSquare := by
  intro z hz
  rw [mp_mem_complexSquare]
  have hn : ‖z - mp_squareCenter‖ ≤ (1 / 4 : ℝ) := mem_closedBall_iff_norm.mp hz
  have hre := abs_re_le_norm (z - mp_squareCenter)
  have him := abs_im_le_norm (z - mp_squareCenter)
  norm_num [mp_squareCenter] at hre him
  dsimp [mp_squareCenter] at hn
  constructor <;> constructor <;> linarith [le_abs_self (z.re - 1 / 2),
    neg_le_abs (z.re - 1 / 2), le_abs_self (z.im - 1 / 2), neg_le_abs (z.im - 1 / 2)]

theorem mp_square_norm_sub_center {z : ℂ} (hz : z ∈ mp_complexSquare) :
    ‖z - mp_squareCenter‖ ≤ 1 := by
  obtain ⟨hzr, hzi⟩ := (mp_mem_complexSquare z).mp hz
  have h := norm_le_abs_re_add_abs_im (z - mp_squareCenter)
  norm_num [mp_squareCenter] at h
  have hr : |z.re - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [hzr.1], by linarith [hzr.2]⟩
  have hi : |z.im - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [hzi.1], by linarith [hzi.2]⟩
  dsimp [mp_squareCenter]
  linarith

/-- One cutoff is fixed once and for all; its derivative constant does not depend
on the base point, scale, or function being estimated. -/
theorem mp_fixed_plateau : ∃ (η : ℂ → ℂ) (K : ℝ),
    ContDiff ℝ 1 η ∧ HasCompactSupport η ∧ tsupport η ⊆ mp_complexSquare ∧
      (∀ z, ‖η z‖ ≤ 1) ∧ 0 ≤ K ∧ (∀ z, ‖dzbar η z‖ ≤ K) ∧
      ∀ z ∈ closedBall mp_squareCenter (1 / 8 : ℝ), η z = 1 := by
  let b : ContDiffBump mp_squareCenter := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let η : ℂ → ℂ := fun z => (b z : ℂ)
  have hη : ContDiff ℝ 1 η := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : HasCompactSupport η := b.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  have hts : tsupport η ⊆ mp_complexSquare := by
    have hs : tsupport η ⊆ tsupport b := tsupport_comp_subset (g := Complex.ofReal) rfl b
    exact hs.trans (by simpa only [b.tsupport_eq] using mp_closedBall_subset_square)
  have hd : Continuous (dzbar η) := by
    exact (((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      (continuous_const.mul ((hη.continuous_fderiv one_ne_zero).clm_apply
        continuous_const))).div_const 2
  obtain ⟨B, hB⟩ := (mp_complexSquare_compact.image hd).isBounded.exists_norm_le
  refine ⟨η, max B 0, hη, hc, hts, ?_, le_max_right _ _, ?_, ?_⟩
  · intro z
    simpa only [η, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using
      (b.le_one (x := z))
  · intro z
    by_cases hz : z ∈ mp_complexSquare
    · exact (hB _ (mem_image_of_mem (dzbar η) hz)).trans (le_max_left _ _)
    · have hn : z ∉ tsupport η := fun h => hz (hts h)
      simpa [dzbar, fderiv_of_notMem_tsupport ℝ hn] using (le_max_right B 0)
  · intro z hz
    change (b z : ℂ) = 1
    rw [b.one_of_mem_closedBall hz]
    norm_num

def mp_scale (z : ℂ) (r : ℝ) (w : ℂ) : ℂ := z + r • (w - mp_squareCenter)

theorem mp_scale_contDiff (z : ℂ) (r : ℝ) : ContDiff ℝ 1 (mp_scale z r) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul r)

theorem mp_scale_map (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Measure.map (mp_scale z r) volume = ENNReal.ofReal ((r ^ 2)⁻¹) • volume := by
  have he : mp_scale z r = (fun w : ℂ => z + w) ∘ (fun w : ℂ => r • w) ∘
      (fun w : ℂ => -mp_squareCenter + w) := by
    funext w; dsimp [mp_scale]; abel
  have hsm : Measure.map (fun w : ℂ => r • w) volume =
      ENNReal.ofReal ((r ^ 2)⁻¹) • volume := by
    simpa [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] using
      (Measure.map_addHaar_smul (volume : Measure ℂ) hr.ne')
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_add_left_eq_self volume (-mp_squareCenter), hsm,
    Measure.map_smul, map_add_left_eq_self] <;> fun_prop

def mp_scaleHomeomorph (z : ℂ) (r : ℝ) (hr : r ≠ 0) : ℂ ≃ₜ ℂ where
  toFun := mp_scale z r
  invFun := fun w => mp_squareCenter + r⁻¹ • (w - z)
  left_inv := by intro w; simp [mp_scale, smul_smul, hr]
  right_inv := by intro w; simp [mp_scale, smul_smul, hr]
  continuous_toFun := (mp_scale_contDiff z r).continuous
  continuous_invFun := by fun_prop

theorem mp_scale_map_restrict (z : ℂ) {r : ℝ} (hr : 0 < r) (s : Set ℂ) :
    Measure.map (mp_scale z r) (volume.restrict s) =
      ENNReal.ofReal ((r ^ 2)⁻¹) • volume.restrict (mp_scale z r '' s) := by
  let e := mp_scaleHomeomorph z r hr.ne'
  have hm := e.toMeasurableEquiv.measurableEmbedding.restrict_map volume (e '' s)
  change (Measure.map (⇑e) volume).restrict (e '' s) =
    Measure.map (⇑e) (volume.restrict (e ⁻¹' (e '' s))) at hm
  rw [Set.preimage_image_eq _ e.injective] at hm
  change (Measure.map (mp_scale z r) volume).restrict (mp_scale z r '' s) =
    Measure.map (mp_scale z r) (volume.restrict s) at hm
  rw [mp_scale_map z hr, Measure.restrict_smul] at hm
  exact hm.symm

theorem mp_scale_l4 (z : ℂ) {r : ℝ} (hr : 0 < r) (s : Set ℂ) (F : ℂ → ℂ) :
    (eLpNorm (fun w => F (mp_scale z r w)) 4 (volume.restrict s)).toReal =
      r ^ (-1 / 2 : ℝ) * (eLpNorm F 4 (volume.restrict (mp_scale z r '' s))).toReal := by
  let e := mp_scaleHomeomorph z r hr.ne'
  have hm := e.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
    (g := F) (p := 4) (μ := volume.restrict s)
  change eLpNorm F 4 (Measure.map (mp_scale z r) (volume.restrict s)) =
    eLpNorm (fun w => F (mp_scale z r w)) 4 (volume.restrict s) at hm
  rw [mp_scale_map_restrict z hr s,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)] at hm
  rw [← hm, smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg r))]
  norm_num only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  congr 1
  have he : (r ^ 2)⁻¹ = r ^ (-2 : ℝ) := by simp [Real.rpow_neg, Real.rpow_ofNat]
  rw [he, ← Real.rpow_mul hr.le]
  norm_num

theorem mp_scale_image_subset_ball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    mp_scale z r '' mp_complexSquare ⊆ closedBall z r := by
  rintro w ⟨u, hu, rfl⟩
  rw [mem_closedBall_iff_norm]
  simp only [mp_scale, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left (mp_square_norm_sub_center hu) hr.le).trans_eq (mul_one r)

theorem mp_scale_image_compact (z : ℂ) (r : ℝ) :
    IsCompact (mp_scale z r '' mp_complexSquare) :=
  mp_complexSquare_compact.image (mp_scale_contDiff z r).continuous

theorem mp_memLp_on_compact {F : ℂ → ℂ} (hF : Continuous F) {s : Set ℂ} (hs : IsCompact s) :
    MemLp F 4 (volume.restrict s) := by
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.measure_ne_top
  obtain ⟨B, hB⟩ := (hs.image hF).isBounded.exists_norm_le
  apply MemLp.of_bound hF.aestronglyMeasurable B
  filter_upwards [self_mem_ae_restrict hs.measurableSet] with w hw
  exact hB _ (mem_image_of_mem F hw)

theorem mp_l4_real_smul (r : ℝ) (F : ℂ → ℂ) (μ : Measure ℂ) :
    (eLpNorm (fun w => r • F w) 4 μ).toReal =
      |r| * (eLpNorm F 4 μ).toReal := by
  change (eLpNorm (r • F) 4 μ).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, ← ofReal_norm,
    ENNReal.toReal_ofReal (norm_nonneg r), Real.norm_eq_abs]

theorem mp_r_mul_neg_half {r : ℝ} (hr : 0 < r) :
    r * r ^ (-1 / 2 : ℝ) = r ^ (1 / 2 : ℝ) := by
  calc r * r ^ (-1 / 2 : ℝ) = r ^ (1 : ℝ) * r ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = r ^ ((1 : ℝ) + (-1 / 2)) := (Real.rpow_add hr _ _).symm
    _ = _ := by norm_num

/-- Translated and scaled smooth remainder estimate. The spatial domain is
`closedBall z r`, the evaluation distance is at most `r/8`, and the L4 scaling
factor is exactly `r^(1/2)`. The constant is independent of z and r. -/
theorem mp_smooth_scaled_remainder_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, ContDiff ℝ 1 f →
      ∀ (A : ℂ →L[ℝ] ℂ) (z : ℂ) (r : ℝ), 0 < r → ∀ y : ℂ, ‖y - z‖ ≤ r / 8 →
      ‖f y - f z - A (y - z)‖ ≤ C * r ^ (1 / 2 : ℝ) *
        ((eLpNorm (fun w => fderiv ℝ f w 1 - A 1) 4 (volume.restrict (closedBall z r))).toReal +
          (eLpNorm (fun w => fderiv ℝ f w I - A I) 4 (volume.restrict (closedBall z r))).toReal) := by
  obtain ⟨η, K, hη, hc, hs, hηbound, hK, hderiv, hplateau⟩ := mp_fixed_plateau
  obtain ⟨C, hC, hest⟩ := mp_complex_square_morrey_four
  have hCK : 0 ≤ C * (1 + 2 * K) := mul_nonneg hC (by positivity)
  refine ⟨C * (1 + 2 * K), hCK, fun f hf A z r hr y hy => ?_⟩
  let F : ℂ → ℂ := fun w => f (mp_scale z r w)
  let B : ℂ →L[ℝ] ℂ := r • A
  let v := mp_squareCenter + r⁻¹ • (y - z)
  have hF : ContDiff ℝ 1 F := hf.comp (mp_scale_contDiff z r)
  have hv : v ∈ closedBall mp_squareCenter (1 / 8 : ℝ) := by
    rw [mem_closedBall_iff_norm]
    simp only [v, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    rw [← div_eq_inv_mul, div_le_iff₀ hr]
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hy
  have hcenter : F mp_squareCenter = f z := by simp [F, mp_scale]
  have hval : F v = f y := by simp [F, v, mp_scale, smul_smul, hr.ne']
  have hBval : B (v - mp_squareCenter) = A (y - z) := by
    change r • A (v - mp_squareCenter) = _
    rw [show v - mp_squareCenter = r⁻¹ • (y - z) by dsimp [v]; abel,
      A.map_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hdiff : ∀ w t, fderiv ℝ F w t = r • fderiv ℝ f (mp_scale z r w) t := by
    intro w t
    have hS : HasFDerivAt (mp_scale z r) (r • ContinuousLinearMap.id ℝ ℂ) w := by
      change HasFDerivAt (fun u : ℂ => z + r • (u - mp_squareCenter)) _ w
      exact (((hasFDerivAt_id (𝕜 := ℝ) w).sub_const mp_squareCenter).const_smul r).const_add z
    have hh := (hf.differentiable one_ne_zero (mp_scale z r w)).hasFDerivAt.comp w hS
    change (fderiv ℝ (f ∘ mp_scale z r) w) t = _
    rw [hh.fderiv]
    change (fderiv ℝ f (mp_scale z r w)) (r • t) = _
    exact map_smul _ r t
  have hnorm : ∀ t : ℂ,
      (eLpNorm (fun w => fderiv ℝ F w t - B t) 4 (volume.restrict mp_complexSquare)).toReal =
      r ^ (1 / 2 : ℝ) *
        (eLpNorm (fun w => fderiv ℝ f w t - A t)
          4 (volume.restrict (mp_scale z r '' mp_complexSquare))).toReal := by
    intro t
    have he : (fun w => fderiv ℝ F w t - B t) =
        fun w => r • (fderiv ℝ f (mp_scale z r w) t - A t) := by
      funext w
      rw [hdiff]
      simp [B, smul_sub]
    rw [he, mp_l4_real_smul, abs_of_pos hr,
      mp_scale_l4 z hr mp_complexSquare (fun w => fderiv ℝ f w t - A t),
      ← mul_assoc, mp_r_mul_neg_half hr]
  have hmono : ∀ t : ℂ,
      (eLpNorm (fun w => fderiv ℝ f w t - A t)
        4 (volume.restrict (mp_scale z r '' mp_complexSquare))).toReal ≤
      (eLpNorm (fun w => fderiv ℝ f w t - A t) 4 (volume.restrict (closedBall z r))).toReal := by
    intro t
    have hcont : Continuous (fun w => fderiv ℝ f w t - A t) :=
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub continuous_const
    exact ENNReal.toReal_mono (mp_memLp_on_compact hcont (isCompact_closedBall z r)).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono (mp_scale_image_subset_ball z hr) le_rfl))
  have h := hest η F hη hc hF B hs hηbound K hK hderiv v mp_squareCenter
    (hplateau v hv) (hplateau _ (mem_closedBall_self (by norm_num)))
  rw [hval, hcenter, hBval, hnorm, hnorm] at h
  have hp : ‖v - mp_squareCenter‖ ^ (1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one (norm_nonneg _) ((mem_closedBall_iff_norm.mp hv).trans (by norm_num)) (by norm_num)
  have h1 := h.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hCK
    (add_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) ENNReal.toReal_nonneg)
      (mul_nonneg (Real.rpow_nonneg hr.le _) ENNReal.toReal_nonneg))))
  rw [mul_one, ← mul_add, ← mul_assoc] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (add_le_add (hmono 1) (hmono I))
    (mul_nonneg hCK (Real.rpow_nonneg hr.le _)))

/-- The scaled estimate holds for the exact continuous representative supplied
by HasGenPartials. No classical differentiability is assumed. -/
theorem mp_gen_scaled_remainder_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g h : ℂ → ℂ, HasGenPartials f g h univ 4 →
      ∀ (A : ℂ →L[ℝ] ℂ) (z : ℂ) (r : ℝ), 0 < r → ∀ y : ℂ, ‖y - z‖ ≤ r / 8 →
      ‖f y - f z - A (y - z)‖ ≤ C * r ^ (1 / 2 : ℝ) *
        ((eLpNorm (fun w => g w - A 1) 4 (volume.restrict (closedBall z r))).toReal +
          (eLpNorm (fun w => h w - A I) 4 (volume.restrict (closedBall z r))).toReal) := by
  obtain ⟨C, hC, hest⟩ := mp_smooth_scaled_remainder_four
  refine ⟨C, hC, fun f g h hgp A z r hr y hy => ?_⟩
  obtain ⟨hM, fn, hfn, hconv, hconvD⟩ := hgp
  have hfn' : ∀ n, ContDiff ℝ 1 (fn n) := fun n => contDiffOn_univ.mp (hfn n)
  obtain ⟨hg, hh⟩ := hM (closedBall z r) (subset_univ _) (isCompact_closedBall z r)
  obtain ⟨hEx, hEy⟩ := hconvD (closedBall z r) (subset_univ _) (isCompact_closedBall z r)
  have hEx' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEx
  have hEy' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEy
  simp only [ENNReal.toReal_zero] at hEx' hEy'
  let G := (eLpNorm (fun w => g w - A 1) 4 (volume.restrict (closedBall z r))).toReal
  let H := (eLpNorm (fun w => h w - A I) 4 (volume.restrict (closedBall z r))).toReal
  let Ex := fun n => (eLpNorm (fun w => fderiv ℝ (fn n) w 1 - g w)
    4 (volume.restrict (closedBall z r))).toReal
  let Ey := fun n => (eLpNorm (fun w => fderiv ℝ (fn n) w I - h w)
    4 (volume.restrict (closedBall z r))).toReal
  have hbound : ∀ n,
      (eLpNorm (fun w => fderiv ℝ (fn n) w 1 - A 1) 4 (volume.restrict (closedBall z r))).toReal +
        (eLpNorm (fun w => fderiv ℝ (fn n) w I - A I) 4 (volume.restrict (closedBall z r))).toReal ≤
      (Ex n + G) + (Ey n + H) := by
    intro n
    apply add_le_add
    · exact mp_l4_error_triangle
        (mp_memLp_on_compact (((hfn' n).continuous_fderiv one_ne_zero).clm_apply continuous_const)
          (isCompact_closedBall z r)) hg
        (mp_memLp_on_compact continuous_const (isCompact_closedBall z r))
    · exact mp_l4_error_triangle
        (mp_memLp_on_compact (((hfn' n).continuous_fderiv one_ne_zero).clm_apply continuous_const)
          (isCompact_closedBall z r)) hh
        (mp_memLp_on_compact continuous_const (isCompact_closedBall z r))
  have hineq : ∀ n, ‖fn n y - fn n z - A (y - z)‖ ≤
      C * r ^ (1 / 2 : ℝ) * ((Ex n + G) + (Ey n + H)) := by
    intro n
    exact (hest (fn n) (hfn' n) A z r hr y hy).trans
      (mul_le_mul_of_nonneg_left (hbound n) (mul_nonneg hC (Real.rpow_nonneg hr.le _)))
  have hleft : Tendsto (fun n => ‖fn n y - fn n z - A (y - z)‖) atTop
      (𝓝 ‖f y - f z - A (y - z)‖) :=
    (((hconv.tendsto_at (mem_univ y)).sub (hconv.tendsto_at (mem_univ z))).sub_const _).norm
  have hsum : Tendsto (fun n => (Ex n + G) + (Ey n + H)) atTop (𝓝 (G + H)) := by
    simpa only [Ex, Ey, Function.comp_def, zero_add] using (hEx'.add_const G).add (hEy'.add_const H)
  exact le_of_tendsto_of_tendsto hleft (hsum.const_mul _) (Eventually.of_forall hineq)

end TakhtajanTeo

