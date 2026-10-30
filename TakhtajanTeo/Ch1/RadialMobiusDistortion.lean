import TakhtajanTeo.Ch1.RadialDiskExtension
import LiZhongQC.Lemmas.Pompeiu

/-! # Uniform distortion and global QC of radial disk automorphisms

Exact Wirtinger derivatives give the bound `(1+|a|)/(1-|a|)` for a rotation
of a Blaschke factor. Circle removability glues the exterior and interior QC
maps. Classification then yields the explicit closed-disk QC extension of
any conformal disk automorphism continuous on the closed disk.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

set_option backward.isDefEq.respectTransparency false in
theorem norm_wirtinger {z : ℂ} (hz : z ≠ 0) :
    dz (fun w : ℂ => (‖w‖ : ℂ)) z = conj z / (2 * (‖z‖ : ℂ)) ∧
      dzbar (fun w : ℂ => (‖w‖ : ℂ)) z = z / (2 * (‖z‖ : ℂ)) := by
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
    simpa only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_one, one_mul,
      Real.rpow_neg_one] using s15_ra_hasFDerivAt_norm_rpow hz 1
  have hc : HasFDerivAt (fun w : ℂ => (‖w‖ : ℂ))
      (Complex.ofRealCLM.comp (‖z‖⁻¹ • innerSL ℝ z)) z := by
    convert Complex.ofRealCLM.hasFDerivAt.comp z hn using 1
    rfl
  have h1 : fderiv ℝ (fun w : ℂ => (‖w‖ : ℂ)) z 1 = ((‖z‖⁻¹ * z.re : ℝ) : ℂ) := by
    rw [hc.fderiv]
    simp [Complex.inner]
  have hI : fderiv ℝ (fun w : ℂ => (‖w‖ : ℂ)) z I = ((‖z‖⁻¹ * z.im : ℝ) : ℂ) := by
    rw [hc.fderiv]
    simp [Complex.inner]
  have hr : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hconj : conj z = (z.re : ℂ) - I * z.im := by apply Complex.ext <;> simp
  have hrepr : (z.re : ℂ) + I * z.im = z := by simpa [mul_comm] using Complex.re_add_im z
  constructor
  · rw [dz, h1, hI]
    push_cast
    rw [hconj]
    field_simp [hr]
  · rw [dzbar, h1, hI]
    push_cast
    field_simp [hr]
    linear_combination hrepr

/-- Exact exterior Wirtinger derivatives of the explicit radial extension. -/
theorem radialDiskExtension_wirtinger {m : ℂ → ℂ} {z : ℂ} (hz : 1 < ‖z‖)
    (hm : DifferentiableAt ℂ m (z / (‖z‖ : ℂ))) :
    dz (radialDiskExtension m) z =
        (conj (z / (‖z‖ : ℂ)) * m (z / (‖z‖ : ℂ)) + deriv m (z / (‖z‖ : ℂ))) / 2 ∧
      dzbar (radialDiskExtension m) z =
        ((z / (‖z‖ : ℂ)) * m (z / (‖z‖ : ℂ)) -
          (z / (‖z‖ : ℂ)) ^ 2 * deriv m (z / (‖z‖ : ℂ))) / 2 := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hr : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz0
  have he : (fun w : ℂ => ‖w‖ ^ (-1 : ℝ) • w) = fun w : ℂ => w / (‖w‖ : ℂ) := by
    funext w
    simp [Real.rpow_neg_one, Complex.real_smul, div_eq_mul_inv, mul_comm]
  have hu := (s15_ra_hasFDerivAt hz0 (-1)).differentiableAt
  rw [he] at hu
  have hudz := s15_ra_dz hz0 (-1)
  have hudb := s15_ra_dzbar hz0 (-1)
  rw [he] at hudz hudb
  norm_num [Real.rpow_neg, Real.rpow_natCast] at hudz hudb
  have hn : DifferentiableAt ℝ (fun w : ℂ => (‖w‖ : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z
      ((contDiffAt_norm ℝ hz0 : ContDiffAt ℝ 1 norm z).differentiableAt (by norm_num))
  have hcomp := eq6_5 hu hm
  dsimp only [Function.comp_def] at hcomp
  have hmc : DifferentiableAt ℝ (fun w : ℂ => m (w / (‖w‖ : ℂ))) z :=
    (hm.restrictScalars ℝ).comp z hu
  have hnear : radialDiskExtension m =ᶠ[𝓝 z]
      fun w : ℂ => (‖w‖ : ℂ) * m (w / (‖w‖ : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact if_neg (not_le.mpr hw)
  have hdz : dz (radialDiskExtension m) z =
      dz (fun w : ℂ => (‖w‖ : ℂ) * m (w / (‖w‖ : ℂ))) z := by
    unfold dz
    rw [hnear.fderiv_eq]
  have hdb : dzbar (radialDiskExtension m) z =
      dzbar (fun w : ℂ => (‖w‖ : ℂ) * m (w / (‖w‖ : ℂ))) z := by
    unfold dzbar
    rw [hnear.fderiv_eq]
  constructor
  · rw [hdz, dz_mul hn hmc, hcomp.1, hudz, (norm_wirtinger hz0).1]
    simp only [map_div₀, Complex.conj_ofReal]
    push_cast
    field_simp [hr]
    ring
  · rw [hdb, dzbar_mul hn hmc, hcomp.2, hudb, (norm_wirtinger hz0).2]
    push_cast
    field_simp [hr]
    ring

theorem radialDiskExtension_norms_of_slope {m : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hz : 1 < ‖z‖) (ht : 0 < t)
    (hm : DifferentiableAt ℂ m (z / (‖z‖ : ℂ)))
    (hn : ‖m (z / (‖z‖ : ℂ))‖ = 1)
    (hd : deriv m (z / (‖z‖ : ℂ)) =
      (t : ℂ) * conj (z / (‖z‖ : ℂ)) * m (z / (‖z‖ : ℂ))) :
    ‖dz (radialDiskExtension m) z‖ = (1 + t) / 2 ∧
      ‖dzbar (radialDiskExtension m) z‖ = |1 - t| / 2 := by
  let ζ := z / (‖z‖ : ℂ)
  have hζ : ‖ζ‖ = 1 := norm_div_norm_eq_one (norm_ne_zero_iff.mp (by linarith))
  have hunit : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  have hrot : ‖conj ζ * m ζ‖ = 1 := by rw [norm_mul, norm_conj, hζ, hn, one_mul]
  have hrot' : ‖ζ * m ζ‖ = 1 := by rw [norm_mul, hζ, hn, one_mul]
  obtain ⟨hzder, hbder⟩ := radialDiskExtension_wirtinger hz hm
  rw [hd] at hzder hbder
  have hez : dz (radialDiskExtension m) z = (((1 + t) / 2 : ℝ) : ℂ) * (conj ζ * m ζ) := by
    rw [hzder]
    dsimp [ζ]
    push_cast
    ring
  have heb : dzbar (radialDiskExtension m) z = (((1 - t) / 2 : ℝ) : ℂ) * (ζ * m ζ) := by
    rw [hbder]
    change (ζ * m ζ - ζ ^ 2 * ((t : ℂ) * conj ζ * m ζ)) / 2 = _
    push_cast
    linear_combination -(t : ℂ) * ζ * m ζ / 2 * hunit
  constructor
  · rw [hez, norm_mul, hrot, mul_one, Complex.norm_of_nonneg (by positivity)]
  · rw [heb, norm_mul, hrot', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Uniform QC control from positive, uniformly bounded angular slope. -/
theorem radialDiskExtension_distortion_of_slope {m : ℂ → ℂ} {z : ℂ} {t K : ℝ}
    (hz : 1 < ‖z‖) (ht : 0 < t) (htK : t ≤ K) (hiK : t⁻¹ ≤ K)
    (hm : DifferentiableAt ℂ m (z / (‖z‖ : ℂ)))
    (hn : ‖m (z / (‖z‖ : ℂ))‖ = 1)
    (hd : deriv m (z / (‖z‖ : ℂ)) =
      (t : ℂ) * conj (z / (‖z‖ : ℂ)) * m (z / (‖z‖ : ℂ))) :
    ‖dzbar (radialDiskExtension m) z‖ < ‖dz (radialDiskExtension m) z‖ ∧
      dilatationQuotient (radialDiskExtension m) z ≤ K := by
  obtain ⟨h1, h2⟩ := radialDiskExtension_norms_of_slope hz ht hm hn hd
  have hp : 0 < 1 + t := by linarith
  refine ⟨?_, ?_⟩
  · rw [h1, h2]
    have ha : |1 - t| < 1 + t := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  · unfold dilatationQuotient complexDilatation
    rw [norm_div, h1, h2]
    by_cases hle : t ≤ 1
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      calc (1 + ((1 - t) / 2) / ((1 + t) / 2)) /
          (1 - ((1 - t) / 2) / ((1 + t) / 2)) = t⁻¹ := by
            field_simp [ht.ne', hp.ne']
            ring
        _ ≤ K := hiK
    · rw [abs_of_neg (by linarith : 1 - t < 0)]
      calc (1 + (-(1 - t) / 2) / ((1 + t) / 2)) /
          (1 - (-(1 - t) / 2) / ((1 + t) / 2)) = t := by
            field_simp [ht.ne', hp.ne']
            ring
        _ ≤ K := htK

theorem hasDerivAt_blaschke_of_den {a z : ℂ} (hden : 1 - conj a * z ≠ 0) :
    HasDerivAt (blaschke a) ((1 - a * conj a) / (1 - conj a * z) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have hd : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_sub 1
  convert hnum.div hd hden using 1
  · rfl
  · ring

/-- The boundary angular slope of a rotation of a Blaschke factor is positive,
and both it and its reciprocal are bounded by `(1+|a|)/(1-|a|)`. -/
theorem rotationBlaschke_boundary_slope {c a ζ : ℂ}
    (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) (hζ : ‖ζ‖ = 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ (1 + ‖a‖) / (1 - ‖a‖) ∧
      t⁻¹ ≤ (1 + ‖a‖) / (1 - ‖a‖) ∧
      DifferentiableAt ℂ (fun w => c * blaschke a w) ζ ∧
      ‖c * blaschke a ζ‖ = 1 ∧
      deriv (fun w => c * blaschke a w) ζ = (t : ℂ) * conj ζ * (c * blaschke a ζ) := by
  have hden : 1 - conj a * ζ ≠ 0 := by
    intro h
    have he : (1 : ℂ) = conj a * ζ := sub_eq_zero.mp h
    have hh := congrArg norm he
    rw [norm_one, norm_mul, norm_conj, hζ, mul_one] at hh
    linarith
  have hζa : ζ - a ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [hζ] at he
    linarith
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζ]; exact one_ne_zero)
  have hζc0 : conj ζ ≠ 0 := by simpa using hζ0
  have hunit : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  have hconj : conj (1 - conj a * ζ) = conj ζ * (ζ - a) := by
    simp only [map_sub, map_one, map_mul, conj_conj]
    linear_combination -hunit
  have hnumpos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hdenpos : 0 < ‖1 - conj a * ζ‖ := norm_pos_iff.mpr hden
  let t : ℝ := (1 - ‖a‖ ^ 2) / ‖1 - conj a * ζ‖ ^ 2
  have ht : 0 < t := div_pos hnumpos (pow_pos hdenpos 2)
  have hlow : 1 - ‖a‖ ≤ ‖1 - conj a * ζ‖ := by
    simpa only [norm_one, norm_mul, norm_conj, hζ, mul_one] using norm_sub_norm_le (1 : ℂ) (conj a * ζ)
  have hupp : ‖1 - conj a * ζ‖ ≤ 1 + ‖a‖ := by
    simpa only [norm_one, norm_mul, norm_conj, hζ, mul_one] using norm_sub_le (1 : ℂ) (conj a * ζ)
  have hminus : 0 < 1 - ‖a‖ := sub_pos.mpr ha
  have hplus : 0 < 1 + ‖a‖ := by positivity
  have htupper : t ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
    apply (div_le_div_iff₀ (pow_pos hdenpos 2) hminus).mpr
    have hs : (1 - ‖a‖) ^ 2 ≤ ‖1 - conj a * ζ‖ ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs hplus.le
    nlinarith
  have htinv : t⁻¹ ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
    simp only [t, inv_div]
    apply (div_le_div_iff₀ hnumpos hminus).mpr
    have hs : ‖1 - conj a * ζ‖ ^ 2 ≤ (1 + ‖a‖) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs hminus.le
    nlinarith
  have hnorm : ‖ζ - a‖ = ‖1 - conj a * ζ‖ := by
    have hk := normSq_blaschke_key a ζ
    simp only [Complex.normSq_eq_norm_sq, hζ] at hk
    nlinarith [norm_nonneg (ζ - a)]
  have hmapnorm : ‖c * blaschke a ζ‖ = 1 := by
    rw [norm_mul, hc, one_mul, blaschke, norm_div, hnorm, div_self hdenpos.ne']
  have hd := (hasDerivAt_blaschke_of_den hden).const_mul c
  refine ⟨t, ht, htupper, htinv, hd.differentiableAt, hmapnorm, ?_⟩
  have hnumcast : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 1 - a * conj a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hdencast : ((‖1 - conj a * ζ‖ ^ 2 : ℝ) : ℂ) =
      (1 - conj a * ζ) * conj (1 - conj a * ζ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have htcast : (t : ℂ) = (1 - a * conj a) /
      ((1 - conj a * ζ) * conj (1 - conj a * ζ)) := by
    dsimp [t]
    rw [Complex.ofReal_div, hnumcast, hdencast]
  rw [hd.deriv, htcast, blaschke, hconj]
  field_simp [hden, hζa, hζc0] <;> ring

theorem radialRotationBlaschke_distortion {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖dzbar (radialDiskExtension (fun w => c * blaschke a w)) z‖ <
        ‖dz (radialDiskExtension (fun w => c * blaschke a w)) z‖ ∧
      dilatationQuotient (radialDiskExtension (fun w => c * blaschke a w)) z ≤
        (1 + ‖a‖) / (1 - ‖a‖) := by
  have hzn : 1 < ‖z‖ := hz
  obtain ⟨t, ht, htK, hiK, hm, hn, hd⟩ := rotationBlaschke_boundary_slope hc ha
    (norm_div_norm_eq_one (norm_ne_zero_iff.mp (by linarith)))
  exact radialDiskExtension_distortion_of_slope hzn ht htK hiK hm hn hd

theorem blaschke_den_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one, norm_mul, norm_conj] at hn
  have hb := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith

theorem blaschke_norm_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖blaschke a z‖ ≤ 1 := by
  have hd : 0 < ‖1 - conj a * z‖ := norm_pos_iff.mpr (blaschke_den_closed ha hz)
  have hk := normSq_blaschke_key a z
  simp only [Complex.normSq_eq_norm_sq] at hk
  have hp : 0 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖a‖ ^ 2) := by
    apply mul_nonneg <;> nlinarith [norm_nonneg z, norm_nonneg a]
  rw [blaschke, norm_div, div_le_one hd]
  nlinarith [norm_nonneg (z - a)]

theorem blaschke_norm_circle {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖blaschke a z‖ = 1 := by
  obtain ⟨t, ht, htK, hiK, hd, hn, he⟩ := rotationBlaschke_boundary_slope (c := 1) (by simp) ha hz
  simpa using hn

theorem blaschke_inverse_closed {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    blaschke (-a) (blaschke a z) = z := by
  have hden := blaschke_den_closed ha hz
  have hden' : (1 : ℂ) - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  have hne : (1 : ℂ) - conj a * a ≠ 0 := by
    simpa only [mul_comm] using one_sub_mul_conj_ne_zero ha
  have key : (1 : ℂ) - conj (-a) * blaschke a z =
      (1 - conj a * a) / (1 - conj a * z) := by
    simp only [blaschke, map_neg, neg_mul, sub_neg_eq_add]
    field_simp [hden, hden'] <;> ring
  have keynum : blaschke a z - -a = z * (1 - conj a * a) / (1 - conj a * z) := by
    simp only [blaschke, sub_neg_eq_add]
    field_simp [hden, hden'] <;> ring
  have hd2 : (1 : ℂ) - conj (-a) * blaschke a z ≠ 0 := by
    rw [key]
    exact div_ne_zero hne hden
  rw [blaschke, div_eq_iff hd2, keynum, key, mul_div_assoc]

theorem blaschke_closed_properties {a : ℂ} (ha : ‖a‖ < 1) :
    ContinuousOn (blaschke a) (closedBall (0 : ℂ) 1) ∧
      InjOn (blaschke a) (closedBall (0 : ℂ) 1) ∧
      blaschke a '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 ∧
      blaschke a '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
  refine ⟨fun z hz => (hasDerivAt_blaschke_of_den
    (blaschke_den_closed ha (mem_closedBall_zero_iff.mp hz))).continuousAt.continuousWithinAt, ?_, ?_, ?_⟩
  · intro z hz w hw he
    have hh := congrArg (blaschke (-a)) he
    rwa [blaschke_inverse_closed ha (mem_closedBall_zero_iff.mp hz),
      blaschke_inverse_closed ha (mem_closedBall_zero_iff.mp hw)] at hh
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_closedBall_zero_iff.mpr (blaschke_norm_closed ha (mem_closedBall_zero_iff.mp hz))
    · intro hw
      have han : ‖-a‖ < 1 := by simpa using ha
      refine ⟨blaschke (-a) w, mem_closedBall_zero_iff.mpr
        (blaschke_norm_closed han (mem_closedBall_zero_iff.mp hw)), ?_⟩
      simpa only [neg_neg] using blaschke_inverse_closed han (mem_closedBall_zero_iff.mp hw)
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr (blaschke_norm_circle ha (mem_sphere_zero_iff_norm.mp hz))
    · intro hw
      have han : ‖-a‖ < 1 := by simpa using ha
      refine ⟨blaschke (-a) w, mem_sphere_zero_iff_norm.mpr
        (blaschke_norm_circle han (mem_sphere_zero_iff_norm.mp hw)), ?_⟩
      simpa only [neg_neg] using blaschke_inverse_closed han (mem_sphere_zero_iff_norm.mp hw).le

theorem rotation_closed_images {c : ℂ} (hc : ‖c‖ = 1) :
    (fun z => c * z) '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 ∧
      (fun z => c * z) '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
  constructor
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [mem_closedBall_zero_iff, norm_mul, hc, one_mul] using hz
    · intro hw
      refine ⟨w / c, ?_, mul_div_cancel₀ w hc0⟩
      simpa only [mem_closedBall_zero_iff, norm_div, hc, div_one] using hw
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [mem_sphere_zero_iff_norm, norm_mul, hc, one_mul] using hz
    · intro hw
      refine ⟨w / c, ?_, mul_div_cancel₀ w hc0⟩
      simpa only [mem_sphere_zero_iff_norm, norm_div, hc, div_one] using hw

theorem radialRotationBlaschke_homeomorph {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) :
    IsHomeomorphOnto (radialDiskExtension (fun w => c * blaschke a w)) univ univ := by
  obtain ⟨hBc, hBi, hBcl, hBci⟩ := blaschke_closed_properties ha
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
  have hmc : ContinuousOn (fun w => c * blaschke a w) (closedBall (0 : ℂ) 1) := hBc.const_mul c
  have hmi : InjOn (fun w => c * blaschke a w) (closedBall (0 : ℂ) 1) :=
    fun z hz w hw he => hBi hz hw (mul_left_cancel₀ hc0 he)
  have hcl : (fun w => c * blaschke a w) '' closedBall (0 : ℂ) 1 = closedBall (0 : ℂ) 1 := by
    change ((fun w => c * w) ∘ blaschke a) '' _ = _
    rw [image_comp, hBcl, (rotation_closed_images hc).1]
  have hci : (fun w => c * blaschke a w) '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    change ((fun w => c * w) ∘ blaschke a) '' _ = _
    rw [image_comp, hBci, (rotation_closed_images hc).2]
  obtain ⟨e, he⟩ := radialDiskExtension_homeomorph hmc hmi hcl hci
  rw [← he]
  exact nxI1_isHomeomorphOnto_of_homeomorph e

theorem radialRotationBlaschke_isKQC_exterior {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) :
    IsKQC (radialDiskExtension (fun w => c * blaschke a w)) unitDiscExterior
      ((1 + ‖a‖) / (1 - ‖a‖)) := by
  have hhome := radialRotationBlaschke_homeomorph hc ha
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hmd : ContDiffOn ℂ 1 (fun w => c * blaschke a w) (sphere (0 : ℂ) 1) := by
    apply contDiffOn_const.mul
    unfold blaschke
    exact (contDiffOn_id.sub contDiffOn_const).div
      (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id))
      (fun z hz => blaschke_den_closed ha (mem_sphere_zero_iff_norm.mp hz).le)
  apply isKQC_of_isC1Quasiconformal
  refine ⟨hE, ?_, radialDiskExtension_contDiffOn_exterior (hmd.restrict_scalars ℝ),
    aqc_isHomeomorphOnto_restrict hhome isOpen_univ (subset_univ _) hE,
    fun z hz => radialRotationBlaschke_distortion hc ha hz⟩
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith [norm_nonneg a]

theorem radialRotationBlaschke_isKQC {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) :
    IsKQC (radialDiskExtension (fun w => c * blaschke a w)) univ
      ((1 + ‖a‖) / (1 - ‖a‖)) := by
  have hK : 1 ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
    apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
    nlinarith [norm_nonneg a]
  have hhome := radialRotationBlaschke_homeomorph hc ha
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)
  have hBi := (blaschke_closed_properties ha).2.1
  have hmi : InjOn (fun w => c * blaschke a w) unitDisc := by
    intro z hz w hw he
    exact hBi (ball_subset_closedBall hz) (ball_subset_closedBall hw) (mul_left_cancel₀ hc0 he)
  have hinside : IsKQC (radialDiskExtension (fun w => c * blaschke a w)) unitDisc
      ((1 + ‖a‖) / (1 - ‖a‖)) := by
    have hm := isKQC_one_of_conformal (show IsOpen unitDisc from isOpen_ball)
      ⟨(differentiableOn_blaschke ha).const_mul c, hmi, rfl⟩
    exact ad_isKQC_congr (hm.mono hK)
      (fun z hz => radialDiskExtension_eq_closed (ball_subset_closedBall hz))
  refine s13x_removable (L := sphere (0 : ℂ) 1) isOpen_univ hK
    (by rwa [hhome.2.2.1]) (Measure.addHaar_sphere volume 0 1) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => (abR_c_countable_circle x).mono fun y hy => by
      have h := abR_c_norm_eq_one (mem_sphere_zero_iff_norm.mp hy)
      change y ^ 2 + x ^ 2 = 1
      linarith
  · exact Filter.Eventually.of_forall fun y => (abR_c_countable_circle y).mono fun x hx =>
      abR_c_norm_eq_one (mem_sphere_zero_iff_norm.mp hx)
  · intro z hz
    have hn : ‖z‖ ≠ 1 := fun he => hz.2 (mem_sphere_zero_iff_norm.mpr he)
    by_cases hd : ‖z‖ < 1
    · exact ⟨unitDisc, isOpen_ball, mem_ball_zero_iff.mpr hd, subset_univ _, hinside⟩
    · exact ⟨unitDiscExterior, isOpen_lt continuous_const continuous_norm,
        (show 1 < ‖z‖ by have := not_lt.mp hd; rcases lt_or_eq_of_le this with h | h; exact h; exact (hn h.symm).elim),
        subset_univ _, radialRotationBlaschke_isKQC_exterior hc ha⟩

theorem radialDiskExtension_congr_closed {m n : ℂ → ℂ}
    (he : EqOn m n (closedBall (0 : ℂ) 1)) : radialDiskExtension m = radialDiskExtension n := by
  funext z
  unfold radialDiskExtension
  split_ifs with hz
  · exact he (mem_closedBall_zero_iff.mpr hz)
  · rw [he (mem_closedBall_zero_iff.mpr (norm_div_norm_eq_one
      (norm_ne_zero_iff.mp (by have := not_le.mp hz; linarith))).le)]

/-- The explicit radial extension of a conformal disk automorphism continuous
on the closed disk is a quasiconformal plane homeomorphism. -/
theorem radialDiskExtension_quasiconformal_of_conformal {m : ℂ → ℂ}
    (hm : IsConformalOnto m unitDisc unitDisc)
    (hc : ContinuousOn m (closedBall (0 : ℂ) 1)) :
    IsQuasiconformal (radialDiskExtension m) univ ∧
      radialDiskExtension m '' univ = univ := by
  obtain ⟨c, a, hc1, ha, he⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hm
  have hcB := (blaschke_closed_properties ha).1.const_mul c
  have hecl : EqOn m (fun w => c * blaschke a w) (closedBall (0 : ℂ) 1) :=
    he.of_subset_closure hc hcB ball_subset_closedBall
      (by rw [unitDisc, closure_ball _ one_ne_zero])
  rw [radialDiskExtension_congr_closed hecl]
  exact ⟨⟨(1 + ‖a‖) / (1 - ‖a‖), radialRotationBlaschke_isKQC hc1 ha⟩,
    (radialRotationBlaschke_homeomorph hc1 ha).2.2.1⟩

theorem conformal_disk_hasQCExtension_closed {m : ℂ → ℂ}
    (hm : IsConformalOnto m unitDisc unitDisc)
    (hc : ContinuousOn m (closedBall (0 : ℂ) 1)) :
    HasQCExtension m (closedBall (0 : ℂ) 1) :=
  ⟨radialDiskExtension m, (radialDiskExtension_quasiconformal_of_conformal hm hc).1,
    (radialDiskExtension_quasiconformal_of_conformal hm hc).2,
    fun _ hz => radialDiskExtension_eq_closed hz⟩

end TakhtajanTeo
