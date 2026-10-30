import TakhtajanTeo.Ch1.S1_2_Homogeneous

/-! # Circle quasisymmetry of the actual Model A map

Scale-normalized QC distortion and the inverse-map estimate give a full
three-point control function. Möbius postcomposition transfers it to `wA`.
No equivalence of competing definitions of quasisymmetry is assumed.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem planeQC_weak_ratio {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) {b x z : ℂ} (h : ‖x - b‖ ≤ ‖z - b‖) :
    ‖f x - f b‖ ≤ lambdaInv K * ‖f z - f b‖ := by
  have hL : 0 ≤ lambdaInv K := (td_one_le_lambdaInv hf.2.1).trans' zero_le_one
  by_cases hxb : x = b
  · subst x
    simpa using mul_nonneg hL (norm_nonneg (f z - f b))
  have hr : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxb)
  have hout : f z ∉ f '' ball b ‖x - b‖ := by
    rintro ⟨u, hu, he⟩
    have huz := hf.2.2.1.2.1 (mem_univ u) (mem_univ z) he
    subst u
    have hz := mem_ball.mp hu
    rw [dist_eq_norm] at hz
    exact (not_lt.mpr h) hz
  obtain ⟨s, hs0, hs1, hbound, -⟩ := tp_a_side hf hs hr rfl hout
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hs1) hL)

/-- A scale-independent small-ratio estimate, the analytic step in full QS. -/
theorem planeQC_ratio_half {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) {b x z : ℂ} (hzb : z ≠ b)
    (hsmall : ‖x - b‖ / ‖z - b‖ ≤ 1 / 2) :
    ‖f x - f b‖ / ‖f z - f b‖ ≤
      (16 * lambdaInv K) * (‖x - b‖ / ‖z - b‖) ^ (1 / K) := by
  have hK : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hL : 1 ≤ lambdaInv K := td_one_le_lambdaInv hf.2.1
  have hLpos : 0 < lambdaInv K := lt_of_lt_of_le one_pos hL
  have hr : 0 < ‖z - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzb)
  have hi : Function.Injective f := fun a c h => hf.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hd : 0 < ‖f z - f b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hzb))
  let A : ℝ := 2 * lambdaInv K * ‖f z - f b‖
  have hA : 0 < A := by dsimp [A]; positivity
  let F : ℂ → ℂ := fun u => (f ((‖z - b‖ : ℂ) * u + b) - f b) / (A : ℂ)
  have hFqc : IsKQC F unitDisc K := by
    have hcomp := (b4_rat_affine_comp hf hs b (-(A : ℂ)⁻¹ * f b)
      (α := (‖z - b‖ : ℂ)) (γ := (A : ℂ)⁻¹)
      (by exact_mod_cast hr.ne') (inv_ne_zero (by exact_mod_cast hA.ne'))).1
    have he : (fun u : ℂ => (A : ℂ)⁻¹ * f ((‖z - b‖ : ℂ) * u + b) +
        -(A : ℂ)⁻¹ * f b) = F := by funext u; dsimp [F]; ring
    rw [he] at hcomp
    exact ac_t_isKQC_restrict hcomp isOpen_ball (subset_univ _)
  have hFimage : F '' unitDisc ⊆ unitDisc := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hloc : ‖(‖z - b‖ : ℂ) * u + b - b‖ ≤ ‖z - b‖ := by
      rw [add_sub_cancel_right, norm_mul, Complex.norm_of_nonneg (norm_nonneg _)]
      exact mul_le_of_le_one_right hr.le hu'.le
    have hbnd := planeQC_weak_ratio hf hs hloc
    rw [unitDisc, mem_ball_zero_iff]
    dsimp [F]
    rw [norm_div, Complex.norm_of_nonneg hA.le, div_lt_iff₀ hA]
    dsimp [A]
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hL) hd]
  have hF0 : F 0 = 0 := by simp [F]
  let u : ℂ := (x - b) / (‖z - b‖ : ℂ)
  have huNorm : ‖u‖ = ‖x - b‖ / ‖z - b‖ := by
    dsimp [u]
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
  have hu : u ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [huNorm]; linarith)
  have hbnd := eq15_2 ⟨hFqc, hFimage⟩ hF0 hu
  have hpow4 : (4 : ℝ) ^ (1 - 1 / K) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - 1 / K) ≤ (4 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [one_div_pos.mpr hK])
      _ = 4 := Real.rpow_one 4
  have hbase : (1 / 2 : ℝ) ≤ 1 - ‖u‖ ^ 2 := by
    have hu0 := norm_nonneg u
    rw [← huNorm] at hsmall
    nlinarith
  have hbase1 : 1 - ‖u‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖u‖]
  have hden : (1 / 2 : ℝ) ≤ (1 - ‖u‖ ^ 2) ^ (1 / (2 * K)) := by
    apply hbase.trans
    calc 1 - ‖u‖ ^ 2 = (1 - ‖u‖ ^ 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by linarith) hbase1
        ((div_le_iff₀ (by positivity : 0 < 2 * K)).mpr (by nlinarith [hf.2.1]))
  have hscalar : ‖F u‖ ≤ 8 * ‖u‖ ^ (1 / K) := by
    apply hbnd.trans
    apply (div_le_iff₀ (by linarith : 0 < (1 - ‖u‖ ^ 2) ^ (1 / (2 * K)))).mpr
    have hp := Real.rpow_nonneg (norm_nonneg u) (1 / K)
    nlinarith [mul_le_mul_of_nonneg_right hpow4 hp,
      mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hp)]
  have hFu : F u = (f x - f b) / (A : ℂ) := by
    dsimp [F, u]
    congr 2
    field_simp [show (‖z - b‖ : ℂ) ≠ 0 by exact_mod_cast hr.ne']
    ring
  rw [hFu, norm_div, Complex.norm_of_nonneg hA.le, huNorm] at hscalar
  have hmul := (div_le_iff₀ hA).mp hscalar
  apply (div_le_iff₀ hd).mpr
  dsimp [A] at hmul
  nlinarith

theorem planeQC_ratio_one {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) {b x z : ℂ} (hzb : z ≠ b)
    (hsmall : ‖x - b‖ / ‖z - b‖ ≤ 1) :
    ‖f x - f b‖ / ‖f z - f b‖ ≤
      (16 * lambdaInv K) * (‖x - b‖ / ‖z - b‖) ^ (1 / K) := by
  by_cases hhalf : ‖x - b‖ / ‖z - b‖ ≤ 1 / 2
  · exact planeQC_ratio_half hf hs hzb hhalf
  have ht : 1 / 2 < ‖x - b‖ / ‖z - b‖ := not_le.mp hhalf
  have hK : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hL : 1 ≤ lambdaInv K := td_one_le_lambdaInv hf.2.1
  have hr : 0 < ‖z - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzb)
  have hi : Function.Injective f := fun a c h => hf.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hd : 0 < ‖f z - f b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hzb))
  have hp : ‖x - b‖ / ‖z - b‖ ≤ (‖x - b‖ / ‖z - b‖) ^ (1 / K) := by
    calc _ = (‖x - b‖ / ‖z - b‖) ^ (1 : ℝ) := (Real.rpow_one _).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by linarith) hsmall
           ((div_le_iff₀ hK).mpr (by simpa using hf.2.1))
  have hw := planeQC_weak_ratio hf hs ((div_le_one hr).mp hsmall)
  apply (div_le_iff₀ hd).mpr
  have hcoeff : lambdaInv K ≤ (16 * lambdaInv K) * (‖x - b‖ / ‖z - b‖) ^ (1 / K) := by
    nlinarith [mul_pos (lt_of_lt_of_le one_pos hL)
      (show 0 < (‖x - b‖ / ‖z - b‖) ^ (1 / K) - 1 / 2 by linarith)]
  exact hw.trans (mul_le_mul_of_nonneg_right hcoeff hd.le)

theorem planeQC_ratio_large {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) {b x z : ℂ} (hzb : z ≠ b)
    (ht : 1 < ‖x - b‖ / ‖z - b‖) :
    ‖f x - f b‖ / ‖f z - f b‖ ≤
      (16 * lambdaInv K) ^ K * (‖x - b‖ / ‖z - b‖) ^ K := by
  have hK : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hC : 1 ≤ 16 * lambdaInv K := by nlinarith [td_one_le_lambdaInv hf.2.1]
  have hr : 0 < ‖z - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzb)
  have hx : x ≠ b := by intro h; norm_num [h] at ht
  have hi : Function.Injective f := fun a c h => hf.2.2.1.2.1 (mem_univ _) (mem_univ _) h
  have hd : 0 < ‖f z - f b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hzb))
  have ha : 0 < ‖f x - f b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hx))
  have hxr : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  by_cases hsmall : ‖f x - f b‖ / ‖f z - f b‖ ≤ 1
  · exact hsmall.trans (one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hC hK.le) (Real.one_le_rpow ht.le hK.le))
  let g := Function.invFunOn f univ
  have hg : IsKQC g univ K := by
    have h := thm7_2_inv hf
    rwa [hs] at h
  have hgs : g '' univ = univ := by
    have h := (isHomeomorphOnto_invFunOn hf.2.2.1).2.2.1
    rwa [hs] at h
  have hleft : ∀ y, g (f y) = y := fun y => hi.injOn.leftInvOn_invFunOn (mem_univ y)
  have hrev : ‖f z - f b‖ / ‖f x - f b‖ ≤ 1 :=
    (div_le_one ha).mpr (by have := (one_lt_div hd).mp (not_le.mp hsmall); linarith)
  have hest := planeQC_ratio_one hg hgs (hi.ne hx) hrev
  simp only [hleft] at hest
  let t := ‖x - b‖ / ‖z - b‖
  let s := ‖f x - f b‖ / ‖f z - f b‖
  have ht0 : 0 < t := div_pos hxr hr
  have hs0 : 0 < s := div_pos ha hd
  have htInv : ‖z - b‖ / ‖x - b‖ = 1 / t := by dsimp [t]; field_simp
  have hsInv : ‖f z - f b‖ / ‖f x - f b‖ = 1 / s := by dsimp [s]; field_simp
  rw [htInv, hsInv, Real.div_rpow zero_le_one hs0.le, Real.one_rpow,
    ← mul_div_assoc, mul_one] at hest
  have hp : s ^ (1 / K) ≤ (16 * lambdaInv K) * t := by
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hs0 _)).mp hest
    have hh' : s ^ (1 / K) / t ≤ 16 * lambdaInv K := by simpa [div_eq_mul_inv, mul_comm] using hh
    exact (div_le_iff₀ ht0).mp hh'
  have hpK := Real.rpow_le_rpow (Real.rpow_nonneg hs0.le _) hp hK.le
  rw [← Real.rpow_mul hs0.le, div_mul_cancel₀ _ hK.ne', Real.rpow_one,
    Real.mul_rpow (by linarith : 0 ≤ 16 * lambdaInv K) ht0.le] at hpK
  exact hpK

theorem planeQC_circle_quasisymmetric {f : ℂ → ℂ} {K : ℝ}
    (hf : IsKQC f univ K) (hs : f '' univ = univ) : Pommerenke1992.IsQuasisymmetric f := by
  let C := 16 * lambdaInv K
  have hK : 0 < K := lt_of_lt_of_le one_pos hf.2.1
  have hC : 0 < C := by dsimp [C]; nlinarith [td_one_le_lambdaInv hf.2.1]
  have ha : 0 < 1 / K := one_div_pos.mpr hK
  refine ⟨fun t : ℝ => C * t ^ (1 / K) + C ^ K * t ^ K,
    hf.2.2.1.2.1.mono (subset_univ _), ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left (Real.strictMonoOn_rpow_Ici_of_exponent_pos ha hx hy hxy) hC)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy.le hK.le) (Real.rpow_nonneg hC.le K))
  · exact ((Real.continuous_rpow_const ha.le).const_mul C |>.add
      ((Real.continuous_rpow_const hK.le).const_mul (C ^ K))).continuousOn
  · simp only [Real.zero_rpow ha.ne', Real.zero_rpow hK.ne', mul_zero, add_zero]
  · intro x hx b hb z hz hbz
    have hzb := hbz.symm
    have ht0 : 0 ≤ ‖x - b‖ / ‖z - b‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_sub_rev (f b) (f z), norm_sub_rev b z]
    by_cases ht : ‖x - b‖ / ‖z - b‖ ≤ 1
    · exact (planeQC_ratio_one hf hs hzb ht).trans
        (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hC.le K) (Real.rpow_nonneg ht0 K)))
    · exact (planeQC_ratio_large hf hs hzb (not_le.mp ht)).trans
        (le_add_of_nonneg_left (mul_nonneg hC.le (Real.rpow_nonneg ht0 (1 / K))))

theorem mobius_circle_ratio_bound {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hden : ∀ z ∈ sphere (0 : ℂ) 1, c * z + d ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ InjOn (mobiusFn a b c d) (sphere (0 : ℂ) 1) ∧
      ∀ x ∈ sphere (0 : ℂ) 1, ∀ y ∈ sphere (0 : ℂ) 1, ∀ z ∈ sphere (0 : ℂ) 1,
        y ≠ z → ‖mobiusFn a b c d x - mobiusFn a b c d y‖ /
          ‖mobiusFn a b c d y - mobiusFn a b c d z‖ ≤ L * (‖x - y‖ / ‖y - z‖) := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn
    ⟨1, by simp⟩ (show ContinuousOn (fun z : ℂ => ‖c * z + d‖) (sphere 0 1) by fun_prop)
  have hm : 0 < ‖c * p + d‖ := norm_pos_iff.mpr (hden p hp)
  let B : ℝ := ‖c‖ + ‖d‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hupper : ∀ z ∈ sphere (0 : ℂ) 1, ‖c * z + d‖ ≤ B := by
    intro z hz
    have he : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    calc ‖c * z + d‖ ≤ ‖c * z‖ + ‖d‖ := norm_add_le _ _
      _ ≤ B := by rw [norm_mul, he, mul_one]; dsimp [B]; linarith
  refine ⟨B / ‖c * p + d‖, div_pos hB hm, ?_, ?_⟩
  · intro x hx y hy he
    have h : mobiusExt a b c d (x : ExtPlane) = mobiusExt a b c d (y : ExtPlane) := by
      rw [mobiusExt_coe (hden x hx), mobiusExt_coe (hden y hy), he]
    exact OnePoint.coe_injective (isMobius_injective ⟨a, b, c, d, hdet, rfl⟩ h)
  · intro x hx y hy z hz hyz
    have hdiff : ∀ u ∈ sphere (0 : ℂ) 1, ∀ v ∈ sphere (0 : ℂ) 1,
        mobiusFn a b c d u - mobiusFn a b c d v =
          (a * d - b * c) * (u - v) / ((c * u + d) * (c * v + d)) := by
      intro u hu v hv
      dsimp [mobiusFn]
      rw [div_sub_div _ _ (hden u hu) (hden v hv)]
      congr 1
      ring
    have he : ‖mobiusFn a b c d x - mobiusFn a b c d y‖ /
        ‖mobiusFn a b c d y - mobiusFn a b c d z‖ =
        (‖x - y‖ / ‖y - z‖) * (‖c * z + d‖ / ‖c * x + d‖) := by
      rw [hdiff x hx y hy, hdiff y hy z hz]
      simp only [norm_div, norm_mul]
      field_simp [norm_ne_zero_iff.mpr hdet, norm_ne_zero_iff.mpr (hden x hx),
        norm_ne_zero_iff.mpr (hden y hy), norm_ne_zero_iff.mpr (hden z hz),
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyz)]
      <;> ring
    rw [he, mul_comm (B / ‖c * p + d‖)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    exact (div_le_div_of_nonneg_right (hupper z hz) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hB.le hm (hmin hx))

theorem circleQS_mobius_postcompose {f : ℂ → ℂ} (hf : Pommerenke1992.IsQuasisymmetric f)
    (hcircle : MapsTo f (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1))
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hden : ∀ z ∈ sphere (0 : ℂ) 1, c * z + d ≠ 0) :
    Pommerenke1992.IsQuasisymmetric (fun z => mobiusFn a b c d (f z)) := by
  obtain ⟨lam, hi, hmono, hcont, h0, hbound⟩ := hf
  obtain ⟨L, hL, hMi, hMb⟩ := mobius_circle_ratio_bound hdet hden
  refine ⟨fun t => L * lam t, hMi.comp hi hcircle, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact mul_lt_mul_of_pos_left (hmono hx hy hxy) hL
  · exact hcont.const_mul L
  · change L * lam 0 = 0
    rw [h0, mul_zero]
  · intro x hx y hy z hz hyz
    exact (hMb (f x) (hcircle hx) (f y) (hcircle hy) (f z) (hcircle hz)
      (fun he => hyz (hi hy hz he))).trans
      (mul_le_mul_of_nonneg_left (hbound x hx y hy z hz hyz) hL.le)

theorem circleQS_congr {f g : ℂ → ℂ} (hf : Pommerenke1992.IsQuasisymmetric f)
    (he : EqOn g f (sphere (0 : ℂ) 1)) : Pommerenke1992.IsQuasisymmetric g := by
  obtain ⟨lam, hi, hm, hc, h0, hb⟩ := hf
  refine ⟨lam, ?_, hm, hc, h0, ?_⟩
  · intro x hx y hy hxy
    apply hi hx hy
    rw [← he hx, ← he hy]
    exact hxy
  · intro x hx y hy z hz hyz
    rw [he hx, he hy, he hz]
    exact hb x hx y hy z hz hyz

/-- The actual Model A boundary map satisfies the full three-point definition
of circle quasisymmetry, without using the open equivalence of QS definitions. -/
theorem wA_circle_quasisymmetric {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Pommerenke1992.IsQuasisymmetric (wA μ) := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hwf, hwi, -, -, -⟩ := wA_spec hμ
  obtain ⟨K, hK⟩ := hW.1
  have hden : ∀ z ∈ sphere (0 : ℂ) 1, c * z + d ≠ 0 := by
    intro z hz hn
    have hmem : z ∈ W '' univ := by rw [hW.2.1]; trivial
    obtain ⟨u, -, hu⟩ := hmem
    have hu1 : ‖u‖ = 1 := normalized_solution_circle_iff hW
      (by rw [hu]; exact mem_sphere_zero_iff_norm.mp hz)
    obtain ⟨v, -, hv⟩ := wAS_maps_circle hμ hu1
    have he := hwf u
    rw [hu, mobiusExt_coe_of_eq_zero hn] at he
    exact OnePoint.coe_ne_infty v (hv.symm.trans he)
  have hcircle : MapsTo W (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
    intro z hz
    exact mem_sphere_zero_iff_norm.mpr (normalized_solution_circle hW
      (mem_sphere_zero_iff_norm.mp hz))
  have hqs := circleQS_mobius_postcompose (planeQC_circle_quasisymmetric hK hW.2.1)
    hcircle hdet hden
  apply circleQS_congr hqs
  intro z hz
  unfold wA
  rw [hwf, mobiusExt_coe (hden (W z) (hcircle hz))]
  rfl

end TakhtajanTeo
