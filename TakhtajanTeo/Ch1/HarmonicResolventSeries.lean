import TakhtajanTeo.Ch1.HarmonicResolventMoments
import LiZhongQC.Lemmas.GreenPolar

/-! Circle Parseval and integrable polar transport for Lemma 5.8 (TT:2444–2462). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_disk_series_fourierCoeff_negative {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m : ℤ} (hm : m < 0) :
    fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) m = 0 := by
  have hsum := disk_series_summable_norm hc hr0 hr1
  have hexpnorm (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := by simp [norm_exp]
  have hrad (θ : ℝ) : ‖(r : ℂ) * exp (θ * I)‖ = r := by
    rw [norm_mul, hexpnorm, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hneg (θ : ℝ) : ‖exp (-(m * θ * I))‖ = 1 := by simp [norm_exp]
  let f : ℕ → ℝ → ℂ := fun n θ => c n * ((r : ℂ) * exp (θ * I)) ^ n * exp (-(m * θ * I))
  have hi := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    (F := f) (f := fun θ => F ((r : ℂ) * exp (θ * I)) * exp (-(m * θ * I)))
    (fun n _ => ‖c n‖ * r ^ n)
    (fun n => by dsimp [f]; fun_prop)
    (fun n => Filter.Eventually.of_forall fun θ => by
      simp only [f, norm_mul, norm_pow, hrad, hneg, mul_one, le_refl])
    (Filter.Eventually.of_forall fun _ => hsum)
    (integrable_const _)
    (Filter.Eventually.of_forall fun θ =>
      (hc _ (mem_ball_zero_iff.mpr (by rw [hrad]; exact hr1))).mul_right _)
  have hi' := hi.mul_left (1 / (2 * π : ℂ))
  have hiC : HasSum (fun n => fourierCoeff
      (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) m)
      (fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) m) := by
    simpa only [fourierCoeff, intervalIntegral.integral_of_le Real.two_pi_pos.le, f] using hi'
  have hcoeff (n : ℕ) : fourierCoeff
      (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) m = 0 := by
    have hfun : (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) =
        fun θ : ℝ => (c n * (r : ℂ) ^ n) * exp ((n : ℤ) * θ * I) := by
      funext θ
      rw [mul_pow, ← exp_nat_mul]
      push_cast
      ring_nf
    rw [hfun, fourierCoeff_const_mul, fourierCoeff_exponential]
    have hmn : m ≠ (n : ℤ) := by omega
    simp [hmn]
  simp_rw [hcoeff] at hiC
  exact hiC.tsum_eq.symm.trans (by simp)

theorem wp_disk_series_circle_energy {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    (hf : ContinuousOn F unitDisc) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => ‖c n‖ ^ 2 * r ^ (2 * n))
      (Real.circleAverage (fun z => ‖F z‖ ^ 2) 0 r) := by
  have hrad (θ : ℝ) : ‖(r : ℂ) * exp (θ * I)‖ = r := by
    simp [norm_mul, norm_exp, abs_of_nonneg hr0]
  have hz (θ : ℝ) : (r : ℂ) * exp (θ * I) ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [hrad]; exact hr1)
  have hcont : Continuous (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) :=
    hf.comp_continuous (by fun_prop) hz
  have hsum := disk_series_summable_norm hc hr0 hr1
  have hnorm (n : ℕ) (θ : ℝ) :
      ‖c n * ((r : ℂ) * exp (θ * I)) ^ n‖ = ‖c n‖ * r ^ n := by
    rw [norm_mul, norm_pow, hrad]
  have hb (θ : ℝ) : ‖F ((r : ℂ) * exp (θ * I))‖ ≤ ∑' n, ‖c n‖ * r ^ n := by
    rw [← (hc _ (hz θ)).tsum_eq]
    have hi : Summable (fun n => ‖c n * ((r : ℂ) * exp (θ * I)) ^ n‖) := by
      simpa only [hnorm] using hsum
    simpa only [hnorm] using norm_tsum_le_tsum_norm hi
  have hL2 : MemLp (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) 2
      (volume.restrict (Ioc 0 (2 * π))) :=
    MemLp.of_bound hcont.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hP := fourierCoeff_hasSum_sq hL2
  have hneg (m : ℤ) (hm : m ∉ Set.range (fun n : ℕ => (n : ℤ))) :
      ‖fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) m‖ ^ 2 = 0 := by
    have hm0 : m < 0 := by
      by_contra h
      exact hm ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [wp_disk_series_fourierCoeff_negative hc hr0 hr1 hm0]
    norm_num
  have h := (Int.ofNat_injective.hasSum_iff hneg).mpr hP
  change HasSum (fun n : ℕ =>
    ‖fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) (n : ℤ)‖ ^ 2) _ at h
  simpa only [Function.comp_def, disk_series_fourierCoeff hc hr0 hr1, norm_mul,
    norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, mul_pow, ← pow_mul,
    Nat.mul_comm, Real.circleAverage, smul_eq_mul, circleMap, zero_add] using h

theorem wp_integrable_disk_polar_real {F : ℂ → ℝ}
    (hm : Measurable F) (hi : IntegrableOn F unitDisc) :
    Integrable (fun p : ℝ × ℝ => p.1 * F (circleMap 0 p.1 p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (-π) π))) := by
  have hmC : Measurable (fun z => (F z : ℂ)) := Complex.continuous_ofReal.measurable.comp hm
  have hiC : IntegrableOn (fun z => (F z : ℂ)) unitDisc := hi.ofReal
  have hp := integrableOn_polar_of_integrableOn_ball hmC hiC
  have he (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simpa using polarCoord_symm_add_eq_circleMap 0 p.1 p.2
  have h : IntegrableOn (fun p : ℝ × ℝ =>
      ((p.1 : ℂ) * (F (Complex.polarCoord.symm p) : ℂ)).re)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := hp.re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    he] at h
  rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h

theorem wp_disk_circleAverage_integrable {F : ℂ → ℝ}
    (hm : Measurable F) (hi : IntegrableOn F unitDisc) :
    IntegrableOn (fun r => 2 * π * r * Real.circleAverage F 0 r) (Ioo (0 : ℝ) 1) := by
  have h := (wp_integrable_disk_polar_real hm hi).integral_prod_left
  apply h.congr
  filter_upwards with r
  rw [integral_const_mul, integral_circleMap_neg_pi_pi]
  ring

theorem wp_disk_integral_circleAverage {F : ℂ → ℝ}
    (hm : Measurable F) (hi : IntegrableOn F unitDisc) :
    (∫ z in unitDisc, F z) =
      ∫ r in Ioo (0 : ℝ) 1, 2 * π * r * Real.circleAverage F 0 r := by
  have h := setIntegral_ball_zero_polar (fun z => (F z : ℂ)) 1
  have he (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simpa using polarCoord_symm_add_eq_circleMap 0 p.1 p.2
  simp only [← Complex.ofReal_mul, integral_ofReal, he] at h
  have hR : (∫ z in unitDisc, F z) =
      ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π, p.1 * F (circleMap 0 p.1 p.2) := by
    exact_mod_cast h
  rw [hR, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod _ (wp_integrable_disk_polar_real hm hi)]
  apply integral_congr_ae
  filter_upwards with r
  rw [integral_const_mul, integral_circleMap_neg_pi_pi]
  ring

end TakhtajanTeo


