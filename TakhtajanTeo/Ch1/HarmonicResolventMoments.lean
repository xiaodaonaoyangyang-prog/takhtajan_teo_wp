import TakhtajanTeo.Ch1.S4_Metrics
import TakhtajanTeo.Ch1.ResolventRadialGreen

/-! Centered scalar resolvent moments for Lemma 5.8 (TT:2444–2462). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_power_log_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ n * Real.log t) volume 0 1 := by
  exact intervalIntegral.intervalIntegrable_log'.continuousOn_mul (continuous_pow n).continuousOn

theorem wp_power_log_moment (n : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ n * Real.log t) = -1 / (n + 1 : ℝ) ^ 2 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hc : Continuous (fun t : ℝ =>
      t ^ (n + 1) * Real.log t / (n + 1) - t ^ (n + 1) / (n + 1 : ℝ) ^ 2) := by
    convert (((continuous_id.pow n).mul Real.continuous_mul_log).div_const (n + 1)).sub
      ((continuous_id.pow (n + 1)).div_const ((n + 1 : ℝ) ^ 2)) using 1
    funext t
    dsimp
    rw [pow_succ]
    ring
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ =>
        t ^ (n + 1) * Real.log t / (n + 1) - t ^ (n + 1) / (n + 1 : ℝ) ^ 2)
        (t ^ n * Real.log t) t := by
    convert (((hasDerivAt_pow (n + 1) t).mul (Real.hasDerivAt_log ht.1.ne')).div_const
      (n + 1 : ℝ)).sub ((hasDerivAt_pow (n + 1) t).div_const ((n + 1 : ℝ) ^ 2)) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    field_simp [ht.1.ne', hn]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn hd (wp_power_log_intervalIntegrable n)
  simpa [div_eq_mul_inv] using hi

theorem wp_resolvent_profile_moment (n : ℕ) :
    (∫ t in (0 : ℝ)..1,
      t ^ n * (-(1 - t ^ 2) / 2 * Real.log t - (1 - t) ^ 2)) =
        2 / ((n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) := by
  have hp (k : ℕ) : IntervalIntegrable (fun t : ℝ => t ^ k) volume 0 1 :=
    (continuous_pow k).intervalIntegrable 0 1
  have he (t : ℝ) :
      t ^ n * (-(1 - t ^ 2) / 2 * Real.log t - (1 - t) ^ 2) =
        (-1 / 2) * (t ^ n * Real.log t) + (1 / 2) * (t ^ (n + 2) * Real.log t) -
          t ^ n + 2 * t ^ (n + 1) - t ^ (n + 2) := by
    simp only [pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    ((((wp_power_log_intervalIntegrable n).const_mul (-1 / 2)).add
      ((wp_power_log_intervalIntegrable (n + 2)).const_mul (1 / 2))).sub (hp n) |>.add
        ((hp (n + 1)).const_mul 2)) (hp (n + 2)),
    intervalIntegral.integral_add
      ((((wp_power_log_intervalIntegrable n).const_mul (-1 / 2)).add
        ((wp_power_log_intervalIntegrable (n + 2)).const_mul (1 / 2))).sub (hp n))
      ((hp (n + 1)).const_mul 2),
    intervalIntegral.integral_sub
      (((wp_power_log_intervalIntegrable n).const_mul (-1 / 2)).add
        ((wp_power_log_intervalIntegrable (n + 2)).const_mul (1 / 2))) (hp n),
    intervalIntegral.integral_add (wp_power_log_intervalIntegrable n |>.const_mul (-1 / 2))
      (wp_power_log_intervalIntegrable (n + 2) |>.const_mul (1 / 2))]
  simp only [intervalIntegral.integral_const_mul, wp_power_log_moment, integral_pow,
    one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have h3 : (n + 3 : ℝ) ≠ 0 := by positivity
  ring_nf at h1 h2 h3 ⊢
  field_simp
  <;> ring


theorem wp_resolvent_moment_radial_jacobian (n : ℕ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    2 * π * r * (resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹) =
      (1 / 4 : ℝ) * (2 * r * ((r ^ 2) ^ n *
        (-(1 - (r ^ 2) ^ 2) / 2 * Real.log (r ^ 2) - (1 - r ^ 2) ^ 2))) := by
  have hrd : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  rw [resolvent_center_radius_log_formula]
  simp only [rho, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, Real.log_pow]
  rw [← pow_mul]
  field_simp
  <;> ring

theorem wp_resolvent_moment_radius_integral (n : ℕ) :
    (∫ r in Ioo (0 : ℝ) 1,
      2 * π * r * (resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹)) =
        1 / (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) := by
  let f : ℝ → ℝ := fun t =>
    t ^ n * (-(1 - t ^ 2) / 2 * Real.log t - (1 - t) ^ 2)
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r) (g := f)
    (by fun_prop)
    (fun r _ => by simpa using hasDerivAt_pow 2 r)
    (by
      intro r hr
      have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1.le
      positivity)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at hs
  have hs' : (∫ r in Ioo (0 : ℝ) 1, 2 * r * f (r ^ 2)) =
      ∫ t in (0 : ℝ)..1, f t := by
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), one_pow, mul_comm] using hs
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, (1 / 4 : ℝ) * (2 * r * f (r ^ 2)) :=
      setIntegral_congr_fun measurableSet_Ioo (fun r hr => wp_resolvent_moment_radial_jacobian n hr)
    _ = (1 / 4 : ℝ) * ∫ t in (0 : ℝ)..1, f t := by rw [integral_const_mul, hs']
    _ = _ := by
      rw [show (∫ t in (0 : ℝ)..1, f t) =
        2 / ((n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) from wp_resolvent_profile_moment n]
      field_simp
      ring

theorem wp_resolvent_monomial_moment (n : ℕ) :
    (∫ w in unitDisc, resolventKernel 0 w * ‖w‖ ^ (2 * n) * (rho w)⁻¹) =
      1 / (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) := by
  calc
    _ = ∫ w in unitDisc,
        resolventKernel 0 (‖w‖ : ℂ) * ‖w‖ ^ (2 * n) * (rho (‖w‖ : ℂ))⁻¹ := by
      apply integral_congr_ae
      filter_upwards with w
      simp [resolventKernel, pointPair, rho, Complex.norm_real, abs_of_nonneg (norm_nonneg w)]
    _ = 2 * π * ∫ r in Ioo (0 : ℝ) 1,
        r * (resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹) :=
      integral_unitDisc_radial (fun r : ℝ =>
        resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹)
    _ = ∫ r in Ioo (0 : ℝ) 1,
        2 * π * r * (resolventKernel 0 (r : ℂ) * r ^ (2 * n) * (rho (r : ℂ))⁻¹) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring
    _ = _ := wp_resolvent_moment_radius_integral n

end TakhtajanTeo


