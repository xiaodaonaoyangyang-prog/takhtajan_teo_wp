import TakhtajanTeo.Ch1.QCVariationKernel

/-! # Vanishing Laurent moments of an infinitesimal Bers-kernel element -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

theorem qcv_cauchyPower_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    {z w : ℂ} (hz : ‖z‖ ≤ ρ) (hw : 1 < ‖w‖) (n : ℕ) :
    ‖(1 : ℂ) / (w - z) ^ (n + 4)‖ ≤
      ((1 - ρ)⁻¹ ^ n * (12 / (1 - ρ) ^ 4)) * ‖ahKer (-1) w‖ := by
  have hq : 0 < 1 - ρ := by linarith
  have hd : 1 - ρ ≤ ‖w - z‖ := by
    have := norm_sub_norm_le w z
    linarith
  have hi : ‖w - z‖⁻¹ ≤ (1 - ρ)⁻¹ := inv_anti₀ hq hd
  have hfour : ‖w - z‖⁻¹ ^ 4 ≤ (12 / (1 - ρ) ^ 4) * ‖ahKer (-1) w‖ := by
    have hb := (qcv_ker_majorant hρ0 hρ hz hw).2.2.2
    have hh : ‖w - z‖⁻¹ ^ 4 ≤ ‖kerD3 z w‖ := by
      simp only [kerD3, norm_div, norm_pow, Complex.norm_ofNat]
      rw [inv_pow, ← one_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact hh.trans hb
  rw [norm_div, norm_one, norm_pow, one_div, pow_add, mul_inv]
  calc (‖w - z‖ ^ n)⁻¹ * (‖w - z‖ ^ 4)⁻¹
      ≤ (1 - ρ)⁻¹ ^ n * ((12 / (1 - ρ) ^ 4) * ‖ahKer (-1) w‖) := by
        rw [← inv_pow, ← inv_pow]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hi n) hfour
          (by positivity) (by positivity)
    _ = _ := by ring

theorem qcv_cauchyPower_hasDerivAt (n : ℕ) {z w : ℂ} (hwz : w - z ≠ 0) :
    HasDerivAt (fun x : ℂ => (1 : ℂ) / (w - x) ^ (n + 4))
      ((n + 4 : ℂ) / (w - z) ^ (n + 5)) z := by
  have h := (((hasDerivAt_id z).const_sub w).pow (n + 4)).inv
    (pow_ne_zero _ hwz)
  change HasDerivAt (fun x : ℂ => ((w - x) ^ (n + 4))⁻¹)
    (-((n + 4 : ℕ) * (w - z) ^ (n + 4 - 1) * (-1 : ℂ)) /
      ((w - z) ^ (n + 4)) ^ 2) z at h
  convert h using 1
  · simp only [one_div]
  · simp only [Nat.cast_add, Nat.cast_ofNat, mul_neg, mul_one,
      neg_neg]
    rw [show n + 4 - 1 = n + 3 by omega]
    simp only [pow_add]
    field_simp [hwz]

theorem qcv_cauchyMoment_hasDerivAt (μ : LinfStar) (n : ℕ) {z : ℂ}
    (hz : z ∈ unitDisc) :
    HasDerivAt (fun x => ∫ w in unitDiscExterior, μ w / (w - x) ^ (n + 4))
      ((n + 4 : ℂ) * ∫ w in unitDiscExterior, μ w / (w - z) ^ (n + 5)) z := by
  let ρ : ℝ := (‖z‖ + 1) / 2
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hzρ : ‖z‖ < ρ := by dsimp [ρ]; linarith
  let A : ℝ := (1 - ρ)⁻¹ ^ n * (12 / (1 - ρ) ^ 4)
  let B : ℝ := (n + 4 : ℝ) * ((1 - ρ)⁻¹ ^ (n + 1) * (12 / (1 - ρ) ^ 4))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h := qcv_hasDerivAt_extIntegral μ (ρ := ρ) (Cc := A + B)
    (A := fun x w => (1 : ℂ) / (w - x) ^ (n + 4))
    (B := fun x w => (n + 4 : ℂ) / (w - x) ^ (n + 5)) hzρ hρ1
    (fun _ _ => by fun_prop) (by fun_prop)
    (fun x hx w hw => (qcv_cauchyPower_bound hρ0 hρ1 hx hw n).trans
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + B) (norm_nonneg _)))
    (fun x hx w hw => ?_) (fun x hx w hw => ?_)
  · convert h using 1
    · ext x
      simp only [mul_one_div]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      ring
  · have hb := qcv_cauchyPower_bound hρ0 hρ1 hx hw (n + 1)
    have hc : ‖(n + 4 : ℂ)‖ = (n + 4 : ℝ) := by
      exact_mod_cast (Complex.norm_natCast (n + 4))
    have he : (n + 4 : ℂ) / (w - x) ^ (n + 5) =
        (n + 4 : ℂ) * ((1 : ℂ) / (w - x) ^ (n + 1 + 4)) := by
      rw [show n + 1 + 4 = n + 5 by omega]
      ring
    rw [he, norm_mul, hc]
    calc (n + 4 : ℝ) * ‖(1 : ℂ) / (w - x) ^ (n + 1 + 4)‖
        ≤ B * ‖ahKer (-1) w‖ := by
          dsimp [B]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (A + B) * ‖ahKer (-1) w‖ := by gcongr; linarith
  · apply qcv_cauchyPower_hasDerivAt
    intro he
    have he' := sub_eq_zero.mp he
    rw [he'] at hw
    linarith

/-- Vanishing of the Bers derivative kills every exterior Cauchy moment. -/
theorem qcv_ker_D0Phi_cauchyMoments {μ : LinfStar}
    (hμ : fderiv ℂ bersPhi 0 μ = 0) :
    ∀ n : ℕ, ∀ z ∈ unitDisc,
      ∫ w in unitDiscExterior, μ w / (w - z) ^ (n + 4) = 0 := by
  intro n
  induction n with
  | zero =>
      intro z hz
      have he := qcv_eq_1_4 μ z hz
      rw [hμ] at he
      have hleft : AInf.toFun (0 : AInf unitDisc) z = 0 := by
        simp [AInf.toFun, unweight, hz]
      rw [hleft] at he
      have hc : -(6 / (Real.pi : ℂ)) ≠ 0 := neg_ne_zero.mpr
        (div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      exact (mul_eq_zero.mp he.symm).resolve_left hc
  | succ n ih =>
      intro z hz
      have he : (fun x => ∫ w in unitDiscExterior, μ w / (w - x) ^ (n + 4))
          =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
        filter_upwards [isOpen_ball.mem_nhds hz] with x hx
        exact ih x hx
      have hd := qcv_cauchyMoment_hasDerivAt μ n hz
      have hzder := hd.deriv
      rw [he.deriv_eq, deriv_const] at hzder
      have hc : (n + 4 : ℂ) ≠ 0 := by exact_mod_cast (show n + 4 ≠ 0 by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        (mul_eq_zero.mp hzder.symm).resolve_left hc

/-- In particular, all Laurent monomials of degrees `-4,-5,…` pair to zero. -/
theorem qcv_ker_D0Phi_laurentMoments {μ : LinfStar}
    (hμ : fderiv ℂ bersPhi 0 μ = 0) (n : ℕ) :
    ∫ w in unitDiscExterior, μ w / w ^ (n + 4) = 0 := by
  simpa only [sub_zero] using qcv_ker_D0Phi_cauchyMoments hμ n 0
    (mem_ball_self (by norm_num))

end QCV
end TakhtajanTeo
