import Mathlib.Analysis.Complex.CauchyIntegral

/-! The exact inner-circle constant for the reflected triple primitive. -/
open Complex Set Filter Topology Metric
open scoped Real
namespace TakhtajanTeo

 theorem eq22_primitive_circle_integral {Ω : Set ℂ} {q Q1 Q2 Q3 : ℂ → ℂ}
    {z : ℂ} {r : ℝ} (hΩ : IsOpen Ω) (hr : 0 < r) (hball : closedBall z r ⊆ Ω)
    (hQ3 : DifferentiableOn ℂ Q3 Ω)
    (h1 : EqOn (deriv Q1) q Ω) (h2 : EqOn (deriv Q2) Q1 Ω)
    (h3 : EqOn (deriv Q3) Q2 Ω) :
    (∮ u in C(z,r), 2 * Q3 u / (u-z)^4) = (2 * π * I / 3) * q z := by
  have hz : z ∈ Ω := hball (mem_closedBall_self hr.le)
  have ht := (((h3.deriv hΩ).deriv hΩ) hz).trans (((h2.deriv hΩ) hz).trans (h1 hz))
  have hthird : iteratedDeriv 3 Q3 z = q z := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using ht
  have hc := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hr 3 (hQ3.mono hball)
  have he : (fun u : ℂ => 2 * Q3 u / (u-z)^4) =
      (fun u : ℂ => 2 * ((1 / (u-z)^4) * Q3 u)) := by
    funext u
    ring
  rw [he, circleIntegral.integral_const_mul]
  simp only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.reduceAdd, smul_eq_mul] at hc
  rw [hc, hthird]
  ring

end TakhtajanTeo
