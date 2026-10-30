import Mathlib

/-!
# Geometric reductions for the reflection kernel

This module records a conditional two-chart reduction. Deriving its chart
bounds from an arbitrary `IsQCReflection` remains a separate obligation.
No exterior Poincaré density or boundary regularity is substituted here.
-/

open Set

namespace TakhtajanTeo

/-- Two boundary-pole chart bounds and a bounded image give the quadratic
growth estimate needed by the reflection kernel. The chart bounds are explicit
hypotheses, not consequences asserted here of a weak reflection definition. -/
theorem eq22_growth_of_two_chart_bounds {E : Set ℂ} {h : ℂ → ℂ} {L : ℂ → ℝ}
    {a b : ℂ} {B M : ℝ} (hab : a ≠ b) (hB : 0 ≤ B) (hM : 0 < M)
    (hL : ∀ u ∈ E, 0 ≤ L (h u)) (hh : ∀ u ∈ E, ‖h u‖ ≤ B)
    (ha : ∀ u ∈ E, ‖u - h u‖ * L (h u) * ‖h u - a‖ ≤ M * ‖u - a‖)
    (hb : ∀ u ∈ E, ‖u - h u‖ * L (h u) * ‖h u - b‖ ≤ M * ‖u - b‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ E,
      ‖u - h u‖ ^ 2 * L (h u) ≤ C * (1 + ‖u‖ ^ 2) := by
  let A := ‖a‖ + ‖b‖
  let D := ‖a - b‖
  let T := 2 + A + 2 * B + B * A
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD : 0 < D := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨M * T / D, div_pos (mul_pos hM hT) hD, ?_⟩
  intro u hu
  let r := ‖u‖
  let d := ‖u - h u‖
  let l := L (h u)
  have hr : 0 ≤ r := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hl : 0 ≤ l := hL u hu
  have hd : d ≤ r + B := by
    dsimp [d, r]
    linarith [norm_sub_le u (h u), hh u hu]
  have hdelta : D ≤ ‖h u - a‖ + ‖h u - b‖ := by
    calc
      D ≤ ‖a - h u‖ + ‖h u - b‖ := norm_sub_le_norm_sub_add_norm_sub a (h u) b
      _ = ‖h u - a‖ + ‖h u - b‖ := by rw [norm_sub_rev a (h u)]
  have hrad : ‖u - a‖ + ‖u - b‖ ≤ 2 * r + A := by
    dsimp [r, A]
    linarith [norm_sub_le u a, norm_sub_le u b]
  have hsum : d * l * D ≤ M * (2 * r + A) := by
    calc
      d * l * D ≤ d * l * (‖h u - a‖ + ‖h u - b‖) :=
        mul_le_mul_of_nonneg_left hdelta (mul_nonneg hd0 hl)
      _ = d * l * ‖h u - a‖ + d * l * ‖h u - b‖ := by ring
      _ ≤ M * ‖u - a‖ + M * ‖u - b‖ := add_le_add (ha u hu) (hb u hu)
      _ = M * (‖u - a‖ + ‖u - b‖) := by ring
      _ ≤ M * (2 * r + A) := mul_le_mul_of_nonneg_left hrad hM.le
  have hsumd := mul_le_mul_of_nonneg_right hsum hd0
  have hbound := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hM.le (show 0 ≤ 2 * r + A by positivity))
  have hpoly : (2 * r + A) * (r + B) ≤ T * (1 + r ^ 2) := by
    have hsmall : 0 ≤ 1 + r ^ 2 - r := by nlinarith [sq_nonneg (r - 1)]
    have hcoef : 0 ≤ A + 2 * B := by positivity
    have hBA : 0 ≤ B * A := mul_nonneg hB hA
    dsimp [T]
    nlinarith [mul_nonneg hcoef hsmall, mul_nonneg hBA (sq_nonneg r)]
  have hfinal := mul_le_mul_of_nonneg_left hpoly hM.le
  change d ^ 2 * l ≤ M * T / D * (1 + r ^ 2)
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  nlinarith

end TakhtajanTeo
