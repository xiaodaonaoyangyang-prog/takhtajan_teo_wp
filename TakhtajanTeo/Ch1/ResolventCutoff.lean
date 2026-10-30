import TakhtajanTeo.Ch1.ResolventRationalKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Smooth scalar regularization of the reciprocal-square denominator in the tail kernel. -/

open Real Filter Set Topology Metric

noncomputable section

namespace TakhtajanTeo

set_option autoImplicit false

/-- A reciprocal square with its singularity removed by a bump equal to one near zero. -/
def resolventCutoffInvSq (b : ContDiffBump (0 : ℝ)) (x : ℝ) : ℝ := (1 - b x) / x ^ 2

theorem resolventCutoffInvSq_contDiff (b : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (resolventCutoffInvSq b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one_of_mem_ball (mem_ball_self b.rIn_pos)] with y hy
    simp only [resolventCutoffInvSq, hy, Pi.one_apply, sub_self, zero_div]
  · have hb : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
    exact (contDiffAt_const.sub hb.contDiffAt).div (contDiffAt_id.pow 2) (pow_ne_zero 2 hx)

theorem resolventCutoffInvSq_eq (b : ContDiffBump (0 : ℝ)) {x : ℝ}
    (hx : b.rOut ≤ |x|) : resolventCutoffInvSq b x = 1 / x ^ 2 := by
  have hb : b x = 0 := b.zero_of_le_dist (by simpa [Real.norm_eq_abs] using hx)
  simp only [resolventCutoffInvSq, hb, sub_zero]

theorem resolventCutoffInvSq_nonneg (b : ContDiffBump (0 : ℝ)) (x : ℝ) :
    0 ≤ resolventCutoffInvSq b x := by
  exact div_nonneg (sub_nonneg.mpr b.le_one) (sq_nonneg x)

/-- For every positive threshold, a globally smooth nonnegative reciprocal square
agrees with the genuine reciprocal square beyond that threshold. -/
theorem exists_resolvent_cutoff_inv_sq {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ (∀ x, 0 ≤ F x) ∧
      ∀ x, δ ≤ |x| → F x = 1 / x ^ 2 := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := δ / 2, rOut := δ, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  exact ⟨resolventCutoffInvSq b, resolventCutoffInvSq_contDiff b,
    resolventCutoffInvSq_nonneg b, fun x hx => resolventCutoffInvSq_eq b hx⟩

end TakhtajanTeo
