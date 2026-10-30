import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Field

/-! Sequence limits for the contact correction. Eventual boundedness of x
is enough; no convergence or subsequential compactness of x is assumed. -/
open Filter
open scoped Topology

namespace TakhtajanTeo

-- L1
theorem ccl_denominator {p q x : ℕ → ℂ} {C : ℝ}
    (hp : Tendsto p atTop (𝓝 1)) (hq : Tendsto q atTop (𝓝 0))
    (hx : ∀ᶠ n in atTop, ‖x n‖ ≤ C) :
    Tendsto (fun n => 1 - x n * q n / (2 * p n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop, 1 - x n * q n / (2 * p n) ≠ 0 := by
  have hxq : Tendsto (fun n => x n * q n) atTop (𝓝 0) :=
    isBoundedUnder_le_mul_tendsto_zero (isBoundedUnder_of_eventually_le hx) hq
  have hdiv := hxq.div (hp.const_mul 2) (by norm_num : (2 : ℂ) * 1 ≠ 0)
  have hJ : Tendsto (fun n => 1 - x n * q n / (2 * p n)) atTop (𝓝 1) := by
    simpa only [Pi.div_apply, zero_div, sub_zero] using tendsto_const_nhds.sub hdiv
  exact ⟨hJ, hJ.eventually_ne one_ne_zero⟩

-- L2
theorem ccl_correction {p q b x : ℕ → ℂ} {C : ℝ}
    (hp : Tendsto p atTop (𝓝 1)) (hq : Tendsto q atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hx : ∀ᶠ n in atTop, ‖x n‖ ≤ C) :
    Tendsto (fun n => b n * (p n * x n / (1 - x n * q n / (2 * p n))))
      atTop (𝓝 0) := by
  have hbx : Tendsto (fun n => b n * x n) atTop (𝓝 0) :=
    hb.zero_mul_isBoundedUnder_le (isBoundedUnder_of_eventually_le hx)
  have ht := hbx.mul (hp.div (ccl_denominator hp hq hx).1 one_ne_zero)
  simp only [zero_mul] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by simp only [Pi.div_apply, div_eq_mul_inv]; ring

-- L3
theorem ccl_contact {p q b x v : ℕ → ℂ} {C : ℝ} {L : ℂ}
    (hp : Tendsto p atTop (𝓝 1)) (hq : Tendsto q atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0)) (hx : ∀ᶠ n in atTop, ‖x n‖ ≤ C)
    (hv : Tendsto v atTop (𝓝 L)) :
    Tendsto (fun n => v n + b n * (p n * x n / (1 - x n * q n / (2 * p n))))
      atTop (𝓝 L) := by
  simpa only [add_zero] using hv.add (ccl_correction hp hq hb hx)

end TakhtajanTeo
