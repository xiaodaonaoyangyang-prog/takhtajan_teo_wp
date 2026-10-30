import TakhtajanTeo.Ch2.GrunskyOperator
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Strong convergence of diagonal Bergman dilations -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppB

def b7Apply (B : ℕ → ℕ → ℂ) (x : ℕ → ℂ) (m : ℕ) : ℂ := ∑' n, B m n * x n

def b7Diag (r : ℝ) (x : ℕ → ℂ) (n : ℕ) : ℂ := (r : ℂ) ^ (n + 1) * x n

def b7Matrix (r : ℝ) (B : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ :=
  (r : ℂ) ^ (m + 1) * B m n * (r : ℂ) ^ (n + 1)

def B7Contractive (B : ℕ → ℕ → ℂ) : Prop :=
  ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
    Summable (fun m => ‖b7Apply B x m‖ ^ 2) ∧
      (∑' m, ‖b7Apply B x m‖ ^ 2) ≤ ∑' n, ‖x n‖ ^ 2

theorem b7_diag_norm_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x : ℕ → ℂ) (n : ℕ) :
    ‖b7Diag r x n‖ ≤ ‖x n‖ := by
  simp only [b7Diag, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr0 hr1)

theorem b7_diag_sub_norm_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (x : ℕ → ℂ) (n : ℕ) :
    ‖b7Diag r x n - x n‖ ≤ ‖x n‖ := by
  have he : b7Diag r x n - x n = (((r ^ (n + 1) - 1 : ℝ) : ℂ)) * x n := by
    simp only [b7Diag, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [abs_le]
  constructor <;> linarith [pow_nonneg hr0 (n + 1),
    (pow_le_one₀ hr0 hr1 : r ^ (n + 1) ≤ 1)]

theorem b7_diag_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Summable (fun n => ‖b7Diag r x n‖ ^ 2) :=
  hx.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (b7_diag_norm_le hr0 hr1 x n) 2)

theorem b7_diag_mass_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    (∑' n, ‖b7Diag r x n‖ ^ 2) ≤ ∑' n, ‖x n‖ ^ 2 :=
  Summable.tsum_le_tsum (fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (b7_diag_norm_le hr0 hr1 x n) 2)
    (b7_diag_summable hr0 hr1 hx) hx

theorem b7_diag_sub_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Summable (fun n => ‖b7Diag r x n - x n‖ ^ 2) :=
  hx.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (b7_diag_sub_norm_le hr0 hr1 x n) 2)

theorem b7_diag_strong {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hr : Tendsto r atTop (𝓝 1)) {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Tendsto (fun k => ∑' n, ‖b7Diag (r k) x n - x n‖ ^ 2) atTop (𝓝 0) := by
  have hp : ∀ n, Tendsto (fun k => ‖b7Diag (r k) x n - x n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    intro n
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    have hh := (((hc.pow (n + 1)).mul_const (x n)).sub_const (x n)).norm.pow 2
    simpa [b7Diag] using hh
  have hb : ∀ᶠ k in atTop, ∀ n, ‖‖b7Diag (r k) x n - x n‖ ^ 2‖ ≤ ‖x n‖ ^ 2 := by
    exact Eventually.of_forall fun k n => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (b7_diag_sub_norm_le (hr0 k) (hr1 k) x n) 2
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hx hp hb

theorem b7_apply_matrix (B : ℕ → ℕ → ℂ) (r : ℝ) (x : ℕ → ℂ) :
    b7Apply (b7Matrix r B) x = b7Diag r (b7Apply B (b7Diag r x)) := by
  ext m
  dsimp [b7Apply, b7Matrix, b7Diag]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem b7_matrix_contractive {B : ℕ → ℕ → ℂ} (hB : B7Contractive B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : B7Contractive (b7Matrix r B) := by
  intro x hx
  have hd := b7_diag_summable hr0 hr1 hx
  have hy := hB (b7Diag r x) hd
  rw [b7_apply_matrix]
  exact ⟨b7_diag_summable hr0 hr1 hy.1,
    (b7_diag_mass_le hr0 hr1 hy.1).trans (hy.2.trans (b7_diag_mass_le hr0 hr1 hx))⟩

theorem b7_apply_sub {B : ℕ → ℕ → ℂ}
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2))
    {x y : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2))
    (hy : Summable (fun n => ‖y n‖ ^ 2)) :
    b7Apply B (fun n => x n - y n) = fun m => b7Apply B x m - b7Apply B y m := by
  ext m
  dsimp [b7Apply]
  simp only [mul_sub]
  exact ((bergman_pair_summable (hrow m) hx).of_norm.tsum_sub
    (bergman_pair_summable (hrow m) hy).of_norm)

theorem b7_sub_sq_summable {x y : ℕ → ℂ}
    (hx : Summable (fun n => ‖x n‖ ^ 2)) (hy : Summable (fun n => ‖y n‖ ^ 2)) :
    Summable (fun n => ‖x n - y n‖ ^ 2) := by
  apply ((hx.add hy).mul_left 2).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  have ht := norm_sub_le (x n) (y n)
  nlinarith [norm_nonneg (x n - y n), norm_nonneg (x n), norm_nonneg (y n),
    sq_nonneg (‖x n‖ - ‖y n‖)]

theorem b7_matrix_error_bound {B : ℕ → ℕ → ℂ} (hB : B7Contractive B)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    (∑' m, ‖b7Apply (b7Matrix r B) x m - b7Apply B x m‖ ^ 2) ≤
      2 * (∑' n, ‖b7Diag r x n - x n‖ ^ 2) +
        2 * (∑' m, ‖b7Diag r (b7Apply B x) m - b7Apply B x m‖ ^ 2) := by
  let e : ℕ → ℂ := fun n => b7Diag r x n - x n
  have he : Summable (fun n => ‖e n‖ ^ 2) := b7_diag_sub_summable hr0 hr1 hx
  have hy := hB x hx
  have hBe := hB e he
  have hrd := (b7_matrix_contractive hB hr0 hr1) x hx
  have hpoint : ∀ m, ‖b7Apply (b7Matrix r B) x m - b7Apply B x m‖ ^ 2 ≤
      2 * ‖b7Apply B e m‖ ^ 2 +
        2 * ‖b7Diag r (b7Apply B x) m - b7Apply B x m‖ ^ 2 := by
    intro m
    have hs := congrFun (b7_apply_sub hrow (b7_diag_summable hr0 hr1 hx) hx) m
    have hid : b7Apply (b7Matrix r B) x m - b7Apply B x m =
        b7Diag r (b7Apply B e) m + (b7Diag r (b7Apply B x) m - b7Apply B x m) := by
      rw [b7_apply_matrix]
      dsimp only [b7Diag]
      change b7Apply B e m = _ at hs
      rw [hs]
      ring
    rw [hid]
    have hb := b7_diag_norm_le hr0 hr1 (b7Apply B e) m
    have ht := norm_add_le (b7Diag r (b7Apply B e) m)
      (b7Diag r (b7Apply B x) m - b7Apply B x m)
    nlinarith [norm_nonneg (b7Apply B e m),
      norm_nonneg (b7Diag r (b7Apply B x) m - b7Apply B x m),
      norm_nonneg (b7Diag r (b7Apply B e) m + (b7Diag r (b7Apply B x) m - b7Apply B x m)),
      sq_nonneg (‖b7Apply B e m‖ - ‖b7Diag r (b7Apply B x) m - b7Apply B x m‖)]
  have hs := Summable.tsum_le_tsum hpoint (b7_sub_sq_summable hrd.1 hy.1)
    ((hBe.1.mul_left 2).add ((b7_diag_sub_summable hr0 hr1 hy.1).mul_left 2))
  rw [Summable.tsum_add (hBe.1.mul_left 2)
    ((b7_diag_sub_summable hr0 hr1 hy.1).mul_left 2), tsum_mul_left, tsum_mul_left] at hs
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBe.2 (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)

theorem b7_matrix_strong {B : ℕ → ℕ → ℂ} (hB : B7Contractive B)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖ ^ 2))
    {r : ℕ → ℝ} (hr0 : ∀ k, 0 ≤ r k) (hr1 : ∀ k, r k ≤ 1)
    (hr : Tendsto r atTop (𝓝 1)) {x : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖ ^ 2)) :
    Tendsto (fun k => ∑' m, ‖b7Apply (b7Matrix (r k) B) x m - b7Apply B x m‖ ^ 2)
      atTop (𝓝 0) := by
  have h1 := b7_diag_strong hr0 hr1 hr hx
  have h2 := b7_diag_strong hr0 hr1 hr (hB x hx).1
  have ht : Tendsto (fun k => 2 * (∑' n, ‖b7Diag (r k) x n - x n‖ ^ 2) +
      2 * (∑' m, ‖b7Diag (r k) (b7Apply B x) m - b7Apply B x m‖ ^ 2)) atTop (𝓝 0) := by
    simpa using (h1.const_mul 2).add (h2.const_mul 2)
  exact squeeze_zero (fun k => tsum_nonneg fun m => sq_nonneg _)
    (fun k => b7_matrix_error_bound hB hrow (hr0 k) (hr1 k) hx) ht

end AppB
end TakhtajanTeo
