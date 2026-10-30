import TakhtajanTeo.Ch1.BeltramiGroup
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TakhtajanTeo.Ch1.QCVariationTransport
import TakhtajanTeo.Ch1.S4_Metrics
import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch2.S1_BP16Forward

/-!
# Wall (A): real-analytic Beltrami differentials (`ra_`, 下属2, Program G) — INTERFACE

Host: new module `TakhtajanTeo/Ch1/BeltramiRealAnalytic.lean`.

Targets (statements byte-identical to `Ch1/S1_1_TeichmullerTheory.lean`):
`realAnalyticBeltrami_subgroup` (4295), `exists_realAnalytic_rep` (3263), `remark_1_2` (4332).

Route.
* Regularity (the wall). R1 `ra_local_solution`: local real-analytic solution of `∂̄φ = a ∂φ`, `∂φ(z₀) = 1`, for
  real-analytic `a` with `|a(z₀)| < 1` (Cauchy–Kovalevskaya for `φ_y = i(1-a)/(1+a) φ_x` on double coefficient arrays,
  majorant convergence; real-analyticity from the double series). R2 `ra_qc_analytic`: a q.c. map with real-analytic
  dilatation is real-analytic with `∂f ≠ 0` (factor `f = h ∘ φ` with `φ` from R1 and the analytic inverse function
  theorem `OpenPartialHomeomorph.analyticAt_symm`; `h` is 1-q.c., hence conformal). R3 `ra_W_analytic`: R2 for the
  normalized plane solution `W` of `extA μ` on `𝔻*` and, in the chart `1/W(1/z)`, at `∞` (dilatation `μ(1/z) z²/z̄²`,
  the D2 condition).
* R4 `ra_formula_rep`: the composition formula `bc_beltramiMul_inv_formula` has a real-analytic representative
  (inverse of `wA μ = M ∘ W`; the point `w_μ(∞)` uses the `∞`-condition of `μ`, the pole of `w_μ` gives the
  `∞`-condition of the composite; a.e. transport by `thm9_6_cor1_null`).
* R5 `ra_Lambda_mem`: Ahlfors–Weill differentials are real-analytic. R6 `ra_mul_mem`: closure under `beltramiMul`.
  R7 `ra_path_cover`: a chain `0 = q₀, …, q_N = p` along `t ↦ [tμ]` with each step inside a Bers chart of any
  representative of the previous point (`bpa_bersPhi_le`, `ahlfors_weill`, group laws).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

section RAOne

open Finset

/-- Regrouping an absolutely summable double series along antidiagonals. -/
theorem ra_tsum_antidiag {t : ℕ × ℕ → ℂ} (h : Summable fun x => ‖t x‖) :
    ∑' n, ∑ x ∈ antidiagonal n, t x = ∑' k, ∑' j, t (j, k) := by
  have hs : Summable t := h.of_norm
  have hσ : Summable fun x => t (HasAntidiagonal.sigmaAntidiagonalEquivProd x) :=
    (HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr hs
  have h1 : ∑' x : ℕ × ℕ, t x = ∑' n, ∑ x ∈ antidiagonal n, t x := by
    rw [← (HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq t,
      hσ.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
    refine tsum_congr fun n => ?_
    rw [tsum_fintype]
    exact Finset.sum_coe_sort (antidiagonal n) t
  have hu : Summable (Function.uncurry fun j k => t (j, k)) := hs
  rw [← h1, hs.tsum_prod' (fun b => hs.comp_injective (fun x y hxy => (Prod.ext_iff.mp hxy).2))]
  exact Eq.symm (hu.tsum_comm' (fun b => hs.comp_injective (fun x y hxy => (Prod.ext_iff.mp hxy).2))
    (fun c => hs.comp_injective (fun x y hxy => (Prod.ext_iff.mp hxy).1)))

/-- Term bound for a geometrically bounded power series. -/
theorem ra_ps_term {b : ℕ → ℂ} {B τ ρ : ℝ} (hb : ∀ j, ‖b j‖ ≤ B * τ ^ j) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : ‖s‖ ≤ ρ) (j : ℕ) : ‖b j * s ^ j‖ ≤ B * (τ * ρ) ^ j := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((hb 0).trans (by simp))
  rw [norm_mul, norm_pow, mul_pow, ← mul_assoc]
  exact mul_le_mul (hb j) (pow_le_pow_left₀ (norm_nonneg _) hs j) (by positivity) (by positivity)

theorem ra_ps_summable {b : ℕ → ℂ} {B τ ρ : ℝ} (hb : ∀ j, ‖b j‖ ≤ B * τ ^ j) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hτρ : τ * ρ < 1) {s : ℂ} (hs : ‖s‖ ≤ ρ) : Summable fun j => ‖b j * s ^ j‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (ra_ps_term hb hτ hs)
    ((summable_geometric_of_lt_one (mul_nonneg hτ hρ) hτρ).mul_left B)

theorem ra_ps_norm_le {b : ℕ → ℂ} {B τ ρ : ℝ} (hb : ∀ j, ‖b j‖ ≤ B * τ ^ j) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hτρ : τ * ρ < 1) {s : ℂ} (hs : ‖s‖ ≤ ρ) : ‖∑' j, b j * s ^ j‖ ≤ B * ∑' j : ℕ, (τ * ρ) ^ j := by
  have hg := (summable_geometric_of_lt_one (mul_nonneg hτ hρ) hτρ).mul_left B
  refine (norm_tsum_le_tsum_norm (ra_ps_summable hb hτ hρ hτρ hs)).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (ra_ps_term hb hτ hs) (ra_ps_summable hb hτ hρ hτρ hs) hg

/-- Termwise differentiation of a geometrically bounded power series in a real variable. -/
theorem ra_ps_hasDerivAt {b : ℕ → ℂ} {B τ ρ : ℝ} (hb : ∀ j, ‖b j‖ ≤ B * τ ^ j) (hτ : 0 ≤ τ) (hρ : 0 < ρ)
    (hτρ : τ * ρ < 1) {t : ℝ} (ht : |t| < ρ) :
    HasDerivAt (fun s : ℝ => ∑' j, b j * (s : ℂ) ^ j) (∑' j : ℕ, ((j : ℂ) + 1) * b (j + 1) * (t : ℂ) ^ j) t := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((hb 0).trans (by simp))
  have hg : ∀ (j : ℕ) (s : ℝ), s ∈ Ioo (-ρ) ρ →
      HasDerivAt (fun s : ℝ => b j * (s : ℂ) ^ j) (b j * ((j : ℂ) * (s : ℂ) ^ (j - 1))) s :=
    fun j s _ => ((hasDerivAt_pow j (s : ℂ)).comp_ofReal).const_mul (b j)
  have hq : ‖τ * ρ‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; exact hτρ
  have hu : Summable fun j : ℕ => B / ρ * ((j : ℝ) ^ 1 * (τ * ρ) ^ j) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left _
  have hbound : ∀ (j : ℕ) (s : ℝ), s ∈ Ioo (-ρ) ρ →
      ‖b j * ((j : ℂ) * (s : ℂ) ^ (j - 1))‖ ≤ B / ρ * ((j : ℝ) ^ 1 * (τ * ρ) ^ j) := by
    intro j s hs
    have hs' : ‖(s : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_lt.mpr hs).le
    rcases j with _ | m
    · simp
    · rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
      calc ‖b (m + 1)‖ * (((m + 1 : ℕ) : ℝ) * ‖(s : ℂ)‖ ^ m)
          ≤ B * τ ^ (m + 1) * (((m + 1 : ℕ) : ℝ) * ρ ^ m) := by
            gcongr
            exact hb _
        _ = B / ρ * (((m + 1 : ℕ) : ℝ) ^ 1 * (τ * ρ) ^ (m + 1)) := by
            field_simp
            ring
  have h0 : Summable fun j => b j * ((0 : ℝ) : ℂ) ^ j :=
    (ra_ps_summable hb hτ hρ.le hτρ (by simp [hρ.le])).of_norm
  have ht' : t ∈ Ioo (-ρ) ρ := abs_lt.mp ht
  have hD := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hbound
    (by simp [hρ] : (0 : ℝ) ∈ Ioo (-ρ) ρ) h0 ht'
  have hsD : Summable fun j => b j * ((j : ℂ) * (t : ℂ) ^ (j - 1)) :=
    Summable.of_norm_bounded hu (fun j => hbound j t ht')
  convert hD using 1
  rw [hsD.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  exact tsum_congr fun j => by ring

/-- Norm bound of the termwise derivative series. -/
theorem ra_ps_deriv_norm_le {b : ℕ → ℂ} {B τ ρ : ℝ} (hb : ∀ j, ‖b j‖ ≤ B * τ ^ j) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hτρ : τ * ρ < 1) {s : ℂ} (hs : ‖s‖ ≤ ρ) :
    ‖∑' j : ℕ, ((j : ℂ) + 1) * b (j + 1) * s ^ j‖ ≤ B * τ * ∑' j : ℕ, ((j : ℝ) + 1) * (τ * ρ) ^ j := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((hb 0).trans (by simp))
  have hq : ‖τ * ρ‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; exact hτρ
  have hsum : Summable fun j : ℕ => ((j : ℝ) + 1) * (τ * ρ) ^ j := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h2 := summable_geometric_of_lt_one (mul_nonneg hτ hρ) hτρ
    simpa [add_mul] using h1.add h2
  have hterm : ∀ j : ℕ, ‖((j : ℂ) + 1) * b (j + 1) * s ^ j‖ ≤ B * τ * (((j : ℝ) + 1) * (τ * ρ) ^ j) := by
    intro j
    have h := ra_ps_term hb hτ hs (j + 1)
    have hj : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (j + 1)
    have hsj : ‖s‖ ^ j * ‖s‖ ≤ ρ ^ j * ρ := by gcongr
    rw [norm_mul, norm_mul, hj, norm_pow]
    calc ((j : ℝ) + 1) * ‖b (j + 1)‖ * ‖s‖ ^ j ≤ ((j : ℝ) + 1) * (B * τ ^ (j + 1)) * ρ ^ j := by
          gcongr
          exact hb _
        _ = B * τ * (((j : ℝ) + 1) * (τ * ρ) ^ j) := by ring
  have hsn : Summable fun j : ℕ => ‖((j : ℂ) + 1) * b (j + 1) * s ^ j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsum.mul_left _)
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hterm hsn (hsum.mul_left _)

/-- One-variable Cauchy product of power series. -/
theorem ra_cauchy1 {f g : ℕ → ℂ} {x : ℂ} (hf : Summable fun j => ‖f j * x ^ j‖)
    (hg : Summable fun j => ‖g j * x ^ j‖) :
    (∑' j, f j * x ^ j) * (∑' j, g j * x ^ j) = ∑' j, (∑ jj ∈ antidiagonal j, f jj.1 * g jj.2) * x ^ j ∧
      Summable fun j => (∑ jj ∈ antidiagonal j, f jj.1 * g jj.2) * x ^ j := by
  have hc : ∀ j, ∑ jj ∈ antidiagonal j, f jj.1 * x ^ jj.1 * (g jj.2 * x ^ jj.2) =
      (∑ jj ∈ antidiagonal j, f jj.1 * g jj.2) * x ^ j := by
    intro j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun jj hjj => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hjj
    rw [← hjj, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    exact tsum_congr hc
  · have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm
    exact h.congr hc

/-- Row bound for a geometrically bounded double array. -/
theorem ra_row_norm {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hτρ : τ * ρ < 1) {s : ℂ} (hs : ‖s‖ ≤ ρ) (k : ℕ) :
    ‖∑' j, a j k * s ^ j‖ ≤ B * τ ^ k * ∑' j : ℕ, (τ * ρ) ^ j :=
  ra_ps_norm_le (b := fun j => a j k) (fun j => by rw [mul_assoc, ← pow_add, add_comm]; exact ha j k) hτ hρ
    hτρ hs

theorem ra_row_bound {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hτρ : τ * ρ < 1) {s : ℂ} (hs : ‖s‖ ≤ ρ) :
    ∀ k, ‖∑' j, a j k * s ^ j‖ ≤ (B * ∑' j : ℕ, (τ * ρ) ^ j) * τ ^ k := fun k => by
  rw [mul_right_comm]; exact ra_row_norm ha hτ hρ hτρ hs k

theorem ra_row_summable {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hτρ : τ * ρ < 1) {s y : ℂ} (hs : ‖s‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    Summable fun k => ‖(∑' j, a j k * s ^ j) * y ^ k‖ :=
  ra_ps_summable (ra_row_bound ha hτ hρ hτρ hs) hτ hρ hτρ hy

/-- Product of two double power series. -/
theorem ra_dprod {u v : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (hu : ∀ j k, ‖u j k‖ ≤ B * τ ^ (j + k))
    (hv : ∀ j k, ‖v j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hτρ : τ * ρ < 1) {x y : ℂ}
    (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    (∑' i, (∑' j, u j i * x ^ j) * y ^ i) * (∑' l, (∑' j, v j l * x ^ j) * y ^ l) =
      ∑' k, (∑' j, (∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j, u jj.1 il.1 * v jj.2 il.2) * x ^ j) *
        y ^ k := by
  rw [(ra_cauchy1 (ra_row_summable hu hτ hρ hτρ hx hy) (ra_row_summable hv hτ hρ hτρ hx hy)).1]
  refine tsum_congr fun k => ?_
  congr 1
  have hrow : ∀ il ∈ antidiagonal k, (∑' j, u j il.1 * x ^ j) * (∑' j, v j il.2 * x ^ j) =
      ∑' j, (∑ jj ∈ antidiagonal j, u jj.1 il.1 * v jj.2 il.2) * x ^ j := fun il _ =>
    (ra_cauchy1 (ra_ps_summable (b := fun j => u j il.1)
        (fun j => by rw [mul_assoc, ← pow_add, add_comm]; exact hu j il.1) hτ hρ hτρ hx)
      (ra_ps_summable (b := fun j => v j il.2)
        (fun j => by rw [mul_assoc, ← pow_add, add_comm]; exact hv j il.2) hτ hρ hτρ hx)).1
  rw [Finset.sum_congr rfl hrow, ← Summable.tsum_finsetSum]
  · exact tsum_congr fun j => (Finset.sum_mul _ _ _).symm
  · intro il _
    exact (ra_cauchy1 (ra_ps_summable (b := fun j => u j il.1)
        (fun j => by rw [mul_assoc, ← pow_add, add_comm]; exact hu j il.1) hτ hρ hτρ hx)
      (ra_ps_summable (b := fun j => v j il.2)
        (fun j => by rw [mul_assoc, ← pow_add, add_comm]; exact hv j il.2) hτ hρ hτρ hx)).2

/-- Partial derivative in `x` of a double power series. -/
theorem ra_G_hasDerivAt_x {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 < ρ) (hτρ : τ * ρ < 1) {x y : ℝ} (hx : |x| < ρ) (hy : |y| ≤ ρ) :
    HasDerivAt (fun s : ℝ => ∑' k, (∑' j, a j k * (s : ℂ) ^ j) * (y : ℂ) ^ k)
      (∑' k, (∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (x : ℂ) ^ j) * (y : ℂ) ^ k) x := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((ha 0 0).trans (by simp))
  have hrow : ∀ k j, ‖a j k‖ ≤ B * τ ^ k * τ ^ j := fun k j => by
    rw [mul_assoc, ← pow_add, add_comm]; exact ha j k
  have hy' : ‖(y : ℂ)‖ ≤ ρ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hy
  set T1 := ∑' j : ℕ, ((j : ℝ) + 1) * (τ * ρ) ^ j
  have hT1 : 0 ≤ T1 := tsum_nonneg fun j => by positivity
  have hg : ∀ (k : ℕ) (s : ℝ), s ∈ Ioo (-ρ) ρ →
      HasDerivAt (fun s : ℝ => (∑' j, a j k * (s : ℂ) ^ j) * (y : ℂ) ^ k)
        ((∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (s : ℂ) ^ j) * (y : ℂ) ^ k) s :=
    fun k s hs => (ra_ps_hasDerivAt (b := fun j => a j k) (hrow k) hτ hρ hτρ (abs_lt.mpr hs)).mul_const _
  have hbound : ∀ (k : ℕ) (s : ℝ), s ∈ Ioo (-ρ) ρ →
      ‖(∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (s : ℂ) ^ j) * (y : ℂ) ^ k‖ ≤ B * τ * T1 * (τ * ρ) ^ k := by
    intro k s hs
    have hs' : ‖(s : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_lt.mpr hs).le
    have h1 := ra_ps_deriv_norm_le (b := fun j => a j k) (hrow k) hτ hρ.le hτρ hs'
    rw [norm_mul, norm_pow]
    calc ‖∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (s : ℂ) ^ j‖ * ‖(y : ℂ)‖ ^ k
        ≤ B * τ ^ k * τ * T1 * ρ ^ k := by
          gcongr
      _ = B * τ * T1 * (τ * ρ) ^ k := by ring
  have hu : Summable fun k : ℕ => B * τ * T1 * (τ * ρ) ^ k :=
    (summable_geometric_of_lt_one (mul_nonneg hτ hρ.le) hτρ).mul_left _
  have h0 : Summable fun k => (∑' j, a j k * ((0 : ℝ) : ℂ) ^ j) * (y : ℂ) ^ k :=
    (ra_row_summable ha hτ hρ.le hτρ (by simp [hρ.le]) hy').of_norm
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hbound
    (by simp [hρ] : (0 : ℝ) ∈ Ioo (-ρ) ρ) h0 (abs_lt.mp hx)

/-- Partial derivative in `y` of a double power series. -/
theorem ra_G_hasDerivAt_y {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 < ρ) (hτρ : τ * ρ < 1) {x y : ℝ} (hx : |x| ≤ ρ) (hy : |y| < ρ) :
    HasDerivAt (fun s : ℝ => ∑' k, (∑' j, a j k * (x : ℂ) ^ j) * (s : ℂ) ^ k)
      (∑' k : ℕ, ((k : ℂ) + 1) * (∑' j, a j (k + 1) * (x : ℂ) ^ j) * (y : ℂ) ^ k) y := by
  have hx' : ‖(x : ℂ)‖ ≤ ρ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx
  exact ra_ps_hasDerivAt (b := fun k => ∑' j, a j k * (x : ℂ) ^ j) (ra_row_bound ha hτ hρ.le hτρ hx') hτ hρ
    hτρ hy

/-- `(m + 1) r^m (r' - r) ≤ r'^(m+1)` for `0 ≤ r ≤ r'`. -/
theorem ra_pow_le {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') (m : ℕ) :
    ((m : ℝ) + 1) * r ^ m * (r' - r) ≤ r' ^ (m + 1) := by
  have h := (Commute.all r' r).geom_sum₂_mul (m + 1)
  have hle : ((m : ℝ) + 1) * r ^ m ≤ ∑ i ∈ range (m + 1), r' ^ i * r ^ (m + 1 - 1 - i) := by
    have hterm : ∀ i ∈ range (m + 1), r ^ m ≤ r' ^ i * r ^ (m + 1 - 1 - i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      calc r ^ m = r ^ i * r ^ (m + 1 - 1 - i) := by rw [← pow_add]; congr 1; omega
        _ ≤ r' ^ i * r ^ (m + 1 - 1 - i) := by gcongr
    calc ((m : ℝ) + 1) * r ^ m = ∑ i ∈ range (m + 1), r ^ m := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have h2 := mul_le_mul_of_nonneg_right hle (sub_nonneg.mpr hrr)
  rw [h] at h2
  have h3 : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  linarith

/-- Finite Cauchy product bound for nonnegative sequences. -/
theorem ra_conv_le {u v : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (J : ℕ) :
    ∑ j ∈ range J, ∑ x ∈ antidiagonal j, u x.1 * v x.2 ≤ (∑ j ∈ range J, u j) * ∑ j ∈ range J, v j := by
  have h1 : ∑ j ∈ range J, ∑ x ∈ antidiagonal j, u x.1 * v x.2 =
      ∑ j ∈ range J, ∑ i ∈ range (j + 1), u i * v (j - i) :=
    Finset.sum_congr rfl fun j _ => Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i m => u i * v m) j
  have h2 : ∑ j ∈ range J, ∑ i ∈ range (j + 1), u i * v (j - i) =
      ∑ i ∈ range J, ∑ j ∈ Ico i J, u i * v (j - i) := by
    apply Finset.sum_comm'
    intro j i
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h1, h2, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hu i)
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le J i))
    (fun j _ _ => hv j)

/-- `(l + 2)^l ≤ 3 (l + 1)^l`. -/
theorem ra_e3 (l : ℕ) : ((l : ℝ) + 2) ^ l ≤ 3 * ((l : ℝ) + 1) ^ l := by
  have hl : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have h1 : 1 + 1 / ((l : ℝ) + 1) ≤ Real.exp (1 / ((l : ℝ) + 1)) := by
    have := Real.add_one_le_exp (1 / ((l : ℝ) + 1)); linarith
  have h2 : (1 + 1 / ((l : ℝ) + 1)) ^ l ≤ Real.exp 1 := by
    calc (1 + 1 / ((l : ℝ) + 1)) ^ l ≤ Real.exp (1 / ((l : ℝ) + 1)) ^ l := by
          gcongr
      _ = Real.exp ((l : ℝ) * (1 / ((l : ℝ) + 1))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [mul_one_div, div_le_one hl]
          linarith
  have h3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have h4 : ((l : ℝ) + 2) ^ l = ((l : ℝ) + 1) ^ l * (1 + 1 / ((l : ℝ) + 1)) ^ l := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [h4, mul_comm 3]
  exact mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)

/-- Derivative loss on nested radii (one row of the Cauchy–Kovalevskaya estimate). -/
theorem ra_deriv_sum {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) {R M : ℝ} (hM : 0 ≤ M) {l : ℕ}
    (hS : ∀ J r', 0 ≤ r' → r' < R → ∑ j ∈ range J, b j * r' ^ j ≤ M / (R - r') ^ l)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r < R) (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 1) * b (j + 1) * r ^ j ≤ 3 * ((l : ℝ) + 2) * M / (R - r) ^ (l + 1) := by
  have hl2 : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  have hl1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hRr : 0 < R - r := sub_pos.mpr hrR
  set d := (R - r) / ((l : ℝ) + 2) with hd_def
  have hd : 0 < d := div_pos hRr hl2
  set r' := r + d with hr'_def
  have hRr' : R - r' = (R - r) * ((l : ℝ) + 1) / ((l : ℝ) + 2) := by
    rw [hr'_def, hd_def]; field_simp; ring
  have hr'R : r' < R := by
    have : 0 < R - r' := by rw [hRr']; positivity
    linarith
  have hr' : 0 ≤ r' := by linarith
  -- termwise
  have hterm : ∀ j : ℕ, ((j : ℝ) + 1) * b (j + 1) * r ^ j ≤ b (j + 1) * r' ^ (j + 1) / d := by
    intro j
    rw [le_div_iff₀ hd]
    have h := ra_pow_le hr (by linarith : r ≤ r') j
    have h' : r' - r = d := by rw [hr'_def]; ring
    rw [h'] at h
    calc ((j : ℝ) + 1) * b (j + 1) * r ^ j * d = b (j + 1) * (((j : ℝ) + 1) * r ^ j * d) := by ring
      _ ≤ b (j + 1) * r' ^ (j + 1) := mul_le_mul_of_nonneg_left h (hb _)
  have hshift : ∑ j ∈ range J, b (j + 1) * r' ^ (j + 1) ≤ ∑ j ∈ range (J + 1), b j * r' ^ j := by
    rw [Finset.sum_range_succ']
    have : 0 ≤ b 0 * r' ^ 0 := by simp [hb 0]
    linarith
  have hsum : ∑ j ∈ range J, ((j : ℝ) + 1) * b (j + 1) * r ^ j ≤ M / (R - r') ^ l / d := by
    calc ∑ j ∈ range J, ((j : ℝ) + 1) * b (j + 1) * r ^ j ≤ ∑ j ∈ range J, b (j + 1) * r' ^ (j + 1) / d :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j ∈ range J, b (j + 1) * r' ^ (j + 1)) / d := by rw [Finset.sum_div]
      _ ≤ (∑ j ∈ range (J + 1), b j * r' ^ j) / d := by gcongr
      _ ≤ M / (R - r') ^ l / d := by gcongr; exact hS (J + 1) r' hr' hr'R
  have he := ra_e3 l
  calc ∑ j ∈ range J, ((j : ℝ) + 1) * b (j + 1) * r ^ j ≤ M / (R - r') ^ l / d := hsum
    _ = M * ((l : ℝ) + 2) ^ (l + 1) / (((R - r) ^ (l + 1)) * ((l : ℝ) + 1) ^ l) := by
        rw [hRr', hd_def, div_pow, mul_pow]
        field_simp
        ring
    _ ≤ 3 * ((l : ℝ) + 2) * M / (R - r) ^ (l + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc M * ((l : ℝ) + 2) ^ (l + 1) * (R - r) ^ (l + 1)
            = M * ((l : ℝ) + 2) * (R - r) ^ (l + 1) * ((l : ℝ) + 2) ^ l := by ring
          _ ≤ M * ((l : ℝ) + 2) * (R - r) ^ (l + 1) * (3 * ((l : ℝ) + 1) ^ l) := by gcongr
          _ = 3 * ((l : ℝ) + 2) * M * ((R - r) ^ (l + 1) * ((l : ℝ) + 1) ^ l) := by ring

/-- The per-term estimate of the Cauchy–Kovalevskaya induction. -/
theorem ra_ck_term {C σ R L r : ℝ} (hC : 0 ≤ C) (hσ : 0 < σ) (hσR : σ * R = 1 / 2) (hL : 1 ≤ L)
    (hr : 0 ≤ r) (hrR : r < R) {i l k : ℕ} (hk : i + l = k) :
    C * σ ^ i * 2 * (3 * ((l : ℝ) + 2) * (R * L ^ l) / (R - r) ^ (l + 1)) ≤
      6 * C * ((k : ℝ) + 2) * R * L ^ k * (1 / 2) ^ i / (R - r) ^ (k + 1) := by
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hR : 0 < R := by linarith
  have hsplit : (R - r) ^ (k + 1) = (R - r) ^ i * (R - r) ^ (l + 1) := by
    rw [← pow_add]; congr 1; omega
  have hlk : ((l : ℝ) + 2) ≤ (k : ℝ) + 2 := by
    have : (l : ℝ) ≤ k := by exact_mod_cast (show l ≤ k by omega)
    linarith
  have hLk : L ^ l ≤ L ^ k := pow_le_pow_right₀ hL (by omega)
  have hRi : (R - r) ^ i ≤ R ^ i := pow_le_pow_left₀ hRr.le (by linarith) i
  have hhalf : (1 / 2 : ℝ) ^ i = σ ^ i * R ^ i := by rw [← mul_pow, hσR]
  rw [hsplit, hhalf, ← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : ((l : ℝ) + 2) * L ^ l * (σ ^ i * (R - r) ^ i) ≤ ((k : ℝ) + 2) * L ^ k * (σ ^ i * R ^ i) := by
    have h1 : σ ^ i * (R - r) ^ i ≤ σ ^ i * R ^ i := mul_le_mul_of_nonneg_left hRi (by positivity)
    have h2 : ((l : ℝ) + 2) * L ^ l ≤ ((k : ℝ) + 2) * L ^ k :=
      mul_le_mul hlk hLk (by positivity) (by positivity)
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  have hpos : 0 ≤ 6 * C * R * (R - r) ^ (l + 1) := by positivity
  calc C * σ ^ i * 2 * (3 * ((l : ℝ) + 2) * (R * L ^ l)) * ((R - r) ^ i * (R - r) ^ (l + 1))
      = 6 * C * R * (R - r) ^ (l + 1) * (((l : ℝ) + 2) * L ^ l * (σ ^ i * (R - r) ^ i)) := by ring
    _ ≤ 6 * C * R * (R - r) ^ (l + 1) * (((k : ℝ) + 2) * L ^ k * (σ ^ i * R ^ i)) :=
        mul_le_mul_of_nonneg_left key hpos
    _ = 6 * C * ((k : ℝ) + 2) * R * L ^ k * (σ ^ i * R ^ i) * (R - r) ^ (l + 1) := by ring

/-- `∑_{(i,l) ∈ antidiagonal k} (1/2)^i ≤ 2`. -/
theorem ra_half_sum (k : ℕ) : ∑ il ∈ antidiagonal k, (1 / 2 : ℝ) ^ il.1 ≤ 2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => (1 / 2 : ℝ) ^ i) k]
  have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).sum_le_tsum
    (range (k + 1)) (fun i _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  norm_num at h ⊢
  exact h

/-- **Cauchy–Kovalevskaya bound** for the coefficient recursion of `φ_y = c φ_x`. -/
theorem ra_ck_bound {γ a : ℕ → ℕ → ℂ} {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 < σ)
    (hγ : ∀ j i, ‖γ j i‖ ≤ C * σ ^ (j + i))
    (ha0 : ∀ j, a j 0 = if j = 1 then 1 else 0)
    (hrec : ∀ j k : ℕ, ((k : ℂ) + 1) * a j (k + 1) =
      ∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j, γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * a (jj.2 + 1) il.2)) :
    ∃ B τ : ℝ, 0 < τ ∧ ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k) := by
  set R : ℝ := 1 / (2 * σ) with hR_def
  have hR : 0 < R := by positivity
  have hσR : σ * R = 1 / 2 := by rw [hR_def]; field_simp
  set L : ℝ := 24 * C + 1 with hL_def
  have hL : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have h24 : 24 * C ≤ L := by linarith
  clear_value R L
  have key : ∀ k J (r : ℝ), 0 ≤ r → r < R →
      ∑ j ∈ range J, ‖a j k‖ * r ^ j ≤ R * L ^ k / (R - r) ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro J r hr hrR
    rcases k with _ | k
    · have hterm : ∀ j ∈ range J, ‖a j 0‖ * r ^ j ≤ if j = 1 then r else 0 := by
        intro j _
        rw [ha0 j]
        split_ifs with h
        · subst h; simp
        · simp
      calc ∑ j ∈ range J, ‖a j 0‖ * r ^ j ≤ ∑ j ∈ range J, (if j = 1 then r else 0) := sum_le_sum hterm
        _ = if 1 ∈ range J then r else 0 := Finset.sum_ite_eq' _ _ _
        _ ≤ R * L ^ 0 / (R - r) ^ 0 := by
            simp only [pow_zero, div_one, mul_one]
            split_ifs <;> linarith
    · have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hRr : 0 < R - r := sub_pos.mpr hrR
      have hσr : σ * r ≤ 1 / 2 := by rw [← hσR]; exact mul_le_mul_of_nonneg_left hrR.le hσ.le
      have hcoef : ∀ j, ‖a j (k + 1)‖ * ((k : ℝ) + 1) ≤ ∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
          C * σ ^ (jj.1 + il.1) * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖) := by
        intro j
        have hn : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
        have h := congrArg norm (hrec j k)
        rw [norm_mul, hn] at h
        calc ‖a j (k + 1)‖ * ((k : ℝ) + 1) = ‖∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
              γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * a (jj.2 + 1) il.2)‖ := by rw [← h]; ring
          _ ≤ ∑ il ∈ antidiagonal k, ‖∑ jj ∈ antidiagonal j,
              γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * a (jj.2 + 1) il.2)‖ := norm_sum_le _ _
          _ ≤ ∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
              ‖γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * a (jj.2 + 1) il.2)‖ :=
              sum_le_sum fun il _ => norm_sum_le _ _
          _ ≤ _ := sum_le_sum fun il _ => sum_le_sum fun jj _ => by
              have hn2 : ‖((jj.2 : ℂ) + 1)‖ = (jj.2 : ℝ) + 1 := by
                exact_mod_cast Complex.norm_natCast (jj.2 + 1)
              rw [norm_mul, norm_mul, hn2]
              exact mul_le_mul_of_nonneg_right (hγ _ _) (by positivity)
      have hj : ∀ j, ‖a j (k + 1)‖ * r ^ j ≤ (1 / ((k : ℝ) + 1)) * ∑ il ∈ antidiagonal k,
          C * σ ^ il.1 * ∑ jj ∈ antidiagonal j,
            (σ * r) ^ jj.1 * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖ * r ^ jj.2) := by
        intro j
        have h1 : ‖a j (k + 1)‖ ≤ (1 / ((k : ℝ) + 1)) * ∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
            C * σ ^ (jj.1 + il.1) * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖) := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hk1]; exact hcoef j
        calc ‖a j (k + 1)‖ * r ^ j ≤ (1 / ((k : ℝ) + 1)) * (∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
              C * σ ^ (jj.1 + il.1) * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖)) * r ^ j :=
              mul_le_mul_of_nonneg_right h1 (pow_nonneg hr j)
          _ = _ := by
              rw [mul_assoc, Finset.sum_mul]
              congr 1
              refine sum_congr rfl fun il _ => ?_
              rw [Finset.sum_mul, Finset.mul_sum]
              refine sum_congr rfl fun jj hjj => ?_
              rw [HasAntidiagonal.mem_antidiagonal] at hjj
              rw [← hjj]
              ring
      have hgeo : ∑ m ∈ range J, (σ * r) ^ m ≤ 2 := by
        have hq0 : 0 ≤ σ * r := by positivity
        have hq1 : σ * r < 1 := by linarith
        have h := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (range J) (fun i _ => by positivity)
        rw [tsum_geometric_of_lt_one hq0 hq1] at h
        refine h.trans ?_
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hrow : ∀ il ∈ antidiagonal k, C * σ ^ il.1 * ∑ j ∈ range J, ∑ jj ∈ antidiagonal j,
            (σ * r) ^ jj.1 * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖ * r ^ jj.2) ≤
          6 * C * ((k : ℝ) + 2) * R * L ^ k * (1 / 2) ^ il.1 / (R - r) ^ (k + 1) := by
        intro il hil
        rw [HasAntidiagonal.mem_antidiagonal] at hil
        have hl : il.2 < k + 1 := by omega
        have hD := ra_deriv_sum (b := fun m => ‖a m il.2‖) (fun _ => norm_nonneg _)
          (by positivity : 0 ≤ R * L ^ il.2) (ih il.2 hl) hr hrR J
        have hconv := ra_conv_le (u := fun m => (σ * r) ^ m)
          (v := fun m => ((m : ℝ) + 1) * ‖a (m + 1) il.2‖ * r ^ m) (fun _ => by positivity)
          (fun _ => by positivity) J
        calc C * σ ^ il.1 * ∑ j ∈ range J, ∑ jj ∈ antidiagonal j,
              (σ * r) ^ jj.1 * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖ * r ^ jj.2)
            ≤ C * σ ^ il.1 * ((∑ m ∈ range J, (σ * r) ^ m) *
                ∑ m ∈ range J, ((m : ℝ) + 1) * ‖a (m + 1) il.2‖ * r ^ m) :=
              mul_le_mul_of_nonneg_left hconv (by positivity)
          _ ≤ C * σ ^ il.1 * (2 * (3 * ((il.2 : ℝ) + 2) * (R * L ^ il.2) / (R - r) ^ (il.2 + 1))) := by
              gcongr
          _ = C * σ ^ il.1 * 2 * (3 * ((il.2 : ℝ) + 2) * (R * L ^ il.2) / (R - r) ^ (il.2 + 1)) := by ring
          _ ≤ _ := ra_ck_term hC hσ hσR hL hr hrR hil
      calc ∑ j ∈ range J, ‖a j (k + 1)‖ * r ^ j
          ≤ ∑ j ∈ range J, (1 / ((k : ℝ) + 1)) * ∑ il ∈ antidiagonal k,
              C * σ ^ il.1 * ∑ jj ∈ antidiagonal j,
                (σ * r) ^ jj.1 * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖ * r ^ jj.2) :=
            sum_le_sum fun j _ => hj j
        _ = (1 / ((k : ℝ) + 1)) * ∑ il ∈ antidiagonal k, C * σ ^ il.1 * ∑ j ∈ range J,
              ∑ jj ∈ antidiagonal j,
                (σ * r) ^ jj.1 * (((jj.2 : ℝ) + 1) * ‖a (jj.2 + 1) il.2‖ * r ^ jj.2) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine sum_congr rfl fun il _ => ?_
            rw [Finset.mul_sum]
        _ ≤ (1 / ((k : ℝ) + 1)) * ∑ il ∈ antidiagonal k,
              6 * C * ((k : ℝ) + 2) * R * L ^ k * (1 / 2) ^ il.1 / (R - r) ^ (k + 1) := by
            gcongr with il hil
            exact hrow il hil
        _ = (1 / ((k : ℝ) + 1)) * (6 * C * ((k : ℝ) + 2) * R * L ^ k / (R - r) ^ (k + 1)) *
              ∑ il ∈ antidiagonal k, (1 / 2 : ℝ) ^ il.1 := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine sum_congr rfl fun il _ => ?_
            ring
        _ ≤ (1 / ((k : ℝ) + 1)) * (6 * C * ((k : ℝ) + 2) * R * L ^ k / (R - r) ^ (k + 1)) * 2 :=
            mul_le_mul_of_nonneg_left (ra_half_sum k) (by positivity)
        _ ≤ R * L ^ (k + 1) / (R - r) ^ (k + 1) := by
            have hX : 0 ≤ R * L ^ k / (R - r) ^ (k + 1) := by positivity
            have hk2 : ((k : ℝ) + 2) / ((k : ℝ) + 1) ≤ 2 := by
              rw [div_le_iff₀ hk1]; linarith
            calc 1 / ((k : ℝ) + 1) * (6 * C * ((k : ℝ) + 2) * R * L ^ k / (R - r) ^ (k + 1)) * 2
                = 12 * C * (((k : ℝ) + 2) / ((k : ℝ) + 1)) * (R * L ^ k / (R - r) ^ (k + 1)) := by
                  field_simp
                  ring
              _ ≤ 12 * C * 2 * (R * L ^ k / (R - r) ^ (k + 1)) := by gcongr
              _ ≤ L * (R * L ^ k / (R - r) ^ (k + 1)) := by gcongr; linarith
              _ = R * L ^ (k + 1) / (R - r) ^ (k + 1) := by ring
  refine ⟨R, 2 * L / R, by positivity, fun j k => ?_⟩
  have hr0 : (0 : ℝ) ≤ R / 2 := by positivity
  have hr1 : R / 2 < R := by linarith
  have h1 : ‖a j k‖ * (R / 2) ^ j ≤ R * L ^ k / (R - R / 2) ^ k := by
    refine le_trans ?_ (key k (j + 1) (R / 2) hr0 hr1)
    exact Finset.single_le_sum (f := fun m => ‖a m k‖ * (R / 2) ^ m) (fun m _ => by positivity)
      (Finset.self_mem_range_succ j)
  have h2 : ‖a j k‖ ≤ R * (2 * L / R) ^ k * (2 / R) ^ j := by
    have hR2 : R - R / 2 = R / 2 := by ring
    rw [hR2] at h1
    have hpj : 0 < (R / 2) ^ j := by positivity
    rw [← le_div_iff₀ hpj] at h1
    refine h1.trans (le_of_eq ?_)
    have e1 : 2 * L / R = L / (R / 2) := by field_simp
    have e2 : 2 / R = 1 / (R / 2) := by field_simp
    rw [e1, e2, div_pow L (R / 2) k, one_div_pow (R / 2) j]
    ring
  refine h2.trans ?_
  rw [pow_add, mul_assoc, mul_comm ((2 * L / R) ^ j)]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hR.le
  refine pow_le_pow_left₀ (by positivity) ?_ j
  gcongr
  linarith

/-- `HasSum` form of the antidiagonal regrouping. -/
theorem ra_hasSum_antidiag {t : ℕ × ℕ → ℂ} (h : Summable fun x => ‖t x‖) :
    HasSum (fun n => ∑ x ∈ antidiagonal n, t x) (∑' k, ∑' j, t (j, k)) := by
  have hs : Summable t := h.of_norm
  have hσ : Summable fun x => t (HasAntidiagonal.sigmaAntidiagonalEquivProd x) :=
    (HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr hs
  have hs' : Summable fun n => ∑ x ∈ antidiagonal n, t x := by
    refine (hσ.sigma).congr fun n => ?_
    rw [tsum_fintype]
    exact Finset.sum_coe_sort (antidiagonal n) t
  rw [← ra_tsum_antidiag h]
  exact hs'.hasSum

/-- Absolute summability of a geometrically bounded double series. -/
theorem ra_dsum_summable {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hτρ : τ * ρ ≤ 1 / 2) {x y : ℂ} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    Summable fun jk : ℕ × ℕ => ‖a jk.1 jk.2 * x ^ jk.1 * y ^ jk.2‖ := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((ha 0 0).trans (by simp))
  have hg : Summable fun j : ℕ => ‖(1 / 2 : ℝ) ^ j‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hprod := (summable_mul_of_summable_norm hg hg).mul_left B
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun jk => ?_) hprod
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 : ‖x‖ ^ jk.1 ≤ ρ ^ jk.1 := pow_le_pow_left₀ (norm_nonneg _) hx _
  have h2 : ‖y‖ ^ jk.2 ≤ ρ ^ jk.2 := pow_le_pow_left₀ (norm_nonneg _) hy _
  have h3 : (τ * ρ) ^ jk.1 ≤ (1 / 2) ^ jk.1 := pow_le_pow_left₀ (by positivity) hτρ _
  have h4 : (τ * ρ) ^ jk.2 ≤ (1 / 2) ^ jk.2 := pow_le_pow_left₀ (by positivity) hτρ _
  calc ‖a jk.1 jk.2‖ * ‖x‖ ^ jk.1 * ‖y‖ ^ jk.2 ≤ B * τ ^ (jk.1 + jk.2) * ρ ^ jk.1 * ρ ^ jk.2 := by
        gcongr
        exact ha _ _
    _ = B * ((τ * ρ) ^ jk.1 * (τ * ρ) ^ jk.2) := by ring
    _ ≤ B * ((1 / 2) ^ jk.1 * (1 / 2) ^ jk.2) := by gcongr

/-- The double series as an iterated series. -/
theorem ra_dsum_eq {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 ≤ ρ) (hτρ : τ * ρ ≤ 1 / 2) {x y : ℂ} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    HasSum (fun n => ∑ jk ∈ antidiagonal n, a jk.1 jk.2 * x ^ jk.1 * y ^ jk.2)
      (∑' k, (∑' j, a j k * x ^ j) * y ^ k) := by
  have h := ra_hasSum_antidiag (t := fun jk => a jk.1 jk.2 * x ^ jk.1 * y ^ jk.2)
    (ra_dsum_summable ha hτ hρ hτρ hx hy)
  convert h using 1
  refine tsum_congr fun k => ?_
  rw [← tsum_mul_right]

/-- Existence of the coefficient array solving the formal recursion. -/
theorem ra_rec_exists (γ : ℕ → ℕ → ℂ) : ∃ a : ℕ → ℕ → ℂ, (∀ j, a j 0 = if j = 1 then 1 else 0) ∧
    ∀ j k : ℕ, ((k : ℂ) + 1) * a j (k + 1) =
      ∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j, γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * a (jj.2 + 1) il.2) := by
  let row : ℕ → ℕ → ℂ := Nat.strongRec (motive := fun _ => ℕ → ℂ) (fun k IH =>
    if k = 0 then fun j => if j = 1 then 1 else 0 else
      fun j => (1 / (k : ℂ)) * ∑ il ∈ antidiagonal (k - 1), ∑ jj ∈ antidiagonal j,
        γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * (if h : il.2 < k then IH il.2 h else fun _ => 0) (jj.2 + 1)))
  have hrow0 : row 0 = fun j => if j = 1 then 1 else 0 := by
    rw [show row 0 = _ from Nat.strongRec_eq _ 0]
    rfl
  have hrow : ∀ k, row (k + 1) = fun j => (1 / ((k + 1 : ℕ) : ℂ)) * ∑ il ∈ antidiagonal k,
      ∑ jj ∈ antidiagonal j, γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * row il.2 (jj.2 + 1)) := by
    intro k
    rw [show row (k + 1) = _ from Nat.strongRec_eq _ (k + 1)]
    funext j
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    congr 1
    refine sum_congr rfl fun il hil => sum_congr rfl fun jj _ => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hil
    rw [dif_pos (by omega : il.2 < k + 1)]
  refine ⟨fun j k => row k j, fun j => by show row 0 j = _; rw [hrow0], fun j k => ?_⟩
  show ((k : ℂ) + 1) * row (k + 1) j = _
  rw [hrow k]
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

/-- **Expansion** of a real-analytic function at `0` as a double series in `x = Re`, `y = Im`. -/
theorem ra_expand {c : ℂ → ℂ} (hc : AnalyticAt ℝ c 0) :
    ∃ γ : ℕ → ℕ → ℂ, ∃ C σ δ : ℝ, 0 ≤ C ∧ 0 < σ ∧ 0 < δ ∧ (∀ j i, ‖γ j i‖ ≤ C * σ ^ (j + i)) ∧
      ∀ x y : ℝ, |x| < δ → |y| < δ → c (x + y * I) = ∑' k, (∑' j, γ j k * (x : ℂ) ^ j) * (y : ℂ) ^ k := by
  obtain ⟨p, r, hp⟩ := hc
  obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hr'p : (r' : ℝ≥0∞) < p.radius := lt_of_lt_of_le hr'r hp.r_le
  obtain ⟨C0, hC0, hC0b⟩ := p.norm_mul_pow_le_of_lt_radius hr'p
  have hr'pos : (0 : ℝ) < r' := by exact_mod_cast hr'0
  -- coefficients
  let e : (n : ℕ) → Finset (Fin n) → Fin n → ℂ := fun n s i => if i ∈ s then 1 else I
  let Γ : ℕ → ℕ → ℂ := fun n j => ∑ s ∈ (univ : Finset (Finset (Fin n))).filter (fun s => s.card = j),
    p n (e n s)
  have hpn : ∀ n, ‖p n‖ ≤ C0 / (r' : ℝ) ^ n := fun n => by
    rw [le_div_iff₀ (by positivity)]; exact hC0b n
  have hΓ : ∀ n j, ‖Γ n j‖ ≤ C0 * (2 / (r' : ℝ)) ^ n := by
    intro n j
    have he : ∀ s : Finset (Fin n), ‖p n (e n s)‖ ≤ ‖p n‖ := by
      intro s
      refine ((p n).le_opNorm _).trans (le_of_eq ?_)
      rw [Finset.prod_eq_one (fun i _ => by
        show ‖(if i ∈ s then (1 : ℂ) else I)‖ = 1
        split_ifs <;> simp), mul_one]
    have hcard : (((univ : Finset (Finset (Fin n))).filter (fun s => s.card = j)).card : ℝ) ≤ 2 ^ n := by
      have h1 := Finset.card_filter_le (univ : Finset (Finset (Fin n))) (fun s => s.card = j)
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h1
      exact_mod_cast h1
    calc ‖Γ n j‖ ≤ ∑ s ∈ (univ : Finset (Finset (Fin n))).filter (fun s => s.card = j), ‖p n (e n s)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s ∈ (univ : Finset (Finset (Fin n))).filter (fun s => s.card = j), ‖p n‖ :=
          sum_le_sum fun s _ => he s
      _ = (((univ : Finset (Finset (Fin n))).filter (fun s => s.card = j)).card : ℝ) * ‖p n‖ := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ n * (C0 / (r' : ℝ) ^ n) := by gcongr; exact hpn n
      _ = C0 * (2 / (r' : ℝ)) ^ n := by rw [div_pow]; ring
  refine ⟨fun j i => Γ (j + i) j, C0, 2 / r', r' / 4, hC0.le, by positivity, by positivity,
    fun j i => hΓ _ _, fun x y hx hy => ?_⟩
  -- evaluation
  set z : ℂ := x + y * I with hz
  have hzn : ‖z‖ < r' / 2 := by
    calc ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + |y| := by simp [Complex.norm_real]
      _ < r' / 4 + r' / 4 := add_lt_add hx hy
      _ = r' / 2 := by ring
  have hzball : z ∈ Metric.eball (0 : ℂ) r := by
    show edist z 0 < r
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hr'r.le
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr'pos).mpr (by linarith)
  have hsum := hp.hasSum hzball
  rw [zero_add] at hsum
  -- each term
  have hterm : ∀ n, p n (fun _ => z) =
      ∑ jk ∈ antidiagonal n, Γ (jk.1 + jk.2) jk.1 * (x : ℂ) ^ jk.1 * (y : ℂ) ^ jk.2 := by
    intro n
    have hsplit : (fun _ : Fin n => z) = (fun _ => (x : ℝ) • (1 : ℂ)) + (fun _ => (y : ℝ) • I) := by
      funext i
      simp [hz, Complex.real_smul]
    have hpw : ∀ s : Finset (Fin n), s.piecewise (fun _ => (x : ℝ) • (1 : ℂ)) (fun _ => (y : ℝ) • I) =
        fun i => (if i ∈ s then x else y) • e n s i := by
      intro s
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi, e]
    have hprod : ∀ s : Finset (Fin n), (∏ i, (if i ∈ s then x else y)) = x ^ s.card * y ^ (n - s.card) := by
      intro s
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have h1 : (univ : Finset (Fin n)).filter (fun i => i ∈ s) = s := by ext i; simp
      have h2 : (univ : Finset (Fin n)).filter (fun i => i ∉ s) = sᶜ := by ext i; simp
      rw [h1, h2, Finset.card_compl, Fintype.card_fin]
    rw [hsplit, (p n).map_add_univ]
    simp_rw [hpw, (p n).map_smul_univ, hprod]
    -- group by cardinality
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Finset (Fin n) => s.card) (t := range (n + 1))
      (fun s _ => by rw [Finset.mem_range]; exact Nat.lt_succ_of_le (by simpa using s.card_le_univ))]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j k => Γ (j + k) j * (x : ℂ) ^ j * (y : ℂ) ^ k) n]
    refine sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hjn : j + (n - j) = n := by omega
    rw [hjn]
    have hfib : ∀ s ∈ (univ : Finset (Finset (Fin n))).filter (fun s => s.card = j),
        (x ^ s.card * y ^ (n - s.card)) • p n (e n s) = ((x : ℂ) ^ j * (y : ℂ) ^ (n - j)) * p n (e n s) := by
      intro s hs
      rw [mem_filter] at hs
      rw [hs.2, Complex.real_smul]
      push_cast
      ring
    rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
    ring
  have hsum' : HasSum (fun n => ∑ jk ∈ antidiagonal n,
      (fun j i => Γ (j + i) j) jk.1 jk.2 * (x : ℂ) ^ jk.1 * (y : ℂ) ^ jk.2) (c z) := by
    convert hsum using 1
    funext n
    exact (hterm n).symm
  have hx' : ‖(x : ℂ)‖ ≤ r' / 4 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx.le
  have hy' : ‖(y : ℂ)‖ ≤ r' / 4 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hy.le
  have hd := ra_dsum_eq (a := fun j i => Γ (j + i) j) (fun j i => hΓ _ _) (by positivity) (by positivity)
    (by rw [div_mul_div_comm]; field_simp; norm_num) hx' hy'
  exact hsum'.unique hd

/-- **Double-series analyticity.** A geometrically bounded double power series in `Re z`, `Im z` is
real-analytic at `0`. -/
theorem ra_DS {a : ℕ → ℕ → ℂ} {B τ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 < τ) :
    AnalyticAt ℝ (fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k) 0 := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((ha 0 0).trans (by simp))
  let p : FormalMultilinearSeries ℝ ℂ ℂ := fun n => ∑ jk ∈ antidiagonal n,
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a jk.1 jk.2)).compContinuousLinearMap
      (fun i : Fin n => if (i : ℕ) < jk.1 then reCLM else imCLM)
  have hval : ∀ n (z : ℂ), p n (fun _ => z) =
      ∑ jk ∈ antidiagonal n, a jk.1 jk.2 * (z.re : ℂ) ^ jk.1 * (z.im : ℂ) ^ jk.2 := by
    intro n z
    simp only [p, _root_.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiRing_apply]
    refine sum_congr rfl fun jk hjk => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hjk
    have hprod : (∏ i : Fin n, (if (i : ℕ) < jk.1 then reCLM else imCLM : ℂ →L[ℝ] ℝ) z) =
        z.re ^ jk.1 * z.im ^ jk.2 := by
      have hc : (∏ i : Fin n, (if (i : ℕ) < jk.1 then reCLM else imCLM : ℂ →L[ℝ] ℝ) z) =
          ∏ i : Fin n, (if (i : ℕ) < jk.1 then z.re else z.im) :=
        Finset.prod_congr rfl fun i _ => by split_ifs <;> simp
      rw [hc, Fin.prod_univ_eq_prod_range (fun i => if i < jk.1 then z.re else z.im) n,
        Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have h1 : (range n).filter (fun i => i < jk.1) = range jk.1 := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
      have h2 : ((range n).filter (fun i => ¬ i < jk.1)).card = jk.2 := by
        have h3 : (range n).filter (fun i => ¬ i < jk.1) = Finset.Ico jk.1 n := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [h3, Nat.card_Ico]
        omega
      rw [h1, h2, card_range]
    rw [hprod, Complex.real_smul]
    push_cast
    ring
  have hnorm : ∀ n, ‖p n‖ ≤ ((n : ℝ) + 1) * B * τ ^ n := by
    intro n
    calc ‖p n‖ ≤ ∑ jk ∈ antidiagonal n, ‖(ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (a jk.1 jk.2)).compContinuousLinearMap
          (fun i : Fin n => if (i : ℕ) < jk.1 then reCLM else imCLM)‖ := norm_sum_le _ _
      _ ≤ ∑ jk ∈ antidiagonal n, B * τ ^ n := by
          refine sum_le_sum fun jk hjk => ?_
          rw [HasAntidiagonal.mem_antidiagonal] at hjk
          refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
          rw [ContinuousMultilinearMap.norm_mkPiRing, Finset.prod_eq_one (fun i _ => by
            show ‖(if (i : ℕ) < jk.1 then reCLM else imCLM : ℂ →L[ℝ] ℝ)‖ = 1
            split_ifs
            · exact Complex.reCLM_norm
            · exact Complex.imCLM_norm), mul_one, ← hjk]
          exact ha _ _
      _ = ((n : ℝ) + 1) * B * τ ^ n := by
          rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
  set ρ : ℝ := 1 / (2 * τ) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hτρ : τ * ρ = 1 / 2 := by rw [hρ_def]; field_simp
  have hρc : ((Real.toNNReal ρ : ℝ≥0) : ℝ) = ρ := Real.coe_toNNReal ρ hρ.le
  have hrad : ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound B fun n => ?_
    rw [hρc]
    have h2n : ((n : ℝ) + 1) ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this
    calc ‖p n‖ * ρ ^ n ≤ ((n : ℝ) + 1) * B * τ ^ n * ρ ^ n := by gcongr; exact hnorm n
      _ = ((n : ℝ) + 1) * B * (1 / 2) ^ n := by rw [mul_assoc _ (τ ^ n), ← mul_pow, hτρ]
      _ ≤ 2 ^ n * B * (1 / 2) ^ n := by gcongr
      _ = B := by rw [mul_comm (2 ^ n) B, mul_assoc, ← mul_pow]; norm_num
  have hball : HasFPowerSeriesOnBall (fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k) p 0
      ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) := by
    refine { r_le := hrad, r_pos := by simpa using hρ, hasSum := fun {y} hy => ?_ }
    rw [zero_add]
    have hy' : ‖y‖ < ρ := by
      have hy2 : edist y 0 < ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) := hy
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, hρc] at hy2
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hy2
    have hre : ‖((y.re : ℝ) : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_re_le_norm y).trans hy'.le
    have him : ‖((y.im : ℝ) : ℂ)‖ ≤ ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (abs_im_le_norm y).trans hy'.le
    have hd := ra_dsum_eq ha hτ.le hρ.le hτρ.le hre him
    convert hd using 1
    funext n
    exact hval n y
  exact hball.analyticAt

/-- Directional derivatives of a double power series in `Re z`, `Im z`. -/
theorem ra_phi_fderiv {a : ℕ → ℕ → ℂ} {B τ ρ : ℝ} (ha : ∀ j k, ‖a j k‖ ≤ B * τ ^ (j + k)) (hτ : 0 ≤ τ)
    (hρ : 0 < ρ) (hτρ : τ * ρ < 1) {h : ℂ} (hre : |h.re| < ρ) (him : |h.im| < ρ)
    (hd : DifferentiableAt ℝ (fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k) h) :
    fderiv ℝ (fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k) h 1 =
        ∑' k, (∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (h.re : ℂ) ^ j) * (h.im : ℂ) ^ k ∧
      fderiv ℝ (fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k) h I =
        ∑' k : ℕ, ((k : ℂ) + 1) * (∑' j, a j (k + 1) * (h.re : ℂ) ^ j) * (h.im : ℂ) ^ k := by
  set Φ := fun z : ℂ => ∑' k, (∑' j, a j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k with hΦ
  constructor
  · have hl : HasDerivAt (fun t : ℝ => h + (t : ℂ)) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add h
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    have hG := ra_G_hasDerivAt_x ha hτ hρ hτρ hre him.le
    have hG' : HasDerivAt (fun s : ℝ => ∑' k, (∑' j, a j k * (s : ℂ) ^ j) * (h.im : ℂ) ^ k)
        (∑' k, (∑' j : ℕ, ((j : ℂ) + 1) * a (j + 1) k * (h.re : ℂ) ^ j) * (h.im : ℂ) ^ k) (h.re + 0) := by
      rw [add_zero]; exact hG
    have h2 := hG'.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add h.re)
    rw [one_smul] at h2
    refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    simp only [Function.comp, hΦ, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, add_zero]
  · have hl : HasDerivAt (fun t : ℝ => h + (t : ℂ) * I) I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add h
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    have hG := ra_G_hasDerivAt_y ha hτ hρ hτρ hre.le him
    have hG' : HasDerivAt (fun s : ℝ => ∑' k, (∑' j, a j k * (h.re : ℂ) ^ j) * (s : ℂ) ^ k)
        (∑' k : ℕ, ((k : ℂ) + 1) * (∑' j, a j (k + 1) * (h.re : ℂ) ^ j) * (h.im : ℂ) ^ k) (h.im + 0) := by
      rw [add_zero]; exact hG
    have h2 := hG'.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add h.im)
    rw [one_smul] at h2
    refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    simp only [Function.comp, hΦ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero]

/-- `∑' k, f k * 0 ^ k = f 0`. -/
theorem ra_tsum_zero_pow (f : ℕ → ℂ) : ∑' k, f k * (0 : ℂ) ^ k = f 0 := by
  rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
  simp

/-- Scaling and translation of `∂`, `∂̄`. -/
theorem ra_dz_scale {Φ : ℂ → ℂ} {K z₀ z : ℂ} (hd : DifferentiableAt ℝ Φ (z - z₀)) :
    dz (fun w => K * Φ (w - z₀)) z = K * dz Φ (z - z₀) ∧
      dzbar (fun w => K * Φ (w - z₀)) z = K * dzbar Φ (z - z₀) := by
  have hd' : DifferentiableAt ℝ (fun w => Φ (w - z₀)) z := hd.comp z (differentiableAt_id.sub_const z₀)
  have hf : ∀ v : ℂ, fderiv ℝ (fun w => K * Φ (w - z₀)) z v = K * fderiv ℝ Φ (z - z₀) v := by
    intro v
    rw [fderiv_const_mul hd' K, smul_apply, smul_eq_mul, fderiv_comp_sub]
  constructor
  · show (fderiv ℝ (fun w => K * Φ (w - z₀)) z 1 - I * fderiv ℝ (fun w => K * Φ (w - z₀)) z I) / 2 =
      K * ((fderiv ℝ Φ (z - z₀) 1 - I * fderiv ℝ Φ (z - z₀) I) / 2)
    rw [hf, hf]; ring
  · show (fderiv ℝ (fun w => K * Φ (w - z₀)) z 1 + I * fderiv ℝ (fun w => K * Φ (w - z₀)) z I) / 2 =
      K * ((fderiv ℝ Φ (z - z₀) 1 + I * fderiv ℝ Φ (z - z₀) I) / 2)
    rw [hf, hf]; ring

/-- **R1** (wall). Local real-analytic solutions of the Beltrami equation with real-analytic coefficient. -/
theorem ra_local_solution {a : ℂ → ℂ} {z₀ : ℂ} (ha : AnalyticAt ℝ a z₀) (h1 : ‖a z₀‖ < 1) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℝ φ z₀ ∧ dz φ z₀ = 1 ∧ ∀ᶠ z in 𝓝 z₀, dzbar φ z = a z * dz φ z := by
  set A : ℂ → ℂ := fun h => a (z₀ + h) with hA_def
  have hA : AnalyticAt ℝ A 0 := by
    have : AnalyticAt ℝ (fun h : ℂ => z₀ + h) 0 := analyticAt_const.add analyticAt_id
    exact ha.comp_of_eq this (by simp)
  have hA0 : A 0 = a z₀ := by simp [hA_def]
  have hA1 : 1 + A 0 ≠ 0 := by
    intro h
    have h' : A 0 = -1 := by linear_combination h
    rw [hA0] at h'
    rw [h'] at h1
    simp at h1
  set c : ℂ → ℂ := fun h => I * (1 - A h) / (1 + A h) with hc_def
  have hc : AnalyticAt ℝ c 0 :=
    (analyticAt_const.mul (analyticAt_const.sub hA)).div (analyticAt_const.add hA) hA1
  obtain ⟨γ, C, σ, δ, hC, hσ, hδ, hγ, hcexp⟩ := ra_expand hc
  obtain ⟨arr, h0, hrec⟩ := ra_rec_exists γ
  obtain ⟨B, τ, hτ, harr⟩ := ra_ck_bound hC hσ hγ h0 hrec
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((harr 0 0).trans (by simp))
  set T : ℝ := max σ (2 * τ) + 1 with hT_def
  have hT : 0 < T := by positivity
  have hσT : σ ≤ T := by have := le_max_left σ (2 * τ); linarith
  have hτT : 2 * τ ≤ T := by have := le_max_right σ (2 * τ); linarith
  set B' : ℝ := max C (B * τ) with hB'_def
  set ρ : ℝ := min (δ / 2) (1 / (4 * T)) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρδ : ρ < δ := by have := min_le_left (δ / 2) (1 / (4 * T)); linarith
  have hTρ : T * ρ ≤ 1 / 4 := by
    have := min_le_right (δ / 2) (1 / (4 * T))
    calc T * ρ ≤ T * (1 / (4 * T)) := mul_le_mul_of_nonneg_left this hT.le
      _ = 1 / 4 := by field_simp
  have hτρ : τ * ρ < 1 := by
    have : τ * ρ ≤ T * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ.le
    linarith
  -- bounds for the product
  have hu : ∀ j i, ‖γ j i‖ ≤ B' * T ^ (j + i) := fun j i =>
    (hγ j i).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hσ.le hσT _) (by positivity)
      (by positivity))
  have hv : ∀ j l : ℕ, ‖((j : ℂ) + 1) * arr (j + 1) l‖ ≤ B' * T ^ (j + l) := by
    intro j l
    have hj : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (j + 1)
    have h2j : (j : ℝ) + 1 ≤ 2 ^ (j + l) := by
      have h3 : j < 2 ^ j := Nat.lt_two_pow_self
      have h4 : (2 : ℝ) ^ j ≤ 2 ^ (j + l) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h5 : ((j : ℝ) + 1) ≤ 2 ^ j := by exact_mod_cast h3
      linarith
    rw [norm_mul, hj]
    calc ((j : ℝ) + 1) * ‖arr (j + 1) l‖ ≤ 2 ^ (j + l) * (B * τ ^ (j + 1 + l)) :=
          mul_le_mul h2j (harr _ _) (norm_nonneg _) (by positivity)
      _ = B * τ * (2 * τ) ^ (j + l) := by
          rw [mul_pow, show j + 1 + l = (j + l) + 1 by omega, pow_succ]; ring
      _ ≤ B' * T ^ (j + l) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by positivity) hτT _) (by positivity)
            (by positivity)
  set Φ : ℂ → ℂ := fun z => ∑' k, (∑' j, arr j k * (z.re : ℂ) ^ j) * (z.im : ℂ) ^ k with hΦ_def
  have hΦ : AnalyticAt ℝ Φ 0 := ra_DS harr hτ
  -- the PDE for `Φ` at points of the small square
  have hpde : ∀ h : ℂ, |h.re| < ρ → |h.im| < ρ → DifferentiableAt ℝ Φ h →
      fderiv ℝ Φ h I = c h * fderiv ℝ Φ h 1 := by
    intro h hre him hd
    obtain ⟨hP, hQ⟩ := ra_phi_fderiv harr hτ.le hρ hτρ hre him hd
    rw [hP, hQ]
    have hch : c h = ∑' k, (∑' j, γ j k * (h.re : ℂ) ^ j) * (h.im : ℂ) ^ k := by
      have := hcexp h.re h.im (hre.trans hρδ) (him.trans hρδ)
      rw [← this, Complex.re_add_im]
    have hx : ‖((h.re : ℝ) : ℂ)‖ ≤ ρ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hre.le
    have hy : ‖((h.im : ℝ) : ℂ)‖ ≤ ρ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact him.le
    have hTρ1 : T * ρ < 1 := by linarith
    rw [hch, ra_dprod (v := fun j l => ((j : ℂ) + 1) * arr (j + 1) l) hu hv hT.le hρ.le hTρ1 hx hy]
    refine tsum_congr fun k => ?_
    have hk : ∑' j : ℕ, (∑ il ∈ antidiagonal k, ∑ jj ∈ antidiagonal j,
        γ jj.1 il.1 * (((jj.2 : ℂ) + 1) * arr (jj.2 + 1) il.2)) * (h.re : ℂ) ^ j =
        ((k : ℂ) + 1) * ∑' j, arr j (k + 1) * (h.re : ℂ) ^ j := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by rw [← hrec j k]; ring
    rw [hk]
  -- `1 + A` does not vanish near `0`
  have hev : ∀ᶠ h in 𝓝 (0 : ℂ), DifferentiableAt ℝ Φ h ∧ ‖h‖ < ρ ∧ 1 + A h ≠ 0 := by
    have e1 : ∀ᶠ h in 𝓝 (0 : ℂ), DifferentiableAt ℝ Φ h :=
      hΦ.eventually_analyticAt.mono fun h hh => hh.differentiableAt
    have e2 : ∀ᶠ h in 𝓝 (0 : ℂ), ‖h‖ < ρ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with h hh
      simpa using hh
    have e3 : ∀ᶠ h in 𝓝 (0 : ℂ), 1 + A h ≠ 0 :=
      (continuousAt_const.add hA.continuousAt).eventually_ne hA1
    filter_upwards [e1, e2, e3] with h h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hsq : ∀ h : ℂ, ‖h‖ < ρ → |h.re| < ρ ∧ |h.im| < ρ := fun h hh =>
    ⟨(abs_re_le_norm h).trans_lt hh, (abs_im_le_norm h).trans_lt hh⟩
  -- the algebraic identity
  have hkey : ∀ h : ℂ, 1 + A h ≠ 0 → 1 + I * c h = A h * (1 - I * c h) := by
    intro h hh
    have hIc : I * c h = -(1 - A h) / (1 + A h) := by
      simp only [hc_def]
      rw [← mul_div_assoc, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [hIc]
    field_simp
    ring
  refine ⟨fun z => (1 + A 0) * Φ (z - z₀), ?_, ?_, ?_⟩
  · have h := hΦ.comp_sub z₀
    rw [zero_add] at h
    exact analyticAt_const.mul h
  · obtain ⟨hd0, hn0, -⟩ := hev.self_of_nhds
    have hd0' : DifferentiableAt ℝ Φ (z₀ - z₀) := by rw [sub_self]; exact hd0
    rw [(ra_dz_scale hd0').1, sub_self]
    obtain ⟨hr0, hi0⟩ := hsq 0 hn0
    have hQ := hpde 0 hr0 hi0 hd0
    have hP : fderiv ℝ Φ 0 1 = 1 := by
      rw [(ra_phi_fderiv harr hτ.le hρ hτρ hr0 hi0 hd0).1]
      simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero]
      rw [ra_tsum_zero_pow, ra_tsum_zero_pow (fun j => ((j : ℂ) + 1) * arr (j + 1) 0)]
      rw [h0 1]
      simp
    show (1 + A 0) * ((fderiv ℝ Φ 0 1 - I * fderiv ℝ Φ 0 I) / 2) = 1
    rw [hQ, hP, mul_one]
    have hk := hkey 0 hA1
    have h2 : (1 + A 0) * (1 - I * c 0) = 2 := by
      have hIc : I * c 0 = -(1 - A 0) / (1 + A 0) := by
        simp only [hc_def]
        rw [← mul_div_assoc, ← mul_assoc, Complex.I_mul_I]
        ring
      rw [hIc]
      field_simp
      ring
    linear_combination h2 / 2
  · have ht : Filter.Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
      have h := (tendsto_id (x := 𝓝 z₀)).sub (tendsto_const_nhds (x := z₀))
      rw [sub_self] at h
      exact h
    filter_upwards [ht.eventually hev] with z hz
    obtain ⟨hd, hn, hne⟩ := hz
    obtain ⟨hre, him⟩ := hsq _ hn
    obtain ⟨hdz, hdzbar⟩ := ra_dz_scale (K := 1 + A 0) hd
    rw [hdz, hdzbar]
    have hAz : A (z - z₀) = a z := by simp [hA_def]
    have hQ := hpde _ hre him hd
    have hk := hkey _ hne
    rw [hAz] at hk
    show (1 + A 0) * ((fderiv ℝ Φ (z - z₀) 1 + I * fderiv ℝ Φ (z - z₀) I) / 2) =
      a z * ((1 + A 0) * ((fderiv ℝ Φ (z - z₀) 1 - I * fderiv ℝ Φ (z - z₀) I) / 2))
    rw [hQ]
    linear_combination ((1 + A 0) * fderiv ℝ Φ (z - z₀) 1 / 2) * hk

end RAOne

/-- A function continuous on an open set and a.e. bounded there is bounded everywhere there. -/
theorem ra_le_of_ae_le {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContinuousOn g U) {k : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict U), ‖g z‖ ≤ k) : ∀ z ∈ U, ‖g z‖ ≤ k := by
  by_contra hne
  push Not at hne
  obtain ⟨z₀, hz₀, hk⟩ := hne
  have hS : IsOpen (U ∩ g ⁻¹' {w | k < ‖w‖}) :=
    hg.isOpen_inter_preimage hU (isOpen_lt continuous_const continuous_norm)
  have hS0 : volume (U ∩ g ⁻¹' {w | k < ‖w‖}) = 0 := by
    rw [ae_restrict_iff' hU.measurableSet, ae_iff] at h
    refine measure_mono_null (fun z hz => ?_) h
    simp only [Set.mem_ofPred_eq, not_imp, not_le]
    exact ⟨hz.1, hz.2⟩
  exact (IsOpen.measure_pos (μ := volume) hS ⟨z₀, hz₀, hk⟩).ne' hS0

/-- A quasiconformal map carries `a.e.` statements on `D` to `a.e.` statements on `φ(D)`. -/
theorem ra_ae_image {φ : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hφ : IsKQC φ D K) {P : ℂ → Prop}
    (h : ∀ᵐ z ∂(volume.restrict D), P (φ z)) : ∀ᵐ w ∂(volume.restrict (φ '' D)), P w := by
  have hD : MeasurableSet D := hφ.1.measurableSet
  have hD' : MeasurableSet (φ '' D) :=
    (isOpen_image_of_continuousOn_injOn hφ.1 hφ.2.2.1.1 hφ.2.2.1.2.1).measurableSet
  rw [ae_restrict_iff' hD, ae_iff] at h
  have hN : {z | ¬(z ∈ D → P (φ z))} ⊆ D := fun z hz => by
    simp only [Set.mem_ofPred_eq, not_imp] at hz
    exact hz.1
  have himg := thm9_6_cor1_null hφ hN h
  rw [ae_restrict_iff' hD', ae_iff]
  refine measure_mono_null (fun w hw => ?_) himg
  simp only [Set.mem_ofPred_eq, not_imp] at hw
  obtain ⟨⟨z, hz, rfl⟩, hP⟩ := hw
  refine ⟨z, ?_, rfl⟩
  simp only [Set.mem_ofPred_eq, not_imp]
  exact ⟨hz, hP⟩

/-- **R2.** A quasiconformal map whose complex dilatation is a.e. a real-analytic function is real-analytic, with
nonvanishing `∂f`. -/
theorem ra_qc_analytic {f g : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) (hg : AnalyticOnNhd ℝ g U)
    (hfg : ∀ᵐ z ∂(volume.restrict U), complexDilatation f z = g z) :
    ∀ z ∈ U, AnalyticAt ℝ f z ∧ dz f z ≠ 0 := by
  have hU : IsOpen U := hf.1
  have hK1 : 1 ≤ K := hf.2.1
  set k : ℝ := (K - 1) / (K + 1) with hk_def
  have hk1 : k < 1 := by rw [hk_def, div_lt_one (by linarith)]; linarith
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hgk : ∀ z ∈ U, ‖g z‖ ≤ k := by
    refine ra_le_of_ae_le hU (fun z hz => (hg z hz).continuousAt.continuousWithinAt) ?_
    filter_upwards [(isKQC_maxDilatation_le hf).2, hfg] with z h1 h2
    rw [← h2]
    exact h1
  intro z₀ hz₀
  obtain ⟨φ, hφa, hφ1, hφpde⟩ := ra_local_solution (hg z₀ hz₀) ((hgk z₀ hz₀).trans_lt hk1)
  have hφd : DifferentiableAt ℝ φ z₀ := hφa.differentiableAt
  -- the derivative at `z₀` is invertible
  have hL : ∀ v, fderiv ℝ φ z₀ v = v + g z₀ * conj v := by
    intro v
    rw [fderiv_eq_dz_dzbar hφd v, hφpde.self_of_nhds, hφ1]
    ring
  have hinj : Function.Injective (fderiv ℝ φ z₀) := by
    intro v w hvw
    have h0 : fderiv ℝ φ z₀ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    rw [hL] at h0
    by_contra hne
    have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
    have h2 : ‖v - w‖ = ‖g z₀‖ * ‖v - w‖ := by
      have h5 : v - w = -(g z₀ * conj (v - w)) := by linear_combination h0
      calc ‖v - w‖ = ‖-(g z₀ * conj (v - w))‖ := by rw [← h5]
        _ = ‖g z₀‖ * ‖v - w‖ := by rw [norm_neg, norm_mul, Complex.norm_conj]
    have h3 : ‖g z₀‖ < 1 := (hgk z₀ hz₀).trans_lt hk1
    have h4 : 0 < ‖v - w‖ := norm_pos_iff.mpr hne'
    nlinarith
  let i : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ φ z₀).toLinearMap hinj).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt φ (i : ℂ →L[ℝ] ℂ) z₀ := by
    have h := hφa.hasStrictFDerivAt
    convert h using 1
    exact ContinuousLinearMap.ext fun v => rfl
  set e := hstrict.toOpenPartialHomeomorph φ with he_def
  have hecoe : (e : ℂ → ℂ) = φ := hstrict.toOpenPartialHomeomorph_coe
  have hsrc : z₀ ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- a small disc
  have hdzc : ContinuousAt (dz φ) z₀ := by
    have hc := hφa.fderiv.continuousAt
    show ContinuousAt (fun z => (fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) / 2) z₀
    exact ((hc.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (hc.clm_apply continuousAt_const))).div_const _
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ z ∈ e.source ∧ AnalyticAt ℝ φ z ∧ dzbar φ z = g z * dz φ z ∧
      dz φ z ≠ 0 := by
    filter_upwards [hU.mem_nhds hz₀, e.open_source.mem_nhds hsrc, hφa.eventually_analyticAt, hφpde,
      hdzc.eventually_ne (by rw [hφ1]; exact one_ne_zero)] with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hDU : ball z₀ r ⊆ U := fun z hz => (hball z hz).1
  have hinjD : InjOn φ (ball z₀ r) := by
    have := e.injOn.mono (fun z hz => (hball z hz).2.1)
    rwa [hecoe] at this
  have hleft : ∀ z ∈ ball z₀ r, Function.invFunOn φ (ball z₀ r) (φ z) = z :=
    fun z hz => hinjD.leftInvOn_invFunOn hz
  have hμφ : ∀ z ∈ ball z₀ r, complexDilatation φ z = g z := by
    intro z hz
    obtain ⟨-, -, -, h4, h5⟩ := hball z hz
    show dzbar φ z / dz φ z = g z
    rw [h4]
    field_simp
  -- `φ` is quasiconformal on the disc
  set K' : ℝ := (1 + k) / (1 - k) with hK'_def
  have hk1' : 0 < 1 - k := by linarith
  have hφC1 : IsC1Quasiconformal φ (ball z₀ r) K' := by
    refine ⟨isOpen_ball, ?_, fun z hz => (hball z hz).2.2.1.contDiffAt.contDiffWithinAt,
      ⟨fun z hz => (hball z hz).2.2.1.continuousAt.continuousWithinAt, hinjD, rfl, ?_⟩, fun z hz => ?_⟩
    · rw [hK'_def, le_div_iff₀ hk1']; linarith
    · refine (e.continuousOn_symm.mono ?_).congr ?_
      · rintro _ ⟨z, hz, rfl⟩
        rw [← hecoe]
        exact e.map_source (hball z hz).2.1
      · rintro _ ⟨z, hz, rfl⟩
        rw [hleft z hz]
        have := e.left_inv (hball z hz).2.1
        rw [hecoe] at this
        exact this.symm
    · obtain ⟨h1, -, -, h4, h5⟩ := hball z hz
      have hgz := hgk z h1
      have hdz : 0 < ‖dz φ z‖ := norm_pos_iff.mpr h5
      refine ⟨?_, ?_⟩
      · rw [h4, norm_mul]
        calc ‖g z‖ * ‖dz φ z‖ ≤ k * ‖dz φ z‖ := by gcongr
          _ < 1 * ‖dz φ z‖ := by gcongr
          _ = ‖dz φ z‖ := one_mul _
      · show (1 + ‖complexDilatation φ z‖) / (1 - ‖complexDilatation φ z‖) ≤ K'
        rw [hμφ z hz, hK'_def, div_le_div_iff₀ (by linarith) hk1']
        nlinarith
  have hφq := isKQC_of_isC1Quasiconformal hφC1
  have hfD := nx_isKQC_restrict hf isOpen_ball hDU
  have hψ := thm7_2_inv hφq
  have hsub : Function.invFunOn φ (ball z₀ r) '' (φ '' ball z₀ r) ⊆ ball z₀ r := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [hleft z hz]
    exact hz
  have hF := thm7_1_comp hψ hfD hsub
  -- the dilatation of `F = f ∘ φ⁻¹` vanishes
  have hfgD : ∀ᵐ z ∂(volume.restrict (ball z₀ r)), complexDilatation f z = g z :=
    ae_restrict_of_ae_restrict_of_subset hDU hfg
  have h0 : ∀ᵐ z ∂(volume.restrict (ball z₀ r)),
      complexDilatation (f ∘ Function.invFunOn φ (ball z₀ r)) (φ z) = 0 := by
    filter_upwards [ab_comp_inv_dilatation hfD hφq, hfgD, ae_restrict_mem isOpen_ball.measurableSet]
      with z h1 h2 h3
    rw [h2, hμφ z h3, sub_self, norm_zero] at h1
    have hgz : ‖g z‖ < 1 := (hgk z (hDU h3)).trans_lt hk1
    have hpos : ‖1 - conj (g z) * g z‖ ≠ 0 := by
      rw [Complex.conj_mul']
      have : (0 : ℝ) < 1 - ‖g z‖ ^ 2 := by nlinarith [norm_nonneg (g z)]
      intro h
      rw [norm_eq_zero, sub_eq_zero] at h
      have h' := congrArg Complex.re h
      simp only [Complex.one_re] at h'
      rw [← Complex.ofReal_pow, Complex.ofReal_re] at h'
      linarith
    exact norm_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hpos)
  have h0' := ra_ae_image (P := fun w => complexDilatation (f ∘ Function.invFunOn φ (ball z₀ r)) w = 0) hφq h0
  have hFhol := nx_differentiableOn_of_dilatation_zero hF h0'
  have hopen : IsOpen (φ '' ball z₀ r) :=
    isOpen_image_of_continuousOn_injOn isOpen_ball hφq.2.2.1.1 hinjD
  have hmem : φ z₀ ∈ φ '' ball z₀ r := ⟨z₀, mem_ball_self hr, rfl⟩
  have hFa : AnalyticAt ℂ (f ∘ Function.invFunOn φ (ball z₀ r)) (φ z₀) :=
    hFhol.analyticAt (hopen.mem_nhds hmem)
  have hcomp : AnalyticAt ℝ ((f ∘ Function.invFunOn φ (ball z₀ r)) ∘ φ) z₀ :=
    (hFa.restrictScalars (𝕜 := ℝ)).comp hφa
  have heq : f =ᶠ[𝓝 z₀] (f ∘ Function.invFunOn φ (ball z₀ r)) ∘ φ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    simp only [Function.comp, hleft z hz]
  refine ⟨hcomp.congr heq.symm, ?_⟩
  -- `∂f(z₀) = F'(φ z₀) ≠ 0`
  have hFdC : DifferentiableAt ℂ (f ∘ Function.invFunOn φ (ball z₀ r)) (φ z₀) := hFa.differentiableAt
  have hFdR := hFdC.restrictScalars ℝ
  have hdz : dz f z₀ = dz ((f ∘ Function.invFunOn φ (ball z₀ r)) ∘ φ) z₀ := by
    show (fderiv ℝ f z₀ 1 - I * fderiv ℝ f z₀ I) / 2 =
      (fderiv ℝ ((f ∘ Function.invFunOn φ (ball z₀ r)) ∘ φ) z₀ 1 -
        I * fderiv ℝ ((f ∘ Function.invFunOn φ (ball z₀ r)) ∘ φ) z₀ I) / 2
    rw [heq.fderiv_eq]
  rw [hdz, eq6_2_dz_comp hφd hFdR, (cauchyRiemann_iff.mp hFdC).2, zero_mul, add_zero,
    dz_eq_deriv hFdC, hφ1, mul_one]
  exact deriv_ne_zero_of_injOn hopen hFhol hF.2.2.1.2.1 hmem

/-- **R3.** The normalized plane solution of `extA μ`, `μ` real-analytic, is real-analytic on `𝔻*` and at `∞`. -/
theorem ra_W_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hμa : μ ∈ realAnalyticBeltrami) {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extA μ)) :
    (∀ z ∈ unitDiscExterior, AnalyticAt ℝ W z ∧ dz W z ≠ 0) ∧
      ∃ V : ℂ → ℂ, AnalyticAt ℝ V 0 ∧ dz V 0 ≠ 0 ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → V z = (W z⁻¹)⁻¹ := by
  have _hμ := hμ
  obtain ⟨g, hg, hμg, h, hh, hhg⟩ := hμa
  obtain ⟨⟨K, hK⟩, hs, h0, -, hdil⟩ := hW
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- the dilatation of `W` is `g` a.e. on `𝔻*`
  have hWg : ∀ᵐ ζ, ζ ∈ unitDiscExterior → complexDilatation W ζ = g ζ := by
    have h1 := (ae_restrict_iff' hE.measurableSet).mp hμg
    filter_upwards [hdil, h1] with ζ hζ1 hζ2 hζE
    rw [hζ1, ← hζ2 hζE]
    show (if 1 < ‖ζ‖ then μ ζ else if ‖ζ‖ < 1 then conj (μ (refl ζ)) * ζ ^ 2 / conj ζ ^ 2 else 0) = μ ζ
    rw [if_pos (show 1 < ‖ζ‖ from hζE)]
  refine ⟨ra_qc_analytic (nx_isKQC_restrict hK hE (subset_univ _)) hg
    ((ae_restrict_iff' hE.measurableSet).mpr hWg), ?_⟩
  -- the chart at `∞`
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  obtain ⟨E, hE'⟩ := nxI1_exists_homeo e (by rw [he]; exact h0)
  have hVhom : IsHomeomorphOnto (nxInvConj W) univ univ := by
    rw [← he, ← hE']
    exact nxI1_isHomeomorphOnto_of_homeomorph E
  have hWinj : Function.Injective W := by rw [← he]; exact e.injective
  have hVq0 : IsKQC (nxInvConj W) {0}ᶜ K := by
    have hinvq : IsKQC (fun z : ℂ => z⁻¹) {0}ᶜ 1 :=
      isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
    have h1 : IsKQC (W ∘ fun z : ℂ => z⁻¹) {0}ᶜ (1 * K) := thm7_1_comp hinvq hK (subset_univ _)
    have hsub : (W ∘ fun z : ℂ => z⁻¹) '' {0}ᶜ ⊆ {0}ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ hw
      rw [mem_singleton_iff, Function.comp_apply, ← h0] at hw
      exact hz (inv_eq_zero.mp (hWinj hw))
    have h2 := thm7_1_comp h1 hinvq hsub
    rw [mul_one, one_mul] at h2
    exact h2
  have hVq : IsKQC (nxInvConj W) univ K := b4_isKQC_univ_of_punctured hVhom hVq0
  have hdiffW : ∀ᵐ z, DifferentiableAt ℝ W z := by
    have h1 := thm9_3_differentiable_ae hK
    rwa [Measure.restrict_univ] at h1
  have hVh : ∀ᵐ z, ‖z‖ < 1 → complexDilatation (nxInvConj W) z = h z := by
    have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [nx_ae_inv hdiffW, nx_ae_inv hWg, hne] with z hzd hzg hz0 hz1
    have hzi : z⁻¹ ≠ 0 := inv_ne_zero hz0
    have hfz : W z⁻¹ ≠ 0 := fun hw => hzi (hWinj (hw.trans h0.symm))
    have hzE : z⁻¹ ∈ unitDiscExterior := by
      show 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
    rw [nxI2_dilatation_invConj_at hz0 hfz hzd, hzg hzE, hhg z hz0 hz1]
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.mp hh.eventually_analyticAt
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hVU := nx_isKQC_restrict hVq (isOpen_ball (x := (0 : ℂ)) (ε := min ε 1)) (subset_univ _)
  have hhU : AnalyticOnNhd ℝ h (ball 0 (min ε 1)) := fun z hz =>
    hεb z (ball_subset_ball (min_le_left _ _) hz)
  have hdilU : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) (min ε 1))), complexDilatation (nxInvConj W) z = h z := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hVh] with z hz hzb
    refine hz ?_
    have h1 := mem_ball_zero_iff.mp hzb
    have h2 := min_le_right ε 1
    linarith
  obtain ⟨hVa, hVd⟩ := ra_qc_analytic hVU hhU hdilU 0 (mem_ball_self hε')
  exact ⟨nxInvConj W, hVa, hVd, fun z _ _ => rfl⟩

/-- **S1.** Analytic local right inverse of a real-analytic map with `|∂̄Θ| < |∂Θ|` at `x₀`. -/
theorem ra_local_inverse {Θ : ℂ → ℂ} {x₀ : ℂ} (hΘ : AnalyticAt ℝ Θ x₀) (hlt : ‖dzbar Θ x₀‖ < ‖dz Θ x₀‖) :
    ∃ κ : ℂ → ℂ, AnalyticAt ℝ κ (Θ x₀) ∧ κ (Θ x₀) = x₀ ∧ ∀ᶠ u in 𝓝 (Θ x₀), Θ (κ u) = u := by
  have hd : DifferentiableAt ℝ Θ x₀ := hΘ.differentiableAt
  have hinj : Function.Injective (fderiv ℝ Θ x₀) := by
    intro v w hvw
    have h0 : fderiv ℝ Θ x₀ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    rw [fderiv_eq_dz_dzbar hd] at h0
    by_contra hne
    have h4 : 0 < ‖v - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h5 : dz Θ x₀ * (v - w) = -(dzbar Θ x₀ * conj (v - w)) := by linear_combination h0
    have h6 : ‖dz Θ x₀‖ * ‖v - w‖ = ‖dzbar Θ x₀‖ * ‖v - w‖ := by
      have h7 := congrArg norm h5
      rwa [norm_mul, norm_neg, norm_mul, Complex.norm_conj] at h7
    have h8 := mul_right_cancel₀ h4.ne' h6
    linarith
  let i : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ Θ x₀).toLinearMap hinj).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt Θ (i : ℂ →L[ℝ] ℂ) x₀ := by
    have h := hΘ.hasStrictFDerivAt
    convert h using 1
    exact ContinuousLinearMap.ext fun v => rfl
  set e := hstrict.toOpenPartialHomeomorph Θ with he_def
  have hecoe : (e : ℂ → ℂ) = Θ := hstrict.toOpenPartialHomeomorph_coe
  have hsrc : x₀ ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  have htgt : Θ x₀ ∈ e.target := by rw [← hecoe]; exact e.map_source hsrc
  have hsymm : e.symm (Θ x₀) = x₀ := by
    have h := e.left_inv hsrc
    rwa [hecoe] at h
  refine ⟨e.symm, ?_, hsymm, ?_⟩
  · refine e.analyticAt_symm (i := i) htgt ?_ ?_
    · rw [hsymm, hecoe]; exact hΘ
    · rw [hsymm, hecoe]; exact hstrict.hasFDerivAt.fderiv
  · filter_upwards [e.open_target.mem_nhds htgt] with u hu
    have h := e.right_inv hu
    rwa [hecoe] at h

/-- A real-analytic representative of an element of `L∞(𝔻*)₁` is bounded by `‖μ‖ < 1` on `𝔻*`. -/
theorem ra_rep_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {gμ : ℂ → ℂ}
    (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior) (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ) :
    ∀ x ∈ unitDiscExterior, ‖gμ x‖ ≤ ‖μ‖ := by
  refine ra_le_of_ae_le bc_hEo (fun z hz => (hgμ z hz).continuousAt.continuousWithinAt) ?_
  filter_upwards [LinfStar_ae_norm_le μ, hμg] with z h1 h2
  rw [← h2]
  exact h1

/-- Structure of `w_μ = M ∘ W`, with its finite values and its value at `∞`. -/
theorem ra_wA_form {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ (a b c d : ℂ) (W : ℂ → ℂ), a * d - b * c ≠ 0 ∧ IsNormalizedSolution W (extA μ) ∧
      wA μ = (fun z => mobiusFn a b c d (W z)) ∧
      (∀ z : ℂ, wAS μ (z : ExtPlane) = mobiusExt a b c d (W z : ExtPlane)) ∧
      wAS μ extInf = mobiusExt a b c d extInf := by
  obtain ⟨M, ⟨a, b, c, d, hdet, rfl⟩, W, hW, hfin, hinf, -⟩ := wA_spec hμ
  refine ⟨a, b, c, d, W, hdet, hW, funext fun z => ?_, hfin, hinf⟩
  show finPart (wAS μ (z : ExtPlane)) = _
  rw [hfin z]
  by_cases h : c * W z + d = 0
  · rw [mobiusExt_coe_of_eq_zero h]
    simp [mobiusFn, h, finPart]
  · rw [mobiusExt_coe h]
    rfl

/-- `∂f` and `∂̄f` of a real-analytic map are real-analytic. -/
theorem ra_dz_analytic {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (dz f) x ∧ AnalyticAt ℝ (dzbar f) x := by
  have hd := hf.fderiv
  have h1 : AnalyticAt ℝ (fun z => fderiv ℝ f z 1) x :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).analyticAt _).comp hd
  have hI : AnalyticAt ℝ (fun z => fderiv ℝ f z I) x :=
    ((ContinuousLinearMap.apply ℝ ℂ I).analyticAt _).comp hd
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  refine ⟨?_, ?_⟩
  · show AnalyticAt ℝ (fun z => (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2) x
    exact (h1.sub (analyticAt_const.mul hI)).div analyticAt_const h2
  · show AnalyticAt ℝ (fun z => (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2) x
    exact (h1.add (analyticAt_const.mul hI)).div analyticAt_const h2

/-- Complex conjugation preserves real-analyticity. -/
theorem ra_conj_analytic {F : ℂ → ℂ} {x : ℂ} (hF : AnalyticAt ℝ F x) :
    AnalyticAt ℝ (fun y => conj (F y)) x :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt _).comp hF

/-- Möbius maps are holomorphic off their pole. -/
theorem ra_mobius_analytic {a b c d w : ℂ} (hw : c * w + d ≠ 0) : AnalyticAt ℂ (mobiusFn a b c d) w :=
  ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hw

/-- Chain rule with a holomorphic outer map. -/
theorem ra_dz_comp_holo {g f : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g (f z)) (hf : DifferentiableAt ℝ f z) :
    dz (g ∘ f) z = deriv g (f z) * dz f z ∧ dzbar (g ∘ f) z = deriv g (f z) * dzbar f z := by
  have hgR := hg.restrictScalars ℝ
  have h0 := (cauchyRiemann_iff.mp hg).2
  have h1 := dz_eq_deriv hg
  rw [eq6_2_dz_comp hf hgR, eq6_2_dzbar_comp hf hgR, h0, h1]
  constructor <;> ring

/-- Chain rule with the inversion as inner map. -/
theorem ra_dz_comp_inv {Ψ : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hΨ : DifferentiableAt ℝ Ψ z⁻¹) :
    dz (fun x => Ψ x⁻¹) z = dz Ψ z⁻¹ * (-(z ^ 2)⁻¹) := by
  have hiC : DifferentiableAt ℂ (fun x : ℂ => x⁻¹) z := differentiableAt_inv hz
  have hiR : DifferentiableAt ℝ (fun x : ℂ => x⁻¹) z := hiC.restrictScalars ℝ
  have h := eq6_2_dz_comp (g := Ψ) hiR hΨ
  have h1 : dz (fun x : ℂ => x⁻¹) z = -(z ^ 2)⁻¹ := by rw [dz_eq_deriv hiC, deriv_inv]
  have h2 : dz (fun w : ℂ => conj (w⁻¹)) z = 0 := by
    rw [← (eq6_3 hiR).2, (cauchyRiemann_iff.mp hiC).2, map_zero]
  have h3 : (Ψ ∘ fun x : ℂ => x⁻¹) = fun x => Ψ x⁻¹ := rfl
  rw [h3] at h
  rw [h, h1, h2]
  ring

/-- Pointwise Beltrami equation from the a.e. one, for real-analytic maps and continuous coefficients. -/
theorem ra_pde_of_ae {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ∀ z ∈ U, AnalyticAt ℝ f z ∧ dz f z ≠ 0)
    (hg : ContinuousOn g U) (h : ∀ᵐ z ∂(volume.restrict U), complexDilatation f z = g z) :
    ∀ z ∈ U, dzbar f z = g z * dz f z := by
  have hc : ContinuousOn (fun z => complexDilatation f z - g z) U := by
    intro z hz
    obtain ⟨hfa, hdz⟩ := hf z hz
    obtain ⟨h1, h2⟩ := ra_dz_analytic hfa
    exact ((h2.continuousAt.div h1.continuousAt hdz).sub (hg.continuousAt (hU.mem_nhds hz))).continuousWithinAt
  have h0 := ra_le_of_ae_le hU hc (k := 0) (by
    filter_upwards [h] with z hz
    rw [hz, sub_self, norm_zero])
  intro z hz
  have h4 := norm_le_zero_iff.mp (h0 z hz)
  rw [sub_eq_zero] at h4
  have h3 : dzbar f z / dz f z = g z := h4
  rwa [div_eq_iff (hf z hz).2] at h3

/-- The pointwise Beltrami equation for the normalized solution on `𝔻*`. -/
theorem ra_W_pde {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hμa : μ ∈ realAnalyticBeltrami) {W gμ : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extA μ)) (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior)
    (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ) :
    ∀ x ∈ unitDiscExterior, dzbar W x = gμ x * dz W x := by
  refine ra_pde_of_ae bc_hEo (ra_W_analytic hμ hμa hW).1
    (fun z hz => (hgμ z hz).continuousAt.continuousWithinAt) ?_
  have h1 := (ae_restrict_iff' bc_hEo.measurableSet).mp hμg
  rw [ae_restrict_iff' bc_hEo.measurableSet]
  filter_upwards [hW.2.2.2.2, h1] with ζ hζ1 hζ2 hζE
  rw [hζ1, ← hζ2 hζE]
  show (if 1 < ‖ζ‖ then μ ζ else if ‖ζ‖ < 1 then conj (μ (refl ζ)) * ζ ^ 2 / conj ζ ^ 2 else 0) = μ ζ
  rw [if_pos (show 1 < ‖ζ‖ from hζE)]

/-- Analyticity of the composition-formula integrand. -/
theorem ra_E_analytic {gμ gν w : ℂ → ℂ} {x : ℂ} (h1 : AnalyticAt ℝ gμ x) (h2 : AnalyticAt ℝ gν x)
    (hb1 : ‖gμ x‖ < 1) (hb2 : ‖gν x‖ < 1) (hw : AnalyticAt ℝ w x) (hdz : dz w x ≠ 0) :
    AnalyticAt ℝ (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz w x / conj (dz w x))) x := by
  obtain ⟨hd, -⟩ := ra_dz_analytic hw
  have hden : 1 - conj (gμ x) * gν x ≠ 0 := by
    intro h
    have h3 := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul, Complex.norm_conj] at h3
    nlinarith [norm_nonneg (gμ x), norm_nonneg (gν x)]
  have hc : conj (dz w x) ≠ 0 := (map_ne_zero _).mpr hdz
  exact ((h2.sub h1).div (analyticAt_const.sub ((ra_conj_analytic h1).mul h2)) hden).mul
    (hd.div (ra_conj_analytic hd) hc)

/-- `∂` and `∂̄` only depend on the germ. -/
theorem ra_dz_congr {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) : dz f x = dz g x ∧ dzbar f x = dzbar g x := by
  have e : fderiv ℝ f x = fderiv ℝ g x := h.fderiv_eq
  constructor
  · show (fderiv ℝ f x 1 - I * fderiv ℝ f x I) / 2 = (fderiv ℝ g x 1 - I * fderiv ℝ g x I) / 2
    rw [e]
  · show (fderiv ℝ f x 1 + I * fderiv ℝ f x I) / 2 = (fderiv ℝ g x 1 + I * fderiv ℝ g x I) / 2
    rw [e]

/-- The phase of a product. -/
theorem ra_phase_mul (D P : ℂ) : D * P / conj (D * P) = D / conj D * (P / conj P) := by
  rw [map_mul, mul_div_mul_comm]

/-- Transport of the first factor under the `(-1,1)`-form rule. -/
theorem ra_factor_phase {A B z : ℂ} (hz : z ≠ 0) :
    (B * (conj z ^ 2 / z ^ 2) - A * (conj z ^ 2 / z ^ 2)) /
        (1 - conj (A * (conj z ^ 2 / z ^ 2)) * (B * (conj z ^ 2 / z ^ 2))) =
      (B - A) / (1 - conj A * B) * (conj z ^ 2 / z ^ 2) := by
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
  have e : conj (A * (conj z ^ 2 / z ^ 2)) * (B * (conj z ^ 2 / z ^ 2)) = conj A * B := by
    simp only [map_mul, map_div₀, map_pow, Complex.conj_conj]
    field_simp
  rw [e]
  ring

theorem ra_phase_sq {z : ℂ} (hz : z ≠ 0) : (-z ^ 2) / conj (-z ^ 2) * (conj z ^ 2 / z ^ 2) = 1 := by
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
  rw [map_neg, map_pow, neg_div_neg_eq]
  field_simp

theorem ra_phase_inv_sq {s : ℂ} (hs : s ≠ 0) : (-(s ^ 2)⁻¹) / conj (-(s ^ 2)⁻¹) * (s ^ 2 / conj s ^ 2) = 1 := by
  have hc : conj s ≠ 0 := (map_ne_zero _).mpr hs
  rw [map_neg, map_inv₀, map_pow, neg_div_neg_eq]
  field_simp

/-- `|h(z)| ≤ C` up to `z = 0`, for the `∞`-coefficient of a bounded representative. -/
theorem ra_h_bound {g h : ℂ → ℂ} {C : ℝ} (hgb : ∀ x ∈ unitDiscExterior, ‖g x‖ ≤ C) (hh : AnalyticAt ℝ h 0)
    (hgh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → h z = g z⁻¹ * (z ^ 2 / conj z ^ 2)) : ‖h 0‖ ≤ C := by
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖h z‖ ≤ C := by
    have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
      simpa using hz
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz0 hz1
    have hz0' : z ≠ 0 := hz0
    rw [hgh z hz0' hz1, norm_mul]
    have hph : ‖z ^ 2 / conj z ^ 2‖ = 1 := by
      rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
      exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0'))
    rw [hph, mul_one]
    refine hgb _ ?_
    show 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0')).mpr hz1
  have ht : Tendsto (fun z => ‖h z‖) (𝓝[≠] 0) (𝓝 ‖h 0‖) :=
    (hh.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht hev

/-- The chart of `W` at `∞`. -/
theorem ra_V_facts {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {gμ hμ' W : ℂ → ℂ}
    (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior) (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ)
    (hhμ : AnalyticAt ℝ hμ' 0) (hμh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → hμ' z = gμ z⁻¹ * (z ^ 2 / conj z ^ 2))
    (hW : IsNormalizedSolution W (extA μ)) :
    ∃ V : ℂ → ℂ, AnalyticAt ℝ V 0 ∧ dz V 0 ≠ 0 ∧ V 0 = 0 ∧
      (∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → V z = (W z⁻¹)⁻¹ ∧ V z ≠ 0) ∧ ‖dzbar V 0‖ < ‖dz V 0‖ := by
  have hμa : μ ∈ realAnalyticBeltrami := ⟨gμ, hgμ, hμg, hμ', hhμ, hμh⟩
  obtain ⟨hWa, V, hVa, hVd, hVe⟩ := ra_W_analytic hμ hμa hW
  obtain ⟨K, hK⟩ := hW.1
  have hs := hW.2.1
  have h0 : W 0 = 0 := hW.2.2.1
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  obtain ⟨E, hE'⟩ := nxI1_exists_homeo e (by rw [he]; exact h0)
  have hWinj : Function.Injective W := by rw [← he]; exact e.injective
  have hVne : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → V z ≠ 0 := by
    intro z hz0 hz1
    rw [hVe z hz0 hz1]
    refine inv_ne_zero fun hw => ?_
    exact inv_ne_zero hz0 (hWinj (hw.trans h0.symm))
  -- `V 0 = 0`
  have hV0 : V 0 = 0 := by
    have hE0 : nxInvConj W 0 = 0 := by
      show (W 0⁻¹)⁻¹ = 0
      rw [inv_zero, h0, inv_zero]
    have hEc : ContinuousAt (nxInvConj W) 0 := by rw [← he, ← hE']; exact E.continuous.continuousAt
    have t1 : Tendsto V (𝓝[≠] 0) (𝓝 (V 0)) := hVa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto V (𝓝[≠] 0) (𝓝 0) := by
      have h3 := hEc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      rw [hE0] at h3
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with z hz0 hz1
      exact (hVe z hz0 (mem_ball_zero_iff.mp hz1)).symm
    exact tendsto_nhds_unique t1 t2
  -- the Beltrami equation of `V` at `0`
  have hdzV := (ra_dz_analytic hVa).1
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℝ V z ∧ dz V z ≠ 0 ∧ AnalyticAt ℝ hμ' z ∧ ‖z‖ < 1 := by
    filter_upwards [hVa.eventually_analyticAt, hdzV.continuousAt.eventually_ne hVd,
      hhμ.eventually_analyticAt, Metric.ball_mem_nhds (0 : ℂ) one_pos] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, mem_ball_zero_iff.mp h4⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hWpde := ra_W_pde hμ hμa hW hgμ hμg
  have hpt : ∀ z ∈ ball (0 : ℂ) ε, z ≠ 0 → complexDilatation V z = hμ' z := by
    intro z hz hz0
    obtain ⟨-, -, -, hz1⟩ := hεb z hz
    have hzE : z⁻¹ ∈ unitDiscExterior := by
      show 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
    have hloc : V =ᶠ[𝓝 z] nxInvConj W := by
      have hU : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
      filter_upwards [hU.mem_nhds ⟨mem_ball_zero_iff.mpr hz1, hz0⟩] with y hy
      exact hVe y hy.2 (mem_ball_zero_iff.mp hy.1)
    have hc := ra_dz_congr hloc
    have hWz : W z⁻¹ ≠ 0 := fun hw => inv_ne_zero hz0 (hWinj (hw.trans h0.symm))
    have h1 : complexDilatation V z = complexDilatation (nxInvConj W) z := by
      show dzbar V z / dz V z = dzbar (nxInvConj W) z / dz (nxInvConj W) z
      rw [hc.1, hc.2]
    rw [h1, nxI2_dilatation_invConj_at hz0 hWz (hWa z⁻¹ hzE).1.differentiableAt, hμh z hz0 hz1]
    congr 1
    show dzbar W z⁻¹ / dz W z⁻¹ = gμ z⁻¹
    rw [hWpde z⁻¹ hzE, mul_div_assoc, div_self (hWa z⁻¹ hzE).2, mul_one]
  have hpde := ra_pde_of_ae isOpen_ball (fun z hz => ⟨(hεb z hz).1, (hεb z hz).2.1⟩)
    (fun z hz => (hεb z hz).2.2.1.continuousAt.continuousWithinAt) (f := V) (g := hμ') (by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz0 hz
      exact hpt z hz hz0)
  have hb := ra_h_bound (fun x hx => ra_rep_bound hμ hgμ hμg x hx) hhμ hμh
  have hb1 : ‖hμ' 0‖ < 1 := hb.trans_lt (bc_norm_lt_one hμ)
  refine ⟨V, hVa, hVd, hV0, fun z hz0 hz1 => ⟨hVe z hz0 hz1, hVne z hz0 hz1⟩, ?_⟩
  rw [hpde 0 (mem_ball_self hε), norm_mul]
  have hpos : 0 < ‖dz V 0‖ := norm_pos_iff.mpr hVd
  nlinarith

/-- **S4.** Regular points. -/
theorem ra_rep_regular {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hμa : μ ∈ realAnalyticBeltrami) {gμ gν : ℂ → ℂ}
    (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior) (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ)
    (hgν : AnalyticOnNhd ℝ gν unitDiscExterior) {C : ℝ} (hC : C < 1)
    (hgνb : ∀ x ∈ unitDiscExterior, ‖gν x‖ ≤ C)
    {u₀ : ℂ} (hu₀ : u₀ ∈ unitDiscExterior) (hq : u₀ ≠ finPart (wAS μ extInf)) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℝ Q u₀ ∧ ∀ᶠ u in 𝓝 u₀,
      (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
        (Function.invFun (wA μ) u) = Q u := by
  obtain ⟨a, b, c, d, W, hdet, hW, hw, hfin, -⟩ := ra_wA_form hμ
  have hWa := (ra_W_analytic hμ hμa hW).1
  have hWpde := ra_W_pde hμ hμa hW hgμ hμg
  have hgμb : ∀ x ∈ unitDiscExterior, ‖gμ x‖ < 1 := fun x hx =>
    (ra_rep_bound hμ hgμ hμg x hx).trans_lt (bc_norm_lt_one hμ)
  -- the preimage of `u₀`
  have hpre : ∃ x₀ ∈ unitDiscExterior, wA μ x₀ = u₀ ∧ c * W x₀ + d ≠ 0 := by
    have hyS : (u₀ : ExtPlane) ∈ wAS μ '' (toExt unitDiscExterior ∪ {extInf}) := by
      rw [(wA_mapsTo hμ).2.1]
      exact Or.inl ⟨u₀, hu₀, rfl⟩
    obtain ⟨p, hp, he⟩ := hyS
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · refine ⟨x, hx, ?_, ?_⟩
      · show finPart (wAS μ (x : ExtPlane)) = u₀
        rw [he, finPart_coe]
      · intro h
        rw [hfin x, mobiusExt_coe_of_eq_zero h] at he
        exact OnePoint.coe_ne_infty u₀ he.symm
    · rw [mem_singleton_iff] at hp
      subst hp
      rw [he, finPart_coe] at hq
      exact absurd rfl hq
  obtain ⟨x₀, hx₀, hwx, hpole⟩ := hpre
  have hM := ra_mobius_analytic (a := a) (b := b) hpole
  have hMd : HasDerivAt (mobiusFn a b c d) ((a * d - b * c) / (c * W x₀ + d) ^ 2) (W x₀) :=
    bc_mobiusFn_hasDerivAt hpole
  have hM' : deriv (mobiusFn a b c d) (W x₀) ≠ 0 := by
    rw [hMd.deriv]
    exact div_ne_zero hdet (pow_ne_zero 2 hpole)
  have hwa : AnalyticAt ℝ (wA μ) x₀ := by
    rw [hw]
    exact (hM.restrictScalars (𝕜 := ℝ)).comp (hWa x₀ hx₀).1
  have hdc := ra_dz_comp_holo hM.differentiableAt (hWa x₀ hx₀).1.differentiableAt
  have hdzw : dz (wA μ) x₀ = deriv (mobiusFn a b c d) (W x₀) * dz W x₀ := by rw [hw]; exact hdc.1
  have hdzbw : dzbar (wA μ) x₀ = deriv (mobiusFn a b c d) (W x₀) * (gμ x₀ * dz W x₀) := by
    rw [hw, ← hWpde x₀ hx₀]; exact hdc.2
  have hdz0 : dz (wA μ) x₀ ≠ 0 := by rw [hdzw]; exact mul_ne_zero hM' (hWa x₀ hx₀).2
  have hlt : ‖dzbar (wA μ) x₀‖ < ‖dz (wA μ) x₀‖ := by
    rw [hdzbw, hdzw, norm_mul, norm_mul, norm_mul]
    have hpos : 0 < ‖deriv (mobiusFn a b c d) (W x₀)‖ * ‖dz W x₀‖ :=
      mul_pos (norm_pos_iff.mpr hM') (norm_pos_iff.mpr (hWa x₀ hx₀).2)
    have hg1 := hgμb x₀ hx₀
    nlinarith
  obtain ⟨κ, hκa, hκ0, hκe⟩ := ra_local_inverse hwa hlt
  rw [hwx] at hκa hκ0 hκe
  have hE := ra_E_analytic (hgμ x₀ hx₀) (hgν x₀ hx₀) (hgμb x₀ hx₀) ((hgνb x₀ hx₀).trans_lt hC) hwa hdz0
  refine ⟨(fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x))) ∘ κ,
    hE.comp_of_eq hκa hκ0, ?_⟩
  filter_upwards [hκe, bc_hEo.mem_nhds hu₀] with u hu1 hu2
  have hu0 : wA μ (κ u) ≠ 0 := by
    rw [hu1]
    intro h
    rw [h] at hu2
    exact absurd hu2 (by norm_num [unitDiscExterior])
  have hinv := bc_invFun_wA hu0
  rw [hu1] at hinv
  rw [hinv]
  rfl

/-- **S5.** The point `q = w(∞)`. -/
theorem ra_rep_q {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {gμ gν hμ' hν' : ℂ → ℂ}
    (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior) (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ)
    (hhμ : AnalyticAt ℝ hμ' 0) (hμh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → hμ' z = gμ z⁻¹ * (z ^ 2 / conj z ^ 2))
    (hgν : AnalyticOnNhd ℝ gν unitDiscExterior) {C : ℝ} (hC : C < 1)
    (hgνb : ∀ x ∈ unitDiscExterior, ‖gν x‖ ≤ C)
    (hhν : AnalyticAt ℝ hν' 0) (hνh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → hν' z = gν z⁻¹ * (z ^ 2 / conj z ^ 2))
    (hq : finPart (wAS μ extInf) ∈ unitDiscExterior) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℝ Q (finPart (wAS μ extInf)) ∧ ∀ᶠ u in 𝓝[≠] (finPart (wAS μ extInf)),
      (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
        (Function.invFun (wA μ) u) = Q u := by
  have hμa : μ ∈ realAnalyticBeltrami := ⟨gμ, hgμ, hμg, hμ', hhμ, hμh⟩
  obtain ⟨a, b, c, d, W, hdet, hW, hw, hfin, hinf⟩ := ra_wA_form hμ
  have hc : c ≠ 0 := by
    intro hc0
    have h1 : mobiusExt a b c d extInf = extInf := by simp [mobiusExt, hc0]
    rw [hinf, h1] at hq
    have h2 : finPart extInf = 0 := rfl
    rw [h2] at hq
    exact absurd hq (by norm_num [unitDiscExterior])
  have hqv : finPart (wAS μ extInf) = a / c := by
    rw [hinf]
    simp [mobiusExt, hc, finPart]
  obtain ⟨V, hVa, hVd, hV0, hVe, hVlt⟩ := ra_V_facts hμ hgμ hμg hhμ hμh hW
  have hWinj : ∀ y : ℂ, y ≠ 0 → W y ≠ 0 := by
    obtain ⟨K, hK⟩ := hW.1
    obtain ⟨e, he⟩ := t1_homeomorph hK hW.2.1
    intro y hy hWy
    exact hy (by rw [← he] at hWy; exact e.injective (hWy.trans (by rw [he]; exact hW.2.2.1.symm)))
  -- the chart `Ψ(z) = w(1/z)`
  set Ψ : ℂ → ℂ := fun z => mobiusFn b a d c (V z) with hΨ_def
  have hM0 : d * V 0 + c ≠ 0 := by rw [hV0, mul_zero, zero_add]; exact hc
  have hMa := ra_mobius_analytic (a := b) (b := a) hM0
  have hΨa : AnalyticAt ℝ Ψ 0 := (hMa.restrictScalars (𝕜 := ℝ)).comp hVa
  have hΨ0 : Ψ 0 = a / c := by
    show (b * V 0 + a) / (d * V 0 + c) = a / c
    rw [hV0]
    ring_nf
  have hMd : HasDerivAt (mobiusFn b a d c) ((b * c - a * d) / (d * V 0 + c) ^ 2) (V 0) :=
    bc_mobiusFn_hasDerivAt hM0
  have hM' : deriv (mobiusFn b a d c) (V 0) ≠ 0 := by
    rw [hMd.deriv]
    refine div_ne_zero ?_ (pow_ne_zero 2 hM0)
    intro h
    apply hdet
    linear_combination -h
  have hdc := ra_dz_comp_holo hMa.differentiableAt hVa.differentiableAt
  have e1 : dz Ψ 0 = deriv (mobiusFn b a d c) (V 0) * dz V 0 := hdc.1
  have e2 : dzbar Ψ 0 = deriv (mobiusFn b a d c) (V 0) * dzbar V 0 := hdc.2
  have hlt : ‖dzbar Ψ 0‖ < ‖dz Ψ 0‖ := by
    rw [e1, e2, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hVlt (norm_pos_iff.mpr hM')
  have hdzΨ : dz Ψ 0 ≠ 0 := by rw [e1]; exact mul_ne_zero hM' hVd
  -- `w = Ψ ∘ inv` on `𝔻*`
  have hid : ∀ y ∈ unitDiscExterior, wA μ y = Ψ y⁻¹ := by
    intro y hy
    have hy1 : 1 < ‖y‖ := hy
    have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
    have hz1 : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy1
    obtain ⟨hVy, hVy0⟩ := hVe y⁻¹ (inv_ne_zero hy0) hz1
    rw [inv_inv] at hVy
    have hWy : W y = (V y⁻¹)⁻¹ := by rw [hVy, inv_inv]
    rw [hw]
    show (a * W y + b) / (c * W y + d) = (b * V y⁻¹ + a) / (d * V y⁻¹ + c)
    rw [hWy]
    have hv := hVy0
    have h1 : a * (V y⁻¹)⁻¹ + b = (b * V y⁻¹ + a) * (V y⁻¹)⁻¹ := by
      linear_combination (-b) * mul_inv_cancel₀ hv
    have h2 : c * (V y⁻¹)⁻¹ + d = (d * V y⁻¹ + c) * (V y⁻¹)⁻¹ := by
      linear_combination (-d) * mul_inv_cancel₀ hv
    rw [h1, h2, mul_div_mul_right _ _ (inv_ne_zero hv)]
  obtain ⟨χ, hχa, hχ0, hχe⟩ := ra_local_inverse hΨa hlt
  rw [hΨ0] at hχa hχ0 hχe
  rw [hqv]
  have hbμ : ‖hμ' 0‖ < 1 :=
    (ra_h_bound (fun x hx => ra_rep_bound hμ hgμ hμg x hx) hhμ hμh).trans_lt (bc_norm_lt_one hμ)
  have hbν : ‖hν' 0‖ < 1 := (ra_h_bound hgνb hhν hνh).trans_lt hC
  have hR := ra_E_analytic hhμ hhν hbμ hbν hΨa hdzΨ
  refine ⟨(fun x => (hν' x - hμ' x) / (1 - conj (hμ' x) * hν' x) * (dz Ψ x / conj (dz Ψ x))) ∘ χ,
    hR.comp_of_eq hχa hχ0, ?_⟩
  -- points near `q`
  have hqE : a / c ∈ unitDiscExterior := by rw [← hqv]; exact hq
  have hΨev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℝ Ψ z ∧ ‖z‖ < 1 := by
    filter_upwards [hΨa.eventually_analyticAt, Metric.ball_mem_nhds (0 : ℂ) one_pos] with z h1 h2
    exact ⟨h1, mem_ball_zero_iff.mp h2⟩
  have hχt : ∀ᶠ u in 𝓝 (a / c), AnalyticAt ℝ Ψ (χ u) ∧ ‖χ u‖ < 1 := by
    have := hχa.continuousAt.tendsto
    rw [hχ0] at this
    exact this.eventually hΨev
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hχe, hχt, bc_hEo.mem_nhds hqE] with u hu1 hu2 hu3 hune
  obtain ⟨hΨz, hz1⟩ := hu2
  have hune' : u ≠ a / c := hune
  set z := χ u with hz_def
  have hz0 : z ≠ 0 := by
    intro h
    apply hune'
    rw [← hu1, h, hΨ0]
  set x := z⁻¹ with hx_def
  have hx0 : x ≠ 0 := inv_ne_zero hz0
  have hxE : x ∈ unitDiscExterior := by
    show 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
  have hwx : wA μ x = u := by rw [hid x hxE, hx_def, inv_inv, hu1]
  have hu0 : wA μ x ≠ 0 := by
    rw [hwx]
    intro h
    have h3 : 1 < ‖u‖ := hu3
    rw [h, norm_zero] at h3
    linarith
  have hinv := bc_invFun_wA hu0
  rw [hwx] at hinv
  rw [hinv]
  -- `dz w` at `x`
  have hloc : wA μ =ᶠ[𝓝 x] fun y => Ψ y⁻¹ := by
    filter_upwards [bc_hEo.mem_nhds hxE] with y hy
    exact hid y hy
  have hΨx : DifferentiableAt ℝ Ψ x⁻¹ := by rw [hx_def, inv_inv]; exact hΨz.differentiableAt
  have hdzw : dz (wA μ) x = dz Ψ z * (-z ^ 2) := by
    rw [(ra_dz_congr hloc).1, ra_dz_comp_inv hx0 hΨx, hx_def, inv_inv, inv_pow, inv_inv]
  have hgμx : gμ x = hμ' z * (conj z ^ 2 / z ^ 2) := by
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    rw [hμh z hz0 hz1, hx_def]
    field_simp
  have hgνx : gν x = hν' z * (conj z ^ 2 / z ^ 2) := by
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    rw [hνh z hz0 hz1, hx_def]
    field_simp
  show (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)) =
    (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (dz Ψ z / conj (dz Ψ z))
  rw [hgμx, hgνx, hdzw, ra_factor_phase hz0, ra_phase_mul]
  have hph := ra_phase_sq hz0
  calc (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (conj z ^ 2 / z ^ 2) *
        (dz Ψ z / conj (dz Ψ z) * (-z ^ 2 / conj (-z ^ 2)))
      = (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (dz Ψ z / conj (dz Ψ z)) *
          (-z ^ 2 / conj (-z ^ 2) * (conj z ^ 2 / z ^ 2)) := by ring
    _ = _ := by rw [hph, mul_one]

/-- **S6.** The `∞`-condition of the composite. -/
theorem ra_rep_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {gμ gν hμ' hν' : ℂ → ℂ}
    (hgμ : AnalyticOnNhd ℝ gμ unitDiscExterior) (hμg : (μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] gμ)
    (hhμ : AnalyticAt ℝ hμ' 0) (hμh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → hμ' z = gμ z⁻¹ * (z ^ 2 / conj z ^ 2))
    (hgν : AnalyticOnNhd ℝ gν unitDiscExterior) {C : ℝ} (hC : C < 1)
    (hgνb : ∀ x ∈ unitDiscExterior, ‖gν x‖ ≤ C)
    (hhν : AnalyticAt ℝ hν' 0) (hνh : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → hν' z = gν z⁻¹ * (z ^ 2 / conj z ^ 2)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℝ H 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
        (Function.invFun (wA μ) s⁻¹) * (s ^ 2 / conj s ^ 2) = H s := by
  have hμa : μ ∈ realAnalyticBeltrami := ⟨gμ, hgμ, hμg, hμ', hhμ, hμh⟩
  obtain ⟨a, b, c, d, W, hdet, hW, hw, hfin, -⟩ := ra_wA_form hμ
  have hWa := (ra_W_analytic hμ hμa hW).1
  have hWpde := ra_W_pde hμ hμa hW hgμ hμg
  have hgμb : ∀ x ∈ unitDiscExterior, ‖gμ x‖ < 1 := fun x hx =>
    (ra_rep_bound hμ hgμ hμg x hx).trans_lt (bc_norm_lt_one hμ)
  have hbμ : ‖hμ' 0‖ < 1 :=
    (ra_h_bound (fun x hx => ra_rep_bound hμ hgμ hμg x hx) hhμ hμh).trans_lt (bc_norm_lt_one hμ)
  have hbν : ‖hν' 0‖ < 1 := (ra_h_bound hgνb hhν hνh).trans_lt hC
  by_cases hc : c = 0
  · -- `w(∞) = ∞`: the chart `Θ(z) = 1/w(1/z)`
    have had : a * d ≠ 0 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    have ha : a ≠ 0 := left_ne_zero_of_mul had
    obtain ⟨V, hVa, hVd, hV0, hVe, hVlt⟩ := ra_V_facts hμ hgμ hμg hhμ hμh hW
    set Θ : ℂ → ℂ := fun z => mobiusFn d 0 b a (V z) with hΘ_def
    have hM0 : b * V 0 + a ≠ 0 := by rw [hV0, mul_zero, zero_add]; exact ha
    have hMa := ra_mobius_analytic (a := d) (b := 0) hM0
    have hΘa : AnalyticAt ℝ Θ 0 := (hMa.restrictScalars (𝕜 := ℝ)).comp hVa
    have hΘ0 : Θ 0 = 0 := by
      show (d * V 0 + 0) / (b * V 0 + a) = 0
      rw [hV0, mul_zero, add_zero, zero_div]
    have hMd : HasDerivAt (mobiusFn d 0 b a) ((d * a - 0 * b) / (b * V 0 + a) ^ 2) (V 0) :=
      bc_mobiusFn_hasDerivAt hM0
    have hM' : deriv (mobiusFn d 0 b a) (V 0) ≠ 0 := by
      rw [hMd.deriv, zero_mul, sub_zero]
      exact div_ne_zero (by rw [mul_comm]; exact had) (pow_ne_zero 2 hM0)
    have hdc := ra_dz_comp_holo hMa.differentiableAt hVa.differentiableAt
    have e1 : dz Θ 0 = deriv (mobiusFn d 0 b a) (V 0) * dz V 0 := hdc.1
    have e2 : dzbar Θ 0 = deriv (mobiusFn d 0 b a) (V 0) * dzbar V 0 := hdc.2
    have hlt : ‖dzbar Θ 0‖ < ‖dz Θ 0‖ := by
      rw [e1, e2, norm_mul, norm_mul]
      exact mul_lt_mul_of_pos_left hVlt (norm_pos_iff.mpr hM')
    have hdzΘ : dz Θ 0 ≠ 0 := by rw [e1]; exact mul_ne_zero hM' hVd
    have hid : ∀ y ∈ unitDiscExterior, wA μ y = (Θ y⁻¹)⁻¹ := by
      intro y hy
      have hy1 : 1 < ‖y‖ := hy
      have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
      have hz1 : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy1
      obtain ⟨hVy, hv⟩ := hVe y⁻¹ (inv_ne_zero hy0) hz1
      rw [inv_inv] at hVy
      have hWy : W y = (V y⁻¹)⁻¹ := by rw [hVy, inv_inv]
      rw [hw]
      show (a * W y + b) / (c * W y + d) = ((d * V y⁻¹ + 0) / (b * V y⁻¹ + a))⁻¹
      rw [hWy, inv_div, hc]
      have h1 : a * (V y⁻¹)⁻¹ + b = (b * V y⁻¹ + a) * (V y⁻¹)⁻¹ := by
        linear_combination (-b) * mul_inv_cancel₀ hv
      have h2 : 0 * (V y⁻¹)⁻¹ + d = (d * V y⁻¹ + 0) * (V y⁻¹)⁻¹ := by
        linear_combination (-d) * mul_inv_cancel₀ hv
      rw [h1, h2, mul_div_mul_right _ _ (inv_ne_zero hv)]
    obtain ⟨κ, hκa, hκ0, hκe⟩ := ra_local_inverse hΘa hlt
    rw [hΘ0] at hκa hκ0 hκe
    have hR := ra_E_analytic hhμ hhν hbμ hbν hΘa hdzΘ
    refine ⟨(fun x => (hν' x - hμ' x) / (1 - conj (hμ' x) * hν' x) * (dz Θ x / conj (dz Θ x))) ∘ κ,
      hR.comp_of_eq hκa hκ0, ?_⟩
    have hΘev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℝ Θ z ∧ ‖z‖ < 1 := by
      filter_upwards [hΘa.eventually_analyticAt, Metric.ball_mem_nhds (0 : ℂ) one_pos] with z h1 h2
      exact ⟨h1, mem_ball_zero_iff.mp h2⟩
    have hκt : ∀ᶠ s in 𝓝 (0 : ℂ), AnalyticAt ℝ Θ (κ s) ∧ ‖κ s‖ < 1 := by
      have h3 := hκa.continuousAt.tendsto
      rw [hκ0] at h3
      exact h3.eventually hΘev
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hκe, hκt] with s hs1 hs2 hs0
    obtain ⟨hΘz, hz1⟩ := hs2
    have hs0' : s ≠ 0 := hs0
    set z := κ s with hz_def
    have hz0 : z ≠ 0 := by
      intro h
      apply hs0'
      rw [← hs1, h, hΘ0]
    set x := z⁻¹ with hx_def
    have hx0 : x ≠ 0 := inv_ne_zero hz0
    have hxE : x ∈ unitDiscExterior := by
      show 1 < ‖z⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz1
    have hwx : wA μ x = s⁻¹ := by rw [hid x hxE, hx_def, inv_inv, hs1]
    have hinv := bc_invFun_wA (μ := μ) (x := x) (by rw [hwx]; exact inv_ne_zero hs0')
    rw [hwx] at hinv
    rw [hinv]
    have hloc : wA μ =ᶠ[𝓝 x] fun y => (fun w => (Θ w)⁻¹) y⁻¹ := by
      filter_upwards [bc_hEo.mem_nhds hxE] with y hy
      exact hid y hy
    have hiC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (Θ z) := differentiableAt_inv (by rw [hs1]; exact hs0')
    have hdΞ := (ra_dz_comp_holo hiC hΘz.differentiableAt).1
    have hΞ : DifferentiableAt ℝ (fun w => (Θ w)⁻¹) x⁻¹ := by
      rw [hx_def, inv_inv]
      exact (hiC.restrictScalars ℝ).comp z hΘz.differentiableAt
    have hdzw : dz (wA μ) x = (-(s ^ 2)⁻¹ * dz Θ z) * (-z ^ 2) := by
      rw [(ra_dz_congr hloc).1, ra_dz_comp_inv hx0 hΞ, hx_def, inv_inv, inv_pow, inv_inv]
      have h4 : dz (fun w => (Θ w)⁻¹) z = deriv (fun w : ℂ => w⁻¹) (Θ z) * dz Θ z := hdΞ
      rw [h4, deriv_inv, hs1]
    have hgμx : gμ x = hμ' z * (conj z ^ 2 / z ^ 2) := by
      have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
      rw [hμh z hz0 hz1, hx_def]
      field_simp
    have hgνx : gν x = hν' z * (conj z ^ 2 / z ^ 2) := by
      have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
      rw [hνh z hz0 hz1, hx_def]
      field_simp
    show (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)) * (s ^ 2 / conj s ^ 2) =
      (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (dz Θ z / conj (dz Θ z))
    rw [hgμx, hgνx, hdzw, ra_factor_phase hz0, ra_phase_mul, ra_phase_mul]
    have hp1 := ra_phase_sq hz0
    have hp2 := ra_phase_inv_sq hs0'
    calc (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (conj z ^ 2 / z ^ 2) *
          (-(s ^ 2)⁻¹ / conj (-(s ^ 2)⁻¹) * (dz Θ z / conj (dz Θ z)) * (-z ^ 2 / conj (-z ^ 2))) *
          (s ^ 2 / conj s ^ 2)
        = (hν' z - hμ' z) / (1 - conj (hμ' z) * hν' z) * (dz Θ z / conj (dz Θ z)) *
            ((-z ^ 2 / conj (-z ^ 2) * (conj z ^ 2 / z ^ 2)) *
              (-(s ^ 2)⁻¹ / conj (-(s ^ 2)⁻¹) * (s ^ 2 / conj s ^ 2))) := by ring
      _ = _ := by rw [hp1, hp2, mul_one, mul_one]
  · -- the pole `p₀` of `w` lies in `𝔻*`: the chart `Θ = 1/w`
    have hmem : (-d / c) ∈ W '' univ := by rw [hW.2.1]; exact mem_univ _
    obtain ⟨p₀, -, hp₀⟩ := hmem
    have hpole : c * W p₀ + d = 0 := by rw [hp₀]; field_simp; ring
    have hinfp : wAS μ (p₀ : ExtPlane) = extInf := by rw [hfin p₀, mobiusExt_coe_of_eq_zero hpole]
    have hp₀E : p₀ ∈ unitDiscExterior := by
      rcases lt_trichotomy ‖p₀‖ 1 with h | h | h
      · exfalso
        have hm : wAS μ (p₀ : ExtPlane) ∈ toExt unitDisc := by
          rw [← (wA_mapsTo hμ).1]
          exact ⟨(p₀ : ExtPlane), ⟨p₀, mem_ball_zero_iff.mpr h, rfl⟩, rfl⟩
        rw [hinfp] at hm
        obtain ⟨w, -, hw'⟩ := hm
        exact OnePoint.coe_ne_infty w hw'
      · exfalso
        have hm : wAS μ (p₀ : ExtPlane) ∈ toExt unitCircle := by
          rw [← (wA_mapsTo hμ).2.2]
          exact ⟨(p₀ : ExtPlane), ⟨p₀, h, rfl⟩, rfl⟩
        rw [hinfp] at hm
        obtain ⟨w, -, hw'⟩ := hm
        exact OnePoint.coe_ne_infty w hw'
      · exact h
    have hb0 : a * W p₀ + b ≠ 0 := by
      intro h
      apply hdet
      have h5 : W p₀ = -d / c := hp₀
      rw [h5] at h
      field_simp at h
      linear_combination -h
    set Θ : ℂ → ℂ := fun x => mobiusFn c d a b (W x) with hΘ_def
    have hMa := ra_mobius_analytic (a := c) (b := d) hb0
    have hΘa : AnalyticAt ℝ Θ p₀ := (hMa.restrictScalars (𝕜 := ℝ)).comp (hWa p₀ hp₀E).1
    have hΘ0 : Θ p₀ = 0 := by
      show (c * W p₀ + d) / (a * W p₀ + b) = 0
      rw [hpole, zero_div]
    have hwΘ : wA μ = fun x => (Θ x)⁻¹ := by
      rw [hw]
      funext x
      show (a * W x + b) / (c * W x + d) = ((c * W x + d) / (a * W x + b))⁻¹
      rw [inv_div]
    have hMd : HasDerivAt (mobiusFn c d a b) ((c * b - d * a) / (a * W p₀ + b) ^ 2) (W p₀) :=
      bc_mobiusFn_hasDerivAt hb0
    have hM' : deriv (mobiusFn c d a b) (W p₀) ≠ 0 := by
      rw [hMd.deriv]
      refine div_ne_zero ?_ (pow_ne_zero 2 hb0)
      intro h
      apply hdet
      linear_combination -h
    have hdc := ra_dz_comp_holo hMa.differentiableAt (hWa p₀ hp₀E).1.differentiableAt
    have e1 : dz Θ p₀ = deriv (mobiusFn c d a b) (W p₀) * dz W p₀ := hdc.1
    have e2 : dzbar Θ p₀ = deriv (mobiusFn c d a b) (W p₀) * (gμ p₀ * dz W p₀) := by
      rw [← hWpde p₀ hp₀E]; exact hdc.2
    have hdzΘ : dz Θ p₀ ≠ 0 := by rw [e1]; exact mul_ne_zero hM' (hWa p₀ hp₀E).2
    have hlt : ‖dzbar Θ p₀‖ < ‖dz Θ p₀‖ := by
      rw [e2, e1, norm_mul, norm_mul, norm_mul]
      have hpos : 0 < ‖deriv (mobiusFn c d a b) (W p₀)‖ * ‖dz W p₀‖ :=
        mul_pos (norm_pos_iff.mpr hM') (norm_pos_iff.mpr (hWa p₀ hp₀E).2)
      have hg1 := hgμb p₀ hp₀E
      nlinarith
    obtain ⟨κ, hκa, hκ0, hκe⟩ := ra_local_inverse hΘa hlt
    rw [hΘ0] at hκa hκ0 hκe
    have hS := ra_E_analytic (hgμ p₀ hp₀E) (hgν p₀ hp₀E) (hgμb p₀ hp₀E) ((hgνb p₀ hp₀E).trans_lt hC) hΘa hdzΘ
    refine ⟨(fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz Θ x / conj (dz Θ x))) ∘ κ,
      hS.comp_of_eq hκa hκ0, ?_⟩
    have hΘev : ∀ᶠ x in 𝓝 p₀, AnalyticAt ℝ Θ x ∧ x ∈ unitDiscExterior := by
      filter_upwards [hΘa.eventually_analyticAt, bc_hEo.mem_nhds hp₀E] with x h1 h2
      exact ⟨h1, h2⟩
    have hκt : ∀ᶠ s in 𝓝 (0 : ℂ), AnalyticAt ℝ Θ (κ s) ∧ κ s ∈ unitDiscExterior := by
      have h3 := hκa.continuousAt.tendsto
      rw [hκ0] at h3
      exact h3.eventually hΘev
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hκe, hκt] with s hs1 hs2 hs0
    obtain ⟨hΘx, -⟩ := hs2
    have hs0' : s ≠ 0 := hs0
    set x := κ s with hx_def
    have hwx : wA μ x = s⁻¹ := by rw [hwΘ]; show (Θ x)⁻¹ = s⁻¹; rw [hs1]
    have hinv := bc_invFun_wA (μ := μ) (x := x) (by rw [hwx]; exact inv_ne_zero hs0')
    rw [hwx] at hinv
    rw [hinv]
    have hiC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) (Θ x) := differentiableAt_inv (by rw [hs1]; exact hs0')
    have hdzw : dz (wA μ) x = -(s ^ 2)⁻¹ * dz Θ x := by
      have h4 : dz (wA μ) x = deriv (fun w : ℂ => w⁻¹) (Θ x) * dz Θ x := by
        rw [hwΘ]; exact (ra_dz_comp_holo hiC hΘx.differentiableAt).1
      rw [h4, deriv_inv, hs1]
    show (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)) * (s ^ 2 / conj s ^ 2) =
      (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz Θ x / conj (dz Θ x))
    rw [hdzw, ra_phase_mul]
    have hp2 := ra_phase_inv_sq hs0'
    calc (gν x - gμ x) / (1 - conj (gμ x) * gν x) *
          (-(s ^ 2)⁻¹ / conj (-(s ^ 2)⁻¹) * (dz Θ x / conj (dz Θ x))) * (s ^ 2 / conj s ^ 2)
        = (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz Θ x / conj (dz Θ x)) *
            (-(s ^ 2)⁻¹ / conj (-(s ^ 2)⁻¹) * (s ^ 2 / conj s ^ 2)) := by ring
      _ = _ := by rw [hp2, mul_one]

/-- **R4.** The composition formula for `ν * μ⁻¹` has a real-analytic representative (with the `∞`-condition). -/
theorem ra_formula_rep {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hμa : μ ∈ realAnalyticBeltrami) (hνa : ν ∈ realAnalyticBeltrami) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℝ G unitDiscExterior ∧
      (∀ᵐ u ∂(volume.restrict unitDiscExterior),
        (fun x => (ν x - μ x) / (1 - conj (μ x) * ν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
          (Function.invFun (wA μ) u) = G u) ∧
      ∃ h : ℂ → ℂ, AnalyticAt ℝ h 0 ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → h z = G z⁻¹ * (z ^ 2 / conj z ^ 2) := by
  have hμa' := hμa
  obtain ⟨gμ, hgμ, hμg, hμ', hhμ, hμh⟩ := hμa
  obtain ⟨gν, hgν, hνg, hν', hhν, hνh⟩ := hνa
  have hgνb : ∀ x ∈ unitDiscExterior, ‖gν x‖ ≤ ‖ν‖ := ra_rep_bound hν hgν hνg
  have hC := bc_norm_lt_one hν
  have key : ∃ G : ℂ → ℂ, AnalyticOnNhd ℝ G unitDiscExterior ∧ ∀ u ∈ unitDiscExterior,
      u ≠ finPart (wAS μ extInf) → G u =
        (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
          (Function.invFun (wA μ) u) := by
    by_cases hq : finPart (wAS μ extInf) ∈ unitDiscExterior
    · obtain ⟨Q, hQ, hQe⟩ := ra_rep_q hμ hgμ hμg hhμ hμh hgν hC hgνb hhν hνh hq
      refine ⟨Function.update (fun u =>
          (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
            (Function.invFun (wA μ) u)) (finPart (wAS μ extInf)) (Q (finPart (wAS μ extInf))),
        fun u hu => ?_, fun u _ huq => by rw [Function.update_of_ne huq]⟩
      by_cases huq : u = finPart (wAS μ extInf)
      · subst huq
        refine hQ.congr ?_
        have h := eventually_nhdsWithin_iff.mp hQe
        filter_upwards [h] with v hv
        by_cases hvq : v = finPart (wAS μ extInf)
        · rw [hvq, Function.update_self]
        · rw [Function.update_of_ne hvq]
          exact (hv hvq).symm
      · obtain ⟨Q', hQ', hQ'e⟩ := ra_rep_regular hμ hμa' hgμ hμg hgν hC hgνb hu huq
        refine hQ'.congr ?_
        filter_upwards [hQ'e, isOpen_compl_singleton.mem_nhds huq] with v hv hvq
        rw [Function.update_of_ne hvq]
        exact hv.symm
    · refine ⟨fun u =>
          (fun x => (gν x - gμ x) / (1 - conj (gμ x) * gν x) * (dz (wA μ) x / conj (dz (wA μ) x)))
            (Function.invFun (wA μ) u), fun u hu => ?_, fun u _ _ => rfl⟩
      obtain ⟨Q', hQ', hQ'e⟩ := ra_rep_regular hμ hμa' hgμ hμg hgν hC hgνb hu (fun h => hq (h ▸ hu))
      exact hQ'.congr (hQ'e.mono fun v hv => hv.symm)
  obtain ⟨G, hG, hGE⟩ := key
  refine ⟨G, hG, ?_, ?_⟩
  · have h1 := bc_invFun_pullback_ae hμ (P := fun x => μ x = gμ x) hμg
    have h2 := bc_invFun_pullback_ae hμ (P := fun x => ν x = gν x) hνg
    have hq0 : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ≠ finPart (wAS μ extInf) :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton _))
    filter_upwards [h1, h2, hq0, ae_restrict_mem bc_hEo.measurableSet] with u hu1 hu2 hu3 hu4
    rw [hGE u hu4 hu3]
    simp only [hu1, hu2]
  · obtain ⟨H, hH, hHe⟩ := ra_rep_infty hμ hgμ hμg hhμ hμh hgν hC hgνb hhν hνh
    refine ⟨fun s => if s = 0 then H 0 else G s⁻¹ * (s ^ 2 / conj s ^ 2), hH.congr ?_,
      fun z hz _ => by simp only [hz, if_false]⟩
    set q := finPart (wAS μ extInf)
    have hR : (0 : ℝ) < 1 / (‖q‖ + 1) := by positivity
    have h := eventually_nhdsWithin_iff.mp hHe
    filter_upwards [h, Metric.ball_mem_nhds (0 : ℂ) hR] with s hs hsb
    by_cases hs0 : s = 0
    · simp only [hs0, if_true]
    · simp only [hs0, if_false]
      have hsn : ‖s‖ < 1 / (‖q‖ + 1) := mem_ball_zero_iff.mp hsb
      have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
      have hinv : ‖q‖ + 1 < ‖s⁻¹‖ := by
        rw [norm_inv, lt_inv_comm₀ (by positivity) hspos]
        rwa [one_div] at hsn
      have hE : s⁻¹ ∈ unitDiscExterior := by
        show 1 < ‖s⁻¹‖
        linarith [norm_nonneg q]
      have hne : s⁻¹ ≠ q := by
        intro he
        rw [he] at hinv
        linarith
      rw [hGE _ hE hne]
      exact (hs hs0).symm

/-- **R5.** Ahlfors–Weill differentials are real-analytic. -/
theorem ra_Lambda_mem (φ : AInf unitDisc) : Lambda φ ∈ realAnalyticBeltrami := by
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDisc := φ.2
  have hφa : ∀ w ∈ unitDisc, AnalyticAt ℝ (AInf.toFun φ) w := fun w hw =>
    (hφd.analyticAt (isOpen_ball.mem_nhds hw)).restrictScalars
  have hnsq : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hn_an : ∀ z : ℂ, AnalyticAt ℝ (fun z : ℂ => ((‖z‖ : ℂ)) ^ 2) z := fun z => by
    have h : (fun z : ℂ => ((‖z‖ : ℂ)) ^ 2) = fun z => z * conj z := funext hnsq
    rw [h]
    exact analyticAt_id.mul (ra_conj_analytic analyticAt_id)
  refine ⟨fun z => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (refl z) / conj z ^ 4, ?_, Lambda_coe_ae φ,
    fun z => -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (conj z), ?_, ?_⟩
  · intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; linarith
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    have hrefl : AnalyticAt ℝ refl z := by
      have h1 : AnalyticAt ℝ (fun w : ℂ => w⁻¹) (conj z) := (analyticAt_inv (𝕜 := ℂ) hc0).restrictScalars
      exact h1.comp (ra_conj_analytic analyticAt_id)
    have hreflD : refl z ∈ unitDisc := by
      show refl z ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_refl]
      exact inv_lt_one_of_one_lt₀ hz1
    exact ((analyticAt_const.mul ((analyticAt_const.sub (hn_an z)).pow 2)).mul
      ((hφa _ hreflD).comp hrefl)).div ((ra_conj_analytic analyticAt_id).pow 4) (pow_ne_zero 4 hc0)
  · have h0D : conj (0 : ℂ) ∈ unitDisc := by rw [map_zero]; exact mem_ball_self one_pos
    exact (analyticAt_const.mul ((analyticAt_const.sub (hn_an 0)).pow 2)).mul
      ((hφa _ h0D).comp (ra_conj_analytic analyticAt_id))
  · intro z hz0 _
    have hc0 : conj z ≠ 0 := (map_ne_zero _).mpr hz0
    have hr : refl z⁻¹ = conj z := by
      show (conj z⁻¹)⁻¹ = conj z
      rw [map_inv₀, inv_inv]
    show -(1 / 2 : ℂ) * (1 - ‖z‖ ^ 2) ^ 2 * AInf.toFun φ (conj z) =
      -(1 / 2 : ℂ) * (1 - ‖z⁻¹‖ ^ 2) ^ 2 * AInf.toFun φ (refl z⁻¹) / conj z⁻¹ ^ 4 * (z ^ 2 / conj z ^ 2)
    rw [hr, norm_inv]
    push_cast
    rw [inv_pow, hnsq z, map_inv₀]
    field_simp
    ring

/-- **R6.** Real-analytic Beltrami differentials are closed under `beltramiMul`. -/
theorem ra_mul_mem {ν μ : LinfStar} (hν : ν ∈ LinfStarBall) (hμ : μ ∈ LinfStarBall)
    (hνa : ν ∈ realAnalyticBeltrami) (hμa : μ ∈ realAnalyticBeltrami) :
    beltramiMul ν μ ∈ realAnalyticBeltrami := by
  have hsub : ∀ {a b : LinfStar}, a ∈ LinfStarBall → b ∈ LinfStarBall → a ∈ realAnalyticBeltrami →
      b ∈ realAnalyticBeltrami → beltramiMul b (beltramiInv a) ∈ realAnalyticBeltrami := by
    intro a b ha hb haa hba
    obtain ⟨G, hG, hae, hinf⟩ := ra_formula_rep ha hb haa hba
    refine ⟨G, hG, ?_, hinf⟩
    filter_upwards [bc_beltramiMul_inv_formula ha hb, hae] with u h1 h2
    exact h1.trans h2
  have h0 : (0 : LinfStar) ∈ realAnalyticBeltrami :=
    ⟨0, analyticOnNhd_const, Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior), 0, analyticAt_const,
      fun _ _ _ => by simp⟩
  have h00 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hinv : beltramiInv μ ∈ realAnalyticBeltrami := by
    have h1 := hsub hμ h00 hμa h0
    rwa [grp_zero_mul (grp_inv_mem hμ)] at h1
  have h2 := hsub (grp_inv_mem hμ) hν hinv hνa
  rwa [grp_inv_inv hμ] at h2

/-- Norm bound for `a * b⁻¹`. -/
theorem ra_mul_inv_norm_le {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall) :
    ‖beltramiMul a (beltramiInv b)‖ ≤ ‖a - b‖ / (1 - ‖a‖ * ‖b‖) := by
  have hna := bc_norm_lt_one ha
  have hnb := bc_norm_lt_one hb
  have hden : 0 < 1 - ‖a‖ * ‖b‖ := by nlinarith [norm_nonneg a, norm_nonneg b]
  refine bc_Lp_norm_le _ (div_nonneg (norm_nonneg _) hden.le) ?_
  have hf := bc_beltramiMul_inv_formula hb ha
  have hP := bc_invFun_pullback_ae hb
    (P := fun x => ‖a x‖ ≤ ‖a‖ ∧ ‖b x‖ ≤ ‖b‖ ∧ ‖(a - b : LinfStar) x‖ ≤ ‖a - b‖ ∧
      (a - b : LinfStar) x = a x - b x) (by
      filter_upwards [LinfStar_ae_norm_le a, LinfStar_ae_norm_le b, LinfStar_ae_norm_le (a - b),
        Lp.coeFn_sub a b] with x h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩)
  filter_upwards [hf, hP] with z hz hQ
  obtain ⟨h1, h2, h3, h4⟩ := hQ
  rw [hz]
  set x := Function.invFun (wA b) z
  show ‖(a x - b x) / (1 - conj (b x) * a x) * (dz (wA b) x / conj (dz (wA b) x))‖ ≤ ‖a - b‖ / (1 - ‖a‖ * ‖b‖)
  have hph : ‖dz (wA b) x / conj (dz (wA b) x)‖ ≤ 1 := by
    by_cases hd : dz (wA b) x = 0
    · rw [hd, map_zero, div_zero, norm_zero]; norm_num
    · rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd)]
  have hnum : ‖a x - b x‖ ≤ ‖a - b‖ := by rw [← h4]; exact h3
  have hd1 : 1 - ‖a‖ * ‖b‖ ≤ ‖1 - conj (b x) * a x‖ := by
    have h5 := norm_sub_norm_le (1 : ℂ) (conj (b x) * a x)
    rw [norm_one, norm_mul, Complex.norm_conj] at h5
    have h6 : ‖b x‖ * ‖a x‖ ≤ ‖a‖ * ‖b‖ := by
      rw [mul_comm]; exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    linarith
  rw [norm_mul, norm_div]
  calc ‖a x - b x‖ / ‖1 - conj (b x) * a x‖ * ‖dz (wA b) x / conj (dz (wA b) x)‖
      ≤ ‖a x - b x‖ / ‖1 - conj (b x) * a x‖ * 1 := by gcongr
    _ ≤ ‖a - b‖ / (1 - ‖a‖ * ‖b‖) := by
        rw [mul_one]
        exact div_le_div₀ (norm_nonneg _) hnum hden hd1

/-- **R7.** Every point of `T(1)` is reached from the origin by finitely many Bers-chart steps, each step taken in
the chart of an arbitrary representative of the previous point. -/
theorem ra_path_cover (p : T1) :
    ∃ N : ℕ, ∃ q : ℕ → T1, q 0 = originT ∧ q N = p ∧
      ∀ k < N, ∀ ν : LinfStarBall, Phi ν = q k → ∃ φ : AInf unitDisc, ‖φ‖ < 2 ∧ bersChartInv ν φ = q (k + 1) := by
  set μ₀ : LinfStarBall := Quotient.out p with hμ₀
  have hm : ‖(μ₀ : LinfStar)‖ < 1 := bc_norm_lt_one μ₀.2
  set m := ‖(μ₀ : LinfStar)‖ with hm_def
  have hm0 : 0 ≤ m := norm_nonneg _
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (7 * m / (2 * (1 - m ^ 2)) + 1)
  have hN0 : (1 : ℝ) < N := by
    have : 0 ≤ 7 * m / (2 * (1 - m ^ 2)) := by positivity
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  set t : ℕ → ℝ := fun k => ((min k N : ℕ) : ℝ) / N with ht_def
  have ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [ht_def, div_le_one hNpos]
    exact_mod_cast min_le_right k N
  set lam : ℕ → LinfStar := fun k => ((t k : ℝ) : ℂ) • (μ₀ : LinfStar) with hlam_def
  have hnlam : ∀ k, ‖lam k‖ = t k * m := by
    intro k
    rw [hlam_def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht k).1]
  have hlamb : ∀ k, lam k ∈ LinfStarBall := by
    intro k
    show lam k ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, hnlam]
    calc t k * m ≤ 1 * m := mul_le_mul_of_nonneg_right (ht k).2 hm0
      _ < 1 := by linarith
  refine ⟨N, fun k => Phi ⟨lam k, hlamb k⟩, ?_, ?_, fun k hk ν hν => ?_⟩
  · show Phi ⟨lam 0, hlamb 0⟩ = Phi ⟨0, mem_ball_self one_pos⟩
    congr 1
    apply Subtype.ext
    show ((t 0 : ℝ) : ℂ) • (μ₀ : LinfStar) = 0
    simp [ht_def]
  · show Phi ⟨lam N, hlamb N⟩ = p
    have hN' : lam N = (μ₀ : LinfStar) := by
      show ((t N : ℝ) : ℂ) • (μ₀ : LinfStar) = μ₀
      have : t N = 1 := by
        rw [ht_def]
        simp only [min_self]
        exact div_self hNpos.ne'
      rw [this]
      simp
    have he : (⟨lam N, hlamb N⟩ : LinfStarBall) = μ₀ := Subtype.ext hN'
    rw [he, hμ₀]
    exact Quotient.out_eq p
  · set a := lam (k + 1) with ha_def
    set b := lam k with hb_def
    have ha := hlamb (k + 1)
    have hb := hlamb k
    have hρ : beltramiMul a (beltramiInv b) ∈ LinfStarBall := bg_mul_mem_ball (grp_inv_mem hb) ha
    -- the step is small
    have htk : t (k + 1) - t k = 1 / N := by
      rw [ht_def]
      simp only
      rw [min_eq_left (by omega : k + 1 ≤ N), min_eq_left hk.le]
      push_cast
      field_simp
      ring
    have hab : ‖a - b‖ = m / N := by
      rw [ha_def, hb_def, hlam_def]
      simp only
      rw [← sub_smul, norm_smul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, htk,
        abs_of_nonneg (by positivity)]
      ring
    have hprod : ‖a‖ * ‖b‖ ≤ m ^ 2 := by
      rw [hnlam, hnlam]
      have h1 := ht (k + 1)
      have h2 := ht k
      calc t (k + 1) * m * (t k * m) = (t (k + 1) * t k) * m ^ 2 := by ring
        _ ≤ 1 * m ^ 2 := by
            gcongr
            calc t (k + 1) * t k ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
              _ = 1 := one_mul 1
        _ = m ^ 2 := one_mul _
    have hρn : ‖beltramiMul a (beltramiInv b)‖ ≤ m / N / (1 - m ^ 2) := by
      refine (ra_mul_inv_norm_le ha hb).trans ?_
      rw [hab]
      exact div_le_div_of_nonneg_left (by positivity) hm2 (by linarith)
    set φ := bersPhi (beltramiMul a (beltramiInv b)) with hφ_def
    have hφn : ‖φ‖ < 2 := by
      refine (Ch2.bpa_bersPhi_le hρ).trans_lt ?_
      have h1 : 7 * (m / N / (1 - m ^ 2)) < 2 := by
        rw [show 7 * (m / N / (1 - m ^ 2)) = 7 * m / (1 - m ^ 2) / N by ring, div_lt_iff₀ hNpos]
        have h2 : 7 * m / (2 * (1 - m ^ 2)) < N := by linarith
        rw [div_lt_iff₀ (by positivity)] at h2
        rw [div_lt_iff₀ hm2]
        nlinarith
      calc 7 * ‖beltramiMul a (beltramiInv b)‖ ≤ 7 * (m / N / (1 - m ^ 2)) := by gcongr
        _ < 2 := h1
    refine ⟨φ, hφn, ?_⟩
    obtain ⟨hΛ, hbers⟩ := ahlfors_weill hφn
    have hcls : Phi ⟨Lambda φ, hΛ⟩ = Phi ⟨_, hρ⟩ := by
      apply bers_injective
      rw [hbers, bers_Phi]
    have hrel : teichSetoid ⟨Lambda φ, hΛ⟩ ⟨_, hρ⟩ := Quotient.exact hcls
    have hνb : teichSetoid ν ⟨b, hb⟩ := Quotient.exact hν
    have hm1 : beltramiMul (Lambda φ) (ν : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball ν.2 hΛ
    have hm2' : beltramiMul (beltramiMul a (beltramiInv b)) b ∈ LinfStarBall := bg_mul_mem_ball hb hρ
    show (if h : beltramiMul (Lambda φ) (ν : LinfStar) ∈ LinfStarBall then Phi ⟨_, h⟩ else Phi ν) =
      Phi ⟨a, ha⟩
    rw [dif_pos hm1]
    have hstep : Phi ⟨beltramiMul (Lambda φ) (ν : LinfStar), hm1⟩ =
        Phi ⟨beltramiMul (beltramiMul a (beltramiInv b)) b, hm2'⟩ :=
      Quotient.sound (show teichSetoid _ _ from
        bc_beltramiMul_respects (l₁ := ⟨Lambda φ, hΛ⟩) (l₂ := ⟨_, hρ⟩) (μ₁ := ν) (μ₂ := ⟨b, hb⟩) hrel hνb)
    rw [hstep]
    congr 1
    apply Subtype.ext
    show beltramiMul (beltramiMul a (beltramiInv b)) b = a
    rw [grp_mul_assoc ha (grp_inv_mem hb) hb, grp_inv_mul hb, grp_mul_zero ha]

/-- `0` is real-analytic. -/
theorem ra_zero_mem : (0 : LinfStar) ∈ realAnalyticBeltrami :=
  ⟨0, analyticOnNhd_const, Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior), 0, analyticAt_const,
    fun _ _ _ => by simp⟩

/-- Bers-chart images of real-analytic base points have real-analytic representatives. -/
theorem ra_bersChartInv_mem {ν : LinfStarBall} (hνa : (ν : LinfStar) ∈ realAnalyticBeltrami) {φ : AInf unitDisc}
    (hφ : ‖φ‖ < 2) :
    ∃ l : LinfStarBall, (l : LinfStar) ∈ realAnalyticBeltrami ∧ Phi l = bersChartInv ν φ := by
  have hm := bg_mul_mem_ball ν.2 (Lambda_mem_ball hφ)
  refine ⟨⟨_, hm⟩, ra_mul_mem (Lambda_mem_ball hφ) ν.2 (ra_Lambda_mem φ) hνa, ?_⟩
  show _ = (if h : beltramiMul (Lambda φ) (ν : LinfStar) ∈ LinfStarBall then Phi ⟨_, h⟩ else Phi ν)
  rw [dif_pos hm]

/-- `exists_realAnalytic_rep`. -/
theorem ra_exists_realAnalytic_rep (p : T1) : ∃ μ : LinfStarBall, (μ : LinfStar) ∈ realAnalyticBeltrami ∧ Phi μ = p := by
  obtain ⟨N, q, hq0, hqN, hstep⟩ := ra_path_cover p
  have key : ∀ k ≤ N, ∃ μ : LinfStarBall, (μ : LinfStar) ∈ realAnalyticBeltrami ∧ Phi μ = q k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨⟨0, mem_ball_self one_pos⟩, ra_zero_mem, hq0.symm⟩
    | succ k ih =>
      intro hk
      obtain ⟨ν, hνa, hνq⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨φ, hφ, hφq⟩ := hstep k (Nat.lt_of_succ_le hk) ν hνq
      obtain ⟨l, hla, hlq⟩ := ra_bersChartInv_mem hνa hφ
      exact ⟨l, hla, hlq.trans hφq⟩
  obtain ⟨μ, hμa, hμq⟩ := key N le_rfl
  exact ⟨μ, hμa, hμq.trans hqN⟩

/-- `realAnalyticBeltrami_subgroup`. -/
theorem ra_realAnalyticBeltrami_subgroup {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hμa : μ ∈ realAnalyticBeltrami) (hνa : ν ∈ realAnalyticBeltrami) :
    beltramiMul ν (beltramiInv μ) ∈ realAnalyticBeltrami := by
  obtain ⟨G, hG, hae, hinf⟩ := ra_formula_rep hμ hν hμa hνa
  refine ⟨G, hG, ?_, hinf⟩
  filter_upwards [bc_beltramiMul_inv_formula hμ hν, hae] with u h1 h2
  exact h1.trans h2

/-- `remark_1_2`. -/
theorem ra_remark_1_2 :
    (⋃ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ realAnalyticBeltrami}, bersChartDomain μ.1) = univ := by
  refine eq_univ_of_forall fun p => ?_
  obtain ⟨μ, hμa, hμp⟩ := ra_exists_realAnalytic_rep p
  refine mem_iUnion.mpr ⟨⟨μ, hμa⟩, 0, mem_ball_self two_pos, ?_⟩
  have hL : beltramiMul (Lambda 0) (μ : LinfStar) = μ := by rw [wp_Lambda_zero, QCV.qcv_beltramiMul_zero μ.2]
  show (if h : beltramiMul (Lambda 0) (μ : LinfStar) ∈ LinfStarBall then Phi ⟨_, h⟩ else Phi μ) = p
  split_ifs with h
  · rw [← hμp]
    congr 1
    exact Subtype.ext hL
  · exact hμp

/-- (TT:363, [Leh87, III.1.1]) Every point of `T(1)` is represented by a real-analytic Beltrami differential. -/
theorem exists_realAnalytic_rep (p : T1) : ∃ μ : LinfStarBall, (μ : LinfStar) ∈ realAnalyticBeltrami ∧ Phi μ = p := by
  exact ra_exists_realAnalytic_rep p

/-- (TT:454) The real-analytic Beltrami differentials form a subgroup of `L∞(𝔻*)₁`. -/
theorem realAnalyticBeltrami_subgroup {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (hμa : μ ∈ realAnalyticBeltrami) (hνa : ν ∈ realAnalyticBeltrami) :
    beltramiMul ν (beltramiInv μ) ∈ realAnalyticBeltrami := by
  exact ra_realAnalyticBeltrami_subgroup hμ hν hμa hνa

/-- **Remark 1.2** (TT:514). The charts `(U_μ, h_μ)` with real-analytic `μ` already cover `T(1)`. -/
theorem remark_1_2 : (⋃ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ realAnalyticBeltrami}, bersChartDomain μ.1) = univ := by
  exact ra_remark_1_2

end TakhtajanTeo
