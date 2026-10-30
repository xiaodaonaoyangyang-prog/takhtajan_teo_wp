import TakhtajanTeo.Ch2.S5_PeriodMapping
import TakhtajanTeo.Ch2.S2_GrunskyOp

/-! # Bounded matrix products for the KYNS period map

This module connects `IsBoundedMat` to the existing genuine `ell2` operator.
It does not assume or use the open Nag–Sullivan or Proposition 5.1 statements.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- L1
theorem pmb_partial_bound {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) :
    ∃ C : ℝ, ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖ ^ 2) →
      ∀ M, ∑ m ∈ Finset.range M, ‖∑' n, A m n * x n‖ ^ 2 ≤
        C * ∑' n, ‖x n‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hA
  refine ⟨C, fun x hx M => ?_⟩
  exact ((hC x hx).1.sum_le_tsum (Finset.range M)
    (fun _ _ => sq_nonneg _)).trans (hC x hx).2

-- L2
theorem pmb_apply {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (x : ell2) (m : ℕ) :
    gopOp A x m = matApply A x m := by
  exact gop_apply (isBoundedMat_row_isL2 hA) (pmb_partial_bound hA) x m

-- L3
theorem pmb_entry {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A) (m n : ℕ) :
    gopOp A (lp.single 2 n 1 : ell2) m = A m n := by
  exact gop_single_entry (isBoundedMat_row_isL2 hA) (pmb_partial_bound hA) m n

-- L4
theorem pmb_of_operator (T : ell2 →L[ℂ] ell2) {A : ℕ → ℕ → ℂ}
    (hA : ∀ m n, T (lp.single 2 n 1 : ell2) m = A m n) : IsBoundedMat A := by
  refine ⟨‖T‖ ^ 2, fun x hx => ?_⟩
  let X : ell2 := ⟨x, gop_mem_of_summable hx⟩
  have he : ∀ m, T X m = matApply A x m := by
    intro m
    rw [gop_clm_apply]
    exact tsum_congr fun n => by rw [hA m n]
  have hs : IsL2 (matApply A x) := by
    simpa only [IsL2, he] using gop_l2_summable (T X)
  refine ⟨hs, ?_⟩
  have hb := mul_self_le_mul_self (norm_nonneg (T X)) (T.le_opNorm X)
  simpa only [← sq, mul_pow, gop_norm_sq, he, sqSum, X] using hb

-- L5
theorem pmb_mul_entry {A B : ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : IsBoundedMat B) (m n : ℕ) :
    (gopOp A * gopOp B) (lp.single 2 n 1 : ell2) m = mulMat A B m n := by
  rw [mul_apply_eq_comp, pmb_apply hA]
  exact tsum_congr fun k => by rw [pmb_entry hB]

-- L6
theorem pmb_bounded_mul {A B : ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : IsBoundedMat B) : IsBoundedMat (mulMat A B) := by
  exact pmb_of_operator (gopOp A * gopOp B) (pmb_mul_entry hA hB)

-- L7
theorem pmb_mul {A B : ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : IsBoundedMat B) :
    gopOp (mulMat A B) = gopOp A * gopOp B := by
  apply gop_ext
  intro m n
  rw [pmb_entry (pmb_bounded_mul hA hB), pmb_mul_entry hA hB]

-- L8
theorem pmb_mul_assoc {A B C : ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : IsBoundedMat B) (hC : IsBoundedMat C) :
    mulMat (mulMat A B) C = mulMat A (mulMat B C) := by
  have he : gopOp (mulMat (mulMat A B) C) = gopOp (mulMat A (mulMat B C)) := by
    rw [pmb_mul (pmb_bounded_mul hA hB) hC, pmb_mul hA hB,
      pmb_mul hA (pmb_bounded_mul hB hC), pmb_mul hB hC, mul_assoc]
  funext m n
  simpa only [pmb_entry (pmb_bounded_mul (pmb_bounded_mul hA hB) hC),
    pmb_entry (pmb_bounded_mul hA (pmb_bounded_mul hB hC))] using
    congrArg (fun T : ell2 →L[ℂ] ell2 => T (lp.single 2 n 1 : ell2) m) he

-- L9
theorem pmb_right_cancel {A B R S : ℕ → ℕ → ℂ}
    (hA : IsBoundedMat A) (hB : IsBoundedMat B)
    (hR : IsBoundedMat R) (hS : IsBoundedMat S)
    (hRS : ∀ m n, mulMat R S m n = kron m n)
    (h : mulMat A R = mulMat B R) : A = B := by
  have hi : gopOp R * gopOp S = 1 := by
    apply gop_ext
    intro m n
    rw [pmb_mul_entry hR hS, hRS, one_apply_eq_self, gop_single_apply]
    rfl
  have he : gopOp A * gopOp R = gopOp B * gopOp R := by
    rw [← pmb_mul hA hR, ← pmb_mul hB hR, h]
  have he' := congrArg (fun T : ell2 →L[ℂ] ell2 => T * gopOp S) he
  rw [mul_assoc, mul_assoc, hi, mul_one, mul_one] at he'
  funext m n
  simpa only [pmb_entry hA, pmb_entry hB] using
    congrArg (fun T : ell2 →L[ℂ] ell2 => T (lp.single 2 n 1 : ell2) m) he'

-- L10
theorem pmb_kyns_unique (p : T1) {Z S : ℕ → ℕ → ℂ}
    (hZ : IsBoundedMat Z) (hS : IsBoundedMat S)
    (hA : IsBoundedMat (fun m n => conj (matA (wA (Quotient.out p : LinfStarBall)) m n)))
    (hAS : ∀ m n, mulMat (fun k l => conj (matA (wA (Quotient.out p : LinfStarBall)) k l)) S m n = kron m n)
    (hZeq : ∀ m n, mulMat Z (fun k l => conj (matA (wA (Quotient.out p : LinfStarBall)) k l)) m n =
      matB (wA (Quotient.out p : LinfStarBall)) m n) : kyns p = Z := by
  unfold kyns
  dsimp only
  split_ifs with hex
  · apply pmb_right_cancel hex.choose_spec.1 hZ hA hS hAS
    funext m n
    exact (hex.choose_spec.2 m n).trans (hZeq m n).symm
  · exact False.elim (hex ⟨Z, hZ, hZeq⟩)

end Ch2
end TakhtajanTeo
