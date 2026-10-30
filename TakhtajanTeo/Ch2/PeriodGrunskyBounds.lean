import TakhtajanTeo.Ch2.PeriodMatrixBridge
import TakhtajanTeo.Ch2.S2_Remark23

/-! # Actual Grunsky bounds and invertibility for the period matrix

Only proved Grunsky identities and strict contraction estimates are used.
The remaining Fourier identification with `matA` is a separate obligation.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- G1
theorem pgb_bounded {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {A : ℕ → ℕ → ℂ}
    (hA : A ∈ ({B1 (grunsky (fsans μ) (gsans μ)), B2 (grunsky (fsans μ) (gsans μ)),
      B3 (grunsky (fsans μ) (gsans μ)), B4 (grunsky (fsans μ) (gsans μ))} : Set (ℕ → ℕ → ℂ))) :
    IsBoundedMat A := by
  obtain ⟨hr, hb⟩ := gop_grunsky_bounds
    (AppB.b8_welding_normalized_pair hμ) (r22_complement_null hμ) A hA
  exact pmb_of_operator (gopOp A) (gop_single_entry hr hb)

-- G2
theorem pgb_norm_lt_one {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ‖gopOp (B1 (grunsky (fsans μ) (gsans μ)))‖ < 1 ∧
      ‖gopOp (B4 (grunsky (fsans μ) (gsans μ)))‖ < 1 := by
  obtain ⟨c, hc0, hc1, C, hC⟩ := remark_2_3 hμ
  have hb1 := pgb_bounded hμ (A := B1 (grunsky (fsans μ) (gsans μ))) (by simp)
  have hb4 := pgb_bounded hμ (A := B4 (grunsky (fsans μ) (gsans μ))) (by simp)
  have hb {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A)
      (hh : ∀ x : ℕ → ℂ, IsL2 x → sqSum (matApply A x) ≤ c ^ 2 * sqSum x) :
      ‖gopOp A‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ hc0
    intro x
    have hs : ‖gopOp A x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2 := by
      simpa only [gop_norm_sq, pmb_apply hA, sqSum] using hh x (gop_l2_summable x)
    nlinarith [norm_nonneg (gopOp A x), norm_nonneg x, mul_nonneg hc0 (norm_nonneg x)]
  exact ⟨(hb hb1 (fun x hx => (hC x hx).1)).trans_lt hc1,
    (hb hb4 (fun x hx => (hC x hx).2.1)).trans_lt hc1⟩

-- G3
theorem pgb_period_siegel (p : T1) : periodP p ∈ siegelDisk := by
  let μ : LinfStar := (Quotient.out p : LinfStarBall)
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hb : IsBoundedMat (periodP p) := pgb_bounded hμ (by simp [periodP, μ])
  have hn : ‖gopOp (periodP p)‖ < 1 := (pgb_norm_lt_one hμ).1
  refine ⟨fun m n => ((grunsky_unitary (AppB.b8_welding_normalized_pair hμ)
    (r22_complement_null hμ)).1 m n).1, hb, ?_⟩
  intro x hx hx0
  let X : ell2 := ⟨x, gop_mem_of_summable hx⟩
  have hX : X ≠ 0 := by
    intro h
    apply hx0
    funext n
    exact congrArg (fun y : ell2 => y n) h
  have ht : ‖gopOp (periodP p) X‖ < ‖X‖ :=
    (ContinuousLinearMap.le_opNorm _ X).trans_lt
      (by simpa using mul_lt_mul_of_pos_right hn (norm_pos_iff.mpr hX))
  have hs : ‖gopOp (periodP p) X‖ ^ 2 < ‖X‖ ^ 2 := by
    nlinarith [norm_nonneg (gopOp (periodP p) X)]
  simpa only [gop_norm_sq, pmb_apply hb, sqSum, X] using hs

-- G4
theorem pgb_unit_of_defects (T U V : ell2 →L[ℂ] ell2)
    (hU : ‖U‖ < 1) (hV : ‖V‖ < 1)
    (hleft : T * star T = 1 - U * star U)
    (hright : star T * T = 1 - star V * V) : IsUnit T := by
  have hu : ‖U * star U‖ < 1 := by
    apply (norm_mul_le _ _).trans_lt
    change ‖U‖ * ‖ContinuousLinearMap.adjoint U‖ < 1
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg U]
  have hv : ‖star V * V‖ < 1 := by
    apply (norm_mul_le _ _).trans_lt
    change ‖ContinuousLinearMap.adjoint V‖ * ‖V‖ < 1
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg V]
  obtain ⟨R, hR, -⟩ := isUnit_iff_exists.mp (isUnit_one_sub_of_norm_lt_one hu)
  obtain ⟨L, -, hL⟩ := isUnit_iff_exists.mp (isUnit_one_sub_of_norm_lt_one hv)
  rw [← hleft] at hR
  rw [← hright] at hL
  apply isUnit_iff_exists_and_exists.mpr
  exact ⟨⟨star T * R, by rwa [← mul_assoc]⟩, ⟨L * star T, by rwa [mul_assoc]⟩⟩

-- G5
theorem pgb_mixed_isUnit {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsUnit (gopOp (B2 (grunsky (fsans μ) (gsans μ)))) ∧
      IsUnit (gopOp (B3 (grunsky (fsans μ) (gsans μ)))) := by
  obtain ⟨h1, h2, _, h3, h4, _⟩ := gop_blocks
    (AppB.b8_welding_normalized_pair hμ) (r22_complement_null hμ)
  obtain ⟨hn1, hn4⟩ := pgb_norm_lt_one hμ
  constructor
  · apply pgb_unit_of_defects _ _ _ hn1 hn4
    · exact eq_sub_of_add_eq' h1
    · exact eq_sub_of_add_eq h4
  · apply pgb_unit_of_defects _ _ _ hn4 hn1
    · exact eq_sub_of_add_eq h2
    · exact eq_sub_of_add_eq' h3

-- G6
theorem pgb_inverse_matrix {A : ℕ → ℕ → ℂ} (hA : IsBoundedMat A)
    (hu : IsUnit (gopOp A)) :
    ∃ R : ℕ → ℕ → ℂ, IsBoundedMat R ∧
      (∀ m n, mulMat A R m n = kron m n) ∧
      ∀ m n, mulMat R A m n = kron m n := by
  obtain ⟨u, hu⟩ := hu
  let R : ℕ → ℕ → ℂ := fun m n => (↑u⁻¹ : ell2 →L[ℂ] ell2) (lp.single 2 n 1 : ell2) m
  have hR : IsBoundedMat R := pmb_of_operator (↑u⁻¹) (fun _ _ => rfl)
  have he : gopOp R = (↑u⁻¹ : ell2 →L[ℂ] ell2) :=
    gop_ext (fun m n => pmb_entry hR m n)
  have hl : gopOp A * gopOp R = 1 := by rw [he, ← hu]; exact u.val_inv
  have hr : gopOp R * gopOp A = 1 := by rw [he, ← hu]; exact u.inv_val
  refine ⟨R, hR, fun m n => ?_, fun m n => ?_⟩
  · rw [← pmb_mul_entry hA hR, hl, one_apply_eq_self, gop_single_apply]
    rfl
  · rw [← pmb_mul_entry hR hA, hr, one_apply_eq_self, gop_single_apply]
    rfl

-- G7
theorem pgb_B3_inverse {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ R : ℕ → ℕ → ℂ, IsBoundedMat R ∧
      (∀ m n, mulMat (B3 (grunsky (fsans μ) (gsans μ))) R m n = kron m n) ∧
      ∀ m n, mulMat R (B3 (grunsky (fsans μ) (gsans μ))) m n = kron m n := by
  exact pgb_inverse_matrix (pgb_bounded hμ (by simp)) (pgb_mixed_isUnit hμ).2

end Ch2
end TakhtajanTeo
