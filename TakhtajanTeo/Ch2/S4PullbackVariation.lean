import TakhtajanTeo.Ch2.S4ModelAVariation

/-! # Actual moving-base coefficient and Schwarzian variation (`s4pv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- P1
theorem s4pv_fraction_cancel {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ((a + b) / (1 + conj a * b) - a) /
      (1 - conj a * ((a + b) / (1 + conj a * b))) = b := by
  have hab : ‖conj a * b‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hd : 1 + conj a * b ≠ 0 := by
    intro h
    have he : conj a * b = -1 := by linear_combination h
    rw [he] at hab
    simp at hab
  have hδ : 1 - conj a * a ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul, norm_conj] at hn
    nlinarith [norm_nonneg a]
  have he : 1 - conj a * ((a + b) / (1 + conj a * b)) =
      (1 - conj a * a) / (1 + conj a * b) := by
    field_simp [hd]
    ring
  rw [he]
  apply (div_eq_iff (div_ne_zero hδ hd)).2
  apply (mul_right_cancel₀ hd)
  rw [sub_mul, div_mul_cancel₀ _ hd, mul_assoc, div_mul_cancel₀ _ hd]
  ring

-- P2
theorem s4pv_source_quotient {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar)
    {e : ℂ} (he : ‖e • ν‖ < 1) :
    ∀ᵐ x ∂(volume.restrict unitDiscExterior),
      (beltramiMul (e • ν) κ x - κ x) / (1 - conj (κ x) * beltramiMul (e • ν) κ x) =
        e * (qcv_rightDerivative κ ν x) / (1 - conj (κ x) * κ x) := by
  have heB : e • ν ∈ LinfStarBall := by simpa [LinfStarBall] using he
  filter_upwards [bc_mul_ae hκ heB, LinfStar_ae_norm_le κ, bc_b_bound (l := e • ν) hκ,
    qcv_rightDerivative_ae hκ ν, bc_pullback_ae hκ (Lp.coeFn_smul e ν)] with x hmul hk hb hD hsmul
  have hκx : ‖κ x‖ < 1 := hk.trans_lt (bc_norm_lt_one hκ)
  have hbx : ‖(e • ν) (wA κ x) * (conj (dz (wA κ) x) / dz (wA κ) x)‖ < 1 := hb.trans_lt he
  have hδ : 1 - conj (κ x) * κ x ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul, norm_conj] at hn
    nlinarith [norm_nonneg (κ x)]
  have hρ : (1 - (‖κ x‖ : ℂ) ^ 2) = 1 - conj (κ x) * κ x := by
    rw [mul_comm (conj (κ x)) (κ x), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow]
  calc
    _ = (e • ν) (wA κ x) * (conj (dz (wA κ) x) / dz (wA κ) x) := by
      rw [hmul]
      simpa only [mul_assoc] using s4pv_fraction_cancel hκx hbx
    _ = _ := by
      rw [hD, hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hρ]
      field_simp [hδ]
      <;> ring

-- P3
theorem s4pv_quotient_linear {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar)
    {e : ℂ} (he : ‖e • ν‖ < 1) :
    ahQuot (extB (beltramiMul (e • ν) κ)) (extB κ) (qcv_planeSolution κ) =ᵐ[volume]
      (fun y => e * ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ) y) := by
  have hsrc : ∀ᵐ x : ℂ,
      (extB (beltramiMul (e • ν) κ) x - extB κ x) /
        (1 - conj (extB κ x) * extB (beltramiMul (e • ν) κ) x) =
      e * extB (qcv_rightDerivative κ ν) x / (1 - conj (extB κ x) * extB κ x) := by
    filter_upwards [(ae_restrict_iff' wp_exterior_isOpen.measurableSet).mp
      (s4pv_source_quotient hκ ν he)] with x hx
    by_cases h : x ∈ unitDiscExterior
    · simpa only [extB, indicator_of_mem h] using hx h
    · simp only [extB, indicator_of_notMem h, sub_self, zero_div, mul_zero]
  have hN := (qcv_W_props (bc_norm_lt_one hκ)).1
  filter_upwards [(ahT_qmp_inv hN.1 hN.2.1).ae hsrc] with y hy
  simp only [ahQuot, ahT_dot, qcv_planeSolution]
  rw [hy]
  ring

-- P4
theorem s4pv_plane_transition {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (ν : LinfStar)
    {e : ℂ} (he : ‖e • ν‖ < 1)
    (heM : ‖e‖ * (‖qcv_rightDerivative κ ν‖ / (1 - ‖κ‖ ^ 2)) < 1) :
    qcv_planeTransition (beltramiMul (e • ν) κ) κ =
      normalizedSolution (fun y => e *
        ahT_dot (extB (qcv_rightDerivative κ ν)) (extB κ) (qcv_planeSolution κ) y) := by
  have heB : e • ν ∈ LinfStarBall := by simpa [LinfStarBall] using he
  have hell : beltramiMul (e • ν) κ ∈ LinfStarBall := (wA_mul hκ heB).1
  let ell := beltramiMul (e • ν) κ
  let K : ℝ := max ‖κ‖ ‖ell‖
  have hK0 : 0 ≤ K := (norm_nonneg κ).trans (le_max_left _ _)
  have hK1 : K < 1 := max_lt (bc_norm_lt_one hκ) (bc_norm_lt_one hell)
  have hBCκ : IsBeltramiCoeff (extB κ) univ K :=
    ⟨(extB_isBeltramiCoeff κ).1,
      (extB_isBeltramiCoeff κ).2.mono fun x hx => hx.trans (le_max_left _ _)⟩
  have hBCell : IsBeltramiCoeff (extB ell) univ K :=
    ⟨(extB_isBeltramiCoeff ell).1,
      (extB_isBeltramiCoeff ell).2.mono fun x hx => hx.trans (le_max_right _ _)⟩
  have hNκ := (qcv_W_props (bc_norm_lt_one hκ)).1
  have hNell := (qcv_W_props (bc_norm_lt_one hell)).1
  have htrans := (ah_quotient hK0 hK1 hBCell hBCκ hNell hNκ).1
  have hlin := qcv_isNS_congr (s4pv_quotient_linear hκ ν he) htrans
  have hm := qcv_base_dot_isBeltramiCoeff hκ (qcv_rightDerivative κ ν)
  have hden : 0 < 1 - ‖κ‖ ^ 2 := by
    have hk := bc_norm_lt_one hκ
    nlinarith [norm_nonneg κ]
  have hM0 : 0 ≤ ‖qcv_rightDerivative κ ν‖ / (1 - ‖κ‖ ^ 2) := div_nonneg (norm_nonneg _) hden.le
  have hsol := qcv_ns_eq (mul_nonneg (norm_nonneg e) hM0) heM (s4v_linear_coeff hm e) hlin
  rw [hsol]
  funext y
  change qcv_planeSolution ell (Function.invFun (qcv_planeSolution κ) y) =
    qcv_planeSolution ell (Function.invFunOn (qcv_planeSolution κ) univ y)
  congr 1
  obtain ⟨x, rfl⟩ := (qcv_planeSolution_bijective hκ).2 y
  rw [Function.leftInverse_invFun (qcv_planeSolution_bijective hκ).1,
    (qcv_planeSolution_bijective hκ).1.injOn.leftInvOn_invFunOn (mem_univ x)]

end Ch2
end TakhtajanTeo
