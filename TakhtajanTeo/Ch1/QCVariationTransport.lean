import TakhtajanTeo.Ch1.BeltramiCompose
import TakhtajanTeo.Ch1.QCVariationKernelEquality

/-!
# Tangent transport by Beltrami right translations

The forward and inverse derivatives are inverse continuous complex-linear maps.
These results use the established a.e. composition formulas, not `wA_mul`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

def qcv_rightDerivative (μ : LinfStar) : LinfStar →L[ℂ] LinfStar :=
  fderiv ℂ (fun l => beltramiMul l μ) 0

def qcv_inverseRightDerivative (μ : LinfStar) : LinfStar →L[ℂ] LinfStar :=
  fderiv ℂ (fun l => beltramiMul l (beltramiInv μ)) μ

theorem qcv_rightDerivative_ae {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      qcv_rightDerivative μ ν z =
        (1 - ‖μ z‖ ^ 2) * ν (wA μ z) * (conj (dz (wA μ) z) / dz (wA μ) z) :=
  bc_remark_1_3 hμ ν

theorem qcv_inverseRightDerivative_apply {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    qcv_inverseRightDerivative μ ν = Rnm ν μ := bc_eq_1_5 hμ ν

theorem qcv_rightDerivative_Rnm {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    qcv_rightDerivative μ (Rnm ν μ) = ν := by
  apply Lp.ext
  filter_upwards [qcv_rightDerivative_ae hμ (Rnm ν μ),
    bc_pullback_ae hμ (bc_Rnm_ae hμ ν),
    bc_pullback_ae hμ (ae_restrict_mem bc_hEo.measurableSet),
    ae_restrict_of_ae (bc_wA_ae hμ), LinfStar_ae_norm_le μ]
    with z hD hR hw hz hm
  have hwn : wA μ z ≠ 0 := by
    intro he
    norm_num [he, unitDiscExterior] at hw
  rw [bc_invFun_wA hwn] at hR
  have hmn : (1 - ‖μ z‖ ^ 2 : ℂ) ≠ 0 := by
    have hsmall : ‖μ z‖ < 1 := hm.trans_lt (bc_norm_lt_one hμ)
    have hreal : (1 - ‖μ z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg (μ z)]
    exact_mod_cast hreal
  have hdz := hz.2.1
  have hconj : conj (dz (wA μ) z) ≠ 0 := by simpa using hdz
  rw [hD, hR]
  field_simp

theorem qcv_Rnm_rightDerivative {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    Rnm (qcv_rightDerivative μ ν) μ = ν := by
  apply Lp.ext
  filter_upwards [bc_Rnm_ae hμ (qcv_rightDerivative μ ν),
    bc_invFun_pullback_ae hμ (qcv_rightDerivative_ae hμ ν),
    bc_invFun_pullback_ae hμ (ae_restrict_of_ae (bc_wA_ae hμ)),
    bc_invFun_pullback_ae hμ (LinfStar_ae_norm_le μ), bc_invFun_right_ae hμ]
    with y hR hD hy hm hw
  let z := Function.invFun (wA μ) y
  have hmn : (1 - ‖μ z‖ ^ 2 : ℂ) ≠ 0 := by
    have hsmall : ‖μ z‖ < 1 := hm.trans_lt (bc_norm_lt_one hμ)
    have hreal : (1 - ‖μ z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg (μ z)]
    exact_mod_cast hreal
  have hdz : dz (wA μ) z ≠ 0 := hy.2.1
  have hconj : conj (dz (wA μ) z) ≠ 0 := by simpa using hdz
  rw [hR, hD, hw]
  change (1 - ‖μ z‖ ^ 2) * ν y * (conj (dz (wA μ) z) / dz (wA μ) z) /
    (1 - ‖μ z‖ ^ 2) * (dz (wA μ) z / conj (dz (wA μ) z)) = ν y
  field_simp

/-- Right translation induces an isomorphism of the full `L∞` tangent spaces. -/
def qcv_rightDerivativeEquiv {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    LinfStar ≃L[ℂ] LinfStar :=
  ContinuousLinearEquiv.equivOfInverse (qcv_rightDerivative μ) (qcv_inverseRightDerivative μ)
    (fun ν => by rw [qcv_inverseRightDerivative_apply hμ, qcv_Rnm_rightDerivative hμ])
    (fun ν => by rw [qcv_inverseRightDerivative_apply hμ, qcv_rightDerivative_Rnm hμ])

theorem qcv_rightDerivative_norm_le {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ‖qcv_rightDerivative μ ν‖ ≤ ‖ν‖ := by
  apply bc_Lp_norm_le _ (norm_nonneg _)
  filter_upwards [qcv_rightDerivative_ae hμ ν, bc_g_bound hμ ν] with z hz hb
  rw [hz]
  convert hb using 1
  push_cast
  rfl

theorem qcv_inverseRightDerivative_norm_le {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    ‖qcv_inverseRightDerivative μ ν‖ ≤ (1 / (1 - ‖μ‖ ^ 2)) * ‖ν‖ := by
  rw [qcv_inverseRightDerivative_apply hμ]
  exact bc_Rnm_norm_le hμ ν

/-- The right translation really sends zero to its base coefficient. -/
theorem qcv_beltramiMul_zero {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    beltramiMul 0 μ = μ := by
  obtain ⟨D, hD⟩ := bc_exists_D hμ
  have hh := bc_remainder (l := 0) hμ D hD (by norm_num)
  apply sub_eq_zero.mp
  simpa using hh

theorem qcv_rightTranslation_hasFDerivAt {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    HasFDerivAt (fun l => beltramiMul l μ) (qcv_rightDerivative μ) 0 := by
  obtain ⟨D, hD, _⟩ := bc_hasFDerivAt hμ
  simpa only [qcv_rightDerivative, hD.fderiv] using hD

/-- Chain rule for the actual Bers map after Beltrami right translation. -/
theorem qcv_bers_rightTranslation_hasFDerivAt {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) :
    HasFDerivAt (fun l => bersPhi (beltramiMul l μ))
      ((fderiv ℂ bersPhi μ).comp (qcv_rightDerivative μ)) 0 := by
  have hb := (qcv_bersPhi_differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds hμ)).hasFDerivAt
  have hb' : HasFDerivAt bersPhi (fderiv ℂ bersPhi μ) (beltramiMul 0 μ) := by
    simpa only [qcv_beltramiMul_zero hμ] using hb
  exact hb'.comp 0 (qcv_rightTranslation_hasFDerivAt hμ)

/-- The origin has the claimed closed harmonic complement. -/
theorem qcv_origin_isCompl : IsCompl trivialBeltrami harmonicBeltrami := by
  rw [← qcv_ker_D0Phi]
  have hL0 : Lambda (0 : AInf unitDisc) = 0 := by
    simpa using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)
  constructor
  · rw [Submodule.disjoint_def]
    intro ν hν hh
    have hi := qcv_lambda_inverse_D0bers.2.2 ν hh
    change fderiv ℂ bersPhi 0 ν = 0 at hν
    rw [hν, hL0] at hi
    exact hi.symm
  · rw [codisjoint_iff_le_sup]
    intro ν _
    apply Submodule.mem_sup.mpr
    refine ⟨ν - Lambda (fderiv ℂ bersPhi 0 ν), ?_,
      Lambda (fderiv ℂ bersPhi 0 ν), Lambda_mem_harmonic _, ?_⟩
    · change fderiv ℂ bersPhi 0 (ν - Lambda (fderiv ℂ bersPhi 0 ν)) = 0
      rw [map_sub, qcv_D0_Lambda, sub_self]
    · exact sub_add_cancel _ _

theorem qcv_phi_submersion_zero :
    LinearMap.range (fderiv ℂ bersPhi 0 : LinfStar →ₗ[ℂ] AInf unitDisc) = ⊤ ∧
      ∃ C : Submodule ℂ LinfStar, IsClosed (C : Set LinfStar) ∧
        IsCompl (LinearMap.ker (fderiv ℂ bersPhi 0 : LinfStar →ₗ[ℂ] AInf unitDisc)) C := by
  refine ⟨LinearMap.range_eq_top.mpr (fun φ => ⟨Lambda φ, qcv_D0_Lambda φ⟩),
    harmonicBeltrami, isClosed_harmonicBeltrami, ?_⟩
  rw [qcv_ker_D0Phi]
  exact qcv_origin_isCompl

end QCV
end TakhtajanTeo
