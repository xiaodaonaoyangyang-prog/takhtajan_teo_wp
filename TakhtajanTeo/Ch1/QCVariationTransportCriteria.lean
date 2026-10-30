import TakhtajanTeo.Ch1.QCVariationTransportSplitting

/-! # Exact reductions for the actual Bers derivative at a nonzero base -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- The actual Bers derivative after right translation, as opposed to the
transported origin quotient defined in the splitting module. -/
def qcv_translatedBersDerivative (μ : LinfStar) : LinfStar →L[ℂ] AInf unitDisc :=
  fderiv ℂ (fun l => bersPhi (beltramiMul l μ)) 0

theorem qcv_translatedBersDerivative_apply {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    qcv_translatedBersDerivative μ ν = fderiv ℂ bersPhi μ (qcv_rightDerivative μ ν) := by
  rw [qcv_translatedBersDerivative, (qcv_bers_rightTranslation_hasFDerivAt hμ).fderiv]
  rfl

/-- An unconditional kernel-transport identity for the actual Bers map. -/
theorem qcv_bers_kernel_transport {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (fderiv ℂ bersPhi μ).ker =
      (qcv_translatedBersDerivative μ).ker.map (qcv_rightDerivative μ).toLinearMap := by
  ext ν
  constructor
  · intro hν
    apply Submodule.mem_map.mpr
    refine ⟨qcv_inverseRightDerivative μ ν, ?_, ?_⟩
    · change qcv_translatedBersDerivative μ (qcv_inverseRightDerivative μ ν) = 0
      rw [qcv_translatedBersDerivative_apply hμ, qcv_inverseRightDerivative_apply hμ,
        qcv_rightDerivative_Rnm hμ]
      exact hν
    · change qcv_rightDerivative μ (qcv_inverseRightDerivative μ ν) = ν
      rw [qcv_inverseRightDerivative_apply hμ, qcv_rightDerivative_Rnm hμ]
  · rintro ⟨v, hv, rfl⟩
    change fderiv ℂ bersPhi μ (qcv_rightDerivative μ v) = 0
    change qcv_translatedBersDerivative μ v = 0 at hv
    rwa [qcv_translatedBersDerivative_apply hμ] at hv

/-- Precise remaining kernel criterion for the general-base memoir statement. -/
theorem qcv_ker_DmuPhi_iff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (fderiv ℂ bersPhi μ).ker = qcv_transportedTrivial μ ↔
      (qcv_translatedBersDerivative μ).ker = trivialBeltrami := by
  rw [qcv_bers_kernel_transport hμ]
  exact (Submodule.orderIsoMapComap (qcv_rightDerivativeEquiv hμ).toLinearEquiv).injective.eq_iff

/-- Surjectivity is unchanged by the explicit tangent reparametrization. -/
theorem qcv_bers_surjective_iff {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Surjective (fderiv ℂ bersPhi μ) ↔
      Function.Surjective (qcv_translatedBersDerivative μ) := by
  constructor
  · intro hs φ
    obtain ⟨ν, hν⟩ := hs φ
    refine ⟨qcv_inverseRightDerivative μ ν, ?_⟩
    rw [qcv_translatedBersDerivative_apply hμ, qcv_inverseRightDerivative_apply hμ,
      qcv_rightDerivative_Rnm hμ, hν]
  · intro hs φ
    obtain ⟨ν, hν⟩ := hs φ
    exact ⟨qcv_rightDerivative μ ν, (qcv_translatedBersDerivative_apply hμ ν).symm.trans hν⟩

end QCV
end TakhtajanTeo
