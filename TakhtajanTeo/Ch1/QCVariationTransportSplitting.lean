import TakhtajanTeo.Ch1.QCVariationTransport

/-!
# Closed splittings transported to an arbitrary Beltrami coefficient

The transported origin quotient is explicit and split-surjective. Identifying
its kernel with the actual Bers derivative at the new base still requires the
Bers covariance argument; that identification is not assumed here.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

def qcv_transportedTrivial (μ : LinfStar) : Submodule ℂ LinfStar :=
  trivialBeltrami.map (qcv_rightDerivative μ).toLinearMap

def qcv_transportedHarmonic (μ : LinfStar) : Submodule ℂ LinfStar :=
  harmonicBeltrami.map (qcv_rightDerivative μ).toLinearMap

/-- The origin quotient expressed in the tangent space at `μ`. This is not a
definition of the actual derivative of `bersPhi` at `μ`. -/
def qcv_transportedOriginDerivative (μ : LinfStar) : LinfStar →L[ℂ] AInf unitDisc :=
  (fderiv ℂ bersPhi 0).comp (qcv_inverseRightDerivative μ)

theorem qcv_transported_isCompl {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsCompl (qcv_transportedTrivial μ) (qcv_transportedHarmonic μ) := by
  exact (Submodule.orderIsoMapComap (qcv_rightDerivativeEquiv hμ).toLinearEquiv).isCompl_iff.mp
    qcv_origin_isCompl

theorem qcv_rightDerivative_map_isClosed {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (P : Submodule ℂ LinfStar) (hP : IsClosed (P : Set LinfStar)) :
    IsClosed ((P.map (qcv_rightDerivative μ).toLinearMap : Submodule ℂ LinfStar) : Set LinfStar) := by
  have he : ((P.map (qcv_rightDerivative μ).toLinearMap : Submodule ℂ LinfStar) : Set LinfStar) =
      (qcv_rightDerivativeEquiv hμ) '' (P : Set LinfStar) := by
    ext y
    change (∃ x, x ∈ P ∧ qcv_rightDerivative μ x = y) ↔
      ∃ x, x ∈ P ∧ qcv_rightDerivativeEquiv hμ x = y
    rfl
  rw [he]
  exact (qcv_rightDerivativeEquiv hμ).toHomeomorph.isClosedMap _ hP

theorem qcv_transportedTrivial_isClosed {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsClosed (qcv_transportedTrivial μ : Set LinfStar) :=
  qcv_rightDerivative_map_isClosed hμ _ isClosed_trivialBeltrami

theorem qcv_transportedHarmonic_isClosed {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsClosed (qcv_transportedHarmonic μ : Set LinfStar) :=
  qcv_rightDerivative_map_isClosed hμ _ isClosed_harmonicBeltrami

/-- An explicit right inverse for the transported origin quotient. -/
theorem qcv_transportedOriginDerivative_rightInverse {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (φ : AInf unitDisc) :
    qcv_transportedOriginDerivative μ (qcv_rightDerivative μ (Lambda φ)) = φ := by
  change fderiv ℂ bersPhi 0 (qcv_inverseRightDerivative μ
    (qcv_rightDerivative μ (Lambda φ))) = φ
  rw [qcv_inverseRightDerivative_apply hμ, qcv_Rnm_rightDerivative hμ, qcv_D0_Lambda]

theorem qcv_transportedOriginDerivative_surjective {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) : Function.Surjective (qcv_transportedOriginDerivative μ) :=
  fun φ => ⟨qcv_rightDerivative μ (Lambda φ), qcv_transportedOriginDerivative_rightInverse hμ φ⟩

theorem qcv_transportedOriginDerivative_ker {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    (qcv_transportedOriginDerivative μ).ker = qcv_transportedTrivial μ := by
  ext ν
  constructor
  · intro hν
    apply Submodule.mem_map.mpr
    refine ⟨qcv_inverseRightDerivative μ ν, ?_, ?_⟩
    · rw [← qcv_ker_D0Phi]
      exact hν
    · change qcv_rightDerivative μ (qcv_inverseRightDerivative μ ν) = ν
      rw [qcv_inverseRightDerivative_apply hμ, qcv_rightDerivative_Rnm hμ]
  · rintro ⟨v, hv, rfl⟩
    change fderiv ℂ bersPhi 0 (qcv_inverseRightDerivative μ (qcv_rightDerivative μ v)) = 0
    rw [qcv_inverseRightDerivative_apply hμ, qcv_Rnm_rightDerivative hμ]
    rwa [← qcv_ker_D0Phi] at hv

/-- The transported harmonic component, with its complementary trivial part. -/
theorem qcv_transported_decomposition {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    qcv_rightDerivative μ (Lambda (qcv_transportedOriginDerivative μ ν)) ∈
      qcv_transportedHarmonic μ ∧
    ν - qcv_rightDerivative μ (Lambda (qcv_transportedOriginDerivative μ ν)) ∈
      qcv_transportedTrivial μ := by
  constructor
  · exact Submodule.mem_map.mpr ⟨_, Lambda_mem_harmonic _, rfl⟩
  · rw [← qcv_transportedOriginDerivative_ker hμ]
    change qcv_transportedOriginDerivative μ
      (ν - qcv_rightDerivative μ (Lambda (qcv_transportedOriginDerivative μ ν))) = 0
    rw [map_sub, qcv_transportedOriginDerivative_rightInverse hμ, sub_self]

end QCV
end TakhtajanTeo
