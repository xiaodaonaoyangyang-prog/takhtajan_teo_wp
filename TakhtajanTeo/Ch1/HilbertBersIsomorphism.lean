import TakhtajanTeo.Ch1.HilbertBersSurjection
import TakhtajanTeo.Ch1.HilbertBersChartBridge
import TakhtajanTeo.Ch1.HilbertInjectiveSubmersion

/-! Actual groupO derivative isomorphisms, obtained from the proved reflected
surjection and local injectivity of the strictly differentiable A2 chart.
No all-base injectivity claim is made. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem hbSurj_bijective_groupO (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    Function.Bijective (hbL2_bersOperator μ) := by
  obtain ⟨hstrict, U, hU, hinj⟩ := hbBridge_chart_local_data μ hμ
  have honto := hbSurj_bersOperator μ
  exact ⟨his_injective_of_surjective hstrict honto hU hinj, honto⟩

/-- The now-proved origin input for the actual Hilbert inverse-chart machinery. -/
theorem hbSurj_origin_iso : hibOriginDerivativeIso :=
  hib_origin_of_bersOperator_bijective hbSurj_bijective_groupO

/-- Holomorphic recentering gives actual derivative isomorphisms at every
point of each groupO Hilbert chart, not only its center. -/
theorem hbSurj_derivative_iso : hibDerivativeIso := hib_iso_of_origin hbSurj_origin_iso

/-- The original distribution equality, valid at every admissible base. -/
theorem hbSurj_distT_eq (μ : LinfStarBall) :
    {φ | ∃ ψ ∈ distT μ, EqOn ψ φ unitDisc} =
      {φ | ∃ ψ ∈ A2fun unitDisc, EqOn ψ φ unitDisc} :=
  hbL2_distT_eq_of_surjective μ (hbSurj_bersOperator μ)

theorem hbSurj_bers_openEmbedding :
    @Topology.IsOpenEmbedding T1 (AInf unitDisc) hilbertTopology hilbertTopologyA bers :=
  hib_bers_openEmbedding hbSurj_derivative_iso

/-- The exact Theorem 2.13 conclusion, now with the actual operator input discharged. -/
theorem hbSurj_thm_2_13 :
    (∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
      (∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ) ∈ A2fun unitDisc) ∧
      DifferentiableOn ℂ (hib_chart μ) (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        Function.Bijective (fderiv ℂ (hib_chart μ) φ)) ∧
      @IsOpen (AInf unitDisc) hilbertTopologyA (range bers) :=
  hib_thm_2_13_of_iso hbSurj_derivative_iso

theorem hbSurj_cor_3_2 : T01 = {p | AInf.toFun (bers p) ∈ A2fun unitDisc} :=
  hib_cor_3_2_of_iso hbSurj_derivative_iso

#print axioms hbSurj_bijective_groupO
#print axioms hbSurj_origin_iso
#print axioms hbSurj_derivative_iso
#print axioms hbSurj_distT_eq
#print axioms hbSurj_bers_openEmbedding
#print axioms hbSurj_thm_2_13
#print axioms hbSurj_cor_3_2
end TakhtajanTeo
