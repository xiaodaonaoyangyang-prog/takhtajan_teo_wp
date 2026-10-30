import TakhtajanTeo.Ch1.HilbertBersInverse
import TakhtajanTeo.Ch1.BersAtlasPartial

/-! The actual A2 chart satisfies the geometric hypotheses of the local
surjection-to-injection argument. Reproduction/surjectivity is still separate.
The groupO premise is inherited from actual A2 chart holomorphy. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Recovering the ambient Bers value proves injectivity on the whole actual
Hilbert chart ball. No smallness condition on the base Bers coordinate occurs. -/
theorem hbBridge_chart_injOn (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    InjOn (hib_chart μ) (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) := by
  intro x hx y hy he
  have hB : bers (bersChartInv μ (A2toAInf x)) =
      bers (bersChartInv μ (A2toAInf y)) := by
    rw [hib_chart_value hμ hx, hib_chart_value hμ hy, he]
  apply A2toAInf_injective
  exact ba_injOn μ (mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt hx))
    (mem_ball_zero_iff.mpr (ct_A2toAInf_norm_lt hy)) (bers_injective hB)

/-- The strict derivative needed by the fiber argument is the concrete
fourth-order-kernel operator, not a separately chosen model derivative. -/
theorem hbBridge_chart_strict_zero (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    HasStrictFDerivAt (hib_chart μ) (hbL2_bersOperator μ) 0 := by
  have h0 : (0 : A2 unitDisc) ∈ ball 0 (Real.sqrt (π / 3)) :=
    mem_ball_self (by positivity)
  have hd := hib_chart_strict hμ h0
  rw [show fderiv ℂ (hib_chart μ) 0 = hbL2_bersOperator μ from
    hbL2_chart_fderiv_zero μ hμ] at hd
  exact hd

/-- Exact neighborhood and derivative inputs for the Hilbert fiber argument. -/
theorem hbBridge_chart_local_data (μ : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) :
    HasStrictFDerivAt (hib_chart μ) (hbL2_bersOperator μ) 0 ∧
      ∃ U ∈ 𝓝 (0 : A2 unitDisc), InjOn (hib_chart μ) U := by
  refine ⟨hbBridge_chart_strict_zero μ hμ,
    ball 0 (Real.sqrt (π / 3)), ?_, hbBridge_chart_injOn μ hμ⟩
  exact isOpen_ball.mem_nhds (mem_ball_self (by positivity))

#print axioms hbBridge_chart_injOn
#print axioms hbBridge_chart_strict_zero
#print axioms hbBridge_chart_local_data
end TakhtajanTeo
