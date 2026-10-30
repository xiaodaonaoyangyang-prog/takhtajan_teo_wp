import TakhtajanTeo.Ch1.ComponentTC

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Theorem 2.10** (TT:1772–1778). For `μ, ν ∈ 𝒪(𝔻*)₁`:
- the sets `h̃_μ(V_μ ∩ V_ν)` and `h̃_ν(V_μ ∩ V_ν)` are open in `A₂(𝔻)`;
- `h̃_μν = h̃_μ ∘ h̃_ν⁻¹` is biholomorphic between them: holomorphic in the Hilbert space `A₂(𝔻)`, with holomorphic
  inverse `h̃_νμ`. -/
theorem thm_2_10 (μ ν : LinfStarBall) (hμ : (μ : LinfStar) ∈ groupO) (hν : (ν : LinfStar) ∈ groupO) :
    IsOpen (hilbertChart μ '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      IsOpen (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      DifferentiableOn ℂ (fun φ => hilbertChart μ (bersChartInv ν (A2toAInf φ)))
        (hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) ∧
      DifferentiableOn ℂ (fun φ => hilbertChart ν (bersChartInv μ (A2toAInf φ)))
        (hilbertChart μ '' (hilbertChartDomain μ ∩ hilbertChartDomain ν)) := by
  exact ctc_thm_2_10 μ ν hμ hν

/-- (TT:1354) In the Hilbert manifold topology `T(1)` is a disjoint union of uncountably many components. -/
theorem componentT_uncountable : ¬ (range componentT).Countable := by
  exact ctb_componentT_uncountable

end TakhtajanTeo
