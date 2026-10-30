import TakhtajanTeo.Ch2.S1_LiouvilleWellDefined

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- (TT:3780) `S₁` is well defined on `T₀(1)`: both integrals converge (Theorem 1.12) and `𝗀_μ'(∞) ≠ 0`. -/
theorem liouvilleS1_wellDefined {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    IntegrableOn (fun z => ‖preSchwarzian (fsans μ) z‖ ^ 2) unitDisc ∧
      IntegrableOn (fun z => ‖preSchwarzian (gsans μ) z‖ ^ 2) unitDiscExterior ∧ derivAtInfty (gsans μ) ≠ 0 := by
  exact ls1wd_liouvilleS1_wellDefined hp

end TakhtajanTeo.Ch2
