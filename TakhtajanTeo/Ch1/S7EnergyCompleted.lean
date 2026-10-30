import TakhtajanTeo.Ch1.S7ResolventEnergy

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Proposition 7.2** (TT:2762–2768). For `μ ∈ H^{-1,1}(𝔻*)` and `ν ∈ Ω^{-1,1}(𝔻*)`:
- `Q̇(μ)[ν] ∈ L²(𝔻*, ρ d²z)`;
- `‖Q̇(μ)[ν]‖₂² = ‖μν̄‖₂² - (μν̄, G(μν̄))`. -/
theorem prop_7_2 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {ν : LinfStar} (hν : ν ∈ harmonicBeltrami) :
    normL2 unitDiscExterior (Qdot (toLinf μ) ν) < ∞ ∧
      l2Inner (Qdot (toLinf μ) ν) (Qdot (toLinf μ) ν) =
        l2Inner (fun z => μ z * conj (ν z)) (fun z => μ z * conj (ν z)) -
          l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => μ z * conj (ν z)) := s7re_prop_7_2 hμ hν

end TakhtajanTeo
