import TakhtajanTeo.Ch1.S7Polarization

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Corollary 7.3** (TT:2812–2815). For `μ, ν ∈ H^{-1,1}(𝔻*)` and `κ ∈ Ω^{-1,1}(𝔻*)`:
`(Q̇(μ)[κ], Q̇(ν)[κ]) = (μκ̄, νκ̄) - (μκ̄, G(νκ̄))`. -/
theorem cor_7_3 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    l2Inner (Qdot (toLinf μ) κ) (Qdot (toLinf ν) κ) =
      l2Inner (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) -
        l2Inner (fun z => μ z * conj (κ z)) (resolventStar fun z => ν z * conj (κ z)) := s7pol_cor_7_3 hμ hν hκ

end TakhtajanTeo
