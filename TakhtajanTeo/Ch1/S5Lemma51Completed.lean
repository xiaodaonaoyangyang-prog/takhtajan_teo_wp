import TakhtajanTeo.Ch1.S5Lemma51

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **Lemma 5.1** (TT:2272–2276).
- `K` is real-analytic on `𝒯(1)` (in coordinates).
- Under `𝒯(1) ∋ ([μ], z) ↦ 𝗀 = σ_w ∘ 𝗀_μ ∈ S¹\Homeo_qs(S¹)`, with `z = g_μ(w)` and `𝗀 = (g⁻¹ ∘ f)|S¹`,
  `K(𝗀) = log |g'(∞)|`.
- Here `g = λ_w ∘ g_μ ∘ σ_w⁻¹`, `c_w = -1/g_μ(w)` (`fiber_welding`). -/
theorem lemma_5_1 :
    AnalyticOnNhd ℝ (fun x => potentialK (tcCoordInv x)) (tcCoord '' TCurve) ∧
      ∀ (p : T1) (w : ℂ), w ∈ unitDiscExterior →
        potentialK (p, (gMu (Quotient.out p : LinfStarBall) w : ExtPlane)) =
          Real.log ‖derivAtInfty (fun z => lambdaW (-1 / gMu (Quotient.out p : LinfStarBall) w)
            (gMu (Quotient.out p : LinfStarBall) (Function.invFun (sigmaW w) z)))‖ := s5cf_lemma_5_1

end TakhtajanTeo
