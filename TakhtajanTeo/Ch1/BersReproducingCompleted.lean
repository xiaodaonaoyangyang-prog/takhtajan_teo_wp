import TakhtajanTeo.Ch1.Eq22ReproducingFinal
import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.HilbertReflectionProduct

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- **(2.2)** (TT:1526–1529), the Bers reproducing formula [Ber66]. Let `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)`, and let `h` be a
q.c. reflection in `∂Ω`. For `q` holomorphic on `Ω` with `∬_Ω |q|² ρ₁⁻¹ d²z < ∞`, where `ρ₁` is the hyperbolic
density of `Ω` (`ρ₁ = λ_Ω²`, `λ_Ω = LiZhongQC.poincareDensity Ω`), and `z ∈ Ω`:
`q(z) = -(3/π) ∬_{Ω*} q(h(u)) (u - h(u))² h_ū(u)/(u - z)⁴ d²u`. -/
theorem eq_2_2 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc))
    (hq2 : ∫⁻ z in fsans μ '' unitDisc, (‖q z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (poincareDensity (fsans μ '' unitDisc) z ^ 2)⁻¹ < ∞)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    q z = -(3 / π) * ∫ u in gsans μ '' unitDiscExterior, q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4 := by
  exact eq22_reproducing hμ hh hq hq2 hz

/-- **(2.3)** (TT:1566–1570), the Earle–Nag estimate [EN88]. For the conformally natural q.c. reflection `h` in
`∂Ω` (attached to the Douady–Earle extension), there is `C` with
`1/C ≤ |z - h(z)|⁴ ρ₁(h(z)) ρ₂(z) ≤ C` on `Ω*`, where `ρ₁`, `ρ₂` are the hyperbolic densities of `Ω`, `Ω*`.
- The memoir adds that `C` depends only on `‖μ‖∞`.
- Stated here: such a reflection and constant exist.

[CORRECTION 2026-10-25] `ρ₂ = λ_{Ω*}²` with `λ_{Ω*}` computed in the sphere chart `1/z`
(`poincareDensityNearInfty`); `LiZhongQC.poincareDensity` of `Ω*` is junk `0`. -/
theorem eq_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ h : ℂ → ℂ, IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h ∧ ∃ C > 0,
      ∀ z ∈ gsans μ '' unitDiscExterior,
        1 / C ≤ ‖z - h z‖ ^ 4 * poincareDensity (fsans μ '' unitDisc) (h z) ^ 2 *
          poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 ∧
        ‖z - h z‖ ^ 4 * poincareDensity (fsans μ '' unitDisc) (h z) ^ 2 *
          poincareDensityNearInfty (gsans μ '' unitDiscExterior) z ^ 2 ≤ C := by
  obtain ⟨h, C0, hC0, hh, hC1, hraw⟩ := hc6_chosen_raw_coefficient hμ
  obtain ⟨C, hC, hproduct⟩ := hr6_reflection_density_product hμ hh
  exact ⟨h, hh, C, hC, hproduct⟩

end TakhtajanTeo
