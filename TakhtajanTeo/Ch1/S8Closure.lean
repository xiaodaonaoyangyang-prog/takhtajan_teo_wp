import TakhtajanTeo.Ch1.S19Rep
import TakhtajanTeo.Ch1.S8Lemma84Conditional

/-! # Closure of `petersson_average`, `lemma_8_2`, `lemma_8_4` (Program G, 2026-10-29)

The conditional proofs (`S8PeterssonConditional`, `S8Lemma84Conditional`) instantiated with the now-proved
`lemma_1_9` (`s19f_lemma_1_9`, `S19Rep`). The originals are relocated here from `S8_FiniteDimensional`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- (TT:3181) The Petersson product as an average (Lemma 1.9 in the model `𝔻`): for `μ, ν ∈ Ω^{-1,1}(𝔻, Γ)`,
`(μ, ν)_Γ = lim_{r → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_{𝔻_r} μ ν̄ ρ d²z = lim_{r → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 μ_r ν̄_r ρ d²z`. -/
theorem s8z_petersson_average {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (truncR r μ) (truncR r ν)) (𝓝[<] 1)
      (𝓝 (innerGamma Γ μ ν)) :=
  s8c_petersson_average hΓ (fun hm hb ha => s19f_lemma_1_9 hΓ hm hb ha) hμ hν hμΓ hνΓ

/-- **Lemma 8.2** (TT:3266–3270). For `μ, ν ∈ Ω^{-1,1}(𝔻, Γ)`:
`(μ, ν)_Γ = lim_{r → 1⁻} lim_{s → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 P(μ_s) \overline{P(ν_r)} ρ d²z`. -/
theorem s8z_lemma_8_2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
        (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν)))
      (𝓝[<] 1) (𝓝 (innerGamma Γ μ ν)) :=
  s8c_lemma_8_2 hΓ (fun hm hb ha => s19f_lemma_1_9 hΓ hm hb ha) hμ hν hμΓ hνΓ

/-- **Lemma 8.4** (TT:3298–3302). For `μ, ν, κ ∈ Ω^{-1,1}(𝔻, Γ)` with `‖κ‖∞` small enough:
`g_{μν̄}(κ) = lim_{r → 1⁻} lim_{s → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 P(R(P(μ_s), κ)) \overline{P(R(P(ν_r), κ))} ρ d²z`.

[CORRECTION 2026-10-25] `δ` is chosen before `κ`. The skeleton quantified `∃ δ` after fixing `κ`, which made the
statement vacuous for `κ ≢ 0` (下属1). -/
theorem s8z_lemma_8_4 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∃ δ > 0, ∀ κ : ℂ → ℂ, IsHarmonicD κ → IsGammaInvD Γ κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ) →
      Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
          (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
            (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ)))
        (𝓝[<] 1) (𝓝 (gGamma Γ μ ν κ)) :=
  s8w_lemma_8_4 hΓ (fun hm hb ha => s19f_lemma_1_9 hΓ hm hb ha) hμ hν hμΓ hνΓ

/-- (TT:3181) The Petersson product as an average (Lemma 1.9 in the model `𝔻`): for `μ, ν ∈ Ω^{-1,1}(𝔻, Γ)`,
`(μ, ν)_Γ = lim_{r → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_{𝔻_r} μ ν̄ ρ d²z = lim_{r → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 μ_r ν̄_r ρ d²z`. -/
theorem petersson_average {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (truncR r μ) (truncR r ν)) (𝓝[<] 1)
      (𝓝 (innerGamma Γ μ ν)) :=
  s8z_petersson_average hΓ hμ hν hμΓ hνΓ

/-- **Lemma 8.2** (TT:3266–3270). For `μ, ν ∈ Ω^{-1,1}(𝔻, Γ)`:
`(μ, ν)_Γ = lim_{r → 1⁻} lim_{s → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 P(μ_s) \overline{P(ν_r)} ρ d²z`. -/
theorem lemma_8_2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
        (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (truncR s μ)) (harmonicProjD (truncR r ν)))
      (𝓝[<] 1) (𝓝 (innerGamma Γ μ ν)) :=
  s8z_lemma_8_2 hΓ hμ hν hμΓ hνΓ

/-- **Lemma 8.4** (TT:3298–3302). For `μ, ν, κ ∈ Ω^{-1,1}(𝔻, Γ)` with `‖κ‖∞` small enough:
`g_{μν̄}(κ) = lim_{r → 1⁻} lim_{s → 1⁻} (A(Γ\𝔻)/A(𝔻_r)) ∬_𝔻 P(R(P(μ_s), κ)) \overline{P(R(P(ν_r), κ))} ρ d²z`.

[CORRECTION 2026-10-25] `δ` is chosen before `κ`. The skeleton quantified `∃ δ` after fixing `κ`, which made the
statement vacuous for `κ ≢ 0` (下属1). -/
theorem lemma_8_4 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∃ δ > 0, ∀ κ : ℂ → ℂ, IsHarmonicD κ → IsGammaInvD Γ κ → (∀ z ∈ unitDisc, ‖κ z‖ < δ) →
      Tendsto (fun r : ℝ => limUnder (𝓝[<] (1 : ℝ)) fun s : ℝ =>
          (hypAreaD Γ / hypAreaDiscR r : ℂ) * l2InnerD (harmonicProjD (RnmD (harmonicProjD (truncR s μ)) κ))
            (harmonicProjD (RnmD (harmonicProjD (truncR r ν)) κ)))
        (𝓝[<] 1) (𝓝 (gGamma Γ μ ν κ)) :=
  s8z_lemma_8_4 hΓ hμ hν hμΓ hνΓ

end TakhtajanTeo
