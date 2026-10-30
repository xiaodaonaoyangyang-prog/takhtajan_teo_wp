import TakhtajanTeo.Ch1.S7FirstVariation
import TakhtajanTeo.Ch1.S7QOrthogonality
import TakhtajanTeo.Ch1.S7_Curvature

/-!
# Program G, F1 interface: `thm_7_4` and `cor_7_5` (下属1)

* `s7g_first_variation` (proved in `Ch1/S7FirstVariation`): real differentiability of `ε ↦ g_{μν̄}(εκ)` at
  `0`, with `∂_ε g = \overline{(Q̇(ν)[κ], μ)}`.
* `s7g_thm_7_4`: the statement of `thm_7_4`, from the stub and `s7qo_Qdot` (orthogonality, both orders).
* `s7g_cor_7_5`: the statement of `cor_7_5`, from `s7g_thm_7_4`, `Lambda_smul` and `Lambda_mem_harmonic`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Prefixed copy of `thm_7_4`. -/
theorem s7g_thm_7_4 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    DifferentiableAt ℝ (fun ε : ℂ => gWP μ ν (ε • κ)) 0 ∧ dz (fun ε => gWP μ ν (ε • κ)) 0 = 0 ∧
      l2Inner (Qdot (toLinf μ) κ) ν = 0 := by
  obtain ⟨hd, hdz⟩ := s7g_first_variation hμ hν hκ
  refine ⟨hd, ?_, s7qo_Qdot hμ hν hκ⟩
  rw [hdz, s7qo_Qdot hν hμ hκ, map_zero]

/-- Prefixed copy of `cor_7_5`. -/
theorem s7g_cor_7_5 {l m n : ℕ} (hl : 2 ≤ l) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    DifferentiableAt ℝ (fun t : ℂ => gWPChart (basisMu m) (basisMu n) (t • fderiv ℂ bersPhi 0 (toLinf (basisMu l))))
        0 ∧
      dz (fun t => gWPChart (basisMu m) (basisMu n) (t • fderiv ℂ bersPhi 0 (toLinf (basisMu l)))) 0 = 0 := by
  -- `hl` is not needed: `Lambda X` is harmonic for every `X`, so the statement holds for all `l`.
  have _hl := hl
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 2 := ⟨n - 2, by omega⟩
  set X := fderiv ℂ bersPhi 0 (toLinf (basisMu l)) with hX
  have he : (fun t : ℂ => gWPChart (basisMu (a + 2)) (basisMu (b + 2)) (t • X)) =
      fun t : ℂ => gWP (basisMu (a + 2)) (basisMu (b + 2)) (t • Lambda X) := by
    funext t
    change gWP _ _ (Lambda (t • X)) = _
    rw [Lambda_smul]
  have h := s7g_thm_7_4 (basisMu_mem_harmonicL2 a) (basisMu_mem_harmonicL2 b) (Lambda_mem_harmonic X)
  rw [he]
  exact ⟨h.1, h.2.1⟩

/-- **Theorem 7.4** (TT:2818–2842). For `μ, ν ∈ H^{-1,1}(𝔻*)` and `κ ∈ Ω^{-1,1}(𝔻*)`:
`∂/∂ε g_{μν̄}(εκ)|_{ε=0} = 0`. (In the proof: `(Q̇(μ)[κ], ν) = 0`.)

[CORRECTION 2026-10-28, user-approved] Clause 1 now also asserts that `ε ↦ g_{μν̄}(εκ)` is ℝ-differentiable at `0`;
without it `dz … 0 = 0` holds by the junk value `fderiv = 0` (the memoir differentiates under the integral sign). -/
theorem thm_7_4 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    DifferentiableAt ℝ (fun ε : ℂ => gWP μ ν (ε • κ)) 0 ∧ dz (fun ε => gWP μ ν (ε • κ)) 0 = 0 ∧
      l2Inner (Qdot (toLinf μ) κ) ν = 0 := by
  exact s7g_thm_7_4 hμ hν hκ

/-- **Corollary 7.5** (TT:2852–2866).
- The Weil–Petersson metric is Kähler on the Hilbert manifold `T(1)`.
- The Bers coordinates `ε_n` (dual to `μ_n`) are geodesic at the origin: `∂g_{m n̄}/∂ε_l(0) = 0`.
- Here `g_{m n̄}` is a function on `V₀` in Bers coordinates (`gWPChart`), and `∂/∂ε_l` is the derivative in the
  direction `D₀β(μ_l)`.

[CORRECTION 2026-10-28, user-approved] The statement now also asserts that `t ↦ g_{m n̄}(t D₀β(μ_l))` is
ℝ-differentiable at `0`; without it `dz … 0 = 0` holds by the junk value `fderiv = 0`. -/
theorem cor_7_5 {l m n : ℕ} (hl : 2 ≤ l) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    DifferentiableAt ℝ (fun t : ℂ => gWPChart (basisMu m) (basisMu n) (t • fderiv ℂ bersPhi 0 (toLinf (basisMu l))))
        0 ∧
      dz (fun t => gWPChart (basisMu m) (basisMu n) (t • fderiv ℂ bersPhi 0 (toLinf (basisMu l)))) 0 = 0 := by
  exact s7g_cor_7_5 hl hm hn

end TakhtajanTeo
