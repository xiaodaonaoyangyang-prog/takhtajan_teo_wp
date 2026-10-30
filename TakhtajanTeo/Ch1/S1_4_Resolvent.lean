import TakhtajanTeo.Ch1.S1_4_ResolventCore
import TakhtajanTeo.Ch1.ResolventWeakToStrong
import TakhtajanTeo.Ch1.ResolventExteriorEquation
import TakhtajanTeo.Ch1.ResolventGammaPointwise

/-!
# Chapter 1, §1.4 — Resolvent kernel: RK3 and the automorphic kernel

The definitions and the proved properties RK1, RK2, RK4 are in `S1_4_ResolventCore` (split off to avoid an import cycle with the modules proving RK3). This module assembles RK3 from `RK3_disc` and the exterior results, and proves the automorphic-kernel theorem (1.20).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **RK3** (TT:1112–1124), on `D = 𝔻` and on `D = 𝔻*`.
- If `g ∈ BC^∞(D)`, the integral `G(g)(z)` converges absolutely for every `z ∈ D`.
- `f = G(g)` lies in `BC^∞(D)` and solves `2(Δ₀ + ½) f = g`.
- Conversely, if `f ∈ BC^∞(D)` and `g = 2(Δ₀ + ½) f ∈ BC^∞(D)`, then `f = G(g)`. -/
theorem RK3 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) :
    (∀ g ∈ BCinf D, (∀ z ∈ D, Integrable (fun w => (resolventKernel z w : ℂ) * g w * rho w) (volume.restrict D)) ∧
        resolventOp D g ∈ BCinf D ∧
        ∀ z ∈ D, 2 * (laplace0 (resolventOp D g) z + (1 / 2) * resolventOp D g z) = g z) ∧
      ∀ f ∈ BCinf D, (fun z => 2 * (laplace0 f z + (1 / 2) * f z)) ∈ BCinf D →
        ∀ z ∈ D, f z = resolventOp D (fun z => 2 * (laplace0 f z + (1 / 2) * f z)) z := by
  rcases hD with rfl | rfl
  · exact RK3_disc
  · exact ⟨fun g hg => ⟨fun z hz => RK3_absolute_convergence (Or.inr rfl) hg hz,
      RK3_output_BCinf_exterior hg, RK3_output_equation_exterior hg⟩,
      fun f hf hg => RK3_inverse_exterior hf hg⟩

/-- (TT:1142–1148) For a cofinite group the series (1.20) converges (for `z` not in the orbit of `w`), and `G_Γ`
enjoys RK1–RK4 on `Γ\𝔻*`:
- symmetry and `Γ`-invariance in each variable;
- positivity;
- `∬_{Γ\𝔻*} G_Γ(z, w) ρ(w) d²w = 1`. -/
theorem resolventKernelGamma_spec {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    (∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, (∀ g ∈ Γ, mob g w ≠ z) →
        Summable fun γ : (fun g : SL2C => mob g) '' (Γ : Set SL2C) => resolventKernel z ((γ : ℂ → ℂ) w)) ∧
      (∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, resolventKernelGamma Γ z w = resolventKernelGamma Γ w z) ∧
      (∀ g ∈ Γ, ∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior,
        resolventKernelGamma Γ (mob g z) w = resolventKernelGamma Γ z w) ∧
      (∀ z ∈ unitDiscExterior, ∀ w ∈ unitDiscExterior, (∀ g ∈ Γ, mob g w ≠ z) → 0 < resolventKernelGamma Γ z w) ∧
      ∀ z ∈ unitDiscExterior, quotientIntegral Γ (fun w => resolventKernelGamma Γ z w * rho w) = 1 := by
  exact ⟨fun z hz w hw hoff => gam_series_summable hΓ.1 hz hw hoff,
    fun z hz w hw => gam_clause2 hΓ.1 hz hw,
    fun g hg z hz w hw => gam_clause3 hΓ.1 hg hz hw,
    fun z hz w hw hoff => gam_kernel_strict_pos hΓ.1 hz hw hoff,
    fun z hz => gam_quotient_kernel_mass hΓ.1 hz⟩

end TakhtajanTeo
