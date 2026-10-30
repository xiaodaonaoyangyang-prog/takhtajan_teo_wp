import LiZhongQC.Ch05.S21_UniversalTeichmuller

/-!
# Basic objects of Takhtajan–Teo, Chapter 1 §1.1.1

Shared definitions for the whole skeleton (see `ARCHITECTURE.md`).

* the unit disk `𝔻 = LiZhongQC.unitDisc`, its exterior `𝔻* = LiZhongQC.unitDiscExterior`, the unit circle, and the
  reflection `z ↦ 1/z̄`
* the Banach space `L∞(𝔻*)` of bounded Beltrami differentials on `𝔻*` and its open unit ball `L∞(𝔻*)₁`
* the extensions of `μ ∈ L∞(𝔻*)` used by Model A (reflection (1.1)) and Model B (by zero)
* the hyperbolic density `ρ(z) = 4/(1 - |z|²)²` (1.17)
* the Banach spaces `A∞(𝔻)`, `A∞(𝔻*)`, the space `A₁(𝔻*)`, the subspace `𝓝(𝔻*)` of infinitesimally trivial
  Beltrami differentials, and the space `Ω^{-1,1}(𝔻*)` of bounded harmonic Beltrami differentials

The memoir is cited as `TT:<line>` (lines of `source/TakhtajanTeo2006.md`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate BoundedContinuousFunction Classical

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ### Disks, circle, reflection -/

/-- The unit circle `S¹ = {|z| = 1}` as a subset of `ℂ`. -/
def unitCircle : Set ℂ := {z | ‖z‖ = 1}

/-- The reflection `z ↦ 1/z̄` in the unit circle (TT:342). At `z = 0` Lean's convention `0⁻¹ = 0` gives the junk
value `0`; it is never used there. -/
def refl (z : ℂ) : ℂ := (conj z)⁻¹

/-! ### Bounded Beltrami differentials on `𝔻*` -/

/-- The complex Banach space `L∞(𝔻*)` of bounded Beltrami differentials on `𝔻*` (TT:340): essentially bounded
functions on `𝔻*` modulo null functions.

The function `⇑μ` of an element `μ` is determined only almost everywhere on `𝔻*`; its values off `𝔻*` are arbitrary.
Every use outside `𝔻*` goes through `extA` or `extB`. -/
abbrev LinfStar : Type := Lp ℂ ∞ (volume.restrict unitDiscExterior)

/-- The open unit ball `L∞(𝔻*)₁` of `L∞(𝔻*)` (TT:340). -/
def LinfStarBall : Set LinfStar := ball 0 1

/-- **(1.1)** (TT:342–346). Model A extension of `μ ∈ L∞(𝔻*)` to the plane: `μ` on `𝔻*`, and on `𝔻` the reflection
`μ(z) = \overline{μ(1/z̄)} z²/z̄²`.
- The circle `S¹` is a null set; the value there is `0`.
- At `z = 0` the formula gives `0` (because `z² = 0`), also on a null set. -/
def extA (μ : LinfStar) (z : ℂ) : ℂ :=
  if 1 < ‖z‖ then μ z else if ‖z‖ < 1 then conj (μ (refl z)) * z ^ 2 / conj z ^ 2 else 0

/-- Model B extension of `μ ∈ L∞(𝔻*)` to the plane: `μ` on `𝔻*`, zero outside `𝔻*` (TT:355). -/
def extB (μ : LinfStar) : ℂ → ℂ :=
  unitDiscExterior.indicator μ

/-! ### Hyperbolic density -/

/-- **(1.17)** (TT:1037). The density `ρ(z) = 4/(1 - |z|²)²` of the hyperbolic (Poincaré) metric
`ds² = ρ(z)|dz|²` on `𝔻` and on `𝔻*`. -/
def rho (z : ℂ) : ℝ := 4 / (1 - ‖z‖ ^ 2) ^ 2

/-! ### Spaces of holomorphic quadratic differentials -/

/-- `ψ/(1 - |z|²)²` on `D`, `0` off `D`: the function `φ` represented by the weighted function `ψ = (1 - |z|²)² φ`. -/
def unweight (D : Set ℂ) (ψ : D →ᵇ ℂ) (z : ℂ) : ℂ :=
  if h : z ∈ D then ψ ⟨z, h⟩ / (1 - ‖z‖ ^ 2) ^ 2 else 0

theorem unweight_add (D : Set ℂ) (ψ χ : D →ᵇ ℂ) : unweight D (ψ + χ) = unweight D ψ + unweight D χ := by
  funext z
  by_cases h : z ∈ D
  · simp [unweight, h, add_div]
  · simp [unweight, h]

theorem unweight_smul (D : Set ℂ) (c : ℂ) (ψ : D →ᵇ ℂ) : unweight D (c • ψ) = c • unweight D ψ := by
  funext z
  by_cases h : z ∈ D
  · simp [unweight, h, mul_div_assoc]
  · simp [unweight, h]

/-- The complex Banach space `A∞(D)` (TT:363, TT:477) for `D = 𝔻` or `D = 𝔻*`: holomorphic functions `φ` on `D` with
`‖φ‖∞ = sup_{z ∈ D} |(1 - |z|²)² φ(z)| < ∞`.

It is realized isometrically as the subspace of bounded continuous functions `ψ = (1 - |z|²)² φ` on `D` such that
`φ = ψ/(1 - |z|²)²` is holomorphic on `D`. The sup norm of `ψ` is then exactly `‖φ‖∞`. -/
def AInf (D : Set ℂ) : Submodule ℂ (D →ᵇ ℂ) where
  carrier := {ψ | DifferentiableOn ℂ (unweight D ψ) D}
  add_mem' {ψ χ} hψ hχ := by
    change DifferentiableOn ℂ (unweight D (ψ + χ)) D
    rw [unweight_add]
    exact hψ.add hχ
  zero_mem' := by
    change DifferentiableOn ℂ (unweight D 0) D
    have : unweight D 0 = 0 := by
      funext z
      by_cases h : z ∈ D <;> simp [unweight, h]
    rw [this]
    exact differentiableOn_const 0
  smul_mem' c {ψ} hψ := by
    change DifferentiableOn ℂ (unweight D (c • ψ)) D
    rw [unweight_smul]
    exact hψ.const_smul c

/-- The holomorphic function `φ` on `D` represented by an element of `A∞(D)` (`0` off `D`). -/
def AInf.toFun {D : Set ℂ} (φ : AInf D) : ℂ → ℂ := unweight D φ.1

/-- The space `A₁(𝔻*)` of integrable holomorphic functions on `𝔻*` (TT:357): `∬_{𝔻*} |φ| d²z < ∞`.

[CORRECTION 2026-10-25] Elements of `A₁(𝔻*)` are integrable holomorphic quadratic differentials on `𝔻*`, so they are
regular at `∞`: `φ(z) = O(|z|⁻⁴)`. The third conjunct records this. Without it `ζ⁻³` (integrable on `𝔻*`, not a
quadratic differential regular at `∞`) would belong to `A₁(𝔻*)`, and `ker_D0Phi` would fail (found by 下属5). -/
def AOneStar : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ unitDiscExterior ∧ IntegrableOn φ unitDiscExterior ∧
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖φ z‖ ≤ C / ‖z‖ ^ 4}

/-- The set of infinitesimally trivial Beltrami differentials (TT:353): `μ ∈ L∞(𝔻*)` with `∬_{𝔻*} μ φ d²z = 0` for all
`φ ∈ A₁(𝔻*)`. -/
def trivialBeltramiSet : Set LinfStar :=
  {μ | ∀ φ ∈ AOneStar, ∫ z in unitDiscExterior, μ z * φ z = 0}

/-- The subspace `𝓝(𝔻*)` of infinitesimally trivial Beltrami differentials (TT:351–353), the kernel of `D₀Φ`.
- The defining set `trivialBeltramiSet` is a linear subspace, since `μ φ` is integrable for `μ ∈ L∞`, `φ ∈ A₁`.
- The subspace is written as its span, so that no closure proof enters the definition.
- `mem_trivialBeltrami_iff` states that the span adds nothing. -/
def trivialBeltrami : Submodule ℂ LinfStar := Submodule.span ℂ trivialBeltramiSet

/-- The set of bounded harmonic Beltrami differentials on `𝔻*` (TT:361): `μ = (1 - |z|²)² φ̄` with `φ ∈ A∞(𝔻*)`. -/
def harmonicBeltramiSet : Set LinfStar :=
  {μ | ∃ φ : AInf unitDiscExterior, ∀ᵐ z ∂(volume.restrict unitDiscExterior),
    μ z = (1 - ‖z‖ ^ 2) ^ 2 * conj (AInf.toFun φ z)}

/-- The Banach space `Ω^{-1,1}(𝔻*)` of bounded harmonic Beltrami differentials on `𝔻*` (TT:361), the model space of
`T(1)`. It is written as the span of `harmonicBeltramiSet` (a linear subspace, since `φ ↦ (1 - |z|²)² φ̄` is
conjugate-linear); `mem_harmonicBeltrami_iff` states that the span adds nothing. -/
def harmonicBeltrami : Submodule ℂ LinfStar := Submodule.span ℂ harmonicBeltramiSet

/-! ### Converting functions to elements -/

/-- The element of `L∞(𝔻*)` represented by `f : ℂ → ℂ` (restricted to `𝔻*`).
- If `f` is not essentially bounded and a.e. strongly measurable on `𝔻*`, the junk value is `0`.
- Every use comes with a theorem that `f` is admissible. -/
def toLinf (f : ℂ → ℂ) : LinfStar :=
  if h : MemLp f ∞ (volume.restrict unitDiscExterior) then MemLp.toLp f h else 0

/-- The element of `A∞(D)` representing the holomorphic function `φ` on `D`, i.e. with `toFun = φ` on `D`.
- The element is unique when it exists.
- If no element exists (`φ` not holomorphic on `D`, or `(1 - |z|²)² φ` unbounded), the junk value is `0`. -/
def toAInf (D : Set ℂ) (φ : ℂ → ℂ) : AInf D :=
  if h : ∃ ψ : AInf D, ∀ z ∈ D, AInf.toFun ψ z = φ z then h.choose else 0

/-- The span in `trivialBeltrami` adds nothing: `𝓝(𝔻*)` is exactly the set of `μ` annihilating `A₁(𝔻*)`. -/
theorem mem_trivialBeltrami_iff (μ : LinfStar) : μ ∈ trivialBeltrami ↔ μ ∈ trivialBeltramiSet := by
  constructor
  · intro h
    change μ ∈ Submodule.span ℂ trivialBeltramiSet at h
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro φ hφ
      calc
        _ = ∫ z in unitDiscExterior, (0 : ℂ) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_zero (E := ℂ) (p := ∞)
            (μ := volume.restrict unitDiscExterior)] with z hz
          change (0 : LinfStar) z = 0 at hz
          change (0 : LinfStar) z * φ z = 0
          rw [hz, zero_mul]
        _ = 0 := integral_zero _ _ 
    | add x y hx hy hpx hpy =>
      intro φ hφ
      have hi₁ : IntegrableOn (fun z => x z * φ z) unitDiscExterior :=
        hφ.2.1.mul_of_top_right (Lp.memLp x)
      have hi₂ : IntegrableOn (fun z => y z * φ z) unitDiscExterior :=
        hφ.2.1.mul_of_top_right (Lp.memLp y)
      calc
        _ = ∫ z in unitDiscExterior, x z * φ z + y z * φ z := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_add x y] with z hz
          simp only [hz, Pi.add_apply, add_mul]
        _ = 0 := by rw [integral_add hi₁ hi₂, hpx φ hφ, hpy φ hφ, add_zero]
    | smul a x hx hpx =>
      intro φ hφ
      calc
        _ = ∫ z in unitDiscExterior, a * (x z * φ z) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_smul a x] with z hz
          simp only [hz, Pi.smul_apply, smul_eq_mul, mul_assoc]
        _ = 0 := by rw [integral_const_mul, hpx φ hφ, mul_zero]
  · intro h
    exact Submodule.subset_span h

/-- The span in `harmonicBeltrami` adds nothing: `Ω^{-1,1}(𝔻*)` is exactly the set of `(1 - |z|²)² φ̄`,
`φ ∈ A∞(𝔻*)`. -/
theorem mem_harmonicBeltrami_iff (μ : LinfStar) : μ ∈ harmonicBeltrami ↔ μ ∈ harmonicBeltramiSet := by
  constructor
  · intro h
    change μ ∈ Submodule.span ℂ harmonicBeltramiSet at h
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, ?_⟩
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := ∞)
        (μ := volume.restrict unitDiscExterior)] with z hz
      change (0 : LinfStar) z = 0 at hz
      rw [hz]
      simp [AInf.toFun, unweight]
    | add x y hx hy hpx hpy =>
      obtain ⟨φ, hφ⟩ := hpx
      obtain ⟨ψ, hψ⟩ := hpy
      refine ⟨φ + ψ, ?_⟩
      filter_upwards [Lp.coeFn_add x y, hφ, hψ] with z hz hφz hψz
      simp only [hz, Pi.add_apply, hφz, hψz, AInf.toFun, Submodule.coe_add,
        unweight_add, Pi.add_apply, map_add]
      ring
    | smul a x hx hpx =>
      obtain ⟨φ, hφ⟩ := hpx
      refine ⟨conj a • φ, ?_⟩
      filter_upwards [Lp.coeFn_smul a x, hφ] with z hz hφz
      simp only [hz, Pi.smul_apply, smul_eq_mul, hφz, AInf.toFun,
        Submodule.coe_smul, unweight_smul, Pi.smul_apply, smul_eq_mul,
        map_mul, starRingEnd_self_apply]
      ring
  · intro h
    exact Submodule.subset_span h

end TakhtajanTeo
