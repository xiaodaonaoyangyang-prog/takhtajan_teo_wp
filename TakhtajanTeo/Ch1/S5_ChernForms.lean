import TakhtajanTeo.Ch1.S4_Metrics
import TakhtajanTeo.Ch1.HarmonicResolventTransport
import TakhtajanTeo.Ch1.QCVariationBergman
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Chapter 1, §5 — Characteristic forms of the universal Teichmüller curve (TT:2218–2546)

* holomorphic coordinates on `𝒯(1)`, the hyperbolic norm `‖z²∂_z‖²` on the vertical bundle `V`, the curvature
  `Θ = ∂̄∂ log ‖z²∂_z‖²`, `c₁(V) = (i/2π) Θ`, the function `K`
* §5.1 Lemma 5.1, Theorem 5.3 (`c₁(V) = -(2/π) ω_VK`), Lemma 5.4 (right invariance), Lemma 5.5 (5.2), (5.3)–(5.4)
* §5.2 Proposition 5.7, Lemma 5.8
* §5.3 the Mumford–Morita–Miller forms `κ_n` (5.1), Theorem 5.10, Corollary 5.11

**Modelling.**
- *Coordinates.* `𝒯(1) ⊂ T(1) × ℂ̄` has holomorphic coordinates `([μ], z) ↦ (β([μ]), ζ = 1/z) ∈ A∞(𝔻) × ℂ`
  (`tcCoord`). The fiber coordinate is taken in `ℂ̄ \ {0} ≅ ℂ` via `z ↦ 1/z`, as in the memoir (footnote, TT:586).
  The holomorphic section `-z²∂_z` becomes `∂_ζ`.
- *Forms.* A real `(1,1)`-form is determined by its Hermitian form. `Θ(X, Ȳ)` is the polarization of
  `X ↦ -∂_t∂_{t̄} log ‖z²∂_z‖²(p + tX)`, computed in coordinates (since `∂̄∂ = -∂∂̄`).
- *Velling–Kirillov metric.* At the origin `(0, ∞)`, a coordinate vector `(φ, c) ∈ A∞(𝔻) × ℂ` corresponds to
  `v = Σ_{n ≥ 1} c_n e^{inθ} d/dθ`:
  - `φ = i Σ_{n ≥ 2} (n³ - n) c_n z^{n-2}` (TS2);
  - `i c₁ = c + ḟ''(0)/2` along the real line `s ↦ s(φ, c)`, where `ḟ''(0) = ∂_s (fB (sΛφ))''(0)`, `s ∈ ℝ` (TT:2351,
    convention `ḟ = u₊`); the norm averages the directions `X`, `iX` as in (5.4).
    `c` is the vertical part (`∂_ζ = -z²∂_z` at `z = ∞`, TV2; the curve `σ_{1/(tc)}`). The second term is the `c₁` of
    the coordinate line `([tΛφ], ∞)`.
  - **[CORRECTION 2026-10-28, user-approved]** Formerly `|c₁| = |c|`, by TT's Lemma 1.5 (`w^μ(∞) = ∞`). That holds
    only for the `f''(0) = 0` normalization. In Model B, `w^μ(∞) = −2/(f^μ)''(0)` (`lemma_1_5_fB_infty`), and
    `ḟ''(0) ≠ 0` for some harmonic `μ` (first variation, `collaboration/下属2/LEMMA15_PROPOSAL.md` §2).

  At other points the metric is transported by right translations of `𝒯(1)` (TT:2124), in coordinates.
- *`κ_n`.* `π_*(c₁(V)^{n+1})` is defined at the origin of `T(1)` by integrating `Θ^{n+1}` over the fiber
  `π⁻¹(0) = 𝔻*` (TT:2515), with the horizontal lifts `τ_μ` (TV1).
  - Convention: `θ^m(X₁, Ȳ₁, …, X_m, Ȳ_m) = m! det(θ(X_i, Ȳ_j))`.
  - `dz ∧ dz̄ = -2i d²z`.
  - With these, the memoir's constant `iⁿ (n+1)!/(2π)^{n+1}` in Theorem 5.10 is reproduced.

  The right-invariance of `κ_n` (Theorem 5.10, first clause) follows from Lemma 5.4. `κ_n` is defined at the origin
  only, so that clause is not stated separately.

**Not stated** (recorded):
- The Hilbert manifold structure of `𝒯(1)` (TT:2228) is used only through `T(1)`; that `𝒯₀(1)` is a topological group
  is Appendix A.
- Remark 5.2 (TT:2286) identifies `|g'(∞)|` with the capacity of `g(S¹)`; capacity is not defined in the project.
- Remarks 5.6, 5.9, 5.12, 5.13 (TT:2394, 2500, 2544, 2546) are citations and comparisons.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Coordinates and forms on `𝒯(1)` -/

/-- Coordinates on `𝒯(1)`: `([μ], z) ↦ (β([μ]), 1/z)`, with the welding normalization (not holomorphic, see
`tcCoordH`, [CORRECTION 2026-10-28, Program G]). -/
def tcCoord (q : T1 × ExtPlane) : AInf unitDisc × ℂ := (bers q.1, finPart (inversion q.2))

/-- The inverse of the coordinate map on `𝒯(1)`. -/
def tcCoordInv : AInf unitDisc × ℂ → T1 × ExtPlane := Function.invFunOn tcCoord TCurve

/-- The holomorphic coordinates of the memoir on `𝒯(1)` (TT:568, TT:586, Model B with `f''(0) = 0`, TT:355–363):
`([μ], z) ↦ (β([μ]), 1/z_mem)`, `z_mem = λ_c(z) = z/(cz + 1)`, `c = (f^μ)''(0)/2`, i.e. `1/z_mem = 1/z + c`.
- **[CORRECTION 2026-10-28, Program G]** `tcCoord` uses `1/z` with the welding normalization `w(p_μ) = ∞`
  (`IsNormalizedB`). That normalization depends on `μ̄`, so `tcCoord` is not a holomorphic chart, and its right
  translations are not ℂ-differentiable (DEFECT G1). In the `s = 1/z` coordinate, the memoir's renormalization `λ_c` is
  the translation `s ↦ s + c`. It is always defined, even when `λ_c ∘ f^μ` has a pole in `𝔻` (W2-01). -/
def tcCoordH (q : T1 × ExtPlane) : AInf unitDisc × ℂ :=
  (bers q.1, finPart (inversion q.2) + deriv (deriv (fB (Quotient.out q.1 : LinfStarBall))) 0 / 2)

/-- The inverse of the holomorphic coordinate map on `𝒯(1)`. -/
def tcCoordHInv : AInf unitDisc × ℂ → T1 × ExtPlane := Function.invFunOn tcCoordH TCurve

-- `tcCoord_chart` moved to `Ch1/TcChart.lean` (2026-10-28).

/-- The coordinate expression `coord ∘ F ∘ coord⁻¹` of a self-map of `𝒯(1)`, in the holomorphic coordinates
`tcCoordH`. -/
def tcCoordExpr (F : T1 × ExtPlane → T1 × ExtPlane) : AInf unitDisc × ℂ → AInf unitDisc × ℂ :=
  tcCoordH ∘ F ∘ tcCoordHInv

/-- The Levi form `X ↦ ∂_t ∂_{t̄} F(q + tX)|_{t=0}` of a real function on `𝒯(1)`, in the holomorphic coordinates
`tcCoordH`. -/
def leviTC (F : T1 × ExtPlane → ℝ) (q : T1 × ExtPlane) (X : AInf unitDisc × ℂ) : ℝ :=
  (dz (dzbar fun t : ℂ => (F (tcCoordHInv (tcCoordH q + t • X)) : ℂ)) 0).re

/-- The Hermitian form `h(X, Y)` (linear in `X`, conjugate linear in `Y`) with `h(X, X) = N(X)`, by polarization. -/
def polarize {V : Type*} [AddCommGroup V] [Module ℂ V] (N : V → ℝ) (X Y : V) : ℂ :=
  (1 / 4) * ((N (X + Y) : ℂ) - N (X - Y) + I * N (X + I • Y) - I * N (X - I • Y))

/-- The function `G = ι ∘ g_μ⁻¹ ∘ ι` (`ι(z) = 1/z`, `G(0) = 0`) near `ζ = 1/z`: the conformal map of the fiber
`1/w^μ(𝔻*)` onto `𝔻`. -/
def fiberUniformizer (μ : LinfStar) (s : ℂ) : ℂ :=
  if s = 0 then 0 else (Function.invFunOn (gMu μ) unitDiscExterior s⁻¹)⁻¹

/-- `log ‖z²∂_z‖²` (TT:2255) at `([μ], z) ∈ 𝒯(1)`: the hyperbolic metric of the fiber `w^μ(𝔻*)`, pulled back from
`𝔻*` by `g_μ⁻¹`. The formula is
`‖z²∂_z‖² = 4|z² (g_μ⁻¹)'(z)|²/(|g_μ⁻¹(z)|² - 1)² = 4|G'(ζ)|²/(1 - |G(ζ)|²)²` with `ζ = 1/z`, which also covers
`z = ∞`. -/
def logNormSq (q : T1 × ExtPlane) : ℝ :=
  let μ : LinfStar := (Quotient.out q.1 : LinfStarBall)
  let ζ := finPart (inversion q.2)
  Real.log (4 * ‖deriv (fiberUniformizer μ) ζ‖ ^ 2 / (1 - ‖fiberUniformizer μ ζ‖ ^ 2) ^ 2)

/-- The curvature form `Θ(X, Ȳ) = ∂̄∂ log ‖z²∂_z‖²(X, Ȳ)` of `V` (TT:2261), in coordinates at `q`. -/
def thetaForm (q : T1 × ExtPlane) (X Y : AInf unitDisc × ℂ) : ℂ := -polarize (leviTC logNormSq q) X Y

/-- The first Chern form `c₁(V) = (i/2π) Θ` (TT:2261), on `(X, X̄)`. -/
def chernForm (q : T1 × ExtPlane) (X : AInf unitDisc × ℂ) : ℂ := I / (2 * π) * thetaForm q X X

/-- `K = log ‖z²∂_z‖ - log 2` (TT:2269). -/
def potentialK (q : T1 × ExtPlane) : ℝ := logNormSq q / 2 - Real.log 2

/-- `g'(∞) = lim_{z → ∞} g(z)/z`. -/
def derivAtInfty (g : ℂ → ℂ) : ℂ := limUnder (cocompact ℂ) fun z => g z / z

-- lemma_5_1 moved unchanged to Ch1/S5Lemma51Completed (2026-10-28).

/-! ## The Velling–Kirillov metric on `𝒯(1)` -/

/-- The coefficients `c_n`, `n ≥ 2`, of the horizontal part `φ = i Σ_{n ≥ 2} (n³ - n) c_n z^{n-2}` of a coordinate
vector at the origin (TS2). -/
def tangentCoeff (φ : AInf unitDisc) (n : ℕ) : ℂ :=
  iteratedDeriv (n - 2) (AInf.toFun φ) 0 / (Nat.factorial (n - 2)) / (I * ((n : ℂ) ^ 3 - n))

/-- **(4.1)** in the holomorphic coordinates `tcCoordH` at the origin `(0, ∞)` of `𝒯(1)` (TT:2386):
`‖(φ, c)‖²_VK = Σ_{n ≥ 2} n |c_n|² + |c|²`.
- **[CORRECTION 2026-10-28, Program G]** This reverts the 2026-10-28 `c₁` shift. In `tcCoordH` the coordinate line
  `t ↦ ([tΛφ], s = tc)` has `c₁ = c` (in `tcCoord` it was `c + ∂_s f''(0)/2`). The shift was an artifact of the
  non-holomorphic chart (DEFECT G1). -/
def vkNormSqCoordOrigin (X : AInf unitDisc × ℂ) : ℝ :=
  (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) * ‖tangentCoeff X.1 (n + 2)‖ ^ 2) + ‖X.2‖ ^ 2

/-- The origin `(0, ∞)` of `𝒯(1)`. -/
def tOrigin : T1 × ExtPlane := (originT, extInf)

/-- The right translation `R_{q₀} : q ↦ q * q₀ = q * (q₀⁻¹)⁻¹` of `𝒯(1)`, with `q₀⁻¹ = (0, ∞) * q₀⁻¹` from (1.13)–(1.14)
(TT:782, TT:828). -/
def tcurveRight (q₀ : T1 × ExtPlane) (q : T1 × ExtPlane) : T1 × ExtPlane :=
  tcurveMulInv q (tcurveMulInv tOrigin q₀)

/-- The right-invariant Velling–Kirillov norm at `q ∈ 𝒯(1)` (TT:2124): transport `X ∈ T_q𝒯(1)` to the origin by the
differential of `R_{q⁻¹} : x ↦ x * q⁻¹`, in coordinates, and apply (4.1). -/
def vkNormSq (q : T1 × ExtPlane) (X : AInf unitDisc × ℂ) : ℝ :=
  vkNormSqCoordOrigin (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x q) (tcCoordH q) X)

/-- `ω_VK(X, X̄) = (i/2) ‖X‖²_VK` (TT:2139). -/
def omegaVK (q : T1 × ExtPlane) (X : AInf unitDisc × ℂ) : ℂ := I / 2 * vkNormSq q X

-- `thm_5_3` moved to `TakhtajanTeo.Ch1.S5Thm53Grunsky` (2026-10-29, Program G).

-- `lemma_5_4` moved to `TakhtajanTeo.Ch1.S5Lemma54` (2026-10-29, Program G).

-- `lemma_5_5` moved to `Ch1/L55.lean` (2026-10-28).

/-- A smooth curve `𝗀_t = g_t⁻¹ ∘ f^t` in `𝒯(1) ≅ S¹\Homeo_qs(S¹)` through the origin, tangent to `u` (TT:2351–2354,
TS1).
- Each `(f^t, g_t)` is the welding (CW1, CW2′, CW3′, CW4) of a map fixing `1`.
- `f^0 = id`, `g_0 = id`.
- `f^t`, `g_t` are `C²` in `t` (jointly with `z`).
- `ḟ = u₊` on `𝔻` and `ġ - ġ'(∞) z = -u₋` on `𝔻*`. -/
def IsWeldingCurve (u : ℝ → ℝ) (F G : ℝ → ℂ → ℂ) : Prop :=
  (∀ t, ∃ h, IsOneFixedQS h ∧ IsWeldingPrime h (F t) (G t)) ∧
    (∀ z ∈ unitDisc, F 0 z = z) ∧ (∀ z ∈ unitDiscExterior, G 0 z = z) ∧
    ContDiffOn ℝ 2 (fun p : ℝ × ℂ => F p.1 p.2) (univ ×ˢ unitDisc) ∧
    ContDiffOn ℝ 2 (fun p : ℝ × ℂ => G p.1 p.2) (univ ×ˢ unitDiscExterior) ∧
    (∀ z ∈ unitDisc, HasDerivAt (fun t => F t z) (uPlus u z) 0) ∧
    ∀ z ∈ unitDiscExterior, HasDerivAt (fun t => G t z - derivAtInfty (G t) * z) (-uMinus u z) 0

-- eq_5_3_5_4 moved unchanged to Ch1/S5CoefficientVariation.lean (2026-10-28).

/-! ## §5.2 The Chern form `c₁(V)` and the resolvent kernel -/

/-- The vertical vector `∂_z` at `(0, z)`, in the coordinates `(β, ζ = 1/z)`: `(0, -1/z²)`. -/
def vertVec (z : ℂ) : AInf unitDisc × ℂ := (0, -1 / z ^ 2)

/-- The horizontal lift `τ_μ = ∂/∂ε_μ|₀ + ẇ^μ(z) ∂_z` at `(0, z)` (TV1), in the coordinates `tcCoordH`: the velocity
of `t ↦ ([tμ], w^{tμ}(z))`, i.e. `(D₀β(μ), -ẇ^μ(z)/z² + ∂_t (f^{tμ})''(0)/2)`.
- **[CORRECTION 2026-10-28, Program G]** The `ċ` term is the velocity of the shift in `tcCoordH`. `ẇ` is that of the
  welding-normalized `w^{tμ}`, and `ẇ_mem = ẇ - ċ z²`. -/
def horVec (μ : LinfStar) (z : ℂ) : AInf unitDisc × ℂ :=
  (fderiv ℂ bersPhi 0 μ,
    -wdot μ z / z ^ 2 + deriv (fun t : ℝ => deriv (deriv (fB ((t : ℂ) • μ))) 0) 0 / 2)

/-- The point `(0, z)` of the fiber `π⁻¹(0) = 𝔻*`. -/
def fiberPt (z : ℂ) : T1 × ExtPlane := (originT, (z : ExtPlane))

/-- `G(f)(z) = ∬_{𝔻*} G(z, u) f(u) ρ(u) d²u` (TT:2409, TT:2507). -/
def resolventStar (f : ℂ → ℂ) (z : ℂ) : ℂ := resolventOp unitDiscExterior f z

-- `prop_5_7` moved to `TakhtajanTeo.Ch1.S5Prop57` (2026-10-29, Program G).

/-- Conjugation transports the center of the weighted resolvent integral (TT:2444–2462). -/
theorem wp_conj_resolvent_area (f : ℂ → ℂ) (a : ℂ) :
    (∫ w in unitDisc, resolventKernel a w * ‖f (conj w)‖ ^ 2 * (rho w)⁻¹) =
      ∫ w in unitDisc, resolventKernel (conj a) w * ‖f w‖ ^ 2 * (rho w)⁻¹ := by
  let F : ℂ → ℝ := fun w => resolventKernel (conj a) w * ‖f w‖ ^ 2 * (rho w)⁻¹
  have h := Complex.conjLIE.measurePreserving.integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding (unitDisc.indicator F)
  have he : (fun w => unitDisc.indicator F (Complex.conjLIE w)) =
      unitDisc.indicator (fun w => resolventKernel a w * ‖f (conj w)‖ ^ 2 * (rho w)⁻¹) := by
    funext w
    have hc : conj w ∈ unitDisc ↔ w ∈ unitDisc := by simp [unitDisc]
    have hG : resolventKernel (conj a) (conj w) = resolventKernel a w := by
      simp only [resolventKernel, pointPair, ← map_sub, norm_conj]
    by_cases hw : w ∈ unitDisc <;>
      simp [Complex.conjLIE_apply, hc, hw, F, rho, hG]
  rw [he, integral_indicator (s := unitDisc) measurableSet_ball,
    integral_indicator (s := unitDisc) measurableSet_ball] at h
  exact h

/-- Inversion transports the exterior quadratic energy to the disk (TT:2444–2462). -/
theorem wp_inverted_resolvent_area (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior,
      resolventKernel z w * ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) =
      ∫ v in unitDisc, resolventKernel z⁻¹ v * ‖f v‖ ^ 2 * (rho v)⁻¹ := by
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hi := ahP_integral_image hopen hc.1 hc.2.1
    (fun w : ℂ => resolventKernel z w * ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹)
  rw [hc.2.2] at hi
  calc
    _ = ∫ v in unitDisc \ {0}, ‖deriv (fun w : ℂ => w⁻¹) v‖ ^ 2 •
        (resolventKernel z v⁻¹ * ‖f (v⁻¹)⁻¹ / (v⁻¹) ^ 4‖ ^ 2 * (rho v⁻¹)⁻¹) := hi
    _ = ∫ v in unitDisc \ {0}, resolventKernel z⁻¹ v * ‖f v‖ ^ 2 * (rho v)⁻¹ := by
      apply setIntegral_congr_fun hopen.measurableSet
      intro v hv
      have hweight := inverted_quadratic_weight (φ := fun w => f w⁻¹ / w ^ 4) hv.2
      rw [wp_quadratic_inversion_involutive f hv.2] at hweight
      have hG : resolventKernel z v⁻¹ = resolventKernel z⁻¹ v := by
        simpa only [inv_inv] using
          (resolventKernel_inv (resolvent_exterior_ne_zero hz) (inv_ne_zero hv.2)).symm
      dsimp only at hweight ⊢
      rw [smul_eq_mul, hG]
      linear_combination -(resolventKernel z⁻¹ v) * hweight
    _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))

/-- The real Lambda resolvent energy is four times the reflected disk energy (TT:2444–2462). -/
theorem wp_Lambda_resolvent_area_real (φ : AInf unitDisc) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, resolventKernel z w * ‖(Lambda φ : ℂ → ℂ) w‖ ^ 2 * rho w) =
      4 * ∫ v in unitDisc, resolventKernel (conj z)⁻¹ v * ‖AInf.toFun φ v‖ ^ 2 * (rho v)⁻¹ := by
  let f : ℂ → ℂ := fun v => conj (AInf.toFun φ (conj v))
  calc
    _ = ∫ w in unitDiscExterior, 4 *
        (resolventKernel z w * ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) := by
      apply integral_congr_ae
      filter_upwards [wp_Lambda_harmonicDisk_ae φ,
        ae_restrict_mem wp_exterior_isOpen.measurableSet] with w hw hwD
      rw [hw]
      change resolventKernel z w *
        ‖-2 * ((rho w : ℂ)⁻¹ * conj (f w⁻¹ / w ^ 4))‖ ^ 2 * rho w = _
      simp only [norm_mul, norm_neg, norm_ofNat, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (wp_rho_pos hwD), norm_conj, mul_pow]
      field_simp [(wp_rho_pos hwD).ne']
      <;> ring
    _ = 4 * ∫ w in unitDiscExterior,
        resolventKernel z w * ‖f w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹ := integral_const_mul _ _
    _ = _ := by
      rw [wp_inverted_resolvent_area f hz]
      simp only [f, norm_conj]
      rw [wp_conj_resolvent_area, map_inv₀]

/-- Operator form of Lambda energy transport (TT:2444–2462). -/
theorem wp_Lambda_resolvent (φ : AInf unitDisc) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    resolventOp unitDiscExterior (fun w => (‖(Lambda φ : ℂ → ℂ) w‖ ^ 2 : ℝ)) z =
      ((4 * ∫ v in unitDisc,
        resolventKernel (conj z)⁻¹ v * ‖AInf.toFun φ v‖ ^ 2 * (rho v)⁻¹ : ℝ) : ℂ) := by
  simp only [resolventOp, ← Complex.ofReal_mul]
  calc
    _ = ((∫ w in unitDiscExterior,
        resolventKernel z w * ‖(Lambda φ : ℂ → ℂ) w‖ ^ 2 * rho w : ℝ) : ℂ) := integral_ofReal
    _ = _ := congrArg Complex.ofReal (wp_Lambda_resolvent_area_real φ hz)

/-- The cubic coefficient weight cancels the exact resolvent monomial moment (TT:2444–2462). -/
theorem wp_resolvent_coefficient_weight (n : ℕ) (a : ℂ) :
    ‖((((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) * a)‖ ^ 2 /
      (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) =
      ((n + 2 : ℝ) / 2) * ‖a‖ ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hW : 0 ≤ (n + 2 : ℝ) ^ 3 - (n + 2) := by
    nlinarith [mul_nonneg hn (sq_nonneg (n : ℝ))]
  have he : (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) =
      (((n + 2 : ℝ) ^ 3 - (n + 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW, mul_pow]
  have h1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have h3 : (n + 3 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring


/-- **Lemma 5.8** (TT:2444–2462).
- Let `μ ∈ Ω^{-1,1}(𝔻*)` and `φ = D₀β(μ)`.
- Let `(σ_z⁻¹)^*(φ) = φ ∘ σ_z⁻¹ ((σ_z⁻¹)')² = Σ_{n ≥ 2} (n³ - n) a_n^z u^{n-2}` on `𝔻`.
- Then `∬_{𝔻*} G(z, u)|μ(u)|² ρ(u) d²u = 2 Σ_{n ≥ 2} n |a_n^z|²`. -/
theorem lemma_5_8 {μ : LinfStar} (hμ : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) {a : ℕ → ℂ}
    (ha : ∀ u ∈ unitDisc, HasSum (fun n : ℕ => (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) * a (n + 2) * u ^ n)
      (AInf.toFun (fderiv ℂ bersPhi 0 μ) (sigmaInv z u) * deriv (sigmaInv z) u ^ 2)) :
    resolventStar (fun u => (‖μ u‖ ^ 2 : ℝ)) z = 2 * ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * (‖a (n + 2)‖ ^ 2 : ℝ) := by
  let φ := fderiv ℂ bersPhi 0 μ
  let F : ℂ → ℂ := fun u => AInf.toFun φ (sigmaInv z u) * deriv (sigmaInv z) u ^ 2
  let c : ℕ → ℂ := fun n => (((n + 2 : ℕ) : ℂ) ^ 3 - (n + 2 : ℕ)) * a (n + 2)
  have hc : ∀ u ∈ unitDisc, HasSum (fun n => c n * u ^ n) (F u) := ha
  have hσ := wp_sigmaInv_disk_conformal hz
  have hFc : ContinuousOn F unitDisc :=
    ((φ.property.comp hσ.1 hσ.mapsTo).mul ((hσ.1.deriv isOpen_ball).pow 2)).continuousOn
  have hσm : Measurable (sigmaInv z) := by unfold sigmaInv; fun_prop
  have hFm : Measurable F :=
    ((wp_AInf_disc_measurable φ).comp hσm).mul ((measurable_deriv (sigmaInv z)).pow_const 2)
  have hb (u : ℂ) (hu : u ∈ unitDisc) : ‖F u‖ * (rho u)⁻¹ ≤ ‖φ‖ / 4 := by
    dsimp only [F]
    rw [wp_sigmaInv_pullback_norm (AInf.toFun φ) hz hu]
    exact wp_AInf_disc_weighted_bound φ (hσ.mapsTo hu)
  have hi := wp_resolvent_quadratic_integrable hFm
    (by positivity : 0 ≤ ‖φ‖ / 4) hb (by simp [unitDisc] : (0 : ℂ) ∈ unitDisc)
  have hs := wp_resolvent_series_parseval hc hFc hFm hi
  have he (n : ℕ) : ‖c n‖ ^ 2 /
      (2 * (n + 1 : ℝ) ^ 2 * (n + 2) * (n + 3) ^ 2) =
      ((n + 2 : ℝ) / 2) * ‖a (n + 2)‖ ^ 2 := wp_resolvent_coefficient_weight n (a (n + 2))
  simp_rw [he] at hs
  have hs4 := hs.mul_left 4
  have hC := Complex.ofRealCLM.hasSum hs4
  have hterm (n : ℕ) :
      Complex.ofRealCLM (4 * (((n + 2 : ℝ) / 2) * ‖a (n + 2)‖ ^ 2)) =
        2 * (((n + 2 : ℕ) : ℂ) * (‖a (n + 2)‖ ^ 2 : ℝ)) := by
    simp only [Complex.ofRealCLM_apply]
    push_cast
    ring
  simp_rw [hterm] at hC
  have hLam : Lambda φ = μ := lambda_inverse_D0bers.2.2 μ hμ
  calc
    _ = ((4 * ∫ u in unitDisc, resolventKernel 0 u * ‖F u‖ ^ 2 * (rho u)⁻¹ : ℝ) : ℂ) := by
      change resolventOp unitDiscExterior (fun u => (‖μ u‖ ^ 2 : ℝ)) z = _
      rw [← hLam, wp_Lambda_resolvent φ hz, wp_sigmaInv_resolvent_area (AInf.toFun φ) hz]
    _ = _ := by
      simpa only [Complex.ofRealCLM_apply, tsum_mul_left] using hC.tsum_eq.symm

/-! ## §5.3 Mumford–Morita–Miller characteristic forms -/

/-- The matrix `(Θ_{(0,z)}(X_i, Ȳ_j))_{i,j = 0..n}` with `X₀ = Y₀ = ∂_z`, `X_k = τ_{μ_k}`, `Y_k = τ_{ν_k}`. -/
def thetaMatrix (n : ℕ) (μs νs : Fin n → LinfStar) (z : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => thetaForm (fiberPt z) (Fin.cases (vertVec z) (fun k => horVec (μs k) z) i)
    (Fin.cases (vertVec z) (fun k => horVec (νs k) z) j)

/-- **(5.1)** (TT:2247, TT:2515). The Mumford–Morita–Miller form `κ_n = (-1)^{n+1} π_*(c₁(V)^{n+1})` at the origin of
`T(1)`, on `(μ₁, …, μ_n, ν̄₁, …, ν̄_n)`:
`κ_n = (-i/2π)^{n+1} ∬_{𝔻*} Θ^{n+1}(∂_z, ∂_{z̄}, τ_{μ₁}, τ_{ν̄₁}, …) dz ∧ dz̄`, where
`Θ^{n+1}(…) = (n+1)! det(Θ(X_i, Ȳ_j))` and `dz ∧ dz̄ = -2i d²z`. -/
def kappaOrigin (n : ℕ) (μs νs : Fin n → LinfStar) : ℂ :=
  (-I / (2 * π)) ^ (n + 1) *
    ∫ z in unitDiscExterior, ((Nat.factorial (n + 1) : ℕ) : ℂ) * (thetaMatrix n μs νs z).det * (-2 * I)

-- `thm_5_10` moved to `TakhtajanTeo.Ch1.S5Kappa` (2026-10-29, Program G).

-- `cor_5_11` moved to `TakhtajanTeo.Ch1.S5Kappa` (2026-10-29, Program G).

end TakhtajanTeo
