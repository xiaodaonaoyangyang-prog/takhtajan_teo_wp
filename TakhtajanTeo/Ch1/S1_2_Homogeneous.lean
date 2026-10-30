import TakhtajanTeo.Ch1.S1_1_TeichmullerTheory
import TakhtajanTeo.Ch1.Lemma15
import TakhtajanTeo.Ch1.TV1Variation
import References.Pommerenke1992.Ch05.S05_QuasiconformalExtension
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Chapter 1, §1.2 — Homogeneous spaces of `Homeo_qs(S¹)` (TT:594–1004)

* `Homeo_qs(S¹)` and its subgroups `Diff₊(S¹)`, `Möb(S¹)`, `S¹`; the classes `𝒟`, `𝒟̃`; the bijections (1.9)
* §1.2.1 conformal welding CW1–CW4; `α_μ`, `𝗀_μ = α_μ ∘ w_μ`, `g_μ`, (1.10); Lemma 1.5, Remark 1.6; the bijections
  `𝒟̃ ← 𝒯(1) → S¹\Homeo_qs(S¹)`, CW2′–CW3′, `σ_w`, `λ_w`; the group law (1.13)–(1.14) of `𝒯(1)`; (1.15)
* §1.2.2 horizontal and vertical lifts TV1–TV2
* §1.2.3 Zygmund vector fields, the conjugation operator `J`, the Sobolev spaces `𝓗ˢ(S¹)`, TS2–TS4

**Modelling.**
- Maps of the circle are functions `ℂ → ℂ`, read on `S¹`.
- "Quasisymmetric" is Pommerenke's three-point definition `Pommerenke1992.IsQuasisymmetric` ((5.4.4)). "Orientation
  preserving homeomorphism of `S¹`" is `Pommerenke1992.IsSensePreservingCircleHomeo`.
- The coset spaces are represented as in the memoir:
  - `Möb(S¹)\Homeo_qs(S¹)` by the maps fixing `-1, -i, 1` (TT:620);
  - `S¹\Homeo_qs(S¹)` by the maps fixing `1` (TT:732).
- Elements of `Möb(S¹)` are Möbius maps of `ℂ̄` preserving `𝔻`.

**Not stated** (recorded here):
- Remark 1.4 (TT:622) poses a problem.
- Remark 1.7 (TT:780) cites [Kir87] for the Lie group structure of `Diff₊(S¹)` and Fréchet manifold structures, which
  the memoir does not use.
- Remark 1.8 (TT:930) is a sign convention.
- TS1 (TT:958) identifies tangent spaces through derivatives of curves in `𝒟̃`; the memoir uses it only through TS2.
- The directional derivatives (1.16) (TT:947) of functions on `𝒯(1)` are defined where they are used (§5).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate BoundedContinuousFunction Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## The groups and classes -/

/-- `h ∈ Homeo_qs(S¹)` (TT:594): an orientation preserving quasisymmetric homeomorphism of the unit circle. -/
def IsQSCircleHomeo (h : ℂ → ℂ) : Prop :=
  Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetric h

/-- `h ∈ Diff₊(S¹)` (TT:594): `h(e^{it}) = e^{iu(t)}` with `u` smooth, `u' > 0`, `u(t + 2π) = u(t) + 2π`.
[CORRECTION] The explicit ENat infinity expresses C-infinity regularity; bare
top in Mathlib's larger differentiability-order type would require analyticity. -/
def IsCircleDiffeo (h : ℂ → ℂ) : Prop :=
  ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ (∀ t, 0 < deriv u t) ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
    ∀ t : ℝ, h (exp (t * I)) = exp (u t * I)

/-- `α ∈ Möb(S¹)` (TT:594): a Möbius transformation of `ℂ̄` mapping `𝔻` onto `𝔻` (so preserving `S¹` and its
orientation). -/
def IsDiscMobius (α : ExtPlane → ExtPlane) : Prop :=
  IsMobius α ∧ α '' toExt unitDisc = toExt unitDisc

/-- The rotations `S¹ ⊂ Möb(S¹)` (TT:594): `z ↦ e^{iθ} z`. -/
def IsRotation (h : ℂ → ℂ) : Prop := ∃ θ : ℝ, ∀ z, h z = exp (θ * I) * z

/-- The representatives of `Möb(S¹)\Homeo_qs(S¹)`: the elements of `Homeo_qs(S¹)` fixing `-1, -i, 1` (TT:620). -/
def IsNormalizedQS (h : ℂ → ℂ) : Prop :=
  IsQSCircleHomeo h ∧ h (-1) = -1 ∧ h (-I) = -I ∧ h 1 = 1

/-- The representatives of `S¹\Homeo_qs(S¹)`: the elements of `Homeo_qs(S¹)` fixing `1` (TT:732). -/
def IsOneFixedQS (h : ℂ → ℂ) : Prop :=
  IsQSCircleHomeo h ∧ h 1 = 1

/-- `F : ℂ → ℂ` admits a quasiconformal extension to `ℂ` from `D`: some quasiconformal homeomorphism of `ℂ` agrees
with `F` on `D`. -/
def HasQCExtension (F : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∃ G : ℂ → ℂ, IsQuasiconformal G univ ∧ G '' univ = univ ∧ EqOn G F D

/-- The class `𝒟` (TT:598): univalent `f` on `𝔻`, `f(0) = 0`, `f'(0) = 1`, `f''(0) = 0`, with a q.c. extension to
`ℂ`. -/
def ClassD : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧ deriv (deriv f) 0 = 0 ∧
    HasQCExtension f unitDisc}

/-- The class `𝒟̃` (TT:600): univalent `f` on `𝔻`, `f(0) = 0`, `f'(0) = 1`, with a q.c. extension to `ℂ`. -/
def ClassDtilde : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧ HasQCExtension f unitDisc}

/-- `g` is univalent on `𝔻*` with `g(∞) = ∞`: holomorphic and injective on `𝔻*`, and `g(z) → ∞` as `z → ∞` (CW4,
TT:634). -/
def IsUnivalentAtInfty (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g unitDiscExterior ∧ InjOn g unitDiscExterior ∧ Tendsto g (cocompact ℂ) (cocompact ℂ)

/-- The conditions CW1, CW2′, CW3′, CW4 (TT:732–736) for `h ∈ S¹\Homeo_qs(S¹)`: as `IsWelding` with `α = id` and
CW3′ `f(0) = 0`, `f'(0) = 1` (no condition on `f''(0)`). -/
def IsWeldingPrime (h : ℂ → ℂ) (f g : ℂ → ℂ) : Prop :=
  (∃ F G : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧ EqOn F f unitDisc ∧
      IsQuasiconformal G univ ∧ G '' univ = univ ∧ EqOn G g unitDiscExterior ∧
      ∀ z ∈ unitCircle, G (h z) = F z) ∧
    DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧ IsUnivalentAtInfty g

-- `eq_1_9_classD` moved to `Ch1/Eq19Completed.lean` (2026-10-25).

-- `eq_1_9_homeo` moved to `Ch1/Eq19Completed.lean` (2026-10-25).

/-! ## §1.2.1 Conformal welding -/

/-- The conditions CW1–CW4 (TT:624–634) for `h : S¹ → S¹`, `α ∈ Möb(S¹)` fixing `1`, `f` on `𝔻`, `g` on `𝔻*`:
* CW1 `f`, `g` univalent with q.c. extensions to `ℂ`;
* CW2 `α ∘ h = (g⁻¹ ∘ f)|S¹`, i.e. `g ∘ α ∘ h = f` on `S¹` (boundary values: `f`, `g` extend continuously to `S¹`
  through their q.c. extensions, so they are read through those extensions);
* CW3 `f(0) = 0`, `f'(0) = 1`;
* CW4 `g(∞) = ∞`.

**[CORRECTION 2026-10-25]** With the normalization `w^μ(∞) = ∞` of Model B (TT's `f''(0) = 0` is not always
attainable), TT's `α ∈ Möb(S¹)` is the identity, and `f''(0) = 0` is dropped. -/
def IsWelding (h : ℂ → ℂ) (α : ExtPlane → ExtPlane) (f g : ℂ → ℂ) : Prop :=
  α = id ∧
    (∃ F G : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧ EqOn F f unitDisc ∧
      IsQuasiconformal G univ ∧ G '' univ = univ ∧ EqOn G g unitDiscExterior ∧
      ∀ z ∈ unitCircle, (G (finPart (α (h z))) : ExtPlane) = F z) ∧
    DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧
    IsUnivalentAtInfty g

-- `conformal_welding` moved to `Ch1/HomogeneousCompleted.lean` (2026-10-25).

/-- The Möbius map `α_μ ∈ Möb(S¹)` of the welding of `w_μ|S¹` (TT:636), chosen with `f = f^μ = w^μ|𝔻`. -/
def alphaMu (μ : LinfStar) : ExtPlane → ExtPlane :=
  if h : ∃ α g, IsWelding (wA μ) α (fB μ) g then h.choose else id

/-- The chosen welding normalization is bijective (TT:636). A selected welding has `α = id`, and the fallback is the
identity. -/
theorem alphaMu_bijective (μ : LinfStar) : Function.Bijective (alphaMu μ) := by
  unfold alphaMu
  split_ifs with h
  · obtain ⟨g, hg⟩ := h.choose_spec
    rw [hg.1]
    exact Function.bijective_id
  · exact Function.bijective_id

/-- The univalent function `g_μ` on `𝔻*` of the welding of `w_μ|S¹` (TT:636). -/
def gMu (μ : LinfStar) : ℂ → ℂ :=
  if h : ∃ g, IsWelding (wA μ) (alphaMu μ) (fB μ) g then h.choose else id

/-- The q.c. map `𝗀_μ = α_μ ∘ w_μ` of `ℂ̄` (TT:636, TT:642), at finite points, as a point of `ℂ̄` (`w_μ` is a map of the
sphere, so `𝗀_μ(z)` may be `∞`). -/
def gammaMu (μ : LinfStar) (z : ℂ) : ExtPlane :=
  alphaMu μ (wAS μ z)

-- `welding_of_wA` moved to `Ch1/HomogeneousCompleted.lean` (2026-10-25).

/-- **(1.10)** (TT:645). The factorization `𝗀_μ = g_μ⁻¹ ∘ f^μ` of q.c. maps of `ℂ̄`, i.e. `g_μ ∘ 𝗀_μ = w^μ`, where
`g_μ = w^μ ∘ w_μ⁻¹ ∘ α_μ⁻¹` is the q.c. extension of the welding function. Moreover `𝗀_μ` has the reflection
property (1.2). -/
theorem eq_1_10 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∀ z : ℂ, wB μ (Function.invFun (wAS μ) (Function.invFun (alphaMu μ) (gammaMu μ z))) = wB μ (z : ExtPlane) := by
  intro z
  unfold gammaMu
  rw [Function.leftInverse_invFun (alphaMu_bijective μ).injective,
    Function.leftInverse_invFun (wAS_bijective μ).injective]

/-- **Lemma 1.5** (TT:658). For harmonic `μ ∈ Ω^{-1,1}(𝔻*)₁`, `α_μ = id` fixes `∞`, and the renormalization
`λ_c ∘ w^μ` with `c = (f^μ)''(0)/2` (so that `(λ_c ∘ f^μ)''(0) = 0`) fixes `∞`.
- **[CORRECTION 2026-10-25]** With the welding normalization `α_μ = id`; TT's `𝗀_μ(0) = 0` (false for `α_μ = id`:
  `w_μ(0) ≠ 0` in general) is replaced by its content, the fixed point `∞` of the `f''(0) = 0` renormalization. -/
theorem lemma_1_5 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    alphaMu μ extInf = extInf ∧
      mobiusExt 1 0 (deriv (deriv (fB μ)) 0 / 2) 1 (wB μ extInf) = extInf := by
  refine ⟨?_, l15_conj2 hμ hh⟩
  have : alphaMu μ = id := by
    unfold alphaMu
    split_ifs with h
    · obtain ⟨g, hg⟩ := h.choose_spec
      exact hg.1
    · rfl
  rw [this]; rfl

/-- The inversion `ι(z) = 1/z` of `ℂ̄`. -/
def inversion : ExtPlane → ExtPlane := mobiusExt 0 1 1 0

/-- (TT:660) For harmonic `μ`: `w^μ(∞) = -2/(f^μ)''(0)` (`∞` if `(f^μ)''(0) = 0`).
- **[CORRECTION 2026-10-25]** TT's `w^μ(∞) = ∞` holds for the `f''(0) = 0` normalization; for the welding
  normalization of Model B it becomes this Möbius image. -/
theorem lemma_1_5_fB_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (hh : μ ∈ harmonicBeltrami) :
    wB μ extInf = mobiusExt 1 0 (-(deriv (deriv (fB μ)) 0 / 2)) 1 extInf :=
  l15_fB_infty hμ hh

-- `remark_1_6` moved to `Ch1/Remark16.lean` (2026-10-28).

-- `conformal_welding_prime` moved to `Ch1/HomogeneousCompleted.lean` (2026-10-25).

/-- `σ_w(z) = ((1 - w)/(1 - w̄)) (1 - z w̄)/(z - w) ∈ S¹\Möb(S¹)` for `w ∈ 𝔻*` (TT:741). -/
def sigmaW (w z : ℂ) : ℂ := (1 - w) / (1 - conj w) * ((1 - z * conj w) / (z - w))

/-- `λ_w(z) = z/(c_w z + 1)` (TT:759). -/
def lambdaW (c z : ℂ) : ℂ := z / (c * z + 1)

/-- The change of the second derivative under the fiber Möbius map. -/
theorem lambdaW_comp_jets {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1) (c : ℂ) :
    deriv (fun z => lambdaW c (F z)) 0 = 1 ∧
      deriv (deriv (fun z => lambdaW c (F z))) 0 = deriv (deriv F) 0 - 2 * c := by
  have h := mobius_comp_first_second (a := 1) (b := 0) (c := c) (d := 1)
    hF (by simp [h0])
  simpa [mobiusFn, lambdaW, h0, h1, sub_eq_add_neg, add_comm] using h

theorem fiber_welding_derivative_identity {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (c : ℂ) :
    c = -(1 / 2) * (deriv (deriv fun z => lambdaW c (fB μ z)) 0 -
      deriv (deriv (fB μ)) 0) / deriv (fun z => lambdaW c (fB μ z)) 0 := by
  have hF : AnalyticAt ℂ (fB μ) 0 :=
    (fB_holomorphic_injective hμ).1.analyticOnNhd isOpen_ball 0 (by simp [unitDisc])
  have hj := lambdaW_comp_jets hF (fB_normalization μ).1 (fB_normalization μ).2.1 c
  rw [hj.1, hj.2]
  ring


/- The proved, user-approved sphere correction of `fiber_welding` is declared
in `TakhtajanTeo.Ch1.HomogeneousCompleted`, downstream of the welding helpers. -/

-- `TCurve_equiv_oneFixed` moved to `Ch1/TCurve.lean` (2026-10-26).

/-- **(1.13)** (TT:791). The Beltrami part `λ` of `([λ], z) = ([ν], ζ) * ([μ], w)⁻¹` in `𝒯(1)`:
`λ = ((ν - μ_𝗀)/(1 - \overline{μ_𝗀} ν) 𝗀_z/\overline{𝗀_z}) ∘ 𝗀⁻¹`, where `𝗀` is a q.c. extension of `σ_u ∘ 𝗀_μ`,
`u = g_μ⁻¹(w)` (TT:800) and `μ_𝗀 = complexDilatation 𝗀` is the Beltrami coefficient of `𝗀` (the Beltrami coefficient of
`w^ν ∘ 𝗀⁻¹` on `𝔻*`).
- **[CORRECTION 2026-10-26]** The former `tcurveLambda ν μ G` used the given `μ` in place of `μ_𝗀`; this is only right for
  `𝗀` with dilatation `μ` on `𝔻*`, and made the independence statement false (`μ = 0`, `u = ∞`, `G₂ = |z|z`). -/
def tcurveLambda (ν : LinfStar) (G : ℂ → ℂ) : LinfStar :=
  toLinf fun z =>
    (fun u => (ν u - complexDilatation G u) / (1 - conj (complexDilatation G u) * ν u) *
      (dz G u / conj (dz G u))) (Function.invFun G z)

/-- **(1.14)** (TT:797). The fiber part `z = (w^λ ∘ 𝗀 ∘ (w^ν)⁻¹)(ζ)` of the group law of `𝒯(1)`. -/
def tcurveZ (ν : LinfStar) (G : ℂ → ℂ) (lam : LinfStar) (ζ : ExtPlane) : ExtPlane :=
  wB lam (OnePoint.map G (Function.invFun (wB ν) ζ))

-- `tcurve_mul_independent` moved to `Ch1/TCurve.lean` (2026-10-26).

-- `eq_1_15` moved to `Ch1/HomogeneousCompleted.lean` (2026-10-25).

/-! ## §1.2.2 Horizontal and vertical subspaces -/

/-- `(σ_z⁻¹)^* μ = μ ∘ σ_z⁻¹ · \overline{(σ_z⁻¹)'}/(σ_z⁻¹)'` (TT:861), the pull-back of a Beltrami differential by
`σ_z⁻¹`. -/
def pullbackSigmaInv (z : ℂ) (μ : LinfStar) : LinfStar :=
  toLinf fun u => μ (Function.invFun (sigmaW z) u) *
    (conj (deriv (Function.invFun (sigmaW z)) u) / deriv (Function.invFun (sigmaW z)) u)

/-- `ẇ^μ(z) = d/dt|_{t=0} w^{tμ}(z)` (TT:867), the vertical component of the horizontal lift `τ_μ`. -/
def wdot (μ : LinfStar) (z : ℂ) : ℂ := deriv (fun t : ℝ => finPart (wB ((t : ℂ) • μ) (z : ExtPlane))) 0

/-- **TV1** (TT:850–870).
- The horizontal lift of `μ ∈ Ω^{-1,1}(𝔻*)` to `(0, z) ∈ π⁻¹(0)` is the vector field
  `τ_μ = ∂/∂ε_μ|₀ + ẇ^μ(z) ∂/∂z`.
- It comes from the curve `([tμ], w^{tμ}(z))`; at `(0, z)` it is identified with `(σ_z⁻¹)^*μ ∈ T_{(0,∞)}𝒯(1)`.
- Stated here: the curve's fiber component `t ↦ w^{tμ}(z)` is differentiable at `t = 0`, with derivative `ẇ^μ(z)`.
- `(σ_z⁻¹)^*μ` is again a harmonic Beltrami differential, because `σ_z⁻¹` preserves `𝔻*` and the hyperbolic metric. -/
theorem TV1 {μ : LinfStar} (hh : μ ∈ harmonicBeltrami) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasDerivAt (fun t : ℝ => finPart (wB ((t : ℂ) • μ) (z : ExtPlane))) (wdot μ z) 0 ∧
      pullbackSigmaInv z μ ∈ harmonicBeltrami := by
  refine ⟨(tv1_a_diff μ z).hasDerivAt, ?_⟩
  obtain ⟨ha, hT, hw⟩ := tv1_sigma_inv hz
  exact tv_pullback_harmonic hh ha hT hw

/-- The inverse of `σ_z` (TT:741): `σ_z⁻¹(w) = (k + w z)/(w + k z̄)` with `k = (1 - z)/(1 - z̄)`. -/
def sigmaInv (z w : ℂ) : ℂ := ((1 - z) / (1 - conj z) + w * z) / (w + (1 - z) / (1 - conj z) * conj z)

/-- The sphere version of the normalized fiber map (TT:741), with the
parameter infinity representing the identity. Polynomial coefficients avoid
an artificial pole in the normalization factor. -/
def sigmaSphere (w : ExtPlane) : ExtPlane → ExtPlane :=
  OnePoint.elim w id fun z =>
    mobiusExt (-(1 - z) * conj z) (1 - z) (1 - conj z) (-z * (1 - conj z))

/-- Inverse sphere map for the normalized fiber coordinate (TT:741).
The finite branch is the adjugate matrix of `sigmaSphere`. -/
def sigmaInvSphere (w : ExtPlane) : ExtPlane → ExtPlane :=
  OnePoint.elim w id fun z =>
    mobiusExt (-z * (1 - conj z)) (-(1 - z)) (-(1 - conj z)) (-(1 - z) * conj z)

/-- Multiplying every Möbius coefficient by the same nonzero scalar preserves
the sphere map, including its pole and its value at infinity. -/
theorem sphere_mobius_scale (a b c d s : ℂ) (hs : s ≠ 0) (p : ExtPlane) :
    mobiusExt (s * a) (s * b) (s * c) (s * d) p = mobiusExt a b c d p := by
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · simp [mobiusExt, hc]
    · rw [mobiusExt_infty_of_ne (mul_ne_zero hs hc), mobiusExt_infty_of_ne hc]
      congr 1
      exact mul_div_mul_left a c hs
  | coe z =>
    have he : s * c * z + s * d = s * (c * z + d) := by ring
    by_cases hz : c * z + d = 0
    · rw [mobiusExt_coe_of_eq_zero (by rw [he, hz, mul_zero]),
        mobiusExt_coe_of_eq_zero hz]
    · rw [mobiusExt_coe (by rw [he]; exact mul_ne_zero hs hz), mobiusExt_coe hz]
      congr 1
      dsimp [mobiusFn]
      rw [he, show s * a * z + s * b = s * (a * z + b) by ring]
      exact mul_div_mul_left _ _ hs

/-- A matrix in the disk Möbius form fixing one is recovered from its pole.
This includes the zero off-diagonal case, whose pole is infinity. -/
theorem sphere_mobius_normalized (u v : ℂ)
    (hdet : u * conj u - v * conj v ≠ 0)
    (hfix : u + v = conj u + conj v) (p : ExtPlane) :
    mobiusExt u v (conj v) (conj u) p =
      sigmaSphere (mobiusExt (conj u) (-v) (-conj v) u extInf) p := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := by
      intro hu
      apply hdet
      simp [hu, hv]
    have hur : conj u = u := by simpa [hv] using hfix.symm
    simp only [hv, map_zero, neg_zero, mobiusExt_infty_of_eq rfl,
      sigmaSphere, OnePoint.elim_infty, id_eq, hur]
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simpa using hu)]
      congr 1
      simp [mobiusFn, hu]
  · have hvc : conj v ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hv
    have hs : u + v ≠ 0 := by
      intro he
      have hu : u = -v := eq_neg_of_add_eq_zero_left he
      apply hdet
      simp [hu]
    have hscale : (u + v) / (v * conj v) ≠ 0 :=
      div_ne_zero hs (mul_ne_zero hv hvc)
    rw [mobiusExt_infty_of_ne (neg_ne_zero.mpr hvc)]
    change mobiusExt u v (conj v) (conj u) p =
      mobiusExt (-(1 - conj u / -conj v) * conj (conj u / -conj v))
        (1 - conj u / -conj v) (1 - conj (conj u / -conj v))
        (-(conj u / -conj v) * (1 - conj (conj u / -conj v))) p
    have he1 : -(1 - conj u / -conj v) * conj (conj u / -conj v) =
        ((u + v) / (v * conj v)) * u := by
      simp only [map_div₀, map_neg, starRingEnd_self_apply]
      field_simp
      linear_combination -u * hfix
    have he2 : 1 - conj u / -conj v = ((u + v) / (v * conj v)) * v := by
      field_simp
      linear_combination -hfix
    have he3 : 1 - conj (conj u / -conj v) =
        ((u + v) / (v * conj v)) * conj v := by
      simp only [map_div₀, map_neg, starRingEnd_self_apply]
      field_simp
      <;> ring
    have he4 : -(conj u / -conj v) * (1 - conj (conj u / -conj v)) =
        ((u + v) / (v * conj v)) * conj u := by
      simp only [map_div₀, map_neg, starRingEnd_self_apply]
      field_simp
      <;> ring
    rw [he4, he1, he2, he3, sphere_mobius_scale _ _ _ _ _ hscale]

/-- The determinant of the finite normalized fiber map does not vanish for
an exterior parameter (TT:741). -/
theorem sigmaSphere_det {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (-(1 - w) * conj w) * (-w * (1 - conj w)) -
      (1 - w) * (1 - conj w) ≠ 0 := by
  have hw1 : w ≠ 1 := by
    intro he
    subst w
    norm_num [unitDiscExterior] at hw
  have hc1 : conj w ≠ 1 := by
    intro he
    apply hw1
    simpa using congrArg (starRingEnd ℂ) he
  have hn : w * conj w - 1 ≠ 0 := by
    intro he
    have he' : (‖w‖ : ℂ) ^ 2 = 1 := by
      rw [← Complex.mul_conj']
      exact sub_eq_zero.mp he
    have heR : ‖w‖ ^ 2 = 1 := by exact_mod_cast he'
    have hwR : 1 < ‖w‖ := hw
    nlinarith
  have he : (-(1 - w) * conj w) * (-w * (1 - conj w)) -
      (1 - w) * (1 - conj w) = (1 - w) * (1 - conj w) * (w * conj w - 1) := by ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hw1.symm)
    (sub_ne_zero.mpr hc1.symm)) hn

/-- The sphere inverse is a right inverse, including infinity (TT:741). -/
theorem sigmaSphere_inv_apply {w : ExtPlane} (hw : w ∈ extDiscExterior) (z : ExtPlane) :
    sigmaSphere w (sigmaInvSphere w z) = z := by
  induction w using OnePoint.rec with
  | infty => rfl
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hw
    exact (mobiusHomeomorph _ _ _ _ (sigmaSphere_det hw')).right_inv z

/-- The sphere map sends its parameter to infinity (TT:741), also when the
parameter itself is infinity. -/
theorem sigmaSphere_pole (w : ExtPlane) : sigmaSphere w w = extInf := by
  induction w using OnePoint.rec with
  | infty => rfl
  | coe w => exact mobiusExt_coe_of_eq_zero (by ring)

/-- Every normalized fiber map has disk Möbius matrix form and fixes one
(TT:741), with a nonzero determinant for exterior parameters. -/
theorem sigmaSphere_matrix {w : ExtPlane} (hw : w ∈ extDiscExterior) :
    ∃ u v : ℂ, sigmaSphere w = mobiusExt u v (conj v) (conj u) ∧
      u * conj u - v * conj v ≠ 0 ∧ u + v = conj u + conj v := by
  induction w using OnePoint.rec with
  | infty =>
    refine ⟨1, 0, ?_, by norm_num, by simp⟩
    funext p
    induction p using OnePoint.rec with
    | infty => simp [sigmaSphere, mobiusExt]
    | coe p => simp [sigmaSphere, mobiusExt]
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hw
    refine ⟨-(1 - w) * conj w, 1 - w, ?_, ?_, ?_⟩
    · simp only [sigmaSphere, OnePoint.elim_some, map_sub, map_one,
        map_mul, map_neg, starRingEnd_self_apply]
      congr 1 <;> ring
    · simpa only [map_sub, map_one, map_mul, map_neg, starRingEnd_self_apply,
        neg_mul, mul_comm] using sigmaSphere_det hw'
    · simp only [map_sub, map_one, map_mul, map_neg, starRingEnd_self_apply]
      ring

/-- Sphere-valued composition law for the fiber over the origin
(TT:738, TT:875). [CORRECTION] The product parameter must be allowed to be
infinity: a = -2 and b = 2 give the identity, with pole infinity. The former
affine formula returned the junk value zero in this case. -/
theorem sigma_comp {a b : ExtPlane} (ha : a ∈ extDiscExterior)
    (hb : b ∈ extDiscExterior) (p : ExtPlane) :
    sigmaSphere a (sigmaSphere b p) = sigmaSphere (sigmaInvSphere b a) p := by
  obtain ⟨u, v, hau, hda, hfa⟩ := sigmaSphere_matrix ha
  obtain ⟨r, s, hbr, hdb, hfb⟩ := sigmaSphere_matrix hb
  let U : ℂ := u * r + v * conj s
  let V : ℂ := u * s + v * conj r
  have hcomp : ∀ z, sigmaSphere a (sigmaSphere b z) =
      mobiusExt U V (conj V) (conj U) z := by
    intro z
    rw [hau, hbr, s16p_mobiusExt_comp hdb]
    dsimp [U, V]
    simp only [map_add, map_mul, starRingEnd_self_apply]
    congr 1 <;> ring
  have hd : U * conj U - V * conj V ≠ 0 := by
    have he : U * conj U - V * conj V =
        (u * conj u - v * conj v) * (r * conj r - s * conj s) := by
      dsimp [U, V]
      simp only [map_add, map_mul, starRingEnd_self_apply]
      ring
    rw [he]
    exact mul_ne_zero hda hdb
  have hf : U + V = conj U + conj V := by
    dsimp [U, V]
    simp only [map_add, map_mul, starRingEnd_self_apply]
    linear_combination (r + s) * hfa + (conj u - v) * hfb
  have hpole : sigmaInvSphere b a =
      mobiusExt (conj U) (-V) (-conj V) U extInf := by
    apply (mobiusHomeomorph U V (conj V) (conj U) hd).injective
    change mobiusExt U V (conj V) (conj U) (sigmaInvSphere b a) = _
    rw [← hcomp, sigmaSphere_inv_apply hb, sigmaSphere_pole]
    exact ((mobiusHomeomorph U V (conj V) (conj U) hd).right_inv extInf).symm
  rw [hcomp, hpole]
  exact sphere_mobius_normalized U V hd hf p

/-- Disk Möbius matrices with positive norm determinant preserve the sphere
exterior, including points sent to infinity (TT:738–741). -/
theorem sphere_mobius_mapsTo_exterior (u v : ℂ) (huv : normSq v < normSq u) :
    MapsTo (mobiusExt u v (conj v) (conj u)) extDiscExterior extDiscExterior := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    by_cases hv : conj v = 0
    · rw [mobiusExt_infty_of_eq hv]
      exact Or.inr rfl
    · rw [mobiusExt_infty_of_ne hv]
      refine Or.inl ⟨u / conj v, ?_, rfl⟩
      apply one_lt_normSq_iff.mp
      rw [normSq_div, normSq_conj]
      apply (one_lt_div (normSq_pos.mpr ?_)).mpr
      · exact huv
      · exact fun he => hv (by simp [he])
  | coe z =>
    have hz : z ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hp
    by_cases hd : conj v * z + conj u = 0
    · rw [mobiusExt_coe_of_eq_zero hd]
      exact Or.inr rfl
    · rw [mobiusExt_coe hd]
      refine Or.inl ⟨mobiusFn u v (conj v) (conj u) z, ?_, rfl⟩
      apply one_lt_normSq_iff.mp
      rw [mobiusFn, normSq_div]
      apply (one_lt_div (normSq_pos.mpr hd)).mpr
      have he : normSq (u * z + v) - normSq (conj v * z + conj u) =
          (normSq u - normSq v) * (normSq z - 1) := by
        simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im]
        ring
      have hz' : 1 < normSq z := one_lt_normSq_iff.mpr hz
      have hpos := mul_pos (sub_pos.mpr huv) (sub_pos.mpr hz')
      linarith

/-- Both the fiber map and its inverse have a positive disk Möbius matrix
for an exterior sphere parameter (TT:738–741). -/
theorem sigmaSphere_positive_matrix {w : ExtPlane} (hw : w ∈ extDiscExterior) :
    ∃ u v : ℂ, sigmaSphere w = mobiusExt u v (conj v) (conj u) ∧
      sigmaInvSphere w = mobiusExt (conj u) (-v) (conj (-v)) (conj (conj u)) ∧
      normSq v < normSq u := by
  induction w using OnePoint.rec with
  | infty =>
    refine ⟨1, 0, ?_, ?_, by norm_num⟩
    · funext p
      induction p using OnePoint.rec <;> simp [sigmaSphere, mobiusExt]
    · funext p
      induction p using OnePoint.rec <;> simp [sigmaInvSphere, mobiusExt]
  | coe w =>
    have hw' : w ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hw
    have hw1 : w ≠ 1 := by
      rintro rfl
      norm_num [unitDiscExterior] at hw'
    refine ⟨-(1 - w) * conj w, 1 - w, ?_, ?_, ?_⟩
    · simp only [sigmaSphere, OnePoint.elim_some, map_sub, map_one,
        map_mul, map_neg, starRingEnd_self_apply]
      congr 1 <;> ring
    · simp only [sigmaInvSphere, OnePoint.elim_some, map_sub, map_one,
        map_mul, map_neg, starRingEnd_self_apply]
      congr 1 <;> ring
    · simp only [normSq_mul, normSq_neg, normSq_conj]
      exact lt_mul_of_one_lt_right (normSq_pos.mpr (sub_ne_zero.mpr hw1.symm))
        (one_lt_normSq_iff.mpr hw')

/-- The sphere fiber coordinate and its inverse preserve the exterior
(TT:738–741), so the parameter in the composition law stays in the same domain. -/
theorem sigmaSphere_mapsTo {w : ExtPlane} (hw : w ∈ extDiscExterior) :
    MapsTo (sigmaSphere w) extDiscExterior extDiscExterior ∧
      MapsTo (sigmaInvSphere w) extDiscExterior extDiscExterior := by
  obtain ⟨u, v, hσ, hι, hpos⟩ := sigmaSphere_positive_matrix hw
  rw [hσ, hι]
  refine ⟨sphere_mobius_mapsTo_exterior u v hpos,
    sphere_mobius_mapsTo_exterior (conj u) (-v) ?_⟩
  simpa only [normSq_neg, normSq_conj] using hpos

/-- The normalized fiber map carries the entire sphere exterior onto itself
(TT:738–741). -/
theorem sigmaSphere_image_exterior {w : ExtPlane} (hw : w ∈ extDiscExterior) :
    sigmaSphere w '' extDiscExterior = extDiscExterior := by
  apply Subset.antisymm (sigmaSphere_mapsTo hw).1.image_subset
  intro z hz
  exact ⟨sigmaInvSphere w z, (sigmaSphere_mapsTo hw).2 hz, sigmaSphere_inv_apply hw z⟩

/-- The sphere map agrees with the original finite formula away from its pole
(TT:741). The normalization is meaningful for exterior parameters. -/
theorem sigmaSphere_coe_eq {w z : ℂ} (hw : w ∈ unitDiscExterior) (hz : z ≠ w) :
    sigmaSphere (w : ExtPlane) (z : ExtPlane) = (sigmaW w z : ExtPlane) := by
  have hw1 : w ≠ 1 := by
    rintro rfl
    norm_num [unitDiscExterior] at hw
  have hc : 1 - conj w ≠ 0 := by
    intro he
    apply hw1
    simpa using congrArg (starRingEnd ℂ) (sub_eq_zero.mp he).symm
  have hden : (1 - conj w) * z + -w * (1 - conj w) ≠ 0 := by
    convert mul_ne_zero hc (sub_ne_zero.mpr hz) using 1 <;> ring
  change mobiusExt _ _ _ _ (z : ExtPlane) = _
  rw [mobiusExt_coe hden]
  congr 1
  dsimp [mobiusFn, sigmaW]
  rw [div_mul_div_comm, div_eq_div_iff hden (mul_ne_zero hc (sub_ne_zero.mpr hz))]
  ring

/-- The sphere inverse agrees with the original affine inverse whenever that
inverse has a finite value (TT:741). -/
theorem sigmaInvSphere_coe_eq {w z : ℂ} (hw : w ∈ unitDiscExterior)
    (hz : z + (1 - w) / (1 - conj w) * conj w ≠ 0) :
    sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = (sigmaInv w z : ExtPlane) := by
  have hw1 : w ≠ 1 := by
    rintro rfl
    norm_num [unitDiscExterior] at hw
  have hc : 1 - conj w ≠ 0 := by
    intro he
    apply hw1
    simpa using congrArg (starRingEnd ℂ) (sub_eq_zero.mp he).symm
  have he : -(1 - conj w) * z + -(1 - w) * conj w =
      -(1 - conj w) * (z + (1 - w) / (1 - conj w) * conj w) := by
    field_simp
    <;> ring
  have hden : -(1 - conj w) * z + -(1 - w) * conj w ≠ 0 := by
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr hc) hz
  change mobiusExt _ _ _ _ (z : ExtPlane) = _
  rw [mobiusExt_coe hden]
  congr 1
  dsimp [mobiusFn, sigmaInv]
  rw [div_eq_div_iff hden hz]
  field_simp
  <;> ring

/-- **TV2** (TT:872–888).
- The curve `(0, t⁻¹) * (0, z) = (0, z(t))` is, by `sigma_comp`, `z(t) = σ_z⁻¹(t⁻¹) = (z + k t)/(1 + k z̄ t)`, where
  `k = (1 - z)/(1 - z̄)`.
- Its tangent vector is `dz/dt(0) = (1 - z)(1 - |z|²)/(1 - z̄)`, the right translate of `𝟏 = ∂_z|_{z=∞}` to `(0, z)`.
- Stated for the closed form, together with the identity `σ_z⁻¹(t⁻¹) = (z + k t)/(1 + k z̄ t)` for `t ≠ 0`. -/
theorem TV2 {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∀ t : ℂ, t ≠ 0 → 1 + (1 - z) / (1 - conj z) * conj z * t ≠ 0 →
        sigmaInv z t⁻¹ = (z + (1 - z) / (1 - conj z) * t) / (1 + (1 - z) / (1 - conj z) * conj z * t)) ∧
      HasDerivAt (fun t : ℂ => (z + (1 - z) / (1 - conj z) * t) / (1 + (1 - z) / (1 - conj z) * conj z * t))
        ((1 - z) * (1 - ‖z‖ ^ 2) / (1 - conj z)) 0 := by
  let k : ℂ := (1 - z) / (1 - conj z)
  constructor
  · intro t ht hd
    change (k + t⁻¹ * z) / (t⁻¹ + k * conj z) =
      (z + k * t) / (1 + k * conj z * t)
    have he : t⁻¹ + k * conj z = (1 + k * conj z * t) / t := by
      field_simp
    rw [he]
    field_simp
    <;> ring
  · have hd := ((hasDerivAt_const (0 : ℂ) z).add
        ((hasDerivAt_id (0 : ℂ)).const_mul k)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
        ((hasDerivAt_id (0 : ℂ)).const_mul (k * conj z))) (by simp)
    have hn : (‖z‖ ^ 2 : ℂ) = z * conj z := by
      exact (Complex.mul_conj' z).symm
    convert hd using 1
    · rfl
    · dsimp [k]
      simp only [mul_zero, add_zero, zero_add, mul_one, one_pow, div_one]
      rw [hn]
      ring

/-! ## §1.2.3 The isomorphisms of the tangent spaces -/

/-- The Fourier coefficients `c_n = (1/2π) ∫₀^{2π} u(θ) e^{-inθ} dθ` of a `2π`-periodic function. -/
def fourierCoeff (u : ℝ → ℂ) (n : ℤ) : ℂ := (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π, u θ * exp (-(n * θ * I))

/-- Fourier coefficients of a real vector field have conjugate symmetry
(TT:899–921). Conjugation commutes with the interval integral even under its
totalized convention. -/
theorem fourierCoeff_neg_real (u : ℝ → ℝ) (n : ℤ) :
    fourierCoeff (fun θ => (u θ : ℂ)) (-n) =
      conj (fourierCoeff (fun θ => (u θ : ℂ)) n) := by
  have he : (fun θ : ℝ => (u θ : ℂ) * exp (-((-n : ℤ) * θ * I))) =
      (fun θ : ℝ => conj ((u θ : ℂ) * exp (-(n * θ * I)))) := by
    funext θ
    simp only [map_mul, conj_ofReal, ← exp_conj, map_neg, map_intCast, conj_I,
      Int.cast_neg]
    congr 2
    ring
  have hi (f : ℝ → ℂ) : (∫ θ in (0 : ℝ)..2 * π, conj (f θ)) =
      conj (∫ θ in (0 : ℝ)..2 * π, f θ) := by
    simp only [intervalIntegral, integral_conj, map_sub]
  unfold fourierCoeff
  rw [he, hi, map_mul]
  congr 1
  norm_num [Complex.ext_iff]

/-- The Zygmund class (TT:890): continuous `2π`-periodic `u` with `|u(θ + t) + u(θ - t) - 2u(θ)| ≤ C|t|`. -/
def IsZygmund (u : ℝ → ℝ) : Prop :=
  Continuous u ∧ (∀ θ, u (θ + 2 * π) = u θ) ∧ ∃ C : ℝ, ∀ θ t, |u (θ + t) + u (θ - t) - 2 * u θ| ≤ C * |t|

/-- The real tangent space `T₀^ℝ S¹\Homeo_qs(S¹)` (TT:890–894): Zygmund class real vector fields `u(θ) d/dθ` with
`∫₀^{2π} u(θ) dθ = 0`. -/
def tangentQS : Set (ℝ → ℝ) := {u | IsZygmund u ∧ ∫ θ in (0 : ℝ)..2 * π, u θ = 0}

/-- The memoir's interval convention agrees with Mathlib's Fourier
coefficients on a period (TT:899). -/
theorem fourierCoeff_eq_mathlib (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff f n = _root_.fourierCoeffOn Real.two_pi_pos f n := by
  rw [_root_.fourierCoeffOn_eq_integral]
  simp only [sub_zero]
  simp only [fourierCoeff, smul_eq_mul, real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [_root_.fourier_coe_apply, mul_comm (f θ)]
  congr 1
  congr 1
  push_cast
  field_simp
  ring

/-- Parseval's identity for the Fourier convention used in the memoir
(TT:896, TT:1004). -/
theorem fourierCoeff_hasSum_sq {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2) := by
  simpa only [fourierCoeff_eq_mathlib, sub_zero, smul_eq_mul] using
    _root_.hasSum_sq_fourierCoeffOn Real.two_pi_pos hf

/-- A bounded continuous function has its finite Fourier energy bounded
by the square of its sup bound (TT:896, TT:1004). -/
theorem fourierCoeff_sum_sq_le {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ θ ∈ Icc 0 (2 * π), ‖f θ‖ ≤ C) (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeff f n‖ ^ 2 ≤ C ^ 2 := by
  have hL2 : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))) := by
    apply MemLp.of_bound hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hb θ (Ioc_subset_Icc_self hθ)
  have hs := (fourierCoeff_hasSum_sq hL2).summable.sum_le_tsum s (fun n hn => sq_nonneg _)
  rw [(fourierCoeff_hasSum_sq hL2).tsum_eq] at hs
  apply hs.trans
  have hi : (∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2) ≤ (2 * π) * C ^ 2 := by
    calc
      _ ≤ ∫ θ in (0 : ℝ)..2 * π, C ^ 2 := by
        apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
          (by apply Continuous.intervalIntegrable; fun_prop) (intervalIntegrable_const)
        intro θ hθ
        exact pow_le_pow_left₀ (norm_nonneg _) (hb θ hθ) 2
      _ = _ := by simp
  have hp : 0 < 2 * π := Real.two_pi_pos
  calc
    _ ≤ (2 * π)⁻¹ * ((2 * π) * C ^ 2) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp

/-- Translation multiplies the nth Fourier coefficient by its character
(TT:899). Periodicity suffices, including for totalized integrals. -/
theorem fourierCoeff_translate {f : ℝ → ℂ} (hp : Function.Periodic f (2 * π))
    (t : ℝ) (n : ℤ) :
    fourierCoeff (fun θ => f (θ + t)) n = exp (n * t * I) * fourierCoeff f n := by
  let H : ℝ → ℂ := fun θ => f θ * exp (-(n * θ * I))
  have hstep : exp (-((n : ℂ) * (2 * π) * I)) = 1 := by
    convert exp_int_mul_two_pi_mul_I (-n) using 1 <;> push_cast <;> ring
  have hH : Function.Periodic H (2 * π) := by
    intro θ
    dsimp only [H]
    rw [hp θ]
    have he : -((n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) =
        -(n * θ * I) + -(n * (2 * π) * I) := by push_cast; ring
    rw [he, exp_add, hstep, mul_one]
  have he (θ : ℝ) : f (θ + t) * exp (-(n * θ * I)) = exp (n * t * I) * H (θ + t) := by
    dsimp only [H]
    rw [mul_left_comm, ← exp_add]
    congr 1
    congr 1
    push_cast
    ring
  unfold fourierCoeff
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have hi := hH.intervalIntegral_add_eq t 0
  simp only [zero_add, add_comm (2 * π) t] at *
  rw [hi]
  ring

/-- Additivity of Fourier coefficients for continuous functions (TT:899). -/
theorem fourierCoeff_add_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeff (fun θ => f θ + g θ) n = fourierCoeff f n + fourierCoeff g n := by
  unfold fourierCoeff
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- Scalar multiplication commutes with Fourier coefficients (TT:899). -/
theorem fourierCoeff_const_mul (f : ℝ → ℂ) (a : ℂ) (n : ℤ) :
    fourierCoeff (fun θ => a * f θ) n = a * fourierCoeff f n := by
  unfold fourierCoeff
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The second symmetric difference has its explicit Fourier multiplier
(TT:890, TT:896). -/
theorem fourierCoeff_second_difference {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * π)) (t : ℝ) (n : ℤ) :
    fourierCoeff (fun θ => f (θ + t) + f (θ - t) - 2 * f θ) n =
      (exp (n * t * I) + exp (-(n * t * I)) - 2) * fourierCoeff f n := by
  have he : (fun θ => f (θ + t) + f (θ - t) - 2 * f θ) =
      (fun θ => (f (θ + t) + f (θ + -t)) + (-2 : ℂ) * f θ) := by
    funext θ
    simp only [sub_eq_add_neg]
    ring
  rw [he, fourierCoeff_add_continuous (by fun_prop) (by fun_prop),
    fourierCoeff_add_continuous (by fun_prop) (by fun_prop), fourierCoeff_const_mul,
    fourierCoeff_translate hp, fourierCoeff_translate hp]
  push_cast
  rw [show (n : ℂ) * -(t : ℂ) * I = -(n * t * I) by ring]
  ring

/-- The Zygmund second-difference condition controls every finite Fourier
energy sum after multiplication by its exact difference multiplier
(TT:890, TT:896, TT:1004). -/
theorem zygmund_fourier_energy {u : ℝ → ℝ} (hu : IsZygmund u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (s : Finset ℤ),
      ∑ n ∈ s, ‖(exp (n * t * I) + exp (-(n * t * I)) - 2) *
        fourierCoeff (fun θ => (u θ : ℂ)) n‖ ^ 2 ≤ C ^ 2 * t ^ 2 := by
  obtain ⟨hc, hp, C, hb⟩ := hu
  have hf : Continuous (fun θ => (u θ : ℂ)) := Complex.continuous_ofReal.comp hc
  have hper : Function.Periodic (fun θ => (u θ : ℂ)) (2 * π) := by
    intro θ
    dsimp only
    rw [hp θ]
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t s
  have hbd : ∀ θ ∈ Icc 0 (2 * π),
      ‖(u (θ + t) : ℂ) + u (θ - t) - 2 * u θ‖ ≤ max C 0 * |t| := by
    intro θ hθ
    have he : (u (θ + t) : ℂ) + u (θ - t) - 2 * u θ =
        ((u (θ + t) + u (θ - t) - 2 * u θ : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_real, Real.norm_eq_abs]
    exact (hb θ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hs := fourierCoeff_sum_sq_le (by fun_prop : Continuous
    (fun θ => (u (θ + t) : ℂ) + u (θ - t) - 2 * u θ))
    (mul_nonneg (le_max_right _ _) (abs_nonneg _)) hbd s
  simpa only [fourierCoeff_second_difference hf hper, mul_pow, sq_abs] using hs

/-- On a half-turn away from zero, the second-difference Fourier
multiplier has norm at least two (TT:896, TT:1004). -/
theorem fourier_second_multiplier_norm_ge_two {x : ℝ} (hx : π / 2 ≤ x) (hx' : x ≤ π) :
    2 ≤ ‖exp ((x : ℂ) * I) + exp (-((x : ℂ) * I)) - 2‖ := by
  let z : ℂ := exp ((x : ℂ) * I) + exp (-((x : ℂ) * I)) - 2
  have hre : z.re = 2 * Real.cos x - 2 := by
    dsimp [z]
    simp [Complex.exp_re]
    ring
  have hcos : Real.cos x ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hx
    (by linarith [Real.pi_pos])
  have hb := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
  change 2 ≤ ‖z‖
  rw [hre] at hb
  linarith

/-- The Zygmund condition bounds the square energy in each positive
frequency block by a constant divided by the square of its first frequency
(TT:896, TT:1004). -/
theorem zygmund_fourier_block_sq {u : ℝ → ℝ} (hu : IsZygmund u) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 0 < N →
      (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ico N (2 * N),
        ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2 ≤ D ^ 2 := by
  obtain ⟨C, hC, henergy⟩ := zygmund_fourier_energy hu
  refine ⟨C * π, mul_nonneg hC Real.pi_pos.le, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let t : ℝ := π / (2 * N)
  have ht : 0 < t := div_pos Real.pi_pos (by positivity)
  have he := henergy t ((Finset.Ico N (2 * N)).image (fun n : ℕ => (n : ℤ)))
  rw [Finset.sum_image (fun a _ b _ hab => Int.ofNat_inj.mp hab)] at he
  have hle : (∑ n ∈ Finset.Ico N (2 * N),
      ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2) ≤ C ^ 2 * t ^ 2 := by
    apply le_trans (Finset.sum_le_sum ?_) he
    intro n hn
    obtain ⟨hnL, hnU⟩ := Finset.mem_Ico.mp hn
    have hnLR : (N : ℝ) ≤ n := by exact_mod_cast hnL
    have hnUR : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnU.le
    have hx : π / 2 ≤ (n : ℝ) * t := by
      dsimp [t]
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr
      nlinarith [Real.pi_pos]
    have hx' : (n : ℝ) * t ≤ π := by
      dsimp [t]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr
      nlinarith [Real.pi_pos]
    have hm := fourier_second_multiplier_norm_ge_two hx hx'
    have hcast : (((n : ℝ) * t : ℝ) : ℂ) = (n : ℂ) * t := by push_cast; rfl
    rw [hcast] at hm
    simp only [Int.cast_natCast, norm_mul, mul_pow]
    have hn0 := sq_nonneg ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖
    nlinarith [sq_nonneg (‖exp ((n : ℂ) * t * I) + exp (-((n : ℂ) * t * I)) - 2‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hle (sq_nonneg (N : ℝ))
  have htcalc : (N : ℝ) ^ 2 * (C ^ 2 * t ^ 2) = (C * π) ^ 2 / 4 := by
    dsimp [t]
    field_simp
    ring
  rw [htcalc] at hm
  exact hm.trans (by nlinarith [sq_nonneg (C * π)])

/-- A geometric bound on dyadic block sums proves summability of a
nonnegative sequence (TT:896, TT:1004). -/
theorem summable_of_dyadic_block_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {B q : ℝ} (hB : 0 ≤ B) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ k : ℕ, ∑ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), f n ≤ B * q ^ k) :
    Summable f := by
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_abs_lt_one (by simpa only [abs_of_nonneg hq0] using hq1)
  have hsum : ∀ k : ℕ, (∑ n ∈ Finset.range (2 ^ k), f n) ≤
      f 0 + B * ∑ j ∈ Finset.range k, q ^ j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpow : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
      rw [← Finset.sum_range_add_sum_Ico f hpow]
      have h := add_le_add ih (hb k)
      rw [Finset.sum_range_succ]
      nlinarith
  apply summable_of_sum_range_le hf (c := f 0 + B * ∑' j : ℕ, q ^ j)
  intro m
  have hsub : (∑ n ∈ Finset.range m, f n) ≤ ∑ n ∈ Finset.range (2 ^ m), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.lt_two_pow_self.le))
      (fun n hn hnm => hf n)
  apply hsub.trans ((hsum m).trans ?_)
  exact add_le_add_right (mul_le_mul_of_nonneg_left
    (hgeom.sum_le_tsum _ (fun n hn => pow_nonneg hq0 n)) hB) _

/-- Positive Fourier coefficients of a Zygmund function are absolutely
summable, by Cauchy–Schwarz on dyadic blocks (TT:896). -/
theorem zygmund_fourier_nat_summable {u : ℝ → ℝ} (hu : IsZygmund u) :
    Summable (fun n : ℕ => ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖) := by
  obtain ⟨D, hD, hb⟩ := zygmund_fourier_block_sq hu
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hq0 : 0 ≤ q := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hq1 : q < 1 := by
    apply (inv_lt_one₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
    exact Real.one_lt_sqrt_two
  have hq2 : q ^ 2 = 1 / 2 := by
    dsimp [q]
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  apply summable_of_dyadic_block_bound (fun n => norm_nonneg _) hD hq0 hq1
  intro k
  let s := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let S : ℝ := ∑ n ∈ s, ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖
  let E : ℝ := ∑ n ∈ s, ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2
  have hN : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hblock : ((2 : ℝ) ^ k) ^ 2 * E ≤ D ^ 2 := by
    convert hb (2 ^ k) (by positivity) using 1 <;> simp only [s, E, pow_succ, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1 : ℝ))
    (fun n => ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖)
  have hcard : s.card = 2 ^ k := by
    simp only [s, Nat.card_Ico, pow_succ]
    omega
  have hSE : S ^ 2 ≤ (2 : ℝ) ^ k * E := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard,
      Nat.cast_pow, Nat.cast_ofNat, S, E] using hcs
  have hbound : (2 : ℝ) ^ k * S ^ 2 ≤ D ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hSE hN.le
    nlinarith
  have hprod : (2 : ℝ) ^ k * (q ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, hq2, ← mul_pow]
    norm_num
  have heq : (2 : ℝ) ^ k * (D * q ^ k) ^ 2 = D ^ 2 := by
    calc
      _ = D ^ 2 * ((2 : ℝ) ^ k * (q ^ k) ^ 2) := by ring
      _ = _ := by rw [hprod, mul_one]
  rw [← heq] at hbound
  have hsquare : S ^ 2 ≤ (D * q ^ k) ^ 2 := by nlinarith
  have hnonneg : 0 ≤ D * q ^ k := mul_nonneg hD (pow_nonneg hq0 k)
  change S ≤ D * q ^ k
  nlinarith [sq_nonneg (S - D * q ^ k)]

/-- The dyadic square-energy bound gives every nonnegative Sobolev
order strictly below one (TT:1004). -/
theorem zygmund_fourier_nat_sobolev_nonneg {u : ℝ → ℝ} (hu : IsZygmund u)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ (2 * s) *
      ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2) := by
  obtain ⟨D, hD, hb⟩ := zygmund_fourier_block_sq hu
  let q : ℝ := (2 : ℝ) ^ (2 * s - 2)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply summable_of_dyadic_block_bound (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
    (B := D ^ 2 * (2 : ℝ) ^ (2 * s)) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) hq0 hq1
  intro k
  let N : ℝ := (2 : ℝ) ^ k
  let J := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let E : ℝ := ∑ n ∈ J, ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2
  let S : ℝ := ∑ n ∈ J, (n : ℝ) ^ (2 * s) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  have hblock : N ^ 2 * E ≤ D ^ 2 := by
    convert hb (2 ^ k) (by positivity) using 1 <;> simp only [N, J, E, pow_succ, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  have hSE : S ≤ (2 * N) ^ (2 * s) * E := by
    dsimp only [S, E]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnU := (Finset.mem_Ico.mp hn).2.le
    have hnUR : (n : ℝ) ≤ 2 * N := by
      dsimp [N]
      exact_mod_cast (by simpa only [pow_succ, mul_comm] using hnU : n ≤ 2 * 2 ^ k)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnUR (by linarith)) (sq_nonneg _)
  have hqk : q ^ k = N ^ (2 * s - 2) := by
    dsimp [q, N]
    rw [← Real.rpow_mul_natCast (by norm_num), mul_comm (2 * s - 2),
      Real.rpow_natCast_mul (by norm_num)]
  have hp : N ^ 2 * N ^ (2 * s - 2) = N ^ (2 * s) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN]
    congr 1
    ring
  have hW : (2 * N) ^ (2 * s) = (2 : ℝ) ^ (2 * s) * N ^ (2 * s) :=
    Real.mul_rpow (by norm_num) hN.le
  have hid : N ^ 2 * (D ^ 2 * (2 : ℝ) ^ (2 * s) * q ^ k) = (2 * N) ^ (2 * s) * D ^ 2 := by
    rw [hqk, hW]
    calc
      _ = (D ^ 2 * (2 : ℝ) ^ (2 * s)) * (N ^ 2 * N ^ (2 * s - 2)) := by ring
      _ = _ := by rw [hp]; ring
  have hmul := mul_le_mul_of_nonneg_left hSE (sq_nonneg N)
  have hmul' := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (by positivity : 0 ≤ 2 * N) (2 * s))
  have hscaled : N ^ 2 * S ≤ N ^ 2 * (D ^ 2 * (2 : ℝ) ^ (2 * s) * q ^ k) := by
    rw [hid]
    nlinarith
  change S ≤ D ^ 2 * (2 : ℝ) ^ (2 * s) * q ^ k
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp hscaled

/-- All real Sobolev orders below one follow; negative orders are
dominated by order zero (TT:1004). -/
theorem zygmund_fourier_nat_sobolev {u : ℝ → ℝ} (hu : IsZygmund u)
    {s : ℝ} (hs : s < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ (2 * s) *
      ‖fourierCoeff (fun θ => (u θ : ℂ)) (n : ℤ)‖ ^ 2) := by
  by_cases hs0 : 0 ≤ s
  · exact zygmund_fourier_nat_sobolev_nonneg hu hs0 hs
  · have hzero := zygmund_fourier_nat_sobolev_nonneg hu (s := 0) (by norm_num) (by norm_num)
    apply hzero.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
    intro n
    simp only [mul_zero, Real.rpow_zero, one_mul]
    apply mul_le_of_le_one_left (sq_nonneg _)
    cases n with
    | zero => simp [Real.zero_rpow (by linarith : 2 * s ≠ 0)]
    | succ n =>
      have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      simpa using Real.rpow_le_rpow_of_exponent_le hn (show 2 * s ≤ 0 by linarith)

/-- (TT:896) For `u ∈ T₀^ℝ S¹\Homeo_qs(S¹)` the Fourier series is absolutely convergent. -/
theorem tangentQS_fourier_summable {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    Summable fun n : ℤ => ‖fourierCoeff (fun θ => (u θ : ℂ)) n‖ := by
  have hp := zygmund_fourier_nat_summable hu.1
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨hp, ?_⟩
  simpa only [fourierCoeff_neg_real, norm_conj] using hp

/-- A continuous periodic function with absolutely summable Fourier
coefficients is recovered pointwise by its Fourier series (TT:896–899). -/
theorem fourierCoeff_hasSum_reconstruction {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * π)) (hs : Summable (fourierCoeff f)) (θ : ℝ) :
    HasSum (fun n : ℤ => fourierCoeff f n * exp (n * θ * I)) (f θ) := by
  letI : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let F : C(AddCircle (2 * π), ℂ) := ⟨hp.lift, hf.quotient_liftOn' _⟩
  have hF (t : ℝ) : F (t : AddCircle (2 * π)) = f t := rfl
  have hchar (n : ℤ) (t : ℝ) : _root_.fourier n (t : AddCircle (2 * π)) = exp (n * t * I) := by
    rw [_root_.fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  have hcoeff (n : ℤ) : _root_.fourierCoeff F n = fourierCoeff f n := by
    rw [_root_.fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, hF,
      hchar, Int.cast_neg, neg_mul, smul_eq_mul, real_smul,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, fourierCoeff]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    ring
  have hfs : Summable (_root_.fourierCoeff F) := by
    rw [show _root_.fourierCoeff F = fourierCoeff f from funext hcoeff]
    exact hs
  have h := _root_.has_pointwise_sum_fourier_series_of_summable hfs (θ : AddCircle (2 * π))
  simpa only [hcoeff, hchar, smul_eq_mul, hF] using h

/-- The Zygmund Fourier series reconstructs the original real vector
field at every angle (TT:896–899). -/
theorem tangentQS_fourier_reconstruction {u : ℝ → ℝ} (hu : u ∈ tangentQS) (θ : ℝ) :
    HasSum (fun n : ℤ => fourierCoeff (fun t => (u t : ℂ)) n * exp (n * θ * I)) (u θ : ℂ) := by
  apply fourierCoeff_hasSum_reconstruction (Complex.continuous_ofReal.comp hu.1.1)
  · intro t
    change (u (t + 2 * π) : ℂ) = (u t : ℂ)
    rw [hu.1.2.1 t]
  · exact (tangentQS_fourier_summable hu).of_norm

/-- Zygmund vector fields are determined by their Fourier coefficients
(TT:896–899, TT:982–990). -/
theorem tangentQS_eq_of_fourierCoeff_eq {u v : ℝ → ℝ} (hu : u ∈ tangentQS) (hv : v ∈ tangentQS)
    (h : ∀ n : ℤ, fourierCoeff (fun t => (u t : ℂ)) n = fourierCoeff (fun t => (v t : ℂ)) n) :
    u = v := by
  funext θ
  apply Complex.ofReal_injective
  have huθ := tangentQS_fourier_reconstruction hu θ
  have hvθ := tangentQS_fourier_reconstruction hv θ
  simp_rw [h] at huθ
  exact huθ.unique hvθ

/-- `u₊(z) = i Σ_{n ≥ 1} c_n z^{n+1}` (TT:917), holomorphic on `𝔻` with `u₊(0) = 0`. -/
def uPlus (u : ℝ → ℝ) (z : ℂ) : ℂ := I * ∑' n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) (n + 1) * z ^ (n + 2)

/-- `u₋(z) = i Σ_{n ≥ 1} c_{-n} z^{1-n}` (TT:921), holomorphic on `𝔻*`. -/
def uMinus (u : ℝ → ℝ) (z : ℂ) : ℂ := I * ∑' n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) (-(n + 1)) * z ^ (-(n : ℤ))

/-- (TT:899–921) On `S¹`, `ũ(z) = i Σ_{n ≠ 0} c_n z^{n+1} = u₊(z) + u₋(z)`. -/
theorem utilde_decomposition {u : ℝ → ℝ} (hu : u ∈ tangentQS) {z : ℂ} (hz : z ∈ unitCircle) :
    I * ∑' n : ℤ, (if n = 0 then 0 else fourierCoeff (fun θ => (u θ : ℂ)) n * z ^ (n + 1)) = uPlus u z + uMinus u z := by
  let c : ℤ → ℂ := fourierCoeff (fun θ => (u θ : ℂ))
  let f : ℤ → ℂ := fun n => if n = 0 then 0 else c n * z ^ (n + 1)
  let p : ℕ → ℂ := fun n => c (n + 1) * z ^ (n + 2)
  let q : ℕ → ℂ := fun n => c (-(n + 1)) * z ^ (-(n : ℤ))
  have hpos (n : ℕ) : f ((n + 1 : ℕ) : ℤ) = p n := by
    have hn : (n : ℤ) + 1 ≠ 0 := by omega
    simp [f, p, Nat.cast_add, Nat.cast_one, ← zpow_natCast, add_assoc, hn]
  have hneg (n : ℕ) : f (-(n + 1)) = q n := by
    have hn : -(n + 1 : ℤ) ≠ 0 := by omega
    have he : -(n + 1 : ℤ) + 1 = -(n : ℤ) := by ring
    simp only [f, q, if_neg hn, he]
  have hnorm (n : ℕ) : ‖p n‖ = ‖q n‖ := by
    simp only [p, q, norm_mul, norm_pow, Complex.norm_zpow,
      show ‖z‖ = 1 from hz, one_pow, one_zpow, mul_one]
    simpa only [norm_conj] using (congrArg norm (fourierCoeff_neg_real u (n + 1))).symm
  have hs : Summable p ↔ Summable q := by
    constructor
    · intro h
      exact summable_norm_iff.mp ((summable_norm_iff.mpr h).congr hnorm)
    · intro h
      exact summable_norm_iff.mp ((summable_norm_iff.mpr h).congr fun n => (hnorm n).symm)
  have hp0 : Summable (fun n : ℕ => f n) ↔ Summable p := by
    rw [← summable_nat_add_iff 1]
    simp only [hpos]
  have he : (∑' n : ℤ, f n) = (∑' n : ℕ, p n) + ∑' n : ℕ, q n := by
    by_cases hp : Summable p
    · have hp' := hp0.mpr hp
      have hq' : Summable (fun n : ℕ => f (-(n + 1))) :=
        (hs.mp hp).congr fun n => (hneg n).symm
      rw [tsum_of_nat_of_neg_add_one hp' hq', hp'.tsum_eq_zero_add]
      rw [show f ((0 : ℕ) : ℤ) = 0 from rfl, zero_add]
      exact congrArg₂ (fun x y : ℂ => x + y) (tsum_congr hpos) (tsum_congr hneg)
    · have hq : ¬ Summable q := fun h => hp (hs.mpr h)
      have hf : ¬ Summable f := fun h => hp (hp0.mp
        (h.comp_injective Nat.cast_injective))
      rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hp,
        tsum_eq_zero_of_not_summable hq, zero_add]
  change I * (∑' n : ℤ, f n) = I * (∑' n : ℕ, p n) + I * ∑' n : ℕ, q n
  rw [he, mul_add]

/-- The conjugation operator (the almost complex structure `J`, TT:927) on Fourier coefficients:
`(J c)_n = i sgn(n) c_n`. -/
def conjugationJ (c : ℤ → ℂ) (n : ℤ) : ℂ := I * (Int.sign n : ℂ) * c n

/-- (TT:935) The holomorphic and anti-holomorphic parts `v = (u - iJu)/2`, `v̄ = (u + iJu)/2` keep the coefficients
with `n ≥ 1`, respectively `n ≤ -1`. -/
theorem holomorphic_part (c : ℤ → ℂ) (hc : c 0 = 0) (n : ℤ) :
    (c n - I * conjugationJ c n) / 2 = (if 1 ≤ n then c n else 0) ∧
      (c n + I * conjugationJ c n) / 2 = (if n ≤ -1 then c n else 0) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : n ≤ -1 := by omega
    have hn'' : ¬ 1 ≤ n := by omega
    simp [conjugationJ, Int.sign_eq_neg_one_of_neg hn, hn', hn'',
      ← mul_assoc, Complex.I_mul_I]
  · subst n
    simp [hc, conjugationJ]
  · have hn' : 1 ≤ n := by omega
    have hn'' : ¬ n ≤ -1 := by omega
    simp [conjugationJ, Int.sign_eq_one_of_pos hn, hn', hn'',
      ← mul_assoc, Complex.I_mul_I]

/-- The Sobolev space `𝓗ˢ(S¹)` (TT:953) of complex vector fields `Σ a_n e^{inθ} d/dθ`, in terms of coefficients:
`Σ |n|^{2s} |a_n|² < ∞`. -/
def sobolevH (s : ℝ) : Set (ℤ → ℂ) := {a | Summable fun n : ℤ => (|(n : ℝ)| ^ (2 * s)) * ‖a n‖ ^ 2}

-- `TS2` moved to `Ch1/TS2.lean` (2026-10-26).

/-- A scalar power series converging throughout the disk converges
absolutely at every smaller radius (TT:992–1001). -/
theorem disk_series_summable_norm {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖c n‖ * r ^ n) := by
  let R : ℝ≥0 := ⟨(r + 1) / 2, by linarith⟩
  have hR0 : (0 : ℝ) < R := by change 0 < (r + 1) / 2; linarith
  have hR1 : (R : ℝ) < 1 := by change (r + 1) / 2 < 1; linarith
  have hrR : r < R := by change r < (r + 1) / 2; linarith
  have hz : ((R : ℝ) : ℂ) ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hR0] using hR1
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have ht : Tendsto (fun n => ‖p n‖ * (R : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) := by
    have h := (hc ((R : ℝ) : ℂ) hz).summable.tendsto_atTop_zero.norm
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      norm_real, Real.norm_eq_abs, abs_of_pos hR0, norm_zero] using h
  have hrad : (R : ℝ≥0∞) ≤ p.radius := p.le_radius_of_tendsto ht
  let rNN : ℝ≥0 := ⟨r, hr0⟩
  have hradius : (rNN : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast hrR) hrad
  have hh := p.summable_norm_mul_pow hradius
  simp only [p, FormalMultilinearSeries.ofScalars_norm] at hh
  change Summable (fun n => ‖c n‖ * r ^ n) at hh
  exact hh

/-- Fourier orthogonality for exponential modes in the memoir's
normalization (TT:899, TT:992). -/
theorem fourierCoeff_exponential (k n : ℤ) :
    fourierCoeff (fun θ : ℝ => exp (k * θ * I)) n = if n = k then 1 else 0 := by
  unfold fourierCoeff
  have he : (fun θ : ℝ => exp (k * θ * I) * exp (-(n * θ * I))) =
      fun θ : ℝ => exp ((((k - n : ℤ) : ℂ) * I) * θ) := by
    funext θ
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  by_cases hnk : n = k
  · subst n
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp
    field_simp
  · have hk : ((k - n : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast (sub_ne_zero.mpr (fun h => hnk h.symm))
    rw [integral_exp_mul_complex (mul_ne_zero hk I_ne_zero)]
    have hp : exp ((((k - n : ℤ) : ℂ) * I) * ((2 * π : ℝ) : ℂ)) = 1 := by
      convert exp_int_mul_two_pi_mul_I (k - n) using 1
      congr 1
      push_cast
      ring
    rw [hp]
    simp [hnk]

/-- The scalar Taylor coefficients of a disk series are its Fourier
coefficients on every interior circle (TT:992–1001). -/
theorem disk_series_fourierCoeff {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) (m : ℤ) = c m * (r : ℂ) ^ m := by
  have hsum := disk_series_summable_norm hc hr0 hr1
  have hexpnorm (θ : ℝ) : ‖exp ((θ : ℂ) * I)‖ = 1 := by simp [norm_exp]
  have hrad (θ : ℝ) : ‖(r : ℂ) * exp (θ * I)‖ = r := by
    rw [norm_mul, hexpnorm, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hneg (θ : ℝ) : ‖exp (-((m : ℤ) * θ * I))‖ = 1 := by simp [norm_exp]
  let f : ℕ → ℝ → ℂ := fun n θ => c n * ((r : ℂ) * exp (θ * I)) ^ n * exp (-((m : ℤ) * θ * I))
  have hi := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * π)))
    (F := f) (f := fun θ => F ((r : ℂ) * exp (θ * I)) * exp (-((m : ℤ) * θ * I)))
    (fun n _ => ‖c n‖ * r ^ n)
    (fun n => by dsimp [f]; fun_prop)
    (fun n => Filter.Eventually.of_forall fun θ => by
      simp only [f, norm_mul, norm_pow, hrad, hneg, mul_one, le_refl])
    (Filter.Eventually.of_forall fun _ => hsum)
    (integrable_const _)
    (Filter.Eventually.of_forall fun θ =>
      (hc _ (mem_ball_zero_iff.mpr (by rw [hrad]; exact hr1))).mul_right _)
  have hi' := hi.mul_left (1 / (2 * π : ℂ))
  have hiC : HasSum (fun n => fourierCoeff
      (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) (m : ℤ))
      (fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) (m : ℤ)) := by
    simpa only [fourierCoeff, intervalIntegral.integral_of_le Real.two_pi_pos.le, f] using hi'
  have hcoeff (n : ℕ) : fourierCoeff
      (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) (m : ℤ) =
      if n = m then c m * (r : ℂ) ^ m else 0 := by
    have hfun : (fun θ : ℝ => c n * ((r : ℂ) * exp (θ * I)) ^ n) =
        fun θ : ℝ => (c n * (r : ℂ) ^ n) * exp ((n : ℤ) * θ * I) := by
      funext θ
      rw [mul_pow, ← exp_nat_mul]
      push_cast
      ring_nf
    rw [hfun, fourierCoeff_const_mul, fourierCoeff_exponential]
    by_cases hnm : n = m
    · simp [hnm]
    · have hmn : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast Ne.symm hnm
      simp [hnm, hmn]
  simp_rw [hcoeff] at hiC
  exact hiC.tsum_eq.symm.trans (by simp)

/-- The weighted sup norm bounds a disk A-infinity function on every
interior circle (TT:363, TT:992–1001). -/
theorem AInf_disc_pointwise_bound (φ : AInf unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖AInf.toFun φ z‖ ≤ ‖φ‖ / (1 - ‖z‖ ^ 2) ^ 2 := by
  have hn := φ.1.norm_coe_le_norm ⟨z, hz⟩
  simp only [AInf.toFun, unweight, dif_pos hz, norm_div, norm_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    norm_real, Real.norm_eq_abs, sq_abs]
  exact div_le_div_of_nonneg_right hn (sq_nonneg _)

/-- Parseval bounds the finite square energy of the Taylor coefficients
at any interior radius (TT:992–1001). -/
theorem AInf_disk_series_energy (φ : AInf unitDisc) {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (AInf.toFun φ z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : Finset ℕ) :
    ∑ n ∈ J, ‖c n‖ ^ 2 * r ^ (2 * n) ≤ (‖φ‖ / (1 - r ^ 2) ^ 2) ^ 2 := by
  have hrad (θ : ℝ) : ‖(r : ℂ) * exp (θ * I)‖ = r := by
    simp [norm_mul, norm_exp, abs_of_nonneg hr0]
  have hz (θ : ℝ) : (r : ℂ) * exp (θ * I) ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [hrad]; exact hr1)
  have hf : Continuous (fun θ : ℝ => AInf.toFun φ ((r : ℂ) * exp (θ * I))) :=
    φ.property.continuousOn.comp_continuous (by fun_prop) hz
  have hb : ∀ θ ∈ Icc 0 (2 * π),
      ‖AInf.toFun φ ((r : ℂ) * exp (θ * I))‖ ≤ ‖φ‖ / (1 - r ^ 2) ^ 2 := by
    intro θ hθ
    simpa only [hrad] using AInf_disc_pointwise_bound φ (hz θ)
  have he := fourierCoeff_sum_sq_le hf (div_nonneg (norm_nonneg _) (sq_nonneg _)) hb
    (J.image (fun n : ℕ => (n : ℤ)))
  rw [Finset.sum_image (fun a _ b _ hab => Int.ofNat_inj.mp hab)] at he
  simpa only [disk_series_fourierCoeff hc hr0 hr1, norm_mul, norm_pow, norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0, mul_pow, ← pow_mul, mul_comm _ 2] using he

/-- The coefficients in TS3 satisfy the same dyadic square-energy bound
as Zygmund Fourier coefficients (TT:992–1001). -/
theorem TS3_coefficient_block (φ : AInf unitDisc) (a : ℕ → ℂ)
    (ha : ∀ z ∈ unitDisc, HasSum (fun n : ℕ =>
      ((n + 2 : ℕ) ^ 3 - (n + 2 : ℕ) : ℂ) * a (n + 2) * z ^ n) (AInf.toFun φ z))
    (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ico N (2 * N), ‖a (n + 2)‖ ^ 2 ≤ (128 * ‖φ‖) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let r : ℝ := 1 - (8 * N : ℝ)⁻¹
  have hinv0 : 0 < (8 * N : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  have hinv : (8 * N : ℝ)⁻¹ ≤ 1 / 8 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * N)).mpr
    nlinarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hw : 0 < 1 - r ^ 2 := by nlinarith
  have hprod : (8 * N : ℝ) * (1 - r) = 1 := by
    dsimp [r]
    field_simp
    ring
  have hrecip : (1 - r ^ 2)⁻¹ ≤ (8 : ℝ) * N := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hw).mpr
    have hr : r ^ 2 ≤ r := by nlinarith
    nlinarith
  have hsup : ‖φ‖ / (1 - r ^ 2) ^ 2 ≤ 64 * ‖φ‖ * (N : ℝ) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hsq := pow_le_pow_left₀ (inv_nonneg.mpr hw.le) hrecip 2
    have hm := mul_le_mul_of_nonneg_left hsq (norm_nonneg φ)
    nlinarith
  let c : ℕ → ℂ := fun n => ((n + 2 : ℕ) ^ 3 - (n + 2 : ℕ) : ℂ) * a (n + 2)
  have he := AInf_disk_series_energy φ (c := c) ha hr0.le hr1 (Finset.Ico N (2 * N))
  have hupper : (∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 * r ^ (2 * n)) ≤
      4096 * ‖φ‖ ^ 2 * (N : ℝ) ^ 4 := by
    have hh := pow_le_pow_left₀ (div_nonneg (norm_nonneg φ) (sq_nonneg _)) hsup 2
    nlinarith
  have hlow : (N : ℝ) ^ 6 / 2 * (∑ n ∈ Finset.Ico N (2 * N), ‖a (n + 2)‖ ^ 2) ≤
      ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 * r ^ (2 * n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hnL, hnU⟩ := Finset.mem_Ico.mp hn
    have hnLR : (N : ℝ) ≤ n := by exact_mod_cast hnL
    have hnUR : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnU.le
    have hbern := one_add_mul_le_pow (a := -((8 * N : ℝ)⁻¹)) (by linarith : (-2 : ℝ) ≤ -((8 * N : ℝ)⁻¹)) (2 * n)
    have hrpow : (1 / 2 : ℝ) ≤ r ^ (2 * n) := by
      have hsmall : (2 * n : ℝ) * (8 * N : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * N)).mpr
        nlinarith
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hbern
      change 1 + (2 * n : ℝ) * -((8 * N : ℝ)⁻¹) ≤ r ^ (2 * n) at hbern
      linarith
    have hpoly : (N : ℝ) ^ 3 ≤ (n + 2 : ℝ) ^ 3 - (n + 2) := by
      have hp := pow_le_pow_left₀ hNR.le hnLR 3
      nlinarith [sq_nonneg (n : ℝ)]
    have hnorm : ‖((n + 2 : ℕ) ^ 3 - (n + 2 : ℕ) : ℂ)‖ = (n + 2 : ℝ) ^ 3 - (n + 2) := by
      have heq : ((n + 2 : ℕ) ^ 3 - (n + 2 : ℕ) : ℂ) =
          (((n + 2 : ℝ) ^ 3 - (n + 2) : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by positivity) hpoly)]
    have hs : (N : ℝ) ^ 6 * ‖a (n + 2)‖ ^ 2 ≤ ‖c n‖ ^ 2 := by
      simp only [c, norm_mul, mul_pow, hnorm]
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hpoly 2) (sq_nonneg ‖a (n + 2)‖)
      nlinarith
    have hh := mul_le_mul hs hrpow (by norm_num) (sq_nonneg ‖c n‖)
    nlinarith
  have hh := hlow.trans hupper
  have hscaled : (N : ℝ) ^ 4 * ((N : ℝ) ^ 2 *
      ∑ n ∈ Finset.Ico N (2 * N), ‖a (n + 2)‖ ^ 2) ≤
      (N : ℝ) ^ 4 * (128 * ‖φ‖) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ‖φ‖) (pow_nonneg hNR.le 4)]
  exact (mul_le_mul_iff_right₀ (pow_pos hNR 4)).mp hscaled

/-- A square-decaying frequency-block bound implies every shifted
Sobolev weight of nonnegative order below one is summable (TT:992–1001). -/
theorem summable_shifted_rpow_of_block {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {D : ℝ} (hb : ∀ N : ℕ, 0 < N → (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ico N (2 * N), f n ≤ D ^ 2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (2 * s) * f n) := by
  let q : ℝ := (2 : ℝ) ^ (2 * s - 2)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply summable_of_dyadic_block_bound (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf n))
    (B := D ^ 2 * (4 : ℝ) ^ (2 * s)) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) hq0 hq1
  intro k
  let N : ℝ := (2 : ℝ) ^ k
  let J := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let E : ℝ := ∑ n ∈ J, f n
  let S : ℝ := ∑ n ∈ J, ((n + 2 : ℕ) : ℝ) ^ (2 * s) * f n
  have hN : 0 < N := by dsimp [N]; positivity
  have hblock : N ^ 2 * E ≤ D ^ 2 := by
    convert hb (2 ^ k) (by positivity) using 1 <;> simp only [N, J, E, pow_succ, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  have hSE : S ≤ (4 * N) ^ (2 * s) * E := by
    dsimp only [S, E]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnU := (Finset.mem_Ico.mp hn).2.le
    have hNN : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
    have hnUR : ((n + 2 : ℕ) : ℝ) ≤ 4 * N := by
      dsimp [N]
      have hn' : n + 2 ≤ 4 * 2 ^ k := by rw [pow_succ] at hnU; omega
      exact_mod_cast hn'
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnUR (by linarith)) (hf n)
  have hqk : q ^ k = N ^ (2 * s - 2) := by
    dsimp [q, N]
    rw [← Real.rpow_mul_natCast (by norm_num), mul_comm (2 * s - 2),
      Real.rpow_natCast_mul (by norm_num)]
  have hp : N ^ 2 * N ^ (2 * s - 2) = N ^ (2 * s) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hN]
    congr 1
    ring
  have hW : (4 * N) ^ (2 * s) = (4 : ℝ) ^ (2 * s) * N ^ (2 * s) :=
    Real.mul_rpow (by norm_num) hN.le
  have hid : N ^ 2 * (D ^ 2 * (4 : ℝ) ^ (2 * s) * q ^ k) = (4 * N) ^ (2 * s) * D ^ 2 := by
    rw [hqk, hW]
    calc
      _ = (D ^ 2 * (4 : ℝ) ^ (2 * s)) * (N ^ 2 * N ^ (2 * s - 2)) := by ring
      _ = _ := by rw [hp]; ring
  have hmul := mul_le_mul_of_nonneg_left hSE (sq_nonneg N)
  have hmul' := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (by positivity : 0 ≤ 4 * N) (2 * s))
  have hscaled : N ^ 2 * S ≤ N ^ 2 * (D ^ 2 * (4 : ℝ) ^ (2 * s) * q ^ k) := by
    rw [hid]
    nlinarith
  change S ≤ D ^ 2 * (4 : ℝ) ^ (2 * s) * q ^ k
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp hscaled

/-- **TS3** (TT:992–1001). If `φ(z) = Σ_{n ≥ 2} (n³ - n) a_n z^{n-2} ∈ A∞(𝔻)`, then `Σ_{n ≥ 2} n^{2s} |a_n|² < ∞` for
all `s < 1`. -/
theorem TS3 (φ : AInf unitDisc) (a : ℕ → ℂ)
    (ha : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => ((n + 2 : ℕ) ^ 3 - (n + 2 : ℕ) : ℂ) * a (n + 2) * z ^ n) (AInf.toFun φ z))
    {s : ℝ} (hs : s < 1) :
    Summable fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (2 * s) * ‖a (n + 2)‖ ^ 2 := by
  have hh := summable_shifted_rpow_of_block (fun n => sq_nonneg ‖a (n + 2)‖)
    (TS3_coefficient_block φ a ha) (s := max s 0) (le_max_right _ _)
    (max_lt hs (by norm_num))
  apply hh.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
  intro n
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (show 1 ≤ n + 2 by omega)
  · linarith [le_max_left s 0]

/-- An absolutely summable scalar coefficient sequence defines a
holomorphic function on the disk (TT:917). -/
theorem scalar_series_analyticOnNhd {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    AnalyticOnNhd ℂ (fun z => ∑' n : ℕ, a n * z ^ n) unitDisc := by
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hr : (1 : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable_norm (r := 1)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one] using ha
  intro z hz
  have hzn : (‖z‖₊ : ℝ≥0∞) < 1 := by exact_mod_cast (mem_ball_zero_iff.mp hz)
  have hzball : z ∈ Metric.eball 0 p.radius := by
    simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using lt_of_lt_of_le hzn hr
  have h := p.analyticOnNhd z hzball
  change AnalyticAt ℂ (FormalMultilinearSeries.ofScalarsSum a) z at h
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using h

/-- The positive-frequency vector field factors as z squared times
an analytic scalar power series (TT:917). -/
theorem uPlus_eq_series (u : ℝ → ℝ) (z : ℂ) :
    uPlus u z = I * z ^ 2 *
      ∑' n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) (n + 1) * z ^ n := by
  unfold uPlus
  simp_rw [pow_add, ← mul_assoc]
  rw [tsum_mul_right]
  ring

/-- Positive-frequency Zygmund vector fields are holomorphic in the
disk (TT:917, TT:982–990). -/
theorem uPlus_analyticOnNhd {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    AnalyticOnNhd ℂ (uPlus u) unitDisc := by
  have ha : Summable (fun n : ℕ => ‖fourierCoeff (fun θ => (u θ : ℂ)) (n + 1)‖) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (zygmund_fourier_nat_summable hu.1)
  have hA := scalar_series_analyticOnNhd ha
  intro z hz
  have hh : AnalyticAt ℂ (fun w : ℂ => I * w ^ 2 *
      ∑' n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) (n + 1) * w ^ n) z :=
    (analyticAt_const.mul (analyticAt_id.pow 2)).mul (hA z hz)
  simpa only [← uPlus_eq_series] using hh

/-- The first three jets of the positive-frequency vector field are
fixed by its first Fourier coefficient (TT:917, TT:982–990). -/
theorem uPlus_jets {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    uPlus u 0 = 0 ∧ deriv (uPlus u) 0 = 0 ∧
      deriv (deriv (uPlus u)) 0 = 2 * I * fourierCoeff (fun θ => (u θ : ℂ)) 1 := by
  let H : ℂ → ℂ := fun z => ∑' n : ℕ, fourierCoeff (fun θ => (u θ : ℂ)) (n + 1) * z ^ n
  have ha : Summable (fun n : ℕ => ‖fourierCoeff (fun θ => (u θ : ℂ)) (n + 1)‖) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (zygmund_fourier_nat_summable hu.1)
  have hH : AnalyticAt ℂ H 0 := scalar_series_analyticOnNhd ha 0 (mem_ball_self (by norm_num))
  have hH0 : H 0 = fourierCoeff (fun θ => (u θ : ℂ)) 1 := by
    calc
      _ = fourierCoeff (fun θ => (u θ : ℂ)) ((0 : ℕ) + 1) * (0 : ℂ) ^ (0 : ℕ) :=
        tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])
      _ = _ := by norm_num
  let P : ℂ → ℂ := fun z => I * (z ^ 2 * H z)
  have heP : uPlus u = P := by
    funext z
    rw [uPlus_eq_series]
    dsimp [P, H]
    ring
  have hd (z : ℂ) (hz : AnalyticAt ℂ H z) :
      HasDerivAt P (I * (2 * z * H z + z ^ 2 * deriv H z)) z := by
    convert (((hasDerivAt_id z).pow 2).mul hz.differentiableAt.hasDerivAt).const_mul I using 1 <;>
      simp only [P, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq,
        Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  have heD : deriv P =ᶠ[𝓝 (0 : ℂ)] (fun z => I * (2 * z * H z + z ^ 2 * deriv H z)) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    exact (hd z hz).deriv
  have hdQ : HasDerivAt (fun z => I * (2 * z * H z + z ^ 2 * deriv H z))
      (2 * I * H 0) 0 := by
    convert ((((hasDerivAt_id (0 : ℂ)).const_mul 2).mul hH.differentiableAt.hasDerivAt).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul hH.deriv.differentiableAt.hasDerivAt)).const_mul I using 1 <;>
      simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq, zero_mul, mul_zero,
        zero_pow (by norm_num : 2 ≠ 0), zero_add, add_zero, Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, mul_one] <;> ring
  rw [heP]
  refine ⟨by simp [P], by simpa using (hd 0 hH).deriv, ?_⟩
  rw [heD.deriv_eq, hdQ.deriv, hH0]

/-- Equal third derivatives and the vanishing low modes determine the
positive-frequency disk maps (TT:982–990). -/
theorem uPlus_eqOn_of_third_deriv_eq {u v : ℝ → ℝ} (hu : u ∈ tangentQS) (hv : v ∈ tangentQS)
    (hu1 : fourierCoeff (fun θ => (u θ : ℂ)) 1 = 0)
    (hv1 : fourierCoeff (fun θ => (v θ : ℂ)) 1 = 0)
    (h : EqOn (iteratedDeriv 3 (uPlus u)) (iteratedDeriv 3 (uPlus v)) unitDisc) :
    EqOn (uPlus u) (uPlus v) unitDisc := by
  have hU := uPlus_analyticOnNhd hu
  have hV := uPlus_analyticOnNhd hv
  obtain ⟨hu0, huD, huDD⟩ := uPlus_jets hu
  obtain ⟨hv0, hvD, hvDD⟩ := uPlus_jets hv
  rw [hu1, mul_zero] at huDD
  rw [hv1, mul_zero] at hvDD
  have hzero : (0 : ℂ) ∈ unitDisc := mem_ball_self (by norm_num)
  have hconn := (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
  have h3 : EqOn (deriv (deriv (deriv (uPlus u)))) (deriv (deriv (deriv (uPlus v)))) unitDisc := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  have h2 := isOpen_ball.eqOn_of_deriv_eq hconn
    (fun z hz => (hU z hz).deriv.deriv.differentiableAt.differentiableWithinAt)
    (fun z hz => (hV z hz).deriv.deriv.differentiableAt.differentiableWithinAt) h3 hzero
    (huDD.trans hvDD.symm)
  have h1 := isOpen_ball.eqOn_of_deriv_eq hconn
    (fun z hz => (hU z hz).deriv.differentiableAt.differentiableWithinAt)
    (fun z hz => (hV z hz).deriv.differentiableAt.differentiableWithinAt) h2 hzero
    (huD.trans hvD.symm)
  exact isOpen_ball.eqOn_of_deriv_eq hconn
    (fun z hz => (hU z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hV z hz).differentiableAt.differentiableWithinAt) h1 hzero
    (hu0.trans hv0.symm)

/-- The scalar series used in uPlus has its intended sum on the disk
(TT:917). -/
theorem scalar_series_hasSum {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    {z : ℂ} (hz : z ∈ unitDisc) :
    HasSum (fun n => a n * z ^ n) (∑' n : ℕ, a n * z ^ n) := by
  have hn : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hs : Summable (fun n => ‖a n * z ^ n‖) := by
    apply ha.of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hn)
  exact hs.of_norm.hasSum

/-- The mean-zero tangent condition is exactly the vanishing constant
Fourier coefficient (TT:890–899). -/
theorem tangentQS_fourierCoeff_zero {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    fourierCoeff (fun θ => (u θ : ℂ)) 0 = 0 := by
  simp only [fourierCoeff, Int.cast_zero, zero_mul, neg_zero, exp_zero, mul_one,
    intervalIntegral.integral_ofReal, hu.2, Complex.ofReal_zero, mul_zero]

/-- The positive-frequency disk map determines a real mean-zero
Zygmund vector field (TT:917, TT:982–990). -/
theorem tangentQS_eq_of_uPlus_eqOn {u v : ℝ → ℝ} (hu : u ∈ tangentQS) (hv : v ∈ tangentQS)
    (h : EqOn (uPlus u) (uPlus v) unitDisc) : u = v := by
  let cu : ℕ → ℂ := fun n => fourierCoeff (fun θ => (u θ : ℂ)) (n + 1)
  let cv : ℕ → ℂ := fun n => fourierCoeff (fun θ => (v θ : ℂ)) (n + 1)
  let H : (ℕ → ℂ) → ℂ → ℂ := fun c z => ∑' n : ℕ, c n * z ^ n
  have hcu : Summable (fun n => ‖cu n‖) := by
    simpa only [cu, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (zygmund_fourier_nat_summable hu.1)
  have hcv : Summable (fun n => ‖cv n‖) := by
    simpa only [cv, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (zygmund_fourier_nat_summable hv.1)
  have hHu : ∀ z ∈ unitDisc, HasSum (fun n => cu n * z ^ n) (H cu z) :=
    fun z hz => scalar_series_hasSum hcu hz
  have hHv : ∀ z ∈ unitDisc, HasSum (fun n => cv n * z ^ n) (H cv z) :=
    fun z hz => scalar_series_hasSum hcv hz
  have he : (fun θ : ℝ => H cu ((1 / 2 : ℂ) * exp (θ * I))) =
      (fun θ : ℝ => H cv ((1 / 2 : ℂ) * exp (θ * I))) := by
    funext θ
    let z : ℂ := (1 / 2 : ℂ) * exp (θ * I)
    have hz : z ∈ unitDisc := by
      apply mem_ball_zero_iff.mpr
      norm_num [z, norm_mul, norm_exp]
    have hz0 : z ≠ 0 := mul_ne_zero (by norm_num) (exp_ne_zero _)
    have hh := h hz
    rw [uPlus_eq_series, uPlus_eq_series] at hh
    exact mul_left_cancel₀ (mul_ne_zero I_ne_zero (pow_ne_zero 2 hz0)) hh
  have hpos (n : ℕ) : cu n = cv n := by
    have hh := congrArg (fun f : ℝ → ℂ => fourierCoeff f (n : ℤ)) he
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hhalf, disk_series_fourierCoeff hHu (by norm_num) (by norm_num),
      disk_series_fourierCoeff hHv (by norm_num) (by norm_num)] at hh
    exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : ((1 / 2 : ℝ) : ℂ) ≠ 0)) hh
  apply tangentQS_eq_of_fourierCoeff_eq hu hv
  intro n
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (tangentQS_fourierCoeff_zero hu).trans (tangentQS_fourierCoeff_zero hv).symm
    | succ n =>
      change fourierCoeff (fun t => (u t : ℂ)) (((n + 1 : ℕ) : ℤ)) =
        fourierCoeff (fun t => (v t : ℂ)) (((n + 1 : ℕ) : ℤ))
      push_cast
      exact hpos n
  | negSucc n =>
    change fourierCoeff (fun θ => (u θ : ℂ)) (-((n : ℤ) + 1)) =
      fourierCoeff (fun θ => (v θ : ℂ)) (-((n : ℤ) + 1))
    rw [fourierCoeff_neg_real, fourierCoeff_neg_real]
    exact congrArg conj (hpos n)

/-- Injectivity in TS2: normalized real Zygmund vector fields are
determined by the third derivative of their positive-frequency part
(TT:982–990). This does not assume the unfinished surjectivity assertion. -/
theorem TS2_injective {u v : ℝ → ℝ} (hu : u ∈ tangentQS) (hv : v ∈ tangentQS)
    (hu1 : fourierCoeff (fun θ => (u θ : ℂ)) 1 = 0)
    (hv1 : fourierCoeff (fun θ => (v θ : ℂ)) 1 = 0)
    (h : EqOn (iteratedDeriv 3 (uPlus u)) (iteratedDeriv 3 (uPlus v)) unitDisc) : u = v :=
  tangentQS_eq_of_uPlus_eqOn hu hv (uPlus_eqOn_of_third_deriv_eq hu hv hu1 hv1 h)

/-- Every disk holomorphic function has a triple primitive with all
three low jets zero, the analytic inverse needed in TS2 (TT:982–990).
The boundary Zygmund condition is a separate step. -/
theorem exists_normalized_triple_primitive {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
      deriv (deriv F) 0 = 0 ∧ EqOn (iteratedDeriv 3 F) φ unitDisc := by
  obtain ⟨G₁, hG₁0, hG₁⟩ := hφ.isExactOn_ball.with_val_at 0 0
  have hd₁ : DifferentiableOn ℂ G₁ unitDisc := fun z hz => (hG₁ z hz).differentiableAt.differentiableWithinAt
  obtain ⟨G₂, hG₂0, hG₂⟩ := hd₁.isExactOn_ball.with_val_at 0 0
  have hd₂ : DifferentiableOn ℂ G₂ unitDisc := fun z hz => (hG₂ z hz).differentiableAt.differentiableWithinAt
  obtain ⟨F, hF0, hF⟩ := hd₂.isExactOn_ball.with_val_at 0 0
  have hdF : DifferentiableOn ℂ F unitDisc := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have he₂ : EqOn (deriv F) G₂ unitDisc := fun z hz => (hF z hz).deriv
  have he₁ : EqOn (deriv (deriv F)) G₁ unitDisc := by
    intro z hz
    have he : deriv F =ᶠ[𝓝 z] G₂ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) he₂
    rw [he.deriv_eq]
    exact (hG₂ z hz).deriv
  have heφ : EqOn (iteratedDeriv 3 F) φ unitDisc := by
    intro z hz
    have he : deriv (deriv F) =ᶠ[𝓝 z] G₁ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) he₁
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, he.deriv_eq] using (hG₁ z hz).deriv
  have hzero : (0 : ℂ) ∈ unitDisc := mem_ball_self (by norm_num)
  exact ⟨F, hdF, hF0, (he₂ hzero).trans hG₂0, (he₁ hzero).trans hG₁0, heφ⟩

/-- Normalized triple primitives are unique on the disk (TT:982–990). -/
theorem normalized_triple_primitive_unique {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F unitDisc) (hG : DifferentiableOn ℂ G unitDisc)
    (h0 : F 0 = G 0) (h1 : deriv F 0 = deriv G 0)
    (h2 : deriv (deriv F) 0 = deriv (deriv G) 0)
    (h3 : EqOn (iteratedDeriv 3 F) (iteratedDeriv 3 G) unitDisc) : EqOn F G unitDisc := by
  have hzero : (0 : ℂ) ∈ unitDisc := mem_ball_self (by norm_num)
  have hconn := (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
  have h3' : EqOn (deriv (deriv (deriv F))) (deriv (deriv (deriv G))) unitDisc := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h3
  have he2 := isOpen_ball.eqOn_of_deriv_eq hconn
    ((hF.deriv isOpen_ball).deriv isOpen_ball) ((hG.deriv isOpen_ball).deriv isOpen_ball) h3' hzero h2
  have he1 := isOpen_ball.eqOn_of_deriv_eq hconn
    (hF.deriv isOpen_ball) (hG.deriv isOpen_ball) he2 hzero h1
  exact isOpen_ball.eqOn_of_deriv_eq hconn hF hG he1 hzero h0

/-- Integrating a quadratic boundary-growth bound once gives a linear
boundary-growth bound for the normalized primitive (TT:982–990). -/
theorem disk_primitive_growth_bound {F G : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ContinuousOn F unitDisc) (hG : ∀ z ∈ unitDisc, HasDerivAt G (F z) z)
    (hG0 : G 0 = 0) (hbound : ∀ z ∈ unitDisc, ‖F z‖ ≤ C / (1 - ‖z‖) ^ 2)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖G z‖ ≤ C * ‖z‖ / (1 - ‖z‖) := by
  let r : ℝ := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz
  have hnorm {t : ℝ} (ht : t ∈ Icc 0 1) : ‖(t : ℂ) * z‖ = t * r := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hmaps {t : ℝ} (ht : t ∈ Icc 0 1) : (t : ℂ) * z ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [hnorm ht]
    exact lt_of_le_of_lt (mul_le_of_le_one_left hr0 ht.2) hr1
  have hden {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < 1 - t * r := by
    have hle := mul_le_of_le_one_left hr0 ht.2
    linarith
  have hdpath : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => G ((t : ℂ) * z)) (z * F ((t : ℂ) * z)) t := by
    intro t ht
    have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const z)
    simpa only [Function.comp_def, smul_eq_mul] using (hG _ (hmaps ht)).scomp t hpath
  have hcont : ContinuousOn (fun t : ℝ => z * F ((t : ℂ) * z)) (Icc 0 1) :=
    continuousOn_const.mul (hF.comp (by fun_prop) (fun t ht => hmaps ht))
  have hint : IntervalIntegrable (fun t : ℝ => z * F ((t : ℂ) * z)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hdpath t (by simpa using ht)) hint
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, hG0, sub_zero] at he
  let b : ℝ → ℝ := fun t => C * r / (1 - t * r) ^ 2
  have hbcont : ContinuousOn b (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hden ht).ne'
  have hbint : IntervalIntegrable b volume 0 1 := hbcont.intervalIntegrable_of_Icc (by norm_num)
  have hmajor : ∀ t ∈ Icc (0 : ℝ) 1, ‖z * F ((t : ℂ) * z)‖ ≤ b t := by
    intro t ht
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hbound _ (hmaps ht)) hr0
    rw [hnorm ht] at hh
    dsimp [b]
    convert hh using 1 <;> dsimp [r] <;> ring
  have hbd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun t : ℝ => C / (1 - t * r)) (b t) t := by
    convert (hasDerivAt_const t C).div
      ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).mul_const r)) (hden ht).ne' using 1 <;>
      simp only [b, Pi.div_apply, Pi.sub_apply, Pi.mul_apply, id_eq, zero_mul, one_mul, zero_sub] <;>
      first | rfl | (funext x; simp only [Pi.div_apply, Pi.sub_apply]; ring) | ring
  have hbe := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hbd t (by simpa using ht)) hbint
  have hlast : (∫ t in (0 : ℝ)..1, b t) = C * r / (1 - r) := by
    rw [hbe]
    simp only [one_mul, zero_mul, sub_zero, div_one]
    field_simp [sub_ne_zero.mpr (ne_of_gt hr1)]
    ring
  rw [← he]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, b t := intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall (fun t ht => hmajor t (Ioc_subset_Icc_self ht))) hbint
    _ = _ := hlast

/-- A normalized primitive of a disk A-infinity function satisfies the
linear boundary-growth estimate needed for TS2 (TT:982–990). -/
theorem AInf_disc_primitive_growth_bound (φ : AInf unitDisc) {G : ℂ → ℂ}
    (hG : ∀ z ∈ unitDisc, HasDerivAt G (AInf.toFun φ z) z) (hG0 : G 0 = 0)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖G z‖ ≤ ‖φ‖ * ‖z‖ / (1 - ‖z‖) := by
  apply disk_primitive_growth_bound (norm_nonneg φ) φ.property.continuousOn hG hG0 ?_ hz
  intro w hw
  have hr : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hlow : 0 < (1 - ‖w‖) ^ 2 := sq_pos_of_pos (by linarith)
  have hle : (1 - ‖w‖) ^ 2 ≤ (1 - ‖w‖ ^ 2) ^ 2 := by
    have hsq : ‖w‖ ^ 2 ≤ ‖w‖ := by nlinarith [norm_nonneg w]
    nlinarith [sq_nonneg (‖w‖ ^ 2)]
  exact (AInf_disc_pointwise_bound φ hw).trans
    (div_le_div_of_nonneg_left (norm_nonneg φ) hlow hle)

/-- The normalized analytic inverse of the third derivative has the
required second-derivative growth bound (TT:982–990). -/
theorem exists_triple_primitive_growth (φ : AInf unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
      deriv (deriv F) 0 = 0 ∧ EqOn (iteratedDeriv 3 F) (AInf.toFun φ) unitDisc ∧
      ∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ ‖φ‖ * ‖z‖ / (1 - ‖z‖) := by
  obtain ⟨F, hF, hF0, hF1, hF2, hF3⟩ := exists_normalized_triple_primitive φ.property
  refine ⟨F, hF, hF0, hF1, hF2, hF3, ?_⟩
  intro z hz
  apply AInf_disc_primitive_growth_bound φ ?_ hF2 hz
  intro w hw
  have han := hF.analyticAt (isOpen_ball.mem_nhds hw)
  have hd := han.deriv.deriv.differentiableAt.hasDerivAt
  have he : deriv (deriv (deriv F)) w = AInf.toFun φ w := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, AInf.toFun] using hF3 hw
  rwa [he] at hd

/-- Radial integration recovers a holomorphic primitive on the disk
(TT:982–990). -/
theorem disk_primitive_radial_formula {F G : ℂ → ℂ} (hF : ContinuousOn F unitDisc)
    (hG : ∀ z ∈ unitDisc, HasDerivAt G (F z) z) {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ t in (0 : ℝ)..1, z * F ((t : ℂ) * z)) = G z - G 0 := by
  have hmaps {t : ℝ} (ht : t ∈ Icc 0 1) : (t : ℂ) * z ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg z) ht.2) (mem_ball_zero_iff.mp hz)
  have hdpath : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => G ((t : ℂ) * z)) (z * F ((t : ℂ) * z)) t := by
    intro t ht
    have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const z)
    simpa only [Function.comp_def, smul_eq_mul] using (hG _ (hmaps ht)).scomp t hpath
  have hcont : ContinuousOn (fun t : ℝ => z * F ((t : ℂ) * z)) (Icc 0 1) :=
    continuousOn_const.mul (hF.comp (by fun_prop) (fun t ht => hmaps ht))
  have hint : IntervalIntegrable (fun t : ℝ => z * F ((t : ℂ) * z)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hdpath t (by simpa using ht)) hint

/-- Radial majorants bound a primitive by their one-dimensional integral
(TT:982–990). -/
theorem disk_primitive_norm_le_integral {F G : ℂ → ℂ} (hF : ContinuousOn F unitDisc)
    (hG : ∀ z ∈ unitDisc, HasDerivAt G (F z) z) {z : ℂ} (hz : z ∈ unitDisc)
    {b : ℝ → ℝ} (hb : IntervalIntegrable b volume 0 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ b t) :
    ‖G z - G 0‖ ≤ ∫ t in (0 : ℝ)..1, ‖z‖ * b t := by
  rw [← disk_primitive_radial_formula hF hG hz]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ (hb.const_mul ‖z‖)
  filter_upwards [] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound t (Ioc_subset_Icc_self ht)) (norm_nonneg z)

/-- A simple-pole boundary-growth bound integrates to logarithmic
growth for the normalized primitive (TT:982–990). -/
theorem disk_primitive_log_bound {F G : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ContinuousOn F unitDisc) (hG : ∀ z ∈ unitDisc, HasDerivAt G (F z) z)
    (hG0 : G 0 = 0) (hbound : ∀ z ∈ unitDisc, ‖F z‖ ≤ C / (1 - ‖z‖))
    {z : ℂ} (hz : z ∈ unitDisc) : ‖G z‖ ≤ -C * Real.log (1 - ‖z‖) := by
  let r : ℝ := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz
  have hden {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < 1 - t * r := by
    have hh := mul_le_of_le_one_left hr0 ht.2
    linarith
  have hnorm {t : ℝ} (ht : t ∈ Icc 0 1) : ‖(t : ℂ) * z‖ = t * r := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  let b : ℝ → ℝ := fun t => C / (1 - t * r)
  have hbcont : ContinuousOn b (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (hden ht).ne'
  have hbint : IntervalIntegrable b volume 0 1 :=
    hbcont.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hmajor : ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ b t := by
    intro t ht
    have htz : (t : ℂ) * z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnorm ht]; linarith [hden ht])
    simpa only [b, hnorm ht] using hbound _ htz
  have hi := disk_primitive_norm_le_integral hF hG hz hbint hmajor
  rw [hG0, sub_zero] at hi
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun t : ℝ => -C * Real.log (1 - t * r)) (r * b t) t := by
    convert (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).mul_const r)).log (hden ht).ne').const_mul (-C) using 1 <;>
      simp only [b, Pi.sub_apply, Pi.mul_apply, id_eq, one_mul, zero_sub] <;>
      first | rfl | (funext x; simp only [Pi.sub_apply, Pi.mul_apply]; ring) | ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht)) (hbint.const_mul r)
  have he' : (∫ t in (0 : ℝ)..1, r * b t) = -C * Real.log (1 - r) := by simpa using he
  change ‖G z‖ ≤ ∫ t in (0 : ℝ)..1, r * b t at hi
  rw [he'] at hi
  exact hi

/-- The first derivative of the normalized triple primitive has only
logarithmic growth at the circle (TT:982–990). -/
theorem exists_triple_primitive_log_growth (φ : AInf unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
      deriv (deriv F) 0 = 0 ∧ EqOn (iteratedDeriv 3 F) (AInf.toFun φ) unitDisc ∧
      (∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ ‖φ‖ * ‖z‖ / (1 - ‖z‖)) ∧
      ∀ z ∈ unitDisc, ‖deriv F z‖ ≤ -‖φ‖ * Real.log (1 - ‖z‖) := by
  obtain ⟨F, hF, hF0, hF1, hF2, hF3, hB⟩ := exists_triple_primitive_growth φ
  refine ⟨F, hF, hF0, hF1, hF2, hF3, hB, ?_⟩
  intro z hz
  apply disk_primitive_log_bound (norm_nonneg φ)
    ((hF.deriv isOpen_ball).deriv isOpen_ball).continuousOn ?_ hF1 ?_ hz
  · intro w hw
    exact (hF.analyticAt (isOpen_ball.mem_nhds hw)).deriv.differentiableAt.hasDerivAt
  · intro w hw
    have hr := mem_ball_zero_iff.mp hw
    apply (hB w hw).trans
    apply div_le_div_of_nonneg_right ?_ (by linarith)
    exact mul_le_of_le_one_right (norm_nonneg φ) hr.le

/-- Logarithmic boundary growth integrates to a bounded normalized
primitive (TT:982–990). -/
theorem disk_primitive_bounded_of_log_bound {F G : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ContinuousOn F unitDisc) (hG : ∀ z ∈ unitDisc, HasDerivAt G (F z) z)
    (hG0 : G 0 = 0) (hbound : ∀ z ∈ unitDisc, ‖F z‖ ≤ -C * Real.log (1 - ‖z‖))
    {z : ℂ} (hz : z ∈ unitDisc) : ‖G z‖ ≤ C := by
  let r : ℝ := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg z
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz
  have hden {t : ℝ} (ht : t ∈ Icc 0 1) : 0 < 1 - t * r := by
    have hh := mul_le_of_le_one_left hr0 ht.2
    linarith
  have hnorm {t : ℝ} (ht : t ∈ Icc 0 1) : ‖(t : ℂ) * z‖ = t * r := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  let b : ℝ → ℝ := fun t => -C * Real.log (1 - t * r)
  have hbcont : ContinuousOn b (Icc 0 1) := by
    apply continuousOn_const.mul
    exact (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t * r) (Icc 0 1)).log
      (fun t ht => (hden ht).ne')
  have hbint : IntervalIntegrable b volume 0 1 := hbcont.intervalIntegrable_of_Icc (by norm_num)
  have hmajor : ∀ t ∈ Icc (0 : ℝ) 1, ‖F ((t : ℂ) * z)‖ ≤ b t := by
    intro t ht
    have htz : (t : ℂ) * z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnorm ht]; linarith [hden ht])
    simpa only [b, hnorm ht] using hbound _ htz
  have hi := disk_primitive_norm_le_integral hF hG hz hbint hmajor
  rw [hG0, sub_zero] at hi
  let P : ℝ → ℝ := fun t => C * ((1 - t * r) * Real.log (1 - t * r) - (1 - t * r))
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt P (r * b t) t := by
    have hlin : HasDerivAt (fun t : ℝ => 1 - t * r) (-r) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const r) using 1 <;>
        first | rfl | simp only [Pi.sub_apply, id_eq, one_mul, zero_sub]
    convert ((hlin.mul (hlin.log (hden ht).ne')).sub hlin).const_mul C using 1 <;>
      first | rfl | (
        change r * (-C * Real.log (1 - t * r)) =
          C * (-r * Real.log (1 - t * r) + (1 - t * r) * (-r / (1 - t * r)) - -r)
        rw [mul_div_cancel₀ (-r) (hden ht).ne']
        ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa using ht)) (hbint.const_mul r)
  have he' : (∫ t in (0 : ℝ)..1, r * b t) = C * ((1 - r) * Real.log (1 - r) + r) := by
    rw [he]
    simp only [P, one_mul, zero_mul, sub_zero, Real.log_one, mul_zero, zero_sub, mul_neg, mul_one]
    ring
  change ‖G z‖ ≤ ∫ t in (0 : ℝ)..1, r * b t at hi
  rw [he'] at hi
  have hlog : Real.log (1 - r) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hp : (1 - r) * Real.log (1 - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  exact hi.trans (mul_le_of_le_one_right hC (by linarith))

/-- The normalized analytic inverse in TS2 is bounded and has both
first- and second-derivative boundary estimates (TT:982–990). -/
theorem exists_triple_primitive_bounded (φ : AInf unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
      deriv (deriv F) 0 = 0 ∧ EqOn (iteratedDeriv 3 F) (AInf.toFun φ) unitDisc ∧
      (∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ ‖φ‖ * ‖z‖ / (1 - ‖z‖)) ∧
      (∀ z ∈ unitDisc, ‖deriv F z‖ ≤ -‖φ‖ * Real.log (1 - ‖z‖)) ∧
      ∀ z ∈ unitDisc, ‖F z‖ ≤ ‖φ‖ := by
  obtain ⟨F, hF, hF0, hF1, hF2, hF3, hB2, hB1⟩ := exists_triple_primitive_log_growth φ
  refine ⟨F, hF, hF0, hF1, hF2, hF3, hB2, hB1, ?_⟩
  intro z hz
  exact disk_primitive_bounded_of_log_bound (norm_nonneg φ) (hF.deriv isOpen_ball).continuousOn
    (fun w hw => (hF.analyticAt (isOpen_ball.mem_nhds hw)).differentiableAt.hasDerivAt) hF0 hB1 hz

/-- A simple-pole bound on the second derivative gives a uniform
first-order radial Taylor remainder, including as the outer radius tends
to one (TT:982–990). -/
theorem disk_radial_taylor_remainder {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (hbound : ∀ w ∈ unitDisc, ‖deriv (deriv F) w‖ ≤ C / (1 - ‖w‖))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) :
    ‖F ((s : ℂ) * ζ) - F ((r : ℂ) * ζ) - ((s - r : ℝ) : ℂ) * ζ * deriv F ((r : ℂ) * ζ)‖ ≤ C * (s - r) := by
  have hnorm {t : ℝ} (ht : t ∈ Icc r s) : ‖(t : ℂ) * ζ‖ = t := by
    rw [norm_mul, hζ, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (hr.trans ht.1)]
  have hmaps {t : ℝ} (ht : t ∈ Icc r s) : (t : ℂ) * ζ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [hnorm ht]; exact ht.2.trans_lt hs)
  let K : ℝ → ℂ := fun t => F ((t : ℂ) * ζ) + ((s - t : ℝ) : ℂ) * ζ * deriv F ((t : ℂ) * ζ)
  let dK : ℝ → ℂ := fun t => ((s - t : ℝ) : ℂ) * ζ ^ 2 * deriv (deriv F) ((t : ℂ) * ζ)
  have hd : ∀ t ∈ Icc r s, HasDerivAt K (dK t) t := by
    intro t ht
    have han := hF.analyticAt (isOpen_ball.mem_nhds (hmaps ht))
    have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) * ζ) ζ t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const ζ)
    have hFpath := han.differentiableAt.hasDerivAt.scomp t hpath
    have hDpath := han.deriv.differentiableAt.hasDerivAt.scomp t hpath
    have hcoeff : HasDerivAt (fun t : ℝ => ((s - t : ℝ) : ℂ) * ζ) (-ζ) t := by
      simpa only [Pi.sub_apply, id_eq, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
        zero_sub] using (((hasDerivAt_const t s).sub (hasDerivAt_id t)).ofReal_comp.mul_const ζ)
    convert hFpath.add (hcoeff.mul hDpath) using 1 <;>
      simp only [K, dK, Function.comp_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul] <;>
      first | rfl | (funext x; ring) | ring
  have hb : ∀ t ∈ Ico r s, ‖dK t‖ ≤ C := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hpos : 0 < 1 - t := by linarith [ht.2]
    have hrem : 0 ≤ s - t := by linarith [ht.2]
    have hh := mul_le_mul_of_nonneg_left (hbound _ (hmaps ht')) hrem
    rw [hnorm ht'] at hh
    calc
      ‖dK t‖ = (s - t) * ‖deriv (deriv F) ((t : ℂ) * ζ)‖ := by
        simp only [dK, norm_mul, norm_pow, hζ, one_pow, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_nonneg hrem]
      _ ≤ (s - t) * (C / (1 - t)) := hh
      _ ≤ C := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hpos).mpr
        nlinarith
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb s (right_mem_Icc.mpr hrs)
  convert hh using 1
  congr 1
  simp only [K, sub_self, Complex.ofReal_zero, zero_mul, add_zero]
  ring

/-- Logarithmic first-derivative growth and simple-pole second-derivative
growth give a continuous circle boundary value, via uniform radial
convergence (TT:982–990). -/
theorem exists_continuous_boundary_of_growth {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (h1 : ∀ z ∈ unitDisc, ‖deriv F z‖ ≤ -C * Real.log (1 - ‖z‖))
    (h2 : ∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ C / (1 - ‖z‖)) :
    ∃ B : C(Circle, ℂ), TendstoUniformly
      (fun n : ℕ => fun ζ : Circle => F (((1 - (1 / 2 : ℝ) ^ n : ℝ) : ℂ) * ζ)) B atTop := by
  let δ : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  let R : ℕ → ℝ := fun n => 1 - δ n
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hR0 (n : ℕ) : 0 ≤ R n := sub_nonneg.mpr (hδle n)
  have hR1 (n : ℕ) : R n < 1 := by dsimp [R]; linarith [hδpos n]
  have hδanti : Antitone δ := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [δ]
    rw [pow_succ]
    nlinarith [hδpos n]
  have hRmono {m n : ℕ} (hmn : m ≤ n) : R m ≤ R n := by
    dsimp [R]
    linarith [hδanti hmn]
  have hnorm (n : ℕ) (ζ : Circle) : ‖(R n : ℂ) * ζ‖ = R n := by
    rw [norm_mul, Circle.norm_coe, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (hR0 n)]
  have hmaps (n : ℕ) (ζ : Circle) : (R n : ℂ) * ζ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [hnorm]; exact hR1 n)
  let f : ℕ → C(Circle, ℂ) := fun n =>
    ⟨fun ζ => F ((R n : ℂ) * ζ), hF.continuousOn.comp_continuous (by fun_prop) (hmaps n)⟩
  let b : ℕ → ℝ := fun n => C * δ n * (1 - Real.log (δ n))
  have hlog (n : ℕ) : Real.log (δ n) ≤ 0 := Real.log_nonpos (hδpos n).le (hδle n)
  have hb0 (n : ℕ) : 0 ≤ b n := by
    have hl := hlog n
    exact mul_nonneg (mul_nonneg hC (hδpos n).le) (by linarith)
  have hb : Tendsto b atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hn := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hh := (hp.sub (hn.mul_const (Real.log (1 / 2 : ℝ)))).const_mul C
    convert hh using 1
    · funext n
      simp only [b, δ, Real.log_pow]
      ring
    · simp
  have hdist {m n : ℕ} (hmn : m ≤ n) : ‖f n - f m‖ ≤ b m := by
    apply (ContinuousMap.norm_le _ (hb0 m)).mpr
    intro ζ
    have hrem := disk_radial_taylor_remainder hC hF h2 (Circle.norm_coe ζ)
      (hR0 m) (hRmono hmn) (hR1 n)
    have hd := h1 _ (hmaps m ζ)
    rw [hnorm, show 1 - R m = δ m by dsimp [R]; ring] at hd
    have hΔ : 0 ≤ R n - R m := sub_nonneg.mpr (hRmono hmn)
    have hΔle : R n - R m ≤ δ m := by dsimp [R]; linarith [hδpos n]
    let A : ℂ := F ((R n : ℂ) * ζ) - F ((R m : ℂ) * ζ)
    let L : ℂ := ((R n - R m : ℝ) : ℂ) * ζ * deriv F ((R m : ℂ) * ζ)
    have hLn : ‖L‖ = (R n - R m) * ‖deriv F ((R m : ℂ) * ζ)‖ := by
      simp only [L, norm_mul, Circle.norm_coe, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    have hL : ‖L‖ ≤ δ m * (-C * Real.log (δ m)) := by
      rw [hLn]
      exact mul_le_mul hΔle hd (norm_nonneg _) (hδpos m).le
    have htri : ‖A‖ ≤ ‖A - L‖ + ‖L‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A - L) L
    have hsmall := mul_le_mul_of_nonneg_left hΔle hC
    change ‖A‖ ≤ b m
    dsimp only [b]
    change ‖A - L‖ ≤ C * (R n - R m) at hrem
    nlinarith
  have hcs : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp hb).2 ε hε)
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases le_total m n with hmn | hnm
    · rw [dist_comm, dist_eq_norm]
      exact (hdist hmn).trans_lt (hN m hm)
    · rw [dist_eq_norm]
      exact (hdist hnm).trans_lt (hN n hn)
  obtain ⟨B, hB⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨B, ?_⟩
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp hB

/-- The uniform radial boundary value inherits the first-order Taylor
remainder estimate all the way to the circle (TT:982–990). -/
theorem disk_boundary_taylor_remainder {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (h2 : ∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ C / (1 - ‖z‖))
    (B : C(Circle, ℂ))
    (hB : TendstoUniformly (fun n : ℕ => fun ζ : Circle =>
      F (((1 - (1 / 2 : ℝ) ^ n : ℝ) : ℂ) * ζ)) B atTop)
    (ζ : Circle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖B ζ - F ((r : ℂ) * ζ) - ((1 - r : ℝ) : ℂ) * ζ * deriv F ((r : ℂ) * ζ)‖ ≤ C * (1 - r) := by
  let R : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ n
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hR : Tendsto R atTop (𝓝 1) := by simpa only [sub_zero] using tendsto_const_nhds.sub hp
  have heval : Tendsto (fun n => F ((R n : ℂ) * ζ)) atTop (𝓝 (B ζ)) := hB.tendsto_at ζ
  have hscalar := (Complex.continuous_ofReal.tendsto (1 - r)).comp (hR.sub_const r)
  have hleft := ((heval.sub_const (F ((r : ℂ) * ζ))).sub
    ((hscalar.mul_const (ζ : ℂ)).mul_const (deriv F ((r : ℂ) * ζ)))).norm
  have hright := (hR.sub_const r).const_mul C
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [(tendsto_order.mp hR).1 r hr1] with n hn
  exact disk_radial_taylor_remainder hC hF h2 (Circle.norm_coe ζ) hr0 hn.le
    (by
      dsimp [R]
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
      linarith)

/-- Uniform radial limits preserve the disk sup bound (TT:982–990). -/
theorem disk_boundary_norm_le {F : ℂ → ℂ} {C : ℝ}
    (hF : ∀ z ∈ unitDisc, ‖F z‖ ≤ C) (B : C(Circle, ℂ))
    (hB : TendstoUniformly (fun n : ℕ => fun ζ : Circle =>
      F (((1 - (1 / 2 : ℝ) ^ n : ℝ) : ℂ) * ζ)) B atTop) (ζ : Circle) : ‖B ζ‖ ≤ C := by
  apply le_of_tendsto (hB.tendsto_at ζ).norm
  apply Filter.Eventually.of_forall
  intro n
  apply hF
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  apply mem_ball_zero_iff.mpr
  rw [norm_mul, Circle.norm_coe, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- The normalized analytic inverse of TS2 has a continuous bounded
circle trace with a uniform radial Taylor estimate (TT:982–990). -/
theorem exists_triple_primitive_boundary (φ : AInf unitDisc) :
    ∃ (F : ℂ → ℂ) (B : C(Circle, ℂ)), DifferentiableOn ℂ F unitDisc ∧ F 0 = 0 ∧
      deriv F 0 = 0 ∧ deriv (deriv F) 0 = 0 ∧
      EqOn (iteratedDeriv 3 F) (AInf.toFun φ) unitDisc ∧
      (∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ ‖φ‖ / (1 - ‖z‖)) ∧
      (∀ z ∈ unitDisc, ‖deriv F z‖ ≤ -‖φ‖ * Real.log (1 - ‖z‖)) ∧
      (∀ ζ : Circle, ‖B ζ‖ ≤ ‖φ‖) ∧
      (∀ ζ : Circle, ∀ r : ℝ, 0 ≤ r → r < 1 →
        ‖B ζ - F ((r : ℂ) * ζ) - ((1 - r : ℝ) : ℂ) * ζ * deriv F ((r : ℂ) * ζ)‖ ≤ ‖φ‖ * (1 - r)) ∧
      TendstoUniformly (fun n : ℕ => fun ζ : Circle =>
        F (((1 - (1 / 2 : ℝ) ^ n : ℝ) : ℂ) * ζ)) B atTop := by
  obtain ⟨F, hF, hF0, hF1, hF2, hF3, hB2, hB1, hB0⟩ := exists_triple_primitive_bounded φ
  have h2 : ∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ ‖φ‖ / (1 - ‖z‖) := by
    intro z hz
    have hr := mem_ball_zero_iff.mp hz
    apply (hB2 z hz).trans
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg φ) hr.le) (by linarith)
  obtain ⟨B, hB⟩ := exists_continuous_boundary_of_growth (norm_nonneg φ) hF hB1 h2
  refine ⟨F, B, hF, hF0, hF1, hF2, hF3, h2, hB1, ?_, ?_, hB⟩
  · exact fun ζ => disk_boundary_norm_le hB0 B hB ζ
  · exact fun ζ r hr0 hr1 => disk_boundary_taylor_remainder (norm_nonneg φ) hF h2 B hB ζ hr0 hr1

/-- A bounded derivative controls differences of a complex-valued real
curve (TT:982–990). -/
theorem curve_norm_sub_le {f df : ℝ → ℂ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x) (hb : ∀ x, ‖df x‖ ≤ M) (x y : ℝ) :
    ‖f y - f x‖ ≤ M * |y - x| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (univ : Set ℝ)) (fun t _ => (hf t).differentiableAt)
    (fun t _ => by rw [(hf t).deriv]; exact hb t) convex_univ (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using hh

/-- A globally bounded derivative controls the second symmetric
difference of a curve (TT:982–990). -/
theorem curve_second_difference_first_bound {f df : ℝ → ℂ} {M : ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x) (hb : ∀ x, ‖df x‖ ≤ M) (x t : ℝ) :
    ‖f (x + t) + f (x - t) - 2 * f x‖ ≤ 2 * M * |t| := by
  have hplus := curve_norm_sub_le hf hb x (x + t)
  have hminus := curve_norm_sub_le hf hb x (x - t)
  have htri := norm_add_le (f (x + t) - f x) (f (x - t) - f x)
  have he : f (x + t) + f (x - t) - 2 * f x = (f (x + t) - f x) + (f (x - t) - f x) := by ring
  rw [he]
  simp only [add_sub_cancel_left, sub_sub_cancel_left, abs_neg] at hplus hminus
  linarith

/-- A bounded second derivative controls the second symmetric difference
quadratically (TT:982–990). -/
theorem curve_second_difference_second_bound {f df ddf : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, HasDerivAt f (df x) x) (hdf : ∀ x, HasDerivAt df (ddf x) x)
    (hb : ∀ x, ‖ddf x‖ ≤ M) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖f (x + t) + f (x - t) - 2 * f x‖ ≤ 2 * M * t ^ 2 := by
  let g : ℝ → ℂ := fun s => f (x + s) + f (x - s) - 2 * f x
  let dg : ℝ → ℂ := fun s => df (x + s) - df (x - s)
  have hg (s : ℝ) : HasDerivAt g (dg s) s := by
    have hp := (hf (x + s)).scomp s ((hasDerivAt_const s x).add (hasDerivAt_id s))
    have hm := (hf (x - s)).scomp s ((hasDerivAt_const s x).sub (hasDerivAt_id s))
    convert (hp.add hm).sub_const (2 * f x) using 1 <;>
      simp only [g, dg, Function.comp_apply, Pi.add_apply, Pi.sub_apply, zero_add,
        zero_sub, one_smul, neg_smul, sub_eq_add_neg]
  have hdb : ∀ s ∈ Ico (0 : ℝ) t, ‖dg s‖ ≤ 2 * M * t := by
    intro s hs
    have hh := curve_norm_sub_le hdf hb (x - s) (x + s)
    have he : x + s - (x - s) = 2 * s := by ring
    rw [he, abs_of_nonneg (by linarith [hs.1])] at hh
    dsimp [dg]
    nlinarith [hs.2]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hg s).hasDerivWithinAt) hdb t (right_mem_Icc.mpr ht)
  have hg0 : g 0 = 0 := by dsimp [g]; ring
  rw [hg0, sub_zero, sub_zero] at hh
  simpa only [g, pow_two, mul_assoc] using hh

/-- Bounds on the first two complex derivatives control angular second
differences on an interior circle (TT:982–990). -/
theorem disk_angular_difference_bounds {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc)
    {r A B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ∀ z : ℂ, ‖z‖ = r → ‖deriv F z‖ ≤ A)
    (h2 : ∀ z : ℂ, ‖z‖ = r → ‖deriv (deriv F) z‖ ≤ B) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖F ((r : ℂ) * exp ((x + t) * I)) + F ((r : ℂ) * exp ((x - t) * I)) -
        2 * F ((r : ℂ) * exp (x * I))‖ ≤ 2 * (A + B) * t ^ 2 ∧
    ‖exp ((x + t) * I) * deriv F ((r : ℂ) * exp ((x + t) * I)) +
        exp ((x - t) * I) * deriv F ((r : ℂ) * exp ((x - t) * I)) -
        2 * exp (x * I) * deriv F ((r : ℂ) * exp (x * I))‖ ≤ 2 * (A + B) * t := by
  let e : ℝ → ℂ := fun θ => exp (θ * I)
  let Z : ℝ → ℂ := fun θ => (r : ℂ) * e θ
  have heNorm (θ : ℝ) : ‖e θ‖ = 1 := by simp [e, norm_exp]
  have hZNorm (θ : ℝ) : ‖Z θ‖ = r := by
    simp only [Z, norm_mul, heNorm, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hZmem (θ : ℝ) : Z θ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hZNorm]; exact hr1)
  have heD (θ : ℝ) : HasDerivAt e (I * e θ) θ := by
    have hpath : HasDerivAt (fun θ : ℝ => (θ : ℂ) * I) I θ := by
      simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const I)
    simpa only [e, Function.comp_def, smul_eq_mul] using (Complex.hasDerivAt_exp _).scomp θ hpath
  have hZD (θ : ℝ) : HasDerivAt Z (I * Z θ) θ := by
    convert (heD θ).const_mul (r : ℂ) using 1 <;> dsimp only [Z] <;> ring
  have hFD (θ : ℝ) : HasDerivAt (fun θ => F (Z θ)) (I * Z θ * deriv F (Z θ)) θ := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (hF.analyticAt (isOpen_ball.mem_nhds (hZmem θ))).differentiableAt.hasDerivAt.scomp θ (hZD θ)
  have hDD (θ : ℝ) : HasDerivAt (fun θ => deriv F (Z θ))
      (I * Z θ * deriv (deriv F) (Z θ)) θ := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (hF.analyticAt (isOpen_ball.mem_nhds (hZmem θ))).deriv.differentiableAt.hasDerivAt.scomp θ (hZD θ)
  let dd : ℝ → ℂ := fun θ => (I * (I * Z θ)) * deriv F (Z θ) +
    (I * Z θ) * (I * Z θ * deriv (deriv F) (Z θ))
  have hdD (θ : ℝ) : HasDerivAt (fun θ => I * Z θ * deriv F (Z θ)) (dd θ) θ := by
    exact ((hZD θ).const_mul I).mul (hDD θ)
  have hddbound (θ : ℝ) : ‖dd θ‖ ≤ A + B := by
    have hb := norm_add_le ((I * (I * Z θ)) * deriv F (Z θ))
      ((I * Z θ) * (I * Z θ * deriv (deriv F) (Z θ)))
    simp only [norm_mul, Complex.norm_I, one_mul, hZNorm] at hb
    have hfirst := mul_le_mul_of_nonneg_left (h1 _ (hZNorm θ)) hr0
    have hsecond := mul_le_mul_of_nonneg_left (h2 _ (hZNorm θ)) (mul_nonneg hr0 hr0)
    have hrA := mul_le_of_le_one_left hA hr1.le
    have hrB : r * r * B ≤ B := by nlinarith [mul_nonneg hr0 hB]
    change ‖_ + _‖ ≤ A + B
    nlinarith
  have hP := curve_second_difference_second_bound (add_nonneg hA hB) hFD hdD hddbound x ht
  let dR : ℝ → ℂ := fun θ => (I * e θ) * deriv F (Z θ) +
    e θ * (I * Z θ * deriv (deriv F) (Z θ))
  have hRD (θ : ℝ) : HasDerivAt (fun θ => e θ * deriv F (Z θ)) (dR θ) θ :=
    (heD θ).mul (hDD θ)
  have hdRbound (θ : ℝ) : ‖dR θ‖ ≤ A + B := by
    have hb := norm_add_le ((I * e θ) * deriv F (Z θ))
      (e θ * (I * Z θ * deriv (deriv F) (Z θ)))
    simp only [norm_mul, Complex.norm_I, one_mul, heNorm, hZNorm] at hb
    have hfirst := h1 _ (hZNorm θ)
    have hsecond := mul_le_mul_of_nonneg_left (h2 _ (hZNorm θ)) hr0
    have hrB := mul_le_of_le_one_left hB hr1.le
    change ‖_ + _‖ ≤ A + B
    linarith
  have hR := curve_second_difference_first_bound hRD hdRbound x t
  constructor
  · simpa only [e, Z, Complex.ofReal_add, Complex.ofReal_sub] using hP
  · simpa only [e, Z, abs_of_nonneg ht, mul_assoc, Complex.ofReal_add, Complex.ofReal_sub] using hR

/-- A sup bound controls a second difference, with no differentiability
assumption (TT:982–990). -/
theorem second_difference_norm_le_four {f : ℝ → ℂ} {K : ℝ} (hb : ∀ x, ‖f x‖ ≤ K) (x t : ℝ) :
    ‖f (x + t) + f (x - t) - 2 * f x‖ ≤ 4 * K := by
  have h1 := norm_sub_le (f (x + t) + f (x - t)) (2 * f x)
  have h2 := norm_add_le (f (x + t)) (f (x - t))
  norm_num only [norm_mul, norm_ofNat] at h1
  linarith [hb (x + t), hb (x - t), hb x]

/-- The continuous trace of an analytic function with the normalized
derivative-growth bounds is Zygmund, with an explicit constant
(TT:982–990). -/
theorem disk_boundary_second_difference_bound {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F unitDisc)
    (h1 : ∀ z ∈ unitDisc, ‖deriv F z‖ ≤ -C * Real.log (1 - ‖z‖))
    (h2 : ∀ z ∈ unitDisc, ‖deriv (deriv F) z‖ ≤ C / (1 - ‖z‖))
    (B : C(Circle, ℂ)) (hB0 : ∀ ζ : Circle, ‖B ζ‖ ≤ C)
    (hBT : ∀ ζ : Circle, ∀ r : ℝ, 0 ≤ r → r < 1 →
      ‖B ζ - F ((r : ℂ) * ζ) - ((1 - r : ℝ) : ℂ) * ζ * deriv F ((r : ℂ) * ζ)‖ ≤ C * (1 - r)) :
    ∀ x t : ℝ, ‖B (Circle.exp (x + t)) + B (Circle.exp (x - t)) - 2 * B (Circle.exp x)‖ ≤ 12 * C * |t| := by
  let b : ℝ → ℂ := fun x => B (Circle.exp x)
  have hb (x : ℝ) : ‖b x‖ ≤ C := hB0 _
  have hpos : ∀ x t : ℝ, 0 < t → ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 12 * C * t := by
    intro x t ht
    by_cases hbig : 1 / 2 ≤ t
    · have hh := second_difference_norm_le_four hb x t
      nlinarith
    · have ht1 : t < 1 := by linarith
      let r : ℝ := 1 - t
      have hr0 : 0 ≤ r := by dsimp [r]; linarith
      have hr1 : r < 1 := by dsimp [r]; linarith
      have hrt : 1 - r = t := by dsimp [r]; ring
      let A : ℝ := -C * Real.log t
      let D : ℝ := C / t
      have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1.le
      have hA : 0 ≤ A := mul_nonneg_of_nonpos_of_nonpos (by linarith) hlog
      have hD : 0 ≤ D := div_nonneg hC ht.le
      have hcircle1 : ∀ z : ℂ, ‖z‖ = r → ‖deriv F z‖ ≤ A := by
        intro z hz
        simpa only [hz, hrt, A] using h1 z (mem_ball_zero_iff.mpr (hz ▸ hr1))
      have hcircle2 : ∀ z : ℂ, ‖z‖ = r → ‖deriv (deriv F) z‖ ≤ D := by
        intro z hz
        simpa only [hz, hrt, D] using h2 z (mem_ball_zero_iff.mpr (hz ▸ hr1))
      let Q : ℝ → ℂ := fun y => F ((r : ℂ) * exp (y * I))
      let R : ℝ → ℂ := fun y => exp (y * I) * deriv F ((r : ℂ) * exp (y * I))
      let E : ℝ → ℂ := fun y => b y - Q y - (t : ℂ) * R y
      have hE (y : ℝ) : ‖E y‖ ≤ C * t := by
        have hh := hBT (Circle.exp y) r hr0 hr1
        rw [hrt] at hh
        simpa only [E, b, Q, R, Circle.coe_exp, mul_assoc] using hh
      have hEs := second_difference_norm_le_four hE x t
      obtain ⟨hQ, hR⟩ := disk_angular_difference_bounds hF hr0 hr1 hA hD hcircle1 hcircle2 x ht.le
      have hQ' : ‖Q (x + t) + Q (x - t) - 2 * Q x‖ ≤ 2 * (A + D) * t ^ 2 := by
        simpa only [Q, Complex.ofReal_add, Complex.ofReal_sub] using hQ
      have hR' : ‖R (x + t) + R (x - t) - 2 * R x‖ ≤ 2 * (A + D) * t := by
        simpa only [R, Complex.ofReal_add, Complex.ofReal_sub, mul_assoc] using hR
      let ΔQ := Q (x + t) + Q (x - t) - 2 * Q x
      let ΔR := R (x + t) + R (x - t) - 2 * R x
      let ΔE := E (x + t) + E (x - t) - 2 * E x
      have he : b (x + t) + b (x - t) - 2 * b x = ΔQ + (t : ℂ) * ΔR + ΔE := by
        dsimp [ΔQ, ΔR, ΔE, E]
        ring
      have htri1 := norm_add_le (ΔQ + (t : ℂ) * ΔR) ΔE
      have htri2 := norm_add_le ΔQ ((t : ℂ) * ΔR)
      have hn : ‖(t : ℂ) * ΔR‖ = t * ‖ΔR‖ := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht]
      rw [hn] at htri2
      have hmul := mul_le_mul_of_nonneg_left hR' ht.le
      have hsum : ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 4 * (A + D) * t ^ 2 + 4 * C * t := by
        rw [he]
        change ‖ΔQ‖ ≤ _ at hQ'
        change ‖ΔE‖ ≤ _ at hEs
        change t * ‖ΔR‖ ≤ _ at hmul
        nlinarith
      have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
      rw [Real.log_inv] at hl
      have hm := mul_le_mul_of_nonneg_left hl ht.le
      have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
      have hlogt : -t * Real.log t ≤ 1 := by nlinarith
      have hmlog := mul_le_mul_of_nonneg_left hlogt (show 0 ≤ 4 * C * t by positivity)
      have halg : 4 * (A + D) * t ^ 2 + 4 * C * t = 8 * C * t + (4 * C * t) * (-t * Real.log t) := by
        dsimp [A, D]
        field_simp
        ring
      rw [halg] at hsum
      linarith
  intro x t
  change ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ 12 * C * |t|
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hh := hpos x (-t) (neg_pos.mpr ht)
    rw [abs_of_neg ht]
    simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_comm] using hh
  · subst t
    simp [two_mul]
  · simpa only [abs_of_pos ht] using hpos x t ht

/-- Multiplication by a bounded Lipschitz scalar preserves the
second-difference bound of a bounded Zygmund function (TT:982–990). -/
theorem second_difference_product_bound {p b : ℝ → ℂ} {C K : ℝ}
    (hp : ∀ x, ‖p x‖ ≤ 1) (hpd : ∀ x y, ‖p y - p x‖ ≤ |y - x|)
    (hb : ∀ x, ‖b x‖ ≤ C)
    (hbd : ∀ x t, ‖b (x + t) + b (x - t) - 2 * b x‖ ≤ K * |t|) (x t : ℝ) :
    ‖p (x + t) * b (x + t) + p (x - t) * b (x - t) - 2 * (p x * b x)‖ ≤ (K + 2 * C) * |t| := by
  let D := b (x + t) + b (x - t) - 2 * b x
  let U := (p (x + t) - p x) * b (x + t)
  let V := (p (x - t) - p x) * b (x - t)
  have he : p (x + t) * b (x + t) + p (x - t) * b (x - t) - 2 * (p x * b x) = p x * D + U + V := by
    dsimp [D, U, V]
    ring
  have hD : ‖p x * D‖ ≤ K * |t| := by
    rw [norm_mul]
    have hh := mul_le_mul (hp x) (hbd x t) (norm_nonneg D) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hU : ‖U‖ ≤ |t| * C := by
    rw [show ‖U‖ = ‖p (x + t) - p x‖ * ‖b (x + t)‖ by exact norm_mul _ _]
    have hh := hpd x (x + t)
    simp only [add_sub_cancel_left] at hh
    exact mul_le_mul hh (hb _) (norm_nonneg _) (abs_nonneg _)
  have hV : ‖V‖ ≤ |t| * C := by
    rw [show ‖V‖ = ‖p (x - t) - p x‖ * ‖b (x - t)‖ by exact norm_mul _ _]
    have hh := hpd x (x - t)
    have he' : x - t - x = -t := by ring
    rw [he', abs_neg] at hh
    exact mul_le_mul hh (hb _) (norm_nonneg _) (abs_nonneg _)
  have htri1 := norm_add_le (p x * D + U) V
  have htri2 := norm_add_le (p x * D) U
  rw [he]
  linarith

/-- The rotating factor 1/(i exp(i theta)) is bounded by one and
one-Lipschitz (TT:917, TT:982–990). -/
theorem boundary_rotation_factor :
    (∀ x : ℝ, ‖-I * conj ((Circle.exp x : Circle) : ℂ)‖ = 1) ∧
    ∀ x y : ℝ, ‖-I * conj ((Circle.exp y : Circle) : ℂ) -
      (-I * conj ((Circle.exp x : Circle) : ℂ))‖ ≤ |y - x| := by
  let p : ℝ → ℂ := fun x => -I * conj ((Circle.exp x : Circle) : ℂ)
  have he (x : ℝ) : p x = -I * exp (-((x : ℂ) * I)) := by
    simp only [p, Circle.coe_exp, ← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  have hd (x : ℝ) : HasDerivAt p (-exp (-((x : ℂ) * I))) x := by
    have hpath : HasDerivAt (fun x : ℝ => -((x : ℂ) * I)) (-I) x := by
      convert ((hasDerivAt_id x).ofReal_comp.mul_const I).neg using 1 <;>
        first | rfl | simp only [Pi.neg_apply, Complex.ofReal_one, one_mul]
    have hh := ((Complex.hasDerivAt_exp _).scomp x hpath).const_mul (-I)
    convert hh using 1
    · funext y
      exact he y
    · simp only [smul_eq_mul]
      ring_nf
      simp only [Complex.I_sq]
      ring
  have hn (x : ℝ) : ‖-exp (-((x : ℂ) * I))‖ ≤ 1 := by simp [norm_exp]
  refine ⟨?_, ?_⟩
  · intro x
    simp only [norm_mul, norm_neg, Complex.norm_I, norm_conj, Circle.norm_coe, mul_one]
  · intro x y
    simpa only [p, one_mul] using curve_norm_sub_le hd hn x y

/-- Taking the real rotating boundary field preserves the Zygmund
condition, the boundary step in the inverse of TS2 (TT:917, TT:982–990). -/
theorem real_boundary_isZygmund (B : C(Circle, ℂ)) {C K : ℝ}
    (hb : ∀ ζ : Circle, ‖B ζ‖ ≤ C)
    (hbd : ∀ x t : ℝ, ‖B (Circle.exp (x + t)) + B (Circle.exp (x - t)) - 2 * B (Circle.exp x)‖ ≤ K * |t|) :
    IsZygmund (fun x : ℝ => 2 * ((-I * conj ((Circle.exp x : Circle) : ℂ)) * B (Circle.exp x)).re) := by
  let p : ℝ → ℂ := fun x => -I * conj ((Circle.exp x : Circle) : ℂ)
  let b : ℝ → ℂ := fun x => B (Circle.exp x)
  let u : ℝ → ℝ := fun x => 2 * (p x * b x).re
  have hc : Continuous u := by dsimp [u, p, b]; fun_prop
  have hperiod (x : ℝ) : Circle.exp (x + 2 * π) = Circle.exp x := by
    apply Subtype.ext
    simp only [Circle.coe_exp, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
      add_mul, exp_add, exp_two_pi_mul_I, mul_one]
  refine ⟨hc, ?_, 2 * (K + 2 * C), ?_⟩
  · intro x
    change u (x + 2 * π) = u x
    simp only [u, p, b, hperiod]
  · intro x t
    have hcomplex := second_difference_product_bound
      (fun x => (boundary_rotation_factor.1 x).le) boundary_rotation_factor.2
      (fun x => hb (Circle.exp x)) hbd x t
    let D := p (x + t) * b (x + t) + p (x - t) * b (x - t) - 2 * (p x * b x)
    have he : u (x + t) + u (x - t) - 2 * u x = 2 * D.re := by
      dsimp only [u, D]
      norm_num [add_re, sub_re, mul_re] <;> ring
    change |u (x + t) + u (x - t) - 2 * u x| ≤ _
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hnorm := Complex.abs_re_le_norm D
    change ‖D‖ ≤ (K + 2 * C) * |t| at hcomplex
    nlinarith

/-- A disk holomorphic function has one scalar Taylor series throughout
the disk, with its first three coefficients determined by its jets
(TT:917, TT:982–1001). -/
theorem exists_disk_scalar_series {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) :
    ∃ c : ℕ → ℂ, (∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z)) ∧
      c 0 = F 0 ∧ c 1 = deriv F 0 ∧ 2 * c 2 = deriv (deriv F) 0 := by
  let R₀ : ℝ≥0 := 1 / 2
  have hR₀ : 0 < R₀ := by norm_num [R₀]
  have hbaseD : DifferentiableOn ℂ F (closedBall 0 (R₀ : ℝ)) := by
    apply hF.mono
    intro z hz
    apply mem_ball_zero_iff.mpr
    have hh := mem_closedBall_zero_iff.mp hz
    norm_num [R₀] at hh
    linarith
  let p := cauchyPowerSeries F 0 R₀
  have hbase : HasFPowerSeriesOnBall F p 0 R₀ := hbaseD.hasFPowerSeriesOnBall hR₀
  refine ⟨p.coeff, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    let R : ℝ≥0 := ⟨(‖z‖ + 1) / 2, by positivity⟩
    have hR0 : 0 < R := by change 0 < (‖z‖ + 1) / 2; positivity
    have hR1 : (R : ℝ) < 1 := by change (‖z‖ + 1) / 2 < 1; linarith
    have hzr : ‖z‖ < R := by change ‖z‖ < (‖z‖ + 1) / 2; linarith
    have hlocalD : DifferentiableOn ℂ F (closedBall 0 (R : ℝ)) := by
      apply hF.mono
      intro w hw
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hR1)
    have hlocal := hbase.exchange_radius (hlocalD.hasFPowerSeriesOnBall hR0)
    have hzn : (‖z‖₊ : ℝ≥0∞) < (R : ℝ≥0∞) := by exact_mod_cast hzr
    have hzball : z ∈ Metric.eball 0 (R : ℝ≥0∞) := by
      simpa only [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] using hzn
    simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul, mul_comm] using hlocal.hasSum hzball
  · exact hbase.hasFPowerSeriesAt.coeff_zero 1
  · exact hbase.hasFPowerSeriesAt.deriv.symm
  · have hh := hbase.factorial_smul (1 : ℂ) 2
    rw [← iteratedDeriv_eq_iteratedFDeriv] at hh
    simpa only [FormalMultilinearSeries.coeff, Pi.one_def, Nat.factorial_succ, Nat.factorial_zero,
      Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, nsmul_eq_mul, Nat.cast_ofNat,
      iteratedDeriv_succ, iteratedDeriv_zero] using hh

/-- **TS4** (TT:1004). `T₀^ℝ S¹\Homeo_qs(S¹) ⊂ 𝓗ˢ(S¹)` for all `s < 1`. -/
theorem TS4 {u : ℝ → ℝ} (hu : u ∈ tangentQS) {s : ℝ} (hs : s < 1) :
    fourierCoeff (fun θ => (u θ : ℂ)) ∈ sobolevH s := by
  have hp := zygmund_fourier_nat_sobolev hu.1 hs
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa using hp
  · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast,
      fourierCoeff_neg_real, norm_conj] using hp

end TakhtajanTeo
