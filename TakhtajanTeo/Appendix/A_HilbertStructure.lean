import TakhtajanTeo.Ch2.S5_PeriodMapping
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Appendix A — The Hilbert manifold structure of `𝒯₀(1)` (TT:5752–5967)

The Bers embedding `β` and the pre-Bers embedding `β̂` of `𝒯(1)`. Lemma A.1, Corollary A.2, Theorem A.3,
Corollary A.4, `β*`, `β̂*`, Lemma A.5, Corollary A.6.

**Modelling.**
- A point of `𝒯(1)` is parametrized by `([μ], w) ∈ T(1) × 𝔻*` (TT:571), i.e. the point `([μ], 𝗀_μ(w)) ∈ TCurve`.
  - By `fiber_welding` (Chapter 1, §1.2), its welding `γ = g⁻¹ ∘ f` (CW1, CW2′, CW3′, CW4) has
    `f = λ_c ∘ f^μ` and `g = λ_c ∘ g_μ ∘ σ_w⁻¹`, with `c = -1/g_μ(w)` (`weldF`, `weldG`).
  - `𝒯₀(1)` is the part over `T₀(1)`.
  - Its topology is the product of the Hilbert manifold topology of `T₀(1)` with that of `ℂ̄`, as in Proposition 3.9
    of Chapter 1.
- Spaces of holomorphic functions are the function sets `A21fun`, `A2fun` with their norms (`normA21`, `normA2`).
  - Openness is metric openness for these norms.
  - "Same Hilbert manifold structure" (Theorem A.3) is stated as what its proof establishes:
    - `β = Ψ̂ ∘ β̂` with `Ψ̂` injective and holomorphic;
    - at every `ψ ∈ β̂(𝒯₀(1))` the derivative `D_ψΨ̂ : φ ↦ (φ' - ψφ, ½φ(0))` is a bounded bijection
      `A₂¹(𝔻) → A₂(𝔻) ⊕ ℂ`. The inverse function theorem then gives a biholomorphism.
  - Holomorphy of a map between these spaces is complex differentiability along complex lines in norm (TT:5782).

**Corrections.** Corollary A.6 (TT:5928–5948): "`\varliminf`" is an OCR rendering of `lim`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-- The univalent function `f` of the welding of the point `([μ], 𝗀_μ(w))` of `𝒯(1)`: `f = λ_c ∘ f^μ`, `c = -1/g_μ(w)`. -/
def weldF (μ : LinfStar) (w : ℂ) (z : ℂ) : ℂ := lambdaW (-1 / gMu μ w) (fB μ z)
/-- The univalent function `g = λ_c ∘ g_μ ∘ σ_w⁻¹` of the welding of `([μ], 𝗀_μ(w))`.

[CORRECTION 2026-10-27] Computed on the sphere, exactly as the exterior map of the corrected `fiber_welding`: the
earlier `Function.invFun (sigmaW w)` was arbitrary at `σ_w(∞) ∈ 𝔻*`, which made `weldG` discontinuous there (found by
下属1). -/
def weldG (μ : LinfStar) (w : ℂ) (z : ℂ) : ℂ :=
  finPart (mobiusExt 1 0 (-1 / gMu μ w) 1
    (normalizedWeldingSphere μ (sigmaInvSphere (w : ExtPlane) (z : ExtPlane))))

/-- The Bers embedding `β(γ) = (𝒮(f), ½𝒜(f)(0))` of `𝒯(1)` into `A_∞(𝔻) ⊕ ℂ` (TT:5758). -/
def betaT (p : T1) (w : ℂ) : (ℂ → ℂ) × ℂ :=
  (schwarzianHol (weldF (Quotient.out p : LinfStarBall) w),
    (1 / 2) * preSchwarzian (weldF (Quotient.out p : LinfStarBall) w) 0)

/-- The pre-Bers embedding `β̂(γ) = 𝒜(f)` of `𝒯(1)` into `A_∞¹(𝔻)` (TT:5764). -/
def betaHat (p : T1) (w : ℂ) : ℂ → ℂ := preSchwarzian (weldF (Quotient.out p : LinfStarBall) w)

/-- `β̂(𝒯₀(1))` as a set of functions on `𝔻` (compared on `𝔻`). -/
def betaHatT0 : Set (ℂ → ℂ) :=
  {ψ | ∃ p ∈ T01, ∃ w ∈ unitDiscExterior, EqOn ψ (betaHat p w) unitDisc}

-- `betaHat_spec` moved to `Appendix/AppACompleted.lean` (2026-10-27).

/-- The injectivity assertion in Lemma A.1 holds for all holomorphic functions on the disk
(TT:5774–5798). An integrating factor turns the difference into a function with zero derivative. -/
theorem PsiOp_injective_with_value {ψ₁ ψ₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ ψ₁ unitDisc) (h₂ : DifferentiableOn ℂ ψ₂ unitDisc)
    (hPsi : EqOn (PsiOp ψ₁) (PsiOp ψ₂) unitDisc) (hzero : ψ₁ 0 = ψ₂ 0) :
    EqOn ψ₁ ψ₂ unitDisc := by
  have hq : DifferentiableOn ℂ (fun z => (ψ₁ z + ψ₂ z) / 2) (ball 0 1) :=
    (h₁.add h₂).div_const 2
  obtain ⟨H, hH⟩ := hq.isExactOn_ball
  let F : ℂ → ℂ := fun z => (ψ₁ z - ψ₂ z) * Complex.exp (-H z)
  have hF : ∀ z ∈ unitDisc, HasDerivAt F 0 z := by
    intro z hz
    have hd₁ := (h₁.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hd₂ := (h₂.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hdiff : deriv ψ₁ z - deriv ψ₂ z = (ψ₁ z + ψ₂ z) / 2 * (ψ₁ z - ψ₂ z) := by
      have he := hPsi hz
      dsimp [PsiOp] at he
      linear_combination he
    have hp := (hd₁.sub hd₂).mul ((hH z hz).neg.cexp)
    exact hp.congr_deriv (by rw [hdiff]; simp only [Pi.sub_apply]; ring)
  intro z hz
  have hconst : F z = F 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF w hw).deriv) hz (mem_ball_self (by norm_num))
  have hprod : (ψ₁ z - ψ₂ z) * Complex.exp (-H z) = 0 := by
    simpa only [F, hzero, sub_self, zero_mul] using hconst
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (Complex.exp_ne_zero _))

/-- The exact pointwise remainder used in the holomorphy proof of Lemma A.1 (TT:5782–5788).
The weighted norm estimate is a separate analytic step. -/
theorem PsiOp_line_remainder {ψ φ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (hφ : DifferentiableAt ℂ φ z)
    {t t₀ : ℂ} (ht : t ≠ t₀) :
    (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
      (deriv φ z - (ψ z + t₀ * φ z) * φ z) = -(t - t₀) / 2 * φ z ^ 2 := by
  have hd (a : ℂ) : deriv (fun u => ψ u + a * φ u) z = deriv ψ z + a * deriv φ z :=
    (hψ.hasDerivAt.add (hφ.hasDerivAt.const_mul a)).deriv
  simp only [PsiOp, hd]
  field_simp [sub_ne_zero.mpr ht]
  <;> ring

/-- A square of an `A₂¹` direction has finite weighted norm when the direction also satisfies the
`A∞¹` bound used in the proof of Lemma A.1 (TT:5786–5788). -/
theorem normA2_sq_lt_top_of_A21_AInf1 {D : Set ℂ} (hD : MeasurableSet D) {φ : ℂ → ℂ}
    (h₂ : φ ∈ A21fun D) (hInf : φ ∈ AInf1fun D) : normA2 D (fun z => φ z ^ 2) < ∞ := by
  obtain ⟨C₀, hC₀⟩ := hInf.2
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hpoint (z : ℂ) (hz : z ∈ D) :
      (‖φ z ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ ≤
        ENNReal.ofReal (C ^ 2) * (‖φ z‖₊ : ℝ≥0∞) ^ 2 := by
    have hb : |1 - ‖z‖ ^ 2| * ‖φ z‖ ≤ C := by
      have := (hC₀ z hz).trans (le_max_left C₀ 0)
      have hcast : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast] at this
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using this
    have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg (1 - ‖z‖ ^ 2)) (norm_nonneg (φ z))) hb 2
    have hrho : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm,
      ENNReal.toReal_ofReal hrho, ENNReal.toReal_ofReal (sq_nonneg C)]
    calc
      _ = (|1 - ‖z‖ ^ 2| * ‖φ z‖) ^ 2 / 4 * ‖φ z‖ ^ 2 := by
        rw [norm_pow, rho, inv_div, mul_pow, sq_abs]
        ring
      _ ≤ C ^ 2 * ‖φ z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg C]) (sq_nonneg _)
  have hint : (∫⁻ z in D, (‖φ z‖₊ : ℝ≥0∞) ^ 2) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h₂.2
  have htotal : (∫⁻ z in D, (‖φ z ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) < ∞ := by
    have hle : (∫⁻ z in D, (‖φ z ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) ≤
        ∫⁻ z in D, ENNReal.ofReal (C ^ 2) * (‖φ z‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hD] with z hz
      exact hpoint z hz
    apply lt_of_le_of_lt hle
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) htotal.ne

/-- The norm remainder along a complex line on an arbitrary open domain. -/
theorem PsiOp_line_remainder_tendsto_on {D : Set ℂ} (hD : IsOpen D) {ψ φ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ D) (hφ : DifferentiableOn ℂ φ D)
    (hφsq : normA2 D (fun z => φ z ^ 2) < ∞) (t₀ : ℂ) :
    Tendsto (fun t : ℂ => normA2 D (fun z =>
      (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
        (deriv φ z - (ψ z + t₀ * φ z) * φ z))) (𝓝[≠] t₀) (𝓝 0) := by
  have hc : Continuous (fun t : ℂ => (‖-(t - t₀) / 2‖₊ : ℝ≥0∞)) := by fun_prop
  have ht₀ : Tendsto (fun t : ℂ => (‖-(t - t₀) / 2‖₊ : ℝ≥0∞)) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self, neg_zero, zero_div, nnnorm_zero, ENNReal.coe_zero] using hc.tendsto t₀
  have ht : Tendsto (fun t : ℂ => (‖-(t - t₀) / 2‖₊ : ℝ≥0∞)) (𝓝[≠] t₀) (𝓝 0) := by
    exact ht₀.mono_left nhdsWithin_le_nhds
  have hm := ENNReal.Tendsto.mul_const ht (Or.inr hφsq.ne)
  simp only [zero_mul] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  symm
  calc
    _ = normA2 D (fun z => (-(t - t₀) / 2) * φ z ^ 2) := by
      apply normA2_congr hD.measurableSet
      intro z hz
      exact PsiOp_line_remainder
        (hψ.differentiableAt (hD.mem_nhds hz))
        (hφ.differentiableAt (hD.mem_nhds hz)) ht
    _ = _ := normA2_const_mul _ _ _

/-- Squaring a direction in either A₂¹ disk model gives a genuine A₂ function. -/
theorem A21_square_mem_A2 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {φ : ℂ → ℂ} (hφ : φ ∈ A21fun D) : (fun z => φ z ^ 2) ∈ A2fun D := by
  have hm : MeasurableSet D := by
    rcases hD with rfl | rfl
    · exact measurableSet_ball
    · exact resolvent_exterior_isOpen.measurableSet
  exact ⟨hφ.1.pow 2, normA2_sq_lt_top_of_A21_AInf1 hm hφ (a21_mem_AInf1fun hD hφ)⟩

/-- The line derivative in Lemma A.1 follows once the squared direction has finite weighted norm
(TT:5782–5788). This isolates the analytic integrability prerequisite explicitly. -/
theorem PsiOp_line_remainder_tendsto {ψ φ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ unitDisc) (hφ : DifferentiableOn ℂ φ unitDisc)
    (hφsq : normA2 unitDisc (fun z => φ z ^ 2) < ∞) (t₀ : ℂ) :
    Tendsto (fun t : ℂ => normA2 unitDisc (fun z =>
      (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
        (deriv φ z - (ψ z + t₀ * φ z) * φ z))) (𝓝[≠] t₀) (𝓝 0) := by

  exact PsiOp_line_remainder_tendsto_on isOpen_ball hψ hφ hφsq t₀

/-- **Lemma A.1** (TT:5774–5798). `Ψ̂ : A₂¹(𝔻) → A₂(𝔻) ⊕ ℂ`, `Ψ̂(ψ) = (Ψ(ψ), ½ψ(0))`, `Ψ(ψ) = ψ_z - ½ψ²`, is one to one
and holomorphic.
- `Ψ` maps `A₂¹(𝔻)` to `A₂(𝔻)`.
- `t ↦ Ψ(ψ + tφ)` is complex differentiable in `A₂(𝔻)`, with derivative `φ' - (ψ + t₀φ)φ` at `t₀`.
- `|ψ(0)| ≤ √(1/π) ‖ψ‖_{A₂¹}`.
- `Ψ̂` is injective [Teo04]. -/
theorem lemma_A_1 :
    (∀ ψ ∈ A21fun unitDisc, PsiOp ψ ∈ A2fun unitDisc) ∧
      (∀ ψ ∈ A21fun unitDisc, ∀ φ ∈ A21fun unitDisc, ∀ t₀ : ℂ,
        Tendsto (fun t : ℂ => normA2 unitDisc (fun z =>
            (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
              (deriv φ z - (ψ z + t₀ * φ z) * φ z))) (𝓝[≠] t₀) (𝓝 0)) ∧
      (∀ ψ ∈ A21fun unitDisc, ENNReal.ofReal ‖ψ 0‖ ≤ ENNReal.ofReal (Real.sqrt (1 / π)) * normA21 unitDisc ψ) ∧
      ∀ ψ₁ ∈ A21fun unitDisc, ∀ ψ₂ ∈ A21fun unitDisc, EqOn (PsiOp ψ₁) (PsiOp ψ₂) unitDisc → ψ₁ 0 = ψ₂ 0 →
        EqOn ψ₁ ψ₂ unitDisc := by
  refine ⟨fun _ hψ => lemma_1_5_disc hψ, ?_, ?_, ?_⟩
  · intro ψ hψ φ hφ t₀
    exact PsiOp_line_remainder_tendsto hψ.1 hφ.1
      (normA2_sq_lt_top_of_A21_AInf1 measurableSet_ball hφ (a21_mem_AInf1fun (Or.inl rfl) hφ)) t₀
  · intro ψ hψ
    simpa only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] using a21_origin_bound hψ
  · intro ψ₁ h₁ ψ₂ h₂ hPsi hzero
    exact PsiOp_injective_with_value h₁.1 h₂.1 hPsi hzero

-- `cor_A_2` moved to `Appendix/AppACor2.lean` (2026-10-27).

/-- The first-order linearized equation in Theorem A.3 has a unique solution with a prescribed value at zero. -/
theorem linearized_Psi_injective {ψ φ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ unitDisc) (hφ : DifferentiableOn ℂ φ unitDisc)
    (heq : EqOn (fun z => deriv φ z - ψ z * φ z) 0 unitDisc) (hzero : φ 0 = 0) :
    EqOn φ 0 unitDisc := by
  obtain ⟨H, hH⟩ := hψ.isExactOn_ball
  let F : ℂ → ℂ := fun z => φ z * Complex.exp (-H z)
  have hF (z : ℂ) (hz : z ∈ unitDisc) : HasDerivAt F 0 z := by
    have hd := (hφ.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hdz : deriv φ z = ψ z * φ z := sub_eq_zero.mp (heq hz)
    apply (hd.mul ((hH z hz).neg.cexp)).congr_deriv
    rw [hdz]
    ring
  intro z hz
  have hconst : F z = F 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF w hw).deriv) hz (mem_ball_self (by norm_num))
  have hprod : φ z * Complex.exp (-H z) = 0 := by simpa only [F, hzero, zero_mul] using hconst
  exact (mul_eq_zero.mp hprod).resolve_right (Complex.exp_ne_zero _)

/-- The linearized Psi operator is bounded from disk A₂¹ to A₂ for every weighted-bounded holomorphic coefficient. -/
theorem linearized_Psi_bounded {ψ : ℂ → ℂ} (hψ : ψ ∈ AInf1fun unitDisc) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ φ ∈ A21fun unitDisc,
      (fun z => deriv φ z - ψ z * φ z) ∈ A2fun unitDisc ∧
      normA2 unitDisc (fun z => deriv φ z - ψ z * φ z) ≤ C * normA21 unitDisc φ := by
  obtain ⟨B₀, hB₀⟩ := hψ.2
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨ENNReal.ofReal (1 + B), ENNReal.ofReal_lt_top, ?_⟩
  intro φ hφ
  let G : ℂ → ℂ := fun z => deriv φ z - ψ z * φ z
  have hhol : DifferentiableOn ℂ G unitDisc :=
    (hφ.1.deriv isOpen_ball).sub (hψ.1.mul hφ.1)
  have hprod (z : ℂ) (hz : z ∈ unitDisc) :
      ‖ψ z * φ z‖ ^ 2 * (rho z)⁻¹ ≤ (B ^ 2 / 4) * ‖φ z‖ ^ 2 := by
    have hb : |1 - ‖z‖ ^ 2| * ‖ψ z‖ ≤ B := by
      have h := (hB₀ z hz).trans (le_max_left B₀ 0)
      have hcast : 1 - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast] at h
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
    have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hb 2
    rw [mul_pow, sq_abs] at hs
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖φ z‖)
    simp only [norm_mul, mul_pow, rho, inv_div]
    nlinarith only [hm]
  have hpoint (z : ℂ) (hz : z ∈ unitDisc) :
      ‖G z‖ ^ 2 * (rho z)⁻¹ ≤ 2 * (‖deriv φ z‖ ^ 2 * (rho z)⁻¹) + (B ^ 2 / 2) * ‖φ z‖ ^ 2 := by
    have hn : ‖G z‖ ≤ ‖deriv φ z‖ + ‖ψ z * φ z‖ := norm_sub_le _ _
    have hs : ‖G z‖ ^ 2 ≤ 2 * ‖deriv φ z‖ ^ 2 + 2 * ‖ψ z * φ z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖deriv φ z‖ - ‖ψ z * φ z‖),
        mul_nonneg (sub_nonneg.mpr hn) (by positivity : 0 ≤ ‖deriv φ z‖ + ‖ψ z * φ z‖ + ‖G z‖)]
    have hm := mul_le_mul_of_nonneg_right hs (by dsimp [rho]; positivity : 0 ≤ (rho z)⁻¹)
    nlinarith only [hm, hprod z hz]
  have hφInt := a21_integrable_sq (D := unitDisc) measurableSet_ball hφ
  have hdInt := A21_disk_derivative_integrable hφ
  have hc : ContinuousOn (fun z => ‖G z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply (hhol.continuousOn.norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  have hGInt : IntegrableOn (fun z => ‖G z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply ((hdInt.const_mul 2).add (hφInt.const_mul (B ^ 2 / 2))).mono' (hc.aestronglyMeasurable measurableSet_ball)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [rho]; positivity)]
    exact hpoint z hz
  have hGA2 : G ∈ A2fun unitDisc := ⟨hhol, normA2_lt_top_of_integrable_weighted_sq hGInt⟩
  refine ⟨hGA2, ?_⟩
  have hdMass : (∫ z in unitDisc, ‖deriv φ z‖ ^ 2 * (rho z)⁻¹) ≤
      (1 / 2) * ∫ z in unitDisc, ‖φ z‖ ^ 2 := by
    have hb := A21_disk_derivative_bound hφ
    rw [← ofReal_integral_eq_lintegral_ofReal hdInt (Eventually.of_forall fun z =>
      show 0 ≤ ‖deriv φ z‖ ^ 2 * (rho z)⁻¹ by dsimp [rho]; positivity)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hMass : (∫ z in unitDisc, ‖G z‖ ^ 2 * (rho z)⁻¹) ≤
      (1 + B) ^ 2 * ∫ z in unitDisc, ‖φ z‖ ^ 2 := by
    have hb := integral_mono_ae hGInt ((hdInt.const_mul 2).add (hφInt.const_mul (B ^ 2 / 2)))
      ((ae_restrict_mem measurableSet_ball).mono fun z hz => hpoint z hz)
    simp only [Pi.add_apply] at hb
    rw [integral_add (hdInt.const_mul 2) (hφInt.const_mul (B ^ 2 / 2)), integral_const_mul, integral_const_mul] at hb
    have harea : 0 ≤ ∫ z in unitDisc, ‖φ z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
    have hcoef : 1 + B ^ 2 / 2 ≤ (1 + B) ^ 2 := by nlinarith [sq_nonneg B]
    have hcMass := mul_le_mul_of_nonneg_right hcoef harea
    nlinarith only [hb, hdMass, hcMass]
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [A2fun.normA2_sq (D := unitDisc) isOpen_ball hGA2,
    a21_norm_sq_eq_integral (D := unitDisc) measurableSet_ball hφ,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + B), ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hMass

/-- Real parametrization of the segment from zero stays inside the disk. -/
theorem disk_radial_segment_mem {z : ℂ} (hz : z ∈ unitDisc) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (t : ℂ) * z ∈ unitDisc := by
  apply mem_ball_zero_iff.mpr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt (mem_ball_zero_iff.mp hz)

/-- The concrete segment integral equals the difference of any holomorphic primitive. -/
theorem disk_segment_integral_eq_primitive {q H : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q unitDisc) (hH : ∀ z ∈ unitDisc, HasDerivAt H (q z) z)
    {z : ℂ} (hz : z ∈ unitDisc) :
    (∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z) = H z - H 0 := by
  have hmap : MapsTo (fun t : ℝ => (t : ℂ) * z) (Icc (0 : ℝ) 1) unitDisc :=
    fun _ ht => disk_radial_segment_mem hz ht
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => H ((t : ℂ) * z)) (q ((t : ℂ) * z) * z) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simpa only [Function.comp_def, id_eq, one_mul] using
      ((hH _ (hmap ht')).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => q ((t : ℂ) * z) * z) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hq.continuousOn.comp (by fun_prop) hmap).mul_const z
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul] using he

/-- The actual radial-segment integral is a holomorphic primitive, with derivative q. -/
theorem disk_segment_integral_hasDerivAt {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun z : ℂ => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z) (q z) z := by
  obtain ⟨H, hH⟩ := hq.isExactOn_ball
  have he : (fun w : ℂ => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * w) * w) =ᶠ[𝓝 z]
      (fun w => H w - H 0) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact disk_segment_integral_eq_primitive hq hH hw
  exact ((hH z hz).sub_const (H 0)).congr_of_eventuallyEq he

/-- The explicit variation-of-constants formula in Theorem A.3 solves its first-order equation.
The value at zero includes f'(0); the normalized conclusion needs f'(0)=1. -/
theorem explicit_linearized_Psi_solution {f ϕ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hϕ : DifferentiableOn ℂ ϕ unitDisc) (c : ℂ) :
    let φ : ℂ → ℂ := fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
    DifferentiableOn ℂ φ unitDisc ∧
      EqOn (fun z => deriv φ z - preSchwarzian f z * φ z) ϕ unitDisc ∧
      (1 / 2) * φ 0 = deriv f 0 * c := by
  let q : ℂ → ℂ := fun z => ϕ z / deriv f z
  let P : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  have hq : DifferentiableOn ℂ q unitDisc := hϕ.div hdf hne
  have hP (z : ℂ) (hz : z ∈ unitDisc) : HasDerivAt P (q z) z := disk_segment_integral_hasDerivAt hq hz
  have hφ (z : ℂ) (hz : z ∈ unitDisc) :
      HasDerivAt (fun z => deriv f z * (P z + 2 * c))
        (deriv (deriv f) z * (P z + 2 * c) + deriv f z * q z) z :=
    ((hdf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).mul ((hP z hz).add_const (2 * c))
  refine ⟨fun z hz => (hφ z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    change deriv (fun z => deriv f z * (P z + 2 * c)) z -
      preSchwarzian f z * (deriv f z * (P z + 2 * c)) = ϕ z
    rw [(hφ z hz).deriv]
    dsimp [preSchwarzian, q]
    field_simp [hne z hz]
    <;> ring
  · simp only [mul_zero, intervalIntegral.integral_zero, zero_add]
    ring

/-- The original A.3 value condition follows from the explicit origin normalization. -/
theorem explicit_linearized_Psi_solution_normalized {f ϕ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hϕ : DifferentiableOn ℂ ϕ unitDisc) (c : ℂ) :
    let φ : ℂ → ℂ := fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
    DifferentiableOn ℂ φ unitDisc ∧
      EqOn (fun z => deriv φ z - preSchwarzian f z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c := by
  simpa only [hzero, one_mul] using explicit_linearized_Psi_solution hf hne hϕ c

/-- A holomorphic function whose derivative has finite A₂ energy belongs to disk A₂¹.
This uses the valid coercive estimate (1.2), not the unqualified Lemma 1.11. -/
theorem a21_of_derivative_A2 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hd : deriv g ∈ A2fun unitDisc) : g ∈ A21fun unitDisc := by
  have hi := A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hd
  let W : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖ ^ 2
  have hW : IntegrableOn W unitDisc := by
    have he : W = (fun z => 4 * (‖deriv g z‖ ^ 2 * (rho z)⁻¹)) := by
      funext z
      dsimp [W, rho]
      rw [inv_div]
      ring
    rw [he]
    exact hi.const_mul 4
  apply a21_of_uniform_disk_mass hg
  refine ⟨2 * (∫ z in unitDisc, W z) + π * ‖g 0‖ ^ 2, ?_⟩
  intro r hr0 hr1
  have hb := eq_1_2_of_differentiable hg hr0 hr1
  have hm : (∫ z in ball (0 : ℂ) r, W z) ≤ ∫ z in unitDisc, W z :=
    setIntegral_mono_set hW (Filter.Eventually.of_forall fun z => by dsimp [W]; positivity)
      (Filter.Eventually.of_forall fun z hz => ball_subset_ball hr1.le hz)
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hconst := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖g 0‖ ^ 2 by positivity)
  change (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖g z‖ ^ 2) - π / 2 * ‖g 0‖ ^ 2 * r ^ 2 ≤
    ∫ z in ball (0 : ℂ) r, W z at hb
  nlinarith only [hb, hm, hconst]

/-- A₂ energy of the integrand gives A₂¹ energy of the actual segment primitive. -/
theorem disk_segment_integral_A21 {q : ℂ → ℂ} (hq : q ∈ A2fun unitDisc) :
    (fun z : ℂ => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z) ∈ A21fun unitDisc := by
  let P : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z
  have hP : DifferentiableOn ℂ P unitDisc := fun z hz =>
    (disk_segment_integral_hasDerivAt hq.1 hz).differentiableAt.differentiableWithinAt
  have hd : EqOn (deriv P) q unitDisc := fun z hz => (disk_segment_integral_hasDerivAt hq.1 hz).deriv
  apply a21_of_derivative_A2 hP
  refine ⟨hP.deriv isOpen_ball, ?_⟩
  rw [normA2_congr (D := unitDisc) measurableSet_ball hd]
  exact hq.2

/-- A small weighted coefficient near the boundary lets the linearized equation control its solution's A₂¹ energy. -/
theorem linearized_Psi_solution_A21_of_boundary_small {ψ φ ϕ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hϕ : ϕ ∈ A2fun unitDisc)
    (heq : EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc)
    (hsmall : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ z ∈ unitDisc,
      s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖ψ z‖ ≤ 1 / 4) : φ ∈ A21fun unitDisc := by
  obtain ⟨s, hs0, hs1, hs⟩ := hsmall
  let H : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv φ z‖ ^ 2
  have hH : ContinuousOn H unitDisc :=
    (by fun_prop : ContinuousOn (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) unitDisc).mul
      ((hφ.deriv isOpen_ball).continuousOn.norm.pow 2)
  have hsub (r : ℝ) (hr : r < 1) : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    (hH.mono (hsub s hs1))
  let J : ℂ → ℝ := fun z => 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) + max B 0
  have hJi : IntegrableOn J unitDisc :=
    ((A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hϕ).const_mul 8).add
      (integrableOn_const (show volume unitDisc ≠ ∞ from measure_ball_lt_top.ne))
  have hJ0 (z : ℂ) : 0 ≤ J z := by dsimp [J, rho]; positivity
  have hpoint (z : ℂ) (hz : z ∈ unitDisc) : H z ≤ J z + (1 / 4) * ‖φ z‖ ^ 2 := by
    by_cases hzs : ‖z‖ ≤ s
    · have hb := hB z (mem_closedBall_zero_iff.mpr hzs)
      have hH0 : 0 ≤ H z := by dsimp [H]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hH0] at hb
      have hpos : 0 ≤ 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) := by unfold rho; positivity
      dsimp [J]
      nlinarith [le_max_left B 0, sq_nonneg ‖φ z‖]
    · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hw : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hψsq := pow_le_pow_left₀ (mul_nonneg hw (norm_nonneg _)) (hs z hz (lt_of_not_ge hzs)) 2
      rw [mul_pow] at hψsq
      have hψscaled := mul_le_mul_of_nonneg_right hψsq (sq_nonneg ‖φ z‖)
      have hd : deriv φ z = ψ z * φ z + ϕ z := by
        have he := heq hz
        dsimp only at he
        linear_combination he
      have hn : ‖deriv φ z‖ ≤ ‖ψ z‖ * ‖φ z‖ + ‖ϕ z‖ := by
        rw [hd]
        simpa only [norm_mul] using norm_add_le (ψ z * φ z) (ϕ z)
      have hdSq : ‖deriv φ z‖ ^ 2 ≤ 2 * (‖ψ z‖ ^ 2 * ‖φ z‖ ^ 2) + 2 * ‖ϕ z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖ψ z‖ * ‖φ z‖ - ‖ϕ z‖),
          mul_nonneg (sub_nonneg.mpr hn)
            (by positivity : 0 ≤ ‖ψ z‖ * ‖φ z‖ + ‖ϕ z‖ + ‖deriv φ z‖)]
      have hm := mul_le_mul_of_nonneg_left hdSq (sq_nonneg (1 - ‖z‖ ^ 2))
      dsimp [H, J, rho]
      rw [inv_div]
      nlinarith [hm, hψscaled, le_max_right B 0, sq_nonneg ‖φ z‖]
  apply a21_of_uniform_disk_mass hφ
  refine ⟨4 * (∫ z in unitDisc, J z) + 2 * π * ‖φ 0‖ ^ 2, ?_⟩
  intro r hr0 hr1
  have hφi : IntegrableOn (fun z => ‖φ z‖ ^ 2) (ball (0 : ℂ) r) :=
    (((hφ.continuousOn.norm.pow 2).mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hHi : IntegrableOn H (ball (0 : ℂ) r) :=
    ((hH.mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hrd : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hJr := hJi.mono_set hrd
  have hupper : (∫ z in ball (0 : ℂ) r, H z) ≤
      (∫ z in unitDisc, J z) + (1 / 4) * ∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2 := by
    have hi := setIntegral_mono_on hHi (hJr.add (hφi.const_mul (1 / 4))) measurableSet_ball
      (fun z hz => hpoint z (hrd hz))
    simp only [Pi.add_apply] at hi
    rw [integral_add hJr (hφi.const_mul (1 / 4)), integral_const_mul] at hi
    have hJle := setIntegral_mono_set hJi (Eventually.of_forall hJ0) (Eventually.of_forall hrd)
    linarith
  have hlower := eq_1_2_of_differentiable hφ hr0 hr1
  change (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2) - π / 2 * ‖φ 0‖ ^ 2 * r ^ 2 ≤
    ∫ z in ball (0 : ℂ) r, H z at hlower
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have herror := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖φ 0‖ ^ 2 by positivity)
  nlinarith

/-- An A₂¹ coefficient automatically supplies the needed boundary smallness, so every holomorphic solution has finite energy. -/
theorem linearized_Psi_solution_A21 {ψ φ ϕ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun unitDisc) (hφ : DifferentiableOn ℂ φ unitDisc)
    (hϕ : ϕ ∈ A2fun unitDisc) (heq : EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc) :
    φ ∈ A21fun unitDisc := by
  have htwice := a21_const_mul (D := unitDisc) measurableSet_ball hψ (2 : ℂ)
  obtain ⟨s, hs0, hs1, hs⟩ := boundary_small_of_weighted_tendsto_zero (cor_1_4 (Or.inl rfl) htwice)
  apply linearized_Psi_solution_A21_of_boundary_small hφ hϕ heq
  refine ⟨s, hs0, hs1, ?_⟩
  intro z hz hzs
  have hb := hs z hz hzs
  rw [norm_mul] at hb
  norm_num only [Complex.norm_ofNat] at hb
  linarith

/-- The A.3 segment preimage has finite A₂¹ energy whenever the actual pre-Schwarzian is in A₂¹.
No global bound on f' or 1/f' is required. -/
theorem explicit_linearized_Psi_solution_A21 {f ϕ : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hpre : preSchwarzian f ∈ A21fun unitDisc) (hϕ : ϕ ∈ A2fun unitDisc) (c : ℂ) :
    (fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) ∈ A21fun unitDisc := by
  have hsol := explicit_linearized_Psi_solution hf hne hϕ.1 c
  exact linearized_Psi_solution_A21 hpre hsol.1 hϕ hsol.2.1

/-- The elementary Möbius factor in the actual weldF definition has an explicit nonzero derivative off its pole. -/
theorem lambdaW_hasDerivAt (a z : ℂ) (hne : a * z + 1 ≠ 0) :
    HasDerivAt (lambdaW a) ((a * z + 1) ^ 2)⁻¹ z := by
  have hd := (hasDerivAt_id z).div (((hasDerivAt_id z).const_mul a).add_const 1) hne
  apply hd.congr_deriv
  dsimp only [id_eq]
  simp only [mul_one, one_mul]
  ring

/-- Origin normalization of the actual weldF follows from the proved Model B normalization, without a welding spec. -/
theorem weldF_normalization (μ : LinfStar) (w : ℂ) :
    weldF μ w 0 = 0 ∧ deriv (weldF μ w) 0 = 1 := by
  have hn := fB_normalization μ
  have hdiff : DifferentiableAt ℂ (fB μ) 0 :=
    differentiableAt_of_deriv_ne_zero (by rw [hn.2.1]; exact one_ne_zero)
  have hf : HasDerivAt (fB μ) 1 0 := by simpa only [hn.2.1] using hdiff.hasDerivAt
  have hMob : HasDerivAt (lambdaW (-1 / gMu μ w)) 1 (fB μ 0) := by
    rw [hn.1]
    simpa only [mul_zero, zero_add, one_pow, inv_one] using
      lambdaW_hasDerivAt (-1 / gMu μ w) 0 (by simp only [mul_zero, zero_add]; exact one_ne_zero)
  refine ⟨?_, ?_⟩
  · simp only [weldF, hn.1, lambdaW, zero_div]
  · change deriv (fun z => lambdaW (-1 / gMu μ w) (fB μ z)) 0 = 1
    simpa only [Function.comp_def, one_mul] using (hMob.comp 0 hf).deriv

/-- Holomorphy, univalence, and nonvanishing derivative for weldF under the exact missing pole-avoidance premise. -/
theorem weldF_regular_of_avoids_pole {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (w : ℂ)
    (hpole : ∀ z ∈ unitDisc, (-1 / gMu μ w) * fB μ z + 1 ≠ 0) :
    DifferentiableOn ℂ (weldF μ w) unitDisc ∧ InjOn (weldF μ w) unitDisc ∧
      ∀ z ∈ unitDisc, deriv (weldF μ w) z ≠ 0 := by
  have hB := fB_holomorphic_injective hμ
  have hhol : DifferentiableOn ℂ (weldF μ w) unitDisc := by
    change DifferentiableOn ℂ (fun z => fB μ z / ((-1 / gMu μ w) * fB μ z + 1)) unitDisc
    exact hB.1.div ((hB.1.const_mul _).add_const 1) hpole
  have hinj : InjOn (weldF μ w) unitDisc := by
    intro x hx y hy he
    apply hB.2 hx hy
    change fB μ x / ((-1 / gMu μ w) * fB μ x + 1) =
      fB μ y / ((-1 / gMu μ w) * fB μ y + 1) at he
    have hm := (div_eq_div_iff (hpole x hx) (hpole y hy)).mp he
    linear_combination hm
  exact ⟨hhol, hinj, fun z hz => deriv_ne_zero_of_injOn isOpen_ball hhol hinj hz⟩

/-- Pointwise disjointness of the exterior value from the disk image suffices for the precise pole premise. -/
theorem weldF_avoids_pole_of_excluded_value (μ : LinfStar) (w : ℂ)
    (hexcluded : ∀ z ∈ unitDisc, fB μ z ≠ gMu μ w) :
    ∀ z ∈ unitDisc, (-1 / gMu μ w) * fB μ z + 1 ≠ 0 := by
  intro z hz he
  by_cases hg : gMu μ w = 0
  · simpa only [hg, div_zero, zero_mul, zero_add, one_ne_zero] using he
  · apply hexcluded z hz
    field_simp [hg] at he
    linear_combination -he

/-- The exact A.3 formula for the actual weldF satisfies the analytic equation and value condition,
using only explicit pole avoidance and proved Model B interfaces. -/
theorem weldF_explicit_solution_of_avoids_pole {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (w : ℂ)
    (hpole : ∀ z ∈ unitDisc, (-1 / gMu μ w) * fB μ z + 1 ≠ 0)
    {ϕ : ℂ → ℂ} (hϕ : ϕ ∈ A2fun unitDisc) (c : ℂ) :
    let f := weldF μ w
    let φ : ℂ → ℂ := fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
    DifferentiableOn ℂ φ unitDisc ∧
      EqOn (fun z => deriv φ z - preSchwarzian f z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c := by
  have hreg := weldF_regular_of_avoids_pole hμ w hpole
  exact explicit_linearized_Psi_solution_normalized hreg.1 hreg.2.2
    (weldF_normalization μ w).2 hϕ.1 c

/-- The full analytic content of Theorem A.3, with the actual regularity and A₂¹ pre-Schwarzian premises explicit. -/
theorem thm_A_3_analytic {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hpre : preSchwarzian f ∈ A21fun unitDisc) :
    (∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      let φ : ℂ → ℂ := fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
      φ ∈ A21fun unitDisc ∧ EqOn (fun z => deriv φ z - preSchwarzian f z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c) ∧
      (∀ φ ∈ A21fun unitDisc, EqOn (fun z => deriv φ z - preSchwarzian f z * φ z) 0 unitDisc →
        φ 0 = 0 → EqOn φ 0 unitDisc) ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ φ ∈ A21fun unitDisc,
        normA2 unitDisc (fun z => deriv φ z - preSchwarzian f z * φ z) ≤ C * normA21 unitDisc φ := by
  refine ⟨?_, ?_, ?_⟩
  · intro ϕ hϕ c
    have hsol := explicit_linearized_Psi_solution_normalized hf hne hzero hϕ.1 c
    exact ⟨explicit_linearized_Psi_solution_A21 hf hne hpre hϕ c, hsol.2⟩
  · intro φ hφ he hv
    exact linearized_Psi_injective hpre.1 hφ.1 he hv
  · obtain ⟨C, hC, hb⟩ := linearized_Psi_bounded (a21_mem_AInf1fun (Or.inl rfl) hpre)
    exact ⟨C, hC, fun φ hφ => (hb φ hφ).2⟩

/-- The exact original A.3 conclusion follows once pole avoidance and the actual betaHat A₂¹ membership are supplied.
This does not infer those geometric premises from an unproved welding or component theorem. -/
theorem thm_A_3_of_pole_and_A21 (p : T1) (w : ℂ)
    (hpole : ∀ z ∈ unitDisc, (-1 / gMu (Quotient.out p : LinfStarBall) w) *
      fB (Quotient.out p : LinfStarBall) z + 1 ≠ 0)
    (hpre : betaHat p w ∈ A21fun unitDisc) :
    let f := weldF (Quotient.out p : LinfStarBall) w
    let ψ := betaHat p w
    (∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      let φ : ℂ → ℂ := fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)
      φ ∈ A21fun unitDisc ∧ EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc ∧ (1 / 2) * φ 0 = c) ∧
      (∀ φ ∈ A21fun unitDisc, EqOn (fun z => deriv φ z - ψ z * φ z) 0 unitDisc → φ 0 = 0 → EqOn φ 0 unitDisc) ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ φ ∈ A21fun unitDisc,
        normA2 unitDisc (fun z => deriv φ z - ψ z * φ z) ≤ C * normA21 unitDisc φ := by
  have hreg := weldF_regular_of_avoids_pole (Quotient.out p : LinfStarBall).property w hpole
  exact thm_A_3_analytic hreg.1 hreg.2.2
    (weldF_normalization (Quotient.out p : LinfStarBall) w).2 hpre

/-- An integrable disk mass is the limit of its masses on expanding smaller disks. -/
theorem integrableOn_disk_mass_tendsto {F : ℂ → ℝ} (hF : IntegrableOn F unitDisc) :
    Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) r, F z) (𝓝[<] 1) (𝓝 (∫ z in unitDisc, F z)) := by
  let H : ℂ → ℝ := unitDisc.indicator F
  have hH : Integrable H := hF.integrable_indicator measurableSet_ball
  have hlim : ∀ᵐ z : ℂ, Tendsto (fun r : ℝ => (ball (0 : ℂ) r).indicator H z) (𝓝 1) (𝓝 (H z)) := by
    apply ae_of_all
    intro z
    by_cases hz : z ∈ unitDisc
    · have he : ∀ᶠ r : ℝ in 𝓝 1, ‖z‖ < r := Ioi_mem_nhds (mem_ball_zero_iff.mp hz)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with r hr
      exact (indicator_of_mem (mem_ball_zero_iff.mpr hr) H).symm
    · have hzero : H z = 0 := indicator_of_notMem hz F
      simp only [indicator_apply, hzero, ite_self]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => ‖H z‖)
    (Filter.Eventually.of_forall fun r : ℝ => hH.aestronglyMeasurable.indicator measurableSet_ball)
    (Filter.Eventually.of_forall fun _ => ae_of_all volume fun z => norm_indicator_le_norm_self H z)
    hH.norm hlim
  have htotal : (∫ z : ℂ, H z) = ∫ z in unitDisc, F z := integral_indicator measurableSet_ball
  have hball (r : ℝ) : (∫ z : ℂ, (ball (0 : ℂ) r).indicator H z) = ∫ z in ball (0 : ℂ) r, H z :=
    integral_indicator measurableSet_ball
  have ht' : Tendsto (fun r : ℝ => ∫ z in ball (0 : ℂ) r, H z) (𝓝[<] 1)
      (𝓝 (∫ z in unitDisc, F z)) := by
    simpa only [hball, htotal] using ht.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  have hrlt : r < 1 := hr
  exact indicator_of_mem (ball_subset_ball hrlt.le hz) F

/-- A global coercive energy bound for a disk holomorphic function with A₂ derivative. -/
theorem a21_mass_bound_of_derivative_A2 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hd : deriv g ∈ A2fun unitDisc) :
    (∫ z in unitDisc, ‖g z‖ ^ 2) ≤
      8 * (∫ z in unitDisc, ‖deriv g z‖ ^ 2 * (rho z)⁻¹) + π * ‖g 0‖ ^ 2 := by
  have hA21 := a21_of_derivative_A2 hg hd
  have hmass := integrableOn_disk_mass_tendsto (a21_integrable_sq (D := unitDisc) measurableSet_ball hA21)
  have hi := A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hd
  have hpos₀ : ∀ᶠ r : ℝ in 𝓝 1, 0 < r := Ioi_mem_nhds (by norm_num)
  apply le_of_tendsto hmass
  filter_upwards [hpos₀.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr0 hr1
  have hrlt : r < 1 := hr1
  have hb := eq_1_2_of_differentiable hg hr0 hrlt
  have hsub : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hrlt.le
  have hm := setIntegral_mono_set hi
    (Filter.Eventually.of_forall fun z => show 0 ≤ ‖deriv g z‖ ^ 2 * (rho z)⁻¹ by dsimp [rho]; positivity)
    (Filter.Eventually.of_forall hsub)
  have he (z : ℂ) : (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖ ^ 2 =
      4 * (‖deriv g z‖ ^ 2 * (rho z)⁻¹) := by simp only [rho, inv_div]; ring
  simp_rw [he] at hb
  rw [integral_const_mul] at hb
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hc := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖g 0‖ ^ 2 by positivity)
  nlinarith only [hb, hm, hc]

/-- The concrete segment integration operator has a uniform A₂-to-A₂¹ norm bound. -/
theorem disk_segment_integral_norm_bound {q : ℂ → ℂ} (hq : q ∈ A2fun unitDisc) :
    normA21 unitDisc (fun z : ℂ => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z) ≤
      ENNReal.ofReal (Real.sqrt 8) * normA2 unitDisc q := by
  let P : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..1, q ((t : ℂ) * z) * z
  have hP : P ∈ A21fun unitDisc := disk_segment_integral_A21 hq
  have hd : EqOn (deriv P) q unitDisc := fun z hz => (disk_segment_integral_hasDerivAt hq.1 hz).deriv
  have hdA2 : deriv P ∈ A2fun unitDisc := by
    refine ⟨hP.1.deriv isOpen_ball, ?_⟩
    rw [normA2_congr (D := unitDisc) measurableSet_ball hd]
    exact hq.2
  have hm := a21_mass_bound_of_derivative_A2 hP.1 hdA2
  have hzero : P 0 = 0 := by simp only [P, mul_zero, intervalIntegral.integral_zero]
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at hm
  have he : (∫ z in unitDisc, ‖deriv P z‖ ^ 2 * (rho z)⁻¹) =
      ∫ z in unitDisc, ‖q z‖ ^ 2 * (rho z)⁻¹ := by
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro z hz
    dsimp only
    rw [hd hz]
  rw [he] at hm
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [a21_norm_sq_eq_integral (D := unitDisc) measurableSet_ball hP,
    A2fun.normA2_sq (D := unitDisc) isOpen_ball hq,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  exact ENNReal.ofReal_le_ofReal hm

-- `thm_A_3` moved to `Appendix/AppACompleted.lean` (2026-10-27).

-- `cor_A_4` moved to `TakhtajanTeo.Appendix.AppACor4Final` (2026-10-29, Program G).

/-- `β̂*(γ) = 𝒜(g)` on `𝔻*` (TT:5934). -/
def betaHatStar (p : T1) (w : ℂ) : ℂ → ℂ := preSchwarzian (weldG (Quotient.out p : LinfStarBall) w)

/-- `Ã₂¹(𝔻*) = {ψ ∈ A₂¹(𝔻*) : ψ(z) = O(z⁻³), z → ∞}` (TT:5942). -/
def A21tildeExt : Set (ℂ → ℂ) :=
  {ψ ∈ A21fun unitDiscExterior | ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3}

-- `betaStar_spec` moved to `Appendix/AppACompleted2.lean` (2026-10-27).

/-- Cubic exterior decay gives a holomorphic inverted one-form vanishing at zero,
with the precise transformed Psi equation on the punctured disk. -/
theorem A21tildeExt.inverted_extension {ψ : ℂ → ℂ} (hψ : ψ ∈ A21tildeExt) :
    ∃ q : ℂ → ℂ, q ∈ A21fun unitDisc ∧ q 0 = 0 ∧
      EqOn q (fun z => -ψ z⁻¹ / z ^ 2) (unitDisc \ {0}) ∧
      ∀ z ∈ unitDisc \ {0}, PsiOp ψ z⁻¹ / z ^ 4 = PsiOp q z + 2 * q z / z := by
  obtain ⟨g, hg, heq, _⟩ := a21_remove_puncture (a21_inverted_cubic hψ.1 hψ.2)
  let q : ℂ → ℂ := fun z => z * g z
  refine ⟨q, A21_disk_mul_id hg, by simp only [q, zero_mul], ?_, ?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := hz.2
    change z * g z = -ψ z⁻¹ / z ^ 2
    rw [heq hz]
    field_simp [hz0]
  · intro z hz
    have hz0 : z ≠ 0 := hz.2
    rw [PsiOp_inversion_identity hψ.1.1 heq hz]
    change PsiOp q z + 2 * g z = PsiOp q z + 2 * (z * g z) / z
    field_simp [hz0]

/-- The transformed Psi equality gives the precise first-order equation for the inverted difference. -/
theorem inverted_Psi_difference_deriv {q₁ q₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ q₁ unitDisc) (h₂ : DifferentiableOn ℂ q₂ unitDisc)
    (heq : ∀ z ∈ unitDisc \ {0}, PsiOp q₁ z + 2 * q₁ z / z = PsiOp q₂ z + 2 * q₂ z / z)
    {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    deriv (fun w => q₁ w - q₂ w) z = ((q₁ z + q₂ z) / 2 - 2 / z) * (q₁ z - q₂ z) := by
  have hd₁ := (h₁.differentiableAt (isOpen_ball.mem_nhds hz.1)).hasDerivAt
  have hd₂ := (h₂.differentiableAt (isOpen_ball.mem_nhds hz.1)).hasDerivAt
  change deriv (q₁ - q₂) z = ((q₁ z + q₂ z) / 2 - 2 / z) * (q₁ z - q₂ z)
  rw [(hd₁.sub hd₂).deriv]
  have he := heq z hz
  dsimp [PsiOp] at he
  linear_combination he

/-- Multiplying the inverted difference by z² removes the singular coefficient -2/z.
The resulting equation is holomorphic at zero, with zero initial value. -/
theorem inverted_Psi_difference_linear_ode {q₁ q₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ q₁ unitDisc) (h₂ : DifferentiableOn ℂ q₂ unitDisc)
    (heq : ∀ z ∈ unitDisc \ {0}, PsiOp q₁ z + 2 * q₁ z / z = PsiOp q₂ z + 2 * q₂ z / z) :
    let F : ℂ → ℂ := fun z => z ^ 2 * (q₁ z - q₂ z)
    EqOn (fun z => deriv F z - ((q₁ z + q₂ z) / 2) * F z) 0 unitDisc ∧ F 0 = 0 := by
  let F : ℂ → ℂ := fun z => z ^ 2 * (q₁ z - q₂ z)
  have hF (z : ℂ) (hz : z ∈ unitDisc) : HasDerivAt F
      (2 * z * (q₁ z - q₂ z) + z ^ 2 * (deriv q₁ z - deriv q₂ z)) z := by
    have hd₁ := (h₁.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hd₂ := (h₂.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    simpa only [F, Pi.mul_def, Pi.sub_def, Pi.pow_apply, id_eq,
      show (2 : ℕ) - 1 = 1 by decide, pow_one, mul_one, Nat.cast_ofNat] using
      ((hasDerivAt_id z).pow 2).mul (hd₁.sub hd₂)
  refine ⟨?_, by simp only [F, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]⟩
  intro z hz
  change deriv F z - ((q₁ z + q₂ z) / 2) * F z = 0
  rw [(hF z hz).deriv]
  by_cases hz0 : z = 0
  · simp only [hz0, F, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, add_zero, sub_zero]
  · have he := heq z ⟨hz, hz0⟩
    calc
      _ = z ^ 2 * ((PsiOp q₁ z + 2 * q₁ z / z) - (PsiOp q₂ z + 2 * q₂ z / z)) := by
        dsimp [F, PsiOp]
        field_simp [hz0]
        <;> ring
      _ = 0 := by rw [he, sub_self, mul_zero]

/-- The valid injectivity clause of Lemma A.5 on its original cubic-decay space.
No unrestricted exterior Psi inclusion or welding assertion is used. -/
theorem PsiOp_injective_on_A21tildeExt {ψ₁ ψ₂ : ℂ → ℂ}
    (h₁ : ψ₁ ∈ A21tildeExt) (h₂ : ψ₂ ∈ A21tildeExt)
    (hPsi : EqOn (PsiOp ψ₁) (PsiOp ψ₂) unitDiscExterior) :
    EqOn ψ₁ ψ₂ unitDiscExterior := by
  obtain ⟨q₁, hq₁, hq₁zero, hq₁eq, hq₁Psi⟩ := A21tildeExt.inverted_extension h₁
  obtain ⟨q₂, hq₂, hq₂zero, hq₂eq, hq₂Psi⟩ := A21tildeExt.inverted_extension h₂
  have heq : ∀ z ∈ unitDisc \ {0}, PsiOp q₁ z + 2 * q₁ z / z = PsiOp q₂ z + 2 * q₂ z / z := by
    intro z hz
    rw [← hq₁Psi z hz, ← hq₂Psi z hz, hPsi (a21_inv_punctured hz)]
  let F : ℂ → ℂ := fun z => z ^ 2 * (q₁ z - q₂ z)
  have hF : DifferentiableOn ℂ F unitDisc := (differentiableOn_id.pow 2).mul (hq₁.1.sub hq₂.1)
  have hcoef : DifferentiableOn ℂ (fun z => (q₁ z + q₂ z) / 2) unitDisc := (hq₁.1.add hq₂.1).div_const 2
  have hode := inverted_Psi_difference_linear_ode hq₁.1 hq₂.1 heq
  have hzero : EqOn F 0 unitDisc := linearized_Psi_injective hcoef hF hode.1 hode.2
  intro z hz
  have ht : z⁻¹ ∈ unitDisc \ {0} := a21_inv_exterior hz
  have ht0 : z⁻¹ ≠ 0 := ht.2
  have he : q₁ z⁻¹ = q₂ z⁻¹ := by
    have hh := hzero ht.1
    change (z⁻¹) ^ 2 * (q₁ z⁻¹ - q₂ z⁻¹) = 0 at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 ht0))
  rw [hq₁eq ht, hq₂eq ht] at he
  dsimp only at he
  rw [inv_inv] at he
  exact neg_injective ((div_left_inj' (pow_ne_zero 2 ht0)).mp he)

/-- A weighted-bounded holomorphic coefficient multiplies A₂¹ into A₂ with the explicit half-weight bound. -/
theorem A21_product_bound_of_weighted_bound {D : Set ℂ} (hD : IsOpen D) {ψ φ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ D) (hφ : φ ∈ A21fun D) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ D, ‖(1 - (‖z‖ : ℂ) ^ 2) * ψ z‖ ≤ C) :
    (fun z => ψ z * φ z) ∈ A2fun D ∧
      normA2 D (fun z => ψ z * φ z) ≤ ENNReal.ofReal (C / 2) * normA21 D φ := by
  have hhol := hψ.mul hφ.1
  have hpoint (z : ℂ) (hz : z ∈ D) :
      ‖ψ z * φ z‖ ^ 2 * (rho z)⁻¹ ≤ (C ^ 2 / 4) * ‖φ z‖ ^ 2 := by
    have hb : |1 - ‖z‖ ^ 2| * ‖ψ z‖ ≤ C := by
      have h := hbound z hz
      have hcast : 1 - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast] at h
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
    have hs := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hb 2
    rw [mul_pow, sq_abs] at hs
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖φ z‖)
    simp only [norm_mul, mul_pow, rho, inv_div]
    nlinarith only [hm]
  have hφInt := a21_integrable_sq hD.measurableSet hφ
  have hc : ContinuousOn (fun z => ‖ψ z * φ z‖ ^ 2 * (rho z)⁻¹) D := by
    apply (hhol.continuousOn.norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  have hi : IntegrableOn (fun z => ‖ψ z * φ z‖ ^ 2 * (rho z)⁻¹) D := by
    apply (hφInt.const_mul (C ^ 2 / 4)).mono' (hc.aestronglyMeasurable hD.measurableSet)
    filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [rho]; positivity)]
    exact hpoint z hz
  have hA2 : (fun z => ψ z * φ z) ∈ A2fun D := ⟨hhol, normA2_lt_top_of_integrable_weighted_sq hi⟩
  refine ⟨hA2, ?_⟩
  have hm : (∫ z in D, ‖ψ z * φ z‖ ^ 2 * (rho z)⁻¹) ≤ (C / 2) ^ 2 * ∫ z in D, ‖φ z‖ ^ 2 := by
    have hh := integral_mono_ae hi (hφInt.const_mul (C ^ 2 / 4))
      ((ae_restrict_mem hD.measurableSet).mono fun z hz => hpoint z hz)
    rw [integral_const_mul] at hh
    convert hh using 1 <;> ring
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [A2fun.normA2_sq hD hA2, a21_norm_sq_eq_integral hD.measurableSet hφ,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ C / 2), ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hm

/-- Multiplication A₂¹×A₂¹→A₂ is bounded on either full disk model, hence also on the cubic-decay subspace. -/
theorem A21_product_bounded {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {ψ φ : ℂ → ℂ} (hψ : ψ ∈ A21fun D) (hφ : φ ∈ A21fun D) :
    (fun z => ψ z * φ z) ∈ A2fun D ∧
      normA2 D (fun z => ψ z * φ z) ≤
        ENNReal.ofReal (1 / (2 * Real.sqrt π)) * normA21 D ψ * normA21 D φ := by
  have hopen : IsOpen D := by rcases hD with rfl | rfl; exact isOpen_ball; exact resolvent_exterior_isOpen
  let N : ℝ := (normA21 D ψ).toReal
  let C : ℝ := (1 / Real.sqrt π) * N
  have hC : 0 ≤ C := by dsimp [C, N]; positivity
  have hb (z : ℂ) (hz : z ∈ D) : ‖(1 - (‖z‖ : ℂ) ^ 2) * ψ z‖ ≤ C := by
    have h := lemma_1_3 hD hψ z hz
    rw [← ENNReal.ofReal_toReal hψ.2.ne,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt π)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp h
  obtain ⟨hm, hn⟩ := A21_product_bound_of_weighted_bound hopen hψ.1 hφ hC hb
  refine ⟨hm, ?_⟩
  have he : C / 2 = (1 / (2 * Real.sqrt π)) * N := by dsimp [C]; ring
  rw [he, ENNReal.ofReal_mul (by positivity), show ENNReal.ofReal N = normA21 D ψ from ENNReal.ofReal_toReal hψ.2.ne] at hn
  exact hn

/-- The product has a Lipschitz estimate in each fixed factor, expressed with the actual integral norms. -/
theorem A21_product_sub_bound {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {ψ φ₁ φ₂ : ℂ → ℂ} (hψ : ψ ∈ A21fun D) (h₁ : φ₁ ∈ A21fun D) (h₂ : φ₂ ∈ A21fun D) :
    normA2 D (fun z => ψ z * φ₁ z - ψ z * φ₂ z) ≤
      ENNReal.ofReal (1 / (2 * Real.sqrt π)) * normA21 D ψ * normA21 D (fun z => φ₁ z - φ₂ z) := by
  have hm : MeasurableSet D := by
    rcases hD with rfl | rfl
    · exact measurableSet_ball
    · exact resolvent_exterior_isOpen.measurableSet
  have hsub : (fun z => φ₁ z - φ₂ z) ∈ A21fun D := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using a21_add hm h₁ (a21_const_mul hm h₂ (-1 : ℂ))
  have he : (fun z => ψ z * φ₁ z - ψ z * φ₂ z) = (fun z => ψ z * (φ₁ z - φ₂ z)) := by
    funext z; ring
  rw [he]
  exact (A21_product_bounded hD hψ hsub).2

/-- Fixed-factor multiplication is continuous for the actual A₂¹ and A₂ integral norms. -/
theorem A21_product_tendsto {ι : Type*} {l : Filter ι} {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior) {ψ φ : ℂ → ℂ} {u : ι → ℂ → ℂ}
    (hψ : ψ ∈ A21fun D) (hφ : φ ∈ A21fun D) (hu : ∀ i, u i ∈ A21fun D)
    (hlim : Tendsto (fun i => normA21 D (fun z => u i z - φ z)) l (𝓝 0)) :
    Tendsto (fun i => normA2 D (fun z => ψ z * u i z - ψ z * φ z)) l (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.sqrt π)) * normA21 D ψ
  have hK : K < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψ.2
  have ht : Tendsto (fun i => K * normA21 D (fun z => u i z - φ z)) l (𝓝 0) := by
    simpa only [mul_comm, zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hK.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) (fun i => A21_product_sub_bound hD hψ (hu i) hφ)

/-- The second clause of Lemma A.5 holds for the original full exterior A₂¹ hypotheses,
independently of its invalid unrestricted Psi-image clause. -/
theorem lemma_A_5_line_remainder :
    ∀ ψ ∈ A21fun unitDiscExterior, ∀ φ ∈ A21fun unitDiscExterior, ∀ t₀ : ℂ,
      Tendsto (fun t : ℂ => normA2 unitDiscExterior (fun z =>
          (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
            (deriv φ z - (ψ z + t₀ * φ z) * φ z))) (𝓝[≠] t₀) (𝓝 0) := by
  intro ψ hψ φ hφ t₀
  exact PsiOp_line_remainder_tendsto_on resolvent_exterior_isOpen hψ.1 hφ.1
    (A21_square_mem_A2 (Or.inr rfl) hφ).2 t₀

/-- The first clause of Lemma A.5: `Ψ*` maps `Ã₂¹(𝔻*)` into `A₂(𝔻*)` (Lemma 1.5, exterior case with cubic decay). -/
theorem lemma_A_5_mapping : ∀ ψ ∈ A21tildeExt, PsiOp ψ ∈ A2fun unitDiscExterior :=
  fun _ hψ => lemma_1_5_exterior_of_cubic_decay hψ.1 hψ.2

-- `lemma_A_5` moved to `Appendix/AppACompleted2.lean` (2026-10-27); conjunct 5 still open there.

-- `cor_A_6` moved to `TakhtajanTeo.Appendix.AppACor6` (2026-10-29, Program G).

end AppA

end TakhtajanTeo
