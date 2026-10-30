import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.SmoothFourier
import TakhtajanTeo.Ch1.WeightedPowerSeries
import TakhtajanTeo.Ch1.PowerSeriesThirdDerivative
import TakhtajanTeo.Ch1.ZygmundSummable

/-!
# Chapter 1, §4 — Velling–Kirillov and Weil–Petersson metrics (TT:2122–2216)

* (4.1) the Velling–Kirillov metric at the origin of `𝒯(1)`, its convergence (TS4 with `s = 1/2`), `ω_VK`
* (4.2) the Weil–Petersson inner product at the origin of `T(1)`; (4.3) the metric coefficients `g_{μν̄}` on `V₀`
* Lemma 4.2 (continuity), Remark 4.3 (real analyticity), `ω_WP`, Remark 4.4 (Nag–Verjovsky)

**Modelling.**
- At the origin, a holomorphic tangent vector `v = (u - iJu)/2` is given by the Fourier coefficients `c_n`, `n ≥ 1`,
  of `u`.
- The Velling–Kirillov metric at the other points of `𝒯(1)` is defined in §5, by right translation in holomorphic
  coordinates, where it is compared with `c₁(V)` (Theorem 5.3).
- "VK is a smooth right-invariant Kähler metric" (TT:2136) is the content of Theorem 5.3 (`K` is a Kähler potential)
  and is stated there.
- Remark 4.1 (TT:2146) cites [Kir87, KY87, Vel, Teo04], including the uniqueness of the right-invariant Kähler metric
  on `𝒯(1)` [Teo04]. The memoir does not use it, and it is not stated.
- "The WP metric is Kähler" (TT:2200) is proved in §7 and stated there.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- **(4.1)** (TT:2127). The Velling–Kirillov norm at the origin of `𝒯(1)`: `‖v‖²_VK = Σ_{n ≥ 1} n |c_n|²` for
`v = (u - iJu)/2`, `u = Σ_{n ≠ 0} c_n e^{inθ} d/dθ`. -/
def vkNormSqOrigin (c : ℤ → ℂ) : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖c (n + 1)‖ ^ 2

/-- (TT:2136) The series (4.1) converges for every `u ∈ T₀^ℝ S¹\Homeo_qs(S¹)` (TS4 with `s = 1/2`). -/
theorem vkNormSqOrigin_summable {u : ℝ → ℝ} (hu : u ∈ tangentQS) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (n + 1)‖ ^ 2 := by
  exact zygmund_vk_summable hu.1

/-- The symplectic form `ω_VK(v, v̄) = (i/2) ‖v‖²_VK` at the origin (TT:2139). -/
def omegaVKOrigin (c : ℤ → ℂ) : ℂ := I / 2 * vkNormSqOrigin c

/-- **(4.2)** (TT:2157). The Weil–Petersson inner product at the origin of `T(1)`:
`⟨μ, ν⟩_WP = ∬_{𝔻*} μ ν̄ ρ(z) d²z` for `μ, ν ∈ H^{-1,1}(𝔻*) = T₀T(1)`. -/
def wpInner (μ ν : ℂ → ℂ) : ℂ := ∫ z in unitDiscExterior, μ z * conj (ν z) * rho z

/-- `ω_WP(μ, ν̄) = (i/2) ⟨μ, ν⟩_WP` at the origin (TT:2203). -/
def omegaWPOrigin (μ ν : ℂ → ℂ) : ℂ := I / 2 * wpInner μ ν

/-- The density in (4.2) is nonnegative, including its totalized values (TT:2157). -/
theorem wp_rho_nonneg (z : ℂ) : 0 ≤ rho z := by
  unfold rho
  positivity

/-- The density in (4.2) is positive on the exterior disk (TT:2157). -/
theorem wp_rho_pos {z : ℂ} (hz : z ∈ unitDiscExterior) : 0 < rho z := by
  change 1 < ‖z‖ at hz
  have hn : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  exact div_pos (by norm_num) (sq_pos_of_ne_zero hn)

/-- The exterior disk used in (4.2) is open (TT:2157). -/
theorem wp_exterior_isOpen : IsOpen unitDiscExterior := by
  exact isOpen_lt continuous_const continuous_norm

/-- Continuity of the density in (4.2) on the exterior disk (TT:2157). -/
theorem wp_rho_continuousOn : ContinuousOn rho unitDiscExterior := by
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub (continuous_norm.continuousOn.pow 2)).pow 2)
  intro z hz
  change 1 < ‖z‖ at hz
  apply pow_ne_zero
  change 1 - ‖z‖ ^ 2 ≠ 0
  nlinarith [norm_nonneg z]

/-- Harmonic representatives in (4.2) are continuous on the exterior disk (TT:2154). -/
theorem wp_harmonic_continuousOn {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ContinuousOn μ unitDiscExterior := by
  obtain ⟨φ, hφ, hrep, _⟩ := hμ
  have hc := (Complex.continuous_ofReal.comp_continuousOn wp_rho_continuousOn).inv₀
    (fun z hz => Complex.ofReal_ne_zero.mpr (wp_rho_pos hz).ne')
  exact (hc.mul (Complex.continuous_conj.comp_continuousOn hφ.continuousOn)).congr hrep

/-- The defining finite norm in (4.2) gives an integrable weighted squared norm (TT:2154). -/
theorem wp_integrable_sq {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => ‖μ z‖ ^ 2 * rho z) unitDiscExterior := by
  have hc := ((wp_harmonic_continuousOn hμ).norm.pow 2).mul wp_rho_continuousOn
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have hf : (∫⁻ z in unitDiscExterior,
      (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hfinite
  refine ⟨hc.aestronglyMeasurable wp_exterior_isOpen.measurableSet, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun z => mul_nonneg (sq_nonneg _) (wp_rho_nonneg z)))]
  simpa only [ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm, enorm_eq_nnnorm] using hf

/-- The product in (4.2) is integrable by the weighted squared-norm bound (TT:2154). -/
theorem wpInner_integrable {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    Integrable (fun z => μ z * conj (ν z) * rho z) (volume.restrict unitDiscExterior) := by
  have hc := ((wp_harmonic_continuousOn hμ).mul
    (Complex.continuous_conj.comp_continuousOn (wp_harmonic_continuousOn hν))).mul
    (Complex.continuous_ofReal.comp_continuousOn wp_rho_continuousOn)
  apply ((wp_integrable_sq hμ).add (wp_integrable_sq hν)).mono'
    (hc.aestronglyMeasurable wp_exterior_isOpen.measurableSet)
  filter_upwards [] with z
  change ‖μ z * conj (ν z) * (rho z : ℂ)‖ ≤
    ‖μ z‖ ^ 2 * rho z + ‖ν z‖ ^ 2 * rho z
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (wp_rho_nonneg z)]
  have hab : ‖μ z‖ * ‖ν z‖ ≤ ‖μ z‖ ^ 2 + ‖ν z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖μ z‖ - ‖ν z‖), sq_nonneg ‖μ z‖, sq_nonneg ‖ν z‖]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hab (wp_rho_nonneg z)

/-- Conjugate symmetry of (4.2), also valid for totalized integrals (TT:2154). -/
theorem wpInner_conj_symm (μ ν : ℂ → ℂ) : wpInner ν μ = conj (wpInner μ ν) := by
  unfold wpInner
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ring

/-- The diagonal of (4.2) is the real weighted squared-norm integral (TT:2154). -/
theorem wpInner_self_re {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (wpInner μ μ).re = ∫ z in unitDiscExterior, ‖μ z‖ ^ 2 * rho z := by
  unfold wpInner
  calc
    (∫ z in unitDiscExterior, μ z * conj (μ z) * rho z).re =
        ∫ z in unitDiscExterior, (μ z * conj (μ z) * (rho z : ℂ)).re :=
      (integral_re (wpInner_integrable hμ hμ)).symm
    _ = _ := ?_
  apply integral_congr_ae
  filter_upwards [] with z
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- A nonzero harmonic representative has strictly positive squared WP norm (TT:2154). -/
theorem wpInner_self_pos {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hne : ∃ z ∈ unitDiscExterior, μ z ≠ 0) : 0 < (wpInner μ μ).re := by
  rw [wpInner_self_re hμ]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (wp_rho_nonneg z)))
    (wp_integrable_sq hμ)).mpr
  have hc := ((wp_harmonic_continuousOn hμ).norm.pow 2).mul wp_rho_continuousOn
  have hopen := hc.isOpen_inter_preimage wp_exterior_isOpen (isOpen_Ioi (a := (0 : ℝ)))
  obtain ⟨z, hz, hμz⟩ := hne
  have hpos : 0 < ‖μ z‖ ^ 2 * rho z :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hμz)) (wp_rho_pos hz)
  have hm := hopen.measure_pos (μ := volume) ⟨z, hz, hpos⟩
  apply lt_of_lt_of_le hm
  apply measure_mono
  intro w hw
  exact ⟨ne_of_gt hw.2, hw.1⟩

/-- (TT:2154) `⟨·, ·⟩_WP` is a Hermitian inner product on `H^{-1,1}(𝔻*)`: finite, conjugate symmetric, positive
definite (on functions nonzero on a set of positive measure of `𝔻*`). -/
theorem wpInner_hermitian {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    Integrable (fun z => μ z * conj (ν z) * rho z) (volume.restrict unitDiscExterior) ∧
      wpInner ν μ = conj (wpInner μ ν) ∧ ((∃ z ∈ unitDiscExterior, μ z ≠ 0) → 0 < (wpInner μ μ).re) := by
  exact ⟨wpInner_integrable hμ hν, wpInner_conj_symm μ ν, wpInner_self_pos hμ⟩

/-- Multiplication by `√ρ` realizes the tangent vectors of (4.2) in ordinary L2
on the exterior disk (TT:2154–2157). -/
theorem wp_weighted_memLp {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    MemLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)) 2 (volume.restrict unitDiscExterior) := by
  have hc := (wp_harmonic_continuousOn hμ).mul
    (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_sqrt.comp_continuousOn wp_rho_continuousOn))
  apply (memLp_two_iff_integrable_sq_norm
    (hc.aestronglyMeasurable wp_exterior_isOpen.measurableSet)).mpr
  change Integrable (fun z => ‖μ z * (Real.sqrt (rho z) : ℂ)‖ ^ 2)
    (volume.restrict unitDiscExterior)
  simpa only [IntegrableOn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (wp_rho_nonneg _)]
    using wp_integrable_sq hμ

/-- The convention of (4.2) is linear in the first variable, hence the reversed
arguments in Mathlib's L2 inner product (TT:2157). -/
theorem wpInner_eq_L2_inner {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    inner ℂ ((wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ)))
      ((wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))) = wpInner μ ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(wp_weighted_memLp hν).coeFn_toLp,
    (wp_weighted_memLp hμ).coeFn_toLp] with z hνz hμz
  rw [hνz, hμz]
  rw [RCLike.inner_apply]
  change (μ z * (Real.sqrt (rho z) : ℂ)) * conj (ν z * (Real.sqrt (rho z) : ℂ)) =
    μ z * conj (ν z) * (rho z : ℂ)
  simp only [map_mul, Complex.conj_ofReal]
  have hs : (Real.sqrt (rho z) : ℂ) ^ 2 = (rho z : ℂ) := by
    exact_mod_cast Real.sq_sqrt (wp_rho_nonneg z)
  calc
    _ = μ z * conj (ν z) * (Real.sqrt (rho z) : ℂ) ^ 2 := by ring
    _ = _ := by rw [hs]

/-- Cauchy–Schwarz for the Weil–Petersson inner product (4.2), in squared form
(TT:2154–2157). -/
theorem wpInner_cauchy_schwarz {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    ‖wpInner μ ν‖ ^ 2 ≤ (wpInner μ μ).re * (wpInner ν ν).re := by
  let f := (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))
  let g := (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))
  have hgf : inner ℂ g f = wpInner μ ν := wpInner_eq_L2_inner hμ hν
  have hff : inner ℂ f f = wpInner μ μ := wpInner_eq_L2_inner hμ hμ
  have hgg : inner ℂ g g = wpInner ν ν := wpInner_eq_L2_inner hν hν
  have hfnorm : ‖f‖ ^ 2 = (wpInner μ μ).re := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) f).trans (congrArg Complex.re hff)
  have hgnorm : ‖g‖ ^ 2 = (wpInner ν ν).re := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) g).trans (congrArg Complex.re hgg)
  have hbound := pow_le_pow_left₀ (norm_nonneg (inner ℂ g f))
    (norm_inner_le_norm (𝕜 := ℂ) g f) 2
  rw [hgf, mul_pow, hfnorm, hgnorm] at hbound
  simpa only [mul_comm] using hbound

/-- Equality of real multiples of the weighted L2 vectors is exactly equality of
the harmonic representatives on the exterior disk (TT:2154, TT:3121–3128). -/
theorem wp_weighted_smul_eq_iff {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) (a : ℝ) :
    a • (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ)) =
        (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)) ↔
      EqOn (fun z => a • ν z) μ unitDiscExterior := by
  let f := (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))
  let g := (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))
  constructor
  · intro heq
    have hae : (fun z => a • ν z) =ᵐ[volume.restrict unitDiscExterior] μ := by
      filter_upwards [Lp.coeFn_smul a g, (wp_weighted_memLp hν).coeFn_toLp,
        (wp_weighted_memLp hμ).coeFn_toLp,
        ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hs hn hm hz
      change (a • g) z = a • g z at hs
      change g z = ν z * (Real.sqrt (rho z) : ℂ) at hn
      change f z = μ z * (Real.sqrt (rho z) : ℂ) at hm
      have hval := congrArg (fun q : Lp ℂ 2 (volume.restrict unitDiscExterior) => q z) heq
      change (a • g) z = f z at hval
      rw [hs, hn, hm] at hval
      have hs0 : (Real.sqrt (rho z) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (wp_rho_pos hz)).ne'
      apply mul_right_cancel₀ hs0
      simpa only [smul_mul_assoc] using hval
    exact Measure.eqOn_open_of_ae_eq hae wp_exterior_isOpen
      ((wp_harmonic_continuousOn hν).const_smul a) (wp_harmonic_continuousOn hμ)
  · intro heq
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul a g, (wp_weighted_memLp hν).coeFn_toLp,
      (wp_weighted_memLp hμ).coeFn_toLp,
      ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hs hn hm hz
    change (a • g) z = a • g z at hs
    change g z = ν z * (Real.sqrt (rho z) : ℂ) at hn
    change f z = μ z * (Real.sqrt (rho z) : ℂ) at hm
    change (a • g) z = f z
    rw [hs, hn, hm]
    simpa only [smul_mul_assoc] using
      congrArg (fun c : ℂ => c * (Real.sqrt (rho z) : ℂ)) (heq hz)

/-- The L2 tangent vector vanishes exactly when its harmonic representative vanishes
on the exterior disk (TT:2154). -/
theorem wp_weighted_eq_zero_iff {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)) = 0 ↔
      ∀ z ∈ unitDiscExterior, μ z = 0 := by
  constructor
  · intro heq
    have hp := (wp_weighted_smul_eq_iff hμ hμ 0).mp (by simp [heq])
    intro z hz
    simpa only [zero_smul] using (hp hz).symm
  · intro heq
    have hp := (wp_weighted_smul_eq_iff hμ hμ 0).mpr (by
      intro z hz
      simp [heq z hz])
    simpa only [zero_smul] using hp.symm

/-- The two intrinsic independence conditions for the real plane in (7.9) agree:
weighted L2 tangent vectors, or harmonic representatives restricted to the exterior
disk (TT:2154, TT:3121–3128). -/
theorem wp_weighted_linearIndependent_iff {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    LinearIndependent ℝ
      ![(wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ)),
        (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))] ↔
      LinearIndependent ℝ
        ![(fun z : unitDiscExterior => μ z), (fun z : unitDiscExterior => ν z)] := by
  let f := (wp_weighted_memLp hμ).toLp (fun z => μ z * (Real.sqrt (rho z) : ℂ))
  let g := (wp_weighted_memLp hν).toLp (fun z => ν z * (Real.sqrt (rho z) : ℂ))
  have hg : g = 0 ↔ (fun z : unitDiscExterior => ν z) = 0 := by
    rw [wp_weighted_eq_zero_iff hν]
    constructor
    · intro h
      funext z
      exact h z z.property
    · intro h z hz
      exact congrFun h ⟨z, hz⟩
  have ha (a : ℝ) : a • g = f ↔
      a • (fun z : unitDiscExterior => ν z) = (fun z : unitDiscExterior => μ z) := by
    rw [wp_weighted_smul_eq_iff hμ hν a]
    constructor
    · intro h
      funext z
      exact h z.property
    · intro h z hz
      exact congrFun h ⟨z, hz⟩
  rw [linearIndependent_fin2, linearIndependent_fin2]
  change (g ≠ 0 ∧ ∀ a : ℝ, a • g ≠ f) ↔
    ((fun z : unitDiscExterior => ν z) ≠ 0 ∧
      ∀ a : ℝ, a • (fun z : unitDiscExterior => ν z) ≠ (fun z : unitDiscExterior => μ z))
  exact and_congr (not_congr hg) (forall_congr' (fun a => not_congr (ha a)))

/-- **(4.3)** (TT:2163). The coefficients of the Weil–Petersson metric on the chart `V₀`:
`g_{μν̄}(κ) = ⟨∂/∂ε_μ|_κ, ∂/∂ε_ν|_κ⟩_WP = ∬_{𝔻*} P(R(μ, κ)) \overline{P(R(ν, κ))} ρ(z) d²z`, where `κ ∈ V₀` is
represented by the harmonic Beltrami differential `Λ(h₀(κ))`. -/
def gWP (μ ν : ℂ → ℂ) (κ : LinfStar) : ℂ :=
  ∫ z in unitDiscExterior, harmonicProj (Rnm (toLinf μ) κ) z * conj (harmonicProj (Rnm (toLinf ν) κ) z) * rho z

/-- `g_{μν̄}` as a function on the chart `V₀`, in Bers coordinates `φ = h₀(κ)` (`κ = Λ(φ)`). -/
def gWPChart (μ ν : ℂ → ℂ) (φ : AInf unitDisc) : ℂ := gWP μ ν (Lambda φ)

/-- Complex-coordinate formula for the density coefficient in the factorization
(TT:2787). -/
theorem wp_rho_complex (z : ℂ) : (rho z : ℂ) = 4 / (1 - z * conj z) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold rho
  push_cast
  rfl

/-- The reciprocal density is a polynomial in z and its conjugate (TT:2787). -/
theorem wp_rho_inv_complex (z : ℂ) : (rho z : ℂ)⁻¹ = (1 - z * conj z) ^ 2 / 4 := by
  rw [wp_rho_complex, inv_div]

/-- A uniform lower bound for the Bergman denominator in (7.8), TT:3053–3072. -/
theorem bKernel_denominator_lower_bound {w v : ℂ} (hw : ‖w‖ ≤ 1) :
    1 - ‖v‖ ≤ ‖1 - w * conj v‖ := by
  have hm : ‖w * conj v‖ ≤ ‖v‖ := by
    simpa only [norm_mul, norm_conj, one_mul] using
      mul_le_mul_of_nonneg_right hw (norm_nonneg v)
  calc
    _ ≤ 1 - ‖w * conj v‖ := sub_le_sub_left hm 1
    _ ≤ _ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (w * conj v)

/-- The Bergman denominator has no zero on the closed disk for a disk parameter, TT:3053. -/
theorem bKernel_denominator_ne_zero {w v : ℂ} (hw : ‖w‖ ≤ 1) (hv : ‖v‖ < 1) :
    1 - w * conj v ≠ 0 :=
  norm_pos_iff.mp ((sub_pos.mpr hv).trans_le (bKernel_denominator_lower_bound hw))

/-- Polar coordinates and the circle parametrization agree, for the computation in (7.8). (TT:3053–3082). -/
theorem bKernel_polar_circle (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  simp only [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_ofReal_mul_I]

/-- Angular integration over `(-π,π)` in terms of the circle average, TT:3072. -/
theorem bKernel_circle_integral (f : ℂ → ℂ) (r : ℝ) :
    (∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ))) =
      (2 * π) • Real.circleAverage f 0 r := by
  simp_rw [bKernel_polar_circle]
  have h := Real.circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-π)
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap 0 r θ)) (-π)] at h
  have hep : 2 * π + -π = π := by ring
  rw [zero_add, hep, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π),
    integral_Ioc_eq_integral_Ioo] at h
  rw [h, smul_smul, mul_inv_cancel₀ (ne_of_gt Real.two_pi_pos), one_smul]

/-- Disk polar integration under explicit absolute-integrability control, used in (7.8). (TT:3053–3082). -/
theorem bKernel_polar_integral (f : ℂ → ℂ)
    (hi : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π)) :
    (∫ w in unitDisc, f w) =
      ∫ r in Ioo (0 : ℝ) 1, r • ((2 * π) • Real.circleAverage f 0 r) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : S ⊆ polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  calc
    _ = ∫ w, unitDisc.indicator f w := (integral_indicator measurableSet_ball).symm
    _ = ∫ p in polarCoord.target, p.1 • unitDisc.indicator f (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target, S.indicator
        (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      have hmem : Complex.polarCoord.symm p ∈ unitDisc ↔ p.1 < 1 := by
        simp only [unitDisc, mem_ball_zero_iff, norm_polarCoord_symm, abs_of_pos hp0]
      dsimp only
      by_cases hp1 : p.1 < 1
      · rw [indicator_of_mem (hmem.mpr hp1), indicator_of_mem (show p ∈ S from ⟨⟨hp0, hp1⟩, hp.2⟩)]
      · rw [indicator_of_notMem (mt hmem.mp hp1), smul_zero,
          indicator_of_notMem (show p ∉ S from fun h => hp1 h.1.2)]
    _ = ∫ p in S, p.1 • f (Complex.polarCoord.symm p) := by
      rw [setIntegral_indicator hS, inter_eq_right.mpr hsub]
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (-π) π,
        r • f (Complex.polarCoord.symm (r, θ)) := by
      rw [Measure.volume_eq_prod] at hi ⊢
      exact setIntegral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      rw [integral_smul, bKernel_circle_integral]

/-- Polarized disk identity for the Blaschke change of variables in (7.8), TT:3058. -/
theorem bKernel_blaschke_polarization {a w v : ℂ}
    (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) (hv : ‖v‖ < 1) :
    1 - blaschke a w * conj (blaschke a v) =
      (1 - a * conj a) * (1 - w * conj v) /
        ((1 - conj a * w) * (1 - a * conj v)) := by
  have hwd := blaschke_den_ne_zero ha hw
  have hwd' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hwd
  have hvd := blaschke_den_ne_zero ha hv
  have hvdc : 1 - a * conj v ≠ 0 := by
    intro h
    apply hvd
    simpa using congrArg (starRingEnd ℂ) h
  simp only [blaschke, map_div₀, map_sub, map_one, map_mul, conj_conj]
  field_simp [hwd, hwd', hvdc]
  <;> ring

/-- Polar integrability for a bounded continuous disk function, used in weighted reproduction. (TT:1351–1390, TT:2844–2850). -/
theorem wp_polar_integrable_of_bounded {f : ℂ → ℂ} (hf : ContinuousOn f unitDisc)
    {C : ℝ} (hb : ∀ z ∈ unitDisc, ‖f z‖ ≤ C) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap : MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p) S unitDisc := by
    intro p hps
    apply mem_ball_zero_iff.mpr
    rw [norm_polarCoord_symm, abs_of_pos hps.1.1]
    exact hps.1.2
  have hc := continuous_fst.continuousOn.smul (hf.comp hp.continuousOn hmap)
  have hfin : volume S < ∞ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  apply IntegrableOn.of_bound hfin
    (hc.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)) C
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hps
  change ‖p.1 • f (Complex.polarCoord.symm p)‖ ≤ C
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hps.1.1]
  calc
    _ ≤ ‖f (Complex.polarCoord.symm p)‖ := mul_le_of_le_one_left (norm_nonneg _) hps.1.2.le
    _ ≤ C := hb _ (hmap hps)

/-- The scalar polar mass of the inverse hyperbolic density is `π/12`, TT:1374–1378. -/
theorem wp_bergman_radius_mass :
    (∫ r in Ioo (0 : ℝ) 1, 2 * π * r * ((1 - r ^ 2) ^ 2 / 4)) = π / 12 := by
  have h := bergman_monomial_area 0
  norm_num only [pow_zero, norm_one, one_pow, one_mul, Nat.cast_zero, zero_add] at h
  have hr := integral_unitDisc_radial (fun r : ℝ => (1 - r ^ 2) ^ 2 / 4)
  have hleft : (∫ z in unitDisc, (rho z)⁻¹) =
      ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 2 / 4 := by simp only [rho, inv_div]
  rw [hleft, hr] at h
  rw [← integral_const_mul] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with r
    ring

/-- Weighted Bergman reproduction at the disk center for bounded weighted data, TT:1374–1390. -/
theorem wp_bergman_reproduce_center {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {C : ℝ} (hb : ∀ z ∈ unitDisc, ‖f z * ((rho z)⁻¹ : ℝ)‖ ≤ C) :
    (∫ z in unitDisc, f z * ((rho z)⁻¹ : ℝ)) = (π / 12 : ℝ) • f 0 := by
  let F : ℂ → ℂ := fun z => f z * ((rho z)⁻¹ : ℝ)
  have hw : Continuous (fun z : ℂ => ((rho z)⁻¹ : ℝ)) := by
    simp only [rho, inv_div]
    fun_prop
  have hF : ContinuousOn F unitDisc := hf.continuousOn.mul
    (Complex.continuous_ofReal.comp_continuousOn hw.continuousOn)
  have havg (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      Real.circleAverage F 0 r = ((1 - r ^ 2) ^ 2 / 4 : ℝ) • f 0 := by
    have hsub : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
      intro z hz
      apply mem_ball_zero_iff.mpr
      exact (mem_closedBall_zero_iff.mp hz).trans_lt (by simpa only [abs_of_pos hr.1] using hr.2)
    have hmean := (DiffContOnCl.mk_ball (hf.mono (ball_subset_closedBall.trans hsub))
      (hf.continuousOn.mono hsub)).circleAverage
    calc
      _ = Real.circleAverage (fun z => ((1 - r ^ 2) ^ 2 / 4 : ℝ) • f z) 0 r := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hn : ‖z‖ = |r| := by simpa only [mem_sphere, dist_zero_right] using hz
        dsimp only [F]
        simp only [rho, inv_div, hn, sq_abs, Complex.real_smul]
        ring
      _ = _ := by rw [Real.circleAverage_fun_smul, hmean]
  change (∫ z in unitDisc, F z) = _
  rw [bKernel_polar_integral F (wp_polar_integrable_of_bounded hF hb)]
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, (2 * π * r * ((1 - r ^ 2) ^ 2 / 4)) • f 0 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [havg r hr, smul_smul, smul_smul]
      congr 1
      ring
    _ = _ := by rw [integral_smul_const, wp_bergman_radius_mass]

/-- The derivative of a Blaschke automorphism is holomorphic on the disk. (TT:1351–1390, TT:2844–2850). -/
theorem wp_bergman_blaschke_deriv_differentiable {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (deriv (blaschke a)) unitDisc := by
  have h : DifferentiableOn ℂ (fun w : ℂ => (1 - a * conj a) / (1 - conj a * w) ^ 2) unitDisc :=
    (differentiableOn_const _).div
      (((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).pow 2)
      (fun w hw => pow_ne_zero 2 (blaschke_den_ne_zero ha (mem_ball_zero_iff.mp hw)))
  exact h.congr (fun w hw => (hasDerivAt_blaschke ha (mem_ball_zero_iff.mp hw)).deriv)

/-- The weighted pointwise norm of a quadratic differential is invariant under disk pullback. (TT:1351–1390, TT:2844–2850). -/
theorem wp_bergman_pullback_norm (f : ℂ → ℂ) {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖(f (blaschke a w) * deriv (blaschke a) w ^ 2) * ((rho w)⁻¹ : ℝ)‖ =
      ‖f (blaschke a w) * ((rho (blaschke a w))⁻¹ : ℝ)‖ := by
  have hrw : 0 < rho w := rho_pos_of_norm_ne_one hw.ne
  have hrb : 0 < rho (blaschke a w) := rho_pos_of_norm_ne_one (blaschke_mem_unitDisc ha hw).ne
  have hd : deriv (blaschke a) w ≠ 0 := by
    rw [(hasDerivAt_blaschke ha hw).deriv]
    exact div_ne_zero (one_sub_mul_conj_ne_zero ha) (pow_ne_zero 2 (blaschke_den_ne_zero ha hw))
  have hdn : ‖deriv (blaschke a) w‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hrw), abs_of_pos (inv_pos.mpr hrb)]
  rw [← rho_blaschke_jacobian ha hw]
  field_simp

/-- The inverse Blaschke denominator identity used in weighted reproduction. (TT:1351–1390, TT:2844–2850). -/
theorem wp_bergman_blaschke_inverse_factor {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 + conj a * blaschke a w = (1 - a * conj a) / (1 - conj a * w) := by
  have hd := blaschke_den_ne_zero ha hw
  have hd' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hd
  unfold blaschke
  field_simp [hd, hd']
  <;> ring

/-- The derivative of the inverse disk automorphism, in the original coordinate. (TT:1351–1390, TT:2844–2850). -/
theorem wp_bergman_blaschke_inverse_deriv {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    deriv (blaschke (-a)) (blaschke a w) = (1 - conj a * w) ^ 2 / (1 - a * conj a) := by
  have hna : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hd := blaschke_den_ne_zero ha hw
  have hq := one_sub_mul_conj_ne_zero ha
  rw [(hasDerivAt_blaschke hna (blaschke_mem_unitDisc ha hw)).deriv]
  simp only [map_neg, neg_mul, mul_neg, neg_neg, sub_neg_eq_add]
  rw [wp_bergman_blaschke_inverse_factor ha hw]
  field_simp

set_option maxHeartbeats 800000 in
/-- The full change-of-variables integrand for weighted Bergman reproduction. (TT:1351–1390, TT:2844–2850). -/
theorem wp_bergman_blaschke_integrand (f : ℂ → ℂ) {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    (‖deriv (blaschke a) w‖ ^ 2 : ℝ) •
      ((f (blaschke (-a) (blaschke a w)) * deriv (blaschke (-a)) (blaschke a w) ^ 2) *
        ((rho (blaschke a w))⁻¹ : ℝ)) =
      (1 - a * conj a) ^ 2 * (f w * ((rho w)⁻¹ : ℝ) / (1 - a * conj w) ^ 4) := by
  have hd := blaschke_den_ne_zero ha hw
  have hd' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hd
  have hdc := bKernel_denominator_ne_zero ha.le hw
  have hq := one_sub_mul_conj_ne_zero ha
  have hq' : 1 - conj a * a ≠ 0 := by simpa only [mul_comm] using hq
  have hJ : ((‖deriv (blaschke a) w‖ ^ 2 : ℝ) : ℂ) =
      deriv (blaschke a) w * conj (deriv (blaschke a) w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Complex.real_smul, hJ, (hasDerivAt_blaschke ha hw).deriv,
    wp_bergman_blaschke_inverse_deriv ha hw, blaschke_neg_blaschke ha hw]
  simp only [Complex.ofReal_inv, wp_rho_inv_complex]
  rw [bKernel_blaschke_polarization ha hw hw]
  simp only [map_div₀, map_pow, map_sub, map_one, map_mul, conj_conj]
  field_simp [hd, hd', hdc, hq, hq']
  <;> ring

/-- Weighted Bergman reproduction at an arbitrary disk point, TT:1374–1390. -/
theorem wp_bergman_reproduce {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {C : ℝ} (hb : ∀ w ∈ unitDisc, ‖f w * ((rho w)⁻¹ : ℝ)‖ ≤ C)
    {a : ℂ} (ha : a ∈ unitDisc) :
    (∫ w in unitDisc, f w * ((rho w)⁻¹ : ℝ) / (1 - a * conj w) ^ 4) = (π / 12 : ℝ) • f a := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hna : ‖-a‖ < 1 := by simpa only [norm_neg] using ha1
  let g : ℂ → ℂ := fun w => f (blaschke (-a) w) * deriv (blaschke (-a)) w ^ 2
  have hg : DifferentiableOn ℂ g unitDisc :=
    (hf.comp (differentiableOn_blaschke hna) (fun w hw =>
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hna (mem_ball_zero_iff.mp hw)))).mul
      ((wp_bergman_blaschke_deriv_differentiable hna).pow 2)
  have hgb : ∀ w ∈ unitDisc, ‖g w * ((rho w)⁻¹ : ℝ)‖ ≤ C := by
    intro w hw
    dsimp only [g]
    rw [wp_bergman_pullback_norm f hna (mem_ball_zero_iff.mp hw)]
    exact hb _ (mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hna (mem_ball_zero_iff.mp hw)))
  have hcenter := wp_bergman_reproduce_center hg hgb
  have hzero : g 0 = f a * (1 - a * conj a) ^ 2 := by
    dsimp only [g]
    rw [(hasDerivAt_blaschke hna (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
    simp only [blaschke, map_neg, mul_zero, sub_zero, div_one, zero_sub, neg_neg,
      neg_mul, mul_neg, one_pow]
  have hconf := isConformalOnto_blaschke ha1
  have ht := ahP_integral_image (U := unitDisc) (show IsOpen unitDisc from isOpen_ball)
    hconf.1 hconf.2.1 (fun w : ℂ => g w * ((rho w)⁻¹ : ℝ))
  rw [hconf.2.2] at ht
  have htransport : (∫ w in unitDisc, g w * ((rho w)⁻¹ : ℝ)) =
      (1 - a * conj a) ^ 2 * ∫ w in unitDisc, f w * ((rho w)⁻¹ : ℝ) / (1 - a * conj w) ^ 4 := by
    rw [ht, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    exact wp_bergman_blaschke_integrand f ha1 (mem_ball_zero_iff.mp hw)
  apply mul_left_cancel₀ (pow_ne_zero 2 (one_sub_mul_conj_ne_zero ha1))
  calc
    _ = ∫ w in unitDisc, g w * ((rho w)⁻¹ : ℝ) := htransport.symm
    _ = (π / 12 : ℝ) • g 0 := hcenter
    _ = _ := by rw [hzero]; simp only [Complex.real_smul]; ring

/-- The inverse-density-weighted value of an A2 function is uniformly bounded, TT:1366–1396. -/
theorem wp_bergman_A2_weighted_bound {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖f z * ((rho z)⁻¹ : ℝ)‖ ≤ (Real.sqrt (12 / π) / 4) * (normA2 unitDisc f).toReal := by
  have hb := lemma_2_1_disc hf z hz
  have hp : (1 - ‖z‖ ^ 2) ^ 2 * ‖f z‖ ≤
      Real.sqrt (12 / π) * (normA2 unitDisc f).toReal := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_toReal hf.2.ne] using hb
  have hr : 0 ≤ (rho z)⁻¹ := inv_nonneg.mpr (wp_rho_nonneg z)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp only [rho, inv_div]
  nlinarith

/-- The weighted Bergman formula for every A2 function, used for completeness in TT:2844–2850. -/
theorem wp_bergman_reproduce_A2 {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {a : ℂ} (ha : a ∈ unitDisc) :
    (∫ w in unitDisc, f w * ((rho w)⁻¹ : ℝ) / (1 - a * conj w) ^ 4) = (π / 12 : ℝ) • f a :=
  wp_bergman_reproduce hf.1 (fun _ hw => wp_bergman_A2_weighted_bound hf hw) ha

/-- Quadratic-differential pullback by inversion is involutive off zero. (TT:1351–1410, TT:2844–2850). -/
theorem wp_quadratic_inversion_involutive (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    (f (z⁻¹)⁻¹ / (z⁻¹) ^ 4) / z ^ 4 = f z := by
  simp only [inv_inv, inv_pow, div_inv_eq_mul]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 4 hz)

/-- Harmonic contraction of a disk quadratic differential after inversion, TT:1401, TT:2844. -/
def wp_harmonicOfDisk (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (rho w : ℂ)⁻¹ * conj (f w⁻¹ / w ^ 4)

/-- Every harmonic exterior L2 representative comes from a disk A2 function, with equal norm. (TT:1351–1410, TT:2844–2850). -/
theorem wp_harmonic_disk_representative {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ f : ℂ → ℂ, f ∈ A2fun unitDisc ∧ EqOn μ (wp_harmonicOfDisk f) unitDiscExterior ∧
      normA2 unitDisc f = normL2 unitDiscExterior μ := by
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have he := normA2_eq_normL2_of_harmonic wp_exterior_isOpen.measurableSet
    (fun w hw => ne_of_gt hw) hrep
  have hφA : φ ∈ A2fun unitDiscExterior := ⟨hφ, by rw [he]; exact hfinite⟩
  obtain ⟨f, hf, hfe, hnorm⟩ := exists_inverted_A2 hφA
  refine ⟨f, hf, ?_, hnorm.trans he⟩
  intro w hw
  have hw0 := resolvent_exterior_ne_zero hw
  have hwi := resolvent_inv_exterior_conformal.mapsTo hw
  unfold wp_harmonicOfDisk
  rw [hfe hwi, wp_quadratic_inversion_involutive φ hw0]
  exact hrep w hw

/-- The pointwise harmonic L2 bound needed in the curvature-energy argument, TT:1410, TT:3128. -/
theorem wp_harmonic_pointwise_bound {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ‖μ z‖ ≤ (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal := by
  obtain ⟨φ, hφ, hrep, hfinite⟩ := hμ
  have hnorm := normA2_eq_normL2_of_harmonic wp_exterior_isOpen.measurableSet
    (fun w hw => ne_of_gt hw) hrep
  have hA2 : φ ∈ A2fun unitDiscExterior := ⟨hφ, by rw [hnorm]; exact hfinite⟩
  have hb := lemma_2_1 (Or.inr rfl) hA2 z hz
  rw [hnorm] at hb
  have hpoint : (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ ≤
      Real.sqrt (12 / π) * (normL2 unitDiscExterior μ).toReal := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
    simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_toReal hfinite.ne] using hb
  have he : ‖μ z‖ = ((1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖) / 4 := by
    rw [hrep z hz]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (wp_rho_pos hz), norm_conj]
    simp only [rho, inv_div]
    ring
  rw [he]
  calc
    _ ≤ (Real.sqrt (12 / π) * (normL2 unitDiscExterior μ).toReal) / 4 :=
      div_le_div_of_nonneg_right hpoint (by norm_num)
    _ = _ := by ring

/-- The Model A normalization fixes the identity solution at zero Beltrami coefficient (TT:346, TT:2163). -/
theorem wp_wA_zero : wA 0 = id := by
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      simp [mobiusFn]
  have hnorm : IsNormalizedA 0 id := by
    refine ⟨id, ⟨1, 0, 0, 1, by norm_num, hid.symm⟩, _root_.id,
      ⟨⟨1, isKQC_one_of_conformal isOpen_univ (isConformalOnto_id univ)⟩, image_id _, rfl, rfl, ?_⟩,
      fun z => rfl, rfl, rfl, rfl, rfl⟩
    filter_upwards [extA_ae_norm_le (0 : LinfStar)] with z hz
    have he : extA 0 z = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [norm_zero] using hz) (norm_nonneg _))
    rw [td_complexDilatation_id, he]
  have hS : wAS 0 = id := (wA_unique (by simp [LinfStarBall]) hnorm).symm
  funext z
  simp [wA, hS, finPart]

/-- The harmonic chart inverse takes zero to zero (TT:501, TT:2163). -/
theorem wp_Lambda_zero : Lambda 0 = 0 := by
  simpa only [zero_smul] using Lambda_smul (0 : ℂ) (0 : AInf unitDisc)

/-- Passing an existing L-infinity element through the raw-function wrapper changes nothing (TT:2163). -/
theorem wp_toLinf_coe (μ : LinfStar) : toLinf (fun z => μ z) = μ := by
  have hm : MemLp (fun z => μ z) ∞ (volume.restrict unitDiscExterior) := Lp.memLp μ
  unfold toLinf
  rw [dif_pos hm]
  apply Lp.ext
  exact hm.coeFn_toLp

/-- The L-infinity wrapper depends only on the almost-everywhere class of its input (TT:2163). -/
theorem wp_toLinf_congr {f g : ℂ → ℂ} (he : f =ᵐ[volume.restrict unitDiscExterior] g) :
    toLinf f = toLinf g := by
  by_cases hf : MemLp f ∞ (volume.restrict unitDiscExterior)
  · have hg : MemLp g ∞ (volume.restrict unitDiscExterior) := (memLp_congr_ae he).mp hf
    simp only [toLinf, dif_pos hf, dif_pos hg]
    apply Lp.ext
    exact hf.coeFn_toLp.trans (he.trans hg.coeFn_toLp.symm)
  · have hg : ¬MemLp g ∞ (volume.restrict unitDiscExterior) := fun h => hf ((memLp_congr_ae he).mpr h)
    simp only [toLinf, dif_neg hf, dif_neg hg]

/-- Right-translation differentiation reduces to the identity at zero (TT:539, TT:2163). -/
theorem wp_Rnm_zero (ν : LinfStar) : Rnm ν 0 = ν := by
  have hd (z : ℂ) : dz (id : ℂ → ℂ) z = 1 := by simp [dz, fderiv_id]
  have hinv (z : ℂ) : Function.invFun (id : ℂ → ℂ) z = z :=
    Function.leftInverse_invFun Function.injective_id z
  unfold Rnm
  rw [wp_wA_zero]
  calc
    _ = toLinf (fun z => ν z) := by
      apply wp_toLinf_congr
      filter_upwards [Lp.coeFn_zero ℂ ∞ (volume.restrict unitDiscExterior)] with z hz
      simp only [hinv, id_eq, hd, map_one, div_self one_ne_zero,
        mul_one, hz, Pi.zero_apply, norm_zero, Complex.ofReal_zero,
        zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]
    _ = ν := wp_toLinf_coe ν

/-- Inversion turns the exterior harmonic projector into the disk Bergman kernel (TT:551, TT:2163). -/
theorem wp_projection_inversion_integrand (f : ℂ → ℂ) {z u : ℂ}
    (hz : z ∈ unitDiscExterior) (hu : u ∈ unitDisc \ {0}) :
    (‖deriv (fun w : ℂ => w⁻¹) u‖ ^ 2 : ℝ) •
      (wp_harmonicOfDisk f u⁻¹ / (1 - u⁻¹ * conj z) ^ 4) =
      conj (f u) * ((rho u)⁻¹ : ℝ) / (u - conj z) ^ 4 := by
  have hu0 : u ≠ 0 := hu.2
  have huc : conj u ≠ 0 := by
    intro h
    apply hu0
    simpa only [conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hdiff : u - conj z ≠ 0 := by
    intro he
    have hnorm := mem_ball_zero_iff.mp hu.1
    rw [sub_eq_zero.mp he, norm_conj] at hnorm
    exact (not_lt_of_ge hz.le) hnorm
  have hden : 1 - u⁻¹ * conj z ≠ 0 := by
    intro he
    apply hdiff
    calc
      _ = u * (1 - u⁻¹ * conj z) := by field_simp
      _ = 0 := by rw [he, mul_zero]
  have hJ : ((‖deriv (fun w : ℂ => w⁻¹) u‖ ^ 2 : ℝ) : ℂ) = 1 / (u * conj u) ^ 2 := by
    rw [(hasDerivAt_inv hu0).deriv, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [norm_neg, norm_inv, norm_pow, Complex.ofReal_pow, Complex.ofReal_inv,
      one_div, inv_pow]
  rw [Complex.real_smul, hJ]
  simp only [wp_harmonicOfDisk, inv_inv, Complex.ofReal_inv, wp_rho_inv_complex,
    map_inv₀, map_div₀, map_pow]
  field_simp [hu0, huc, hdiff, hden]
  <;> ring

/-- The exterior projection integral is the inverted disk weighted integral (TT:551, TT:2163). -/
theorem wp_projection_inversion_integral (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, wp_harmonicOfDisk f w / (1 - w * conj z) ^ 4) =
      ∫ u in unitDisc, conj (f u) * ((rho u)⁻¹ : ℝ) / (u - conj z) ^ 4 := by
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hi := ahP_integral_image hopen hc.1 hc.2.1
    (fun w : ℂ => wp_harmonicOfDisk f w / (1 - w * conj z) ^ 4)
  rw [hc.2.2] at hi
  rw [hi]
  calc
    _ = ∫ u in unitDisc \ {0}, conj (f u) * ((rho u)⁻¹ : ℝ) / (u - conj z) ^ 4 := by
      apply setIntegral_congr_fun hopen.measurableSet
      intro u hu
      exact wp_projection_inversion_integrand f hz hu
    _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton 0))

/-- The explicit exterior projector fixes harmonic contractions of disk A2 functions (TT:551). -/
theorem wp_projection_of_disk_A2 {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (3 : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) / π *
      (∫ w in unitDiscExterior, wp_harmonicOfDisk f w / (1 - w * conj z) ^ 4) =
      wp_harmonicOfDisk f z := by
  have hz0 := resolvent_exterior_ne_zero hz
  have hzc : conj z ≠ 0 := by
    intro h
    apply hz0
    simpa only [conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have ha := (resolvent_inv_exterior_conformal.mapsTo hz).1
  rw [wp_projection_inversion_integral f hz]
  have he : (∫ u in unitDisc, conj (f u) * ((rho u)⁻¹ : ℝ) / (u - conj z) ^ 4) =
      (1 / conj z ^ 4) * conj ((π / 12 : ℝ) • f z⁻¹) := by
    calc
      _ = (1 / conj z ^ 4) * conj (∫ u in unitDisc,
          f u * ((rho u)⁻¹ : ℝ) / (1 - z⁻¹ * conj u) ^ 4) := by
        rw [← integral_conj, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_ball
        intro u hu
        have hd := bKernel_denominator_ne_zero (mem_ball_zero_iff.mp hu).le
          (mem_ball_zero_iff.mp ha)
        dsimp only
        simp only [map_div₀, map_pow, map_sub, map_one, map_mul, conj_ofReal, map_inv₀, conj_conj]
        field_simp [hzc]
        <;> ring
      _ = _ := by rw [wp_bergman_reproduce_A2 hf ha]
  rw [he]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [wp_harmonicOfDisk, Complex.real_smul, map_mul, conj_ofReal, map_div₀, map_pow,
    rho, Complex.ofReal_div, inv_div, Complex.ofReal_ofNat, map_ofNat]
  field_simp
  <;> ring

/-- Pointwise reproduction of every harmonic exterior L2 representative (TT:551, TT:2163). -/
theorem wp_harmonic_projection_raw {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (3 : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) / π *
      (∫ w in unitDiscExterior, μ w / (1 - w * conj z) ^ 4) = μ z := by
  obtain ⟨f, hf, he, _⟩ := wp_harmonic_disk_representative hμ
  calc
    _ = (3 : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) / π *
        (∫ w in unitDiscExterior, wp_harmonicOfDisk f w / (1 - w * conj z) ^ 4) := by
      congr 1
      apply setIntegral_congr_fun wp_exterior_isOpen.measurableSet
      intro w hw
      dsimp only
      rw [he hw]
    _ = _ := (wp_projection_of_disk_A2 hf hz).trans (he hz).symm

/-- Harmonic exterior L2 functions have genuine bounded-function representatives (TT:1410, TT:2163). -/
theorem wp_harmonic_memLp_top {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    MemLp μ ∞ (volume.restrict unitDiscExterior) := by
  apply memLp_top_of_bound ((wp_harmonic_continuousOn hμ).aestronglyMeasurable
    wp_exterior_isOpen.measurableSet) ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior μ).toReal)
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
  exact wp_harmonic_pointwise_bound hμ hz

/-- The L-infinity wrapper represents the original harmonic L2 function almost everywhere (TT:2163). -/
theorem wp_harmonic_toLinf_ae {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (toLinf μ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] μ := by
  have hm := wp_harmonic_memLp_top hμ
  simp only [toLinf, dif_pos hm]
  exact hm.coeFn_toLp

/-- The actual L-infinity harmonic projector fixes harmonic L2 representatives (TT:551, TT:2163). -/
theorem wp_harmonicProj_fix {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    harmonicProj (toLinf μ) = toLinf μ := by
  unfold harmonicProj
  apply wp_toLinf_congr
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
  have hi : (∫ w in unitDiscExterior, (toLinf μ) w / (1 - w * conj z) ^ 4) =
      ∫ w in unitDiscExterior, μ w / (1 - w * conj z) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [wp_harmonic_toLinf_ae hμ] with w hw
    rw [hw]
  rw [hi]
  simpa only [Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one] using
    wp_harmonic_projection_raw hμ hz

/-- (TT:2163) At the origin, `g_{μν̄}(0) = ⟨μ, ν⟩_WP` for `μ, ν ∈ H^{-1,1}(𝔻*)`. -/
theorem gWP_origin {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    gWPChart μ ν 0 = wpInner μ ν := by
  unfold gWPChart
  rw [wp_Lambda_zero]
  unfold gWP
  rw [wp_Rnm_zero, wp_Rnm_zero, wp_harmonicProj_fix hμ, wp_harmonicProj_fix hν]
  unfold wpInner
  apply integral_congr_ae
  filter_upwards [wp_harmonic_toLinf_ae hμ, wp_harmonic_toLinf_ae hν] with z hm hn
  rw [hm, hn]

-- `lemma_4_2` moved to `Ch1/L42.lean` (2026-10-28).

-- `remark_4_3` moved to `TakhtajanTeo.Ch2.R43Potential` (2026-10-29, Program G).

/-- The diagonal WP integral is a real squared-norm integral for every representative (TT:2206–2216). -/
theorem wpInner_self_re_integral (μ : ℂ → ℂ) :
    (wpInner μ μ).re = ∫ z in unitDiscExterior, ‖μ z‖ ^ 2 * rho z := by
  have he : wpInner μ μ = ((∫ z in unitDiscExterior, ‖μ z‖ ^ 2 * rho z : ℝ) : ℂ) := by
    unfold wpInner
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    exact integral_ofReal
  simpa only [Complex.ofReal_re] using congrArg Complex.re he

/-- Lambda agrees almost everywhere with the reflected harmonic disk formula (TT:501, TT:2206–2216). -/
theorem wp_Lambda_harmonicDisk_ae (φ : AInf unitDisc) :
    (Lambda φ : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      (fun w => -2 * wp_harmonicOfDisk (fun v => conj (AInf.toFun φ (conj v))) w) := by
  filter_upwards [Lambda_coe_ae φ] with w hw
  rw [hw]
  dsimp only [wp_harmonicOfDisk, refl]
  simp only [map_inv₀, conj_conj, map_div₀, map_pow]
  simp only [rho, Complex.ofReal_div, Complex.ofReal_ofNat, inv_div]
  push_cast
  ring

/-- Reflection preserves the weighted area integral on the disk (TT:2206–2216). -/
theorem wp_conj_weighted_area (f : ℂ → ℂ) :
    (∫ z in unitDisc, ‖f (conj z)‖ ^ 2 * (rho z)⁻¹) =
      ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
  let F : ℂ → ℝ := fun z => ‖f z‖ ^ 2 * (rho z)⁻¹
  have h := Complex.conjLIE.measurePreserving.integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding (unitDisc.indicator F)
  have he : (fun z => unitDisc.indicator F (Complex.conjLIE z)) =
      unitDisc.indicator (fun z => ‖f (conj z)‖ ^ 2 * (rho z)⁻¹) := by
    funext z
    have hc : conj z ∈ unitDisc ↔ z ∈ unitDisc := by simp [unitDisc]
    by_cases hz : z ∈ unitDisc <;> simp [Complex.conjLIE_apply, hc, hz, F, rho]
  rw [he, integral_indicator (s := unitDisc) measurableSet_ball,
    integral_indicator (s := unitDisc) measurableSet_ball] at h
  exact h

/-- The diagonal Lambda WP pairing is four times the disk quadratic area (TT:2206–2216). -/
theorem wp_Lambda_wpInner_area (φ : AInf unitDisc) :
    (wpInner (Lambda φ) (Lambda φ)).re =
      4 * ∫ z in unitDisc, ‖AInf.toFun φ z‖ ^ 2 * (rho z)⁻¹ := by
  let g : ℂ → ℂ := fun v => conj (AInf.toFun φ (conj v))
  have harea : (∫ w in unitDiscExterior, ‖g w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) =
      ∫ z in unitDisc, ‖g z‖ ^ 2 * (rho z)⁻¹ := by
    rw [← inverted_quadratic_weighted_integral]
    calc
      _ = ∫ z in unitDisc \ {0}, ‖g z‖ ^ 2 * (rho z)⁻¹ := by
        apply setIntegral_congr_fun (measurableSet_ball.diff (measurableSet_singleton 0))
        intro z hz
        dsimp only
        rw [wp_quadratic_inversion_involutive g hz.2]
      _ = _ := setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ)))
  rw [wpInner_self_re_integral]
  calc
    _ = ∫ w in unitDiscExterior, 4 * (‖g w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹) := by
      apply integral_congr_ae
      filter_upwards [wp_Lambda_harmonicDisk_ae φ,
        ae_restrict_mem wp_exterior_isOpen.measurableSet] with w hw hwD
      rw [hw]
      change ‖-2 * ((rho w : ℂ)⁻¹ * conj (g w⁻¹ / w ^ 4))‖ ^ 2 * rho w = _
      simp only [norm_mul, norm_neg, norm_ofNat, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (wp_rho_pos hwD), norm_conj, mul_pow]
      field_simp [(wp_rho_pos hwD).ne']
      <;> ring
    _ = 4 * ∫ w in unitDiscExterior, ‖g w⁻¹ / w ^ 4‖ ^ 2 * (rho w)⁻¹ := integral_const_mul _ _
    _ = 4 * ∫ z in unitDisc, ‖AInf.toFun φ z‖ ^ 2 * (rho z)⁻¹ := by
      rw [harea]
      simp only [g, norm_conj]
      rw [wp_conj_weighted_area]

/-- **Remark 4.4** (TT:2206–2216), [NV90]. On `Möb(S¹)\Diff₊(S¹)` the Weil–Petersson metric agrees, up to a constant,
with Kirillov's metric `‖v‖² = Σ_{n ≥ 2} (n³ - n)|c_n|²`.
- The tangent vector `u = Σ_{n ∉ {0, ±1}} c_n e^{inθ} d/dθ` is smooth.
- It corresponds (TS2) to `φ = d³u₊/dz³ ∈ A∞(𝔻)`, hence to the harmonic Beltrami differential `Λ(φ)`.
- Stated: there is a constant `C > 0` with `⟨Λ(φ), Λ(φ)⟩_WP = C Σ_{n ≥ 2} (n³ - n)|c_n|²` for all such `u`. -/
theorem remark_4_4 :
    ∃ C > 0, ∀ u : ℝ → ℝ, u ∈ tangentQS → ContDiff ℝ (⊤ : ℕ∞) u →
      (∀ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) → fourierCoeff (fun θ => (u θ : ℂ)) n = 0) →
      ∀ φ : AInf unitDisc, (∀ z ∈ unitDisc, AInf.toFun φ z = iteratedDeriv 3 (uPlus u) z) →
        (wpInner (Lambda φ) (Lambda φ)).re =
          C * ∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ 3 - (n + 2 : ℕ)) * ‖fourierCoeff (fun θ => (u θ : ℂ)) (n + 2)‖ ^ 2 := by
  refine ⟨2 * π, Real.two_pi_pos, ?_⟩
  intro u hu hsmooth _hzero φ hφ
  let f : ℝ → ℂ := fun θ => (u θ : ℂ)
  let a : ℕ → ℂ := fun n => I * fourierCoeff f (n + 1)
  let b : ℕ → ℂ := fun n => a (n + 1) * ((n + 1 : ℂ) * (n + 2) * (n + 3))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa only [f, Function.comp_def, Complex.ofRealCLM_apply] using!
      (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp hsmooth
  have hp : Function.Periodic f (2 * π) := by
    intro θ
    dsimp only [f]
    rw [hu.1.2.1 θ]
  have ha : Summable (fun n => ((n + 2 : ℕ) : ℝ) ^ 3 * ‖a n‖) := by
    simpa only [a, norm_mul, Complex.norm_I, one_mul] using
      wp_smooth_fourier_shifted_cubic_summable hf hp
  have hb : Summable (fun n => ‖b n‖) := wp_shiftedSeries_third_coeff_summable ha
  have hU : uPlus u = (fun z => ∑' n, a n * z ^ (n + 2)) := by
    funext z
    simp only [uPlus, a, f, mul_assoc, tsum_mul_left]
  have hseries (z : ℂ) (hz : z ∈ unitDisc) :
      AInf.toFun φ z = ∑' n, b n * z ^ n := by
    rw [hφ z hz, hU]
    simpa only [b] using wp_shiftedSeries_third ha hz
  have hint : (∫ z in unitDisc, ‖AInf.toFun φ z‖ ^ 2 * (rho z)⁻¹) =
      ∫ z in unitDisc, ‖∑' n, b n * z ^ n‖ ^ 2 * (rho z)⁻¹ := by
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro z hz
    dsimp only
    rw [hseries z hz]
  have hcoeff (n : ℕ) :
      ‖b n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) =
        (((n + 2 : ℕ) : ℝ) ^ 3 - (n + 2 : ℕ)) * ‖fourierCoeff f (n + 2)‖ ^ 2 := by
    have hprod : ((n + 1 : ℂ) * (n + 2) * (n + 3)) =
        ((((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hpos : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by positivity
    simp only [b, a, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℤ) + 1 = 2 by norm_num]
    rw [hprod, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
    field_simp [hpos.ne']
    push_cast
    ring
  rw [wp_Lambda_wpInner_area, hint, wp_scalarSeries_weighted_area hb]
  simp_rw [hcoeff]
  dsimp only [f]
  ring

end TakhtajanTeo
