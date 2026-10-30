import TakhtajanTeo.Ch2.S5_PeriodMapping
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.Eq19Completed
import TakhtajanTeo.Ch1.CircleQuasisymmetry
import TakhtajanTeo.Ch1.FiberCircleOrientation
import TakhtajanTeo.Ch2.S1_Part5

/-!
# Boundary Fourier coefficients of a function with a Laurent expansion on `𝔻*`

If `F` is continuous on `{|z| ≥ 1}` and `F(z) = z^N + Σ_{m ≥ 0} c_m z^{-(m+1)}` on `|z| > 1`, then the Fourier
coefficients of `θ ↦ F(e^{iθ})` are `δ_{kN}` for `k ≥ 0` and `c_{-k-1}` for `k < 0`.
This is the boundary step of Remark 5.7 (clauses 1–2): `w_n = P_{n+1}(𝗀)/√(n+1)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2
namespace FB

/-- `∫₀^{2π}`-form of the Fourier coefficient of a constant multiple. -/
theorem fb_coeff_const_mul (c : ℂ) (u : ℝ → ℂ) (k : ℤ) :
    fourierCoeff (fun θ => c * u θ) k = c * fourierCoeff u k := by
  unfold fourierCoeff
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Fourier coefficient on the circle of radius `r` of a power `z^j`. -/
theorem fb_coeff_zpow {r : ℝ} (hr : 0 < r) (j k : ℤ) :
    fourierCoeff (fun θ : ℝ => ((r : ℂ) * exp (θ * I)) ^ j) k = if k = j then (r : ℂ) ^ j else 0 := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h : (fun θ : ℝ => ((r : ℂ) * exp (θ * I)) ^ j) = fun θ : ℝ => (r : ℂ) ^ j * exp (θ * I) ^ j := by
    funext θ; rw [mul_zpow]
  rw [h, fb_coeff_const_mul]
  have := circleCoeff_zpow j k
  unfold circleCoeff at this
  rw [this]
  split_ifs <;> simp

/-- Fourier coefficients on the circle of radius `r > 1` of a function with a Laurent expansion on `𝔻*`. -/
theorem fb_coeff_radius {F : ℂ → ℂ} {c : ℕ → ℂ} {N : ℕ}
    (hF : ContinuousOn F {z | 1 ≤ ‖z‖})
    (hsum : ∀ z ∈ unitDiscExterior, HasSum (fun m : ℕ => c m * z ^ (-(m + 1 : ℤ))) (F z - z ^ N))
    {r : ℝ} (hr : 1 < r) (k : ℤ) :
    fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) k =
      (if k = N then (r : ℂ) ^ N else 0) + (if k < 0 then c (k.natAbs - 1) * (r : ℂ) ^ k else 0) := by
  have hr0 : 0 < r := by linarith
  set z : ℝ → ℂ := fun θ => (r : ℂ) * exp (θ * I) with hz
  have hznorm : ∀ θ, ‖z θ‖ = r := by
    intro θ; simp [hz, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr0]
  have hzne : ∀ θ, z θ ≠ 0 := fun θ => by
    intro h; have := hznorm θ; rw [h, norm_zero] at this; linarith
  have hzE : ∀ θ, z θ ∈ unitDiscExterior := fun θ => by
    show 1 < ‖z θ‖; rw [hznorm]; exact hr
  have hzc : Continuous z := by simp only [hz]; fun_prop
  have hFc : Continuous fun θ => F (z θ) :=
    hF.comp_continuous hzc (fun θ => by show 1 ≤ ‖z θ‖; rw [hznorm]; exact hr.le)
  set e : ℝ → ℂ := fun θ => exp (-((k : ℂ) * θ * I)) with he
  have hec : Continuous e := by simp only [he]; fun_prop
  have hen : ∀ θ, ‖e θ‖ = 1 := by
    intro θ; simp [he, Complex.norm_exp]
  set T : ℕ → ℝ → ℂ := fun m θ => c m * (z θ) ^ (-(m + 1 : ℤ)) * e θ with hTdef
  have hTc : ∀ m, Continuous (T m) := by
    intro m
    have : Continuous fun θ => (z θ) ^ (-(m + 1 : ℤ)) := hzc.zpow₀ _ (fun θ => Or.inl (hzne θ))
    exact (continuous_const.mul this).mul hec
  have hrs : (r : ℂ) ∈ unitDiscExterior := by
    show 1 < ‖(r : ℂ)‖; rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr
  have hs : Summable fun m : ℕ => ‖c m‖ * r ^ (-(m + 1 : ℤ)) := by
    have h2 := (summable_norm_iff.2 (hsum (r : ℂ) hrs).summable)
    simpa [norm_mul, norm_zpow, Complex.norm_real, abs_of_pos hr0] using h2
  have hT : HasSum (fun m => ∫ θ in (0 : ℝ)..2 * π, T m θ)
      (∫ θ in (0 : ℝ)..2 * π, (F (z θ) - z θ ^ N) * e θ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun m _ => ‖c m‖ * r ^ (-(m + 1 : ℤ))) (fun m => (hTc m).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · intro m
      refine Eventually.of_forall fun θ _ => ?_
      simp only [hTdef, norm_mul, hen, mul_one, norm_zpow, hznorm]
      exact le_rfl
    · exact Eventually.of_forall fun _ _ => hs
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun θ _ => (hsum (z θ) (hzE θ)).mul_right (e θ)
  -- the terms
  have hterm : ∀ m : ℕ, (1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..2 * π, T m θ =
      c m * (if k = -(m + 1 : ℤ) then (r : ℂ) ^ (-(m + 1 : ℤ)) else 0) := by
    intro m
    have h1 := fb_coeff_const_mul (c m) (fun θ => (z θ) ^ (-(m + 1 : ℤ))) k
    have h2 := fb_coeff_zpow hr0 (-(m + 1 : ℤ)) k
    rw [h2] at h1
    rw [← h1]
    unfold fourierCoeff
    simp only [hTdef, he]
  have hT2 := hT.mul_left (1 / (2 * π : ℂ))
  have hsingle : HasSum (fun m : ℕ => c m * (if k = -(m + 1 : ℤ) then (r : ℂ) ^ (-(m + 1 : ℤ)) else 0))
      (if k < 0 then c (k.natAbs - 1) * (r : ℂ) ^ k else 0) := by
    by_cases hk : k < 0
    · have hm : ((k.natAbs - 1 : ℕ) : ℤ) = -k - 1 := by omega
      have hkk : k = -(((k.natAbs - 1 : ℕ) : ℤ) + 1) := by omega
      rw [if_pos hk]
      convert hasSum_single (f := fun m : ℕ => c m * (if k = -(m + 1 : ℤ) then (r : ℂ) ^ (-(m + 1 : ℤ)) else 0))
        (k.natAbs - 1) ?_ using 1
      · rw [if_pos hkk, ← hkk]
      · intro m hm'
        have : k ≠ -((m : ℤ) + 1) := by
          intro h; apply hm'; omega
        rw [if_neg this, mul_zero]
    · rw [if_neg hk]
      convert hasSum_zero using 1
      funext m
      have : k ≠ -((m : ℤ) + 1) := by intro h; omega
      rw [if_neg this, mul_zero]
  have hT3 : HasSum (fun m : ℕ => c m * (if k = -(m + 1 : ℤ) then (r : ℂ) ^ (-(m + 1 : ℤ)) else 0))
      ((1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..2 * π, (F (z θ) - z θ ^ N) * e θ) := by
    convert hT2 using 1
    funext m
    exact (hterm m).symm
  have hval := hT3.unique hsingle
  have hc1 : Continuous fun θ => (F (z θ) - z θ ^ N) * e θ :=
    (hFc.sub (hzc.pow N)).mul hec
  have hc2 : Continuous fun θ => (z θ) ^ N * e θ := (hzc.pow N).mul hec
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, F (z θ) * e θ =
      (∫ θ in (0 : ℝ)..2 * π, (F (z θ) - z θ ^ N) * e θ) + ∫ θ in (0 : ℝ)..2 * π, (z θ) ^ N * e θ := by
    rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    congr 1; funext θ; ring
  have hpow := fb_coeff_zpow hr0 (N : ℤ) k
  simp only [zpow_natCast] at hpow
  unfold fourierCoeff at hpow ⊢
  simp only [zpow_natCast] at hpow
  change (1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..2 * π, F (z θ) * e θ = _
  rw [hsplit, mul_add, hval]
  have hpow' : (1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..2 * π, (z θ) ^ N * e θ = if k = N then (r : ℂ) ^ N else 0 := hpow
  rw [hpow', add_comm]

theorem fb_cont_circle {F : ℂ → ℂ} (hF : ContinuousOn F {z | 1 ≤ ‖z‖}) {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun θ : ℝ => F ((r : ℂ) * exp (θ * I)) := by
  have hz : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
  refine hF.comp_continuous hz (fun θ => ?_)
  show 1 ≤ ‖(r : ℂ) * exp (θ * I)‖
  simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos (lt_of_lt_of_le one_pos hr), hr]

/-- The radius-`r` Fourier coefficients converge to the boundary ones as `r ↓ 1`. -/
theorem fb_tendsto_radius {F : ℂ → ℂ} (hF : ContinuousOn F {z | 1 ≤ ‖z‖}) (k : ℤ) :
    Tendsto (fun r : ℝ => fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) k) (𝓝[>] 1)
      (𝓝 (circleCoeff F k)) := by
  have hK : IsCompact ({z : ℂ | 1 ≤ ‖z‖} ∩ closedBall (0 : ℂ) 2) :=
    (isCompact_closedBall (0 : ℂ) 2).inter_left (isClosed_le continuous_const continuous_norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF.mono inter_subset_left)
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 1, r ∈ Ioo (1 : ℝ) 2 := Ioo_mem_nhdsGT (by norm_num)
  unfold fourierCoeff circleCoeff fourierCoeff
  refine Tendsto.const_mul _ ?_
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with r hr
    exact ((fb_cont_circle hF hr.1.le).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [hev] with r hr
    refine Eventually.of_forall fun θ _ => ?_
    have hn : ‖(r : ℂ) * exp (θ * I)‖ = r := by
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos (lt_trans one_pos hr.1)]
    have hmem : (r : ℂ) * exp (θ * I) ∈ {z : ℂ | 1 ≤ ‖z‖} ∩ closedBall (0 : ℂ) 2 :=
      ⟨by show 1 ≤ ‖(r : ℂ) * exp (θ * I)‖; rw [hn]; exact hr.1.le,
        by rw [mem_closedBall_zero_iff, hn]; exact hr.2.le⟩
    have he : ‖exp (-((k : ℂ) * θ * I))‖ = 1 := by simp [Complex.norm_exp]
    rw [norm_mul, he, mul_one]
    exact hC _ hmem
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ => ?_
    have h1 : Tendsto (fun r : ℝ => (r : ℂ) * exp (θ * I)) (𝓝[>] 1) (𝓝[{z : ℂ | 1 ≤ ‖z‖}] (exp (θ * I))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => (r : ℂ) * exp (θ * I)) (𝓝 1) (𝓝 ((1 : ℝ) * exp (θ * I))) := by
          apply Continuous.tendsto; fun_prop
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        show 1 ≤ ‖(r : ℂ) * exp (θ * I)‖
        have hr1 : (1 : ℝ) < r := hr
        simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos (lt_trans one_pos hr1), hr1.le]
    have hmem : exp (θ * I) ∈ {z : ℂ | 1 ≤ ‖z‖} := by
      show 1 ≤ ‖exp (θ * I)‖; simp [Complex.norm_exp_ofReal_mul_I]
    exact ((hF _ hmem).tendsto.comp h1).mul_const _

/-- **Boundary coefficients.** For `F` continuous on `{|z| ≥ 1}` with `F(z) = z^N + Σ c_m z^{-(m+1)}` on `|z| > 1`. -/
theorem fb_coeff_boundary {F : ℂ → ℂ} {c : ℕ → ℂ} {N : ℕ}
    (hF : ContinuousOn F {z | 1 ≤ ‖z‖})
    (hsum : ∀ z ∈ unitDiscExterior, HasSum (fun m : ℕ => c m * z ^ (-(m + 1 : ℤ))) (F z - z ^ N))
    (k : ℤ) :
    circleCoeff F k = (if k = N then 1 else 0) + (if k < 0 then c (k.natAbs - 1) else 0) := by
  have h1 := fb_tendsto_radius hF k
  have h2 : Tendsto (fun r : ℝ => (if k = N then (r : ℂ) ^ N else 0) +
      (if k < 0 then c (k.natAbs - 1) * (r : ℂ) ^ k else 0)) (𝓝[>] 1)
      (𝓝 ((if k = N then 1 else 0) + (if k < 0 then c (k.natAbs - 1) else 0))) := by
    have hc1 : Tendsto (fun r : ℝ => (r : ℂ) ^ N) (𝓝[>] 1) (𝓝 1) := by
      have : Continuous fun r : ℝ => (r : ℂ) ^ N := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
    have hc2 : Tendsto (fun r : ℝ => (r : ℂ) ^ k) (𝓝[>] 1) (𝓝 1) := by
      have : ContinuousAt (fun r : ℝ => (r : ℂ) ^ k) 1 :=
        (Complex.continuous_ofReal.continuousAt).zpow₀ k (Or.inl (by simp))
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    refine Tendsto.add ?_ ?_
    · by_cases hk : k = N
      · simpa [hk] using hc1
      · simp [hk]
    · by_cases hk : k < 0
      · simpa [hk] using hc2.const_mul (c (k.natAbs - 1))
      · simp [hk]
  have hev : (fun r : ℝ => fourierCoeff (fun θ : ℝ => F ((r : ℂ) * exp (θ * I))) k) =ᶠ[𝓝[>] 1]
      fun r : ℝ => (if k = N then (r : ℂ) ^ N else 0) + (if k < 0 then c (k.natAbs - 1) * (r : ℂ) ^ k else 0) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact fb_coeff_radius hF hsum hr k
  exact tendsto_nhds_unique_of_eventuallyEq h1 h2 hev

/-- Clauses 1–2 of Remark 5.7 (with the boundary values of `𝗀_μ` read through its continuous extension
`normalizedWeldingExterior μ`, which equals `gsans μ` on `𝔻*`). -/
theorem fb_clauses12 {p : T1} (hp : p ∈ T01) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z =>
      (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = B4 b n m) := by
  intro μ b w
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hcont := (normalizedWeldingExterior_continuous_proper hμ).1
  have hcoef : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) k =
      (if k = ((n + 1 : ℕ) : ℤ) then 1 else 0) +
        (if k < 0 then ((n + 1 : ℕ) : ℂ) * grunsky (fsans μ) (gsans μ) (n + 1) ((k.natAbs - 1 : ℕ) + 1 : ℕ) else 0) := by
    intro n k
    have hF : ContinuousOn (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) {z | 1 ≤ ‖z‖} :=
      ((Polynomial.continuous _).comp hcont).continuousOn
    have hsum : ∀ z ∈ unitDiscExterior, HasSum
        (fun m : ℕ => (((n + 1 : ℕ) : ℂ) * grunsky (fsans μ) (gsans μ) (n + 1) (m + 1)) * z ^ (-(m + 1 : ℤ)))
        ((P (n + 1)).eval (normalizedWeldingExterior μ z) - z ^ (n + 1)) := by
      intro z hz
      have h := hPQ.2.1 n z hz
      have hg : gsans μ z = normalizedWeldingExterior μ z := by
        rw [e13_gsans_eq hμ]; exact gMu_eq_normalizedWeldingExterior hμ hz
      rw [hg] at h
      exact h
    exact fb_coeff_boundary hF hsum k
  have hdiv : ∀ n : ℕ, ∀ k : ℤ, circleCoeff (w n) k =
      circleCoeff (fun z => (P (n + 1)).eval (normalizedWeldingExterior μ z)) k / (Real.sqrt (n + 1) : ℝ) :=
    fun n k => circleCoeff_div_const _ _ k
  have hsq : ∀ n : ℕ, (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  refine ⟨fun n m => ?_, fun n m => ?_⟩
  · rw [hdiv, hcoef]
    have : ¬ ((m : ℤ) + 1 < 0) := by omega
    simp only [this, if_false, add_zero]
    unfold kron
    by_cases hmn : m = n
    · subst hmn
      have hk : ((m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ)) := by push_cast; rfl
      rw [if_pos hk, if_pos rfl, div_mul_cancel₀ _ (hsq m)]
    · have : ¬ ((m : ℤ) + 1 = ((n + 1 : ℕ) : ℤ)) := by omega
      simp [this, hmn]
  · rw [hdiv, hcoef]
    have h1 : ¬ (-((m : ℤ) + 1) = ((n + 1 : ℕ) : ℤ)) := by omega
    have h2 : -((m : ℤ) + 1) < 0 := by omega
    have h3 : (-((m : ℤ) + 1)).natAbs - 1 = m := by omega
    simp only [h1, h2, if_false, if_true, zero_add, h3]
    unfold B4
    have hs1 := hsq n
    have hs2 : (Real.sqrt ((m : ℝ) + 1) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    have hb : grunsky (fsans μ) (gsans μ) (n + 1) ((m : ℕ) + 1 : ℕ) = grunsky (fsans μ) (gsans μ) ((n : ℤ) + 1) ((m : ℤ) + 1) := by
      push_cast; rfl
    rw [hb]
    have hprod : (Real.sqrt (((n : ℝ) + 1) * ((m : ℝ) + 1)) : ℂ) =
        (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((m : ℝ) + 1) : ℂ) := by
      rw [Real.sqrt_mul (by positivity)]; push_cast; ring
    rw [hprod]
    have hn2 : (((n + 1 : ℕ) : ℂ)) = (Real.sqrt ((n : ℝ) + 1) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    rw [hn2]
    field_simp
    rfl

/-! ### Clause 3, step A: the Grunsky coefficients of `(fsans, gsans)` depend only on the class -/

theorem fb_derivAtInfty_congr {g g' : ℂ → ℂ} (h : EqOn g g' unitDiscExterior) :
    derivAtInfty g = derivAtInfty g' := by
  unfold derivAtInfty limUnder
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, 1 < ‖z‖ := tendsto_norm_cocompact_atTop.eventually_gt_atTop 1
  have heq : (fun z => g z / z) =ᶠ[cocompact ℂ] fun z => g' z / z := by
    filter_upwards [hev] with z hz
    rw [h (show z ∈ unitDiscExterior from hz)]
  rw [Filter.map_congr heq]

theorem fb_isGrunskyCoeff_mp {f f' g g' : ℂ → ℂ} {b : ℤ → ℤ → ℂ} (hf : EqOn f f' unitDisc)
    (hg : EqOn g g' unitDiscExterior) (hb : IsGrunskyCoeff f g b) : IsGrunskyCoeff f' g' b := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  refine ⟨by rw [← fb_derivAtInfty_congr hg]; exact h0, ?_, ?_, ?_, h4⟩
  · intro z hz ζ hζ hne
    obtain ⟨S, hS, he⟩ := h1 z hz ζ hζ hne
    exact ⟨S, hS, by rw [← hg hz, ← hg hζ]; exact he⟩
  · intro z hz ζ hζ
    obtain ⟨S, hS, he⟩ := h2 z hz ζ hζ
    refine ⟨S, hS, ?_⟩
    rw [← hg hz, ← hf hζ, ← fb_derivAtInfty_congr hg]
    exact he
  · intro z hz ζ hζ hne
    obtain ⟨S, hS, he⟩ := h3 z hz ζ hζ hne
    exact ⟨S, hS, by rw [← hf hz, ← hf hζ]; exact he⟩

theorem fb_isGrunskyCoeff_congr {f f' g g' : ℂ → ℂ} (hf : EqOn f f' unitDisc)
    (hg : EqOn g g' unitDiscExterior) (b : ℤ → ℤ → ℂ) :
    IsGrunskyCoeff f g b ↔ IsGrunskyCoeff f' g' b :=
  ⟨fb_isGrunskyCoeff_mp hf hg, fb_isGrunskyCoeff_mp hf.symm hg.symm⟩

theorem fb_pair_class {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (h : ∀ z ∈ unitCircle, wA μ z = wA ν z) :
    EqOn (fsans μ) (fsans ν) unitDisc ∧ EqOn (gsans μ) (gsans ν) unitDiscExterior := by
  have hOF : IsOneFixedQS (wA μ) := by
    obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hm2⟩ := wA_spec hμ
    refine ⟨⟨wA_circle_sensePreserving hμ, wA_circle_quasisymmetric hμ⟩, ?_⟩
    show finPart (wAS _ ((1 : ℂ) : ExtPlane)) = 1
    rw [hm2]; rfl
  have hw0 := weldingPrime_congr_h (h := wA μ) (h' := wA ν) (fun z hz => h z hz)
    (normalizedWeldingPrime_actual hμ)
  have hu := conformal_welding_prime_unique hOF (normalizedWeldingPrime_actual hμ)
    (weldingPrime_congr_h (h := wA ν) (h' := wA μ) (fun z hz => (h z hz).symm)
      (normalizedWeldingPrime_actual hν))
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [e13_fsans_eq hμ, e13_fsans_eq hν]
    exact hu.1 hz
  · intro z hz
    rw [e13_gsans_eq hμ, e13_gsans_eq hν, gMu_eq_normalizedWeldingExterior hμ hz,
      gMu_eq_normalizedWeldingExterior hν hz]
    exact hu.2 hz

theorem fb_grunsky_class {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (h : ∀ z ∈ unitCircle, wA μ z = wA ν z) :
    grunsky (fsans μ) (gsans μ) = grunsky (fsans ν) (gsans ν) := by
  obtain ⟨hf, hg⟩ := fb_pair_class hμ hν h
  have hpred : IsGrunskyCoeff (fsans μ) (gsans μ) = IsGrunskyCoeff (fsans ν) (gsans ν) :=
    funext fun b => propext (fb_isGrunskyCoeff_congr hf hg b)
  unfold grunsky
  rw [hpred]

/-! ### Clause 3, step B: coefficient comparison from `exp E = 1` -/

/-- If the double series `D(s,t) = Σ d_{pq} s^p t^q` has `exp D(s,t) = 1` for distinct nonzero `s,t ∈ 𝔻`, then every
coefficient except `d_{00}` vanishes. -/
theorem fb_double_zero_of_exp {d : ℕ → ℕ → ℂ}
    (hS : ∀ s ∈ unitDisc, s ≠ 0 → ∀ t ∈ unitDisc, t ≠ 0 → s ≠ t → ∃ E : ℂ,
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * s ^ p.1 * t ^ p.2) E ∧ exp E = 1) :
    ∀ p q, (p, q) ≠ (0, 0) → d p q = 0 := by
  let D' : Set ℂ := unitDisc \ {0}
  have hD'dense : ∀ F : Set ℂ, F.Finite → unitDisc ⊆ closure (unitDisc \ F) := by
    intro F hF z hz
    have hd : Dense Fᶜ := hF.countable.dense_compl ℝ
    have := hd.open_subset_closure_inter (show IsOpen unitDisc from isOpen_ball) hz
    exact closure_mono (by intro w hw; exact ⟨hw.1, hw.2⟩) this
  let Ev : ℂ → ℂ → ℂ := fun s t => ∑' p : ℕ × ℕ, d p.1 p.2 * s ^ p.1 * t ^ p.2
  let e : ℂ → ℕ → ℂ := fun t p => ∑' q : ℕ, d p q * t ^ q
  let Φ : ℂ → ℂ → ℂ := fun t s => ∑' p : ℕ, e t p * s ^ p
  have hconn : IsPreconnected unitDisc := (convex_ball (0 : ℂ) 1).isPreconnected
  haveI : PreconnectedSpace unitDisc := isPreconnected_iff_preconnectedSpace.mp hconn
  have hmemD' : ∀ z, z ∈ D' ↔ z ∈ unitDisc ∧ z ≠ 0 := fun z => by simp [D']
  have F1 : ∀ s ∈ D', ∀ t ∈ D', s ≠ t →
      HasSum (fun p : ℕ × ℕ => d p.1 p.2 * s ^ p.1 * t ^ p.2) (Ev s t) ∧ exp (Ev s t) = 1 := by
    intro s hs t ht hst
    obtain ⟨hs1, hs0⟩ := (hmemD' s).mp hs
    obtain ⟨ht1, ht0⟩ := (hmemD' t).mp ht
    obtain ⟨E, hE, hexp⟩ := hS s hs1 hs0 t ht1 ht0 hst
    have : Ev s t = E := hE.tsum_eq
    rw [this]
    exact ⟨hE, hexp⟩
  have F2 : ∀ s ∈ D', ∀ t ∈ D', s ≠ t →
      (∀ p, Summable (fun q => d p q * t ^ q)) ∧ HasSum (fun p => e t p * s ^ p) (Ev s t) := by
    intro s hs t ht hst
    obtain ⟨hE, -⟩ := F1 s hs t ht hst
    obtain ⟨hs1, hs0⟩ := (hmemD' s).mp hs
    have hrs : ∀ p, Summable (fun q => d p q * t ^ q) := by
      intro p
      have h1 := hE.summable.prod_factor p
      have hsp : s ^ p ≠ 0 := pow_ne_zero p hs0
      have h2 : Summable (fun q => s ^ p * (d p q * t ^ q)) :=
        h1.congr (fun q => by simp only; ring)
      exact (summable_mul_left_iff hsp).mp h2
    refine ⟨hrs, ?_⟩
    apply hE.prod_fiberwise
    intro p
    have := (hrs p).hasSum.mul_right (s ^ p)
    convert this using 1
    funext q
    simp only
    ring
  have F3 : ∀ t ∈ D', (∀ s ∈ unitDisc, HasSum (fun p => e t p * s ^ p) (Φ t s)) ∧
      ContinuousOn (Φ t) unitDisc := by
    intro t ht
    apply g1_series_disk (d := e t)
    intro x hx0 hx1
    by_cases hxt : ((x : ℝ) : ℂ) = t
    · refine ⟨-(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : (-(x : ℂ)) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        simpa using hx0.ne'
      have hne : (-(x : ℂ)) ≠ t := by
        intro h
        have : (x : ℂ) = 0 := by rw [← hxt] at h; linear_combination -h / 2
        exact hx0.ne' (by exact_mod_cast this)
      exact (F2 _ hs t ht hne).2.summable
    · refine ⟨(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : ((x : ℝ) : ℂ) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        exact_mod_cast hx0.ne'
      exact (F2 _ hs t ht hxt).2.summable
  have F4 : ∀ t ∈ D', ∀ s ∈ D', s ≠ t → Φ t s = Ev s t := by
    intro t ht s hs hst
    exact ((F3 t ht).1 s ((hmemD' s).mp hs).1).unique (F2 s hs t ht hst).2
  have F5 : ∀ t ∈ D', ∀ s ∈ unitDisc, exp (Φ t s) = 1 := by
    intro t ht s hs
    have hcl := hD'dense {0, t} (Set.toFinite _)
    have hEq : EqOn (fun s => exp (Φ t s)) (fun _ => (1 : ℂ)) unitDisc := by
      apply Set.EqOn.of_subset_closure (s := unitDisc \ {0, t}) (t := unitDisc) _
        (Complex.continuous_exp.comp_continuousOn (F3 t ht).2) continuousOn_const diff_subset hcl
      intro w hw
      have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
      have hwt : w ≠ t := fun h => hw.2 (by simp [h])
      have hwD' : w ∈ D' := (hmemD' w).mpr ⟨hw.1, hw0⟩
      show exp (Φ t w) = 1
      rw [F4 t ht w hwD' hwt]
      exact (F1 w hwD' t ht hwt).2
    exact hEq hs
  have F6 : ∀ t ∈ D', ∀ s ∈ unitDisc, Φ t s = Φ t 0 := by
    intro t ht s hs
    have hc : Continuous (fun x : unitDisc => Φ t (x : ℂ)) :=
      (F3 t ht).2.comp_continuous continuous_subtype_val (fun x => x.2)
    have := continuous_exp_lift_unique (X := unitDisc) (L := fun x => Φ t (x : ℂ))
      (M := fun _ => Φ t 0) hc continuous_const
      (fun x => by rw [F5 t ht _ x.2, F5 t ht 0 (mem_ball_self one_pos)])
      (x₀ := ⟨0, mem_ball_self one_pos⟩) rfl
    exact congrFun this ⟨s, hs⟩
  -- rows `p ≥ 1` vanish
  have F11 : ∀ t ∈ D', ∀ p, p ≠ 0 → e t p = 0 := by
    intro t ht p hp
    have := powerSeries_coeff_unique (a := e t) (b := fun r => if r = 0 then Φ t 0 else 0)
      (F := fun _ => Φ t 0)
      (fun z hz => by simpa [F6 t ht z hz] using (F3 t ht).1 z hz)
      (fun z _ => by
        convert hasSum_ite_eq 0 (Φ t 0) using 1
        funext r
        by_cases hr : r = 0
        · subst hr; simp
        · simp [hr])
    have := congrFun this p
    simpa [hp] using this
  have hrowsum : ∀ t ∈ D', ∀ p, Summable (fun q => d p q * t ^ q) := by
    intro t ht p
    by_cases h : t = 1 / 2
    · exact (F2 (1 / 3) (by simp [hmemD', unitDisc, mem_ball_zero_iff, norm_div]; norm_num) t ht
        (by rw [h]; norm_num)).1 p
    · exact (F2 (1 / 2) (by simp [hmemD', unitDisc, mem_ball_zero_iff, norm_div]; norm_num) t ht
        (Ne.symm h)).1 p
  have F12 : ∀ p, p ≠ 0 → ∀ q, d p q = 0 := by
    intro p hp q
    have hpr := g1_series_disk (d := fun q => d p q) (by
      intro x hx0 hx1
      refine ⟨(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
      have hs : ((x : ℝ) : ℂ) ∈ D' := by
        refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
        exact_mod_cast hx0.ne'
      exact hrowsum _ hs p)
    have hcl := hD'dense {0} (Set.toFinite _)
    have hG0 : EqOn (fun z => ∑' q, d p q * z ^ q) (fun _ => (0 : ℂ)) unitDisc := by
      apply Set.EqOn.of_subset_closure (s := unitDisc \ {0}) (t := unitDisc) _ hpr.2 continuousOn_const
        diff_subset hcl
      intro w hw
      have hwD' : w ∈ D' := hw
      show ∑' q, d p q * w ^ q = 0
      exact F11 w hwD' p hp
    have := powerSeries_coeff_unique (a := fun q => d p q) (b := fun _ => 0) (F := fun _ => 0)
      (fun z hz => by simpa [hG0 hz] using hpr.1 z hz)
      (fun z _ => by simpa using hasSum_zero)
    exact congrFun this q
  -- row `0`: the sum `Σ_q d_{0q} t^q = Φ t 0` has `exp = 1`, hence is constant
  have hpr0 := g1_series_disk (d := fun q => d 0 q) (by
    intro x hx0 hx1
    refine ⟨(x : ℂ), by simp [abs_of_pos hx0], ?_⟩
    have hs : ((x : ℝ) : ℂ) ∈ D' := by
      refine (hmemD' _).mpr ⟨mem_ball_zero_iff.mpr (by simpa [abs_of_pos hx0] using hx1), ?_⟩
      exact_mod_cast hx0.ne'
    exact hrowsum _ hs 0)
  have hexp0 : ∀ t ∈ D', exp (∑' q, d 0 q * t ^ q) = 1 := by
    intro t ht
    have h1 : ∑' q, d 0 q * t ^ q = Φ t 0 := by
      have h2 : Φ t 0 = e t 0 := by
        show ∑' p, e t p * (0 : ℂ) ^ p = e t 0
        rw [tsum_eq_single 0 (fun b hb => by rw [zero_pow hb, mul_zero])]
        simp
      rw [h2]
    rw [h1]
    simpa [F6 t ht 0 (mem_ball_self one_pos)] using F5 t ht 0 (mem_ball_self one_pos)
  have hEq0 : EqOn (fun t => exp (∑' q, d 0 q * t ^ q)) (fun _ => (1 : ℂ)) unitDisc := by
    have hcl := hD'dense {0} (Set.toFinite _)
    apply Set.EqOn.of_subset_closure (s := unitDisc \ {0}) (t := unitDisc) _
      (Complex.continuous_exp.comp_continuousOn hpr0.2) continuousOn_const diff_subset hcl
    intro w hw
    exact hexp0 w hw
  have hconst0 : ∀ t ∈ unitDisc, ∑' q, d 0 q * t ^ q = ∑' q, d 0 q * (0 : ℂ) ^ q := by
    intro t ht
    have hc : Continuous (fun x : unitDisc => ∑' q, d 0 q * (x : ℂ) ^ q) :=
      hpr0.2.comp_continuous continuous_subtype_val (fun x => x.2)
    have := continuous_exp_lift_unique (X := unitDisc) (L := fun x => ∑' q, d 0 q * (x : ℂ) ^ q)
      (M := fun _ => ∑' q, d 0 q * (0 : ℂ) ^ q) hc continuous_const
      (fun x => (hEq0 x.2).trans (hEq0 (mem_ball_self one_pos)).symm)
      (x₀ := ⟨0, mem_ball_self one_pos⟩) rfl
    exact congrFun this ⟨t, ht⟩
  have F13 : ∀ q, q ≠ 0 → d 0 q = 0 := by
    intro q hq
    have := powerSeries_coeff_unique (a := fun q => d 0 q)
      (b := fun r => if r = 0 then ∑' q, d 0 q * (0 : ℂ) ^ q else 0)
      (F := fun _ => ∑' q, d 0 q * (0 : ℂ) ^ q)
      (fun z hz => by simpa [hconst0 z hz] using hpr0.1 z hz)
      (fun z _ => by
        convert hasSum_ite_eq 0 (∑' q, d 0 q * (0 : ℂ) ^ q) using 1
        funext r
        by_cases hr : r = 0
        · subst hr; simp
        · simp [hr])
    have := congrFun this q
    simpa [hq] using this
  intro p q hpq
  by_cases hp : p = 0
  · subst hp
    exact F13 q (fun h => hpq (by simp [h]))
  · exact F12 p hp q

/-! ### Clause 3, step C: the exponential for `f^{μ⁻¹}` in terms of the coefficients of `μ` -/

/-- Coefficient array of the conjugated exponent. -/
def fbA2 (b : ℤ → ℤ → ℂ) (p q : ℕ) : ℂ :=
  (if 1 ≤ p ∧ 1 ≤ q then conj (b p q) else 0) +
    (if q = 0 ∧ 1 ≤ p then -conj (b p 0) else 0) + (if p = 0 ∧ 1 ≤ q then -conj (b q 0) else 0)

theorem fb_conj_zpow_refl {s : ℂ} (n : ℕ) : conj ((refl s) ^ (-((n : ℤ) + 1))) = s ^ (n + 1) := by
  have h : conj (refl s) = s⁻¹ := by simp [refl]
  rw [map_zpow₀, h, g1_zpow_neg_succ, inv_inv]

theorem fb_refl_ne {s : ℂ} (hs : s ≠ 0) : refl s ≠ 0 := by
  simp [refl, hs]

theorem fb_refl_refl {s : ℂ} : refl (refl s) = s := by
  simp [refl]

theorem fb_refl_mem {s : ℂ} (hs : s ∈ unitDisc) (hs0 : s ≠ 0) : refl s ∈ unitDiscExterior := by
  have hsn : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  show 1 < ‖refl s‖
  simp only [refl, norm_inv, Complex.norm_conj]
  exact (one_lt_inv₀ hpos).mpr hsn

theorem fb_ratio_alg {gw gv w v β : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) (hwv : w ≠ v) (hgw : gw ≠ 0)
    (hgv : gv ≠ 0) :
    conj β * (((conj gw)⁻¹ - (conj gv)⁻¹) / ((conj w)⁻¹ - (conj v)⁻¹)) =
      conj (β * ((gw - gv) / (w - v) * (w * v) / (gw * gv))) := by
  have h1 : (gw⁻¹ - gv⁻¹) / (w⁻¹ - v⁻¹) = (gw - gv) / (w - v) * (w * v) / (gw * gv) := by
    have hwv' : w - v ≠ 0 := sub_ne_zero.2 hwv
    have : w⁻¹ - v⁻¹ ≠ 0 := by
      intro h; apply hwv; field_simp at h; exact (sub_eq_zero.1 (by linear_combination -h))
    field_simp
    ring
  have h2 : ((conj gw)⁻¹ - (conj gv)⁻¹) / ((conj w)⁻¹ - (conj v)⁻¹) =
      conj ((gw⁻¹ - gv⁻¹) / (w⁻¹ - v⁻¹)) := by
    simp [map_sub, map_inv₀, map_div₀]
  rw [h2, h1, map_mul]

/-- The first-axis expansion `g(w) = β w exp(-T(w))`. -/
theorem fb_axis_exp {f g : ℂ → ℂ} {b : ℤ → ℤ → ℂ} (hb : IsGrunskyCoeff f g b) (hf0 : f 0 = 0)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ T, HasSum (fun m : ℕ => b (m + 1) 0 * w ^ (-(m + 1 : ℤ))) T ∧
      g w = derivAtInfty g * w * exp (-T) := by
  have hβ : derivAtInfty g ≠ 0 := by rw [← hb.1]; exact exp_ne_zero _
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; exact absurd hw (by norm_num [unitDiscExterior])
  obtain ⟨S, hS, he⟩ := hb.2.2.1 w hw 0 (mem_ball_self one_pos)
  have hT : HasSum (fun m : ℕ => b (m + 1) 0 * w ^ (-(m + 1 : ℤ))) S := by
    refine hS.prod_fiberwise (fun n => ?_)
    apply (hasSum_ite_eq (0 : ℕ) (b (n + 1) 0 * w ^ (-(n + 1 : ℤ)))).congr_fun
    intro m
    by_cases hm : m = 0
    · subst hm; simp
    · simp [hm]
  refine ⟨S, hT, ?_⟩
  rw [hf0, sub_zero] at he
  have : derivAtInfty g * w ≠ 0 := mul_ne_zero hβ hw0
  rw [div_eq_iff this] at he
  rw [he]; ring

/-- The exponential for `f' = r ∘ j ∘ g ∘ j` in terms of the exterior coefficients of `(f, g)`. -/
theorem fb_inv_exp {f g f' : ℂ → ℂ} {b : ℤ → ℤ → ℂ} (hb : IsGrunskyCoeff f g b) (hf0 : f 0 = 0)
    (hf' : ∀ z ∈ unitDisc, z ≠ 0 → f' z = conj (derivAtInfty g) * refl (g (refl z)))
    {s t : ℂ} (hs : s ∈ unitDisc) (hs0 : s ≠ 0) (ht : t ∈ unitDisc) (ht0 : t ≠ 0) (hst : s ≠ t) :
    ∃ E2, HasSum (fun p : ℕ × ℕ => fbA2 b p.1 p.2 * s ^ p.1 * t ^ p.2) E2 ∧
      (f' s - f' t) / (s - t) = exp (-E2) := by
  have hβ : derivAtInfty g ≠ 0 := by rw [← hb.1]; exact exp_ne_zero _
  set w := refl s with hw
  set v := refl t with hv
  have hwE : w ∈ unitDiscExterior := fb_refl_mem hs hs0
  have hvE : v ∈ unitDiscExterior := fb_refl_mem ht ht0
  have hw0 : w ≠ 0 := fb_refl_ne hs0
  have hv0 : v ≠ 0 := fb_refl_ne ht0
  have hwv : w ≠ v := by
    intro h
    apply hst
    have := congrArg refl h
    rwa [fb_refl_refl, fb_refl_refl] at this
  obtain ⟨Sg, hSg, hKg⟩ := hb.2.1 w hwE v hvE hwv
  obtain ⟨Tw, hTw, hgw⟩ := fb_axis_exp hb hf0 hwE
  obtain ⟨Tv, hTv, hgv⟩ := fb_axis_exp hb hf0 hvE
  have hgw0 : g w ≠ 0 := by rw [hgw]; exact mul_ne_zero (mul_ne_zero hβ hw0) (exp_ne_zero _)
  have hgv0 : g v ≠ 0 := by rw [hgv]; exact mul_ne_zero (mul_ne_zero hβ hv0) (exp_ne_zero _)
  -- the three conjugated series
  have hSc : HasSum (fun p : ℕ × ℕ => (if 1 ≤ p.1 ∧ 1 ≤ p.2 then conj (b p.1 p.2) else 0) *
      s ^ p.1 * t ^ p.2) (conj Sg) := by
    have h1 := (Complex.hasSum_conj'.2 hSg)
    have h2 : HasSum (fun p : ℕ × ℕ => conj (b (p.1 + 1) (p.2 + 1)) * s ^ (p.1 + 1) * t ^ (p.2 + 1))
        (conj Sg) := by
      refine h1.congr_fun (fun p => ?_)
      simp only [map_mul]
      rw [fb_conj_zpow_refl p.1, fb_conj_zpow_refl p.2]
    let e : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2 + 1)
    have he : Function.Injective e := by
      intro p q hpq
      simp only [e, Prod.mk.injEq, add_left_inj] at hpq
      exact Prod.ext hpq.1 hpq.2
    have hz : ∀ x ∉ Set.range e, (fun p : ℕ × ℕ => (if 1 ≤ p.1 ∧ 1 ≤ p.2 then conj (b p.1 p.2) else 0) *
        s ^ p.1 * t ^ p.2) x = 0 := by
      rintro ⟨a, c⟩ hx
      simp only
      rcases a with _ | a
      · simp
      · rcases c with _ | c
        · simp
        · exact absurd ⟨(a, c), rfl⟩ hx
    refine (he.hasSum_iff hz).mp ?_
    refine h2.congr_fun (fun p => ?_)
    simp [e]
  have hTc1 : HasSum (fun p : ℕ × ℕ => (if p.2 = 0 ∧ 1 ≤ p.1 then -conj (b p.1 0) else 0) *
      s ^ p.1 * t ^ p.2) (-conj Tw) := by
    have h1 := (Complex.hasSum_conj'.2 hTw).neg
    have h2 : HasSum (fun m : ℕ => -conj (b (m + 1) 0) * s ^ (m + 1)) (-conj Tw) := by
      refine h1.congr_fun (fun m => ?_)
      simp only [map_mul]
      rw [fb_conj_zpow_refl m]
      simp [hw]
    let e : ℕ → ℕ × ℕ := fun m => (m + 1, 0)
    have he : Function.Injective e := by
      intro p q hpq
      simpa [e] using hpq
    have hz : ∀ x ∉ Set.range e, (fun p : ℕ × ℕ => (if p.2 = 0 ∧ 1 ≤ p.1 then -conj (b p.1 0) else 0) *
        s ^ p.1 * t ^ p.2) x = 0 := by
      rintro ⟨a, c⟩ hx
      simp only
      by_cases hc : c = 0
      · rcases a with _ | a
        · simp
        · exact absurd ⟨a, by simp [e, hc]⟩ hx
      · simp [hc]
    refine (he.hasSum_iff hz).mp ?_
    refine h2.congr_fun (fun m => ?_)
    simp [e]
  have hTc2 : HasSum (fun p : ℕ × ℕ => (if p.1 = 0 ∧ 1 ≤ p.2 then -conj (b p.2 0) else 0) *
      s ^ p.1 * t ^ p.2) (-conj Tv) := by
    have h1 := (Complex.hasSum_conj'.2 hTv).neg
    have h2 : HasSum (fun m : ℕ => -conj (b (m + 1) 0) * t ^ (m + 1)) (-conj Tv) := by
      refine h1.congr_fun (fun m => ?_)
      simp only [map_mul]
      rw [fb_conj_zpow_refl m]
      simp [hv]
    let e : ℕ → ℕ × ℕ := fun m => (0, m + 1)
    have he : Function.Injective e := by
      intro p q hpq
      simpa [e] using hpq
    have hz : ∀ x ∉ Set.range e, (fun p : ℕ × ℕ => (if p.1 = 0 ∧ 1 ≤ p.2 then -conj (b p.2 0) else 0) *
        s ^ p.1 * t ^ p.2) x = 0 := by
      rintro ⟨a, c⟩ hx
      simp only
      by_cases ha : a = 0
      · rcases c with _ | c
        · simp
        · exact absurd ⟨c, by simp [e, ha]⟩ hx
      · simp [ha]
    refine (he.hasSum_iff hz).mp ?_
    refine h2.congr_fun (fun m => ?_)
    simp [e]
  refine ⟨conj Sg + -conj Tw + -conj Tv, ?_, ?_⟩
  · have := (hSc.add hTc1).add hTc2
    refine this.congr_fun (fun p => ?_)
    simp only [fbA2]
    ring
  · -- the value
    rw [hf' s hs hs0, hf' t ht ht0]
    have hs' : s = (conj w)⁻¹ := (fb_refl_refl (s := s)).symm
    have ht' : t = (conj v)⁻¹ := (fb_refl_refl (s := t)).symm
    have hcore : (conj (derivAtInfty g) * refl (g w) - conj (derivAtInfty g) * refl (g v)) / (s - t) =
        conj (derivAtInfty g) * (((conj (g w))⁻¹ - (conj (g v))⁻¹) / ((conj w)⁻¹ - (conj v)⁻¹)) := by
      rw [← mul_sub, mul_div_assoc, ← hs', ← ht']
      rfl
    rw [hcore, fb_ratio_alg hw0 hv0 hwv hgw0 hgv0]
    have hE : derivAtInfty g * ((g w - g v) / (w - v) * (w * v) / (g w * g v)) =
        exp (-Sg + Tw + Tv) := by
      rw [hKg]
      rw [hgw, hgv, exp_sub, hb.1]
      have e1 : exp (-Sg + Tw + Tv) = exp (-Sg) * exp Tw * exp Tv := by rw [exp_add, exp_add]
      rw [e1, exp_neg Tw, exp_neg Tv, exp_neg Sg]
      have := exp_ne_zero Tw
      have := exp_ne_zero Tv
      have := exp_ne_zero Sg
      field_simp
    rw [hE, ← Complex.exp_conj]
    congr 1
    simp only [map_add, map_neg]
    ring

/-! ### Clause 3, step D: assembly -/

theorem fb_inv_block {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ)) (-(p : ℤ)) (-(q : ℤ)) =
      conj (grunsky (fsans μ) (gsans μ) p q) := by
  have hν := bc_beltramiInv_mem_ball hμ
  have hpair := AppB.b8_welding_normalized_pair hμ
  have hpair' := AppB.b8_welding_normalized_pair hν
  have hb : IsGrunskyCoeff (fsans μ) (gsans μ) (grunsky (fsans μ) (gsans μ)) := (grunsky_spec hpair).1
  have hb' : IsGrunskyCoeff (fsans (beltramiInv μ)) (gsans (beltramiInv μ))
      (grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ))) := (grunsky_spec hpair').1
  have hf0 : fsans μ 0 = 0 := hpair.2.2.1
  have hf' : ∀ z ∈ unitDisc, z ≠ 0 →
      fsans (beltramiInv μ) z = conj (derivAtInfty (gsans μ)) * refl (gsans μ (refl z)) :=
    fun z hz hz0 => (w3_eq_1_3 hμ).1 z hz hz0
  set b := grunsky (fsans μ) (gsans μ) with hbdef
  set b' := grunsky (fsans (beltramiInv μ)) (gsans (beltramiInv μ)) with hb'def
  let d : ℕ → ℕ → ℂ := fun p q =>
    (if p = 0 ∧ q = 0 then b' 0 0 else 0) - b' (-(p : ℤ)) (-(q : ℤ)) + fbA2 b p q
  have hz := fb_double_zero_of_exp (d := d) (by
    intro s hs hs0 t ht ht0 hst
    obtain ⟨S1, hS1, he1⟩ := hb'.2.2.2.1 s hs t ht hst
    obtain ⟨E2, hE2, he2⟩ := fb_inv_exp hb hf0 hf' hs hs0 ht ht0 hst
    have hc : HasSum (fun p : ℕ × ℕ => (if p.1 = 0 ∧ p.2 = 0 then b' 0 0 else 0) * s ^ p.1 * t ^ p.2)
        (b' 0 0) := by
      have := hasSum_single (f := fun p : ℕ × ℕ => (if p.1 = 0 ∧ p.2 = 0 then b' 0 0 else 0) * s ^ p.1 * t ^ p.2)
        (0, 0) (fun x hx => by
          have : ¬ (x.1 = 0 ∧ x.2 = 0) := fun h => hx (Prod.ext h.1 h.2)
          simp [this])
      simpa using this
    refine ⟨b' 0 0 - S1 + E2, ?_, ?_⟩
    · have := (hc.sub hS1).add hE2
      refine this.congr_fun (fun x => ?_)
      simp only [d]
      ring
    · rw [exp_add, ← he1, he2, ← exp_add]
      simp)
  have := hz p q (by intro h; simp at h; omega)
  simp only [d] at this
  have h1 : ¬ (p = 0 ∧ q = 0) := by omega
  have h2 : fbA2 b p q = conj (b p q) := by
    simp only [fbA2]
    have n1 : ¬ (q = 0 ∧ 1 ≤ p) := by omega
    have n2 : ¬ (p = 0 ∧ 1 ≤ q) := by omega
    rw [if_pos ⟨hp, hq⟩, if_neg n1, if_neg n2, add_zero, add_zero]
  rw [if_neg h1, h2] at this
  linear_combination -this

/-- **Clause 3 of Remark 5.7.** -/
theorem fb_clause3 (p : T1) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    ∀ m n, B4 b m n = conj (periodP (invT p) m n) := by
  intro μ b m n
  have hμ : μ ∈ LinfStarBall := (Quotient.out p : LinfStarBall).2
  have hν := bc_beltramiInv_mem_ball hμ
  have hinv : invT p = Phi ⟨beltramiInv μ, hν⟩ := by
    unfold invT
    rw [dif_pos hν]
  have hout : teichSetoid.r (Phi ⟨beltramiInv μ, hν⟩).out ⟨beltramiInv μ, hν⟩ :=
    Quotient.mk_out (s := teichSetoid) ⟨beltramiInv μ, hν⟩
  have hcl := fb_grunsky_class (Quotient.out (Phi ⟨beltramiInv μ, hν⟩) : LinfStarBall).2 hν
    (fun z hz => hout z hz)
  unfold periodP
  rw [hinv, hcl]
  unfold B1 B4
  have hc := fb_inv_block hμ (m + 1) (n + 1) (by omega) (by omega)
  push_cast at hc
  rw [hc, map_mul]
  simp
  exact Or.inl rfl

end FB

/-- **Remark 5.7** (TT:5688–5700), proved here under the exact (repaired) statement of S5. -/
theorem x5_remark_5_7 {p : T1} (hp : p ∈ T01) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z => (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = B4 b n m) ∧
      ∀ m n, B4 b m n = conj (periodP (invT p) m n) := by
  intro μ b w
  obtain ⟨h1, h2⟩ := FB.fb_clauses12 hp hPQ
  exact ⟨h1, h2, FB.fb_clause3 p⟩

/-! ### Original relocated (2026-10-26) -/

/-- **Remark 5.7** (TT:5688–5700). The mirror embedding `ℰ̃ = J ∘ ℰ ∘ ℐ`.
- `W̃_μ` is spanned by `w̃_n = P_n(𝗀_μ)/√n = e_n + Σ_m √(nm) b_{nm} f_m`, so `pr₋w̃ = B₄(𝗀_μ)`.
- `B₄([μ]) = \overline{B₁([μ]⁻¹)}`.
- **[CORRECTION 2026-10-26]** The boundary values of `𝗀_μ` are those of its continuous extension
  `normalizedWeldingExterior μ`; `gsans μ` is unconstrained on `S¹`, so its Fourier coefficients there were junk
  (found by 下属5). -/
theorem remark_5_7 {p : T1} (hp : p ∈ T01) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber (fsans (Quotient.out p : LinfStarBall)) (gsans (Quotient.out p : LinfStarBall)) P Q) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    let b := grunsky (fsans μ) (gsans μ)
    let w : ℕ → ℂ → ℂ := fun n z => (P (n + 1)).eval (normalizedWeldingExterior μ z) / Real.sqrt (n + 1)
    (∀ n m : ℕ, circleCoeff (w n) (m + 1) * Real.sqrt (m + 1) = kron m n) ∧
      (∀ n m : ℕ, circleCoeff (w n) (-(m + 1 : ℤ)) * Real.sqrt (m + 1) = B4 b n m) ∧
      ∀ m n, B4 b m n = conj (periodP (invT p) m n) :=
  x5_remark_5_7 hp hPQ

end Ch2

end TakhtajanTeo
