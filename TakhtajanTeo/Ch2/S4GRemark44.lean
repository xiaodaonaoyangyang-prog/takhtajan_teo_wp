import TakhtajanTeo.Ch2.S4HolomorphicChart
import TakhtajanTeo.Ch2.S4PrincipalValue
import TakhtajanTeo.Ch2.S4PullbackSmooth
import TakhtajanTeo.Ch2.S4PullbackAssembly
import TakhtajanTeo.Ch2.S4FourthOrderPV
import TakhtajanTeo.Ch1.TCurvePlaneExtensions

/-! # Remark 4.4 (`s4g_`, Program G)

`L_ν ϑ` is the round-excision principal value of `ν` against the difference kernel, with the constant
`-(6/π)` (ERRATA G-1), and `∂ϑ = 0`.

* W1 (`s4g_ahVar_dz3_pv`): `∂³ v̇ = -(6/π) PV ∫ m/(u - y)⁴` where the coefficient `m` is smooth near the point.
* W1b (`s4g_flat_pv`): the flat term `∂³ ahVar (extB ν)`.
* W2a (`s4g_chart_cov`): change of variables from the plane chart to `𝔻*` (Möbius invariance of the kernel).
* W2b (`s4g_sliver_split`): the excision `J(B(y, δ/|J'(y)|))` may be replaced by `B(z, δ)`; the sliver term
  tends to `0` (TT's kernel, checked in `REMARK44_SCOUT.md`).
* W0 (`s4g_exceptional_point`): the point `z = w_κ(∞)` not covered by the plane chart.
* W3 (`s4g_pv_pairing_symm`): symmetry of the pairing of the principal values.
-/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

/-- A `C¹` cutoff killing the pole of `(ζ - z)^{-k}`: `χ = 1` off `ball z ε` and `χ · (· - z)^{-k} ∈ C¹`. -/
theorem s4g_cutoff_pow (z : ℂ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ χ : ℂ → ℂ, (∀ w : ℂ, ε ≤ ‖w - z‖ → χ w = 1) ∧
      ContDiff ℝ 1 (fun ζ : ℂ => χ ζ * ((ζ - z) ^ k)⁻¹) := by
  set b : ContDiffBump z := ⟨ε / 2, ε, by positivity, by linarith⟩ with hb
  refine ⟨fun w => 1 - ((b w : ℝ) : ℂ), ?_, ?_⟩
  · intro w hw
    have h0 : b w = 0 := by
      refine b.zero_of_le_dist ?_
      simpa only [hb, dist_eq_norm] using hw
    simp [h0]
  · rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x z with rfl | hx
    · have hev : (fun ζ : ℂ => (1 - ((b ζ : ℝ) : ℂ)) * ((ζ - x) ^ k)⁻¹) =ᶠ[𝓝 x]
          fun _ => (0 : ℂ) := by
        filter_upwards [Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < ε / 2)] with w hw
        have h1 : b w = 1 :=
          b.one_of_mem_closedBall (by
            simp only [hb, Metric.mem_closedBall]
            exact le_of_lt (Metric.mem_ball.1 hw))
        simp [h1]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (contDiff_const.sub
        (Complex.ofRealCLM.contDiff.comp b.contDiff)).contDiffAt.mul
        (((contDiffAt_id.sub contDiffAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hx)))

/-- `∂_z (ζ - z)^{-k} = -k (ζ - z)^{-(k+1)}` away from the pole. -/
theorem s4g_dz_inv_pow {z w : ℂ} (hw : w ≠ z) (k : ℕ) :
    dz (fun ζ : ℂ => ((ζ - z) ^ k)⁻¹) w = -(k : ℂ) * ((w - z) ^ (k + 1))⁻¹ := by
  have hne : w - z ≠ 0 := sub_ne_zero.2 hw
  have hd : HasDerivAt (fun ζ : ℂ => ((ζ - z) ^ k)⁻¹) (-(k : ℂ) * ((w - z) ^ (k + 1))⁻¹) w := by
    have h1 : HasDerivAt (fun ζ : ℂ => (ζ - z) ^ k) ((k : ℂ) * (w - z) ^ (k - 1)) w := by
      have h := (hasDerivAt_pow k (w - z)).comp w ((hasDerivAt_id w).sub_const z)
      simpa [Function.comp_def] using h
    have h2 := h1.inv (pow_ne_zero k hne)
    convert h2 using 1
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      field_simp
      simp only [Nat.add_sub_cancel]
      ring
  have hf : fderiv ℝ (fun ζ : ℂ => ((ζ - z) ^ k)⁻¹) w =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(k : ℂ) * ((w - z) ^ (k + 1))⁻¹)).restrictScalars
        ℝ) :=
    (hd.hasFDerivAt.restrictScalars ℝ).fderiv
  simp only [dz, hf, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  linear_combination (-(-(k : ℂ) * ((w - z) ^ (k + 1))⁻¹) / 2) * I_mul_I

/-- The `∂_z` Green identity on an annulus for the kernel `(ζ - z)^{-k}`: for `ω ∈ C¹` vanishing on
`|ζ - z| = R`, `∬_{r ≤ |ζ - z| < R} (∂_z ω (ζ - z)^{-k} - k ω (ζ - z)^{-(k+1)}) =
(1/2i) ∮_{|ζ - z| = r} ω (ζ - z)^{-k} dζ̄` (`integral_ball_diff_dz_eq` is `k = 1`). -/
theorem s4g_annulus_ibp {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) {z : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hvan : ∀ θ : ℝ, ω (circleMap z R θ) = 0) (k : ℕ) :
    ∫ ζ in ball z R \ ball z r, (dz ω ζ * ((ζ - z) ^ k)⁻¹ - (k : ℂ) * ω ζ * ((ζ - z) ^ (k + 1))⁻¹) =
      (∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ *
        conj (deriv (circleMap z r) θ)) / (2 * I) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨χ, hχ1, hu⟩ := s4g_cutoff_pow z hr k
  obtain ⟨u, hudef⟩ : ∃ u : ℂ → ℂ, u = fun ζ => (χ ζ * ((ζ - z) ^ k)⁻¹) * ω ζ := ⟨_, rfl⟩
  have huC : ContDiff ℝ 1 u := by rw [hudef]; exact hu.mul hω
  have hG1 := green_disc_dz_closedBall (c := z) hR huC.contDiffOn
  have hG2 := green_disc_dz_closedBall (c := z) hr huC.contDiffOn
  have hc1 : ∀ θ : ℝ, u (circleMap z R θ) = 0 := fun θ => by
    rw [hudef]
    simp only [hvan θ, mul_zero]
  have hc2 : ∀ θ : ℝ, u (circleMap z r θ) = ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ := by
    intro θ
    have h1 : r ≤ ‖circleMap z r θ - z‖ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    rw [hudef]
    simp only [hχ1 _ h1, one_mul]
    ring
  simp only [hc1, zero_mul, intervalIntegral.integral_zero] at hG1
  simp only [hc2] at hG2
  have hdzc : Continuous (dz u) := by
    have h := huC.continuous_fderiv one_ne_zero
    show Continuous fun ζ => (fderiv ℝ u ζ 1 - I * fderiv ℝ u ζ I) / 2
    exact ((h.clm_apply continuous_const).sub
      (continuous_const.mul (h.clm_apply continuous_const))).div_const 2
  have hint : IntegrableOn (dz u) (ball z R) :=
    (hdzc.continuousOn.integrableOn_compact (isCompact_closedBall z R)).mono_set
      ball_subset_closedBall
  have hsplit := setIntegral_diff (μ := volume) measurableSet_ball hint (ball_subset_ball hrR.le)
  have h0 : ∫ ζ in ball z R, dz u ζ = 0 :=
    (mul_eq_zero.1 hG1.symm).resolve_left (by simp)
  have hcongr : ∫ ζ in ball z R \ ball z r, dz u ζ =
      ∫ ζ in ball z R \ ball z r,
        (dz ω ζ * ((ζ - z) ^ k)⁻¹ - (k : ℂ) * ω ζ * ((ζ - z) ^ (k + 1))⁻¹) := by
    refine setIntegral_congr_ae (measurableSet_ball.diff measurableSet_ball) ?_
    have hs : ∀ᵐ ζ : ℂ, ζ ∉ sphere z r := by
      rw [ae_iff]
      exact measure_mono_null (fun a ha => not_not.1 ha)
        (Measure.addHaar_sphere (volume : Measure ℂ) z r)
    filter_upwards [hs] with ζ hζs hζ
    have hge : r ≤ ‖ζ - z‖ := by
      have h := hζ.2
      rwa [mem_ball, dist_eq_norm, not_lt] at h
    have hgt : r < ‖ζ - z‖ :=
      lt_of_le_of_ne hge fun h => hζs (by rw [mem_sphere, dist_eq_norm]; exact h.symm)
    have hne : ζ ≠ z := fun h => by
      rw [h, sub_self, norm_zero] at hgt
      linarith
    have hev : u =ᶠ[𝓝 ζ] fun w => ((w - z) ^ k)⁻¹ * ω w := by
      have hopen : IsOpen {w : ℂ | r < ‖w - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hgt] with w hw
      rw [hudef]
      simp only [hχ1 w hw.le, one_mul]
    have hdinv : DifferentiableAt ℝ (fun w : ℂ => ((w - z) ^ k)⁻¹) ζ :=
      ((((differentiableAt_id.sub_const z).pow k).inv
        (pow_ne_zero k (sub_ne_zero.2 hne))) : DifferentiableAt ℂ _ ζ).restrictScalars ℝ
    rw [show dz u ζ = dz (fun w => ((w - z) ^ k)⁻¹ * ω w) ζ by simp only [dz, hev.fderiv_eq],
      dz_mul hdinv ((hω.differentiable one_ne_zero) ζ), s4g_dz_inv_pow hne]
    ring
  rw [← hcongr, hsplit, h0, zero_sub, hG2,
    show (-2 * I * ∫ ζ in ball z r, dz u ζ) = -((∫ ζ in ball z r, dz u ζ) * (2 * I)) by ring,
    neg_div, mul_div_cancel_right₀ _ (by simp : (2 * I : ℂ) ≠ 0)]

/-- `∫₀^{2π} e^{inθ} dθ = 0` for `n ≠ 0`. -/
theorem s4g_int_exp_zpow {n : ℤ} (hn : n ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp ((θ : ℂ) * I) ^ n = 0 := by
  have hc : (n : ℂ) * I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) I_ne_zero
  have he : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * I) ^ n = Complex.exp ((n : ℂ) * I * θ) := by
    intro θ
    rw [← Complex.exp_int_mul]
    ring_nf
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((n : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I n]
    push_cast
    ring_nf
  rw [h1]
  simp

/-- An `ℝ`-linear map `ℂ → ℂ` is `h ↦ α h + β h̄`. -/
theorem s4g_rlin_decomp (D : ℂ →L[ℝ] ℂ) (h : ℂ) :
    D h = (D 1 - I * D I) / 2 * h + (D 1 + I * D I) / 2 * conj h := by
  have hh : h = (h.re : ℝ) • (1 : ℂ) + (h.im : ℝ) • I := by
    apply Complex.ext <;> simp
  have hD : D h = (h.re : ℂ) * D 1 + (h.im : ℂ) * D I := by
    conv_lhs => rw [hh]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hD]
  conv_rhs => rw [show h = (h.re : ℂ) + (h.im : ℂ) * I from (Complex.re_add_im h).symm]
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  ring_nf
  rw [I_sq]
  ring

/-- An `ℝ`-bilinear form on `ℂ`, on the diagonal, is a quadratic polynomial in `h, h̄`. -/
theorem s4g_rbilin_decomp (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) :
    ∃ A B C : ℂ, ∀ h : ℂ, Q h h = A * h ^ 2 + B * (h * conj h) + C * conj h ^ 2 := by
  set a1 := (Q 1 1 - I * Q I 1) / 2
  set b1 := (Q 1 1 + I * Q I 1) / 2
  set aI := (Q 1 I - I * Q I I) / 2
  set bI := (Q 1 I + I * Q I I) / 2
  refine ⟨(a1 - I * aI) / 2, (b1 - I * bI) / 2 + (a1 + I * aI) / 2, (b1 + I * bI) / 2, fun h => ?_⟩
  have h1 : Q h 1 = a1 * h + b1 * conj h := by
    have := s4g_rlin_decomp (Q.flip 1) h
    simpa only [ContinuousLinearMap.flip_apply] using this
  have hI : Q h I = aI * h + bI * conj h := by
    have := s4g_rlin_decomp (Q.flip I) h
    simpa only [ContinuousLinearMap.flip_apply] using this
  rw [s4g_rlin_decomp (Q h) h, h1, hI]
  ring

/-- The Fourier modes `-3` and `-4` of a quadratic polynomial in `h = r e^{iθ}`, `h̄` vanish. -/
theorem s4g_mode_vanish (a α β A B C : ℂ) (r : ℝ) {j : ℤ} (hj : 3 ≤ j) :
    ∫ θ in (0 : ℝ)..2 * π,
      (a + α * (r * Complex.exp ((θ : ℂ) * I)) + β * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ)) +
        A * (r * Complex.exp ((θ : ℂ) * I)) ^ 2 +
        B * ((r * Complex.exp ((θ : ℂ) * I)) * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ))) +
        C * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ)) ^ 2) * Complex.exp ((θ : ℂ) * I) ^ (-j) = 0 := by
  have hE : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * I) ≠ 0 := fun θ => Complex.exp_ne_zero _
  have hpt : ∀ θ : ℝ,
      (a + α * (r * Complex.exp ((θ : ℂ) * I)) + β * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ)) +
        A * (r * Complex.exp ((θ : ℂ) * I)) ^ 2 +
        B * ((r * Complex.exp ((θ : ℂ) * I)) * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ))) +
        C * (r * Complex.exp ((θ : ℂ) * I) ^ (-1 : ℤ)) ^ 2) * Complex.exp ((θ : ℂ) * I) ^ (-j) =
      (a + B * r ^ 2) * Complex.exp ((θ : ℂ) * I) ^ (-j) +
        α * r * Complex.exp ((θ : ℂ) * I) ^ (1 - j) +
        β * r * Complex.exp ((θ : ℂ) * I) ^ (-1 - j) +
        A * r ^ 2 * Complex.exp ((θ : ℂ) * I) ^ (2 - j) +
        C * r ^ 2 * Complex.exp ((θ : ℂ) * I) ^ (-2 - j) := by
    intro θ
    set E := Complex.exp ((θ : ℂ) * I)
    have h1 : E ^ (1 - j) = E * E ^ (-j) := by
      rw [show (1 : ℤ) - j = 1 + -j by ring, zpow_add₀ (hE θ), zpow_one]
    have h2 : E ^ (-1 - j) = E ^ (-1 : ℤ) * E ^ (-j) := by
      rw [show (-1 : ℤ) - j = -1 + -j by ring, zpow_add₀ (hE θ)]
    have h3 : E ^ (2 - j) = E ^ 2 * E ^ (-j) := by
      rw [show (2 : ℤ) - j = 2 + -j by ring, zpow_add₀ (hE θ)]
      norm_cast
    have h4 : E ^ (-2 - j) = (E ^ (-1 : ℤ)) ^ 2 * E ^ (-j) := by
      rw [show (-2 : ℤ) - j = -1 + -1 + -j by ring, zpow_add₀ (hE θ), zpow_add₀ (hE θ)]
      ring
    have h5 : E * E ^ (-1 : ℤ) = 1 := by
      rw [zpow_neg_one]; exact mul_inv_cancel₀ (hE θ)
    rw [h1, h2, h3, h4]
    linear_combination (B * r ^ 2 * E ^ (-j)) * h5
  have hc : ∀ m : ℤ, Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * I) ^ m := fun m =>
    (Continuous.zpow₀ (Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)) m
      (fun θ => Or.inl (hE θ)))
  have hi : ∀ (c : ℂ) (m : ℤ), IntervalIntegrable (fun θ : ℝ => c * Complex.exp ((θ : ℂ) * I) ^ m)
      volume 0 (2 * π) := fun c m => (continuous_const.mul (hc m)).intervalIntegrable _ _
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((((hi _ _).add (hi _ _)).add (hi _ _)).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add ((((hi _ _).add (hi _ _)).add (hi _ _))) (hi _ _),
    intervalIntegral.integral_add (((hi _ _).add (hi _ _))) (hi _ _),
    intervalIntegral.integral_add (hi _ _) (hi _ _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [s4g_int_exp_zpow (by omega), s4g_int_exp_zpow (by omega), s4g_int_exp_zpow (by omega),
    s4g_int_exp_zpow (by omega), s4g_int_exp_zpow (by omega)]
  simp

/-- **The boundary terms of the annulus identities vanish.** For `ω ∈ C^∞` and `k ∈ {2, 3}`,
`(1/2i) ∮_{|ζ - z| = r} ω (ζ - z)^{-k} dζ̄ → 0` as `r → 0⁺` (its Fourier mode `-(k+1)` sees only the cubic
Taylor remainder). -/
theorem s4g_boundary_lim {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) (z : ℂ) {k : ℕ}
    (hk2 : 2 ≤ k) (hk3 : k ≤ 3) :
    Tendsto (fun r : ℝ => (∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ *
      conj (deriv (circleMap z r) θ)) / (2 * I)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ρ, hρ, L, hL, hT⟩ := s4p4_taylor2 hω z
  set D := fderiv ℝ ω z with hDdef
  set Q := fderiv ℝ (fderiv ℝ ω) z with hQdef
  obtain ⟨A, B, C, hQ⟩ := s4g_rbilin_decomp Q
  have hpi : 0 < π := Real.pi_pos
  -- the bound `π L r` for `0 < r < min ρ 1`
  have hbound : ∀ r : ℝ, 0 < r → r < min ρ 1 →
      ‖(∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ *
        conj (deriv (circleMap z r) θ)) / (2 * I)‖ ≤ π * L * r := by
    intro r hr hrm
    have hrρ : r < ρ := hrm.trans_le (min_le_left _ _)
    have hr1 : r < 1 := hrm.trans_le (min_le_right _ _)
    set j : ℤ := (k : ℤ) + 1 with hj
    have hj3 : 3 ≤ j := by omega
    set E : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I) with hEdef
    have hE0 : ∀ θ, E θ ≠ 0 := fun θ => Complex.exp_ne_zero _
    have hEn : ∀ θ, ‖E θ‖ = 1 := fun θ => by
      simp only [hEdef]; rw [Complex.norm_exp_ofReal_mul_I]
    have hconjE : ∀ θ, conj (E θ) = E θ ^ (-1 : ℤ) := by
      intro θ
      simp only [hEdef, zpow_neg_one, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ← Complex.exp_neg]
      congr 1
      ring
    set c : ℂ := -I * (((r : ℂ) ^ k)⁻¹ * r) with hc
    let P : ℝ → ℂ := fun θ => ω z + D (r * E θ) + (1 / 2 : ℝ) • Q (r * E θ) (r * E θ)
    let Rm : ℝ → ℂ := fun θ => ω (z + r * E θ) - P θ
    have hpt : ∀ θ : ℝ, ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ * conj (deriv (circleMap z r) θ) =
        c * (P θ * E θ ^ (-j)) + c * (Rm θ * E θ ^ (-j)) := by
      intro θ
      have hcm : circleMap z r θ = z + r * E θ := rfl
      have hd : deriv (circleMap z r) θ = r * E θ * I := by
        rw [deriv_circleMap, circleMap, zero_add]
      rw [hcm, hd, add_sub_cancel_left]
      simp only [map_mul, conj_ofReal, conj_I, hconjE]
      have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
      have hEj : E θ ^ (-j) = (E θ ^ k)⁻¹ * E θ ^ (-1 : ℤ) := by
        rw [hj, neg_add, zpow_add₀ (hE0 θ), zpow_neg, zpow_natCast]
      rw [hEj]
      simp only [Rm, mul_pow, mul_inv]
      ring
    have hcont_E : ∀ m : ℤ, Continuous fun θ : ℝ => E θ ^ m := fun m =>
      Continuous.zpow₀ (Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)) m
        (fun θ => Or.inl (hE0 θ))
    have hcont_w : Continuous fun θ : ℝ => ω (z + r * E θ) :=
      hω.continuous.comp (continuous_const.add (continuous_const.mul (hcont_E 1 |>.congr fun θ => zpow_one _)))
    have hcont_P : Continuous P := by
      have hEc : Continuous fun θ : ℝ => (r : ℂ) * E θ :=
        continuous_const.mul ((hcont_E 1).congr fun θ => zpow_one _)
      exact (continuous_const.add (D.continuous.comp hEc)).add
        (((Q.continuous.comp hEc).clm_apply hEc).const_smul (1 / 2 : ℝ))
    have hiP : IntervalIntegrable (fun θ => c * (P θ * E θ ^ (-j))) volume 0 (2 * π) :=
      (continuous_const.mul (hcont_P.mul (hcont_E _))).intervalIntegrable _ _
    have hiR : IntervalIntegrable (fun θ => c * (Rm θ * E θ ^ (-j))) volume 0 (2 * π) :=
      (continuous_const.mul ((hcont_w.sub hcont_P).mul (hcont_E _))).intervalIntegrable _ _
    have hP0 : ∫ θ in (0 : ℝ)..2 * π, P θ * E θ ^ (-j) = 0 := by
      have hform : ∀ θ : ℝ, P θ = ω z + (D 1 - I * D I) / 2 * (r * E θ) +
          (D 1 + I * D I) / 2 * (r * E θ ^ (-1 : ℤ)) + A / 2 * (r * E θ) ^ 2 +
          B / 2 * ((r * E θ) * (r * E θ ^ (-1 : ℤ))) + C / 2 * (r * E θ ^ (-1 : ℤ)) ^ 2 := by
        intro θ
        simp only [P]
        rw [s4g_rlin_decomp D, hQ, map_mul, conj_ofReal, hconjE, Complex.real_smul]
        push_cast
        ring
      simp_rw [hform]
      exact s4g_mode_vanish _ _ _ _ _ _ r hj3
    have hRb : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖Rm θ * E θ ^ (-j)‖ ≤ L * r ^ 3 := by
      intro θ _
      have hh : ‖(r : ℂ) * E θ‖ = r := by rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
      have := hT ((r : ℂ) * E θ) (by rw [hh]; exact hrρ)
      rw [norm_mul, norm_zpow, hEn, one_zpow, mul_one]
      simpa only [Rm, P, hh, sub_sub] using this
    have hRint := intervalIntegral.norm_integral_le_of_norm_le_const hRb
    simp_rw [hpt]
    rw [intervalIntegral.integral_add hiP hiR, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hP0, mul_zero, zero_add, norm_div, norm_mul]
    have hcn : ‖c‖ = r / r ^ k := by
      rw [hc, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
      ring
    have h2I : ‖(2 * I : ℂ)‖ = 2 := by simp
    rw [hcn, h2I]
    have hab : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
    rw [hab] at hRint
    have hrk : r / r ^ k * (L * r ^ 3 * (2 * π)) / 2 ≤ π * L * r := by
      have hk' : r ^ 3 = r ^ k * r ^ (3 - k) := by rw [← pow_add]; congr 1; omega
      have hrk0 : 0 < r ^ k := pow_pos hr k
      have hle : r ^ (3 - k) ≤ 1 := pow_le_one₀ hr.le hr1.le
      rw [hk']
      field_simp
      nlinarith [mul_nonneg hL hr.le, mul_nonneg (mul_nonneg hL hr.le) hpi.le, pow_nonneg hr.le (3 - k)]
    calc r / r ^ k * ‖∫ θ in (0 : ℝ)..2 * π, Rm θ * E θ ^ (-j)‖ / 2
        ≤ r / r ^ k * (L * r ^ 3 * (2 * π)) / 2 := by gcongr
      _ ≤ π * L * r := hrk
  -- squeeze
  have hlim : Tendsto (fun r : ℝ => π * L * r) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => π * L * r := continuous_const.mul continuous_id
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (lt_min hρ one_pos)] with r hr hr'
  exact hbound r hr hr'.2

/-- The Fourier modes `≤ -3` of a smooth function on small circles are `O(r³)`. -/
theorem s4g_fourier_cubic {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (z : ℂ) {j : ℤ}
    (hj : 3 ≤ j) :
    ∃ ρ > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ‖∫ θ in (0 : ℝ)..2 * π, f (z + r * Complex.exp ((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) ^ (-j)‖ ≤
        L * r ^ 3 * (2 * π) := by
  obtain ⟨ρ, hρ, L, hL, hT⟩ := s4p4_taylor2 hf z
  set D := fderiv ℝ f z with hDdef
  set Q := fderiv ℝ (fderiv ℝ f) z with hQdef
  obtain ⟨A, B, C, hQ⟩ := s4g_rbilin_decomp Q
  refine ⟨ρ, hρ, L, hL, fun r hr hrρ => ?_⟩
  set E : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I) with hEdef
  have hE0 : ∀ θ, E θ ≠ 0 := fun θ => Complex.exp_ne_zero _
  have hEn : ∀ θ, ‖E θ‖ = 1 := fun θ => by
    simp only [hEdef]; rw [Complex.norm_exp_ofReal_mul_I]
  have hconjE : ∀ θ, conj (E θ) = E θ ^ (-1 : ℤ) := by
    intro θ
    simp only [hEdef, zpow_neg_one, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ← Complex.exp_neg]
    congr 1
    ring
  let P : ℝ → ℂ := fun θ => f z + D (r * E θ) + (1 / 2 : ℝ) • Q (r * E θ) (r * E θ)
  have hcont_E : ∀ m : ℤ, Continuous fun θ : ℝ => E θ ^ m := fun m =>
    Continuous.zpow₀ (Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)) m
      (fun θ => Or.inl (hE0 θ))
  have hEc : Continuous fun θ : ℝ => (r : ℂ) * E θ :=
    continuous_const.mul ((hcont_E 1).congr fun θ => zpow_one _)
  have hcont_w : Continuous fun θ : ℝ => f (z + r * E θ) := hf.continuous.comp (continuous_const.add hEc)
  have hcont_P : Continuous P :=
    (continuous_const.add (D.continuous.comp hEc)).add
      (((Q.continuous.comp hEc).clm_apply hEc).const_smul (1 / 2 : ℝ))
  have hsplit : ∀ θ, f (z + r * E θ) * E θ ^ (-j) = P θ * E θ ^ (-j) + (f (z + r * E θ) - P θ) * E θ ^ (-j) :=
    fun θ => by ring
  have hP0 : ∫ θ in (0 : ℝ)..2 * π, P θ * E θ ^ (-j) = 0 := by
    have hform : ∀ θ : ℝ, P θ = f z + (D 1 - I * D I) / 2 * (r * E θ) +
        (D 1 + I * D I) / 2 * (r * E θ ^ (-1 : ℤ)) + A / 2 * (r * E θ) ^ 2 +
        B / 2 * ((r * E θ) * (r * E θ ^ (-1 : ℤ))) + C / 2 * (r * E θ ^ (-1 : ℤ)) ^ 2 := by
      intro θ
      simp only [P]
      rw [s4g_rlin_decomp D, hQ, map_mul, conj_ofReal, hconjE, Complex.real_smul]
      push_cast
      ring
    simp_rw [hform]
    exact s4g_mode_vanish _ _ _ _ _ _ r hj
  have hiP : IntervalIntegrable (fun θ => P θ * E θ ^ (-j)) volume 0 (2 * π) :=
    (hcont_P.mul (hcont_E _)).intervalIntegrable _ _
  have hiR : IntervalIntegrable (fun θ => (f (z + r * E θ) - P θ) * E θ ^ (-j)) volume 0 (2 * π) :=
    ((hcont_w.sub hcont_P).mul (hcont_E _)).intervalIntegrable _ _
  have hRb : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖(f (z + r * E θ) - P θ) * E θ ^ (-j)‖ ≤ L * r ^ 3 := by
    intro θ _
    have hh : ‖(r : ℂ) * E θ‖ = r := by rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have := hT ((r : ℂ) * E θ) (by rw [hh]; exact hrρ)
    rw [norm_mul, norm_zpow, hEn, one_zpow, mul_one]
    simpa only [P, hh, sub_sub] using this
  have hRint := intervalIntegral.norm_integral_le_of_norm_le_const hRb
  have hab : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
  rw [hab] at hRint
  have h2 : (∫ θ in (0 : ℝ)..2 * π, f (z + r * Complex.exp ((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) ^ (-j)) =
      ∫ θ in (0 : ℝ)..2 * π, (P θ * E θ ^ (-j) + (f (z + r * E θ) - P θ) * E θ ^ (-j)) :=
    intervalIntegral.integral_congr fun θ _ => hsplit θ
  rw [h2, intervalIntegral.integral_add hiP hiR, hP0, zero_add]
  exact hRint

/-- A function continuous off the pole is integrable against `(ζ - z)^{-k}` on a closed annulus. -/
theorem s4g_int_ann {g : ℂ → ℂ} (hg : Continuous g) (z : ℂ) {r R : ℝ} (hr : 0 < r) (k : ℕ) :
    IntegrableOn (fun ζ => g ζ * ((ζ - z) ^ k)⁻¹) (ball z R \ ball z r) := by
  have hK : IsCompact (closedBall z R ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) :=
    (isCompact_closedBall z R).inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hcont : ContinuousOn (fun ζ => g ζ * ((ζ - z) ^ k)⁻¹) (closedBall z R ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) := by
    refine hg.continuousOn.mul (ContinuousOn.inv₀ ((continuous_id.sub continuous_const).pow k).continuousOn ?_)
    intro ζ hζ h0
    have h1 : r ≤ ‖ζ - z‖ := hζ.2
    rw [pow_eq_zero_iff', sub_eq_zero] at h0
    rw [h0.1, sub_self, norm_zero] at h1
    linarith
  refine (hcont.integrableOn_compact hK).mono_set ?_
  intro ζ hζ
  refine ⟨ball_subset_closedBall hζ.1, ?_⟩
  have h := hζ.2
  rw [mem_ball, dist_eq_norm, not_lt] at h
  exact h

/-- Integrals of a function vanishing off `ball z R` over `ball z R \ ball z r`, over `{r < |ζ - z|}`
and over `(ball z r)ᶜ` agree. -/
theorem s4g_ann_sets {f : ℂ → ℂ} {z : ℂ} {r R : ℝ} (hvan : ∀ ζ, R ≤ ‖ζ - z‖ → f ζ = 0) :
    (∫ ζ in ball z R \ ball z r, f ζ) = ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, f ζ ∧
      (∫ ζ in ball z R \ ball z r, f ζ) = ∫ ζ in (ball z r)ᶜ, f ζ := by
  set T : Set ℂ := annulusAt z r R with hT
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const (measurable_id.sub_const z).norm).inter
      (measurableSet_lt (measurable_id.sub_const z).norm measurable_const)
  have hs : ∀ᵐ ζ : ℂ, ζ ∉ sphere z r := by
    rw [ae_iff]
    exact measure_mono_null (fun a ha => not_not.1 ha) (Measure.addHaar_sphere (volume : Measure ℂ) z r)
  have h1 : (∫ ζ in ball z R \ ball z r, f ζ) = ∫ ζ in T, f ζ := by
    refine setIntegral_eq_of_subset_of_ae_diff_eq_zero
      (measurableSet_ball.diff measurableSet_ball).nullMeasurableSet ?_ ?_
    · intro ζ hζ
      refine ⟨mem_ball_iff_norm.2 hζ.2, ?_⟩
      rw [mem_ball_iff_norm, not_lt]
      exact hζ.1.le
    · filter_upwards [hs] with ζ hζs hζ
      exfalso
      apply hζ.2
      refine ⟨?_, mem_ball_iff_norm.1 hζ.1.1⟩
      have h := hζ.1.2
      rw [mem_ball_iff_norm, not_lt] at h
      exact lt_of_le_of_ne h fun he => hζs (by rw [mem_sphere_iff_norm]; exact he.symm)
  have h2 : (∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, f ζ) = ∫ ζ in T, f ζ := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (measurableSet_lt measurable_const (measurable_id.sub_const z).norm) (fun ζ hζ => hζ.1) ?_
    intro ζ hζ
    apply hvan
    by_contra hlt
    exact hζ.2 ⟨hζ.1, not_le.1 hlt⟩
  have h3 : (∫ ζ in (ball z r)ᶜ, f ζ) = ∫ ζ in T, f ζ := by
    refine setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_ball.compl.nullMeasurableSet ?_ ?_
    · intro ζ hζ
      rw [mem_compl_iff, mem_ball_iff_norm, not_lt]
      exact hζ.1.le
    · filter_upwards [hs] with ζ hζs hζ
      apply hvan
      by_contra hlt
      apply hζ.2
      have h := hζ.1
      rw [mem_compl_iff, mem_ball_iff_norm, not_lt] at h
      exact ⟨lt_of_le_of_ne h fun he => hζs (by rw [mem_sphere_iff_norm]; exact he.symm), not_le.1 hlt⟩
  exact ⟨h1.trans h2.symm, h1.trans h3.symm⟩

/-- `s4g_annulus_ibp` with the two integrals split. -/
theorem s4g_annulus_ibp_split {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hvan : ∀ θ : ℝ, ω (circleMap z R θ) = 0) (k : ℕ) :
    (∫ ζ in ball z R \ ball z r, dz ω ζ * ((ζ - z) ^ k)⁻¹) -
        (k : ℂ) * ∫ ζ in ball z R \ ball z r, ω ζ * ((ζ - z) ^ (k + 1))⁻¹ =
      (∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * ((circleMap z r θ - z) ^ k)⁻¹ *
        conj (deriv (circleMap z r) θ)) / (2 * I) := by
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hf := s4g_int_ann (dz_contDiff hω).continuous z hr (R := R) k
  have hg := (s4g_int_ann hω.continuous z hr (R := R) (k + 1)).const_mul (k : ℂ)
  rw [← integral_const_mul, ← integral_sub hf hg, ← s4g_annulus_ibp (hω.of_le hone) hr hrR hvan k]
  congr 1
  funext ζ
  ring

/-- **The near part of W1.** For `n ∈ C^∞_c`, `-(6/π) PV ∫ n(u)/(u - y)⁴ = T(∂³n)(y) = ∂³ T n (y)`. -/
theorem s4g_cauchyT_dz3_pv {n : ℂ → ℂ} (hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n) (hc : HasCompactSupport n)
    (y : ℂ) :
    Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ u in (ball y δ)ᶜ, n u / (u - y) ^ 4) (𝓝[>] 0)
      (𝓝 (cauchyT (dz (dz (dz n))) y)) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz n) := dz_contDiff hn
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz (dz n)) := dz_contDiff h1
  have hc1 : HasCompactSupport (dz n) := wr_dz_hasCompactSupport hc
  have hc2 : HasCompactSupport (dz (dz n)) := wr_dz_hasCompactSupport hc1
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hS := tendsto_truncated_cauchyT_dz (h2.of_le hone) hc2 y
  -- a radius outside all supports
  obtain ⟨M₀, hM₀⟩ := hc.isCompact.isBounded.subset_closedBall y
  set R : ℝ := max M₀ 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hMR : M₀ < R := by rw [hRdef]; linarith [le_max_left M₀ 0]
  set V : Set ℂ := {ζ : ℂ | M₀ < ‖ζ - y‖} with hVdef
  have hVo : IsOpen V := isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  have hn0 : ∀ ζ ∈ V, n ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have h := mem_closedBall.1 (hM₀ hm)
    rw [dist_eq_norm] at h
    have h' : M₀ < ‖ζ - y‖ := hζ
    linarith
  have hdz0 : ∀ {g : ℂ → ℂ}, (∀ ζ ∈ V, g ζ = 0) → ∀ ζ ∈ V, dz g ζ = 0 := by
    intro g hg ζ hζ
    have hev : g =ᶠ[𝓝 ζ] fun _ => (0 : ℂ) := by
      filter_upwards [hVo.mem_nhds hζ] with w hw
      exact hg w hw
    simp only [dz, hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, sub_zero,
      mul_zero, zero_div]
  have hd1 := hdz0 hn0
  have hd2 := hdz0 hd1
  have hRV : ∀ ζ, R ≤ ‖ζ - y‖ → ζ ∈ V := fun ζ hζ => hMR.trans_le hζ
  have hcR : ∀ {g : ℂ → ℂ}, (∀ ζ ∈ V, g ζ = 0) → ∀ θ : ℝ, g (circleMap y R θ) = 0 := by
    intro g hg θ
    apply hg
    apply hRV
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
  have hB2 := s4g_boundary_lim h1 y (k := 2) le_rfl (by norm_num)
  have hB3 := s4g_boundary_lim hn y (k := 3) (by norm_num) le_rfl
  have hlim := hS.sub ((hB2.add (hB3.const_mul 2)).const_mul (-(1 / π : ℂ)))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hr0 : 0 < r := hr.1
  have hc0 : Continuous n := hn.continuous
  have hc1' : Continuous (dz n) := h1.continuous
  have hc2' : Continuous (dz (dz n)) := h2.continuous
  have hA := s4g_annulus_ibp_split h1 hr0 hr.2 (hcR hd1) 2
  have hB := s4g_annulus_ibp_split hn hr0 hr.2 (hcR hn0) 3
  have e2 := (s4g_ann_sets (f := fun ζ => dz (dz n) ζ / (ζ - y) ^ 2) (r := r)
    (fun ζ hζ => by rw [hd2 ζ (hRV ζ hζ), zero_div])).1
  have e4 := (s4g_ann_sets (f := fun ζ => n ζ / (ζ - y) ^ 4) (r := r)
    (fun ζ hζ => by rw [hn0 ζ (hRV ζ hζ), zero_div])).2
  simp only [div_eq_mul_inv] at e2 e4 ⊢
  rw [← e2, ← e4]
  push_cast at hA hB ⊢
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  linear_combination (-(1 / π : ℂ)) * hA + (-(2 / π : ℂ)) * hB

/-- `∂_z` is additive on real-differentiable functions. -/
theorem s4g_dz_add {f g : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun w => f w + g w) x = dz f x + dz g x := by
  simp only [dz, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]
  ring

/-- The quartic kernel is integrable off a disc. -/
theorem s4g_int_kernel4 (y : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun u : ℂ => ((u - y) ^ 4)⁻¹) {u : ℂ | ρ < ‖u - y‖} := by
  have hfin := lintegral_compl_ball_sub_enorm_rpow_neg (a := 4) (by norm_num) hρ y
  have hS : MeasurableSet {u : ℂ | ρ < ‖u - y‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const y).norm
  refine ⟨((measurable_id.sub_const y).pow_const 4).inv.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have he : ∀ u ∈ {u : ℂ | ρ < ‖u - y‖}, ‖((u - y) ^ 4)⁻¹‖ₑ = ‖u - y‖ₑ ^ (-(4 : ℝ)) := by
    intro u hu
    have hne : (u - y) ^ 4 ≠ 0 := by
      apply pow_ne_zero
      intro h0
      have h1 : ρ < ‖u - y‖ := hu
      rw [h0, norm_zero] at h1
      linarith
    rw [enorm_inv hne, enorm_pow, ENNReal.rpow_neg, ENNReal.rpow_ofNat]
  rw [setLIntegral_congr_fun hS he, hfin]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- A bounded coefficient divided by `(u - y)⁴` is integrable off `ball y δ`. -/
theorem s4g_int_compl {g : ℂ → ℂ} {k : ℝ} (hg : IsBeltramiCoeff g univ k) (y : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun u => g u / (u - y) ^ 4) (ball y δ)ᶜ := by
  have hm : AEStronglyMeasurable g volume := by simpa using hg.1
  have hb : ∀ᵐ u : ℂ, ‖g u‖ ≤ k := by simpa using hg.2
  have hsub : (ball y δ)ᶜ ⊆ {u : ℂ | δ / 2 < ‖u - y‖} := by
    intro u hu
    rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hu
    show δ / 2 < ‖u - y‖
    linarith
  have hK := (s4g_int_kernel4 y (half_pos hδ)).mono_set hsub
  have hF : (fun u => g u / (u - y) ^ 4) = fun u => g u * ((u - y) ^ 4)⁻¹ := by
    funext u; rw [div_eq_mul_inv]
  rw [hF]
  exact hK.bdd_mul hm.restrict (ae_restrict_of_ae hb)

/-- One level of the derivative bookkeeping: if `F = T + H` on an open set `B` with `T` real-differentiable and
`H` holomorphic there, then `∂_z F = ∂_z T + H'` on `B`. -/
theorem s4g_dz_step {F T H : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B) (hT : Differentiable ℝ T)
    (hH : DifferentiableOn ℂ H B) (hF : ∀ x ∈ B, F x = T x + H x) :
    ∀ x ∈ B, dz F x = dz T x + deriv H x := by
  intro x hx
  have hev : F =ᶠ[𝓝 x] fun w => T w + H w := by
    filter_upwards [hB.mem_nhds hx] with w hw
    exact hF w hw
  have hHx : DifferentiableAt ℂ H x := hH.differentiableAt (hB.mem_nhds hx)
  rw [show dz F x = dz (fun w => T w + H w) x by simp only [dz, hev.fderiv_eq],
    s4g_dz_add (hT x) (hHx.restrictScalars ℝ), dz_eq_deriv hHx]

/-- Möbius invariance of the cross-ratio kernel: `M'(p) M'(q)/(M p - M q)² = 1/(p - q)²`. -/
theorem s4g_mobius_kernel {a b c d p q : ℂ} (hdet : a * d - b * c ≠ 0) (hp : c * p + d ≠ 0)
    (hq : c * q + d ≠ 0) (hpq : p ≠ q) :
    (a * d - b * c) / (c * p + d) ^ 2 * ((a * d - b * c) / (c * q + d) ^ 2) /
        ((a * p + b) / (c * p + d) - (a * q + b) / (c * q + d)) ^ 2 = 1 / (p - q) ^ 2 := by
  have hsub : (a * p + b) / (c * p + d) - (a * q + b) / (c * q + d) =
      (a * d - b * c) * (p - q) / ((c * p + d) * (c * q + d)) := by
    rw [div_sub_div _ _ hp hq]
    congr 1
    ring
  have hpq' : p - q ≠ 0 := sub_ne_zero.2 hpq
  rw [hsub]
  field_simp

/-- The plane chart and the welding map: on `V = N_κ(𝔻* ∖ pole)`, `g ∘ J` is a Möbius map `M`, so
`g'(J y) J'(y) = M'(y)`, and `J` is injective on `V`. -/
theorem s4g_chart_facts {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U) (hmap : MapsTo J U unitDiscExterior)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      (∀ y ∈ qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf},
        c * y + d ≠ 0 ∧ gsans κ (J y) = (a * y + b) / (c * y + d) ∧
          deriv (gsans κ) (J y) * deriv J y = (a * d - b * c) / (c * y + d) ^ 2) ∧
      InjOn J (qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) := by
  set V := qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf} with hVdef
  have hVo : IsOpen V := s4pv_plane_exterior_isOpen hκ
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  obtain ⟨a, b, c, d, hdet, -, hfac⟩ := S2C.s2c_mobius hκ
  have hg := S2C.s2c_conf_g hκ
  have hMV : ∀ y ∈ V, c * y + d ≠ 0 ∧ gsans κ (J y) = (a * y + b) / (c * y + d) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := hfac x hx.1 hx.2
    exact ⟨h1, by rw [(hchart x hx.1 hx.2).2]; exact h2⟩
  refine ⟨a, b, c, d, hdet, fun y hy => ⟨(hMV y hy).1, (hMV y hy).2, ?_⟩, ?_⟩
  · have hJy : J y ∈ unitDiscExterior := hmap (hVU hy)
    have hgd : HasDerivAt (gsans κ) (deriv (gsans κ) (J y)) (J y) :=
      (hg.1.differentiableAt (wp_exterior_isOpen.mem_nhds hJy)).hasDerivAt
    have hJd : HasDerivAt J (deriv J y) y := (hJ y (hVU hy)).differentiableAt.hasDerivAt
    have h1 := hgd.comp y hJd
    have h2 := bc_mobiusFn_hasDerivAt (a := a) (b := b) (hMV y hy).1
    have heq : mobiusFn a b c d =ᶠ[𝓝 y] (gsans κ ∘ J) := by
      filter_upwards [hVo.mem_nhds hy] with w hw
      simp only [Function.comp_apply, (hMV w hw).2, mobiusFn]
    exact h1.unique (h2.congr_of_eventuallyEq heq.symm)
  · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ h
    rw [(hchart x₁ hx₁.1 hx₁.2).2, (hchart x₂ hx₂.1 hx₂.2).2] at h
    have hfin : ∀ x : ℂ, wAS κ (x : ExtPlane) ≠ extInf → wAS κ (x : ExtPlane) = ((wA κ x : ℂ) : ExtPlane) := by
      intro x hx
      obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.mp hx
      rw [← hu, wA, ← hu, finPart_coe]
    have hS : wAS κ (x₁ : ExtPlane) = wAS κ (x₂ : ExtPlane) := by
      rw [hfin x₁ hx₁.2, hfin x₂ hx₂.2, h]
    have := (wAS_bijective κ).1 hS
    rw [OnePoint.coe_eq_coe] at this
    rw [this]

/-- At most one finite point is sent to `∞` by `w_κ`. -/
theorem s4g_pole_subsingleton (κ : LinfStar) :
    {x : ℂ | wAS κ (x : ExtPlane) = extInf}.Subsingleton := by
  intro x₁ hx₁ x₂ hx₂
  have h : wAS κ (x₁ : ExtPlane) = wAS κ (x₂ : ExtPlane) := by rw [hx₁, hx₂]
  have := (wAS_bijective κ).1 h
  rwa [OnePoint.coe_eq_coe] at this

/-- The transported coefficient vanishes off `V = N_κ(𝔻* ∖ pole)`, except at the image of the pole. -/
theorem s4g_ahT_off {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (μd : LinfStar) {u : ℂ}
    (hu : u ∉ qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf})
    (hp : u ∉ qcv_planeSolution κ '' {x : ℂ | wAS κ (x : ExtPlane) = extInf}) :
    ahT_dot (extB μd) (extB κ) (qcv_planeSolution κ) u = 0 := by
  obtain ⟨x, rfl⟩ := (qcv_planeSolution_bijective hκ).2 u
  have hinv := (qcv_planeSolution_bijective hκ).1.injOn.leftInvOn_invFunOn (mem_univ x)
  have hx : x ∉ unitDiscExterior := by
    intro hx
    by_cases hw : wAS κ (x : ExtPlane) = extInf
    · exact hp ⟨x, hw, rfl⟩
    · exact hu ⟨x, ⟨hx, hw⟩, rfl⟩
  unfold ahT_dot
  rw [hinv, extB, indicator_of_notMem hx, zero_div, zero_mul]

/-- On `V` the transported coefficient is `ν(J y) conj J'(y)/J'(y)` a.e. (P6 transferred to the plane). -/
theorem s4g_ahT_ae {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior)
    {U : Set ℂ} {J : ℂ → ℂ} (hJ : AnalyticOnNhd ℂ J U)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x) :
    ∀ᵐ u : ℂ, u ∈ qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf} →
      ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ) (qcv_planeSolution κ) u =
        ν (J u) * conj (deriv J u) / deriv J u := by
  have hpull := bc_pullback_ae hκ (bc_toLinf_ae (d2_harmonicL2_memLp hν))
  have hsrc : ∀ᵐ x : ℂ ∂(volume.restrict unitDiscExterior),
      wAS κ (x : ExtPlane) ≠ extInf →
        ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ) (qcv_planeSolution κ)
          (qcv_planeSolution κ x) =
        ν (J (qcv_planeSolution κ x)) * conj (deriv J (qcv_planeSolution κ x)) /
          deriv J (qcv_planeSolution κ x) := by
    filter_upwards [s4pv_dot_chart_ae hκ (toLinf ν) hJ hchart, hpull,
      ae_restrict_mem wp_exterior_isOpen.measurableSet] with x hx hrx hxE
    intro hp
    rw [hx hp, hrx, (hchart x hxE hp).2]
  have hN := (qcv_W_props (bc_norm_lt_one hκ)).1
  filter_upwards [(ahT_qmp_inv hN.1 hN.2.1).ae
    ((ae_restrict_iff' wp_exterior_isOpen.measurableSet).mp hsrc)] with y hy
  rintro ⟨x, hx, rfl⟩
  have hinv := (qcv_planeSolution_bijective hκ).1.injOn.leftInvOn_invFunOn (mem_univ x)
  simp only [qcv_planeSolution] at hinv hy
  rw [hinv] at hy
  exact hy hx.1 hx.2

/-- `J(V ∖ B) = 𝔻* ∖ J(B)` up to the single point `w_κ(∞)`. -/
theorem s4g_chart_image_ae {κ : LinfStar} (hκ : κ ∈ LinfStarBall)
    {U : Set ℂ} {J : ℂ → ℂ} (hmap : MapsTo J U unitDiscExterior)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    (hinj : InjOn J (qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}))
    {B : Set ℂ} (hB : B ⊆ qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    J '' (qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf} \ B) =ᵐ[volume]
      (unitDiscExterior \ J '' B : Set ℂ) := by
  set V := qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  have hsub : J '' (V \ B) ⊆ unitDiscExterior \ J '' B := by
    rw [hinj.image_sdiff_subset hB]
    exact fun w hw => ⟨let ⟨v, hv, hvw⟩ := hw.1; hvw ▸ hmap (hVU hv), hw.2⟩
  have hrest : (unitDiscExterior \ J '' B) \ J '' (V \ B) ⊆ {w : ℂ | wAS κ extInf = (w : ExtPlane)} := by
    intro w hw
    by_contra hz₀
    obtain ⟨v, hv, hvw⟩ := s4pv_chart_surjective hκ (fun x hx hp => (hchart x hx hp).2) hw.1.1 hz₀
    by_cases hvB : v ∈ B
    · exact hw.1.2 ⟨v, hvB, hvw⟩
    · exact hw.2 ⟨v, ⟨hv, hvB⟩, hvw⟩
  have hsing : {w : ℂ | wAS κ extInf = (w : ExtPlane)}.Subsingleton := by
    intro w₁ h₁ w₂ h₂
    have h : ((w₁ : ℂ) : ExtPlane) = ((w₂ : ℂ) : ExtPlane) := h₁.symm.trans h₂
    rwa [OnePoint.coe_eq_coe] at h
  have hnull : volume ((unitDiscExterior \ J '' B) \ J '' (V \ B)) = 0 :=
    measure_mono_null hrest (hsing.countable.measure_zero volume)
  refine ae_eq_set.2 ⟨?_, hnull⟩
  rw [Set.diff_eq_empty.2 hsub, measure_empty]

/-- The area of a round annulus. -/
theorem s4g_vol_ann (z : ℂ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    volume.real (ball z a \ ball z b) = π * (a ^ 2 - b ^ 2) := by
  have hsub : ball z b ⊆ ball z a := ball_subset_ball hba
  rw [measureReal_diff hsub measurableSet_ball (measure_ball_lt_top).ne]
  have hr : ∀ r : ℝ, 0 ≤ r → volume.real (ball z r) = π * r ^ 2 := by
    intro r hr
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  rw [hr a (hb.trans hba), hr b hb]
  ring

/-- **The conformal disc is round to first order.** For `J` with strict derivative `J' ≠ 0` at `y`, the excision
`E_δ = J(B(y, δ/|J'|))` lies between `B(J y, δ(1-η))` and `B(J y, δ(1+η))` for small `δ`. -/
theorem s4g_conformal_disc {J : ℂ → ℂ} {J' y : ℂ} (hJ : HasStrictDerivAt J J' y) (hJ0 : J' ≠ 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1 / 2) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), J '' ball y (δ / ‖J'‖) ⊆ ball (J y) (δ * (1 + η)) ∧
      ball (J y) (δ * (1 - η)) ⊆ J '' ball y (δ / ‖J'‖) := by
  have hc : 0 < ‖J'‖ := norm_pos_iff.2 hJ0
  -- the forward estimate
  have hf := hJ.hasDerivAt.hasFDerivAt.isLittleO
  have hf1 := hf.def (show 0 < η * ‖J'‖ by positivity)
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 hf1
  -- the local inverse and its estimate
  set Φ := hJ.localInverse J J' y hJ0
  have hΦd := hJ.to_localInverse hJ0
  have hΦy : Φ (J y) = y := (hJ.eventually_left_inverse hJ0).self_of_nhds
  have hg := hΦd.hasDerivAt.hasFDerivAt.isLittleO
  have hg1 := hg.def (show 0 < η / ‖J'‖ by positivity)
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 hg1
  obtain ⟨ρ₃, hρ₃, hb₃⟩ := Metric.eventually_nhds_iff_ball.1 (hJ.eventually_right_inverse hJ0)
  have hδ0 : 0 < min (ρ₁ * ‖J'‖) (min ρ₂ ρ₃) := lt_min (by positivity) (lt_min hρ₂ hρ₃)
  filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ
  have hδ1 : δ < ρ₁ * ‖J'‖ := hδ.2.trans_le (min_le_left _ _)
  have hδ2 : δ < ρ₂ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : δ < ρ₃ := hδ.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : ‖u - y‖ < δ / ‖J'‖ := by rwa [mem_ball, dist_eq_norm] at hu
    have hu1 : u ∈ ball y ρ₁ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖u - y‖ < δ / ‖J'‖ := hu'
        _ < ρ₁ := by rw [div_lt_iff₀ hc]; exact hδ1
    have h := hb₁ u hu1
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    rw [mem_ball, dist_eq_norm]
    calc ‖J u - J y‖ ≤ ‖J u - J y - (u - y) * J'‖ + ‖(u - y) * J'‖ := by
          have := norm_add_le (J u - J y - (u - y) * J') ((u - y) * J')
          rwa [sub_add_cancel] at this
      _ ≤ η * ‖J'‖ * ‖u - y‖ + ‖u - y‖ * ‖J'‖ := by rw [norm_mul]; exact add_le_add h le_rfl
      _ = ‖u - y‖ * ‖J'‖ * (1 + η) := by ring
      _ < δ / ‖J'‖ * ‖J'‖ * (1 + η) := by gcongr
      _ = δ * (1 + η) := by field_simp
  · intro w hw
    have hw' : ‖w - J y‖ < δ * (1 - η) := by rwa [mem_ball, dist_eq_norm] at hw
    have hwδ : ‖w - J y‖ < δ := hw'.trans_le (by nlinarith [hδ.1])
    have hw2 : w ∈ ball (J y) ρ₂ := by rw [mem_ball, dist_eq_norm]; exact hwδ.trans hδ2
    have hw3 : w ∈ ball (J y) ρ₃ := by rw [mem_ball, dist_eq_norm]; exact hwδ.trans hδ3
    have h := hb₂ w hw2
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    change ‖Φ w - Φ (J y) - (w - J y) * J'⁻¹‖ ≤ η / ‖J'‖ * ‖w - J y‖ at h
    rw [hΦy] at h
    refine ⟨Φ w, ?_, hb₃ w hw3⟩
    rw [mem_ball, dist_eq_norm]
    calc ‖Φ w - y‖ ≤ ‖Φ w - y - (w - J y) * J'⁻¹‖ + ‖(w - J y) * J'⁻¹‖ := by
          have := norm_add_le (Φ w - y - (w - J y) * J'⁻¹) ((w - J y) * J'⁻¹)
          rwa [sub_add_cancel] at this
      _ ≤ η / ‖J'‖ * ‖w - J y‖ + ‖w - J y‖ * ‖J'‖⁻¹ := by
          rw [norm_mul, norm_inv]; exact add_le_add h le_rfl
      _ = ‖w - J y‖ * (1 + η) / ‖J'‖ := by ring
      _ < δ * (1 - η) * (1 + η) / ‖J'‖ := by gcongr
      _ ≤ δ / ‖J'‖ := by
          gcongr
          nlinarith [hδ.1, sq_nonneg η, mul_nonneg hδ.1.le (sq_nonneg η)]

/-- **The sliver lemma.** For `|F(w)| ≤ C/|w - z|²` near `z = J y`, the integrals of `F` over the two crescents
between `B(z, δ)` and `J(B(y, δ/|J'|))` tend to `0`. -/
theorem s4g_sliver_small {J : ℂ → ℂ} {J' y : ℂ} (hJ : HasStrictDerivAt J J' y) (hJ0 : J' ≠ 0)
    {F : ℂ → ℂ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hF : ∀ w, 0 < ‖w - J y‖ → ‖w - J y‖ < ρ → ‖F w‖ ≤ C / ‖w - J y‖ ^ 2) :
    Tendsto (fun δ : ℝ => (∫ w in ball (J y) δ \ J '' ball y (δ / ‖J'‖), F w) -
      ∫ w in J '' ball y (δ / ‖J'‖) \ ball (J y) δ, F w) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := min (1 / 4) (ε / (12 * π * (C + 1))) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hηε : η * (12 * π * (C + 1)) ≤ ε := by
    have h := min_le_right (1 / 4 : ℝ) (ε / (12 * π * (C + 1)))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    exact h
  filter_upwards [s4g_conformal_disc hJ hJ0 hη hη1, Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 2 by positivity)]
    with δ hE hδ
  have hδ0 : 0 < δ := hδ.1
  have hpi : 0 < π := Real.pi_pos
  -- the first crescent lies in the annulus `δ(1-η) ≤ |h| < δ`
  have h1 : ‖∫ w in ball (J y) δ \ J '' ball y (δ / ‖J'‖), F w‖ ≤
      C / (δ * (1 - η)) ^ 2 * (π * (δ ^ 2 - (δ * (1 - η)) ^ 2)) := by
    have hsub : ball (J y) δ \ J '' ball y (δ / ‖J'‖) ⊆ ball (J y) δ \ ball (J y) (δ * (1 - η)) :=
      fun w hw => ⟨hw.1, fun h => hw.2 (hE.2 h)⟩
    calc _ ≤ C / (δ * (1 - η)) ^ 2 * volume.real (ball (J y) δ \ J '' ball y (δ / ‖J'‖)) := by
          refine norm_setIntegral_le_of_norm_le_const
            ((measure_mono (diff_subset.trans ball_subset_closedBall)).trans_lt measure_closedBall_lt_top) ?_
          intro w hw
          have hw1 : ‖w - J y‖ < δ := by have := hw.1; rwa [mem_ball, dist_eq_norm] at this
          have hw2 : δ * (1 - η) ≤ ‖w - J y‖ := by
            have := (hsub hw).2; rwa [mem_ball, dist_eq_norm, not_lt] at this
          have hpos : 0 < δ * (1 - η) := by nlinarith
          calc ‖F w‖ ≤ C / ‖w - J y‖ ^ 2 := hF w (hpos.trans_le hw2) (hw1.trans (by linarith [hδ.2]))
            _ ≤ C / (δ * (1 - η)) ^ 2 := by gcongr
      _ ≤ C / (δ * (1 - η)) ^ 2 * volume.real (ball (J y) δ \ ball (J y) (δ * (1 - η))) := by
          gcongr
          · exact (measure_mono (diff_subset.trans ball_subset_closedBall)).trans_lt
              measure_closedBall_lt_top |>.ne
      _ = _ := by rw [s4g_vol_ann (J y) (by nlinarith) (by nlinarith)]
  -- the second crescent lies in `δ ≤ |h| < δ(1+η)`
  have h2 : ‖∫ w in J '' ball y (δ / ‖J'‖) \ ball (J y) δ, F w‖ ≤
      C / δ ^ 2 * (π * ((δ * (1 + η)) ^ 2 - δ ^ 2)) := by
    have hsub : J '' ball y (δ / ‖J'‖) \ ball (J y) δ ⊆ ball (J y) (δ * (1 + η)) \ ball (J y) δ :=
      fun w hw => ⟨hE.1 hw.1, hw.2⟩
    calc _ ≤ C / δ ^ 2 * volume.real (J '' ball y (δ / ‖J'‖) \ ball (J y) δ) := by
          refine norm_setIntegral_le_of_norm_le_const
            ((measure_mono ((hsub.trans diff_subset).trans ball_subset_closedBall)).trans_lt
              measure_closedBall_lt_top) ?_
          intro w hw
          have hw1 : ‖w - J y‖ < δ * (1 + η) := by
            have := (hsub hw).1; rwa [mem_ball, dist_eq_norm] at this
          have hw2 : δ ≤ ‖w - J y‖ := by
            have := hw.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
          calc ‖F w‖ ≤ C / ‖w - J y‖ ^ 2 := hF w (hδ0.trans_le hw2) (hw1.trans (by nlinarith [hδ.2]))
            _ ≤ C / δ ^ 2 := by gcongr
      _ ≤ C / δ ^ 2 * volume.real (ball (J y) (δ * (1 + η)) \ ball (J y) δ) := by
          gcongr
          · exact (measure_mono (diff_subset.trans ball_subset_closedBall)).trans_lt
              measure_closedBall_lt_top |>.ne
      _ = _ := by rw [s4g_vol_ann (J y) hδ0.le (by nlinarith)]
  have e1 : C / (δ * (1 - η)) ^ 2 * (π * (δ ^ 2 - (δ * (1 - η)) ^ 2)) = C * π * (2 * η - η ^ 2) / (1 - η) ^ 2 := by
    field_simp
    ring
  have e2 : C / δ ^ 2 * (π * ((δ * (1 + η)) ^ 2 - δ ^ 2)) = C * π * (2 * η + η ^ 2) := by
    field_simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  have hb1 : C * π * (2 * η - η ^ 2) / (1 - η) ^ 2 ≤ 8 * π * (C + 1) * η := by
    have hη4 : η ≤ 1 / 4 := min_le_left _ _
    have hq : (9 / 16 : ℝ) ≤ (1 - η) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    calc C * π * (2 * η - η ^ 2) ≤ C * π * (2 * η) := by nlinarith [mul_nonneg hC hpi.le, sq_nonneg η]
      _ ≤ 8 * π * (C + 1) * η * (9 / 16) := by nlinarith [mul_pos hpi hη, mul_nonneg (mul_nonneg hC hpi.le) hη.le]
      _ ≤ 8 * π * (C + 1) * η * (1 - η) ^ 2 := by gcongr
  have hb2 : C * π * (2 * η + η ^ 2) ≤ 3 * π * (C + 1) * η := by
    nlinarith [mul_nonneg hC hpi.le, mul_nonneg (mul_nonneg hC hpi.le) hη.le, mul_pos hpi hη]
  rw [dist_zero_right]
  calc _ ≤ ‖∫ w in ball (J y) δ \ J '' ball y (δ / ‖J'‖), F w‖ +
        ‖∫ w in J '' ball y (δ / ‖J'‖) \ ball (J y) δ, F w‖ := norm_sub_le _ _
    _ ≤ 8 * π * (C + 1) * η + 3 * π * (C + 1) * η := add_le_add (h1.trans hb1) (h2.trans hb2)
    _ < ε := by nlinarith [mul_pos hpi hη]

/-- The Wirtinger chain rule through a holomorphic map: `∂_z (G ∘ J) = (∂_z G ∘ J) J'`. -/
theorem s4g_dz_comp_holo {G J : ℂ → ℂ} {u : ℂ} (hG : DifferentiableAt ℝ G (J u)) (hJ : DifferentiableAt ℂ J u) :
    dz (G ∘ J) u = dz G (J u) * deriv J u := by
  have hJR : HasFDerivAt J ((ContinuousLinearMap.toSpanSingleton ℂ (deriv J u)).restrictScalars ℝ) u :=
    hJ.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := hG.hasFDerivAt.comp u hJR
  have hd : fderiv ℝ (G ∘ J) u = (fderiv ℝ G (J u)).comp
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv J u)).restrictScalars ℝ) := hc.fderiv
  set D := fderiv ℝ G (J u)
  have h1 : fderiv ℝ (G ∘ J) u 1 = D (deriv J u) := by
    rw [hd]; simp
  have hI : fderiv ℝ (G ∘ J) u I = D (deriv J u * I) := by
    rw [hd]; simp [mul_comm]
  show (fderiv ℝ (G ∘ J) u 1 - I * fderiv ℝ (G ∘ J) u I) / 2 = (D 1 - I * D I) / 2 * deriv J u
  rw [h1, hI, s4g_rlin_decomp D (deriv J u), s4g_rlin_decomp D (deriv J u * I)]
  simp only [map_mul, conj_I]
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  ring_nf
  rw [h3]
  ring_nf
  rw [I_sq]
  ring

/-- `∂_z` of the conjugate of a holomorphic function vanishes. -/
theorem s4g_dz_conj_holo {f : ℂ → ℂ} {u : ℂ} (hf : DifferentiableAt ℂ f u) :
    dz (fun v => conj (f v)) u = 0 := by
  have hR : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f u)).restrictScalars ℝ) u :=
    hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp u hR
  have hd := hc.fderiv
  show (fderiv ℝ (fun v => conj (f v)) u 1 - I * fderiv ℝ (fun v => conj (f v)) u I) / 2 = 0
  have heq : (fun v => conj (f v)) = (Complex.conjCLE.toContinuousLinearMap) ∘ f := rfl
  rw [heq, hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_mul, conj_I, one_smul, map_one, mul_one]
  ring_nf
  rw [I_sq]
  ring

/-- The `∂_z` Green identity on an annulus, for `ω` that is `C¹` off the centre and vanishes on the outer circle. -/
theorem s4g_annulus_green0 {ω : ℂ → ℂ} {z : ℂ} (hω : ∀ u, u ≠ z → ContDiffAt ℝ 1 ω u) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hvan : ∀ θ : ℝ, ω (circleMap z R θ) = 0) :
    ∫ ζ in ball z R \ ball z r, dz ω ζ =
      (∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * conj (deriv (circleMap z r) θ)) / (2 * I) := by
  set b : ContDiffBump z := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hb
  set χ : ℂ → ℂ := fun w => 1 - ((b w : ℝ) : ℂ) with hχ
  have hχs : ContDiff ℝ 1 χ := contDiff_const.sub (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hχ0 : ∀ w ∈ ball z (r / 4), χ w = 0 := by
    intro w hw
    have h1 : b w = 1 := b.one_of_mem_closedBall (by
      simp only [hb, Metric.mem_closedBall]; exact le_of_lt (Metric.mem_ball.1 hw))
    simp [hχ, h1]
  have hχ1 : ∀ w : ℂ, r / 2 ≤ ‖w - z‖ → χ w = 1 := by
    intro w hw
    have h0 : b w = 0 := b.zero_of_le_dist (by simpa only [hb, dist_eq_norm] using hw)
    simp [hχ, h0]
  set ω' : ℂ → ℂ := fun w => χ w * ω w with hω'
  have hω's : ContDiff ℝ 1 ω' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x z with rfl | hx
    · have hev : ω' =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [ball_mem_nhds x (by positivity : (0 : ℝ) < r / 4)] with w hw
        simp [hω', hχ0 w hw]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact hχs.contDiffAt.mul (hω x hx)
  have hvan' : ∀ θ : ℝ, ω' (circleMap z R θ) = 0 := fun θ => by simp [hω', hvan θ]
  have h := s4g_annulus_ibp hω's hr hrR hvan' 0
  simp only [pow_zero, inv_one, mul_one, CharP.cast_eq_zero, zero_mul, sub_zero] at h
  have hc : ∀ θ : ℝ, ω' (circleMap z r θ) = ω (circleMap z r θ) := by
    intro θ
    have h1 : r / 2 ≤ ‖circleMap z r θ - z‖ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]; linarith
    simp [hω', hχ1 _ h1]
  simp only [hc] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) fun ζ hζ => ?_
  have hge : r ≤ ‖ζ - z‖ := by
    have := hζ.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hev : ω =ᶠ[𝓝 ζ] ω' := by
    have hopen : IsOpen {w : ℂ | r / 2 < ‖w - z‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    filter_upwards [hopen.mem_nhds (show r / 2 < ‖ζ - z‖ by linarith)] with w hw
    simp [hω', hχ1 w hw.le]
  simp only [dz, hev.fderiv_eq]

/-- **Green's identity off a conformal disc.** For `J` holomorphic and injective on `B(y, 2ρ)` and `G` `C¹` off
`J y`, vanishing off `J(B(y, ρ/2))`, the integral of `∂_z G` off `J(B(y, r))` is a round boundary term in the chart:
`(1/2i) ∮_{|u - y| = r} G(J u) conj J'(u) dū`. -/
theorem s4g_conformal_green {J : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJa : AnalyticOnNhd ℂ J (ball y (2 * ρ))) (hinj : InjOn J (ball y (2 * ρ)))
    {G : ℂ → ℂ} (hG : ∀ w, w ≠ J y → ContDiffAt ℝ 1 G w)
    (hsupp : ∀ w, w ∉ J '' ball y (ρ / 2) → G w = 0) {r : ℝ} (hr : 0 < r) (hrρ : r < ρ / 2) :
    ∫ w in (J '' ball y r)ᶜ, dz G w =
      (∫ θ in (0 : ℝ)..2 * π, G (J (circleMap y r θ)) * conj (deriv J (circleMap y r θ)) *
        conj (deriv (circleMap y r) θ)) / (2 * I) := by
  have hJc : ContinuousOn J (ball y (2 * ρ)) := hJa.continuousOn
  have hsubρ : ball y ρ ⊆ ball y (2 * ρ) := ball_subset_ball (by linarith)
  have hsubr : ball y r ⊆ ball y ρ := ball_subset_ball (by linarith)
  -- measurability of conformal images
  have hmeasJ : ∀ {s : Set ℂ}, MeasurableSet s → s ⊆ ball y (2 * ρ) → MeasurableSet (J '' s) :=
    fun hs hs2 => hs.image_of_continuousOn_injOn (hJc.mono hs2) (hinj.mono hs2)
  have hEr : MeasurableSet (J '' ball y r) := hmeasJ measurableSet_ball (hsubr.trans hsubρ)
  -- `∂_z G = 0` off `J(B(y, ρ))`
  have hKc : IsCompact (J '' closedBall y (ρ / 2)) :=
    (isCompact_closedBall y (ρ / 2)).image_of_continuousOn
      (hJc.mono (closedBall_subset_ball (by linarith)))
  have hdz0 : ∀ w, w ∉ J '' ball y ρ → dz G w = 0 := by
    intro w hw
    have hwK : w ∉ J '' closedBall y (ρ / 2) := fun h =>
      hw (image_mono (closedBall_subset_ball (by linarith)) h)
    have hev : G =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hwK] with v hv
      exact hsupp v fun h => hv (image_mono ball_subset_closedBall h)
    simp only [dz, hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
      sub_zero, mul_zero, zero_div]
  have hA : MeasurableSet (ball y ρ \ ball y r) := measurableSet_ball.diff measurableSet_ball
  have hstep1 : (∫ w in (J '' ball y r)ᶜ, dz G w) = ∫ w in J '' (ball y ρ \ ball y r), dz G w := by
    rw [hinj.mono hsubρ |>.image_sdiff_subset hsubr]
    have hsub : J '' ball y ρ \ J '' ball y r ⊆ (J '' ball y r)ᶜ := fun w hw => hw.2
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) (f := dz G) hEr.compl hsub
      (fun w hw => hdz0 w (fun h => hw.2 ⟨h, hw.1⟩)))
  -- change of variables
  have hder : ∀ u ∈ ball y ρ \ ball y r, HasFDerivWithinAt J
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv J u)).restrictScalars ℝ) (ball y ρ \ ball y r) u :=
    fun u hu => ((hJa u (hsubρ hu.1)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hA hder
    ((hinj.mono hsubρ).mono sdiff_subset) (dz G)
  simp only [det_restrictScalars_toSpanSingleton] at hcv
  -- the chart function
  set ω : ℂ → ℂ := fun u => if u ∈ ball y (2 * ρ) then G (J u) * conj (deriv J u) else 0 with hωdef
  have hω_eq : ∀ u ∈ ball y (2 * ρ), ω u = G (J u) * conj (deriv J u) := fun u hu => if_pos hu
  have hω0 : ∀ u, ρ / 2 ≤ ‖u - y‖ → ω u = 0 := by
    intro u hu
    by_cases h2 : u ∈ ball y (2 * ρ)
    · rw [hω_eq u h2]
      have : G (J u) = 0 := by
        apply hsupp
        rintro ⟨v, hv, hvu⟩
        have := hinj (ball_subset_ball (by linarith) hv) h2 hvu
        rw [this, mem_ball, dist_eq_norm] at hv
        linarith
      rw [this, zero_mul]
    · exact if_neg h2
  have hωs : ∀ u, u ≠ y → ContDiffAt ℝ 1 ω u := by
    intro u hu
    by_cases hlt : ‖u - y‖ < ρ
    · have hu2 : u ∈ ball y (2 * ρ) := by rw [mem_ball, dist_eq_norm]; linarith
      have hev : ω =ᶠ[𝓝 u] fun v => G (J v) * conj (deriv J v) := by
        filter_upwards [isOpen_ball.mem_nhds hu2] with v hv
        exact hω_eq v hv
      have hJu : J u ≠ J y := fun h => hu (hinj hu2 (mem_ball_self (by positivity)) h)
      have h1 : ContDiffAt ℝ 1 (fun v => G (J v)) u :=
        (hG (J u) hJu).comp u ((hJa u hu2).contDiffAt.restrict_scalars ℝ |>.of_le le_top)
      have h2 : ContDiffAt ℝ 1 (fun v => conj (deriv J v)) u :=
        Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp u
          (((hJa.deriv u hu2).contDiffAt).restrict_scalars ℝ |>.of_le le_top)
      exact (h1.mul h2).congr_of_eventuallyEq hev
    · have hev : ω =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
        have hopen : IsOpen {v : ℂ | ρ / 2 < ‖v - y‖} :=
          isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
        filter_upwards [hopen.mem_nhds (show ρ / 2 < ‖u - y‖ by linarith [not_lt.1 hlt])] with v hv
        exact hω0 v hv.le
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hvan : ∀ θ : ℝ, ω (circleMap y ρ θ) = 0 := fun θ => hω0 _ (by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]; linarith)
  have hgreen := s4g_annulus_green0 hωs hr (by linarith : r < ρ) hvan
  -- pointwise identification
  have hpt : ∀ u ∈ ball y ρ \ ball y r, |‖deriv J u‖ ^ 2| • dz G (J u) = dz ω u := by
    intro u hu
    have hu2 : u ∈ ball y (2 * ρ) := hsubρ hu.1
    have huy : u ≠ y := fun h => hu.2 (h ▸ mem_ball_self hr)
    have hJu : J u ≠ J y := fun h => huy (hinj hu2 (mem_ball_self (by positivity)) h)
    have hev : ω =ᶠ[𝓝 u] fun v => G (J v) * conj (deriv J v) := by
      filter_upwards [isOpen_ball.mem_nhds hu2] with v hv
      exact hω_eq v hv
    have hGd : DifferentiableAt ℝ G (J u) := (hG (J u) hJu).differentiableAt one_ne_zero
    have hJd : DifferentiableAt ℂ J u := (hJa u hu2).differentiableAt
    have hJ'd : DifferentiableAt ℂ (deriv J) u := (hJa.deriv u hu2).differentiableAt
    have hd1 : DifferentiableAt ℝ (fun v => G (J v)) u := hGd.comp u (hJd.restrictScalars ℝ)
    have hd2 : DifferentiableAt ℝ (fun v => conj (deriv J v)) u :=
      (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp u (hJ'd.restrictScalars ℝ)
    rw [show dz ω u = dz (fun v => G (J v) * conj (deriv J v)) u by simp only [dz, hev.fderiv_eq],
      dz_mul hd1 hd2, s4g_dz_conj_holo hJ'd]
    have hc := s4g_dz_comp_holo hGd hJd
    simp only [Function.comp_def] at hc
    rw [hc, abs_of_nonneg (sq_nonneg _), Complex.real_smul]
    have hn : ((‖deriv J u‖ ^ 2 : ℝ) : ℂ) = deriv J u * conj (deriv J u) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hn]
    ring
  have hc2 : ∀ θ : ℝ, ω (circleMap y r θ) = G (J (circleMap y r θ)) * conj (deriv J (circleMap y r θ)) := by
    intro θ
    apply hω_eq
    rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    linarith
  rw [hstep1, hcv, setIntegral_congr_fun hA hpt, hgreen]
  simp only [hc2]

/-- **The conformal boundary terms vanish.** For `J` holomorphic near `y` with `J'(y) ≠ 0`, `n ∈ C^∞` and
`k ∈ {2, 3}`, `(1/2i) ∮_{|u - y| = r} n(J u) (J u - J y)^{-k} conj J'(u) dū → 0` as `r → 0⁺`. -/
theorem s4g_conformal_boundary_lim {J : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJa : AnalyticOnNhd ℂ J (ball y (2 * ρ))) (hJ0 : deriv J y ≠ 0)
    {n : ℂ → ℂ} (hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n) {k : ℕ} (hk2 : 2 ≤ k) (hk3 : k ≤ 3) :
    Tendsto (fun r : ℝ => (∫ θ in (0 : ℝ)..2 * π, n (J (circleMap y r θ)) *
      ((J (circleMap y r θ) - J y) ^ k)⁻¹ * conj (deriv J (circleMap y r θ)) *
        conj (deriv (circleMap y r) θ)) / (2 * I)) (𝓝[>] 0) (𝓝 0) := by
  have hpi : 0 < π := Real.pi_pos
  have hB2 : ball y (2 * ρ) ∈ 𝓝 y := ball_mem_nhds y (by positivity)
  set H := dslope J y with hHdef
  have hH : DifferentiableOn ℂ H (ball y (2 * ρ)) :=
    (Complex.differentiableOn_dslope hB2).2 hJa.differentiableOn
  have hHy : H y ≠ 0 := by rw [hHdef, dslope_same]; exact hJ0
  have hHc : ContinuousAt H y := (hH.differentiableAt hB2).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁H⟩ := Metric.eventually_nhds_iff_ball.1 (hHc.eventually_ne hHy)
  set ρ₀ : ℝ := min ρ₁ ρ with hρ₀
  have hρ₀p : 0 < ρ₀ := lt_min hρ₁ hρ
  have hsub₀ : ball y ρ₀ ⊆ ball y (2 * ρ) := ball_subset_ball (by rw [hρ₀]; linarith [min_le_right ρ₁ ρ])
  -- the smooth amplitude and a global extension
  set f : ℂ → ℂ := fun u => n (J u) * ((H u) ^ k)⁻¹ * conj (deriv J u) with hfdef
  have hfs : ∀ u ∈ ball y ρ₀, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f u := by
    intro u hu
    have hu2 := hsub₀ hu
    have hHu : H u ≠ 0 := hρ₁H u (ball_subset_ball (min_le_left _ _) hu)
    have hJs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J u := ((hJa u hu2).contDiffAt).restrict_scalars ℝ |>.of_le le_top
    have hHs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H u :=
      ((hH.analyticOnNhd isOpen_ball u hu2).contDiffAt).restrict_scalars ℝ |>.of_le le_top
    have hJ's : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) u :=
      ((hJa.deriv u hu2).contDiffAt).restrict_scalars ℝ |>.of_le le_top
    exact ((hn.contDiffAt.comp u hJs).mul ((hHs.pow k).inv (pow_ne_zero k hHu))).mul
      (Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt.comp u hJ's)
  set b : ContDiffBump y := ⟨ρ₀ / 4, ρ₀ / 2, by positivity, by linarith⟩ with hb
  set f' : ℂ → ℂ := fun u => ((b u : ℝ) : ℂ) * f u with hf'def
  have hf's : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x - y‖ < ρ₀
    · exact (Complex.ofRealCLM.contDiff.comp b.contDiff).contDiffAt.mul
        (hfs x (by rw [mem_ball, dist_eq_norm]; exact hx))
    · have hopen : IsOpen {u : ℂ | ρ₀ / 2 < ‖u - y‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      have hev : f' =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds (show ρ₀ / 2 < ‖x - y‖ by linarith [not_lt.1 hx])] with u hu
        have h0 : b u = 0 := b.zero_of_le_dist (by simpa only [hb, dist_eq_norm] using hu.le)
        simp [hf'def, h0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  obtain ⟨ρ₂, hρ₂, L, hL, hF⟩ := s4g_fourier_cubic hf's y (j := (k : ℤ) + 1) (by omega)
  -- the bound `π L r` for small `r`
  have hbound : ∀ r : ℝ, 0 < r → r < min (min (ρ₀ / 4) ρ₂) 1 →
      ‖(∫ θ in (0 : ℝ)..2 * π, n (J (circleMap y r θ)) * ((J (circleMap y r θ) - J y) ^ k)⁻¹ *
        conj (deriv J (circleMap y r θ)) * conj (deriv (circleMap y r) θ)) / (2 * I)‖ ≤ π * L * r := by
    intro r hr hrm
    have hr4 : r < ρ₀ / 4 := hrm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hr2 : r < ρ₂ := hrm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hr1 : r < 1 := hrm.trans_le (min_le_right _ _)
    set E : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I) with hEdef
    have hE0 : ∀ θ, E θ ≠ 0 := fun θ => Complex.exp_ne_zero _
    have hconjE : ∀ θ, conj (E θ) = E θ ^ (-1 : ℤ) := by
      intro θ
      simp only [hEdef, zpow_neg_one, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ← Complex.exp_neg]
      congr 1
      ring
    have hpt : ∀ θ : ℝ, n (J (circleMap y r θ)) * ((J (circleMap y r θ) - J y) ^ k)⁻¹ *
        conj (deriv J (circleMap y r θ)) * conj (deriv (circleMap y r) θ) =
        -I * (r * ((r : ℂ) ^ k)⁻¹) * (f' (y + r * E θ) * E θ ^ (-((k : ℤ) + 1))) := by
      intro θ
      have hcm : circleMap y r θ = y + r * E θ := rfl
      have hd : deriv (circleMap y r) θ = r * E θ * I := by rw [deriv_circleMap, circleMap, zero_add]
      have hmem : ‖(y + r * E θ) - y‖ < ρ₀ / 4 := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hEdef,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hr4
      have hb1 : b (y + r * E θ) = 1 := b.one_of_mem_closedBall (by
        simp only [hb, Metric.mem_closedBall, dist_eq_norm]; linarith)
      have hsl := sub_smul_dslope J y (y + r * E θ)
      rw [add_sub_cancel_left, smul_eq_mul] at hsl
      have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
      have hEj : E θ ^ (-((k : ℤ) + 1)) = (E θ ^ k)⁻¹ * E θ ^ (-1 : ℤ) := by
        rw [neg_add, zpow_add₀ (hE0 θ), zpow_neg, zpow_natCast]
      rw [hcm, hd, ← hsl, hf'def, hfdef]
      simp only [hb1, ofReal_one, one_mul, map_mul, conj_ofReal, conj_I, hconjE, hEj, ← hHdef]
      simp only [mul_pow, mul_inv]
      ring
    have hint : (∫ θ in (0 : ℝ)..2 * π, n (J (circleMap y r θ)) * ((J (circleMap y r θ) - J y) ^ k)⁻¹ *
        conj (deriv J (circleMap y r θ)) * conj (deriv (circleMap y r) θ)) =
        -I * (r * ((r : ℂ) ^ k)⁻¹) * ∫ θ in (0 : ℝ)..2 * π, f' (y + r * E θ) * E θ ^ (-((k : ℤ) + 1)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun θ _ => hpt θ
    rw [hint, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_inv, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
    have h2I : ‖(2 * I : ℂ)‖ = 2 := by simp
    rw [h2I]
    have hFr := hF r hr hr2
    have hrk0 : 0 < r ^ k := pow_pos hr k
    have hk' : r ^ 3 = r ^ k * r ^ (3 - k) := by rw [← pow_add]; congr 1; omega
    have hle : r ^ (3 - k) ≤ 1 := pow_le_one₀ hr.le hr1.le
    calc r * (r ^ k)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, f' (y + r * E θ) * E θ ^ (-((k : ℤ) + 1))‖ / 2
        ≤ r * (r ^ k)⁻¹ * (L * r ^ 3 * (2 * π)) / 2 := by gcongr
      _ ≤ π * L * r := by
          rw [hk']
          field_simp
          nlinarith [mul_nonneg hL hr.le, mul_nonneg (mul_nonneg hL hr.le) hpi.le, pow_nonneg hr.le (3 - k)]
  have hlim : Tendsto (fun r : ℝ => π * L * r) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => π * L * r := continuous_const.mul continuous_id
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (lt_min (lt_min (by positivity : (0 : ℝ) < ρ₀ / 4) hρ₂) one_pos)] with r hr hr'
  exact hbound r hr hr'.2

/-- A compactly supported continuous function against `(ζ - z)^{-k}` is integrable off any disc. -/
theorem s4g_int_compl_cs {g : ℂ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) {s : ℝ}
    (hs : 0 < s) (k : ℕ) : IntegrableOn (fun ζ => g ζ * ((ζ - z) ^ k)⁻¹) (ball z s)ᶜ := by
  obtain ⟨M₀, hM₀⟩ := hgc.isCompact.isBounded.subset_closedBall z
  set R : ℝ := max M₀ s + 1
  refine (s4g_int_ann hg z hs (R := R) k).of_forall_sdiff_eq_zero measurableSet_ball.compl ?_
  intro ζ hζ
  have hζR : ζ ∉ ball z R := fun h => hζ.2 ⟨h, hζ.1⟩
  have hg0 : g ζ = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have h1 := mem_closedBall.1 (hM₀ hm)
    rw [mem_ball, not_lt, dist_eq_norm] at hζR
    rw [dist_eq_norm] at h1
    linarith [le_max_left M₀ s]
  simp [hg0]

/-- Swapping two excisions: `∫_{Eᶜ} F - ∫_{Bᶜ} F = ∫_{B ∖ E} F - ∫_{E ∖ B} F`. -/
theorem s4g_swap {F : ℂ → ℂ} {E B : Set ℂ} (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hF : IntegrableOn F (E ∩ B)ᶜ) :
    (∫ w in Eᶜ, F w) - ∫ w in Bᶜ, F w = (∫ w in B \ E, F w) - ∫ w in E \ B, F w := by
  have h1 : Eᶜ = (Eᶜ ∩ Bᶜ) ∪ (B \ E) := by ext w; by_cases hw : w ∈ B <;> simp [hw]
  have h2 : Bᶜ = (Eᶜ ∩ Bᶜ) ∪ (E \ B) := by ext w; by_cases hw : w ∈ E <;> simp [hw]
  have hs : ∀ {S : Set ℂ}, S ⊆ (E ∩ B)ᶜ → IntegrableOn F S := fun hS => hF.mono_set hS
  have hd1 : Disjoint (Eᶜ ∩ Bᶜ) (B \ E) := by
    rw [Set.disjoint_left]; intro w hw hw'; exact hw.2 hw'.1
  have hd2 : Disjoint (Eᶜ ∩ Bᶜ) (E \ B) := by
    rw [Set.disjoint_left]; intro w hw hw'; exact hw.1 hw'.1
  have hsub0 : Eᶜ ∩ Bᶜ ⊆ (E ∩ B)ᶜ := fun w hw h => hw.1 h.1
  have hsub1 : B \ E ⊆ (E ∩ B)ᶜ := fun w hw h => hw.2 h.1
  have hsub2 : E \ B ⊆ (E ∩ B)ᶜ := fun w hw h => hw.2 h.2
  have e1 : (∫ w in Eᶜ, F w) = (∫ w in Eᶜ ∩ Bᶜ, F w) + ∫ w in B \ E, F w := by
    conv_lhs => rw [h1]
    exact setIntegral_union hd1 (hB.diff hE) (hs hsub0) (hs hsub1)
  have e2 : (∫ w in Bᶜ, F w) = (∫ w in Eᶜ ∩ Bᶜ, F w) + ∫ w in E \ B, F w := by
    conv_lhs => rw [h2]
    exact setIntegral_union hd2 (hE.diff hB) (hs hsub0) (hs hsub2)
  rw [e1, e2]
  ring

/-- **The near part with a conformal excision.** For `J` holomorphic and injective on `B(y, 2ρ)` with
`J'(y) ≠ 0`, and `n ∈ C^∞_c` supported in `J(B(y, ρ/2))`, the fourth-order integrals of `n` off
`J(B(y, δ/|J'(y)|))` and off `B(J y, δ)` have the same limit. -/
theorem s4g_near_conf {J : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJa : AnalyticOnNhd ℂ J (ball y (2 * ρ))) (hinj : InjOn J (ball y (2 * ρ))) (hJ0 : deriv J y ≠ 0)
    {n : ℂ → ℂ} (hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n) (hc : HasCompactSupport n)
    (hsupp : tsupport n ⊆ J '' ball y (ρ / 2)) :
    Tendsto (fun δ : ℝ => (∫ u in (J '' ball y (δ / ‖deriv J y‖))ᶜ, n u / (u - J y) ^ 4) -
      ∫ u in (ball (J y) δ)ᶜ, n u / (u - J y) ^ 4) (𝓝[>] 0) (𝓝 0) := by
  set z := J y with hz
  set c := ‖deriv J y‖ with hcdef
  have hc0 : 0 < c := norm_pos_iff.2 hJ0
  have hy2 : y ∈ ball y (2 * ρ) := mem_ball_self (by positivity)
  have hJs : HasStrictDerivAt J (deriv J y) y := (hJa y hy2).hasStrictDerivAt
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz n) := dz_contDiff hn
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz (dz n)) := dz_contDiff h1
  have hc1 : HasCompactSupport (dz n) := wr_dz_hasCompactSupport hc
  have hc2 : HasCompactSupport (dz (dz n)) := wr_dz_hasCompactSupport hc1
  -- the round limit and the scaled radius
  have hround := s4g_cauchyT_dz3_pv hn hc z
  have hsc : Tendsto (fun δ : ℝ => δ / c) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := ((continuous_id.div_const c).tendsto (0 : ℝ))
      simp only [id, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ hc0
  -- the second-order term with the conformal excision
  obtain ⟨C₂, hC₂⟩ := hc2.exists_bound_of_continuous h2.continuous
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ 0)
  have hsl := s4g_sliver_small hJs hJ0 (F := fun w => dz (dz n) w * ((w - z) ^ 2)⁻¹) hC₂0 one_pos
    (fun w hw _ => by
      rw [norm_mul, norm_inv, norm_pow, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hC₂ w) (by positivity))
  have hS := tendsto_truncated_cauchyT_dz (h2.of_le hone) hc2 z
  have hset : ∀ δ : ℝ, (∫ ζ in {ζ : ℂ | δ < ‖ζ - z‖}, dz (dz n) ζ / (ζ - z) ^ 2) =
      ∫ w in (ball z δ)ᶜ, dz (dz n) w * ((w - z) ^ 2)⁻¹ := by
    intro δ
    simp only [div_eq_mul_inv]
    refine setIntegral_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · have : {ζ : ℂ | δ < ‖ζ - z‖} \ (ball z δ)ᶜ = ∅ := by
        ext w
        constructor
        · rintro ⟨h1, h2⟩
          exfalso
          apply h2
          intro h3
          have h1' : δ < ‖w - z‖ := h1
          rw [mem_ball, dist_eq_norm] at h3
          linarith
        · intro h; exact h.elim
      rw [this, measure_empty]
    · refine measure_mono_null ?_ (Measure.addHaar_sphere (volume : Measure ℂ) z δ)
      rintro w ⟨h1, h2⟩
      have h1' : δ ≤ ‖w - z‖ := by
        have := h1; rw [Set.mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at this; exact this
      have h2' : ¬ δ < ‖w - z‖ := h2
      rw [mem_sphere, dist_eq_norm]
      linarith [not_lt.1 h2']
  have hS' : Tendsto (fun δ : ℝ => -(1 / π : ℂ) * ∫ w in (ball z δ)ᶜ, dz (dz n) w * ((w - z) ^ 2)⁻¹)
      (𝓝[>] 0) (𝓝 (cauchyT (dz (dz (dz n))) z)) := by
    simp only [← hset]
    exact hS
  -- eventually `E_δ ⊇ B(z, δ/2)` and `r = δ/c < ρ/2`
  have hevE := s4g_conformal_disc hJs hJ0 (η := 1 / 4) (by norm_num) (by norm_num)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), J '' ball y (δ / c) ⊆ ball z (δ * (1 + 1 / 4)) ∧
      ball z (δ * (1 - 1 / 4)) ⊆ J '' ball y (δ / c) ∧ 0 < δ ∧ δ / c < ρ / 2 := by
    filter_upwards [hevE, Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 2 * c by positivity)] with δ hE hδ
    exact ⟨hE.1, hE.2, hδ.1, by rw [div_lt_iff₀ hc0]; exact hδ.2⟩
  -- the boundary terms
  have hBd2 := (s4g_conformal_boundary_lim hρ hJa hJ0 h1 (k := 2) le_rfl (by norm_num)).comp hsc
  have hBd3 := (s4g_conformal_boundary_lim hρ hJa hJ0 hn (k := 3) (by norm_num) le_rfl).comp hsc
  have hlimE : Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ u in (J '' ball y (δ / c))ᶜ, n u / (u - z) ^ 4)
      (𝓝[>] 0) (𝓝 (cauchyT (dz (dz (dz n))) z)) := by
    have hlim := (hS'.add (hsl.const_mul (-(1 / π : ℂ)))).sub
      ((hBd2.add (hBd3.const_mul 2)).const_mul (-(1 / π : ℂ)))
    simp only [mul_zero, add_zero, sub_zero] at hlim
    apply hlim.congr'
    filter_upwards [hev] with δ hδ
    obtain ⟨-, hE2, hδ0, hr⟩ := hδ
    have hr0 : 0 < δ / c := div_pos hδ0 hc0
    have hEm : MeasurableSet (J '' ball y (δ / c)) :=
      measurableSet_ball.image_of_continuousOn_injOn
        (hJa.continuousOn.mono (ball_subset_ball (by linarith)))
        (hinj.mono (ball_subset_ball (by linarith)))
    have hzE : z ∈ J '' ball y (δ / c) := ⟨y, mem_ball_self hr0, rfl⟩
    have hEc : (J '' ball y (δ / c))ᶜ ⊆ (ball z (δ / 2))ᶜ := by
      intro w hw hwb
      have hd : dist w z < δ / 2 := hwb
      exact hw (hE2 (show dist w z < δ * (1 - 1 / 4) by linarith))
    have hint : ∀ {g : ℂ → ℂ}, Continuous g → HasCompactSupport g → ∀ k : ℕ,
        IntegrableOn (fun ζ => g ζ * ((ζ - z) ^ k)⁻¹) (J '' ball y (δ / c))ᶜ :=
      fun hg hgc k => (s4g_int_compl_cs hg hgc z (by positivity) k).mono_set hEc
    -- the swap for the second-order term
    have hsw := s4g_swap (F := fun w => dz (dz n) w * ((w - z) ^ 2)⁻¹) hEm measurableSet_ball
      ((s4g_int_compl_cs h2.continuous hc2 z (by positivity : (0 : ℝ) < δ / 2) 2).mono_set (by
        intro w hw hwb
        have hd : dist w z < δ / 2 := hwb
        exact hw ⟨hE2 (show dist w z < δ * (1 - 1 / 4) by linarith), show dist w z < δ by linarith⟩))
    -- the two conformal Green identities
    have hvan : ∀ {g : ℂ → ℂ}, tsupport g ⊆ tsupport n → ∀ w, w ∉ J '' ball y (ρ / 2) → g w = 0 :=
      fun hg w hw => image_eq_zero_of_notMem_tsupport fun hm => hw (hsupp (hg hm))
    have hts1 : tsupport (dz n) ⊆ tsupport n := by
      intro w hw
      by_contra hwn
      have hev0 : n =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [(isClosed_tsupport n).isOpen_compl.mem_nhds hwn] with v hv
        exact image_eq_zero_of_notMem_tsupport hv
      have hdz : ∀ᶠ v in 𝓝 w, dz n v = 0 := by
        filter_upwards [(isClosed_tsupport n).isOpen_compl.mem_nhds hwn] with v hv
        have hev1 : n =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [(isClosed_tsupport n).isOpen_compl.mem_nhds hv] with v' hv'
          exact image_eq_zero_of_notMem_tsupport hv'
        simp only [dz, hev1.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
          ContinuousLinearMap.zero_apply, sub_zero, mul_zero, zero_div]
      exact (notMem_tsupport_iff_eventuallyEq.2 hdz) hw
    have hGs : ∀ {g : ℂ → ℂ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ k : ℕ, ∀ w, w ≠ J y →
        ContDiffAt ℝ 1 (fun v => g v * ((v - z) ^ k)⁻¹) w := by
      intro g hg k w hw
      exact (hg.of_le hone).contDiffAt.mul
        (((contDiffAt_id.sub contDiffAt_const).pow k).inv (pow_ne_zero _ (sub_ne_zero.2 hw)))
    have hG2 := s4g_conformal_green hρ hJa hinj (G := fun v => dz n v * ((v - z) ^ 2)⁻¹) (hGs h1 2)
      (fun w hw => by simp [hvan hts1 w hw]) hr0 hr
    have hG3 := s4g_conformal_green hρ hJa hinj (G := fun v => n v * ((v - z) ^ 3)⁻¹) (hGs hn 3)
      (fun w hw => by simp [hvan subset_rfl w hw]) hr0 hr
    have hdzG : ∀ {g : ℂ → ℂ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ k : ℕ, ∀ w, w ≠ z →
        dz (fun v => g v * ((v - z) ^ k)⁻¹) w =
          dz g w * ((w - z) ^ k)⁻¹ - (k : ℂ) * g w * ((w - z) ^ (k + 1))⁻¹ := by
      intro g hg k w hw
      have hdinv : DifferentiableAt ℝ (fun v : ℂ => ((v - z) ^ k)⁻¹) w :=
        ((((differentiableAt_id.sub_const z).pow k).inv
          (pow_ne_zero k (sub_ne_zero.2 hw))) : DifferentiableAt ℂ _ w).restrictScalars ℝ
      rw [dz_mul ((hg.differentiable (by simp)) w) hdinv, s4g_dz_inv_pow hw]
      ring
    have hEm' := hEm.compl
    rw [setIntegral_congr_fun hEm' (fun w hw => hdzG h1 2 w (fun h => hw (h ▸ hzE)))] at hG2
    rw [setIntegral_congr_fun hEm' (fun w hw => hdzG hn 3 w (fun h => hw (h ▸ hzE)))] at hG3
    rw [integral_sub (hint h2.continuous hc2 2)
      (IntegrableOn.congr_fun ((hint h1.continuous hc1 3).const_mul ((2 : ℕ) : ℂ))
        (fun w _ => by ring) hEm')] at hG2
    rw [integral_sub (hint h1.continuous hc1 3)
      (IntegrableOn.congr_fun ((hint hn.continuous hc 4).const_mul ((3 : ℕ) : ℂ))
        (fun w _ => by ring) hEm')] at hG3
    simp only [Function.comp_apply]
    simp only [div_eq_mul_inv]
    simp only [mul_assoc] at hG2 hG3
    rw [integral_const_mul] at hG2 hG3
    simp only [← hz, ← hcdef, div_eq_mul_inv, mul_assoc] at hG2 hG3 hsw ⊢
    push_cast at hG2 hG3 hsw ⊢
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    linear_combination (1 / π : ℂ) * hsw + (-(1 / π : ℂ)) * hG2 + (-(2 / π : ℂ)) * hG3
  have hdiff := hlimE.sub hround
  rw [sub_self] at hdiff
  have h6 : (-(6 / (π : ℂ))) ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    exact neg_ne_zero.2 (div_ne_zero (by norm_num) hπ)
  have h := hdiff.const_mul (-(6 / (π : ℂ)))⁻¹
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [] with δ
  rw [← mul_sub, ← mul_assoc, inv_mul_cancel₀ h6, one_mul]

/-- **The conformal excision against `(w - z)⁻⁴`.** For `J` as in `s4g_near_conf` and a coefficient `m`
smooth on an open set `U ∋ J y` whose quotient `m/(w - J y)⁴` is integrable off every disc about `J y`, the
integrals off `J(B(y, δ/|J'(y)|))` and off `B(J y, δ)` have the same limit. -/
theorem s4g_conf_diff {J : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJa : AnalyticOnNhd ℂ J (ball y (2 * ρ))) (hinj : InjOn J (ball y (2 * ρ))) (hJ0 : deriv J y ≠ 0)
    {m : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hzU : J y ∈ U)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m U)
    (hmi : ∀ r : ℝ, 0 < r → IntegrableOn (fun u => m u / (u - J y) ^ 4) (ball (J y) r)ᶜ) :
    Tendsto (fun δ : ℝ => (∫ u in (J '' ball y (δ / ‖deriv J y‖))ᶜ, m u / (u - J y) ^ 4) -
      ∫ u in (ball (J y) δ)ᶜ, m u / (u - J y) ^ 4) (𝓝[>] 0) (𝓝 0) := by
  set z := J y with hz
  have hy2 : y ∈ ball y (2 * ρ) := mem_ball_self (by positivity)
  have hJs : HasStrictDerivAt J (deriv J y) y := (hJa y hy2).hasStrictDerivAt
  -- `J(B(y, ρ/2))` is a neighbourhood of `z`
  have hnh : J '' ball y (ρ / 2) ∈ 𝓝 z := by
    rw [hz, ← hJs.map_nhds_eq hJ0]
    exact image_mem_map (ball_mem_nhds y (by positivity))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (inter_mem hnh (hU.mem_nhds hzU))
  set r : ℝ := ε / 2 with hrdef
  have hr0 : 0 < r := by positivity
  -- a smooth cutoff `χ = 1` on `ball z (r/4)`, supported in `closedBall z (r/2)`
  set b : ContDiffBump z := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hb
  set χ : ℂ → ℂ := fun u => ((b u : ℝ) : ℂ) with hχdef
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχ1 : ∀ u ∈ ball z (r / 4), χ u = 1 := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (by
      simp only [hb, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.1 hu))
    simp [hχdef, h1]
  have hχ0 : ∀ u : ℂ, r / 2 ≤ ‖u - z‖ → χ u = 0 := by
    intro u hu
    have h0 : b u = 0 := b.zero_of_le_dist (by simpa only [hb, dist_eq_norm] using hu)
    simp [hχdef, h0]
  set n : ℂ → ℂ := fun u => χ u * m u with hndef
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x - z‖ < ε
    · have hxU : x ∈ U := (hεU (mem_ball_iff_norm.2 hx)).2
      exact hχs.contDiffAt.mul (hsm.contDiffAt (hU.mem_nhds hxU))
    · have hopen : IsOpen {u : ℂ | r / 2 < ‖u - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      have hxo : x ∈ {u : ℂ | r / 2 < ‖u - z‖} := by
        show r / 2 < ‖x - z‖
        linarith [not_lt.1 hx]
      have hev : n =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hxo] with u hu
        simp only [hndef, hχ0 u (le_of_lt hu), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hsuppC : Function.support n ⊆ closedBall z (r / 2) := by
    intro u hu
    by_contra h
    apply hu
    have h' : r / 2 < ‖u - z‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at h
      exact h
    simp only [hndef, hχ0 u h'.le, zero_mul]
  have hnc : HasCompactSupport n :=
    HasCompactSupport.intro (isCompact_closedBall z (r / 2)) fun u hu => by
      by_contra h
      exact hu (hsuppC h)
  have hsupp : tsupport n ⊆ J '' ball y (ρ / 2) := by
    refine (closure_minimal hsuppC isClosed_closedBall).trans ?_
    intro u hu
    refine (hεU ?_).1
    rw [mem_ball]
    rw [Metric.mem_closedBall] at hu
    linarith
  have hnear := s4g_near_conf hρ hJa hinj hJ0 hns hnc hsupp
  -- the far part does not see the excision once both sets lie in `ball z (r/4)`
  have hevE := s4g_conformal_disc hJs hJ0 (η := 1 / 4) (by norm_num) (by norm_num)
  apply hnear.congr'
  filter_upwards [hevE, Ioo_mem_nhdsGT (show (0 : ℝ) < r / 8 by positivity)] with δ hE hδ
  obtain ⟨hE1, hE2⟩ := hE
  have hδ0 : 0 < δ := hδ.1
  have hint_n : IntegrableOn (fun u => n u / (u - z) ^ 4) (ball z (δ / 2))ᶜ := by
    refine (s4g_int_compl_cs hns.continuous hnc z (by positivity) 4).congr_fun (fun u _ => ?_)
      measurableSet_ball.compl
    rw [div_eq_mul_inv]
  have hint_f : IntegrableOn (fun u => (m u - n u) / (u - z) ^ 4) (ball z (δ / 2))ᶜ :=
    ((hmi (δ / 2) (by positivity)).sub hint_n).congr_fun (fun u _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_ball.compl
  have hf0 : ∀ u ∈ ball z (r / 4), (m u - n u) / (u - z) ^ 4 = 0 := by
    intro u hu
    simp only [hndef, hχ1 u hu, one_mul, sub_self, zero_div]
  have hEs : J '' ball y (δ / ‖deriv J y‖) ⊆ ball z (r / 4) :=
    hE1.trans (ball_subset_ball (by nlinarith [hδ.2]))
  have hBs : ball z δ ⊆ ball z (r / 4) := ball_subset_ball (by linarith [hδ.2])
  have hEc : (J '' ball y (δ / ‖deriv J y‖))ᶜ ⊆ (ball z (δ / 2))ᶜ := by
    intro w hw hwb
    have hd : dist w z < δ / 2 := hwb
    exact hw (hE2 (show dist w z < δ * (1 - 1 / 4) by linarith))
  have hBc : (ball z δ)ᶜ ⊆ (ball z (δ / 2))ᶜ :=
    compl_subset_compl.2 (ball_subset_ball (by linarith))
  have hsplit : ∀ {S : Set ℂ}, S ⊆ (ball z (δ / 2))ᶜ → (∀ u ∉ S, u ∈ ball z (r / 4)) →
      (∫ u in S, m u / (u - z) ^ 4) = (∫ u in S, n u / (u - z) ^ 4) +
        ∫ u, (m u - n u) / (u - z) ^ 4 := by
    intro S hS hSc
    have e : (fun u => m u / (u - z) ^ 4) = fun u => n u / (u - z) ^ 4 + (m u - n u) / (u - z) ^ 4 := by
      funext u
      ring
    rw [e, integral_add (hint_n.mono_set hS) (hint_f.mono_set hS)]
    congr 1
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => hf0 u (hSc u hu)
  rw [hsplit hEc (fun u hu => hEs (not_not.1 hu)), hsplit hBc (fun u hu => hBs (not_not.1 hu))]
  ring

/-- A homeomorphism of `ℂ̄` that preserves the exterior of the closed disc and is conformal there is a Möbius map on
the complement of the open disc (the argument of `sphere_circle_id`, keeping the Möbius map). -/
theorem s4g_sphere_mobius {Csph : ExtPlane → ExtPlane} (hCcont : Continuous Csph)
    (hCinj : Function.Injective Csph)
    (hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1))
    (hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p = p')
    (hdiff' : DifferentiableOn ℂ (fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))))) unitDisc) :
    ∃ N : ExtPlane → ExtPlane, IsMobius N ∧ ∀ p ∉ toExt (ball (0 : ℂ) 1), Csph p = N p := by
  have hσc : Continuous (mobiusExt 0 1 1 0) := continuous_mobiusExt (by norm_num)
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  rw [← hcdef] at hdiff'
  have hc1 : ∀ w ∈ unitDisc, mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) =
      ((c w : ℂ) : ExtPlane) ∧ c w ∈ unitDisc := by
    intro w hw
    obtain ⟨y, hy, hyD⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hw))
    have hcy : c w = y := by
      rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph _)) = y
      rw [hy]
      rfl
    exact ⟨by rw [hcy]; exact hy, hcy ▸ hyD⟩
  have hcinj : InjOn c unitDisc := by
    intro w1 hw1 w2 hw2 h
    have e1 := (hc1 w1 hw1).1
    have e2 := (hc1 w2 hw2).1
    rw [h] at e1
    have := hCinj (hσi (e1.trans e2.symm))
    exact OnePoint.coe_injective (hσi this)
  have hcsurj : c '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact (hc1 w hw).2
    · intro y hy
      obtain ⟨p, hpn, hp⟩ := hCsurj _ (sigma_not_closed hy)
      obtain ⟨w, hwp, hwD⟩ := sigma_of_not_closed hpn
      refine ⟨w, hwD, ?_⟩
      have e := (hc1 w hwD).1
      rw [← hwp, sigma_invol, hp, sigma_invol] at e
      exact (OnePoint.coe_injective e).symm
  obtain ⟨A, B, C, D, hdet, heq⟩ :=
    exists_mobius_of_isConformalOnto_unitDisc ⟨hdiff', hcinj, hcsurj⟩
  have hmc : Continuous (mobiusExt A B C D) := continuous_mobiusExt hdet
  have hZ : {x : ℂ | C * x + D = 0}.Subsingleton := by
    intro x hx y hy
    have hx' : C * x + D = 0 := hx
    have hy' : C * y + D = 0 := hy
    by_cases hC : C = 0
    · exfalso
      rw [hC, zero_mul, zero_add] at hx'
      apply hdet
      rw [hC, hx']
      ring
    · have : C * (x - y) = 0 := by linear_combination hx' - hy'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC)
  have hZd : Dense ({x : ℂ | C * x + D = 0}ᶜ) := Set.Countable.dense_compl ℂ hZ.finite.countable
  have hagree : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ)) := by
    rintro _ ⟨w, ⟨hw, hwZ⟩, rfl⟩
    have hwD : w ∈ unitDisc := hw
    show mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
    rw [(hc1 w hwD).1, mobiusExt_coe hwZ, heq hwD]
  have hcl : EqOn (fun p => mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 p))) (mobiusExt A B C D)
      (closure (((↑) : ℂ → ExtPlane) '' (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ))) :=
    EqOn.closure hagree (hσc.comp (hCcont.comp hσc)) hmc
  have hcb : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (ζ : ExtPlane))) =
      mobiusExt A B C D (ζ : ExtPlane) := by
    intro ζ hζ
    apply hcl
    have h1 : ζ ∈ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) := by
      have hsub : ball (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        hZd.open_subset_closure_inter isOpen_ball
      have : closure (ball (0 : ℂ) 1) ⊆ closure (ball (0 : ℂ) 1 ∩ {x : ℂ | C * x + D = 0}ᶜ) :=
        closure_minimal hsub isClosed_closure
      apply this
      rw [closure_ball _ one_ne_zero]
      exact mem_closedBall_zero_iff.2 hζ
    exact (image_closure_subset_closure_image OnePoint.continuous_coe) ⟨ζ, h1, rfl⟩
  have hσM : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  refine ⟨fun p => mobiusExt 0 1 1 0 (mobiusExt A B C D (mobiusExt 0 1 1 0 p)),
    isMobius_comp (isMobius_comp hσM ⟨A, B, C, D, hdet, rfl⟩) hσM, ?_⟩
  intro p hp
  have hb : ∃ ζ : ℂ, ‖ζ‖ ≤ 1 ∧ mobiusExt 0 1 1 0 p = (ζ : ExtPlane) := by
    induction p using OnePoint.rec with
    | infty => exact ⟨0, by simp, sigma_infty⟩
    | coe z =>
      have hz : 1 ≤ ‖z‖ := by
        rw [coe_mem_toExt_iff, mem_ball_zero_iff, not_lt] at hp
        exact hp
      have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by linarith)
      refine ⟨z⁻¹, ?_, sigma_coe hz0⟩
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hz
  obtain ⟨ζ, hζ, hpζ⟩ := hb
  have h1 := hcb ζ hζ
  rw [← hpζ, sigma_invol] at h1
  show Csph p = mobiusExt 0 1 1 0 (mobiusExt A B C D (mobiusExt 0 1 1 0 p))
  rw [← h1, sigma_invol]

/-- A coefficient `τ ∼ 0` whose normalized map moves `∞`: the coefficient of the plane extension of `σ_2`
(`tcg_sigma_extension`). By the argument of `crc_normalized_boundary`, `w_τ ∘ ê⁻¹` is a Möbius map `N` on the closed
exterior, and `N ∘ σ_2` fixes `-1, -i, 1`, so `N ∘ σ_2 = id`; hence `w_τ = id` on `S¹` and `w_τ(∞) = N(∞) = 2`. -/
theorem s4g_tau_exists : ∃ τ : LinfStar, τ ∈ LinfStarBall ∧
    (∀ z : ℂ, ‖z‖ = 1 → wAS τ (z : ExtPlane) = (z : ExtPlane)) ∧ wAS τ extInf ≠ extInf := by
  set u : ℂ := 2 with hudef
  have huE : u ∈ unitDiscExterior := by
    show 1 < ‖u‖
    rw [hudef]
    norm_num
  have hu : (u : ExtPlane) ∈ extDiscExterior := Or.inl ⟨u, huE, rfl⟩
  obtain ⟨e, K, hH, hE, hconf, hbd⟩ := tcg_sigma_extension hu
  obtain ⟨ω, hμae⟩ := crc_coefficient e hH
  set μ : LinfStar := (ω : LinfStar) with hμdef
  have hμ : μ ∈ LinfStarBall := ω.2
  -- `e` preserves the circle
  have hDisc : (⇑e) '' unitDisc = unitDisc := by
    have h1 := hconf.2.2
    conv_lhs => rw [← h1, ← image_comp]
    simp only [Function.comp_def, Homeomorph.apply_symm_apply, image_id']
  have hHc : e '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    have hs : sphere (0 : ℂ) 1 = (unitDisc ∪ unitDiscExterior)ᶜ := by
      ext w
      simp only [mem_sphere_zero_iff_norm, mem_compl_iff, mem_union, unitDisc, mem_ball_zero_iff,
        unitDiscExterior, mem_setOf_eq, not_or, not_lt]
      constructor
      · intro h; exact ⟨h.ge, h.le⟩
      · intro h; exact le_antisymm h.2 h.1
    rw [hs, e.image_compl, image_union, hDisc, hE]
  have hDo : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨Mμ, hMμ, Wμ, hWμ, hwfμ, hwiμ, hm1', hmI', hm2'⟩ := wA_spec hμ
  obtain ⟨KW, hKW⟩ := hWμ.1
  have hKWD := ac_t_isKQC_restrict hKW hDo (subset_univ _)
  have hKeD := ac_t_isKQC_restrict hH hDo (subset_univ _)
  have hdil : ∀ᵐ z ∂(volume.restrict {w : ℂ | 1 < ‖w‖}),
      complexDilatation Wμ z = complexDilatation (⇑e) z := by
    filter_upwards [ae_restrict_of_ae hWμ.2.2.2.2, hμae, ae_restrict_mem hDo.measurableSet]
      with z h1 h2 hz
    rw [h1, extA_eq_on_exterior μ hz]
    exact h2
  have hψ := bg_conformal_of_dilatation_eq hKeD hKWD hdil
  obtain ⟨hreg1, hreg2, hreg3⟩ := planeHomeomorph_circle_regions e hHc
  have hD : (⇑e) '' {w : ℂ | 1 < ‖w‖} = {w : ℂ | 1 < ‖w‖} := hreg3
  rw [hD] at hψ
  -- the sphere map
  have hE' : ∀ u : ℂ, e.onePointCongr (u : ExtPlane) = ((e u : ℂ) : ExtPlane) := fun u => rfl
  have hEs : ∀ u : ℂ, e.onePointCongr.symm (u : ExtPlane) = ((e.symm u : ℂ) : ExtPlane) := by
    intro u
    exact e.onePointCongr.symm_apply_eq.2 (by rw [hE', e.apply_symm_apply])
  have hEinf : e.onePointCongr.symm extInf = extInf :=
    e.onePointCongr.symm_apply_eq.2 rfl
  have hEcl : ∀ q ∈ toExt (closedBall (0 : ℂ) 1), e.onePointCongr q ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨e v, hreg1 ▸ mem_image_of_mem e hv, rfl⟩
  have hEscl : ∀ p ∈ toExt (closedBall (0 : ℂ) 1),
      e.onePointCongr.symm p ∈ toExt (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hEs]
    rw [← hreg1] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [e.symm_apply_apply]
  obtain ⟨Csph, hCdef⟩ : ∃ Csph : ExtPlane → ExtPlane,
      Csph = fun p => wAS μ (e.onePointCongr.symm p) := ⟨_, rfl⟩
  have hCcont : Continuous Csph := by
    rw [hCdef]
    exact (wAS_continuous hμ).comp e.onePointCongr.symm.continuous
  have hCinj : Function.Injective Csph := by
    intro p q hpq
    rw [hCdef] at hpq
    exact e.onePointCongr.symm.injective ((wAS_bijective μ).1 hpq)
  have hCnot : ∀ p ∉ toExt (closedBall (0 : ℂ) 1), Csph p ∉ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp hC
    rw [hCdef] at hC
    have h2 := hEcl _ ((wAS_closed_iff hμ _).2 hC)
    rw [e.onePointCongr.apply_symm_apply] at h2
    exact hp h2
  have hCsurj : ∀ p' ∉ toExt (closedBall (0 : ℂ) 1), ∃ p ∉ toExt (closedBall (0 : ℂ) 1),
      Csph p = p' := by
    intro p' hp'
    obtain ⟨q, hq⟩ := (wAS_bijective μ).2 p'
    have hqn : q ∉ toExt (closedBall (0 : ℂ) 1) := by
      intro hqc
      apply hp'
      rw [← hq]
      exact (wAS_closed_iff hμ q).1 hqc
    refine ⟨e.onePointCongr q, ?_, ?_⟩
    · intro hc
      have h5 := hEscl _ hc
      rw [e.onePointCongr.symm_apply_apply] at h5
      exact hqn h5
    · rw [hCdef]
      show wAS μ (e.onePointCongr.symm (e.onePointCongr q)) = p'
      rw [e.onePointCongr.symm_apply_apply, hq]
  -- conformality of `c`
  have hσi : Function.Injective (mobiusExt 0 1 1 0) := fun a b h => by
    rw [← sigma_invol a, ← sigma_invol b, h]
  have hσ : IsMobius (mobiusExt 0 1 1 0) := ⟨0, 1, 1, 0, by norm_num, rfl⟩
  have hP : IsMobius (fun p => mobiusExt 0 1 1 0 (Mμ p)) := isMobius_comp hMμ hσ
  have hPc := mobius_finite_conformal hP
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ → ℂ, c = fun w : ℂ =>
      finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) := ⟨_, rfl⟩
  have hinvon : ∀ u ∈ {w : ℂ | 1 < ‖w‖}, Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖} u = e.symm u := by
    intro u hu
    rw [← hD] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [e.symm_apply_apply]
    exact (e.injective.injOn).leftInvOn_invFunOn hv
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Set ℂ, Ω = {w | w ∈ unitDisc ∧ w ≠ 0 ∧
      Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) ≠ extInf} := ⟨_, rfl⟩
  have hcw : ∀ w ∈ Ω, w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} ∧
      c w = finPart (mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) :
        ExtPlane))) ∧
      mobiusExt 0 1 1 0 (Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane)) ≠
        extInf := by
    intro w hw
    rw [hΩ] at hw
    obtain ⟨hwD, hw0, hwne⟩ := hw
    have hwin : w⁻¹ ∈ {w : ℂ | 1 < ‖w‖} := by
      show 1 < ‖w⁻¹‖
      rw [norm_inv]
      have : ‖w‖ < 1 := mem_ball_zero_iff.1 hwD
      exact one_lt_inv₀ (norm_pos_iff.2 hw0) |>.2 this
    have hCw : Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) =
        Mμ (((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) w⁻¹ : ℂ) : ExtPlane) := by
      rw [hCdef]
      show wAS μ (e.onePointCongr.symm (mobiusExt 0 1 1 0 (w : ExtPlane))) = _
      rw [sigma_coe hw0, hEs, Function.comp_apply, hinvon _ hwin]
      exact hwfμ _
    refine ⟨hwin, ?_, ?_⟩
    · rw [hcdef]
      show finPart (mobiusExt 0 1 1 0 (Csph (mobiusExt 0 1 1 0 (w : ExtPlane)))) = _
      rw [hCw]
    · rw [← hCw]
      obtain ⟨y, hy, -⟩ := sigma_of_not_closed (hCnot _ (sigma_not_closed hwD))
      rw [hy]
      exact OnePoint.coe_ne_infty y
  have hdiffΩ : DifferentiableOn ℂ c Ω := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω := fun w hw =>
      ((differentiableAt_id.inv (by
        rw [hΩ] at hw
        exact hw.2.1))).differentiableWithinAt
    have h2 : DifferentiableOn ℂ ((Wμ ∘ Function.invFunOn (⇑e) {w : ℂ | 1 < ‖w‖}) ∘ fun w : ℂ => w⁻¹) Ω :=
      hψ.1.comp h1 (fun w hw => (hcw w hw).1)
    have h3 := hPc.1.comp h2 (fun w hw => (hcw w hw).2.2)
    refine h3.congr (fun w hw => ?_)
    exact (hcw w hw).2.1
  have hE1 : {w : ℂ | w ∈ unitDisc ∧ Csph (mobiusExt 0 1 1 0 (w : ExtPlane)) = extInf}.Subsingleton := by
    intro w1 h1 w2 h2
    have := hCinj (h1.2.trans h2.2.symm)
    exact OnePoint.coe_injective (hσi this)
  have hEfin : (unitDisc \ Ω).Finite := by
    refine ((Set.finite_singleton (0 : ℂ)).union hE1.finite).subset ?_
    intro w hw
    by_cases h0 : w = 0
    · exact Or.inl h0
    · refine Or.inr ⟨hw.1, ?_⟩
      by_contra hb
      apply hw.2
      rw [hΩ]
      exact ⟨hw.1, h0, hb⟩
  have hdiffc : DifferentiableOn ℂ c unitDisc := by
    refine differentiableOn_of_finite_exceptional (show IsOpen unitDisc from isOpen_ball) hEfin ?_ ?_
    · rw [hcdef]
      exact sphere_c_continuousOn hCcont hCnot
    · refine hdiffΩ.mono ?_
      intro w hw
      by_contra h
      exact hw.2 ⟨hw.1, h⟩
  obtain ⟨N, hN, hCN⟩ := s4g_sphere_mobius hCcont hCinj hCnot hCsurj (by rw [← hcdef]; exact hdiffc)
  -- `σ_u` is Möbius and `N ∘ σ_u = id`
  obtain ⟨a, b, hσab, hdet, -⟩ := sigmaSphere_matrix hu
  have hσu : IsMobius (sigmaSphere (u : ExtPlane)) := ⟨a, b, conj b, conj a, hdet, hσab⟩
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → wAS μ (z : ExtPlane) = N (sigmaSphere (u : ExtPlane) (z : ExtPlane)) := by
    intro z hz
    have hzu : z ≠ u := by
      intro h
      rw [h] at hz
      exact (ne_of_lt (show (1 : ℝ) < ‖u‖ from huE)) hz.symm
    have hfin : sigmaSphere (u : ExtPlane) (z : ExtPlane) = ((e z : ℂ) : ExtPlane) := by
      rw [show e z = finPart (sigmaSphere (u : ExtPlane) (z : ExtPlane)) from hbd (show z ∈ unitCircle from hz),
        sigmaSphere_coe_eq huE hzu]
      rfl
    have hez : ‖e z‖ = 1 :=
      mem_sphere_zero_iff_norm.1 (hHc ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.2 hz))
    have h1 : Csph ((e z : ℂ) : ExtPlane) = wAS μ (z : ExtPlane) := by
      rw [hCdef]
      show wAS μ (e.onePointCongr.symm ((e z : ℂ) : ExtPlane)) = _
      rw [hEs, e.symm_apply_apply]
    rw [hfin, ← h1]
    apply hCN
    rw [coe_mem_toExt_iff, mem_ball_zero_iff, hez]
    exact lt_irrefl 1
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      simp [mobiusFn]
  have hNσ : (fun p => N (sigmaSphere (u : ExtPlane) p)) = id := by
    rw [← hid]
    refine mobius_eq_of_three_points (p₁ := -1) (p₂ := -I) (p₃ := 1) (isMobius_comp hσu hN)
      ⟨1, 0, 0, 1, by norm_num, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · norm_num
    · intro h
      have := congrArg Complex.re h
      norm_num at this
    · rw [hid]
      exact (hcirc (-1) (by simp)).symm.trans hm1'
    · rw [hid]
      exact (hcirc (-I) (by simp)).symm.trans hmI'
    · rw [hid]
      exact (hcirc 1 (by simp)).symm.trans hm2'
  refine ⟨μ, hμ, fun z hz => ?_, ?_⟩
  · rw [hcirc z hz]
    exact congrFun hNσ (z : ExtPlane)
  · have h1 : wAS μ extInf = Csph extInf := by
      rw [hCdef]
      show wAS μ extInf = wAS μ (e.onePointCongr.symm extInf)
      rw [hEinf]
    have h2 : Csph extInf = N extInf := hCN _ (infty_notMem_toExt _)
    have h3 : N extInf = (u : ExtPlane) := by
      rw [← sigmaSphere_pole (u : ExtPlane)]
      exact congrFun hNσ (u : ExtPlane)
    rw [h1, h2, h3]
    exact OnePoint.coe_ne_infty u

/-- The Schwarzian at a point depends only on the germ of the map there. -/
theorem s4g_schwarzian_congr {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[𝓝 w] g) :
    schwarzianHol f w = schwarzianHol g w := by
  have h1 := h.deriv
  have h2 := h1.deriv
  have h3 : (fun v => deriv (deriv f) v / deriv f v) =ᶠ[𝓝 w] (fun v => deriv (deriv g) v / deriv g v) := by
    filter_upwards [h1, h2] with v hv1 hv2
    rw [hv1, hv2]
  show deriv (fun v => deriv (deriv f) v / deriv f v) w - (1 / 2) * (deriv (deriv f) w / deriv f w) ^ 2 =
    deriv (fun v => deriv (deriv g) v / deriv g v) w - (1 / 2) * (deriv (deriv g) w / deriv g w) ^ 2
  rw [h3.deriv_eq, h1.eq_of_nhds, h2.eq_of_nhds]

/-- Right multiplication by `τ ∼ 0` does not change boundary values, even after a further left multiplication. -/
theorem s4g_class_boundary {κ τ ρ : LinfStar} (hκ : κ ∈ LinfStarBall) (hτ : τ ∈ LinfStarBall)
    (hτ1 : ∀ z : ℂ, ‖z‖ = 1 → wAS τ (z : ExtPlane) = (z : ExtPlane)) (hρ : ρ ∈ LinfStarBall) :
    ∀ z ∈ unitCircle, wA (beltramiMul ρ (beltramiMul κ τ)) z = wA (beltramiMul ρ κ) z := by
  have hm := wA_mul hτ hκ
  intro z hz
  show finPart (wAS (beltramiMul ρ (beltramiMul κ τ)) (z : ExtPlane)) =
    finPart (wAS (beltramiMul ρ κ) (z : ExtPlane))
  rw [(wA_mul hm.1 hρ).2.1, (wA_mul hκ hρ).2.1, hm.2.1]
  simp only [Function.comp_apply]
  rw [hτ1 z hz]

/-- `L_ν ϑ` is unchanged when the base point `κ` is replaced by `κ * τ`, `τ ∼ 0`. -/
theorem s4g_lieTheta_class {κ τ : LinfStar} (hκ : κ ∈ LinfStarBall) (hτ : τ ∈ LinfStarBall)
    (hτ1 : ∀ z : ℂ, ‖z‖ = 1 → wAS τ (z : ExtPlane) = (z : ExtPlane)) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    lieTheta (beltramiMul κ τ) ν z = lieTheta κ ν z := by
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  have hκ' := (wA_mul hτ hκ).1
  have hsmall : ∀ᶠ e : ℂ in 𝓝 0, ‖e‖ * ‖toLinf ν‖ < 1 :=
    (continuous_norm.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simp)
  have heq : (fun e : ℂ => schwarzianHol (gsans (beltramiMul (e • toLinf ν) (beltramiMul κ τ)))
      (wA (e • toLinf ν) z) * dz (wA (e • toLinf ν)) z ^ 2) =ᶠ[𝓝 0]
      (fun e : ℂ => schwarzianHol (gsans (beltramiMul (e • toLinf ν) κ))
      (wA (e • toLinf ν) z) * dz (wA (e • toLinf ν)) z ^ 2) := by
    filter_upwards [hsmall, s4ma_pole_absent_eventually (toLinf ν) z] with e he hp
    have heB : e • toLinf ν ∈ LinfStarBall := by
      simpa [LinfStarBall, mem_ball_zero_iff, norm_smul] using he
    obtain ⟨-, -, hwE⟩ := e41_w_regular hνh he hz hp
    have hg := (FB.fb_pair_class (wA_mul hκ' heB).1 (wA_mul hκ heB).1
      (s4g_class_boundary hκ hτ hτ1 heB)).2
    have hev : gsans (beltramiMul (e • toLinf ν) (beltramiMul κ τ)) =ᶠ[𝓝 (wA (e • toLinf ν) z)]
        gsans (beltramiMul (e • toLinf ν) κ) :=
      Filter.eventuallyEq_of_mem (wp_exterior_isOpen.mem_nhds hwE) hg
    rw [s4g_schwarzian_congr hev]
  rw [lieTheta, lieTheta]
  exact (t203_c1_dz_congr heq).1

/-- On `T₀(1)`, `K₄` is square integrable on `𝔻* × 𝔻*` (the argument of `gk_thm_2_6`, for any representative). -/
theorem s4g_w3_K4_L2 {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    (∫⁻ q in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 (gsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  have hinv : invT (Phi ⟨κ, hκ⟩) ∈ T01 := TakhtajanTeo.lemma_3_4.2.2 _ hκT
  rw [gtp_invT_phi] at hinv
  exact gk_K4_of_K1 hκ (gk_K1_T01 _ hinv ⟨beltramiInv κ, grp_inv_mem hκ⟩ rfl)

/-- The column expansion `K₄(w, z) = Σ_n (B₄ e_z)_n f_n(w)`. -/
theorem s4g_w3_col {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ unitDiscExterior)
    (hw : w ∈ unitDiscExterior) :
    HasSum (fun n => (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n * basisF n w)
      (kerK4 (gsans κ) w z) := by
  have hs := bergman_pair_summable (gop_l2_summable (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)))
    (s3st_basisF_sq hw)
  have h := hs.of_norm.hasSum
  rwa [← s3st_kernel_series _ hw z, s3st_B4_kernel hκ hw hz] at h

/-- Parseval for the column: `Σ_n |(B₄ e_z)_n|² = ∫_{𝔻*} |K₄(w, z)|²`. -/
theorem s4g_w3_col_parseval {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasSum (fun n => ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ ^ 2)
      (∫ w in unitDiscExterior, ‖kerK4 (gsans κ) w z‖ ^ 2) := by
  set c := gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z) with hc
  have hx := gop_l2_summable c
  have h := e24_ext_pair hx hx (E := ∅) Set.finite_empty
    (fun u hu _ => s4g_w3_col hκ hz hu) (fun u hu _ => s4g_w3_col hκ hz hu)
  have e1 : (fun n => c n * conj (c n)) = fun n => ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    funext n
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (∫ u in unitDiscExterior, kerK4 (gsans κ) u z * conj (kerK4 (gsans κ) u z)) =
      ((∫ u in unitDiscExterior, ‖kerK4 (gsans κ) u z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, e2] at h
  exact Complex.hasSum_ofReal.1 h

/-- The open exterior `{δ < |ζ - z|}` and `(B(z, δ))ᶜ` differ by a null set. -/
theorem s4g_ballc_ae (z : ℂ) (δ : ℝ) :
    ({ζ : ℂ | δ < ‖ζ - z‖} : Set ℂ) =ᵐ[volume] ((ball z δ)ᶜ : Set ℂ) := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · have : {ζ : ℂ | δ < ‖ζ - z‖} \ (ball z δ)ᶜ = ∅ := by
      ext w
      constructor
      · rintro ⟨h1, h2⟩
        exfalso
        apply h2
        intro h3
        have h1' : δ < ‖w - z‖ := h1
        rw [mem_ball, dist_eq_norm] at h3
        linarith
      · intro h; exact h.elim
    rw [this, measure_empty]
  · refine measure_mono_null ?_ (Measure.addHaar_sphere (volume : Measure ℂ) z δ)
    rintro w ⟨h1, h2⟩
    have h1' : δ ≤ ‖w - z‖ := by
      have := h1; rw [Set.mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at this; exact this
    have h2' : ¬ δ < ‖w - z‖ := h2
    rw [mem_sphere, dist_eq_norm]
    linarith [not_lt.1 h2']

/-- The second-order truncations of a test function converge to `-π H n`. -/
theorem s4g_trunc2 {n : ℂ → ℂ} (hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n) (hc : HasCompactSupport n)
    (z : ℂ) :
    Tendsto (fun δ : ℝ => ∫ w in (ball z δ)ᶜ, n w / (w - z) ^ 2) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * hilbertHSmooth n z)) := by
  have hS := (tendsto_truncated_cauchyT_dz (hn.of_le (by exact_mod_cast le_top)) hc z).const_mul (-(π : ℂ))
  rw [← (i1_hilbertH_eq_cauchyT_dz hn hc).1] at hS
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  refine hS.congr fun δ => ?_
  rw [setIntegral_congr_set (s4g_ballc_ae z δ), ← mul_assoc]
  field_simp

/-- An `L²` function against `(w - z)⁻²` is integrable off any disc. -/
theorem s4g_int_L2_compl {f : ℂ → ℂ} (hf : MemLp f 2) (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun w => f w / (w - z) ^ 2) (ball z δ)ᶜ := by
  have h1 : IsBeltramiCoeff (fun _ : ℂ => (1 : ℂ)) univ 1 :=
    ⟨aestronglyMeasurable_const, Filter.Eventually.of_forall fun _ => by simp⟩
  have hi := s4g_int_compl h1 z hδ
  have hm : AEStronglyMeasurable (fun w : ℂ => 1 / (w - z) ^ 2) (volume.restrict (ball z δ)ᶜ) :=
    (measurable_const.div ((measurable_id.sub_const z).pow_const 2)).aestronglyMeasurable
  have hL2 : MemLp (fun w : ℂ => 1 / (w - z) ^ 2) 2 (volume.restrict (ball z δ)ᶜ) := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hi.norm).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [norm_div, norm_one, norm_pow, div_pow, one_pow]
    ring
  have h := (hf.restrict (ball z δ)ᶜ).integrable_mul hL2
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.mul_apply, div_eq_mul_inv, one_mul]

/-- `H h` at points off the support is the absolutely convergent integral, for `h ∈ L²` vanishing on
`B(x, 2s)` (truncate to discs and pass to the limit). -/
theorem s4g_H_off {h : ℂ → ℂ} (hm : Measurable h) (hh : MemLp h 2) {x : ℂ} {s : ℝ} (hs : 0 < s)
    (h0 : ∀ w ∈ ball x (2 * s), h w = 0) :
    ∀ᵐ z ∂(volume.restrict (ball x s)), hilbertH h z = ∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - z) ^ 2 := by
  set hR : ℕ → ℂ → ℂ := fun k => (closedBall (0 : ℂ) k).indicator h with hRdef
  have hRm : ∀ k, Measurable (hR k) := fun k => hm.indicator measurableSet_closedBall
  have hR2 : ∀ k, MemLp (hR k) 2 := fun k => hh.indicator measurableSet_closedBall
  have hRc : ∀ k, HasCompactSupport (hR k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall 0 k) fun w hw => indicator_of_notMem hw _
  have hsupp : ∀ k, ball x s ⊆ (tsupport (hR k))ᶜ := by
    intro k
    have hcl : tsupport (hR k) ⊆ (ball x (2 * s))ᶜ := by
      refine closure_minimal ?_ isOpen_ball.isClosed_compl
      intro w hw hwb
      apply hw
      simp only [hRdef]
      by_cases hwk : w ∈ closedBall (0 : ℂ) k
      · rw [indicator_of_mem hwk, h0 w hwb]
      · rw [indicator_of_notMem hwk]
    intro w hw hwt
    exact hcl hwt (ball_subset_ball (by linarith) hw)
  have hoff : ∀ k, ∀ᵐ z ∂(volume.restrict (ball x s)),
      hilbertH (hR k) z = ∫ ζ, -(1 / π : ℂ) * hR k ζ / (ζ - z) ^ 2 := fun k =>
    ae_restrict_of_ae_restrict_of_subset (hsupp k)
      (hilbertH_eq_integral_ae_off_support (hRm k) (hR2 k) (hRc k))
  -- `hR k → h` in `L²`
  have hL2 : Tendsto (fun k => eLpNorm (hR k - h) 2 volume) atTop (𝓝 0) := by
    have he : ∀ k, eLpNorm (hR k - h) 2 volume =
        (∫⁻ w, ‖(closedBall (0 : ℂ) k)ᶜ.indicator h w‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      intro k
      have e : hR k - h = -((closedBall (0 : ℂ) k)ᶜ.indicator h) := by
        funext w
        simp only [hRdef, Pi.sub_apply, Pi.neg_apply]
        by_cases hw : w ∈ closedBall (0 : ℂ) k
        · rw [indicator_of_mem hw, indicator_of_notMem (by simpa using hw), sub_self, neg_zero]
        · rw [indicator_of_notMem hw, indicator_of_mem (by simpa using hw), zero_sub]
      rw [e, eLpNorm_neg, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (hm.indicator measurableSet_closedBall.compl).aestronglyMeasurable]
      norm_num
    simp only [he]
    have hfin : (∫⁻ w, ‖h w‖ₑ ^ (2 : ℝ)) ≠ ∞ := by
      have h2 : eLpNorm h 2 volume < ∞ := hh
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm.aestronglyMeasurable] at h2
      norm_num at h2
      first
        | exact h2.ne
        | (convert ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h2).ne using 4; norm_num)
    have hlim : Tendsto (fun k : ℕ => ∫⁻ w, ‖(closedBall (0 : ℂ) k)ᶜ.indicator h w‖ₑ ^ (2 : ℝ))
        atTop (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence (fun w => ‖h w‖ₑ ^ (2 : ℝ))
        (F := fun k : ℕ => fun w => ‖(closedBall (0 : ℂ) k)ᶜ.indicator h w‖ₑ ^ (2 : ℝ))
        (f := fun _ => 0)
        (fun k => ((hm.indicator measurableSet_closedBall.compl).enorm.pow_const _))
        (fun k => Filter.Eventually.of_forall fun w => by
          show ‖(closedBall (0 : ℂ) k)ᶜ.indicator h w‖ₑ ^ (2 : ℝ) ≤ ‖h w‖ₑ ^ (2 : ℝ)
          by_cases hw : w ∈ (closedBall (0 : ℂ) k)ᶜ
          · rw [indicator_of_mem hw]
          · rw [indicator_of_notMem hw, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
            exact bot_le)
        hfin
        (Filter.Eventually.of_forall fun w => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Filter.eventually_ge_atTop ⌈‖w‖⌉₊] with k hk
          have hwk : w ∉ (closedBall (0 : ℂ) k)ᶜ := by
            rw [Set.mem_compl_iff, not_not, mem_closedBall_zero_iff]
            exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
          rw [indicator_of_notMem hwk, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)])
      simpa only [lintegral_zero] using this
    have hc := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
    exact hc.comp hlim
  -- hence `H (hR k) → H h` in measure, and along a subsequence a.e.
  have hHL2 : Tendsto (fun k => eLpNorm (hilbertH (hR k) - hilbertH h) 2 volume) atTop (𝓝 0) := by
    refine hL2.congr fun k => ?_
    rw [hilbertH_eLpNorm_sub_eq (hR2 k) hh]
  have htm : TendstoInMeasure volume (fun k => hilbertH (hR k)) atTop (hilbertH h) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hHL2
  obtain ⟨ns, hmono, hns⟩ := htm.exists_seq_tendsto_ae
  -- the integrals converge at every point of `B(x, s)` (dominated convergence)
  have hint : ∀ z ∈ ball x s, Tendsto (fun k => ∫ ζ, -(1 / π : ℂ) * hR (ns k) ζ / (ζ - z) ^ 2) atTop
      (𝓝 (∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - z) ^ 2)) := by
    intro z hz
    have hzs : ball z s ⊆ ball x (2 * s) := by
      intro w hw
      rw [mem_ball] at hw hz ⊢
      linarith [dist_triangle w z x]
    have hG : Integrable (fun ζ => ‖h ζ / (ζ - z) ^ 2‖) := by
      have hi := (s4g_int_L2_compl hh z hs).norm
      refine (integrableOn_univ.1 ?_)
      rw [← union_compl_self (ball z s)]
      refine IntegrableOn.union ?_ hi
      refine (integrableOn_zero).congr_fun (fun w hw => ?_) measurableSet_ball
      simp [h0 w (hzs hw)]
    refine tendsto_integral_of_dominated_convergence (fun ζ => (1 / π) * ‖h ζ / (ζ - z) ^ 2‖)
      (fun k => ?_) (hG.const_mul _) (fun k => Filter.Eventually.of_forall fun ζ => ?_)
      (Filter.Eventually.of_forall fun ζ => ?_)
    · exact (((hRm (ns k)).const_mul _).div ((measurable_id.sub_const z).pow_const 2)).aestronglyMeasurable
    · simp only [hRdef, mul_div_assoc, norm_mul, norm_neg, norm_div, one_div, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_pow]
      gcongr
      by_cases hw : ζ ∈ closedBall (0 : ℂ) (ns k)
      · rw [indicator_of_mem hw]
      · rw [indicator_of_notMem hw, norm_zero]
        exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop ⌈‖ζ‖⌉₊] with k hk
      have hk' : ⌈‖ζ‖⌉₊ ≤ ns k := hk.trans (hmono.id_le k)
      have hwk : ζ ∈ closedBall (0 : ℂ) (ns k) := by
        rw [mem_closedBall_zero_iff]
        exact (Nat.le_ceil _).trans (by exact_mod_cast hk')
      simp only [hRdef, indicator_of_mem hwk]
  filter_upwards [ae_restrict_of_ae hns, ae_all_iff.2 fun k => hoff (ns k),
    ae_restrict_mem measurableSet_ball] with z hz hk hzb
  refine tendsto_nhds_unique hz ?_
  exact (hint z hzb).congr fun k => (hk k).symm

/-- Local form of `s4g_pv_H`: on `B(x, s)` with `B(x, 4s) ⊆ U`. -/
theorem s4g_pv_H_ball {f : ℂ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) {U : Set ℂ} (hU : IsOpen U)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {x : ℂ} {s : ℝ} (hs : 0 < s)
    (hxU : ball x (4 * s) ⊆ U) :
    ∃ G : ℂ → ℂ, (∀ z ∈ ball x s, Tendsto (fun δ : ℝ => ∫ w in (ball z δ)ᶜ, f w / (w - z) ^ 2)
        (𝓝[>] 0) (𝓝 (G z))) ∧
      ∀ᵐ z ∂(volume.restrict (ball x s)), G z = -(π : ℂ) * hilbertH f z := by
  -- a smooth cutoff `χ = 1` on `ball x (2s)`, supported in `closedBall x (3s)`
  set b : ContDiffBump x := ⟨2 * s, 3 * s, by positivity, by linarith⟩ with hb
  set χ : ℂ → ℂ := fun u => ((b u : ℝ) : ℂ) with hχdef
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχ1 : ∀ u ∈ ball x (2 * s), χ u = 1 := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (by
      simp only [hb, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.1 hu))
    simp [hχdef, h1]
  have hχ0 : ∀ u : ℂ, 3 * s ≤ ‖u - x‖ → χ u = 0 := by
    intro u hu
    have h0 : b u = 0 := b.zero_of_le_dist (by simpa only [hb, dist_eq_norm] using hu)
    simp [hχdef, h0]
  set n : ℂ → ℂ := fun u => χ u * f u with hndef
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : ‖y - x‖ < 4 * s
    · have hyU : y ∈ U := hxU (mem_ball_iff_norm.2 hy)
      exact hχs.contDiffAt.mul (hsm.contDiffAt (hU.mem_nhds hyU))
    · have hopen : IsOpen {u : ℂ | 3 * s < ‖u - x‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      have hyo : y ∈ {u : ℂ | 3 * s < ‖u - x‖} := by
        show 3 * s < ‖y - x‖
        linarith [not_lt.1 hy]
      have hev : n =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hyo] with u hu
        simp only [hndef, hχ0 u (le_of_lt hu), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hnc : HasCompactSupport n := by
    refine HasCompactSupport.intro (isCompact_closedBall x (3 * s)) ?_
    intro u hu
    have h : 3 * s < ‖u - x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hu
      exact hu
    simp only [hndef, hχ0 u h.le, zero_mul]
  have hn2 : MemLp n 2 := hns.continuous.memLp_of_hasCompactSupport hnc
  set h : ℂ → ℂ := fun u => f u - n u with hhdef
  have hhm : Measurable h := hfm.sub hns.continuous.measurable
  have hh2 : MemLp h 2 := hf.sub hn2
  have h0 : ∀ w ∈ ball x (2 * s), h w = 0 := by
    intro w hw
    simp only [hhdef, hndef, hχ1 w hw, one_mul, sub_self]
  have hfnh : f = n + h := by
    funext u
    simp only [Pi.add_apply, hhdef]
    ring
  refine ⟨fun z => -(π : ℂ) * hilbertHSmooth n z + ∫ w, h w / (w - z) ^ 2, ?_, ?_⟩
  · intro z hz
    refine ((s4g_trunc2 hns hnc z).add tendsto_const_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with δ hδ
    have hsub : ball z δ ⊆ ball x (2 * s) := by
      intro w hw
      rw [mem_ball] at hw hz ⊢
      linarith [dist_triangle w z x, hδ.2]
    have e : (fun w => f w / (w - z) ^ 2) = fun w => n w / (w - z) ^ 2 + h w / (w - z) ^ 2 := by
      funext w
      rw [hfnh]
      simp only [Pi.add_apply, add_div]
    rw [e, integral_add (s4g_int_L2_compl hn2 z hδ.1) (s4g_int_L2_compl hh2 z hδ.1)]
    congr 1
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
      rw [h0 w (hsub (not_not.1 hw)), zero_div]).symm
  · have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hadd := hilbertH_add_ae hn2 hh2
    rw [← hfnh] at hadd
    filter_upwards [ae_restrict_of_ae hadd, ae_restrict_of_ae (hilbertH_eq_ae_smooth hns hnc),
      s4g_H_off hhm hh2 hs h0] with z hz1 hz2 hz3
    rw [hz1, Pi.add_apply, hz2, hz3]
    have e : (∫ ζ, -(1 / π : ℂ) * h ζ / (ζ - z) ^ 2) = -(1 / π : ℂ) * ∫ ζ, h ζ / (ζ - z) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext ζ
      ring
    rw [e]
    field_simp
    ring

/-- **PV against `(w - z)⁻²` is `-π H f`.** For `f ∈ L²` smooth on an open set `U`, the round truncations
`∫_{|w - z| > δ} f(w)/(w - z)²` converge at every point of `U`, to `-π (H f)(z)` at almost every point. -/
theorem s4g_pv_H {f : ℂ → ℂ} (hfm : Measurable f) (hf : MemLp f 2) {U : Set ℂ} (hU : IsOpen U)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    (∀ z ∈ U, ∃ L : ℂ, Tendsto (fun δ : ℝ => ∫ w in (ball z δ)ᶜ, f w / (w - z) ^ 2) (𝓝[>] 0) (𝓝 L)) ∧
      ∀ᵐ z ∂(volume.restrict U), Tendsto (fun δ : ℝ => ∫ w in (ball z δ)ᶜ, f w / (w - z) ^ 2) (𝓝[>] 0)
        (𝓝 (-(π : ℂ) * hilbertH f z)) := by
  have hr : ∀ x : U, ∃ s : ℝ, 0 < s ∧ ball (x : ℂ) (4 * s) ⊆ U := by
    intro x
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x x.2
    exact ⟨ε / 4, by positivity, by rwa [show 4 * (ε / 4) = ε by ring]⟩
  choose s hs hsU using hr
  have hG : ∀ x : U, ∃ G : ℂ → ℂ, (∀ z ∈ ball (x : ℂ) (s x), Tendsto
      (fun δ : ℝ => ∫ w in (ball z δ)ᶜ, f w / (w - z) ^ 2) (𝓝[>] 0) (𝓝 (G z))) ∧
      ∀ᵐ z ∂(volume.restrict (ball (x : ℂ) (s x))), G z = -(π : ℂ) * hilbertH f z :=
    fun x => s4g_pv_H_ball hfm hf hU hsm (hs x) (hsU x)
  choose G hGt hGae using hG
  refine ⟨fun z hz => ⟨_, hGt ⟨z, hz⟩ z (mem_ball_self (hs _))⟩, ?_⟩
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : ℂ) (s x)) (fun _ => isOpen_ball)
  have hcov : U = ⋃ x ∈ T, ball (x : ℂ) (s x) := by
    rw [hTU]
    ext z
    simp only [mem_iUnion]
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, mem_ball_self (hs _)⟩
    · rintro ⟨x, hx⟩
      exact hsU x (ball_subset_ball (by linarith [hs x]) hx)
  rw [hcov, ae_restrict_biUnion_iff _ hT]
  intro x _
  filter_upwards [hGae x, ae_restrict_mem measurableSet_ball] with z hz hzb
  rw [← hz]
  exact hGt x z hzb

/-- `∫_{r < |w - z| < R} (w - z)⁻² = 0` (rotation by `i` changes the sign). -/
theorem s4g_ann_zero (z : ℂ) (r R : ℝ) : ∫ w in ball z R \ ball z r, ((w - z) ^ 2)⁻¹ = 0 := by
  set A₀ : Set ℂ := ball (0 : ℂ) R \ ball (0 : ℂ) r with hA₀
  set F : ℂ → ℂ := A₀.indicator fun u => (u ^ 2)⁻¹ with hF
  have hmem : ∀ w : ℂ, w ∈ ball z R \ ball z r ↔ w - z ∈ A₀ := by
    intro w
    simp only [hA₀, mem_diff, mem_ball, dist_eq_norm, sub_zero]
  have h1 : (∫ w in ball z R \ ball z r, ((w - z) ^ 2)⁻¹) = ∫ u, F u := by
    rw [← integral_indicator (measurableSet_ball.diff measurableSet_ball)]
    have e : (ball z R \ ball z r).indicator (fun w => ((w - z) ^ 2)⁻¹) = fun w => F (w - z) := by
      funext w
      by_cases hw : w ∈ ball z R \ ball z r
      · rw [indicator_of_mem hw, hF, indicator_of_mem ((hmem w).1 hw)]
      · rw [indicator_of_notMem hw, hF, indicator_of_notMem (fun h => hw ((hmem w).2 h))]
    rw [e]
    exact (measurePreserving_sub_right volume z).integral_comp
      (Homeomorph.subRight z).measurableEmbedding F
  set a : Circle := Circle.exp (π / 2) with ha
  have haI : (a : ℂ) = I := by
    rw [ha, Circle.coe_exp]
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  have h2 : (∫ u, F (rotation a u)) = ∫ u, F u :=
    (LinearIsometryEquiv.measurePreserving (rotation a)).integral_comp
      (rotation a).toHomeomorph.measurableEmbedding F
  have h3 : ∀ u, F (rotation a u) = -F u := by
    intro u
    rw [rotation_apply, haI]
    have hn : ‖I * u‖ = ‖u‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have hm : I * u ∈ A₀ ↔ u ∈ A₀ := by
      simp only [hA₀, mem_diff, mem_ball, dist_zero_right, hn]
    by_cases hu : u ∈ A₀
    · rw [hF, indicator_of_mem (hm.2 hu), indicator_of_mem hu, mul_pow, I_sq, neg_one_mul, inv_neg]
    · rw [hF, indicator_of_notMem (fun h => hu (hm.1 h)), indicator_of_notMem hu, neg_zero]
  simp only [h3, integral_neg] at h2
  rw [h1]
  linear_combination -h2 / 2

/-- `|w - z|⁻¹` is integrable on discs. -/
theorem s4g_int_inv_norm_ball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => ‖w - z‖⁻¹) (ball z r) := by
  refine ⟨((measurable_id.sub_const z).norm.inv).aestronglyMeasurable, ?_⟩
  show (∫⁻ w in ball z r, ‖‖w - z‖⁻¹‖ₑ) < ∞
  have h := lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hr z
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (h ▸ ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top)
  by_cases hw : w = z
  · subst hw
    simp
  · have hne : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
    rw [ENNReal.rpow_neg_one, enorm_inv hne, Real.enorm_eq_ofReal (norm_nonneg _), ofReal_norm]

/-- Splitting a round truncation into the annulus `δ < |w - z| < r`, where only the Lipschitz increment of `m`
at `z` contributes, and the exterior of `B(z, r)`. -/
theorem s4g_pv_near_bound {m : ℂ → ℂ} {z : ℂ} {r δ L : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hL : 0 ≤ L)
    (hlip : ∀ w ∈ ball z r, ‖m w - m z‖ ≤ L * ‖w - z‖)
    (hm : IntegrableOn (fun w => m w / (w - z) ^ 2) (ball z δ)ᶜ) :
    ‖∫ w in (ball z δ)ᶜ, m w / (w - z) ^ 2‖ ≤
      L * (∫ w in ball z r, ‖w - z‖⁻¹) + ‖∫ w in (ball z r)ᶜ, m w / (w - z) ^ 2‖ := by
  set A : Set ℂ := ball z r \ ball z δ with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hsplit : (ball z δ)ᶜ = A ∪ (ball z r)ᶜ := by
    ext w
    simp only [hA, mem_compl_iff, mem_union, mem_diff]
    constructor
    · intro h
      by_cases hw : w ∈ ball z r
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr hw
    · rintro (h | h)
      · exact h.2
      · exact fun h' => h (ball_subset_ball hδr h')
  have hdisj : Disjoint A (ball z r)ᶜ := by
    rw [Set.disjoint_left]
    intro w hw hw'
    exact hw' hw.1
  have hAsub : A ⊆ (ball z δ)ᶜ := fun w hw => hw.2
  have hFsub : (ball z r)ᶜ ⊆ (ball z δ)ᶜ := compl_subset_compl.2 (ball_subset_ball hδr)
  have hk : IntegrableOn (fun w : ℂ => ((w - z) ^ 2)⁻¹) A :=
    (s4g_int_ann continuous_const z hδ (R := r) 2).congr_fun (fun w _ => one_mul _) hAm
  have hmA := hm.mono_set hAsub
  have hdA : IntegrableOn (fun w => (m w - m z) / (w - z) ^ 2) A :=
    (hmA.sub (hk.const_mul (m z))).congr_fun (fun w _ => by simp only [Pi.sub_apply]; ring) hAm
  have hAeq : (∫ w in A, m w / (w - z) ^ 2) = ∫ w in A, (m w - m z) / (w - z) ^ 2 := by
    have e : (fun w => m w / (w - z) ^ 2) = fun w => (m w - m z) / (w - z) ^ 2 + m z * ((w - z) ^ 2)⁻¹ := by
      funext w
      ring
    rw [e, integral_add hdA (hk.const_mul (m z)), integral_const_mul, s4g_ann_zero, mul_zero, add_zero]
  have hbd : ‖∫ w in A, (m w - m z) / (w - z) ^ 2‖ ≤ ∫ w in A, L * ‖w - z‖⁻¹ := by
    refine norm_integral_le_of_norm_le (((s4g_int_inv_norm_ball z (lt_of_lt_of_le hδ hδr)).mono_set
      sdiff_subset).const_mul L) ?_
    filter_upwards [ae_restrict_mem hAm] with w hw
    have hwz : 0 < ‖w - z‖ := by
      have := hw.2
      rw [mem_ball, not_lt, dist_eq_norm] at this
      linarith
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖m w - m z‖ ≤ L * ‖w - z‖ := hlip w hw.1
      _ = L * ‖w - z‖⁻¹ * ‖w - z‖ ^ 2 := by field_simp
  have hmono : (∫ w in A, L * ‖w - z‖⁻¹) ≤ L * ∫ w in ball z r, ‖w - z‖⁻¹ := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (setIntegral_mono_set
      (s4g_int_inv_norm_ball z (lt_of_lt_of_le hδ hδr)) (Filter.Eventually.of_forall fun w => by positivity)
      (Filter.Eventually.of_forall sdiff_subset)) hL
  rw [hsplit, setIntegral_union hdisj measurableSet_ball.compl hmA (hm.mono_set hFsub), hAeq]
  calc _ ≤ ‖∫ w in A, (m w - m z) / (w - z) ^ 2‖ + ‖∫ w in (ball z r)ᶜ, m w / (w - z) ^ 2‖ :=
        norm_add_le _ _
    _ ≤ _ := by linarith

/-- `f_n ∈ A₂¹(𝔻*)`. -/
theorem s4g_basisF_A21 (n : ℕ) : basisF n ∈ A21fun unitDiscExterior := by
  have hx : Summable fun m : ℕ => ‖(if m = n then (1 : ℂ) else 0)‖ ^ 2 := by
    refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    simp [hm]
  refine (ab112_A21fun_congr wp_exterior_isOpen (φ := fun w => ∑' m, (if m = n then (1 : ℂ) else 0) * basisF m w)
    (ψ := basisF n) ?_).1 (e212_ext_series hx)
  intro w _
  show (∑' m, (if m = n then (1 : ℂ) else 0) * basisF m w) = basisF n w
  rw [tsum_eq_single n (fun m hm => by simp [hm])]
  simp

/-- The exterior Bergman diagonal: `‖e_u‖² = Σ |f_n(u)|² = 1/(π(|u|² - 1)²)`. -/
theorem s4g_sv_norm_sq {u : ℂ} (hu : u ∈ unitDiscExterior) :
    ‖s3st_vector u‖ ^ 2 = 1 / (π * (‖u‖ ^ 2 - 1) ^ 2) := by
  rw [gop_norm_sq]
  have h := e24_sumF hu hu
  have e1 : (fun p : ℕ => basisF p u * conj (basisF p u)) = fun p => ((‖basisF p u‖ ^ 2 : ℝ) : ℂ) := by
    funext p
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (1 / (π * (1 - u * conj u) ^ 2) : ℂ) = ((1 / (π * (‖u‖ ^ 2 - 1) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    first
      | done
      | (push_cast; ring)
  rw [e1, e2] at h
  have hr := Complex.hasSum_ofReal.1 h
  rw [← hr.tsum_eq]
  exact tsum_congr fun p => by rw [s3st_vector_apply hu]

/-- `a x ≤ a²/(2t) + t x²/2`. -/
theorem s4g_amgm (a x : ℝ) {t : ℝ} (ht : 0 < t) : a * x ≤ a ^ 2 / (2 * t) + t * x ^ 2 / 2 := by
  have h := sq_nonneg (a - t * x)
  have e : a ^ 2 / (2 * t) + t * x ^ 2 / 2 = (a ^ 2 + t ^ 2 * x ^ 2) / (2 * t) := by
    field_simp
    first
      | done
      | ring
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Pointwise series for the principal value.** At `z ∈ 𝔻*`, if the truncations of
`∫ μ K₄(·, z)/(w - z)²` converge to `v` and those of `∫ μ f_n/(w - z)²` to `L_n`, then
`v = Σ_n (B₄ e_z)_n L_n` (as a limit of partial sums). The tail `R_N = Σ_{n ≥ N} c_n f_n` is controlled
uniformly in the truncation radius: near `z` by its Lipschitz constant (Cauchy estimates, mean zero of
`(w - z)⁻²` on annuli), far from `z` by its `L²` norm. -/
theorem s4g_pv_series_pt {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) {v : ℂ}
    (hv : Tendsto (fun δ : ℝ => ∫ w in unitDiscExterior \ ball z δ,
      μ w * kerK4 (gsans κ) w z / (w - z) ^ 2) (𝓝[>] 0) (𝓝 v))
    {L : ℕ → ℂ} (hL : ∀ n, Tendsto (fun δ : ℝ => ∫ w in unitDiscExterior \ ball z δ,
      μ w * basisF n w / (w - z) ^ 2) (𝓝[>] 0) (𝓝 (L n))) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n * L n) atTop (𝓝 v) := by
  set D := unitDiscExterior with hDdef
  have hDo : IsOpen D := wp_exterior_isOpen
  have hD : MeasurableSet D := hDo.measurableSet
  set c : ell2 := gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z) with hcdef
  -- the tail vectors
  set c' : ℕ → ell2 := fun N => c - ∑ n ∈ Finset.range N, lp.single 2 n (c n) with hc'def
  have hc'n : ∀ N n, c' N n = c n - if n ∈ Finset.range N then c n else 0 := by
    intro N n
    simp only [hc'def, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
    rw [Finset.sum_pi_single]
  have hc'0 : Tendsto (fun N => ‖c' N‖) atTop (𝓝 0) := by
    have h := (lp.hasSum_single (by norm_num) c).tendsto_sum_nat
    have h2 := (tendsto_const_nhds (x := c)).sub h
    rw [sub_self] at h2
    simpa only [norm_zero] using h2.norm
  set R : ℕ → ℂ → ℂ := fun N w => ∑' n, c' N n * basisF n w with hRdef
  have hRA : ∀ N, R N ∈ A21fun D := fun N => e212_ext_series (gop_l2_summable (c' N))
  have hRhs : ∀ N, ∀ w ∈ D, HasSum (fun n => c' N n * basisF n w) (R N w) := fun N w hw =>
    (bergman_pair_summable (gop_l2_summable (c' N)) (s3st_basisF_sq hw)).of_norm.hasSum
  have hRe : ∀ N, ∀ w ∈ D, R N w = kerK4 (gsans κ) w z - ∑ n ∈ Finset.range N, c n * basisF n w := by
    intro N w hw
    have h1 := s4g_w3_col hκ hz hw
    have h2 : HasSum (fun n => if n ∈ Finset.range N then c n * basisF n w else 0)
        (∑ n ∈ Finset.range N, (if n ∈ Finset.range N then c n * basisF n w else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
    rw [Finset.sum_congr rfl (fun n hn => if_pos hn)] at h2
    refine ((hRhs N w hw).unique ?_)
    convert h1.sub h2 using 1
    funext n
    rw [hc'n]
    split_ifs <;> ring
  have hRbd : ∀ N, ∀ w ∈ D, ‖R N w‖ ≤ ‖c' N‖ * ‖s3st_vector w‖ := by
    intro N w hw
    have he : R N w = inner ℂ (star (s3st_vector w)) (c' N) := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun n => ?_
      rw [gop_inner_apply]
      change c' N n * basisF n w = conj (conj (s3st_vector w n)) * c' N n
      rw [Complex.conj_conj, s3st_vector_apply hw, mul_comm]
    rw [he]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_star, mul_comm]
  have hRpar : ∀ N, (∫ w in D, ‖R N w‖ ^ 2) = ‖c' N‖ ^ 2 := by
    intro N
    have hx := gop_l2_summable (c' N)
    have h := e24_ext_pair hx hx (E := ∅) Set.finite_empty
      (fun u hu _ => hRhs N u hu) (fun u hu _ => hRhs N u hu)
    have e1 : (fun n => c' N n * conj (c' N n)) = fun n => ((‖c' N n‖ ^ 2 : ℝ) : ℂ) := by
      funext n
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e2 : (∫ u in D, R N u * conj (R N u)) = ((∫ u in D, ‖R N u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e1, e2] at h
    rw [gop_norm_sq, ← (Complex.hasSum_ofReal.1 h).tsum_eq]
  -- the radius and the constants
  have hg : ContDiffAt ℝ 1 μ z :=
    ((s4hv_harmonic_smooth hμ).contDiffAt (hDo.mem_nhds hz)).of_le (by simp)
  obtain ⟨Lμ, t, ht, hLt⟩ := hg.exists_lipschitzOnWith
  obtain ⟨ρ0, hρ0, hρ0t⟩ := Metric.mem_nhds_iff.mp ht
  have hz1 : 1 < ‖z‖ := hz
  set r : ℝ := min ρ0 ((‖z‖ - 1) / 4) with hrdef
  have hr : 0 < r := lt_min hρ0 (by linarith)
  have hr4 : 4 * r ≤ ‖z‖ - 1 := by
    have := min_le_right ρ0 ((‖z‖ - 1) / 4)
    linarith
  have hb2 : ∀ u ∈ ball z (2 * r), u ∈ D ∧ 1 + 2 * r ≤ ‖u‖ := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    have h1 : ‖z‖ - ‖u - z‖ ≤ ‖u‖ := by
      have := norm_sub_norm_le z (z - u)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    have h2 : 1 + 2 * r ≤ ‖u‖ := by linarith
    exact ⟨show 1 < ‖u‖ by linarith, h2⟩
  have hbr : ball z r ⊆ ball z (2 * r) := ball_subset_ball (by linarith)
  set S₀ : ℝ := 1 / (4 * r) with hS₀
  have hS₀0 : 0 ≤ S₀ := by positivity
  have hsv : ∀ u ∈ ball z (2 * r), ‖s3st_vector u‖ ≤ S₀ := by
    intro u hu
    obtain ⟨huD, hu2⟩ := hb2 u hu
    have hsq := s4g_sv_norm_sq huD
    have hq : 4 * r ≤ ‖u‖ ^ 2 - 1 := by nlinarith
    have hpi : 1 ≤ π := by linarith [Real.pi_gt_three]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hS₀0 two_ne_zero).1 ?_
    have hq0 : 0 < ‖u‖ ^ 2 - 1 := by linarith
    rw [hsq, hS₀, div_pow, one_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    calc (4 * r) ^ 2 ≤ (‖u‖ ^ 2 - 1) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
      _ = 1 * (‖u‖ ^ 2 - 1) ^ 2 := (one_mul _).symm
      _ ≤ π * (‖u‖ ^ 2 - 1) ^ 2 := mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 D μ).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  have hμM : ∀ w ∈ D, ‖μ w‖ ≤ M := fun w hw => wp_harmonic_pointwise_bound hμ hw
  set Cr : ℝ := ∫ w in ball z r, ‖w - z‖⁻¹ with hCr
  have hCr0 : 0 ≤ Cr := setIntegral_nonneg measurableSet_ball fun w _ => by positivity
  set C₄ : ℝ := ∫ w in (ball z r)ᶜ, (‖w - z‖ ^ 4)⁻¹ with hC₄
  have hC₄i : IntegrableOn (fun w : ℂ => (‖w - z‖ ^ 4)⁻¹) (ball z r)ᶜ := by
    have h : IntegrableOn (fun u : ℂ => ‖((u - z) ^ 4)⁻¹‖) {u : ℂ | r < ‖u - z‖} :=
      (s4g_int_kernel4 z hr).norm
    refine (IntegrableOn.congr_set_ae h (s4g_ballc_ae z r).symm).congr_fun (fun w _ => ?_)
      measurableSet_ball.compl
    simp only [norm_inv, norm_pow]
  have hC₄0 : 0 ≤ C₄ := setIntegral_nonneg measurableSet_ball.compl fun w _ => by positivity
  -- Lipschitz bound for the tail on `B(z, r)`
  have hRlip : ∀ N, ∀ w ∈ ball z r, ‖R N w - R N z‖ ≤ ‖c' N‖ * S₀ / r * ‖w - z‖ := by
    intro N w hw
    have hdiff : DifferentiableOn ℂ (R N) D := (hRA N).1
    refine Convex.norm_image_sub_le_of_norm_deriv_le (s := ball z r)
      (fun x hx => hdiff.differentiableAt (hDo.mem_nhds (hb2 x (hbr hx)).1)) (fun x hx => ?_)
      (convex_ball z r) (mem_ball_self hr) hw
    have hcl : closedBall x r ⊆ ball z (2 * r) := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball] at hx ⊢
      linarith [dist_triangle y x z]
    have hdc : DiffContOnCl ℂ (R N) (ball x r) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball x hr.ne']
      exact hdiff.mono fun y hy => (hb2 y (hcl hy)).1
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc fun y hy => ?_
    have hy2 := hcl (sphere_subset_closedBall hy)
    calc ‖R N y‖ ≤ ‖c' N‖ * ‖s3st_vector y‖ := hRbd N y (hb2 y hy2).1
      _ ≤ ‖c' N‖ * S₀ := mul_le_mul_of_nonneg_left (hsv y hy2) (norm_nonneg _)
  -- the uniform bound on the truncated tail integrals
  have hbound : ∀ N, ∀ δ : ℝ, 0 < δ → δ ≤ r → ∀ τ : ℝ, 0 < τ →
      ‖∫ w in D \ ball z δ, μ w * R N w / (w - z) ^ 2‖ ≤
        ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * Cr + M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ) + τ * C₄ / 2 := by
    intro N δ hδ hδr τ hτ
    set m : ℂ → ℂ := D.indicator fun w => μ w * R N w with hmdef
    have hind : ∀ S : Set ℂ, (∫ w in D \ S, μ w * R N w / (w - z) ^ 2) =
        ∫ w in Sᶜ, m w / (w - z) ^ 2 := by
      intro S
      have e : (fun w => m w / (w - z) ^ 2) = D.indicator (fun w => μ w * R N w / (w - z) ^ 2) := by
        funext w
        by_cases hw : w ∈ D
        · rw [hmdef, indicator_of_mem hw, indicator_of_mem hw]
        · rw [hmdef, indicator_of_notMem hw, indicator_of_notMem hw, zero_div]
      rw [e, setIntegral_indicator hD, Set.sdiff_eq, inter_comm]
    have hmi : IntegrableOn (fun w => m w / (w - z) ^ 2) (ball z δ)ᶜ := by
      have e : (fun w => m w / (w - z) ^ 2) = D.indicator (fun w => μ w * R N w / (w - z) ^ 2) := by
        funext w
        by_cases hw : w ∈ D
        · rw [hmdef, indicator_of_mem hw, indicator_of_mem hw]
        · rw [hmdef, indicator_of_notMem hw, indicator_of_notMem hw, zero_div]
      rw [e, integrableOn_indicator_iff hD]
      have h := s4hv_bounded_Bergman_trunc hμ (hRA N) z hδ
      refine h.congr_set_ae (Filter.EventuallyEq.of_eq ?_)
      rw [Set.sdiff_eq]
    have hlip : ∀ w ∈ ball z r, ‖m w - m z‖ ≤ ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * ‖w - z‖ := by
      intro w hw
      have hwD := (hb2 w (hbr hw)).1
      rw [hmdef, indicator_of_mem hwD, indicator_of_mem hz]
      have hwt : w ∈ t := hρ0t (ball_subset_ball (min_le_left _ _) hw)
      have hzt : z ∈ t := mem_of_mem_nhds ht
      have h1 : ‖μ w - μ z‖ ≤ Lμ * ‖w - z‖ := hLt.norm_sub_le hwt hzt
      have h2 : ‖R N w‖ ≤ ‖c' N‖ * S₀ :=
        (hRbd N w hwD).trans (mul_le_mul_of_nonneg_left (hsv w (hbr hw)) (norm_nonneg _))
      have h3 := hRlip N w hw
      have h4 := hμM z hz
      have e : μ w * R N w - μ z * R N z = (μ w - μ z) * R N w + μ z * (R N w - R N z) := by ring
      rw [e]
      calc ‖(μ w - μ z) * R N w + μ z * (R N w - R N z)‖
          ≤ ‖μ w - μ z‖ * ‖R N w‖ + ‖μ z‖ * ‖R N w - R N z‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (Lμ * ‖w - z‖) * (‖c' N‖ * S₀) + M * (‖c' N‖ * S₀ / r * ‖w - z‖) := by
            gcongr
        _ = ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * ‖w - z‖ := by ring
    have hnear := s4g_pv_near_bound hδ hδr (by positivity) hlip hmi
    -- the far part
    have hfar : ‖∫ w in (ball z r)ᶜ, m w / (w - z) ^ 2‖ ≤ M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ) + τ * C₄ / 2 := by
      have hm2 : IntegrableOn (fun w => ‖m w‖ ^ 2) (ball z r)ᶜ := by
        have h := e212_sq_integrable hDo (hRA N)
        have hI : Integrable (D.indicator fun w => M ^ 2 * ‖R N w‖ ^ 2) :=
          (integrable_indicator_iff hD).2 (h.const_mul _)
        refine (hI.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)).integrableOn
        · exact ((aestronglyMeasurable_indicator_iff hD).2
            (((wp_harmonic_continuousOn hμ).mul (hRA N).1.continuousOn).aestronglyMeasurable hD)).norm.pow 2
        · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          by_cases hw : w ∈ D
          · rw [hmdef, indicator_of_mem hw, indicator_of_mem hw, norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hμM w hw) 2) (sq_nonneg _)
          · rw [hmdef, indicator_of_notMem hw, indicator_of_notMem hw, norm_zero]
            norm_num
      have hm2D : (∫ w in (ball z r)ᶜ, ‖m w‖ ^ 2) ≤ M ^ 2 * ‖c' N‖ ^ 2 := by
        calc (∫ w in (ball z r)ᶜ, ‖m w‖ ^ 2) ≤ ∫ w, ‖m w‖ ^ 2 := by
              refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun w => by positivity)
              have h := e212_sq_integrable hDo (hRA N)
              refine ((integrable_indicator_iff hD).2 (h.const_mul (M ^ 2))).mono' ?_
                (Filter.Eventually.of_forall fun w => ?_)
              · exact ((aestronglyMeasurable_indicator_iff hD).2
                  (((wp_harmonic_continuousOn hμ).mul (hRA N).1.continuousOn).aestronglyMeasurable hD)).norm.pow 2
              · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                by_cases hw : w ∈ D
                · rw [hmdef, indicator_of_mem hw, indicator_of_mem hw, norm_mul, mul_pow]
                  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hμM w hw) 2)
                    (sq_nonneg _)
                · rw [hmdef, indicator_of_notMem hw, indicator_of_notMem hw, norm_zero]
                  norm_num
          _ = ∫ w in D, ‖μ w * R N w‖ ^ 2 := by
              rw [← integral_indicator hD]
              congr 1
              funext w
              by_cases hw : w ∈ D
              · rw [hmdef, indicator_of_mem hw, indicator_of_mem hw]
              · rw [hmdef, indicator_of_notMem hw, indicator_of_notMem hw, norm_zero]
                norm_num
          _ ≤ ∫ w in D, M ^ 2 * ‖R N w‖ ^ 2 := by
              refine setIntegral_mono_on ?_ ((e212_sq_integrable hDo (hRA N)).const_mul _) hD
                (fun w hw => ?_)
              · refine ((e212_sq_integrable hDo (hRA N)).const_mul (M ^ 2)).mono'
                  ((((wp_harmonic_continuousOn hμ).mul (hRA N).1.continuousOn).aestronglyMeasurable hD).norm.pow 2)
                  ?_
                filter_upwards [ae_restrict_mem hD] with w hw
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hμM w hw) 2) (sq_nonneg _)
              · rw [norm_mul, mul_pow]
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hμM w hw) 2) (sq_nonneg _)
          _ = M ^ 2 * ‖c' N‖ ^ 2 := by rw [integral_const_mul, hRpar]
      have hpt : ∀ w ∈ (ball z r)ᶜ, ‖m w / (w - z) ^ 2‖ ≤
          ‖m w‖ ^ 2 / (2 * τ) + τ * (‖w - z‖ ^ 4)⁻¹ / 2 := by
        intro w hw
        have hwz : 0 < ‖w - z‖ := by
          rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm] at hw
          linarith
        have h := s4g_amgm ‖m w‖ (‖w - z‖ ^ 2)⁻¹ hτ
        rw [norm_div, norm_pow, div_eq_mul_inv]
        calc ‖m w‖ * (‖w - z‖ ^ 2)⁻¹ ≤ ‖m w‖ ^ 2 / (2 * τ) + τ * ((‖w - z‖ ^ 2)⁻¹) ^ 2 / 2 := h
          _ = _ := by ring
      have hsum : IntegrableOn (fun w => ‖m w‖ ^ 2 / (2 * τ) + τ * (‖w - z‖ ^ 4)⁻¹ / 2) (ball z r)ᶜ :=
        (hm2.div_const _).add ((hC₄i.const_mul τ).div_const 2)
      calc ‖∫ w in (ball z r)ᶜ, m w / (w - z) ^ 2‖
          ≤ ∫ w in (ball z r)ᶜ, (‖m w‖ ^ 2 / (2 * τ) + τ * (‖w - z‖ ^ 4)⁻¹ / 2) :=
            norm_integral_le_of_norm_le hsum
              (by filter_upwards [ae_restrict_mem measurableSet_ball.compl] with w hw; exact hpt w hw)
        _ = (∫ w in (ball z r)ᶜ, ‖m w‖ ^ 2) / (2 * τ) + τ * C₄ / 2 := by
            rw [integral_add (hm2.div_const _) ((hC₄i.const_mul τ).div_const 2), integral_div,
              integral_div, integral_const_mul]
        _ ≤ M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ) + τ * C₄ / 2 := by
            gcongr
    rw [hind]
    calc _ ≤ ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * Cr + ‖∫ w in (ball z r)ᶜ, m w / (w - z) ^ 2‖ :=
          hnear
      _ ≤ _ := by linarith
  -- the truncated tail integrals converge to `v - Σ_{n<N} c_n L_n`
  have hlim : ∀ N, Tendsto (fun δ : ℝ => ∫ w in D \ ball z δ, μ w * R N w / (w - z) ^ 2) (𝓝[>] 0)
      (𝓝 (v - ∑ n ∈ Finset.range N, c n * L n)) := by
    intro N
    refine (hv.sub (tendsto_finset_sum _ fun n _ => (hL n).const_mul (c n))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : 0 < δ := hδ
    have hS : MeasurableSet (D \ ball z δ) := hD.diff measurableSet_ball
    have hK := s4hv_bounded_Bergman_trunc hμ (s4hv_K4_column_A21 hκ hz) z hδ0
    have hF : ∀ n, IntegrableOn (fun w => μ w * basisF n w / (w - z) ^ 2) (D \ ball z δ) :=
      fun n => s4hv_bounded_Bergman_trunc hμ (s4g_basisF_A21 n) z hδ0
    have e1 : (∫ w in D \ ball z δ, μ w * R N w / (w - z) ^ 2) =
        ∫ w in D \ ball z δ, μ w * (kerK4 (gsans κ) w z - ∑ n ∈ Finset.range N, c n * basisF n w) /
          (w - z) ^ 2 :=
      setIntegral_congr_fun hS (fun w hw => by simp only [hRe N w hw.1])
    rw [e1]
    have e : (fun w => μ w * (kerK4 (gsans κ) w z - ∑ n ∈ Finset.range N, c n * basisF n w) / (w - z) ^ 2) =
        fun w => μ w * kerK4 (gsans κ) w z / (w - z) ^ 2 -
          ∑ n ∈ Finset.range N, c n * (μ w * basisF n w / (w - z) ^ 2) := by
      funext w
      rw [mul_sub, sub_div, Finset.mul_sum, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [e, integral_sub hK (integrable_finset_sum _ fun n _ => (hF n).const_mul (c n)),
      integral_finset_sum _ fun n _ => (hF n).const_mul (c n)]
    simp only [integral_const_mul]
    first
      | done
      | rfl
  -- conclusion
  have hP : ∀ N, ∀ τ : ℝ, 0 < τ → ‖v - ∑ n ∈ Finset.range N, c n * L n‖ ≤
      ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * Cr + M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ) + τ * C₄ / 2 := by
    intro N τ hτ
    refine le_of_tendsto (hlim N).norm ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    exact hbound N δ hδ.1 hδ.2.le τ hτ
  rw [Metric.tendsto_atTop]
  intro ε hε
  set τ : ℝ := ε / (2 * (C₄ + 1)) with hτdef
  have hτ : 0 < τ := by positivity
  have hτC : τ * C₄ / 2 < ε / 2 := by
    rw [hτdef]
    rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
    calc ε / (2 * (C₄ + 1)) * C₄ < ε / (2 * (C₄ + 1)) * (2 * (C₄ + 1)) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = ε := by field_simp
  have hT : Tendsto (fun N => ((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * Cr +
      M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ)) atTop (𝓝 0) := by
    have h := ((hc'0.const_mul (((Lμ : ℝ) * S₀ + M * (S₀ / r)))).mul_const Cr).add
      (((hc'0.pow 2).const_mul (M ^ 2)).div_const (2 * τ))
    simpa using h
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hT (ε / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := hN₀ N hN
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := hP N τ hτ
  rw [dist_eq_norm, norm_sub_rev]
  have h3 := le_abs_self (((Lμ : ℝ) * S₀ + M * (S₀ / r)) * ‖c' N‖ * Cr + M ^ 2 * ‖c' N‖ ^ 2 / (2 * τ))
  linarith

/-- The indicator of a function continuous on an open set is measurable. -/
theorem s4g_meas_ind {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ} (hφ : ContinuousOn φ U) :
    Measurable (U.indicator φ) := by
  rw [← Set.piecewise_eq_indicator]
  exact hφ.measurable_piecewise continuousOn_const hU.measurableSet

/-- The diagonal of `𝔻* × 𝔻*` is null. -/
theorem s4g_offdiag_ae :
    ∀ᵐ q ∂(volume.restrict (unitDiscExterior ×ˢ unitDiscExterior)),
      q ∈ {q : ℂ × ℂ | q.1 ∈ unitDiscExterior ∧ q.2 ∈ unitDiscExterior ∧ q.1 ≠ q.2} := by
  have hdiag : (volume : Measure (ℂ × ℂ)) {q | q.1 = q.2} = 0 := by
    rw [Measure.volume_eq_prod]
    have hm : MeasurableSet {q : ℂ × ℂ | q.1 = q.2} := measurableSet_diagonal
    rw [Measure.measure_prod_null hm]
    refine Filter.Eventually.of_forall fun a => ?_
    have : Prod.mk a ⁻¹' {q : ℂ × ℂ | q.1 = q.2} = {a} := by
      ext b
      simp [eq_comm]
    simp [this]
  have h1 : ∀ᵐ q ∂(volume : Measure (ℂ × ℂ)), q.1 ≠ q.2 := by
    rw [ae_iff]
    simpa using hdiag
  filter_upwards [ae_restrict_of_ae h1,
    ae_restrict_mem (wp_exterior_isOpen.prod wp_exterior_isOpen).measurableSet] with q hq hm
  exact ⟨hm.1, hm.2, hq⟩

/-- `K₄` is a.e. strongly measurable on `𝔻* × 𝔻*` (continuous off the diagonal). -/
theorem s4g_K4_aesm {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    AEStronglyMeasurable (fun q : ℂ × ℂ => kerK4 (gsans κ) q.1 q.2)
      (volume.restrict (unitDiscExterior ×ˢ unitDiscExterior)) := by
  set D' := {q : ℂ × ℂ | q.1 ∈ unitDiscExterior ∧ q.2 ∈ unitDiscExterior ∧ q.1 ≠ q.2} with hD'
  have hDo : IsOpen D' :=
    (wp_exterior_isOpen.preimage continuous_fst).inter
      ((wp_exterior_isOpen.preimage continuous_snd).inter (isOpen_ne_fun continuous_fst continuous_snd))
  have hcg := S2C.s2c_conf_g hκ
  have hgc : ContinuousOn (gsans κ) unitDiscExterior := hcg.1.continuousOn
  have hg'c : ContinuousOn (deriv (gsans κ)) unitDiscExterior :=
    (hcg.1.deriv wp_exterior_isOpen).continuousOn
  have hcont : ContinuousOn (fun q : ℂ × ℂ => kerK4 (gsans κ) q.1 q.2) D' := by
    have h1 : ContinuousOn (fun q : ℂ × ℂ => 1 / π * (1 / (q.1 - q.2) ^ 2 -
        deriv (gsans κ) q.1 * deriv (gsans κ) q.2 / (gsans κ q.1 - gsans κ q.2) ^ 2)) D' := by
      refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
      · refine continuousOn_const.div ((continuous_fst.sub continuous_snd).pow 2).continuousOn ?_
        intro q hq
        exact pow_ne_zero 2 (sub_ne_zero.2 hq.2.2)
      · refine ContinuousOn.div ?_ ?_ ?_
        · exact (hg'c.comp continuous_fst.continuousOn fun q hq => hq.1).mul
            (hg'c.comp continuous_snd.continuousOn fun q hq => hq.2.1)
        · exact ((hgc.comp continuous_fst.continuousOn fun q hq => hq.1).sub
            (hgc.comp continuous_snd.continuousOn fun q hq => hq.2.1)).pow 2
        · intro q hq
          exact pow_ne_zero 2 (sub_ne_zero.2 fun h => hq.2.2 (hcg.2.1 hq.1 hq.2.1 h))
    refine h1.congr fun q hq => ?_
    simp only [kerK4, if_neg hq.2.2]
  have hae := hcont.aestronglyMeasurable (μ := volume) hDo.measurableSet
  have hset : (unitDiscExterior ×ˢ unitDiscExterior : Set (ℂ × ℂ)) =ᵐ[volume] D' := by
    have h := s4g_offdiag_ae
    have hm : MeasurableSet (unitDiscExterior ×ˢ unitDiscExterior : Set (ℂ × ℂ)) :=
      (wp_exterior_isOpen.prod wp_exterior_isOpen).measurableSet
    rw [ae_restrict_iff' hm] at h
    exact Filter.eventuallyEq_set.2 (h.mono fun q hq => ⟨hq, fun hd => ⟨hd.1, hd.2.1⟩⟩)
  rwa [Measure.restrict_congr_set hset]

/-- `K₄` is symmetric. -/
theorem s4g_kerK4_symm (g : ℂ → ℂ) (w z : ℂ) : kerK4 g w z = kerK4 g z w := by
  by_cases h : w = z
  · rw [h]
  · rw [kerK4_of_ne g h, kerK4_of_ne g (Ne.symm h)]
    rw [show (z - w) ^ 2 = (w - z) ^ 2 by ring, show (g z - g w) ^ 2 = (g w - g z) ^ 2 by ring, mul_comm (deriv g z)]

/-- `‖x‖ₑ² = ofReal ‖x‖²`. -/
theorem s4g_enorm_sq (x : ℂ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- `Σ_n |f_n(w)|² = 1/(π(|w|² - 1)²)` in `ℝ≥0∞`. -/
theorem s4g_sumF_enorm {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∑' n, ‖basisF n w‖ₑ ^ 2 = ENNReal.ofReal (1 / (π * (‖w‖ ^ 2 - 1) ^ 2)) := by
  have hs := s3st_basisF_sq hw
  have h := s4g_sv_norm_sq hw
  rw [gop_norm_sq] at h
  simp only [s3st_vector_apply hw] at h
  simp only [s4g_enorm_sq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs, h]

/-- `Σ_n ∫_{𝔻*} |μ f_n|² < ∞` for `μ ∈ L²` harmonic. -/
theorem s4g_fn_L2sum {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∑' n, ∫⁻ w in unitDiscExterior, ‖μ w * basisF n w‖ₑ ^ 2 < ∞ := by
  obtain ⟨φ, -, -, hfin⟩ := id hμ
  have hD : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hlt : (∫⁻ z in unitDiscExterior, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) < ∞ := by
    have h := hfin
    rw [normL2] at h
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h
  have hmeas : ∀ n, AEMeasurable (fun w => ‖μ w * basisF n w‖ₑ ^ 2) (volume.restrict unitDiscExterior) := by
    intro n
    have hc : ContinuousOn (fun w => μ w * basisF n w) unitDiscExterior :=
      (wp_harmonic_continuousOn hμ).mul (s4g_basisF_A21 n).1.continuousOn
    exact ((hc.aestronglyMeasurable hD).aemeasurable.enorm).pow_const 2
  rw [← lintegral_tsum hmeas]
  refine lt_of_le_of_lt (le_of_eq ?_) (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 1 / (4 * π))) hlt)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hD (fun w hw => ?_)
  simp only [enorm_mul, mul_pow]
  rw [ENNReal.tsum_mul_left, s4g_sumF_enorm hw]
  have hw1 : 1 < ‖w‖ := hw
  have hq : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  have e : (1 / (π * (‖w‖ ^ 2 - 1) ^ 2)) = 1 / (4 * π) * rho w := by
    rw [rho]
    have : (1 - ‖w‖ ^ 2) ^ 2 = (‖w‖ ^ 2 - 1) ^ 2 := by ring
    rw [this]
    field_simp
    first
      | done
      | ring
  rw [e, ENNReal.ofReal_mul (by positivity)]
  rw [enorm_eq_nnnorm]
  ring

/-- `∫_{𝔻*} Σ_n |(B₄ e_z)_n|² dz < ∞` on `T₀(1)`. -/
theorem s4g_c_L2sum {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    ∫⁻ z in unitDiscExterior,
      ∑' n, ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ₑ ^ 2 < ∞ := by
  have hD : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hK := s4g_w3_K4_L2 hκ hκT
  have hpt : ∀ z ∈ unitDiscExterior,
      ∑' n, ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ₑ ^ 2 =
        ∫⁻ w in unitDiscExterior, ‖kerK4 (gsans κ) w z‖ₑ ^ 2 := by
    intro z hz
    have hp := s4g_w3_col_parseval hκ hz
    simp only [s4g_enorm_sq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hp.summable, hp.tsum_eq,
      ofReal_integral_eq_lintegral_ofReal
        (e212_sq_integrable wp_exterior_isOpen (s4hv_K4_column_A21 hκ hz))
        (Filter.Eventually.of_forall fun w => by positivity)]
  rw [setLIntegral_congr_fun hD hpt]
  have hm : AEMeasurable (fun q : ℂ × ℂ => ‖kerK4 (gsans κ) q.1 q.2‖ₑ ^ 2)
      ((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((s4g_K4_aesm hκ).aemeasurable.enorm).pow_const 2
  have e := lintegral_prod_symm _ hm
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at e
  rw [← e]
  simpa only [enorm_eq_nnnorm] using hK

/-- `H f` is a.e. strongly measurable for `f ∈ L²`. -/
theorem s4g_hilbertH_aesm {f : ℂ → ℂ} (hf : MemLp f 2) : AEStronglyMeasurable (hilbertH f) volume := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) := by simpa using hf
  obtain ⟨ns, -, hns⟩ := hilbertH_exists_seq_tendsto_ae (p := 2) one_lt_two hf'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun k =>
    (i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff one_le_two hf' (ns k))
      (hilbertHApprox_hasCompactSupport f (ns k))).2.1.continuous.aestronglyMeasurable) hns

/-- `eLpNorm f 2` through the lintegral of `‖f‖²`. -/
theorem s4g_eLpNorm_two {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume = (∫⁻ w, ‖f w‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

/-- `MemLp f 2` from a finite lintegral of `‖f‖²`. -/
theorem s4g_memLp_of_lint {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∫⁻ w, ‖f w‖ₑ ^ 2 < ∞) : MemLp f 2 := by
  show eLpNorm f 2 volume < ∞
  rw [s4g_eLpNorm_two hf]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/-- `H` preserves `∫ ‖·‖²`. -/
theorem s4g_lint_H {f : ℂ → ℂ} (hf : MemLp f 2) (hfm : AEStronglyMeasurable f volume) :
    ∫⁻ w, ‖hilbertH f w‖ₑ ^ 2 = ∫⁻ w, ‖f w‖ₑ ^ 2 := by
  have h := (hilbertH_memLp_two hf).2
  rw [s4g_eLpNorm_two (s4g_hilbertH_aesm hf), s4g_eLpNorm_two hfm] at h
  have h2 := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) h
  simp only [← ENNReal.rpow_mul] at h2
  norm_num at h2
  exact h2

/-- `∫ ‖1_D φ‖² = ∫_D ‖φ‖²`. -/
theorem s4g_lint_ind {D : Set ℂ} (hD : MeasurableSet D) (φ : ℂ → ℂ) :
    ∫⁻ w, ‖D.indicator φ w‖ₑ ^ 2 = ∫⁻ w in D, ‖φ w‖ₑ ^ 2 := by
  rw [← lintegral_indicator hD]
  congr 1
  funext w
  by_cases hw : w ∈ D
  · rw [indicator_of_mem hw, indicator_of_mem hw]
  · rw [indicator_of_notMem hw, indicator_of_notMem hw, enorm_zero]
    norm_num

/-- The row expansion `(B₄ e_z)_n = Σ_m (B₄)_{nm} f_m(z)` and continuity in `z`. -/
theorem s4g_c_row {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (n : ℕ) :
    Summable (fun m => ‖B4 (grunsky (fsans κ) (gsans κ)) n m‖ ^ 2) ∧
    (∀ z ∈ unitDiscExterior, (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n =
      ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m * basisF m z) ∧
    ContinuousOn (fun z => (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n) unitDiscExterior := by
  have hB : IsBoundedMat (B4 (grunsky (fsans κ) (gsans κ))) := pgb_bounded hκ (by simp)
  have hrow : Summable (fun m => ‖B4 (grunsky (fsans κ) (gsans κ)) n m‖ ^ 2) := isBoundedMat_row_isL2 hB n
  have he : ∀ z ∈ unitDiscExterior, (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n =
      ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m * basisF m z := by
    intro z hz
    rw [pmb_apply hB]
    exact tsum_congr fun m => by rw [s3st_vector_apply hz]
  refine ⟨hrow, he, ?_⟩
  exact (e212_ext_series hrow).1.continuousOn.congr he

/-- **The principal-value pairing as a series.** On `T₀(1)`, with `f_n = 1_{𝔻*} μ f_n` and
`c_n(z) = (B₄ e_z)_n`: `∫_{𝔻*} v_μ ν = Σ_n -π ∫_{𝔻*} ν c_n H f_n`, where `v_μ(z)` is the principal value of
`∫ μ K₄(·, z)/(w - z)²`. -/
theorem s4g_w3_vpair {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) {vμ : ℂ → ℂ}
    (hvμ : ∀ z ∈ unitDiscExterior, Tendsto (fun δ : ℝ => ∫ w in unitDiscExterior \ ball z δ,
      μ w * kerK4 (gsans κ) w z / (w - z) ^ 2) (𝓝[>] 0) (𝓝 (vμ z))) :
    IntegrableOn (fun z => vμ z * ν z) unitDiscExterior ∧
      HasSum (fun n => -(π : ℂ) * ∫ z in unitDiscExterior,
        ν z * (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n *
          hilbertH (unitDiscExterior.indicator fun w => μ w * basisF n w) z)
        (∫ z in unitDiscExterior, vμ z * ν z) := by
  set D := unitDiscExterior with hDdef
  have hDo : IsOpen D := wp_exterior_isOpen
  have hD : MeasurableSet D := hDo.measurableSet
  set c : ℂ → ell2 := fun z => gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z) with hcdef
  set f : ℕ → ℂ → ℂ := fun n => D.indicator fun w => μ w * basisF n w with hfdef
  have hFc : ∀ n, ContinuousOn (fun w => μ w * basisF n w) D := fun n =>
    (wp_harmonic_continuousOn hμ).mul (s4g_basisF_A21 n).1.continuousOn
  have hfm : ∀ n, Measurable (f n) := fun n => s4g_meas_ind hDo (hFc n)
  have hfsum := s4g_fn_L2sum hμ
  have hflint : ∀ n, ∫⁻ w, ‖f n w‖ₑ ^ 2 = ∫⁻ w in D, ‖μ w * basisF n w‖ₑ ^ 2 := fun n =>
    s4g_lint_ind hD _
  have hf2 : ∀ n, MemLp (f n) 2 := fun n =>
    s4g_memLp_of_lint (hfm n).aestronglyMeasurable
      (by
        rw [hflint n]
        exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ w in D, ‖μ w * basisF k w‖ₑ ^ 2) n) hfsum)
  have hfs : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f n) D := by
    intro n
    have h1 := s4hv_harmonic_smooth hμ
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (basisF n) D :=
      ((s4g_basisF_A21 n).1.contDiffOn hDo).restrict_scalars ℝ
    exact (h1.mul h2).congr fun w hw => indicator_of_mem (show w ∈ D from hw) _
  -- the truncations of `f n` are those of `μ f_n` on `𝔻*`
  have htr : ∀ n z δ, (∫ w in (ball z δ)ᶜ, f n w / (w - z) ^ 2) =
      ∫ w in D \ ball z δ, μ w * basisF n w / (w - z) ^ 2 := by
    intro n z δ
    have e : (fun w => f n w / (w - z) ^ 2) = D.indicator (fun w => μ w * basisF n w / (w - z) ^ 2) := by
      funext w
      by_cases hw : w ∈ D
      · rw [hfdef]; simp only [indicator_of_mem hw]
      · rw [hfdef]; simp only [indicator_of_notMem hw, zero_div]
    rw [e, setIntegral_indicator hD, Set.sdiff_eq, inter_comm]
  have hpv : ∀ n, ∀ᵐ z ∂(volume.restrict D), Tendsto (fun δ : ℝ =>
      ∫ w in D \ ball z δ, μ w * basisF n w / (w - z) ^ 2) (𝓝[>] 0) (𝓝 (-(π : ℂ) * hilbertH (f n) z)) := by
    intro n
    filter_upwards [(s4g_pv_H (hfm n) (hf2 n) hDo (hfs n)).2] with z hz
    simpa only [htr] using hz
  -- `Σ_n |H f_n|²` is integrable
  have hHm : ∀ n, AEStronglyMeasurable (hilbertH (f n)) volume := fun n => s4g_hilbertH_aesm (hf2 n)
  have hHsum : ∫⁻ z in D, ∑' n, ‖hilbertH (f n) z‖ₑ ^ 2 < ∞ := by
    rw [lintegral_tsum fun n => (((hHm n).aemeasurable.enorm).pow_const 2).restrict]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => ?_) hfsum
    calc (∫⁻ z in D, ‖hilbertH (f n) z‖ₑ ^ 2) ≤ ∫⁻ z, ‖hilbertH (f n) z‖ₑ ^ 2 := setLIntegral_le_lintegral _ _
      _ = _ := by rw [s4g_lint_H (hf2 n) (hfm n).aestronglyMeasurable, hflint n]
  have hcsum := s4g_c_L2sum hκ hκT
  have hcc : ∀ n, ContinuousOn (fun z => c z n) D := fun n => (s4g_c_row hκ n).2.2
  have hcm : ∀ n, AEStronglyMeasurable (fun z => c z n) (volume.restrict D) := fun n =>
    (hcc n).aestronglyMeasurable hD
  -- a.e. summability of `Σ |H f_n|²`
  have hHsumm : ∀ᵐ z ∂(volume.restrict D), Summable fun n => ‖hilbertH (f n) z‖ ^ 2 := by
    have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (((hHm n).aemeasurable.enorm).pow_const 2).restrict)
      hHsum.ne
    filter_upwards [hae] with z hz
    have e : ∀ n, ‖hilbertH (f n) z‖ₑ ^ 2 = ((‖hilbertH (f n) z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      intro n
      rw [enorm_eq_nnnorm, ENNReal.coe_pow]
    simp only [e] at hz
    have hs := ENNReal.tsum_coe_ne_top_iff_summable.1 hz.ne
    exact (NNReal.summable_coe.2 hs).congr fun n => by simp
  -- the series at almost every point
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 D ν).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  have hνM : ∀ z ∈ D, ‖ν z‖ ≤ M := fun z hz => wp_harmonic_pointwise_bound hν hz
  have hlim : ∀ᵐ z ∂(volume.restrict D), HasSum (fun n => -(π : ℂ) * (ν z * c z n * hilbertH (f n) z))
      (vμ z * ν z) := by
    filter_upwards [ae_all_iff.2 hpv, hHsumm, ae_restrict_mem hD] with z hz hs hzD
    have hser := s4g_pv_series_pt hκ hμ hzD (hvμ z hzD) (L := fun n => -(π : ℂ) * hilbertH (f n) z) hz
    have hsum : Summable fun n => c z n * (-(π : ℂ) * hilbertH (f n) z) := by
      refine Summable.of_norm_bounded (g := fun n => π * ((‖c z n‖ ^ 2 + ‖hilbertH (f n) z‖ ^ 2) / 2))
        (((gop_l2_summable (c z)).add hs).div_const 2 |>.mul_left π) fun n => ?_
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have := two_mul_le_add_sq ‖c z n‖ ‖hilbertH (f n) z‖
      nlinarith [Real.pi_pos, norm_nonneg (c z n), norm_nonneg (hilbertH (f n) z)]
    have hv : vμ z = ∑' n, c z n * (-(π : ℂ) * hilbertH (f n) z) :=
      tendsto_nhds_unique hser hsum.hasSum.tendsto_sum_nat
    have h := hsum.hasSum.mul_right (ν z)
    rw [← hv] at h
    convert h using 1
    funext n
    ring
  -- the dominating series
  set bnd : ℕ → ℂ → ℝ := fun n z => π * M * ((‖c z n‖ ^ 2 + ‖hilbertH (f n) z‖ ^ 2) / 2) with hbnd
  have hbound : ∀ n, ∀ᵐ z ∂(volume.restrict D), ‖-(π : ℂ) * (ν z * c z n * hilbertH (f n) z)‖ ≤ bnd n z := by
    intro n
    filter_upwards [ae_restrict_mem hD] with z hz
    rw [hbnd, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_mul, norm_mul]
    have h1 := hνM z hz
    have h2 := two_mul_le_add_sq ‖c z n‖ ‖hilbertH (f n) z‖
    have h3 : ‖c z n‖ * ‖hilbertH (f n) z‖ ≤ (‖c z n‖ ^ 2 + ‖hilbertH (f n) z‖ ^ 2) / 2 := by linarith
    calc π * (‖ν z‖ * ‖c z n‖ * ‖hilbertH (f n) z‖) = π * (‖ν z‖ * (‖c z n‖ * ‖hilbertH (f n) z‖)) := by ring
      _ ≤ π * (M * ((‖c z n‖ ^ 2 + ‖hilbertH (f n) z‖ ^ 2) / 2)) := by
          gcongr
      _ = _ := by ring
  have hbsum : ∀ᵐ z ∂(volume.restrict D), Summable fun n => bnd n z := by
    filter_upwards [hHsumm] with z hs
    exact (((gop_l2_summable (c z)).add hs).div_const 2).mul_left (π * M)
  have hint_c : Integrable (fun z => ∑' n, ‖c z n‖ ^ 2) (volume.restrict D) := by
    have h := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict D)
      (AEMeasurable.ennreal_tsum fun n => ((hcm n).aemeasurable.enorm).pow_const 2) hcsum.ne
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [ENNReal.tsum_toReal_eq fun n => ENNReal.pow_ne_top enorm_ne_top]
    exact tsum_congr fun n => by rw [s4g_enorm_sq, ENNReal.toReal_ofReal (by positivity)]
  have hint_H : Integrable (fun z => ∑' n, ‖hilbertH (f n) z‖ ^ 2) (volume.restrict D) := by
    have h := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict D)
      (AEMeasurable.ennreal_tsum fun n => (((hHm n).aemeasurable.enorm).pow_const 2).restrict) hHsum.ne
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [ENNReal.tsum_toReal_eq fun n => ENNReal.pow_ne_top enorm_ne_top]
    exact tsum_congr fun n => by rw [s4g_enorm_sq, ENNReal.toReal_ofReal (by positivity)]
  have hbint : Integrable (fun z => ∑' n, bnd n z) (volume.restrict D) := by
    refine ((hint_c.add hint_H).const_mul (π * M / 2)).congr ?_
    filter_upwards [hHsumm] with z hs
    simp only [hbnd]
    rw [tsum_mul_left, tsum_div_const, (gop_l2_summable (c z)).tsum_add hs]
    simp only [Pi.add_apply]
    ring
  have hFm : ∀ n, AEStronglyMeasurable (fun z => -(π : ℂ) * (ν z * c z n * hilbertH (f n) z))
      (volume.restrict D) := fun n =>
    (((((wp_harmonic_continuousOn hν).aestronglyMeasurable hD).mul (hcm n)).mul
      (hHm n).restrict).const_mul _)
  have hmain := hasSum_integral_of_dominated_convergence bnd hFm hbound hbsum hbint hlim
  refine ⟨?_, ?_⟩
  · refine hbint.mono' ?_ ?_
    · exact aestronglyMeasurable_of_tendsto_ae atTop
        (fun N => Finset.aestronglyMeasurable_sum _ fun n _ => hFm n)
        (by filter_upwards [hlim] with z hz; simpa only [Finset.sum_apply] using hz.tendsto_sum_nat)
    · filter_upwards [hlim, hbsum, ae_all_iff.2 hbound] with z hz hbs hb
      exact hz.norm_le_of_bounded hbs.hasSum hb
  · have e : (fun n => ∫ z in D, -(π : ℂ) * (ν z * c z n * hilbertH (f n) z)) =
        fun n => -(π : ℂ) * ∫ z in D, ν z * c z n * hilbertH (f n) z := by
      funext n
      rw [integral_const_mul]
    rw [e] at hmain
    exact hmain

/-- `∫ ‖g‖² = (∫⁻ ‖g‖²).toReal`. -/
theorem s4g_int_sq_toReal {g : ℂ → ℂ} {m : Measure ℂ} (hg : AEStronglyMeasurable g m) :
    ∫ w, ‖g w‖ ^ 2 ∂m = (∫⁻ w, ‖g w‖ₑ ^ 2 ∂m).toReal := by
  have hm : AEStronglyMeasurable (fun w => ‖g w‖ ^ 2) m := hg.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity) hm]
  congr 1
  exact lintegral_congr fun w => (s4g_enorm_sq _).symm

/-- **Row expansion of the pairing.** For `h ∈ L²`: `∫_{𝔻*} ν c_n h = Σ_m (B₄)_{nm} ∫ (1_{𝔻*} ν f_m) h`, with
`c_n(z) = (B₄ e_z)_n = Σ_m (B₄)_{nm} f_m(z)` converging in `L²(𝔻*)`. -/
theorem s4g_w3_row {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {h : ℂ → ℂ} (hh : MemLp h 2) (hhm : AEStronglyMeasurable h volume)
    (n : ℕ) :
    HasSum (fun m => B4 (grunsky (fsans κ) (gsans κ)) n m *
        ∫ w, unitDiscExterior.indicator (fun u => ν u * basisF m u) w * h w)
      (∫ z in unitDiscExterior, ν z * (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n * h z) := by
  set D := unitDiscExterior with hDdef
  have hDo : IsOpen D := wp_exterior_isOpen
  have hD : MeasurableSet D := hDo.measurableSet
  set B := B4 (grunsky (fsans κ) (gsans κ)) with hBdef
  obtain ⟨hrow, hce, hcc⟩ := s4g_c_row hκ n
  set c : ℂ → ℂ := fun z => (gopOp B (s3st_vector z)) n with hcdef
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 D ν).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  have hνM : ∀ z ∈ D, ‖ν z‖ ≤ M := fun z hz => wp_harmonic_pointwise_bound hν hz
  have hνc : ContinuousOn ν D := wp_harmonic_continuousOn hν
  have hh2 : Integrable (fun w => ‖h w‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hhm).1 hh
  set Hh : ℝ := ∫ w, ‖h w‖ ^ 2 with hHh
  have hHh0 : 0 ≤ Hh := integral_nonneg fun w => by positivity
  -- integrability of `ν φ h` on `𝔻*` for `φ ∈ L²(𝔻*)` continuous
  have hint : ∀ {φ : ℂ → ℂ}, ContinuousOn φ D → IntegrableOn (fun z => ‖φ z‖ ^ 2) D →
      IntegrableOn (fun z => ν z * φ z * h z) D := by
    intro φ hφc hφ2
    refine ((hφ2.const_mul (M ^ 2 / 2)).add (hh2.integrableOn.div_const 2)).mono' ?_ ?_
    · exact ((hνc.mul hφc).aestronglyMeasurable hD).mul hhm.restrict
    · filter_upwards [ae_restrict_mem hD] with z hz
      rw [norm_mul, norm_mul]
      have h1 := hνM z hz
      have h2 := s4g_amgm (M * ‖φ z‖) ‖h z‖ (t := 1) one_pos
      have h3 : ‖ν z‖ * ‖φ z‖ * ‖h z‖ ≤ M * ‖φ z‖ * ‖h z‖ := by gcongr
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖φ z‖), sq_nonneg M]
  have hFi : ∀ m, IntegrableOn (fun z => ν z * basisF m z * h z) D := fun m =>
    hint (s4g_basisF_A21 m).1.continuousOn (e212_sq_integrable hDo (s4g_basisF_A21 m))
  have hterm : ∀ m, (∫ w, D.indicator (fun u => ν u * basisF m u) w * h w) =
      ∫ z in D, ν z * basisF m z * h z := by
    intro m
    rw [← integral_indicator hD]
    congr 1
    funext w
    by_cases hw : w ∈ D
    · rw [indicator_of_mem hw, indicator_of_mem hw]
    · rw [indicator_of_notMem hw, indicator_of_notMem hw, zero_mul]
  -- the row as an `ℓ²` vector and its tails
  set x : ell2 := ⟨B n, gop_mem_of_summable hrow⟩ with hxdef
  set x' : ℕ → ell2 := fun K => x - ∑ m ∈ Finset.range K, lp.single 2 m (x m) with hx'def
  have hx'n : ∀ K m, x' K m = B n m - if m ∈ Finset.range K then B n m else 0 := by
    intro K m
    simp only [hx'def, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
    rw [Finset.sum_pi_single]
    first
      | done
      | rfl
  have hx'0 : Tendsto (fun K => ‖x' K‖) atTop (𝓝 0) := by
    have h := (lp.hasSum_single (by norm_num) x).tendsto_sum_nat
    have h2 := (tendsto_const_nhds (x := x)).sub h
    rw [sub_self] at h2
    simpa only [norm_zero] using h2.norm
  set Q : ℕ → ℂ → ℂ := fun K z => ∑' m, x' K m * basisF m z with hQdef
  have hQA : ∀ K, Q K ∈ A21fun D := fun K => e212_ext_series (gop_l2_summable (x' K))
  have hQhs : ∀ K, ∀ z ∈ D, HasSum (fun m => x' K m * basisF m z) (Q K z) := fun K z hz =>
    (bergman_pair_summable (gop_l2_summable (x' K)) (s3st_basisF_sq hz)).of_norm.hasSum
  have hQe : ∀ K, ∀ z ∈ D, Q K z = c z - ∑ m ∈ Finset.range K, B n m * basisF m z := by
    intro K z hz
    have h1 : HasSum (fun m => B n m * basisF m z) (c z) := by
      show HasSum _ ((gopOp B (s3st_vector z)) n)
      rw [hce z hz]
      exact (bergman_pair_summable hrow (s3st_basisF_sq hz)).of_norm.hasSum
    have h2 : HasSum (fun m => if m ∈ Finset.range K then B n m * basisF m z else 0)
        (∑ m ∈ Finset.range K, (if m ∈ Finset.range K then B n m * basisF m z else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun m hm => if_neg hm)
    rw [Finset.sum_congr rfl (fun m hm => if_pos hm)] at h2
    refine ((hQhs K z hz).unique ?_)
    convert h1.sub h2 using 1
    funext m
    rw [hx'n]
    split_ifs <;> ring
  have hQpar : ∀ K, (∫ z in D, ‖Q K z‖ ^ 2) = ‖x' K‖ ^ 2 := by
    intro K
    have hx := gop_l2_summable (x' K)
    have hp := e24_ext_pair hx hx (E := ∅) Set.finite_empty
      (fun u hu _ => hQhs K u hu) (fun u hu _ => hQhs K u hu)
    have e1 : (fun m => x' K m * conj (x' K m)) = fun m => ((‖x' K m‖ ^ 2 : ℝ) : ℂ) := by
      funext m
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e2 : (∫ u in D, Q K u * conj (Q K u)) = ((∫ u in D, ‖Q K u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e1, e2] at hp
    rw [gop_norm_sq, ← (Complex.hasSum_ofReal.1 hp).tsum_eq]
  -- partial sums
  have hc2 : IntegrableOn (fun z => ‖c z‖ ^ 2) D :=
    (e212_sq_integrable hDo (e212_ext_series hrow)).congr_fun
      (fun z hz => by show _ = ‖(gopOp B (s3st_vector z)) n‖ ^ 2; rw [hce z hz]) hD
  have hcint : IntegrableOn (fun z => ν z * c z * h z) D := hint hcc hc2
  have hpart : ∀ K, (∑ m ∈ Finset.range K, B n m * ∫ w, D.indicator (fun u => ν u * basisF m u) w * h w) =
      (∫ z in D, ν z * c z * h z) - ∫ z in D, ν z * Q K z * h z := by
    intro K
    have e : ∀ z ∈ D, ν z * Q K z * h z =
        ν z * c z * h z - ∑ m ∈ Finset.range K, B n m * (ν z * basisF m z * h z) := by
      intro z hz
      rw [hQe K z hz, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [setIntegral_congr_fun hD e, integral_sub hcint
      (integrable_finset_sum _ fun m _ => (hFi m).const_mul _), integral_finset_sum _ fun m _ =>
        (hFi m).const_mul _]
    simp only [integral_const_mul, hterm]
    ring
  have hQb : ∀ K τ, 0 < τ → ‖∫ z in D, ν z * Q K z * h z‖ ≤ M ^ 2 * ‖x' K‖ ^ 2 / (2 * τ) + τ * Hh / 2 := by
    intro K τ hτ
    have hQ2 := e212_sq_integrable hDo (hQA K)
    have hb : IntegrableOn (fun z => M ^ 2 * ‖Q K z‖ ^ 2 / (2 * τ) + τ * ‖h z‖ ^ 2 / 2) D :=
      ((hQ2.const_mul (M ^ 2)).div_const _).add ((hh2.integrableOn.const_mul τ).div_const 2)
    calc ‖∫ z in D, ν z * Q K z * h z‖
        ≤ ∫ z in D, (M ^ 2 * ‖Q K z‖ ^ 2 / (2 * τ) + τ * ‖h z‖ ^ 2 / 2) := by
          refine norm_integral_le_of_norm_le hb ?_
          filter_upwards [ae_restrict_mem hD] with z hz
          rw [norm_mul, norm_mul]
          have h1 := hνM z hz
          have h2 := s4g_amgm (M * ‖Q K z‖) ‖h z‖ hτ
          have h3 : ‖ν z‖ * ‖Q K z‖ * ‖h z‖ ≤ M * ‖Q K z‖ * ‖h z‖ := by gcongr
          calc _ ≤ M * ‖Q K z‖ * ‖h z‖ := h3
            _ ≤ (M * ‖Q K z‖) ^ 2 / (2 * τ) + τ * ‖h z‖ ^ 2 / 2 := h2
            _ = _ := by ring
      _ = M ^ 2 * ‖x' K‖ ^ 2 / (2 * τ) + τ * (∫ z in D, ‖h z‖ ^ 2) / 2 := by
          rw [integral_add ((hQ2.const_mul (M ^ 2)).div_const _) ((hh2.integrableOn.const_mul τ).div_const 2),
            integral_div, integral_div, integral_const_mul, integral_const_mul, hQpar]
      _ ≤ M ^ 2 * ‖x' K‖ ^ 2 / (2 * τ) + τ * Hh / 2 := by
          gcongr
          exact setIntegral_le_integral hh2 (Filter.Eventually.of_forall fun w => by positivity)
  have hlim : Tendsto (fun K => ∑ m ∈ Finset.range K, B n m *
      ∫ w, D.indicator (fun u => ν u * basisF m u) w * h w) atTop (𝓝 (∫ z in D, ν z * c z * h z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set τ : ℝ := ε / (2 * (Hh + 1)) with hτdef
    have hτ : 0 < τ := by positivity
    have hτH : τ * Hh / 2 < ε / 2 := by
      rw [hτdef, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
      calc ε / (2 * (Hh + 1)) * Hh < ε / (2 * (Hh + 1)) * (2 * (Hh + 1)) :=
            mul_lt_mul_of_pos_left (by linarith) (by positivity)
        _ = ε := by field_simp
    have hT : Tendsto (fun K => M ^ 2 * ‖x' K‖ ^ 2 / (2 * τ)) atTop (𝓝 0) := by
      simpa using ((hx'0.pow 2).const_mul (M ^ 2)).div_const (2 * τ)
    obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.1 hT (ε / 2) (by positivity)
    refine ⟨K₀, fun K hK => ?_⟩
    have h1 := hK₀ K hK
    rw [Real.dist_eq, sub_zero] at h1
    rw [dist_eq_norm, hpart K, sub_sub_cancel_left, norm_neg]
    have h2 := hQb K τ hτ
    have h3 := le_abs_self (M ^ 2 * ‖x' K‖ ^ 2 / (2 * τ))
    linarith
  -- absolute summability
  have hgm : ∀ m, Measurable (D.indicator (fun u => ν u * basisF m u)) := fun m =>
    s4g_meas_ind hDo (hνc.mul (s4g_basisF_A21 m).1.continuousOn)
  have hgsum : Summable fun m => ∫ w, ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2 := by
    have hs := s4g_fn_L2sum hν
    have e : ∀ m, ∫ w, ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2 =
        (∫⁻ w in D, ‖ν w * basisF m w‖ₑ ^ 2).toReal := by
      intro m
      rw [s4g_int_sq_toReal (hgm m).aestronglyMeasurable, s4g_lint_ind hD]
    simp only [e]
    exact ENNReal.summable_toReal hs.ne
  have hg2 : ∀ m, Integrable (fun w => ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2) := by
    intro m
    refine ((integrable_indicator_iff hD).2 ((e212_sq_integrable hDo (s4g_basisF_A21 m)).const_mul (M ^ 2))).mono'
      ((hgm m).aestronglyMeasurable.norm.pow 2) (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hw : w ∈ D
    · rw [indicator_of_mem hw, indicator_of_mem hw, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hνM w hw) 2) (sq_nonneg _)
    · rw [indicator_of_notMem hw, indicator_of_notMem hw, norm_zero]
      norm_num
  have hsum : Summable fun m => B n m * ∫ w, D.indicator (fun u => ν u * basisF m u) w * h w := by
    refine Summable.of_norm_bounded
      (g := fun m => (‖B n m‖ ^ 2 * Hh + ∫ w, ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2) / 2)
      (((hrow.mul_right Hh).add hgsum).div_const 2) fun m => ?_
    have hbi : Integrable (fun w => (‖B n m‖ ^ 2 * ‖h w‖ ^ 2 +
        ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2) / 2) :=
      ((hh2.const_mul _).add (hg2 m)).div_const 2
    calc ‖B n m * ∫ w, D.indicator (fun u => ν u * basisF m u) w * h w‖
        = ‖∫ w, B n m * (D.indicator (fun u => ν u * basisF m u) w * h w)‖ := by
          rw [integral_const_mul]
      _ ≤ ∫ w, (‖B n m‖ ^ 2 * ‖h w‖ ^ 2 + ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2) / 2 := by
          refine norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall fun w => ?_)
          rw [norm_mul, norm_mul]
          have := two_mul_le_add_sq (‖B n m‖ * ‖h w‖) ‖D.indicator (fun u => ν u * basisF m u) w‖
          nlinarith [norm_nonneg (B n m), norm_nonneg (h w),
            norm_nonneg (D.indicator (fun u => ν u * basisF m u) w)]
      _ = (‖B n m‖ ^ 2 * Hh + ∫ w, ‖D.indicator (fun u => ν u * basisF m u) w‖ ^ 2) / 2 := by
          rw [integral_div, integral_add (hh2.const_mul _) (hg2 m), integral_const_mul]
  have hv := tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat
  rw [hv]
  exact hsum.hasSum

/-- Row Parseval: `∫_{𝔻*} |(B₄ e_z)_n|² dz = Σ_m |(B₄)_{nm}|²`. -/
theorem s4g_row_parseval {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (n : ℕ) :
    HasSum (fun m => ‖B4 (grunsky (fsans κ) (gsans κ)) n m‖ ^ 2)
      (∫ z in unitDiscExterior, ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ ^ 2) := by
  obtain ⟨hrow, hce, -⟩ := s4g_c_row hκ n
  have hhs : ∀ z ∈ unitDiscExterior, HasSum (fun m => B4 (grunsky (fsans κ) (gsans κ)) n m * basisF m z)
      ((gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n) := by
    intro z hz
    rw [hce z hz]
    exact (bergman_pair_summable hrow (s3st_basisF_sq hz)).of_norm.hasSum
  have hp := e24_ext_pair hrow hrow (E := ∅) Set.finite_empty (fun u hu _ => hhs u hu) (fun u hu _ => hhs u hu)
  have e1 : (fun m => B4 (grunsky (fsans κ) (gsans κ)) n m * conj (B4 (grunsky (fsans κ) (gsans κ)) n m)) =
      fun m => ((‖B4 (grunsky (fsans κ) (gsans κ)) n m‖ ^ 2 : ℝ) : ℂ) := by
    funext m
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (∫ u in unitDiscExterior, (gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector u)) n *
      conj ((gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector u)) n)) =
      ((∫ u in unitDiscExterior, ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector u)) n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, e2] at hp
  exact Complex.hasSum_ofReal.1 hp

/-- On `T₀(1)`, `B₄` is Hilbert–Schmidt: `Σ_{n,m} |(B₄)_{nm}|² < ∞`. -/
theorem s4g_B4_HS {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) :
    Summable fun p : ℕ × ℕ => ‖B4 (grunsky (fsans κ) (gsans κ)) p.1 p.2‖ ^ 2 := by
  have hD : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hc := s4g_c_L2sum hκ hκT
  have hm : ∀ n, AEMeasurable (fun z => ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ₑ ^ 2)
      (volume.restrict unitDiscExterior) := fun n =>
    (((s4g_c_row hκ n).2.2.aestronglyMeasurable hD).aemeasurable.enorm).pow_const 2
  rw [lintegral_tsum hm] at hc
  have hrow : ∀ n, (∫⁻ z in unitDiscExterior,
      ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ₑ ^ 2) =
      ∑' m, ‖B4 (grunsky (fsans κ) (gsans κ)) n m‖ₑ ^ 2 := by
    intro n
    have hp := s4g_row_parseval hκ n
    have hi : IntegrableOn (fun z => ‖(gopOp (B4 (grunsky (fsans κ) (gsans κ))) (s3st_vector z)) n‖ ^ 2)
        unitDiscExterior :=
      (e212_sq_integrable wp_exterior_isOpen (e212_ext_series (s4g_c_row hκ n).1)).congr_fun
        (fun z hz => by rw [(s4g_c_row hκ n).2.1 z hz]) hD
    simp only [s4g_enorm_sq]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => by positivity),
      ← hp.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hp.summable]
  simp only [hrow] at hc
  rw [← ENNReal.tsum_prod] at hc
  have e : ∀ p : ℕ × ℕ, ‖B4 (grunsky (fsans κ) (gsans κ)) p.1 p.2‖ₑ ^ 2 =
      ((‖B4 (grunsky (fsans κ) (gsans κ)) p.1 p.2‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    intro p
    rw [enorm_eq_nnnorm, ENNReal.coe_pow]
  simp only [e] at hc
  exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hc.ne)).congr fun p => by simp

/-- `(‖f‖₂)² = ∫ ‖f‖²`. -/
theorem s4g_eLp_sq {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    (eLpNorm f 2 volume).toReal ^ 2 = ∫ w, ‖f w‖ ^ 2 := by
  rw [s4g_eLpNorm_two hf, s4g_int_sq_toReal hf, ← ENNReal.toReal_pow, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- `Σ_n ‖1_{𝔻*} μ f_n‖₂² < ∞`. -/
theorem s4g_fn_eLp_summable {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    Summable fun n => (eLpNorm (unitDiscExterior.indicator fun w => μ w * basisF n w) 2 volume).toReal ^ 2 := by
  have hD : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hm : ∀ n, Measurable (unitDiscExterior.indicator fun w => μ w * basisF n w) := fun n =>
    s4g_meas_ind wp_exterior_isOpen ((wp_harmonic_continuousOn hμ).mul (s4g_basisF_A21 n).1.continuousOn)
  have e : ∀ n, (eLpNorm (unitDiscExterior.indicator fun w => μ w * basisF n w) 2 volume).toReal ^ 2 =
      (∫⁻ w in unitDiscExterior, ‖μ w * basisF n w‖ₑ ^ 2).toReal := by
    intro n
    rw [s4g_eLp_sq (hm n).aestronglyMeasurable, s4g_int_sq_toReal (hm n).aestronglyMeasurable, s4g_lint_ind hD]
  simp only [e]
  exact ENNReal.summable_toReal (s4g_fn_L2sum hμ).ne

/-- **Symmetry of the double series** (`B₄ = B₄ᵀ`, `∫ (H g) f = ∫ g (H f)`, Hilbert–Schmidt summability). -/
theorem s4g_w3_dsym {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    (∑' n, ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m *
        ∫ w, unitDiscExterior.indicator (fun u => ν u * basisF m u) w *
          hilbertH (unitDiscExterior.indicator fun u => μ u * basisF n u) w) =
      ∑' n, ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m *
        ∫ w, unitDiscExterior.indicator (fun u => μ u * basisF m u) w *
          hilbertH (unitDiscExterior.indicator fun u => ν u * basisF n u) w := by
  set D := unitDiscExterior with hDdef
  set B := B4 (grunsky (fsans κ) (gsans κ)) with hBdef
  set f : ℕ → ℂ → ℂ := fun n => D.indicator fun u => μ u * basisF n u with hfdef
  set g : ℕ → ℂ → ℂ := fun n => D.indicator fun u => ν u * basisF n u with hgdef
  have hfm : ∀ n, Measurable (f n) := fun n =>
    s4g_meas_ind wp_exterior_isOpen ((wp_harmonic_continuousOn hμ).mul (s4g_basisF_A21 n).1.continuousOn)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    s4g_meas_ind wp_exterior_isOpen ((wp_harmonic_continuousOn hν).mul (s4g_basisF_A21 n).1.continuousOn)
  have hfsum := s4g_fn_eLp_summable hμ
  have hgsum := s4g_fn_eLp_summable hν
  have hf2 : ∀ n, MemLp (f n) 2 := by
    intro n
    show eLpNorm (f n) 2 volume < ∞
    rw [s4g_eLpNorm_two (hfm n).aestronglyMeasurable, s4g_lint_ind wp_exterior_isOpen.measurableSet]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ w in D, ‖μ w * basisF k w‖ₑ ^ 2) n)
        (s4g_fn_L2sum hμ)).ne
  have hg2 : ∀ n, MemLp (g n) 2 := by
    intro n
    show eLpNorm (g n) 2 volume < ∞
    rw [s4g_eLpNorm_two (hgm n).aestronglyMeasurable, s4g_lint_ind wp_exterior_isOpen.measurableSet]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ w in D, ‖ν w * basisF k w‖ₑ ^ 2) n)
        (s4g_fn_L2sum hν)).ne
  have hsym : ∀ m n, B m n = B n m := by
    intro m n
    exact ((hook_unitary (AppB.b8_welding_normalized_pair hκ) (r22_complement_null hκ)).1 m n).2.1
  set Y : ℕ → ℕ → ℂ := fun n m => B n m * ∫ w, f m w * hilbertH (g n) w with hYdef
  have hX : ∀ n m, B n m * ∫ w, g m w * hilbertH (f n) w = Y m n := by
    intro n m
    rw [hYdef]
    simp only
    rw [← hilbertH_pairing_symm_L2 (hg2 m) (hf2 n), hsym n m]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hYs : Summable (Function.uncurry Y) := by
    have hHS := s4g_B4_HS hκ hκT
    have hprod : Summable fun p : ℕ × ℕ =>
        (eLpNorm (g p.1) 2 volume).toReal ^ 2 * (eLpNorm (f p.2) 2 volume).toReal ^ 2 :=
      hgsum.mul_of_nonneg hfsum (fun n => by positivity) (fun n => by positivity)
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (‖B p.1 p.2‖ ^ 2 +
        (eLpNorm (g p.1) 2 volume).toReal ^ 2 * (eLpNorm (f p.2) 2 volume).toReal ^ 2) / 2)
      ((hHS.add hprod).div_const 2) fun p => ?_
    simp only [Function.uncurry, hYdef, norm_mul]
    have hcs := cauchy_schwarz_L2 (hf2 p.2) (hilbertH_memLp_two (hg2 p.1)).1
    rw [(hilbertH_memLp_two (hg2 p.1)).2] at hcs
    have h2 := two_mul_le_add_sq ‖B p.1 p.2‖
      ((eLpNorm (g p.1) 2 volume).toReal * (eLpNorm (f p.2) 2 volume).toReal)
    have h3 : ‖B p.1 p.2‖ * ‖∫ w, f p.2 w * hilbertH (g p.1) w‖ ≤
        ‖B p.1 p.2‖ * ((eLpNorm (g p.1) 2 volume).toReal * (eLpNorm (f p.2) 2 volume).toReal) := by
      rw [mul_comm ((eLpNorm (g p.1) 2 volume).toReal)]
      exact mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
    nlinarith
  calc _ = ∑' n, ∑' m, Y m n := tsum_congr fun n => tsum_congr fun m => hX n m
    _ = ∑' n, ∑' m, Y n m := hYs.tsum_comm

/-- `1_{𝔻*} μ f_n ∈ L²`. -/
theorem s4g_fn_memLp {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (n : ℕ) :
    MemLp (unitDiscExterior.indicator fun w => μ w * basisF n w) 2 := by
  have hm : Measurable (unitDiscExterior.indicator fun w => μ w * basisF n w) := s4g_meas_ind wp_exterior_isOpen
    ((wp_harmonic_continuousOn hμ).mul (s4g_basisF_A21 n).1.continuousOn)
  show eLpNorm _ 2 volume < ∞
  rw [s4g_eLpNorm_two hm.aestronglyMeasurable, s4g_lint_ind wp_exterior_isOpen.measurableSet]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ w in unitDiscExterior, ‖μ w * basisF k w‖ₑ ^ 2) n)
      (s4g_fn_L2sum hμ)).ne

/-- **The `K₄²` part** (Fubini on `𝔻* × 𝔻*`, `K₄` symmetric and square integrable on `T₀(1)`). -/
theorem s4g_w3_A {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    IntegrableOn (fun z => (∫ w in unitDiscExterior, μ w * kerK4 (gsans κ) w z ^ 2) * ν z) unitDiscExterior ∧
      (∫ z in unitDiscExterior, (∫ w in unitDiscExterior, μ w * kerK4 (gsans κ) w z ^ 2) * ν z) =
        ∫ z in unitDiscExterior, (∫ w in unitDiscExterior, ν w * kerK4 (gsans κ) w z ^ 2) * μ z := by
  set D := unitDiscExterior with hDdef
  have hD : MeasurableSet D := wp_exterior_isOpen.measurableSet
  set K : ℂ → ℂ → ℂ := kerK4 (gsans κ) with hKdef
  set Mμ : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 D μ).toReal with hMμ
  set Mν : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 D ν).toReal with hMν
  have hprod : (volume.restrict D).prod (volume.restrict D) = volume.restrict (D ×ˢ D) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hK2 : Integrable (fun q : ℂ × ℂ => ‖K q.1 q.2‖ ^ 2) (volume.restrict (D ×ˢ D)) := by
    refine ⟨(s4g_K4_aesm hκ).norm.pow 2, ?_⟩
    show (∫⁻ q in D ×ˢ D, ‖‖K q.1 q.2‖ ^ 2‖ₑ) < ∞
    have h := s4g_w3_K4_L2 hκ hκT
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun q => ?_)) h
    rw [Real.enorm_eq_ofReal (by positivity), ← s4g_enorm_sq, enorm_eq_nnnorm]
  set F : ℂ × ℂ → ℂ := fun q => μ q.1 * ν q.2 * K q.1 q.2 ^ 2 with hFdef
  have hFi : Integrable F ((volume.restrict D).prod (volume.restrict D)) := by
    rw [hprod]
    have hm : AEStronglyMeasurable F (volume.restrict (D ×ˢ D)) := by
      have h1 : AEStronglyMeasurable (fun q : ℂ × ℂ => μ q.1) (volume.restrict (D ×ˢ D)) := by
        rw [← hprod]
        exact ((wp_harmonic_continuousOn hμ).aestronglyMeasurable hD).comp_fst
      have h2 : AEStronglyMeasurable (fun q : ℂ × ℂ => ν q.2) (volume.restrict (D ×ˢ D)) := by
        rw [← hprod]
        exact ((wp_harmonic_continuousOn hν).aestronglyMeasurable hD).comp_snd
      exact (h1.mul h2).mul ((s4g_K4_aesm hκ).pow 2)
    refine (hK2.const_mul (Mμ * Mν)).mono' hm ?_
    filter_upwards [ae_restrict_mem ((wp_exterior_isOpen.prod wp_exterior_isOpen).measurableSet)] with q hq
    rw [hFdef]
    simp only [norm_mul, norm_pow]
    have h1 := wp_harmonic_pointwise_bound hμ hq.1
    have h2 := wp_harmonic_pointwise_bound hν hq.2
    calc ‖μ q.1‖ * ‖ν q.2‖ * ‖K q.1 q.2‖ ^ 2 ≤ Mμ * Mν * ‖K q.1 q.2‖ ^ 2 := by gcongr
      _ = _ := rfl
  have hL : (∫ z in D, (∫ w in D, μ w * K w z ^ 2) * ν z) =
      ∫ q, F q ∂((volume.restrict D).prod (volume.restrict D)) := by
    rw [integral_prod_symm F hFi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFdef]
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
  have hR : (∫ z in D, (∫ w in D, ν w * K w z ^ 2) * μ z) =
      ∫ q, F q ∂((volume.restrict D).prod (volume.restrict D)) := by
    rw [integral_prod F hFi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFdef]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [hKdef, s4g_kerK4_symm (gsans κ) w z]
    ring
  refine ⟨?_, by rw [hL, hR]⟩
  refine (hFi.integral_prod_right).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [hFdef]
  rw [← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)

/-- **Stub W1.** For a bounded measurable coefficient `m` that is smooth on an open set `U ∋ y`, the third
derivative of the infinitesimal deformation `ahVar m` at `y` is the round-excision principal value
`-(6/π) PV ∫ m(u)/(u - y)⁴ d²u` (no vanishing of `m` near `y`; compare `qcv_ahVar_iter3`). -/
theorem s4g_ahVar_dz3_pv {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hm : IsBeltramiCoeff m univ k) {U : Set ℂ}
    (hU : IsOpen U) (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m U) {y : ℂ} (hy : y ∈ U) :
    Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ u in (ball y δ)ᶜ, m u / (u - y) ^ 4) (𝓝[>] 0)
      (𝓝 (dz (dz (dz (ahVar m))) y)) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y hy
  set r : ℝ := ε / 2 with hrdef
  have hr0 : 0 < r := by positivity
  -- a smooth cutoff `χ = 1` on `ball y (r/4)`, supported in `closedBall y (r/2)`
  set b : ContDiffBump y := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hb
  set χ : ℂ → ℂ := fun u => ((b u : ℝ) : ℂ) with hχdef
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hχ1 : ∀ u ∈ ball y (r / 4), χ u = 1 := by
    intro u hu
    have h1 : b u = 1 := b.one_of_mem_closedBall (by
      simp only [hb, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.1 hu))
    simp [hχdef, h1]
  have hχ0 : ∀ u : ℂ, r / 2 ≤ ‖u - y‖ → χ u = 0 := by
    intro u hu
    have h0 : b u = 0 := b.zero_of_le_dist (by simpa only [hb, dist_eq_norm] using hu)
    simp [hχdef, h0]
  have hχn : ∀ u, ‖χ u‖ ≤ 1 := by
    intro u
    simp only [hχdef, Complex.norm_real, Real.norm_of_nonneg b.nonneg]
    exact b.le_one
  have hmm : AEStronglyMeasurable m volume := by simpa using hm.1
  have hmb : ∀ᵐ u : ℂ, ‖m u‖ ≤ k := by simpa using hm.2
  -- the near part `n = χ m` and the far part `f = m - n`
  set n : ℂ → ℂ := fun u => χ u * m u with hndef
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) n := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x - y‖ < ε
    · have hxU : x ∈ U := hεU (mem_ball_iff_norm.2 hx)
      exact hχs.contDiffAt.mul (hsm.contDiffAt (hU.mem_nhds hxU))
    · have hopen : IsOpen {u : ℂ | r / 2 < ‖u - y‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      have hxo : x ∈ {u : ℂ | r / 2 < ‖u - y‖} := by
        show r / 2 < ‖x - y‖
        linarith [not_lt.1 hx]
      have hev : n =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hxo] with u hu
        simp only [hndef, hχ0 u (le_of_lt hu), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hnc : HasCompactSupport n := by
    refine HasCompactSupport.intro (isCompact_closedBall y (r / 2)) ?_
    intro u hu
    have h : r / 2 < ‖u - y‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hu
      exact hu
    simp only [hndef, hχ0 u h.le, zero_mul]
  set f : ℂ → ℂ := fun u => m u - n u with hfdef
  have hf0 : ∀ u ∈ ball y (r / 4), f u = 0 := by
    intro u hu
    simp only [hfdef, hndef, hχ1 u hu, one_mul, sub_self]
  have hnB : IsBeltramiCoeff n univ k := by
    refine ⟨by rw [Measure.restrict_univ]; exact hns.continuous.aestronglyMeasurable, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [hmb] with u hu
    calc ‖n u‖ = ‖χ u‖ * ‖m u‖ := norm_mul _ _
      _ ≤ 1 * k := mul_le_mul (hχn u) hu (norm_nonneg _) zero_le_one
      _ = k := one_mul k
  have hfB : IsBeltramiCoeff f univ (k + k) := by
    refine ⟨by rw [Measure.restrict_univ]; exact hmm.sub hns.continuous.aestronglyMeasurable, ?_⟩
    rw [Measure.restrict_univ]
    filter_upwards [hmb] with u hu
    calc ‖f u‖ ≤ ‖m u‖ + ‖n u‖ := norm_sub_le _ _
      _ ≤ k + k := by
          refine add_le_add hu ?_
          calc ‖n u‖ = ‖χ u‖ * ‖m u‖ := norm_mul _ _
            _ ≤ 1 * k := mul_le_mul (hχn u) hu (norm_nonneg _) zero_le_one
            _ = k := one_mul k
  have hkk : 0 ≤ k + k := by linarith
  -- `ahVar m = T n + G` with `G` holomorphic on `ball y (r/4)`
  have hlin : ∀ w, ahVar m w = ahVar n w + ahVar f w := by
    intro w
    have h := ah_var_linear hnB hfB 1 w
    have hmeq : (fun ζ => (1 : ℂ) * n ζ + f ζ) = m := by
      funext ζ
      simp only [hfdef, one_mul]
      ring
    rw [hmeq, one_mul] at h
    exact h
  have hnLp : MemLp n (ENNReal.ofReal 4) := hns.continuous.memLp_of_hasCompactSupport hnc
  have hnR : ∀ z : ℂ, ‖y‖ + r < ‖z‖ → n z = 0 := by
    intro z hz
    have h : r / 2 ≤ ‖z - y‖ := by
      have := norm_sub_norm_le z y
      linarith
    simp only [hndef, hχ0 z h, zero_mul]
  have hC := ahC_ahVar_eq (p := 4) (by norm_num) (by positivity : (0 : ℝ) < ‖y‖ + r) hnLp hnR
  set B : Set ℂ := ball y (r / 4) with hBdef
  have hHf : DifferentiableOn ℂ (ahVar f) B := QCV.qcv_ahVar_holomorphic hkk hfB isOpen_ball hf0
  set c₀ : ℂ := cauchyT n 0
  set c₁ : ℂ := cauchyT n 1 - cauchyT n 0
  set G : ℂ → ℂ := fun w => ahVar f w - c₀ - w * c₁ with hGdef
  have hG : DifferentiableOn ℂ G B := (hHf.sub_const _).sub (differentiableOn_id.mul_const _)
  have hsplit : ∀ w, ahVar m w = cauchyT n w + G w := by
    intro w
    rw [hlin, hC]
    simp only [hGdef]
    ring
  -- the Cauchy transforms
  have hone : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hd1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz n) := dz_contDiff hns
  have hd2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz (dz n)) := dz_contDiff hd1
  have hc1 : HasCompactSupport (dz n) := wr_dz_hasCompactSupport hnc
  have hc2 : HasCompactSupport (dz (dz n)) := wr_dz_hasCompactSupport hc1
  have hT0 : Differentiable ℝ (cauchyT n) :=
    (contDiff_cauchyT (hns.of_le hone) hnc).differentiable one_ne_zero
  have hT1 : Differentiable ℝ (cauchyT (dz n)) :=
    (contDiff_cauchyT (hd1.of_le hone) hc1).differentiable one_ne_zero
  have hT2 : Differentiable ℝ (cauchyT (dz (dz n))) :=
    (contDiff_cauchyT (hd2.of_le hone) hc2).differentiable one_ne_zero
  have hdT0 : ∀ x, dz (cauchyT n) x = cauchyT (dz n) x := dz_cauchyT (hns.of_le hone) hnc
  have hdT1 : ∀ x, dz (cauchyT (dz n)) x = cauchyT (dz (dz n)) x := dz_cauchyT (hd1.of_le hone) hc1
  have hdT2 : ∀ x, dz (cauchyT (dz (dz n))) x = cauchyT (dz (dz (dz n))) x :=
    dz_cauchyT (hd2.of_le hone) hc2
  -- three derivative levels on `B`
  have s1 := s4g_dz_step isOpen_ball hT0 hG (fun x _ => hsplit x)
  have hG1 : DifferentiableOn ℂ (deriv G) B := hG.deriv isOpen_ball
  have s2 := s4g_dz_step (F := dz (ahVar m)) isOpen_ball hT1 hG1 (fun x hx => by rw [s1 x hx, hdT0])
  have hG2 : DifferentiableOn ℂ (deriv (deriv G)) B := hG1.deriv isOpen_ball
  have s3 := s4g_dz_step (F := dz (dz (ahVar m))) isOpen_ball hT2 hG2 (fun x hx => by rw [s2 x hx, hdT1])
  have hy' : y ∈ B := mem_ball_self (by positivity)
  have hdz3 : dz (dz (dz (ahVar m))) y = cauchyT (dz (dz (dz n))) y + deriv (deriv (deriv G)) y := by
    rw [s3 y hy', hdT2]
  -- `G''' = (ahVar f)'''` on `B`
  have hGd : ∀ x ∈ B, deriv G x = deriv (ahVar f) x - c₁ := by
    intro x hx
    have hfx : DifferentiableAt ℂ (ahVar f) x := hHf.differentiableAt (isOpen_ball.mem_nhds hx)
    have h := ((hfx.hasDerivAt.sub_const c₀).sub ((hasDerivAt_id x).mul_const c₁)).deriv
    rw [one_mul] at h
    exact h
  have hGd2 : ∀ x ∈ B, deriv (deriv G) x = deriv (deriv (ahVar f)) x := by
    intro x hx
    have hev : deriv G =ᶠ[𝓝 x] fun w => deriv (ahVar f) w - c₁ := by
      filter_upwards [isOpen_ball.mem_nhds hx] with w hw
      exact hGd w hw
    rw [hev.deriv_eq, deriv_sub_const]
  have hGd3 : deriv (deriv (deriv G)) y = deriv (deriv (deriv (ahVar f))) y := by
    have hev : deriv (deriv G) =ᶠ[𝓝 y] deriv (deriv (ahVar f)) := by
      filter_upwards [isOpen_ball.mem_nhds hy'] with w hw
      exact hGd2 w hw
    rw [hev.deriv_eq]
  have hiter : iteratedDeriv 3 (ahVar f) y = deriv (deriv (deriv (ahVar f))) y := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hfar := QCV.qcv_ahVar_iter3 hkk hfB isOpen_ball hf0 hy'
  rw [hdz3, hGd3, ← hiter, hfar]
  -- the limits
  have hnear := s4g_cauchyT_dz3_pv hns hnc y
  have hfar' : Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ u in (ball y δ)ᶜ, f u / (u - y) ^ 4) (𝓝[>] 0)
      (𝓝 (-(6 / (π : ℂ)) * ∫ u, f u / (u - y) ^ 4)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 4 by positivity)] with δ hδ
    congr 1
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    have hu' : u ∈ ball y (r / 4) := by
      rw [mem_compl_iff, not_not] at hu
      exact ball_subset_ball hδ.2.le hu
    rw [hf0 u hu', zero_div]
  have hπ : ((-(6 / π) : ℂ)) = -(6 / (π : ℂ)) := rfl
  refine (hnear.add hfar').congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 4 by positivity)] with δ hδ
  rw [← mul_add, ← integral_add (s4g_int_compl hnB y hδ.1) (s4g_int_compl hfB y hδ.1)]
  congr 1
  refine setIntegral_congr_fun measurableSet_ball.compl fun u _ => ?_
  simp only [hfdef]
  ring

/-- **Stub W1b.** The flat term: for `ν ∈ A₂-harmonic` and `z ∈ 𝔻*`,
`∂³ ahVar (extB ν)(z) = -(6/π) PV ∫_{𝔻*} ν(w)/(w - z)⁴ d²w`. -/
theorem s4g_flat_pv {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ, ν w / (w - z) ^ 4) (𝓝[>] 0)
      (𝓝 (dz (dz (dz (ahVar (extB (toLinf ν))))) z)) := by
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  set m : ℂ → ℂ := unitDiscExterior.indicator ν with hmdef
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hmB : IsBeltramiCoeff m univ M := by
    refine ⟨?_, Filter.Eventually.of_forall fun u => ?_⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hE).2 ((wp_harmonic_continuousOn hν).aestronglyMeasurable hE)
    · by_cases hu : u ∈ unitDiscExterior
      · rw [hmdef, indicator_of_mem hu]
        exact wp_harmonic_pointwise_bound hν hu
      · rw [hmdef, indicator_of_notMem hu, norm_zero]
        exact hM0
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m unitDiscExterior :=
    (s4hv_harmonic_smooth hν).congr fun u hu => by rw [hmdef, indicator_of_mem hu]
  have hW1 := s4g_ahVar_dz3_pv hM0 hmB wp_exterior_isOpen hsm hz
  have hae : extB (toLinf ν) =ᵐ[volume] m := by
    have h := bc_toLinf_ae (d2_harmonicL2_memLp hν)
    rw [Filter.EventuallyEq, ae_restrict_iff' hE] at h
    filter_upwards [h] with u hu
    by_cases hum : u ∈ unitDiscExterior
    · rw [extB, hmdef, indicator_of_mem hum, indicator_of_mem hum]
      exact hu hum
    · rw [extB, hmdef, indicator_of_notMem hum, indicator_of_notMem hum]
  have hahV : ahVar (extB (toLinf ν)) = ahVar m := funext fun w => qcv_ahVar_congr_ae hae w
  rw [hahV]
  apply hW1.congr'
  filter_upwards [] with δ
  congr 1
  have hind : (fun u => m u / (u - z) ^ 4) = unitDiscExterior.indicator (fun u => ν u / (u - z) ^ 4) := by
    funext u
    by_cases hu : u ∈ unitDiscExterior
    · rw [hmdef, indicator_of_mem hu, indicator_of_mem hu]
    · rw [hmdef, indicator_of_notMem hu, indicator_of_notMem hu, zero_div]
  rw [hind, setIntegral_indicator hE, sdiff_eq, inter_comm]

/-- **Stub W2a.** Change of variables `y' ↦ w = J y'` in the plane chart: the transported coefficient is
`ν(J y') conj J'(y')/J'(y')` (`s4pv_dot_chart_ae`), and `J⁻¹ = M ∘ g` on `𝔻*` for a Möbius `M`, so the
pulled-back kernel is `g'(w)² g'(z)²/(g(w) - g(z))⁴` (Möbius invariance), `z = J y`. -/
theorem s4g_chart_cov {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior)
    {U : Set ℂ} {J : ℂ → ℂ} (hU : IsOpen U) (hJ : AnalyticOnNhd ℂ J U)
    (hmap : MapsTo J U unitDiscExterior) (hJzero : ∀ y ∈ U, deriv J y ≠ 0)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    {m : ℂ → ℂ}
    (hm : ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ) (qcv_planeSolution κ) =ᵐ[volume] m)
    {y : ℂ} (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ u in (ball y δ)ᶜ, m u / (u - y) ^ 4) = deriv J y ^ 2 *
      ∫ w in unitDiscExterior \ J '' ball y δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4) := by
  set V := qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf} with hVdef
  set A := ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ) (qcv_planeSolution κ) with hAdef
  have hVo : IsOpen V := s4pv_plane_exterior_isOpen hκ
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  obtain ⟨a, b, c, d, hdet, hMV, hinj⟩ := s4g_chart_facts hκ hJ hmap hchart
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo y hy
  have hyU : y ∈ U := hVU hy
  have hJy0 : deriv J y ≠ 0 := hJzero y hyU
  -- the pole image and the off-`V` vanishing
  set P := qcv_planeSolution κ '' {x : ℂ | wAS κ (x : ExtPlane) = extInf} with hPdef
  have hPnull : volume P = 0 :=
    (((s4g_pole_subsingleton κ).image _).countable.measure_zero volume)
  have hoff : ∀ᵐ u : ℂ, u ∉ V → A u = 0 := by
    have hP : ∀ᵐ u : ℂ, u ∉ P := by
      rw [ae_iff]
      simpa only [not_not, setOf_mem_eq] using hPnull
    filter_upwards [hP] with u hu huV
    exact s4g_ahT_off hκ _ huV hu
  have hon := s4g_ahT_ae hκ hν hJ hchart
  filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
  have hB : ball y δ ⊆ V := (ball_subset_ball hδ.2.le).trans hεV
  have hS : MeasurableSet (V \ ball y δ) := hVo.measurableSet.diff measurableSet_ball
  -- `|det J'| = |J'|²` and the change of variables
  have hder : ∀ v ∈ V \ ball y δ, HasFDerivWithinAt J
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv J v)).restrictScalars ℝ) (V \ ball y δ) v := by
    intro v hv
    exact ((hJ v (hVU hv.1)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  set G : ℂ → ℂ := fun w => deriv J y ^ 2 *
    (ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4)) with hGdef
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hS hder (hinj.mono sdiff_subset) G
  simp only [det_restrictScalars_toSpanSingleton] at hcv
  -- the pointwise kernel identity on `V ∖ ball y δ`
  have hpt : ∀ v ∈ V \ ball y δ, ν (J v) * conj (deriv J v) / deriv J v / (v - y) ^ 4 =
      |‖deriv J v‖ ^ 2| • G (J v) := by
    intro v hv
    have hvU : v ∈ U := hVU hv.1
    have hJv0 : deriv J v ≠ 0 := hJzero v hvU
    have hvy : v ≠ y := by
      intro h
      apply hv.2
      rw [h]
      exact mem_ball_self hδ.1
    obtain ⟨hcv0, hgv, hdv⟩ := hMV v hv.1
    obtain ⟨hcy0, hgy, hdy⟩ := hMV y hy
    have e1 : deriv (gsans κ) (J v) = (a * d - b * c) / (c * v + d) ^ 2 / deriv J v := eq_div_of_mul_eq hJv0 hdv
    have e2 : deriv (gsans κ) (J y) = (a * d - b * c) / (c * y + d) ^ 2 / deriv J y := eq_div_of_mul_eq hJy0 hdy
    have hK : deriv (gsans κ) (J v) ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ (J v) - gsans κ (J y)) ^ 4 =
        ((a * d - b * c) / (c * v + d) ^ 2 * ((a * d - b * c) / (c * y + d) ^ 2) /
          ((a * v + b) / (c * v + d) - (a * y + b) / (c * y + d)) ^ 2) ^ 2 /
        (deriv J v * deriv J y) ^ 2 := by
      rw [e1, e2, hgv, hgy]
      generalize (a * v + b) / (c * v + d) - (a * y + b) / (c * y + d) = D
      ring
    rw [s4g_mobius_kernel hdet hcv0 hcy0 hvy] at hK
    have hn : ((|‖deriv J v‖ ^ 2| : ℝ) : ℂ) = deriv J v * conj (deriv J v) := by
      rw [abs_of_nonneg (sq_nonneg _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hvy' : v - y ≠ 0 := sub_ne_zero.2 hvy
    rw [Complex.real_smul, hn, hGdef]
    simp only
    rw [hK]
    field_simp
  -- assemble
  have hstep1 : (∫ u in (ball y δ)ᶜ, m u / (u - y) ^ 4) = ∫ u in (ball y δ)ᶜ, A u / (u - y) ^ 4 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hm] with u hu
    rw [hu]
  have hstep2 : (∫ u in (ball y δ)ᶜ, A u / (u - y) ^ 4) = ∫ u in V \ ball y δ, A u / (u - y) ^ 4 := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_ball.compl.nullMeasurableSet
      (fun u (hu : u ∈ V \ ball y δ) => hu.2) ?_
    filter_upwards [hoff] with u hu hu'
    have huV : u ∉ V := fun h => hu'.2 ⟨h, hu'.1⟩
    rw [hu huV, zero_div]
  have hstep3 : (∫ u in V \ ball y δ, A u / (u - y) ^ 4) =
      ∫ u in V \ ball y δ, ν (J u) * conj (deriv J u) / deriv J u / (u - y) ^ 4 := by
    refine setIntegral_congr_ae hS ?_
    filter_upwards [hon] with u hu hu'
    rw [show A u = ν (J u) * conj (deriv J u) / deriv J u from hu hu'.1]
  have hstep4 : (∫ u in V \ ball y δ, ν (J u) * conj (deriv J u) / deriv J u / (u - y) ^ 4) =
      ∫ u in V \ ball y δ, |‖deriv J u‖ ^ 2| • G (J u) :=
    setIntegral_congr_fun hS hpt
  have hstep5 : (∫ w in J '' (V \ ball y δ), G w) = ∫ w in unitDiscExterior \ J '' ball y δ, G w :=
    setIntegral_congr_set (s4g_chart_image_ae hκ hmap hchart hinj hB)
  rw [hstep1, hstep2, hstep3, hstep4, ← hcv, hstep5, hGdef, integral_const_mul]

/-- **Stub W2b.** Replacing the excision `J(B(y, δ/|J'(y)|))` by the round disc `B(z, δ)`, `z = J y`: the
sliver term tends to `0`, and the rest is the difference-kernel integral. -/
theorem s4g_sliver_split {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior)
    {U : Set ℂ} {J : ℂ → ℂ} (hU : IsOpen U) (hJ : AnalyticOnNhd ℂ J U)
    (hmap : MapsTo J U unitDiscExterior) (hJzero : ∀ y ∈ U, deriv J y ≠ 0)
    (hchart : ∀ x ∈ unitDiscExterior, wAS κ (x : ExtPlane) ≠ extInf →
      qcv_planeSolution κ x ∈ U ∧ J (qcv_planeSolution κ x) = wA κ x)
    {y : ℂ} (hy : y ∈ qcv_planeSolution κ ''
      {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf}) :
    Tendsto (fun δ : ℝ =>
      (∫ w in unitDiscExterior \ J '' ball y (δ / ‖deriv J y‖),
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4)) -
      (∫ w in unitDiscExterior \ ball (J y) δ, ν w / (w - J y) ^ 4) -
      ∫ w in unitDiscExterior \ ball (J y) δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4 -
          1 / (w - J y) ^ 4)) (𝓝[>] 0) (𝓝 0) := by
  set V := qcv_planeSolution κ '' {x : ℂ | x ∈ unitDiscExterior ∧ wAS κ (x : ExtPlane) ≠ extInf} with hVdef
  have hVo : IsOpen V := s4pv_plane_exterior_isOpen hκ
  have hVU : V ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hchart x hx.1 hx.2).1
  obtain ⟨-, -, -, -, -, -, hinjV⟩ := s4g_chart_facts hκ hJ hmap hchart
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo y hy
  set ρ : ℝ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hb2 : ball y (2 * ρ) ⊆ V := by
    intro w hw
    apply hεV
    rw [mem_ball] at hw ⊢
    linarith
  have hJa : AnalyticOnNhd ℂ J (ball y (2 * ρ)) := fun w hw => hJ w (hVU (hb2 hw))
  have hinj : InjOn J (ball y (2 * ρ)) := hinjV.mono hb2
  have hyU : y ∈ U := hVU hy
  have hJ0 : deriv J y ≠ 0 := hJzero y hyU
  have hJs : HasStrictDerivAt J (deriv J y) y := (hJ y hyU).hasStrictDerivAt
  have hzD : J y ∈ unitDiscExterior := hmap hyU
  have hc0 : 0 < ‖deriv J y‖ := norm_pos_iff.2 hJ0
  have hD : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  -- the coefficient extended by zero
  set M : ℝ := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal with hM
  have hM0 : 0 ≤ M := by positivity
  set m : ℂ → ℂ := unitDiscExterior.indicator ν with hmdef
  have hmB : IsBeltramiCoeff m univ M := by
    refine ⟨?_, Filter.Eventually.of_forall fun u => ?_⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hD).2 ((wp_harmonic_continuousOn hν).aestronglyMeasurable hD)
    · by_cases hu : u ∈ unitDiscExterior
      · rw [hmdef, indicator_of_mem hu]
        exact wp_harmonic_pointwise_bound hν hu
      · rw [hmdef, indicator_of_notMem hu, norm_zero]
        exact hM0
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m unitDiscExterior :=
    (s4hv_harmonic_smooth hν).congr fun u hu => by rw [hmdef, indicator_of_mem hu]
  have hind : (fun u => m u / (u - J y) ^ 4) =
      unitDiscExterior.indicator (fun u => ν u / (u - J y) ^ 4) := by
    funext u
    by_cases hu : u ∈ unitDiscExterior
    · rw [hmdef, indicator_of_mem hu, indicator_of_mem hu]
    · rw [hmdef, indicator_of_notMem hu, indicator_of_notMem hu, zero_div]
  -- the difference kernel extended by zero
  set F : ℂ → ℂ := unitDiscExterior.indicator (fun w => ν w * (deriv (gsans κ) w ^ 2 *
    deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4 - 1 / (w - J y) ^ 4)) with hF
  obtain ⟨hKint, -⟩ := s4hv_actual_kernel_pv hκ hν hzD
  have hFint : ∀ r : ℝ, 0 < r → IntegrableOn F (ball (J y) r)ᶜ := by
    intro r hr
    rw [hF, integrableOn_indicator_iff hD]
    exact hKint r hr
  have hI : ∀ (S : Set ℂ) (f : ℂ → ℂ), (∫ w in unitDiscExterior \ S, f w) =
      ∫ w in Sᶜ, unitDiscExterior.indicator f w := by
    intro S f
    rw [setIntegral_indicator hD, sdiff_eq, inter_comm]
  -- the sliver bound `|F(w)| ≤ C/|w - z|²`
  have hK4c : ContinuousAt (fun w => kerK4 (gsans κ) w (J y)) (J y) :=
    ((s4hv_K4_analytic hκ hzD) (J y) hzD).continuousAt
  obtain ⟨r0, hr0, hr0b⟩ := Metric.continuousAt_iff.1 hK4c 1 one_pos
  set A : ℝ := ‖kerK4 (gsans κ) (J y) (J y)‖ + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hpi : 0 < π := Real.pi_pos
  have hFb : ∀ w, 0 < ‖w - J y‖ → ‖w - J y‖ < r0 →
      ‖F w‖ ≤ M * (π ^ 2 * A ^ 2 * r0 ^ 2 + 2 * π * A) / ‖w - J y‖ ^ 2 := by
    intro w hw0 hwr
    by_cases hwD : w ∈ unitDiscExterior
    · rw [hF, indicator_of_mem hwD]
      have hwz : w ≠ J y := fun h => by rw [h, sub_self, norm_zero] at hw0; exact lt_irrefl _ hw0
      have hk := s4hv_kernel_factorization (gsans κ) hwz
      change ‖ν w * s4hv_kernel (gsans κ) w (J y)‖ ≤ _
      rw [hk]
      have hKA : ‖kerK4 (gsans κ) w (J y)‖ ≤ A := by
        have h1 := hr0b (show dist w (J y) < r0 by rwa [dist_eq_norm])
        rw [dist_eq_norm] at h1
        have h2 := norm_sub_norm_le (kerK4 (gsans κ) w (J y)) (kerK4 (gsans κ) (J y) (J y))
        rw [hA]
        linarith
      have ht2 : 0 < ‖w - J y‖ ^ 2 := by positivity
      have h1 : ‖(π : ℂ) ^ 2 * kerK4 (gsans κ) w (J y) ^ 2‖ ≤ π ^ 2 * A ^ 2 := by
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpi.le]
        gcongr
      have h2 : ‖2 * (π : ℂ) * kerK4 (gsans κ) w (J y) / (w - J y) ^ 2‖ ≤ 2 * π * A / ‖w - J y‖ ^ 2 := by
        rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpi.le,
          Complex.norm_two]
        gcongr
      have h3 := (norm_sub_le _ _).trans (add_le_add h1 h2)
      rw [norm_mul]
      calc ‖ν w‖ * ‖(π : ℂ) ^ 2 * kerK4 (gsans κ) w (J y) ^ 2 -
            2 * π * kerK4 (gsans κ) w (J y) / (w - J y) ^ 2‖
          ≤ M * (π ^ 2 * A ^ 2 + 2 * π * A / ‖w - J y‖ ^ 2) :=
            mul_le_mul (wp_harmonic_pointwise_bound hν hwD) h3 (norm_nonneg _) hM0
        _ = M * (π ^ 2 * A ^ 2 * ‖w - J y‖ ^ 2 + 2 * π * A) / ‖w - J y‖ ^ 2 := by
            field_simp
        _ ≤ M * (π ^ 2 * A ^ 2 * r0 ^ 2 + 2 * π * A) / ‖w - J y‖ ^ 2 := by
            gcongr
    · rw [hF, indicator_of_notMem hwD, norm_zero]
      positivity
  have hsl := s4g_sliver_small hJs hJ0 (F := F) (by positivity) hr0 hFb
  have hcd := s4g_conf_diff hρ hJa hinj hJ0 wp_exterior_isOpen hzD hsm
    (fun r hr => s4g_int_compl hmB (J y) hr)
  have hlim := hsl.add hcd
  rw [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [s4g_conformal_disc hJs hJ0 (η := 1 / 4) (by norm_num) (by norm_num),
    Ioo_mem_nhdsGT (show (0 : ℝ) < ρ * ‖deriv J y‖ by positivity)] with δ hE hδ
  obtain ⟨-, hE2⟩ := hE
  have hδ0 : 0 < δ := hδ.1
  have hr : δ / ‖deriv J y‖ < ρ := by rw [div_lt_iff₀ hc0]; exact hδ.2
  have hEm : MeasurableSet (J '' ball y (δ / ‖deriv J y‖)) :=
    measurableSet_ball.image_of_continuousOn_injOn
      (hJa.continuousOn.mono (ball_subset_ball (by linarith)))
      (hinj.mono (ball_subset_ball (by linarith)))
  have hEc : (J '' ball y (δ / ‖deriv J y‖))ᶜ ⊆ (ball (J y) (δ / 2))ᶜ := by
    intro w hw hwb
    have hd : dist w (J y) < δ / 2 := hwb
    exact hw (hE2 (show dist w (J y) < δ * (1 - 1 / 4) by linarith))
  have hsw := s4g_swap (F := F) hEm measurableSet_ball ((hFint (δ / 2) (by positivity)).mono_set (by
    intro w hw hwb
    have hd : dist w (J y) < δ / 2 := hwb
    exact hw ⟨hE2 (show dist w (J y) < δ * (1 - 1 / 4) by linarith), show dist w (J y) < δ by linarith⟩))
  -- splitting the conformal integral
  have hsubE : unitDiscExterior \ J '' ball y (δ / ‖deriv J y‖) ⊆ unitDiscExterior \ ball (J y) (δ / 2) :=
    fun w hw => ⟨hw.1, fun h => hEc hw.2 h⟩
  have hiK := (hKint (δ / 2) (by positivity)).mono_set hsubE
  have hiN : IntegrableOn (fun u => ν u / (u - J y) ^ 4)
      (unitDiscExterior \ J '' ball y (δ / ‖deriv J y‖)) :=
    ((s4g_int_compl hmB (J y) (show 0 < δ / 2 by positivity)).mono_set
      (fun w hw => hEc hw.2)).congr_fun (fun u hu => by simp only [hmdef, indicator_of_mem hu.1])
      (hD.diff hEm)
  have iE : (∫ w in unitDiscExterior \ J '' ball y (δ / ‖deriv J y‖),
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4)) =
      (∫ w in (J '' ball y (δ / ‖deriv J y‖))ᶜ, F w) +
        ∫ w in (J '' ball y (δ / ‖deriv J y‖))ᶜ, m w / (w - J y) ^ 4 := by
    have e : (fun w => ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 /
        (gsans κ w - gsans κ (J y)) ^ 4)) = fun w => ν w * (deriv (gsans κ) w ^ 2 *
          deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4 - 1 / (w - J y) ^ 4) +
          ν w / (w - J y) ^ 4 := by
      funext w
      ring
    rw [e, integral_add (f := fun w => ν w * (deriv (gsans κ) w ^ 2 *
          deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4 - 1 / (w - J y) ^ 4)) hiK hiN,
      hI, hI, hind]
  have iB1 : (∫ w in unitDiscExterior \ ball (J y) δ, ν w / (w - J y) ^ 4) =
      ∫ w in (ball (J y) δ)ᶜ, m w / (w - J y) ^ 4 := by
    rw [hI, hind]
  have iB2 : (∫ w in unitDiscExterior \ ball (J y) δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4 -
          1 / (w - J y) ^ 4)) = ∫ w in (ball (J y) δ)ᶜ, F w := by
    rw [hI]
  linear_combination -iE + iB1 + iB2 - hsw

/-- **Stub W3.** Symmetry of the pairing: if `L_μ` and `L_ν` are the principal values of the difference kernel
against `μ` and `ν` at every point of `𝔻*`, then `∬ L_μ ν = ∬ L_ν μ` (Fubini for the absolutely integrable
`π² K₄²` part; `B₄ = B₄ᵀ` and the symmetric Beurling pairing for the `K₄/(w - z)²` part). -/
theorem s4g_pv_pairing_symm {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {μ ν : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) {Lμ Lν : ℂ → ℂ}
    (hLμ : ∀ z ∈ unitDiscExterior, Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        μ w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) z ^ 2 / (gsans κ w - gsans κ z) ^ 4 - 1 / (w - z) ^ 4))
      (𝓝[>] 0) (𝓝 (Lμ z)))
    (hLν : ∀ z ∈ unitDiscExterior, Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) z ^ 2 / (gsans κ w - gsans κ z) ^ 4 - 1 / (w - z) ^ 4))
      (𝓝[>] 0) (𝓝 (Lν z))) :
    (∫ z in unitDiscExterior, Lμ z * ν z) = ∫ z in unitDiscExterior, Lν z * μ z := by
  set D := unitDiscExterior with hDdef
  have hD : MeasurableSet D := wp_exterior_isOpen.measurableSet
  -- `L = -(6/π) (π² ∫ ρ K₄² - 2π v)` with `v` the principal value of `∫ ρ K₄/(w - z)²` (H10)
  have hrep : ∀ {ρ : ℂ → ℂ}, ρ ∈ harmonicL2 D → ∀ {L : ℂ → ℂ}, (∀ z ∈ D, Tendsto (fun δ : ℝ =>
      -(6 / (π : ℂ)) * ∫ w in D \ ball z δ, ρ w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) z ^ 2 /
        (gsans κ w - gsans κ z) ^ 4 - 1 / (w - z) ^ 4)) (𝓝[>] 0) (𝓝 (L z))) →
      ∃ v : ℂ → ℂ, (∀ z ∈ D, Tendsto (fun δ : ℝ => ∫ w in D \ ball z δ,
          ρ w * kerK4 (gsans κ) w z / (w - z) ^ 2) (𝓝[>] 0) (𝓝 (v z))) ∧
        ∀ z ∈ D, L z = -(6 / (π : ℂ)) * ((π : ℂ) ^ 2 * (∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) -
          2 * π * v z) := by
    intro ρ hρ L hL
    have hex : ∀ z, ∃ v : ℂ, z ∈ D →
        Tendsto (fun δ : ℝ => ∫ w in D \ ball z δ, ρ w * kerK4 (gsans κ) w z / (w - z) ^ 2) (𝓝[>] 0) (𝓝 v) ∧
        Tendsto (fun δ : ℝ => ∫ w in D \ ball z δ, ρ w * s4hv_kernel (gsans κ) w z) (𝓝[>] 0)
          (𝓝 ((π : ℂ) ^ 2 * (∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) - 2 * π * v)) := by
      intro z
      by_cases hz : z ∈ D
      · obtain ⟨-, v, hv, hT⟩ := s4hv_actual_kernel_pv hκ hρ hz
        exact ⟨v, fun _ => ⟨hv, hT⟩⟩
      · exact ⟨0, fun h => absurd h hz⟩
    choose v hv using hex
    refine ⟨v, fun z hz => (hv z hz).1, fun z hz => ?_⟩
    exact tendsto_nhds_unique (hL z hz) (((hv z hz).2).const_mul (-(6 / (π : ℂ))))
  obtain ⟨vμ, hvμ, hLμe⟩ := hrep hμ hLμ
  obtain ⟨vν, hvν, hLνe⟩ := hrep hν hLν
  obtain ⟨hAμi, hAeq⟩ := s4g_w3_A hκ hκT hμ hν
  obtain ⟨hAνi, -⟩ := s4g_w3_A hκ hκT hν hμ
  obtain ⟨hvμi, hvμs⟩ := s4g_w3_vpair hκ hκT hμ hν hvμ
  obtain ⟨hvνi, hvνs⟩ := s4g_w3_vpair hκ hκT hν hμ hvν
  -- the principal-value pairings as double series
  have hSμ : (∫ z in D, vμ z * ν z) = -(π : ℂ) * ∑' n, ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m *
      ∫ w, D.indicator (fun u => ν u * basisF m u) w * hilbertH (D.indicator fun u => μ u * basisF n u) w := by
    rw [← hvμs.tsum_eq, tsum_mul_left]
    congr 1
    refine tsum_congr fun n => ?_
    exact (s4g_w3_row hκ hν (hilbertH_memLp_two (s4g_fn_memLp hμ n)).1
      (s4g_hilbertH_aesm (s4g_fn_memLp hμ n)) n).tsum_eq.symm
  have hSν : (∫ z in D, vν z * μ z) = -(π : ℂ) * ∑' n, ∑' m, B4 (grunsky (fsans κ) (gsans κ)) n m *
      ∫ w, D.indicator (fun u => μ u * basisF m u) w * hilbertH (D.indicator fun u => ν u * basisF n u) w := by
    rw [← hvνs.tsum_eq, tsum_mul_left]
    congr 1
    refine tsum_congr fun n => ?_
    exact (s4g_w3_row hκ hμ (hilbertH_memLp_two (s4g_fn_memLp hν n)).1
      (s4g_hilbertH_aesm (s4g_fn_memLp hν n)) n).tsum_eq.symm
  have hsplit : ∀ {ρ σ : ℂ → ℂ} {L v : ℂ → ℂ},
      IntegrableOn (fun z => (∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) * σ z) D →
      IntegrableOn (fun z => v z * σ z) D →
      (∀ z ∈ D, L z = -(6 / (π : ℂ)) * ((π : ℂ) ^ 2 * (∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) -
        2 * π * v z)) →
      (∫ z in D, L z * σ z) = -(6 / (π : ℂ)) * ((π : ℂ) ^ 2 *
        (∫ z in D, (∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) * σ z) - 2 * π * ∫ z in D, v z * σ z) := by
    intro ρ σ L v hA hv hLe
    have e : (∫ z in D, L z * σ z) = ∫ z in D, -(6 / (π : ℂ)) * ((π : ℂ) ^ 2 *
        ((∫ w in D, ρ w * kerK4 (gsans κ) w z ^ 2) * σ z) - 2 * π * (v z * σ z)) :=
      setIntegral_congr_fun hD (fun z hz => by rw [hLe z hz]; ring)
    rw [e, integral_const_mul, integral_sub (hA.const_mul _) (hv.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [hsplit hAμi hvμi hLμe, hsplit hAνi hvνi hLνe, hAeq, hSμ, hSν, s4g_w3_dsym hκ hκT hμ hν]

/-- Clause 1 at the points covered by the plane chart (from W1, W1b, W2a, W2b and `s4hv_lieTheta_chart`). -/
theorem s4g_clause1_chart {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior)
    (hz₀ : wAS κ extInf ≠ (z : ExtPlane)) :
    Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) z ^ 2 / (gsans κ w - gsans κ z) ^ 4 - 1 / (w - z) ^ 4))
      (𝓝[>] 0) (𝓝 (lieTheta κ ν z)) := by
  obtain ⟨U, J, hU, hJ, hmap, hJzero, hchart⟩ := s4pv_actual_chart hκ
  obtain ⟨y, hy, hJy⟩ := s4pv_chart_surjective hκ (fun x hx hp => (hchart x hx hp).2) hz hz₀
  subst hJy
  have hyU : y ∈ U := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hchart x hx.1 hx.2).1
  have hJ0 : deriv J y ≠ 0 := hJzero y hyU
  have hc : 0 < ‖deriv J y‖ := norm_pos_iff.mpr hJ0
  have hνh : toLinf ν ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec ν hν).1
  -- the chart term
  obtain ⟨m, hm, hmB, hsm⟩ := s4pv_dot_smooth_rep hκ hνh
  have hk : 0 ≤ ‖qcv_rightDerivative κ (toLinf ν)‖ / (1 - ‖κ‖ ^ 2) := by
    have h1 : ‖κ‖ < 1 := mem_ball_zero_iff.mp hκ
    have h2 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    positivity
  have hW1 := s4g_ahVar_dz3_pv hk hmB (s4pv_plane_exterior_isOpen hκ) hsm hy
  have hahV : ahVar m = ahVar (ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ)
      (qcv_planeSolution κ)) := funext fun w => qcv_ahVar_congr_ae hm.symm w
  rw [hahV] at hW1
  have hsc : Tendsto (fun δ : ℝ => δ / ‖deriv J y‖) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := ((continuous_id.div_const ‖deriv J y‖).tendsto (0 : ℝ))
      simp only [id, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ hc
  have hcov := hsc.eventually (s4g_chart_cov hκ hν hU hJ hmap hJzero hchart hm hy)
  set I₁ : ℝ → ℂ := fun δ => ∫ w in unitDiscExterior \ J '' ball y (δ / ‖deriv J y‖),
    ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) (J y) ^ 2 / (gsans κ w - gsans κ (J y)) ^ 4) with hI₁
  have hA : Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * I₁ δ) (𝓝[>] 0)
      (𝓝 (dz (dz (dz (ahVar (ahT_dot (extB (qcv_rightDerivative κ (toLinf ν))) (extB κ)
        (qcv_planeSolution κ))))) y / deriv J y ^ 2)) := by
    have h := (hW1.comp hsc).div_const (deriv J y ^ 2)
    apply h.congr'
    filter_upwards [hcov] with δ hδ
    simp only [Function.comp_apply]
    rw [hδ, mul_left_comm, mul_div_cancel_left₀ _ (pow_ne_zero 2 hJ0)]
  -- the flat term and the sliver
  have hB := s4g_flat_pv hν hz
  have hS := s4g_sliver_split hκ hν hU hJ hmap hJzero hchart hy
  have hT := (hA.sub hB).sub (hS.const_mul (-(6 / (π : ℂ))))
  rw [mul_zero, sub_zero, ← s4hv_lieTheta_chart hκ hν hJ hmap hJzero hchart hy] at hT
  apply hT.congr'
  filter_upwards [] with δ
  simp only [hI₁]
  ring

/-- **Stub W0.** Clause 1 at the point `z = w_κ(∞)` of `𝔻*`, which the plane chart misses. -/
theorem s4g_exceptional_point {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior)
    (hz₀ : wAS κ extInf = (z : ExtPlane)) :
    Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv (gsans κ) w ^ 2 * deriv (gsans κ) z ^ 2 / (gsans κ w - gsans κ z) ^ 4 - 1 / (w - z) ^ 4))
      (𝓝[>] 0) (𝓝 (lieTheta κ ν z)) := by
  -- change the representative: `κ' = κ * τ` with `τ ∼ 0` and `w_τ(∞) ≠ ∞`
  obtain ⟨τ, hτ, hτ1, hτinf⟩ := s4g_tau_exists
  have hm := wA_mul hτ hκ
  have hκ' : beltramiMul κ τ ∈ LinfStarBall := hm.1
  have hz₀' : wAS (beltramiMul κ τ) extInf ≠ (z : ExtPlane) := by
    rw [hm.2.1, Function.comp_apply, ← hz₀]
    intro h
    exact hτinf ((wAS_bijective κ).1 h)
  have hcl := s4g_clause1_chart hκ' hν hz hz₀'
  have hg : EqOn (gsans (beltramiMul κ τ)) (gsans κ) unitDiscExterior := by
    refine (FB.fb_pair_class hκ' hκ (fun w hw => ?_)).2
    show finPart (wAS (beltramiMul κ τ) (w : ExtPlane)) = finPart (wAS κ (w : ExtPlane))
    rw [hm.2.1, Function.comp_apply, hτ1 w hw]
  have hd : ∀ v ∈ unitDiscExterior, deriv (gsans (beltramiMul κ τ)) v = deriv (gsans κ) v :=
    fun v hv => (Filter.eventuallyEq_of_mem (wp_exterior_isOpen.mem_nhds hv) hg).deriv_eq
  rw [← s4g_lieTheta_class hκ hτ hτ1 hν hz]
  apply hcl.congr'
  filter_upwards [] with δ
  congr 1
  refine setIntegral_congr_fun (wp_exterior_isOpen.measurableSet.diff measurableSet_ball) (fun w hw => ?_)
  simp only [hg hw.1, hg hz, hd w hw.1, hd z hz]

/-- **Remark 4.4** (TT:5372–5394). `∂ϑ = 0` on `T₀(1)`. Directly, at `[κ] ∈ T₀(1)` with `g = 𝗀_κ`:
- `(L_ν ϑ)(z) = -(6/π) ∬_{𝔻*} ν(w) (g'(w)²g'(z)²/(g(w) - g(z))⁴ - 1/(w - z)⁴) d²w` (principal value), `z ∈ 𝔻*`;
  **[CORRECTION 2026-10-28, Program G]** the memoir prints `-(12/π)` (TT:5387); the derivative of the
  Schwarzian is `∂³ẇ = -(6/π) PV ∫ ν(w)/(w - z)⁴` (`qcv_ahVar_iter3`); the factor 12 is copied from Theorem 4.1,
  where `∂S₁ = 2ϑ` supplies the 2 (ERRATA G-1);
- `∂ϑ(μ, ν) = L_μ ϑ(ν) - L_ν ϑ(μ) = 0`. -/
theorem s4g_remark_4_4 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    let κ : LinfStar := (Quotient.out p : LinfStarBall)
    let g := gsans κ
    (∀ z ∈ unitDiscExterior, Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv g w ^ 2 * deriv g z ^ 2 / (g w - g z) ^ 4 - 1 / (w - z) ^ 4)) (𝓝[>] 0) (𝓝 (lieTheta κ ν z))) ∧
      (∫ z in unitDiscExterior, lieTheta κ μ z * ν z) = ∫ z in unitDiscExterior, lieTheta κ ν z * μ z := by
  intro κ g
  -- `T₀(1)` is used only in clause 2 (B4 is Hilbert–Schmidt).
  have hκ : κ ∈ LinfStarBall := (Quotient.out p).2
  have hp' : Phi ⟨κ, hκ⟩ ∈ T01 := by
    rw [show Phi (Quotient.out p : LinfStarBall) = p from Quotient.out_eq (s := teichSetoid) p]
    exact hp
  have hcl : ∀ {ν : ℂ → ℂ}, ν ∈ harmonicL2 unitDiscExterior → ∀ z ∈ unitDiscExterior,
      Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv g w ^ 2 * deriv g z ^ 2 / (g w - g z) ^ 4 - 1 / (w - z) ^ 4))
      (𝓝[>] 0) (𝓝 (lieTheta κ ν z)) := by
    intro ν hν z hz
    by_cases hz₀ : wAS κ extInf = (z : ExtPlane)
    · exact s4g_exceptional_point hκ hν hz hz₀
    · exact s4g_clause1_chart hκ hν hz hz₀
  exact ⟨hcl hν, s4g_pv_pairing_symm hκ hp' hμ hν (hcl hμ) (hcl hν)⟩

/-- **Remark 4.4** (TT:5372–5394). `∂ϑ = 0` on `T₀(1)`. Directly, at `[κ] ∈ T₀(1)` with `g = 𝗀_κ`:
- `(L_ν ϑ)(z) = -(6/π) ∬_{𝔻*} ν(w) (g'(w)²g'(z)²/(g(w) - g(z))⁴ - 1/(w - z)⁴) d²w` (principal value), `z ∈ 𝔻*`;
  **[CORRECTION 2026-10-28, Program G]** the memoir prints `-(12/π)` (TT:5387); the derivative of the
  Schwarzian is `∂³ẇ = -(6/π) PV ∫ ν(w)/(w - z)⁴` (`qcv_ahVar_iter3`); the factor 12 is copied from Theorem 4.1,
  where `∂S₁ = 2ϑ` supplies the 2 (ERRATA G-1);
- `∂ϑ(μ, ν) = L_μ ϑ(ν) - L_ν ϑ(μ) = 0`. -/
theorem remark_4_4 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    let κ : LinfStar := (Quotient.out p : LinfStarBall)
    let g := gsans κ
    (∀ z ∈ unitDiscExterior, Tendsto (fun δ : ℝ => -(6 / (π : ℂ)) * ∫ w in unitDiscExterior \ ball z δ,
        ν w * (deriv g w ^ 2 * deriv g z ^ 2 / (g w - g z) ^ 4 - 1 / (w - z) ^ 4)) (𝓝[>] 0) (𝓝 (lieTheta κ ν z))) ∧
      (∫ z in unitDiscExterior, lieTheta κ μ z * ν z) = ∫ z in unitDiscExterior, lieTheta κ ν z * μ z := by
  exact s4g_remark_4_4 hp hμ hν

end Ch2
end TakhtajanTeo
