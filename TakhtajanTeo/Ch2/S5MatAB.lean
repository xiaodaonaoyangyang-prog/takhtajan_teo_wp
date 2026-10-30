import TakhtajanTeo.Ch2.S5NagSullivan

/-!
# The Fourier matrices of `Π̂(γ)` (Program G, 下属6)

Host of `matAB_spec` (TT:5494–5520).

* M0 `s5mab_inv_qs`: `γ⁻¹` (on `S¹`) is again a quasisymmetric circle homeomorphism.
* M1 `s5mab_inv_coeff`: the Fourier coefficients of the powers of `γ⁻¹` through those of `γ`.
* M2 `s5mab_compat`: the completed operator agrees with literal composition on continuous `HC` data.
* M3 `s5mab_basis`: the matrices are the basis coefficients of `Π̂(γ)` (clauses 3, 4).
* M4 `s5mab_inv_mat`: `𝔄(γ⁻¹) = 𝔄(γ)*`, `𝔅(γ⁻¹) = -𝔅(γ)ᵗ` (clause 5).
* M5 `s5mab_rows`: `𝔄𝔄* - 𝔅𝔅* = I`, `𝔄𝔅ᵗ = 𝔅𝔄ᵗ` (clauses 1, 2), from `Π̂(γ)Π̂(γ⁻¹) = 1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- M0. The inverse of a quasisymmetric circle homeomorphism on `S¹`. Only values on `S¹` enter `IsQSCircleHomeo`.
The lift of `γ⁻¹` is the inverse lift; quasisymmetry comes from the inverse of the plane quasiconformal extension. -/
theorem s5mab_inv_qs {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) : IsQSCircleHomeo (Function.invFunOn γ unitCircle) := by
  obtain ⟨-, -, -, hGγ, -⟩ := s5ns_inv_data hγ
  obtain ⟨f, hc, hm, hp, hu⟩ := s5ns_qs_lift hγ
  have hs := s5ns_lift_surj hc hp
  set e := StrictMono.orderIsoOfSurjective f hm hs
  have hfe (s : ℝ) : f (e.symm s) = s := StrictMono.orderIsoOfSurjective_self_symm_apply f hm hs s
  have hper (s : ℝ) : e.symm (s + 2 * π) = e.symm s + 2 * π := by
    apply hm.injective
    rw [hfe, hp, hfe]
  have hGe (θ : ℝ) : Function.invFunOn γ unitCircle (exp (θ * I)) = exp (e.symm θ * I) := by
    have h1 : γ (exp (e.symm θ * I)) = exp (θ * I) := by rw [hu, hfe]
    rw [← h1]
    exact hGγ _ (s5ns_exp_mem _)
  refine ⟨⟨e.symm, e.symm.continuous, e.symm.strictMono, hper, hGe⟩, ?_⟩
  obtain ⟨H, ⟨K, hK⟩, hHs, hHsph, hHe⟩ := circle_quasisymmetric_plane_extension hγ
  have hinv := thm7_2_inv hK
  rw [hHs] at hinv
  have hinjH : InjOn H univ := hK.2.2.1.2.1
  have hsurj : Function.invFunOn H univ '' univ = univ :=
    eq_univ_of_forall fun z => ⟨H z, mem_univ _, hinjH.leftInvOn_invFunOn (mem_univ z)⟩
  apply circleQS_congr (planeQC_circle_quasisymmetric hinv hsurj)
  intro w hw
  rw [← hHsph] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have hz' : z ∈ unitCircle := by simpa [unitCircle] using hz
  rw [hHe hz', hGγ z hz', ← hHe hz', hinjH.leftInvOn_invFunOn (mem_univ z)]

/-- M1. `Q c_Q((γ⁻¹)^P) = P c_{-P}(γ^{-Q})`: substitute `s = u(t)` and integrate by parts against `μ_u`. -/
theorem s5mab_inv_coeff {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (P Q : ℤ) (hQ : Q ≠ 0) :
    (Q : ℂ) * circleCoeff (fun z => Function.invFunOn γ unitCircle z ^ P) Q =
      P * circleCoeff (fun z => γ z ^ (-Q)) (-P) := by
  have hπ : 0 < 2 * π := by positivity
  obtain ⟨f, hc, hm, hp', hu⟩ := s5ns_qs_lift hγ
  have hs := s5ns_lift_surj hc hp'
  set e := StrictMono.orderIsoOfSurjective f hm hs
  have hfe (s : ℝ) : f (e.symm s) = s := StrictMono.orderIsoOfSurjective_self_symm_apply f hm hs s
  have hef (t : ℝ) : e.symm (f t) = t := StrictMono.orderIsoOfSurjective_symm_apply_self f hm hs t
  have hper (s : ℝ) : e.symm (s + 2 * π) = e.symm s + 2 * π := by
    apply hm.injective
    rw [hfe, hp', hfe]
  obtain ⟨-, -, -, hGγ, -⟩ := s5ns_inv_data hγ
  have hGe (θ : ℝ) : Function.invFunOn γ unitCircle (exp (θ * I)) = exp (e.symm θ * I) := by
    have h1 : γ (exp (e.symm θ * I)) = exp (θ * I) := by rw [hu, hfe]
    rw [← h1]
    exact hGγ _ (s5ns_exp_mem _)
  set c : ℂ := -((Q : ℂ) * I) with hcdef
  -- the integration by parts with `Ψ(s) = e^{cs}`
  have hΨ (s : ℝ) : HasDerivAt (fun s : ℝ => exp (c * (s : ℂ))) (c * exp (c * (s : ℂ))) s := by
    have h := ((hasDerivAt_id s).ofReal_comp.const_mul c).cexp
    convert h using 1
    · rfl
    · show c * exp (c * (s : ℂ)) = exp (c * (s : ℂ)) * (c * ((1 : ℝ) : ℂ))
      rw [Complex.ofReal_one, mul_one, mul_comm]
  have hΨ'c : Continuous (fun s : ℝ => c * exp (c * (s : ℂ))) := by fun_prop
  have hΨper (s : ℝ) : exp (c * (((s + 2 * π : ℝ)) : ℂ)) = exp (c * (s : ℂ)) := by
    rw [show c * (((s + 2 * π : ℝ)) : ℂ) = c * (s : ℂ) + ((-Q : ℤ) : ℂ) * (2 * π * I) by
      rw [hcdef]; push_cast; ring]
    exact (Complex.exp_periodic.int_mul (-Q)) _
  have hibp := s5ns_lift_ibp f hc hm hp' hΨ hΨ'c hΨper (-P)
  -- left side: the coefficient of `(γ⁻¹)^P`
  set H : ℝ → ℂ := fun θ => exp ((P : ℂ) * ((e.symm θ : ℂ) * I)) * exp (-((Q : ℂ) * θ * I)) with hH
  have hHc : Continuous H :=
    (Complex.continuous_exp.comp (continuous_const.mul
      ((Complex.continuous_ofReal.comp e.symm.continuous).mul continuous_const))).mul (by fun_prop)
  have hHp : Function.Periodic H (2 * π) := by
    intro θ
    simp only [hH, hper]
    congr 1
    · rw [show (P : ℂ) * (((e.symm θ + 2 * π : ℝ) : ℂ) * I) = (P : ℂ) * ((e.symm θ : ℂ) * I) + (P : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact (Complex.exp_periodic.int_mul P) _
    · rw [show -((Q : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) = -((Q : ℂ) * θ * I) + ((-Q : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact (Complex.exp_periodic.int_mul (-Q)) _
  have hL : circleCoeff (fun z => Function.invFunOn γ unitCircle z ^ P) Q =
      (1 / (2 * π)) * ∫ t in Ioc 0 (2 * π), exp (-(((-P : ℤ) : ℂ) * t * I)) * exp (c * (f t : ℂ)) ∂f.measure := by
    unfold circleCoeff fourierCoeff
    congr 1
    have h1 : ∫ θ in (0 : ℝ)..2 * π, Function.invFunOn γ unitCircle (exp (θ * I)) ^ P * exp (-((Q : ℂ) * θ * I)) =
        ∫ θ in (0 : ℝ)..2 * π, H θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [hH, hGe, ← Complex.exp_int_mul]
    rw [h1]
    have hshift := hHp.intervalIntegral_add_eq 0 (f 0)
    rw [zero_add] at hshift
    rw [hshift, intervalIntegral.integral_of_le (by linarith), ← show f (2 * π) = f 0 + 2 * π by
      simpa using hp' 0, ← s5ns_lift_cov f hc hm hp' hHc 0 (2 * π)]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [hH, hef, hcdef]
      congr 1 <;> congr 1 <;> push_cast <;> ring
  -- right side: the coefficient of `γ^{-Q}`
  have hR : circleCoeff (fun z => γ z ^ (-Q)) (-P) =
      (1 / (2 * π)) * ∫ t in (0 : ℝ)..2 * π, exp (c * (f t : ℂ)) * exp (-(((-P : ℤ) : ℂ) * t * I)) := by
    unfold circleCoeff fourierCoeff
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hu, ← Complex.exp_int_mul, hcdef]
    congr 1
    congr 1
    push_cast
    ring
  have hlhs : ∫ t in Ioc 0 (2 * π), exp (-(((-P : ℤ) : ℂ) * t * I)) * (c * exp (c * (f t : ℂ))) ∂f.measure =
      c * ∫ t in Ioc 0 (2 * π), exp (-(((-P : ℤ) : ℂ) * t * I)) * exp (c * (f t : ℂ)) ∂f.measure := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [hlhs] at hibp
  beta_reduce at hibp
  set X := ∫ t in Ioc 0 (2 * π), exp (-(((-P : ℤ) : ℂ) * t * I)) * exp (c * (f t : ℂ)) ∂f.measure with hXdef
  set Y := ∫ t in (0 : ℝ)..2 * π, exp (c * (f t : ℂ)) * exp (-(((-P : ℤ) : ℂ) * t * I)) with hYdef
  push_cast at hibp
  have key : (Q : ℂ) * X = P * Y := by
    linear_combination I * hibp - (I * X) * hcdef + ((Q : ℂ) * X - P * Y) * Complex.I_sq
  rw [hL, hR]
  linear_combination (1 / (2 * π : ℂ)) * key

/-- Circle traces of continuous circle functions are continuous. -/
theorem s5mab_trace {F : ℂ → ℂ} (hc : ContinuousOn F unitCircle) : Continuous (fun θ : ℝ => F (exp (θ * I))) :=
  hc.comp_continuous (by fun_prop) (fun θ => s5ns_exp_mem θ)

/-- Differences of continuous `HC` functions lie in `HC`. -/
theorem s5mab_sub_HC {F₁ F₂ : ℂ → ℂ} (h₁ : F₁ ∈ HC) (h₂ : F₂ ∈ HC) (c₁ : ContinuousOn F₁ unitCircle)
    (c₂ : ContinuousOn F₂ unitCircle) : (fun z => F₁ z - F₂ z) ∈ HC :=
  ⟨((s5mab_trace c₁).sub (s5mab_trace c₂)).intervalIntegrable _ _, by
    simpa only [s5ns_coeff_sub (s5mab_trace c₁) (s5mab_trace c₂)] using (s5ns_energy_sub h₁.2 h₂.2).1⟩

/-- Coordinates only see the nonzero modes. -/
theorem s5mab_coords_congr {F₁ F₂ : ℂ → ℂ} (h₁ : F₁ ∈ HC) (h₂ : F₂ ∈ HC)
    (he : ∀ k : ℤ, k ≠ 0 → circleCoeff F₁ k = circleCoeff F₂ k) :
    s5ca_coordinates F₁ h₁ = s5ca_coordinates F₂ h₂ := by
  apply Prod.ext
  · ext n
    change s5ca_coeff F₁ false n = s5ca_coeff F₂ false n
    simp only [s5ca_coeff, Bool.false_eq_true, ite_false]
    rw [he _ (by omega)]
  · ext n
    change s5ca_coeff F₁ true n = s5ca_coeff F₂ true n
    simp only [s5ca_coeff, ite_true]
    rw [he _ (by omega)]

/-- The coordinate distance is controlled by the energy of the coefficient difference. -/
theorem s5mab_coords_sub {F₁ F₂ : ℂ → ℂ} (h₁ : F₁ ∈ HC) (h₂ : F₂ ∈ HC) (c₁ : ContinuousOn F₁ unitCircle)
    (c₂ : ContinuousOn F₂ unitCircle) :
    ‖s5ca_coordinates F₁ h₁ - s5ca_coordinates F₂ h₂‖ ^ 2 ≤
      ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F₁ n - circleCoeff F₂ n‖ ^ 2 := by
  have hD := s5mab_sub_HC h₁ h₂ c₁ c₂
  have hs := s5ns_coeff_sub (s5mab_trace c₁) (s5mab_trace c₂)
  have he : s5ca_coordinates F₁ h₁ - s5ca_coordinates F₂ h₂ = s5ca_coordinates (fun z => F₁ z - F₂ z) hD := by
    apply Prod.ext
    · ext n
      simp only [Prod.fst_sub, lp.coeFn_sub, Pi.sub_apply]
      change s5ca_coeff F₁ false n - s5ca_coeff F₂ false n = s5ca_coeff (fun z => F₁ z - F₂ z) false n
      simp only [s5ca_coeff, hs]
      ring
    · ext n
      simp only [Prod.snd_sub, lp.coeFn_sub, Pi.sub_apply]
      change s5ca_coeff F₁ true n - s5ca_coeff F₂ true n = s5ca_coeff (fun z => F₁ z - F₂ z) true n
      simp only [s5ca_coeff, hs]
      ring
  rw [he]
  refine (s5ca_prod_energy _).1.trans (le_of_eq ?_)
  rw [s5ca_coordinates_energy]
  simp only [hs]

/-- Energy convergence of the Abel–truncated approximants, at the coefficient level. -/
theorem s5mab_poly_energy {F : ℂ → ℂ} (hF : F ∈ HC) {N : ℕ → ℕ} (hNj : ∀ j, j ≤ N j) :
    Tendsto (fun j => ∑' k : ℤ, |(k : ℝ)| *
      ‖circleCoeff (s5ct_poly F (s5ct_radius j) (N j)) k - circleCoeff F k‖ ^ 2) atTop (𝓝 0) := by
  have hr (j : ℕ) := s5ct_radius_spec.1 j
  set w : ℕ → ℤ → ℝ := fun j k => s5ct_radius j ^ k.natAbs * if k.natAbs ≤ N j then 1 else 0 with hw
  have hw01 (j : ℕ) (k : ℤ) : 0 ≤ w j k ∧ w j k ≤ 1 := by
    have h0 := (hr j).1
    have h1 : s5ct_radius j ^ k.natAbs ≤ 1 := pow_le_one₀ h0 (hr j).2.le
    simp only [hw]
    split_ifs <;> constructor <;> simp only [mul_one, mul_zero] <;> first | positivity | linarith | norm_num
  have hdiff (j : ℕ) (k : ℤ) :
      |(k : ℝ)| * ‖circleCoeff (s5ct_poly F (s5ct_radius j) (N j)) k - circleCoeff F k‖ ^ 2 =
        |(k : ℝ)| * (‖circleCoeff F k‖ ^ 2 * (1 - w j k) ^ 2) := by
    by_cases hk : k = 0
    · subst hk
      simp
    rw [s5ns_poly_coeff_ne _ _ _ hk]
    congr 1
    have he : circleCoeff F k * ((s5ct_radius j : ℂ) ^ k.natAbs * if k.natAbs ≤ N j then 1 else 0) -
        circleCoeff F k = circleCoeff F k * ((w j k - 1 : ℝ) : ℂ) := by
      simp only [hw]
      push_cast
      split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero] <;> ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp only [hdiff]
  have hz : (∑' _ : ℤ, (0 : ℝ)) = 0 := tsum_zero
  rw [← hz]
  apply tendsto_tsum_of_dominated_convergence hF.2
  · intro k
    by_cases hk : k = 0
    · subst hk
      simp
    have hev : ∀ᶠ j in atTop, w j k = s5ct_radius j ^ k.natAbs := by
      filter_upwards [eventually_ge_atTop k.natAbs] with j hj
      simp only [hw, if_pos (hj.trans (hNj j)), mul_one]
    have hlimw : Tendsto (fun j => w j k) atTop (𝓝 1) := by
      have h := (s5ct_radius_spec.2).pow k.natAbs
      rw [one_pow] at h
      exact h.congr' (hev.mono fun j hj => hj.symm)
    have h : Tendsto (fun j => |(k : ℝ)| * (‖circleCoeff F k‖ ^ 2 * (1 - w j k) ^ 2)) atTop
        (𝓝 (|(k : ℝ)| * (‖circleCoeff F k‖ ^ 2 * (1 - 1) ^ 2))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hlimw).pow 2))
    simpa using h
  · refine Eventually.of_forall fun j k => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (1 - w j k) ^ 2 ≤ 1 := by nlinarith [hw01 j k]
    have h2 : 0 ≤ |(k : ℝ)| * ‖circleCoeff F k‖ ^ 2 := by positivity
    nlinarith [sq_nonneg (1 - w j k)]

/-- M2. The completed operator agrees with literal composition on continuous `HC` data. -/
theorem s5mab_compat {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) {F : ℂ → ℂ} (hF : F ∈ HC)
    (hc : ContinuousOn F unitCircle) (hP : piHat γ F ∈ HC) :
    s5ca_completed γ hγ (s5ca_coordinates F hF) = s5ca_coordinates (piHat γ F) hP := by
  obtain ⟨C, hC⟩ := s5ns_bound hγ
  obtain ⟨N, hNj, -⟩ := s5ct_uniform_approximation hc
  set r := s5ct_radius
  set P : ℕ → ℂ → ℂ := fun j => s5ct_poly F (r j) (N j) with hPdef
  have hPc (j : ℕ) : ContinuousOn (P j) unitCircle := (s5ct_poly_contDiff F _ _).continuous.continuousOn
  have hPH (j : ℕ) : P j ∈ HC := by
    refine ⟨((s5ct_poly_contDiff F _ _).continuous.comp (by fun_prop)).intervalIntegrable _ _, ?_⟩
    have h := (s5ns_energy_sub (s5ns_energy_sub hF.2 hF.2).1 hF.2).1
    apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hF.2
    by_cases hk : k = 0
    · subst hk
      simp
    rw [s5ns_poly_coeff_ne _ _ _ hk, norm_mul]
    have hw : ‖(r j : ℂ) ^ k.natAbs * (if k.natAbs ≤ N j then (1 : ℂ) else 0)‖ ≤ 1 := by
      have h0 := (s5ct_radius_spec.1 j).1
      have h1 := (s5ct_radius_spec.1 j).2.le
      split_ifs
      · rw [mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0]
        exact pow_le_one₀ h0 h1
      · simp
    have h2 : 0 ≤ |(k : ℝ)| := abs_nonneg _
    have h3 := norm_nonneg (circleCoeff F k)
    have h4 := norm_nonneg ((r j : ℂ) ^ k.natAbs * (if k.natAbs ≤ N j then (1 : ℂ) else 0))
    calc |(k : ℝ)| * (‖circleCoeff F k‖ * ‖(r j : ℂ) ^ k.natAbs * (if k.natAbs ≤ N j then (1 : ℂ) else 0)‖) ^ 2
        ≤ |(k : ℝ)| * (‖circleCoeff F k‖ * 1) ^ 2 := by gcongr
      _ = |(k : ℝ)| * ‖circleCoeff F k‖ ^ 2 := by ring
  have hPP (j : ℕ) : piHat γ (P j) ∈ HC := (hC _ (hPH j) (hPc j)).1
  -- the approximants are finite data
  let x : ℕ → ℕ → ℂ := fun j n => s5ca_coeff F false n * (r j : ℂ) ^ (n + 1)
  let y : ℕ → ℕ → ℂ := fun j n => s5ca_coeff F true n * (r j : ℂ) ^ (n + 1)
  let xf : ℕ → ℕ →₀ ℂ := fun j => Finsupp.onFinset (Finset.range (N j))
    (fun n => if n ∈ Finset.range (N j) then x j n else 0) (fun n hn => by by_contra h; exact hn (if_neg h))
  let yf : ℕ → ℕ →₀ ℂ := fun j => Finsupp.onFinset (Finset.range (N j))
    (fun n => if n ∈ Finset.range (N j) then y j n else 0) (fun n hn => by by_contra h; exact hn (if_neg h))
  have hxs (j : ℕ) : (xf j).support ⊆ Finset.range (N j) := Finsupp.support_onFinset_subset
  have hys (j : ℕ) : (yf j).support ⊆ Finset.range (N j) := Finsupp.support_onFinset_subset
  have hharm (j : ℕ) : s5qc_harmonic (Finset.range (N j)) (xf j) (yf j) =
      s5qc_harmonic (Finset.range (N j)) (x j) (y j) := by
    funext z
    rw [s5qc_harmonic_sum, s5qc_harmonic_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [xf, yf, Finsupp.onFinset_apply, if_pos hn]
  obtain ⟨K, -, hK⟩ := s5qc_piHat_smooth hγ
  have hHH (j : ℕ) : piHat γ (s5qc_harmonic (Finset.range (N j)) (xf j) (yf j)) ∈ HC :=
    (hK _ (s5qc_harmonic_contDiff _ _ _)).1
  -- `completed (coords P_j) = coords (piHat P_j)`
  have hA (j : ℕ) : s5ca_completed γ hγ (s5ca_coordinates (P j) (hPH j)) = s5ca_coordinates (piHat γ (P j)) (hPP j) := by
    have hB : s5ca_coordinates (P j) (hPH j) = (s5ca_embed (xf j), s5ca_embed (yf j)) := by
      apply Prod.ext
      · ext n
        change s5ca_coeff (P j) false n = s5ca_embed (xf j) n
        rw [s5ca_embed_apply]
        simp only [xf, Finsupp.onFinset_apply, Finset.mem_range, x, s5ca_coeff, Bool.false_eq_true, ite_false]
        rw [s5ns_poly_coeff_ne _ _ _ (by omega)]
        have hna : ((n : ℤ) + 1).natAbs = n + 1 := by omega
        rw [hna]
        by_cases hn : n < N j
        · rw [if_pos hn, if_pos (by omega)]
          ring
        · rw [if_neg hn, if_neg (by omega)]
          ring
      · ext n
        change s5ca_coeff (P j) true n = s5ca_embed (yf j) n
        rw [s5ca_embed_apply]
        simp only [yf, Finsupp.onFinset_apply, Finset.mem_range, y, s5ca_coeff, ite_true]
        rw [s5ns_poly_coeff_ne _ _ _ (by omega)]
        have hna : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
        rw [hna]
        by_cases hn : n < N j
        · rw [if_pos hn, if_pos (by omega)]
          ring
        · rw [if_neg hn, if_neg (by omega)]
          ring
    rw [hB, s5ca_completed_finite hγ (xf j) (yf j) (Finset.range (N j)) (hxs j) (hys j) (hHH j)]
    apply s5mab_coords_congr
    intro k hk
    have hhc : Continuous (s5qc_harmonic (Finset.range (N j)) (xf j) (yf j)) :=
      (s5qc_harmonic_contDiff _ _ _).continuous
    rw [s5ca_piHat_coeff hγ hhc hk, s5ns_piHat_coeff hγ (hPc j) hk, hharm]
    have hpe := s5ns_poly_eq F (r j) (N j)
    have h := s5ca_center_coeff (F := s5qc_harmonic (Finset.range (N j)) (x j) (y j) ∘ γ)
      (((s5qc_harmonic_contDiff _ _ _).continuous).comp (s5ca_circle_continuous hγ)) (-circleCoeff F 0) hk
    rw [← h]
    congr 1
    funext z
    simp only [Function.comp_apply, P, hpe]
    ring
  -- convergence of the inputs
  have hE := s5mab_poly_energy hF hNj
  have hin : Tendsto (fun j => s5ca_coordinates (P j) (hPH j)) atTop (𝓝 (s5ca_coordinates F hF)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun j => ‖s5ca_coordinates (P j) (hPH j) - s5ca_coordinates F hF‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun j => by positivity) (fun j => s5mab_coords_sub (hPH j) hF (hPc j) hc) hE
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h
    exact h.congr fun j => by simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]
  -- convergence of the outputs
  have hout : Tendsto (fun j => s5ca_coordinates (piHat γ (P j)) (hPP j)) atTop
      (𝓝 (s5ca_coordinates (piHat γ F) hP)) := by
    have hPc' (j : ℕ) : ContinuousOn (piHat γ (P j)) unitCircle :=
      ((hPc j).comp (s5ns_circle hγ).2 (s5ns_circle hγ).1).sub continuousOn_const
    have hFc' : ContinuousOn (piHat γ F) unitCircle :=
      (hc.comp (s5ns_circle hγ).2 (s5ns_circle hγ).1).sub continuousOn_const
    have hbd (j : ℕ) : (∑' k : ℤ, |(k : ℝ)| * ‖circleCoeff (piHat γ (P j)) k - circleCoeff (piHat γ F) k‖ ^ 2) ≤
        C * ∑' k : ℤ, |(k : ℝ)| * ‖circleCoeff (P j) k - circleCoeff F k‖ ^ 2 := by
      have hD := s5mab_sub_HC (hPH j) hF (hPc j) hc
      have hDc : ContinuousOn (fun z => P j z - F z) unitCircle := (hPc j).sub hc
      have hs := s5ns_coeff_sub (s5mab_trace (hPc j)) (s5mab_trace hc)
      refine le_of_eq_of_le ?_ ((hC _ hD hDc).2.trans (le_of_eq (by simp only [hs])))
      apply tsum_congr
      intro k
      by_cases hk : k = 0
      · subst hk
        simp
      rw [s5ns_piHat_coeff hγ (hPc j) hk, s5ns_piHat_coeff hγ hc hk, s5ns_piHat_coeff hγ hDc hk]
      congr 3
      exact (s5ns_coeff_sub (s5ns_comp_trace hγ (hPc j)) (s5ns_comp_trace hγ hc) k).symm
    have hE' := hE.const_mul C
    rw [mul_zero] at hE'
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun j => ‖s5ca_coordinates (piHat γ (P j)) (hPP j) - s5ca_coordinates (piHat γ F) hP‖ ^ 2)
        atTop (𝓝 0) :=
      squeeze_zero (fun j => by positivity)
        (fun j => (s5mab_coords_sub (hPP j) hP (hPc' j) hFc').trans (hbd j)) hE'
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h
    exact h.congr fun j => by simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]
  have hlim := ((s5ca_completed γ hγ).continuous.tendsto _).comp hin
  simp only [Function.comp_def, hA] at hlim
  exact tendsto_nhds_unique hlim hout

/-- M3. Clauses 3, 4. -/
theorem s5mab_basis {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (n + 1) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) = matA γ m n) ∧
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (-(n + 1 : ℤ)) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) =
        matB γ m n) := by
  have hsq (n : ℕ) : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have hdiv (m n : ℕ) : ((Real.sqrt (((m : ℝ) + 1) / ((n : ℝ) + 1)) : ℝ) : ℂ) =
      (Real.sqrt ((m : ℝ) + 1) : ℂ) / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
    rw [Real.sqrt_div (by positivity)]
    push_cast
    ring
  have hne (m : ℕ) : ((m : ℤ) + 1) ≠ 0 := by omega
  constructor
  · intro n m
    have hc : ContinuousOn (fun z : ℂ => z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) unitCircle :=
      ((continuous_pow _).div_const _).continuousOn
    rw [s5ns_piHat_coeff hγ hc (hne m)]
    rw [show ((fun z : ℂ => z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) ∘ γ) =
      fun z => (fun z => γ z ^ (n + 1)) z / (Real.sqrt ((n : ℝ) + 1) : ℂ) from rfl, circleCoeff_div_const]
    simp only [matA]
    rw [hdiv]
    field_simp [hsq n]
  · intro n m
    have hc : ContinuousOn (fun z : ℂ => z ^ (-(n + 1 : ℤ)) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) unitCircle := by
      apply ContinuousOn.div_const
      exact continuousOn_id.zpow₀ _ fun z hz => Or.inl (by
        intro h0
        have : ‖z‖ = 1 := hz
        rw [show z = 0 from h0, norm_zero] at this
        exact zero_ne_one this)
    rw [s5ns_piHat_coeff hγ hc (hne m)]
    rw [show ((fun z : ℂ => z ^ (-(n + 1 : ℤ)) / (Real.sqrt ((n : ℝ) + 1) : ℂ)) ∘ γ) =
      fun z => (fun z => γ z ^ (-(n + 1 : ℤ))) z / (Real.sqrt ((n : ℝ) + 1) : ℂ) from rfl, circleCoeff_div_const]
    simp only [matB]
    rw [hdiv]
    field_simp [hsq n]

/-- On `S¹`, `γ^{-k} = conj (γ^k)`, so `c_{-p}(γ^{-k}) = conj (c_p(γ^k))`. -/
theorem s5mab_coeff_inv_pow {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (k : ℕ) (p : ℤ) :
    circleCoeff (fun z => γ z ^ (-(k : ℤ))) (-p) = conj (circleCoeff (fun z => γ z ^ k) p) := by
  have he : EqOn (fun z => γ z ^ (-(k : ℤ))) (fun z => conj (γ z ^ k)) unitCircle := by
    intro z hz
    simp only
    rw [zpow_neg, zpow_natCast, map_pow, ← Complex.inv_eq_conj ((s5ns_circle hγ).1 hz), inv_pow]
  rw [s5qc_coeff_congr he, s5ns_coeff_conj, neg_neg]

/-- M4. Clause 5. -/
theorem s5mab_inv_mat {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
      ∀ m n, matA (Function.invFunOn γ unitCircle) m n = conj (matA γ n m) ∧
        matB (Function.invFunOn γ unitCircle) m n = -matB γ n m := by
  intro m n
  have hm0 : ((m : ℤ) + 1) ≠ 0 := by omega
  have hsq (k : ℕ) : (Real.sqrt ((k : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k + 1)).ne'
  have hsq2 (k : ℕ) : (Real.sqrt ((k : ℝ) + 1) : ℂ) ^ 2 = (k : ℂ) + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hdiv (a b : ℕ) : ((Real.sqrt (((a : ℝ) + 1) / ((b : ℝ) + 1)) : ℝ) : ℂ) =
      (Real.sqrt ((a : ℝ) + 1) : ℂ) / (Real.sqrt ((b : ℝ) + 1) : ℂ) := by
    rw [Real.sqrt_div (by positivity)]
    push_cast
    ring
  constructor
  · have h1 := s5mab_inv_coeff hγ ((n : ℤ) + 1) ((m : ℤ) + 1) hm0
    have hpow : (fun z => Function.invFunOn γ unitCircle z ^ ((n : ℤ) + 1)) =
        fun z => Function.invFunOn γ unitCircle z ^ (n + 1) := by
      funext z
      rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hconj := s5mab_coeff_inv_pow hγ (m + 1) ((n : ℤ) + 1)
    rw [hpow, show (-((m : ℤ) + 1)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, hconj] at h1
    simp only [matA, map_mul, Complex.conj_ofReal]
    rw [hdiv, hdiv]
    have hsm := hsq m
    have hsn := hsq n
    have e1 := hsq2 m
    have e2 := hsq2 n
    push_cast at h1
    rw [← e1, ← e2] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hsn hsm]
    linear_combination h1
  · have h1 := s5mab_inv_coeff hγ (-((n : ℤ) + 1)) ((m : ℤ) + 1) hm0
    rw [neg_neg] at h1
    simp only [matB]
    rw [hdiv, hdiv]
    have hsm := hsq m
    have hsn := hsq n
    have e1 := hsq2 m
    have e2 := hsq2 n
    push_cast at h1
    rw [← e1, ← e2] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← neg_div, div_eq_div_iff hsn hsm]
    linear_combination h1

/-- The positive normalized basis function, explicitly. -/
theorem s5mab_basis_false (n : ℕ) :
    s5ca_basis false n = fun z : ℂ => z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  funext z
  simp [s5ca_basis]

/-- The negative normalized basis function, explicitly. -/
theorem s5mab_basis_true (n : ℕ) :
    s5ca_basis true n = fun z : ℂ => conj z ^ (n + 1) / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  funext z
  simp [s5ca_basis]

/-- The basis functions lie in `HC`. -/
theorem s5mab_basis_HC (b : Bool) (n : ℕ) : s5ca_basis b n ∈ HC := by
  cases b
  · rw [s5mab_basis_false]
    refine (s5qc_HC_congr fun z _ => ?_).mpr (zpow_div_mem_HC ((n : ℤ) + 1) (Real.sqrt ((n : ℝ) + 1) : ℂ))
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  · rw [s5mab_basis_true]
    refine (s5qc_HC_congr fun z hz => ?_).mpr (zpow_div_mem_HC (-((n : ℤ) + 1)) (Real.sqrt ((n : ℝ) + 1) : ℂ))
    rw [← Complex.inv_eq_conj hz, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, inv_pow]

/-- Coordinates of the basis functions. -/
theorem s5mab_basis_coords (b : Bool) (n : ℕ) :
    s5ca_coordinates (s5ca_basis b n) (s5mab_basis_HC b n) =
      (if b then (0, lp.single 2 n 1) else (lp.single 2 n 1, 0)) := by
  have hsq : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  cases b
  · apply Prod.ext
    · ext m
      change s5ca_coeff (s5ca_basis false n) false m = (lp.single 2 n (1 : ℂ) : ell2) m
      rw [lp.single_apply, Pi.single_apply]
      simp only [s5ca_coeff, Bool.false_eq_true, ite_false, s5mab_basis_false, circleCoeff_div_const,
        s5ns_coeff_pow]
      by_cases h : m = n
      · subst h
        simp only [if_true]
        field_simp
      · rw [if_neg (by omega), if_neg h]
        simp
    · ext m
      change s5ca_coeff (s5ca_basis false n) true m = (0 : ell2) m
      simp only [s5ca_coeff, ite_true, s5mab_basis_false, circleCoeff_div_const, s5ns_coeff_pow]
      rw [if_neg (by omega)]
      simp
  · apply Prod.ext
    · ext m
      change s5ca_coeff (s5ca_basis true n) false m = (0 : ell2) m
      simp only [s5ca_coeff, Bool.false_eq_true, ite_false, s5mab_basis_true, circleCoeff_div_const,
        s5ns_coeff_conj_pow]
      rw [if_neg (by omega)]
      simp
    · ext m
      change s5ca_coeff (s5ca_basis true n) true m = (lp.single 2 n (1 : ℂ) : ell2) m
      rw [lp.single_apply, Pi.single_apply]
      simp only [s5ca_coeff, ite_true, s5mab_basis_true, circleCoeff_div_const, s5ns_coeff_conj_pow]
      by_cases h : m = n
      · subst h
        simp only [if_true]
        field_simp
      · rw [if_neg (by omega), if_neg h]
        simp

/-- `Π̂(γ) Π̂(γ⁻¹)` fixes the basis, in coordinates. -/
theorem s5mab_inv_column {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (b : Bool) (n : ℕ) :
    s5ca_completed γ hγ (s5ca_column (Function.invFunOn γ unitCircle) (s5mab_inv_qs hγ) b n) =
      (if b then (0, lp.single 2 n 1) else (lp.single 2 n 1, 0)) := by
  set G := Function.invFunOn γ unitCircle
  have hG := s5mab_inv_qs hγ
  obtain ⟨-, -, -, hGγ, -⟩ := s5ns_inv_data hγ
  obtain ⟨C, hC⟩ := s5ns_bound hγ
  have hψc : Continuous (s5ca_basis b n) := (s5ca_basis_contDiff b n).continuous
  have hFH : piHat G (s5ca_basis b n) ∈ HC := s5ca_basis_HC hG b n
  have hFc : ContinuousOn (piHat G (s5ca_basis b n)) unitCircle :=
    (hψc.comp_continuousOn (s5ns_circle hG).2).sub continuousOn_const
  have hFP := (hC _ hFH hFc).1
  change s5ca_completed γ hγ (s5ca_coordinates (piHat G (s5ca_basis b n)) hFH) = _
  rw [s5mab_compat hγ hFH hFc hFP, ← s5mab_basis_coords b n]
  apply s5mab_coords_congr
  intro k hk
  have he : EqOn (piHat γ (piHat G (s5ca_basis b n)))
      (fun z => s5ca_basis b n z - circleCoeff (s5ca_basis b n ∘ (G ∘ γ)) 0) unitCircle := by
    intro z hz
    rw [← s5ns_right hG γ hγ _ (s5mab_basis_HC b n) hψc.continuousOn z hz]
    simp only [piHat, Function.comp_apply, hGγ z hz]
    rfl
  rw [s5qc_coeff_congr he, s5ca_center_coeff (hψc.comp (by fun_prop)) _ hk]

/-- M5. Clauses 1, 2: the rows of `Π̂(γ)Π̂(γ⁻¹) = 1` with `Π̂(γ⁻¹) = (𝔄* -𝔅ᵗ; -𝔅* 𝔄ᵗ)` (M4). -/
theorem s5mab_rows {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∀ m n, mulAdj (matA γ) (matA γ) m n - mulAdj (matB γ) (matB γ) m n = kron m n) ∧
      (∀ m n, (∑' k, matA γ m k * matB γ n k) = ∑' k, matB γ m k * matA γ n k) := by
  have hG := s5mab_inv_qs hγ
  obtain ⟨hAb, hBb, -, -⟩ := s5ca_bounded_matrices hγ
  have hinv := s5mab_inv_mat hγ
  have hrow (b : Bool) (n m : ℕ) :
      (∑' k, matA γ m k * (s5ca_column (Function.invFunOn γ unitCircle) hG b n).1 k) + (∑' k, matB γ m k * (s5ca_column (Function.invFunOn γ unitCircle) hG b n).2 k) =
        ((if b then ((0 : ell2), lp.single 2 n (1 : ℂ)) else (lp.single 2 n (1 : ℂ), (0 : ell2))).1 : ell2) m := by
    have h := congrArg (fun u : ell2 × ell2 => u.1 m) (s5mab_inv_column hγ b n)
    have hb := s5ca_completed_blocks hγ (s5ca_column (Function.invFunOn γ unitCircle) hG b n).1 (s5ca_column (Function.invFunOn γ unitCircle) hG b n).2
    rw [Prod.mk.eta] at hb
    simp only [hb, lp.coeFn_add, Pi.add_apply, pmb_apply hAb, pmb_apply hBb, matApply] at h
    exact h
  constructor
  · intro m n
    have h := hrow false n m
    simp only [Bool.false_eq_true, ite_false, lp.single_apply, Pi.single_apply] at h
    have hx (k : ℕ) : (s5ca_column (Function.invFunOn γ unitCircle) hG false n).1 k = conj (matA γ n k) := by
      rw [s5ca_column_A hG k n, (hinv k n).1]
    have hy (k : ℕ) : (s5ca_column (Function.invFunOn γ unitCircle) hG false n).2 k = -conj (matB γ n k) := by
      rw [s5ca_column_conj hG false k n, Bool.not_false, s5ca_column_B hG k n, (hinv k n).2, map_neg]
    simp only [hx, hy, mul_neg, tsum_neg] at h
    unfold mulAdj kron
    rw [← h]
    ring
  · intro m n
    have h := hrow true n m
    simp only [ite_true, lp.coeFn_zero, Pi.zero_apply] at h
    have hx (k : ℕ) : (s5ca_column (Function.invFunOn γ unitCircle) hG true n).1 k = -matB γ n k := by
      rw [s5ca_column_B hG k n, (hinv k n).2]
    have hy (k : ℕ) : (s5ca_column (Function.invFunOn γ unitCircle) hG true n).2 k = matA γ n k := by
      rw [s5ca_column_conj hG true k n, Bool.not_true, s5ca_column_A hG k n, (hinv k n).1, Complex.conj_conj]
    simp only [hx, hy, mul_neg, tsum_neg] at h
    linear_combination -h

/-- (TT:5494–5520) In the basis `{e_n} ∪ {f_n}`, `Π̂(γ) = (𝔄 𝔅; 𝔅̄ 𝔄̄)` (columns: the images of `e_n`, `f_n`). By (5.1):
- `𝔄𝔄* - 𝔅𝔅* = I` and `𝔄𝔅ᵗ = 𝔅𝔄ᵗ`;
- `Π̂(γ⁻¹) = Π̂(γ)⁻¹ = (𝔄* -𝔅ᵗ; -𝔅* 𝔄ᵗ)`, so `𝔄(γ⁻¹) = 𝔄(γ)*` and `𝔅(γ⁻¹) = -𝔅(γ)ᵗ`. -/
theorem s5mab_matAB_spec {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∀ m n, mulAdj (matA γ) (matA γ) m n - mulAdj (matB γ) (matB γ) m n = kron m n) ∧
      (∀ m n, (∑' k, matA γ m k * matB γ n k) = ∑' k, matB γ m k * matA γ n k) ∧
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (n + 1) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) = matA γ m n) ∧
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (-(n + 1 : ℤ)) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) =
        matB γ m n) ∧
      ∀ m n, matA (Function.invFunOn γ unitCircle) m n = conj (matA γ n m) ∧
        matB (Function.invFunOn γ unitCircle) m n = -matB γ n m :=
  ⟨(s5mab_rows hγ).1, (s5mab_rows hγ).2, (s5mab_basis hγ).1, (s5mab_basis hγ).2, s5mab_inv_mat hγ⟩

/-- (TT:5494–5520) In the basis `{e_n} ∪ {f_n}`, `Π̂(γ) = (𝔄 𝔅; 𝔅̄ 𝔄̄)` (columns: the images of `e_n`, `f_n`). By (5.1):
- `𝔄𝔄* - 𝔅𝔅* = I` and `𝔄𝔅ᵗ = 𝔅𝔄ᵗ`;
- `Π̂(γ⁻¹) = Π̂(γ)⁻¹ = (𝔄* -𝔅ᵗ; -𝔅* 𝔄ᵗ)`, so `𝔄(γ⁻¹) = 𝔄(γ)*` and `𝔅(γ⁻¹) = -𝔅(γ)ᵗ`. -/
theorem matAB_spec {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∀ m n, mulAdj (matA γ) (matA γ) m n - mulAdj (matB γ) (matB γ) m n = kron m n) ∧
      (∀ m n, (∑' k, matA γ m k * matB γ n k) = ∑' k, matB γ m k * matA γ n k) ∧
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (n + 1) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) = matA γ m n) ∧
      (∀ n m : ℕ, circleCoeff (piHat γ fun z => z ^ (-(n + 1 : ℤ)) / Real.sqrt (n + 1)) (m + 1) * Real.sqrt (m + 1) =
        matB γ m n) ∧
      ∀ m n, matA (Function.invFunOn γ unitCircle) m n = conj (matA γ n m) ∧
        matB (Function.invFunOn γ unitCircle) m n = -matB γ n m :=
  s5mab_matAB_spec hγ

end TakhtajanTeo.Ch2
