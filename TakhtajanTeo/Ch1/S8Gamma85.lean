import TakhtajanTeo.Ch1.S7Cor79
import TakhtajanTeo.Ch1.S8Lemma84Conditional

/-!
# Program G, W-GAMMA sub-interface: `thm_8_5` and `eq_8_1` (下属1)

Direct route, unconditional (no `lemma_1_9`, no `lemma_8_4`, no interchange of limits). The cor_7_9 architecture of
T(1) is redone for `gGamma`; the integrals are over a fundamental domain `F` (finite hyperbolic area) instead of `𝔻*`.
The analysis is done in the model `𝕌` (Cayley transport), where the T(1) machinery lives.
* (D4) `s8g_D4`: pointwise uniform hyperbolic quasi-invariance of the 4-parameter family `W_P` of `s7g_L1`
  (coefficients `P.1.1 a + P.1.2 b` on `𝕌`, the reflected `P.2.1 ā + P.2.2 b̄` on `𝕃`), for complex `P` near `0`:
  `J_{W_P}(z) ≤ C dist(W_P z, ∂W_P(H))² ρ_𝕌(z)` on each half-plane `H`. Route: Stoilow factorisation
  `W_P = Ψ ∘ V` on `H` with `V` the symmetric solution (preserves `H`) and `Ψ` conformal on `H`; Koebe 1/4 for `Ψ`
  (`koebe_quarter`); K3 (`s8w_density`) for `V`, transported by the Cayley map. With `s7g_r1_pt`, `s7g_f2_wd` and
  the `r24` outside bound it gives `∫_𝕌 |K_P(t, s̄)|² ≲ ρ(s)`, the line-1 triple bound, and so every integrand is
  `≤ C ρ` on `F` uniformly in `P`; cusps cost only `∫_F ρ < ∞`.
* (CORE) `s8g_core`: `gGamma Γ μ ν (p₁κ + p₂l) = Φ(p̄, p)` with `Φ` separately holomorphic and bounded near `0`
  (line-2 representation over `F × 𝕌` via `s8w_selfAdj_quot`, K1/K2/K4/K5, Cayley transport, D4, `s7g_f2_Gint`).
* (FV) the first variation vanishes; (DIAG) the second variation (Γ-version of `thm_7_7`): line-1/line-2
  representations over `F`, `s7g_f2_mixed`, the pointwise identity `s7g_f2_pt` (needs only `IsHarmonicU`), and the
  identification of the three terms with `G_Γ` by unfolding (`fdD_hasSum_integral_unfold`) and a Γ-version of `cor_7_3`.
* (SES), (SYM): sesquilinear expansion and symmetry of the right-hand side (`K_Γ` symmetric, Fubini on `F × F`).
* Assembly: `s8g_C2` (`s7g_c79_hartogs`), `s8g_cor_7_9` (polarisation `s7g_c79_pol`, as `s7g_cor_7_9`),
  `s8g_thm_8_5`, `s8g_eq_8_1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `Ω^{-1,1}(𝔻)` is a complex vector space: `κ + c l`. -/
theorem s8g_harm_lin {κ l : ℂ → ℂ} (hκ : IsHarmonicD κ) (hl : IsHarmonicD l) (c : ℂ) :
    IsHarmonicD (fun z => κ z + c * l z) := by
  obtain ⟨φ, hφ, ⟨C, hC⟩, hr⟩ := hκ
  obtain ⟨ψ, hψ, ⟨D, hD⟩, hs⟩ := hl
  refine ⟨fun z => φ z + conj c * ψ z, hφ.add (hψ.const_mul _), ⟨C + ‖c‖ * D, fun z hz => ?_⟩, fun z hz => ?_⟩
  · dsimp only
    rw [mul_add, mul_left_comm _ (conj c)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul (conj c), Complex.norm_conj]
    exact add_le_add (hC z hz) (mul_le_mul_of_nonneg_left (hD z hz) (norm_nonneg c))
  · dsimp only
    rw [hr z hz, hs z hz]
    simp only [map_add, map_mul, Complex.conj_conj]
    ring

/-- `Γ`-invariance is preserved by `κ + c l`. -/
theorem s8g_inv_lin {Γ : Subgroup SL2C} {κ l : ℂ → ℂ} (hκ : IsGammaInvD Γ κ) (hl : IsGammaInvD Γ l) (c : ℂ) :
    IsGammaInvD Γ (fun z => κ z + c * l z) := by
  intro g hg z hz
  have h1 := hκ g hg z hz
  have h2 := hl g hg z hz
  dsimp only
  rw [← h1, ← h2]
  ring

/-- The half-plane step of D4: if `F` is q.c. on `H` with the coefficient of `κ ∘ σ` (`σ : H → 𝔻` conformal, an
isometry `ρ_𝔻(σ u)|σ'(u)|² = ρ_𝕌(u)`, `κ` harmonic and small), then `J_F(z) ≤ 16 C₃ dist(F z, ∂F(H))² ρ_𝕌(z)`, where
`C₃` is the constant of K3. Stoilow against `w_κ ∘ σ`, Koebe 1/4 for the conformal factor, K3. -/
theorem s8g_d4_half {σ F κ : ℂ → ℂ} {H : Set ℂ} (hH : IsOpen H) (hH0 : ∀ u ∈ H, u.im ≠ 0)
    (hσ : IsConformalOnto σ H unitDisc) (hρ : ∀ u ∈ H, rho (σ u) * ‖deriv σ u‖ ^ 2 = rhoU u)
    (hκ : IsHarmonicD κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ x ∈ unitDisc, ‖κ x‖ ≤ k) {C3 : ℝ}
    (hC3 : ∀ x ∈ unitDisc, rho (wD κ x) * ‖dz (wD κ) x‖ ^ 2 ≤ C3 * rho x)
    (hF : IsQuasiconformal F H)
    (hdil : ∀ᵐ u ∂(volume.restrict H), complexDilatation F u = κ (σ u) * (conj (deriv σ u) / deriv σ u))
    (hne : (F '' H)ᶜ.Nonempty) {z : ℂ} (hz : z ∈ H) :
    jacobian F z ≤ 16 * C3 * infDist (F z) (F '' H)ᶜ ^ 2 * rhoU z := by
  obtain ⟨-, hwmap, hwimg, hwd⟩ := s8w_wD_facts hκ hk1 hk
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ hk1 hk
  obtain ⟨⟨K, hK⟩, -, -, -, -⟩ := hN
  have hσd : ∀ u ∈ H, DifferentiableAt ℂ σ u := fun u hu => hσ.1.differentiableAt (hH.mem_nhds hu)
  have hσm : ∀ u ∈ H, σ u ∈ unitDisc := fun u hu => hσ.2.2 ▸ mem_image_of_mem σ hu
  have hρU : ∀ u ∈ H, 0 < rhoU u := fun u hu => by
    have h := hH0 u hu
    unfold rhoU
    positivity
  have hσ0 : ∀ u ∈ H, deriv σ u ≠ 0 := by
    intro u hu h0
    have e := hρ u hu
    rw [h0, norm_zero, zero_pow two_ne_zero, mul_zero] at e
    linarith [hρU u hu]
  have hGK : IsKQC (wD κ ∘ σ) H (1 * K) := thm7_1_comp (isKQC_one_of_conformal hH hσ) hK (subset_univ _)
  have hGdil : ∀ u ∈ H, complexDilatation (wD κ ∘ σ) u = κ (σ u) * (conj (deriv σ u) / deriv σ u) := by
    intro u hu
    obtain ⟨hwdu, hdz0, hdzb⟩ := hwd (σ u) (hσm u hu)
    obtain ⟨e1, e2⟩ := s8w_dz_comp_right hwdu (hσd u hu)
    unfold complexDilatation
    rw [e1, e2, hdzb]
    have h1 := hσ0 u hu
    have hc : conj (deriv σ u) ≠ 0 := (map_ne_zero _).2 h1
    field_simp
  have hdil' : ∀ᵐ u ∂(volume.restrict H), complexDilatation (wD κ ∘ σ) u = complexDilatation F u := by
    filter_upwards [hdil, ae_restrict_mem hH.measurableSet] with u hu hu'
    rw [hu, hGdil u hu']
  obtain ⟨φ, hφ, hrel⟩ := grp_stoilow hH ⟨_, hGK⟩ hF hdil'
  have hGH : (wD κ ∘ σ) '' H = unitDisc := by rw [image_comp, hσ.2.2, hwimg]
  rw [hGH] at hφ
  -- the local data at `z`
  have hxD : σ z ∈ unitDisc := hσm z hz
  obtain ⟨hwdx, -, -⟩ := hwd (σ z) hxD
  have hyD : wD κ (σ z) ∈ unitDisc := hwmap hxD
  have hφd : DifferentiableAt ℂ φ (wD κ (σ z)) := hφ.1.differentiableAt (isOpen_ball.mem_nhds hyD)
  have hGdz : DifferentiableAt ℝ (wD κ ∘ σ) z := hwdx.comp z ((hσd z hz).restrictScalars ℝ)
  have hev : F =ᶠ[𝓝 z] φ ∘ (wD κ ∘ σ) := by
    filter_upwards [hH.mem_nhds hz] with u hu
    exact hrel u hu
  have hFz : F z = φ (wD κ (σ z)) := hrel z hz
  have hdzF : dz F z = deriv φ (wD κ (σ z)) * (dz (wD κ) (σ z) * deriv σ z) := by
    rw [(ra_dz_congr hev).1, (ra_dz_comp_holo (f := wD κ ∘ σ) (z := z) hφd hGdz).1, (s8w_dz_comp_right hwdx (hσd z hz)).1]
    rfl
  have hJ : jacobian F z ≤ ‖deriv φ (wD κ (σ z))‖ ^ 2 * (‖deriv σ z‖ ^ 2 * ‖dz (wD κ) (σ z)‖ ^ 2) := by
    unfold jacobian
    have hb : 0 ≤ ‖dzbar F z‖ ^ 2 := by positivity
    rw [hdzF, norm_mul, norm_mul]
    nlinarith [hb]
  -- Koebe 1/4 for `φ` on `B(y, 1 - |y|)`
  set y := wD κ (σ z) with hy
  set r := 1 - ‖y‖ with hr
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hyD
  have hr0 : 0 < r := by rw [hr]; linarith
  have hx0 : 0 < rho (σ z) := s8w_rho_pos hxD
  have hC30 : 0 ≤ C3 := by
    have h := hC3 (σ z) hxD
    have h0 : 0 ≤ rho y * ‖dz (wD κ) (σ z)‖ ^ 2 := mul_nonneg (s8w_rho_pos hyD).le (by positivity)
    nlinarith
  have hρy : 1 ≤ r ^ 2 * rho y := by
    have hy0 := norm_nonneg y
    have hd : 0 < 1 - ‖y‖ ^ 2 := by nlinarith
    have hle : (1 - ‖y‖ ^ 2) ^ 2 ≤ 4 * r ^ 2 := by
      rw [hr]
      nlinarith [mul_nonneg hy0 hr0.le]
    show 1 ≤ r ^ 2 * (4 / (1 - ‖y‖ ^ 2) ^ 2)
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  have hiso := hρ z hz
  have hK3 := hC3 (σ z) hxD
  by_cases hφ0 : deriv φ y = 0
  · rw [hφ0, norm_zero] at hJ
    have h1 : 0 ≤ 16 * C3 * infDist (F z) (F '' H)ᶜ ^ 2 * rhoU z := by
      have := hρU z hz
      positivity
    nlinarith
  have hφn : 0 < ‖deriv φ y‖ := norm_pos_iff.2 hφ0
  have hrd : (r : ℂ) * deriv φ y ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hr0.ne') hφ0
  have hmaps : ∀ t ∈ ball (0 : ℂ) 1, y + r * t ∈ unitDisc := by
    intro t ht
    have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
    refine mem_ball_zero_iff.2 ?_
    calc ‖y + r * t‖ ≤ ‖y‖ + r * ‖t‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      _ < ‖y‖ + r * 1 := by gcongr
      _ = 1 := by rw [hr]; ring
  have hfd : DifferentiableOn ℂ (fun t => (φ (y + r * t) - φ y) / (r * deriv φ y)) (ball (0 : ℂ) 1) := by
    intro t ht
    have h1 : DifferentiableAt ℂ φ (y + r * t) := hφ.1.differentiableAt (isOpen_ball.mem_nhds (hmaps t ht))
    have h2 : DifferentiableAt ℂ (fun t : ℂ => y + r * t) t := by fun_prop
    exact ((h1.comp t h2).sub_const _).div_const _ |>.differentiableWithinAt
  have hfi : InjOn (fun t => (φ (y + r * t) - φ y) / (r * deriv φ y)) (ball (0 : ℂ) 1) := by
    intro t1 ht1 t2 ht2 he
    have he' : φ (y + r * t1) = φ (y + r * t2) := by
      have := he
      simp only at this
      rw [div_left_inj' hrd, sub_left_inj] at this
      exact this
    have := hφ.2.1 (hmaps t1 ht1) (hmaps t2 ht2) he'
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
    have h3 : (r : ℂ) * t1 = r * t2 := by linear_combination this
    exact mul_left_cancel₀ hr' h3
  have hf0 : (fun t => (φ (y + r * t) - φ y) / (r * deriv φ y)) 0 = 0 := by simp
  have hf1 : deriv (fun t => (φ (y + r * t) - φ y) / (r * deriv φ y)) 0 = 1 := by
    have h1 : HasDerivAt φ (deriv φ y) (y + r * 0) := by
      rw [mul_zero, add_zero]
      exact hφd.hasDerivAt
    have h2 : HasDerivAt (fun t : ℂ => y + r * t) (r : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add y
    have h3 := ((h1.comp 0 h2).sub_const (φ y)).div_const ((r : ℂ) * deriv φ y)
    have h4 : deriv (fun t => (φ (y + r * t) - φ y) / (r * deriv φ y)) 0 =
        deriv φ y * r / (r * deriv φ y) := h3.deriv
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
    rw [h4]
    field_simp
  have hq := koebe_quarter hfd hfi hf0 hf1
  have hsub : ball (φ y) (r * ‖deriv φ y‖ / 4) ⊆ F '' H := by
    intro w hw
    have ht0 : (w - φ y) / (r * deriv φ y) ∈ ball (0 : ℂ) (1 / 4) := by
      rw [mem_ball_zero_iff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        div_lt_iff₀ (by positivity)]
      have := mem_ball.1 hw
      rw [dist_eq_norm] at this
      linarith
    obtain ⟨t, ht, hte⟩ := hq ht0
    simp only at hte
    rw [div_left_inj' hrd, sub_left_inj] at hte
    rw [← hφ.2.2, ← hte]
    exact mem_image_of_mem φ (hmaps t ht)
  have hinf : r * ‖deriv φ y‖ / 4 ≤ infDist (F z) (F '' H)ᶜ := by
    refine (Metric.le_infDist hne).2 fun w hw => ?_
    by_contra hlt
    push Not at hlt
    apply hw
    apply hsub
    rw [mem_ball, dist_comm, ← hFz]
    exact hlt
  -- assembly
  have hD0 : 0 ≤ r * ‖deriv φ y‖ / 4 := by positivity
  have hsq : (r * ‖deriv φ y‖) ^ 2 ≤ 16 * infDist (F z) (F '' H)ᶜ ^ 2 := by
    have := pow_le_pow_left₀ hD0 hinf 2
    nlinarith
  have hrz := hρU z hz
  calc jacobian F z ≤ ‖deriv φ y‖ ^ 2 * (‖deriv σ z‖ ^ 2 * ‖dz (wD κ) (σ z)‖ ^ 2) := hJ
    _ ≤ ‖deriv φ y‖ ^ 2 * (‖deriv σ z‖ ^ 2 * ‖dz (wD κ) (σ z)‖ ^ 2) * (r ^ 2 * rho y) :=
        le_mul_of_one_le_right (by positivity) hρy
    _ = (r * ‖deriv φ y‖) ^ 2 * ‖deriv σ z‖ ^ 2 * (rho y * ‖dz (wD κ) (σ z)‖ ^ 2) := by ring
    _ ≤ (r * ‖deriv φ y‖) ^ 2 * ‖deriv σ z‖ ^ 2 * (C3 * rho (σ z)) := by gcongr
    _ = (r * ‖deriv φ y‖) ^ 2 * C3 * rhoU z := by rw [← hiso]; ring
    _ ≤ 16 * infDist (F z) (F '' H)ᶜ ^ 2 * C3 * rhoU z := by gcongr
    _ = 16 * C3 * infDist (F z) (F '' H)ᶜ ^ 2 * rhoU z := by ring

/-- `(1 - |S u|²)² = -(u - ū)² |S'(u)|²` for the Cayley map `S`, as complex numbers. -/
theorem s8g_d4_bf {u : ℂ} (hu : u ∈ upperHalf) :
    ((1 : ℂ) - (‖cayley u‖ : ℂ) ^ 2) ^ 2 =
      -(u - conj u) ^ 2 * (2 * I / (u + I) ^ 2 * conj (2 * I / (u + I) ^ 2)) := by
  have hb := rhoU_cayley_boundary_factor hu
  have hN : 0 < Complex.normSq (u + I) := Complex.normSq_pos.2 (cayley_den_ne_zero hu)
  have e1 : (1 : ℂ) - (‖cayley u‖ : ℂ) ^ 2 = ((4 * u.im / Complex.normSq (u + I) : ℝ) : ℂ) := by
    rw [← hb]
    push_cast
    ring
  have e2 : 2 * I / (u + I) ^ 2 * conj (2 * I / (u + I) ^ 2) = ((4 / Complex.normSq (u + I) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]
    congr 1
    rw [Complex.normSq_div]
    simp only [map_pow, Complex.normSq_mul, Complex.normSq_ofNat, Complex.normSq_I]
    norm_num
  rw [e1, e2, Complex.sub_conj]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Cayley transport of a harmonic Beltrami differential on `𝕌` to `𝔻`:
`κ(x) = A(S⁻¹x) S'(S⁻¹x)/\overline{S'(S⁻¹x)}` is harmonic on `𝔻`, bounded by the same constant, and
`κ(S u) \overline{S'(u)}/S'(u) = A(u)`. -/
theorem s8g_d4_kU {A φ : ℂ → ℂ} (hA : IsHarmonicU A φ) {k : ℝ} (hAk : ∀ u ∈ upperHalf, ‖A u‖ ≤ k) :
    IsHarmonicD (fun x => A (cayleyInv x) * (2 * I / (cayleyInv x + I) ^ 2 / conj (2 * I / (cayleyInv x + I) ^ 2))) ∧
      (∀ x ∈ unitDisc, ‖A (cayleyInv x) * (2 * I / (cayleyInv x + I) ^ 2 /
        conj (2 * I / (cayleyInv x + I) ^ 2))‖ ≤ k) ∧
      ∀ u ∈ upperHalf, A (cayleyInv (cayley u)) * (2 * I / (cayleyInv (cayley u) + I) ^ 2 /
        conj (2 * I / (cayleyInv (cayley u) + I) ^ 2)) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) = A u := by
  have hmem : ∀ x ∈ unitDisc, cayleyInv x ∈ upperHalf := fun x hx => cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 hx)
  have hd0 : ∀ u ∈ upperHalf, 2 * I / (u + I) ^ 2 ≠ 0 := fun u hu =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
  have hph : ∀ x, ‖2 * I / (cayleyInv x + I) ^ 2 / conj (2 * I / (cayleyInv x + I) ^ 2)‖ ≤ 1 := by
    intro x
    rw [norm_div, Complex.norm_conj]
    exact div_self_le_one _
  -- the representation on `𝔻`
  have hrep : ∀ x ∈ unitDisc, A (cayleyInv x) * (2 * I / (cayleyInv x + I) ^ 2 /
      conj (2 * I / (cayleyInv x + I) ^ 2)) =
      ((1 : ℂ) - (‖x‖ : ℂ) ^ 2) ^ 2 * conj (-(1 / 2) * φ (cayleyInv x) / (2 * I / (cayleyInv x + I) ^ 2) ^ 2) := by
    intro x hx
    have hu := hmem x hx
    have hx' : cayley (cayleyInv x) = x := cayley_cayleyInv (mem_ball_zero_iff.1 hx)
    have hbf := s8g_d4_bf hu
    rw [hx'] at hbf
    rw [hbf, hA.2.2 _ hu]
    have hd := hd0 _ hu
    have hdc : conj (2 * I / (cayleyInv x + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hd
    generalize 2 * I / (cayleyInv x + I) ^ 2 = d at hd hdc ⊢
    simp only [map_div₀, map_mul, map_neg, map_one, map_ofNat, map_pow]
    field_simp
  refine ⟨⟨fun x => -(1 / 2) * φ (cayleyInv x) / (2 * I / (cayleyInv x + I) ^ 2) ^ 2, ?_, ⟨k, fun x hx => ?_⟩,
    hrep⟩, fun x hx => ?_, fun u hu => ?_⟩
  · have hci := s35a_x_isConformalOnto_cayleyInv.1
    intro x hx
    have hu := hmem x hx
    have h1 : DifferentiableAt ℂ cayleyInv x := hci.differentiableAt (isOpen_ball.mem_nhds hx)
    have h2 : DifferentiableAt ℂ φ (cayleyInv x) :=
      hA.1.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu)
    have h3 : DifferentiableAt ℂ (fun x => 2 * I / (cayleyInv x + I) ^ 2) x :=
      (differentiableAt_const _).div ((h1.add_const I).pow 2) (pow_ne_zero _ (cayley_den_ne_zero hu))
    exact (((h2.comp x h1).const_mul _).div (h3.pow 2) (pow_ne_zero _ (hd0 _ hu))).differentiableWithinAt
  · have h := hrep x hx
    calc ‖((1 : ℂ) - (‖x‖ : ℂ) ^ 2) ^ 2 * (-(1 / 2) * φ (cayleyInv x) / (2 * I / (cayleyInv x + I) ^ 2) ^ 2)‖
        = ‖((1 : ℂ) - (‖x‖ : ℂ) ^ 2) ^ 2 *
            conj (-(1 / 2) * φ (cayleyInv x) / (2 * I / (cayleyInv x + I) ^ 2) ^ 2)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]
      _ = ‖A (cayleyInv x) * (2 * I / (cayleyInv x + I) ^ 2 / conj (2 * I / (cayleyInv x + I) ^ 2))‖ := by
          rw [h]
      _ ≤ k := by
          rw [norm_mul]
          have h0 := (norm_nonneg (A (cayleyInv x)))
          nlinarith [hAk _ (hmem x hx), hph x]
  · rw [norm_mul]
    have h0 := (norm_nonneg (A (cayleyInv x)))
    nlinarith [hAk _ (hmem x hx), hph x, norm_nonneg (2 * I / (cayleyInv x + I) ^ 2 /
      conj (2 * I / (cayleyInv x + I) ^ 2))]
  · rw [cayleyInv_cayley hu]
    have hd := hd0 u hu
    have hdc : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hd
    have hc := cayley_den_ne_zero hu
    field_simp

/-- `Ω^{-1,1}(𝕌)` is a complex vector space: `p a + q b`. -/
theorem s8g_harmU_lin {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) (p q : ℂ) :
    IsHarmonicU (fun u => p * a u + q * b u) (fun u => conj p * φa u + conj q * φb u) := by
  obtain ⟨ha1, ⟨Ca, hCa⟩, ha3⟩ := ha
  obtain ⟨hb1, ⟨Cb, hCb⟩, hb3⟩ := hb
  refine ⟨(ha1.const_mul _).add (hb1.const_mul _), ⟨‖p‖ * Ca + ‖q‖ * Cb, fun z hz => ?_⟩, fun z hz => ?_⟩
  · rw [mul_add, mul_left_comm _ (conj p), mul_left_comm _ (conj q)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul (conj p), norm_mul (conj q), Complex.norm_conj, Complex.norm_conj]
    exact add_le_add (mul_le_mul_of_nonneg_left (hCa z hz) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hCb z hz) (norm_nonneg _))
  · dsimp only
    rw [ha3 z hz, hb3 z hz]
    simp only [map_add, map_mul, Complex.conj_conj]
    ring

/-- Reflection `κ ↦ \overline{κ(z̄)}` preserves `Ω^{-1,1}(𝔻)`. -/
theorem s8g_d4_reflD {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) : IsHarmonicD (fun x => conj (κ (conj x))) := by
  obtain ⟨φ, hφ, ⟨C, hC⟩, hr⟩ := hκ
  have hcD : ∀ x ∈ unitDisc, conj x ∈ unitDisc := fun x hx => by
    refine mem_ball_zero_iff.2 ?_
    rw [Complex.norm_conj]
    exact mem_ball_zero_iff.1 hx
  refine ⟨fun x => conj (φ (conj x)), fun x hx => ?_, ⟨C, fun x hx => ?_⟩, fun x hx => ?_⟩
  · have h1 : DifferentiableAt ℂ φ (conj x) := hφ.differentiableAt (isOpen_ball.mem_nhds (hcD x hx))
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  · have h := hC (conj x) (hcD x hx)
    rw [Complex.norm_conj] at h
    rw [norm_mul, Complex.norm_conj]
    rw [norm_mul] at h
    exact h
  · dsimp only
    rw [hr (conj x) (hcD x hx), Complex.norm_conj]
    simp only [map_mul, map_pow, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj]

/-- `σ₂(u) = \overline{S(ū)}` maps `𝕃` conformally onto `𝔻`, with derivative `\overline{S'(ū)}`, isometrically. -/
theorem s8g_d4_sig2 :
    IsConformalOnto (fun u => conj (cayley (conj u))) {u : ℂ | u.im < 0} unitDisc ∧
      ∀ u : ℂ, u.im < 0 → HasDerivAt (fun u => conj (cayley (conj u))) (conj (2 * I / (conj u + I) ^ 2)) u ∧
        rho (conj (cayley (conj u))) * ‖deriv (fun u => conj (cayley (conj u))) u‖ ^ 2 = rhoU u := by
  have hc := isConformalOnto_cayley
  have hcu : ∀ u : ℂ, u.im < 0 → conj u ∈ upperHalf := fun u hu => by
    show 0 < (conj u).im
    rw [Complex.conj_im]
    linarith
  have hd : ∀ u : ℂ, u.im < 0 →
      HasDerivAt (fun u => conj (cayley (conj u))) (conj (2 * I / (conj u + I) ^ 2)) u := by
    intro u hu
    have h := (rhoU_hasDerivAt_cayley (hcu u hu)).conj_conj
    rw [Complex.conj_conj] at h
    exact h
  refine ⟨⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt, ?_, ?_⟩, fun u hu => ⟨hd u hu, ?_⟩⟩
  · intro u1 hu1 u2 hu2 he
    have he' : cayley (conj u1) = cayley (conj u2) := by
      have := congrArg conj he
      simpa only [Complex.conj_conj] using this
    have := hc.2.1 (hcu u1 hu1) (hcu u2 hu2) he'
    simpa only [Complex.conj_conj] using congrArg conj this
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h := hc.2.2 ▸ mem_image_of_mem cayley (hcu u hu)
      refine mem_ball_zero_iff.2 ?_
      rw [Complex.norm_conj]
      exact mem_ball_zero_iff.1 h
    · intro hx
      have hx' : conj x ∈ unitDisc := by
        refine mem_ball_zero_iff.2 ?_
        rw [Complex.norm_conj]
        exact mem_ball_zero_iff.1 hx
      rw [← hc.2.2] at hx'
      obtain ⟨w, hw, hwe⟩ := hx'
      refine ⟨conj w, ?_, ?_⟩
      · show (conj w).im < 0
        rw [Complex.conj_im]
        have : 0 < w.im := hw
        linarith
      · simp only [Complex.conj_conj, hwe]
  · have h := rhoU_cayley_pullback (hcu u hu)
    rw [(hd u hu).deriv, Complex.norm_conj, ← (rhoU_hasDerivAt_cayley (hcu u hu)).deriv]
    have e1 : rho (conj (cayley (conj u))) = rho (cayley (conj u)) := by
      unfold rho
      rw [Complex.norm_conj]
    have e2 : rhoU (conj u) = rhoU u := by
      unfold rhoU
      rw [Complex.conj_im, neg_sq]
    rw [e1, h, e2]

/-- STUB D4. Pointwise uniform hyperbolic quasi-invariance of the 4-parameter family `W_P` (both half-planes). -/
theorem s8g_D4 {k : ℝ} (hk : 0 ≤ k) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, ∀ a φa b φb : ℂ → ℂ, IsHarmonicU a φa → IsHarmonicU b φb →
      (∀ u ∈ upperHalf, ‖a u‖ ≤ k) → (∀ u ∈ upperHalf, ‖b u‖ ≤ k) →
      ∀ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = (fun P => normalizedSolution fun u =>
          (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
            (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0)) →
      ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R, ∀ z ∈ upperHalf,
        jacobian (W P) z ≤ C * infDist (W P z) (W P '' upperHalf)ᶜ ^ 2 * rhoU z ∧
          jacobian (W P) (conj z) ≤ C * infDist (W P (conj z)) (W P '' {u : ℂ | u.im < 0})ᶜ ^ 2 * rhoU z := by
  obtain ⟨δ₀, hδ0, hδ1, C3, hC3⟩ := s8w_density
  refine ⟨δ₀ / (4 * (k + 1)), by positivity, 16 * C3, ?_⟩
  intro a φa b φb ha hb hak hbk W hW P hP z hz
  set R := δ₀ / (4 * (k + 1)) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hRk : 2 * R * k ≤ δ₀ / 2 := by
    calc 2 * R * k = δ₀ / 2 * (k / (k + 1)) := by rw [hRdef]; field_simp; ring
      _ ≤ δ₀ / 2 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ₀ / 2 := mul_one _
  have hk0 : 0 ≤ 2 * R * k := by positivity
  have hk2 : 2 * R * k < 1 := by linarith
  have hk2δ : 2 * R * k < δ₀ := by linarith
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  -- `W P` is the normalised solution: q.c., injective, with the prescribed coefficient
  have haB : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hak u hu⟩
  have hbB : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hbk u hu⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, -, -, hm₂0, hm₁0, heq⟩ :=
    s7g_r1_coeffs hk haB hbB (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb) hP
  have hc : IsBeltramiCoeff (fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) univ (2 * R * k) := by
    simpa using s7g_r1_supp hk0 hm₁ hm₂ hm₂0 hm₁0 (1, 1)
  have hWP : W P = normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u := by
    rw [hW]
    exact congrArg normalizedSolution heq
  have hspec := QCV.qcv_ns_spec hk0 hk2 hc
  rw [← hWP] at hspec
  obtain ⟨⟨K, hK⟩, -, -, -, hdilW⟩ := hspec
  obtain ⟨-, -, ⟨-, hinj, -, -⟩, -⟩ := id hK
  have hdil0 : ∀ᵐ u, complexDilatation (W P) u = (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
      (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0) := by
    filter_upwards [hdilW] with u hu
    rw [hu]
    exact (congrFun heq u).symm
  have hne : ∀ H : Set ℂ, (0 : ℂ) ∉ H → (W P '' H)ᶜ.Nonempty := by
    intro H h0
    refine ⟨W P 0, ?_⟩
    rintro ⟨u, hu, he⟩
    have : u = 0 := hinj (mem_univ _) (mem_univ _) he
    exact h0 (this ▸ hu)
  have hP' : ‖P‖ ≤ R := by simpa using hP
  have hp11 : ‖P.1.1‖ ≤ R := (norm_fst_le P.1).trans ((norm_fst_le P).trans hP')
  have hp12 : ‖P.1.2‖ ≤ R := (norm_snd_le P.1).trans ((norm_fst_le P).trans hP')
  have hp21 : ‖P.2.1‖ ≤ R := (norm_fst_le P.2).trans ((norm_snd_le P).trans hP')
  have hp22 : ‖P.2.2‖ ≤ R := (norm_snd_le P.2).trans ((norm_snd_le P).trans hP')
  have hbd : ∀ (p q : ℂ) (u : ℂ), u ∈ upperHalf → ‖p‖ ≤ R → ‖q‖ ≤ R → ‖p * a u + q * b u‖ ≤ 2 * R * k := by
    intro p q u hu hp hq
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hp (hak u hu) (norm_nonneg _) hR0
    have h2 := mul_le_mul hq (hbk u hu) (norm_nonneg _) hR0
    linarith
  constructor
  · -- the upper half-plane, through `S`
    obtain ⟨hκ, hκk, hκrel⟩ := s8g_d4_kU (s8g_harmU_lin ha hb P.1.1 P.1.2)
      (fun u hu => hbd P.1.1 P.1.2 u hu hp11 hp12)
    have hK3 := hC3 _ hκ (fun x hx => (hκk x hx).trans_lt hk2δ)
    refine s8g_d4_half (σ := cayley) hUo (fun u hu => ne_of_gt hu) isConformalOnto_cayley
      (fun u hu => rhoU_cayley_pullback hu) hκ hk2 hκk hK3 ⟨K, nx_isKQC_restrict hK hUo (subset_univ _)⟩ ?_
      (hne _ (fun h => by have h' : 0 < (0 : ℂ).im := h; simp at h')) hz
    filter_upwards [ae_restrict_of_ae hdil0, ae_restrict_mem hU] with u hu hu'
    have hu0 : 0 < u.im := hu'
    have hu1 : ¬ u.im < 0 := by linarith
    rw [hu, (rhoU_hasDerivAt_cayley hu').deriv]
    beta_reduce
    rw [hκrel u hu']
    simp only [hu0, hu1, ↓reduceIte, add_zero]
  · -- the lower half-plane, through `σ₂ = conj ∘ S ∘ conj`
    obtain ⟨hκ, hκk, hκrel⟩ := s8g_d4_kU (s8g_harmU_lin ha hb (conj P.2.1) (conj P.2.2))
      (fun u hu => hbd _ _ u hu (by rw [Complex.norm_conj]; exact hp21) (by rw [Complex.norm_conj]; exact hp22))
    have hκ2 := s8g_d4_reflD hκ
    have hκ2k : ∀ x ∈ unitDisc, ‖conj ((fun x => (conj P.2.1 * a (cayleyInv x) + conj P.2.2 * b (cayleyInv x)) *
        (2 * I / (cayleyInv x + I) ^ 2 / conj (2 * I / (cayleyInv x + I) ^ 2))) (conj x))‖ ≤ 2 * R * k := by
      intro x hx
      rw [Complex.norm_conj]
      refine hκk (conj x) ?_
      refine mem_ball_zero_iff.2 ?_
      rw [Complex.norm_conj]
      exact mem_ball_zero_iff.1 hx
    have hK3 := hC3 _ hκ2 (fun x hx => (hκ2k x hx).trans_lt hk2δ)
    obtain ⟨hσ, hσd⟩ := s8g_d4_sig2
    have hz' : conj z ∈ {u : ℂ | u.im < 0} := by
      show (conj z).im < 0
      rw [Complex.conj_im]
      have : 0 < z.im := hz
      linarith
    have h := s8g_d4_half hLo (fun u hu => ne_of_lt hu) hσ (fun u hu => (hσd u hu).2) hκ2 hk2 hκ2k hK3
      ⟨K, nx_isKQC_restrict hK hLo (subset_univ _)⟩ ?_ (hne _ (fun h => by have h' : (0 : ℂ).im < 0 := h; simp at h'))
      hz'
    · have e2 : rhoU (conj z) = rhoU z := by
        unfold rhoU
        rw [Complex.conj_im, neg_sq]
      rwa [e2] at h
    filter_upwards [ae_restrict_of_ae hdil0, ae_restrict_mem hLo.measurableSet] with u hu hu'
    have hu0 : u.im < 0 := hu'
    have hu1 : ¬ 0 < u.im := by linarith
    have hcu : conj u ∈ upperHalf := by
      show 0 < (conj u).im
      rw [Complex.conj_im]
      linarith
    rw [hu, (hσd u hu0).1.deriv]
    beta_reduce
    have hr := congrArg conj (hκrel (conj u) hcu)
    simp only [map_mul, map_div₀, Complex.conj_conj, map_add] at hr
    simp only [hu0, hu1, ↓reduceIte, zero_add, Complex.conj_conj, map_mul, map_div₀]
    rw [← hr]
    simp only [map_add, map_mul, Complex.conj_conj]

/-- CORE step 1, the line-2 identity in the model `𝔻` (TT:3304–3349): with `w = w_κ`,
`g_{μν̄}(κ) = (12/π) ∬_F ν̄(v) \overline{w_z(v)}² ∬_𝔻 μ(t) w_z(t)²/(1 - w(t)\overline{w(v)})⁴ d²t d²v`.
From A3 (`s8w_final`), quotient self-adjointness P5 for `Γ`, and K2 for the inner integral. -/
theorem s8g_c_line2D {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hκΓ : IsGammaInvD Γ κ) {k : ℝ} (hk1 : k < 1) (hk : ∀ z ∈ unitDisc, ‖κ z‖ ≤ k) {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ u) * ‖dz (wD κ) u‖ ^ 2 ≤ C * rho u) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    gGamma Γ μ ν κ = (12 / π : ℂ) * ∫ v in fundDomainOn Γ unitDisc, conj (ν v) * conj (dz (wD κ) v) ^ 2 *
      ∫ t in unitDisc, μ t * dz (wD κ) t ^ 2 / (1 - wD κ t * conj (wD κ v)) ^ 4 := by
  rw [← s8w_final hΓ hκ hκΓ hk1 hk hC hμ hν hμΓ hνΓ]
  obtain ⟨hlamb, hlamm, hlamΓ⟩ := s8w_lambda_facts hΓ.1 hκ hκΓ hk1 hk hC hμ hμΓ
  have hFD := s8w_fundD hΓ.1
  unfold innerGamma quotIntD
  rw [s8w_selfAdj_quot hΓ.1 hFD (s8w_area_fin hΓ) hlamm hlamb hlamΓ hν hνΓ, ← integral_const_mul]
  obtain ⟨⟨e, he⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts hκ hk1 hk
  have hinj : InjOn (wD κ) unitDisc := by rw [← he]; exact e.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ) u ∧ dzbar (wD κ) u = κ u * dz (wD κ) u ∧ ‖κ u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk u hu).trans hk1.le⟩
  have hRf := s8w_R_facts hκ hk1 hk (harmonicD_continuousOn hμ) (harmonicD_bound hμ).choose_spec
  have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  refine setIntegral_congr_fun hFD.1 fun v hv => ?_
  have hvD : v ∈ unitDisc := hFD.2.1 hv
  -- the inner integral, by K2
  have hI : (∫ ζ in unitDisc, RnmD μ κ ζ / (1 - ζ * conj (wD κ v)) ^ 4) =
      ∫ t in unitDisc, μ t * dz (wD κ) t ^ 2 / (1 - wD κ t * conj (wD κ v)) ^ 4 := by
    conv_lhs => rw [← hD]
    rw [s8w_change (S := unitDisc) hinj hd measurableSet_ball subset_rfl]
    refine setIntegral_congr_fun measurableSet_ball fun t ht => ?_
    rw [hRf.1 t ht, Complex.real_smul]
    have hdn := (hdiff t ht).2.1
    have hcd : conj (dz (wD κ) t) ≠ 0 := (map_ne_zero _).mpr hdn
    have hK : (1 : ℂ) - (‖κ t‖ : ℂ) ^ 2 ≠ 0 := by
      have : (1 : ℝ) - ‖κ t‖ ^ 2 ≠ 0 := by nlinarith [hk t ht, norm_nonneg (κ t)]
      exact_mod_cast this
    push_cast
    rw [hnsq (dz (wD κ) t)]
    field_simp
  have hwv : wD κ v ∈ unitDisc := hmaps hvD
  have hρw : (rho (wD κ v) : ℂ) * ((1 : ℂ) - (‖wD κ v‖ : ℂ) ^ 2) ^ 2 = 4 := by
    have h1 : (1 : ℝ) - ‖wD κ v‖ ^ 2 ≠ 0 := by
      have := mem_ball_zero_iff.1 hwv
      nlinarith [norm_nonneg (wD κ v)]
    unfold rho
    push_cast
    have h1' : (1 : ℂ) - (‖wD κ v‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1
    field_simp
  have hρv : (rho v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (s8w_rho_pos hvD).ne'
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  show harmonicProjD (RnmD μ κ) (wD κ v) * conj (dz (wD κ) v) ^ 2 * (rho (wD κ v) : ℂ) / (rho v : ℂ) *
      conj (ν v) * (rho v : ℂ) = _
  unfold harmonicProjD
  rw [hI]
  generalize (∫ t in unitDisc, μ t * dz (wD κ) t ^ 2 / (1 - wD κ t * conj (wD κ v)) ^ 4) = J
  generalize (rho v : ℂ) = P2 at hρv ⊢
  field_simp
  linear_combination (3 * J * conj (dz (wD κ) v) ^ 2 * conj (ν v)) * hρw

/-- The 4-parameter family on a closed polydisc `‖P‖ ≤ R`, `2Rk < 1`: `K`-q.c. onto `ℂ`, injective, with the
prescribed coefficient almost everywhere. -/
theorem s8g_W_spec {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) {P : (ℂ × ℂ) × (ℂ × ℂ)}
    (hP : P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R) :
    IsKQC (W P) univ ((1 + 2 * R * k) / (1 - 2 * R * k)) ∧ InjOn (W P) univ ∧
      ∀ᵐ u, complexDilatation (W P) u = (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0) := by
  have hU := measurableSet_upperHalf_aux
  have haB : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hak u hu⟩
  have hbB : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hbk u hu⟩
  obtain ⟨hK, -, -, -⟩ := s7g_r1_W hk haB hbB (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb) hR hRk
    hW hP
  have hk0 : 0 ≤ 2 * R * k := by positivity
  obtain ⟨m₁, m₂, hm₁, hm₂, -, -, hm₂0, hm₁0, heq⟩ :=
    s7g_r1_coeffs hk haB hbB (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb) hP
  have hc : IsBeltramiCoeff (fun u => (1 : ℂ) * m₁ u + 1 * m₂ u) univ (2 * R * k) := by
    simpa using s7g_r1_supp hk0 hm₁ hm₂ hm₂0 hm₁0 (1, 1)
  have hWP : W P = normalizedSolution fun u => (1 : ℂ) * m₁ u + 1 * m₂ u := by
    rw [hW]
    exact congrArg normalizedSolution heq
  have hspec := QCV.qcv_ns_spec hk0 hRk hc
  rw [← hWP] at hspec
  obtain ⟨-, -, -, -, hdilW⟩ := hspec
  obtain ⟨-, -, ⟨-, hinj, -, -⟩, -⟩ := id hK
  refine ⟨hK, hinj, ?_⟩
  filter_upwards [hdilW] with u hu
  rw [hu]
  exact (congrFun heq u).symm

/-- `Aut(𝔻)` preserves the kernel `1/(1 - X Ȳ)²`: `M'(X) \overline{M'(Y)}/(1 - M(X)\overline{M(Y)})² = 1/(1 - X Ȳ)²`
for `M = c · blaschke a`, `|c| = 1`. -/
theorem s8g_c_mob {c a X Y : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    c * ((1 - a * conj a) / (1 - conj a * X) ^ 2) * conj (c * ((1 - a * conj a) / (1 - conj a * Y) ^ 2)) /
        (1 - c * blaschke a X * conj (c * blaschke a Y)) ^ 2 = 1 / (1 - X * conj Y) ^ 2 := by
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hX0 := blaschke_den_ne_zero ha hX
  have hY0 := blaschke_den_ne_zero ha hY
  have hY0' : (1 : ℂ) - a * conj Y ≠ 0 := by
    intro h
    apply hY0
    have := congrArg conj h
    simpa [map_sub, map_mul] using this
  have haa : (1 : ℂ) - a * conj a ≠ 0 := one_sub_mul_conj_ne_zero ha
  have hXY : (1 : ℂ) - X * conj Y ≠ 0 := by
    intro h
    have h1 : ‖X * conj Y‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
    rw [norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg X, norm_nonneg Y]
  have hX0' : (1 : ℂ) - X * conj a ≠ 0 := by rw [mul_comm]; exact hX0
  have hY0'' : (1 : ℂ) - conj Y * a ≠ 0 := by rw [mul_comm]; exact hY0'
  have hkey : (1 : ℂ) - c * blaschke a X * conj (c * blaschke a Y) =
      (1 - a * conj a) * (1 - X * conj Y) / ((1 - conj a * X) * (1 - a * conj Y)) := by
    unfold blaschke
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_conj]
    rw [show c * ((X - a) / (1 - conj a * X)) * (conj c * ((conj Y - conj a) / (1 - a * conj Y))) =
      (c * conj c) * ((X - a) / (1 - conj a * X) * ((conj Y - conj a) / (1 - a * conj Y))) by ring, hcc, one_mul]
    field_simp
    ring
  rw [hkey]
  simp only [map_mul, map_div₀, map_sub, map_one, map_pow, Complex.conj_conj]
  rw [show c * ((1 - a * conj a) / (1 - conj a * X) ^ 2) * (conj c * ((1 - conj a * a) / (1 - a * conj Y) ^ 2)) =
    (c * conj c) * ((1 - a * conj a) / (1 - conj a * X) ^ 2 * ((1 - conj a * a) / (1 - a * conj Y) ^ 2)) by ring,
    hcc, one_mul]
  field_simp

/-- The Cayley map turns the `𝔻`-kernel into minus the `𝕌`-kernel:
`S'(x)\overline{S'(y)}/(1 - S(x)\overline{S(y)})² = -1/(x - ȳ)²`. -/
theorem s8g_c_cay {x y : ℂ} (hx : x ∈ upperHalf) (hy : y ∈ upperHalf) :
    2 * I / (x + I) ^ 2 * conj (2 * I / (y + I) ^ 2) / (1 - cayley x * conj (cayley y)) ^ 2 =
      -1 / (x - conj y) ^ 2 := by
  have hx0 := cayley_den_ne_zero hx
  have hy0 := cayley_den_ne_zero hy
  have hy0' : conj y - I ≠ 0 := by
    intro h
    apply hy0
    have := congrArg conj h
    simpa [map_sub, Complex.conj_I] using this
  have hxy : x - conj y ≠ 0 := by
    intro h
    have h1 : x.im = (conj y).im := by rw [sub_eq_zero.1 h]
    rw [Complex.conj_im] at h1
    have : 0 < x.im := hx
    have : 0 < y.im := hy
    linarith
  have hkey : (1 : ℂ) - cayley x * conj (cayley y) = -2 * I * (x - conj y) / ((x + I) * (conj y - I)) := by
    have ey : conj (cayley y) = (conj y + I) / (conj y - I) := by
      unfold cayley
      rw [map_div₀, map_sub, map_add, Complex.conj_I, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [ey, show cayley x = (x - I) / (x + I) from rfl, div_mul_div_comm, one_sub_div (mul_ne_zero hx0 hy0')]
    congr 1
    ring
  have hc' : conj (2 * I / (y + I) ^ 2) = -2 * I / (conj y - I) ^ 2 := by
    rw [map_div₀, map_pow, map_add, map_mul, Complex.conj_I, map_ofNat, ← sub_eq_add_neg]
    ring
  have hI : (2 * I) * (-2 * I) = 4 := by ring_nf; rw [Complex.I_sq]; ring
  have hI' : (-2 * I) ^ 2 = -4 := by ring_nf; rw [Complex.I_sq]; ring
  calc 2 * I / (x + I) ^ 2 * conj (2 * I / (y + I) ^ 2) / (1 - cayley x * conj (cayley y)) ^ 2
      = (2 * I * (-2 * I)) / ((-2 * I) ^ 2 * (x - conj y) ^ 2) := by
        rw [hkey, hc']
        field_simp
    _ = 4 / (-4 * (x - conj y) ^ 2) := by rw [hI, hI']
    _ = -1 / (x - conj y) ^ 2 := by
        field_simp

/-- The symmetric member `V = W_{(q, q̄)}` of the 4-parameter family: `V(x̄) = \overline{V(x)}`, and `V` maps `𝕌` onto
`𝕌`. -/
theorem s8g_c_Vsym {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) {q : ℂ × ℂ}
    (hq : ((q.1, q.2), (conj q.1, conj q.2)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R) :
    (∀ x, W ((q.1, q.2), (conj q.1, conj q.2)) (conj x) = conj (W ((q.1, q.2), (conj q.1, conj q.2)) x)) ∧
      W ((q.1, q.2), (conj q.1, conj q.2)) '' upperHalf = upperHalf := by
  have hU := measurableSet_upperHalf_aux
  have hq' : ‖((q.1, q.2), (conj q.1, conj q.2))‖ ≤ R := mem_closedBall_zero_iff.1 hq
  have h1 : ‖q.1‖ ≤ R := (norm_fst_le (q.1, q.2)).trans ((norm_fst_le _).trans hq')
  have h2 : ‖q.2‖ ≤ R := (norm_snd_le (q.1, q.2)).trans ((norm_fst_le _).trans hq')
  set m : ℂ → ℂ := fun u => q.1 * a u + q.2 * b u with hmdef
  have hmB : IsBeltramiCoeff m upperHalf (2 * R * k) := by
    refine ⟨((harmonicU_continuousOn ha).const_smul q.1).add ((harmonicU_continuousOn hb).const_smul q.2)
      |>.aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => ?_⟩
    show ‖q.1 * a u + q.2 * b u‖ ≤ 2 * R * k
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := mul_le_mul h1 (hak u hu) (norm_nonneg _) hR
    have := mul_le_mul h2 (hbk u hu) (norm_nonneg _) hR
    linarith
  have hk0 : 0 ≤ 2 * R * k := by positivity
  obtain ⟨-, hbij, hsym, hinv⟩ := p71_V_facts hk0 hmB (ε := 1) (by rw [norm_one, one_mul]; exact hRk)
  have hVeq : (wU fun y => (1 : ℂ) * m y) = W ((q.1, q.2), (conj q.1, conj q.2)) := by
    have h := s7g_c79_wU a b (conj q.1, conj q.2)
    simp only [Complex.conj_conj] at h
    rw [hW]
    simp only [one_mul]
    exact h
  rw [hVeq] at hsym hinv hbij
  refine ⟨hsym, ?_⟩
  set V := W ((q.1, q.2), (conj q.1, conj q.2))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : 0 < x.im := hx
    show 0 < (V x).im
    by_contra hneg
    push Not at hneg
    rcases hneg.lt_or_eq with hlt | heq
    · have hc : conj (V x) ∈ upperHalf := by
        show 0 < (conj (V x)).im
        rw [Complex.conj_im]
        linarith
      obtain ⟨hi1, hi2⟩ := hinv _ hc
      have e : V (Function.invFun V (conj (V x))) = V (conj x) := by rw [hi2, hsym]
      have h3 := hbij.1 e
      rw [h3] at hi1
      have h4 : 0 < (conj x).im := hi1
      rw [Complex.conj_im] at h4
      linarith
    · have hr : V (conj x) = V x := by
        rw [hsym]
        apply Complex.ext
        · simp
        · rw [Complex.conj_im, heq]
          simp
      have := hbij.1 hr
      have h3 : (conj x).im = x.im := by rw [this]
      rw [Complex.conj_im] at h3
      linarith
  · intro hy
    exact ⟨_, (hinv y hy).1, (hinv y hy).2⟩

/-- CORE kernel identity: with `w = w_κ'` on `𝔻` and `V = W_{(q, q̄)}` on `𝕌` (same coefficient after the Cayley
transport), the `𝔻`-kernel at `S τ, S s` is minus the `𝕌`-kernel `V'(τ)V'(s̄)/(V τ - V s̄)²`. -/
theorem s8g_c_kernel {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) {q : ℂ × ℂ}
    (hq : ((q.1, q.2), (conj q.1, conj q.2)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R)
    {κ' : ℂ → ℂ} (hκ' : IsHarmonicD κ') {k' : ℝ} (hk1 : k' < 1) (hk' : ∀ z ∈ unitDisc, ‖κ' z‖ ≤ k')
    (hm : ∀ u ∈ upperHalf, q.1 * a u + q.2 * b u =
      κ' (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {s τ : ℂ} (hs : s ∈ upperHalf) (hτ : τ ∈ upperHalf) :
    dz (wD κ') (cayley τ) * conj (dz (wD κ') (cayley s)) /
        (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 2 * (2 * I / (τ + I) ^ 2 * conj (2 * I / (s + I) ^ 2)) =
      -(dz (W ((q.1, q.2), (conj q.1, conj q.2))) τ * dz (W ((q.1, q.2), (conj q.1, conj q.2))) (conj s) /
        (W ((q.1, q.2), (conj q.1, conj q.2)) τ - W ((q.1, q.2), (conj q.1, conj q.2)) (conj s)) ^ 2) := by
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hsym, hVimg⟩ := s8g_c_Vsym ha hb hk hak hbk hW hR hRk hq
  obtain ⟨hVK, -, hVdil⟩ := s8g_W_spec ha hb hk hak hbk hW hR hRk hq
  have haB : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hak u hu⟩
  have hbB : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hbk u hu⟩
  obtain ⟨-, -, hVs, -⟩ := s7g_r1_W hk haB hbB (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb) hR
    hRk hW hq
  set V := W ((q.1, q.2), (conj q.1, conj q.2)) with hVdef
  have hVd : ∀ x ∈ upperHalf, DifferentiableAt ℝ V x := fun x hx =>
    (hVs.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds (ne_of_gt (show 0 < x.im from hx)))
  -- `F = w_κ' ∘ S` and Stoilow against `V`
  obtain ⟨-, hwmap, hwimg, hwd⟩ := s8w_wD_facts hκ' hk1 hk'
  obtain ⟨-, hN, -, -⟩ := s8w_wD_normalized hκ' hk1 hk'
  obtain ⟨⟨K, hK⟩, -, -, -, -⟩ := hN
  have hcay := isConformalOnto_cayley
  have hFK : IsKQC (wD κ' ∘ cayley) upperHalf (1 * K) :=
    thm7_1_comp (isKQC_one_of_conformal hUo hcay) hK (subset_univ _)
  have hcm : ∀ u ∈ upperHalf, cayley u ∈ unitDisc := fun u hu => hcay.2.2 ▸ mem_image_of_mem cayley hu
  have hcd : ∀ u ∈ upperHalf, DifferentiableAt ℂ cayley u := fun u hu =>
    (rhoU_hasDerivAt_cayley hu).differentiableAt
  have hFdil : ∀ u ∈ upperHalf, complexDilatation (wD κ' ∘ cayley) u = q.1 * a u + q.2 * b u := by
    intro u hu
    obtain ⟨hwdu, hdz0, hdzb⟩ := hwd (cayley u) (hcm u hu)
    obtain ⟨e1, e2⟩ := s8w_dz_comp_right hwdu (hcd u hu)
    unfold complexDilatation
    rw [e1, e2, hdzb, hm u hu, (rhoU_hasDerivAt_cayley hu).deriv]
    have hd0 : 2 * I / (u + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
    have hc0 : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hd0
    field_simp
  have hdil : ∀ᵐ u ∂(volume.restrict upperHalf), complexDilatation V u = complexDilatation (wD κ' ∘ cayley) u := by
    filter_upwards [ae_restrict_of_ae hVdil, ae_restrict_mem hU] with u hu hu'
    have hu0 : 0 < u.im := hu'
    have hu1 : ¬ u.im < 0 := by linarith
    rw [hu, hFdil u hu']
    simp only [hu0, hu1, ↓reduceIte, add_zero]
  obtain ⟨φ, hφ, hrel⟩ := grp_stoilow hUo ⟨_, nx_isKQC_restrict hVK hUo (subset_univ _)⟩ ⟨_, hFK⟩ hdil
  rw [hVimg, image_comp, hcay.2.2, hwimg] at hφ
  obtain ⟨c0, a0, hc0, ha0, hφeq⟩ :=
    exists_rotation_blaschke_of_isConformalOnto_unitDisc (hφ.comp s35a_x_isConformalOnto_cayleyInv)
  have hφU : ∀ x ∈ upperHalf, φ x = c0 * blaschke a0 (cayley x) := by
    intro x hx
    have h := hφeq (hcm x hx)
    simp only [Function.comp_apply, cayleyInv_cayley (show 0 < x.im from hx)] at h
    exact h
  have hVU : ∀ x ∈ upperHalf, V x ∈ upperHalf := fun x hx => hVimg ▸ mem_image_of_mem V hx
  -- derivative data at a point of `𝕌`
  have hloc : ∀ x ∈ upperHalf, wD κ' (cayley x) = c0 * blaschke a0 (cayley (V x)) ∧
      dz (wD κ') (cayley x) * (2 * I / (x + I) ^ 2) =
        c0 * ((1 - a0 * conj a0) / (1 - conj a0 * cayley (V x)) ^ 2) * (2 * I / (V x + I) ^ 2) * dz V x := by
    intro x hx
    have hVx := hVU x hx
    have hX : ‖cayley (V x)‖ < 1 := mem_ball_zero_iff.1 (hcm _ hVx)
    have hMd : HasDerivAt (fun y => c0 * blaschke a0 (cayley y))
        (c0 * ((1 - a0 * conj a0) / (1 - conj a0 * cayley (V x)) ^ 2) * (2 * I / (V x + I) ^ 2)) (V x) := by
      exact ((hasDerivAt_blaschke ha0 hX).const_mul c0).comp (V x) (rhoU_hasDerivAt_cayley hVx)
    have hev : (wD κ' ∘ cayley) =ᶠ[𝓝 x] (fun y => c0 * blaschke a0 (cayley y)) ∘ V := by
      filter_upwards [hUo.mem_nhds hx] with y hy
      rw [hrel y hy, Function.comp_apply, hφU _ (hVU y hy)]
    have e1 := (ra_dz_congr hev).1
    rw [(ra_dz_comp_holo (f := V) (z := x) hMd.differentiableAt (hVd x hx)).1, hMd.deriv] at e1
    obtain ⟨hwdx, -, -⟩ := hwd (cayley x) (hcm x hx)
    rw [(s8w_dz_comp_right hwdx (hcd x hx)).1, (rhoU_hasDerivAt_cayley hx).deriv] at e1
    refine ⟨?_, e1⟩
    have := hrel x hx
    rw [Function.comp_apply, hφU _ (hVx)] at this
    exact this
  obtain ⟨hFt, hDt⟩ := hloc τ hτ
  obtain ⟨hFs, hDs⟩ := hloc s hs
  have hXt : ‖cayley (V τ)‖ < 1 := mem_ball_zero_iff.1 (hcm _ (hVU τ hτ))
  have hXs : ‖cayley (V s)‖ < 1 := mem_ball_zero_iff.1 (hcm _ (hVU s hs))
  have hmob := s8g_c_mob hc0 ha0 hXt hXs
  have hcy := s8g_c_cay (hVU τ hτ) (hVU s hs)
  have hds : dz V (conj s) = conj (dz V s) := QCV.qcv_dz_conj_sym hsym s
  rw [hds, hsym s]
  calc dz (wD κ') (cayley τ) * conj (dz (wD κ') (cayley s)) /
        (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 2 * (2 * I / (τ + I) ^ 2 * conj (2 * I / (s + I) ^ 2))
      = (dz (wD κ') (cayley τ) * (2 * I / (τ + I) ^ 2)) * conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) /
          (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 2 := by
        rw [map_mul]
        ring
    _ = (c0 * ((1 - a0 * conj a0) / (1 - conj a0 * cayley (V τ)) ^ 2) *
            conj (c0 * ((1 - a0 * conj a0) / (1 - conj a0 * cayley (V s)) ^ 2)) /
            (1 - c0 * blaschke a0 (cayley (V τ)) * conj (c0 * blaschke a0 (cayley (V s)))) ^ 2) *
          (2 * I / (V τ + I) ^ 2 * conj (2 * I / (V s + I) ^ 2)) * (dz V τ * conj (dz V s)) := by
        rw [hDt, hDs, hFt, hFs]
        simp only [map_mul]
        ring
    _ = (2 * I / (V τ + I) ^ 2 * conj (2 * I / (V s + I) ^ 2) / (1 - cayley (V τ) * conj (cayley (V s))) ^ 2) *
          (dz V τ * conj (dz V s)) := by
        rw [hmob]
        ring
    _ = -(dz V τ * conj (dz V s) / (V τ - conj (V s)) ^ 2) := by
        rw [hcy]
        ring

/-- Change of variables through the Cayley map on a measurable subset of `𝕌`. -/
theorem s8g_cay_cov {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ upperHalf) (g : ℂ → ℂ) :
    ∫ w in cayley '' S, g w = ∫ z in S, ((‖2 * I / (z + I) ^ 2‖ ^ 2 : ℝ) : ℂ) * g (cayley z) := by
  have hi : InjOn cayley S := isConformalOnto_cayley.2.1.mono hSU
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z hz => ((rhoU_hasDerivAt_cayley (hSU hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi g]
  refine setIntegral_congr_fun hS fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _), Complex.real_smul]

/-- The Cayley preimage of the fundamental domain. -/
theorem s8g_cayE {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    MeasurableSet (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
      upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc ⊆ upperHalf ∧
      cayley '' (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) = fundDomainOn Γ unitDisc := by
  have hFD := s8w_fundD hΓ
  have hcm : Measurable cayley := by unfold cayley; fun_prop
  refine ⟨measurableSet_upperHalf_aux.inter (hcm hFD.1), inter_subset_left, ?_⟩
  ext v
  constructor
  · rintro ⟨s, ⟨-, hs⟩, rfl⟩
    exact hs
  · intro hv
    have hvD : ‖v‖ < 1 := mem_ball_zero_iff.1 (hFD.2.1 hv)
    refine ⟨cayleyInv v, ⟨cayleyInv_mem_upperHalf hvD, ?_⟩, cayley_cayleyInv hvD⟩
    show cayley (cayleyInv v) ∈ fundDomainOn Γ unitDisc
    rw [cayley_cayleyInv hvD]
    exact hv

/-- CORE step 3: the line-2 identity transported to `𝕌`. With `V = W_{(q, q̄)}` (same coefficient as `w_κ'` after the
Cayley transport) and `Bf(u) = f(S u) \overline{S'(u)}/S'(u)`:
`g_{μν̄}(κ') = (12/π) ∬_E \overline{Bν(s)} ∬_𝕌 Bμ(τ) (V'(τ)V'(s̄)/(V τ - V s̄)²)² d²τ d²s`, `E = S⁻¹(F)`. -/
theorem s8g_c_line2U {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) {κ' : ℂ → ℂ} (hκ' : IsHarmonicD κ')
    (hκ'Γ : IsGammaInvD Γ κ') {k' : ℝ} (hk1 : k' < 1) (hk' : ∀ z ∈ unitDisc, ‖κ' z‖ ≤ k') {C : ℝ}
    (hC : ∀ u ∈ unitDisc, rho (wD κ' u) * ‖dz (wD κ') u‖ ^ 2 ≤ C * rho u)
    {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) {q : ℂ × ℂ}
    (hq : ((q.1, q.2), (conj q.1, conj q.2)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R)
    (hm : ∀ u ∈ upperHalf, q.1 * a u + q.2 * b u =
      κ' (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    gGamma Γ μ ν κ' = (12 / π : ℂ) * ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
      conj (ν (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) *
        ∫ τ in upperHalf, μ (cayley τ) * (conj (2 * I / (τ + I) ^ 2) / (2 * I / (τ + I) ^ 2)) *
          (dz (W ((q.1, q.2), (conj q.1, conj q.2))) τ * dz (W ((q.1, q.2), (conj q.1, conj q.2))) (conj s) /
            (W ((q.1, q.2), (conj q.1, conj q.2)) τ - W ((q.1, q.2), (conj q.1, conj q.2)) (conj s)) ^ 2) ^ 2 := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨hEm, hEU, hEimg⟩ := s8g_cayE hΓ.1
  rw [s8g_c_line2D hΓ hκ' hκ'Γ hk1 hk' hC hμ hν hμΓ hνΓ]
  congr 1
  conv_lhs => rw [← hEimg]
  rw [s8g_cay_cov hEm hEU]
  refine setIntegral_congr_fun hEm fun s hs => ?_
  have hsU := hEU hs
  have hDimg : cayley '' upperHalf = unitDisc := isConformalOnto_cayley.2.2
  have hinner : (∫ t in unitDisc, μ t * dz (wD κ') t ^ 2 / (1 - wD κ' t * conj (wD κ' (cayley s))) ^ 4) =
      ∫ τ in upperHalf, ((‖2 * I / (τ + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
        (μ (cayley τ) * dz (wD κ') (cayley τ) ^ 2 / (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 4) := by
    conv_lhs => rw [← hDimg]
    exact s8g_cay_cov hU subset_rfl _
  rw [hinner]
  conv_lhs => rw [← integral_const_mul (L := ℂ), ← integral_const_mul (L := ℂ)]
  conv_rhs => rw [← integral_const_mul (L := ℂ)]
  refine setIntegral_congr_fun hU fun τ hτ => ?_
  have hker := s8g_c_kernel ha hb hk hak hbk hW hR hRk hq hκ' hk1 hk' hm hsU hτ
  have hds : 2 * I / (s + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hsU))
  have hdt : 2 * I / (τ + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hτ))
  have hdsc : conj (2 * I / (s + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hds
  have hdtc : conj (2 * I / (τ + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hdt
  have hnsq : ∀ x : ℂ, ((‖x‖ ^ 2 : ℝ) : ℂ) = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnsq, hnsq]
  set V := W ((q.1, q.2), (conj q.1, conj q.2))
  set KU := dz V τ * dz V (conj s) / (V τ - V (conj s)) ^ 2 with hKU
  have hK2 : KU = -(dz (wD κ') (cayley τ) * conj (dz (wD κ') (cayley s)) /
      (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 2 * (2 * I / (τ + I) ^ 2 * conj (2 * I / (s + I) ^ 2))) := by
    rw [hker]
    ring
  rw [hK2]
  simp only [map_mul, map_div₀, Complex.conj_conj]
  generalize hD : (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) = D
  generalize dz (wD κ') (cayley τ) = A
  generalize conj (dz (wD κ') (cayley s)) = B
  generalize 2 * I / (s + I) ^ 2 = cs at hds hdsc ⊢
  generalize 2 * I / (τ + I) ^ 2 = ct at hdt hdtc ⊢
  generalize conj cs = ccs at hdsc ⊢
  generalize conj ct = cct at hdtc ⊢
  field_simp

/-- The inner kernel integral at a point `s̄`: `∫_𝕌 |W'(τ)W'(s̄)/(W τ - W s̄)²|² ≤ c₀² C π ρ(s)` from the pointwise bound D4
on `𝕃` and the outside integral `∫_{|X - Y| ≥ d} |X - Y|⁻⁴ = π/d²`. -/
theorem s8g_c_inner {W : ℂ → ℂ} {K k' C : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ) (hk0 : 0 ≤ k')
    (hk1 : k' < 1) (hker : ∀ y : ℂ, y.im ≠ 0 → (1 - k' ^ 2) * ‖dz W y‖ ^ 2 ≤ jacobian W y)
    (hD4 : ∀ z ∈ upperHalf,
      jacobian W (conj z) ≤ C * infDist (W (conj z)) (W '' {u : ℂ | u.im < 0})ᶜ ^ 2 * rhoU z)
    {s : ℂ} (hsU : s ∈ upperHalf) :
    ∫⁻ τ in upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (C * π * rhoU s) := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hinj : Function.Injective W := by rw [← he]; exact e.injective
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hs0 : 0 < s.im := hsU
  have hcs : conj s ∈ {u : ℂ | u.im < 0} := by
    show (conj s).im < 0
    rw [Complex.conj_im]
    linarith
  set Y := W (conj s) with hY
  set d := infDist Y (W '' {u : ℂ | u.im < 0})ᶜ with hd
  have hLimg : IsOpen (W '' {u : ℂ | u.im < 0}) := by rw [← he]; exact e.isOpenMap _ hLo
  have hne : (W '' {u : ℂ | u.im < 0})ᶜ.Nonempty := by
    refine ⟨W 0, fun hW0 => ?_⟩
    obtain ⟨u, hu, he'⟩ := hW0
    have := hinj he'
    rw [this] at hu
    exact lt_irrefl _ (show (0 : ℂ).im < 0 from hu)
  have hd0 : 0 < d := by
    rw [hd]
    exact (hLimg.isClosed_compl.notMem_iff_infDist_pos (x := Y) hne).1 (fun hc => hc (mem_image_of_mem W hcs))
  have hc0 : (1 : ℝ) - k' ^ 2 > 0 := by nlinarith
  -- pointwise
  have hpt : ∀ τ ∈ upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
        (ENNReal.ofReal (jacobian W τ) * ((‖W τ - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4)) := by
    intro τ hτ
    have hw : W τ - W (conj s) ≠ 0 := by
      intro h
      have h1 := hinj (sub_eq_zero.1 h)
      have h2 : τ.im = (conj s).im := by rw [h1]
      rw [Complex.conj_im] at h2
      have : 0 < τ.im := hτ
      linarith
    have h := s7g_r1_pt hk1 hk0 hker hsU hτ hw 1 1
    simp only [one_mul, mul_one] at h
    refine h.trans (le_of_eq ?_)
    rw [one_div, enorm_eq_nnnorm, ENNReal.inv_pow]
    ring
  have hJs := hD4 s hsU
  calc ∫⁻ τ in upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2
      ≤ ∫⁻ τ in upperHalf, ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          (ENNReal.ofReal (jacobian W τ) * ((‖W τ - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4)) :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_upperHalf_aux).mono hpt)
    _ = ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          ∫⁻ X in W '' upperHalf, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
        rw [lintegral_const_mul' _ _ (by finiteness),
          QCV.qcv_lintegral_image_eq (nx_isKQC_restrict hK hUo (subset_univ _))]
    _ ≤ ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          ENNReal.ofReal (π / d ^ 2) := by
        gcongr
        refine r24_lintegral_outside hd0 fun X hX => ?_
        have hXc : X ∈ (W '' {u : ℂ | u.im < 0})ᶜ := by
          rintro ⟨u, hu, rfl⟩
          obtain ⟨v, hv, hvX⟩ := hX
          have := hinj hvX
          rw [this] at hv
          have h1 : 0 < u.im := hv
          have h2 : u.im < 0 := hu
          linarith
        rw [hd, ← dist_eq_norm, dist_comm]
        exact infDist_le_dist_of_mem hXc
    _ ≤ ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (C * π * rhoU s) := by
        rw [mul_assoc]
        gcongr
        rw [mul_comm, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc π / d ^ 2 * jacobian W (conj s) ≤ π / d ^ 2 * (C * d ^ 2 * rhoU s) := by
              gcongr
          _ = C * π * rhoU s := by field_simp

/-- The uniform `L¹` bound for the line-2 integrand over `E × S` (`E` of finite hyperbolic area, bounded data),
uniformly for `Q` in a polydisc: the Γ-version of `s7g_c79_L1`, through D4. -/
theorem s8g_c_L1 {a φa b φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {E S : Set ℂ} (hEm : MeasurableSet E) (hEU : E ⊆ upperHalf) (hSm : MeasurableSet S) (hSU : S ⊆ upperHalf)
    (hEA : ∫⁻ s in E, ENNReal.ofReal (rhoU s) < ∞) {A B : ℂ → ℂ} {CA CB : ℝ}
    (hA : ∀ s ∈ E, ‖A s‖ ≤ CA) (hB : ∀ t ∈ S, ‖B t‖ ≤ CB) :
    ∃ R : ℝ, 0 < R ∧ 2 * R * k < 1 ∧ ∃ M : ℝ, ∀ Q ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R,
      ∫⁻ x in E ×ˢ S, ‖A x.1 * (conj (B x.2) *
        (dz (W Q) x.2 * dz (W Q) (conj x.1) / (W Q x.2 - W Q (conj x.1)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal M := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨R4, hR4, C, hD4⟩ := s8g_D4 hk
  set R := min R4 (1 / (4 * (k + 1))) with hRdef
  have hR0 : 0 < R := lt_min hR4 (by positivity)
  have hRk : 2 * R * k < 1 := by
    have h1 : R ≤ 1 / (4 * (k + 1)) := min_le_right _ _
    have h2 : 2 * R * k ≤ 2 * (1 / (4 * (k + 1))) * k := by gcongr
    have h3 : 2 * (1 / (4 * (k + 1))) * k < 1 := by
      rw [show 2 * (1 / (4 * (k + 1))) * k = k / (2 * (k + 1)) by field_simp; ring, div_lt_one (by positivity)]
      linarith
    linarith
  have haB : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hak u hu⟩
  have hbB : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hbk u hu⟩
  set c : ℝ≥0∞ := ENNReal.ofReal ((1 - (2 * R * k) ^ 2)⁻¹) ^ 2 with hc
  set X : ℝ≥0∞ := c * ENNReal.ofReal (max C 0 * π) * ∫⁻ s in E, ENNReal.ofReal (rhoU s) with hX
  have hXfin : X ≠ ∞ := by
    rw [hX]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by rw [hc]; finiteness) ENNReal.ofReal_ne_top) hEA.ne
  refine ⟨R, hR0, hRk, max CA 0 * max CB 0 * X.toReal, fun Q hQ => ?_⟩
  have hQ4 : Q ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R4 :=
    closedBall_subset_closedBall (min_le_left _ _) hQ
  obtain ⟨hK, hs, -, hker⟩ := s7g_r1_W hk haB hbB (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb)
    hR0.le hRk hW hQ
  have hk0 : 0 ≤ 2 * R * k := by positivity
  have hinner : ∀ s ∈ upperHalf, ∫⁻ τ in upperHalf, ‖dz (W Q) τ * dz (W Q) (conj s) /
      (W Q τ - W Q (conj s)) ^ 2‖ₑ ^ 2 ≤ c * ENNReal.ofReal (max C 0 * π * rhoU s) := by
    intro s hs'
    refine (s8g_c_inner (C := max C 0) hK hs hk0 hRk hker (fun z hz => ?_) hs').trans ?_
    · refine (hD4 a φa b φb ha hb hak hbk W hW Q hQ4 z hz).2.trans ?_
      have := sq_nonneg (infDist (W Q (conj z)) (W Q '' {u : ℂ | u.im < 0})ᶜ)
      have h2 : 0 ≤ rhoU z := by unfold rhoU; positivity
      have h3 : C ≤ max C 0 := le_max_left _ _
      nlinarith [mul_nonneg this h2]
    · gcongr
  have hCA := le_max_right CA 0
  have hCB := le_max_right CB 0
  have hAB : ∀ s ∈ E, ∀ t ∈ S, ‖A s * (conj (B t) * (dz (W Q) t * dz (W Q) (conj s) /
      (W Q t - W Q (conj s)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal (max CA 0 * max CB 0) *
        ‖dz (W Q) t * dz (W Q) (conj s) / (W Q t - W Q (conj s)) ^ 2‖ₑ ^ 2 := by
    intro s hs t ht
    rw [enorm_mul, enorm_mul, enorm_pow, ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    gcongr
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hA s hs).trans (le_max_left _ _))
    · rw [← ofReal_norm, Complex.norm_conj]
      exact ENNReal.ofReal_le_ofReal ((hB t ht).trans (le_max_left _ _))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans ?_
  calc ∫⁻ s in E, ∫⁻ t in S, ‖A (s, t).1 * (conj (B (s, t).2) * (dz (W Q) (s, t).2 * dz (W Q) (conj (s, t).1) /
        (W Q (s, t).2 - W Q (conj (s, t).1)) ^ 2) ^ 2)‖ₑ
      ≤ ∫⁻ s in E, ENNReal.ofReal (max CA 0 * max CB 0) * (c * ENNReal.ofReal (max C 0 * π * rhoU s)) := by
        refine lintegral_mono_ae ((ae_restrict_mem hEm).mono fun s hs => ?_)
        calc ∫⁻ t in S, ‖A (s, t).1 * (conj (B (s, t).2) * (dz (W Q) (s, t).2 * dz (W Q) (conj (s, t).1) /
              (W Q (s, t).2 - W Q (conj (s, t).1)) ^ 2) ^ 2)‖ₑ
            ≤ ∫⁻ t in S, ENNReal.ofReal (max CA 0 * max CB 0) *
                ‖dz (W Q) t * dz (W Q) (conj s) / (W Q t - W Q (conj s)) ^ 2‖ₑ ^ 2 :=
              lintegral_mono_ae ((ae_restrict_mem hSm).mono fun t ht => hAB s hs t ht)
          _ = ENNReal.ofReal (max CA 0 * max CB 0) *
                ∫⁻ t in S, ‖dz (W Q) t * dz (W Q) (conj s) / (W Q t - W Q (conj s)) ^ 2‖ₑ ^ 2 :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (max CA 0 * max CB 0) * (c * ENNReal.ofReal (max C 0 * π * rhoU s)) := by
              gcongr
              exact (lintegral_mono_set hSU).trans (hinner s (hEU hs))
    _ = ENNReal.ofReal (max CA 0 * max CB 0) * X := by
        have hcfin : c ≠ ∞ := by rw [hc]; finiteness
        rw [hX, mul_assoc c, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ hcfin,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_mul (p := max C 0 * π) (q := rhoU s) (by positivity)]
    _ = ENNReal.ofReal (max CA 0 * max CB 0 * X.toReal) := by
        rw [ENNReal.ofReal_mul (p := max CA 0 * max CB 0) (q := X.toReal) (by positivity),
          ENNReal.ofReal_toReal hXfin]

/-- (two-set copy of `s7g_c79_dir`, outer variable in `E`, inner in `S`) Holomorphy of the line-2 double integral of the 4-parameter family along a complex line `t ↦ Q₀ + t e`. -/
theorem s8g_c_dir {a b φa φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hσ : σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * b u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u)) else 0))
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun Q => normalizedSolution (σ Q))
    {E S : Set ℂ} (hEm : MeasurableSet E) (hEU : E ⊆ upperHalf) (hSm : MeasurableSet S) (hSU : S ⊆ upperHalf)
    {A B : ℂ → ℂ} (hAc : ContinuousOn A E) (hBc : ContinuousOn B S) {Q₀ e : (ℂ × ℂ) × (ℂ × ℂ)} {c : ℂ} {ρ : ℝ}
    (hρ : ∀ t ∈ closedBall c ρ, ‖Q₀ + t • e‖ * (2 * k) < 1) {M : ℝ}
    (hM : ∀ t ∈ closedBall c ρ, ∫⁻ x in E ×ˢ S, ‖A x.1 * (conj (B x.2) *
      (dz (W (Q₀ + t • e)) x.2 * dz (W (Q₀ + t • e)) (conj x.1) /
        (W (Q₀ + t • e) x.2 - W (Q₀ + t • e) (conj x.1)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal M) :
    ContinuousOn (fun q : ℂ × (ℂ × ℂ) => A q.2.1 * (conj (B q.2.2) *
      (dz (W (Q₀ + q.1 • e)) q.2.2 * dz (W (Q₀ + q.1 • e)) (conj q.2.1) /
        (W (Q₀ + q.1 • e) q.2.2 - W (Q₀ + q.1 • e) (conj q.2.1)) ^ 2) ^ 2)) (closedBall c ρ ×ˢ (E ×ˢ S)) ∧
    DifferentiableOn ℂ (fun t => ∫ x in E ×ˢ S, A x.1 * (conj (B x.2) *
      (dz (W (Q₀ + t • e)) x.2 * dz (W (Q₀ + t • e)) (conj x.1) /
        (W (Q₀ + t • e) x.2 - W (Q₀ + t • e) (conj x.1)) ^ 2) ^ 2)) (ball c ρ) := by
  obtain ⟨hσB, hσs, hσl⟩ := s7g_c79_sig ha hb hk hak hbk hσ
  have hWt : ∀ t : ℂ, W (Q₀ + t • e) = normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u := by
    intro t
    rw [hW]
    show normalizedSolution (σ (Q₀ + t • e)) = _
    rw [hσl, one_smul, add_comm]
  simp only [hWt] at hM ⊢
  set V : Set (ℂ × ℂ) := {P | ‖P.1 • e + P.2 • Q₀‖ * (2 * k) < 1} with hVdef
  have hV : IsOpen V :=
    isOpen_lt (((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)).norm.mul
      continuous_const) continuous_const
  have hVk : ∀ P ∈ V, ∃ k' < 1, IsBeltramiCoeff (fun u => P.1 * σ e u + P.2 * σ Q₀ u) univ k' := by
    intro P hP
    refine ⟨_, hP, ?_⟩
    rw [hσl]
    exact hσB _
  obtain ⟨hWc, hDc, hinj, hhol⟩ := s7g_c79_slice (hσB e) (hσB Q₀) (hσs e) (hσs Q₀) hV hVk
  have hVt : ∀ t ∈ closedBall c ρ, ((t, (1 : ℂ)) : ℂ × ℂ) ∈ V := by
    intro t ht
    show ‖t • e + (1 : ℂ) • Q₀‖ * (2 * k) < 1
    rw [one_smul, add_comm]
    exact hρ t ht
  have him1 : ∀ x ∈ E ×ˢ S, x.2.im ≠ 0 := fun x hx => (hSU hx.2 : 0 < x.2.im).ne'
  have him2 : ∀ x ∈ E ×ˢ S, (conj x.1).im ≠ 0 := fun x hx => by
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr (hEU hx.1 : 0 < x.1.im).ne'
  have hne : ∀ t ∈ closedBall c ρ, ∀ x ∈ E ×ˢ S,
      ((normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u) x.2 -
        (normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u) (conj x.1)) ^ 2 ≠ 0 := by
    intro t ht x hx
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have h' := hinj (t, 1) (hVt t ht) h
    have h2 : x.2.im = (conj x.1).im := by rw [h']
    rw [Complex.conj_im] at h2
    have h3 : 0 < x.1.im := hEU hx.1
    have h4 : 0 < x.2.im := hSU hx.2
    linarith
  have hT := hEm.prod hSm
  have hcont : ContinuousOn (fun q : ℂ × (ℂ × ℂ) => A q.2.1 * (conj (B q.2.2) *
      (dz (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) q.2.2 *
        dz (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) (conj q.2.1) /
        ((normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) q.2.2 -
          (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) (conj q.2.1)) ^ 2) ^ 2))
      (closedBall c ρ ×ˢ (E ×ˢ S)) := by
    have m2 : MapsTo (fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), q.2.2)) (closedBall c ρ ×ˢ (E ×ˢ S))
        (V ×ˢ {u : ℂ | u.im ≠ 0}) := fun q hq => ⟨hVt q.1 hq.1, him1 q.2 hq.2⟩
    have m1 : MapsTo (fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), conj q.2.1)) (closedBall c ρ ×ˢ (E ×ˢ S))
        (V ×ˢ {u : ℂ | u.im ≠ 0}) := fun q hq => ⟨hVt q.1 hq.1, him2 q.2 hq.2⟩
    have c2 : Continuous fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), q.2.2) := by fun_prop
    have c1 : Continuous fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), conj q.2.1) := by fun_prop
    have hW2 := hWc.comp c2.continuousOn m2
    have hW1 := hWc.comp c1.continuousOn m1
    have hD2 := hDc.comp c2.continuousOn m2
    have hD1 := hDc.comp c1.continuousOn m1
    have hA := hAc.comp continuous_snd.fst.continuousOn (fun q (hq : q ∈ closedBall c ρ ×ˢ (E ×ˢ S)) => hq.2.1)
    have hB := Complex.continuous_conj.comp_continuousOn
      (hBc.comp continuous_snd.snd.continuousOn (fun q (hq : q ∈ closedBall c ρ ×ˢ (E ×ˢ S)) => hq.2.2))
    exact hA.mul (hB.mul (((hD2.mul hD1).div ((hW2.sub hW1).pow 2) fun q hq => hne q.1 hq.1 q.2 hq.2).pow 2))
  refine ⟨hcont, s7g_f2_param (m := volume) hT hcont ?_ hM⟩
  intro x hx t ht
  have hP := hVt t (ball_subset_closedBall ht)
  obtain ⟨h1, h2⟩ := hhol (t, 1) hP x.2 (him1 x hx)
  obtain ⟨h3, h4⟩ := hhol (t, 1) hP (conj x.1) (him2 x hx)
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).mul (((h2.mul h4).div ((h1.sub h3).pow 2)
    (hne t (ball_subset_closedBall ht) x hx)).pow 2))).differentiableWithinAt

/-- Cayley transport `𝔻 → 𝕌` of a harmonic Beltrami differential: `a(u) = κ(S u) \overline{S'(u)}/S'(u)` is harmonic on
`𝕌` with `φ_a(u) = -2 S'(u)² φ_κ(S u)`, and bounded by the bound of `κ`. -/
theorem s8g_c_kD {κ : ℂ → ℂ} (hκ : IsHarmonicD κ) {Cκ : ℝ} (hCκ : ∀ z ∈ unitDisc, ‖κ z‖ ≤ Cκ) :
    ∃ φa : ℂ → ℂ, IsHarmonicU (fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) φa ∧
      ∀ u ∈ upperHalf, ‖κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))‖ ≤ Cκ := by
  obtain ⟨φ, hφ, -, hr⟩ := hκ
  have hcm : ∀ u ∈ upperHalf, cayley u ∈ unitDisc := fun u hu =>
    isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have hd0 : ∀ u ∈ upperHalf, 2 * I / (u + I) ^ 2 ≠ 0 := fun u hu =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
  have hnorm : ∀ u ∈ upperHalf,
      ‖κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))‖ = ‖κ (cayley u)‖ := by
    intro u hu
    rw [norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (hd0 u hu)), mul_one]
  have hrep : ∀ u ∈ upperHalf, κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) =
      (u - conj u) ^ 2 / 2 * conj (-2 * (2 * I / (u + I) ^ 2) ^ 2 * φ (cayley u)) := by
    intro u hu
    rw [hr _ (hcm u hu), s8g_d4_bf hu]
    have hd := hd0 u hu
    have hdc : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hd
    generalize 2 * I / (u + I) ^ 2 = d at hd hdc ⊢
    simp only [map_mul, map_neg, map_pow, map_ofNat]
    field_simp
  refine ⟨fun u => -2 * (2 * I / (u + I) ^ 2) ^ 2 * φ (cayley u), ⟨?_, ⟨Cκ / 2, fun z hz => ?_⟩, hrep⟩,
    fun u hu => by rw [hnorm u hu]; exact hCκ _ (hcm u hu)⟩
  · intro u hu
    have h1 : DifferentiableAt ℂ cayley u := (rhoU_hasDerivAt_cayley hu).differentiableAt
    have h2 : DifferentiableAt ℂ φ (cayley u) := hφ.differentiableAt (isOpen_ball.mem_nhds (hcm u hu))
    have h3 : DifferentiableAt ℂ (fun u : ℂ => 2 * I / (u + I) ^ 2) u :=
      (differentiableAt_const _).div ((differentiableAt_id.add_const I).pow 2) (pow_ne_zero _ (cayley_den_ne_zero hu))
    exact (((h3.pow 2).const_mul _).mul (h2.comp u h1)).differentiableWithinAt
  · have h := hrep z hz
    have hn := hnorm z hz
    rw [h] at hn
    have hz0 : 0 < z.im := hz
    rw [norm_mul, Complex.norm_conj, Complex.sub_conj] at hn
    have e1 : ‖(((2 * z.im : ℝ) : ℂ) * I) ^ 2 / 2‖ = 2 * z.im ^ 2 := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      norm_num
      ring
    rw [e1] at hn
    have hb := hCκ _ (hcm z hz)
    beta_reduce
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz0]
    nlinarith [norm_nonneg (-2 * (2 * I / (z + I) ^ 2) ^ 2 * φ (cayley z))]

/-- `∫⁻_E ρ_𝕌 < ∞` for the Cayley preimage `E` of the fundamental domain. -/
theorem s8g_cayE_area {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    ∫⁻ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, ENNReal.ofReal (rhoU s) < ∞ := by
  obtain ⟨hEm, hEU, hEimg⟩ := s8g_cayE hΓ.1
  have hi : InjOn cayley (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) := isConformalOnto_cayley.2.1.mono hEU
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hEm
    (fun z hz => ((rhoU_hasDerivAt_cayley (hEU hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hi
    (fun w => ENNReal.ofReal (rho w))
  rw [hEimg] at h
  have key : (∫⁻ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, ENNReal.ofReal (rhoU s)) =
      ∫⁻ w in fundDomainOn Γ unitDisc, ENNReal.ofReal (rho w) := by
    rw [h]
    refine setLIntegral_congr_fun hEm fun x hx => ?_
    simp only [det_restrictScalars_toSpanSingleton]
    rw [abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm,
      ← (rhoU_hasDerivAt_cayley (hEU hx)).deriv, rhoU_cayley_pullback (hEU hx)]
  rw [key]
  exact s8w_area_fin hΓ

/-- STUB CORE. `gGamma Γ μ ν (p₁ κ + p₂ l) = Φ(p̄, p)` with `Φ` separately holomorphic and bounded near `0`. -/
theorem s8g_core {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ l : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hl : IsHarmonicD l) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) (hlΓ : IsGammaInvD Γ l) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∃ Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ,
      (∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1 ∧
        DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2 ∧
        DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1 ∧
        DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2) ∧
      (∃ M : ℝ, ∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ‖Φ p‖ ≤ M) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ R0 ∧ ∀ p : ℂ × ℂ, ‖p‖ < r →
        gGamma Γ μ ν (fun z => p.1 * κ z + p.2 * l z) = Φ ((conj p.1, conj p.2), p) := by
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cl, hCl⟩ := harmonicD_bound hl
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hCκ0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ 0 h0D)
  have hCl0 : 0 ≤ Cl := (norm_nonneg _).trans (hCl 0 h0D)
  -- the phase `\overline{S'}/S'` and the transported data
  have hd0 : ∀ u ∈ upperHalf, 2 * I / (u + I) ^ 2 ≠ 0 := fun u hu =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
  have hph1 : ∀ u ∈ upperHalf, ‖conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)‖ = 1 := fun u hu => by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (hd0 u hu))]
  have hphc : ContinuousOn (fun u => conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) upperHalf := by
    have hc : ContinuousOn (fun u : ℂ => 2 * I / (u + I) ^ 2) upperHalf :=
      continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
        fun u hu => pow_ne_zero _ (cayley_den_ne_zero hu)
    exact (Complex.continuous_conj.comp_continuousOn hc).div hc hd0
  have hcayc : ContinuousOn cayley upperHalf := fun u hu =>
    (rhoU_hasDerivAt_cayley hu).continuousAt.continuousWithinAt
  have hcm : MapsTo cayley upperHalf unitDisc := fun u hu => isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have htr : ∀ {f : ℂ → ℂ}, IsHarmonicD f →
      ContinuousOn (fun u => f (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) upperHalf :=
    fun hf => ((harmonicD_continuousOn hf).comp hcayc hcm).mul hphc
  obtain ⟨φa, ha, hak0⟩ := s8g_c_kD hκ hCκ
  obtain ⟨φb, hb, hbk0⟩ := s8g_c_kD hl hCl
  generalize hadef : (fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) = a at ha hak0
  generalize hbdef : (fun u => l (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) = b at hb hbk0
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = max Cκ Cl := ⟨_, rfl⟩
  have hk : 0 ≤ k := by rw [hkdef]; exact le_max_of_le_left hCκ0
  have hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k := fun u hu => by
    rw [hkdef, ← hadef]
    exact (hak0 u hu).trans (le_max_left _ _)
  have hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k := fun u hu => by
    rw [hkdef, ← hbdef]
    exact (hbk0 u hu).trans (le_max_right _ _)
  obtain ⟨hEm, hEU, -⟩ := s8g_cayE hΓ.1
  have hEA := s8g_cayE_area hΓ
  set E := upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc with hEdef
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℂ, A = fun s =>
      conj (ν (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ → ℂ, B = fun s =>
      conj (μ (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) := ⟨_, rfl⟩
  have hAc : ContinuousOn A E := by
    rw [hAdef]
    exact (Complex.continuous_conj.comp_continuousOn (htr hν)).mono hEU
  have hBc : ContinuousOn B upperHalf := by
    rw [hBdef]
    exact Complex.continuous_conj.comp_continuousOn (htr hμ)
  have hAb : ∀ s ∈ E, ‖A s‖ ≤ Cν := fun s hs => by
    rw [hAdef]
    show ‖conj (ν (cayley s) * _)‖ ≤ Cν
    rw [Complex.norm_conj, norm_mul, hph1 s (hEU hs), mul_one]
    exact hCν _ (hcm (hEU hs))
  have hBb : ∀ s ∈ upperHalf, ‖B s‖ ≤ Cμ := fun s hs => by
    rw [hBdef]
    show ‖conj (μ (cayley s) * _)‖ ≤ Cμ
    rw [Complex.norm_conj, norm_mul, hph1 s hs, mul_one]
    exact hCμ _ (hcm hs)
  -- the 4-parameter family
  obtain ⟨σ, hσ⟩ : ∃ σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * b u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = fun Q => normalizedSolution (σ Q) := ⟨_, rfl⟩
  have hW' : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0) := by
    rw [hW, hσ]
  obtain ⟨R0, hR0p, hR0k2, M, hM⟩ := s8g_c_L1 ha hb hk hak hbk hW' hEm hEU hU subset_rfl hEA hAb hBb
  obtain ⟨F, hF⟩ : ∃ F : (ℂ × ℂ) × (ℂ × ℂ) → ℂ × ℂ → ℂ, F = fun P x => A x.1 * (conj (B x.2) *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  have hM' : ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ∫⁻ x in E ×ˢ upperHalf, ‖F P x‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    rw [hF]
    exact hM P hP
  have hsw : ∀ P : (ℂ × ℂ) × (ℂ × ℂ), ‖((P.2, P.1) : (ℂ × ℂ) × (ℂ × ℂ))‖ = ‖P‖ := fun P => by
    simp only [Prod.norm_def, max_comm]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ, Φ = fun Q =>
      (12 / π : ℂ) * ∫ x in E ×ˢ upperHalf, F (Q.2, Q.1) x := ⟨_, rfl⟩
  have hTm : MeasurableSet (E ×ˢ upperHalf) := hEm.prod hU
  have hρk : ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ‖P‖ * (2 * k) < 1 := by
    intro P hP
    have h := mem_closedBall_zero_iff.1 hP
    calc ‖P‖ * (2 * k) ≤ R0 * (2 * k) := mul_le_mul_of_nonneg_right h (by positivity)
      _ < 1 := by linarith
  -- separate holomorphy along complex lines
  have hline : ∀ (L : ℂ → (ℂ × ℂ) × (ℂ × ℂ)) (Q₀ e : (ℂ × ℂ) × (ℂ × ℂ)), (∀ t, L t = Q₀ + t • e) →
      ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → (∀ t ∈ closedBall c ρ, ‖L t‖ ≤ R0) → DifferentiableAt ℂ (fun t => Φ (L t)) c := by
    intro L Q₀ e hL c ρ hρ hc
    have hmem : ∀ t ∈ closedBall c ρ, ((Q₀.2, Q₀.1) : (ℂ × ℂ) × (ℂ × ℂ)) + t • (e.2, e.1) ∈
        closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := fun t ht => by
      have h := hc t ht
      rw [hL] at h
      refine mem_closedBall_zero_iff.2 ?_
      have e1 : ((Q₀.2, Q₀.1) : (ℂ × ℂ) × (ℂ × ℂ)) + t • (e.2, e.1) = ((Q₀ + t • e).2, (Q₀ + t • e).1) := by
        ext <;> simp
      rw [e1, hsw]
      exact h
    obtain ⟨-, hd⟩ := s8g_c_dir ha hb hk hak hbk hσ hW hEm hEU hU subset_rfl hAc hBc
      (Q₀ := (Q₀.2, Q₀.1)) (e := (e.2, e.1)) (c := c) (ρ := ρ)
      (fun t ht => hρk _ (hmem t ht)) (M := M) (fun t ht => hM _ (hmem t ht))
    have hd' := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
    have e1 : (fun t => Φ (L t)) = fun t => (12 / π : ℂ) *
        ∫ x in E ×ˢ upperHalf, F (((Q₀.2, Q₀.1) : (ℂ × ℂ) × (ℂ × ℂ)) + t • (e.2, e.1)) x := by
      funext t
      rw [hΦ, hL]
      congr 3
    rw [e1, hF]
    exact (differentiableAt_const _).mul hd'
  have hRp : ∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ∀ x : ℂ, ‖x‖ ≤ ‖p‖ →
      ∀ t ∈ closedBall x ((R0 - ‖p‖) / 2), ‖t‖ ≤ R0 := by
    intro p hp x hx t ht
    have hp' := mem_ball_zero_iff.1 hp
    have h1 : ‖t‖ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by
      have := mem_closedBall.1 ht
      rw [dist_eq_norm] at this
      calc ‖t‖ = ‖x + (t - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖t - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by linarith
    linarith
  refine ⟨R0, hR0p, Φ, fun p hp => ?_, ⟨‖(12 / π : ℂ)‖ * max M 0, fun p hp => ?_⟩, ?_⟩
  · -- the four coordinate slices
    have hp' : ‖p‖ < R0 := mem_ball_zero_iff.1 hp
    have hρ : 0 < (R0 - ‖p‖) / 2 := by linarith
    have hpR : ‖p‖ ≤ R0 := hp'.le
    have h11 : ‖p.1.1‖ ≤ ‖p‖ := (norm_fst_le p.1).trans (norm_fst_le p)
    have h12 : ‖p.1.2‖ ≤ ‖p‖ := (norm_snd_le p.1).trans (norm_fst_le p)
    have h21 : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
    have h22 : ‖p.2.2‖ ≤ ‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
    have h1' : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have h2' : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine hline (fun z => ((z, p.1.2), p.2)) ((0, p.1.2), p.2) ((1, 0), (0, 0)) (fun t => by ext <;> simp)
        p.1.1 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨hRp p hp _ h11 t ht, h12.trans hpR⟩, h2'.trans hpR⟩
    · refine hline (fun z => ((p.1.1, z), p.2)) ((p.1.1, 0), p.2) ((0, 1), (0, 0)) (fun t => by ext <;> simp)
        p.1.2 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨h11.trans hpR, hRp p hp _ h12 t ht⟩, h2'.trans hpR⟩
    · refine hline (fun z => (p.1, (z, p.2.2))) (p.1, (0, p.2.2)) ((0, 0), (1, 0)) (fun t => by ext <;> simp)
        p.2.1 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨h1'.trans hpR, norm_prod_le_iff.2 ⟨hRp p hp _ h21 t ht, h22.trans hpR⟩⟩
    · refine hline (fun z => (p.1, (p.2.1, z))) (p.1, (p.2.1, 0)) ((0, 0), (0, 1)) (fun t => by ext <;> simp)
        p.2.2 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨h1'.trans hpR, norm_prod_le_iff.2 ⟨h21.trans hpR, hRp p hp _ h22 t ht⟩⟩
  · -- the bound
    have hp2 : ((p.2, p.1) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
      rw [mem_closedBall_zero_iff, hsw]
      exact (mem_ball_zero_iff.1 hp).le
    have h1 := (enorm_integral_le_lintegral_enorm (μ := volume.restrict (E ×ˢ upperHalf)) (F (p.2, p.1))).trans
      (hM' _ hp2)
    have h2 : ENNReal.ofReal ‖∫ x in E ×ˢ upperHalf, F (p.2, p.1) x‖ ≤ ENNReal.ofReal (max M 0) := by
      rw [ofReal_norm]
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [hΦ]
    show ‖(12 / π : ℂ) * ∫ x in E ×ˢ upperHalf, F (p.2, p.1) x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2) (norm_nonneg _)
  -- the representation on a small ball
  obtain ⟨δ₀, hδ0, hδ1, C3, hC3⟩ := s8w_density
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (δ₀ / (Cκ + Cl + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  refine ⟨r, hr0, hrR, fun p hp => ?_⟩
  have hpR : ‖p‖ < R0 := lt_of_lt_of_le hp hrR
  have hpδ : ‖p‖ * (Cκ + Cl + 1) < δ₀ := by
    have h := lt_of_lt_of_le hp (show r ≤ δ₀ / (Cκ + Cl + 1) by rw [hr]; exact min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at h
  have hn1 := norm_fst_le p
  have hn2 := norm_snd_le p
  have hnp := norm_nonneg p
  have hκp : IsHarmonicD (fun z => p.1 * κ z + p.2 * l z) := by
    refine (congrArg IsHarmonicD ?_).mp (s8g_harm_lin (s8g_harm_lin (s8g_harm_lin hκ hκ (-1)) hκ p.1) hl p.2)
    funext z
    ring
  have hκpΓ : IsGammaInvD Γ (fun z => p.1 * κ z + p.2 * l z) := by
    refine (congrArg (IsGammaInvD Γ) ?_).mp (s8g_inv_lin (s8g_inv_lin (s8g_inv_lin hκΓ hκΓ (-1)) hκΓ p.1) hlΓ p.2)
    funext z
    ring
  have hbd : ∀ z ∈ unitDisc, ‖p.1 * κ z + p.2 * l z‖ ≤ ‖p‖ * (Cκ + Cl) := fun z hz => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖p.1‖ * ‖κ z‖ ≤ ‖p‖ * Cκ := mul_le_mul hn1 (hCκ z hz) (norm_nonneg _) hnp
    have h2 : ‖p.2‖ * ‖l z‖ ≤ ‖p‖ * Cl := mul_le_mul hn2 (hCl z hz) (norm_nonneg _) hnp
    linarith
  have hkδ : ‖p‖ * (Cκ + Cl) < δ₀ := by nlinarith
  have hC := hC3 _ hκp fun z hz => lt_of_le_of_lt (hbd z hz) hkδ
  obtain ⟨Pst, hPst⟩ : ∃ Pst : (ℂ × ℂ) × (ℂ × ℂ), Pst = ((p.1, p.2), (conj p.1, conj p.2)) := ⟨_, rfl⟩
  have hPmem : Pst ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
    rw [hPst]
    refine mem_closedBall_zero_iff.2 (norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩,
      norm_prod_le_iff.2 ⟨?_, ?_⟩⟩)
    · linarith
    · linarith
    · rw [Complex.norm_conj]
      linarith
    · rw [Complex.norm_conj]
      linarith
  have hm : ∀ u ∈ upperHalf, p.1 * a u + p.2 * b u =
      (p.1 * κ (cayley u) + p.2 * l (cayley u)) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
    intro u _
    rw [← hadef, ← hbdef]
    ring
  have hrep := s8g_c_line2U hΓ hμ hν hμΓ hνΓ hκp hκpΓ (lt_trans hkδ hδ1) hbd hC ha hb hk hak hbk hW' hR0p.le
    hR0k2 (q := p) (hPst ▸ hPmem) hm
  rw [← hPst] at hrep
  obtain ⟨hcP, -⟩ := s8g_c_dir ha hb hk hak hbk hσ hW hEm hEU hU subset_rfl hAc hBc (Q₀ := Pst)
    (e := 0) (c := 0) (ρ := 1) (fun t _ => by rw [smul_zero, add_zero]; exact hρk _ hPmem) (M := M)
    (fun t _ => by rw [smul_zero, add_zero]; exact hM _ hPmem)
  simp only [smul_zero, add_zero] at hcP
  have hcF : ContinuousOn (F Pst) (E ×ˢ upperHalf) := by
    have h := hcP.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => (⟨mem_closedBall_self zero_le_one, hx⟩ : ((0 : ℂ), x) ∈ closedBall (0 : ℂ) 1 ×ˢ (E ×ˢ upperHalf)))
    rw [hF]
    exact h
  have hint : Integrable (F Pst) ((volume.restrict E).prod (volume.restrict upperHalf)) := by
    rw [Measure.prod_restrict]
    exact ⟨hcF.aestronglyMeasurable hTm, lt_of_le_of_lt (hM' _ hPmem) ENNReal.ofReal_lt_top⟩
  have hprod := integral_prod (F Pst) hint
  have e2 : (∫ x in E ×ˢ upperHalf, F Pst x) = ∫ s in E, ∫ t in upperHalf, F Pst (s, t) := by
    rw [← hprod, Measure.prod_restrict]
    rfl
  have ePst : ((((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ)).2, (((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ)).1) =
      Pst := by
    rw [hPst]
  rw [hΦ]
  show _ = (12 / π : ℂ) * ∫ x in E ×ˢ upperHalf, F ((((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ)).2,
    (((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ)).1) x
  rw [ePst, hrep, e2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [hF, hAdef, hBdef]
  simp only [Complex.conj_conj]

/-- FV, pointwise: the holomorphic (upper-slot) derivative of the inner line-2 integrand integrates to `0` over `𝕌`,
since `∂_ε Q_Y(εa)|₀ = 0` (`p71_prop_7_1U`) and `ρ ∂_ε Q = (12/π) ∂_ε J` (`s71_Q_quot`). -/
theorem s8g_fv_inner {Y φY a φa : ℂ → ℂ} (hY : IsHarmonicU Y φY) (ha : IsHarmonicU a φa) {k R : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hR : 0 < R) (hRk : R * k < 1) {W : ℂ × ℂ → ℂ → ℂ}
    (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then a u else 0) + P.2 * (if u.im < 0 then conj (a (conj u)) else 0))
    {s : ℂ} (hs : s ∈ upperHalf) :
    ∫ τ in upperHalf, deriv (fun z => Y τ * (dz (W (z, 0)) τ * dz (W (z, 0)) (conj s) /
      (W (z, 0) τ - W (z, 0) (conj s)) ^ 2) ^ 2) 0 = 0 := by
  have hU := measurableSet_upperHalf_aux
  have hmB : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hak u hu⟩
  have hms := wr_isHarmonicU_contDiffOn ha
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ → ℂ, Ψ = fun P u =>
      Y u * (dz (W P) u * dz (W P) (conj s) / (W P u - W P (conj s)) ^ 2) ^ 2 := ⟨_, rfl⟩
  have hUo : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have hpt : ∀ τ ∈ upperHalf, deriv (fun z => Y τ * (dz (W (z, 0)) τ * dz (W (z, 0)) (conj s) /
      (W (z, 0) τ - W (z, 0) (conj s)) ^ 2) ^ 2) 0 =
      dz (fun e => Y τ * kernelKbar (fun y => e * a y) τ s ^ 2) 0 := by
    intro τ hτ
    obtain ⟨hh1, hh2⟩ := s71_b2_holo (μ := Y) hk hmB hms hs hRk hW hΨ hτ
    have hcΨ := s71_b2_cont (μ := Y) hk hmB hms (harmonicU_continuousOn hY) hs hRk hW hΨ
    obtain ⟨Bd, hBd⟩ :=
      ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
        (hcΨ.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun P hP => (⟨hP, hτ⟩ : (P, τ) ∈ (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ upperHalf)))
    have k1 : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ (fun z => Ψ (z, p.2) τ) p.1 :=
      fun p hp => (hh1 p.2 (ball_subset_closedBall hp.2)).differentiableAt (isOpen_ball.mem_nhds hp.1)
    have k2 : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ (fun w => Ψ (p.1, w) τ) p.2 :=
      fun p hp => (hh2 p.1 (ball_subset_closedBall hp.1)).differentiableAt (isOpen_ball.mem_nhds hp.2)
    have kb : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, ∃ ρ > 0, ∃ M' : ℝ, ∀ q ∈ ball p ρ, ‖Ψ q τ‖ ≤ M' := by
      intro p hp
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hUo p hp
      exact ⟨ρ, hρ, Bd, fun q hq =>
        hBd q ⟨ball_subset_closedBall (hsub hq).1, ball_subset_closedBall (hsub hq).2⟩⟩
    have hfd := s7g_h_fderiv (Φ := fun P => Ψ P τ) hUo k1 k2 kb (p := ((0 : ℂ), (0 : ℂ)))
      ⟨mem_ball_self hR, mem_ball_self hR⟩
    have hsw : DifferentiableAt ℂ (fun P : ℂ × ℂ => Ψ (P.2, P.1) τ) (conj (0 : ℂ), (0 : ℂ)) := by
      rw [map_zero]
      have hswap : DifferentiableAt ℂ (fun P : ℂ × ℂ => (P.2, P.1)) ((0 : ℂ), (0 : ℂ)) :=
        differentiableAt_snd.prodMk differentiableAt_fst
      exact DifferentiableAt.comp (g := fun P => Ψ P τ) ((0 : ℂ), (0 : ℂ)) (by simpa using hfd.differentiableAt) hswap
    have hpar := s7g_dz_partial hsw
    simp only [map_zero] at hpar
    have hev : (fun y => Ψ (y, conj y) τ) =ᶠ[𝓝 (0 : ℂ)] fun e => Y τ * kernelKbar (fun y => e * a y) τ s ^ 2 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / (k + 1) by positivity)] with e he
      have he' : ‖e‖ * k < 1 := by
        rw [mem_ball_zero_iff, lt_div_iff₀ (by positivity)] at he
        nlinarith [norm_nonneg e]
      exact s71_b2_diag hk hmB hW hΨ he' τ
    have hdz : dz (fun y => Ψ (y, conj y) τ) 0 = dz (fun e => Y τ * kernelKbar (fun y => e * a y) τ s ^ 2) 0 := by
      simp only [dz, hev.fderiv_eq]
    have e0 : (fun z => Y τ * (dz (W (z, 0)) τ * dz (W (z, 0)) (conj s) /
        (W (z, 0) τ - W (z, 0) (conj s)) ^ 2) ^ 2) = fun z => Ψ (z, 0) τ := by
      rw [hΨ]
    rw [e0, ← hpar, hdz]
  rw [setIntegral_congr_fun hU hpt, ← (s71_J_deriv hY ha hs).2.1]
  have hq := (s71_Q_quot hY ha hs).1
  rw [(p71_prop_7_1U hY ha hs).2.1] at hq
  have hs0 : s - conj s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith [show 0 < s.im from hs]
  have hr : rhoVar a 0 s ≠ 0 := by
    rw [s71_rho0]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ hs0)
  have hπ : (12 / π : ℂ) ≠ 0 := div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have h := hq.symm
  rw [div_eq_zero_iff, mul_eq_zero] at h
  rcases h with (h | h) | h
  · exact absurd h hπ
  · exact h
  · exact absurd h hr

/-- Unfolding, step 1: `G_𝔻 f(z) = ∑_a ∬_F G(z, a w) f(w) ρ(w)` for a bounded measurable `Γ`-invariant `f`. -/
theorem s8g_unf_L {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} (hfm : Measurable f) {C : ℝ}
    (hfC : ∀ w ∈ unitDisc, ‖f w‖ ≤ C) (hinv : ∀ g ∈ Γ, ∀ w ∈ unitDisc, f (mob g w) = f w)
    {z : ℂ} (hz : z ∈ unitDisc) :
    resolventOp unitDisc f z = ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∫ w in fundDomainOn Γ unitDisc, (resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f w * rho w := by
  have hF := s8w_fundD hΓ
  have hh := resolvent_integrand_integrable_of_bounded (Or.inl rfl) hfm.aestronglyMeasurable hfC hz
  have hsum := fdD_hasSum_integral_unfold hΓ hF
    (h := fun w => (resolventKernel z w : ℂ) * f w * rho w) hh
  have hterm : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      (∫ w in fundDomainOn Γ unitDisc, (‖deriv (a : ℂ → ℂ) w‖ ^ 2) •
        ((resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f ((a : ℂ → ℂ) w) * rho ((a : ℂ → ℂ) w))) =
      ∫ w in fundDomainOn Γ unitDisc, (resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f w * rho w := by
    rintro ⟨_, g, hg, rfl⟩
    refine setIntegral_congr_fun hF.1 fun w hw => ?_
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hF.2.1 hw)
    have hJ := gam_rho_mob_jacobian (hΓ.1 g hg) (fdD_denom_ne (hΓ.1 g hg) hw1)
    show (‖deriv (mob g) w‖ ^ 2) • ((resolventKernel z (mob g w) : ℂ) * f (mob g w) * rho (mob g w)) =
      (resolventKernel z (mob g w) : ℂ) * f w * rho w
    rw [hinv g hg w (hF.2.1 hw), Complex.real_smul, ← hJ]
    push_cast
    ring
  exact ((tsum_congr hterm).symm.trans hsum.tsum_eq).symm

/-- Unfolding, step 2: the series of absolute tile integrals is finite. -/
theorem s8g_unf_fin {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} {C : ℝ}
    (hfC : ∀ w ∈ unitDisc, ‖f w‖ ≤ C) {z : ℂ} (hz : z ∈ unitDisc) :
    ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∫⁻ w in fundDomainOn Γ unitDisc, ‖(resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f w * rho w‖ₑ ≠ ⊤ := by
  have hF := s8w_fundD hΓ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hfC 0 (mem_ball_self one_pos))
  have hne : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ∀ᵐ w ∂(volume.restrict (fundDomainOn Γ unitDisc)), (a : ℂ → ℂ) w ≠ z := by
    rintro ⟨_, g, hg, rfl⟩
    have hs : ∀ᵐ w : ℂ ∂volume, w ≠ mob g⁻¹ z := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem hF.1, ae_restrict_of_ae hs] with w hw hw2 heq
    apply hw2
    have hb := (fd_inv_step g (fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp (hF.2.1 hw)))).2
    change mob g w = z at heq
    rw [heq] at hb
    exact hb.symm
  have hbd : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      (∫⁻ w in fundDomainOn Γ unitDisc, ‖(resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f w * rho w‖ₑ) ≤
      ENNReal.ofReal C * ∫⁻ w in fundDomainOn Γ unitDisc,
        ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) w) * rho w) := by
    intro a
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hF.1, hne a] with w hw hwz
    have hw1 := hF.2.1 hw
    have hK : 0 < resolventKernel z ((a : ℂ → ℂ) w) :=
      RK2 (Ne.symm hwz) (Or.inl ⟨hz, fdD_action_mem hΓ a hw1⟩)
    have hr : 0 ≤ rho w := by unfold rho; positivity
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hK, abs_of_nonneg hr]
    have := hfC w hw1
    nlinarith [mul_nonneg hK.le hr]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbd)
  rw [ENNReal.tsum_mul_left, fdD_sum_tile_kernel_mass hΓ hF hz, mul_one]
  exact ENNReal.ofReal_ne_top

/-- Unfolding of the disk resolvent (term B of DIAG): for a bounded measurable `Γ`-invariant density `f`,
`G_𝔻 f = G_Γ f` on `𝔻`. -/
theorem s8g_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} (hfm : Measurable f) {C : ℝ}
    (hfC : ∀ w ∈ unitDisc, ‖f w‖ ≤ C) (hinv : ∀ g ∈ Γ, ∀ w ∈ unitDisc, f (mob g w) = f w)
    {z : ℂ} (hz : z ∈ unitDisc) :
    resolventOp unitDisc f z = resolventGammaD Γ f z := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hmeas : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), AEStronglyMeasurable
      (fun w => (resolventKernel z ((a : ℂ → ℂ) w) : ℂ) * f w * rho w)
      (volume.restrict (fundDomainOn Γ unitDisc)) := by
    intro a
    have h1 : Measurable (fun w => (resolventKernel z ((a : ℂ → ℂ) w) : ℂ)) :=
      Complex.measurable_ofReal.comp (gam_kernel_comp_measurable _ (gam_action_measurable Γ a) z)
    have h3 : Measurable (fun w => (rho w : ℂ)) := Complex.measurable_ofReal.comp gam_rho_measurable
    exact ((h1.mul hfm).mul h3).aestronglyMeasurable
  rw [s8g_unf_L hΓ hfm hfC hinv hz, ← integral_tsum hmeas (s8g_unf_fin hΓ hfC hz)]
  show _ = ∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * f u * rho u
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), (resolventKernel z ((a : ℂ → ℂ) u) : ℂ) * f u * rho u =
    ((∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), resolventKernel z ((a : ℂ → ℂ) u) : ℝ) : ℂ) * f u * rho u
  rw [Complex.ofReal_tsum, tsum_mul_right, tsum_mul_right]

/-- `ρ ≥ 0` everywhere. -/
theorem s8q_rho_nonneg (z : ℂ) : 0 ≤ rho z := by
  unfold rho
  positivity

/-- Symmetry of `G_Γ` on `𝔻`: `G_Γ(z, u) = G_Γ(u, z)`. -/
theorem s8q_K_symm {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z u : ℂ} (hz : z ∈ unitDisc) (hu : u ∈ unitDisc) :
    resolventKernelGamma Γ z u = resolventKernelGamma Γ u z := by
  obtain ⟨e, he⟩ := fdD_inv_perm Γ
  unfold resolventKernelGamma
  rw [← e.tsum_eq (fun b : (fun g : SL2C => mob g) '' (Γ : Set SL2C) => resolventKernel u ((b : ℂ → ℂ) z))]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg, ha, hea⟩ := he a
  rw [ha, hea, (RK1 z (mob g u)).1]
  exact fdD_kernel_act (hΓ.1 g hg) hu hz

/-- The `ℝ≥0∞`-majorant `∑_a G(z, a u)` of `G_Γ` is jointly measurable. -/
theorem s8q_Ke_meas {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    Measurable fun p : ℂ × ℂ => ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2)) := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  refine Measurable.ennreal_tsum (f := fun (a : (fun g : SL2C => mob g) '' (Γ : Set SL2C)) (p : ℂ × ℂ) =>
    ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2))) fun a => ?_
  have hm : Measurable fun p : ℂ × ℂ => (p.1, (a : ℂ → ℂ) p.2) :=
    measurable_fst.prodMk ((gam_action_measurable Γ a).comp measurable_snd)
  have hK : Measurable fun p : ℂ × ℂ => resolventKernel p.1 ((a : ℂ → ℂ) p.2) := by
    have h := measurable_resolventKernel.comp hm
    simpa only [Function.comp_def] using h
  exact ENNReal.measurable_ofReal.comp hK

/-- Off the orbit of `z`, `G_Γ(z, u)` is the real part of its `ℝ≥0∞`-majorant (all terms are positive). -/
theorem s8q_K_eq {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {z u : ℂ} (hu : u ∈ unitDisc)
    (hz : z ∈ unitDisc) (hoff : ∀ g ∈ Γ, mob g u ≠ z) :
    resolventKernelGamma Γ z u = (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u))).toReal := by
  -- termwise-finite `ℝ≥0∞` series: `toReal` commutes with `tsum` (both sides are `0` if the series diverges)
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  unfold resolventKernelGamma
  refine tsum_congr fun a => ?_
  obtain ⟨_, g, hg, rfl⟩ := a
  have hmem : mob g u ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1 g hg) (mem_ball_zero_iff.mp hu))
  exact (ENNReal.toReal_ofReal (RK2 (hoff g hg).symm (Or.inl ⟨hz, hmem⟩)).le).symm

/-- The orbit relation `{(z, u) : ∃ g ∈ Γ, g u = z}` is null in `ℂ × ℂ`. -/
theorem s8q_orbit_null {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    ((volume : Measure ℂ).prod volume) {p : ℂ × ℂ | ∃ g ∈ Γ, mob g p.2 = p.1} = 0 := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hsub : {p : ℂ × ℂ | ∃ g ∈ Γ, mob g p.2 = p.1} ⊆
      ⋃ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), {p : ℂ × ℂ | (a : ℂ → ℂ) p.2 = p.1} := by
    rintro p ⟨g, hg, hp⟩
    exact mem_iUnion.mpr ⟨⟨mob g, g, hg, rfl⟩, hp⟩
  refine measure_mono_null hsub (measure_iUnion_null fun a => ?_)
  have hmS : MeasurableSet {p : ℂ × ℂ | (a : ℂ → ℂ) p.2 = p.1} :=
    measurableSet_eq_fun ((gam_action_measurable Γ a).comp measurable_snd) measurable_fst
  rw [Measure.prod_apply_symm hmS]
  have hs : ∀ y : ℂ, (fun x : ℂ => (x, y)) ⁻¹' {p : ℂ × ℂ | (a : ℂ → ℂ) p.2 = p.1} = {(a : ℂ → ℂ) y} := by
    intro y
    ext x
    simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
    exact eq_comm
  simp only [hs, measure_singleton, lintegral_const, zero_mul]

/-- `∬_{F × F} ∑_a G(z, a u) ρ(z) ρ(u) < ∞` (RK4 unfolded, finite area). -/
theorem s8q_K_lint {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    ∫⁻ p, (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2))) *
          (ENNReal.ofReal (rho p.1) * ENNReal.ofReal (rho p.2))
        ∂((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))) < ⊤ := by
  haveI : DiscreteTopology Γ := hΓ.1.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hF := s8w_fundD hΓ.1
  have hρm : Measurable fun z : ℂ => ENNReal.ofReal (rho z) := ENNReal.measurable_ofReal.comp gam_rho_measurable
  have hm : Measurable fun p : ℂ × ℂ => (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2))) *
        (ENNReal.ofReal (rho p.1) * ENNReal.ofReal (rho p.2)) :=
    (s8q_Ke_meas hΓ.1).mul ((hρm.comp measurable_fst).mul (hρm.comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  have hin : ∀ z ∈ fundDomainOn Γ unitDisc, (∫⁻ u in fundDomainOn Γ unitDisc,
      (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u))) *
        (ENNReal.ofReal (rho z) * ENNReal.ofReal (rho u))) = ENNReal.ofReal (rho z) := by
    intro z hz
    have hzD := hF.2.1 hz
    calc (∫⁻ u in fundDomainOn Γ unitDisc,
          (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u))) *
            (ENNReal.ofReal (rho z) * ENNReal.ofReal (rho u)))
        = ∫⁻ u in fundDomainOn Γ unitDisc, ENNReal.ofReal (rho z) *
            ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
              ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u) * rho u) := by
          refine lintegral_congr fun u => ?_
          simp only [ENNReal.ofReal_mul' (s8q_rho_nonneg u), ENNReal.tsum_mul_right]
          ring
      _ = ENNReal.ofReal (rho z) * ∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
            ∫⁻ u in fundDomainOn Γ unitDisc, ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u) * rho u) := by
          have hmeas : ∀ a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), AEMeasurable
              (fun u => ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u) * rho u))
              (volume.restrict (fundDomainOn Γ unitDisc)) := fun a =>
            (ENNReal.measurable_ofReal.comp ((gam_kernel_comp_measurable _ (gam_action_measurable Γ a) z).mul
              gam_rho_measurable)).aemeasurable
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeas]
      _ = ENNReal.ofReal (rho z) := by rw [fdD_sum_tile_kernel_mass hΓ.1 hF hzD, mul_one]
  rw [setLIntegral_congr_fun hF.1 hin]
  exact s8w_area_fin hΓ

/-- A.e. on `F × F`: both points in `F`, off the orbit relation. -/
theorem s8q_ae_off {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    ∀ᵐ p ∂((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))),
      p.1 ∈ fundDomainOn Γ unitDisc ∧ p.2 ∈ fundDomainOn Γ unitDisc ∧ ∀ g ∈ Γ, mob g p.2 ≠ p.1 := by
  have hFm := (s8w_fundD hΓ).1
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (hFm.prod hFm),
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (s8q_orbit_null hΓ))] with p hp hn
  exact ⟨hp.1, hp.2, fun g hg h => hn ⟨g, hg, h⟩⟩

/-- `G_Γ` is a.e.-strongly measurable on `F × F`. -/
theorem s8q_K_aesm {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    AEStronglyMeasurable (fun p : ℂ × ℂ => (resolventKernelGamma Γ p.1 p.2 : ℂ))
      ((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))) := by
  have hFD := (s8w_fundD hΓ).2.1
  have hm : Measurable fun p : ℂ × ℂ => (((∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
      ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2))).toReal : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (s8q_Ke_meas hΓ).ennreal_toReal
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [s8q_ae_off hΓ] with p hp
  rw [s8q_K_eq hΓ (hFD hp.2.1) (hFD hp.1) hp.2.2]

/-- Pointwise majorant of the `F × F` integrand. -/
theorem s8q_int_pt {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {A B : ℂ → ℂ} {CA CB : ℝ} (hCA : 0 ≤ CA)
    {z u : ℂ} (hz : z ∈ unitDisc) (hu : u ∈ unitDisc) (hAz : ‖A z‖ ≤ CA) (hBu : ‖B u‖ ≤ CB)
    (hoff : ∀ g ∈ Γ, mob g u ≠ z) :
    ‖A z * (resolventKernelGamma Γ z u : ℂ) * B u * (rho u : ℂ) * (rho z : ℂ)‖ₑ ≤
      ENNReal.ofReal (CA * CB) * ((∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
        ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u))) * (ENNReal.ofReal (rho z) * ENNReal.ofReal (rho u))) := by
  have hCB : 0 ≤ CB := (norm_nonneg _).trans hBu
  rw [s8q_K_eq hΓ hu hz hoff, ← ofReal_norm_eq_enorm]
  generalize (∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C),
    ENNReal.ofReal (resolventKernel z ((a : ℂ → ℂ) u))) = K
  have hK : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hr1 := s8q_rho_nonneg z
  have hr2 := s8q_rho_nonneg u
  have hn : ‖A z * ((K.toReal : ℝ) : ℂ) * B u * (rho u : ℂ) * (rho z : ℂ)‖ =
      ‖A z‖ * K.toReal * ‖B u‖ * rho u * rho z := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hK, Real.norm_of_nonneg hr2, Real.norm_of_nonneg hr1]
  have hle : ‖A z‖ * K.toReal * ‖B u‖ * rho u * rho z ≤ CA * CB * (K.toReal * (rho z * rho u)) := by
    have hAB : ‖A z‖ * ‖B u‖ ≤ CA * CB := mul_le_mul hAz hBu (norm_nonneg _) hCA
    have hX : 0 ≤ K.toReal * (rho z * rho u) := mul_nonneg hK (mul_nonneg hr1 hr2)
    calc ‖A z‖ * K.toReal * ‖B u‖ * rho u * rho z
        = (‖A z‖ * ‖B u‖) * (K.toReal * (rho z * rho u)) := by ring
      _ ≤ (CA * CB) * (K.toReal * (rho z * rho u)) := mul_le_mul_of_nonneg_right hAB hX
  rw [hn]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hCA hCB), ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hr1]
  gcongr
  exact ENNReal.ofReal_toReal_le

/-- The `F × F` integrand of the symmetric pairing is integrable. -/
theorem s8q_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {A B : ℂ → ℂ} (hA : ContinuousOn A unitDisc)
    (hB : ContinuousOn B unitDisc) {CA CB : ℝ} (hAb : ∀ z ∈ unitDisc, ‖A z‖ ≤ CA)
    (hBb : ∀ z ∈ unitDisc, ‖B z‖ ≤ CB) :
    Integrable (fun p : ℂ × ℂ => A p.1 * (resolventKernelGamma Γ p.1 p.2 : ℂ) * B p.2 * (rho p.2 : ℂ) * (rho p.1 : ℂ))
      ((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))) := by
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  have hCA : 0 ≤ CA := (norm_nonneg _).trans (hAb 0 (mem_ball_self one_pos))
  have hAm : AEStronglyMeasurable A (volume.restrict (fundDomainOn Γ unitDisc)) :=
    (hA.mono hFD).aestronglyMeasurable hFm
  have hBm : AEStronglyMeasurable B (volume.restrict (fundDomainOn Γ unitDisc)) :=
    (hB.mono hFD).aestronglyMeasurable hFm
  have hρm : Measurable fun z : ℂ => (rho z : ℂ) := Complex.measurable_ofReal.comp gam_rho_measurable
  have h1 : AEStronglyMeasurable (fun p : ℂ × ℂ => A p.1)
      ((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))) := hAm.comp_fst
  have h2 : AEStronglyMeasurable (fun p : ℂ × ℂ => B p.2)
      ((volume.restrict (fundDomainOn Γ unitDisc)).prod (volume.restrict (fundDomainOn Γ unitDisc))) := hBm.comp_snd
  have h3 : Measurable fun p : ℂ × ℂ => (rho p.2 : ℂ) := hρm.comp measurable_snd
  have h4 : Measurable fun p : ℂ × ℂ => (rho p.1 : ℂ) := hρm.comp measurable_fst
  refine ⟨(((h1.mul (s8q_K_aesm hΓ.1)).mul h2).mul h3.aestronglyMeasurable).mul h4.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun p => ENNReal.ofReal (CA * CB) *
      ((∑' a : (fun g : SL2C => mob g) '' (Γ : Set SL2C), ENNReal.ofReal (resolventKernel p.1 ((a : ℂ → ℂ) p.2))) *
        (ENNReal.ofReal (rho p.1) * ENNReal.ofReal (rho p.2)))) ?_) ?_
  · filter_upwards [s8q_ae_off hΓ.1] with p hp
    exact s8q_int_pt hΓ.1 hCA (hFD hp.1) (hFD hp.2.1) (hAb _ (hFD hp.1)) (hBb _ (hFD hp.2.1)) hp.2.2
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (s8q_K_lint hΓ)

/-- **Core of SYM**: `(A, G_Γ B)_Γ = (B̄, G_Γ Ā)_Γ` for bounded continuous `A, B` on `𝔻`. -/
theorem s8q_sym_core {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {A B : ℂ → ℂ} (hA : ContinuousOn A unitDisc)
    (hB : ContinuousOn B unitDisc) {CA CB : ℝ} (hAb : ∀ z ∈ unitDisc, ‖A z‖ ≤ CA)
    (hBb : ∀ z ∈ unitDisc, ‖B z‖ ≤ CB) :
    innerGamma Γ A (resolventGammaD Γ B) =
      innerGamma Γ (fun z => conj (B z)) (resolventGammaD Γ fun z => conj (A z)) := by
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  have hcB : ContinuousOn (fun z => conj (B z)) unitDisc := Complex.continuous_conj.comp_continuousOn hB
  have hcBb : ∀ z ∈ unitDisc, ‖conj (B z)‖ ≤ CB := fun z hz => by rw [Complex.norm_conj]; exact hBb z hz
  have hint := s8q_int hΓ hA hcB hAb hcBb
  have hL : innerGamma Γ A (resolventGammaD Γ B) = ∫ z in fundDomainOn Γ unitDisc, ∫ u in fundDomainOn Γ unitDisc,
      A z * (resolventKernelGamma Γ z u : ℂ) * conj (B u) * (rho u : ℂ) * (rho z : ℂ) := by
    show (∫ z in fundDomainOn Γ unitDisc, A z *
        conj (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * B u * rho u) * rho z) = _
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [← integral_conj, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    beta_reduce
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hR : innerGamma Γ (fun z => conj (B z)) (resolventGammaD Γ fun z => conj (A z)) =
      ∫ z in fundDomainOn Γ unitDisc, ∫ u in fundDomainOn Γ unitDisc,
        conj (B z) * (resolventKernelGamma Γ z u : ℂ) * A u * (rho u : ℂ) * (rho z : ℂ) := by
    show (∫ z in fundDomainOn Γ unitDisc, conj (B z) *
        conj (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * conj (A u) * rho u) * rho z) = _
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [← integral_conj, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    beta_reduce
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [hL, hR, integral_integral_swap (f := fun z u =>
    A z * (resolventKernelGamma Γ z u : ℂ) * conj (B u) * (rho u : ℂ) * (rho z : ℂ)) hint]
  refine setIntegral_congr_fun hFm fun u hu => ?_
  refine setIntegral_congr_fun hFm fun z hz => ?_
  beta_reduce
  rw [s8q_K_symm hΓ.1 (hFD hz) (hFD hu)]
  ring

/-- Bounded continuous functions times `ρ` are integrable on `F` (finite area). -/
theorem s8q_bdd_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {U : ℂ → ℂ} (hU : ContinuousOn U unitDisc) {C : ℝ}
    (hUb : ∀ z ∈ unitDisc, ‖U z‖ ≤ C) :
    IntegrableOn (fun z => U z * (rho z : ℂ)) (fundDomainOn Γ unitDisc) := by
  have hF := s8w_fundD hΓ.1
  have hρ : IntegrableOn (fun z => ((rho z : ℝ) : ℂ)) (fundDomainOn Γ unitDisc) :=
    (s8w_rho_integrableOn (s8w_area_fin hΓ)).ofReal
  exact hρ.bdd_mul (c := C) ((hU.mono hF.2.1).aestronglyMeasurable hF.1)
    ((ae_restrict_iff' hF.1).mpr (Eventually.of_forall fun z hz => hUb z (hF.2.1 hz)))

/-- Fatou for monotone-free exhaustions: uniformly bounded integrals of `w_n f` with `0 ≤ w_n ≤ 1`, `w_n → 1`,
force integrability of `f ≥ 0`. -/
theorem s8q_fatou {S : Set ℂ} (hS : MeasurableSet S) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict S))
    (hf0 : ∀ z ∈ S, 0 ≤ f z) {w : ℕ → ℂ → ℝ} (hw : ∀ n, ∀ z ∈ S, 0 ≤ w n z)
    (hlim : ∀ z ∈ S, Tendsto (fun n => w n z) atTop (𝓝 1))
    (hint : ∀ n, IntegrableOn (fun z => w n z * f z) S) {B : ℝ}
    (hB : ∀ n, ∫ z in S, w n z * f z ≤ B) : IntegrableOn f S := by
  refine ⟨hf, ?_⟩
  have hfae : ∀ᵐ z ∂(volume.restrict S), 0 ≤ f z := (ae_restrict_iff' hS).mpr (Eventually.of_forall hf0)
  rw [hasFiniteIntegral_iff_ofReal hfae]
  have hliminf : ∀ᵐ z ∂(volume.restrict S),
      Filter.liminf (fun n => ENNReal.ofReal (w n z * f z)) atTop = ENNReal.ofReal (f z) := by
    refine (ae_restrict_iff' hS).mpr (Eventually.of_forall fun z hz => ?_)
    have ht : Tendsto (fun n => ENNReal.ofReal (w n z * f z)) atTop (𝓝 (ENNReal.ofReal (f z))) := by
      have := ((hlim z hz).mul_const (f z))
      rw [one_mul] at this
      exact (ENNReal.continuous_ofReal.tendsto _).comp this
    exact ht.liminf_eq
  have hmeas : ∀ n, AEMeasurable (fun z => ENNReal.ofReal (w n z * f z)) (volume.restrict S) := fun n =>
    (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  calc ∫⁻ z in S, ENNReal.ofReal (f z)
      = ∫⁻ z in S, Filter.liminf (fun n => ENNReal.ofReal (w n z * f z)) atTop :=
        (lintegral_congr_ae hliminf).symm
    _ ≤ Filter.liminf (fun n => ∫⁻ z in S, ENNReal.ofReal (w n z * f z)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal B := by
        refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
          ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun z hz => mul_nonneg (hw n z hz) (hf0 z hz)))]
        exact ENNReal.ofReal_le_ofReal (hB n)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A continuous `Γ`-invariant function is bounded on the support of a cutoff compactly supported mod `Γ`. -/
theorem s8q_inv_bound {Γ : Subgroup SL2C} {Φ : ℂ → ℝ} (hΦ : ContinuousOn Φ unitDisc)
    (hΦΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, Φ (mob g z) = Φ z) {χ : ℂ → ℝ}
    (hK : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ unitDisc ∧ ∀ z ∈ unitDisc, χ z ≠ 0 → ∃ g ∈ Γ, mob g z ∈ K) :
    ∃ M : ℝ, ∀ z ∈ unitDisc, χ z ≠ 0 → |Φ z| ≤ M := by
  obtain ⟨K, hKc, hKD, hKm⟩ := hK
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.mono hKD)
  refine ⟨M, fun z hz hχ => ?_⟩
  obtain ⟨g, hg, hgK⟩ := hKm z hz hχ
  rw [← hΦΓ g hg z hz, ← Real.norm_eq_abs]
  exact hM _ hgK

/-- `G_Γ` is `Γ`-invariant in its first variable on `𝔻`. -/
theorem s8q_KG_inv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {g : SL2C} (hg : g ∈ Γ) {z u : ℂ}
    (hz : z ∈ unitDisc) (hu : u ∈ unitDisc) :
    resolventKernelGamma Γ (mob g z) u = resolventKernelGamma Γ z u := by
  obtain ⟨e, he⟩ := gam_equiv_mul Γ (Γ.inv_mem hg)
  unfold resolventKernelGamma
  rw [← e.tsum_eq (fun b : (fun k : SL2C => mob k) '' (Γ : Set SL2C) => resolventKernel z ((b : ℂ → ℂ) u))]
  refine tsum_congr fun a => ?_
  obtain ⟨k, hk, hka⟩ := a.2
  have hka' : mob k = a.1 := hka
  rw [he a k hk hka', ← hka']
  have hku : mob k u ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1 k hk) (mem_ball_zero_iff.mp hu))
  have hDk := fdD_denom_ne (hΓ.1 k hk) (mem_ball_zero_iff.mp hu)
  have hDg := fdD_denom_ne (isSU11_inv (hΓ.1 g hg)) (mem_ball_zero_iff.mp hku)
  rw [fdD_kernel_act (hΓ.1 g hg) hz hku, (fd_mob_mul hDk hDg).2]

/-- `G_Γ F = G_𝔻 F` on `𝔻` for bounded smooth `Γ`-invariant `F` (via the disk indicator and `s8g_unfold`). -/
theorem s8q_res_eq {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : ℂ → ℂ} (hF : F ∈ BCinf unitDisc)
    (hFΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, F (mob g z) = F z) {z : ℂ} (hz : z ∈ unitDisc) :
    resolventGammaD Γ F z = resolventOp unitDisc F z := by
  classical
  obtain ⟨C, hC⟩ := hF.2
  have hFD := (s8w_fundD hΓ).2.1
  have hm : Measurable (unitDisc.piecewise F fun _ => (0 : ℂ)) :=
    (hF.1.continuousOn).measurable_piecewise continuousOn_const measurableSet_ball
  have hb : ∀ w ∈ unitDisc, ‖unitDisc.piecewise F (fun _ => (0 : ℂ)) w‖ ≤ C := fun w hw => by
    rw [Set.piecewise_eq_of_mem _ _ _ hw]; exact hC w hw
  have hi : ∀ g ∈ Γ, ∀ w ∈ unitDisc, unitDisc.piecewise F (fun _ => (0 : ℂ)) (mob g w) =
      unitDisc.piecewise F (fun _ => (0 : ℂ)) w := fun g hg w hw => by
    have hgw : mob g w ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1 g hg) (mem_ball_zero_iff.mp hw))
    rw [Set.piecewise_eq_of_mem _ _ _ hw, Set.piecewise_eq_of_mem _ _ _ hgw, hFΓ g hg w hw]
  have h := s8g_unfold hΓ hm hb hi hz
  have e1 : resolventOp unitDisc (unitDisc.piecewise F fun _ => (0 : ℂ)) z = resolventOp unitDisc F z :=
    setIntegral_congr_fun measurableSet_ball fun w hw => by
      beta_reduce
      rw [Set.piecewise_eq_of_mem _ _ _ hw]
  have e2 : resolventGammaD Γ (unitDisc.piecewise F fun _ => (0 : ℂ)) z = resolventGammaD Γ F z :=
    setIntegral_congr_fun (s8w_fundD hΓ).1 fun w hw => by
      beta_reduce
      rw [Set.piecewise_eq_of_mem _ _ _ (hFD hw)]
  rw [← e1, ← e2, h]

/-- Wirtinger chain rule through a holomorphic inner map. -/
theorem s8q_chain_holo {H m : ℂ → ℂ} {z : ℂ} (hm : DifferentiableAt ℂ m z) (hH : DifferentiableAt ℝ H (m z)) :
    dz (fun w => H (m w)) z = dz H (m z) * deriv m z ∧
      dzbar (fun w => H (m w)) z = dzbar H (m z) * conj (deriv m z) := by
  have hmR := hm.restrictScalars ℝ
  have hd1 : dz m z = deriv m z := dz_eq_deriv hm
  have hd0 : dzbar m z = 0 := (cauchyRiemann_iff.1 hm).2
  have e1 := eq6_2_dz_comp hmR hH
  have e2 := eq6_2_dzbar_comp hmR hH
  rw [s7g_f2_dz_conj, hd0, map_zero, mul_zero, add_zero, hd1] at e1
  rw [p71r_dzbar_conj, hd0, hd1, mul_zero, zero_add] at e2
  exact ⟨e1, e2⟩

/-- `∂̄` depends only on the germ. -/
theorem s8q_dzbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dzbar f z = dzbar g z := by
  unfold dzbar
  rw [h.fderiv_eq]

/-- `ρ ≠ 0` on `𝔻`. -/
theorem s8q_rho_ne {w : ℂ} (hw : w ∈ unitDisc) : (rho w : ℂ) ≠ 0 := by
  have h : (rho w : ℂ)⁻¹ ≠ 0 := by
    rw [wp_rho_inv_complex]
    exact div_ne_zero (pow_ne_zero 2 (wp_disk_factor_ne_zero hw)) (by norm_num)
  exact fun h0 => h (by rw [h0, inv_zero])

/-- Smoothness of a parametric integral `z ↦ ∫ k(z, w) f(w) dw` with a jointly smooth kernel supported in `w ∈ S`
(written as a convolution, `contDiffOn_convolution_left_with_param_comp`). -/
theorem s8q_pint_smooth {k : ℂ → ℂ → ℂ} {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hS : IsCompact S)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 q.2) (U ×ˢ univ))
    (hks : ∀ z ∈ U, ∀ w ∉ S, k z w = 0) (hf : LocallyIntegrable f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ∫ w, k z w * f w) U := by
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 (-q.2)) (U ×ˢ univ) :=
    hk.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn fun q hq => ⟨hq.1, mem_univ _⟩
  have hgs : ∀ p t, p ∈ U → t ∉ -S → k p (-t) = 0 := fun p t hp ht =>
    hks p hp (-t) fun h => ht (Set.mem_neg.mpr h)
  have hc : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => convolution (fun t => k x (-t)) f (ContinuousLinearMap.mul ℝ ℂ) volume ((fun _ => (0 : ℂ)) x)) U :=
    contDiffOn_convolution_left_with_param_comp (𝕜 := ℝ) (G := ℂ) (P := ℂ) (ContinuousLinearMap.mul ℝ ℂ)
      contDiffOn_const hU hS.neg hgs hf hg
  refine hc.congr fun z _ => ?_
  show ∫ w, k z w * f w = ∫ t, (ContinuousLinearMap.mul ℝ ℂ) (k z (-t)) (f (0 - t))
  simp only [ContinuousLinearMap.mul_apply', zero_sub]
  exact (integral_neg_eq_self (fun w => k z w * f w) volume).symm

/-- The partial derivative of a jointly smooth kernel vanishes where the kernel does. -/
theorem s8q_pint_d0 {k : ℂ → ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hS : IsCompact S)
    (hks : ∀ z ∈ U, ∀ w ∉ S, k z w = 0) {z w : ℂ} (hz : z ∈ U) (hw : w ∉ S) :
    fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) = 0 := by
  refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
  filter_upwards [(hU.prod hS.isClosed.isOpen_compl).mem_nhds (show (z, w) ∈ U ×ˢ Sᶜ from ⟨hz, hw⟩)] with q hq
  exact hks q.1 hq.1 q.2 hq.2

/-- Differentiation under the integral sign for `z ↦ ∫ k(z, w) f(w) dw` (kernel jointly smooth, supported in
`w ∈ S`, `f` integrable). -/
theorem s8q_pint_fderiv {k : ℂ → ℂ → ℂ} {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hS : IsCompact S)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 q.2) (U ×ˢ univ))
    (hks : ∀ z ∈ U, ∀ w ∉ S, k z w = 0) (hf : Integrable f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    Integrable (fun w => f w • (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w)).comp
        (ContinuousLinearMap.inl ℝ ℂ ℂ)) ∧
      HasFDerivAt (fun z => ∫ w, k z w * f w)
        (∫ w, f w • (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) z₀ := by
  have hO : IsOpen (U ×ˢ (univ : Set ℂ)) := hU.prod isOpen_univ
  have hKd : ∀ z ∈ U, ∀ w, HasFDerivAt (fun q : ℂ × ℂ => k q.1 q.2)
      (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w)) (z, w) := fun z hz w =>
    ((hk.differentiableOn (by simp)).differentiableAt (hO.mem_nhds ⟨hz, mem_univ w⟩)).hasFDerivAt
  have hKc : ContinuousOn (fun q => fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) q) (U ×ˢ univ) :=
    hk.continuousOn_fderiv_of_isOpen hO (by simp)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hcb : closedBall z₀ (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨B, hB⟩ := ((isCompact_closedBall z₀ (ε / 2)).prod hS).exists_bound_of_continuousOn
    (hKc.mono (prod_mono hcb (subset_univ _)))
  have hbd : ∀ x ∈ ball z₀ (ε / 2), ∀ w, ‖f w • (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (x, w)).comp
      (ContinuousLinearMap.inl ℝ ℂ ℂ)‖ ≤ ‖f w‖ * max B 0 := fun x hx w => by
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hw : w ∈ S
    · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := hB (x, w) ⟨ball_subset_closedBall hx, hw⟩
      have h2 := ContinuousLinearMap.norm_inl_le_one ℝ ℂ ℂ
      nlinarith [norm_nonneg (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (x, w)), le_max_left B 0,
        norm_nonneg (ContinuousLinearMap.inl ℝ ℂ ℂ)]
    · rw [s8q_pint_d0 hU hS hks (hcb (ball_subset_closedBall hx)) hw, ContinuousLinearMap.zero_comp, norm_zero]
      exact le_max_right _ _
  have hcont : ∀ x ∈ U, Continuous fun w => (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (x, w)).comp
      (ContinuousLinearMap.inl ℝ ℂ ℂ) := fun x hx =>
    (hKc.comp_continuous (Continuous.prodMk_right x) fun w => ⟨hx, mem_univ w⟩).clm_comp continuous_const
  haveI : ContinuousSMul ℂ (ℂ →L[ℝ] ℂ) := IsBoundedSMul.continuousSMul
  have hm' : AEStronglyMeasurable (fun w => f w • (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w)).comp
      (ContinuousLinearMap.inl ℝ ℂ ℂ)) volume :=
    hf.aestronglyMeasurable.smul (hcont z₀ hz₀).aestronglyMeasurable
  have hI : Integrable (fun w => f w • (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w)).comp
      (ContinuousLinearMap.inl ℝ ℂ ℂ)) :=
    Integrable.mono' (hf.norm.mul_const _) hm' (Eventually.of_forall fun w => hbd z₀ (mem_ball_self (by linarith)) w)
  refine ⟨hI, ?_⟩
  have hkc : ∀ x ∈ U, Continuous fun w => k x w := fun x hx =>
    hk.continuousOn.comp_continuous (Continuous.prodMk_right x) fun w => ⟨hx, mem_univ w⟩
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hkc z₀ hz₀).continuousOn
  have hFi : Integrable (fun w => k z₀ w * f w) := by
    refine hf.bdd_mul (c := max C 0) (hkc z₀ hz₀).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ S
    · exact (hC w hw).trans (le_max_left _ _)
    · rw [hks z₀ hz₀ w hw, norm_zero]; exact le_max_right _ _
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds z₀ (by linarith : 0 < ε / 2))
    ?_ hFi hm' (Eventually.of_forall fun w x hx => hbd x hx w) (hf.norm.mul_const _)
    (Eventually.of_forall fun w x hx => ?_)
  · filter_upwards [hU.mem_nhds hz₀] with x hx
    exact (hkc x hx).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · have hxU := hεU (ball_subset_ball (by linarith) hx)
    have h1 := (hKd x hxU w).comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x w)
    exact h1.mul_const (f w)

/-- Wirtinger derivatives of a parametric integral: `∂_z ∫ k f = ∫ (∂_z k) f`, `∂̄_z ∫ k f = ∫ (∂̄_z k) f`. -/
theorem s8q_pint_wirt {k : ℂ → ℂ → ℂ} {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hS : IsCompact S)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 q.2) (U ×ˢ univ))
    (hks : ∀ z ∈ U, ∀ w ∉ S, k z w = 0) (hf : Integrable f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    dz (fun z => ∫ w, k z w * f w) z₀ =
        ∫ w, (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (1, 0) -
          I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (I, 0)) / 2 * f w ∧
      dzbar (fun z => ∫ w, k z w * f w) z₀ =
        ∫ w, (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (1, 0) +
          I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (I, 0)) / 2 * f w := by
  obtain ⟨hI, hD⟩ := s8q_pint_fderiv hU hS hk hks hf hz₀
  have hap : ∀ v : ℂ, fderiv ℝ (fun z => ∫ w, k z w * f w) z₀ v =
      ∫ w, f w * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (v, 0) := fun v => by
    rw [hD.fderiv, ContinuousLinearMap.integral_apply hI]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      smul_eq_mul]
  have hiv : ∀ v : ℂ, Integrable (fun w => f w * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z₀, w) (v, 0)) := fun v => by
    have := hI.apply_continuousLinearMap v
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      smul_eq_mul] using this
  constructor
  · show (fderiv ℝ (fun z => ∫ w, k z w * f w) z₀ 1 - I * fderiv ℝ (fun z => ∫ w, k z w * f w) z₀ I) / 2 = _
    rw [hap, hap, ← integral_const_mul, ← integral_sub (hiv 1) ((hiv I).const_mul I), ← integral_div]
    congr 1; funext w; ring
  · show (fderiv ℝ (fun z => ∫ w, k z w * f w) z₀ 1 + I * fderiv ℝ (fun z => ∫ w, k z w * f w) z₀ I) / 2 = _
    rw [hap, hap, ← integral_const_mul, ← integral_add (hiv 1) ((hiv I).const_mul I), ← integral_div]
    congr 1; funext w; ring

/-- The `∂̄_z`-kernel of a jointly smooth kernel is jointly smooth and has the same `w`-support. -/
theorem s8q_pint_dbar_kernel {k : ℂ → ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U) (hS : IsCompact S)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 q.2) (U ×ˢ univ))
    (hks : ∀ z ∈ U, ∀ w ∉ S, k z w = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (q.1, q.2) (1, 0) +
        I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (q.1, q.2) (I, 0)) / 2) (U ×ˢ univ) ∧
      ∀ z ∈ U, ∀ w ∉ S, (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
        I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2 = 0 := by
  have hO : IsOpen (U ×ˢ (univ : Set ℂ)) := hU.prod isOpen_univ
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) q) (U ×ˢ univ) :=
    hk.fderiv_of_isOpen hO (by simp)
  refine ⟨?_, fun z hz w hw => ?_⟩
  · exact (((hd.clm_apply contDiffOn_const).add (contDiffOn_const.mul (hd.clm_apply contDiffOn_const))).div_const
      _).congr fun q _ => rfl
  · rw [s8q_pint_d0 hU hS hks hz hw]; simp

/-- `‖∫ A f‖ ≤ B ∫ ‖f‖` when `‖A‖ ≤ B` on `S` and `A = 0` off `S`. -/
theorem s8q_pint_bound {A f : ℂ → ℂ} {S : Set ℂ} {B : ℝ} (hB : 0 ≤ B) (hA : ∀ w ∈ S, ‖A w‖ ≤ B)
    (hA0 : ∀ w ∉ S, A w = 0) (hf : Integrable f) :
    ‖∫ w, A w * f w‖ ≤ B * ∫ w, ‖f w‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _) (hf.norm.const_mul B)
    (Eventually.of_forall fun w => ?_)
  show ‖A w * f w‖ ≤ B * ‖f w‖
  rw [norm_mul]
  by_cases hw : w ∈ S
  · exact mul_le_mul_of_nonneg_right (hA w hw) (norm_nonneg _)
  · rw [hA0 w hw, norm_zero, zero_mul]; exact mul_nonneg hB (norm_nonneg _)

/-- `|1 - z̄w|² = (1 - |z|²)(1 - |w|²) + |z - w|²`. -/
theorem s8q_den_id (z w : ℂ) : ‖1 - conj z * w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) + ‖z - w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- Point-pair localization: `|z| ≤ s < 1`, `w ∈ 𝔻` and `u(z, w) ≤ 2` force `(1 - s)² ≤ 3(1 - |w|²)`. -/
theorem s8q_pp_loc {z w : ℂ} {s : ℝ} (hzs : ‖z‖ ≤ s) (hs : s < 1) (hw : ‖w‖ < 1) (hp : pointPair z w ≤ 2) :
    (1 - s) ^ 2 ≤ 3 * (1 - ‖w‖ ^ 2) := by
  have hz : ‖z‖ < 1 := hzs.trans_lt hs
  have hs0 : 0 ≤ s := (norm_nonneg z).trans hzs
  have ha : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hb : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hp' : ‖z - w‖ ^ 2 ≤ 2 * ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
    unfold pointPair at hp
    rwa [div_le_iff₀ (mul_pos ha hb)] at hp
  have hid := s8q_den_id z w
  have hlow : 1 - s ≤ ‖1 - conj z * w‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (conj z * w)
    rw [norm_one, norm_mul, Complex.norm_conj] at h1
    have h2 := mul_le_mul hzs hw.le (norm_nonneg w) hs0
    linarith
  have h1 : (1 - s) ^ 2 ≤ ‖1 - conj z * w‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlow 2
  have h3 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  nlinarith [mul_le_mul_of_nonneg_right h3 hb.le]

/-- `u(z, w)` is measurable in `w`. -/
theorem s8q_pp_meas (z : ℂ) : Measurable fun w => pointPair z w := by
  unfold pointPair; fun_prop

/-- The cutoff kernel `k(z, w) = b(w) η(u(z, w))` is jointly smooth on `B(0, ½) × ℂ`, supported in `|w| ≤ 49/50`,
and equals `η(u(z, w))` for `w ∈ 𝔻`. -/
theorem s8q_ker (η : ContDiffBump (0 : ℝ)) (hη : η.rOut = 2) (b : ContDiffBump (0 : ℂ)) (hb1 : b.rIn = 24 / 25)
    (hb2 : b.rOut = 49 / 50) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => (b q.2 : ℂ) * (η (pointPair q.1 q.2) : ℂ)) (ball 0 (1 / 2) ×ˢ univ) ∧
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w ∉ closedBall (0 : ℂ) (49 / 50),
        (b w : ℂ) * (η (pointPair z w) : ℂ) = 0) ∧
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w ∈ unitDisc,
        (b w : ℂ) * (η (pointPair z w) : ℂ) = (η (pointPair z w) : ℂ)) := by
  have hb0 : ∀ w : ℂ, 49 / 50 ≤ ‖w‖ → b w = 0 := fun w hw =>
    Function.notMem_support.mp fun h => by
      rw [b.support_eq, mem_ball_zero_iff, hb2] at h; linarith
  refine ⟨fun q hq => ?_, fun z _ w hw => ?_, fun z hz w hw => ?_⟩
  · have hz : ‖q.1‖ < 1 / 2 := mem_ball_zero_iff.mp hq.1
    by_cases hw : ‖q.2‖ < 99 / 100
    · have h1 : 1 - ‖q.1‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg q.1]
      have h2 : 1 - ‖q.2‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg q.2]
      have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => pointPair p.1 p.2) (q.1, q.2) :=
        (pointPair_contDiffAt q.1 q.2 h1 h2).of_le le_top
      have hbq : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => (b p.2 : ℂ)) q :=
        (Complex.ofRealCLM.contDiff.comp (b.contDiff.comp contDiff_snd)).contDiffAt
      have hηq : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => (η (pointPair p.1 p.2) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q (η.contDiff.contDiffAt.comp q hp)
      exact (hbq.mul hηq).contDiffWithinAt
    · push_neg at hw
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_ |>.contDiffWithinAt
      have ho : IsOpen {p : ℂ × ℂ | 49 / 50 < ‖p.2‖} := isOpen_lt continuous_const continuous_snd.norm
      filter_upwards [ho.mem_nhds (show 49 / 50 < ‖q.2‖ by linarith)] with p hp
      simp only [hb0 p.2 (le_of_lt hp), Complex.ofReal_zero, zero_mul]
  · have : 49 / 50 < ‖w‖ := by
      rw [mem_closedBall_zero_iff] at hw; push_neg at hw; exact hw
    simp only [hb0 w this.le, Complex.ofReal_zero, zero_mul]
  · by_cases h0 : η (pointPair z w) = 0
    · simp only [h0, Complex.ofReal_zero, mul_zero]
    · have hlt : |pointPair z w| < 2 := by
        have := Function.mem_support.mpr h0
        rwa [η.support_eq, mem_ball, Real.dist_eq, sub_zero, hη] at this
      have hl := s8q_pp_loc (mem_ball_zero_iff.mp hz).le (by norm_num) (mem_ball_zero_iff.mp hw)
        (le_of_lt (abs_lt.mp hlt).2)
      have hw2 : ‖w‖ ≤ 24 / 25 := by
        by_contra hc; push_neg at hc; nlinarith [norm_nonneg w]
      rw [b.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, hb1]; exact hw2), Complex.ofReal_one, one_mul]

/-- An `SU(1,1)` Möbius map maps `𝔻` onto `𝔻`. -/
theorem s8q_mob_image {g : SL2C} (hg : IsSU11 g) : mob g '' unitDisc = unitDisc := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_ball_zero_iff.mpr (fdD_mob_lt hg (mem_ball_zero_iff.mp hw))
  · intro hu
    have hi := isSU11_inv hg
    refine ⟨mob g⁻¹ u, mem_ball_zero_iff.mpr (fdD_mob_lt hi (mem_ball_zero_iff.mp hu)), ?_⟩
    have := (fd_inv_step g⁻¹ (fdD_denom_ne hi (mem_ball_zero_iff.mp hu))).2
    rwa [inv_inv] at this

/-- Covariance of point-pair integral operators under `SU(1,1)`:
`∫_𝔻 φ(u(γz, w)) G(w) ρ(w) dw = ∫_𝔻 φ(u(z, w)) G(γw) ρ(w) dw`. -/
theorem s8q_cov {g : SL2C} (hg : IsSU11 g) (φ : ℝ → ℝ) (G : ℂ → ℝ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∫ w in unitDisc, φ (pointPair (mob g z) w) * G w * rho w =
      ∫ w in unitDisc, φ (pointPair z w) * G (mob g w) * rho w := by
  have hD : ∀ w ∈ unitDisc, g 1 0 * w + g 1 1 ≠ 0 := fun w hw => fdD_denom_ne hg (mem_ball_zero_iff.mp hw)
  have h := fdq_mob_integral_image (E := ℝ) (s := unitDisc) g measurableSet_ball hD
    (fun w => φ (pointPair (mob g z) w) * G w * rho w)
  rw [s8q_mob_image hg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_ball fun w hw => ?_
  have hj := gam_rho_mob_jacobian hg (hD w hw)
  simp only [smul_eq_mul]
  rw [pointPair_mob_of_denominator_ne_zero g hg z w (hD z hz) (hD w hw), ← hj]
  ring

/-- Every point of `𝔻` is `γ(0)` for some `γ ∈ SU(1,1)`. -/
theorem s8q_su11_to {z : ℂ} (hz : z ∈ unitDisc) : ∃ g : SL2C, IsSU11 g ∧ mob g 0 = z := by
  have hz' : ‖-z‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp hz
  obtain ⟨g, hg, hm⟩ := s8w_su11_of_blaschke (c := 1) (by simp) hz'
  refine ⟨g, hg, ?_⟩
  rw [hm 0 (mem_ball_self one_pos), one_mul]
  show (0 - -z) / (1 - conj (-z) * 0) = z
  simp

/-- `ρ(w) ≤ 4/δ²` where `1 - |w|² ≥ δ > 0`. -/
theorem s8q_rho_le {w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hw : δ ≤ 1 - ‖w‖ ^ 2) : rho w ≤ 4 / δ ^ 2 := by
  show 4 / (1 - ‖w‖ ^ 2) ^ 2 ≤ 4 / δ ^ 2
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hδ.le hw 2)

/-- The point-pair operator with a bump `η` (support in `(-2, 2)`, `|η| ≤ 1`) is absolutely convergent at every
`z ∈ 𝔻` on bounded measurable data, with a uniform bound `4/δ²` on the integrand. -/
theorem s8q_T_int (η : ContDiffBump (0 : ℝ)) (hη : η.rOut = 2) {G : ℂ → ℝ} (hG : Measurable G)
    (hG1 : ∀ w, |G w| ≤ 1) {z : ℂ} (hz : z ∈ unitDisc) :
    IntegrableOn (fun w => η (pointPair z w) * G w * rho w) unitDisc := by
  have hz1 := mem_ball_zero_iff.mp hz
  set δ := (1 - ‖z‖) ^ 2 / 3
  have hz0 : 0 < 1 - ‖z‖ := by linarith
  have hδ : 0 < δ := by positivity
  have hbd : ∀ w ∈ unitDisc, ‖η (pointPair z w) * G w * rho w‖ ≤ 4 / δ ^ 2 := fun w hw => by
    by_cases h0 : η (pointPair z w) = 0
    · rw [h0, zero_mul, zero_mul, norm_zero]; positivity
    · have hlt : |pointPair z w| < 2 := by
        have := Function.mem_support.mpr h0
        rwa [η.support_eq, mem_ball, Real.dist_eq, sub_zero, hη] at this
      have hl := s8q_pp_loc le_rfl hz1 (mem_ball_zero_iff.mp hw) (le_of_lt (abs_lt.mp hlt).2)
      have hr := s8q_rho_le hδ (by show (1 - ‖z‖) ^ 2 / 3 ≤ 1 - ‖w‖ ^ 2; linarith)
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_of_nonneg (s8q_rho_nonneg w),
        abs_of_nonneg η.nonneg]
      have h1 := η.le_one (x := pointPair z w)
      have h2 := hG1 w
      have h3 := s8q_rho_nonneg w
      have h4 := η.nonneg (x := pointPair z w)
      calc η (pointPair z w) * |G w| * rho w ≤ 1 * 1 * (4 / δ ^ 2) := by gcongr
        _ = 4 / δ ^ 2 := by ring
  have hm : AEStronglyMeasurable (fun w => η (pointPair z w) * G w * rho w) (volume.restrict unitDisc) :=
    (((η.contDiff (n := 0)).continuous.measurable.comp (s8q_pp_meas z)).mul hG |>.mul
      gam_rho_measurable).aestronglyMeasurable
  exact Integrable.mono' (integrableOn_const (measure_ball_lt_top).ne) hm
    ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall hbd))

/-- Uniform first- and second-order Wirtinger bounds at `0` for `z ↦ ∫ k(z, w) f(w) dw`, over all integrable `f` with
`∫ |f| ≤ A` (the constants depend only on the kernel). -/
theorem s8q_F_bounds {k : ℂ → ℂ → ℂ} {S : Set ℂ} (hS : IsCompact S)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => k q.1 q.2) (ball 0 (1 / 2) ×ˢ univ))
    (hk0 : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w ∉ S, k z w = 0) (A : ℝ) :
    ∃ c₁ c₂ : ℝ, ∀ f : ℂ → ℂ, Integrable f → ∫ w, ‖f w‖ ≤ A →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ∫ w, k z w * f w) (ball 0 (1 / 2)) ∧
        ‖dz (fun z => ∫ w, k z w * f w) 0‖ ≤ c₁ ∧ ‖dz (dzbar fun z => ∫ w, k z w * f w) 0‖ ≤ c₂ := by
  have hU : IsOpen (ball (0 : ℂ) (1 / 2)) := isOpen_ball
  have h0U : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
  have hO : IsOpen (ball (0 : ℂ) (1 / 2) ×ˢ (univ : Set ℂ)) := hU.prod isOpen_univ
  obtain ⟨hkb, hkb0⟩ := s8q_pint_dbar_kernel hU hS hk hk0
  have hcoef : ∀ κ : ℂ → ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℂ × ℂ => κ q.1 q.2) (ball 0 (1 / 2) ×ˢ univ) →
      ∃ B, 0 ≤ B ∧ ∀ w ∈ S, ‖(fderiv ℝ (fun q : ℂ × ℂ => κ q.1 q.2) (0, w) (1, 0) -
        I * fderiv ℝ (fun q : ℂ × ℂ => κ q.1 q.2) (0, w) (I, 0)) / 2‖ ≤ B := fun κ hκ => by
    have hc := hκ.continuousOn_fderiv_of_isOpen hO (by simp)
    have hc0 : Continuous fun w => fderiv ℝ (fun q : ℂ × ℂ => κ q.1 q.2) (0, w) :=
      hc.comp_continuous (Continuous.prodMk_right 0) fun w => ⟨h0U, mem_univ w⟩
    have hcw : Continuous fun w => (fderiv ℝ (fun q : ℂ × ℂ => κ q.1 q.2) (0, w) (1, 0) -
        I * fderiv ℝ (fun q : ℂ × ℂ => κ q.1 q.2) (0, w) (I, 0)) / 2 :=
      ((hc0.clm_apply continuous_const).sub (continuous_const.mul (hc0.clm_apply continuous_const))).div_const _
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hcw.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun w hw => (hB w hw).trans (le_max_left _ _)⟩
  obtain ⟨B₁, hB₁0, hB₁⟩ := hcoef k hk
  obtain ⟨B₂, hB₂0, hB₂⟩ := hcoef (fun z w => (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
    I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2) hkb
  refine ⟨B₁ * A, B₂ * A, fun f hf hfA => ⟨s8q_pint_smooth hU hS hk hk0 hf.locallyIntegrable, ?_, ?_⟩⟩
  · rw [(s8q_pint_wirt hU hS hk hk0 hf h0U).1]
    refine (s8q_pint_bound hB₁0 hB₁ (fun w hw => ?_) hf).trans (mul_le_mul_of_nonneg_left hfA hB₁0)
    rw [s8q_pint_d0 hU hS hk0 h0U hw]
    simp
  · have hev : dzbar (fun z => ∫ w, k z w * f w) =ᶠ[𝓝 0] fun z => ∫ w,
        (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
          I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2 * f w := by
      filter_upwards [hU.mem_nhds h0U] with z hz
      exact (s8q_pint_wirt hU hS hk hk0 hf hz).2
    have e : dz (dzbar fun z => ∫ w, k z w * f w) 0 = dz (fun z => ∫ w,
        (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
          I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2 * f w) 0 := by
      unfold dz
      rw [hev.fderiv_eq]
    rw [e, (s8q_pint_wirt (k := fun z w => (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
      I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2) hU hS hkb hkb0 hf h0U).1]
    refine (s8q_pint_bound hB₂0 hB₂ (fun w hw => ?_) hf).trans (mul_le_mul_of_nonneg_left hfA hB₂0)
    rw [s8q_pint_d0 (k := fun z w => (fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (1, 0) +
      I * fderiv ℝ (fun q : ℂ × ℂ => k q.1 q.2) (z, w) (I, 0)) / 2) hU hS hkb0 h0U hw]
    simp

/-- Local representation of the point-pair operator near `0`: a parametric integral over `ℂ` with the kernel of
`s8q_ker` and the compactly supported density `1_S G ρ`. -/
theorem s8q_rep (η : ContDiffBump (0 : ℝ)) (hη : η.rOut = 2) (b : ContDiffBump (0 : ℂ)) (hb1 : b.rIn = 24 / 25)
    (hb2 : b.rOut = 49 / 50) (G : ℂ → ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1 / 2)) :
    ∫ w, (b w : ℂ) * (η (pointPair z w) : ℂ) *
        (((closedBall (0 : ℂ) (49 / 50)).indicator (fun w => G w * rho w) w : ℝ) : ℂ) =
      ((∫ w in unitDisc, η (pointPair z w) * G w * rho w : ℝ) : ℂ) := by
  obtain ⟨-, hk0, hk1⟩ := s8q_ker η hη b hb1 hb2
  rw [← integral_complex_ofReal, ← integral_indicator (show MeasurableSet unitDisc from measurableSet_ball)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  beta_reduce
  by_cases hw : w ∈ unitDisc
  · rw [Set.indicator_of_mem hw, hk1 z hz w hw]
    by_cases hS : w ∈ closedBall (0 : ℂ) (49 / 50)
    · rw [Set.indicator_of_mem hS]
      push_cast
      ring
    · have h0 := hk0 z hz w hS
      rw [hk1 z hz w hw] at h0
      have h0' : η (pointPair z w) = 0 := by exact_mod_cast h0
      rw [h0']
      simp
  · have hS : w ∉ closedBall (0 : ℂ) (49 / 50) := fun h => hw (by
      rw [mem_closedBall_zero_iff] at h
      exact mem_ball_zero_iff.mpr (by linarith))
    rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hS]
    simp

/-- Equivariance of `∂̄h`, `q h`, `Δ₀ h` for `Γ`-invariant smooth `h` (body of QA3, placed above Q4 which uses it). -/
theorem s8q_equiv_aux {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hhΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, h (mob g z) = h z) :
    ∀ g ∈ Γ, ∀ z ∈ unitDisc,
      dzbar h (mob g z) * conj (deriv (mob g) z) = dzbar h z ∧
        s7et_q h (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = s7et_q h z ∧
        laplace0 h (mob g z) = laplace0 h z := by
  intro g hg z hz
  have hs := hΓ.1 g hg
  have hD : ∀ w ∈ unitDisc, g 1 0 * w + g 1 1 ≠ 0 := fun w hw => fdD_denom_ne hs (mem_ball_zero_iff.mp hw)
  have hmd : ∀ w ∈ unitDisc, DifferentiableAt ℂ (mob g) w := fun w hw =>
    (wp_mob_hasDerivAt g (hD w hw)).differentiableAt
  have hmD : DifferentiableOn ℂ (mob g) unitDisc := fun w hw => (hmd w hw).differentiableWithinAt
  have hmaps : MapsTo (mob g) unitDisc unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr (fdD_mob_lt hs (mem_ball_zero_iff.mp hw))
  have hdne : ∀ w ∈ unitDisc, deriv (mob g) w ≠ 0 := fun w hw => by
    rw [gam_mob_deriv (hD w hw)]
    exact one_div_ne_zero (pow_ne_zero 2 (hD w hw))
  have diff (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ f w :=
    (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hhb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc := wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹ * dzbar h w) unitDisc := ha.mul hhb
  have hinv : ∀ w ∈ unitDisc, (fun u => h (mob g u)) =ᶠ[𝓝 w] h := fun w hw =>
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) fun u hu => hhΓ g hg u hu
  -- (a) `∂̄h` has weight `(0, 1)`
  have hA : ∀ w ∈ unitDisc, dzbar h (mob g w) * conj (deriv (mob g) w) = dzbar h w := fun w hw => by
    rw [← (s8q_chain_holo (hmd w hw) (diff h hh _ (hmaps hw))).2, s8q_dzbar_congr (hinv w hw)]
  -- `v = ρ⁻¹ ∂̄h` satisfies `v(γw) = v(w) γ'(w)`
  have hV : ∀ w ∈ unitDisc, (rho (mob g w) : ℂ)⁻¹ * dzbar h (mob g w) =
      ((rho w : ℂ)⁻¹ * dzbar h w) * deriv (mob g) w := fun w hw => by
    have hj := gam_rho_mob_jacobian hs (hD w hw)
    have hj' : (rho (mob g w) : ℂ) * (deriv (mob g) w * conj (deriv (mob g) w)) = rho w := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast hj
    have hρ0 := s8q_rho_ne (hmaps hw)
    have hc : conj (deriv (mob g) w) ≠ 0 := (map_ne_zero _).mpr (hdne w hw)
    have hd0 := hdne w hw
    rw [← hA w hw, ← hj']
    field_simp
  have hdd : DifferentiableAt ℂ (deriv (mob g)) z :=
    (hmD.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)
  have hdR : DifferentiableAt ℝ (deriv (mob g)) z := hdd.restrictScalars ℝ
  have hB : s7et_q h (mob g z) * conj (deriv (mob g) z) = deriv (mob g) z * s7et_q h z := by
    have e : (fun u => (rho (mob g u) : ℂ)⁻¹ * dzbar h (mob g u)) =ᶠ[𝓝 z]
        fun u => ((rho u : ℂ)⁻¹ * dzbar h u) * deriv (mob g) u :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hV
    have h1 := (s8q_chain_holo (H := fun w => (rho w : ℂ)⁻¹ * dzbar h w) (hmd z hz)
      (diff _ hv _ (hmaps hz))).2
    rw [s8q_dzbar_congr e, dzbar_mul (diff _ hv z hz) hdR, (cauchyRiemann_iff.1 hdd).2, mul_zero, zero_add] at h1
    show dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar h w) (mob g z) * conj (deriv (mob g) z) =
      deriv (mob g) z * dzbar (fun w => (rho w : ℂ)⁻¹ * dzbar h w) z
    rw [← h1]
  -- (c) `Δ₀h` is invariant
  have hC : laplace0 h (mob g z) = laplace0 h z := by
    have h2 : ContDiffOn ℝ 2 h unitDisc := hh.of_le (by simp)
    have hcomp := dz_dzbar_comp_holomorphic isOpen_ball isOpen_ball hmD hmaps h2 hz
    have e : dzbar (h ∘ mob g) =ᶠ[𝓝 z] dzbar h :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun u hu => s8q_dzbar_congr (hinv u hu)
    rw [s7g_f2_dz_congr e] at hcomp
    have hj := gam_rho_mob_jacobian hs (hD z hz)
    have hρ0 := s8q_rho_ne (hmaps hz)
    have hρz := s8q_rho_ne hz
    have hn : ((‖deriv (mob g) z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (norm_pos_iff.mpr (hdne z hz)) 2).ne'
    have hj' : (rho (mob g z) : ℂ) * ((‖deriv (mob g) z‖ ^ 2 : ℝ) : ℂ) = rho z := by exact_mod_cast hj
    show -((rho (mob g z) : ℂ)⁻¹ * dz (dzbar h) (mob g z)) = -((rho z : ℂ)⁻¹ * dz (dzbar h) z)
    rw [hcomp, ← hj']
    field_simp
  refine ⟨hA z hz, ?_, hC⟩
  have hd0 := hdne z hz
  field_simp
  exact hB

/-- **Q1 (STUB).** `Γ`-invariant smooth exhaustion cutoffs `χ_n` (invariant convolution of the indicator of the
`Γ`-saturation of `{|w| ≤ 1 - 1/(n+2)}` with a smooth point-pair bump): `0 ≤ χ_n ≤ 1`, compactly supported modulo `Γ`,
eventually `≡ 1` near each point, with uniform hyperbolic gradient and Laplacian bounds. -/
theorem s8q_cutoff {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) :
    ∃ χ : ℕ → ℂ → ℝ, ∃ C : ℝ,
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (χ n) unitDisc) ∧
      (∀ n, ∀ z ∈ unitDisc, 0 ≤ χ n z ∧ χ n z ≤ 1) ∧
      (∀ n, ∀ g ∈ Γ, ∀ z ∈ unitDisc, χ n (mob g z) = χ n z) ∧
      (∀ n, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ unitDisc ∧ ∀ z ∈ unitDisc, χ n z ≠ 0 → ∃ g ∈ Γ, mob g z ∈ K) ∧
      (∀ z ∈ unitDisc, ∀ᶠ n in atTop, ∀ᶠ w in 𝓝 z, χ n w = 1) ∧
      (∀ n, ∀ z ∈ unitDisc, ‖dz (fun w => (χ n w : ℂ)) z‖ ≤ C * Real.sqrt (rho z)) ∧
      (∀ n, ∀ z ∈ unitDisc, ‖laplace0 (fun w => (χ n w : ℂ)) z‖ ≤ C) := by
  haveI := hΓ.2
  obtain ⟨η, hη2, hη1⟩ : ∃ η : ContDiffBump (0 : ℝ), η.rOut = 2 ∧ η.rIn = 1 :=
    ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl, rfl⟩
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ContDiffBump (0 : ℂ), b.rIn = 24 / 25 ∧ b.rOut = 49 / 50 :=
    ⟨⟨24 / 25, 49 / 50, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hηs : ∀ u, η u ≠ 0 → u < 2 := fun u h => by
    have := Function.mem_support.mpr h
    rw [η.support_eq, mem_ball, Real.dist_eq, sub_zero, hη2] at this
    exact (abs_lt.mp this).2
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h0U : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
  -- the mass `M = ∫_𝔻 η(u(z, w)) ρ(w) dw` (independent of `z`)
  set M := ∫ w in unitDisc, η (pointPair 0 w) * (1 : ℝ) * rho w with hMdef
  have hM : ∀ z ∈ unitDisc, ∫ w in unitDisc, η (pointPair z w) * (1 : ℝ) * rho w = M := fun z hz => by
    obtain ⟨g, hg, hg0⟩ := s8q_su11_to hz
    have h := s8q_cov hg η (fun _ => 1) h0D
    rw [hg0] at h
    exact h
  have hMpos : 0 < M := by
    have hi := s8q_T_int η hη2 (G := fun _ => 1) measurable_const (fun _ => by simp) h0D
    have hsub : ball (0 : ℂ) (1 / 2) ⊆ unitDisc := ball_subset_ball (by norm_num)
    have h1 : ∀ w ∈ ball (0 : ℂ) (1 / 2), (4 : ℝ) ≤ η (pointPair 0 w) * 1 * rho w := fun w hw => by
      have hw' := mem_ball_zero_iff.mp hw
      have hw0 := norm_nonneg w
      have hd : 0 < 1 - ‖w‖ ^ 2 := by nlinarith
      have hp0 : 0 ≤ pointPair 0 w := by
        unfold pointPair
        exact div_nonneg (sq_nonneg _) (by simp only [norm_zero]; nlinarith)
      have hp1 : pointPair 0 w ≤ 1 := by
        unfold pointPair
        simp only [zero_sub, norm_neg, norm_zero]
        rw [div_le_one (by nlinarith)]
        nlinarith
      have he : η (pointPair 0 w) = 1 := η.one_of_mem_closedBall (by
        rw [mem_closedBall, Real.dist_eq, sub_zero, hη1, abs_le]; constructor <;> linarith)
      have hρ : 4 ≤ rho w := by
        show 4 ≤ 4 / (1 - ‖w‖ ^ 2) ^ 2
        rw [le_div_iff₀ (pow_pos hd 2)]
        nlinarith
      rw [he, one_mul, one_mul]
      exact hρ
    have h2 := setIntegral_mono_on (integrableOn_const (C := (4 : ℝ)) (measure_ball_lt_top).ne) (hi.mono_set hsub) measurableSet_ball h1
    have h3 : ∫ w in ball (0 : ℂ) (1 / 2), η (pointPair 0 w) * 1 * rho w ≤ M :=
      setIntegral_mono_set hi ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun w _ =>
        mul_nonneg (mul_nonneg η.nonneg zero_le_one) (s8q_rho_nonneg w))) (Eventually.of_forall hsub)
    rw [setIntegral_const, smul_eq_mul] at h2
    have h4 : 0 < volume.real (ball (0 : ℂ) (1 / 2)) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_ball_pos _ _ (by norm_num)).ne' measure_ball_lt_top.ne
    nlinarith
  -- the exhaustion `Sat n = Γ · {|w| ≤ r n}` and its indicator
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  set Sat : ℕ → Set ℂ := fun n => {w | ∃ g ∈ Γ, ‖mob g w‖ ≤ r n} with hSat
  set Ψ : ℕ → ℂ → ℝ := fun n => (Sat n).indicator (fun _ => (1 : ℝ)) with hΨ
  have hSm : ∀ n, MeasurableSet (Sat n) := fun n => by
    have e : Sat n = ⋃ g ∈ (Γ : Set SL2C), mob g ⁻¹' closedBall 0 (r n) := by
      ext w
      simp only [hSat, mem_setOf_eq, mem_iUnion, mem_preimage, mem_closedBall_zero_iff, SetLike.mem_coe,
        exists_prop]
    rw [e]
    exact MeasurableSet.biUnion fd_countable fun g _ => fd_measurable_mob g measurableSet_closedBall
  have hΨm : ∀ n, Measurable (Ψ n) := fun n => measurable_const.indicator (hSm n)
  have hΨ01 : ∀ n w, 0 ≤ Ψ n w ∧ Ψ n w ≤ 1 := fun n w => by
    simp only [hΨ, Set.indicator]
    split_ifs <;> norm_num
  have hΨ1 : ∀ n w, |Ψ n w| ≤ 1 := fun n w => by
    rw [abs_of_nonneg (hΨ01 n w).1]; exact (hΨ01 n w).2
  have hSinv : ∀ n, ∀ h ∈ Γ, ∀ w ∈ unitDisc, (mob h w ∈ Sat n ↔ w ∈ Sat n) := fun n h hh w hw => by
    have hD := fdD_denom_ne (hΓ.1 h hh) (mem_ball_zero_iff.mp hw)
    have hhw : ‖mob h w‖ < 1 := fdD_mob_lt (hΓ.1 h hh) (mem_ball_zero_iff.mp hw)
    constructor
    · rintro ⟨g, hg, hgr⟩
      refine ⟨g * h, Γ.mul_mem hg hh, ?_⟩
      rw [(fd_mob_mul hD (fdD_denom_ne (hΓ.1 g hg) hhw)).2]
      exact hgr
    · rintro ⟨g, hg, hgr⟩
      refine ⟨g * h⁻¹, Γ.mul_mem hg (Γ.inv_mem hh), ?_⟩
      have hi := fd_inv_step h hD
      have hg' : g 1 0 * mob h⁻¹ (mob h w) + g 1 1 ≠ 0 := by
        rw [hi.2]; exact fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp hw)
      rw [(fd_mob_mul hi.1 hg').2, hi.2]
      exact hgr
  have hΨinv : ∀ n, ∀ h ∈ Γ, ∀ w ∈ unitDisc, Ψ n (mob h w) = Ψ n w := fun n h hh w hw => by
    show (Sat n).indicator (fun _ => (1 : ℝ)) (mob h w) = (Sat n).indicator (fun _ => (1 : ℝ)) w
    by_cases hw' : w ∈ Sat n
    · rw [Set.indicator_of_mem hw', Set.indicator_of_mem ((hSinv n h hh w hw).mpr hw')]
    · rw [Set.indicator_of_notMem hw', Set.indicator_of_notMem fun h' => hw' ((hSinv n h hh w hw).mp h')]
  -- local smooth representation and uniform Wirtinger bounds
  obtain ⟨hk, hk0, -⟩ := s8q_ker η hη2 b hb1 hb2
  have hρS : IntegrableOn (fun w => rho w) (closedBall (0 : ℂ) (49 / 50)) := by
    refine Integrable.mono' (integrableOn_const (C := 4 / (1 - (49 / 50 : ℝ) ^ 2) ^ 2) (measure_closedBall_lt_top).ne)
      gam_rho_measurable.aestronglyMeasurable ((ae_restrict_iff' measurableSet_closedBall).mpr
        (Eventually.of_forall fun w hw => ?_))
    rw [Real.norm_of_nonneg (s8q_rho_nonneg w)]
    have hw' := mem_closedBall_zero_iff.mp hw
    exact s8q_rho_le (by norm_num) (by nlinarith [norm_nonneg w])
  obtain ⟨c₁, c₂, hc⟩ := s8q_F_bounds (k := fun z w => (b w : ℂ) * (η (pointPair z w) : ℂ)) (isCompact_closedBall (0 : ℂ) (49 / 50)) hk hk0
    (M⁻¹ * ∫ w, (closedBall (0 : ℂ) (49 / 50)).indicator (fun w => rho w) w)
  have hloc : ∀ n, ∀ y ∈ unitDisc, ∃ F : ℂ → ℂ, ∃ h : SL2C, IsSU11 h ∧ mob h y = 0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 (1 / 2)) ∧ ‖dz F 0‖ ≤ c₁ ∧ ‖dz (dzbar F) 0‖ ≤ c₂ ∧
      ∀ y' ∈ unitDisc, mob h y' ∈ ball (0 : ℂ) (1 / 2) →
        ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ) = F (mob h y') := by
    intro n y hy
    obtain ⟨g, hg, hg0⟩ := s8q_su11_to hy
    have hgi := isSU11_inv hg
    have hh0 : mob g⁻¹ y = 0 := by
      rw [← hg0]; exact (fd_inv_step g (fdD_denom_ne hg (mem_ball_zero_iff.mp h0D))).2
    set G : ℂ → ℝ := fun w => M⁻¹ * Ψ n (mob g w) with hG
    have hGm : Measurable G := measurable_const.mul ((hΨm n).comp (fd_measurable_mob g))
    have hGb : ∀ w, |G w| ≤ M⁻¹ := fun w => by
      simp only [hG]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hMpos)]
      exact mul_le_of_le_one_right (inv_pos.mpr hMpos).le (hΨ1 n _)
    set f : ℂ → ℂ := fun w => (((closedBall (0 : ℂ) (49 / 50)).indicator (fun w => G w * rho w) w : ℝ) : ℂ)
      with hf
    have hfS : IntegrableOn (fun w => G w * rho w) (closedBall (0 : ℂ) (49 / 50)) := by
      refine Integrable.mono' (hρS.const_mul M⁻¹) (hGm.mul gam_rho_measurable).aestronglyMeasurable
        (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8q_rho_nonneg w)]
      exact mul_le_mul_of_nonneg_right (hGb w) (s8q_rho_nonneg w)
    have hfi : Integrable f := (hfS.integrable_indicator measurableSet_closedBall).ofReal
    have hfA : ∫ w, ‖f w‖ ≤ M⁻¹ * ∫ w, (closedBall (0 : ℂ) (49 / 50)).indicator (fun w => rho w) w := by
      rw [← integral_const_mul]
      refine integral_mono hfi.norm ((hρS.integrable_indicator measurableSet_closedBall).const_mul _)
        fun w => ?_
      show ‖f w‖ ≤ M⁻¹ * (closedBall (0 : ℂ) (49 / 50)).indicator (fun w => rho w) w
      simp only [hf, Complex.norm_real, Real.norm_eq_abs]
      by_cases hw : w ∈ closedBall (0 : ℂ) (49 / 50)
      · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, abs_mul, abs_of_nonneg (s8q_rho_nonneg w)]
        exact mul_le_mul_of_nonneg_right (hGb w) (s8q_rho_nonneg w)
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, abs_zero, mul_zero]
    obtain ⟨hFs, hF1, hF2⟩ := hc f hfi hfA
    refine ⟨_, g⁻¹, hgi, hh0, hFs, hF1, hF2, fun y' hy' hU => ?_⟩
    have hrep := s8q_rep η hη2 b hb1 hb2 G hU
    have hyy : mob g (mob g⁻¹ y') = y' := by
      have := (fd_inv_step g⁻¹ (fdD_denom_ne hgi (mem_ball_zero_iff.mp hy'))).2
      rwa [inv_inv] at this
    have hx : mob g⁻¹ y' ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hgi (mem_ball_zero_iff.mp hy'))
    have hcov := s8q_cov hg η (Ψ n) hx
    rw [hyy] at hcov
    show _ = ∫ w, (b w : ℂ) * (η (pointPair (mob g⁻¹ y') w) : ℂ) *
      (((closedBall (0 : ℂ) (49 / 50)).indicator (fun w => G w * rho w) w : ℝ) : ℂ)
    rw [hrep, hcov]
    have e : (fun w => η (pointPair (mob g⁻¹ y') w) * G w * rho w) =
        fun w => M⁻¹ * (η (pointPair (mob g⁻¹ y') w) * Ψ n (mob g w) * rho w) := by
      funext w; simp only [hG]; ring
    rw [e, integral_const_mul]
  refine ⟨fun n z => M⁻¹ * ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w, max c₁ 0 + max c₂ 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- smoothness
  · intro n y hy
    obtain ⟨F, h, hh, hh0, hFs, -, -, hrel⟩ := hloc n y hy
    have hmd : DifferentiableOn ℂ (mob h) unitDisc := fun x hx =>
      (fd_mob_differentiableAt h (fdD_denom_ne hh (mem_ball_zero_iff.mp hx))).differentiableWithinAt
    have hVo : IsOpen (unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2)) :=
      hmd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
    have hyV : y ∈ unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2) := ⟨hy, by rw [mem_preimage, hh0]; exact h0U⟩
    have heq : (fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) =ᶠ[𝓝 y]
        F ∘ mob h := by
      filter_upwards [hVo.mem_nhds hyV] with x hx
      exact hrel x hx.1 hx.2
    have hFa : ContDiffAt ℝ (⊤ : ℕ∞) F (mob h y) := hFs.contDiffAt (isOpen_ball.mem_nhds hyV.2)
    have hmaC : ContDiffAt ℂ (⊤ : ℕ∞) (mob h) y :=
      (hmd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hy)
    have hma : ContDiffAt ℝ (⊤ : ℕ∞) (mob h) y := hmaC.restrict_scalars ℝ
    have hca := (hFa.comp y hma).congr_of_eventuallyEq heq
    have hre := Complex.reCLM.contDiff.contDiffAt.comp y hca
    refine (hre.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).contDiffWithinAt
    simp
  -- `0 ≤ χ ≤ 1`
  · intro n z hz
    have hT0 : 0 ≤ ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w :=
      setIntegral_nonneg measurableSet_ball fun w _ =>
        mul_nonneg (mul_nonneg η.nonneg (hΨ01 n w).1) (s8q_rho_nonneg w)
    have hT1 : ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w ≤ M :=
      (setIntegral_mono_on (s8q_T_int η hη2 (hΨm n) (hΨ1 n) hz)
        (s8q_T_int η hη2 (G := fun _ => 1) measurable_const (fun _ => by simp) hz) measurableSet_ball
        fun w _ => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΨ01 n w).2 η.nonneg)
          (s8q_rho_nonneg w)).trans_eq (hM z hz)
    have hMi := inv_pos.mpr hMpos
    refine ⟨mul_nonneg hMi.le hT0, ?_⟩
    calc M⁻¹ * ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w ≤ M⁻¹ * M :=
          mul_le_mul_of_nonneg_left hT1 hMi.le
      _ = 1 := inv_mul_cancel₀ hMpos.ne'
  -- `Γ`-invariance
  · intro n g hg z hz
    show M⁻¹ * ∫ w in unitDisc, η (pointPair (mob g z) w) * Ψ n w * rho w =
      M⁻¹ * ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w
    rw [s8q_cov (hΓ.1 g hg) η (Ψ n) hz]
    congr 1
    exact setIntegral_congr_fun measurableSet_ball fun w hw => by rw [hΨinv n g hg w hw]
  -- compact support modulo `Γ`
  · intro n
    have hr0 : 0 < 1 - r n := by linarith [hr1 n]
    refine ⟨{x | (1 - r n) ^ 2 ≤ 3 * (1 - ‖x‖ ^ 2)}, ?_, ?_, fun z hz hχ => ?_⟩
    · refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
        (isClosed_le continuous_const (continuous_const.mul (continuous_const.sub (continuous_norm.pow 2))))
        fun x hx => ?_
      have hx' : (1 - r n) ^ 2 ≤ 3 * (1 - ‖x‖ ^ 2) := hx
      refine mem_closedBall_zero_iff.mpr ?_
      nlinarith [norm_nonneg x, sq_nonneg (1 - r n)]
    · intro x hx
      have hx' : (1 - r n) ^ 2 ≤ 3 * (1 - ‖x‖ ^ 2) := hx
      refine mem_ball_zero_iff.mpr ?_
      by_contra hc
      push_neg at hc
      nlinarith [norm_nonneg x, pow_pos hr0 2]
    · have hT : ∫ w in unitDisc, η (pointPair z w) * Ψ n w * rho w ≠ 0 := right_ne_zero_of_mul hχ
      obtain ⟨w, hw, hne⟩ : ∃ w ∈ unitDisc, η (pointPair z w) * Ψ n w * rho w ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hT (setIntegral_eq_zero_of_forall_eq_zero hc)
      have hηw : η (pointPair z w) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
      have hΨw : Ψ n w ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
      have hwS : w ∈ Sat n := by
        by_contra hc
        exact hΨw (Set.indicator_of_notMem hc _)
      obtain ⟨g, hg, hgr⟩ := hwS
      refine ⟨g, hg, ?_⟩
      have hs := hΓ.1 g hg
      have hp : pointPair (mob g w) (mob g z) = pointPair z w := by
        rw [pointPair_mob_of_denominator_ne_zero g hs w z (fdD_denom_ne hs (mem_ball_zero_iff.mp hw))
          (fdD_denom_ne hs (mem_ball_zero_iff.mp hz)), pointPair_symm]
      exact s8q_pp_loc hgr (hr1 n) (fdD_mob_lt hs (mem_ball_zero_iff.mp hz))
        (by rw [hp]; exact (hηs _ hηw).le)
  -- eventually `≡ 1`
  · intro z hz
    have hz1 := mem_ball_zero_iff.mp hz
    set s := (1 + ‖z‖) / 2 with hsdef
    have hs1 : s < 1 := by rw [hsdef]; linarith
    set δ := (1 - s) ^ 2 / 3 with hδdef
    have hs0 : 0 < 1 - s := by linarith
    have hδ : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 / 3 := by
      rw [hδdef]
      have : 0 ≤ s := by rw [hsdef]; linarith [norm_nonneg z]
      nlinarith
    obtain ⟨N, hN⟩ := exists_nat_ge (2 / δ)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hrn : 1 - δ / 2 ≤ r n := by
      have h1 : 2 / δ ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
      have h2 : 2 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp h1
      have h3 : 1 / ((n : ℝ) + 2) ≤ δ / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      simp only [hr]
      linarith
    filter_upwards [ball_mem_nhds z (show 0 < (1 - ‖z‖) / 2 by linarith)] with y hy
    have hys : ‖y‖ ≤ s := by
      have := norm_le_norm_add_norm_sub' y z
      rw [mem_ball, dist_eq_norm] at hy
      rw [hsdef]
      linarith [norm_sub_rev y z]
    have hyD : y ∈ unitDisc := mem_ball_zero_iff.mpr (hys.trans_lt hs1)
    show M⁻¹ * ∫ w in unitDisc, η (pointPair y w) * Ψ n w * rho w = 1
    rw [setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball) (g := fun w => η (pointPair y w) * (1 : ℝ) * rho w)
      fun w hw => ?_, hM y hyD, inv_mul_cancel₀ hMpos.ne']
    by_cases h0 : η (pointPair y w) = 0
    · simp [h0]
    · have hl := s8q_pp_loc hys hs1 (mem_ball_zero_iff.mp hw) (hηs _ h0).le
      have hw2 : ‖w‖ ≤ 1 - δ / 2 := by
        by_contra hc
        push_neg at hc
        have h1 : 0 ≤ 1 - δ / 2 := by linarith
        nlinarith [mul_self_lt_mul_self h1 hc]
      have hwS : w ∈ Sat n := ⟨1, Γ.one_mem, by rw [gam_mob_one]; linarith⟩
      show η (pointPair y w) * (Sat n).indicator (fun _ => (1 : ℝ)) w * rho w = η (pointPair y w) * 1 * rho w
      rw [Set.indicator_of_mem hwS]
  -- gradient bound
  · intro n y hy
    obtain ⟨F, h, hh, hh0, hFs, hF1, -, hrel⟩ := hloc n y hy
    have hmd : DifferentiableOn ℂ (mob h) unitDisc := fun x hx =>
      (fd_mob_differentiableAt h (fdD_denom_ne hh (mem_ball_zero_iff.mp hx))).differentiableWithinAt
    have hVo : IsOpen (unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2)) :=
      hmd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
    have hyV : y ∈ unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2) := ⟨hy, by rw [mem_preimage, hh0]; exact h0U⟩
    have heq : (fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) =ᶠ[𝓝 y]
        F ∘ mob h := by
      filter_upwards [hVo.mem_nhds hyV] with x hx
      exact hrel x hx.1 hx.2
    have hFd : DifferentiableAt ℝ F (mob h y) :=
      (hFs.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hyV.2)
    have e1 : dz (fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) y =
        dz F (mob h y) * deriv (mob h) y := by
      rw [← (s8q_chain_holo (hmd.differentiableAt (isOpen_ball.mem_nhds hy)) hFd).1]
      unfold dz
      rw [heq.fderiv_eq]
      try rfl
    have hj := gam_rho_mob_jacobian hh (fdD_denom_ne hh (mem_ball_zero_iff.mp hy))
    have hρ0 : rho 0 = 4 := by show 4 / (1 - ‖(0 : ℂ)‖ ^ 2) ^ 2 = 4; simp
    rw [hh0, hρ0] at hj
    have hsq : Real.sqrt (rho y) = 2 * ‖deriv (mob h) y‖ := by
      rw [← hj, show (4 : ℝ) * ‖deriv (mob h) y‖ ^ 2 = (2 * ‖deriv (mob h) y‖) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    show ‖dz (fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) y‖ ≤ _
    rw [e1, norm_mul, hsq, hh0]
    have hd0 := norm_nonneg (deriv (mob h) y)
    have hm1 := le_max_left c₁ 0
    have hm2 := le_max_right c₂ 0
    have hm3 := le_max_right c₁ 0
    nlinarith [mul_le_mul_of_nonneg_right (hF1.trans hm1) hd0, mul_nonneg hm3 hd0, mul_nonneg hm2 hd0]
  -- Laplacian bound
  · intro n y hy
    obtain ⟨F, h, hh, hh0, hFs, -, hF2, hrel⟩ := hloc n y hy
    have hmd : DifferentiableOn ℂ (mob h) unitDisc := fun x hx =>
      (fd_mob_differentiableAt h (fdD_denom_ne hh (mem_ball_zero_iff.mp hx))).differentiableWithinAt
    have hVo : IsOpen (unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2)) :=
      hmd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ball
    have hyV : y ∈ unitDisc ∩ mob h ⁻¹' ball (0 : ℂ) (1 / 2) := ⟨hy, by rw [mem_preimage, hh0]; exact h0U⟩
    have hev : dzbar (fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) =ᶠ[𝓝 y]
        dzbar (F ∘ mob h) := by
      filter_upwards [hVo.mem_nhds hyV] with x hx
      refine s8q_dzbar_congr ?_
      filter_upwards [hVo.mem_nhds hx] with x' hx'
      exact hrel x' hx'.1 hx'.2
    have hcomp := dz_dzbar_comp_holomorphic hVo isOpen_ball (hmd.mono inter_subset_left)
      (fun x hx => hx.2) (hFs.of_le (by simp)) hyV
    have hj := gam_rho_mob_jacobian hh (fdD_denom_ne hh (mem_ball_zero_iff.mp hy))
    have hρ0 : rho 0 = 4 := by show 4 / (1 - ‖(0 : ℂ)‖ ^ 2) ^ 2 = 4; simp
    rw [hh0, hρ0] at hj
    have hd2 : ‖deriv (mob h) y‖ ^ 2 = rho y / 4 := by linarith
    have hρn := s8q_rho_ne hy
    show ‖-((rho y : ℂ)⁻¹ * dz (dzbar fun y' =>
      ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) y)‖ ≤ _
    have e : dz (dzbar fun y' => ((M⁻¹ * ∫ w in unitDisc, η (pointPair y' w) * Ψ n w * rho w : ℝ) : ℂ)) y =
        dz (dzbar (F ∘ mob h)) y := by
      unfold dz
      rw [hev.fderiv_eq]
    rw [e, hcomp, hd2, hh0]
    have e2 : -((rho y : ℂ)⁻¹ * (dz (dzbar F) 0 * ((rho y / 4 : ℝ) : ℂ))) = -(dz (dzbar F) 0 / 4) := by
      push_cast
      field_simp <;> ring
    rw [e2, norm_neg, norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hm1 := le_max_right c₁ 0
    have hm2 := le_max_left c₂ 0
    have hm4 := le_max_right c₂ 0
    linarith [hF2]

/-- Entries of an `SU(1,1)` matrix moving a point of `|w| ≤ s` into `|γ w| ≤ r` are bounded
(`|cw + d|² (1 - |γ w|²) = 1 - |w|²`). -/
theorem s8d_entries {g : SL2C} (hg : IsSU11 g) {w : ℂ} {s r : ℝ} (hs : s < 1) (hr : r < 1) (hw : ‖w‖ ≤ s)
    (hgw : ‖mob g w‖ ≤ r) : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ √(1 / (1 - r ^ 2)) / (1 - s) := by
  have hdet := fd_su11_det hg
  have hw1 : ‖w‖ < 1 := hw.trans_lt hs
  have hD := fdD_denom_ne hg hw1
  have hid := fd_su11_identity hg w
  have hm : mob g w = (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1) := rfl
  have hDpos : 0 < ‖g 1 0 * w + g 1 1‖ := norm_pos_iff.mpr hD
  have hN : ‖g 0 0 * w + g 0 1‖ = ‖mob g w‖ * ‖g 1 0 * w + g 1 1‖ := by
    rw [hm, norm_div, div_mul_cancel₀ _ hDpos.ne']
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hgw
  have hv2 : ‖mob g w‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgw 2
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hkey : ‖g 1 0 * w + g 1 1‖ ^ 2 * (1 - r ^ 2) ≤ 1 := by
    have e : ‖g 1 0 * w + g 1 1‖ ^ 2 * (1 - ‖mob g w‖ ^ 2) = 1 - ‖w‖ ^ 2 := by
      rw [hN, mul_pow] at hid
      linarith
    nlinarith [sq_nonneg ‖g 1 0 * w + g 1 1‖, sq_nonneg ‖w‖]
  have hDle : ‖g 1 0 * w + g 1 1‖ ≤ √(1 / (1 - r ^ 2)) := by
    have h2 : ‖g 1 0 * w + g 1 1‖ ^ 2 ≤ 1 / (1 - r ^ 2) := (le_div_iff₀ hr2).mpr hkey
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hb : ‖g 0 1‖ ≤ ‖g 0 0‖ := by nlinarith [norm_nonneg (g 0 1), norm_nonneg (g 0 0)]
  have h11 : ‖g 1 1‖ ≤ ‖g 1 0 * w + g 1 1‖ + ‖g 1 0‖ * ‖w‖ := by
    have e : g 1 1 = (g 1 0 * w + g 1 1) - g 1 0 * w := by ring
    calc ‖g 1 1‖ = ‖(g 1 0 * w + g 1 1) - g 1 0 * w‖ := by rw [← e]
      _ ≤ ‖g 1 0 * w + g 1 1‖ + ‖g 1 0 * w‖ := norm_sub_le _ _
      _ = ‖g 1 0 * w + g 1 1‖ + ‖g 1 0‖ * ‖w‖ := by rw [norm_mul]
  have hn10 : ‖g 1 0‖ = ‖g 0 1‖ := by rw [hg.1, Complex.norm_conj]
  have hn11 : ‖g 1 1‖ = ‖g 0 0‖ := by rw [hg.2, Complex.norm_conj]
  rw [hn10, hn11] at h11
  have ha : ‖g 0 0‖ * (1 - s) ≤ √(1 / (1 - r ^ 2)) := by
    nlinarith [mul_le_mul hb hw (norm_nonneg _) (norm_nonneg _)]
  have hA : ‖g 0 0‖ ≤ √(1 / (1 - r ^ 2)) / (1 - s) := (le_div_iff₀ (by linarith)).mpr ha
  intro i j
  fin_cases i <;> fin_cases j
  · exact hA
  · exact hb.trans hA
  · show ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ _
    rw [hn10]
    exact hb.trans hA
  · show ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ≤ _
    rw [hn11]
    exact hA

/-- Local finiteness: only finitely many `a ∈ Γ` move a point of `|w| ≤ s` into `|a w| ≤ r`. -/
theorem s8d_locfin {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {s r : ℝ} (hs : s < 1) (hr : r < 1) :
    {a : (fun g : SL2C => mob g) '' (Γ : Set SL2C) | ∃ w : ℂ, ‖w‖ ≤ s ∧ ‖(a : ℂ → ℂ) w‖ ≤ r}.Finite := by
  haveI : DiscreteTopology Γ := hΓ.2
  have hfin := fd_bounded_finite (Γ := Γ) (√(1 / (1 - r ^ 2)) / (1 - s))
  refine ((hfin.image (fun g : SL2C => mob g)).preimage (Set.injOn_of_injective Subtype.val_injective)).subset ?_
  rintro ⟨_, g, hg, rfl⟩ ⟨w, hw, hgw⟩
  exact ⟨g, ⟨hg, s8d_entries (hΓ.1 g hg) hs hr hw hgw⟩, rfl⟩

/-- A finite set of `a ∈ Γ` outside of which every `a` moves `|w| ≤ s` off `|a w| ≤ r`. -/
theorem s8d_local {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {s r : ℝ} (hs : s < 1) (hr : r < 1) :
    ∃ T : Finset ((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∀ b, b ∉ T → ∀ w : ℂ, ‖w‖ ≤ s →
      r < ‖(b : ℂ → ℂ) w‖ := by
  have hfin := s8d_locfin hΓ hs hr
  refine ⟨hfin.toFinset, fun b hb w hw => ?_⟩
  by_contra hc
  push_neg at hc
  exact hb (hfin.mem_toFinset.mpr ⟨w, hw, hc⟩)

/-- Right multiplication by `h ∈ Γ` permutes the Möbius image set `A` of `Γ`. -/
theorem s8d_perm (Γ : Subgroup SL2C) {h : SL2C} (hh : h ∈ Γ) :
    ∃ e : ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) ≃ ((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∃ g ∈ Γ, (b : ℂ → ℂ) = mob g ∧
        ((e b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) : ℂ → ℂ) = mob (g * h) := by
  classical
  let rep : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → SL2C := fun b => Classical.choose b.2
  have hrep : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), rep b ∈ Γ ∧ mob (rep b) = b.1 :=
    fun b => Classical.choose_spec b.2
  let φ : ∀ k : SL2C, k ∈ Γ → ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) →
      ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    fun k hk b => ⟨mob (rep b * k), rep b * k, Γ.mul_mem (hrep b).1 hk, rfl⟩
  have hφ : ∀ (k : SL2C) (hk : k ∈ Γ) (k' : SL2C) (hk' : k' ∈ Γ) b,
      φ k' hk' (φ k hk b) = φ (k * k') (Γ.mul_mem hk hk') b := by
    intro k hk k' hk' b
    apply Subtype.ext
    show mob (rep (φ k hk b) * k') = mob (rep b * (k * k'))
    have h1 : mob (rep b * k) = mob (rep (φ k hk b)) := (hrep (φ k hk b)).2.symm
    rcases fd_mob_eq h1 with e | e
    · rw [e, mul_assoc]
    · rw [e, neg_mul, fd_mob_neg, mul_assoc]
  have hcongr : ∀ (k k' : SL2C) (hk : k ∈ Γ) (hk' : k' ∈ Γ) b, k = k' → φ k hk b = φ k' hk' b := by
    rintro k _ _ _ b rfl
    rfl
  have hone : ∀ b, φ 1 Γ.one_mem b = b := fun b =>
    Subtype.ext (by show mob (rep b * 1) = b.1; rw [mul_one]; exact (hrep b).2)
  refine ⟨⟨φ h hh, φ h⁻¹ (Γ.inv_mem hh), fun b => ?_, fun b => ?_⟩,
    fun b => ⟨rep b, (hrep b).1, (hrep b).2.symm, rfl⟩⟩
  · exact (hφ h hh h⁻¹ (Γ.inv_mem hh) b).trans ((hcongr _ _ (Γ.mul_mem hh (Γ.inv_mem hh)) Γ.one_mem b
      (mul_inv_cancel h)).trans (hone b))
  · exact (hφ h⁻¹ (Γ.inv_mem hh) h hh b).trans ((hcongr _ _ (Γ.mul_mem (Γ.inv_mem hh) hh) Γ.one_mem b
      (inv_mul_cancel h)).trans (hone b))

/-- Sums over `A` are `Γ`-invariant: `∑_a φ(a(h w)) = ∑_a φ(a w)` on `𝔻`. -/
theorem s8d_sum_inv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) (φ : ℂ → ℝ) {h : SL2C} (hh : h ∈ Γ) {w : ℂ}
    (hw : w ∈ unitDisc) :
    ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), φ ((b : ℂ → ℂ) (mob h w)) =
      ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), φ ((b : ℂ → ℂ) w) := by
  obtain ⟨e, he⟩ := s8d_perm Γ hh
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  rw [← e.tsum_eq (fun b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => φ ((b : ℂ → ℂ) w))]
  refine tsum_congr fun b => ?_
  obtain ⟨g, hg, hb, heb⟩ := he b
  rw [hb, heb, (fd_mob_mul (fdD_denom_ne (hΓ.1 h hh) hw1)
    (fdD_denom_ne (hΓ.1 g hg) (fdD_mob_lt (hΓ.1 h hh) hw1))).2]

/-- Möbius maps of `SU(1,1)` are holomorphic on `𝔻`. -/
theorem s8d_mob_hol {g : SL2C} (hg : IsSU11 g) : DifferentiableOn ℂ (mob g) unitDisc := fun z hz =>
  (fd_mob_differentiableAt g (fdD_denom_ne hg (mem_ball_zero_iff.mp hz))).differentiableWithinAt

/-- Möbius maps of `SU(1,1)` are smooth on `𝔻`. -/
theorem s8d_mob_cd {g : SL2C} (hg : IsSU11 g) : ContDiffOn ℝ 1 (mob g) unitDisc := by
  exact ((s8d_mob_hol hg).contDiffOn isOpen_ball).restrict_scalars ℝ

/-- Near each point of `𝔻`, a sum over `A` of terms vanishing when `|a w| ≥ r` (`r < 1`) is a finite sum. -/
theorem s8d_tsum_local {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {E : Type*} [NormedAddCommGroup E]
    {f : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) → ℂ → E} {r : ℝ} (hr : r < 1)
    (hf : ∀ (b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) (w : ℂ), r ≤ ‖(b : ℂ → ℂ) w‖ → f b w = 0) {w₀ : ℂ} (hw₀ : w₀ ∈ unitDisc) :
    ∃ T : Finset ((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∃ s : ℝ, ‖w₀‖ < s ∧ s < 1 ∧
      ∀ w : ℂ, ‖w‖ ≤ s → (∀ b, b ∉ T → f b w = 0) ∧
        ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), f b w = ∑ b ∈ T, f b w := by
  have h1 : ‖w₀‖ < 1 := mem_ball_zero_iff.mp hw₀
  obtain ⟨T, hT⟩ := s8d_local hΓ (s := (‖w₀‖ + 1) / 2) (by linarith) hr
  refine ⟨T, (‖w₀‖ + 1) / 2, by linarith, by linarith, fun w hw => ?_⟩
  have hz : ∀ b, b ∉ T → f b w = 0 := fun b hb => hf b w (hT b hb w hw).le
  exact ⟨hz, tsum_eq_sum hz⟩

/-- `S(w) = ∑_a θ(a w)` is `C¹` on `𝔻` (locally a finite sum). -/
theorem s8d_S_cd {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {θ : ℂ → ℝ} (hθ : ContDiff ℝ 1 θ) {r : ℝ} (hr : r < 1)
    (hθ0 : ∀ x : ℂ, r ≤ ‖x‖ → θ x = 0) :
    ContDiffOn ℝ 1 (fun w => ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) w))
      unitDisc := by
  refine contDiffOn_of_locally_contDiffOn fun w₀ hw₀ => ?_
  obtain ⟨T, s, hs0, -, hT⟩ := s8d_tsum_local hΓ (f := fun b w => θ ((b : ℂ → ℂ) w)) hr
    (fun b w h => hθ0 _ h) hw₀
  refine ⟨ball 0 s, isOpen_ball, mem_ball_zero_iff.mpr hs0, ?_⟩
  have hsum : ContDiffOn ℝ 1 (fun w => ∑ b ∈ T, θ ((b : ℂ → ℂ) w)) unitDisc := by
    refine ContDiffOn.sum fun b _ => ?_
    obtain ⟨g, hg, hb⟩ := b.2
    rw [← hb]
    exact hθ.comp_contDiffOn (s8d_mob_cd (hΓ.1 g hg))
  exact (hsum.mono inter_subset_left).congr fun w hw => (hT w (mem_ball_zero_iff.mp hw.2).le).2

/-- The normalizing denominator `s + 1 - h(s)`, `h(s) = smoothTransition(2s - 1)`: `≥ ½` for `s ≥ 0`, `= s` for
`s ≥ 1`. -/
theorem s8d_den {s : ℝ} (hs : 0 ≤ s) :
    1 / 2 ≤ s + 1 - Real.smoothTransition (2 * s - 1) ∧
      (1 ≤ s → s + 1 - Real.smoothTransition (2 * s - 1) = s) := by
  refine ⟨?_, fun h1 => ?_⟩
  · by_cases h : 2 * s - 1 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos h]
      linarith
    · have := Real.smoothTransition.le_one (2 * s - 1)
      push_neg at h
      linarith
  · rw [Real.smoothTransition.one_of_one_le (by linarith)]
    ring

/-- The partition function `ψ = θ / (S + 1 - h(S))` is `C¹` on `𝔻`. -/
theorem s8d_psi_cd {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {θ : ℂ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθnn : ∀ x, 0 ≤ θ x) {r : ℝ} (hr : r < 1) (hθ0 : ∀ x : ℂ, r ≤ ‖x‖ → θ x = 0) :
    ContDiffOn ℝ 1 (fun x => θ x /
      ((∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) x)) + 1 -
        Real.smoothTransition (2 * (∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) x))
          - 1))) unitDisc := by
  have hS := s8d_S_cd hΓ hθ hr hθ0
  have hS0 : ∀ x, 0 ≤ ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) x) :=
    fun x => tsum_nonneg fun b => hθnn _
  refine hθ.contDiffOn.div ((hS.add contDiffOn_const).sub
    (Real.smoothTransition.contDiff.comp_contDiffOn ((contDiffOn_const.mul hS).sub contDiffOn_const)))
    fun x _ => ?_
  have := (s8d_den (hS0 x)).1
  exact ne_of_gt (by linarith)

/-- A function `C¹` on `𝔻` vanishing off `|x| < r` (`r < 1`) is `C¹` on `ℂ`. -/
theorem s8d_cd_ext {f : ℂ → ℂ} {r : ℝ} (hr : r < 1) (hf : ContDiffOn ℝ 1 f unitDisc)
    (h0 : ∀ x : ℂ, r ≤ ‖x‖ → f x = 0) : ContDiff ℝ 1 f := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : ‖x‖ < 1
  · exact hf.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx))
  · have hrx : r < ‖x‖ := by push_neg at hx; linarith
    have e : f =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hrx] with y hy
      exact h0 y (le_of_lt hy)
    exact contDiffAt_const.congr_of_eventuallyEq e

/-- `∂` depends only on the germ. -/
theorem s8d_dz_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dz f z = dz g z := by
  unfold dz
  rw [h.fderiv_eq]

/-- `|γ'|²` as a complex number. -/
theorem s8d_normsq (d : ℂ) : ((‖d‖ ^ 2 : ℝ) : ℂ) = d * conj d := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Weight of the divergence: `|γ'(w)|² (∂̄P + ∂Q)(γ w) = (∂̄P + ∂Q)(w)` for `P` of weight `(-1, 0)` and `Q` of
weight `(0, -1)`. -/
theorem s8d_wt_D {g : SL2C} (hg : IsSU11 g) {P Q : ℂ → ℂ} (hP : ContDiffOn ℝ 1 P unitDisc)
    (hQ : ContDiffOn ℝ 1 Q unitDisc) (hPg : ∀ z ∈ unitDisc, P (mob g z) * deriv (mob g) z = P z)
    (hQg : ∀ z ∈ unitDisc, Q (mob g z) * conj (deriv (mob g) z) = Q z) {w : ℂ} (hw : w ∈ unitDisc) :
    ((‖deriv (mob g) w‖ ^ 2 : ℝ) : ℂ) * (dzbar P (mob g w) + dz Q (mob g w)) = dzbar P w + dz Q w := by
  have hdm := s8d_mob_hol hg
  have hmw : DifferentiableAt ℂ (mob g) w := hdm.differentiableAt (isOpen_ball.mem_nhds hw)
  have hm'w : DifferentiableAt ℂ (deriv (mob g)) w :=
    (hdm.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hw)
  have hmw' : mob g w ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hg (mem_ball_zero_iff.mp hw))
  have hPd : DifferentiableAt ℝ P (mob g w) :=
    (hP.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hmw')
  have hQd : DifferentiableAt ℝ Q (mob g w) :=
    (hQ.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hmw')
  have eP : P =ᶠ[𝓝 w] fun z => P (mob g z) * deriv (mob g) z := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz using (hPg z hz).symm
  have eQ : Q =ᶠ[𝓝 w] fun z => Q (mob g z) * conj (deriv (mob g) z) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz using (hQg z hz).symm
  have hPc : DifferentiableAt ℝ (fun z => P (mob g z)) w := hPd.comp w (hmw.restrictScalars ℝ)
  have hQc : DifferentiableAt ℝ (fun z => Q (mob g z)) w := hQd.comp w (hmw.restrictScalars ℝ)
  have hd' : DifferentiableAt ℝ (deriv (mob g)) w := hm'w.restrictScalars ℝ
  have hdc : DifferentiableAt ℝ (fun z => conj (deriv (mob g) z)) w := hd'.star
  have h0 : dzbar (deriv (mob g)) w = 0 := (cauchyRiemann_iff.1 hm'w).2
  have h0' : dz (fun z => conj (deriv (mob g) z)) w = 0 := by rw [s7g_f2_dz_conj, h0, map_zero]
  have hcP := s8q_chain_holo hmw hPd
  have hcQ := s8q_chain_holo hmw hQd
  rw [s8q_dzbar_congr eP, s8d_dz_congr eQ, dzbar_mul hPc hd', dz_mul hQc hdc, h0, h0', hcP.2, hcQ.1,
    s8d_normsq]
  ring

/-- Weight of the cut-off term: `|γ'|² (∂̄ψ P + ∂ψ Q)(γ w) = ∂̄(ψ∘γ) P(w) + ∂(ψ∘γ) Q(w)`. -/
theorem s8d_wt_psi {g : SL2C} (hg : IsSU11 g) {P Q ψ : ℂ → ℂ}
    (hPg : ∀ z ∈ unitDisc, P (mob g z) * deriv (mob g) z = P z)
    (hQg : ∀ z ∈ unitDisc, Q (mob g z) * conj (deriv (mob g) z) = Q z) {w : ℂ} (hw : w ∈ unitDisc)
    (hψ : DifferentiableAt ℝ ψ (mob g w)) :
    dzbar (fun z => ψ (mob g z)) w * P w + dz (fun z => ψ (mob g z)) w * Q w =
      ((‖deriv (mob g) w‖ ^ 2 : ℝ) : ℂ) * (dzbar ψ (mob g w) * P (mob g w) + dz ψ (mob g w) * Q (mob g w)) := by
  have hmw : DifferentiableAt ℂ (mob g) w := (s8d_mob_hol hg).differentiableAt (isOpen_ball.mem_nhds hw)
  have hc := s8q_chain_holo hmw hψ
  rw [hc.1, hc.2, ← hPg w hw, ← hQg w hw, s8d_normsq]
  ring

/-- Wirtinger derivatives of a `C¹` function on `𝔻` are continuous on `𝔻`. -/
theorem s8d_dcont {P : ℂ → ℂ} (hP : ContDiffOn ℝ 1 P unitDisc) :
    ContinuousOn (dzbar P) unitDisc ∧ ContinuousOn (dz P) unitDisc := by
  have hfd := hP.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have h1 : ContinuousOn (fun x => fderiv ℝ P x 1) unitDisc := hfd.clm_apply continuousOn_const
  have hI : ContinuousOn (fun x => fderiv ℝ P x I) unitDisc := hfd.clm_apply continuousOn_const
  constructor
  · show ContinuousOn (fun x => (fderiv ℝ P x 1 + I * fderiv ℝ P x I) / 2) unitDisc
    exact (h1.add (continuousOn_const.mul hI)).div_const 2
  · show ContinuousOn (fun x => (fderiv ℝ P x 1 - I * fderiv ℝ P x I) / 2) unitDisc
    exact (h1.sub (continuousOn_const.mul hI)).div_const 2

/-- `γ'` is continuous on `𝔻`. -/
theorem s8d_deriv_cont {g : SL2C} (hg : IsSU11 g) : ContinuousOn (deriv (mob g)) unitDisc :=
  ((s8d_mob_hol hg).deriv isOpen_ball).continuousOn

/-- Unfolding for continuous densities supported in `|x| < r`: the periodization
`∑_a |a'|² h ∘ a` is integrable on `F`, with integral `∫_𝔻 h`. -/
theorem s8d_unfold {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {h : ℂ → ℂ} {r : ℝ} (hr : r < 1)
    (hc : ContinuousOn h unitDisc) (h0 : ∀ x : ℂ, r ≤ ‖x‖ → h x = 0) :
    IntegrableOn (fun w => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)) (fundDomainOn Γ unitDisc) ∧
      ((∫ w in fundDomainOn Γ unitDisc, ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
        (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)) = ∫ w in unitDisc, h w) ∧
      IntegrableOn h unitDisc := by
  haveI : DiscreteTopology Γ := hΓ.2
  haveI : Countable ((fun g : SL2C => mob g) '' (Γ : Set SL2C)) :=
    (fd_countable (Γ := Γ)).image _ |>.to_subtype
  have hF := s8w_fundD hΓ
  have hout : ∀ x : ℂ, x ∉ unitDisc → h x = 0 := fun x hx => by
    have : ¬ ‖x‖ < 1 := fun h' => hx (mem_ball_zero_iff.mpr h')
    exact h0 x (by push_neg at this; linarith)
  have hpw : unitDisc.piecewise h 0 = h := by
    funext x
    by_cases hx : x ∈ unitDisc
    · exact piecewise_eq_of_mem _ _ _ hx
    · rw [piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, hout x hx]
  have hmeas : Measurable h := by
    rw [← hpw]
    exact hc.measurable_piecewise continuousOn_const measurableSet_ball
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hc.mono (closedBall_subset_ball hr))
  have hb : ∀ x, ‖h x‖ ≤ max M 0 := fun x => by
    by_cases hx : ‖x‖ ≤ r
    · exact (hM x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)
    · rw [h0 x (by push_neg at hx; exact hx.le), norm_zero]
      exact le_max_right _ _
  have hint : IntegrableOn h unitDisc :=
    Measure.integrableOn_of_bounded measure_ball_lt_top.ne hmeas.aestronglyMeasurable (Eventually.of_forall hb)
  have hterm : ∀ a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      Measurable fun w => (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w) := fun a =>
    ((measurable_deriv _).norm.pow_const 2).smul (hmeas.comp (gam_action_measurable Γ a))
  have hlin : ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∫⁻ w in fundDomainOn Γ unitDisc,
      ‖(‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)‖ₑ = ∫⁻ w in unitDisc, ‖h w‖ₑ := by
    rw [fdD_unfold hΓ hF (fun x => ‖h x‖ₑ)]
    refine tsum_congr fun a => lintegral_congr fun w => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (by positivity)]
  have hfin : ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ∫⁻ w in fundDomainOn Γ unitDisc,
      ‖(‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)‖ₑ ≠ ⊤ := by
    rw [hlin]
    exact hint.2.ne
  have hI := integral_tsum (fun a => (hterm a).aestronglyMeasurable) hfin
  have hsum := fdD_hasSum_integral_unfold hΓ hF hint
  refine ⟨?_, hI.trans hsum.tsum_eq, hint⟩
  -- integrability: locally finite, hence continuous on `𝔻`, and dominated by the summed enorms
  have hzero : ∀ (b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) (w : ℂ), r ≤ ‖(b : ℂ → ℂ) w‖ →
      (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • h ((b : ℂ → ℂ) w) = 0 := fun b w hbw => by rw [h0 _ hbw, smul_zero]
  have hcont : ContinuousOn (fun w => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)) unitDisc := by
    refine continuousOn_of_locally_continuousOn fun w₀ hw₀ => ?_
    obtain ⟨T, s, hs0, -, hT⟩ := s8d_tsum_local hΓ hr hzero hw₀
    refine ⟨ball 0 s, isOpen_ball, mem_ball_zero_iff.mpr hs0, ?_⟩
    have hfs : ContinuousOn (fun w => ∑ b ∈ T, (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • h ((b : ℂ → ℂ) w)) unitDisc := by
      refine continuousOn_finset_sum _ fun b _ => ?_
      obtain ⟨g, hg, hb⟩ := b.2
      rw [← hb]
      have hs := hΓ.1 g hg
      refine (((s8d_deriv_cont hs).norm).pow 2).smul (hc.comp (s8d_mob_cd hs).continuousOn fun z hz => ?_)
      exact mem_ball_zero_iff.mpr (fdD_mob_lt hs (mem_ball_zero_iff.mp hz))
    exact (hfs.mono inter_subset_left).congr fun w hw => (hT w (mem_ball_zero_iff.mp hw.2).le).2
  refine ⟨(hcont.mono hF.2.1).aestronglyMeasurable hF.1, ?_⟩
  show (∫⁻ w in fundDomainOn Γ unitDisc, ‖∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)‖ₑ) < ⊤
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun w => ∑' a : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ‖(‖deriv (a : ℂ → ℂ) w‖ ^ 2) • h ((a : ℂ → ℂ) w)‖ₑ) ?_) ?_
  · filter_upwards [ae_restrict_mem hF.1] with w hw
    obtain ⟨T, s, hs0, -, hT⟩ := s8d_tsum_local hΓ hr hzero (hF.2.1 hw)
    rw [(hT w hs0.le).2]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  · rw [lintegral_tsum fun a => (hterm a).enorm.aemeasurable]
    exact lt_top_iff_ne_top.mpr hfin

/-- `∫_ℂ Du(x) v = 0` for `u ∈ C¹_c(ℂ)` (integration by parts against `1`). -/
theorem s8d_plane0 {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) (v : ℂ) :
    Integrable (fun x => fderiv ℝ u x v) ∧ ∫ x, fderiv ℝ u x v = 0 := by
  have hi : Integrable (fun x => fderiv ℝ u x v) :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.fderiv_apply (𝕜 := ℝ) v)
  refine ⟨hi, ?_⟩
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun _ : ℂ => (1 : ℝ)) (g := u) (v := v)
    (by simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_smul]
        exact integrable_zero _ _ _)
    (by simpa only [one_smul] using hi)
    (by simpa only [one_smul] using hu.continuous.integrable_of_hasCompactSupport hcs)
    (fun x _ => differentiableAt_const _) (fun x _ => hu.differentiable one_ne_zero x)
  simp only [one_smul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_smul,
    integral_zero, neg_zero] at h
  exact h

/-- Plane divergence theorem: `∫_ℂ (∂̄u + ∂v) = 0` for `u, v ∈ C¹_c(ℂ)`. -/
theorem s8d_plane {u v : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (hcu : HasCompactSupport u) (hv : ContDiff ℝ 1 v)
    (hcv : HasCompactSupport v) : ∫ x, (dzbar u x + dz v x) = 0 := by
  obtain ⟨hu1, ku1⟩ := s8d_plane0 hu hcu 1
  obtain ⟨huI, kuI⟩ := s8d_plane0 hu hcu I
  obtain ⟨hv1, kv1⟩ := s8d_plane0 hv hcv 1
  obtain ⟨hvI, kvI⟩ := s8d_plane0 hv hcv I
  have Iu : Integrable (fun x => dzbar u x) := by
    show Integrable (fun x => (fderiv ℝ u x 1 + I * fderiv ℝ u x I) / 2)
    exact (hu1.add (huI.const_mul I)).div_const 2
  have Iv : Integrable (fun x => dz v x) := by
    show Integrable (fun x => (fderiv ℝ v x 1 - I * fderiv ℝ v x I) / 2)
    exact (hv1.sub (hvI.const_mul I)).div_const 2
  rw [integral_add Iu Iv]
  show (∫ x, (fderiv ℝ u x 1 + I * fderiv ℝ u x I) / 2) + ∫ x, (fderiv ℝ v x 1 - I * fderiv ℝ v x I) / 2 = 0
  rw [integral_div, integral_div, integral_add hu1 (huI.const_mul I), integral_sub hv1 (hvI.const_mul I),
    integral_const_mul, integral_const_mul, ku1, kuI, kv1, kvI]
  simp

/-- Wirtinger derivatives of a constant vanish. -/
theorem s8d_d_const (c : ℂ) (w : ℂ) : dzbar (fun _ : ℂ => c) w = 0 ∧ dz (fun _ : ℂ => c) w = 0 := by
  unfold dzbar dz
  simp [fderiv_const]

/-- Wirtinger derivatives of a finite sum. -/
theorem s8d_d_sum {ι : Type*} {T : Finset ι} {F : ι → ℂ → ℂ} {w : ℂ}
    (h : ∀ i ∈ T, DifferentiableAt ℝ (F i) w) :
    dzbar (fun z => ∑ i ∈ T, F i z) w = ∑ i ∈ T, dzbar (F i) w ∧
      dz (fun z => ∑ i ∈ T, F i z) w = ∑ i ∈ T, dz (F i) w := by
  unfold dzbar dz
  rw [fderiv_fun_sum h]
  simp only [ContinuousLinearMap.sum_apply]
  constructor
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- Points whose orbit meets `|x| < ρ₁` have `S = ∑_a θ ∘ a ≥ 1` nearby (`θ ≡ 1` on `|x| ≤ ρ₁`). -/
theorem s8d_ge {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {θ : ℂ → ℝ} (hθnn : ∀ x, 0 ≤ θ x) {ρ₁ ρ₂ : ℝ}
    (hρ₂ : ρ₂ < 1) (hθ1 : ∀ x : ℂ, ‖x‖ ≤ ρ₁ → θ x = 1) (hθ0 : ∀ x : ℂ, ρ₂ ≤ ‖x‖ → θ x = 0) {w : ℂ}
    (hw : w ∈ unitDisc) {g : SL2C} (hg : g ∈ Γ) (hgw : ‖mob g w‖ < ρ₁) :
    ∀ᶠ w' in 𝓝 w, 1 ≤ ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) w') := by
  have hcont : ContinuousAt (mob g) w :=
    (fd_mob_differentiableAt g (fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp hw))).continuousAt
  filter_upwards [hcont.norm.eventually (gt_mem_nhds hgw), isOpen_ball.mem_nhds hw] with w' hw' hw'D
  obtain ⟨T, s, hs0, -, hT⟩ := s8d_tsum_local hΓ (f := fun b w => θ ((b : ℂ → ℂ) w)) hρ₂
    (fun b w h => hθ0 _ h) hw'D
  have hsum : Summable fun b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => θ ((b : ℂ → ℂ) w') :=
    summable_of_ne_finset_zero (s := T) fun b hb => (hT w' hs0.le).1 b hb
  have h1 := hsum.le_tsum ⟨mob g, g, hg, rfl⟩ fun j _ => hθnn _
  rw [show θ (mob g w') = 1 from hθ1 _ hw'.le] at h1
  exact h1

/-- Where `S < 1`, every orbit stays off `|x| < ρ₀` in a neighbourhood (`ρ₀ < ρ₁`, `ρ₀ < ρ₂`). -/
theorem s8d_lt {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {θ : ℂ → ℝ} (hθnn : ∀ x, 0 ≤ θ x) {ρ₀ ρ₁ ρ₂ : ℝ}
    (h01 : ρ₀ < ρ₁) (h02 : ρ₀ < ρ₂) (hρ₂ : ρ₂ < 1) (hθ1 : ∀ x : ℂ, ‖x‖ ≤ ρ₁ → θ x = 1)
    (hθ0 : ∀ x : ℂ, ρ₂ ≤ ‖x‖ → θ x = 0) {w : ℂ} (hw : w ∈ unitDisc)
    (hS : ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) w) < 1) :
    ∀ᶠ w' in 𝓝 w, ∀ g ∈ Γ, ρ₀ ≤ ‖mob g w'‖ := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  obtain ⟨T, hT⟩ := s8d_local hΓ (s := (‖w‖ + 1) / 2) (by linarith) hρ₂
  obtain ⟨T', s', hs0', -, hT'⟩ := s8d_tsum_local hΓ (f := fun b w => θ ((b : ℂ → ℂ) w)) hρ₂
    (fun b w h => hθ0 _ h) hw
  have hsum : Summable fun b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => θ ((b : ℂ → ℂ) w) :=
    summable_of_ne_finset_zero (s := T') fun b hb => (hT' w hs0'.le).1 b hb
  have hfar : ∀ b ∈ T, ∀ᶠ w' in 𝓝 w, ρ₀ < ‖(b : ℂ → ℂ) w'‖ := by
    intro b _
    obtain ⟨g, hg, hb⟩ := b.2
    have hbw : ρ₁ < ‖(b : ℂ → ℂ) w‖ := by
      by_contra hc
      push_neg at hc
      have h1 := hsum.le_tsum b fun j _ => hθnn _
      rw [hθ1 _ hc] at h1
      linarith
    have hcont : ContinuousAt (b : ℂ → ℂ) w := by
      rw [← hb]
      exact (fd_mob_differentiableAt g (fdD_denom_ne (hΓ.1 g hg) hw1)).continuousAt
    exact hcont.norm.eventually (lt_mem_nhds (h01.trans hbw))
  filter_upwards [(Filter.eventually_all_finset T).mpr hfar,
    isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (show ‖w‖ < (‖w‖ + 1) / 2 by linarith))] with w' h1 h2 g hg
  by_cases hb : (⟨mob g, g, hg, rfl⟩ : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C))) ∈ T
  · exact (h1 _ hb).le
  · exact h02.le.trans (hT _ hb w' (mem_ball_zero_iff.mp h2).le).le

/-- On `{S ≥ 1}` the partition `ψ = θ / (S + 1 - h(S))` sums to `1` over `A` (`S` is `Γ`-invariant). -/
theorem s8d_psi_one {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {θ S ψ : ℂ → ℝ} (hθnn : ∀ x, 0 ≤ θ x)
    (hS : ∀ w, S w = ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) w))
    (hψ : ∀ x, ψ x = θ x / (S x + 1 - Real.smoothTransition (2 * S x - 1))) {w : ℂ} (hw : w ∈ unitDisc)
    (h1 : 1 ≤ S w) :
    ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), ψ ((b : ℂ → ℂ) w) = 1 := by
  have hinv : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), S ((b : ℂ → ℂ) w) = S w := by
    intro b
    obtain ⟨g, hg, hb⟩ := b.2
    rw [← hb, hS, hS]
    exact s8d_sum_inv hΓ θ hg hw
  have e : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      ψ ((b : ℂ → ℂ) w) = θ ((b : ℂ → ℂ) w) / (S w + 1 - Real.smoothTransition (2 * S w - 1)) := by
    intro b
    rw [hψ, hinv]
  rw [tsum_congr e, tsum_div_const, ← hS, (s8d_den (by linarith)).2 h1, div_self (by linarith)]

/-- If the partition sums to `1` near `w`, the termwise Wirtinger derivatives of `φ ∘ a` sum to `0` at `w`. -/
theorem s8d_deriv_zero {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {φ : ℂ → ℂ} {r : ℝ} (hr : r < 1)
    (hφ0 : ∀ x : ℂ, r ≤ ‖x‖ → φ x = 0) (hφd : DifferentiableOn ℝ φ unitDisc) {w : ℂ} (hw : w ∈ unitDisc)
    (h1 : ∀ᶠ w' in 𝓝 w, ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), φ ((b : ℂ → ℂ) w') = 1) :
    (Summable fun b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => dzbar (fun z => φ ((b : ℂ → ℂ) z)) w) ∧
      (Summable fun b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)) => dz (fun z => φ ((b : ℂ → ℂ) z)) w) ∧
      ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), dzbar (fun z => φ ((b : ℂ → ℂ) z)) w = 0 ∧
      ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), dz (fun z => φ ((b : ℂ → ℂ) z)) w = 0 := by
  obtain ⟨T, s, hs0, -, hT⟩ := s8d_tsum_local hΓ (f := fun b w => φ ((b : ℂ → ℂ) w)) hr
    (fun b w h => hφ0 _ h) hw
  have hball : ball (0 : ℂ) s ∈ 𝓝 w := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hs0)
  have hdiff : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      DifferentiableAt ℝ (fun z => φ ((b : ℂ → ℂ) z)) w := by
    intro b
    obtain ⟨g, hg, hb⟩ := b.2
    rw [← hb]
    have hs := hΓ.1 g hg
    have hbw : mob g w ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hs (mem_ball_zero_iff.mp hw))
    exact (hφd.differentiableAt (isOpen_ball.mem_nhds hbw)).comp w
      (((s8d_mob_hol hs).differentiableAt (isOpen_ball.mem_nhds hw)).restrictScalars ℝ)
  have hz : ∀ b, b ∉ T → (fun z => φ ((b : ℂ → ℂ) z)) =ᶠ[𝓝 w] fun _ => 0 := fun b hb => by
    filter_upwards [hball] with z hz
    exact (hT z (mem_ball_zero_iff.mp hz).le).1 b hb
  have hsumT : (fun z => ∑ b ∈ T, φ ((b : ℂ → ℂ) z)) =ᶠ[𝓝 w] fun _ => (1 : ℂ) := by
    filter_upwards [hball, h1] with z hz hz1
    rw [← (hT z (mem_ball_zero_iff.mp hz).le).2, hz1]
  have hds := s8d_d_sum (T := T) (F := fun b z => φ ((b : ℂ → ℂ) z)) (w := w) fun b _ => hdiff b
  have hz1 : ∀ b, b ∉ T → dzbar (fun z => φ ((b : ℂ → ℂ) z)) w = 0 := fun b hb => by
    rw [s8q_dzbar_congr (hz b hb)]; exact (s8d_d_const 0 w).1
  have hz2 : ∀ b, b ∉ T → dz (fun z => φ ((b : ℂ → ℂ) z)) w = 0 := fun b hb => by
    rw [s8d_dz_congr (hz b hb)]; exact (s8d_d_const 0 w).2
  refine ⟨summable_of_ne_finset_zero hz1, summable_of_ne_finset_zero hz2, ?_, ?_⟩
  · rw [tsum_eq_sum hz1, ← hds.1, s8q_dzbar_congr hsumT]
    exact (s8d_d_const 1 w).1
  · rw [tsum_eq_sum hz2, ← hds.2, s8d_dz_congr hsumT]
    exact (s8d_d_const 1 w).2

/-- **Q2 (STUB).** Divergence theorem on `Γ\𝔻` for compactly supported (mod `Γ`) equivariant vector densities:
`P` of weight `(-1, 0)` (`P(γz) γ'(z) = P(z)`), `Q` of weight `(0, -1)`; then `∂̄P + ∂Q` is an integrable invariant
density on `F` with integral `0` (via a locally finite smooth `Γ`-partition of unity and unfolding). -/
theorem s8q_div_zero {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {P Q : ℂ → ℂ}
    (hP : ContDiffOn ℝ 1 P unitDisc) (hQ : ContDiffOn ℝ 1 Q unitDisc)
    (hPΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, P (mob g z) * deriv (mob g) z = P z)
    (hQΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, Q (mob g z) * conj (deriv (mob g) z) = Q z)
    (hK : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ unitDisc ∧
      ∀ z ∈ unitDisc, (P z ≠ 0 ∨ Q z ≠ 0) → ∃ g ∈ Γ, mob g z ∈ K) :
    IntegrableOn (fun z => dzbar P z + dz Q z) (fundDomainOn Γ unitDisc) ∧
      ∫ z in fundDomainOn Γ unitDisc, (dzbar P z + dz Q z) = 0 := by
  obtain ⟨K, hKc, hKD, hKs⟩ := hK
  have hF := s8w_fundD hΓ
  obtain ⟨r', hr'1, hKr'⟩ := exists_lt_subset_ball hKc.isClosed hKD
  -- radii `a < ρ₁ < ρ₂ < ρ₃ < 1` with `K ⊆ {|x| < a}`
  obtain ⟨a, ha0, ha1, hKa⟩ : ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ ∀ x ∈ K, ‖x‖ < a :=
    ⟨max r' 0, le_max_right _ _, max_lt hr'1 one_pos, fun x hx =>
      (mem_ball_zero_iff.mp (hKr' hx)).trans_le (le_max_left _ _)⟩
  have hρ1 : a < (2 * a + 1) / 3 := by linarith
  have hρ12 : (2 * a + 1) / 3 < (a + 2) / 3 := by linarith
  have hρ2 : (a + 2) / 3 < 1 := by linarith
  have hρ23 : (a + 2) / 3 < (a + 5) / 6 := by linarith
  have hρ3 : (a + 5) / 6 < 1 := by linarith
  -- the bump `θ`: `≡ 1` on `|x| ≤ ρ₁`, `≡ 0` on `|x| ≥ ρ₂`
  obtain ⟨θ, hθd, hθnn, hθ1, hθ0⟩ : ∃ θ : ℂ → ℝ, ContDiff ℝ 1 θ ∧ (∀ x, 0 ≤ θ x) ∧
      (∀ x : ℂ, ‖x‖ ≤ (2 * a + 1) / 3 → θ x = 1) ∧ (∀ x : ℂ, (a + 2) / 3 ≤ ‖x‖ → θ x = 0) := by
    let β : ContDiffBump (0 : ℂ) := ⟨(2 * a + 1) / 3, (a + 2) / 3, by linarith, hρ12⟩
    exact ⟨β, β.contDiff, fun x => β.nonneg, fun x hx => β.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx),
      fun x hx => β.zero_of_le_dist (by rw [dist_zero_right]; exact hx)⟩
  -- `S = ∑_a θ ∘ a`, the partition `ψ = θ / (S + 1 - h(S))`, and `Ψ = ψ` as a complex function
  obtain ⟨S, hS⟩ : ∃ S : ℂ → ℝ, ∀ w, S w = ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      θ ((b : ℂ → ℂ) w) := ⟨_, fun w => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ, ∀ x, ψ x = θ x / (S x + 1 - Real.smoothTransition (2 * S x - 1)) :=
    ⟨_, fun x => rfl⟩
  have hψcd : ContDiffOn ℝ 1 ψ unitDisc := by
    have e : ψ = fun x => θ x / ((∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) x)) + 1 -
        Real.smoothTransition (2 * (∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), θ ((b : ℂ → ℂ) x))
          - 1)) := funext fun x => by rw [hψ, hS]
    rw [e]
    exact s8d_psi_cd hΓ hθd hθnn hρ2 hθ0
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ → ℂ, ∀ x, Ψ x = (ψ x : ℂ) := ⟨_, fun x => rfl⟩
  have hΨcd : ContDiffOn ℝ 1 Ψ unitDisc :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hψcd).congr fun x _ => hΨ x
  have hΨd : DifferentiableOn ℝ Ψ unitDisc := hΨcd.differentiableOn one_ne_zero
  have hΨ0 : ∀ x : ℂ, (a + 2) / 3 ≤ ‖x‖ → Ψ x = 0 := fun x hx => by
    rw [hΨ, hψ, hθ0 x hx, zero_div, Complex.ofReal_zero]
  -- near `Γ · K` the partition sums to `1`
  have hone : ∀ w ∈ unitDisc, (∃ g ∈ Γ, mob g w ∈ K) →
      ∀ᶠ w' in 𝓝 w, ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), Ψ ((b : ℂ → ℂ) w') = 1 := by
    rintro w hw ⟨g, hg, hgK⟩
    filter_upwards [s8d_ge hΓ hθnn hρ2 hθ1 hθ0 hw hg ((hKa _ hgK).trans hρ1), isOpen_ball.mem_nhds hw]
      with w' h1 hw'
    simp only [hΨ]
    rw [← Complex.ofReal_tsum, s8d_psi_one hΓ hθnn hS hψ hw' (by rw [hS]; exact h1), Complex.ofReal_one]
  -- where `S < 1`, `P` and `Q` vanish nearby, so the divergence vanishes
  have hDz : ∀ w ∈ unitDisc, S w < 1 → dzbar P w + dz Q w = 0 := by
    intro w hw hSw
    have hev := s8d_lt hΓ hθnn (ρ₀ := a) hρ1 (by linarith) hρ2 hθ1 hθ0 hw (by rw [← hS]; exact hSw)
    have hPQ : ∀ᶠ w' in 𝓝 w, P w' = 0 ∧ Q w' = 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hw] with w' h1 hw'
      by_contra hc
      obtain ⟨g, hg, hgK⟩ := hKs w' hw' (not_and_or.mp hc)
      exact absurd (hKa _ hgK) (not_lt.mpr (h1 g hg))
    have eP : P =ᶠ[𝓝 w] fun _ => (0 : ℂ) := hPQ.mono fun _ h => h.1
    have eQ : Q =ᶠ[𝓝 w] fun _ => (0 : ℂ) := hPQ.mono fun _ h => h.2
    rw [s8q_dzbar_congr eP, s8d_dz_congr eQ, (s8d_d_const 0 w).1, (s8d_d_const 0 w).2, add_zero]
  -- pointwise: `D = ∑_a |a'|² (Ψ D) ∘ a` on `𝔻`
  have hpt1 : ∀ w ∈ unitDisc, (∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • (Ψ ((b : ℂ → ℂ) w) *
        (dzbar P ((b : ℂ → ℂ) w) + dz Q ((b : ℂ → ℂ) w)))) = dzbar P w + dz Q w := by
    intro w hw
    have e : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), (‖deriv (b : ℂ → ℂ) w‖ ^ 2) •
        (Ψ ((b : ℂ → ℂ) w) * (dzbar P ((b : ℂ → ℂ) w) + dz Q ((b : ℂ → ℂ) w))) =
        Ψ ((b : ℂ → ℂ) w) * (dzbar P w + dz Q w) := by
      intro b
      obtain ⟨g, hg, hb⟩ := b.2
      have hb' : (b : ℂ → ℂ) = mob g := hb.symm
      rw [hb', Complex.real_smul, mul_left_comm,
        s8d_wt_D (hΓ.1 g hg) hP hQ (fun z hz => hPΓ g hg z hz) (fun z hz => hQΓ g hg z hz) hw]
    rw [tsum_congr e, tsum_mul_right]
    by_cases hD : dzbar P w + dz Q w = 0
    · rw [hD, mul_zero]
    · have hS1 : 1 ≤ S w := by
        by_contra hc
        push_neg at hc
        exact hD (hDz w hw hc)
      have h1 : ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), Ψ ((b : ℂ → ℂ) w) = 1 := by
        simp only [hΨ]
        rw [← Complex.ofReal_tsum, s8d_psi_one hΓ hθnn hS hψ hw hS1, Complex.ofReal_one]
      rw [h1, one_mul]
  -- pointwise: `∑_a |a'|² (∂̄Ψ P + ∂Ψ Q) ∘ a = 0` on `𝔻`
  have hpt2 : ∀ w ∈ unitDisc, (∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • (dzbar Ψ ((b : ℂ → ℂ) w) * P ((b : ℂ → ℂ) w) +
        dz Ψ ((b : ℂ → ℂ) w) * Q ((b : ℂ → ℂ) w))) = 0 := by
    intro w hw
    have e : ∀ b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)), (‖deriv (b : ℂ → ℂ) w‖ ^ 2) •
        (dzbar Ψ ((b : ℂ → ℂ) w) * P ((b : ℂ → ℂ) w) + dz Ψ ((b : ℂ → ℂ) w) * Q ((b : ℂ → ℂ) w)) =
        dzbar (fun z => Ψ ((b : ℂ → ℂ) z)) w * P w + dz (fun z => Ψ ((b : ℂ → ℂ) z)) w * Q w := by
      intro b
      obtain ⟨g, hg, hb⟩ := b.2
      have hb' : (b : ℂ → ℂ) = mob g := hb.symm
      have hs := hΓ.1 g hg
      have hbw : mob g w ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt hs (mem_ball_zero_iff.mp hw))
      rw [hb', Complex.real_smul]
      exact (s8d_wt_psi hs (fun z hz => hPΓ g hg z hz) (fun z hz => hQΓ g hg z hz) hw
        (hΨd.differentiableAt (isOpen_ball.mem_nhds hbw))).symm
    rw [tsum_congr e]
    by_cases hPQ : P w = 0 ∧ Q w = 0
    · simp only [hPQ.1, hPQ.2, mul_zero, add_zero, tsum_zero]
    · obtain ⟨g, hg, hgK⟩ := hKs w hw (not_and_or.mp hPQ)
      obtain ⟨hs1, hs2, hz1, hz2⟩ := s8d_deriv_zero hΓ hρ2 hΨ0 hΨd hw (hone w hw ⟨g, hg, hgK⟩)
      rw [(hs1.mul_right _).tsum_add (hs2.mul_right _), tsum_mul_right, tsum_mul_right, hz1, hz2]
      ring
  -- unfold both densities
  have hcont1 : ContinuousOn (fun x => Ψ x * (dzbar P x + dz Q x)) unitDisc :=
    hΨcd.continuousOn.mul ((s8d_dcont hP).1.add (s8d_dcont hQ).2)
  have hU1 := s8d_unfold hΓ hρ3 hcont1 fun x hx => by rw [hΨ0 x (by linarith), zero_mul]
  have hcont2 : ContinuousOn (fun x => dzbar Ψ x * P x + dz Ψ x * Q x) unitDisc :=
    ((s8d_dcont hΨcd).1.mul hP.continuousOn).add ((s8d_dcont hΨcd).2.mul hQ.continuousOn)
  have hU2 := s8d_unfold hΓ hρ3 hcont2 fun x hx => by
    have e : Ψ =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show (a + 2) / 3 < ‖x‖ by linarith)] with y hy
      exact hΨ0 y hy.le
    rw [s8q_dzbar_congr e, s8d_dz_congr e, (s8d_d_const 0 x).1, (s8d_d_const 0 x).2]
    ring
  -- the plane divergence theorem for `Ψ P` and `Ψ Q`
  have hcs : ∀ R : ℂ → ℂ, HasCompactSupport fun x => Ψ x * R x := fun R =>
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((a + 2) / 3)) fun x hx => by
      have : (a + 2) / 3 < ‖x‖ := by
        rw [mem_closedBall_zero_iff, not_le] at hx
        exact hx
      rw [hΨ0 x this.le, zero_mul]
  have hu : ∀ R : ℂ → ℂ, ContDiffOn ℝ 1 R unitDisc → ContDiff ℝ 1 fun x => Ψ x * R x := fun R hR =>
    s8d_cd_ext hρ2 (hΨcd.mul hR) fun x hx => by rw [hΨ0 x hx, zero_mul]
  have hpl := s8d_plane (hu P hP) (hcs P) (hu Q hQ) (hcs Q)
  have hsplit : (∫ x in unitDisc, Ψ x * (dzbar P x + dz Q x)) +
      ∫ x in unitDisc, (dzbar Ψ x * P x + dz Ψ x * Q x) = 0 := by
    rw [← integral_add hU1.2.2 hU2.2.2]
    rw [setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball) (g := fun x => dzbar (fun x => Ψ x * P x) x +
      dz (fun x => Ψ x * Q x) x) fun x hx => ?_]
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
      · exact hpl
      · have h1 : ¬ ‖x‖ < 1 := fun h => hx (mem_ball_zero_iff.mpr h)
        push_neg at h1
        have e : ∀ R : ℂ → ℂ, (fun x => Ψ x * R x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := fun R => by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
            (show (a + 2) / 3 < ‖x‖ by linarith)] with y hy
          rw [hΨ0 y hy.le, zero_mul]
        rw [s8q_dzbar_congr (e P), s8d_dz_congr (e Q), (s8d_d_const 0 x).1, (s8d_d_const 0 x).2, add_zero]
    · have hxd := isOpen_ball.mem_nhds hx
      have hΨx : DifferentiableAt ℝ Ψ x := hΨd.differentiableAt hxd
      have hPx : DifferentiableAt ℝ P x := (hP.differentiableOn one_ne_zero).differentiableAt hxd
      have hQx : DifferentiableAt ℝ Q x := (hQ.differentiableOn one_ne_zero).differentiableAt hxd
      show Ψ x * (dzbar P x + dz Q x) + (dzbar Ψ x * P x + dz Ψ x * Q x) =
        dzbar (fun x => Ψ x * P x) x + dz (fun x => Ψ x * Q x) x
      rw [dzbar_mul hΨx hPx, dz_mul hΨx hQx]
      ring
  have h2 : (∫ x in unitDisc, (dzbar Ψ x * P x + dz Ψ x * Q x)) = 0 := by
    rw [← hU2.2.1, setIntegral_congr_fun hF.1 fun w hw => hpt2 w (hF.2.1 hw), integral_zero]
  have heqF : EqOn (fun w => ∑' b : ↥((fun g : SL2C => mob g) '' (Γ : Set SL2C)),
      (‖deriv (b : ℂ → ℂ) w‖ ^ 2) • (Ψ ((b : ℂ → ℂ) w) *
        (dzbar P ((b : ℂ → ℂ) w) + dz Q ((b : ℂ → ℂ) w)))) (fun z => dzbar P z + dz Q z)
      (fundDomainOn Γ unitDisc) := fun w hw => hpt1 w (hF.2.1 hw)
  refine ⟨hU1.1.congr_fun heqF hF.1, ?_⟩
  rw [← setIntegral_congr_fun hF.1 heqF, hU1.2.1]
  rw [h2, add_zero] at hsplit
  exact hsplit

/-- **Q3 (STUB).** Pointwise polarized second-energy identity on `𝔻` (the integrand of `s7ei_second_energy`):
`ρ q(h) \overline{q(k)} - ρ Δ₀h \overline{Δ₀k} - ½ ρ Δ₀h \overline{k} = ∂̄(∂̄h · \overline{q(k)}) + ∂(∂̄h · \overline{Δ₀k + k/2})`. -/
theorem s8q_energy_pt {h k : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    s7et_q h z * conj (s7et_q k z) * rho z - laplace0 h z * conj (laplace0 k z) * rho z -
        (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z =
      dzbar (fun w => dzbar h w * conj (s7et_q k w)) z +
        dz (fun w => dzbar h w * conj (laplace0 k w + (1 / 2 : ℂ) * k w)) z := by
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hab : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_contDiffOn_dzbar ha isOpen_ball (by simp)
  have hhb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc := wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hkb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar k) unitDisc := wp_contDiffOn_dzbar hk isOpen_ball (by simp)
  have hkbb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar (dzbar k)) unitDisc := wp_contDiffOn_dzbar hkb isOpen_ball (by simp)
  have hkab : ContDiffOn ℝ (⊤ : ℕ∞) (dz (dzbar k)) unitDisc := wp_contDiffOn_dz hkb isOpen_ball (by simp)
  have hqk : ContDiffOn ℝ (⊤ : ℕ∞) (s7et_q k) unitDisc := wp_contDiffOn_dzbar (ha.mul hkb) isOpen_ball (by simp)
  have hLk : ContDiffOn ℝ (⊤ : ℕ∞) (laplace0 k) unitDisc := (ha.mul hkab).neg
  have diff (g : ℂ → ℂ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ g w :=
    (hg.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have hX := wp_disk_factor_ne_zero hz
  -- `q h = ρ⁻¹ ∂̄∂̄h + ∂̄h ∂̄ρ⁻¹`, and the same for `k` near `z`
  have eqk : ∀ w ∈ unitDisc, s7et_q k w =
      (rho w : ℂ)⁻¹ * dzbar (dzbar k) w + dzbar k w * dzbar (fun v => (rho v : ℂ)⁻¹) w :=
    fun w hw => dzbar_mul (diff _ ha w hw) (diff _ hkb w hw)
  have eqh : s7et_q h z =
      (rho z : ℂ)⁻¹ * dzbar (dzbar h) z + dzbar h z * dzbar (fun v => (rho v : ℂ)⁻¹) z :=
    dzbar_mul (diff _ ha z hz) (diff _ hhb z hz)
  have hcomm : dz (dzbar (dzbar k)) z = dzbar (dz (dzbar k)) z :=
    wp_wirtinger_comm ((hkb.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp))
  have d1 : DifferentiableAt ℝ (fun w => (rho w : ℂ)⁻¹ * dzbar (dzbar k) w) z :=
    (diff _ ha z hz).mul (diff _ hkbb z hz)
  have d2 : DifferentiableAt ℝ (fun w => dzbar k w * dzbar (fun v => (rho v : ℂ)⁻¹) w) z :=
    (diff _ hkb z hz).mul (diff _ hab z hz)
  have dqk : dz (s7et_q k) z =
      ((rho z : ℂ)⁻¹ * dz (dzbar (dzbar k)) z + dzbar (dzbar k) z * dz (fun v => (rho v : ℂ)⁻¹) z) +
        (dzbar k z * dz (dzbar fun v => (rho v : ℂ)⁻¹) z + dzbar (fun v => (rho v : ℂ)⁻¹) z * dz (dzbar k) z) := by
    have e : s7et_q k =ᶠ[𝓝 z]
        fun w => (rho w : ℂ)⁻¹ * dzbar (dzbar k) w + dzbar k w * dzbar (fun v => (rho v : ℂ)⁻¹) w :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) eqk
    rw [s7g_f2_dz_congr e, wp_dz_add d1 d2, dz_mul (diff _ ha z hz) (diff _ hkbb z hz),
      dz_mul (diff _ hkb z hz) (diff _ hab z hz)]
  have d3 : DifferentiableAt ℝ (fun w => (rho w : ℂ)⁻¹ * dz (dzbar k) w) z :=
    (diff _ ha z hz).mul (diff _ hkab z hz)
  have dLk : dzbar (laplace0 k) z = -((rho z : ℂ)⁻¹ * dzbar (dz (dzbar k)) z +
      dz (dzbar k) z * dzbar (fun v => (rho v : ℂ)⁻¹) z) := by
    have e : laplace0 k = fun w => (-1 : ℂ) * ((rho w : ℂ)⁻¹ * dz (dzbar k) w) := funext fun w => by
      show -((rho w : ℂ)⁻¹ * dz (dzbar k) w) = _
      ring
    rw [e, wp_dzbar_const_mul d3 (-1), dzbar_mul (diff _ ha z hz) (diff _ hkab z hz)]
    ring
  have cq : DifferentiableAt ℝ (fun w => conj (s7et_q k w)) z := (diff _ hqk z hz).star
  have dk2 : DifferentiableAt ℝ (fun w => (1 / 2 : ℂ) * k w) z := (diff _ hk z hz).const_mul _
  have dL : DifferentiableAt ℝ (fun w => laplace0 k w + (1 / 2 : ℂ) * k w) z := (diff _ hLk z hz).add dk2
  have cL : DifferentiableAt ℝ (fun w => conj (laplace0 k w + (1 / 2 : ℂ) * k w)) z := dL.star
  have T1 : dzbar (fun w => dzbar h w * conj (s7et_q k w)) z =
      dzbar h z * conj (dz (s7et_q k) z) + conj (s7et_q k z) * dzbar (dzbar h) z := by
    rw [dzbar_mul (diff _ hhb z hz) cq, p71r_dzbar_conj]
  have T2 : dz (fun w => dzbar h w * conj (laplace0 k w + (1 / 2 : ℂ) * k w)) z =
      dzbar h z * conj (dzbar (laplace0 k) z + (1 / 2 : ℂ) * dzbar k z) +
        conj (laplace0 k z + (1 / 2 : ℂ) * k z) * dz (dzbar h) z := by
    rw [dz_mul (diff _ hhb z hz) cL, s7g_f2_dz_conj, wp_dzbar_add (diff _ hLk z hz) dk2,
      wp_dzbar_const_mul (diff _ hk z hz)]
  have hρz : (rho z : ℂ) = 4 / (1 - z * conj z) ^ 2 := by
    rw [← inv_inv (rho z : ℂ), wp_rho_inv_complex z, inv_div]
  rw [T1, T2, dqk, dLk, eqh, eqk z hz, ← hcomm]
  unfold laplace0
  rw [wp_dz_rho_inv z, wp_dzbar_rho_inv z, wp_dz_dzbar_rho_inv z, wp_rho_inv_complex z, hρz]
  simp only [map_add, map_mul, map_sub, map_neg, map_div₀, map_pow, map_one, map_ofNat, Complex.conj_conj]
  field_simp
  ring

/-- **Q4 (STUB).** `Γ`-Caccioppoli: a smooth bounded `Γ`-invariant `h` on `𝔻` with bounded `Δ₀h` has finite Dirichlet
energy and finite `q`-energy on `F` (from Q1–Q3 with `χ_n²` weights and absorption). -/
theorem s8q_caccioppoli {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (hhΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, h (mob g z) = h z) {C : ℝ}
    (hb : ∀ z ∈ unitDisc, ‖h z‖ ≤ C) (hΔ : ∀ z ∈ unitDisc, ‖laplace0 h z‖ ≤ C) :
    IntegrableOn (fun z => ‖dzbar h z‖ ^ 2) (fundDomainOn Γ unitDisc) ∧
      IntegrableOn (fun z => ‖s7et_q h z‖ ^ 2 * rho z) (fundDomainOn Γ unitDisc) := by
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0 h0)
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hhd : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc := wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hqh : ContDiffOn ℝ (⊤ : ℕ∞) (s7et_q h) unitDisc := wp_contDiffOn_dzbar (ha.mul hhd) isOpen_ball (by simp)
  have hLh : ContDiffOn ℝ (⊤ : ℕ∞) (laplace0 h) unitDisc :=
    (ha.mul (wp_contDiffOn_dz hhd isOpen_ball (by simp))).neg
  have hch : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (h w)) unitDisc := Complex.conjCLE.contDiff.comp_contDiffOn hh
  have hcqh : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (s7et_q h w)) unitDisc :=
    Complex.conjCLE.contDiff.comp_contDiffOn hqh
  have hRh : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (laplace0 h w + (1 / 2 : ℂ) * h w)) unitDisc :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hLh.add (contDiffOn_const.mul hh))
  have diff (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ f w :=
    (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have aesm (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) :
      AEStronglyMeasurable f (volume.restrict (fundDomainOn Γ unitDisc)) :=
    (hf.continuousOn.mono hFD).aestronglyMeasurable hFm
  have hρr : AEStronglyMeasurable (fun z => rho z) (volume.restrict (fundDomainOn Γ unitDisc)) :=
    gam_rho_measurable.aestronglyMeasurable
  have hρi : IntegrableOn (fun z => rho z) (fundDomainOn Γ unitDisc) := s8w_rho_integrableOn (s8w_area_fin hΓ)
  have hρ0 := s8q_rho_nonneg
  have amgm : ∀ x y : ℝ, 2 * x * y ≤ x ^ 2 / 2 + 2 * y ^ 2 := fun x y => by nlinarith [sq_nonneg (x - 2 * y)]
  have hE := s8q_equiv_aux hΓ.1 hh hhΓ
  have hderiv : ∀ g ∈ Γ, ∀ z ∈ unitDisc, deriv (mob g) z ≠ 0 := fun g hg z hz => by
    have hD := fdD_denom_ne (hΓ.1.1 g hg) (mem_ball_zero_iff.mp hz)
    rw [gam_mob_deriv hD]
    exact one_div_ne_zero (pow_ne_zero 2 hD)
  have hmobD : ∀ g ∈ Γ, ∀ z ∈ unitDisc, mob g z ∈ unitDisc := fun g hg z hz =>
    mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1.1 g hg) (mem_ball_zero_iff.mp hz))
  -- `ρ(γz)⁻¹ = ρ(z)⁻¹ |γ'|²`
  have hjac : ∀ g ∈ Γ, ∀ z ∈ unitDisc,
      (rho (mob g z) : ℂ)⁻¹ = (rho z : ℂ)⁻¹ * (deriv (mob g) z * conj (deriv (mob g) z)) := fun g hg z hz => by
    have hj := gam_rho_mob_jacobian (hΓ.1.1 g hg) (fdD_denom_ne (hΓ.1.1 g hg) (mem_ball_zero_iff.mp hz))
    have hj' : (rho (mob g z) : ℂ) * (deriv (mob g) z * conj (deriv (mob g) z)) = rho z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast hj
    have h1 := s8q_rho_ne (hmobD g hg z hz)
    have h2 := s8q_rho_ne hz
    have hd := hderiv g hg z hz
    have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
    rw [← hj']
    field_simp
  -- cutoffs
  obtain ⟨χ, Cχ, hχs, hχ01, hχΓ, hχK, hχev, hχd, -⟩ := s8q_cutoff hΓ.1
  have hc : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (χ n w : ℂ)) unitDisc := fun n =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχs n)
  have hCχ : 0 ≤ Cχ := by
    have h1 := (norm_nonneg _).trans (hχd 0 0 h0)
    have hρ0' : 0 < Real.sqrt (rho 0) := Real.sqrt_pos.mpr (by unfold rho; norm_num)
    exact nonneg_of_mul_nonneg_left h1 hρ0'
  have hlim : ∀ z ∈ fundDomainOn Γ unitDisc, Tendsto (fun n => χ n z ^ 2) atTop (𝓝 1) := fun z hz => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχev z (hFD hz)] with n hn
    rw [hn.self_of_nhds, one_pow]
  have hdzb : ∀ n z, dzbar (fun w => (χ n w : ℂ)) z = conj (dz (fun w => (χ n w : ℂ)) z) := fun n z => by
    have := p71r_dzbar_conj (fun w => (χ n w : ℂ)) z
    simpa only [Complex.conj_ofReal] using this
  -- derivatives of `χ²`
  have hdcc : ∀ n, ∀ z ∈ unitDisc, dz (fun w => (χ n w : ℂ) * (χ n w : ℂ)) z =
      2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z := fun n z hz => by
    rw [dz_mul (diff _ (hc n) z hz) (diff _ (hc n) z hz)]; ring
  have hdbcc : ∀ n, ∀ z ∈ unitDisc, dzbar (fun w => (χ n w : ℂ) * (χ n w : ℂ)) z =
      2 * (χ n z : ℂ) * dzbar (fun w => (χ n w : ℂ)) z := fun n z hz => by
    rw [dzbar_mul (diff _ (hc n) z hz) (diff _ (hc n) z hz)]; ring
  have hcc : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (χ n w : ℂ) * (χ n w : ℂ)) unitDisc := fun n => (hc n).mul (hc n)
  have hnχ : ∀ n, ∀ z ∈ unitDisc, ‖2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z‖ ≤
      2 * χ n z * (Cχ * Real.sqrt (rho z)) := fun n z hz => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ01 n z hz).1, Complex.norm_two]
    exact mul_le_mul_of_nonneg_left (hχd n z hz) (by linarith [(hχ01 n z hz).1])
  have hssq : ∀ z, Real.sqrt (rho z) ^ 2 = rho z := fun z => Real.sq_sqrt (s8q_rho_nonneg z)
  -- the support condition for `Q2`
  have hsupp : ∀ n (P Q : ℂ → ℂ), (∀ z, P z = (χ n z : ℂ) * (χ n z : ℂ) * (P z / ((χ n z : ℂ) * (χ n z : ℂ)))) →
      True := fun _ _ _ _ => trivial
  clear hsupp
  -- ### Part 1: the Dirichlet energy
  have hlap : ∀ z ∈ unitDisc, dz (dzbar h) z = -((rho z : ℂ) * laplace0 h z) := fun z hz => by
    show dz (dzbar h) z = -((rho z : ℂ) * -((rho z : ℂ)⁻¹ * dz (dzbar h) z))
    field_simp [s8q_rho_ne hz]
  have part1 : ∀ n, IntegrableOn (fun z => χ n z ^ 2 * ‖dzbar h z‖ ^ 2) (fundDomainOn Γ unitDisc) ∧
      ∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * ‖dzbar h z‖ ^ 2 ≤
        2 * ((2 * Cχ ^ 2 * C ^ 2 + C ^ 2) * ∫ z in fundDomainOn Γ unitDisc, rho z) := by
    intro n
    -- the invariant bound `|∂̄h|² ≤ M ρ` on the support of `χ_n`
    have hΦ : ContinuousOn (fun z => ‖dzbar h z‖ ^ 2 * ‖(rho z : ℂ)⁻¹‖) unitDisc :=
      (hhd.continuousOn.norm.pow 2).mul ha.continuousOn.norm
    have hΦΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, ‖dzbar h (mob g z)‖ ^ 2 * ‖(rho (mob g z) : ℂ)⁻¹‖ =
        ‖dzbar h z‖ ^ 2 * ‖(rho z : ℂ)⁻¹‖ := fun g hg z hz => by
      have hd := hderiv g hg z hz
      have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
      have e1 : dzbar h (mob g z) = dzbar h z / conj (deriv (mob g) z) :=
        eq_div_of_mul_eq hcd (hE g hg z hz).1
      rw [e1, hjac g hg z hz, norm_div, norm_mul, norm_mul, Complex.norm_conj]
      have hn : ‖deriv (mob g) z‖ ≠ 0 := norm_ne_zero_iff.mpr hd
      field_simp
    obtain ⟨M, hM⟩ := s8q_inv_bound hΦ hΦΓ (hχK n)
    have hT2b : ∀ z ∈ unitDisc, χ n z ^ 2 * ‖dzbar h z‖ ^ 2 ≤ max M 0 * rho z := fun z hz => by
      by_cases hχ0 : χ n z = 0
      · rw [hχ0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (le_max_right _ _) (s8q_rho_nonneg z)
      · have h1 := hM z hz hχ0
        have hρpos : 0 < rho z := by
          rcases (s8q_rho_nonneg z).lt_or_eq with h | h
          · exact h
          · exact absurd (by exact_mod_cast h.symm) (s8q_rho_ne hz)
        have hinv : ‖(rho z : ℂ)⁻¹‖ = (rho z)⁻¹ := by
          rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
        rw [hinv, abs_of_nonneg (by positivity)] at h1
        have h2 : ‖dzbar h z‖ ^ 2 ≤ max M 0 * rho z := by
          have := mul_le_mul_of_nonneg_right (h1.trans (le_max_left M 0)) hρpos.le
          rwa [mul_assoc, inv_mul_cancel₀ hρpos.ne', mul_one] at this
        have h3 : χ n z ^ 2 ≤ 1 := by nlinarith [hχ01 n z hz]
        nlinarith [sq_nonneg (‖dzbar h z‖), sq_nonneg (χ n z)]
    have hT2m : AEStronglyMeasurable (fun z => χ n z ^ 2 * ‖dzbar h z‖ ^ 2)
        (volume.restrict (fundDomainOn Γ unitDisc)) :=
      (((hχs n).continuousOn.pow 2).mul (hhd.continuousOn.norm.pow 2)).mono hFD |>.aestronglyMeasurable hFm
    have hT2i : IntegrableOn (fun z => χ n z ^ 2 * ‖dzbar h z‖ ^ 2) (fundDomainOn Γ unitDisc) := by
      refine Integrable.mono' (hρi.const_mul (max M 0)) hT2m ((ae_restrict_iff' hFm).mpr
        (Eventually.of_forall fun z hz => ?_))
      rw [Real.norm_of_nonneg (by positivity)]
      exact hT2b z (hFD hz)
    refine ⟨hT2i, ?_⟩
    -- divergence of `Q = χ² h̄ ∂̄h`
    have hQs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (χ n w : ℂ) * (χ n w : ℂ) * conj (h w) * dzbar h w) unitDisc :=
      ((hcc n).mul hch).mul hhd
    have hdiv := (s8q_div_zero hΓ.1 (P := fun _ => (0 : ℂ))
      (Q := fun w => (χ n w : ℂ) * (χ n w : ℂ) * conj (h w) * dzbar h w) contDiffOn_const (hQs.of_le (by simp))
      (fun g hg z hz => by simp) (fun g hg z hz => ?_) ?_).2
    rotate_left
    · show (χ n (mob g z) : ℂ) * (χ n (mob g z) : ℂ) * conj (h (mob g z)) * dzbar h (mob g z) *
          conj (deriv (mob g) z) = (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * dzbar h z
      rw [hχΓ n g hg z hz, hhΓ g hg z hz, mul_assoc _ (dzbar h (mob g z)), (hE g hg z hz).1]
    · obtain ⟨K, hK, hKD, hKm⟩ := hχK n
      refine ⟨K, hK, hKD, fun z hz hne => hKm z hz fun h0 => ?_⟩
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (by simp [h0])
    -- pointwise: `dz Q = T1 + T2 - T3`
    have hpt : ∀ z ∈ unitDisc, dzbar (fun _ => (0 : ℂ)) z +
        dz (fun w => (χ n w : ℂ) * (χ n w : ℂ) * conj (h w) * dzbar h w) z =
        2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z +
          ((χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ) -
            (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z) := fun z hz => by
      have d1 : DifferentiableAt ℝ (fun w => (χ n w : ℂ) * (χ n w : ℂ) * conj (h w)) z :=
        diff _ ((hcc n).mul hch) z hz
      have d2 : DifferentiableAt ℝ (fun w => (χ n w : ℂ) * (χ n w : ℂ)) z := diff _ (hcc n) z hz
      rw [(l613_dz_const 0 z).2, dz_mul d1 (diff _ hhd z hz), dz_mul d2 (diff _ hch z hz), hdcc n z hz,
        s7g_f2_dz_conj, hlap z hz]
      push_cast
      rw [← Complex.conj_mul' (dzbar h z)]
      ring
    rw [setIntegral_congr_fun hFm fun z hz => hpt z (hFD hz)] at hdiv
    -- integrability of the three terms
    have hT1b : ∀ z ∈ unitDisc, ‖2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z‖ ≤
        χ n z ^ 2 * ‖dzbar h z‖ ^ 2 / 2 + 2 * (Cχ ^ 2 * C ^ 2 * rho z) := fun z hz => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have e1 := hnχ n z hz
      have e2 := hb z hz
      have hx := (hχ01 n z hz).1
      have := amgm (χ n z * ‖dzbar h z‖) (Cχ * C * Real.sqrt (rho z))
      calc ‖2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z‖ * ‖h z‖ * ‖dzbar h z‖
          ≤ (2 * χ n z * (Cχ * Real.sqrt (rho z))) * C * ‖dzbar h z‖ := by
            gcongr
        _ = 2 * (χ n z * ‖dzbar h z‖) * (Cχ * C * Real.sqrt (rho z)) := by ring
        _ ≤ _ := by
            rw [show (Cχ * C * Real.sqrt (rho z)) ^ 2 = Cχ ^ 2 * C ^ 2 * rho z by rw [mul_pow, mul_pow, hssq]] at this
            nlinarith
    have hT3b : ∀ z ∈ unitDisc, ‖(χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z)‖ ≤
        C ^ 2 * rho z := fun z hz => by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (hχ01 n z hz).1, Complex.norm_real, Real.norm_of_nonneg (s8q_rho_nonneg z)]
      have hx := hχ01 n z hz
      have h1 : χ n z * χ n z ≤ 1 := by nlinarith
      have h2 := mul_le_mul (hb z hz) (hΔ z hz) (norm_nonneg _) hC0
      have h3 : 0 ≤ ‖h z‖ * ‖laplace0 h z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h4 := s8q_rho_nonneg z
      nlinarith [mul_nonneg (mul_nonneg hx.1 hx.1) h3, mul_nonneg h4 h3]
    have hT1i : IntegrableOn (fun z => 2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z)
        (fundDomainOn Γ unitDisc) := by
      have hdc : ContDiffOn ℝ (⊤ : ℕ∞) (dz fun w => (χ n w : ℂ)) unitDisc :=
        wp_contDiffOn_dz (hc n) isOpen_ball (by simp)
      refine Integrable.mono' ((hT2i.div_const 2).add (hρi.const_mul (2 * (Cχ ^ 2 * C ^ 2))))
        ((((aesm _ (contDiffOn_const.mul (hc n))).mul (aesm _ hdc)).mul (aesm _ hch)).mul (aesm _ hhd))
        ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_))
      have := hT1b z (hFD hz)
      show _ ≤ χ n z ^ 2 * ‖dzbar h z‖ ^ 2 / 2 + 2 * (Cχ ^ 2 * C ^ 2) * rho z
      linarith
    have hT3i : IntegrableOn (fun z => (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z))
        (fundDomainOn Γ unitDisc) := by
      refine Integrable.mono' (hρi.const_mul (C ^ 2))
        ((((aesm _ (hc n)).mul (aesm _ (hc n))).mul (aesm _ hch)).mul
          ((Complex.measurable_ofReal.comp gam_rho_measurable).aestronglyMeasurable.mul (aesm _ hLh)))
        ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => hT3b z (hFD hz)))
    have hT2c : IntegrableOn (fun z => ((χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ)) (fundDomainOn Γ unitDisc) :=
      hT2i.ofReal
    have hsplit : (∫ z in fundDomainOn Γ unitDisc,
        (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z +
          ((χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ) -
            (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z))) =
        ((∫ z in fundDomainOn Γ unitDisc,
          2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z) +
        ∫ z in fundDomainOn Γ unitDisc, ((χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ)) -
        ∫ z in fundDomainOn Γ unitDisc,
          (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z) := by
      refine (integral_sub ?_ hT3i).trans ?_
      · exact hT1i.add hT2c
      · rw [integral_add hT1i hT2c]
    rw [hsplit] at hdiv
    have hX2 : (∫ z in fundDomainOn Γ unitDisc, ((χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ)) =
        ((∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * ‖dzbar h z‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    -- the absorbed estimate
    set X := ∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * ‖dzbar h z‖ ^ 2
    have hX0 : 0 ≤ X := setIntegral_nonneg hFm fun z hz => by positivity
    have hXeq : (X : ℂ) = (∫ z in fundDomainOn Γ unitDisc,
        (χ n z : ℂ) * (χ n z : ℂ) * conj (h z) * ((rho z : ℂ) * laplace0 h z)) -
          ∫ z in fundDomainOn Γ unitDisc, 2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z * conj (h z) * dzbar h z := by
      linear_combination hdiv - hX2
    have hXle : X ≤ (C ^ 2 * ∫ z in fundDomainOn Γ unitDisc, rho z) +
        (X / 2 + 2 * (Cχ ^ 2 * C ^ 2) * ∫ z in fundDomainOn Γ unitDisc, rho z) := by
      have hn := congrArg norm hXeq
      rw [Complex.norm_real, Real.norm_of_nonneg hX0] at hn
      refine hn.le.trans ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      · refine (norm_integral_le_integral_norm _).trans ?_
        rw [← integral_const_mul]
        exact setIntegral_mono_on hT3i.norm (hρi.const_mul _) hFm fun z hz => hT3b z (hFD hz)
      · refine (norm_integral_le_integral_norm _).trans ?_
        have hR : ∫ z in fundDomainOn Γ unitDisc, (χ n z ^ 2 * ‖dzbar h z‖ ^ 2 / 2 + 2 * (Cχ ^ 2 * C ^ 2 * rho z)) =
            X / 2 + 2 * (Cχ ^ 2 * C ^ 2) * ∫ z in fundDomainOn Γ unitDisc, rho z := by
          rw [integral_add (hT2i.div_const 2) ((hρi.const_mul (Cχ ^ 2 * C ^ 2)).const_mul 2), integral_div, integral_const_mul,
            integral_const_mul]
          ring
        rw [← hR]
        exact setIntegral_mono_on hT1i.norm ((hT2i.div_const 2).add ((hρi.const_mul (Cχ ^ 2 * C ^ 2)).const_mul 2)) hFm
          fun z hz => hT1b z (hFD hz)
    linarith
  have hD1 : IntegrableOn (fun z => ‖dzbar h z‖ ^ 2) (fundDomainOn Γ unitDisc) :=
    s8q_fatou hFm (hhd.continuousOn.norm.pow 2 |>.mono hFD |>.aestronglyMeasurable hFm)
      (fun z _ => by positivity) (fun n z _ => by positivity) hlim (fun n => (part1 n).1) (fun n => (part1 n).2)
  refine ⟨hD1, ?_⟩
  -- ### Part 2: the `q`-energy
  have hqnn : ∀ (x : ℝ) z, 0 ≤ x ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) := fun x z =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (s8q_rho_nonneg z))
  have hRb : ∀ z ∈ unitDisc, ‖laplace0 h z + (1 / 2 : ℂ) * h z‖ ≤ 2 * C := fun z hz => by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_div, norm_one, Complex.norm_two]
    linarith [hΔ z hz, hb z hz, norm_nonneg (h z)]
  have part2 : ∀ n, IntegrableOn (fun z => χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z)) (fundDomainOn Γ unitDisc) ∧
      ∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) ≤
        2 * (2 * C ^ 2 * (∫ z in fundDomainOn Γ unitDisc, rho z) +
          2 * Cχ ^ 2 * (∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2) +
          2 * Cχ * C * ((∫ z in fundDomainOn Γ unitDisc, rho z) + ∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2)) := by
    intro n
    have hΦ : ContinuousOn (fun z => ‖s7et_q h z‖ ^ 2) unitDisc := hqh.continuousOn.norm.pow 2
    have hΦΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, ‖s7et_q h (mob g z)‖ ^ 2 = ‖s7et_q h z‖ ^ 2 := fun g hg z hz => by
      have hd := hderiv g hg z hz
      have e := congrArg norm (hE g hg z hz).2.1
      rw [norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd), mul_one] at e
      rw [e]
    obtain ⟨M, hM⟩ := s8q_inv_bound hΦ hΦΓ (hχK n)
    have hT2b : ∀ z ∈ unitDisc, χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) ≤ max M 0 * rho z := fun z hz => by
      by_cases hχ0 : χ n z = 0
      · rw [hχ0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (le_max_right _ _) (s8q_rho_nonneg z)
      · have h1 := (hM z hz hχ0).trans (le_max_left M 0)
        rw [abs_of_nonneg (by positivity)] at h1
        have h3 : χ n z ^ 2 ≤ 1 := by nlinarith [hχ01 n z hz]
        have h4 := s8q_rho_nonneg z
        nlinarith [mul_le_mul_of_nonneg_right h1 h4, mul_nonneg (sq_nonneg ‖s7et_q h z‖) h4]
    have hT2m : AEStronglyMeasurable (fun z => χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z))
        (volume.restrict (fundDomainOn Γ unitDisc)) :=
      (((hχs n).continuousOn.pow 2).mono hFD |>.aestronglyMeasurable hFm).mul
        (((hqh.continuousOn.norm.pow 2).mono hFD |>.aestronglyMeasurable hFm).mul hρr)
    have hT2i : IntegrableOn (fun z => χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z)) (fundDomainOn Γ unitDisc) := by
      refine Integrable.mono' (hρi.const_mul (max M 0)) hT2m ((ae_restrict_iff' hFm).mpr
        (Eventually.of_forall fun z hz => ?_))
      rw [Real.norm_of_nonneg (hqnn _ z)]
      exact hT2b z (hFD hz)
    refine ⟨hT2i, ?_⟩
    have hP0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => dzbar h w * conj (s7et_q h w)) unitDisc := hhd.mul hcqh
    have hQ0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => dzbar h w * conj (laplace0 h w + (1 / 2 : ℂ) * h w)) unitDisc :=
      hhd.mul hRh
    have hdiv := (s8q_div_zero hΓ.1
      (P := fun w => (χ n w : ℂ) * (χ n w : ℂ) * (dzbar h w * conj (s7et_q h w)))
      (Q := fun w => (χ n w : ℂ) * (χ n w : ℂ) * (dzbar h w * conj (laplace0 h w + (1 / 2 : ℂ) * h w)))
      (((hcc n).mul hP0).of_le (by simp)) (((hcc n).mul hQ0).of_le (by simp))
      (fun g hg z hz => ?_) (fun g hg z hz => ?_) ?_).2
    rotate_left
    · have hd := hderiv g hg z hz
      have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
      obtain ⟨e1, e2, -⟩ := hE g hg z hz
      show (χ n (mob g z) : ℂ) * (χ n (mob g z) : ℂ) * (dzbar h (mob g z) * conj (s7et_q h (mob g z))) *
          deriv (mob g) z = (χ n z : ℂ) * (χ n z : ℂ) * (dzbar h z * conj (s7et_q h z))
      rw [hχΓ n g hg z hz, ← e1, ← e2, map_mul, map_div₀, Complex.conj_conj]
      field_simp <;> ring
    · obtain ⟨e1, -, e3⟩ := hE g hg z hz
      show (χ n (mob g z) : ℂ) * (χ n (mob g z) : ℂ) *
          (dzbar h (mob g z) * conj (laplace0 h (mob g z) + (1 / 2 : ℂ) * h (mob g z))) *
          conj (deriv (mob g) z) = (χ n z : ℂ) * (χ n z : ℂ) * (dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z))
      rw [hχΓ n g hg z hz, ← e1, e3, hhΓ g hg z hz]
      ring
    · obtain ⟨K, hK, hKD, hKm⟩ := hχK n
      refine ⟨K, hK, hKD, fun z hz hne => hKm z hz fun h0 => ?_⟩
      rcases hne with hne | hne <;> exact hne (by simp [h0])
    -- pointwise: `div = χ² ρ |q h|² - χ² (lower order) + error`
    have hpt : ∀ z ∈ unitDisc,
        dzbar (fun w => (χ n w : ℂ) * (χ n w : ℂ) * (dzbar h w * conj (s7et_q h w))) z +
          dz (fun w => (χ n w : ℂ) * (χ n w : ℂ) * (dzbar h w * conj (laplace0 h w + (1 / 2 : ℂ) * h w))) z =
        ((χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ) -
          (χ n z : ℂ) * (χ n z : ℂ) * (laplace0 h z * conj (laplace0 h z) * rho z +
            (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z) +
          (dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
            dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z)) :=
      fun z hz => by
      rw [dzbar_mul (diff _ (hcc n) z hz) (diff _ hP0 z hz), dz_mul (diff _ (hcc n) z hz) (diff _ hQ0 z hz),
        hdbcc n z hz, hdcc n z hz, hdzb]
      have e := s8q_energy_pt hh hh hz
      push_cast
      rw [← Complex.conj_mul' (s7et_q h z)]
      linear_combination -((χ n z : ℂ) * (χ n z : ℂ)) * e
    rw [setIntegral_congr_fun hFm fun z hz => hpt z (hFD hz)] at hdiv
    -- bounds
    have hLb : ∀ z ∈ unitDisc, ‖(χ n z : ℂ) * (χ n z : ℂ) * (laplace0 h z * conj (laplace0 h z) * rho z +
        (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z)‖ ≤ 2 * C ^ 2 * rho z := fun z hz => by
      have hx := hχ01 n z hz
      have hr := s8q_rho_nonneg z
      have a1 := hΔ z hz
      have a2 := hb z hz
      have a3 := norm_nonneg (laplace0 h z)
      have a4 := norm_nonneg (h z)
      have h2 : ‖laplace0 h z * conj (laplace0 h z) * rho z + (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z‖ ≤
          2 * C ^ 2 * rho z := by
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hr, norm_div, norm_one,
          Complex.norm_two]
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul a1 a1 a3 hC0) hr,
          mul_le_mul_of_nonneg_right (mul_le_mul a1 a2 a4 hC0) hr, mul_nonneg (mul_nonneg hC0 hC0) hr]
      have h1 : ‖(χ n z : ℂ) * (χ n z : ℂ)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.1]; nlinarith
      refine (norm_mul_le _ _).trans ?_
      calc _ ≤ 1 * (2 * C ^ 2 * rho z) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hEb : ∀ z ∈ unitDisc,
        ‖dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
          dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z)‖ ≤
        χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) / 2 + 2 * Cχ ^ 2 * ‖dzbar h z‖ ^ 2 +
          2 * Cχ * C * (rho z + ‖dzbar h z‖ ^ 2) := fun z hz => by
      have hd := hχd n z hz
      have hx := hχ01 n z hz
      have hR := hRb z hz
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_two]
      rw [Real.norm_of_nonneg hx.1, ← hssq z]
      have ha0 := norm_nonneg (dzbar h z)
      have hb0 := norm_nonneg (s7et_q h z)
      have hd0 := norm_nonneg (dz (fun w => (χ n w : ℂ)) z)
      have ht := Real.sqrt_nonneg (rho z)
      have h2x : (0 : ℝ) ≤ 2 * χ n z := by linarith [hx.1]
      have k1 := mul_le_mul_of_nonneg_left hd (mul_nonneg (mul_nonneg ha0 hb0) h2x)
      have k2 := mul_le_mul_of_nonneg_left (mul_le_mul hR hd hd0 (by linarith)) (mul_nonneg ha0 h2x)
      have k3 := amgm (χ n z * Real.sqrt (rho z) * ‖s7et_q h z‖) (Cχ * ‖dzbar h z‖)
      have k4 : 2 * (Real.sqrt (rho z) * ‖dzbar h z‖) ≤ Real.sqrt (rho z) ^ 2 + ‖dzbar h z‖ ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt (rho z) - ‖dzbar h z‖)]
      have k5 : χ n z * (‖dzbar h z‖ * (2 * C * (Cχ * Real.sqrt (rho z)))) ≤
          ‖dzbar h z‖ * (2 * C * (Cχ * Real.sqrt (rho z))) := mul_le_of_le_one_left (by positivity) hx.2
      have hCC : 0 ≤ 2 * Cχ * C := by positivity
      nlinarith [mul_le_mul_of_nonneg_left k4 hCC]
    have i1 : IntegrableOn (fun z => χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) / 2 + 2 * Cχ ^ 2 * ‖dzbar h z‖ ^ 2)
        (fundDomainOn Γ unitDisc) := (hT2i.div_const 2).add (hD1.const_mul _)
    have i2 : IntegrableOn (fun z => 2 * Cχ * C * (rho z + ‖dzbar h z‖ ^ 2)) (fundDomainOn Γ unitDisc) :=
      (hρi.add hD1).const_mul _
    have hEi : IntegrableOn (fun z =>
        dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
          dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z))
        (fundDomainOn Γ unitDisc) := by
      have hdc : ContDiffOn ℝ (⊤ : ℕ∞) (dz fun w => (χ n w : ℂ)) unitDisc :=
        wp_contDiffOn_dz (hc n) isOpen_ball (by simp)
      have hcdc : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (dz (fun v => (χ n v : ℂ)) w)) unitDisc :=
        Complex.conjCLE.contDiff.comp_contDiffOn hdc
      refine Integrable.mono' (i1.add i2)
        (((aesm _ hP0).mul (aesm _ ((contDiffOn_const.mul (hc n)).mul hcdc))).add
          ((aesm _ hQ0).mul (aesm _ ((contDiffOn_const.mul (hc n)).mul hdc))))
        ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_))
      have := hEb z (hFD hz)
      show _ ≤ χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) / 2 + 2 * Cχ ^ 2 * ‖dzbar h z‖ ^ 2 +
        2 * Cχ * C * (rho z + ‖dzbar h z‖ ^ 2)
      exact this
    have hLi : IntegrableOn (fun z => (χ n z : ℂ) * (χ n z : ℂ) * (laplace0 h z * conj (laplace0 h z) * rho z +
        (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z)) (fundDomainOn Γ unitDisc) := by
      have hl : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => laplace0 h z * conj (laplace0 h z)) unitDisc :=
        hLh.mul (Complex.conjCLE.contDiff.comp_contDiffOn hLh)
      have hl2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (1 / 2 : ℂ) * laplace0 h z * conj (h z)) unitDisc :=
        (contDiffOn_const.mul hLh).mul hch
      refine Integrable.mono' (hρi.const_mul (2 * C ^ 2))
        (((aesm _ (hc n)).mul (aesm _ (hc n))).mul
          (((aesm _ hl).mul (Complex.measurable_ofReal.comp gam_rho_measurable).aestronglyMeasurable).add
            ((aesm _ hl2).mul (Complex.measurable_ofReal.comp gam_rho_measurable).aestronglyMeasurable)))
        ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => hLb z (hFD hz)))
    have hT2c : IntegrableOn (fun z => ((χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ))
        (fundDomainOn Γ unitDisc) := hT2i.ofReal
    have hsplit : (∫ z in fundDomainOn Γ unitDisc,
        (((χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ) -
          (χ n z : ℂ) * (χ n z : ℂ) * (laplace0 h z * conj (laplace0 h z) * rho z +
            (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z) +
          (dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
            dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z)))) =
        ((∫ z in fundDomainOn Γ unitDisc, ((χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ)) -
          ∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (χ n z : ℂ) * (laplace0 h z * conj (laplace0 h z) * rho z +
            (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z)) +
          ∫ z in fundDomainOn Γ unitDisc,
            (dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
              dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z)) := by
      refine (integral_add ?_ hEi).trans ?_
      · exact hT2c.sub hLi
      · rw [integral_sub hT2c hLi]
    rw [hsplit] at hdiv
    have hX2 : (∫ z in fundDomainOn Γ unitDisc, ((χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ)) =
        ((∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) : ℝ) : ℂ) := integral_ofReal
    set X := ∫ z in fundDomainOn Γ unitDisc, χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z)
    have hX0 : 0 ≤ X := setIntegral_nonneg hFm fun z _ => hqnn _ z
    have hXeq : (X : ℂ) = (∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (χ n z : ℂ) *
        (laplace0 h z * conj (laplace0 h z) * rho z + (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z)) -
        ∫ z in fundDomainOn Γ unitDisc,
          (dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
            dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z)) := by
      linear_combination hdiv - hX2
    have hn := congrArg norm hXeq
    rw [Complex.norm_real, Real.norm_of_nonneg hX0] at hn
    have hI1 : ‖∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (χ n z : ℂ) *
        (laplace0 h z * conj (laplace0 h z) * rho z + (1 / 2 : ℂ) * laplace0 h z * conj (h z) * rho z)‖ ≤
          2 * C ^ 2 * ∫ z in fundDomainOn Γ unitDisc, rho z := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      exact setIntegral_mono_on hLi.norm (hρi.const_mul _) hFm fun z hz => hLb z (hFD hz)
    have hI2 : ‖∫ z in fundDomainOn Γ unitDisc,
        (dzbar h z * conj (s7et_q h z) * (2 * (χ n z : ℂ) * conj (dz (fun w => (χ n w : ℂ)) z)) +
          dzbar h z * conj (laplace0 h z + (1 / 2 : ℂ) * h z) * (2 * (χ n z : ℂ) * dz (fun w => (χ n w : ℂ)) z))‖ ≤
        X / 2 + 2 * Cχ ^ 2 * (∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2) +
          2 * Cχ * C * ((∫ z in fundDomainOn Γ unitDisc, rho z) + ∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hR : ∫ z in fundDomainOn Γ unitDisc, (χ n z ^ 2 * (‖s7et_q h z‖ ^ 2 * rho z) / 2 +
          2 * Cχ ^ 2 * ‖dzbar h z‖ ^ 2 + 2 * Cχ * C * (rho z + ‖dzbar h z‖ ^ 2)) =
          X / 2 + 2 * Cχ ^ 2 * (∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2) +
            2 * Cχ * C * ((∫ z in fundDomainOn Γ unitDisc, rho z) + ∫ z in fundDomainOn Γ unitDisc, ‖dzbar h z‖ ^ 2) := by
        rw [integral_add i1 i2, integral_add (hT2i.div_const 2) (hD1.const_mul _), integral_div, integral_const_mul,
          integral_const_mul, integral_add hρi hD1]
      rw [← hR]
      exact setIntegral_mono_on hEi.norm (i1.add i2) hFm fun z hz => hEb z (hFD hz)
    have := (hn.le.trans (norm_sub_le _ _)).trans (add_le_add hI1 hI2)
    linarith
  have hQm : AEStronglyMeasurable (fun z => ‖s7et_q h z‖ ^ 2 * rho z) (volume.restrict (fundDomainOn Γ unitDisc)) :=
    ((hqh.continuousOn.norm.pow 2).mono hFD |>.aestronglyMeasurable hFm).mul hρr
  exact s8q_fatou hFm hQm (fun z _ => mul_nonneg (sq_nonneg _) (s8q_rho_nonneg z)) (fun n z _ => by positivity)
    hlim (fun n => (part2 n).1) (fun n => (part2 n).2)

/-- **QA1 (STUB, assembly).** `G_Γ` on bounded smooth `Γ`-invariant data (`s8g_unfold` + RK3 on `𝔻` + invariance of
`G_𝔻`): smooth, bounded, `Γ`-invariant, and `2(Δ₀ + ½) G_Γ F = F` on `𝔻`. -/
theorem s8q_res_data {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {F : ℂ → ℂ} (hF : F ∈ BCinf unitDisc)
    (hFΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, F (mob g z) = F z) :
    ContDiffOn ℝ (⊤ : ℕ∞) (resolventGammaD Γ F) unitDisc ∧
      (∃ C, ∀ z ∈ unitDisc, ‖resolventGammaD Γ F z‖ ≤ C) ∧
      (∀ g ∈ Γ, ∀ z ∈ unitDisc, resolventGammaD Γ F (mob g z) = resolventGammaD Γ F z) ∧
      ∀ z ∈ unitDisc, 2 * (laplace0 (resolventGammaD Γ F) z + (1 / 2) * resolventGammaD Γ F z) = F z := by
  obtain ⟨_, hGB, hGeq⟩ := RK3_disc.1 F hF
  have heq : ∀ z ∈ unitDisc, resolventGammaD Γ F z = resolventOp unitDisc F z := fun z hz => s8q_res_eq hΓ hF hFΓ hz
  obtain ⟨C, hC⟩ := hGB.2
  refine ⟨hGB.1.congr heq, ⟨C, fun z hz => by rw [heq z hz]; exact hC z hz⟩, fun g hg z hz => ?_, fun z hz => ?_⟩
  · show quotIntD Γ (fun u => (resolventKernelGamma Γ (mob g z) u : ℂ) * F u * rho u) =
      quotIntD Γ (fun u => (resolventKernelGamma Γ z u : ℂ) * F u * rho u)
    refine setIntegral_congr_fun (s8w_fundD hΓ).1 fun u hu => ?_
    beta_reduce
    rw [s8q_KG_inv hΓ hg hz ((s8w_fundD hΓ).2.1 hu)]
  · have e : resolventGammaD Γ F =ᶠ[𝓝 z] resolventOp unitDisc F :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) heq
    have e' : dzbar (resolventGammaD Γ F) =ᶠ[𝓝 z] dzbar (resolventOp unitDisc F) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) fun w hw =>
        s8q_dzbar_congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) heq)
    have hL : laplace0 (resolventGammaD Γ F) z = laplace0 (resolventOp unitDisc F) z := by
      show -((rho z : ℂ)⁻¹ * dz (dzbar (resolventGammaD Γ F)) z) = -((rho z : ℂ)⁻¹ * dz (dzbar (resolventOp unitDisc F)) z)
      rw [s7g_f2_dz_congr e']
    rw [hL, heq z hz]
    exact hGeq z hz

/-- **QA2 (STUB, assembly).** `μ κ̄` is a bounded smooth `Γ`-invariant function on `𝔻` (the phases cancel). -/
theorem s8q_fk_data {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {μ κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hκΓ : IsGammaInvD Γ κ) :
    (fun u => μ u * conj (κ u)) ∈ BCinf unitDisc ∧
      ∀ g ∈ Γ, ∀ z ∈ unitDisc, μ (mob g z) * conj (κ (mob g z)) = μ z * conj (κ z) := by
  have hμs : ContDiffOn ℝ (⊤ : ℕ∞) μ unitDisc := ((s8w_harmD_analytic hμ).contDiffOn isOpen_ball.uniqueDiffOn).of_le le_top
  have hκs : ContDiffOn ℝ (⊤ : ℕ∞) κ unitDisc := ((s8w_harmD_analytic hκ).contDiffOn isOpen_ball.uniqueDiffOn).of_le le_top
  have hcκ : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => conj (κ u)) unitDisc :=
    Complex.conjCLE.contDiff.comp_contDiffOn hκs
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  refine ⟨⟨hμs.mul hcκ, Cμ * Cκ, fun z hz => ?_⟩, fun g hg z hz => ?_⟩
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCμ z hz) (hCκ z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCμ z hz))
  · have hD := fdD_denom_ne (hΓ.1 g hg) (mem_ball_zero_iff.mp hz)
    have hd : deriv (mob g) z ≠ 0 := by
      rw [gam_mob_deriv hD]
      exact one_div_ne_zero (pow_ne_zero 2 hD)
    have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
    have h1 := hμΓ g hg z hz
    have h2 := hκΓ g hg z hz
    rw [← h1, ← h2]
    simp only [map_mul, map_div₀, Complex.conj_conj]
    field_simp

/-- **QA3 (STUB, assembly).** Equivariance of `∂̄h`, `q h`, `Δ₀ h` for `Γ`-invariant smooth `h` (chain rule through the
holomorphic `mob g`, and `ρ(γz)|γ'|² = ρ(z)`). -/
theorem s8q_equiv {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hhΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, h (mob g z) = h z) :
    ∀ g ∈ Γ, ∀ z ∈ unitDisc,
      dzbar h (mob g z) * conj (deriv (mob g) z) = dzbar h z ∧
        s7et_q h (mob g z) * (conj (deriv (mob g) z) / deriv (mob g) z) = s7et_q h z ∧
        laplace0 h (mob g z) = laplace0 h z := by
  exact s8q_equiv_aux hΓ hh hhΓ

/-- **QA4 (STUB, assembly).** The integrated polarized identity on `F` (Q1 cutoffs, Q2 applied to `χ_n · (P, Q)`,
Q3 pointwise, Q4 integrability, dominated convergence `n → ∞`). -/
theorem s8q_energy_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {h k : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (hk : ContDiffOn ℝ (⊤ : ℕ∞) k unitDisc)
    (hhΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, h (mob g z) = h z) (hkΓ : ∀ g ∈ Γ, ∀ z ∈ unitDisc, k (mob g z) = k z)
    {C : ℝ} (hhb : ∀ z ∈ unitDisc, ‖h z‖ ≤ C) (hkb : ∀ z ∈ unitDisc, ‖k z‖ ≤ C)
    (hhΔ : ∀ z ∈ unitDisc, ‖laplace0 h z‖ ≤ C) (hkΔ : ∀ z ∈ unitDisc, ‖laplace0 k z‖ ≤ C) :
    IntegrableOn (fun z => s7et_q h z * conj (s7et_q k z) * rho z) (fundDomainOn Γ unitDisc) ∧
      ∫ z in fundDomainOn Γ unitDisc, (s7et_q h z * conj (s7et_q k z) * rho z -
        laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z) = 0 := by
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hhb 0 (mem_ball_self one_pos))
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hhd : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc := wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hkd : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar k) unitDisc := wp_contDiffOn_dzbar hk isOpen_ball (by simp)
  have hqh : ContDiffOn ℝ (⊤ : ℕ∞) (s7et_q h) unitDisc := wp_contDiffOn_dzbar (ha.mul hhd) isOpen_ball (by simp)
  have hqk : ContDiffOn ℝ (⊤ : ℕ∞) (s7et_q k) unitDisc := wp_contDiffOn_dzbar (ha.mul hkd) isOpen_ball (by simp)
  have hLh : ContDiffOn ℝ (⊤ : ℕ∞) (laplace0 h) unitDisc :=
    (ha.mul (wp_contDiffOn_dz hhd isOpen_ball (by simp))).neg
  have hLk : ContDiffOn ℝ (⊤ : ℕ∞) (laplace0 k) unitDisc :=
    (ha.mul (wp_contDiffOn_dz hkd isOpen_ball (by simp))).neg
  have hcqk : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (s7et_q k w)) unitDisc :=
    Complex.conjCLE.contDiff.comp_contDiffOn hqk
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => laplace0 k w + (1 / 2 : ℂ) * k w) unitDisc :=
    hLk.add (contDiffOn_const.mul hk)
  have hcR : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => conj (laplace0 k w + (1 / 2 : ℂ) * k w)) unitDisc :=
    Complex.conjCLE.contDiff.comp_contDiffOn hR
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => dzbar h w * conj (s7et_q k w)) unitDisc := hhd.mul hcqk
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => dzbar h w * conj (laplace0 k w + (1 / 2 : ℂ) * k w)) unitDisc :=
    hhd.mul hcR
  have diff (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ f w :=
    (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have aesm (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) :
      AEStronglyMeasurable f (volume.restrict (fundDomainOn Γ unitDisc)) :=
    (hf.continuousOn.mono hFD).aestronglyMeasurable hFm
  have hρm : AEStronglyMeasurable (fun z => (rho z : ℂ)) (volume.restrict (fundDomainOn Γ unitDisc)) :=
    (Complex.measurable_ofReal.comp gam_rho_measurable).aestronglyMeasurable
  have hρi : IntegrableOn (fun z => rho z) (fundDomainOn Γ unitDisc) := s8w_rho_integrableOn (s8w_area_fin hΓ)
  -- Caccioppoli for `h` and `k`
  obtain ⟨hDh, hQh⟩ := s8q_caccioppoli hΓ hh hhΓ hhb hhΔ
  obtain ⟨-, hQk⟩ := s8q_caccioppoli hΓ hk hkΓ hkb hkΔ
  -- the `q`-pairing is integrable
  have hA : IntegrableOn (fun z => s7et_q h z * conj (s7et_q k z) * rho z) (fundDomainOn Γ unitDisc) := by
    refine Integrable.mono' (hQh.add hQk) (((aesm _ hqh).mul (aesm _ hcqk)).mul hρm) ?_
    filter_upwards with z
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (s8q_rho_nonneg z)]
    have hr := s8q_rho_nonneg z
    have hkey := mul_nonneg hr (add_nonneg (sq_nonneg (‖s7et_q h z‖ - ‖s7et_q k z‖))
      (mul_nonneg (norm_nonneg (s7et_q h z)) (norm_nonneg (s7et_q k z))))
    show ‖s7et_q h z‖ * ‖s7et_q k z‖ * rho z ≤ ‖s7et_q h z‖ ^ 2 * rho z + ‖s7et_q k z‖ ^ 2 * rho z
    nlinarith [hkey]
  refine ⟨hA, ?_⟩
  -- the lower-order terms
  have hB := s8q_bdd_int hΓ (U := fun z => laplace0 h z * conj (laplace0 k z))
    (hLh.continuousOn.mul (Complex.continuous_conj.comp_continuousOn hLk.continuousOn)) (C := C * C) fun z hz => by
      rw [norm_mul, Complex.norm_conj]; exact mul_le_mul (hhΔ z hz) (hkΔ z hz) (norm_nonneg _) hC0
  have hE := s8q_bdd_int hΓ (U := fun z => (1 / 2 : ℂ) * laplace0 h z * conj (k z))
    ((continuousOn_const.mul hLh.continuousOn).mul (Complex.continuous_conj.comp_continuousOn hk.continuousOn))
    (C := C * C) fun z hz => by
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_div, norm_one, Complex.norm_two]
      have := mul_le_mul (hhΔ z hz) (hkb z hz) (norm_nonneg _) hC0
      nlinarith [norm_nonneg (laplace0 h z), norm_nonneg (k z), mul_nonneg (norm_nonneg (laplace0 h z)) (norm_nonneg (k z))]
  have hDi : IntegrableOn (fun z => s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z)
      (fundDomainOn Γ unitDisc) := (hA.sub hB).sub hE
  -- cutoffs
  obtain ⟨χ, Cχ, hχs, hχ01, hχΓ, hχK, hχev, hχd, -⟩ := s8q_cutoff hΓ.1
  have hχc : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (χ n w : ℂ)) unitDisc := fun n =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχs n)
  have hCχ : 0 ≤ Cχ := by
    have := hχd 0 0 (mem_ball_self one_pos)
    have h2 : 0 ≤ Real.sqrt (rho 0) := Real.sqrt_nonneg _
    by_contra hneg
    push_neg at hneg
    have : Cχ * Real.sqrt (rho 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le h2
    have hρ0 : 0 < Real.sqrt (rho 0) := Real.sqrt_pos.mpr (by unfold rho; norm_num)
    nlinarith [norm_nonneg (dz (fun w => (χ 0 w : ℂ)) 0), mul_pos_of_neg_of_neg hneg (neg_neg_of_pos hρ0)]
  -- equivariance of `∂̄h`, `q k`, `Δ₀ k`
  have hEh := s8q_equiv hΓ.1 hh hhΓ
  have hEk := s8q_equiv hΓ.1 hk hkΓ
  have hderiv : ∀ g ∈ Γ, ∀ z ∈ unitDisc, deriv (mob g) z ≠ 0 := fun g hg z hz => by
    have hD := fdD_denom_ne (hΓ.1.1 g hg) (mem_ball_zero_iff.mp hz)
    rw [gam_mob_deriv hD]
    exact one_div_ne_zero (pow_ne_zero 2 hD)
  -- the divergence theorem for `χ_n (P, Q)`
  have hdiv : ∀ n, ∫ z in fundDomainOn Γ unitDisc,
      (dzbar (fun w => (χ n w : ℂ) * (dzbar h w * conj (s7et_q k w))) z +
        dz (fun w => (χ n w : ℂ) * (dzbar h w * conj (laplace0 k w + (1 / 2 : ℂ) * k w))) z) = 0 := by
    intro n
    refine (s8q_div_zero hΓ.1 (((hχc n).mul hP).of_le (by simp)) (((hχc n).mul hQ).of_le (by simp))
      (fun g hg z hz => ?_) (fun g hg z hz => ?_) ?_).2
    · have hd := hderiv g hg z hz
      have hcd : conj (deriv (mob g) z) ≠ 0 := (map_ne_zero _).mpr hd
      obtain ⟨e1, -, -⟩ := hEh g hg z hz
      obtain ⟨-, e2, -⟩ := hEk g hg z hz
      have hgz : mob g z ∈ unitDisc := mem_ball_zero_iff.mpr (fdD_mob_lt (hΓ.1.1 g hg) (mem_ball_zero_iff.mp hz))
      show (χ n (mob g z) : ℂ) * (dzbar h (mob g z) * conj (s7et_q k (mob g z))) * deriv (mob g) z =
        (χ n z : ℂ) * (dzbar h z * conj (s7et_q k z))
      rw [hχΓ n g hg z hz, ← e1, ← e2]
      simp only [map_mul, map_div₀, Complex.conj_conj]
      field_simp
    · obtain ⟨e1, -, e3⟩ := hEh g hg z hz
      obtain ⟨-, -, e4⟩ := hEk g hg z hz
      show (χ n (mob g z) : ℂ) * (dzbar h (mob g z) * conj (laplace0 k (mob g z) + (1 / 2 : ℂ) * k (mob g z))) *
          conj (deriv (mob g) z) = (χ n z : ℂ) * (dzbar h z * conj (laplace0 k z + (1 / 2 : ℂ) * k z))
      rw [hχΓ n g hg z hz, ← e1, e4, hkΓ g hg z hz]
      ring
    · obtain ⟨K, hK, hKD, hKm⟩ := hχK n
      refine ⟨K, hK, hKD, fun z hz hne => hKm z hz fun h0 => ?_⟩
      rcases hne with hne | hne <;> exact hne (by rw [h0]; simp)
  -- product rule: `div(χ (P, Q)) = χ D + (P ∂̄χ + Q ∂χ)`
  have hpt : ∀ n, ∀ z ∈ unitDisc,
      dzbar (fun w => (χ n w : ℂ) * (dzbar h w * conj (s7et_q k w))) z +
        dz (fun w => (χ n w : ℂ) * (dzbar h w * conj (laplace0 k w + (1 / 2 : ℂ) * k w))) z =
      (χ n z : ℂ) * (s7et_q h z * conj (s7et_q k z) * rho z - laplace0 h z * conj (laplace0 k z) * rho z -
          (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z) +
        (dzbar h z * conj (s7et_q k z) * dzbar (fun w => (χ n w : ℂ)) z +
          dzbar h z * conj (laplace0 k z + (1 / 2 : ℂ) * k z) * dz (fun w => (χ n w : ℂ)) z) := by
    intro n z hz
    rw [dzbar_mul (diff _ (hχc n) z hz) (diff _ hP z hz), dz_mul (diff _ (hχc n) z hz) (diff _ hQ z hz),
      s8q_energy_pt hh hk hz]
    ring
  -- error term
  set Er : ℕ → ℂ → ℂ := fun n z => dzbar h z * conj (s7et_q k z) * dzbar (fun w => (χ n w : ℂ)) z +
    dzbar h z * conj (laplace0 k z + (1 / 2 : ℂ) * k z) * dz (fun w => (χ n w : ℂ)) z with hEr
  have hdzb : ∀ n z, dzbar (fun w => (χ n w : ℂ)) z = conj (dz (fun w => (χ n w : ℂ)) z) := fun n z => by
    have := p71r_dzbar_conj (fun w => (χ n w : ℂ)) z
    simpa only [Complex.conj_ofReal] using this
  have hRb : ∀ z ∈ unitDisc, ‖laplace0 k z + (1 / 2 : ℂ) * k z‖ ≤ 2 * C := fun z hz => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_div, norm_one, Complex.norm_two]
    linarith [hkΔ z hz, hkb z hz, norm_nonneg (k z)]
  have hbound : IntegrableOn (fun z => Cχ * (1 + 2 * C) * (‖dzbar h z‖ ^ 2 + ‖s7et_q k z‖ ^ 2 * rho z + rho z))
      (fundDomainOn Γ unitDisc) := ((hDh.add hQk).add hρi).const_mul _
  have hEb : ∀ n, ∀ z ∈ unitDisc, ‖Er n z‖ ≤
      Cχ * (1 + 2 * C) * (‖dzbar h z‖ ^ 2 + ‖s7et_q k z‖ ^ 2 * rho z + rho z) := by
    intro n z hz
    have hd := hχd n z hz
    have hs := Real.sqrt_nonneg (rho z)
    have hss : Real.sqrt (rho z) ^ 2 = rho z := Real.sq_sqrt (s8q_rho_nonneg z)
    have hR := hRb z hz
    show ‖dzbar h z * conj (s7et_q k z) * dzbar (fun w => (χ n w : ℂ)) z +
        dzbar h z * conj (laplace0 k z + (1 / 2 : ℂ) * k z) * dz (fun w => (χ n w : ℂ)) z‖ ≤ _
    have e1 : ‖dzbar h z * conj (s7et_q k z) * dzbar (fun w => (χ n w : ℂ)) z‖ =
        ‖dzbar h z‖ * ‖s7et_q k z‖ * ‖dz (fun w => (χ n w : ℂ)) z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, hdzb, Complex.norm_conj]
    have e2 : ‖dzbar h z * conj (laplace0 k z + (1 / 2 : ℂ) * k z) * dz (fun w => (χ n w : ℂ)) z‖ =
        ‖dzbar h z‖ * ‖laplace0 k z + (1 / 2 : ℂ) * k z‖ * ‖dz (fun w => (χ n w : ℂ)) z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj]
    refine (norm_add_le _ _).trans ?_
    rw [e1, e2, ← hss]
    have ha0 := norm_nonneg (dzbar h z)
    have hb0 := norm_nonneg (s7et_q k z)
    have hr0 := norm_nonneg (laplace0 k z + (1 / 2 : ℂ) * k z)
    have hd0 := norm_nonneg (dz (fun w => (χ n w : ℂ)) z)
    generalize ‖dzbar h z‖ = a at *
    generalize ‖s7et_q k z‖ = b at *
    generalize ‖laplace0 k z + (1 / 2 : ℂ) * k z‖ = r at *
    generalize ‖dz (fun w => (χ n w : ℂ)) z‖ = d at *
    generalize Real.sqrt (rho z) = t at *
    have h2C : 0 ≤ 2 * C := by linarith
    have h1 : a * b * d ≤ Cχ * (a * b * t) := by
      have := mul_le_mul_of_nonneg_left hd (mul_nonneg ha0 hb0)
      linarith
    have h2 : a * r * d ≤ Cχ * (2 * C) * (a * t) := by
      have h3 := mul_le_mul hR hd hd0 h2C
      have := mul_le_mul_of_nonneg_left h3 ha0
      linarith
    have h4 : a * b * t ≤ (a ^ 2 + b ^ 2 * t ^ 2) / 2 := by nlinarith [sq_nonneg (a - b * t)]
    have h5 : a * t ≤ (a ^ 2 + t ^ 2) / 2 := by nlinarith [sq_nonneg (a - t)]
    have h6 := mul_le_mul_of_nonneg_left h4 hCχ
    have h7 := mul_le_mul_of_nonneg_left h5 (mul_nonneg hCχ h2C)
    have hCC := mul_nonneg hCχ hC0
    nlinarith [mul_nonneg hCχ (sq_nonneg a), mul_nonneg hCχ (sq_nonneg t),
      mul_nonneg hCχ (mul_nonneg (sq_nonneg b) (sq_nonneg t)), mul_nonneg hCC (sq_nonneg a),
      mul_nonneg hCC (sq_nonneg t), mul_nonneg hCC (mul_nonneg (sq_nonneg b) (sq_nonneg t))]
  have hEri : ∀ n, IntegrableOn (Er n) (fundDomainOn Γ unitDisc) := fun n => by
    refine Integrable.mono' hbound ?_ ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => hEb n z (hFD hz)))
    have hχb : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar fun w => (χ n w : ℂ)) unitDisc :=
      wp_contDiffOn_dzbar (hχc n) isOpen_ball (by simp)
    have hχa : ContDiffOn ℝ (⊤ : ℕ∞) (dz fun w => (χ n w : ℂ)) unitDisc :=
      wp_contDiffOn_dz (hχc n) isOpen_ball (by simp)
    exact ((aesm _ hP).mul (aesm _ hχb)).add ((aesm _ hQ).mul (aesm _ hχa))
  have hχD : ∀ n, IntegrableOn (fun z => (χ n z : ℂ) * (s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z))
      (fundDomainOn Γ unitDisc) := fun n => by
    refine Integrable.mono' hDi.norm ((aesm _ (hχc n)).mul hDi.aestronglyMeasurable)
      ((ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ01 n z (hFD hz)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 n z (hFD hz)).2
  -- `∫ χ_n D = - ∫ Er n`
  have hrel : ∀ n, ∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z) =
      -∫ z in fundDomainOn Γ unitDisc, Er n z := by
    intro n
    have e := hdiv n
    rw [setIntegral_congr_fun hFm fun z hz => hpt n z (hFD hz), integral_add (hχD n) (hEri n)] at e
    exact eq_neg_of_add_eq_zero_left e
  -- limits
  have hev1 : ∀ z ∈ unitDisc, ∀ᶠ n in atTop, χ n z = 1 := fun z hz =>
    (hχev z hz).mono fun n hn => hn.self_of_nhds
  have hev0 : ∀ z ∈ unitDisc, ∀ᶠ n in atTop, dz (fun w => (χ n w : ℂ)) z = 0 := fun z hz =>
    (hχev z hz).mono fun n hn => by
      have e : (fun w => (χ n w : ℂ)) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := hn.mono fun w hw => by
        show (χ n w : ℂ) = 1
        rw [hw]
        simp
      rw [s7g_f2_dz_congr e]
      exact (l613_dz_const 1 z).1
  have hlim1 : Tendsto (fun n => ∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z)) atTop
      (𝓝 (∫ z in fundDomainOn Γ unitDisc, (s7et_q h z * conj (s7et_q k z) * rho z -
        laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z‖)
      (fun n => (hχD n).aestronglyMeasurable) hDi.norm (fun n => ?_) ?_
    · refine (ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ01 n z (hFD hz)).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 n z (hFD hz)).2
    · refine (ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev1 z (hFD hz)] with n hn
      rw [hn, Complex.ofReal_one, one_mul]
  have hlim2 : Tendsto (fun n => ∫ z in fundDomainOn Γ unitDisc, Er n z) atTop (𝓝 0) := by
    have h0 : (0 : ℂ) = ∫ z in fundDomainOn Γ unitDisc, (0 : ℂ) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence _ (fun n => (hEri n).aestronglyMeasurable) hbound
      (fun n => (ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => hEb n z (hFD hz))) ?_
    refine (ae_restrict_iff' hFm).mpr (Eventually.of_forall fun z hz => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev0 z (hFD hz)] with n hn
    simp only [hEr, hdzb, hn, map_zero, mul_zero, add_zero]
  have hlim3 := hlim2.neg
  rw [neg_zero] at hlim3
  have hlim4 : Tendsto (fun n => ∫ z in fundDomainOn Γ unitDisc, (χ n z : ℂ) * (s7et_q h z * conj (s7et_q k z) * rho z -
      laplace0 h z * conj (laplace0 k z) * rho z - (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z)) atTop (𝓝 0) :=
    hlim3.congr fun n => (hrel n).symm
  exact tendsto_nhds_unique hlim1 hlim4

/-- `conj (G_Γ \bar U) = G_Γ U` (the kernel is real). -/
theorem s8q_conj_res (Γ : Subgroup SL2C) (U : ℂ → ℂ) (z : ℂ) :
    conj (resolventGammaD Γ (fun u => conj (U u)) z) = resolventGammaD Γ U z := by
  show conj (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * conj (U u) * rho u) =
    ∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * U u * rho u
  rw [← integral_conj]
  congr 1
  funext u
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]

/-- `G_Γ` is self-adjoint on bounded continuous data: `(G_Γ U, V)_Γ = (U, G_Γ V)_Γ`. -/
theorem s8q_selfadj {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {U V : ℂ → ℂ} (hU : ContinuousOn U unitDisc)
    (hV : ContinuousOn V unitDisc) {CU CV : ℝ} (hUb : ∀ z ∈ unitDisc, ‖U z‖ ≤ CU)
    (hVb : ∀ z ∈ unitDisc, ‖V z‖ ≤ CV) :
    innerGamma Γ (resolventGammaD Γ U) V = innerGamma Γ U (resolventGammaD Γ V) := by
  have hcU : ContinuousOn (fun z => conj (U z)) unitDisc := Complex.continuous_conj.comp_continuousOn hU
  have hcV : ContinuousOn (fun z => conj (V z)) unitDisc := Complex.continuous_conj.comp_continuousOn hV
  have hcUb : ∀ z ∈ unitDisc, ‖conj (U z)‖ ≤ CU := fun z hz => by rw [Complex.norm_conj]; exact hUb z hz
  have hcVb : ∀ z ∈ unitDisc, ‖conj (V z)‖ ≤ CV := fun z hz => by rw [Complex.norm_conj]; exact hVb z hz
  have h1 := s8q_sym_core hΓ hcV hcU hcVb hcUb
  calc innerGamma Γ (resolventGammaD Γ U) V
      = innerGamma Γ (fun z => conj (V z)) (resolventGammaD Γ fun z => conj (U z)) := by
        show (∫ z in fundDomainOn Γ unitDisc, resolventGammaD Γ U z * conj (V z) * rho z) =
          ∫ z in fundDomainOn Γ unitDisc, conj (V z) * conj (resolventGammaD Γ (fun z => conj (U z)) z) * rho z
        congr 1
        funext z
        rw [s8q_conj_res]
        ring
    _ = innerGamma Γ (fun z => conj (conj (U z))) (resolventGammaD Γ fun z => conj (conj (V z))) := h1
    _ = innerGamma Γ U (resolventGammaD Γ V) := by simp only [Complex.conj_conj]

/-- STUB FV. The first variation vanishes: `∂/∂ε|₀ g_{μν̄}(εκ) = 0`. -/
theorem s8g_fv {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) (hκΓ : IsGammaInvD Γ κ) :
    dz (fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 = 0 := by
  have hU := measurableSet_upperHalf_aux
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hCκ0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ 0 h0D)
  have hd0 : ∀ u ∈ upperHalf, 2 * I / (u + I) ^ 2 ≠ 0 := fun u hu =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
  have hph1 : ∀ u ∈ upperHalf, ‖conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)‖ = 1 := fun u hu => by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (hd0 u hu))]
  have hphc : ContinuousOn (fun u => conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) upperHalf := by
    have hc : ContinuousOn (fun u : ℂ => 2 * I / (u + I) ^ 2) upperHalf :=
      continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
        fun u hu => pow_ne_zero _ (cayley_den_ne_zero hu)
    exact (Complex.continuous_conj.comp_continuousOn hc).div hc hd0
  have hcayc : ContinuousOn cayley upperHalf := fun u hu =>
    (rhoU_hasDerivAt_cayley hu).continuousAt.continuousWithinAt
  have hcm : MapsTo cayley upperHalf unitDisc := fun u hu => isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have htr : ∀ {f : ℂ → ℂ}, IsHarmonicD f →
      ContinuousOn (fun u => f (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) upperHalf :=
    fun hf => ((harmonicD_continuousOn hf).comp hcayc hcm).mul hphc
  have hYc := htr hμ
  obtain ⟨φa, ha, hak0⟩ := s8g_c_kD hκ hCκ
  obtain ⟨φY, hY, hYk⟩ := s8g_c_kD hμ hCμ
  generalize hadef : (fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) = a at ha hak0
  generalize hYdef : (fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) = Y at hY hYk hYc
  have hk := hCκ0
  have hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ Cκ := fun u hu => by rw [← hadef]; exact hak0 u hu
  obtain ⟨hEm, hEU, -⟩ := s8g_cayE hΓ.1
  have hEA := s8g_cayE_area hΓ
  set E := upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc with hEdef
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℂ, A = fun s =>
      conj (ν (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ → ℂ, B = fun s => conj (Y s) := ⟨_, rfl⟩
  have hBY : ∀ t, conj (B t) = Y t := fun t => by rw [hBdef, Complex.conj_conj]
  have hAc : ContinuousOn A E := by
    rw [hAdef]
    exact (Complex.continuous_conj.comp_continuousOn (htr hν)).mono hEU
  have hBc : ContinuousOn B upperHalf := by
    rw [hBdef]
    exact Complex.continuous_conj.comp_continuousOn hYc
  have hAb : ∀ s ∈ E, ‖A s‖ ≤ Cν := fun s hs => by
    rw [hAdef]
    show ‖conj (ν (cayley s) * _)‖ ≤ Cν
    rw [Complex.norm_conj, norm_mul, hph1 s (hEU hs), mul_one]
    exact hCν _ (hcm (hEU hs))
  have hBb : ∀ s ∈ upperHalf, ‖B s‖ ≤ Cμ := fun s hs => by
    rw [hBdef, Complex.norm_conj, ← hYdef]
    exact hYk s hs
  -- the 4-parameter family with `b = a`, and its 2-parameter restriction
  obtain ⟨σ, hσ⟩ : ∃ σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * a u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (a (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = fun Q => normalizedSolution (σ Q) := ⟨_, rfl⟩
  have hW' : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * a u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (a (conj u)) else 0) := by
    rw [hW, hσ]
  obtain ⟨W2, hW2⟩ : ∃ W2 : ℂ × ℂ → ℂ → ℂ, W2 = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then a u else 0) + P.2 * (if u.im < 0 then conj (a (conj u)) else 0) := ⟨_, rfl⟩
  have hWW : ∀ x y : ℂ, W ((x, 0), (y, 0)) = W2 (x, y) := by
    intro x y
    simp only [hW', hW2]
    congr 1
    funext u
    split_ifs <;> ring
  obtain ⟨R0, hR0p, hR0k2, M, hM⟩ := s8g_c_L1 ha ha hk hak hak hW' hEm hEU hU subset_rfl hEA hAb hBb
  have hR0k : R0 * Cκ < 1 := by nlinarith
  have hρk : ∀ Q : (ℂ × ℂ) × (ℂ × ℂ), ‖Q‖ ≤ R0 → ‖Q‖ * (2 * Cκ) < 1 := fun Q hQ => by
    calc ‖Q‖ * (2 * Cκ) ≤ R0 * (2 * Cκ) := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ < 1 := by linarith
  have hn4 : ∀ x y : ℂ, ‖(((x, 0), (y, 0)) : (ℂ × ℂ) × (ℂ × ℂ))‖ = ‖((x, y) : ℂ × ℂ)‖ := fun x y => by
    simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have hTm : MeasurableSet (E ×ˢ upperHalf) := hEm.prod hU
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℂ × ℂ → ℂ, G2 = fun P => ∫ x in E ×ˢ upperHalf, A x.1 * (conj (B x.2) *
      (dz (W ((P.1, 0), (P.2, 0))) x.2 * dz (W ((P.1, 0), (P.2, 0))) (conj x.1) /
        (W ((P.1, 0), (P.2, 0)) x.2 - W ((P.1, 0), (P.2, 0)) (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  -- holomorphy of `G2` along complex lines
  have hline : ∀ (L : ℂ → ℂ × ℂ) (P₀ e : ℂ × ℂ), (∀ t, L t = P₀ + t • e) →
      ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → (∀ t ∈ closedBall c ρ, ‖L t‖ ≤ R0) →
        DifferentiableAt ℂ (fun t => G2 (L t)) c := by
    intro L P₀ e hL c ρ hρ hc
    have hQ : ∀ t : ℂ, (((P₀.1, 0), (P₀.2, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) + t • ((e.1, 0), (e.2, 0)) =
        (((L t).1, 0), ((L t).2, 0)) := fun t => by
      rw [hL]
      ext <;> simp
    obtain ⟨-, hd⟩ := s8g_c_dir ha ha hk hak hak hσ hW hEm hEU hU subset_rfl hAc hBc
      (Q₀ := ((P₀.1, 0), (P₀.2, 0))) (e := ((e.1, 0), (e.2, 0))) (c := c) (ρ := ρ)
      (fun t ht => by rw [hQ]; exact hρk _ (by rw [hn4]; exact hc t ht)) (M := M)
      (fun t ht => by rw [hQ]; exact hM _ (mem_closedBall_zero_iff.2 (by rw [hn4]; exact hc t ht)))
    have hd' := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
    simp only [hQ] at hd'
    rw [hG2]
    exact hd'
  have hRp : ∀ p : ℂ × ℂ, ‖p‖ < R0 → ∀ x : ℂ, ‖x‖ ≤ ‖p‖ →
      ∀ t ∈ closedBall x ((R0 - ‖p‖) / 2), ‖t‖ ≤ R0 := by
    intro p hp' x hx t ht
    have h1 : ‖t‖ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by
      have := mem_closedBall.1 ht
      rw [dist_eq_norm] at this
      calc ‖t‖ = ‖x + (t - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖t - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by linarith
    linarith
  have hUo : IsOpen (ball (0 : ℂ × ℂ) R0) := isOpen_ball
  have h1 : ∀ p ∈ ball (0 : ℂ × ℂ) R0, DifferentiableAt ℂ (fun z => G2 (z, p.2)) p.1 := by
    intro p hp
    have hp' : ‖p‖ < R0 := mem_ball_zero_iff.1 hp
    exact hline (fun z => (z, p.2)) (0, p.2) (1, 0) (fun t => by ext <;> simp) p.1 _ (by linarith)
      fun t ht => norm_prod_le_iff.2 ⟨hRp p hp' _ (norm_fst_le p) t ht, (norm_snd_le p).trans hp'.le⟩
  have h2 : ∀ p ∈ ball (0 : ℂ × ℂ) R0, DifferentiableAt ℂ (fun w => G2 (p.1, w)) p.2 := by
    intro p hp
    have hp' : ‖p‖ < R0 := mem_ball_zero_iff.1 hp
    exact hline (fun w => (p.1, w)) (p.1, 0) (0, 1) (fun t => by ext <;> simp) p.2 _ (by linarith)
      fun t ht => norm_prod_le_iff.2 ⟨(norm_fst_le p).trans hp'.le, hRp p hp' _ (norm_snd_le p) t ht⟩
  have hbd : ∀ P : ℂ × ℂ, ‖P‖ ≤ R0 → ‖G2 P‖ ≤ max M 0 := by
    intro P hP
    have hP4 : (((P.1, 0), (P.2, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
      rw [mem_closedBall_zero_iff, hn4]
      exact hP
    have e1 := (enorm_integral_le_lintegral_enorm (μ := volume.restrict (E ×ˢ upperHalf)) _).trans (hM _ hP4)
    have e2 : ENNReal.ofReal ‖G2 P‖ ≤ ENNReal.ofReal (max M 0) := by
      rw [ofReal_norm, hG2]
      exact e1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 e2
  have hb : ∀ p ∈ ball (0 : ℂ × ℂ) R0, ∃ ρ > 0, ∃ M' : ℝ, ∀ q ∈ ball p ρ, ‖G2 q‖ ≤ M' := by
    intro p hp
    obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hUo p hp
    exact ⟨ρ, hρ, max M 0, fun q hq => hbd q (mem_ball_zero_iff.1 (hsub hq)).le⟩
  have hG2c : ContDiffOn ℂ 1 G2 (ball (0 : ℂ × ℂ) R0) := s7g_h_contDiffOn hUo 1 G2 h1 h2 hb
  have hG2d : DifferentiableAt ℂ G2 ((0 : ℂ), (0 : ℂ)) :=
    (hG2c.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds (mem_ball_self hR0p))
  obtain ⟨H, hH⟩ : ∃ H : ℂ × ℂ → ℂ, H = fun P => (12 / π : ℂ) * G2 (P.2, P.1) := ⟨_, rfl⟩
  have hHd : DifferentiableAt ℂ H (conj (0 : ℂ), (0 : ℂ)) := by
    rw [map_zero, hH]
    have hswap : DifferentiableAt ℂ (fun P : ℂ × ℂ => (P.2, P.1)) ((0 : ℂ), (0 : ℂ)) :=
      differentiableAt_snd.prodMk differentiableAt_fst
    exact (differentiableAt_const _).mul
      (DifferentiableAt.comp (g := G2) ((0 : ℂ), (0 : ℂ)) (by simpa using hG2d) hswap)
  -- the representation `g(εκ) = H(ε̄, ε)` near `0`
  obtain ⟨δ₀, hδ0, hδ1, C3, hC3⟩ := s8w_density
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (δ₀ / (Cκ + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  have hrep : ∀ ε ∈ ball (0 : ℂ) r, gGamma Γ μ ν (fun z => ε * κ z) = H (conj ε, ε) := by
    intro ε hε
    have hεr : ‖ε‖ < r := mem_ball_zero_iff.1 hε
    have hεR : ‖ε‖ < R0 := lt_of_lt_of_le hεr hrR
    have hεδ : ‖ε‖ * (Cκ + 1) < δ₀ := by
      have h := lt_of_lt_of_le hεr (show r ≤ δ₀ / (Cκ + 1) by rw [hr]; exact min_le_right _ _)
      rwa [lt_div_iff₀ (by positivity)] at h
    have hκp : IsHarmonicD (fun z => ε * κ z) := by
      refine (congrArg IsHarmonicD ?_).mp (s8g_harm_lin (s8g_harm_lin hκ hκ (-1)) hκ ε)
      funext z
      ring
    have hκpΓ : IsGammaInvD Γ (fun z => ε * κ z) := by
      refine (congrArg (IsGammaInvD Γ) ?_).mp (s8g_inv_lin (s8g_inv_lin hκΓ hκΓ (-1)) hκΓ ε)
      funext z
      ring
    have hbdε : ∀ z ∈ unitDisc, ‖ε * κ z‖ ≤ ‖ε‖ * Cκ := fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCκ z hz) (norm_nonneg _)
    have hkδ : ‖ε‖ * Cκ < δ₀ := by nlinarith [norm_nonneg ε]
    have hC := hC3 _ hκp fun z hz => lt_of_le_of_lt (hbdε z hz) hkδ
    obtain ⟨Pst, hPst⟩ : ∃ Pst : (ℂ × ℂ) × (ℂ × ℂ), Pst = ((ε, 0), (conj ε, 0)) := ⟨_, rfl⟩
    have hPmem : Pst ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
      rw [hPst, mem_closedBall_zero_iff, hn4]
      refine norm_prod_le_iff.2 ⟨hεR.le, ?_⟩
      rw [Complex.norm_conj]
      exact hεR.le
    have hm : ∀ u ∈ upperHalf, (ε, (0 : ℂ)).1 * a u + (ε, (0 : ℂ)).2 * a u =
        (fun z => ε * κ z) (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
      intro u _
      rw [← hadef]
      simp only []
      ring
    have hq : (((ε, (0 : ℂ)).1, (ε, (0 : ℂ)).2), (conj (ε, (0 : ℂ)).1, conj (ε, (0 : ℂ)).2)) = Pst := by
      rw [hPst, map_zero]
    have hrep0 := s8g_c_line2U hΓ hμ hν hμΓ hνΓ hκp hκpΓ (lt_trans hkδ hδ1) hbdε hC ha ha hk hak hak hW'
      hR0p.le hR0k2 (q := (ε, 0)) (hq ▸ hPmem) hm
    rw [hq] at hrep0
    obtain ⟨hcP, -⟩ := s8g_c_dir ha ha hk hak hak hσ hW hEm hEU hU subset_rfl hAc hBc (Q₀ := Pst)
      (e := 0) (c := 0) (ρ := 1)
      (fun t _ => by rw [smul_zero, add_zero]; exact hρk _ (mem_closedBall_zero_iff.1 hPmem))
      (M := M) (fun t _ => by rw [smul_zero, add_zero]; exact hM _ hPmem)
    simp only [smul_zero, add_zero] at hcP
    have hcF : ContinuousOn (fun x : ℂ × ℂ => A x.1 * (conj (B x.2) *
        (dz (W Pst) x.2 * dz (W Pst) (conj x.1) / (W Pst x.2 - W Pst (conj x.1)) ^ 2) ^ 2))
        (E ×ˢ upperHalf) :=
      hcP.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => (⟨mem_closedBall_self zero_le_one, hx⟩ :
          ((0 : ℂ), x) ∈ closedBall (0 : ℂ) 1 ×ˢ (E ×ˢ upperHalf)))
    have hint : Integrable (fun x : ℂ × ℂ => A x.1 * (conj (B x.2) *
        (dz (W Pst) x.2 * dz (W Pst) (conj x.1) / (W Pst x.2 - W Pst (conj x.1)) ^ 2) ^ 2))
        ((volume.restrict E).prod (volume.restrict upperHalf)) := by
      rw [Measure.prod_restrict]
      exact ⟨hcF.aestronglyMeasurable hTm, lt_of_le_of_lt (hM _ hPmem) ENNReal.ofReal_lt_top⟩
    have hprod := integral_prod _ hint
    have eG : G2 (ε, conj ε) = ∫ s in E, ∫ t in upperHalf, A s * (conj (B t) *
        (dz (W Pst) t * dz (W Pst) (conj s) / (W Pst t - W Pst (conj s)) ^ 2) ^ 2) := by
      rw [hG2, ← hprod, Measure.prod_restrict, hPst]
      rfl
    rw [hrep0, hH]
    show _ = (12 / π : ℂ) * G2 (ε, conj ε)
    rw [eG]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [hAdef, hBY, ← hYdef]
  have hev : (fun ε => gGamma Γ μ ν (fun z => ε * κ z)) =ᶠ[𝓝 (0 : ℂ)] fun y => H (conj y, y) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr0] with ε hε
    exact hrep ε hε
  have hdz : dz (fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 = dz (fun y => H (conj y, y)) 0 := by
    simp only [dz, hev.fderiv_eq]
  rw [hdz, s7g_dz_partial hHd, map_zero]
  -- `∂_b H(0, b)|₀ = (12/π) ∂_b G2(b, 0)|₀`, differentiated under the integral sign
  have hG2b : DifferentiableAt ℂ (fun b => G2 (b, 0)) 0 := h1 (0, 0) (mem_ball_self hR0p)
  have eH : (fun b => H (0, b)) = fun b => (12 / π : ℂ) * G2 (b, 0) := by rw [hH]
  rw [eH, deriv_const_mul _ hG2b]
  have h0Q : ∀ t : ℂ, (0 : (ℂ × ℂ) × (ℂ × ℂ)) + t • (((1 : ℂ), (0 : ℂ)), ((0 : ℂ), (0 : ℂ))) =
      ((t, 0), (0, 0)) := fun t => by ext <;> simp
  have hz4 : ∀ z : ℂ, ‖z‖ ≤ R0 →
      (((z, 0), (0, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := fun z hz => by
    rw [mem_closedBall_zero_iff, hn4]
    exact norm_prod_le_iff.2 ⟨hz, by rw [norm_zero]; exact hR0p.le⟩
  obtain ⟨hc, -⟩ := s8g_c_dir ha ha hk hak hak hσ hW hEm hEU hU subset_rfl hAc hBc (Q₀ := 0)
    (e := (((1 : ℂ), (0 : ℂ)), ((0 : ℂ), (0 : ℂ)))) (c := 0) (ρ := R0)
    (fun t ht => by rw [h0Q]; exact hρk _ (mem_closedBall_zero_iff.1 (hz4 t (mem_closedBall_zero_iff.1 ht))))
    (M := M) (fun t ht => by rw [h0Q]; exact hM _ (hz4 t (mem_closedBall_zero_iff.1 ht)))
  simp only [h0Q] at hc
  have hmB : IsBeltramiCoeff a upperHalf Cκ :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hak u hu⟩
  have hms := wr_isHarmonicU_contDiffOn ha
  have hhol : ∀ x ∈ E ×ˢ upperHalf, DifferentiableOn ℂ (fun z => A x.1 * (conj (B x.2) *
      (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
        (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2)) (ball (0 : ℂ) R0) := by
    intro x hx
    simp only [hWW, hBY]
    exact ((s71_b2_holo (μ := Y) hk hmB hms (hEU hx.1) hR0k hW2 rfl hx.2).1 0
      (mem_closedBall_self hR0p.le)).const_mul (A x.1)
  have hDer := s7g_h_deriv (F := fun z x => A x.1 * (conj (B x.2) *
      (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
        (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2)) hTm hR0p hc hhol (M := M)
    (fun z hz => hM _ (hz4 z (mem_closedBall_zero_iff.1 hz)))
  have eG0 : (fun b => G2 (b, 0)) = fun z => ∫ x in E ×ˢ upperHalf, A x.1 * (conj (B x.2) *
      (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
        (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2) := by
    rw [hG2]
  rw [eG0, hDer.2]
  have hint : Integrable (fun x : ℂ × ℂ => deriv (fun z => A x.1 * (conj (B x.2) *
      (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
        (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2)) 0)
      ((volume.restrict E).prod (volume.restrict upperHalf)) := by
    rw [Measure.prod_restrict]
    exact hDer.1
  have e1 : (∫ x in E ×ˢ upperHalf, deriv (fun z => A x.1 * (conj (B x.2) *
      (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
        (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2)) 0) =
      ∫ x, deriv (fun z => A x.1 * (conj (B x.2) *
        (dz (W ((z, 0), (0, 0))) x.2 * dz (W ((z, 0), (0, 0))) (conj x.1) /
          (W ((z, 0), (0, 0)) x.2 - W ((z, 0), (0, 0)) (conj x.1)) ^ 2) ^ 2)) 0
        ∂((volume.restrict E).prod (volume.restrict upperHalf)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [e1, integral_prod _ hint]
  have hin : ∀ s ∈ E, (∫ t in upperHalf, deriv (fun z => A s * (conj (B t) *
      (dz (W ((z, 0), (0, 0))) t * dz (W ((z, 0), (0, 0))) (conj s) /
        (W ((z, 0), (0, 0)) t - W ((z, 0), (0, 0)) (conj s)) ^ 2) ^ 2)) 0) = 0 := by
    intro s hs
    have hpt : ∀ t ∈ upperHalf, deriv (fun z => A s * (conj (B t) *
        (dz (W ((z, 0), (0, 0))) t * dz (W ((z, 0), (0, 0))) (conj s) /
          (W ((z, 0), (0, 0)) t - W ((z, 0), (0, 0)) (conj s)) ^ 2) ^ 2)) 0 =
        A s * deriv (fun z => Y t * (dz (W2 (z, 0)) t * dz (W2 (z, 0)) (conj s) /
          (W2 (z, 0) t - W2 (z, 0) (conj s)) ^ 2) ^ 2) 0 := by
      intro t ht
      simp only [hWW, hBY]
      exact deriv_const_mul _ (((s71_b2_holo (μ := Y) hk hmB hms (hEU hs) hR0k hW2 rfl ht).1 0
        (mem_closedBall_self hR0p.le)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0p)))
    rw [setIntegral_congr_fun hU hpt, integral_const_mul,
      s8g_fv_inner hY ha hk hak hR0p hR0k hW2 (hEU hs), mul_zero]
  rw [setIntegral_congr_fun hEm hin, integral_zero, mul_zero]

/-- STUB QDOT (D6). The second-energy identity on `Γ\𝔻` (Γ-version of `cor_7_3` / Proposition 7.2): with
`f = μκ̄`, `g = νκ̄`, `G = G_Γ` and `q h = ∂_z̄(ρ⁻¹ ∂_z̄ h)`,
`4 ∬_F q(G f) \overline{q(G g)} ρ = (f, g)_Γ - (f, G g)_Γ`. -/
theorem s8g_qdot {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) :
    4 * ∫ z in fundDomainOn Γ unitDisc, s7et_q (resolventGammaD Γ fun u => μ u * conj (κ u)) z *
        conj (s7et_q (resolventGammaD Γ fun u => ν u * conj (κ u)) z) * rho z =
      innerGamma Γ (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) -
        innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) := by
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  obtain ⟨hf, hfΓ⟩ := s8q_fk_data hΓ.1 hμ hκ hμΓ hκΓ
  obtain ⟨hg, hgΓ⟩ := s8q_fk_data hΓ.1 hν hκ hνΓ hκΓ
  obtain ⟨Cf, hCf⟩ := hf.2
  obtain ⟨Cg, hCg⟩ := hg.2
  have hfc : ContinuousOn (fun u => μ u * conj (κ u)) unitDisc := hf.1.continuousOn
  have hgc : ContinuousOn (fun u => ν u * conj (κ u)) unitDisc := hg.1.continuousOn
  -- `(G_Γ f, g)_Γ = (f, G_Γ g)_Γ`
  rw [← s8q_selfadj hΓ hfc hgc hCf hCg]
  obtain ⟨hh, ⟨Ch, hCh⟩, hhΓ, heh⟩ := s8q_res_data hΓ.1 hf hfΓ
  obtain ⟨hk, ⟨Ck, hCk⟩, hkΓ, hek⟩ := s8q_res_data hΓ.1 hg hgΓ
  have hhc : ContinuousOn (resolventGammaD Γ fun u => μ u * conj (κ u)) unitDisc := hh.continuousOn
  generalize resolventGammaD Γ (fun u => μ u * conj (κ u)) = h at hh hCh hhΓ heh hhc ⊢
  generalize resolventGammaD Γ (fun u => ν u * conj (κ u)) = k at hk hCk hkΓ hek ⊢
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0 h0)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0 h0)
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0 h0)
  have hCk0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0 h0)
  -- the resolvent equations `Δ₀h = (f - h)/2`, `Δ₀k = (g - k)/2`
  have hΔh : ∀ z ∈ unitDisc, laplace0 h z = (μ z * conj (κ z) - h z) / 2 := fun z hz => by
    have e := heh z hz
    beta_reduce at e
    linear_combination e / 2
  have hΔk : ∀ z ∈ unitDisc, laplace0 k z = (ν z * conj (κ z) - k z) / 2 := fun z hz => by
    have e := hek z hz
    beta_reduce at e
    linear_combination e / 2
  have hbΔ : ∀ (U V : ℂ → ℂ) (CU CV : ℝ), (∀ z ∈ unitDisc, ‖U z‖ ≤ CU) → (∀ z ∈ unitDisc, ‖V z‖ ≤ CV) →
      ∀ z ∈ unitDisc, ‖(U z - V z) / 2‖ ≤ CU + CV := fun U V CU CV hU hV z hz => by
    rw [norm_div, Complex.norm_two]
    have := (norm_sub_le (U z) (V z)).trans (add_le_add (hU z hz) (hV z hz))
    have h2 := norm_nonneg (U z - V z)
    linarith
  have hC : ∀ z ∈ unitDisc, ‖h z‖ ≤ Cf + Cg + Ch + Ck := fun z hz => by linarith [hCh z hz]
  have hC' : ∀ z ∈ unitDisc, ‖k z‖ ≤ Cf + Cg + Ch + Ck := fun z hz => by linarith [hCk z hz]
  have hCΔh : ∀ z ∈ unitDisc, ‖laplace0 h z‖ ≤ Cf + Cg + Ch + Ck := fun z hz => by
    rw [hΔh z hz]; linarith [hbΔ _ _ _ _ hCf hCh z hz]
  have hCΔk : ∀ z ∈ unitDisc, ‖laplace0 k z‖ ≤ Cf + Cg + Ch + Ck := fun z hz => by
    rw [hΔk z hz]; linarith [hbΔ _ _ _ _ hCg hCk z hz]
  obtain ⟨hqi, hzero⟩ := s8q_energy_int hΓ hh hk hhΓ hkΓ hC hC' hCΔh hCΔk
  -- the lower-order terms are bounded times `ρ`
  have hΔhc : ContinuousOn (laplace0 h) unitDisc := fun z hz => by
    have e : laplace0 h =ᶠ[𝓝 z] fun w => (μ w * conj (κ w) - h w) / 2 :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hΔh
    exact (((hfc.sub hhc).div_const 2).continuousAt (isOpen_ball.mem_nhds hz)).congr e.symm |>.continuousWithinAt
  have hΔkc : ContinuousOn (laplace0 k) unitDisc := fun z hz => by
    have e : laplace0 k =ᶠ[𝓝 z] fun w => (ν w * conj (κ w) - k w) / 2 :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hΔk
    exact (((hgc.sub hk.continuousOn).div_const 2).continuousAt (isOpen_ball.mem_nhds hz)).congr e.symm
      |>.continuousWithinAt
  have hB := s8q_bdd_int hΓ (U := fun z => laplace0 h z * conj (laplace0 k z)) (hΔhc.mul (Complex.continuous_conj.comp_continuousOn hΔkc))
    (C := (Cf + Cg + Ch + Ck) * (Cf + Cg + Ch + Ck)) fun z hz => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCΔh z hz) (hCΔk z hz) (norm_nonneg _) (by linarith)
  have hD := s8q_bdd_int hΓ (U := fun z => (1 / 2 : ℂ) * laplace0 h z * conj (k z)) ((continuousOn_const.mul hΔhc).mul (Complex.continuous_conj.comp_continuousOn hk.continuousOn))
    (C := (Cf + Cg + Ch + Ck) * (Cf + Cg + Ch + Ck)) fun z hz => by
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_div, norm_one, Complex.norm_two]
      have := mul_le_mul (hCΔh z hz) (hC' z hz) (norm_nonneg _) (by linarith)
      have h3 : 0 ≤ ‖laplace0 h z‖ * ‖k z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith
  have hfg := s8q_bdd_int hΓ (U := fun z => μ z * conj (κ z) * conj (ν z * conj (κ z))) (hfc.mul (Complex.continuous_conj.comp_continuousOn hgc))
    (C := Cf * Cg) fun z hz => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCf z hz) (hCg z hz) (norm_nonneg _) hCf0
  have hhg := s8q_bdd_int hΓ (U := fun z => h z * conj (ν z * conj (κ z))) (hhc.mul (Complex.continuous_conj.comp_continuousOn hgc))
    (C := Ch * Cg) fun z hz => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCh z hz) (hCg z hz) (norm_nonneg _) hCh0
  -- `∫ q(h) q(k)‾ ρ = ∫ (Δ₀h Δ₀k‾ + ½ Δ₀h k‾) ρ = ¼ ∫ (f - h) g‾ ρ`
  have hsplit : ∫ z in fundDomainOn Γ unitDisc, s7et_q h z * conj (s7et_q k z) * rho z =
      ∫ z in fundDomainOn Γ unitDisc, (laplace0 h z * conj (laplace0 k z) * rho z +
        (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z) := by
    have hBD : IntegrableOn (fun z => laplace0 h z * conj (laplace0 k z) * rho z +
        (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z) (fundDomainOn Γ unitDisc) := hB.add hD
    have hz' : ∫ z in fundDomainOn Γ unitDisc, (s7et_q h z * conj (s7et_q k z) * rho z -
        (laplace0 h z * conj (laplace0 k z) * rho z + (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z)) = 0 := by
      rw [← hzero]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      beta_reduce
      ring
    rw [integral_sub hqi hBD] at hz'
    exact sub_eq_zero.mp hz'
  have hpt : ∀ z ∈ fundDomainOn Γ unitDisc, laplace0 h z * conj (laplace0 k z) * rho z +
      (1 / 2 : ℂ) * laplace0 h z * conj (k z) * rho z =
        (1 / 4 : ℂ) * (μ z * conj (κ z) * conj (ν z * conj (κ z)) * rho z -
          h z * conj (ν z * conj (κ z)) * rho z) := fun z hz => by
    rw [hΔh z (hFD hz), hΔk z (hFD hz)]
    simp only [map_sub, map_div₀, map_ofNat]
    ring
  rw [hsplit, setIntegral_congr_fun hFm hpt, integral_const_mul, integral_sub hfg hhg]
  show 4 * ((1 / 4 : ℂ) * ((∫ z in fundDomainOn Γ unitDisc, μ z * conj (κ z) * conj (ν z * conj (κ z)) * rho z) -
      ∫ z in fundDomainOn Γ unitDisc, h z * conj (ν z * conj (κ z)) * rho z)) =
    (∫ z in fundDomainOn Γ unitDisc, μ z * conj (κ z) * conj (ν z * conj (κ z)) * rho z) -
      ∫ z in fundDomainOn Γ unitDisc, h z * conj (ν z * conj (κ z)) * rho z
  ring

/-- The inner kernel integral at `s̄` without D4: `∫_𝕌 |W'(τ)W'(s̄)/(W τ - W s̄)²|² ≤ c₀² J_W(s̄) π/d²`,
`d = d(W s̄, (W 𝕃)ᶜ) > 0` (the first part of `s8g_c_inner`). -/
theorem s8r_inner {W : ℂ → ℂ} {K k' : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ) (hk0 : 0 ≤ k')
    (hk1 : k' < 1) (hker : ∀ y : ℂ, y.im ≠ 0 → (1 - k' ^ 2) * ‖dz W y‖ ^ 2 ≤ jacobian W y)
    {s : ℂ} (hsU : s ∈ upperHalf) :
    0 < infDist (W (conj s)) (W '' {u : ℂ | u.im < 0})ᶜ ∧
    ∫⁻ τ in upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
        ENNReal.ofReal (π / infDist (W (conj s)) (W '' {u : ℂ | u.im < 0})ᶜ ^ 2) := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hinj : Function.Injective W := by rw [← he]; exact e.injective
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hs0 : 0 < s.im := hsU
  have hcs : conj s ∈ {u : ℂ | u.im < 0} := by
    show (conj s).im < 0
    rw [Complex.conj_im]
    linarith
  set Y := W (conj s) with hY
  set d := infDist Y (W '' {u : ℂ | u.im < 0})ᶜ with hd
  have hLimg : IsOpen (W '' {u : ℂ | u.im < 0}) := by rw [← he]; exact e.isOpenMap _ hLo
  have hne : (W '' {u : ℂ | u.im < 0})ᶜ.Nonempty := by
    refine ⟨W 0, fun hW0 => ?_⟩
    obtain ⟨u, hu, he'⟩ := hW0
    have := hinj he'
    rw [this] at hu
    exact lt_irrefl _ (show (0 : ℂ).im < 0 from hu)
  have hd0 : 0 < d := by
    rw [hd]
    exact (hLimg.isClosed_compl.notMem_iff_infDist_pos (x := Y) hne).1 (fun hc => hc (mem_image_of_mem W hcs))
  refine ⟨hd0, ?_⟩
  have hpt : ∀ τ ∈ upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2 ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
        (ENNReal.ofReal (jacobian W τ) * ((‖W τ - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4)) := by
    intro τ hτ
    have hw : W τ - W (conj s) ≠ 0 := by
      intro h
      have h1 := hinj (sub_eq_zero.1 h)
      have h2 : τ.im = (conj s).im := by rw [h1]
      rw [Complex.conj_im] at h2
      have : 0 < τ.im := hτ
      linarith
    have h := s7g_r1_pt hk1 hk0 hker hsU hτ hw 1 1
    simp only [one_mul, mul_one] at h
    refine h.trans (le_of_eq ?_)
    rw [one_div, enorm_eq_nnnorm, ENNReal.inv_pow]
    ring
  calc ∫⁻ τ in upperHalf, ‖dz W τ * dz W (conj s) / (W τ - W (conj s)) ^ 2‖ₑ ^ 2
      ≤ ∫⁻ τ in upperHalf, ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          (ENNReal.ofReal (jacobian W τ) * ((‖W τ - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4)) :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_upperHalf_aux).mono hpt)
    _ = ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          ∫⁻ X in W '' upperHalf, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
        rw [lintegral_const_mul' _ _ (by finiteness),
          QCV.qcv_lintegral_image_eq (nx_isKQC_restrict hK hUo (subset_univ _))]
    _ ≤ ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 2 * ENNReal.ofReal (jacobian W (conj s)) *
          ENNReal.ofReal (π / d ^ 2) := by
        gcongr
        refine r24_lintegral_outside hd0 fun X hX => ?_
        have hXc : X ∈ (W '' {u : ℂ | u.im < 0})ᶜ := by
          rintro ⟨u, hu, rfl⟩
          obtain ⟨v, hv, hvX⟩ := hX
          have := hinj hvX
          rw [this] at hv
          have h1 : 0 < u.im := hv
          have h2 : u.im < 0 := hu
          linarith
        rw [hd, ← dist_eq_norm, dist_comm]
        exact infDist_le_dist_of_mem hXc

/-- `d(x, W 𝕌) ≤ d(x, (W 𝕃)ᶜ)` for a homeomorphism `W` of `ℂ` (`(W 𝕃)ᶜ ⊆ \overline{W 𝕌}`). -/
theorem s8r_dle {W : ℂ → ℂ} (hWc : Continuous W) (hinj : Function.Injective W) (hs : W '' univ = univ) (x : ℂ) :
    infDist x (W '' upperHalf) ≤ infDist x (W '' {u : ℂ | u.im < 0})ᶜ := by
  rw [← infDist_closure (s := W '' upperHalf)]
  refine infDist_le_infDist_of_subset (fun y hy => ?_) ⟨W 0, fun hW0 => ?_⟩
  · obtain ⟨z, -, rfl⟩ : y ∈ W '' univ := by rw [hs]; trivial
    have hz : 0 ≤ z.im := not_lt.1 fun h => hy ⟨z, h, rfl⟩
    have hzc : z ∈ closure upperHalf := by
      rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, closure_setOfPred_lt_im]
      exact hz
    exact image_closure_subset_closure_image hWc ⟨z, hzc, rfl⟩
  · obtain ⟨u, hu, he'⟩ := hW0
    have := hinj he'
    rw [this] at hu
    exact lt_irrefl _ (show (0 : ℂ).im < 0 from hu)

/-- The real arithmetic of `s8r_R5E` (AM-GM between the two weights). -/
theorem s8r_real {Mμ Mν c Jq J dq d x1 x2 Δ L C ρ κ : ℝ} (hMμ : 0 ≤ Mμ) (hMν : 0 ≤ Mν) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hdq : 0 < dq) (hd : 0 < d) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hΔ : 0 ≤ Δ) (hJq0 : 0 ≤ Jq) (hJ0 : 0 ≤ J) (h1 : Δ ≤ L * d) (h2 : Δ ≤ L * dq) (hj1 : Jq ≤ x1 ^ 2)
    (hj2 : J ≤ x2 ^ 2) (hk1 : κ * x1 ^ 2 ≤ Jq) (hk2 : κ * x2 ^ 2 ≤ J) (hD1 : Jq ≤ C * dq ^ 2 * ρ)
    (hD2 : J ≤ C * d ^ 2 * ρ) :
    Mμ * (c ^ 2 * Jq * (π / dq ^ 2)) * (Mν * (c ^ 2 * J * (π / d ^ 2))) * (Δ ^ 2 / (x1 * x2)) ≤
      Mμ * Mν * (c ^ 4 * π ^ 2) * (L ^ 2 * (C / κ)) * ρ := by
  have hΔ2 : Δ ^ 2 ≤ L ^ 2 * (d * dq) := by
    have := mul_le_mul h1 h2 hΔ (by positivity : 0 ≤ L * d)
    calc Δ ^ 2 = Δ * Δ := by ring
      _ ≤ L * d * (L * dq) := this
      _ = _ := by ring
  have hu : x1 ^ 2 / dq ^ 2 ≤ C / κ * ρ := by
    rw [div_le_iff₀ (by positivity)]
    have : x1 ^ 2 ≤ C * dq ^ 2 * ρ / κ := by rw [le_div_iff₀ hκ]; linarith
    calc x1 ^ 2 ≤ C * dq ^ 2 * ρ / κ := this
      _ = C / κ * ρ * dq ^ 2 := by ring
  have hv : x2 ^ 2 / d ^ 2 ≤ C / κ * ρ := by
    rw [div_le_iff₀ (by positivity)]
    have : x2 ^ 2 ≤ C * d ^ 2 * ρ / κ := by rw [le_div_iff₀ hκ]; linarith
    calc x2 ^ 2 ≤ C * d ^ 2 * ρ / κ := this
      _ = C / κ * ρ * d ^ 2 := by ring
  have e1 : Jq * (1 / dq ^ 2) * (J * (1 / d ^ 2)) * (Δ ^ 2 / (x1 * x2)) ≤
      x1 ^ 2 * (1 / dq ^ 2) * (x2 ^ 2 * (1 / d ^ 2)) * (L ^ 2 * (d * dq) / (x1 * x2)) := by
    gcongr
  have e2 : x1 ^ 2 * (1 / dq ^ 2) * (x2 ^ 2 * (1 / d ^ 2)) * (L ^ 2 * (d * dq) / (x1 * x2)) =
      L ^ 2 * ((x1 / dq) * (x2 / d)) := by
    have := hdq.ne'
    have := hd.ne'
    have := hx1.ne'
    have := hx2.ne'
    field_simp
  have e3 : (x1 / dq) * (x2 / d) ≤ (x1 ^ 2 / dq ^ 2 + x2 ^ 2 / d ^ 2) / 2 := by
    have h := two_mul_le_add_sq (x1 / dq) (x2 / d)
    rw [div_pow, div_pow] at h
    linarith
  have hcore : Jq * (1 / dq ^ 2) * (J * (1 / d ^ 2)) * (Δ ^ 2 / (x1 * x2)) ≤ L ^ 2 * (C / κ) * ρ := by
    calc _ ≤ L ^ 2 * ((x1 / dq) * (x2 / d)) := e1.trans e2.le
      _ ≤ L ^ 2 * ((x1 ^ 2 / dq ^ 2 + x2 ^ 2 / d ^ 2) / 2) := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ ≤ L ^ 2 * ((C / κ * ρ + C / κ * ρ) / 2) := by gcongr
      _ = _ := by ring
  calc _ = Mμ * Mν * (c ^ 4 * π ^ 2) * (Jq * (1 / dq ^ 2) * (J * (1 / d ^ 2)) * (Δ ^ 2 / (x1 * x2))) := by ring
    _ ≤ Mμ * Mν * (c ^ 4 * π ^ 2) * (L ^ 2 * (C / κ) * ρ) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by ring

/-- **R5Γ.** The uniform `L¹` bound of the line-1 triple integrand over `E × 𝕌 × 𝕌`, for bounded harmonic data and
`E` of finite hyperbolic area: pointwise in `s` the `(t₁, t₂)`-integral is `≤ C ρ_𝕌(s)` (`s8r_inner` twice,
`s7g_f2_wd` twice, AM-GM, D4 on `𝕃`). -/
theorem s8r_R5E {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ') {k : ℝ} (hk : 0 ≤ k)
    (hmk : ∀ u ∈ upperHalf, ‖m' u‖ ≤ k)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {mμ mν : ℂ → ℂ} {Mμ Mν : ℝ} (hMμ : 0 ≤ Mμ) (hMν : 0 ≤ Mν) (hμb : ∀ u ∈ upperHalf, ‖mμ u‖ ≤ Mμ)
    (hνb : ∀ u ∈ upperHalf, ‖mν u‖ ≤ Mν) {E : Set ℂ} (hEm : MeasurableSet E) (hEU : E ⊆ upperHalf)
    (hEA : ∫⁻ s in E, ENNReal.ofReal (rhoU s) < ∞) :
    ∃ R : ℝ, 0 < R ∧ 2 * R * k < 1 ∧ ∃ M : ℝ, ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      (∫⁻ s in E, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
        ‖mμ t₁‖ₑ * ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
          (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
          ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) ≤ ENNReal.ofReal M := by
  have hU := measurableSet_upperHalf_aux
  have hmB : IsBeltramiCoeff m' upperHalf k :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, (ae_restrict_mem hU).mono fun u hu => hmk u hu⟩
  have hms := wr_isHarmonicU_contDiffOn hharm
  obtain ⟨R4, hR4, C4, hD4⟩ := s8g_D4 hk
  set R := min R4 (1 / (4 * (k + 1))) with hRdef
  have hR0 : 0 < R := lt_min hR4 (by positivity)
  have hRR4 : R ≤ R4 := min_le_left _ _
  have hRk : 2 * R * k < 1 := by
    have h1 : R ≤ 1 / (4 * (k + 1)) := min_le_right _ _
    have h2 : 2 * R * k ≤ 2 * (1 / (4 * (k + 1))) * k := by gcongr
    have h3 : 2 * (1 / (4 * (k + 1))) * k < 1 := by
      rw [show 2 * (1 / (4 * (k + 1))) * k = k / (2 * (k + 1)) by field_simp; ring, div_lt_one (by positivity)]
      linarith
    linarith
  have hk' : 0 ≤ 2 * R * k := by positivity
  have hc1 : 0 < 1 - (2 * R * k) ^ 2 := by nlinarith
  set K0 : ℝ := (1 + 2 * R * k) / (1 - 2 * R * k) with hK0
  set L : ℝ := lambdaInv K0 + lambdaInv K0 ^ 2 with hLd
  set C4' : ℝ := max C4 0 with hC4'
  set c : ℝ := (1 - (2 * R * k) ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := (inv_pos.2 hc1).le
  set Cst : ℝ := Mμ * Mν * (c ^ 4 * π ^ 2) * (L ^ 2 * (C4' / (1 - (2 * R * k) ^ 2))) with hCst
  have hCst0 : 0 ≤ Cst := by
    have : 0 ≤ C4' := le_max_right _ _
    positivity
  refine ⟨R, hR0, hRk, Cst * (∫⁻ s in E, ENNReal.ofReal (rhoU s)).toReal, fun P hP => ?_⟩
  -- the four-parameter family and D4
  obtain ⟨W4, hW4⟩ : ∃ W4 : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W4 = fun Q => normalizedSolution fun u =>
      (if 0 < u.im then Q.1.1 * m' u + Q.1.2 * m' u else 0) +
        (if u.im < 0 then Q.2.1 * conj (m' (conj u)) + Q.2.2 * conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  have hW24 : ∀ Q : ℂ × ℂ, W Q = W4 ((Q.1, 0), (Q.2, 0)) := fun Q => by
    rw [hW, hW4]
    beta_reduce
    congr 1
    funext u
    split_ifs <;> ring
  have hD4Q : ∀ Q ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R, ∀ z ∈ upperHalf,
      jacobian (W Q) (conj z) ≤ C4' * infDist (W Q (conj z)) (W Q '' {u : ℂ | u.im < 0})ᶜ ^ 2 * rhoU z := by
    intro Q hQ z hz
    have hQ4 : ((Q.1, (0 : ℂ)), (Q.2, (0 : ℂ))) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R4 := by
      have h1 := mem_closedBall_zero_iff.1 hQ.1
      have h2 := mem_closedBall_zero_iff.1 hQ.2
      rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def, Prod.norm_def, norm_zero]
      exact max_le (max_le (h1.trans hRR4) hR4.le) (max_le (h2.trans hRR4) hR4.le)
    have h := (hD4 m' φ' m' φ' hharm hharm hmk hmk W4 hW4 _ hQ4 z hz).2
    rw [← hW24] at h
    generalize infDist (W Q (conj z)) (W Q '' {u : ℂ | u.im < 0})ᶜ = X at h ⊢
    have h0 : 0 ≤ X ^ 2 * rhoU z := by
      have : 0 ≤ rhoU z := by unfold rhoU; positivity
      positivity
    calc _ ≤ C4 * X ^ 2 * rhoU z := h
      _ = C4 * (X ^ 2 * rhoU z) := by ring
      _ ≤ C4' * (X ^ 2 * rhoU z) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ = C4' * X ^ 2 * rhoU z := by ring
  -- the data of `W_P` and `W_{P*}`
  set Ps : ℂ × ℂ := (conj P.2, conj P.1) with hPsd
  have hPs : Ps ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := by
    obtain ⟨h1, h2⟩ := hP
    refine ⟨?_, ?_⟩
    · show conj P.2 ∈ closedBall (0 : ℂ) R
      rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h2
    · show conj P.1 ∈ closedBall (0 : ℂ) R
      rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h1
  have hRk1 : R * k < 1 := by nlinarith
  have hPk : max ‖P.1‖ ‖P.2‖ * k < 1 := e64_polydisc_sub hk hRk1 hP
  have hPsk : max ‖Ps.1‖ ‖Ps.2‖ * k < 1 := e64_polydisc_sub hk hRk1 hPs
  have hPP : (conj Ps.2, conj Ps.1) = P := by
    rw [hPsd]
    simp only [Complex.conj_conj]
  obtain ⟨hKP, hsP, -, hkerP⟩ := s7g_f2_Wdata hk hmB hms hW hR0.le hRk hP
  obtain ⟨hKQ, hsQ, -, hkerQ⟩ := s7g_f2_Wdata hk hmB hms hW hR0.le hRk hPs
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hmB hms hW
  have hWc : Continuous (W P) := continuousOn_univ.1 hKP.2.2.1.1
  have hWcQ : Continuous (W Ps) := continuousOn_univ.1 hKQ.2.2.1.1
  have hWs1 : ∀ s, W Ps (conj s) = conj (W P s) := fun s => by
    have h := s7g_f2_Wsym hk hmB hms hW hPsk s
    rwa [hPP] at h
  have hWs2 : ∀ s, W Ps s = conj (W P (conj s)) := fun s => by
    have h := s7g_f2_Wsym hk hmB hms hW hPk s
    rw [h, Complex.conj_conj]
  have hdzs : ∀ s : ℂ, s.im ≠ 0 → dz (W Ps) (conj s) = conj (dz (W P) s) := fun s hs => by
    have h := s7g_f2_dWsym hk hmB hms hW hPsk hs
    rwa [hPP] at h
  have hdz0 : ∀ y : ℂ, y.im ≠ 0 → dz (W P) y ≠ 0 := by
    intro y hy h0
    rcases lt_or_gt_of_ne hy with h | h
    · obtain ⟨hb, hJ⟩ := e64_t5_beltrami hk hmB hms hW hPk h
      unfold jacobian at hJ
      rw [hb, h0] at hJ
      simp at hJ
    · obtain ⟨hb, hJ⟩ := s71_b2_beltrami hk hmB hms hW hPk h
      unfold jacobian at hJ
      rw [hb, h0] at hJ
      simp at hJ
  have hjle : ∀ (f : ℂ → ℂ) (z : ℂ), jacobian f z ≤ ‖dz f z‖ ^ 2 := fun f z => by
    unfold jacobian
    nlinarith [sq_nonneg ‖dzbar f z‖]
  have hmK : ∀ Q : ℂ × ℂ, Continuous (W Q) → ∀ s : ℂ,
      Measurable (fun t => ‖dz (W Q) t * dz (W Q) (conj s) / (W Q t - W Q (conj s)) ^ 2‖ₑ ^ 2) :=
    fun Q hcQ s => ((((s7g_f2_dzmeas (W Q)).mul_const _).div
      ((hcQ.measurable.sub_const _).pow_const 2)).enorm).pow_const 2
  have hcen : ∀ x : ℂ, ∀ M : ℝ, ‖x‖ ≤ M → ‖x‖ₑ ≤ ENNReal.ofReal M := fun x M h => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h
  -- the pointwise bound
  have hpt : ∀ s ∈ E, (∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
      ‖mμ t₁‖ₑ * ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
        (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
        ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) ≤
      ENNReal.ofReal (Cst * rhoU s) := by
    intro s hs
    have hsU := hEU hs
    have hs0 : 0 < s.im := hsU
    have hsi : s.im ≠ 0 := hs0.ne'
    have hcsi : (conj s).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hsi
    set A1 := ∫⁻ t in upperHalf, ‖dz (W Ps) t * dz (W Ps) (conj s) / (W Ps t - W Ps (conj s)) ^ 2‖ₑ ^ 2 with hA1
    set A2 := ∫⁻ t in upperHalf, ‖dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2‖ₑ ^ 2 with hA2
    set h := ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ with hh
    have hht : h ≠ ⊤ := enorm_ne_top
    have step1 : (∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
        ‖mμ t₁‖ₑ * ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
          (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) * h) ≤
        ENNReal.ofReal Mμ * A1 * (ENNReal.ofReal Mν * A2) * h := by
      calc _ ≤ ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
            ENNReal.ofReal Mμ * ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
              (ENNReal.ofReal Mν * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) * h := by
            refine setLIntegral_mono' hU fun t₁ ht₁ => setLIntegral_mono' hU fun t₂ ht₂ => ?_
            gcongr
            · exact hcen _ _ (hμb t₁ ht₁)
            · exact hcen _ _ (hνb t₂ ht₂)
        _ = ∫⁻ t₁ in upperHalf, ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
              (ENNReal.ofReal Mμ * h * ENNReal.ofReal Mν * A2) := by
            refine lintegral_congr fun t₁ => ?_
            rw [hA2, ← lintegral_const_mul _ (hmK P hWc s), ← lintegral_const_mul _ ((hmK P hWc s).const_mul _)]
            refine lintegral_congr fun t₂ => ?_
            ring
        _ = ENNReal.ofReal Mμ * A1 * (ENNReal.ofReal Mν * A2) * h := by
            rw [lintegral_mul_const _ (hmK Ps hWcQ s), hA1]
            ring
    -- the real quantities
    obtain ⟨hdP, hIP⟩ := s8r_inner hKP hsP hk' hRk hkerP hsU
    obtain ⟨hdQ, hIQ⟩ := s8r_inner hKQ hsQ hk' hRk hkerQ hsU
    set d := infDist (W P (conj s)) (W P '' {u : ℂ | u.im < 0})ᶜ with hd
    set dq := infDist (W Ps (conj s)) (W Ps '' {u : ℂ | u.im < 0})ᶜ with hdq
    set J := jacobian (W P) (conj s) with hJ
    set Jq := jacobian (W Ps) (conj s) with hJq
    set x1 := ‖dz (W P) s‖ with hx1
    set x2 := ‖dz (W P) (conj s)‖ with hx2
    set Δ := ‖W P s - W P (conj s)‖ with hΔ
    have hx1q : ‖dz (W Ps) (conj s)‖ = x1 := by rw [hdzs s hsi, Complex.norm_conj]
    have hΔq : ‖W Ps s - W Ps (conj s)‖ = Δ := by
      rw [hWs1, hWs2, ← map_sub, Complex.norm_conj, norm_sub_rev]
    have hkJ := hkerP (conj s) hcsi
    have hkJq := hkerQ (conj s) hcsi
    rw [hx1q] at hkJq
    have hJ0 : 0 ≤ J := le_trans (by positivity) hkJ
    have hJq0 : 0 ≤ Jq := le_trans (by positivity) hkJq
    have hρ0 : 0 ≤ rhoU s := by unfold rhoU; positivity
    have hx1p : 0 < x1 := norm_pos_iff.2 (hdz0 s hsi)
    have hx2p : 0 < x2 := norm_pos_iff.2 (hdz0 (conj s) hcsi)
    have hwd1 : Δ ≤ L * d := by
      have h1 := s7g_f2_wd hKP hsP hsU
      have h2 := s8r_dle hWc (hinj P hPk) hsP (W P (conj s))
      have hL0 : 0 ≤ L := by
        have := zero_lt_one.trans_le (td_one_le_lambdaInv hKP.2.1)
        positivity
      calc Δ ≤ L * infDist (W P (conj s)) (W P '' upperHalf) := h1
        _ ≤ L * d := mul_le_mul_of_nonneg_left h2 hL0
    have hwd2 : Δ ≤ L * dq := by
      have h1 := s7g_f2_wd hKQ hsQ hsU
      have h2 := s8r_dle hWcQ (hinj Ps hPsk) hsQ (W Ps (conj s))
      have hL0 : 0 ≤ L := by
        have := zero_lt_one.trans_le (td_one_le_lambdaInv hKQ.2.1)
        positivity
      rw [hΔq] at h1
      calc Δ ≤ L * infDist (W Ps (conj s)) (W Ps '' upperHalf) := h1
        _ ≤ L * dq := mul_le_mul_of_nonneg_left h2 hL0
    have hD4P := hD4Q P hP s hsU
    have hD4Ps := hD4Q Ps hPs s hsU
    rw [← hd, ← hJ] at hD4P
    rw [← hdq, ← hJq] at hD4Ps
    have hh' : h = ENNReal.ofReal (Δ ^ 2 / (x1 * x2)) := by
      rw [hh, ← ofReal_norm, norm_inv, norm_div, norm_mul, norm_pow, inv_div]
    have hA1' : A1 ≤ ENNReal.ofReal (c ^ 2 * Jq * (π / dq ^ 2)) := by
      refine hIQ.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc0]
    have hA2' : A2 ≤ ENNReal.ofReal (c ^ 2 * J * (π / d ^ 2)) := by
      refine hIP.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc0]
    have hreal : Mμ * (c ^ 2 * Jq * (π / dq ^ 2)) * (Mν * (c ^ 2 * J * (π / d ^ 2))) * (Δ ^ 2 / (x1 * x2)) ≤
        Cst * rhoU s := by
      have hL0 : 0 ≤ L := by
        have := zero_lt_one.trans_le (td_one_le_lambdaInv hKP.2.1)
        positivity
      have h := s8r_real hMμ hMν hc0 hc1 (le_max_right C4 0) hρ0 hL0 hdQ hdP hx1p hx2p (norm_nonneg _) hJq0 hJ0
        hwd1 hwd2 (by rw [← hx1q]; exact hjle _ _) (hjle _ _) (by linarith [hkJq]) (by linarith [hkJ]) hD4Ps hD4P
      rw [hCst]
      exact h
    calc _ ≤ ENNReal.ofReal Mμ * A1 * (ENNReal.ofReal Mν * A2) * h := step1
      _ ≤ ENNReal.ofReal Mμ * ENNReal.ofReal (c ^ 2 * Jq * (π / dq ^ 2)) *
          (ENNReal.ofReal Mν * ENNReal.ofReal (c ^ 2 * J * (π / d ^ 2))) * ENNReal.ofReal (Δ ^ 2 / (x1 * x2)) := by
        rw [hh']
        gcongr
      _ = ENNReal.ofReal (Mμ * (c ^ 2 * Jq * (π / dq ^ 2)) * (Mν * (c ^ 2 * J * (π / d ^ 2))) *
          (Δ ^ 2 / (x1 * x2))) := by
        rw [← ENNReal.ofReal_mul hMμ, ← ENNReal.ofReal_mul hMν, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cst * rhoU s) := ENNReal.ofReal_le_ofReal hreal
  calc _ ≤ ∫⁻ s in E, ENNReal.ofReal (Cst * rhoU s) := setLIntegral_mono' hEm hpt
    _ = ENNReal.ofReal Cst * ∫⁻ s in E, ENNReal.ofReal (rhoU s) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_mul hCst0]
    _ = _ := by
        rw [ENNReal.ofReal_mul hCst0, ENNReal.ofReal_toReal hEA.ne]

/-- (Γ-version of `s7g_f2_line1D`) Line 1 under the integral over a set `E ⊆ 𝕌` of finite hyperbolic area, for
bounded harmonic data: the uniform `L¹` bound is `s8r_R5E` (pointwise `≤ C ρ_𝕌`) instead of the `L²` Schur bound. -/
theorem s8r_line1D {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ') {mμ φμ mν φν : ℂ → ℂ} (hμh : IsHarmonicU mμ φμ)
    (hνh : IsHarmonicU mν φν) {E : Set ℂ} (hEm : MeasurableSet E) (hEU : E ⊆ upperHalf)
    (hEA : ∫⁻ s in E, ENNReal.ofReal (rhoU s) < ∞) :
    IntegrableOn (fun s => dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0) E ∧
    dzbar (dz fun e => ∫ s in E, conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 =
      ∫ s in E, dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 := by
  have hU := measurableSet_upperHalf_aux
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hms := wr_isHarmonicU_contDiffOn hharm
  obtain ⟨Mμ, hMμ0, hμb⟩ := harmonicU_bounded hμh
  obtain ⟨Mν, hMν0, hνb⟩ := harmonicU_bounded hνh
  have hμc := harmonicU_continuousOn hμh
  have hνc := harmonicU_continuousOn hνh
  have hm'c := harmonicU_continuousOn hharm
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨R5, hR5, -, M5, hM5⟩ := s8r_R5E hharm hC0 hCb hW hMμ0 hMν0 hμb hνb hEm hEU hEA
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = min (1 / (4 * (C + 1))) R5 := ⟨_, rfl⟩
  have hR0p : 0 < R0 := by rw [hR0]; exact lt_min (by positivity) hR5
  have hR05 : R0 ≤ R5 := by rw [hR0]; exact min_le_right _ _
  have hR0k2 : 2 * R0 * C < 1 := by
    have h1 : R0 ≤ 1 / (4 * (C + 1)) := by rw [hR0]; exact min_le_left _ _
    have h2 : 2 * R0 * C ≤ 2 * (1 / (4 * (C + 1))) * C := by gcongr
    have h3 : 2 * (1 / (4 * (C + 1))) * C < 1 := by
      rw [show 2 * (1 / (4 * (C + 1))) * C = C / (2 * (C + 1)) by field_simp; ring, div_lt_one (by positivity)]
      linarith
    linarith
  have hR0k : R0 * C < 1 := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ × (ℂ × ℂ) → ℂ, F = fun P x =>
      conj (mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2) *
      (mν x.2.2 * (dz (W P) x.2.2 * dz (W P) (conj x.1) / (W P x.2.2 - W P (conj x.1)) ^ 2) ^ 2) *
      (1 - P.1 * P.2 * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) x.1 * dz (W P) (conj x.1) / (W P x.1 - W P (conj x.1)) ^ 2) := ⟨_, rfl⟩
  set D : Set (ℂ × ℂ) := closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 with hDdef
  have hTm : MeasurableSet (E ×ˢ (S ×ˢ S)) := hEm.prod (hSm.prod hSm)
  have hsub := e64_polydisc_sub hC0 hR0k
  have hswD : ∀ P ∈ D, ((conj P.2, conj P.1) : ℂ × ℂ) ∈ D := by
    rintro P ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h2
    · rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h1
  -- continuity on `D × (𝕌 ∖ {i})³`
  have hcont : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => F p.1 p.2) (D ×ˢ (E ×ˢ (S ×ˢ S))) := by
    have hmem : ∀ p ∈ D ×ˢ (E ×ˢ (S ×ˢ S)), p.1 ∈ D ∧ p.2.1 ∈ upperHalf ∧ p.2.2.1 ∈ upperHalf ∧
        p.2.2.2 ∈ upperHalf := by
      rintro p ⟨h1, h2, h3, h4⟩
      exact ⟨h1, hEU h2, hSU h3, hSU h4⟩
    have hK1 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (E ×ˢ (S ×ˢ S)))
      (p := fun p => ((conj p.1.2, conj p.1.1) : ℂ × ℂ)) (u := fun p => p.2.2.1) (z := fun p => p.2.1)
      (by fun_prop) (fun p hp => hswD _ (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.2.1) (fun p hp => (hmem p hp).2.1)
    have hK2 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (E ×ˢ (S ×ˢ S)))
      (p := fun p => p.1) (u := fun p => p.2.2.2) (z := fun p => p.2.1)
      continuous_fst.continuousOn (fun p hp => (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.2.2) (fun p hp => (hmem p hp).2.1)
    have hK3 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (E ×ˢ (S ×ˢ S)))
      (p := fun p => p.1) (u := fun p => p.2.1) (z := fun p => p.2.1)
      continuous_fst.continuousOn (fun p hp => (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.1) (fun p hp => (hmem p hp).2.1)
    have hA : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => mμ p.2.2.1) (D ×ˢ (E ×ˢ (S ×ˢ S))) :=
      hμc.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.2.1).continuousOn
        fun p hp => (hmem p hp).2.2.1
    have hB : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => mν p.2.2.2) (D ×ˢ (E ×ˢ (S ×ˢ S))) :=
      hνc.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.2.2).continuousOn
        fun p hp => (hmem p hp).2.2.2
    have hM' : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => ((‖m' p.2.1‖ ^ 2 : ℝ) : ℂ))
        (D ×ˢ (E ×ˢ (S ×ˢ S))) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn
        (hm'c.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.1).continuousOn
          fun p hp => (hmem p hp).2.1)).pow 2)
    have hP1 : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.1.1 * p.1.2) (D ×ˢ (E ×ˢ (S ×ˢ S))) :=
      (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.1.1 * p.1.2).continuousOn
    have h := (((Complex.continuous_conj.comp_continuousOn (hA.mul (hK1.pow 2))).mul (hB.mul (hK2.pow 2))).mul
      ((continuousOn_const (c := (1 : ℂ))).sub (hP1.mul hM'))).div hK3
      (fun p hp => s7g_f2_Kd0 hC0 hmB hms hW (hsub (hmem p hp).1) (hmem p hp).2.1)
    rw [hF]
    exact h
  -- separate holomorphy
  have hR2 : 2 * R0 * C < 1 := hR0k2
  have hhol : ∀ x ∈ E ×ˢ (S ×ˢ S),
      (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R0)) ∧
        ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R0) := by
    intro x hx
    have hs : x.1 ∈ upperHalf := hEU hx.1
    have ht1 : x.2.1 ∈ upperHalf := hSU hx.2.1
    have ht2 : x.2.2 ∈ upperHalf := hSU hx.2.2
    have hin : ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        ((a, b) : ℂ × ℂ) ∈ ball (0 : ℂ) (2 * R0) ×ˢ ball (0 : ℂ) (2 * R0) := fun a b ha hb =>
      ⟨mem_ball_zero_iff.2 (by linarith), mem_ball_zero_iff.2 (by linarith)⟩
    have hK : ∀ {u z : ℂ}, u ∈ upperHalf → z ∈ upperHalf → ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        DifferentiableAt ℂ (fun Q => dz (W Q) u * dz (W Q) (conj z) / (W Q u - W Q (conj z)) ^ 2) (a, b) :=
      fun hu hz a b ha hb => s7g_f2_Khol hC0 hmB hms hW hu hz hR2 (hin a b ha hb)
    have hden : ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        dz (W (a, b)) x.1 * dz (W (a, b)) (conj x.1) / (W (a, b) x.1 - W (a, b) (conj x.1)) ^ 2 ≠ 0 :=
      fun a b ha hb => s7g_f2_Kd0 hC0 hmB hms hW
        (hsub ⟨mem_closedBall_zero_iff.2 ha, mem_closedBall_zero_iff.2 hb⟩) hs
    constructor
    · intro b hb a ha
      have ha' : ‖a‖ ≤ R0 := (mem_ball_zero_iff.1 ha).le
      have hb' : ‖b‖ ≤ R0 := mem_closedBall_zero_iff.1 hb
      have hg : DifferentiableAt ℂ (fun a'' => mμ x.2.1 * (dz (W (conj b, a'')) x.2.1 * dz (W (conj b, a'')) (conj x.1) /
          (W (conj b, a'') x.2.1 - W (conj b, a'') (conj x.1)) ^ 2) ^ 2) (conj a) :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.1 * dz (W Q) (conj x.1) / (W Q x.2.1 - W Q (conj x.1)) ^ 2) (conj a)
          (hK ht1 hs (conj b) (conj a) (by rwa [Complex.norm_conj]) (by rwa [Complex.norm_conj]))
          ((differentiableAt_const _).prodMk differentiableAt_id)).pow 2)
      have h1 : DifferentiableAt ℂ (fun a' => conj (mμ x.2.1 * (dz (W (conj b, conj a')) x.2.1 *
          dz (W (conj b, conj a')) (conj x.1) / (W (conj b, conj a') x.2.1 - W (conj b, conj a') (conj x.1)) ^ 2) ^ 2))
          a := differentiableAt_conj_conj_iff.2 hg
      have h2 : DifferentiableAt ℂ (fun a' => mν x.2.2 * (dz (W (a', b)) x.2.2 * dz (W (a', b)) (conj x.1) /
          (W (a', b) x.2.2 - W (a', b) (conj x.1)) ^ 2) ^ 2) a :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.2 * dz (W Q) (conj x.1) / (W Q x.2.2 - W Q (conj x.1)) ^ 2) a (hK ht2 hs a b ha' hb')
          (differentiableAt_id.prodMk (differentiableAt_const _))).pow 2)
      have h3 : DifferentiableAt ℂ (fun a' : ℂ => 1 - a' * b * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) a := by fun_prop
      have h4 : DifferentiableAt ℂ (fun a' => dz (W (a', b)) x.1 * dz (W (a', b)) (conj x.1) /
          (W (a', b) x.1 - W (a', b) (conj x.1)) ^ 2) a :=
        DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.1 * dz (W Q) (conj x.1) / (W Q x.1 - W Q (conj x.1)) ^ 2) a (hK hs hs a b ha' hb') (differentiableAt_id.prodMk (differentiableAt_const _))
      have h := (((h1.mul h2).mul h3).div h4 (hden a b ha' hb')).differentiableWithinAt (s := ball (0 : ℂ) R0)
      rw [hF]
      exact h
    · intro a ha b hb
      have ha' : ‖a‖ ≤ R0 := mem_closedBall_zero_iff.1 ha
      have hb' : ‖b‖ ≤ R0 := (mem_ball_zero_iff.1 hb).le
      have hg : DifferentiableAt ℂ (fun b'' => mμ x.2.1 * (dz (W (b'', conj a)) x.2.1 * dz (W (b'', conj a)) (conj x.1) /
          (W (b'', conj a) x.2.1 - W (b'', conj a) (conj x.1)) ^ 2) ^ 2) (conj b) :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.1 * dz (W Q) (conj x.1) / (W Q x.2.1 - W Q (conj x.1)) ^ 2) (conj b)
          (hK ht1 hs (conj b) (conj a) (by rwa [Complex.norm_conj]) (by rwa [Complex.norm_conj]))
          (differentiableAt_id.prodMk (differentiableAt_const _))).pow 2)
      have h1 : DifferentiableAt ℂ (fun b' => conj (mμ x.2.1 * (dz (W (conj b', conj a)) x.2.1 *
          dz (W (conj b', conj a)) (conj x.1) / (W (conj b', conj a) x.2.1 - W (conj b', conj a) (conj x.1)) ^ 2) ^ 2))
          b := differentiableAt_conj_conj_iff.2 hg
      have h2 : DifferentiableAt ℂ (fun b' => mν x.2.2 * (dz (W (a, b')) x.2.2 * dz (W (a, b')) (conj x.1) /
          (W (a, b') x.2.2 - W (a, b') (conj x.1)) ^ 2) ^ 2) b :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.2 * dz (W Q) (conj x.1) / (W Q x.2.2 - W Q (conj x.1)) ^ 2) b (hK ht2 hs a b ha' hb')
          ((differentiableAt_const _).prodMk differentiableAt_id)).pow 2)
      have h3 : DifferentiableAt ℂ (fun b' : ℂ => 1 - a * b' * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) b := by fun_prop
      have h4 : DifferentiableAt ℂ (fun b' => dz (W (a, b')) x.1 * dz (W (a, b')) (conj x.1) /
          (W (a, b') x.1 - W (a, b') (conj x.1)) ^ 2) b :=
        DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.1 * dz (W Q) (conj x.1) / (W Q x.1 - W Q (conj x.1)) ^ 2) b (hK hs hs a b ha' hb') ((differentiableAt_const _).prodMk differentiableAt_id)
      have h := (((h1.mul h2).mul h3).div h4 (hden a b ha' hb')).differentiableWithinAt (s := ball (0 : ℂ) R0)
      rw [hF]
      exact h
  -- pointwise norm of `F`
  have hCf : ∀ P ∈ D, ∀ s ∈ upperHalf, ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ₑ ≤ 2 := by
    rintro P ⟨h1, h2⟩ s hs
    have hp1 : ‖P.1‖ ≤ R0 := mem_closedBall_zero_iff.1 h1
    have hp2 : ‖P.2‖ ≤ R0 := mem_closedBall_zero_iff.1 h2
    have hm := hCb s hs
    have hle : ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : ‖P.1‖ * ‖P.2‖ * ‖m' s‖ ^ 2 ≤ (R0 * C) ^ 2 := by
        have := mul_le_mul hp1 hp2 (norm_nonneg _) hR0p.le
        have h4 : ‖m' s‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
        nlinarith [norm_nonneg P.1, norm_nonneg P.2, sq_nonneg ‖m' s‖]
      have h5 : (R0 * C) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hR0p.le hC0]
      linarith
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
      _ = 2 := by norm_num
  have hFn : ∀ P x, ‖F P x‖ₑ = ‖mμ x.2.1‖ₑ * ‖dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2‖ₑ ^ 2 *
      (‖mν x.2.2‖ₑ * ‖dz (W P) x.2.2 * dz (W P) (conj x.1) / (W P x.2.2 - W P (conj x.1)) ^ 2‖ₑ ^ 2) *
      ‖1 - P.1 * P.2 * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)‖ₑ *
      ‖(dz (W P) x.1 * dz (W P) (conj x.1) / (W P x.1 - W P (conj x.1)) ^ 2)⁻¹‖ₑ := by
    intro P x
    rw [hF]
    simp only [div_eq_mul_inv (_ * _ * _), enorm_mul, enorm_pow]
    rw [show ‖conj (mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2)‖ₑ =
        ‖mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2‖ₑ by
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj], enorm_mul, enorm_pow]
  -- the uniform `L¹` bound on `D`
  have hmeas3 : (volume.restrict (E ×ˢ (S ×ˢ S)) : Measure (ℂ × (ℂ × ℂ))) =
      (volume.restrict E).prod ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    rfl
  have hmeas2 : (volume.restrict (S ×ˢ S) : Measure (ℂ × ℂ)) = (volume.restrict S).prod (volume.restrict S) := by
    rw [Measure.prod_restrict]
    rfl
  have hM : ∀ P ∈ D, ∫⁻ x in E ×ˢ (S ×ˢ S), ‖F P x‖ₑ ≤ ENNReal.ofReal (2 * M5) := by
    intro P hP
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc ∫⁻ x in E ×ˢ (S ×ˢ S), ‖F P x‖ₑ
        ≤ ∫⁻ s in E, ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖F P (s, (t₁, t₂))‖ₑ := by
          rw [hmeas3]
          exact (lintegral_prod_le _).trans (lintegral_mono fun s => lintegral_prod_le _)
      _ ≤ ∫⁻ s in E, ∫⁻ t₁ in S, ∫⁻ t₂ in S, 2 * (‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) := by
          refine setLIntegral_mono' hEm fun s hs => setLIntegral_mono' hSm fun t₁ _ =>
            setLIntegral_mono' hSm fun t₂ _ => ?_
          rw [hFn]
          calc _ = (‖mμ t₁‖ₑ * ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
                (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
              (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
              ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) *
                ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ₑ := by ring
            _ ≤ _ := by
              rw [mul_comm 2]
              exact mul_le_mul_right (hCf P hP s (hEU hs)) _
      _ ≤ ∫⁻ s in E, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf, 2 * (‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) :=
          lintegral_mono fun s => (lintegral_mono fun t₁ => lintegral_mono_set hSU).trans
            (lintegral_mono_set hSU)
      _ = 2 * ∫⁻ s in E, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf, ‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ := by
          simp only [lintegral_const_mul' (2 : ℝ≥0∞) _ h2]
      _ ≤ 2 * ENNReal.ofReal M5 := by
          gcongr
          exact hM5 P ⟨closedBall_subset_closedBall hR05 hP.1, closedBall_subset_closedBall hR05 hP.2⟩
      _ = ENNReal.ofReal (2 * M5) := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hce : ∀ z : ℂ, ‖conj z‖ₑ = ‖z‖ₑ := fun z => by rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
  -- the fixed-`s` bound
  have hfix : ∀ s ∈ E, ∃ Ms : ℝ, ∀ P ∈ D, ∫⁻ t in S ×ˢ S, ‖F P (s, t)‖ₑ ≤ ENNReal.ofReal Ms := by
    intro s hs
    have hsU := hEU hs
    obtain ⟨M1, hM1⟩ := s71_b2_L1 hC0 hmB hms hμc hMμ0 hμb hsU hR0k hW rfl
    obtain ⟨M2, hM2⟩ := s71_b2_L1 hC0 hmB hms hνc hMν0 hνb hsU hR0k hW rfl
    have hcq : ContinuousOn (fun P : ℂ × ℂ => (1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)) D :=
      ((continuousOn_const (c := (1 : ℂ))).sub
        (by fun_prop : Continuous fun P : ℂ × ℂ => P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)).continuousOn).div
        (s7g_f2_Kc hC0 hmB hms hW hR0k (T := D) (p := fun P => P) (u := fun _ => s) (z := fun _ => s)
          continuousOn_id (fun P hP => hP) continuous_const continuous_const (fun _ _ => hsU) (fun _ _ => hsU))
        (fun P hP => s7g_f2_Kd0 hC0 hmB hms hW (hsub hP) hsU)
    obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℂ) R0).prod (isCompact_closedBall (0 : ℂ) R0)).exists_bound_of_continuousOn hcq
    refine ⟨max M1 0 * (max M2 0 * max B 0), fun P hP => ?_⟩
    have hPs := hswD P hP
    obtain ⟨hi1, hb1⟩ := hM1 _ hPs
    obtain ⟨hi2, hb2⟩ := hM2 P hP
    have hL1 : (∫⁻ t in S, ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
        (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) ≤ ENNReal.ofReal (max M1 0) :=
      calc _ ≤ ∫⁻ t in upperHalf, ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ := lintegral_mono_set hSU
        _ = ENNReal.ofReal (∫ t in upperHalf, ‖mμ t * (dz (W (conj P.2, conj P.1)) t *
            dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖) :=
          (ofReal_integral_norm_eq_lintegral_enorm hi1).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb1.trans (le_max_left _ _))
    have hL2 : (∫⁻ t in S, ‖mν t * (dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2) ^ 2‖ₑ) ≤
        ENNReal.ofReal (max M2 0) :=
      calc _ ≤ ∫⁻ t in upperHalf, ‖mν t * (dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2) ^ 2‖ₑ :=
            lintegral_mono_set hSU
        _ = ENNReal.ofReal (∫ t in upperHalf, ‖mν t * (dz (W P) t * dz (W P) (conj s) /
            (W P t - W P (conj s)) ^ 2) ^ 2‖) := (ofReal_integral_norm_eq_lintegral_enorm hi2).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb2.trans (le_max_left _ _))
    have hcB : ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ ≤ ENNReal.ofReal (max B 0) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hB P hP).trans (le_max_left _ _))
    have hmeasμ : AEMeasurable (fun t => ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
        (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) (volume.restrict S) :=
      (hi1.mono_set hSU).aestronglyMeasurable.enorm
    calc ∫⁻ t in S ×ˢ S, ‖F P (s, t)‖ₑ ≤ ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖F P (s, (t₁, t₂))‖ₑ := by
          rw [hmeas2]
          exact lintegral_prod_le _
      _ = ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ *
            (‖mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2‖ₑ *
              ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ) := by
          refine lintegral_congr fun t₁ => lintegral_congr fun t₂ => ?_
          have e : F P (s, (t₁, t₂)) = conj (mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ *
              dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2) *
              ((mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2) *
              ((1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2))) := by
            simp only [hF]
            ring
          rw [e, enorm_mul, enorm_mul, hce]
      _ = (∫⁻ t₁ in S, ‖mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) *
            ((∫⁻ t₂ in S, ‖mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2‖ₑ) *
              ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ) := by
          rw [← lintegral_mul_const'' _ hmeasμ]
          refine lintegral_congr fun t₁ => ?_
          rw [← lintegral_mul_const' _ _ enorm_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]
      _ ≤ ENNReal.ofReal (max M1 0) * (ENNReal.ofReal (max M2 0) * ENNReal.ofReal (max B 0)) := by
          gcongr
      _ = ENNReal.ofReal (max M1 0 * (max M2 0 * max B 0)) := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul (le_max_right _ _)]
  -- the diagonal: line 1 at `s` is `c ∫∫ F`
  have hdiag : ∀ e ∈ ball (0 : ℂ) R0, ∀ s ∈ E,
      conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s * (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) *
        rhoVar m' e s = (12 / π : ℂ) ^ 2 / (-4) * ∫ t in S ×ˢ S, F (e, conj e) (s, t) := by
    intro e he s hs
    have hsU := hEU hs
    have he1 : ‖e‖ < R0 := mem_ball_zero_iff.1 he
    have hε : ‖e‖ * C < 1 := by nlinarith [norm_nonneg e]
    have hPd : ((e, conj e) : ℂ × ℂ) ∈ D :=
      ⟨mem_closedBall_zero_iff.2 he1.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact he1.le)⟩
    have hKd := s7g_f2_Kdiag hC0 hmB hW hε
    have hFd : ∀ t : ℂ × ℂ, F (e, conj e) (s, t) = conj (mμ t.1 * kernelKbar (fun y => e * m' y) t.1 s ^ 2) *
        (mν t.2 * kernelKbar (fun y => e * m' y) t.2 s ^ 2) * (1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
          kernelKbar (fun y => e * m' y) s s := by
      intro t
      simp only [hF, Complex.conj_conj]
      rw [hKd, hKd, hKd]
    have hfac : (∫ t in S ×ˢ S, F (e, conj e) (s, t)) =
        conj (∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) *
          (∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) *
          ((1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) / kernelKbar (fun y => e * m' y) s s) := by
      have e1 : ∀ t : ℂ × ℂ, F (e, conj e) (s, t) = conj (mμ t.1 * kernelKbar (fun y => e * m' y) t.1 s ^ 2) *
          (mν t.2 * kernelKbar (fun y => e * m' y) t.2 s ^ 2) * ((1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
            kernelKbar (fun y => e * m' y) s s) := fun t => by rw [hFd]; ring
      rw [hmeas2]
      simp_rw [e1]
      rw [integral_mul_const, integral_prod_mul (fun t => conj (mμ t * kernelKbar (fun y => e * m' y) t s ^ 2))
        (fun t => mν t * kernelKbar (fun y => e * m' y) t s ^ 2), integral_conj, setIntegral_congr_set hnull,
        setIntegral_congr_set hnull]
    have h71μ := s71_eq_7_1 hμh hharm hC0 hmB hε hsU
    have h71ν := s71_eq_7_1 hνh hharm hC0 hmB hε hsU
    have hρ : rhoVar m' e s = -4 * kernelKbar (fun y => e * m' y) s s := eq_6_1 m' e s
    have hkd0 : kernelKbar (fun y => e * m' y) s s ≠ 0 := by
      rw [← hKd]
      exact s7g_f2_Kd0 hC0 hmB hms hW (hsub hPd) hsU
    have hρ0 : rhoVar m' e s ≠ 0 := by rw [hρ]; exact mul_ne_zero (by norm_num) hkd0
    have hc12 : conj (12 / π : ℂ) = 12 / π := by rw [map_div₀, Complex.conj_ofReal, map_ofNat]
    have hQ2 : QfunU mν (fun u => e * m' u) s = (12 / π : ℂ) *
        (∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) / rhoVar m' e s := by
      rw [eq_div_iff hρ0]
      linear_combination h71ν
    have hQ1 : conj (QfunU mμ (fun u => e * m' u) s) = (12 / π : ℂ) *
        conj (∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) / rhoVar m' e s := by
      rw [eq_div_iff hρ0]
      have h := congrArg conj h71μ
      rw [map_mul, map_mul, s71_rho_real, hc12] at h
      linear_combination h
    rw [hfac, hQ1, hQ2, hρ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  -- the mixed partials, outer and fixed-`s`
  obtain ⟨hmixi, hmix⟩ := s7g_f2_mixed (m := volume) hTm hR0p hcont hhol hM
  have hΦ2 := (s7g_f2_mixC2 hTm hcont hhol hM).1
  have hcs : ∀ s ∈ E, ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 (s, p.2)) (D ×ˢ (S ×ˢ S)) := fun s hs =>
    hcont.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨hp.1, hs, hp.2⟩
  have hinner : ∀ s ∈ E,
      deriv (fun b => deriv (fun a => ∫ t in S ×ˢ S, F (a, b) (s, t)) 0) 0 =
        ∫ t in S ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 ∧
      ContDiffOn ℂ 2 (fun P => ∫ t in S ×ˢ S, F P (s, t)) (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := by
    intro s hs
    obtain ⟨Ms, hMs⟩ := hfix s hs
    have hh : ∀ t ∈ S ×ˢ S, (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) (s, t))
        (ball (0 : ℂ) R0)) ∧ ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) (s, t))
        (ball (0 : ℂ) R0) := fun t ht => hhol (s, t) ⟨hs, ht⟩
    exact ⟨(s7g_f2_mixed (m := volume) (hSm.prod hSm) hR0p (hcs s hs) hh hMs).2,
      (s7g_f2_mixC2 (m := volume) (hSm.prod hSm) (hcs s hs) hh hMs).1⟩
  have hpt : ∀ s ∈ E, dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
      (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 =
        (12 / π : ℂ) ^ 2 / (-4) * ∫ t in S ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 := by
    intro s hs
    obtain ⟨hm2, hC2⟩ := hinner s hs
    have hev : (fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (12 / π : ℂ) ^ 2 / (-4) * (fun P => ∫ t in S ×ˢ S, F P (s, t)) (e, conj e) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hR0p] with e he
      exact hdiag e he s hs
    rw [s7g_f2_germ hev, s7g_f2_wconst hR0p (s7g_f2_diagC2 hC2), (s7g_f2_ddpartial hR0p hC2).1, hm2]
  have hint3 : Integrable (fun x : ℂ × (ℂ × ℂ) => deriv (fun b => deriv (fun a => F (a, b) x) 0) 0)
      ((volume.restrict E).prod ((volume.restrict S).prod (volume.restrict S))) := by
    rw [← hmeas3]
    exact hmixi
  refine ⟨?_, ?_⟩
  · refine (hint3.integral_prod_left.const_mul ((12 / π : ℂ) ^ 2 / (-4))).congr ?_
    filter_upwards [ae_restrict_mem hEm] with s hs
    rw [hpt s hs, hmeas2]
  · have hgev : (fun e => ∫ s in E, conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (fun P => (12 / π : ℂ) ^ 2 / (-4) * ∫ x in E ×ˢ (S ×ˢ S), F P x) (e, conj e) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hR0p] with e he
      have he1 : ‖e‖ < R0 := mem_ball_zero_iff.1 he
      have hPd : ((e, conj e) : ℂ × ℂ) ∈ D :=
        ⟨mem_closedBall_zero_iff.2 he1.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact he1.le)⟩
      have hint : Integrable (F (e, conj e)) ((volume.restrict E).prod ((volume.restrict S).prod (volume.restrict S))) := by
        rw [← hmeas3]
        refine ⟨?_, lt_of_le_of_lt (hM _ hPd) ENNReal.ofReal_lt_top⟩
        exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun x hx => ⟨hPd, hx⟩)).aestronglyMeasurable hTm
      show _ = (12 / π : ℂ) ^ 2 / (-4) * ∫ x in E ×ˢ (S ×ˢ S), F (e, conj e) x
      rw [hmeas3, integral_prod _ hint, ← hmeas2, ← integral_const_mul]
      exact setIntegral_congr_fun hEm fun s hs => hdiag e he s hs
    have hΦC : ContDiffOn ℂ 2 (fun P => (12 / π : ℂ) ^ 2 / (-4) * ∫ x in E ×ˢ (S ×ˢ S), F P x)
        (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := contDiffOn_const.mul hΦ2
    rw [s7g_f2_germ hgev, (s7g_f2_ddpartial hR0p hΦC).1]
    simp only [deriv_const_mul_field']
    rw [hmix, hmeas3, integral_prod _ hint3, ← integral_const_mul]
    refine setIntegral_congr_fun hEm fun s hs => ?_
    rw [hpt s hs, hmeas2]

/-- The projection `P(R(f, κ'))` at `w_{κ'}(S s)` through the Cayley chart (`s8g_c_line2D` hI step, `s8g_c_line2U`
inner transport, `s8g_c_kernel`, `s71_eq_7_1`):
`P(R(f,κ'))(w(Ss)) · 4 \overline{w'(Ss) S'(s)}² = (1 - |w(Ss)|²)² ρ^{ea}(s) Q_U(f̃, ea)(s)`. -/
theorem s8r_P {κ' f a φa Tf φf : ℂ → ℂ} (hκ' : IsHarmonicD κ') {k' : ℝ} (hk1 : k' < 1)
    (hk' : ∀ z ∈ unitDisc, ‖κ' z‖ ≤ k') (hf : IsHarmonicD f) (ha : IsHarmonicU a φa) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) {e : ℂ} (hek : 2 * ‖e‖ * k < 1)
    (hm : ∀ u ∈ upperHalf, e * a u = κ' (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hTf : IsHarmonicU Tf φf)
    (hTfe : ∀ u ∈ upperHalf, Tf u = f (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {s : ℂ} (hs : s ∈ upperHalf) :
    harmonicProjD (RnmD f κ') (wD κ' (cayley s)) * (4 * conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) ^ 2) =
      (1 - ‖wD κ' (cayley s)‖ ^ 2) ^ 2 * (rhoVar a e s * QfunU Tf (fun u => e * a u) s) ∧
    rhoVar a e s * (1 - ‖wD κ' (cayley s)‖ ^ 2) ^ 2 =
      4 * (‖dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)‖ : ℂ) ^ 2 := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨W, hW⟩ : ∃ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * a u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (a (conj u)) else 0) := ⟨_, rfl⟩
  set q : ℂ × ℂ := (e, 0) with hqd
  have hq : ((q.1, q.2), (conj q.1, conj q.2)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) ‖e‖ := by
    simp only [hqd, mem_closedBall_zero_iff, Prod.norm_def, norm_zero, map_zero, Complex.norm_conj]
    exact max_le (max_le le_rfl (norm_nonneg e)) (max_le le_rfl (norm_nonneg e))
  have hm' : ∀ u ∈ upperHalf, q.1 * a u + q.2 * a u =
      κ' (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := fun u hu => by
    show e * a u + 0 * a u = _
    rw [zero_mul, add_zero, hm u hu]
  have hVeq : W ((q.1, q.2), (conj q.1, conj q.2)) = wU (fun u => e * a u) := by
    rw [hW]
    beta_reduce
    show _ = normalizedSolution (extU _)
    congr 1
    funext u
    unfold extU
    by_cases h1 : 0 < u.im
    · have h2 : ¬ u.im < 0 := by linarith
      simp [h1, h2, hqd]
    · by_cases h2 : u.im < 0
      · simp [h1, h2, hqd]
      · simp [h1, h2]
  obtain ⟨hsym, -⟩ := s8g_c_Vsym ha ha hk hak hak hW (norm_nonneg e) hek hq
  rw [hVeq] at hsym
  set V := wU (fun u => e * a u) with hVdef
  have hdV : ∀ x, dz V (conj x) = conj (dz V x) := QCV.qcv_dz_conj_sym hsym
  have hker : ∀ τ ∈ upperHalf, kernelKbar (fun y => e * a y) τ s =
      -(dz (wD κ') (cayley τ) * conj (dz (wD κ') (cayley s)) /
        (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 2 * (2 * I / (τ + I) ^ 2 * conj (2 * I / (s + I) ^ 2))) := by
    intro τ hτ
    have h := s8g_c_kernel ha ha hk hak hak hW (norm_nonneg e) hek hq hκ' hk1 hk' hm' hs hτ
    rw [hVeq] at h
    rw [h, neg_neg]
    unfold kernelKbar
    rw [← hdV, ← hsym]
  -- the disc data
  obtain ⟨⟨e', he'⟩, hmaps, hD, hdiff⟩ := s8w_wD_facts hκ' hk1 hk'
  have hinj : InjOn (wD κ') unitDisc := by rw [← he']; exact e'.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ') u ∧ dzbar (wD κ') u = κ' u * dz (wD κ') u ∧ ‖κ' u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk' u hu).trans hk1.le⟩
  have hRf := s8w_R_facts hκ' hk1 hk' (harmonicD_continuousOn hf) (harmonicD_bound hf).choose_spec
  have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hcm : ∀ u ∈ upperHalf, cayley u ∈ unitDisc := fun u hu =>
    isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have hv := hcm s hs
  have hwv : wD κ' (cayley s) ∈ unitDisc := hmaps hv
  -- K2 on `𝔻`
  have hI : (∫ ζ in unitDisc, RnmD f κ' ζ / (1 - ζ * conj (wD κ' (cayley s))) ^ 4) =
      ∫ t in unitDisc, f t * dz (wD κ') t ^ 2 / (1 - wD κ' t * conj (wD κ' (cayley s))) ^ 4 := by
    conv_lhs => rw [← hD]
    rw [s8w_change (S := unitDisc) hinj hd measurableSet_ball subset_rfl]
    refine setIntegral_congr_fun measurableSet_ball fun t ht => ?_
    rw [hRf.1 t ht, Complex.real_smul]
    have hdn := (hdiff t ht).2.1
    have hcd : conj (dz (wD κ') t) ≠ 0 := (map_ne_zero _).mpr hdn
    have hK : (1 : ℂ) - (‖κ' t‖ : ℂ) ^ 2 ≠ 0 := by
      have : (1 : ℝ) - ‖κ' t‖ ^ 2 ≠ 0 := by nlinarith [hk' t ht, norm_nonneg (κ' t)]
      exact_mod_cast this
    push_cast
    rw [hnsq (dz (wD κ') t)]
    field_simp
  -- the Cayley chart
  have hDimg : cayley '' upperHalf = unitDisc := isConformalOnto_cayley.2.2
  have hinner : (∫ t in unitDisc, f t * dz (wD κ') t ^ 2 / (1 - wD κ' t * conj (wD κ' (cayley s))) ^ 4) =
      ∫ τ in upperHalf, ((‖2 * I / (τ + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
        (f (cayley τ) * dz (wD κ') (cayley τ) ^ 2 / (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 4) := by
    conv_lhs => rw [← hDimg]
    exact s8g_cay_cov hU subset_rfl _
  have hB : conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) ≠ 0 := by
    refine (map_ne_zero _).2 (mul_ne_zero (hdiff _ hv).2.1 ?_)
    exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hs))
  have hpt : ∀ τ ∈ upperHalf, ((‖2 * I / (τ + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
      (f (cayley τ) * dz (wD κ') (cayley τ) ^ 2 / (1 - wD κ' (cayley τ) * conj (wD κ' (cayley s))) ^ 4) =
      Tf τ * kernelKbar (fun y => e * a y) τ s ^ 2 / conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) ^ 2 := by
    intro τ hτ
    have hτv := hcm τ hτ
    have hDn : 1 - wD κ' (cayley τ) * conj (wD κ' (cayley s)) ≠ 0 := by
      intro h0
      have h1 : wD κ' (cayley τ) * conj (wD κ' (cayley s)) = 1 := by linear_combination -h0
      have h2 := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at h2
      have h3 := mem_ball_zero_iff.1 (hmaps hτv)
      have h4 := mem_ball_zero_iff.1 hwv
      nlinarith [norm_nonneg (wD κ' (cayley τ)), norm_nonneg (wD κ' (cayley s))]
    have hct : 2 * I / (τ + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hτ))
    have hcct : conj (2 * I / (τ + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hct
    rw [hTfe τ hτ, hker τ hτ, Complex.ofReal_pow, hnsq]
    simp only [map_mul] at hB ⊢
    generalize 1 - wD κ' (cayley τ) * conj (wD κ' (cayley s)) = D at hDn ⊢
    generalize dz (wD κ') (cayley τ) = A
    generalize conj (dz (wD κ') (cayley s)) = B at hB ⊢
    generalize 2 * I / (s + I) ^ 2 = cs at hB ⊢
    generalize 2 * I / (τ + I) ^ 2 = ct at hct hcct ⊢
    generalize conj cs = ccs at hB ⊢
    generalize conj ct = cct at hcct ⊢
    have hB1 : B ≠ 0 := left_ne_zero_of_mul hB
    have hB2 : ccs ≠ 0 := right_ne_zero_of_mul hB
    field_simp
  have h71 := s71_eq_7_1 hTf ha hk ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU,
    (ae_restrict_mem hU).mono fun u hu => hak u hu⟩ (ε := e) (by nlinarith [norm_nonneg e]) hs
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hρ : rhoVar a e s * (1 - ‖wD κ' (cayley s)‖ ^ 2) ^ 2 =
      4 * (‖dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)‖ : ℂ) ^ 2 := by
    have h1 : (1 : ℝ) - ‖wD κ' (cayley s)‖ ^ 2 ≠ 0 := by
      have := mem_ball_zero_iff.1 hwv
      nlinarith [norm_nonneg (wD κ' (cayley s))]
    have hD0 : (1 : ℂ) - wD κ' (cayley s) * conj (wD κ' (cayley s)) ≠ 0 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast h1
    have hcs : 2 * I / (s + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hs))
    rw [eq_6_1, hker s hs, hnsq (wD κ' (cayley s)), hnsq (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)), map_mul]
    generalize 1 - wD κ' (cayley s) * conj (wD κ' (cayley s)) = D at hD0 ⊢
    field_simp
  refine ⟨?_, hρ⟩
  unfold harmonicProjD
  rw [hI, hinner, setIntegral_congr_fun hU hpt, integral_div]
  generalize (∫ τ in upperHalf, Tf τ * kernelKbar (fun y => e * a y) τ s ^ 2) = J at h71 ⊢
  generalize conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) = cB at hB ⊢
  rw [h71]
  field_simp
  ring

/-- STUB DR_LINE1 (part of `s8g_dg_rep`). Line 1 of the second variation over `E = 𝕌 ∩ S⁻¹F` (Γ-version of
`s7g_f2_line1U` + `s7g_f2_line1D`): with the Cayley transports `X = ν̃`, `Y = μ̃`, `a = κ̃`
(`f̃(u) = f(S u) S̄'(u)/S'(u)`), near `0`
`g_{μν̄}(eκ) = ∫_E \overline{Q_X(ea)} Q_Y(ea) (1 - |e|²|a|²) ρ_{ea}`, and `∂_ē∂_e` passes under `∫_E` at `0`. -/
theorem s8g_dr_line1 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) {X Y a : ℂ → ℂ}
    (hX : X = fun u => ν (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hY : Y = fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (ha : a = fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    (∃ r : ℝ, 0 < r ∧ ∀ e ∈ ball (0 : ℂ) r, gGamma Γ μ ν (fun z => e * κ z) =
      ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
        conj (QfunU X (fun u => e * a u) s) * QfunU Y (fun u => e * a u) s *
          (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) ∧
    IntegrableOn (fun s => dzbar (dz fun e => conj (QfunU X (fun u => e * a u) s) * QfunU Y (fun u => e * a u) s *
        (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) 0) (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
    dzbar (dz fun e => ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
        conj (QfunU X (fun u => e * a u) s) * QfunU Y (fun u => e * a u) s *
          (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) 0 =
      ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
        dzbar (dz fun e => conj (QfunU X (fun u => e * a u) s) * QfunU Y (fun u => e * a u) s *
          (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) 0 := by
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hCκ0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ 0 h0D)
  obtain ⟨φa, ha', hak⟩ := s8g_c_kD hκ hCκ
  obtain ⟨φY, hY', -⟩ := s8g_c_kD hμ hCμ
  obtain ⟨φX, hX', -⟩ := s8g_c_kD hν hCν
  rw [← ha] at ha'
  replace hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ Cκ := fun u hu => by rw [ha]; exact hak u hu
  rw [← hY] at hY'
  rw [← hX] at hX'
  obtain ⟨hEm, hEU, hEimg⟩ := s8g_cayE hΓ.1
  have hEA := s8g_cayE_area hΓ
  obtain ⟨hint, hder⟩ := s8r_line1D ha' hX' hY' hEm hEU hEA
  refine ⟨⟨1 / (4 * (Cκ + 1)), by positivity, fun e he => ?_⟩, hint, hder⟩
  have he1 : ‖e‖ < 1 / (4 * (Cκ + 1)) := mem_ball_zero_iff.1 he
  have he4 : ‖e‖ * (4 * (Cκ + 1)) < 1 := by rwa [lt_div_iff₀ (by positivity)] at he1
  have hek : 2 * ‖e‖ * Cκ < 1 := by nlinarith [norm_nonneg e]
  have hk1 : ‖e‖ * Cκ < 1 := by nlinarith [norm_nonneg e]
  set κ' : ℂ → ℂ := fun z => e * κ z with hκ'd
  have hκ' : IsHarmonicD κ' := by
    have h := s8g_harm_lin hκ hκ (e - 1)
    have hf : (fun z => κ z + (e - 1) * κ z) = κ' := by
      funext z
      simp only [hκ'd]
      ring
    rwa [hf] at h
  have hk' : ∀ z ∈ unitDisc, ‖κ' z‖ ≤ ‖e‖ * Cκ := fun z hz => by
    show ‖e * κ z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hCκ z hz) (norm_nonneg e)
  have hm : ∀ u ∈ upperHalf, e * a u = κ' (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) :=
    fun u _ => by
      rw [ha]
      simp only [hκ'd]
      ring
  have hYe : ∀ u ∈ upperHalf, Y u = μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) :=
    fun u _ => by rw [hY]
  have hXe : ∀ u ∈ upperHalf, X u = ν (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) :=
    fun u _ => by rw [hX]
  obtain ⟨⟨e', he'⟩, hmaps, -, hdiff⟩ := s8w_wD_facts hκ' hk1 hk'
  have hinj : InjOn (wD κ') unitDisc := by rw [← he']; exact e'.injective.injOn
  have hd : ∀ u ∈ unitDisc, DifferentiableAt ℝ (wD κ') u ∧ dzbar (wD κ') u = κ' u * dz (wD κ') u ∧ ‖κ' u‖ ≤ 1 :=
    fun u hu => ⟨(hdiff u hu).1, (hdiff u hu).2.2, (hk' u hu).trans hk1.le⟩
  have hFD := s8w_fundD hΓ.1
  have hcm : ∀ u ∈ upperHalf, cayley u ∈ unitDisc := fun u hu =>
    isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have hF : wD κ' '' fundDomainOn Γ unitDisc =
      wD κ' '' (cayley '' (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc)) := by rw [hEimg]
  unfold gGamma
  rw [hF, s8w_change (S := cayley '' (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc)) hinj hd
    (by rw [hEimg]; exact hFD.1) (by rw [hEimg]; exact hFD.2.1), s8g_cay_cov hEm hEU]
  refine setIntegral_congr_fun hEm fun s hs => ?_
  have hsU := hEU hs
  obtain ⟨hPμ, hρ⟩ := s8r_P hκ' hk1 hk' hμ ha' hCκ0 hak hek hm hY' hYe hsU
  obtain ⟨hPν, -⟩ := s8r_P hκ' hk1 hk' hν ha' hCκ0 hak hek hm hX' hXe hsU
  have hwv := hmaps (hcm s hsU)
  have hρr := s71_rho_real a e s
  have hcs : 2 * I / (s + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hsU))
  have hA : dz (wD κ') (cayley s) ≠ 0 := (hdiff _ (hcm s hsU)).2.1
  have hnκ : ‖κ' (cayley s)‖ = ‖e‖ * ‖a s‖ := by
    show ‖e * κ (cayley s)‖ = _
    rw [ha, norm_mul, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hcs), mul_one]
  have hnsq : ∀ x : ℂ, ((‖x‖ : ℂ)) ^ 2 = x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hZ : (1 : ℂ) - (‖wD κ' (cayley s)‖ : ℂ) ^ 2 ≠ 0 := by
    have h1 : (1 : ℝ) - ‖wD κ' (cayley s)‖ ^ 2 ≠ 0 := by
      have := mem_ball_zero_iff.1 hwv
      nlinarith [norm_nonneg (wD κ' (cayley s))]
    exact_mod_cast h1
  have hPν' := congrArg conj hPν
  simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_conj, hρr] at hPν'
  rw [hnκ, Complex.real_smul]
  unfold rho
  push_cast
  have e4 : rhoVar a e s = 4 * (‖dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)‖ : ℂ) ^ 2 /
      (1 - (‖wD κ' (cayley s)‖ : ℂ) ^ 2) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hZ)]
    exact hρ
  have e1 : harmonicProjD (RnmD μ κ') (wD κ' (cayley s)) = (1 - (‖wD κ' (cayley s)‖ : ℂ) ^ 2) ^ 2 *
      (rhoVar a e s * QfunU Y (fun u => e * a u) s) /
        (4 * conj (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) ^ 2) := by
    rw [eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 ((map_ne_zero _).2 (mul_ne_zero hA hcs))))]
    exact hPμ
  have e2 : conj (harmonicProjD (RnmD ν κ') (wD κ' (cayley s))) = (1 - (‖wD κ' (cayley s)‖ : ℂ) ^ 2) ^ 2 *
      (rhoVar a e s * conj (QfunU X (fun u => e * a u) s)) /
        (4 * (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)) ^ 2) := by
    rw [eq_div_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 2 (mul_ne_zero hA hcs)))]
    linear_combination hPν'
  rw [e1, e2, e4, hnsq (dz (wD κ') (cayley s) * (2 * I / (s + I) ^ 2)), hnsq (dz (wD κ') (cayley s)),
    hnsq (2 * I / (s + I) ^ 2)]
  generalize QfunU Y (fun u => e * a u) s = QY
  generalize conj (QfunU X (fun u => e * a u) s) = QX
  generalize (‖wD κ' (cayley s)‖ : ℂ) = r at hZ ⊢
  have hcA : conj (dz (wD κ') (cayley s)) ≠ 0 := (map_ne_zero _).2 hA
  have hcc : conj (2 * I / (s + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hcs
  simp only [map_mul]
  generalize dz (wD κ') (cayley s) = A at hA hcA ⊢
  generalize conj A = cA at hcA ⊢
  generalize 2 * I / (s + I) ^ 2 = cs at hcs hcc ⊢
  generalize conj cs = ccs at hcc ⊢
  field_simp


/-- Hermitian symmetry of the metric: `g_{νμ̄}(κ) = \overline{g_{μν̄}(κ)}`. -/
theorem s8g_dr_herm (Γ : Subgroup SL2C) (μ ν κ : ℂ → ℂ) : gGamma Γ ν μ κ = conj (gGamma Γ μ ν κ) := by
  unfold gGamma
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Line 2 of the second variation over `E` (Γ-version of `s7g_f2_line2`): with the Cayley transports `X = ν̃`,
`Y = μ̃`, `a = κ̃`, both mixed derivatives of `e ↦ g_{μν̄}(eκ)` at `0` are `(12/π) ∫_E X̄ ∂∂̄ J_Y`, where
`J_Y(e)(s) = ∫_𝕌 Y K_{ea}(·, s)²`. -/
theorem s8g_dr_line2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) {X Y a : ℂ → ℂ}
    (hX : X = fun u => ν (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hY : Y = fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (ha : a = fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    IntegrableOn (fun s => conj (X s) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0)
        (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
    dzbar (dz fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 =
      (12 / π : ℂ) * ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, conj (X s) *
        dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 ∧
    IntegrableOn (fun s => conj (X s) *
      dz (dzbar fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0)
        (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
    dz (dzbar fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 =
      (12 / π : ℂ) * ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, conj (X s) *
        dz (dzbar fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 ∧
    dz (dzbar fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 = dzbar (dz fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 := by
  have hU := measurableSet_upperHalf_aux
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  have hCκ0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ 0 h0D)
  have hCμ0 : 0 ≤ Cμ := (norm_nonneg _).trans (hCμ 0 h0D)
  have hd0 : ∀ u ∈ upperHalf, 2 * I / (u + I) ^ 2 ≠ 0 := fun u hu =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (cayley_den_ne_zero hu))
  have hph1 : ∀ u ∈ upperHalf, ‖conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)‖ = 1 := fun u hu => by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (hd0 u hu))]
  have hphc : ContinuousOn (fun u => conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) upperHalf := by
    have hc : ContinuousOn (fun u : ℂ => 2 * I / (u + I) ^ 2) upperHalf :=
      continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
        fun u hu => pow_ne_zero _ (cayley_den_ne_zero hu)
    exact (Complex.continuous_conj.comp_continuousOn hc).div hc hd0
  have hcayc : ContinuousOn cayley upperHalf := fun u hu =>
    (rhoU_hasDerivAt_cayley hu).continuousAt.continuousWithinAt
  have hcm : MapsTo cayley upperHalf unitDisc := fun u hu => isConformalOnto_cayley.2.2 ▸ mem_image_of_mem cayley hu
  have htr : ∀ {f : ℂ → ℂ}, IsHarmonicD f →
      ContinuousOn (fun u => f (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) upperHalf :=
    fun hf => ((harmonicD_continuousOn hf).comp hcayc hcm).mul hphc
  have hYc : ContinuousOn Y upperHalf := by rw [hY]; exact htr hμ
  have hXc : ContinuousOn X upperHalf := by rw [hX]; exact htr hν
  obtain ⟨φa, ha', hak0⟩ := s8g_c_kD hκ hCκ
  obtain ⟨φY, hYh, hYk⟩ := s8g_c_kD hμ hCμ
  rw [← ha] at ha'
  replace hak0 : ∀ u ∈ upperHalf, ‖a u‖ ≤ Cκ := fun u hu => by rw [ha]; exact hak0 u hu
  rw [← hY] at hYh
  replace hYk : ∀ u ∈ upperHalf, ‖Y u‖ ≤ Cμ := fun u hu => by rw [hY]; exact hYk u hu
  have hk := hCκ0
  obtain ⟨hEm, hEU, -⟩ := s8g_cayE hΓ.1
  have hEA := s8g_cayE_area hΓ
  set E := upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc with hEdef
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  have hTm : MeasurableSet (E ×ˢ S) := hEm.prod hSm
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℂ, A = fun s => conj (X s) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ → ℂ, B = fun s => conj (Y s) := ⟨_, rfl⟩
  have hBY : ∀ t, conj (B t) = Y t := fun t => by rw [hBdef, Complex.conj_conj]
  have hAc : ContinuousOn A upperHalf := by rw [hAdef]; exact Complex.continuous_conj.comp_continuousOn hXc
  have hBc : ContinuousOn B upperHalf := by rw [hBdef]; exact Complex.continuous_conj.comp_continuousOn hYc
  have hAb : ∀ s ∈ E, ‖A s‖ ≤ Cν := fun s hs => by
    rw [hAdef, Complex.norm_conj, hX]
    show ‖ν (cayley s) * _‖ ≤ Cν
    rw [norm_mul, hph1 s (hEU hs), mul_one]
    exact hCν _ (hcm (hEU hs))
  have hBb : ∀ s ∈ upperHalf, ‖B s‖ ≤ Cμ := fun s hs => by
    rw [hBdef, Complex.norm_conj]
    exact hYk s hs
  -- the 4-parameter family with `b = a`, and its 2-parameter restriction
  obtain ⟨W, hW'⟩ : ∃ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * a u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (a (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : ℂ × ℂ → ℂ → ℂ, W2 = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then a u else 0) + P.2 * (if u.im < 0 then conj (a (conj u)) else 0) := ⟨_, rfl⟩
  have hWW : ∀ x y : ℂ, W ((x, 0), (y, 0)) = W2 (x, y) := by
    intro x y
    simp only [hW', hW2]
    congr 1
    funext u
    split_ifs <;> ring
  obtain ⟨R0, hR0p, hR0k2, M, hM⟩ := s8g_c_L1 ha' ha' hk hak0 hak0 hW' hEm hEU hU subset_rfl hEA hAb hBb
  have hR0k : R0 * Cκ < 1 := by nlinarith
  have hn4 : ∀ x y : ℂ, ‖(((x, 0), (y, 0)) : (ℂ × ℂ) × (ℂ × ℂ))‖ = ‖((x, y) : ℂ × ℂ)‖ := fun x y => by
    simp only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have hmB : IsBeltramiCoeff a upperHalf Cκ :=
    ⟨(harmonicU_continuousOn ha').aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hak0 u hu⟩
  have hms := wr_isHarmonicU_contDiffOn ha'
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ × ℂ → ℂ, F = fun P x => A x.1 * (conj (B x.2) *
      (dz (W2 P) x.2 * dz (W2 P) (conj x.1) / (W2 P x.2 - W2 P (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  have hcont : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 p.2)
      ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ (E ×ˢ S)) := by
    rw [hF]
    exact (s7g_l3_cont hk hmB hms hW2 subset_rfl hAc hBc hR0k).mono
      (prod_mono subset_rfl (prod_mono hEU hSU))
  have hhol : ∀ x ∈ E ×ˢ S,
      (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R0)) ∧
        ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R0) := by
    intro x hx
    have h := s71_b2_holo (μ := fun t => A x.1 * conj (B t)) hk hmB hms (hEU hx.1) hR0k hW2 rfl (hSU hx.2)
    refine ⟨fun b hb => (h.1 b hb).congr fun a _ => ?_, fun a ha => (h.2 a ha).congr fun b _ => ?_⟩
    · rw [hF]
      ring
    · rw [hF]
      ring
  have hM2 : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ∫⁻ x in E ×ˢ S, ‖F P x‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    have hP4 : (((P.1, 0), (P.2, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
      rw [mem_closedBall_zero_iff, hn4]
      exact norm_prod_le_iff.2 ⟨mem_closedBall_zero_iff.1 hP.1, mem_closedBall_zero_iff.1 hP.2⟩
    refine le_trans (lintegral_mono_set (prod_mono subset_rfl hSU)) (le_of_eq_of_le ?_ (hM _ hP4))
    rw [hF, hWW]
  obtain ⟨hmixi, hmix⟩ := s7g_f2_mixed (m := volume) hTm hR0p hcont hhol hM2
  have hΦ2 := (s7g_f2_mixC2 hTm hcont hhol hM2).1
  obtain ⟨MY, hMY0, hYb⟩ := harmonicU_bounded hYh
  have hpt : ∀ s ∈ E, (∫ t in S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0) =
      conj (X s) * dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 := by
    intro s hs
    obtain ⟨hJ1, hJ2, -⟩ := s7g_f2_Jdd hk hmB hms hYc hMY0 hYb hR0p hR0k hW2 (hEU hs)
    rw [hJ2, hJ1, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, hBY, hAdef, deriv_const_mul_field']
  have hsym : ∀ s ∈ E,
      dz (dzbar fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 =
        dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 := by
    intro s hs
    obtain ⟨-, hJ2, hJ3⟩ := s7g_f2_Jdd hk hmB hms hYc hMY0 hYb hR0p hR0k hW2 (hEU hs)
    rw [hJ2, hJ3]
  have hint2 : Integrable (fun x : ℂ × ℂ => deriv (fun b => deriv (fun a => F (a, b) x) 0) 0)
      ((volume.restrict E).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hmixi
  have hI1 : IntegrableOn (fun s => conj (X s) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0) E := by
    refine hint2.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem hEm] with s hs
    exact hpt s hs
  have hI2 : IntegrableOn (fun s => conj (X s) *
      dz (dzbar fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0) E := by
    refine hI1.congr ?_
    filter_upwards [ae_restrict_mem hEm] with s hs
    rw [hsym s hs]
  -- the representation `g(eκ) = Φ(e, ē)` near `0`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ, Φ = fun P => (12 / π : ℂ) * ∫ x in E ×ˢ S, F P x := ⟨_, rfl⟩
  have hΦC : ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := by
    rw [hΦ]
    exact contDiffOn_const.mul hΦ2
  obtain ⟨δ₀, hδ0, hδ1, C3, hC3⟩ := s8w_density
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (δ₀ / (Cκ + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  have hrep : ∀ e ∈ ball (0 : ℂ) r, gGamma Γ μ ν (fun z => e * κ z) = Φ (e, conj e) := by
    intro e he
    have her : ‖e‖ < r := mem_ball_zero_iff.1 he
    have heR : ‖e‖ < R0 := lt_of_lt_of_le her hrR
    have heδ : ‖e‖ * (Cκ + 1) < δ₀ := by
      have h := lt_of_lt_of_le her (show r ≤ δ₀ / (Cκ + 1) by rw [hr]; exact min_le_right _ _)
      rwa [lt_div_iff₀ (by positivity)] at h
    have hκp : IsHarmonicD (fun z => e * κ z) := by
      refine (congrArg IsHarmonicD ?_).mp (s8g_harm_lin (s8g_harm_lin hκ hκ (-1)) hκ e)
      funext z
      ring
    have hκpΓ : IsGammaInvD Γ (fun z => e * κ z) := by
      refine (congrArg (IsGammaInvD Γ) ?_).mp (s8g_inv_lin (s8g_inv_lin hκΓ hκΓ (-1)) hκΓ e)
      funext z
      ring
    have hbde : ∀ z ∈ unitDisc, ‖e * κ z‖ ≤ ‖e‖ * Cκ := fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCκ z hz) (norm_nonneg _)
    have hkδ : ‖e‖ * Cκ < δ₀ := by nlinarith [norm_nonneg e]
    have hC := hC3 _ hκp fun z hz => lt_of_le_of_lt (hbde z hz) hkδ
    have hPmem : (((e, 0), (conj e, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
      rw [mem_closedBall_zero_iff, hn4]
      refine norm_prod_le_iff.2 ⟨heR.le, ?_⟩
      rw [Complex.norm_conj]
      exact heR.le
    have hm : ∀ u ∈ upperHalf, (e, (0 : ℂ)).1 * a u + (e, (0 : ℂ)).2 * a u =
        (fun z => e * κ z) (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
      intro u _
      rw [ha]
      simp only []
      ring
    have hq : (((e, (0 : ℂ)).1, (e, (0 : ℂ)).2), (conj (e, (0 : ℂ)).1, conj (e, (0 : ℂ)).2)) =
        (((e, 0), (conj e, 0)) : (ℂ × ℂ) × (ℂ × ℂ)) := by
      rw [map_zero]
    have hrep0 := s8g_c_line2U hΓ hμ hν hμΓ hνΓ hκp hκpΓ (lt_trans hkδ hδ1) hbde hC ha' ha' hk hak0 hak0 hW'
      hR0p.le hR0k2 (q := (e, 0)) (hq ▸ hPmem) hm
    rw [hq, hWW] at hrep0
    have hPm2 : ((e, conj e) : ℂ × ℂ) ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 :=
      ⟨mem_closedBall_zero_iff.2 heR.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact heR.le)⟩
    have hint : Integrable (F (e, conj e)) ((volume.restrict E).prod (volume.restrict S)) := by
      rw [Measure.prod_restrict]
      refine ⟨?_, lt_of_le_of_lt (hM2 _ hPm2) ENNReal.ofReal_lt_top⟩
      exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨hPm2, hx⟩)).aestronglyMeasurable hTm
    have e2 : (∫ x in E ×ˢ S, F (e, conj e) x) = ∫ s in E, ∫ t in S, F (e, conj e) (s, t) := by
      rw [← integral_prod _ hint, Measure.prod_restrict]
      rfl
    rw [hrep0, show Φ (e, conj e) = (12 / π : ℂ) * ∫ x in E ×ˢ S, F (e, conj e) x by rw [hΦ], e2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    dsimp only
    rw [← setIntegral_congr_set hnull, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, hAdef, hBY, hX, hY]
  have hgev : (fun e => gGamma Γ μ ν (fun z => e * κ z)) =ᶠ[𝓝 (0 : ℂ)] fun e => Φ (e, conj e) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr0] with e he
    exact hrep e he
  obtain ⟨hdd1, hdd2⟩ := s7g_f2_ddpartial hR0p hΦC
  have hval : deriv (fun b => deriv (fun a => Φ (a, b)) 0) 0 = (12 / π : ℂ) * ∫ s in E, conj (X s) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0 := by
    rw [hΦ]
    simp only [deriv_const_mul_field']
    rw [hmix]
    congr 1
    have e1 : (∫ x in E ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) x) 0) 0) =
        ∫ s in E, ∫ t in S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 := by
      rw [← integral_prod _ hint2, Measure.prod_restrict]
      rfl
    rw [e1]
    exact setIntegral_congr_fun hEm hpt
  refine ⟨hI1, ?_, hI2, ?_, ?_⟩
  · rw [s7g_f2_germ hgev, hdd1, hval]
  · rw [s7g_f2_germ2 hgev, hdd2, hval]
    congr 1
    exact setIntegral_congr_fun hEm fun s hs => by rw [hsym s hs]
  · rw [s7g_f2_germ2 hgev, hdd2, ← hdd1, ← s7g_f2_germ hgev]

/-- `ρ_𝕌` is integrable on `E = 𝕌 ∩ S⁻¹F`. -/
theorem s8g_dr_rhoint {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) :
    IntegrableOn (fun s => rhoU s) (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) := by
  have hm : Measurable (fun s : ℂ => rhoU s) := by
    unfold rhoU
    exact (Complex.measurable_im.pow_const 2).inv
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun s => by unfold rhoU; positivity)).2 (s8g_cayE_area hΓ)

/-- STUB DG_REP. Representation of the second variation over `E = 𝕌 ∩ S⁻¹F` (`S` = Cayley), the Γ-version of the
line computations in `thm_7_7`: with the Cayley transports `X = ν̃`, `Y = μ̃`, `a = κ̃` (`f̃(u) = f(S u) S̄'(u)/S'(u)`),
`∂²_{εε̄} g_{μν̄}(εκ)|₀ = ∫_E A + ∫_E B - ∫_E C`, where `A = X̄ Y |a|² ρ_𝕌`, `B = X̄ Y ρ_𝕌 G_𝕌(|a|²)` and
`C = \overline{∂_ε̄ Q_X(εa)|₀} ∂_ε̄ Q_Y(εa)|₀ ρ_𝕌`; all three are integrable on `E`. -/
theorem s8g_dg_rep {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) {X Y a : ℂ → ℂ}
    (hX : X = fun u => ν (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hY : Y = fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (ha : a = fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    IntegrableOn (fun s => conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s)
        (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
      IntegrableOn (fun s => conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s))
        (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
      IntegrableOn (fun s => conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
          dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s)
        (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) ∧
      dz (dzbar fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 =
        (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s) +
          (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
            conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s)) -
          ∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
            conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
              dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s := by
  have hU := measurableSet_upperHalf_aux
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  obtain ⟨φa, ha', hak0⟩ := s8g_c_kD hκ hCκ
  obtain ⟨φY, hYh, hYk⟩ := s8g_c_kD hμ hCμ
  obtain ⟨φX, hXh, hXk⟩ := s8g_c_kD hν hCν
  rw [← ha] at ha'
  replace hak0 : ∀ u ∈ upperHalf, ‖a u‖ ≤ Cκ := fun u hu => by rw [ha]; exact hak0 u hu
  rw [← hY] at hYh
  replace hYk : ∀ u ∈ upperHalf, ‖Y u‖ ≤ Cμ := fun u hu => by rw [hY]; exact hYk u hu
  rw [← hX] at hXh
  replace hXk : ∀ u ∈ upperHalf, ‖X u‖ ≤ Cν := fun u hu => by rw [hX]; exact hXk u hu
  obtain ⟨hEm, hEU, -⟩ := s8g_cayE hΓ.1
  have hρi := s8g_dr_rhoint hΓ
  set E := upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc with hEdef
  -- the three expressions of `L̈ = ∂_ē∂_e g(eκ)|₀`
  obtain ⟨⟨r1, hr1, hl1⟩, hT1i, hT1⟩ := s8g_dr_line1 hΓ hμ hν hκ hμΓ hνΓ hκΓ hX hY ha
  obtain ⟨hT2i, hT2, -, -, hsw⟩ := s8g_dr_line2 hΓ hμ hν hκ hμΓ hνΓ hκΓ hX hY ha
  obtain ⟨-, -, hT3i, hT3, -⟩ := s8g_dr_line2 hΓ hν hμ hκ hνΓ hμΓ hκΓ hY hX ha
  have e1 : dzbar (dz fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 = ∫ s in E,
      dzbar (dz fun e => conj (QfunU X (fun u => e * a u) s) * QfunU Y (fun u => e * a u) s *
        (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) 0 :=
    (s7g_f2_germ (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr1) hl1)).trans hT1
  have e2 : dzbar (dz fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 = ∫ s in E, conj (X s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0) := by
    rw [hT2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only []
    ring
  have e3 : dzbar (dz fun e => gGamma Γ μ ν (fun z => e * κ z)) 0 = ∫ s in E, Y s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, X t * kernelKbar (fun y => e * a y) t s ^ 2) 0) := by
    have hh : (fun e : ℂ => gGamma Γ μ ν (fun z => e * κ z)) = fun e => conj (gGamma Γ ν μ (fun z => e * κ z)) := by
      funext e
      rw [s8g_dr_herm Γ μ ν, Complex.conj_conj]
    rw [hh, s7g_f2_conjW, hT3, map_mul, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have I2 : IntegrableOn (fun s => conj (X s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0)) E := by
    refine (hT2i.const_mul (12 / π : ℂ)).congr (Eventually.of_forall fun s => ?_)
    simp only []
    ring
  have I3 : IntegrableOn (fun s => Y s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, X t * kernelKbar (fun y => e * a y) t s ^ 2) 0)) E := by
    refine ((Complex.conjCLE.toContinuousLinearMap.integrable_comp hT3i).const_mul (12 / π : ℂ)).congr
      (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_div₀, map_ofNat,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  -- integrability of `A` and `B`
  have hρc : ContinuousOn (fun s => (rhoU s : ℂ)) upperHalf := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    unfold rhoU
    exact (Complex.continuous_im.pow 2).continuousOn.inv₀ fun s hs => pow_ne_zero _ (ne_of_gt hs)
  have hXc := harmonicU_continuousOn hXh
  have hYc := harmonicU_continuousOn hYh
  have hac := harmonicU_continuousOn ha'
  have hCκ0 : 0 ≤ Cκ := (norm_nonneg _).trans (hCκ 0 h0D)
  have hGb : ∀ s ∈ upperHalf, ‖resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s‖ ≤ Cκ ^ 2 := fun s hs =>
    resolventOpU_norm_le (fun w hw => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hak0 w hw) 2) hs
  have hGc : ContinuousOn (resolventOpU fun u => (‖a u‖ ^ 2 : ℝ)) upperHalf :=
    resolventOpU_continuousOn_of_continuous_bounded
      (Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn hac).pow 2))
      (fun w hw => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hak0 w hw) 2)
  have hρ0 : ∀ s, 0 ≤ rhoU s := fun s => by unfold rhoU; positivity
  have iA : IntegrableOn (fun s => conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s) E := by
    refine Integrable.mono' (hρi.const_mul (Cν * Cμ * Cκ ^ 2)) ?_ ?_
    · exact (((((Complex.continuous_conj.comp_continuousOn hXc).mul hYc).mul
        (Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn hac).pow 2))).mul
        hρc).mono hEU).aestronglyMeasurable hEm
    · filter_upwards [ae_restrict_mem hEm] with s hs
      have h1 := hXk s (hEU hs)
      have h2 := hYk s (hEU hs)
      have h3 := hak0 s (hEU hs)
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hρ0 s)]
      have h4 : ‖a s‖ ^ 2 ≤ Cκ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hp1 : ‖X s‖ * ‖Y s‖ ≤ Cν * Cμ := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      have hp2 : ‖X s‖ * ‖Y s‖ * ‖a s‖ ^ 2 ≤ Cν * Cμ * Cκ ^ 2 :=
        mul_le_mul hp1 h4 (sq_nonneg _) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hp1)
      exact mul_le_mul_of_nonneg_right hp2 (hρ0 s)
  have iB : IntegrableOn (fun s => conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s)) E := by
    refine Integrable.mono' (hρi.const_mul (Cν * Cμ * Cκ ^ 2)) ?_ ?_
    · exact ((((Complex.continuous_conj.comp_continuousOn hXc).mul hYc).mul (hρc.mul hGc)).mono hEU).aestronglyMeasurable
        hEm
    · filter_upwards [ae_restrict_mem hEm] with s hs
      have h1 := hXk s (hEU hs)
      have h2 := hYk s (hEU hs)
      have h4 := hGb s (hEU hs)
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 s)]
      have hp1 : ‖X s‖ * ‖Y s‖ ≤ Cν * Cμ := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      have hp2 : rhoU s * ‖resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s‖ ≤ rhoU s * Cκ ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (hρ0 s)
      calc ‖X s‖ * ‖Y s‖ * (rhoU s * ‖resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s‖)
          ≤ Cν * Cμ * (rhoU s * Cκ ^ 2) :=
            mul_le_mul hp1 hp2 (mul_nonneg (hρ0 s) (norm_nonneg _)) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hp1)
        _ = Cν * Cμ * Cκ ^ 2 * rhoU s := by ring
  -- pointwise: `T₁ - T₂ - T₃ = -A - B + C`
  obtain ⟨T1, hT1d⟩ : ∃ T1 : ℂ → ℂ, T1 = fun s => dzbar (dz fun e => conj (QfunU X (fun u => e * a u) s) *
      QfunU Y (fun u => e * a u) s * (1 - ‖e‖ ^ 2 * ‖a s‖ ^ 2) * rhoVar a e s) 0 := ⟨_, rfl⟩
  obtain ⟨T2, hT2d⟩ : ∃ T2 : ℂ → ℂ, T2 = fun s => conj (X s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, Y t * kernelKbar (fun y => e * a y) t s ^ 2) 0) := ⟨_, rfl⟩
  obtain ⟨T3, hT3d⟩ : ∃ T3 : ℂ → ℂ, T3 = fun s => Y s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, X t * kernelKbar (fun y => e * a y) t s ^ 2) 0) := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun s => conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun s =>
      conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s) := ⟨_, rfl⟩
  obtain ⟨Cq, hCd⟩ : ∃ Cq : ℂ → ℂ, Cq = fun s => conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
      dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s := ⟨_, rfl⟩
  have i1 : IntegrableOn T1 E := by rw [hT1d]; exact hT1i
  have i2 : IntegrableOn T2 E := by rw [hT2d]; exact I2
  have i3 : IntegrableOn T3 E := by rw [hT3d]; exact I3
  have iA' : IntegrableOn A E := by rw [hAd]; exact iA
  have iB' : IntegrableOn B E := by rw [hBd]; exact iB
  have hpt : ∀ s ∈ E, T1 s - T2 s - T3 s = -A s - B s + Cq s := by
    intro s hs
    rw [hT1d, hT2d, hT3d, hAd, hBd, hCd]
    exact s7g_f2_pt ha' hXh hYh (hEU hs)
  have iC : IntegrableOn Cq E := by
    refine (((i1.sub i2).sub i3).add (iA'.add iB')).congr ?_
    filter_upwards [ae_restrict_mem hEm] with s hs
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt s hs]
    ring
  have hR : ∫ s in E, (T1 s - T2 s - T3 s) = ∫ s in E, (-A s - B s + Cq s) := setIntegral_congr_fun hEm hpt
  rw [integral_sub (f := fun s => T1 s - T2 s) (i1.sub i2) i3, integral_sub i1 i2,
    integral_add (f := fun s => -A s - B s) (iA'.neg.sub iB') iC, integral_sub (f := fun s => -A s) iA'.neg iB',
    integral_neg] at hR
  rw [← hT1d] at e1
  rw [← hT2d] at e2
  rw [← hT3d] at e3
  refine ⟨iA, iB, ?_, ?_⟩
  · rw [hCd] at iC
    exact iC
  · rw [hsw]
    rw [← e1, ← e2, ← e3] at hR
    simp only [hAd, hBd, hCd] at hR
    linear_combination -hR

/-- The Cayley weight `c = \bar{S'}/S'` (`S'(u) = 2i/(u+i)²`) is unimodular on `𝕌`. -/
theorem s8q_cw {u : ℂ} (hu : u ∈ upperHalf) :
    2 * I / (u + I) ^ 2 ≠ 0 ∧ conj (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) = 1 := by
  have hd := cayley_den_ne_zero hu
  have hw : 2 * I / (u + I) ^ 2 ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero 2 hd)
  have hcw : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hw
  refine ⟨hw, ?_⟩
  rw [map_div₀, Complex.conj_conj, div_mul_div_comm, mul_comm (2 * I / (u + I) ^ 2),
    div_self (mul_ne_zero hcw hw)]

/-- `(1 - |S u|²)² = 4 (Im u)² |S'(u)|²` (`S` = Cayley). -/
theorem s8q_cay_t {u : ℂ} (hu : u ∈ upperHalf) :
    (1 - ‖cayley u‖ ^ 2) ^ 2 = 4 * u.im ^ 2 * ‖2 * I / (u + I) ^ 2‖ ^ 2 := by
  have hpb := rhoU_cayley_pullback hu
  rw [(rhoU_hasDerivAt_cayley hu).deriv] at hpb
  have ht : 0 < 1 - ‖cayley u‖ ^ 2 := by
    have := mem_ball_zero_iff.mp (cayley_mem_unitDisc hu)
    nlinarith [norm_nonneg (cayley u)]
  have hy : 0 < u.im := hu
  have ht' := ht.ne'
  have hy' := hy.ne'
  unfold rho rhoU at hpb
  field_simp at hpb
  linarith

/-- Cayley transport of harmonic Beltrami differentials: `μ̃(u) = μ(S u) \bar{S'}/S'` is harmonic on `𝕌`. -/
theorem s8q_harmU {μ : ℂ → ℂ} (hμ : IsHarmonicD μ) :
    ∃ ψ, IsHarmonicU (fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) ψ := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨φ, hφ, -, hr⟩ := hμ
  have hid : ∀ u ∈ upperHalf, μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) =
      (u - conj u) ^ 2 / 2 * conj (-2 * φ (cayley u) * (2 * I / (u + I) ^ 2) ^ 2) := fun u hu => by
    obtain ⟨hw, -⟩ := s8q_cw hu
    have hcw : conj (2 * I / (u + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hw
    have hS := cayley_mem_unitDisc hu
    have hreal := s8q_cay_t hu
    have hC : (((1 - ‖cayley u‖ ^ 2) ^ 2 : ℝ) : ℂ) = ((4 * u.im ^ 2 : ℝ) : ℂ) *
        ((2 * I / (u + I) ^ 2) * conj (2 * I / (u + I) ^ 2)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hreal]
      push_cast
      ring
    rw [hr _ hS, Complex.sub_conj]
    push_cast at hC ⊢
    rw [hC]
    simp only [map_mul, map_neg, map_pow, map_ofNat]
    have hd := cayley_den_ne_zero hu
    field_simp
    ring_nf
    rw [Complex.I_sq]
    field_simp
  refine ⟨fun u => -2 * φ (cayley u) * (2 * I / (u + I) ^ 2) ^ 2, ?_, ⟨Cμ / 2, fun u hu => ?_⟩, hid⟩
  · intro u hu
    have hd := cayley_den_ne_zero hu
    have hc : DifferentiableAt ℂ cayley u := (rhoU_hasDerivAt_cayley hu).differentiableAt
    have hφc : DifferentiableAt ℂ φ (cayley u) :=
      hφ.differentiableAt (isOpen_ball.mem_nhds (cayley_mem_unitDisc hu))
    have hw : DifferentiableAt ℂ (fun u : ℂ => 2 * I / (u + I) ^ 2) u :=
      (differentiableAt_const _).div ((differentiableAt_id.add_const I).pow 2) (pow_ne_zero 2 hd)
    exact (((differentiableAt_const _).mul (hφc.comp u hc)).mul (hw.pow 2)).differentiableWithinAt
  · obtain ⟨hw, hcc⟩ := s8q_cw hu
    have hy : 0 < u.im := hu
    have e := congrArg norm (hid u hu)
    have hn1 : ‖conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hw)]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_conj, Complex.sub_conj, Complex.norm_real,
      Complex.norm_I, Complex.norm_two, hn1, Real.norm_eq_abs, mul_one, abs_two, abs_of_pos hy, norm_neg] at e
    have hb := hCμ _ (cayley_mem_unitDisc hu)
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Complex.norm_I, Complex.norm_two,
      Real.norm_eq_abs, mul_one, abs_of_pos hy, norm_neg]
    nlinarith [norm_nonneg (φ (cayley u)), norm_nonneg (2 * I / (u + I) ^ 2), norm_nonneg (μ (cayley u))]

/-- Change of variables `E = 𝕌 ∩ S⁻¹F → F` under the Cayley map, with the hyperbolic densities. -/
theorem s8q_E_cov (f : ℂ → ℂ) {F : Set ℂ} (hF : MeasurableSet F) (hFD : F ⊆ unitDisc) :
    ∫ s in upperHalf ∩ cayley ⁻¹' F, f (cayley s) * (rhoU s : ℂ) = ∫ z in F, f z * (rho z : ℂ) := by
  have hc : Measurable cayley := by unfold cayley; fun_prop
  rw [← setIntegral_indicator (hc hF)]
  have e1 : (fun s => (cayley ⁻¹' F).indicator (fun s => f (cayley s) * (rhoU s : ℂ)) s) =
      fun s => F.indicator f (cayley s) * (rhoU s : ℂ) := funext fun s => by
    by_cases h : cayley s ∈ F
    · rw [Set.indicator_of_mem (show s ∈ cayley ⁻¹' F from h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show s ∉ cayley ⁻¹' F from h), Set.indicator_of_notMem h, zero_mul]
  rw [e1, ← rhoU_integral_cayley (F.indicator f)]
  have e2 : (fun z => F.indicator f z * (rho z : ℂ)) = F.indicator fun z => f z * (rho z : ℂ) := funext fun z => by
    by_cases h : z ∈ F
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [e2, setIntegral_indicator hF, inter_eq_right.mpr hFD]

/-- Cayley transport of `q h = ∂̄(ρ⁻¹∂̄h)`: `q_𝕌(h ∘ S)(u) = q(h)(S u) \bar{S'}/S'`. -/
theorem s8q_qU {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) {u : ℂ} (hu : u ∈ upperHalf) :
    dzbar (fun y => (rhoU y : ℂ)⁻¹ * dzbar (h ∘ cayley) y) u =
      s7et_q h (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (rho w : ℂ)⁻¹) unitDisc :=
    wp_rho_inv_contDiff.contDiffOn.of_le le_top
  have hhd : ContDiffOn ℝ (⊤ : ℕ∞) (dzbar h) unitDisc := wp_contDiffOn_dzbar hh isOpen_ball (by simp)
  have hV : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (rho z : ℂ)⁻¹ * dzbar h z) unitDisc := ha.mul hhd
  have diff (f : ℂ → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f unitDisc) (w : ℂ) (hw : w ∈ unitDisc) :
      DifferentiableAt ℝ f w :=
    (hf.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hw)
  have key : (fun y => (rhoU y : ℂ)⁻¹ * dzbar (h ∘ cayley) y) =ᶠ[𝓝 u]
      fun y => ((fun z => (rho z : ℂ)⁻¹ * dzbar h z) ∘ cayley) y * (2 * I / (y + I) ^ 2)⁻¹ := by
    filter_upwards [isOpen_upperHalf.mem_nhds hu] with y hy
    obtain ⟨hw, -⟩ := s8q_cw hy
    have hcw : conj (2 * I / (y + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hw
    have hS := cayley_mem_unitDisc hy
    have hd := (rhoU_hasDerivAt_cayley hy).deriv
    rw [rhoU_dzbar_comp_cayley hy (diff h hh _ hS), hd]
    have hpb := rhoU_cayley_pullback hy
    rw [hd] at hpb
    have hpb' : (rhoU y : ℂ) = (rho (cayley y) : ℂ) * ((2 * I / (y + I) ^ 2) * conj (2 * I / (y + I) ^ 2)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hpb]
      push_cast
      ring
    have hρ := s8q_rho_ne hS
    simp only [Function.comp_apply]
    rw [hpb']
    field_simp
  rw [s8q_dzbar_congr key]
  have hd := cayley_den_ne_zero hu
  have hS := cayley_mem_unitDisc hu
  obtain ⟨hw, -⟩ := s8q_cw hu
  have hwd : DifferentiableAt ℂ (fun y : ℂ => (2 * I / (y + I) ^ 2)⁻¹) u :=
    ((differentiableAt_const _).div ((differentiableAt_id.add_const I).pow 2) (pow_ne_zero 2 hd)).inv hw
  have hVc : DifferentiableAt ℝ ((fun z => (rho z : ℂ)⁻¹ * dzbar h z) ∘ cayley) u :=
    (diff _ hV _ hS).comp u ((rhoU_hasDerivAt_cayley hu).differentiableAt.restrictScalars ℝ)
  rw [dzbar_mul hVc (hwd.restrictScalars ℝ), (cauchyRiemann_iff.mp hwd).2, mul_zero, zero_add,
    rhoU_dzbar_comp_cayley hu (diff _ hV _ hS), (rhoU_hasDerivAt_cayley hu).deriv]
  show (2 * I / (u + I) ^ 2)⁻¹ * (s7et_q h (cayley u) * conj (2 * I / (u + I) ^ 2)) = _
  ring

/-- `G_𝕌(f ∘ S) = G_Γ f ∘ S` on `𝕌` for bounded smooth `Γ`-invariant `f` (any representative `g = f ∘ S` on `𝕌`). -/
theorem s8q_GU {Γ : Subgroup SL2C} (hΓ : IsFuchsian Γ) {f g : ℂ → ℂ} (hf : f ∈ BCinf unitDisc)
    (hfΓ : ∀ γ ∈ Γ, ∀ z ∈ unitDisc, f (mob γ z) = f z) (hg : ∀ u ∈ upperHalf, g u = f (cayley u))
    {y : ℂ} (hy : y ∈ upperHalf) :
    resolventOpU g y = resolventGammaD Γ f (cayley y) := by
  rw [s8q_res_eq hΓ hf hfΓ (cayley_mem_unitDisc hy), resolventOpU_cayley f hy]
  show ∫ w in upperHalf, (resolventKernelU y w : ℂ) * g w * rhoU w =
    ∫ w in upperHalf, (resolventKernelU y w : ℂ) * (f ∘ cayley) w * rhoU w
  exact setIntegral_congr_fun isOpen_upperHalf.measurableSet fun w hw => by rw [hg w hw]; rfl

/-- STUB DG_EVAL. Evaluation of the representation of `DG_REP` (Cayley change of variables, `p71_prop_7_1U`,
unfolding `G_𝔻 = G_Γ` and `s8g_qdot`): `∫_E A = (μκ̄, νκ̄)_Γ`, `∫_E B = (μν̄, G_Γ|κ|²)_Γ`,
`∫_E C = 4∬_F q(G_Γ(μκ̄)) \overline{q(G_Γ(νκ̄))} ρ = (μκ̄, νκ̄)_Γ - (μκ̄, G_Γ(νκ̄))_Γ`. -/
theorem s8g_dg_eval {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) {X Y a : ℂ → ℂ}
    (hX : X = fun u => ν (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hY : Y = fun u => μ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (ha : a = fun u => κ (cayley u) * (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hA : IntegrableOn (fun s => conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s)
      (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc))
    (hB : IntegrableOn (fun s => conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s))
      (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc))
    (hC : IntegrableOn (fun s => conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
        dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s)
      (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc)) :
    (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s) +
        (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
          conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s)) -
        (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
          conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
            dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s) =
      innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
        innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  -- the frozen integrability hypotheses `hA`, `hB`, `hC` are not needed: each integral is evaluated separately
  -- by an exact change of variables (the statement stays true without them)
  have _hA := hA
  have _hB := hB
  have _hC := hC
  have hF := s8w_fundD hΓ.1
  have hFm := hF.1
  have hFD := hF.2.1
  have hcm : Measurable cayley := by unfold cayley; fun_prop
  have hE : MeasurableSet (upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc) :=
    isOpen_upperHalf.measurableSet.inter (hcm hFm)
  have hXs : ∀ s, X s = ν (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2)) := fun s => by rw [hX]
  have hYs : ∀ s, Y s = μ (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2)) := fun s => by rw [hY]
  have has : ∀ s, a s = κ (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2)) := fun s => by rw [ha]
  have hna : ∀ s ∈ upperHalf, ‖a s‖ = ‖κ (cayley s)‖ := fun s hs => by
    obtain ⟨hw, -⟩ := s8q_cw hs
    rw [has, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hw), mul_one]
  -- data
  obtain ⟨hf, hfΓ⟩ := s8q_fk_data hΓ.1 hμ hκ hμΓ hκΓ
  obtain ⟨hg, hgΓ⟩ := s8q_fk_data hΓ.1 hν hκ hνΓ hκΓ
  obtain ⟨hk2, hk2Γ⟩ := s8q_fk_data hΓ.1 hκ hκ hκΓ hκΓ
  obtain ⟨ψY, hYU⟩ := s8q_harmU hμ
  obtain ⟨ψX, hXU⟩ := s8q_harmU hν
  obtain ⟨ψa, haU⟩ := s8q_harmU hκ
  rw [← hY] at hYU
  rw [← hX] at hXU
  rw [← ha] at haU
  obtain ⟨hh, -, -, -⟩ := s8q_res_data hΓ.1 hf hfΓ
  obtain ⟨hk, -, -, -⟩ := s8q_res_data hΓ.1 hg hgΓ
  have hK2 : (fun z => ((‖κ z‖ ^ 2 : ℝ) : ℂ)) = fun u => κ u * conj (κ u) := funext fun z => by
    rw [Complex.mul_conj']; norm_cast
  -- `∂_ε̄ Q_Z(ε a)|₀ = -2 q(G_Γ(ζ κ̄))(S s) c(s)` for `Z = ζ̃`
  have hDQ : ∀ {Z ψZ : ℂ → ℂ} {ζ : ℂ → ℂ}, IsHarmonicU Z ψZ →
      (∀ s, Z s = ζ (cayley s) * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) →
      (fun u => ζ u * conj (κ u)) ∈ BCinf unitDisc →
      (∀ g ∈ Γ, ∀ z ∈ unitDisc, ζ (mob g z) * conj (κ (mob g z)) = ζ z * conj (κ z)) →
      ContDiffOn ℝ (⊤ : ℕ∞) (resolventGammaD Γ fun u => ζ u * conj (κ u)) unitDisc →
      ∀ s ∈ upperHalf, dzbar (fun e => QfunU Z (fun u => e * a u) s) 0 =
        -2 * (s7et_q (resolventGammaD Γ fun u => ζ u * conj (κ u)) (cayley s) *
          (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) := by
    intro Z ψZ ζ hZU hZs hζ hζΓ hGs s hs
    rw [(p71_prop_7_1U hZU haU hs).2.2, ← s8q_qU hGs hs]
    congr 1
    have hGU : ∀ y ∈ upperHalf, resolventOpU (fun u => Z u * conj (a u)) y =
        ((resolventGammaD Γ fun u => ζ u * conj (κ u)) ∘ cayley) y := fun y hy =>
      s8q_GU hΓ.1 hζ hζΓ (fun u hu => by
        obtain ⟨-, hcc⟩ := s8q_cw hu
        rw [hZs, has, map_mul]
        linear_combination ζ (cayley u) * conj (κ (cayley u)) * hcc) hy
    refine s8q_dzbar_congr ?_
    filter_upwards [isOpen_upperHalf.mem_nhds hs] with y hy
    congr 1
    refine s8q_dzbar_congr ?_
    filter_upwards [isOpen_upperHalf.mem_nhds hy] with x hx
    exact hGU x hx
  -- the three integrals
  have hIA : (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc, conj (X s) * Y s * (‖a s‖ ^ 2 : ℝ) * rhoU s) =
      innerGamma Γ (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) := by
    rw [setIntegral_congr_fun hE (g := fun s => (fun z => conj (ν z) * μ z * ((‖κ z‖ ^ 2 : ℝ) : ℂ)) (cayley s) *
      (rhoU s : ℂ)) fun s hs => ?_, s8q_E_cov (fun z => conj (ν z) * μ z * ((‖κ z‖ ^ 2 : ℝ) : ℂ)) hFm hFD]
    · show _ = ∫ z in fundDomainOn Γ unitDisc, μ z * conj (κ z) * conj (ν z * conj (κ z)) * rho z
      refine setIntegral_congr_fun hFm fun z _ => ?_
      beta_reduce
      simp only [map_mul, Complex.conj_conj]
      push_cast
      rw [← Complex.conj_mul' (κ z)]
      ring
    · obtain ⟨-, hcc⟩ := s8q_cw hs.1
      beta_reduce
      rw [hXs, hYs, hna s hs.1, map_mul]
      linear_combination conj (ν (cayley s)) * μ (cayley s) * ((‖κ (cayley s)‖ ^ 2 : ℝ) : ℂ) * (rhoU s : ℂ) * hcc
  have hIB : (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
      conj (X s) * Y s * (rhoU s * resolventOpU (fun u => (‖a u‖ ^ 2 : ℝ)) s)) =
      innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ)) := by
    rw [setIntegral_congr_fun hE (g := fun s => (fun z => conj (ν z) * μ z *
      resolventGammaD Γ (fun u => κ u * conj (κ u)) z) (cayley s) * (rhoU s : ℂ)) fun s hs => ?_, s8q_E_cov (fun z => conj (ν z) * μ z *
      resolventGammaD Γ (fun u => κ u * conj (κ u)) z) hFm hFD]
    · rw [hK2]
      show _ = ∫ z in fundDomainOn Γ unitDisc, μ z * conj (ν z) *
        conj (resolventGammaD Γ (fun u => κ u * conj (κ u)) z) * rho z
      refine setIntegral_congr_fun hFm fun z _ => ?_
      have e : (fun u => conj (κ u * conj (κ u))) = fun u => κ u * conj (κ u) := funext fun u => by
        simp only [map_mul, Complex.conj_conj]; ring
      have hc := s8q_conj_res Γ (fun u => κ u * conj (κ u)) z
      rw [e] at hc
      beta_reduce
      rw [hc]
      ring
    · obtain ⟨-, hcc⟩ := s8q_cw hs.1
      have hG := s8q_GU hΓ.1 hk2 hk2Γ (g := fun u => ((‖a u‖ ^ 2 : ℝ) : ℂ)) (fun u hu => by
        rw [hna u hu, Complex.mul_conj']; norm_cast) hs.1
      beta_reduce
      rw [hG, hXs, hYs, map_mul]
      linear_combination conj (ν (cayley s)) * μ (cayley s) *
        resolventGammaD Γ (fun u => κ u * conj (κ u)) (cayley s) * (rhoU s : ℂ) * hcc
  have hIC : (∫ s in upperHalf ∩ cayley ⁻¹' fundDomainOn Γ unitDisc,
      conj (dzbar (fun e => QfunU X (fun u => e * a u) s) 0) *
        dzbar (fun e => QfunU Y (fun u => e * a u) s) 0 * rhoU s) =
      innerGamma Γ (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) -
        innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) := by
    rw [← s8g_qdot hΓ hμ hν hκ hμΓ hνΓ hκΓ, ← integral_const_mul]
    rw [setIntegral_congr_fun hE (g := fun s => (fun z => 4 * (s7et_q (resolventGammaD Γ fun u => μ u * conj (κ u)) z *
      conj (s7et_q (resolventGammaD Γ fun u => ν u * conj (κ u)) z))) (cayley s) *
        (rhoU s : ℂ)) fun s hs => ?_, s8q_E_cov (fun z => 4 * (s7et_q (resolventGammaD Γ fun u => μ u * conj (κ u)) z *
      conj (s7et_q (resolventGammaD Γ fun u => ν u * conj (κ u)) z))) hFm hFD]
    · refine setIntegral_congr_fun hFm fun z hz => ?_
      beta_reduce
      ring
    · obtain ⟨-, hcc⟩ := s8q_cw hs.1
      rw [hDQ hXU hXs hg hgΓ hk s hs.1, hDQ hYU hYs hf hfΓ hh s hs.1]
      beta_reduce
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination (4 * s7et_q (resolventGammaD Γ fun u => μ u * conj (κ u)) (cayley s) *
        conj (s7et_q (resolventGammaD Γ fun u => ν u * conj (κ u)) (cayley s)) * (rhoU s : ℂ)) * hcc
  rw [hIA, hIB, hIC]
  ring

/-- STUB DIAG. The second variation (Γ-version of `thm_7_7`). -/
theorem s8g_diag {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) :
    dz (dzbar fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 =
      innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
        innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  obtain ⟨hA, hB, hC, h⟩ := s8g_dg_rep hΓ hμ hν hκ hμΓ hνΓ hκΓ rfl rfl rfl
  rw [h]
  exact s8g_dg_eval hΓ hμ hν hκ hμΓ hνΓ hκΓ rfl rfl rfl hA hB hC

/-- Bounded continuous functions on `𝔻` are closed under `A · B̄`. -/
theorem s8s_P_mulc {A B : ℂ → ℂ} (hA : ContinuousOn A unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z‖ ≤ C)
    (hB : ContinuousOn B unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B z‖ ≤ C) :
    ContinuousOn (fun z => A z * conj (B z)) unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z * conj (B z)‖ ≤ C := by
  obtain ⟨hAc, CA, hCA⟩ := hA
  obtain ⟨hBc, CB, hCB⟩ := hB
  refine ⟨hAc.mul (Complex.continuous_conj.comp_continuousOn hBc), CA * CB, fun z hz => ?_⟩
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hCA z hz) (hCB z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCA z hz))

/-- Bounded continuous functions on `𝔻` are closed under `Ā · B`. -/
theorem s8s_P_cmul {A B : ℂ → ℂ} (hA : ContinuousOn A unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z‖ ≤ C)
    (hB : ContinuousOn B unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B z‖ ≤ C) :
    ContinuousOn (fun z => conj (A z) * B z) unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖conj (A z) * B z‖ ≤ C := by
  obtain ⟨hAc, CA, hCA⟩ := hA
  obtain ⟨hBc, CB, hCB⟩ := hB
  refine ⟨(Complex.continuous_conj.comp_continuousOn hAc).mul hBc, CA * CB, fun z hz => ?_⟩
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hCA z hz) (hCB z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCA z hz))

/-- Bounded continuous functions on `𝔻` are closed under `B₁ + b B₂`. -/
theorem s8s_P_lin {B₁ B₂ : ℂ → ℂ} (h₁ : ContinuousOn B₁ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B₁ z‖ ≤ C)
    (h₂ : ContinuousOn B₂ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B₂ z‖ ≤ C) (b : ℂ) :
    ContinuousOn (fun z => B₁ z + b * B₂ z) unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B₁ z + b * B₂ z‖ ≤ C := by
  obtain ⟨h₁c, C₁, hC₁⟩ := h₁
  obtain ⟨h₂c, C₂, hC₂⟩ := h₂
  refine ⟨h₁c.add (continuousOn_const.mul h₂c), C₁ + ‖b‖ * C₂, fun z hz => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add (hC₁ z hz) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC₂ z hz) (norm_nonneg b)

/-- For bounded continuous `B` and a.e. `z ∈ F`, the integrand `u ↦ G_Γ(z, u) B(u) ρ(u)` of `G_Γ B (z)` is
integrable on `F` (Fubini from `s8q_int`, dividing by `ρ(z) > 0`). -/
theorem s8s_res_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {B : ℂ → ℂ}
    (hB : ContinuousOn B unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B z‖ ≤ C) :
    ∀ᵐ z ∂(volume.restrict (fundDomainOn Γ unitDisc)),
      Integrable (fun u => (resolventKernelGamma Γ z u : ℂ) * B u * (rho u : ℂ))
        (volume.restrict (fundDomainOn Γ unitDisc)) := by
  obtain ⟨hBc, CB, hCB⟩ := hB
  have hF := s8w_fundD hΓ.1
  have hint := s8q_int hΓ (A := fun _ => (1 : ℂ)) continuousOn_const hBc (CA := 1)
    (fun z _ => by rw [norm_one]) hCB
  filter_upwards [hint.prod_right_ae, ae_restrict_mem hF.1] with z hz hzF
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hF.2.1 hzF)
  have hpos : 0 < rho z := by
    have h2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    unfold rho
    positivity
  have hρ : (rho z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have key : ∀ X : ℂ, (rho z : ℂ)⁻¹ * (X * rho z) = X := fun X => by
    rw [mul_comm, mul_assoc, mul_inv_cancel₀ hρ, mul_one]
  refine (hz.const_mul ((rho z : ℂ)⁻¹)).congr (Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [key, one_mul]

/-- For bounded continuous `A, B`, the integrand `A · conj(G_Γ B) · ρ` of `(A, G_Γ B)_Γ` is integrable on `F`
(Fubini from `s8q_int`). -/
theorem s8s_inner_int {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {A B : ℂ → ℂ}
    (hA : ContinuousOn A unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z‖ ≤ C)
    (hB : ContinuousOn B unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B z‖ ≤ C) :
    Integrable (fun z => A z * conj (resolventGammaD Γ B z) * (rho z : ℂ))
      (volume.restrict (fundDomainOn Γ unitDisc)) := by
  obtain ⟨hAc, CA, hCA⟩ := hA
  obtain ⟨hBc, CB, hCB⟩ := hB
  have hcB : ContinuousOn (fun z => conj (B z)) unitDisc := Complex.continuous_conj.comp_continuousOn hBc
  have hcBb : ∀ z ∈ unitDisc, ‖conj (B z)‖ ≤ CB := fun z hz => by rw [Complex.norm_conj]; exact hCB z hz
  have hint := s8q_int hΓ hAc hcB hCA hcBb
  refine hint.integral_prod_left.congr (Eventually.of_forall fun z => ?_)
  show (∫ u in fundDomainOn Γ unitDisc,
      A z * (resolventKernelGamma Γ z u : ℂ) * conj (B u) * (rho u : ℂ) * (rho z : ℂ)) =
    A z * conj (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * B u * rho u) * rho z
  rw [← integral_conj, ← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  beta_reduce
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Conjugate-linearity of `(A, G_Γ ·)_Γ` in the second slot, for bounded continuous data. -/
theorem s8s_right {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {A B₁ B₂ : ℂ → ℂ}
    (hA : ContinuousOn A unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z‖ ≤ C)
    (h₁ : ContinuousOn B₁ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B₁ z‖ ≤ C)
    (h₂ : ContinuousOn B₂ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B₂ z‖ ≤ C) (b : ℂ) :
    innerGamma Γ A (resolventGammaD Γ fun z => B₁ z + b * B₂ z) =
      innerGamma Γ A (resolventGammaD Γ B₁) + conj b * innerGamma Γ A (resolventGammaD Γ B₂) := by
  have i₁ := s8s_inner_int hΓ hA h₁
  have i₂ := (s8s_inner_int hΓ hA h₂).const_mul (conj b)
  show (∫ z in fundDomainOn Γ unitDisc,
      A z * conj (resolventGammaD Γ (fun z => B₁ z + b * B₂ z) z) * (rho z : ℂ)) =
    (∫ z in fundDomainOn Γ unitDisc, A z * conj (resolventGammaD Γ B₁ z) * (rho z : ℂ)) +
      conj b * ∫ z in fundDomainOn Γ unitDisc, A z * conj (resolventGammaD Γ B₂ z) * (rho z : ℂ)
  rw [← integral_const_mul, ← integral_add i₁ i₂]
  refine integral_congr_ae ?_
  filter_upwards [s8s_res_int hΓ h₁, s8s_res_int hΓ h₂] with z hz₁ hz₂
  have e : resolventGammaD Γ (fun z => B₁ z + b * B₂ z) z =
      resolventGammaD Γ B₁ z + b * resolventGammaD Γ B₂ z := by
    show (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * (B₁ u + b * B₂ u) * (rho u : ℂ)) =
      (∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * B₁ u * (rho u : ℂ)) +
        b * ∫ u in fundDomainOn Γ unitDisc, (resolventKernelGamma Γ z u : ℂ) * B₂ u * (rho u : ℂ)
    rw [← integral_const_mul, ← integral_add hz₁ (hz₂.const_mul b)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    beta_reduce
    ring
  beta_reduce
  rw [e, map_add, map_mul]
  ring

/-- Linearity of `(·, G_Γ B)_Γ` in the first slot, for bounded continuous data. -/
theorem s8s_left {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {A₁ A₂ B : ℂ → ℂ}
    (h₁ : ContinuousOn A₁ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A₁ z‖ ≤ C)
    (h₂ : ContinuousOn A₂ unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A₂ z‖ ≤ C)
    (hB : ContinuousOn B unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖B z‖ ≤ C) (a : ℂ) :
    innerGamma Γ (fun z => A₁ z + a * A₂ z) (resolventGammaD Γ B) =
      innerGamma Γ A₁ (resolventGammaD Γ B) + a * innerGamma Γ A₂ (resolventGammaD Γ B) := by
  have i₁ := s8s_inner_int hΓ h₁ hB
  have i₂ := (s8s_inner_int hΓ h₂ hB).const_mul a
  show (∫ z in fundDomainOn Γ unitDisc, (A₁ z + a * A₂ z) * conj (resolventGammaD Γ B z) * (rho z : ℂ)) =
    (∫ z in fundDomainOn Γ unitDisc, A₁ z * conj (resolventGammaD Γ B z) * (rho z : ℂ)) +
      a * ∫ z in fundDomainOn Γ unitDisc, A₂ z * conj (resolventGammaD Γ B z) * (rho z : ℂ)
  rw [← integral_const_mul, ← integral_add i₁ i₂]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  beta_reduce
  ring

/-- STUB SES. Sesquilinear expansion of the right-hand side of DIAG along `κ + c l`. -/
theorem s8g_ses {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ l : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hl : IsHarmonicD l) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) (hlΓ : IsGammaInvD Γ l) :
    ∃ B' : ℂ, ∀ c : ℂ,
      innerGamma Γ (fun z => μ z * conj (κ z + c * l z)) (resolventGammaD Γ fun z => ν z * conj (κ z + c * l z)) +
        innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z + c * l z‖ ^ 2 : ℝ)) =
      (innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
          innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ))) +
        conj c * (innerGamma Γ (fun z => μ z * conj (l z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
          innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => conj (κ z) * l z)) +
        c * B' +
        c * conj c * (innerGamma Γ (fun z => μ z * conj (l z)) (resolventGammaD Γ fun z => ν z * conj (l z)) +
          innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖l z‖ ^ 2 : ℝ))) := by
  -- the `Γ`-invariance hypotheses are not needed: the expansion holds for bounded continuous data on `𝔻`
  have hP : ∀ {A : ℂ → ℂ}, IsHarmonicD A → ContinuousOn A unitDisc ∧ ∃ C, ∀ z ∈ unitDisc, ‖A z‖ ≤ C :=
    fun hA => ⟨harmonicD_continuousOn hA, harmonicD_bound hA⟩
  have Pμ := hP hμ
  have Pν := hP hν
  have Pκ := hP hκ
  have Pl := hP hl
  refine ⟨innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (l z)) +
    innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => κ z * conj (l z)), fun c => ?_⟩
  have hn : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e1 : (fun z => μ z * conj (κ z + c * l z)) = fun z => μ z * conj (κ z) + conj c * (μ z * conj (l z)) := by
    funext z
    simp only [map_add, map_mul]
    ring
  have e2 : (fun z => ν z * conj (κ z + c * l z)) = fun z => ν z * conj (κ z) + conj c * (ν z * conj (l z)) := by
    funext z
    simp only [map_add, map_mul]
    ring
  have e3 : (fun z => ((‖κ z + c * l z‖ ^ 2 : ℝ) : ℂ)) = fun z =>
      (κ z * conj (κ z) + conj c * (κ z * conj (l z))) + c * (conj (κ z) * l z + conj c * (l z * conj (l z))) := by
    funext z
    rw [hn]
    simp only [map_add, map_mul]
    ring
  have e4 : (fun z => ((‖κ z‖ ^ 2 : ℝ) : ℂ)) = fun z => κ z * conj (κ z) := funext fun z => hn _
  have e5 : (fun z => ((‖l z‖ ^ 2 : ℝ) : ℂ)) = fun z => l z * conj (l z) := funext fun z => hn _
  rw [e1, e2, e3, e4, e5]
  have Pμκ := s8s_P_mulc Pμ Pκ
  have Pμl := s8s_P_mulc Pμ Pl
  have Pμν := s8s_P_mulc Pμ Pν
  have Pνκ := s8s_P_mulc Pν Pκ
  have Pνl := s8s_P_mulc Pν Pl
  have Pκκ := s8s_P_mulc Pκ Pκ
  have Pκl := s8s_P_mulc Pκ Pl
  have Pll := s8s_P_mulc Pl Pl
  have Pcκl := s8s_P_cmul Pκ Pl
  rw [s8s_left hΓ Pμκ Pμl (s8s_P_lin Pνκ Pνl (conj c)) (conj c), s8s_right hΓ Pμκ Pνκ Pνl (conj c),
    s8s_right hΓ Pμl Pνκ Pνl (conj c),
    s8s_right hΓ Pμν (s8s_P_lin Pκκ Pκl (conj c)) (s8s_P_lin Pcκl Pll (conj c)) c,
    s8s_right hΓ Pμν Pκκ Pκl (conj c), s8s_right hΓ Pμν Pcκl Pll (conj c)]
  simp only [Complex.conj_conj]
  ring

/-- STUB SYM. Symmetry of `G_Γ` on the pairing: `(μ ν̄, G_Γ(κ̄ l))_Γ = (κ l̄, G_Γ(μ̄ ν))_Γ`. -/
theorem s8g_sym {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ l : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hl : IsHarmonicD l) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) (hlΓ : IsGammaInvD Γ l) :
    innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => conj (κ z) * l z) =
      innerGamma Γ (fun z => κ z * conj (l z)) (resolventGammaD Γ fun z => conj (μ z) * ν z) := by
  obtain ⟨Cμ, hCμ⟩ := harmonicD_bound hμ
  obtain ⟨Cν, hCν⟩ := harmonicD_bound hν
  obtain ⟨Cκ, hCκ⟩ := harmonicD_bound hκ
  obtain ⟨Cl, hCl⟩ := harmonicD_bound hl
  have hA : ContinuousOn (fun z => μ z * conj (ν z)) unitDisc :=
    (harmonicD_continuousOn hμ).mul (Complex.continuous_conj.comp_continuousOn (harmonicD_continuousOn hν))
  have hB : ContinuousOn (fun z => conj (κ z) * l z) unitDisc :=
    (Complex.continuous_conj.comp_continuousOn (harmonicD_continuousOn hκ)).mul (harmonicD_continuousOn hl)
  have hAb : ∀ z ∈ unitDisc, ‖μ z * conj (ν z)‖ ≤ Cμ * Cν := fun z hz => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCμ z hz) (hCν z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCμ z hz))
  have hBb : ∀ z ∈ unitDisc, ‖conj (κ z) * l z‖ ≤ Cκ * Cl := fun z hz => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hCκ z hz) (hCl z hz) (norm_nonneg _) ((norm_nonneg _).trans (hCκ z hz))
  have h := s8q_sym_core hΓ hA hB hAb hBb
  have e1 : (fun z => conj (conj (κ z) * l z)) = fun z => κ z * conj (l z) := by
    funext z
    simp only [map_mul, Complex.conj_conj]
  have e2 : (fun z => conj (μ z * conj (ν z))) = fun z => conj (μ z) * ν z := by
    funext z
    simp only [map_mul, Complex.conj_conj]
  rw [e1, e2] at h
  exact h

/-- `C²` regularity of `(p₁, p₂) ↦ g_{μν̄}(p₁ κ + p₂ l)` near `0`, from CORE by Hartogs-lite. -/
theorem s8g_C2 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ l : ℂ → ℂ} (hμ : IsHarmonicD μ)
    (hν : IsHarmonicD ν) (hκ : IsHarmonicD κ) (hl : IsHarmonicD l) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν)
    (hκΓ : IsGammaInvD Γ κ) (hlΓ : IsGammaInvD Γ l) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 2 (fun p : ℂ × ℂ => gGamma Γ μ ν (fun z => p.1 * κ z + p.2 * l z)) (ball 0 r) := by
  obtain ⟨R0, hR0, Φ, hhol, ⟨M, hM⟩, r, hr, hrR, hEq⟩ := s8g_core hΓ hμ hν hκ hl hμΓ hνΓ hκΓ hlΓ
  have hU : IsOpen (ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0) := isOpen_ball
  have hΦ : ContDiffOn ℂ 2 Φ (ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0) :=
    s7g_c79_hartogs hU 2 Φ (fun p hp => (hhol p hp).1) (fun p hp => (hhol p hp).2.1)
      (fun p hp => (hhol p hp).2.2.1) (fun p hp => (hhol p hp).2.2.2)
      (fun p hp => by
        obtain ⟨ρ, hρ, hs⟩ := Metric.isOpen_iff.1 hU p hp
        exact ⟨ρ, hρ, M, fun q hq => hM q (hs hq)⟩)
  have hmap : ContDiff ℝ 2 (fun p : ℂ × ℂ => (((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ))) :=
    ((Complex.conjCLE.contDiff.comp contDiff_fst).prodMk (Complex.conjCLE.contDiff.comp contDiff_snd)).prodMk
      contDiff_id
  refine ⟨r, hr, ((hΦ.restrict_scalars ℝ).comp hmap.contDiffOn fun p hp => ?_).congr fun p hp => hEq p ?_⟩
  · have h1 : ‖p‖ < r := mem_ball_zero_iff.1 hp
    rw [mem_ball_zero_iff]
    simp only [Prod.norm_def, Complex.norm_conj] at h1 ⊢
    rw [max_self]
    exact lt_of_lt_of_le h1 hrR
  · exact mem_ball_zero_iff.1 hp

/-- **Corollary 7.9 for `T(Γ)`**: `R_{μ ν̄ κ l̄} = -(κ l̄, G_Γ(μ̄ ν))_Γ - (l̄ μ, G_Γ(κ̄ ν))_Γ`, by polarisation. -/
theorem s8g_cor_7_9 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {κ l μ ν : ℂ → ℂ} (hκ : IsHarmonicD κ)
    (hl : IsHarmonicD l) (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hκΓ : IsGammaInvD Γ κ) (hlΓ : IsGammaInvD Γ l)
    (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    riemannRGamma Γ μ ν κ l =
      -innerGamma Γ (fun z => κ z * conj (l z)) (resolventGammaD Γ fun z => conj (μ z) * ν z) -
        innerGamma Γ (fun z => conj (l z) * μ z) (resolventGammaD Γ fun z => conj (κ z) * ν z) := by
  obtain ⟨r, hr, hC⟩ := s8g_C2 hΓ hμ hν hκ hl hμΓ hνΓ hκΓ hlΓ
  have hpol := s7g_c79_pol hr hC
  obtain ⟨B', hB'⟩ := s8g_ses hΓ hμ hν hκ hl hμΓ hνΓ hκΓ hlΓ
  have hS : ∀ c : ℂ, dz (dzbar fun ε => gGamma Γ μ ν (fun z => (ε, c * ε).1 * κ z + (ε, c * ε).2 * l z)) 0 =
      innerGamma Γ (fun z => μ z * conj (κ z + c * l z)) (resolventGammaD Γ fun z => ν z * conj (κ z + c * l z)) +
        innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z + c * l z‖ ^ 2 : ℝ)) := by
    intro c
    have e : (fun ε : ℂ => gGamma Γ μ ν (fun z => (ε, c * ε).1 * κ z + (ε, c * ε).2 * l z)) =
        fun ε => gGamma Γ μ ν (fun z => ε * (κ z + c * l z)) := funext fun ε => by
      congr 1
      funext z
      dsimp only
      ring
    rw [e]
    exact s8g_diag hΓ hμ hν (s8g_harm_lin hκ hl c) hμΓ hνΓ (s8g_inv_lin hκΓ hlΓ c)
  have hrie : riemannRGamma Γ μ ν κ l =
      -dz (fun e₁ => dzbar (fun e₂ => gGamma Γ μ ν (fun z => (e₁, e₂).1 * κ z + (e₁, e₂).2 * l z)) 0) 0 := rfl
  rw [hS, hS, hS, hS, hB', hB', hB', hB'] at hpol
  simp only [map_one, Complex.conj_I, map_neg] at hpol
  rw [hrie, ← s8g_sym hΓ hμ hν hκ hl hμΓ hνΓ hκΓ hlΓ]
  have e2 : (fun z => conj (l z) * μ z) = fun z => μ z * conj (l z) := funext fun z => mul_comm _ _
  have e3 : (fun z => conj (κ z) * ν z) = fun z => ν z * conj (κ z) := funext fun z => mul_comm _ _
  rw [e2, e3]
  linear_combination (-1 / 4 : ℂ) * hpol +
    ((innerGamma Γ (fun z => μ z * conj (l z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
      innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => conj (κ z) * l z)) / 2 - B' / 2) *
      Complex.I_sq

/-- `thm_8_5`, assembled from C2, FV and DIAG. -/
theorem s8g_thm_8_5 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) (hκΓ : IsGammaInvD Γ κ) :
    DifferentiableAt ℝ (fun ε : ℂ => gGamma Γ μ ν (fun z => ε * κ z)) 0 ∧
      dz (fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 = 0 ∧
      dz (dzbar fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 =
        innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
          innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  obtain ⟨r, hr, hC⟩ := s8g_C2 hΓ hμ hν hκ hκ hμΓ hνΓ hκΓ hκΓ
  have hm : MapsTo (fun ε : ℂ => (ε, (0 : ℂ))) (ball 0 r) (ball 0 r) := fun ε he => by
    rw [mem_ball_zero_iff] at he ⊢
    simpa [Prod.norm_def] using he
  have hline : ContDiffOn ℝ 2 (fun ε : ℂ => gGamma Γ μ ν (fun z => ε * κ z)) (ball 0 r) := by
    refine (hC.comp (contDiff_id.prodMk contDiff_const).contDiffOn hm).congr fun ε _ => ?_
    show gGamma Γ μ ν (fun z => ε * κ z) = gGamma Γ μ ν (fun z => ε * κ z + 0 * κ z)
    simp only [zero_mul, add_zero]
  exact ⟨(hline.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr)),
    s8g_fv hΓ hμ hν hκ hμΓ hνΓ hκΓ, s8g_diag hΓ hμ hν hκ hμΓ hνΓ hκΓ⟩

/-- `eq_8_1`, termwise from `s8g_cor_7_9` and SYM. The orthonormality `hon` and the spanning `hspan` are not needed:
the identity holds for each term. -/
theorem s8g_eq_8_1 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {d : ℕ} (b : Fin d → ℂ → ℂ)
    (hb : ∀ n, IsHarmonicD (b n) ∧ IsGammaInvD Γ (b n))
    (hon : ∀ m n, innerGamma Γ (b m) (b n) = if m = n then 1 else 0)
    (hspan : ∀ μ, IsHarmonicD μ → IsGammaInvD Γ μ → ∃ c : Fin d → ℂ, ∀ z ∈ unitDisc, μ z = ∑ n, c n * b n z)
    {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∑ n, riemannRGamma Γ μ (b n) (b n) ν =
      -∑ n, (innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖b n z‖ ^ 2 : ℝ)) +
        innerGamma Γ (fun z => μ z * conj (b n z)) (resolventGammaD Γ fun z => ν z * conj (b n z))) := by
  -- `hon` and `hspan` are not needed: the identity holds term by term.
  have _hon := hon
  have _hspan := hspan
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  obtain ⟨hbh, hbΓ⟩ := hb n
  rw [s8g_cor_7_9 hΓ hbh hν hμ hbh hbΓ hνΓ hμΓ hbΓ, ← s8g_sym hΓ hμ hbh hbh hν hμΓ hbΓ hbΓ hνΓ]
  have e1 : (fun z => conj (ν z) * μ z) = fun z => μ z * conj (ν z) := funext fun z => mul_comm _ _
  have e2 : (fun z => conj (b n z) * b n z) = fun z => (((‖b n z‖ ^ 2 : ℝ)) : ℂ) := funext fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e3 : (fun z => conj (b n z) * ν z) = fun z => ν z * conj (b n z) := funext fun z => mul_comm _ _
  rw [e1, e2, e3]
  ring

/-- **Theorem 8.5** (TT:3350–3354), Wolpert [Wol86]. For `μ, ν, κ ∈ Ω^{-1,1}(𝔻, Γ)`:
- `∂/∂ε|_{ε=0} g_{μν̄}(εκ) = 0` (so the Weil–Petersson metric of `T(Γ)` is Kähler, TT:1052);
- `∂²/∂ε∂ε̄|_{ε=0} g_{μν̄}(εκ) = (μκ̄, G_Γ(νκ̄))_Γ + (μν̄, G_Γ(|κ|²))_Γ`.

[CORRECTION 2026-10-28, user-approved] Clause 1 now also asserts that `ε ↦ g_{μν̄}(εκ)` is ℝ-differentiable at `0`;
without it `dz … 0 = 0` holds by the junk value `fderiv = 0` (the memoir differentiates under the integral sign and
interchanges the derivative with the limits of Lemma 8.4, TT:3356). -/
theorem thm_8_5 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {μ ν κ : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν)
    (hκ : IsHarmonicD κ) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) (hκΓ : IsGammaInvD Γ κ) :
    DifferentiableAt ℝ (fun ε : ℂ => gGamma Γ μ ν (fun z => ε * κ z)) 0 ∧
      dz (fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 = 0 ∧
      dz (dzbar fun ε => gGamma Γ μ ν (fun z => ε * κ z)) 0 =
        innerGamma Γ (fun z => μ z * conj (κ z)) (resolventGammaD Γ fun z => ν z * conj (κ z)) +
          innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  exact s8g_thm_8_5 hΓ hμ hν hκ hμΓ hνΓ hκΓ

/-- **(8.1)** (TT:3458–3462). The Ricci tensor at the origin of `T(Γ)`, for an orthonormal basis `μ₁, …, μ_d` of
`Ω^{-1,1}(𝔻, Γ)`: `𝓡_{μν̄} = Σ_n R_{μ μ̄_n μ_n ν̄}`, which equals
`-Σ_n ((μν̄, G_Γ(|μ_n|²))_Γ + (μμ̄_n, G_Γ(νμ̄_n))_Γ)`. -/
theorem eq_8_1 {Γ : Subgroup SL2C} (hΓ : IsCofinite Γ) {d : ℕ} (b : Fin d → ℂ → ℂ)
    (hb : ∀ n, IsHarmonicD (b n) ∧ IsGammaInvD Γ (b n))
    (hon : ∀ m n, innerGamma Γ (b m) (b n) = if m = n then 1 else 0)
    (hspan : ∀ μ, IsHarmonicD μ → IsGammaInvD Γ μ → ∃ c : Fin d → ℂ, ∀ z ∈ unitDisc, μ z = ∑ n, c n * b n z)
    {μ ν : ℂ → ℂ} (hμ : IsHarmonicD μ) (hν : IsHarmonicD ν) (hμΓ : IsGammaInvD Γ μ) (hνΓ : IsGammaInvD Γ ν) :
    ∑ n, riemannRGamma Γ μ (b n) (b n) ν =
      -∑ n, (innerGamma Γ (fun z => μ z * conj (ν z)) (resolventGammaD Γ fun z => (‖b n z‖ ^ 2 : ℝ)) +
        innerGamma Γ (fun z => μ z * conj (b n z)) (resolventGammaD Γ fun z => ν z * conj (b n z))) := by
  exact s8g_eq_8_1 hΓ b hb hon hspan hμ hν hμΓ hνΓ

end TakhtajanTeo
