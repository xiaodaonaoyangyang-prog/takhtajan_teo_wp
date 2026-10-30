import TakhtajanTeo.Ch1.S2Core
import LiZhongQC.Lemmas.Koebe
import LiZhongQC.Lemmas.DiscAutomorphism
import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Lemmas.Conformal

/-!
# Kernel bounds for the welding quasidisks (TT:1508–1518)

For `μ ∈ L∞(𝔻*)₁`, with `Ω = 𝖿(𝔻)`, `Ω* = 𝗀(𝔻*)`, `ρ₁ = (ρ ∘ 𝖿⁻¹)|(𝖿⁻¹)'|²` and `ρ₂ = (ρ ∘ 𝗀⁻¹)|(𝗀⁻¹)'|²`:
- `r24_interior_kernel_bound`: `∬_{Ω*} |u - z|⁻⁴ d²u ≤ 4π ρ₁(z)` for `z ∈ Ω`;
- `r24_exterior_kernel_bound`: `∬_Ω |u - z|⁻⁴ d²z ≤ 4π ρ₂(u)` for `u ∈ Ω*`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Koebe 1/4 at an arbitrary point of the disk. -/
theorem r24_koebe_point {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ unitDisc) (hi : InjOn φ unitDisc)
    {ζ : ℂ} (hζ : ζ ∈ unitDisc) :
    ball (φ ζ) (‖deriv φ ζ‖ * (1 - ‖ζ‖ ^ 2) / 4) ⊆ φ '' unitDisc := by
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have ha : ‖-ζ‖ < 1 := by rwa [norm_neg]
  set M : ℂ → ℂ := LiZhongQC.blaschke (-ζ) with hM
  have hMc := isConformalOnto_blaschke ha
  have hMmaps : MapsTo M unitDisc unitDisc := fun t ht =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp ht))
  have hM0 : M 0 = ζ := by simp [hM, LiZhongQC.blaschke]
  have hφ' : deriv φ ζ ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hd hi hζ
  have hs : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  set c : ℂ := deriv φ ζ * ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := mul_ne_zero hφ' (by exact_mod_cast hs.ne')
  set ψ : ℂ → ℂ := fun t => (φ (M t) - φ ζ) / c with hψ
  have hψd : DifferentiableOn ℂ ψ unitDisc :=
    ((hd.comp hMc.1 hMmaps).sub_const _).div_const _
  have hψi : InjOn ψ unitDisc := by
    intro t₁ h₁ t₂ h₂ he
    have he' : φ (M t₁) = φ (M t₂) := by
      simp only [hψ] at he
      have := (div_left_inj' hc0).mp he
      simpa using this
    exact hMc.2.1 h₁ h₂ (hi (hMmaps h₁) (hMmaps h₂) he')
  have hψ0 : ψ 0 = 0 := by simp [hψ, hM0]
  have hψ'0 : deriv ψ 0 = 1 := by
    have hMd := hasDerivAt_blaschke ha (by simp : ‖(0 : ℂ)‖ < 1)
    have hφd : HasDerivAt φ (deriv φ ζ) (M 0) := by
      rw [hM0]
      exact (hd.differentiableAt (isOpen_ball.mem_nhds hζ)).hasDerivAt
    have h : HasDerivAt ψ _ 0 := ((hφd.comp 0 hMd).sub_const (φ ζ)).div_const c
    rw [h.deriv]
    have hconj : (1 : ℂ) - -ζ * conj (-ζ) = ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) := by
      rw [map_neg, neg_mul_neg, mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [hconj, hc]
    simp only [mul_zero, sub_zero, one_pow, div_one]
    field_simp
    exact div_self (by exact_mod_cast hs.ne')
  have hK := koebe_quarter hψd hψi hψ0 hψ'0
  intro w hw
  have hcn : ‖c‖ = ‖deriv φ ζ‖ * (1 - ‖ζ‖ ^ 2) := by
    rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hw' : (w - φ ζ) / c ∈ ball (0 : ℂ) (1 / 4) := by
    rw [mem_ball_zero_iff, norm_div, hcn, div_lt_iff₀ (by rw [← hcn]; exact norm_pos_iff.mpr hc0)]
    have := mem_ball_iff_norm.mp hw
    linarith
  obtain ⟨t, ht, hte⟩ := hK hw'
  refine ⟨M t, hMmaps ht, ?_⟩
  have := hte
  simp only [hψ] at this
  field_simp at this
  linear_combination this

/-- `∬_S |u - z|⁻⁴ ≤ π/R²` when `S` stays at distance `≥ R` from `z`. -/
theorem r24_lintegral_outside {z : ℂ} {R : ℝ} (hR : 0 < R) {S : Set ℂ} (hS : ∀ u ∈ S, R ≤ ‖u - z‖) :
    ∫⁻ u in S, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤ ENNReal.ofReal (π / R ^ 2) := by
  have hsub : S ⊆ {u : ℂ | R < ‖u - z‖} ∪ sphere z R := by
    intro u hu
    rcases (hS u hu).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [mem_sphere, dist_eq_norm]; exact h.symm)
  have hker : ∀ u : ℂ, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 = ‖u - z‖ₑ ^ (-(4 : ℝ)) := by
    intro u
    rw [ENNReal.rpow_neg, ← ENNReal.inv_pow, enorm_eq_nnnorm, ← ENNReal.rpow_natCast]
    norm_num
  calc ∫⁻ u in S, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4
      ≤ ∫⁻ u in {u : ℂ | R < ‖u - z‖} ∪ sphere z R, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := lintegral_mono_set hsub
    _ ≤ (∫⁻ u in {u : ℂ | R < ‖u - z‖}, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4) +
        ∫⁻ u in sphere z R, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := lintegral_union_le _ _ _
    _ = ∫⁻ u in {u : ℂ | R < ‖u - z‖}, ‖u - z‖ₑ ^ (-(4 : ℝ)) := by
        rw [setLIntegral_measure_zero _ _ (Measure.addHaar_sphere volume z R), add_zero]
        simp_rw [hker]
    _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal (-R ^ (2 - (4 : ℝ)) / (2 - 4)) :=
        lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) hR z
    _ = ENNReal.ofReal (π / R ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (2 : ℝ) - 4 = -2 by norm_num, Real.rpow_neg hR.le]
        rw [show R ^ (2 : ℝ) = R ^ 2 by exact_mod_cast Real.rpow_natCast R 2]
        field_simp
        try ring

/-- **Interior kernel bound** (TT:1517): `∬_{Ω*} |u - z|⁻⁴ d²u ≤ 4π ρ₁(z)` for `z ∈ Ω = 𝖿(𝔻)`. -/
theorem r24_interior_kernel_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ}
    (hz : z ∈ fsans μ '' unitDisc) :
    ∫⁻ u in gsans μ '' unitDiscExterior, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤
      ENNReal.ofReal (4 * π * (rho (Function.invFunOn (fsans μ) unitDisc z) *
        ‖deriv (Function.invFunOn (fsans μ) unitDisc) z‖ ^ 2)) := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have hf := S2C.s2c_conf_f hμ
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hs : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hF : Function.invFunOn (fsans μ) unitDisc (fsans μ ζ) = ζ := hf.2.1.leftInvOn_invFunOn hζ
  have hF' := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hζ
  have hφ' : deriv (fsans μ) ζ ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hζ
  have hball := r24_koebe_point hf.1 hf.2.1 hζ
  have hdisj := (AppB.b8_welding_normalized_pair hμ).2.2.2.2.2
  set R : ℝ := ‖deriv (fsans μ) ζ‖ * (1 - ‖ζ‖ ^ 2) / 4 with hR
  have hR0 : 0 < R := by rw [hR]; have := norm_pos_iff.mpr hφ'; positivity
  have hout : ∀ u ∈ gsans μ '' unitDiscExterior, R ≤ ‖u - fsans μ ζ‖ := by
    intro u hu
    by_contra hlt
    push_neg at hlt
    have hub : u ∈ ball (fsans μ ζ) R := by rw [mem_ball, dist_eq_norm]; exact hlt
    exact Set.disjoint_left.mp hdisj (hball hub) hu
  refine (r24_lintegral_outside hR0 hout).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hF]
  have hn : ‖deriv (Function.invFunOn (fsans μ) unitDisc) (fsans μ ζ)‖ = ‖deriv (fsans μ) ζ‖⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hF', norm_one])
  rw [hn, hR]
  unfold rho
  have hd0 : ‖deriv (fsans μ) ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ'
  field_simp
  try ring

/-- The inversion `H(ξ) = 1/𝗀(1/ξ)` (`H(0) = 0`) of the exterior welding map. -/
theorem r24_inversion {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (fun ξ : ℂ => if ξ = 0 then 0 else (gsans μ ξ⁻¹)⁻¹) unitDisc ∧
      InjOn (fun ξ : ℂ => if ξ = 0 then 0 else (gsans μ ξ⁻¹)⁻¹) unitDisc ∧
      (∀ y ∈ unitDiscExterior, gsans μ y ≠ 0) := by
  have hg := S2C.s2c_conf_g hμ
  have hdisj := (AppB.b8_welding_normalized_pair hμ).2.2.2.2.2
  have hf0 : fsans μ 0 = 0 := by rw [S2C.s2c_fsans_eq hμ]; exact (fB_normalization μ).1
  have hg0 : ∀ y ∈ unitDiscExterior, gsans μ y ≠ 0 := by
    intro y hy h
    have h0 : (0 : ℂ) ∈ fsans μ '' unitDisc := ⟨0, mem_ball_self one_pos, hf0⟩
    exact Set.disjoint_left.mp hdisj h0 ⟨y, hy, h⟩
  have hinvE : ∀ ξ ∈ unitDisc, ξ ≠ 0 → ξ⁻¹ ∈ unitDiscExterior := by
    intro ξ hξ h0
    have h1 : ‖ξ‖ < 1 := mem_ball_zero_iff.mp hξ
    have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr h0
    show 1 < ‖ξ⁻¹‖
    rw [norm_inv]
    exact one_lt_inv₀ hp |>.mpr h1
  have hcocomp : Tendsto (gsans μ) (cocompact ℂ) (cocompact ℂ) := by
    rw [S2C.s2c_gsans_eq hμ]
    exact (gMu_isWelding hμ).2.2.2.2.2.2.2.2
  set H : ℂ → ℂ := fun ξ => if ξ = 0 then 0 else (gsans μ ξ⁻¹)⁻¹ with hH
  have hdiff : DifferentiableOn ℂ H (unitDisc \ {0}) := by
    intro ξ hξ
    have h0 : ξ ≠ 0 := hξ.2
    have hE := hinvE ξ hξ.1 h0
    have hev : H =ᶠ[𝓝 ξ] fun ξ => (gsans μ ξ⁻¹)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds h0] with t ht
      simp [hH, ht]
    have hgd : DifferentiableAt ℂ (gsans μ) ξ⁻¹ :=
      hg.1.differentiableAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hE)
    have hd : DifferentiableAt ℂ (fun ξ => (gsans μ ξ⁻¹)⁻¹) ξ :=
      (hgd.comp ξ (differentiableAt_inv h0)).inv (hg0 _ hE)
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  have hcont : ContinuousAt H 0 := by
    have h1 : Tendsto (fun ξ : ℂ => ξ⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]; exact tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto (fun ξ : ℂ => (gsans μ ξ⁻¹)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
      have := hcocomp.comp h1
      rw [← Metric.cobounded_eq_cocompact] at this
      exact tendsto_inv₀_cobounded.comp this
    have h3 : Tendsto H (𝓝[≠] 0) (𝓝 0) :=
      h2.congr' (eventually_nhdsWithin_of_forall fun t ht => by simp [hH, show t ≠ 0 from ht])
    have hH0 : H 0 = 0 := by simp [hH]
    rw [ContinuousAt, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup, hH0]
    exact ⟨h3, by simpa [hH0] using tendsto_pure_nhds H 0⟩
  refine ⟨(differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 one_pos)).mp
    ⟨hdiff, hcont⟩, ?_, hg0⟩
  intro ξ₁ h₁ ξ₂ h₂ he
  by_cases a₁ : ξ₁ = 0 <;> by_cases a₂ : ξ₂ = 0
  · rw [a₁, a₂]
  · simp only [hH, a₁, a₂, if_true, if_false] at he
    exact absurd he.symm (inv_ne_zero (hg0 _ (hinvE ξ₂ h₂ a₂)))
  · simp only [hH, a₁, a₂, if_true, if_false] at he
    exact absurd he (inv_ne_zero (hg0 _ (hinvE ξ₁ h₁ a₁)))
  · simp only [hH, a₁, a₂, if_false] at he
    have := hg.2.1 (hinvE ξ₁ h₁ a₁) (hinvE ξ₂ h₂ a₂) (inv_injective he)
    exact inv_injective this

/-- Change of variables `∬_{f(U)} G = ∬_U |f'|² G ∘ f` for an injective holomorphic `f` (Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`). The former duplicate `wpcv_conformal_l` (`Ch1/WPChangeOfVariables`)
now uses this theorem. -/
theorem r24_conformal_lintegral {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hi : InjOn f U) (G : ℂ → ℝ≥0∞) :
    (∫⁻ z in f '' U, G z) = ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2) * G (f z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hi G]
  apply setLIntegral_congr_fun hU.measurableSet
  intro z _
  dsimp only
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (sq_nonneg _)]

/-- **Exterior kernel bound** (TT:1511): `∬_Ω |u - z|⁻⁴ d²z ≤ 4π ρ₂(u)` for `u ∈ Ω* = 𝗀(𝔻*)`.

[TT defect, not in the statement] TT derives this from the "classical inequality" `1/4 ≤ η₂² ρ₂` (TT:1502–1503),
which is false on `Ω* ∋ ∞`: for `Ω* = {|u| > 1}`, `η₂² ρ₂ = 4/(|u|+1)² → 0`. The bound itself holds: under
`w = 1/z` (`0 ∈ Ω`), `∬_Ω |u - z|⁻⁴ d²z = |u|⁻⁴ ∬_{1/(Ω∖0)} |w - 1/u|⁻⁴ d²w`, and Koebe 1/4 for the univalent
`H(ξ) = 1/𝗀(1/ξ)` on `𝔻` keeps `1/(Ω∖0)` at distance `≥ |H'(1/x)|(1 - |x|⁻²)/4` from `1/u = H(1/x)`. -/
theorem r24_exterior_kernel_bound {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ℂ}
    (hu : u ∈ gsans μ '' unitDiscExterior) :
    ∫⁻ z in fsans μ '' unitDisc, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤
      ENNReal.ofReal (4 * π * (rho (Function.invFunOn (gsans μ) unitDiscExterior u) *
        ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) u‖ ^ 2)) := by
  obtain ⟨x, hx, rfl⟩ := hu
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hg := S2C.s2c_conf_g hμ
  have hfc := S2C.s2c_conf_f hμ
  obtain ⟨hHd, hHi, hg0⟩ := r24_inversion hμ
  have hdisj := (AppB.b8_welding_normalized_pair hμ).2.2.2.2.2
  have hx1 : 1 < ‖x‖ := hx
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx1
  set u := gsans μ x with hu
  have hu0 : u ≠ 0 := hg0 x hx
  have hG : Function.invFunOn (gsans μ) unitDiscExterior u = x := hg.2.1.leftInvOn_invFunOn hx
  have hG' := t1_deriv_invFunOn_mul hEo hg hx
  have hg' : deriv (gsans μ) x ≠ 0 := kb_deriv_ne_zero_of_injOn hEo hg.1 hg.2.1 hx
  set H : ℂ → ℂ := fun ξ : ℂ => if ξ = 0 then 0 else (gsans μ ξ⁻¹)⁻¹ with hH
  set ξ : ℂ := x⁻¹ with hξ
  have hξ0 : ξ ≠ 0 := inv_ne_zero hx0
  have hξD : ξ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (by rw [hξ, norm_inv]; exact inv_lt_one_of_one_lt₀ hx1)
  have hHξ : H ξ = u⁻¹ := by simp [hH, hξ0, hξ, hu, hx0]
  -- the derivative of `H` at `ξ`
  have hHder : deriv H ξ = deriv (gsans μ) x * x ^ 2 / u ^ 2 := by
    have hev : H =ᶠ[𝓝 ξ] fun t => (gsans μ t⁻¹)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds hξ0] with t ht
      simp [hH, ht]
    have hgd : HasDerivAt (gsans μ) (deriv (gsans μ) x) ξ⁻¹ := by
      rw [hξ, inv_inv]
      exact (hg.1.differentiableAt (hEo.mem_nhds hx)).hasDerivAt
    have h1 : HasDerivAt (fun t => (gsans μ t⁻¹)⁻¹) _ ξ :=
      (hgd.comp ξ (hasDerivAt_inv hξ0)).inv (by simp only [Function.comp, hξ, inv_inv]; exact hu0)
    rw [hev.deriv_eq, h1.deriv]
    simp only [Function.comp, hξ, inv_inv]
    rw [← hu]
    field_simp
  -- Koebe for `H` at `ξ`
  have hball := r24_koebe_point hHd hHi hξD
  set R : ℝ := ‖deriv H ξ‖ * (1 - ‖ξ‖ ^ 2) / 4 with hR
  have hRval : R = ‖deriv (gsans μ) x‖ * (‖x‖ ^ 2 - 1) / (4 * ‖u‖ ^ 2) := by
    rw [hR, hHder, hξ, norm_div, norm_mul, norm_pow, norm_pow, norm_inv]
    have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    field_simp
    try ring
  have hR0 : 0 < R := by
    rw [hRval]
    have h1 := norm_pos_iff.mpr hg'
    have h2 := norm_pos_iff.mpr hu0
    have h3 : 0 < ‖x‖ ^ 2 - 1 := by nlinarith
    positivity
  -- `Ω` is open
  have hΩo : IsOpen (fsans μ '' unitDisc) := by
    rw [S2C.s2c_fsans_eq hμ]
    obtain ⟨hd, hi⟩ := fB_holomorphic_injective hμ
    rcases (hd.analyticOnNhd isOpen_ball).is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with
      ⟨w, hw⟩ | h
    · exfalso
      have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
      have h1 : (1 / 2 : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by norm_num)
      have := hi h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
      norm_num at this
    · exact h _ subset_rfl isOpen_ball
  set Ω0 : Set ℂ := fsans μ '' unitDisc \ {0} with hΩ0
  have hU : IsOpen Ω0 := hΩo.sdiff isClosed_singleton
  have hid : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) Ω0 := fun w hw =>
    (differentiableAt_inv hw.2).differentiableWithinAt
  have hii : InjOn (fun w : ℂ => w⁻¹) Ω0 := inv_injective.injOn
  have hcov := r24_conformal_lintegral hU hid hii (fun w => (‖w - u⁻¹‖₊ : ℝ≥0∞)⁻¹ ^ 4)
  -- kernel in `ofReal` form
  have hker : ∀ v : ℂ, v ≠ 0 → (‖v‖₊ : ℝ≥0∞)⁻¹ ^ 4 = ENNReal.ofReal ((‖v‖ ^ 4)⁻¹) := by
    intro v hv
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hp.le, ← ENNReal.inv_pow, ofReal_norm,
      enorm_eq_nnnorm]
  have hne : ∀ z ∈ fsans μ '' unitDisc, u - z ≠ 0 := by
    intro z hz h
    have : z = u := (sub_eq_zero.mp h).symm
    exact Set.disjoint_left.mp hdisj hz (this ▸ ⟨x, hx, rfl⟩)
  have hpt : ∀ z ∈ Ω0, ENNReal.ofReal (‖deriv (fun w : ℂ => w⁻¹) z‖ ^ 2) * (‖z⁻¹ - u⁻¹‖₊ : ℝ≥0∞)⁻¹ ^ 4 =
      ENNReal.ofReal (‖u‖ ^ 4) * (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    have huz := hne z hz.1
    have hd : z⁻¹ - u⁻¹ ≠ 0 := by
      rw [inv_sub_inv hz0 hu0]; exact div_ne_zero huz (mul_ne_zero hz0 hu0)
    rw [hker _ hd, hker _ huz, deriv_inv, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_sub_inv hz0 hu0, norm_neg, norm_inv, norm_div, norm_mul, norm_pow]
    have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
    have h2 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have h3 : ‖u - z‖ ≠ 0 := norm_ne_zero_iff.mpr huz
    field_simp
  rw [setLIntegral_congr_fun hU.measurableSet hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hcov
  -- points of `1/(Ω ∖ 0)` stay away from `1/u`
  have hout : ∀ w ∈ (fun w : ℂ => w⁻¹) '' Ω0, R ≤ ‖w - u⁻¹‖ := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hlt
    push_neg at hlt
    have hb : z⁻¹ ∈ ball (H ξ) R := by rw [hHξ, mem_ball, dist_eq_norm]; exact hlt
    obtain ⟨t, ht, hte⟩ := hball hb
    by_cases t0 : t = 0
    · simp only [hH, t0, if_true] at hte
      exact inv_ne_zero hz.2 hte.symm
    · simp only [hH, t0, if_false] at hte
      have hzt : z = gsans μ t⁻¹ := (inv_injective hte).symm
      have htE : t⁻¹ ∈ unitDiscExterior := by
        show 1 < ‖t⁻¹‖
        rw [norm_inv]
        exact one_lt_inv₀ (norm_pos_iff.mpr t0) |>.mpr (mem_ball_zero_iff.mp ht)
      exact Set.disjoint_left.mp hdisj hz.1 ⟨t⁻¹, htE, hzt.symm⟩
  have hbound := (r24_lintegral_outside hR0 hout)
  rw [hcov] at hbound
  -- remove the null point `0`
  have hsplit : ∫⁻ z in fsans μ '' unitDisc, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤ ∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
    calc ∫⁻ z in fsans μ '' unitDisc, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4
        ≤ ∫⁻ z in Ω0 ∪ {0}, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := lintegral_mono_set (fun z hz => by
          by_cases h : z = 0
          · exact Or.inr h
          · exact Or.inl ⟨hz, h⟩)
      _ ≤ (∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4) + ∫⁻ z in ({0} : Set ℂ), (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 :=
          lintegral_union_le _ _ _
      _ = ∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
          rw [setLIntegral_measure_zero _ _ (measure_singleton 0), add_zero]
  refine hsplit.trans ?_
  have hu4 : 0 < ‖u‖ ^ 4 := by have := norm_pos_iff.mpr hu0; positivity
  have hI : ∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4 ≤ ENNReal.ofReal ((‖u‖ ^ 4)⁻¹ * (π / R ^ 2)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hu4]
    calc ∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4
        = (ENNReal.ofReal (‖u‖ ^ 4))⁻¹ * (ENNReal.ofReal (‖u‖ ^ 4) * ∫⁻ z in Ω0, (‖u - z‖₊ : ℝ≥0∞)⁻¹ ^ 4) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hu0) ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (‖u‖ ^ 4))⁻¹ * ENNReal.ofReal (π / R ^ 2) := by gcongr
  refine hI.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hG]
  have hn : ‖deriv (Function.invFunOn (gsans μ) unitDiscExterior) u‖ = ‖deriv (gsans μ) x‖⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hG', norm_one])
  rw [hn, hRval]
  unfold rho
  have h1 : ‖deriv (gsans μ) x‖ ≠ 0 := norm_ne_zero_iff.mpr hg'
  have h2 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have h3 : (1 : ℝ) - ‖x‖ ^ 2 ≠ 0 := by nlinarith
  have h4 : ‖x‖ ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  try ring

end TakhtajanTeo
