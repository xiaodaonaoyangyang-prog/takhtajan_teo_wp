import TakhtajanTeo.Appendix.A_HilbertStructure
import TakhtajanTeo.Appendix.AppA5Conj5
import TakhtajanTeo.Ch2.S1_Theorem112Completed
import TakhtajanTeo.Ch1.HomogeneousCompleted
import TakhtajanTeo.Ch1.FiberSphereWelding
import TakhtajanTeo.Ch1.Eq19Completed
import TakhtajanTeo.Ch1.TCurve
import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# Appendix A completed originals, part 2 (`appa2_` copies)

- `appa2_betaStar_spec` is `betaStar_spec` (TT:5930): the `EqOn` part is definitional; `𝒮(weldG) ∈ A₂(𝔻*)` because
  `weldG = λ_c ∘ g_μ ∘ σ_w⁻¹` off the single point `σ_w(∞)`, `𝒮` is Möbius invariant, and the weighted norm of `A₂(𝔻*)`
  is invariant under the automorphism `σ_w⁻¹` of `𝔻̂*`; then Theorem 1.12 (iii).
- `appa2_lemma_A_5_clause` is clause (ii)(a) of `lemma_A_5` (TT:5920–5926): `weldG` is, up to an affine map, the
  exterior welding map `g_{μ'}` of a class `[μ']` (welding uniqueness after a source-side normalization of the fibre
  homeomorphism `σ_w ∘ 𝗀_μ`); `[μ'] ∈ T₀(1)` by Theorem 1.12 (iii) and the first item, and `𝒜(g) = O(z⁻³)` for every
  `g` univalent at `∞`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-! ### Item 3: `betaStar_spec` -/

/-- `weldG μ w` is the exterior map of the corrected `fiber_welding`; it is univalent at `∞`. -/
theorem appa2_weldG_univalent {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsUnivalentAtInfty (weldG μ w) := by
  exact fiberWeldingExterior_isUnivalentAtInfty hμ hw

/-- The Schwarzian of a map univalent at `∞` is holomorphic on `𝔻*`. -/
theorem appa2_schwarzianHol_differentiableOn {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g) :
    DifferentiableOn ℂ (schwarzianHol g) unitDiscExterior := by
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  exact ab112_S_diff hopen hg.1 (fun z hz => deriv_ne_zero_of_injOn hopen hg.1 hg.2.1 hz)

/-- The hyperbolic density `ρ` is invariant under a Möbius map `s` with `|s|² - 1 = κ (|z|² - 1)/|cz + d|²`. -/
theorem appa2_rho_mobius_jacobian {A B C D z : ℂ} {κ : ℝ} (hdet : A * D - B * C = (κ : ℂ)) (hκ : κ ≠ 0)
    (hkey : ‖A * z + B‖ ^ 2 - ‖C * z + D‖ ^ 2 = κ * (‖z‖ ^ 2 - 1)) (hN : C * z + D ≠ 0) (hz : ‖z‖ ^ 2 ≠ 1) :
    rho ((A * z + B) / (C * z + D)) * ‖(A * D - B * C) / (C * z + D) ^ 2‖ ^ 2 = rho z := by
  have hq : ‖C * z + D‖ ≠ 0 := norm_ne_zero_iff.mpr hN
  have hx : 1 - ‖z‖ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h1 : 1 - ‖(A * z + B) / (C * z + D)‖ ^ 2 = κ * (1 - ‖z‖ ^ 2) / ‖C * z + D‖ ^ 2 := by
    rw [norm_div, div_pow, one_sub_div (pow_ne_zero 2 hq)]
    congr 1
    linarith
  unfold rho
  rw [h1, hdet, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_pow, div_pow, sq_abs]
  field_simp
  try ring

/-- The coefficients of `σ_w⁻¹` at finite points: determinant and circle identity. -/
theorem appa2_sigmaInv_coeffs {w : ℂ} :
    (-w * (1 - conj w)) * (-(1 - w) * conj w) - (-(1 - w)) * (-(1 - conj w)) =
        ((‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) : ℝ) : ℂ) ∧
      ∀ z : ℂ, ‖(-w * (1 - conj w)) * z + -(1 - w)‖ ^ 2 - ‖(-(1 - conj w)) * z + -(1 - w) * conj w‖ ^ 2 =
        ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  constructor
  · push_cast
    simp only [← Complex.mul_conj', map_sub, map_one]
    ring
  · intro z
    apply Complex.ofReal_injective
    push_cast
    simp only [← Complex.mul_conj', map_sub, map_one, map_add, map_mul, map_neg, Complex.conj_conj]
    ring

/-- Möbius invariance: the `A₂(𝔻*)` norm of `𝒮(weldG μ w)` equals that of `𝒮(g_μ)`. -/
theorem appa2_normA2_schwarzian_weldG {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    normA2 unitDiscExterior (schwarzianHol (weldG μ w)) = normA2 unitDiscExterior (schwarzianHol (gMu μ)) := by
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hw1 : 1 < ‖w‖ := hw
  obtain ⟨hdet, hkey⟩ := appa2_sigmaInv_coeffs (w := w)
  set A : ℂ := -w * (1 - conj w) with hA
  set B : ℂ := -(1 - w) with hB
  set C : ℂ := -(1 - conj w) with hC
  set D : ℂ := -(1 - w) * conj w with hD
  set κ : ℝ := ‖1 - w‖ ^ 2 * (‖w‖ ^ 2 - 1) with hκ
  set s : ℂ → ℂ := fun z => (A * z + B) / (C * z + D) with hs
  have hwne : w ≠ 1 := by
    rintro rfl
    simp at hw1
  have hC0 : C ≠ 0 := by
    rw [hC, neg_ne_zero, sub_ne_zero]
    intro h
    apply hwne
    have := congrArg conj h
    simpa using this.symm
  have hκ0 : 0 < κ := by
    have h1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hwne))
    have h2 : 1 < ‖w‖ ^ 2 := by nlinarith
    positivity
  have hdet0 : A * D - B * C ≠ 0 := by
    rw [hdet]
    exact_mod_cast hκ0.ne'
  set U : Set ℂ := unitDiscExterior \ {-D / C} with hU
  have hUo : IsOpen U := hopen.sdiff isClosed_singleton
  have hN : ∀ z ∈ U, C * z + D ≠ 0 := by
    intro z hz h
    apply hz.2
    rw [mem_singleton_iff, eq_div_iff hC0]
    linear_combination h
  have hsph : ∀ z : ℂ, C * z + D ≠ 0 →
      sigmaInvSphere (w : ExtPlane) (z : ExtPlane) = ((s z : ℂ) : ExtPlane) := by
    intro z h
    show mobiusExt A B C D (z : ExtPlane) = _
    rw [mobiusExt_coe h]
    rfl
  have hsU : ∀ z ∈ U, s z ∈ unitDiscExterior := by
    intro z hz
    have he := (sigmaSphere_mapsTo (Or.inl ⟨w, hw, rfl⟩)).2 (Or.inl ⟨z, hz.1, rfl⟩)
    rw [hsph z (hN z hz)] at he
    simpa [extDiscExterior, toExt] using he
  have hweld : ∀ z ∈ U, weldG μ w z = lambdaW (-1 / gMu μ w) (gMu μ (s z)) := fun z hz =>
    fiberWeldingExterior_finite hμ hw hz.1 (hsph z (hN z hz))
  have hgU : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding hμ).2.2.2.2.2.2
  have hW := appa2_weldG_univalent hμ hw
  have hsd : ∀ z ∈ U, HasDerivAt s ((A * D - B * C) / (C * z + D) ^ 2) z := fun z hz =>
    hasDerivAt_mobius (hN z hz)
  have hschw : ∀ z ∈ U,
      schwarzianHol (weldG μ w) z = schwarzianHol (gMu μ) (s z) * deriv s z ^ 2 := by
    intro z hz
    have hsa : AnalyticAt ℂ s z :=
      (by fun_prop : AnalyticAt ℂ (fun v : ℂ => A * v + B) z).div
        (by fun_prop : AnalyticAt ℂ (fun v : ℂ => C * v + D) z) (hN z hz)
    have hs' : deriv s z ≠ 0 := by
      rw [(hsd z hz).deriv]
      exact div_ne_zero hdet0 (pow_ne_zero 2 (hN z hz))
    have hga : AnalyticAt ℂ (gMu μ) (s z) := hgU.1.analyticAt (hopen.mem_nhds (hsU z hz))
    have hg' : deriv (gMu μ) (s z) ≠ 0 := deriv_ne_zero_of_injOn hopen hgU.1 hgU.2.1 (hsU z hz)
    have hGa : AnalyticAt ℂ (gMu μ ∘ s) z := hga.comp hsa
    have hG' : deriv (gMu μ ∘ s) z ≠ 0 := by
      rw [deriv_comp z hga.differentiableAt hsa.differentiableAt]
      exact mul_ne_zero hg' hs'
    have hev : weldG μ w =ᶠ[𝓝 z]
        fun v => (1 * (gMu μ ∘ s) v + 0) / ((-1 / gMu μ w) * (gMu μ ∘ s) v + 1) := by
      filter_upwards [hUo.mem_nhds hz] with v hv
      rw [hweld v hv]
      simp [lambdaW]
    have hWa : AnalyticAt ℂ (weldG μ w) z := hW.1.analyticAt (hopen.mem_nhds hz.1)
    rw [← schwarzian_of_analyticAt hWa, schwarzian_congr (hev.filter_mono nhdsWithin_le_nhds),
      schwarzian_mobius_comp_analytic hGa hG' (by simp), eq19_1_chain_rule hsa hs' hga hg',
      schwarzian_of_analyticAt hga, schwarzian_of_analyticAt hsa,
      show schwarzianHol s z = 0 from schwarzianHol_mobius hdet0 (hN z hz), add_zero]
  have hjac : ∀ z ∈ U, rho (s z) * ‖deriv s z‖ ^ 2 = rho z := by
    intro z hz
    have hz1 : ‖z‖ ^ 2 ≠ 1 := by
      have : 1 < ‖z‖ := hz.1
      nlinarith
    rw [(hsd z hz).deriv]
    exact appa2_rho_mobius_jacobian hdet hκ0.ne' (by rw [hkey z]) (hN z hz) hz1
  have hinj : InjOn s U := by
    intro z₁ h₁ z₂ h₂ he
    have h := congrArg (sigmaSphere (w : ExtPlane))
      ((hsph z₁ (hN z₁ h₁)).trans ((congrArg (fun x : ℂ => (x : ExtPlane)) he).trans
        (hsph z₂ (hN z₂ h₂)).symm))
    rw [sigmaSphere_inv_apply (Or.inl ⟨w, hw, rfl⟩), sigmaSphere_inv_apply (Or.inl ⟨w, hw, rfl⟩)] at h
    exact OnePoint.coe_injective h
  have himg : s '' U = unitDiscExterior \ {w} := by
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hsU z hz, fun hu => ?_⟩
      have h := congrArg (sigmaSphere (w : ExtPlane)) (hsph z (hN z hz))
      rw [sigmaSphere_inv_apply (Or.inl ⟨w, hw, rfl⟩), mem_singleton_iff.mp hu, sigmaSphere_pole] at h
      exact OnePoint.coe_ne_infty z h
    · rintro ⟨hu, huw⟩
      have hp := sigmaSphere_coe_eq hw (mem_singleton_iff.not.mp huw)
      have hmem := (sigmaSphere_mapsTo (Or.inl ⟨w, hw, rfl⟩)).1 (Or.inl ⟨u, hu, rfl⟩)
      rw [hp] at hmem
      have hzE : sigmaW w u ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hmem
      have hinv : sigmaInvSphere (w : ExtPlane) (sigmaW w u : ExtPlane) = (u : ExtPlane) := by
        rw [← hp, sigmaInvSphere_apply_sigma hw]
      have hNz : C * sigmaW w u + D ≠ 0 := by
        intro h0
        have h' : sigmaInvSphere (w : ExtPlane) (sigmaW w u : ExtPlane) = extInf :=
          mobiusExt_coe_of_eq_zero h0
        rw [hinv] at h'
        exact OnePoint.coe_ne_infty u h'
      refine ⟨sigmaW w u, ⟨hzE, fun h0 => hNz ?_⟩, ?_⟩
      · rw [mem_singleton_iff.mp h0]
        field_simp
        try ring
      · exact OnePoint.coe_injective ((hsph _ hNz).symm.trans hinv)
  have hsdiff : DifferentiableOn ℂ s U := fun z hz =>
    (hsd z hz).differentiableAt.differentiableWithinAt
  have hnull : ∀ p : ℂ, (unitDiscExterior \ {p} : Set ℂ) =ᵐ[volume] unitDiscExterior := fun p =>
    sdiff_null_ae_eq_self (measure_singleton p)
  have e1 : ∀ x : ℂ, ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  unfold normA2
  congr 1
  calc (∫⁻ z in unitDiscExterior, (‖schwarzianHol (weldG μ w) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹)
      = ∫⁻ z in U, (‖schwarzianHol (weldG μ w) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ :=
        (setLIntegral_congr (hnull _)).symm
    _ = ∫⁻ z in U, ENNReal.ofReal (‖deriv s z‖ ^ 2) *
          ((‖schwarzianHol (gMu μ) (s z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (s z))⁻¹) := by
        apply setLIntegral_congr_fun hUo.measurableSet
        intro z hz
        dsimp only
        have hr : 0 < rho (s z) := by
          have : 1 < ‖s z‖ := hsU z hz
          unfold rho
          have : (1 - ‖s z‖ ^ 2) ≠ 0 := by nlinarith
          positivity
        have hd : deriv s z ≠ 0 := by
          rw [(hsd z hz).deriv]
          exact div_ne_zero hdet0 (pow_ne_zero 2 (hN z hz))
        have hdn : 0 < ‖deriv s z‖ := norm_pos_iff.mpr hd
        rw [hschw z hz, e1, e1, ← hjac z hz, ← ENNReal.ofReal_mul (sq_nonneg _),
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [norm_mul, norm_pow]
        field_simp
    _ = ∫⁻ u in s '' U, (‖schwarzianHol (gMu μ) u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹ :=
        (r24_conformal_lintegral hUo hsdiff hinj
          (fun u => (‖schwarzianHol (gMu μ) u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹)).symm
    _ = ∫⁻ u in unitDiscExterior, (‖schwarzianHol (gMu μ) u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u)⁻¹ := by
        rw [himg]
        exact setLIntegral_congr (hnull _)

/-- Byte-identical copy of `betaStar_spec`. -/
theorem appa2_betaStar_spec {p : T1} (hp : p ∈ T01) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    EqOn (schwarzianHol (weldG (Quotient.out p : LinfStarBall) w)) (PsiOp (betaHatStar p w)) unitDiscExterior ∧
      schwarzianHol (weldG (Quotient.out p : LinfStarBall) w) ∈ A2fun unitDiscExterior := by
  have hμ := (Quotient.out p : LinfStarBall).2
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine ⟨fun z _ => rfl, appa2_schwarzianHol_differentiableOn (appa2_weldG_univalent hμ hw), ?_⟩
  have hA2 := ((thm_1_12 p).2.2.1).mp hp
  rw [S2C.s2c_gsans_eq hμ] at hA2
  rw [appa2_normA2_schwarzian_weldG hμ hw]
  exact hA2.2

/-! ### Item 4: clause (ii)(a) of `lemma_A_5` -/

/-- The pre-Schwarzian at `z` depends only on the germ at `z`. -/
theorem appa2_preSchwarzian_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    preSchwarzian f z = preSchwarzian g z := by
  have h1 : deriv f =ᶠ[𝓝 z] deriv g := h.deriv
  unfold preSchwarzian
  rw [h1.deriv_eq, h1.eq_of_nhds]

/-- `𝒜(g) = O(z⁻³)` at `∞` for `g` univalent at `∞` (`g(z) = az + b + O(z⁻¹)`). -/
theorem appa2_preSchwarzian_cubic {g : ℂ → ℂ} (hg : IsUnivalentAtInfty g) :
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖preSchwarzian g z‖ ≤ C / ‖z‖ ^ 3 := by
  obtain ⟨hgd, hgi, hgt⟩ := hg
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  -- `|g| ≥ 1` near `∞`
  obtain ⟨R₀, hR₀1, hR₀⟩ : ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ z : ℂ, R₀ < ‖z‖ → 1 ≤ ‖g z‖ := by
    have h := (tendsto_norm_cocompact_atTop.comp hgt).eventually_ge_atTop 1
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, eventually_comap, eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨max a 1, le_max_right _ _, fun z hz =>
      ha ‖z‖ ((le_max_left _ _).trans hz.le) z rfl⟩
  have hR₀0 : 0 < R₀ := by linarith
  set r : ℝ := R₀⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hR₀0
  have hinvR : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < r → R₀ < ‖ζ⁻¹‖ := by
    intro ζ hζ hζr
    rw [norm_inv, lt_inv_comm₀ hR₀0 (norm_pos_iff.mpr hζ)]
    exact hζr
  have hext : ∀ z : ℂ, R₀ < ‖z‖ → z ∈ unitDiscExterior := fun z hz =>
    show 1 < ‖z‖ by linarith
  set F : ℂ → ℂ := fun ζ => (g ζ⁻¹)⁻¹ with hF
  have hgne : ∀ z : ℂ, R₀ < ‖z‖ → g z ≠ 0 := fun z hz h0 => by
    have := hR₀ z hz
    rw [h0, norm_zero] at this
    linarith
  have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) r \ {0}) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := hζ.2
    have hR := hinvR ζ hζ0 (mem_ball_zero_iff.mp hζ.1)
    have hga : DifferentiableAt ℂ g ζ⁻¹ := hgd.differentiableAt (hopenE.mem_nhds (hext _ hR))
    exact ((hga.comp ζ (differentiableAt_inv hζ0)).inv (hgne _ hR)).differentiableWithinAt
  have hFb : BddAbove (norm ∘ F '' (ball (0 : ℂ) r \ {0})) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    have hR := hinvR ζ hζ.2 (mem_ball_zero_iff.mp hζ.1)
    simp only [Function.comp, F, norm_inv]
    exact inv_le_one_of_one_le₀ (hR₀ _ hR)
  have hFt : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ζ : ℂ => ζ⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto (fun ζ : ℂ => ‖g ζ⁻¹‖) (𝓝[≠] 0) atTop :=
      tendsto_norm_cocompact_atTop.comp (hgt.comp h1)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [F, norm_inv, Function.comp_def] using tendsto_inv_atTop_zero.comp h2
  set Ft : ℂ → ℂ := Function.update F 0 0 with hFt_def
  have hFtd : DifferentiableOn ℂ Ft (ball (0 : ℂ) r) := by
    have h := Complex.differentiableOn_update_limUnder_of_bddAbove
      (ball_mem_nhds (0 : ℂ) hr0) hFd hFb
    rwa [hFt.limUnder_eq] at h
  have hFt0 : Ft 0 = 0 := by simp [Ft]
  have hFtF : ∀ ζ : ℂ, ζ ≠ 0 → Ft ζ = F ζ := fun ζ hζ => by simp [Ft, hζ]
  have hFtinj : InjOn Ft (ball (0 : ℂ) r) := by
    have hne : ∀ ζ ∈ ball (0 : ℂ) r, ζ ≠ 0 → Ft ζ ≠ 0 := fun ζ hζ hζ0 => by
      rw [hFtF ζ hζ0]
      exact inv_ne_zero (hgne _ (hinvR ζ hζ0 (mem_ball_zero_iff.mp hζ)))
    intro ζ₁ h₁ ζ₂ h₂ he
    by_cases hz₁ : ζ₁ = 0
    · by_contra hne'
      have hz₂ : ζ₂ ≠ 0 := fun h => hne' (hz₁.trans h.symm)
      rw [hz₁, hFt0] at he
      exact hne ζ₂ h₂ hz₂ he.symm
    by_cases hz₂ : ζ₂ = 0
    · rw [hz₂, hFt0] at he
      exact absurd he (hne ζ₁ h₁ hz₁)
    rw [hFtF ζ₁ hz₁, hFtF ζ₂ hz₂] at he
    have he' : g ζ₁⁻¹ = g ζ₂⁻¹ := inv_injective he
    have := hgi (hext _ (hinvR ζ₁ hz₁ (mem_ball_zero_iff.mp h₁)))
      (hext _ (hinvR ζ₂ hz₂ (mem_ball_zero_iff.mp h₂))) he'
    exact inv_injective this
  have hFta : ∀ ζ ∈ ball (0 : ℂ) r, AnalyticAt ℂ Ft ζ := fun ζ hζ =>
    hFtd.analyticAt (isOpen_ball.mem_nhds hζ)
  have hFt' : ∀ ζ ∈ ball (0 : ℂ) r, deriv Ft ζ ≠ 0 := fun ζ hζ =>
    deriv_ne_zero_of_injOn isOpen_ball hFtd hFtinj hζ
  -- `Ft = ζ H`
  set H : ℂ → ℂ := dslope Ft 0 with hH
  have hFH : ∀ ζ, Ft ζ = ζ * H ζ := fun ζ => by
    have := sub_smul_dslope Ft 0 ζ
    rw [hFt0, sub_zero, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) r) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) hr0)).mpr hFtd
  have hHa : ∀ ζ ∈ ball (0 : ℂ) r, AnalyticAt ℂ H ζ := fun ζ hζ =>
    hHd.analyticAt (isOpen_ball.mem_nhds hζ)
  have hH0 : H 0 = deriv Ft 0 := dslope_same Ft 0
  have hb0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr0
  have hH0ne : H 0 ≠ 0 := hH0 ▸ hFt' 0 hb0
  have hdFt : ∀ ζ ∈ ball (0 : ℂ) r, deriv Ft ζ = H ζ + ζ * deriv H ζ := by
    intro ζ hζ
    have he : Ft = fun ζ => ζ * H ζ := funext hFH
    rw [he]
    have := ((hasDerivAt_id ζ).mul (hHa ζ hζ).differentiableAt.hasDerivAt).deriv
    simp only [id, one_mul] at this
    exact this
  have hddFt : deriv (deriv Ft) 0 = 2 * deriv H 0 := by
    have hev : deriv Ft =ᶠ[𝓝 0] fun ζ => H ζ + ζ * deriv H ζ :=
      Filter.eventuallyEq_of_mem (ball_mem_nhds (0 : ℂ) hr0) hdFt
    rw [hev.deriv_eq]
    have hd1 := (hHa 0 hb0).differentiableAt.hasDerivAt
    have hd2 := (hHa 0 hb0).deriv.differentiableAt.hasDerivAt
    have hD : HasDerivAt (fun ζ => H ζ + ζ * deriv H ζ)
        (deriv H 0 + (1 * deriv H 0 + 0 * deriv (deriv H) 0)) 0 :=
      hd1.add ((hasDerivAt_id' (0 : ℂ)).mul hd2)
    rw [hD.deriv]
    ring
  -- `Ψ = 𝒜(Ft) - 2 H'/H` is analytic at `0` and vanishes there
  set Ψ : ℂ → ℂ := fun ζ => preSchwarzian Ft ζ - 2 * deriv H ζ / H ζ with hΨ
  have hΨ0 : Ψ 0 = 0 := by
    simp only [Ψ, preSchwarzian, hddFt, ← hH0]
    field_simp
    ring
  have hΨd : DifferentiableAt ℂ Ψ 0 := by
    have hA : AnalyticAt ℂ (preSchwarzian Ft) 0 :=
      (hFta 0 hb0).deriv.deriv.div (hFta 0 hb0).deriv (hFt' 0 hb0)
    exact hA.differentiableAt.sub (((differentiableAt_const (2 : ℂ)).mul
      (hHa 0 hb0).deriv.differentiableAt).div (hHa 0 hb0).differentiableAt hH0ne)
  obtain ⟨K, hK⟩ := hΨd.isBigO_sub.bound
  have hHc : ∀ᶠ ζ in 𝓝 (0 : ℂ), H ζ ≠ 0 :=
    (hHa 0 hb0).continuousAt.eventually_ne hH0ne
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp
    (hK.and (hHc.and (ball_mem_nhds (0 : ℂ) hr0)))
  refine ⟨K, max R₀ δ⁻¹, fun z hz => ?_⟩
  have hzR : R₀ < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hzδ : δ⁻¹ < ‖z‖ := (le_max_right _ _).trans_lt hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hR₀0.trans hzR)
  set ζ : ℂ := z⁻¹ with hζ
  have hζ0 : ζ ≠ 0 := inv_ne_zero hz0
  have hζδ : dist ζ 0 < δ := by
    rw [dist_zero_right, hζ, norm_inv]
    exact inv_lt_of_inv_lt₀ hδ hzδ
  obtain ⟨hKζ, hHζ, hζr⟩ := hδP hζδ
  -- the inversion formula
  have hloc : (fun w => (Ft w⁻¹)⁻¹) =ᶠ[𝓝 z] g := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hzR] with w hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hR₀0.trans hw)
    simp only [hFtF _ (inv_ne_zero hw0), F, inv_inv]
  have hFtζ : Ft ζ ≠ 0 := by
    rw [hFH]
    exact mul_ne_zero hζ0 hHζ
  have hinv := preSchwarzian_inversion (hFta ζ hζr) hζ0 hFtζ (hFt' ζ hζr)
  rw [show ζ⁻¹ = z from inv_inv z, appa2_preSchwarzian_congr hloc, hdFt ζ hζr, hFH ζ] at hinv
  have hEq : preSchwarzian g z = -(ζ ^ 2) * Ψ ζ := by
    have h' : Ψ ζ = preSchwarzian Ft ζ - 2 * (H ζ + ζ * deriv H ζ) / (ζ * H ζ) + 2 / ζ := by
      simp only [Ψ]
      field_simp
      ring
    rw [h', ← hinv]
    field_simp
  rw [hEq, norm_mul, norm_neg, norm_pow]
  have hK' : ‖Ψ ζ‖ ≤ K * ‖ζ‖ := by
    simpa only [hΨ0, sub_zero] using hKζ
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hζn : ‖ζ‖ = ‖z‖⁻¹ := by rw [hζ, norm_inv]
  rw [hζn] at hK' ⊢
  calc ‖z‖⁻¹ ^ 2 * ‖Ψ ζ‖ ≤ ‖z‖⁻¹ ^ 2 * (K * ‖z‖⁻¹) :=
        mul_le_mul_of_nonneg_left hK' (by positivity)
    _ = K / ‖z‖ ^ 3 := by
        field_simp

/-- Inverting the disc automorphism `y ↦ (y - ā)/(c₀(1 - a y))` of `tce_exists_mu`. -/
theorem appa2_disc_mobius_solve {a c₀ x y : ℂ} (ha : ‖a‖ < 1) (hc : ‖c₀‖ = 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : (y - conj a) / (c₀ * (1 - a * y)) = x) :
    y = c₀ * blaschke (-(conj a * conj c₀)) x := by
  have hcc : c₀ * conj c₀ = 1 := by
    rw [Complex.mul_conj', hc]
    simp
  have hc0 : c₀ ≠ 0 := by
    rintro rfl
    simp at hc
  have hay : 1 - a * y ≠ 0 := by
    intro h0
    have h1 : ‖a * y‖ = 1 := by
      rw [show a * y = 1 by linear_combination -h0]
      simp
    rw [norm_mul] at h1
    nlinarith [norm_nonneg a, norm_nonneg y]
  have he : conj (-(conj a * conj c₀)) = -(a * c₀) := by simp
  have hax : 1 - -(a * c₀) * x ≠ 0 := by
    intro h0
    have h1 : ‖a * c₀ * x‖ = 1 := by
      rw [show a * c₀ * x = -1 by linear_combination h0]
      simp
    rw [norm_mul, norm_mul, hc, mul_one] at h1
    nlinarith [norm_nonneg a, norm_nonneg x]
  rw [div_eq_iff (mul_ne_zero hc0 hay)] at h
  unfold blaschke
  rw [he, mul_div_assoc', eq_div_iff hax]
  linear_combination h - conj a * hcc

/-- The fibre translate: `weldG μ w` is, up to an affine map, the exterior welding map of some class `p'`.
Route: `h' = σ_w ∘ 𝗀_μ` has welding `(λ_c ∘ f^μ, weldG μ w)` (`fiber_welding`); with the q.c. extension `E` of `h'`,
`tce_exists_mu` applied to `E⁻¹` gives a disc automorphism `B` with `h' ∘ B⁻¹` normalized; `eq19_exists_mu` gives `μ'`
with `w_{μ'} = h' ∘ B⁻¹` on `S¹`, whose welding is `(T ∘ λ_c ∘ f^μ ∘ B⁻¹, T ∘ weldG μ w)` for an affine `T`;
uniqueness (`conformal_welding`) and `welding_of_wA` conclude. -/
theorem appa2_exists_translate {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∃ (p' : T1) (a b : ℂ), a ≠ 0 ∧
      EqOn (gMu (Quotient.out p' : LinfStarBall)) (fun z => a * weldG μ w z + b) unitDiscExterior := by
  have hFW := fiber_welding hμ hw
  dsimp only at hFW
  obtain ⟨hOF, hWP, -⟩ := hFW
  obtain ⟨⟨F, G, hFq, hFs, hFf, hGq, hGs, hGg, hcirc⟩, hfd, hfi, -, -, hgU⟩ := hWP
  have hgU' : IsUnivalentAtInfty (weldG μ w) := hgU
  -- a plane q.c. extension `e` of the fibre homeomorphism `h' = σ_w ∘ 𝗀_μ`
  obtain ⟨E, ⟨K, hK⟩, hEs, hEc, hEh⟩ := circle_quasisymmetric_plane_extension hOF.1
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hEs
  have hK' := homeomorph_inverse_isKQC e hK
  have hEc' : e.symm '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    conv_lhs => rw [← hEc]
    exact e.symm_image_image _
  -- `w_{μ₀} = B ∘ e⁻¹` on `S¹` for a disc automorphism `B`
  obtain ⟨μ₀, hμ₀, a, c₀, ha, hc₀, -, hform⟩ := tce_exists_mu hK' hEc' (fun z _ => rfl)
  obtain ⟨-, -, -, -, -, -, hm1, hmI, hm2⟩ := wA_spec hμ₀
  have hn : ∀ x : ℂ, x = 1 ∨ x = -1 ∨ x = -I → wA μ₀ x = x := by
    rintro x (rfl | rfl | rfl)
    · show finPart (wAS μ₀ ((1 : ℂ) : ExtPlane)) = 1
      rw [hm2]
      rfl
    · show finPart (wAS μ₀ ((-1 : ℂ) : ExtPlane)) = -1
      rw [hm1]
      rfl
    · show finPart (wAS μ₀ ((-I : ℂ) : ExtPlane)) = -I
      rw [hmI]
      rfl
  have hcc : c₀ * conj c₀ = 1 := by
    rw [Complex.mul_conj', hc₀]
    simp
  have hc0 : c₀ ≠ 0 := by
    rintro rfl
    simp at hc₀
  set b : ℂ := -(conj a * conj c₀) with hb
  have hbn : ‖b‖ < 1 := by
    rw [hb, norm_neg, norm_mul, Complex.norm_conj, Complex.norm_conj, hc₀, mul_one]
    exact ha
  set N : ℂ → ℂ := fun x => c₀ * blaschke b x with hN
  obtain ⟨-, -, -, hBci⟩ := blaschke_closed_properties hbn
  have hNS : ∀ x : ℂ, ‖x‖ = 1 → ‖N x‖ = 1 := fun x hx => by
    simp only [N, norm_mul, hc₀, one_mul]
    exact blaschke_norm_circle hbn hx
  have hND : ∀ x : ℂ, ‖x‖ < 1 → ‖N x‖ < 1 := fun x hx => by
    simp only [N, norm_mul, hc₀, one_mul]
    exact blaschke_mem_unitDisc hbn hx
  have hsym : ∀ x : ℂ, x = 1 ∨ x = -1 ∨ x = -I → e.symm x = N x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by rcases hx with rfl | rfl | rfl <;> simp
    have hy : ‖e.symm x‖ = 1 := by
      have : e.symm x ∈ e.symm '' sphere (0 : ℂ) 1 := mem_image_of_mem _ (by simpa using hx1)
      rw [hEc'] at this
      simpa using this
    have h1 := hform x hx1
    rw [hn x hx] at h1
    exact appa2_disc_mobius_solve ha hc₀ hx1.le hy.le h1.symm
  -- `h' ∘ N` fixes `1, -1, -i`
  have hfix : ∀ x : ℂ, x = 1 ∨ x = -1 ∨ x = -I →
      sigmaW w (finPart (gammaMu μ (N x))) = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by rcases hx with rfl | rfl | rfl <;> simp
    have hmem : e.symm x ∈ unitCircle := by
      have : e.symm x ∈ e.symm '' sphere (0 : ℂ) 1 := mem_image_of_mem _ (by simpa using hx1)
      rw [hEc'] at this
      simpa [unitCircle] using this
    have h3 : e (e.symm x) = sigmaW w (finPart (gammaMu μ (e.symm x))) := hEh hmem
    rw [← hsym x hx, ← h3, e.apply_symm_apply]
  -- the radial extension of `N` and the composite plane map `e ∘ R`
  set Rr : ℂ → ℂ := radialDiskExtension N with hRr
  have hRK : IsKQC Rr univ ((1 + ‖b‖) / (1 - ‖b‖)) := radialRotationBlaschke_isKQC hc₀ hbn
  have hRh : IsHomeomorphOnto Rr univ univ := radialRotationBlaschke_homeomorph hc₀ hbn
  have hRN : ∀ z : ℂ, ‖z‖ ≤ 1 → Rr z = N z := fun z hz =>
    radialDiskExtension_eq_closed (mem_closedBall_zero_iff.mpr hz)
  have hER := thm7_1_comp hRK hK (subset_univ _)
  have hERs : (⇑e ∘ Rr) '' univ = univ := by rw [image_comp, hRh.2.2.1, hEs]
  obtain ⟨e₂, he₂⟩ := t1_homeomorph hER hERs
  have hK2 : IsKQC (⇑e₂) univ (((1 + ‖b‖) / (1 - ‖b‖)) * K) := he₂ ▸ hER
  have he₂c : e₂ '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    rw [he₂]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 : ‖z‖ = 1 := by simpa using hz
      have : e (N z) ∈ e '' sphere (0 : ℂ) 1 := mem_image_of_mem _ (by simpa using hNS z hz1)
      rw [hEc] at this
      simpa only [Function.comp, hRN z hz1.le] using this
    · intro hy
      rw [← hEc] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      have hu' : conj c₀ * u ∈ blaschke b '' sphere (0 : ℂ) 1 := by
        rw [hBci]
        have hu1 : ‖u‖ = 1 := by simpa using hu
        simp [hc₀, hu1]
      obtain ⟨z, hz, hzu⟩ := hu'
      refine ⟨z, hz, ?_⟩
      have hz1 : ‖z‖ = 1 := by simpa using hz
      simp only [Function.comp, hRN z hz1.le, N, hzu, ← mul_assoc, hcc, one_mul]
  have he₂h : EqOn (⇑e₂) (fun z => sigmaW w (finPart (gammaMu μ (N z)))) unitCircle := by
    intro z hz
    have hz1 : ‖z‖ = 1 := hz
    rw [he₂]
    simp only [Function.comp]
    rw [hRN z hz1.le]
    exact hEh (show N z ∈ unitCircle from hNS z hz1)
  obtain ⟨μ', hμ', hwA⟩ := eq19_exists_mu hK2 he₂c he₂h (hfix _ (Or.inr (Or.inl rfl)))
    (hfix _ (Or.inr (Or.inr rfl))) (hfix _ (Or.inl rfl))
  set p' : T1 := Phi ⟨μ', hμ'⟩ with hp'
  have hν : ((Quotient.out p' : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out p' : LinfStarBall).2
  have h2 : teichSetoid.r (Quotient.out p') ⟨μ', hμ'⟩ := Quotient.mk_out (s := teichSetoid) ⟨μ', hμ'⟩
  have hwν : ∀ z ∈ unitCircle, wA (Quotient.out p' : LinfStarBall) z =
      sigmaW w (finPart (gammaMu μ (N z))) := fun z hz => (h2 z hz).trans (hwA z hz)
  -- the transported welding `(T ∘ f ∘ N, T ∘ weldG)`
  have hNd : DifferentiableOn ℂ N unitDisc := (differentiableOn_blaschke hbn).const_mul c₀
  have hNinj : InjOn N unitDisc := fun x hx y hy he =>
    (isConformalOnto_blaschke hbn).2.1 hx hy (mul_left_cancel₀ hc0 he)
  have hNmaps : MapsTo N unitDisc unitDisc := fun x hx =>
    mem_ball_zero_iff.mpr (hND x (mem_ball_zero_iff.mp hx))
  set φ : ℂ → ℂ := fun z => lambdaW (-1 / gMu μ w) (fB μ (N z)) with hφ
  have hφd : DifferentiableOn ℂ φ unitDisc := hfd.comp hNd hNmaps
  have hφi : InjOn φ unitDisc := hfi.comp hNinj hNmaps
  set k : ℂ := deriv φ 0 with hk_def
  have hk : k ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hφd hφi (mem_ball_self one_pos)
  set β : ℂ := -(k⁻¹ * φ 0) with hβ
  refine ⟨p', k⁻¹, β, inv_ne_zero hk, ?_⟩
  have hWν : IsWelding (wA (Quotient.out p' : LinfStarBall)) id (fB (Quotient.out p' : LinfStarBall))
      (gMu (Quotient.out p' : LinfStarBall)) := by
    have := (welding_of_wA hν).1
    rwa [alphaMu_eq_id] at this
  obtain ⟨KF, hKF⟩ := hFq
  obtain ⟨KG, hKG⟩ := hGq
  have hFR := thm7_1_comp hRK hKF (subset_univ _)
  have hFRs : (F ∘ Rr) '' univ = univ := by rw [image_comp, hRh.2.2.1, hFs]
  have hA1 := td_affine_comp hFR hFRs (0 : ℂ) β one_ne_zero (inv_ne_zero hk)
  have hA2 := td_affine_comp hKG hGs (0 : ℂ) β one_ne_zero (inv_ne_zero hk)
  have hours : IsWelding (wA (Quotient.out p' : LinfStarBall)) id (fun z => k⁻¹ * φ z + β)
      (fun z => k⁻¹ * weldG μ w z + β) := by
    refine ⟨rfl, ⟨fun z => k⁻¹ * (F ∘ Rr) (1 * z + 0) + β, fun z => k⁻¹ * G (1 * z + 0) + β,
      ⟨_, hA1.1⟩, hA1.2, ?_, ⟨_, hA2.1⟩, hA2.2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      simp only [Function.comp, one_mul, add_zero]
      rw [hRN z (mem_ball_zero_iff.mp hz).le, hFf (hNmaps hz)]
    · intro z hz
      simp only [one_mul, add_zero]
      rw [hGg hz]
      rfl
    · intro z hz
      have hz1 : ‖z‖ = 1 := hz
      have key : k⁻¹ * G (1 * wA (Quotient.out p' : LinfStarBall) z + 0) + β =
          k⁻¹ * (F ∘ Rr) (1 * z + 0) + β := by
        simp only [one_mul, add_zero, Function.comp]
        have hc' : G (sigmaW w (finPart (gammaMu μ (N z)))) = F (N z) :=
          hcirc (N z) (show N z ∈ unitCircle from hNS z hz1)
        rw [hwν z hz, hc', hRN z hz1.le]
      exact congrArg (fun x : ℂ => (x : ExtPlane)) key
    · exact (hφd.const_mul _).add_const _
    · intro x hx y hy he
      exact hφi hx hy (mul_left_cancel₀ (inv_ne_zero hk) (add_right_cancel he))
    · show k⁻¹ * φ 0 + -(k⁻¹ * φ 0) = 0
      ring
    · have hd := ((hφd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt.const_mul
        k⁻¹).add_const β
      rw [hd.deriv]
      exact inv_mul_cancel₀ hk
    · refine ⟨(hgU'.1.const_mul _).add_const _, fun x hx y hy he =>
        hgU'.2.1 hx hy (mul_left_cancel₀ (inv_ne_zero hk) (add_right_cancel he)), ?_⟩
      have hA : Tendsto ((Homeomorph.mulLeft₀ k⁻¹ (inv_ne_zero hk)).trans (Homeomorph.addRight β))
          (cocompact ℂ) (cocompact ℂ) :=
        ((Homeomorph.mulLeft₀ k⁻¹ (inv_ne_zero hk)).trans (Homeomorph.addRight β)).isClosedEmbedding.tendsto_cocompact
      exact hA.comp hgU'.2.2
  exact ((conformal_welding (eq_1_9_homeo.1 p')).2 _ _ _ _ hWν hours).2

/-- Post-composition with an affine map, on the open set `𝔻*`, changes neither `𝒜` nor `𝒮`. -/
theorem appa2_eqOn_affine {g G : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) (hG : DifferentiableOn ℂ G unitDiscExterior)
    (h : EqOn g (fun z => a * G z + b) unitDiscExterior) :
    EqOn (preSchwarzian g) (preSchwarzian G) unitDiscExterior ∧
      EqOn (schwarzianHol g) (schwarzianHol G) unitDiscExterior := by
  -- `hG` is not needed: both sides are computed from the formulas `f''/f'` with junk `0/0 = 0` alike
  have _hG := hG
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hP : EqOn (preSchwarzian g) (preSchwarzian G) unitDiscExterior := by
    intro y hy
    rw [← preSchwarzian_affine_postcomp G ha b y]
    exact appa2_preSchwarzian_congr (Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) h)
  refine ⟨hP, fun z hz => ?_⟩
  have hev : preSchwarzian g =ᶠ[𝓝 z] preSchwarzian G :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) hP
  show deriv (preSchwarzian g) z - 1 / 2 * preSchwarzian g z ^ 2 =
    deriv (preSchwarzian G) z - 1 / 2 * preSchwarzian G z ^ 2
  rw [hev.deriv_eq, hP hz]

/-- Clause (ii)(a) of `lemma_A_5`, byte-identical to the fourth conjunct of its statement. -/
theorem appa2_lemma_A_5_clause :
    ∀ p ∈ T01, ∀ w ∈ unitDiscExterior, betaHatStar p w ∈ A21tildeExt ∧
      ∃ p' ∈ T01, EqOn (betaHatStar p w) (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior := by
  intro p hp w hw
  have hμ := (Quotient.out p : LinfStarBall).2
  have hopen : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hU := appa2_weldG_univalent hμ hw
  obtain ⟨p', a, b, ha, heq⟩ := appa2_exists_translate hμ hw
  have hμ' := (Quotient.out p' : LinfStarBall).2
  obtain ⟨hA, hS⟩ := appa2_eqOn_affine ha hU.1 heq
  have hA2 : schwarzianHol (gsans (Quotient.out p' : LinfStarBall)) ∈ A2fun unitDiscExterior := by
    rw [S2C.s2c_gsans_eq hμ', ab112_A2fun_congr hopen hS]
    exact (appa2_betaStar_spec hp hw).2
  have hp' : p' ∈ T01 := ((thm_1_12 p').2.2.1).mpr hA2
  have hA21 := ((thm_1_12 p').2.2.2).mp hp'
  rw [S2C.s2c_gsans_eq hμ', ab112_A21fun_congr hopen hA] at hA21
  exact ⟨⟨hA21, appa2_preSchwarzian_cubic hU⟩, p', hp', fun z hz => (hA hz).symm⟩

/-- **Lemma A.5** (TT:5920–5926).
- (i) `Ψ* : A₂¹(𝔻*) → A₂(𝔻*)`, `Ψ*(ψ) = ψ_z - ½ψ²`, is holomorphic, and injective on `Ã₂¹(𝔻*)`.
- (ii) `β̂*(𝒯₀(1)) = β̂*(T₀(1)) ⊂ Ã₂¹(𝔻*)`, and this set is open in `Ã₂¹(𝔻*)`.

Here `β̂*(T₀(1))` uses the welding `w_μ = g_μ⁻¹ ∘ f^μ` of `[μ]` itself (CW1–CW4), i.e. it is `{𝒜(g_μ)}`.

[CORRECTION 2026-10-25]
- The mapping clause is stated on `Ã₂¹(𝔻*)`: for `ψ = z⁻²`, `Ψ*(ψ) ∉ A₂(𝔻*)` (see Lemma 1.5).
- Openness is relative to `Ã₂¹(𝔻*)`: `Ã₂¹(𝔻*)` is a proper closed subspace, so no subset of it is open in
  `A₂¹(𝔻*)`.

Conjunct 5 proved in `Appendix/AppA5Conj5.lean` (2026-10-27). -/
theorem lemma_A_5 :
    (∀ ψ ∈ A21tildeExt, PsiOp ψ ∈ A2fun unitDiscExterior) ∧
      (∀ ψ ∈ A21fun unitDiscExterior, ∀ φ ∈ A21fun unitDiscExterior, ∀ t₀ : ℂ,
        Tendsto (fun t : ℂ => normA2 unitDiscExterior (fun z =>
            (PsiOp (fun u => ψ u + t * φ u) z - PsiOp (fun u => ψ u + t₀ * φ u) z) / (t - t₀) -
              (deriv φ z - (ψ z + t₀ * φ z) * φ z))) (𝓝[≠] t₀) (𝓝 0)) ∧
      (∀ ψ₁ ∈ A21tildeExt, ∀ ψ₂ ∈ A21tildeExt, EqOn (PsiOp ψ₁) (PsiOp ψ₂) unitDiscExterior →
        EqOn ψ₁ ψ₂ unitDiscExterior) ∧
      (∀ p ∈ T01, ∀ w ∈ unitDiscExterior, betaHatStar p w ∈ A21tildeExt ∧
        ∃ p' ∈ T01, EqOn (betaHatStar p w) (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior) ∧
      ∀ p ∈ T01, ∀ w ∈ unitDiscExterior, ∃ ε > 0, ∀ φ ∈ A21tildeExt,
        normA21 unitDiscExterior (fun z => φ z - betaHatStar p w z) < ENNReal.ofReal ε →
          ∃ p' ∈ T01, EqOn φ (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior :=
  ⟨lemma_A_5_mapping, lemma_A_5_line_remainder, fun ψ₁ h₁ ψ₂ h₂ h => PsiOp_injective_on_A21tildeExt h₁ h₂ h,
    TakhtajanTeo.AppA.appa2_lemma_A_5_clause,
    TakhtajanTeo.AppA.a55_conj5 TakhtajanTeo.AppA.appa2_lemma_A_5_clause TakhtajanTeo.AppA.appa2_preSchwarzian_cubic⟩

/-- (TT:5930) `β*(γ) = \overline{β(γ⁻¹) ∘ j} j_z̄² = 𝒮(g)`, i.e. `β* = Ψ* ∘ β̂*`, and `β*` takes values in `A₂(𝔻*)` on
`𝒯₀(1)`. -/
theorem betaStar_spec {p : T1} (hp : p ∈ T01) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    EqOn (schwarzianHol (weldG (Quotient.out p : LinfStarBall) w)) (PsiOp (betaHatStar p w)) unitDiscExterior ∧
      schwarzianHol (weldG (Quotient.out p : LinfStarBall) w) ∈ A2fun unitDiscExterior :=
  TakhtajanTeo.AppA.appa2_betaStar_spec hp hw

end AppA

end TakhtajanTeo
