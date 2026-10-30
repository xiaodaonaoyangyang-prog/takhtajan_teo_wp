import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.S35WNorm
import TakhtajanTeo.Ch2.WReg3
import TakhtajanTeo.Ch1.S5RightTranslationHol
import TakhtajanTeo.Appendix.AppACont
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch1.WeldingUniqueness
import TakhtajanTeo.Ch1.S5Thm53Curve
import TakhtajanTeo.Ch1.S5ExteriorChartRegularity
import TakhtajanTeo.Ch1.S5WeldingRegularity

/-! # Reused ∂S₁ blocks (G), (A), (C) for the install of `s3d_S1_off` (Program G, STAGE)

`s35_l2sq_variation` (G), `s35_f_variation` (A) and `s35_beta_variation` (C) of 下属4's ∂S₁ host (G35O/HOST/S35Host d088f78f),
with exactly the helpers they need; the declarations are byte-identical to that host, the retired unwelded items
(W-GSIDE, W-GUNIF, (B), (D)) and everything only they use are dropped.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

open scoped InnerProductSpace

/-- `⟪u, v⟫` of `L²` representatives, as an integral. -/
theorem s35g_inner {μ : Measure ℂ} {f g : ℂ → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ z, conj (f z) * g z ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- Integrability of `f̄ g` for `L²` functions. -/
theorem s35g_integrable {μ : Measure ℂ} {f g : ℂ → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => conj (f z) * g z) μ := by
  refine (MeasureTheory.L2.integrable_inner (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- `‖u‖² = ∫ |f|²` for the `L²` representative `u` of `f`. -/
theorem s35g_norm_sq {μ : Measure ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    ((‖hf.toLp f‖ ^ 2 : ℝ) : ℂ) = ((∫ z, ‖f z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f)
  rw [s35g_inner hf hf] at h
  have e : (∫ z, conj (f z) * f z ∂μ) = ((∫ z, ‖f z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [e] at h
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at h
  rw [← h]

/-- `‖u‖` of the `L²` representative, through the lintegral. -/
theorem s35g_norm_eq {μ : Measure ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = ((∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)).toReal := by
  rw [Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- **(G)** If `F_t = F₀ + t δ + t̄ δ' + o(t)` in `L²(D)`, then `t ↦ ∫_D |F_t|²` is real differentiable at `0` with
`∂_t = ∫_D (F₀ δ̄' + F̄₀ δ)`. -/
theorem s35_l2sq_variation {D : Set ℂ} (hD : MeasurableSet D) {F : ℂ → ℂ → ℂ} {F₀ : ℂ → ℂ}
    (h0 : F 0 = F₀) (hL : ∀ᶠ t in 𝓝 (0 : ℂ), MemLp (F t) 2 (volume.restrict D))
    (h1 : MemLp (fun z => dz (fun t => F t z) 0) 2 (volume.restrict D))
    (h2 : MemLp (fun z => dzbar (fun t => F t z) 0) 2 (volume.restrict D))
    (hR : Tendsto (fun t : ℂ => (∫⁻ z in D, ‖F t z - F₀ z - t * dz (fun s => F s z) 0 -
      conj t * dzbar (fun s => F s z) 0‖ₑ ^ 2) / ‖t‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0)) :
    DifferentiableAt ℝ (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) 0 ∧
      dz (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) 0 =
        ∫ z in D, (F₀ z * conj (dzbar (fun s => F s z) 0) + conj (F₀ z) * dz (fun s => F s z) 0) := by
  set μ : Measure ℂ := volume.restrict D with hμ
  set δ₁ : ℂ → ℂ := fun z => dz (fun t => F t z) 0 with hδ₁
  set δ₂ : ℂ → ℂ := fun z => dzbar (fun t => F t z) 0 with hδ₂
  have hF0 : MemLp F₀ 2 μ := h0 ▸ hL.self_of_nhds
  let U : ℂ → Lp ℂ 2 μ := fun t => if h : MemLp (F t) 2 μ then h.toLp (F t) else 0
  have hUe : ∀ t (h : MemLp (F t) 2 μ), U t = h.toLp (F t) := fun t h => dif_pos h
  set d₁ := h1.toLp δ₁
  set d₂ := h2.toLp δ₂
  set u₀ := hF0.toLp F₀
  have hU0 : U 0 = u₀ := by
    have h := hL.self_of_nhds
    rw [hUe 0 h]
    congr 1
  let L : ℂ →L[ℝ] Lp ℂ 2 μ := (ContinuousLinearMap.id ℝ ℂ).smulRight d₁ +
    (Complex.conjCLE.toContinuousLinearMap).smulRight d₂
  have hLap (t : ℂ) : L t = t • d₁ + conj t • d₂ := rfl
  -- the remainder in `L²`
  have hrem : ∀ᶠ t in 𝓝 (0 : ℂ), ‖U t - U 0 - L t‖ =
      ((∫⁻ z in D, ‖F t z - F₀ z - t * δ₁ z - conj t * δ₂ z‖ₑ ^ 2) ^ (1 / 2 : ℝ)).toReal := by
    filter_upwards [hL] with t ht
    have hm : MemLp (fun z => F t z - F₀ z - t * δ₁ z - conj t * δ₂ z) 2 μ :=
      ((ht.sub hF0).sub (h1.const_mul t)).sub (h2.const_mul (conj t))
    rw [← s35g_norm_eq hm]
    congr 1
    rw [hUe t ht, hU0, hLap]
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Lp.coeFn_sub (ht.toLp (F t) - u₀) (t • d₁ + conj t • d₂),
      Lp.coeFn_sub (ht.toLp (F t)) u₀, Lp.coeFn_add (t • d₁) (conj t • d₂), Lp.coeFn_smul t d₁,
      Lp.coeFn_smul (conj t) d₂, ht.coeFn_toLp, hF0.coeFn_toLp, h1.coeFn_toLp, h2.coeFn_toLp]
      with z e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    rw [e1, e2, Pi.sub_apply, e3, Pi.sub_apply, e4, Pi.add_apply, e5, e6, Pi.smul_apply, Pi.smul_apply, e7, e8,
      e9, e10, smul_eq_mul, smul_eq_mul]
    ring
  have hUd : HasFDerivAt U L 0 := by
    rw [hasFDerivAt_iff_tendsto]
    simp only [sub_zero]
    have hlim : Tendsto (fun t : ℂ => (((∫⁻ z in D, ‖F t z - F₀ z - t * δ₁ z - conj t * δ₂ z‖ₑ ^ 2) /
        ‖t‖ₑ ^ 2) ^ (1 / 2 : ℝ)).toReal) (𝓝[≠] 0) (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hR
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
    refine ⟨?_, ?_⟩
    · apply hlim.congr'
      filter_upwards [nhdsWithin_le_nhds hrem, self_mem_nhdsWithin] with t ht htn
      rw [ht]
      have htn' : (t : ℂ) ≠ 0 := htn
      have hte : ‖t‖ₑ ≠ 0 := enorm_ne_zero.mpr htn'
      rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.toReal_div, toReal_enorm, div_eq_inv_mul]
    · rw [tendsto_pure_left]
      intro s hs
      simpa using mem_of_mem_nhds hs
  have hN := hUd.norm_sq
  have hC := (Complex.ofRealCLM.hasFDerivAt).comp (0 : ℂ) hN
  have hQ : (fun t : ℂ => ((∫ z in D, ‖F t z‖ ^ 2 : ℝ) : ℂ)) =ᶠ[𝓝 0] fun t => ((‖U t‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hL] with t ht
    rw [hUe t ht, s35g_norm_sq ht]
  refine ⟨hC.differentiableAt.congr_of_eventuallyEq hQ, ?_⟩
  rw [l613_dz_congr hQ]
  have hfd : fderiv ℝ (fun t : ℂ => ((‖U t‖ ^ 2 : ℝ) : ℂ)) 0 =
      Complex.ofRealCLM.comp (2 • (innerSL ℝ (U 0)).comp L) := hC.fderiv
  have hri : ∀ x y : Lp ℂ 2 μ, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
    intro x y
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← RCLike.re_to_complex,
      ← integral_re (MeasureTheory.L2.integrable_inner x y)]
    rfl
  have key : ∀ v : ℂ, (2 • (innerSL ℝ (U 0)).comp L) v = 2 * (v * ⟪u₀, d₁⟫_ℂ + conj v * ⟪u₀, d₂⟫_ℂ).re := by
    intro v
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, hLap, hU0, hri,
      inner_add_right, inner_smul_right, inner_smul_right, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [dz]
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  rw [key 1, key I]
  -- the two pairings
  have ha : ⟪u₀, d₁⟫_ℂ = ∫ z in D, conj (F₀ z) * δ₁ z := s35g_inner hF0 h1
  have hb : ⟪u₀, d₂⟫_ℂ = ∫ z in D, conj (F₀ z) * δ₂ z := s35g_inner hF0 h2
  have hi1 := s35g_integrable hF0 h1
  have hi2 := s35g_integrable hF0 h2
  have hsplit : (∫ z in D, (F₀ z * conj (δ₂ z) + conj (F₀ z) * δ₁ z)) =
      conj (∫ z in D, conj (F₀ z) * δ₂ z) + ∫ z in D, conj (F₀ z) * δ₁ z := by
    rw [integral_add _ hi1, ← integral_conj]
    · congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      rw [map_mul, Complex.conj_conj, mul_comm]
    · refine (s35g_integrable h2 hF0).congr ?_
      filter_upwards [] with z
      rw [mul_comm]
  show _ = ∫ z in D, (F₀ z * conj (δ₂ z) + conj (F₀ z) * δ₁ z)
  rw [hsplit, ← ha, ← hb]
  generalize ⟪u₀, d₁⟫_ℂ = A
  generalize ⟪u₀, d₂⟫_ℂ = B
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring

/-- A pointwise `o(|t|)` expansion `h(t) = h(0) + t α + t̄ β + o(t)` gives the real derivative at `0`. -/
theorem s35r_hasFDeriv {h : ℂ → ℂ} {α β : ℂ} {R : ℂ → ℝ} (hR : Tendsto R (𝓝[≠] 0) (𝓝 0))
    (hb : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖h t - h 0 - t * α - conj t * β‖ ≤ R t * ‖t‖) :
    HasFDerivAt h ((ContinuousLinearMap.id ℝ ℂ).smulRight α +
      (Complex.conjCLE.toContinuousLinearMap).smulRight β) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  simp only [sub_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul]
  rw [← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
  refine ⟨?_, ?_⟩
  · apply squeeze_zero' _ _ hR
    · exact Eventually.of_forall fun t => by positivity
    · filter_upwards [hb, eventually_mem_nhdsWithin] with t ht htn
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr htn
      rw [inv_mul_le_iff₀ hpos]
      calc ‖_‖ = ‖h t - h 0 - t * α - conj t * β‖ := by congr 1; ring
        _ ≤ R t * ‖t‖ := ht
        _ = ‖t‖ * R t := mul_comm _ _
  · rw [tendsto_pure_left]
    intro s hs
    simpa using mem_of_mem_nhds hs

/-- The Wirtinger parts of the real-linear map `t ↦ t α + t̄ β`. -/
theorem s35r_lin_dz {h : ℂ → ℂ} {α β : ℂ}
    (hh : HasFDerivAt h ((ContinuousLinearMap.id ℝ ℂ).smulRight α +
      (Complex.conjCLE.toContinuousLinearMap).smulRight β) 0) :
    dz h 0 = α ∧ dzbar h 0 = β := by
  simp only [dz, dzbar, hh.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I,
    smul_eq_mul]
  constructor
  · linear_combination (-(1 / 2 : ℂ) * α - (-(1 / 2 : ℂ)) * β) * Complex.I_sq
  · linear_combination ((1 / 2 : ℂ) * α - (1 / 2 : ℂ) * β) * Complex.I_sq

open TakhtajanTeo.AppA

/-- Quantitative form of `linearized_Psi_solution_A21_of_boundary_small`: with a bound `B` for
`(1 - |z|²)² |φ'|²` on the inner ball, the `A₂¹` energy of a solution is bounded explicitly. -/
theorem s35w_mass {ψ φ ϕ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDisc) (hϕ : ϕ ∈ A2fun unitDisc)
    (heq : EqOn (fun z => deriv φ z - ψ z * φ z) ϕ unitDisc) {s : ℝ}
    (hs : ∀ z ∈ unitDisc, s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖ψ z‖ ≤ 1 / 4) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z ∈ closedBall (0 : ℂ) s, (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv φ z‖ ^ 2 ≤ B) :
    (∫ z in unitDisc, ‖φ z‖ ^ 2) ≤
      4 * (8 * (∫ z in unitDisc, ‖ϕ z‖ ^ 2 * (rho z)⁻¹) + B * (volume unitDisc).toReal) + 2 * π * ‖φ 0‖ ^ 2 := by
  let H : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv φ z‖ ^ 2
  have hH : ContinuousOn H unitDisc :=
    (by fun_prop : ContinuousOn (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) unitDisc).mul
      ((hφ.1.deriv isOpen_ball).continuousOn.norm.pow 2)
  have hsub (r : ℝ) (hr : r < 1) : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
  let J : ℂ → ℝ := fun z => 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) + B
  have hϕi := A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hϕ
  have hvol : volume unitDisc ≠ ∞ := measure_ball_lt_top.ne
  have hJi : IntegrableOn J unitDisc := (hϕi.const_mul 8).add (integrableOn_const hvol)
  have hJint : (∫ z in unitDisc, J z) = 8 * (∫ z in unitDisc, ‖ϕ z‖ ^ 2 * (rho z)⁻¹) +
      B * (volume unitDisc).toReal := by
    rw [integral_add (hϕi.const_mul 8) (integrableOn_const hvol), integral_const_mul, setIntegral_const,
      smul_eq_mul, mul_comm B, Measure.real]
  have hJ0 (z : ℂ) : 0 ≤ J z := by dsimp [J, rho]; positivity
  have hpoint (z : ℂ) (hz : z ∈ unitDisc) : H z ≤ J z + (1 / 4) * ‖φ z‖ ^ 2 := by
    by_cases hzs : ‖z‖ ≤ s
    · have hb := hB z (mem_closedBall_zero_iff.mpr hzs)
      have hpos : 0 ≤ 8 * (‖ϕ z‖ ^ 2 * (rho z)⁻¹) := by unfold rho; positivity
      dsimp [J, H]
      nlinarith [sq_nonneg ‖φ z‖]
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
      nlinarith [hm, hψscaled, sq_nonneg ‖φ z‖]
  have hball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      (∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2) ≤ 4 * (∫ z in unitDisc, J z) + 2 * π * ‖φ 0‖ ^ 2 := by
    have hφi : IntegrableOn (fun z => ‖φ z‖ ^ 2) (ball (0 : ℂ) r) :=
      (((hφ.1.continuousOn.norm.pow 2).mono (hsub r hr1)).integrableOn_compact
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
    have hlower := eq_1_2_of_differentiable hφ.1 hr0 hr1
    change (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖φ z‖ ^ 2) - π / 2 * ‖φ 0‖ ^ 2 * r ^ 2 ≤
      ∫ z in ball (0 : ℂ) r, H z at hlower
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have herror := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖φ 0‖ ^ 2 by positivity)
    nlinarith
  have hlim := integrableOn_disk_mass_tendsto (a21_integrable_sq (D := unitDisc) measurableSet_ball hφ)
  rw [← hJint]
  apply le_of_tendsto hlim
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact hr.1
  filter_upwards [hev, self_mem_nhdsWithin] with r hr0 hr1
  exact hball r hr0 hr1

/-- Pointwise bound of an `A₂(𝔻)` function on the closed ball of radius `s < 1` (from `lemma_2_1`). -/
theorem s35w_ptwise {ϕ : ℂ → ℂ} (hϕ : ϕ ∈ A2fun unitDisc) {s : ℝ} (hs1 : s < 1) {w : ℂ} (hw : ‖w‖ ≤ s) :
    ‖ϕ w‖ ≤ Real.sqrt (12 / π) / (1 - s ^ 2) ^ 2 * (normA2 unitDisc ϕ).toReal := by
  have hw1 : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw.trans_lt hs1)
  have hs2 : 0 < 1 - s ^ 2 := by nlinarith [norm_nonneg w]
  have hb := lemma_2_1 (Or.inl rfl) hϕ w hw1
  rw [← ENNReal.ofReal_toReal hϕ.2.ne, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hle : (1 - s ^ 2) ^ 2 ≤ (1 - ‖w‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hs2.le (by nlinarith [norm_nonneg w]) 2
  have hm := mul_le_mul_of_nonneg_left hle (norm_nonneg (ϕ w))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- The arithmetic closing `s35_winv`. -/
theorem s35w_num {m N c B V α β : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c) (hV : 0 ≤ V) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hm : m ≤ 4 * (8 * N ^ 2 + B * V) + 2 * π * (4 * c ^ 2)) (hB : B ≤ (α * N + β * c) ^ 2) :
    m ≤ (Real.sqrt (32 + 4 * ((α + β) ^ 2 * V) + 8 * π) * (N + c)) ^ 2 := by
  have hC : Real.sqrt (32 + 4 * ((α + β) ^ 2 * V) + 8 * π) ^ 2 = 32 + 4 * ((α + β) ^ 2 * V) + 8 * π :=
    Real.sq_sqrt (by positivity)
  have e : (α + β) * (N + c) = α * N + β * c + (α * c + β * N) := by ring
  have h1 : α * N + β * c ≤ (α + β) * (N + c) := by
    rw [e]; linarith [mul_nonneg hα hc, mul_nonneg hβ hN]
  have h2 : B ≤ (α + β) ^ 2 * (N + c) ^ 2 := by
    rw [← mul_pow]; exact hB.trans (pow_le_pow_left₀ (by positivity) h1 2)
  have hNc : N ^ 2 ≤ (N + c) ^ 2 := pow_le_pow_left₀ hN (by linarith) 2
  have hcc : c ^ 2 ≤ (N + c) ^ 2 := pow_le_pow_left₀ hc (by linarith) 2
  have hBV := mul_le_mul_of_nonneg_right h2 hV
  rw [mul_pow, hC]
  have hpi := Real.pi_pos
  have h3 : 2 * π * (4 * c ^ 2) ≤ 8 * π * (N + c) ^ 2 := by nlinarith
  nlinarith

/-- **(W-INV)** The inverse `(ϕ, c) ↦ f' (∫₀^z ϕ/f' + 2c)` of the linearized Riccati map
`δ ↦ (δ' - 𝒜(f) δ, δ(0)/2)` (`thm_A_3_analytic`: bijective `A₂¹(𝔻) → A₂(𝔻) × ℂ`, with a forward bound) is bounded. -/
theorem s35_winv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hpre : preSchwarzian f ∈ A21fun unitDisc) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      normA21 unitDisc (fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) ≤
        C * (normA2 unitDisc ϕ + ‖c‖ₑ) := by
  have htwice := a21_const_mul (D := unitDisc) measurableSet_ball hpre (2 : ℂ)
  obtain ⟨s, hs0, hs1, hs⟩ := boundary_small_of_weighted_tendsto_zero (cor_1_4 (Or.inl rfl) htwice)
  have hsm : ∀ z ∈ unitDisc, s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖preSchwarzian f z‖ ≤ 1 / 4 := by
    intro z hz hzs
    have hb := hs z hz hzs
    rw [norm_mul] at hb
    norm_num only [Complex.norm_ofNat] at hb
    linarith
  have hK : closedBall (0 : ℂ) s ⊆ unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hs1)
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  obtain ⟨Mf, hMf⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn (hdf.continuousOn.mono hK)
  obtain ⟨Mi, hMi⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    ((hdf.continuousOn.inv₀ fun z hz => hne z hz).mono hK)
  obtain ⟨Mψ, hMψ⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    (hpre.1.continuousOn.mono hK)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Real.sqrt (12 / π) / (1 - s ^ 2) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  obtain ⟨Mf', hMf'd⟩ : ∃ x : ℝ, x = max Mf 0 := ⟨_, rfl⟩
  obtain ⟨Mi', hMi'd⟩ : ∃ x : ℝ, x = max Mi 0 := ⟨_, rfl⟩
  obtain ⟨Mψ', hMψ'd⟩ : ∃ x : ℝ, x = max Mψ 0 := ⟨_, rfl⟩
  have hMf' : 0 ≤ Mf' := hMf'd ▸ le_max_right _ _
  have hMi' : 0 ≤ Mi' := hMi'd ▸ le_max_right _ _
  have hMψ' : 0 ≤ Mψ' := hMψ'd ▸ le_max_right _ _
  obtain ⟨α, hα⟩ : ∃ x : ℝ, x = Mψ' * Mf' * (s * Mi' * K) + K := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, x = 2 * Mψ' * Mf' := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; have := hs0.le; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hV0 : 0 ≤ (volume unitDisc).toReal := ENNReal.toReal_nonneg
  refine ⟨ENNReal.ofReal (Real.sqrt (32 + 4 * ((α + β) ^ 2 * (volume unitDisc).toReal) + 8 * π)),
    ENNReal.ofReal_lt_top, ?_⟩
  intro ϕ hϕ c
  obtain ⟨hφA, heq, h0⟩ := (thm_A_3_analytic hf hne hzero hpre).1 ϕ hϕ c
  obtain ⟨N, hN⟩ : ∃ x : ℝ, x = (normA2 unitDisc ϕ).toReal := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hN ▸ ENNReal.toReal_nonneg
  have hKϕ : ∀ w ∈ closedBall (0 : ℂ) s, ‖ϕ w‖ ≤ K * N := fun w hw => by
    rw [hKdef, hN]; exact s35w_ptwise hϕ hs1 (mem_closedBall_zero_iff.mp hw)
  -- bound of the segment integral
  have hP : ∀ z ∈ closedBall (0 : ℂ) s,
      ‖∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z‖ ≤ s * Mi' * K * N := by
    intro z hz
    have hzs : ‖z‖ ≤ s := mem_closedBall_zero_iff.mp hz
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => ϕ (t * z) / deriv f (t * z) * z) (C := s * Mi' * K * N) ?_
    · simpa using h
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htz : (t : ℂ) * z ∈ closedBall (0 : ℂ) s := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
        _ ≤ s := by rw [one_mul]; exact hzs
    have h1 := hKϕ _ htz
    have h2 : ‖(deriv f (t * z))⁻¹‖ ≤ Mi' := hMi'd ▸ (hMi _ htz).trans (le_max_left _ _)
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc ‖ϕ (t * z)‖ * ‖(deriv f (t * z))⁻¹‖ * ‖z‖ ≤ (K * N) * Mi' * s := by
          gcongr
      _ = s * Mi' * K * N := by ring
  have hφb : ∀ z ∈ closedBall (0 : ℂ) s,
      ‖deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)‖ ≤
        Mf' * (s * Mi' * K * N + 2 * ‖c‖) := by
    intro z hz
    have h1 : ‖deriv f z‖ ≤ Mf' := hMf'd ▸ (hMf z hz).trans (le_max_left _ _)
    have h3 : ‖(∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c‖ ≤
        s * Mi' * K * N + 2 * ‖c‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hP z hz]
    rw [norm_mul]
    exact mul_le_mul h1 h3 (norm_nonneg _) hMf'
  have hBb : ∀ z ∈ closedBall (0 : ℂ) s, (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) z‖ ^ 2 ≤ (α * N + β * ‖c‖) ^ 2 := by
    intro z hz
    have hz1 := hK hz
    have he := heq hz1
    simp only at he
    have hψz : ‖preSchwarzian f z‖ ≤ Mψ' := hMψ'd ▸ (hMψ z hz).trans (le_max_left _ _)
    have hn : ‖deriv (fun z => deriv f z *
        ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) z‖ ≤ α * N + β * ‖c‖ := by
      rw [show deriv (fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) z =
        preSchwarzian f z * (deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) + ϕ z
        by linear_combination he]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h1 := mul_le_mul hψz (hφb z hz) (norm_nonneg _) hMψ'
      have h2 := hKϕ z hz
      have e : Mψ' * (Mf' * (s * Mi' * K * N + 2 * ‖c‖)) + K * N = α * N + β * ‖c‖ := by
        rw [hα, hβ]; ring
      linarith
    have hw1 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by
      have h1 := mem_ball_zero_iff.mp hz1
      have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have h2 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      calc (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h2 2
        _ = 1 := one_pow 2
    calc (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (fun z => deriv f z *
          ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) z‖ ^ 2
        ≤ 1 * ‖deriv (fun z => deriv f z *
          ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
      _ ≤ (α * N + β * ‖c‖) ^ 2 := by rw [one_mul]; exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hmass := s35w_mass hφA hϕ heq hsm (sq_nonneg _) hBb
  have hφ0 : deriv f 0 * ((∫ t in (0 : ℝ)..1, ϕ (t * 0) / deriv f (t * 0) * 0) + 2 * c) = 2 * c := by
    linear_combination 2 * h0
  have hI : (∫ z in unitDisc, ‖ϕ z‖ ^ 2 * (rho z)⁻¹) = N ^ 2 := by
    have h := A2fun.normA2_sq (D := unitDisc) isOpen_ball hϕ
    have hnn : 0 ≤ ∫ z in unitDisc, ‖ϕ z‖ ^ 2 * (rho z)⁻¹ :=
      setIntegral_nonneg measurableSet_ball fun z _ => by unfold rho; positivity
    rw [hN, ← ENNReal.toReal_pow, h, ENNReal.toReal_ofReal hnn]
  have hc2 : ‖(2 : ℂ) * c‖ ^ 2 = 4 * ‖c‖ ^ 2 := by rw [norm_mul, Complex.norm_ofNat]; ring
  rw [hI, hφ0, hc2] at hmass
  have hfin := s35w_num hN0 (norm_nonneg c) hV0 hα0 hβ0 hmass le_rfl
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two]
  rw [a21_norm_sq_eq_integral (D := unitDisc) measurableSet_ball hφA,
    ← ENNReal.ofReal_toReal hϕ.2.ne, ← ofReal_norm_eq_enorm, ← hN,
    ← ENNReal.ofReal_add hN0 (norm_nonneg _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (by positivity))]
  exact ENNReal.ofReal_le_ofReal hfin

/-- Weighted measurability of a holomorphic function on `𝔻`. -/
theorem s35r_aesm {ϕ : ℂ → ℂ} (hϕ : DifferentiableOn ℂ ϕ unitDisc) :
    AEStronglyMeasurable ϕ (rhoInvMeasure unitDisc) :=
  (hϕ.continuousOn.aestronglyMeasurable measurableSet_ball).mono_ac (withDensity_absolutelyContinuous _ _)

/-- `A₂(𝔻)` is closed under sums, with the triangle inequality. -/
theorem s35r_A2_add {ϕ ψ : ℂ → ℂ} (hϕ : ϕ ∈ A2fun unitDisc) (hψ : ψ ∈ A2fun unitDisc) :
    (fun z => ϕ z + ψ z) ∈ A2fun unitDisc ∧
      normA2 unitDisc (fun z => ϕ z + ψ z) ≤ normA2 unitDisc ϕ + normA2 unitDisc ψ := by
  have hle : normA2 unitDisc (fun z => ϕ z + ψ z) ≤ normA2 unitDisc ϕ + normA2 unitDisc ψ := by
    rw [normA2_eq_eLpNorm _ _ (s35r_aesm (ϕ := fun z => ϕ z + ψ z) (hϕ.1.add hψ.1)), normA2_eq_eLpNorm _ _ (s35r_aesm hϕ.1),
      normA2_eq_eLpNorm _ _ (s35r_aesm hψ.1)]
    exact eLpNorm_add_le (by norm_num)
  exact ⟨⟨hϕ.1.add hψ.1, hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hϕ.2, hψ.2⟩)⟩, hle⟩

/-- `A₂(𝔻)` is closed under scalar multiples. -/
theorem s35r_A2_smul {ϕ : ℂ → ℂ} (hϕ : ϕ ∈ A2fun unitDisc) (c : ℂ) :
    (fun z => c * ϕ z) ∈ A2fun unitDisc :=
  ⟨hϕ.1.const_mul c, by rw [normA2_const_mul]; exact ENNReal.mul_lt_top ENNReal.coe_lt_top hϕ.2⟩

/-- Continuity of the segment integrand of the linearized inverse. -/
theorem s35r_seg_cont {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hg : DifferentiableOn ℂ g unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    IntervalIntegrable (fun s : ℝ => g (s * z) / deriv f (s * z) * z) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  have hmem : ∀ s ∈ uIcc (0 : ℝ) 1, (s : ℂ) * z ∈ unitDisc := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg z)
      _ < 1 := by rw [one_mul]; exact mem_ball_zero_iff.mp hz
  have hc : ContinuousOn (fun s : ℝ => (s : ℂ) * z) (uIcc (0 : ℝ) 1) :=
    (Complex.continuous_ofReal.mul continuous_const).continuousOn
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  refine ((hg.continuousOn.comp hc hmem).div (hdf.continuousOn.comp hc hmem) ?_).mul continuousOn_const
  intro s hs
  exact hne _ (hmem s hs)

/-- Linearity of the explicit inverse `(ϕ, c) ↦ f' (∫₀^z ϕ/f' + 2c)`. -/
theorem s35r_inv_lin {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    {ϕ σ₁ σ₂ : ℂ → ℂ} (hϕ : DifferentiableOn ℂ ϕ unitDisc) (hσ₁ : DifferentiableOn ℂ σ₁ unitDisc)
    (hσ₂ : DifferentiableOn ℂ σ₂ unitDisc) (c q₁ q₂ t : ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv f z * ((∫ s in (0 : ℝ)..1, ϕ (s * z) / deriv f (s * z) * z) + 2 * c) -
        t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv f (s * z) * z) + 2 * q₁)) -
        conj t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv f (s * z) * z) + 2 * q₂)) =
      deriv f z * ((∫ s in (0 : ℝ)..1, (ϕ (s * z) - t * σ₁ (s * z) - conj t * σ₂ (s * z)) /
        deriv f (s * z) * z) + 2 * (c - t * q₁ - conj t * q₂)) := by
  have h0 := s35r_seg_cont hf hne hϕ hz
  have h1 := (s35r_seg_cont hf hne hσ₁ hz).const_mul t
  have h2 := (s35r_seg_cont hf hne hσ₂ hz).const_mul (conj t)
  have he : (∫ s in (0 : ℝ)..1, (ϕ (s * z) - t * σ₁ (s * z) - conj t * σ₂ (s * z)) / deriv f (s * z) * z) =
      ∫ s in (0 : ℝ)..1, (ϕ (s * z) / deriv f (s * z) * z - t * (σ₁ (s * z) / deriv f (s * z) * z) -
        conj t * (σ₂ (s * z) / deriv f (s * z) * z)) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only
    ring
  rw [he, intervalIntegral.integral_sub (h0.sub h1) h2, intervalIntegral.integral_sub h0 h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- Pointwise bound of the explicit inverse at a fixed point of `𝔻`. -/
theorem s35r_inv_pt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      ‖deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)‖ ≤
        C * ((normA2 unitDisc ϕ).toReal + ‖c‖) := by
  have hs1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hK : closedBall (0 : ℂ) ‖z‖ ⊆ unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hs1)
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  obtain ⟨Mi, hMi⟩ := (isCompact_closedBall (0 : ℂ) ‖z‖).exists_bound_of_continuousOn
    ((hdf.continuousOn.inv₀ fun z hz => hne z hz).mono hK)
  obtain ⟨Mi', hMi'd⟩ : ∃ x : ℝ, x = max Mi 0 := ⟨_, rfl⟩
  have hMi' : 0 ≤ Mi' := hMi'd ▸ le_max_right _ _
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = Real.sqrt (12 / π) / (1 - ‖z‖ ^ 2) ^ 2 := ⟨_, rfl⟩
  have hs2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨‖deriv f z‖ * (‖z‖ * Mi' * K + 2), by positivity, ?_⟩
  intro ϕ hϕ c
  obtain ⟨N, hN⟩ : ∃ x : ℝ, x = (normA2 unitDisc ϕ).toReal := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hN ▸ ENNReal.toReal_nonneg
  have hP : ‖∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z‖ ≤ ‖z‖ * Mi' * K * N := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => ϕ (t * z) / deriv f (t * z) * z) (C := ‖z‖ * Mi' * K * N) ?_
    · simpa using h
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have htz : (t : ℂ) * z ∈ closedBall (0 : ℂ) ‖z‖ := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
        _ = ‖z‖ := one_mul _
    have h1 : ‖ϕ (t * z)‖ ≤ K * N := by
      rw [hKd, hN]; exact s35w_ptwise hϕ hs1 (mem_closedBall_zero_iff.mp htz)
    have h2 : ‖(deriv f (t * z))⁻¹‖ ≤ Mi' := hMi'd ▸ (hMi _ htz).trans (le_max_left _ _)
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc ‖ϕ (t * z)‖ * ‖(deriv f (t * z))⁻¹‖ * ‖z‖ ≤ (K * N) * Mi' * ‖z‖ := by gcongr
      _ = ‖z‖ * Mi' * K * N := by ring
  have h3 : ‖(∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c‖ ≤ ‖z‖ * Mi' * K * N + 2 * ‖c‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have h4 : ‖z‖ * Mi' * K * N + 2 * ‖c‖ ≤ (‖z‖ * Mi' * K + 2) * (N + ‖c‖) := by
    have hzK : 0 ≤ ‖z‖ * Mi' * K := by positivity
    nlinarith [norm_nonneg c, mul_nonneg hzK (norm_nonneg c)]
  rw [norm_mul, ← hN]
  calc ‖deriv f z‖ * ‖(∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c‖
      ≤ ‖deriv f z‖ * (‖z‖ * Mi' * K * N + 2 * ‖c‖) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ ‖deriv f z‖ * ((‖z‖ * Mi' * K + 2) * (N + ‖c‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = ‖deriv f z‖ * (‖z‖ * Mi' * K + 2) * (N + ‖c‖) := by ring

/-- Riccati representation: `𝒜(G) - 𝒜(f)` is the explicit inverse applied to
`(𝒮(G) - 𝒮(f) + (𝒜(G) - 𝒜(f))²/2, (𝒜(G)(0) - 𝒜(f)(0))/2)`. -/
theorem s35r_rep {f G : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hpre : preSchwarzian f ∈ A21fun unitDisc)
    (hG : DifferentiableOn ℂ G unitDisc) (hGne : ∀ z ∈ unitDisc, deriv G z ≠ 0)
    (hGpre : preSchwarzian G ∈ A21fun unitDisc)
    (hΦ : (fun z => schwarzianHol G z - schwarzianHol f z + (preSchwarzian G z - preSchwarzian f z) ^ 2 / 2) ∈
      A2fun unitDisc) :
    EqOn (fun z => preSchwarzian G z - preSchwarzian f z) (fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, (schwarzianHol G (t * z) - schwarzianHol f (t * z) +
        (preSchwarzian G (t * z) - preSchwarzian f (t * z)) ^ 2 / 2) / deriv f (t * z) * z) +
        2 * ((preSchwarzian G 0 - preSchwarzian f 0) / 2))) unitDisc := by
  obtain ⟨hIA, heq, h0⟩ := (thm_A_3_analytic hf hne hzero hpre).1 _ hΦ ((preSchwarzian G 0 - preSchwarzian f 0) / 2)
  have hδ : (fun z => preSchwarzian G z - preSchwarzian f z) ∈ A21fun unitDisc := by
    have h := a21_add measurableSet_ball hGpre (a21_const_mul measurableSet_ball hpre (-1))
    refine ⟨h.1.congr fun z _ => by ring, ?_⟩
    have he : (fun z => preSchwarzian G z - preSchwarzian f z) = fun z => preSchwarzian G z + -1 * preSchwarzian f z := by
      funext z; ring
    rw [he]; exact h.2
  set I : ℂ → ℂ := fun z => deriv f z *
      ((∫ t in (0 : ℝ)..1, (schwarzianHol G (t * z) - schwarzianHol f (t * z) +
        (preSchwarzian G (t * z) - preSchwarzian f (t * z)) ^ 2 / 2) / deriv f (t * z) * z) +
        2 * ((preSchwarzian G 0 - preSchwarzian f 0) / 2)) with hIdef
  have hw : (fun z => (preSchwarzian G z - preSchwarzian f z) - I z) ∈ A21fun unitDisc := by
    have h := a21_add measurableSet_ball hδ (a21_const_mul measurableSet_ball hIA (-1))
    refine ⟨h.1.congr fun z _ => by ring, ?_⟩
    have he : (fun z => (preSchwarzian G z - preSchwarzian f z) - I z) =
        fun z => (preSchwarzian G z - preSchwarzian f z) + -1 * I z := by funext z; ring
    rw [he]; exact h.2
  have hhom : EqOn (fun z => deriv (fun z => (preSchwarzian G z - preSchwarzian f z) - I z) z -
      preSchwarzian f z * ((preSchwarzian G z - preSchwarzian f z) - I z)) 0 unitDisc := by
    intro z hz
    have hzo : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
    have dG := (hGpre.1.differentiableAt hzo).hasDerivAt
    have df := (hpre.1.differentiableAt hzo).hasDerivAt
    have dI := (hIA.1.differentiableAt hzo).hasDerivAt
    show deriv (fun z => preSchwarzian G z - preSchwarzian f z - I z) z - _ = 0
    rw [((dG.fun_sub df).fun_sub dI).deriv]
    have hSG := schwarzian_eq_Psi_preSchwarzian isOpen_ball hG hGne hz
    have hSf := schwarzian_eq_Psi_preSchwarzian isOpen_ball hf hne hz
    have he := heq hz
    simp only [PsiOp] at hSG hSf he
    rw [hSG, hSf] at he
    linear_combination -he
  have hw0 : (fun z => (preSchwarzian G z - preSchwarzian f z) - I z) 0 = 0 := by
    simp only
    linear_combination -2 * h0
  have hz := (thm_A_3_analytic hf hne hzero hpre).2.1 _ hw hhom hw0
  intro z hz'
  have := hz hz'
  simp only [Pi.zero_apply] at this
  exact sub_eq_zero.mp this

/-- Bootstrap for the quadratic remainder: if `nE ≤ A (a + b)|t| + B c nd` and `nd ≤ nE + M|t|` with `a, b, c → 0`,
then `nd = O(|t|)` and `nE = o(|t|)`. -/
theorem s35r_boot {a b c nE nd : ℂ → ℝ} {A B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : Tendsto a (𝓝[≠] 0) (𝓝 0)) (hb : Tendsto b (𝓝[≠] 0) (𝓝 0)) (hc : Tendsto c (𝓝[≠] 0) (𝓝 0))
    (hnE : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 ≤ nE t) (hnd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 ≤ nd t)
    (h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), nE t ≤ A * (a t + b t) * ‖t‖ + B * c t * nd t)
    (h2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), nd t ≤ nE t + M * ‖t‖) :
    (∀ᶠ t in 𝓝[≠] (0 : ℂ), nd t ≤ (2 * M + 1) * ‖t‖) ∧
      Tendsto (fun t => nE t / ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
  have hBc : Tendsto (fun t => B * c t) (𝓝[≠] 0) (𝓝 0) := by simpa using hc.const_mul B
  have hAab : Tendsto (fun t => A * (a t + b t)) (𝓝[≠] 0) (𝓝 0) := by simpa using (ha.add hb).const_mul A
  have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), B * c t < 1 / 2 := hBc.eventually (gt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), A * (a t + b t) < 1 / 2 := hAab.eventually (gt_mem_nhds (by norm_num))
  have hnt : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < ‖t‖ := eventually_mem_nhdsWithin.mono fun t ht => norm_pos_iff.mpr ht
  have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), nd t ≤ (2 * M + 1) * ‖t‖ := by
    filter_upwards [e1, e2, hnd, h1, h2, hnt] with t e1 e2 hnd h1 h2 hnt
    have h3 : nd t * (1 - B * c t) ≤ (A * (a t + b t) + M) * ‖t‖ := by nlinarith
    have h4 : nd t ≤ 2 * (nd t * (1 - B * c t)) := by nlinarith
    nlinarith
  refine ⟨hbd, ?_⟩
  have hu : Tendsto (fun t => A * (a t + b t) + B * |c t| * (2 * M + 1)) (𝓝[≠] 0) (𝓝 0) := by
    have h := hAab.add ((hc.abs.const_mul B).mul_const (2 * M + 1))
    simpa using h
  apply squeeze_zero' _ _ hu
  · filter_upwards [hnE, hnt] with t h1 h2
    exact div_nonneg h1 h2.le
  · filter_upwards [h1, hbd, hnd, hnt] with t h1 hbd hnd hnt
    rw [div_le_iff₀ hnt]
    have h6 : c t * nd t ≤ |c t| * ((2 * M + 1) * ‖t‖) :=
      calc c t * nd t ≤ |c t| * nd t := mul_le_mul_of_nonneg_right (le_abs_self _) hnd
        _ ≤ |c t| * ((2 * M + 1) * ‖t‖) := mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
    have h5 : B * c t * nd t ≤ B * |c t| * ((2 * M + 1) * ‖t‖) := by
      calc B * c t * nd t = B * (c t * nd t) := by ring
        _ ≤ B * (|c t| * ((2 * M + 1) * ‖t‖)) := mul_le_mul_of_nonneg_left h6 hB
        _ = B * |c t| * ((2 * M + 1) * ‖t‖) := by ring
    nlinarith

/-- `(I^{1/2})/|t| = (I/|t|²)^{1/2}` for the real parts. -/
theorem s35r_ratio (I : ℝ≥0∞) {t : ℂ} (ht : t ≠ 0) :
    (I ^ (1 / 2 : ℝ)).toReal / ‖t‖ = ((I / ‖t‖ₑ ^ 2) ^ (1 / 2 : ℝ)).toReal := by
  have hte : ‖t‖ₑ ≠ 0 := enorm_ne_zero.mpr ht
  rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.toReal_div, toReal_enorm]

/-- Triangle inequality in `A₂¹(𝔻)` for `E + t D₁ + t̄ D₂`. -/
theorem s35r_A21_tri {E D₁ D₂ : ℂ → ℂ} (hE : E ∈ A21fun unitDisc) (hD₁ : D₁ ∈ A21fun unitDisc)
    (hD₂ : D₂ ∈ A21fun unitDisc) (t : ℂ) :
    (normA21 unitDisc (fun z => E z + t * D₁ z + conj t * D₂ z)).toReal ≤
      (normA21 unitDisc E).toReal + ‖t‖ * ((normA21 unitDisc D₁).toReal + (normA21 unitDisc D₂).toReal) := by
  have hm (g : ℂ → ℂ) (hg : g ∈ A21fun unitDisc) : AEStronglyMeasurable g (volume.restrict unitDisc) :=
    hg.1.continuousOn.aestronglyMeasurable measurableSet_ball
  have hf : (fun z => E z + t * D₁ z + conj t * D₂ z) = E + t • D₁ + (conj t) • D₂ := by
    funext z; simp [smul_eq_mul]
  have hfE := (a21_memLp_two (D := unitDisc) measurableSet_ball hE).eLpNorm_lt_top
  have hf1 := (a21_memLp_two (D := unitDisc) measurableSet_ball hD₁).eLpNorm_lt_top
  have hf2 := (a21_memLp_two (D := unitDisc) measurableSet_ball hD₂).eLpNorm_lt_top
  have hsum : (fun z => E z + t * D₁ z + conj t * D₂ z) ∈ A21fun unitDisc := by
    have h := a21_add measurableSet_ball (a21_add measurableSet_ball hE (a21_const_mul measurableSet_ball hD₁ t))
      (a21_const_mul measurableSet_ball hD₂ (conj t))
    exact h
  rw [AppB.normA21_eq_eLpNorm (hm _ hsum), AppB.normA21_eq_eLpNorm (hm _ hE), AppB.normA21_eq_eLpNorm (hm _ hD₁),
    AppB.normA21_eq_eLpNorm (hm _ hD₂), hf]
  have hle : eLpNorm (E + t • D₁ + (conj t) • D₂) 2 (volume.restrict unitDisc) ≤
      eLpNorm E 2 (volume.restrict unitDisc) + ‖t‖ₑ * eLpNorm D₁ 2 (volume.restrict unitDisc) +
        ‖t‖ₑ * eLpNorm D₂ 2 (volume.restrict unitDisc) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    have hcj : ‖conj t‖ₑ = ‖t‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]
    rw [eLpNorm_const_smul, hcj]
    gcongr
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_const_smul]
  have hfin : eLpNorm E 2 (volume.restrict unitDisc) + ‖t‖ₑ * eLpNorm D₁ 2 (volume.restrict unitDisc) +
      ‖t‖ₑ * eLpNorm D₂ 2 (volume.restrict unitDisc) ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfE.ne, ENNReal.mul_ne_top enorm_ne_top hf1.ne⟩,
      ENNReal.mul_ne_top enorm_ne_top hf2.ne⟩
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfE.ne, ENNReal.mul_ne_top enorm_ne_top hf1.ne⟩)
      (ENNReal.mul_ne_top enorm_ne_top hf2.ne), ENNReal.toReal_add hfE.ne (ENNReal.mul_ne_top enorm_ne_top hf1.ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm]
  ring

/-- One step of the Riccati linearization at a fixed parameter `t`: the remainder `E = δ - t D₁ - t̄ D₂` is the
explicit inverse of `(r + δ²/2, e/2)`, hence bounded in `A₂¹(𝔻)` and pointwise; and `δ` is controlled by `E`. -/
theorem s35r_step {f G σ₁ σ₂ : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hpre : preSchwarzian f ∈ A21fun unitDisc)
    (hG : DifferentiableOn ℂ G unitDisc) (hGne : ∀ z ∈ unitDisc, deriv G z ≠ 0)
    (hGpre : preSchwarzian G ∈ A21fun unitDisc) (hσ₁ : σ₁ ∈ A2fun unitDisc) (hσ₂ : σ₂ ∈ A2fun unitDisc)
    {C : ℝ≥0∞} (hC : C < ∞) (hCb : ∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      normA21 unitDisc (fun z => deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)) ≤
        C * (normA2 unitDisc ϕ + ‖c‖ₑ))
    {Cz : ℂ → ℝ} (hpt : ∀ z ∈ unitDisc, ∀ ϕ ∈ A2fun unitDisc, ∀ c : ℂ,
      ‖deriv f z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv f (t * z) * z) + 2 * c)‖ ≤
        Cz z * ((normA2 unitDisc ϕ).toReal + ‖c‖))
    (hCz0 : ∀ z ∈ unitDisc, 0 ≤ Cz z) (t p₁ p₂ : ℂ)
    (hr : (fun z => schwarzianHol G z - schwarzianHol f z - t * σ₁ z - conj t * σ₂ z) ∈ A2fun unitDisc) :
    (∀ z ∈ unitDisc, ‖(preSchwarzian G z - preSchwarzian f z) -
        t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv f (s * z) * z) + 2 * (p₁ / 2))) -
        conj t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv f (s * z) * z) + 2 * (p₂ / 2)))‖ ≤
      Cz z * ((normA2 unitDisc (fun z => schwarzianHol G z - schwarzianHol f z - t * σ₁ z - conj t * σ₂ z)).toReal +
        1 / (2 * Real.sqrt π) / 2 * (normA21 unitDisc (fun z => preSchwarzian G z - preSchwarzian f z)).toReal ^ 2 +
        ‖preSchwarzian G 0 - preSchwarzian f 0 - t * p₁ - conj t * p₂‖ / 2)) ∧
    (normA21 unitDisc (fun z => (preSchwarzian G z - preSchwarzian f z) -
        t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv f (s * z) * z) + 2 * (p₁ / 2))) -
        conj t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv f (s * z) * z) + 2 * (p₂ / 2))))).toReal ≤
      C.toReal * ((normA2 unitDisc (fun z => schwarzianHol G z - schwarzianHol f z - t * σ₁ z - conj t * σ₂ z)).toReal +
        1 / (2 * Real.sqrt π) / 2 * (normA21 unitDisc (fun z => preSchwarzian G z - preSchwarzian f z)).toReal ^ 2 +
        ‖preSchwarzian G 0 - preSchwarzian f 0 - t * p₁ - conj t * p₂‖ / 2) ∧
    (fun z => (preSchwarzian G z - preSchwarzian f z) -
        t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv f (s * z) * z) + 2 * (p₁ / 2))) -
        conj t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv f (s * z) * z) + 2 * (p₂ / 2)))) ∈
      A21fun unitDisc ∧
    (fun z => preSchwarzian G z - preSchwarzian f z) ∈ A21fun unitDisc := by
  -- the pieces
  set δ : ℂ → ℂ := fun z => preSchwarzian G z - preSchwarzian f z with hδdef
  set r : ℂ → ℂ := fun z => schwarzianHol G z - schwarzianHol f z - t * σ₁ z - conj t * σ₂ z with hrdef
  set e : ℂ := preSchwarzian G 0 - preSchwarzian f 0 - t * p₁ - conj t * p₂ with hedef
  have hδ : δ ∈ A21fun unitDisc := by
    have h := a21_add measurableSet_ball hGpre (a21_const_mul measurableSet_ball hpre (-1))
    have he : δ = fun z => preSchwarzian G z + -1 * preSchwarzian f z := by funext z; simp [hδdef]; ring
    rw [he]; exact h
  -- `δ²/2 ∈ A₂`, with its bound
  obtain ⟨hsqA, hsqN⟩ := A21_product_bounded (Or.inl rfl) hδ hδ
  have hq : (fun z => (1 / 2 : ℂ) * (δ z * δ z)) ∈ A2fun unitDisc := s35r_A2_smul hsqA (1 / 2)
  obtain ⟨hΦA, hΦN⟩ := s35r_A2_add hr hq
  have hΦe : (fun z => r z + (1 / 2 : ℂ) * (δ z * δ z)) = fun z => r z + δ z ^ 2 / 2 := by funext z; ring
  -- `ΔS + δ²/2 ∈ A₂`
  have hψA : (fun z => schwarzianHol G z - schwarzianHol f z + (preSchwarzian G z - preSchwarzian f z) ^ 2 / 2) ∈
      A2fun unitDisc := by
    obtain ⟨h1, -⟩ := s35r_A2_add hΦA (s35r_A2_add (s35r_A2_smul hσ₁ t) (s35r_A2_smul hσ₂ (conj t))).1
    have he : (fun z => (r z + (1 / 2 : ℂ) * (δ z * δ z)) + (t * σ₁ z + conj t * σ₂ z)) =
        fun z => schwarzianHol G z - schwarzianHol f z + (preSchwarzian G z - preSchwarzian f z) ^ 2 / 2 := by
      funext z; simp only [hrdef, hδdef]; ring
    rw [← he]; exact h1
  have hrep := s35r_rep hf hne hzero hpre hG hGne hGpre hψA
  -- the remainder is the inverse of `(r + δ²/2, e/2)`
  have hE : EqOn (fun z => δ z -
        t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv f (s * z) * z) + 2 * (p₁ / 2))) -
        conj t * (deriv f z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv f (s * z) * z) + 2 * (p₂ / 2))))
      (fun z => deriv f z * ((∫ s in (0 : ℝ)..1, (fun w => r w + (1 / 2 : ℂ) * (δ w * δ w)) (s * z) /
        deriv f (s * z) * z) + 2 * (e / 2))) unitDisc := by
    intro z hz
    have h1 := hrep hz
    simp only at h1
    simp only
    rw [show δ z = preSchwarzian G z - preSchwarzian f z from rfl, h1,
      s35r_inv_lin hf hne hψA.1 hσ₁.1 hσ₂.1 _ _ _ t hz]
    congr 2
    · apply intervalIntegral.integral_congr
      intro s _
      simp only [hrdef, hδdef]
      ring
    · simp only [hedef]; ring
  have hEA := (thm_A_3_analytic hf hne hzero hpre).1 _ hΦA (e / 2)
  -- the `A₂` norm of the source
  have hsrc : (normA2 unitDisc (fun z => r z + (1 / 2 : ℂ) * (δ z * δ z))).toReal ≤
      (normA2 unitDisc r).toReal + 1 / (2 * Real.sqrt π) / 2 * (normA21 unitDisc δ).toReal ^ 2 := by
    have hδf := (a21_memLp_two (D := unitDisc) measurableSet_ball hδ).eLpNorm_lt_top
    have hδn : normA21 unitDisc δ ≠ ∞ := by
      rw [AppB.normA21_eq_eLpNorm (hδ.1.continuousOn.aestronglyMeasurable measurableSet_ball)]; exact hδf.ne
    have hqle : normA2 unitDisc (fun z => (1 / 2 : ℂ) * (δ z * δ z)) ≤
        ENNReal.ofReal (1 / (2 * Real.sqrt π) / 2) * normA21 unitDisc δ * normA21 unitDisc δ := by
      rw [normA2_const_mul]
      calc (‖(1 / 2 : ℂ)‖₊ : ℝ≥0∞) * normA2 unitDisc (fun z => δ z * δ z)
          ≤ (‖(1 / 2 : ℂ)‖₊ : ℝ≥0∞) * (ENNReal.ofReal (1 / (2 * Real.sqrt π)) * normA21 unitDisc δ *
              normA21 unitDisc δ) := by gcongr
        _ = ENNReal.ofReal (1 / (2 * Real.sqrt π) / 2) * normA21 unitDisc δ * normA21 unitDisc δ := by
          have : (‖(1 / 2 : ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
            rw [show ((‖(1 / 2 : ℂ)‖₊ : ℝ≥0∞)) = ‖(1 / 2 : ℂ)‖ₑ from rfl, ← ofReal_norm_eq_enorm]; norm_num
          rw [this, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          congr 3
          ring
    have hfin : ENNReal.ofReal (1 / (2 * Real.sqrt π) / 2) * normA21 unitDisc δ * normA21 unitDisc δ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδn) hδn
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hr.2.ne, hfin⟩) (hΦN.trans (add_le_add le_rfl hqle))
    rw [ENNReal.toReal_add hr.2.ne hfin, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  refine ⟨?_, ?_, ?_, hδ⟩
  · intro z hz
    rw [show (preSchwarzian G z - preSchwarzian f z) = δ z from rfl]
    have hb := hpt z hz _ hΦA (e / 2)
    have he2 : ‖e / 2‖ = ‖e‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
    refine (le_of_eq (congrArg norm (hE hz))).trans ?_
    refine hb.trans ?_
    rw [he2]
    exact mul_le_mul_of_nonneg_left (by linarith [hsrc]) (hCz0 z hz)
  · have hn := hCb _ hΦA (e / 2)
    have hEq := normA21_congr_on (U := unitDisc) measurableSet_ball hE
    have hfin : C * (normA2 unitDisc (fun z => r z + (1 / 2 : ℂ) * (δ z * δ z)) + ‖e / 2‖ₑ) ≠ ∞ :=
      ENNReal.mul_ne_top hC.ne (ENNReal.add_ne_top.mpr ⟨hΦA.2.ne, enorm_ne_top⟩)
    refine (ENNReal.toReal_mono hfin (hEq.le.trans hn)).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hΦA.2.ne enorm_ne_top, toReal_enorm, norm_div, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (by linarith [hsrc]) ENNReal.toReal_nonneg
  · exact (mem_A21fun_iff_memLp measurableSet_ball).mpr
      ⟨(hEA.1.1).congr fun z hz => hE hz,
        ((mem_A21fun_iff_memLp measurableSet_ball).mp hEA.1).2.ae_eq
          ((ae_restrict_mem measurableSet_ball).mono fun z hz => (hE hz).symm)⟩

/-- **(R)** Riccati linearization. Let `F_t` be locally univalent on `𝔻` with `𝒜(F_t) ∈ A₂¹(𝔻)` near `t = 0` and
`F_0'(0) = 1`. If `𝒮(F_t) = 𝒮(F_0) + t σ + t̄ σ' + o(t)` in `A₂(𝔻)`, `t ↦ 𝒜(F_t)(0)` is real differentiable at `0`, and
`𝒜(F_t) → 𝒜(F_0)` in `A₂¹(𝔻)`, then `𝒜(F_t)` has an `A₂¹(𝔻)` remainder expansion, with parts the pointwise
`∂_t`, `∂_t̄` (which exist). -/
theorem s35_riccati_variation {F : ℂ → ℂ → ℂ}
    (hF : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableOn ℂ (F t) unitDisc ∧ (∀ z ∈ unitDisc, deriv (F t) z ≠ 0) ∧
      preSchwarzian (F t) ∈ A21fun unitDisc)
    (h0 : deriv (F 0) 0 = 1) {σ₁ σ₂ : ℂ → ℂ} (hσ₁ : σ₁ ∈ A2fun unitDisc) (hσ₂ : σ₂ ∈ A2fun unitDisc)
    (hS : Tendsto (fun t : ℂ => (∫⁻ z in unitDisc, ‖schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z -
      conj t * σ₂ z‖ₑ ^ 2 * ENNReal.ofReal (rho z)⁻¹) / ‖t‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0))
    (hP : DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (F t) 0) 0)
    (hc : Tendsto (fun t : ℂ => ∫⁻ z in unitDisc, ‖preSchwarzian (F t) z - preSchwarzian (F 0) z‖ₑ ^ 2)
      (𝓝 0) (𝓝 0)) :
    (∀ z ∈ unitDisc, DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (F t) z) 0) ∧
      MemLp (fun z => dz (fun t : ℂ => preSchwarzian (F t) z) 0) 2 (volume.restrict unitDisc) ∧
      MemLp (fun z => dzbar (fun t : ℂ => preSchwarzian (F t) z) 0) 2 (volume.restrict unitDisc) ∧
      Tendsto (fun t : ℂ => (∫⁻ z in unitDisc, ‖preSchwarzian (F t) z - preSchwarzian (F 0) z -
        t * dz (fun s : ℂ => preSchwarzian (F s) z) 0 - conj t * dzbar (fun s : ℂ => preSchwarzian (F s) z) 0‖ₑ ^ 2) /
          ‖t‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨hf, hfne, hfpre⟩ := hF.self_of_nhds
  obtain ⟨C, hC, hCb⟩ := s35_winv hf hfne h0 hfpre
  have hptex : ∀ z ∈ unitDisc, ∃ c : ℝ, 0 ≤ c ∧ ∀ ϕ ∈ A2fun unitDisc, ∀ c' : ℂ,
      ‖deriv (F 0) z * ((∫ t in (0 : ℝ)..1, ϕ (t * z) / deriv (F 0) (t * z) * z) + 2 * c')‖ ≤
        c * ((normA2 unitDisc ϕ).toReal + ‖c'‖) := fun z hz => s35r_inv_pt hf hfne hz
  choose! Cz hCz0 hpt using hptex
  obtain ⟨p₁, hp₁⟩ : ∃ p, p = dz (fun t : ℂ => preSchwarzian (F t) 0) 0 := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p, p = dzbar (fun t : ℂ => preSchwarzian (F t) 0) 0 := ⟨_, rfl⟩
  set D₁ : ℂ → ℂ := fun z => deriv (F 0) z * ((∫ s in (0 : ℝ)..1, σ₁ (s * z) / deriv (F 0) (s * z) * z) +
    2 * (p₁ / 2)) with hD₁
  set D₂ : ℂ → ℂ := fun z => deriv (F 0) z * ((∫ s in (0 : ℝ)..1, σ₂ (s * z) / deriv (F 0) (s * z) * z) +
    2 * (p₂ / 2)) with hD₂
  have hD₁A : D₁ ∈ A21fun unitDisc := ((thm_A_3_analytic hf hfne h0 hfpre).1 σ₁ hσ₁ (p₁ / 2)).1
  have hD₂A : D₂ ∈ A21fun unitDisc := ((thm_A_3_analytic hf hfne h0 hfpre).1 σ₂ hσ₂ (p₂ / 2)).1
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = (normA21 unitDisc D₁).toReal + (normA21 unitDisc D₂).toReal := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMd]; positivity
  -- the remainder of `𝒮` is in `A₂` for small `t ≠ 0`
  have hFw : ∀ᶠ t in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (F t) unitDisc ∧ (∀ z ∈ unitDisc, deriv (F t) z ≠ 0) ∧
      preSchwarzian (F t) ∈ A21fun unitDisc := nhdsWithin_le_nhds hF
  have hShol : ∀ G : ℂ → ℂ, preSchwarzian G ∈ A21fun unitDisc → DifferentiableOn ℂ (schwarzianHol G) unitDisc := by
    intro G hG
    exact ((hG.1.deriv isOpen_ball).sub ((hG.1.pow 2).const_mul (1 / 2))).congr fun z _ => rfl
  have hrA : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z) ∈ A2fun unitDisc := by
    filter_upwards [hFw, hS.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num)), eventually_mem_nhdsWithin]
      with t ht hlt htn
    refine ⟨(((hShol _ ht.2.2).sub (hShol _ hfpre)).sub (hσ₁.1.const_mul t)).sub (hσ₂.1.const_mul (conj t)), ?_⟩
    have hte : ‖t‖ₑ ^ 2 ≠ 0 := pow_ne_zero 2 (enorm_ne_zero.mpr htn)
    have hI := (ENNReal.div_lt_iff (Or.inl hte) (Or.inl (ENNReal.pow_ne_top enorm_ne_top))).mp hlt
    rw [one_mul] at hI
    unfold normA2
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hI.trans (ENNReal.pow_lt_top enorm_lt_top)).ne
  have hstep := fun t (ht : DifferentiableOn ℂ (F t) unitDisc ∧ (∀ z ∈ unitDisc, deriv (F t) z ≠ 0) ∧
      preSchwarzian (F t) ∈ A21fun unitDisc) hr =>
    s35r_step hf hfne h0 hfpre ht.1 ht.2.1 ht.2.2 hσ₁ hσ₂ hC hCb hpt hCz0 t p₁ p₂ hr
  -- the three small quantities
  have ha : Tendsto (fun t : ℂ =>
      (normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal /
        ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hS
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    apply ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).congr'
    filter_upwards [eventually_mem_nhdsWithin] with t htn
    exact (s35r_ratio _ htn).symm
  have hb : Tendsto (fun t : ℂ => ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / ‖t‖)
      (𝓝[≠] 0) (𝓝 0) := by
    have h := (hasFDerivAt_iff_tendsto.mp hP.hasFDerivAt)
    simp only [sub_zero] at h
    apply (h.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [] with t
    rw [fderiv_eq_dz_dzbar hP t, ← hp₁, ← hp₂, div_eq_inv_mul]
    congr 2
    ring
  have hcl : Tendsto (fun t : ℂ => (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal)
      (𝓝[≠] 0) (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hc
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).mono_left nhdsWithin_le_nhds
  -- the bootstrap
  set E : ℂ → ℂ → ℂ := fun t z => (preSchwarzian (F t) z - preSchwarzian (F 0) z) - t * D₁ z - conj t * D₂ z
    with hEdef
  have hh1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (normA21 unitDisc (E t)).toReal ≤ C.toReal * ((normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal / ‖t‖ + ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / ‖t‖) * ‖t‖ + C.toReal * (1 / (2 * Real.sqrt π) / 2) * (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal * (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal := by
    filter_upwards [hFw, hrA, eventually_mem_nhdsWithin] with t ht hr htn
    have hpos : 0 < ‖t‖ := norm_pos_iff.mpr htn
    obtain ⟨-, hn, -, -⟩ := hstep t ht hr
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    have e : C.toReal * ((normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal / ‖t‖ + ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / ‖t‖) * ‖t‖ = C.toReal * ((normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal + ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖) := by
      field_simp
    rw [e]
    refine hn.trans ?_
    have hY := mul_nonneg hC0 (norm_nonneg (preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂))
    nlinarith [hY]
  have hh2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal ≤ (normA21 unitDisc (E t)).toReal + M * ‖t‖ := by
    filter_upwards [hFw, hrA] with t ht hr
    obtain ⟨-, -, hEA, -⟩ := hstep t ht hr
    have htri := s35r_A21_tri hEA hD₁A hD₂A t
    have he : (fun z => (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z - t * D₁ z - conj t * D₂ z) z +
        t * D₁ z + conj t * D₂ z) = fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z := by
      funext z; ring
    rw [he] at htri
    rw [hMd]
    refine htri.trans (le_of_eq ?_)
    rw [mul_comm ‖t‖]
  obtain ⟨hbd, hlim⟩ := s35r_boot (A := C.toReal) (B := C.toReal * (1 / (2 * Real.sqrt π) / 2))
    (nE := fun t => (normA21 unitDisc (E t)).toReal)
    (nd := fun t => (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal)
    (by positivity) hM ha hb hcl (Eventually.of_forall fun t => ENNReal.toReal_nonneg)
    (Eventually.of_forall fun t => ENNReal.toReal_nonneg) hh1 hh2
  -- pointwise expansion
  have hpw : ∀ z ∈ unitDisc, HasFDerivAt (fun t : ℂ => preSchwarzian (F t) z)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight (D₁ z) +
        (Complex.conjCLE.toContinuousLinearMap).smulRight (D₂ z)) 0 := by
    intro z hz
    apply s35r_hasFDeriv (R := fun t => Cz z * (
      (normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal /
        ‖t‖ + 1 / (2 * Real.sqrt π) / 2 * (2 * M + 1) *
          (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal +
        ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / ‖t‖ / 2))
    · have h := ((ha.add ((hcl.const_mul (1 / (2 * Real.sqrt π) / 2 * (2 * M + 1)))) ).add
        (hb.div_const 2)).const_mul (Cz z)
      simpa using h
    · filter_upwards [hFw, hrA, hbd, eventually_mem_nhdsWithin] with t ht hr hbd htn
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr htn
      obtain ⟨hpt', -, -, -⟩ := hstep t ht hr
      have hz' := hpt' z hz
      refine hz'.trans ?_
      have hnd0 : 0 ≤ (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal :=
        ENNReal.toReal_nonneg
      have hsq : (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal ^ 2 ≤
          (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal *
            ((2 * M + 1) * ‖t‖) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hbd hnd0
      have hK0 : 0 ≤ 1 / (2 * Real.sqrt π) / 2 := by positivity
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hCz0 z hz)
      have e : ((normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal / ‖t‖ + 1 / (2 * Real.sqrt π) / 2 * (2 * M + 1) * (normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal + ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / ‖t‖ / 2) * ‖t‖ =
          (normA2 unitDisc (fun z => schwarzianHol (F t) z - schwarzianHol (F 0) z - t * σ₁ z - conj t * σ₂ z)).toReal + 1 / (2 * Real.sqrt π) / 2 * ((normA21 unitDisc (fun z => preSchwarzian (F t) z - preSchwarzian (F 0) z)).toReal * ((2 * M + 1) * ‖t‖)) + ‖preSchwarzian (F t) 0 - preSchwarzian (F 0) 0 - t * p₁ - conj t * p₂‖ / 2 := by
        field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hsq hK0]
  have hdz : ∀ z ∈ unitDisc, dz (fun t : ℂ => preSchwarzian (F t) z) 0 = D₁ z ∧
      dzbar (fun t : ℂ => preSchwarzian (F t) z) 0 = D₂ z := fun z hz => s35r_lin_dz (hpw z hz)
  refine ⟨fun z hz => (hpw z hz).differentiableAt, ?_, ?_, ?_⟩
  · exact (a21_memLp_two (D := unitDisc) measurableSet_ball hD₁A).ae_eq
      ((ae_restrict_mem measurableSet_ball).mono fun z hz => (hdz z hz).1.symm)
  · exact (a21_memLp_two (D := unitDisc) measurableSet_ball hD₂A).ae_eq
      ((ae_restrict_mem measurableSet_ball).mono fun z hz => (hdz z hz).2.symm)
  · -- the `A₂¹` remainder
    have hsq : Tendsto (fun t : ℂ => ENNReal.ofReal (((normA21 unitDisc (E t)).toReal / ‖t‖) ^ 2)) (𝓝[≠] 0)
        (𝓝 0) := by
      have h2 := hlim.pow 2
      rw [zero_pow two_ne_zero] at h2
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp h2
      rw [ENNReal.ofReal_zero] at h
      exact h
    apply hsq.congr'
    filter_upwards [hFw, hrA, eventually_mem_nhdsWithin] with t ht hr htn
    obtain ⟨-, -, hEA, -⟩ := hstep t ht hr
    have hint : (∫⁻ z in unitDisc, ‖preSchwarzian (F t) z - preSchwarzian (F 0) z -
        t * dz (fun s : ℂ => preSchwarzian (F s) z) 0 - conj t * dzbar (fun s : ℂ => preSchwarzian (F s) z) 0‖ₑ ^ 2) =
        normA21 unitDisc (E t) ^ 2 := by
      have hcg : (∫⁻ z in unitDisc, ‖preSchwarzian (F t) z - preSchwarzian (F 0) z -
          t * dz (fun s : ℂ => preSchwarzian (F s) z) 0 - conj t * dzbar (fun s : ℂ => preSchwarzian (F s) z) 0‖ₑ ^ 2) =
          ∫⁻ z in unitDisc, ‖E t z‖ₑ ^ 2 :=
        setLIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
          (fun z hz => by simp only [hEdef, (hdz z hz).1, (hdz z hz).2])
      rw [hcg]
      unfold normA21
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
      rfl
    have hfin : normA21 unitDisc (E t) ≠ ∞ := by
      rw [AppB.normA21_eq_eLpNorm (hEA.1.continuousOn.aestronglyMeasurable measurableSet_ball)]
      exact (a21_memLp_two (D := unitDisc) measurableSet_ball hEA).eLpNorm_lt_top.ne
    have htn' : 0 < ‖t‖ := norm_pos_iff.mpr htn
    rw [hint, ← ENNReal.ofReal_toReal hfin, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_div_of_pos (by positivity), div_pow,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-- The kernel `z ↦ K_A(z, w)` of an HS matrix is holomorphic on `𝔻`. -/
theorem s35a_eval_diff (A : s3tc_HS) {w : ℂ} :
    DifferentiableOn ℂ (fun z => s3kv_eval z w A) unitDisc := by
  set x : ell2 := s3tc_toOperator A (s3kv_vector w) with hx
  apply differentiableOn_of_powerSeries (c := fun n => x n * (Real.sqrt ((n + 1 : ℝ) / π) : ℂ))
  intro z hz
  have hs : Summable (fun n => x n * basisE n z) := by
    refine Summable.of_norm_bounded ((basisE_norm_summable hz).mul_left ‖x‖) fun n => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n) (norm_nonneg _)
  have he : s3kv_eval z w A = ∑' n, x n * basisE n z := by
    rw [s3kv_eval_apply, s3kv_kernel_series _ hz w]
  rw [he]
  refine hs.hasSum.congr_fun fun n => ?_
  simp only [basisE]
  ring

/-- `𝒮(𝖿_ν)(z) = -6π K₁(z, z) = -6π ⟨B₁⟩(z, z)`: the interior Schwarzian is the diagonal of the Grunsky kernel. -/
theorem s35a_schw_eval {ν : LinfStar} (hν : ν ∈ LinfStarBall) {A : s3tc_HS}
    (hA : ∀ q : ℕ × ℕ, A q = B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2) {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzianHol (fsans ν) z = -(6 * π) * s3kv_eval z z A := by
  obtain ⟨hfd, hfi, -⟩ := s2c_facts hν
  have hop : s3tc_toOperator A = gopOp (B1 (grunsky (fsans ν) (gsans ν))) := by
    rw [s3tc_toOperator_apply]
    congr 1
    funext m n
    exact hA (m, n)
  have hoff : ∀ᶠ u in 𝓝[≠] z, s3kv_eval u z A = kerK1 (fsans ν) u z := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), eventually_mem_nhdsWithin] with u hu hne
    rw [s3kv_eval_apply, hop]
    exact s3kv_B1_kernel hν hu hz hne
  have h1 : Tendsto (fun u => s3kv_eval u z A) (𝓝[≠] z) (𝓝 (s3kv_eval z z A)) :=
    (((s35a_eval_diff A).continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto).mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun u => kerK1 (fsans ν) u z) (𝓝[≠] z) (𝓝 (kerK1 (fsans ν) z z)) :=
    (((AppB.differentiableOn_kerK1 isOpen_ball hfd hfi hz).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hz)).tendsto).mono_left nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique (h1.congr' hoff) h2
  rw [heq, kerK1_diag]
  field_simp

/-- `∫_𝔻 |c · K_A(z,z)|² ρ⁻¹` as a lintegral, bounded through `s3dl_diagonal_bound`. -/
theorem s35a_diag_lint (A : s3tc_HS) (c : ℂ) :
    (∫⁻ z in unitDisc, ‖c * s3kv_eval z z A‖ₑ ^ 2 * ENNReal.ofReal (rho z)⁻¹) ≤
      ENNReal.ofReal (‖c‖ ^ 2 * (‖A‖ ^ 2 / (2 * π))) := by
  obtain ⟨hint, hle⟩ := s3dl_diagonal_bound A
  have hnn : ∀ z, 0 ≤ ‖s3kv_eval z z A‖ ^ 2 * (rho z)⁻¹ := fun z => by unfold rho; positivity
  have he : (fun z => ‖c * s3kv_eval z z A‖ₑ ^ 2 * ENNReal.ofReal (rho z)⁻¹) =
      fun z => ENNReal.ofReal (‖c‖ ^ 2 * (‖s3kv_eval z z A‖ ^ 2 * (rho z)⁻¹)) := by
    funext z
    have hr : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      norm_mul]
    congr 1
    ring
  rw [he, ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hnn z)), integral_const_mul]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (sq_nonneg _))

/-- **(A), Schwarzian input.** Along the off-centre line, `𝒮(𝖿_t)` has an `A₂(𝔻)` remainder expansion
(holomorphic in `t`): `σ₁ = -6π ⟨Ḃ₁⟩(z,z)`, `σ₂ = 0`. -/
theorem s35a_hS {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    ∃ σ₁ : ℂ → ℂ, σ₁ ∈ A2fun unitDisc ∧
      Tendsto (fun t : ℂ => (∫⁻ z in unitDisc, ‖schwarzianHol (fsans (beltramiMul (a + t • toLinf m) κ)) z -
        schwarzianHol (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) z - t * σ₁ z -
        conj t * (fun _ : ℂ => (0 : ℂ)) z‖ₑ ^ 2 * ENNReal.ofReal (rho z)⁻¹) / ‖t‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨F, d, hev, hFd, -⟩ := s4g_off_chart_data hκ ha has haL hm
  refine ⟨fun z => -(6 * π) * s3kv_eval z z d, s35r_A2_smul (s3dl_diagonal_A2 d) _, ?_⟩
  obtain ⟨hb0, hF0⟩ := hev.self_of_nhds
  have hlim := hasDerivAt_iff_tendsto.mp hFd
  simp only [sub_zero] at hlim
  have hsq : Tendsto (fun t : ℂ => ENNReal.ofReal (‖-(6 * π : ℂ)‖ ^ 2 / (2 * π) *
      (‖t‖⁻¹ * ‖F t - F 0 - t • d‖) ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    have h := ((hlim.pow 2).const_mul (‖-(6 * π : ℂ)‖ ^ 2 / (2 * π))).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    rw [zero_pow two_ne_zero, mul_zero] at h
    have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h'
    exact h'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq (Eventually.of_forall fun _ => zero_le)
  filter_upwards [nhdsWithin_le_nhds hev, eventually_mem_nhdsWithin] with t ht htn
  obtain ⟨hbt, hFt⟩ := ht
  have hpos : 0 < ‖t‖ := norm_pos_iff.mpr htn
  have hpt : ∀ z ∈ unitDisc, schwarzianHol (fsans (beltramiMul (a + t • toLinf m) κ)) z -
      schwarzianHol (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) z -
      t * (fun z => -(6 * π) * s3kv_eval z z d) z - conj t * (fun _ : ℂ => (0 : ℂ)) z =
      -(6 * π) * s3kv_eval z z (F t - F 0 - t • d) := by
    intro z hz
    rw [s35a_schw_eval hbt hFt hz, s35a_schw_eval hb0 hF0 hz, map_sub, map_sub, map_smul, smul_eq_mul]
    simp only [mul_zero, sub_zero]
    ring
  have hcg : (∫⁻ z in unitDisc, ‖schwarzianHol (fsans (beltramiMul (a + t • toLinf m) κ)) z -
      schwarzianHol (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) z -
      t * (fun z => -(6 * π) * s3kv_eval z z d) z - conj t * (fun _ : ℂ => (0 : ℂ)) z‖ₑ ^ 2 *
        ENNReal.ofReal (rho z)⁻¹) =
      ∫⁻ z in unitDisc, ‖-(6 * π : ℂ) * s3kv_eval z z (F t - F 0 - t • d)‖ₑ ^ 2 * ENNReal.ofReal (rho z)⁻¹ :=
    setLIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball) fun z hz => by rw [hpt z hz]
  rw [hcg]
  have hb := s35a_diag_lint (F t - F 0 - t • d) (-(6 * π : ℂ))
  have hte : ‖t‖ₑ ^ 2 = ENNReal.ofReal (‖t‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hte]
  refine (ENNReal.div_le_div_right hb _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- Near `t = 0` the off-centre line stays in the ball and in `T₀(1)`; the interior maps are locally univalent with
`A₂¹` pre-Schwarzian. -/
theorem s35a_hF {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableOn ℂ (fsans (beltramiMul (a + t • toLinf m) κ)) unitDisc ∧
      (∀ z ∈ unitDisc, deriv (fsans (beltramiMul (a + t • toLinf m) κ)) z ≠ 0) ∧
      preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) ∈ A21fun unitDisc := by
  have hd := delta0_bounds
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hcont : Continuous (fun t : ℂ => a + t • toLinf m) := continuous_const.add (continuous_id.smul continuous_const)
  have h0 : a + (0 : ℂ) • toLinf m ∈ LinfStarBall := by rw [zero_smul, add_zero]; exact ha1
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), a + t • toLinf m ∈ LinfStarBall :=
    hcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0)
  have hle : ∀ᶠ t in 𝓝 (0 : ℂ), ‖t‖ ≤ 1 :=
    (continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)).mono fun t h => h.le
  filter_upwards [hball, hle] with t ht hle
  have hL : normL2 unitDiscExterior ⇑(a + t • toLinf m) < ∞ :=
    (s4g_normL2_line a hm hle).trans_lt (ENNReal.add_lt_top.mpr ⟨haL, hm.choose_spec.2.2⟩)
  have hν := bg_mul_mem_ball κ.2 ht
  have hT := s4g_T01_mul κ.2 hκ ht hL
  obtain ⟨hfd, -, -, -, -, -, -, -, -, hfne⟩ := s2c_facts hν
  exact ⟨hfd, hfne, (s3pk_representative_A21 hν hT).1⟩

/-- `A₂¹(𝔻)`-continuity of `t ↦ 𝒜(𝖿_t)` at `0` (Corollary A.4 inverse, `a4_inverse`): the Schwarzians converge in
`A₂(𝔻)` (diagonal of the HS-continuous Grunsky kernel) and the values at `0` converge (`s35_wnorm`). -/
theorem s35a_hc {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    Tendsto (fun t : ℂ => ∫⁻ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z -
      preSchwarzian (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) z‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
  obtain ⟨F, d, hev, hFd, -⟩ := s4g_off_chart_data hκ ha has haL hm
  have hline := s35a_hF hκ has haL hm
  obtain ⟨hf0d, hf0ne, hf0A⟩ := hline.self_of_nhds
  obtain ⟨hb0, hF0⟩ := hev.self_of_nhds
  have h1 : deriv (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) 0 = 1 := (s2c_facts hb0).2.2.2.1
  set G : ℂ → ℂ → ℂ := fun t => fsans (beltramiMul (a + t • toLinf m) κ) with hG
  have e2 : ∀ t : ℂ, (∫⁻ z in unitDisc, ‖preSchwarzian (G t) z - preSchwarzian (G 0) z‖ₑ ^ 2) =
      normA21 unitDisc (fun z => preSchwarzian (G t) z - preSchwarzian (G 0) z) ^ 2 := by
    intro t
    unfold normA21
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    rfl
  suffices h : Tendsto (fun t => normA21 unitDisc (fun z => preSchwarzian (G t) z - preSchwarzian (G 0) z))
      (𝓝 0) (𝓝 0) by
    have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp h
    rw [zero_pow two_ne_zero] at h2
    exact h2.congr fun t => (e2 t).symm
  rw [tendsto_nhds_iff_seq_tendsto]
  intro u hu
  set ψ : ℕ → ℂ → ℂ := fun n => if DifferentiableOn ℂ (G (u n)) unitDisc ∧
      (∀ z ∈ unitDisc, deriv (G (u n)) z ≠ 0) ∧ preSchwarzian (G (u n)) ∈ A21fun unitDisc
    then preSchwarzian (G (u n)) else preSchwarzian (G 0) with hψ
  have hgood := hu.eventually (hline.and hev)
  have hψe : ∀ᶠ n in atTop, ψ n = preSchwarzian (G (u n)) := hgood.mono fun n hn => by
    simp only [hψ]; rw [if_pos hn.1]
  have hψA : ∀ n, ψ n ∈ A21fun unitDisc := by
    intro n
    simp only [hψ]
    split_ifs with h
    · exact h.2.2
    · exact hf0A
  -- the Schwarzians converge in `A₂(𝔻)`
  have hFc : Tendsto (fun n => ‖F (u n) - F 0‖) atTop (𝓝 0) := by
    have h := (hFd.continuousAt.tendsto.comp hu).sub_const (F 0)
    simpa using h.norm
  have hS : Tendsto (fun n => normA2 unitDisc (fun z => PsiOp (ψ n) z - PsiOp (preSchwarzian (G 0)) z))
      atTop (𝓝 0) := by
    have hbd : Tendsto (fun n => ENNReal.ofReal (‖-(6 * π : ℂ)‖ ^ 2 * (‖F (u n) - F 0‖ ^ 2 / (2 * π))) ^
        (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h := ((hFc.pow 2).div_const (2 * π)).const_mul (‖-(6 * π : ℂ)‖ ^ 2)
      rw [zero_pow two_ne_zero, zero_div, mul_zero] at h
      have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp h
      rw [ENNReal.ofReal_zero] at h1
      have h' := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h1
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbd (Eventually.of_forall fun _ => zero_le)
    filter_upwards [hψe, hgood] with n hn hgn
    obtain ⟨-, hbt, hFt⟩ := hgn
    rw [hn]
    have hcg : normA2 unitDisc (fun z => PsiOp (preSchwarzian (G (u n))) z - PsiOp (preSchwarzian (G 0)) z) =
        normA2 unitDisc (fun z => -(6 * π : ℂ) * s3kv_eval z z (F (u n) - F 0)) := by
      apply normA2_congr measurableSet_ball
      intro z hz
      show schwarzianHol (G (u n)) z - schwarzianHol (G 0) z = _
      rw [s35a_schw_eval hbt hFt hz, s35a_schw_eval hb0 hF0 hz]
      show _ = -(6 * π : ℂ) * s3kv_eval z z (F (u n) - F 0)
      rw [map_sub]
      ring
    rw [hcg]
    unfold normA2
    exact ENNReal.rpow_le_rpow (s35a_diag_lint _ _) (by norm_num)
  -- the values at `0` converge
  have h0 : Tendsto (fun n => ψ n 0) atTop (𝓝 (preSchwarzian (G 0) 0)) := by
    have h := ((s35_wnorm hκ ha has haL hm).1.continuousAt.tendsto).comp hu
    apply h.congr'
    filter_upwards [hψe] with n hn
    rw [hn]
    rfl
  have hinv := a4_inverse hf0d hf0ne h1 hf0A hψA hS h0
  apply hinv.congr'
  filter_upwards [hψe] with n hn
  rw [hn]
  rfl

/-- **(A)** The interior pre-Schwarzian `t ↦ 𝒜(𝖿_t)`, `𝖿_t = fsans (beltramiMul (a + t m) κ)`, has an `A₂¹(𝔻)`
remainder expansion at `t = 0` (the off-centre line of `s35_S1_offcentre_variation`). Route: (R) with `F_t = 𝖿_t`;
`𝒮(𝖿_t)|_𝔻` is the Bers image, `A₂`-differentiable along the line through the Hilbert chart transition. -/
theorem s35_f_variation {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    (∀ z ∈ unitDisc, DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0) ∧
      MemLp (fun z => dz (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
        (volume.restrict unitDisc) ∧
      MemLp (fun z => dzbar (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0) 2
        (volume.restrict unitDisc) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), MemLp (preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ))) 2
        (volume.restrict unitDisc)) ∧
      Tendsto (fun t : ℂ => (∫⁻ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z -
        preSchwarzian (fsans (beltramiMul a κ)) z -
        t * dz (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0 -
        conj t * dzbar (fun s : ℂ => preSchwarzian (fsans (beltramiMul (a + s • toLinf m) κ)) z) 0‖ₑ ^ 2) /
          ‖t‖ₑ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hline := s35a_hF hκ has haL hm
  obtain ⟨σ₁, hσ₁, hS⟩ := s35a_hS hκ ha has haL hm
  have hσ₂ : (fun _ : ℂ => (0 : ℂ)) ∈ A2fun unitDisc := ⟨differentiableOn_const 0, by unfold normA2; simp⟩
  have h1 : deriv (fsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) 0 = 1 := by
    obtain ⟨hb0, -⟩ := (s4g_off_chart_data hκ ha has haL hm).choose_spec.choose_spec.1.self_of_nhds
    exact (s2c_facts hb0).2.2.2.1
  obtain ⟨hd, h1', h2', hrem⟩ := s35_riccati_variation (F := fun t => fsans (beltramiMul (a + t • toLinf m) κ))
    hline h1 hσ₁ hσ₂ hS (s35_wnorm hκ ha has haL hm).1 (s35a_hc hκ ha has haL hm)
  refine ⟨hd, h1', h2', hline.mono fun t ht => a21_memLp_two (D := unitDisc) measurableSet_ball ht.2.2, ?_⟩
  simpa only [zero_smul, add_zero] using hrem

/-- **(C)** `t ↦ 𝗀_t'(∞)` is real differentiable at `0` along the off-centre line. -/
theorem s35_beta_variation {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    DifferentiableAt ℝ (fun t : ℂ => derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))) 0 :=
  (s35_wnorm hκ ha has haL hm).2

end TakhtajanTeo.Ch2
