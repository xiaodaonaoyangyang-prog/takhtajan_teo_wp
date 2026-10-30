import TakhtajanTeo.Appendix.B1Entries
import TakhtajanTeo.Ch2.S2_Thm26
import TakhtajanTeo.Ch1.HilbertBersDifferentialL2

/-!
# Theorem 2.10: the period map is holomorphic in the Hilbert–Schmidt norm (Program F, 下属4)

Route (TT:4206–4240, along the Bers chart `t ↦ [(tμ) * ν]`):
1. `t210_hs_eq`: `‖B₁‖²_HS = ∬∬_{𝔻×𝔻} |K₁|²` (orthonormal expansion `K₁ = Σ B₁ e_m e_n`, `b8_pair_model`).
2. `t210_step_bound`: the quantitative chart step of `gk_step`: `∬∬ |K₁(ν * κ) - K₁(κ)|² ≤ C ‖φ‖²` for
   `ν = Λ(φ)` small.
3. `t210_uniform`: a uniform Hilbert–Schmidt bound along the chart path near `t = 0` (from 1, 2, `gk_K1_T01`,
   `hbL2_harmonic_coordinate`, `Lambda_smul`).
4. `t210_entries`: the entries of `B₁` along the chart path are holomorphic (`l27_kerK1_differentiableOn`,
   `bd_differentiableOn`, `b1_df_coeff_diff`).
5. `t210_cauchy_sq`: the Cauchy estimate (2.10) for one entry, in terms of its `L²` mean on a circle.
6. `t210_hs_tendsto`: the Hilbert–Schmidt difference quotient converges (5 + Tonelli + the uniform bound).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- `‖B₁(𝖿^κ)‖²_HS = ∬∬_{𝔻×𝔻} |K₁(𝖿^κ)|²`: Parseval for the orthonormal expansion `K₁ = Σ (B₁)_{mn} e_m(z) e_n(w)`. -/
theorem t210_hs_eq {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans κ) x.1 x.2‖₊ : ℝ≥0∞) ^ 2 := by
  have h := AppB.b8_welding_normalized_pair hκ
  have hg := grunsky_spec h
  have hcf := S2C.s2c_conf_f hκ
  let a : ℕ → ℕ → ℂ := fun m n => grunsky (fsans κ) (gsans κ) (-(m : ℤ)) (-(n : ℤ))
  have hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (fsans κ z - fsans κ w) / (z - w) = exp (grunsky (fsans κ) (gsans κ) 0 0 - S) := hg.1.2.2.2.1
  rw [s2c_kerK1_lintegral hcf.1 hcf.2.1 hexp]
  refine tsum_congr fun q => ?_
  have e : (‖B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (‖B1 (grunsky (fsans κ) (gsans κ)) q.1 q.2‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  rw [e]
  congr 1
  unfold B1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]
  simp only [a]
  push_cast
  rfl

/-- The quantitative chart step (TT:4110–4160, the bound inside `gk_step`): for `ν = Λ(φ)` with `φ` small,
`∬∬ |K₁(𝖿^{ν * κ}) - K₁(𝖿^κ)|² ≤ (2 / (π (1 - δ₀)⁴)) ‖φ‖²`. -/
theorem t210_step_bound {κ ν : LinfStarBall}
    {φ : A2 unitDisc} (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)))
    (hνφ : (ν : LinfStar) = Lambda (A2toAInf φ)) :
    (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (beltramiMul (ν : LinfStar) (κ : LinfStar))) q.1 q.2 -
        kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal (2 / (π * (1 - delta0) ^ 4) * ‖φ‖ ^ 2) := by
  obtain ⟨hn, hharm, hsm, -⟩ := gtp_small_a hφ
  rw [← hνφ] at hharm hsm
  have hd := delta0_bounds
  have hν1 : ‖(ν : LinfStar)‖ < 1 := hsm.trans hd.2
  have hνL : normL2 unitDiscExterior (ν : LinfStar) = ENNReal.ofReal (2 * ‖φ‖) := by
    rw [hνφ]; exact gtp_normL2_Lambda φ
  obtain ⟨γ', hγ'c, hγ'⟩ := gk_path_C1 (ν := (ν : LinfStar)) (κ := (κ : LinfStar)) hν1 κ.2
  set γ : ℝ → LinfStar := fun t => beltramiMul ((t : ℂ) • (ν : LinfStar)) (κ : LinfStar) with hγ
  have hsν : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • (ν : LinfStar) ∈ LinfStarBall := by
    intro s hs
    have : ‖(s : ℂ) • (ν : LinfStar)‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    simpa [LinfStarBall] using this
  have hγb : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ LinfStarBall := fun s hs => bg_mul_mem_ball κ.2 (hsν s hs)
  have hγ0 : γ 0 = (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_zero, zero_smul]
    exact grp_zero_mul κ.2
  have hγ1 : γ 1 = beltramiMul (ν : LinfStar) (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_one, one_smul]
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hγcont : ContinuousOn γ (Icc 0 1) := fun s hs =>
    (hγ' s hs).1.continuousAt.continuousWithinAt
  -- the variation kernel
  set D := {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} with hDdef
  set k : ℝ → ℂ × ℂ → ℂ := fun s q => fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) q.1 q.2) (γ s) (γ' s)
    with hk
  have hkder : ∀ q ∈ D, ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => kerK1 (fsans (γ t)) q.1 q.2) (k s q) s := by
    intro q hq s hs
    have hΦ := ((l27_kerK1_differentiableOn hq.1 hq.2.1 hq.2.2 (γ s) (hγb s hs)).differentiableAt
      (isOpen_ball.mem_nhds (hγb s hs))).hasFDerivAt
    exact (hΦ.restrictScalars ℝ).comp_hasDerivAt s (hγ' s hs).1
  have hkcont : ∀ q ∈ D, ContinuousOn (fun s => k s q) (Icc 0 1) := by
    intro q hq
    have hF := (l27_fderiv_continuousOn hq.1 hq.2.1 hq.2.2).comp hγcont (fun s hs => hγb s hs)
    exact hF.clm_apply hγ'c
  -- the tangent: `μ̃_s = D_{sν}R_{(sν)⁻¹}(ν)`
  set xs : ℝ → LinfStar := fun s =>
    fderiv ℂ (fun l => beltramiMul l (beltramiInv ((s : ℂ) • (ν : LinfStar)))) ((s : ℂ) • (ν : LinfStar))
      (ν : LinfStar) with hxs
  have hkform : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ D, k s q =
      1 / π ^ 2 * (deriv (fsans (γ s)) q.1 * deriv (fsans (γ s)) q.2) *
        ∫ u in gsans (γ s) '' unitDiscExterior,
          xs s (Function.invFunOn (gsans (γ s)) unitDiscExterior u) *
            (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u) /
              conj (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u))) /
            ((u - fsans (γ s) q.1) ^ 2 * (u - fsans (γ s) q.2) ^ 2) := by
    intro s hs q hq
    have h := gk_k_eq (hγ' s hs).1 (hγb s hs) hq.1 hq.2.1 hq.2.2
    rw [(hγ' s hs).2] at h
    exact h
  -- uniform bound for the tangent
  set B : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖)) ^ 2 with hB
  have hBfin : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  have hxbound : ∀ s ∈ Icc (0 : ℝ) 1, normL2 unitDiscExterior (xs s) ≤
      ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖) := by
    intro s hs
    have hsn : ‖(s : ℂ) • (ν : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    have hh : (s : ℂ) • (ν : LinfStar) ∈ harmonicBeltrami := Submodule.smul_mem _ _ hharm
    have hδ : ‖(s : ℂ) • (ν : LinfStar)‖ < delta0 := lt_of_le_of_lt hsn hsm
    have h := (grp_cor_2_6 hh hδ (hsν s hs) (ν : LinfStar)).2
    rw [hνL] at h
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h1 : 0 < 1 - ‖(ν : LinfStar)‖ := by linarith
    have h2 : 1 - ‖(ν : LinfStar)‖ ≤ 1 - ‖(s : ℂ) • (ν : LinfStar)‖ := by linarith
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  -- a jointly measurable version of the kernel (Carathéodory)
  set c : ℝ → ℝ := fun s => max 0 (min 1 s) with hcdef
  have hcI : ∀ s, c s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcs : ∀ s ∈ Icc (0 : ℝ) 1, c s = s := fun s hs => by
    simp only [hcdef, min_eq_right hs.2, max_eq_right hs.1]
  set K : ℝ → ℂ × ℂ → ℂ := fun s q => D.indicator (fun q => k (c s) q) q with hKdef
  have hKform : ∀ s, K s = D.indicator fun q =>
      1 / π ^ 2 * (deriv (fsans (γ (c s))) q.1 * deriv (fsans (γ (c s))) q.2) *
        ∫ u in gsans (γ (c s)) '' unitDiscExterior,
          xs (c s) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) *
            (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) /
              conj (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u))) /
            ((u - fsans (γ (c s)) q.1) ^ 2 * (u - fsans (γ (c s)) q.2) ^ 2) := by
    intro s
    funext q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact hkform (c s) (hcI s) q hq
    · simp only [hKdef, Set.indicator_of_notMem hq]
  have hKm : ∀ s, Measurable (K s) := fun s => by
    rw [hKform s]
    exact gk_kform_meas (hγb (c s) (hcI s)) (xs (c s))
  have hKc : ∀ q, Continuous fun s => K s q := by
    intro q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact (hkcont q hq).comp_continuous hcc hcI
    · simp only [hKdef, Set.indicator_of_notMem hq]
      exact continuous_const
  have hjoint : Measurable (Function.uncurry K) := measurable_uncurry_of_continuous_of_measurable hKc hKm
  -- pointwise FTC
  have hpt : ∀ q ∈ D, (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    intro q hq
    have h := gk_ftc_sq (F := fun t => kerK1 (fsans (γ t)) q.1 q.2) (F' := fun s => k s q)
      (hkder q hq) (hkcont q hq)
    refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_))
    simp only [hKdef, Set.indicator_of_mem hq, hcs s hs]
  -- per-`s` bound
  have hper : ∀ s, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 ≤ B := by
    intro s
    have hb := gk_I_bound (hγb (c s) (hcI s)) (xs (c s)) (k := fun a b => K s (a, b)) (by
      intro a ha b hb hab
      have hq : (a, b) ∈ D := ⟨ha, hb, hab⟩
      show K s (a, b) = _
      rw [hKform s, Set.indicator_of_mem hq])
    refine hb.trans ?_
    rw [hB]
    exact mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (hxbound (c s) (hcI s)) 2)
  -- Tonelli
  have hswap : ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 =
      ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    refine lintegral_lintegral_swap ?_
    have hm2 : Measurable (fun p : (ℂ × ℂ) × ℝ => (‖K p.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      ((hjoint.comp measurable_swap).nnnorm.coe_nnreal_ennreal).pow_const 2
    exact hm2.aemeasurable
  have hdiff : ∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤ B := by
    calc _ ≤ ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 :=
          lintegral_mono_ae (gk_offdiag_ae.mono fun q hq => hpt q hq)
      _ = _ := hswap
      _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, B := lintegral_mono fun s => hper s
      _ = B := by rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
  rw [hγ1, hγ0] at hdiff
  refine hdiff.trans ?_
  have hν0 : ‖(ν : LinfStar)‖ < delta0 := hsm
  have h1 : 0 < 1 - delta0 := by linarith [hd.2]
  have h2 : 1 - delta0 < 1 - ‖(ν : LinfStar)‖ := by linarith
  have h3 : 0 < 1 - ‖(ν : LinfStar)‖ := by linarith
  rw [hB, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpi : 0 < π := Real.pi_pos
  have e : 1 / (4 * π) * (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2 * (2 * ‖φ‖)) ^ 2 =
      2 / (π * (1 - ‖(ν : LinfStar)‖) ^ 4) * ‖φ‖ ^ 2 := by
    rw [mul_pow, div_pow, hs2]
    field_simp
    ring
  rw [e]
  gcongr

/-- A uniform Hilbert–Schmidt bound for `B₁` along the Bers-chart path `t ↦ (tμ) * ν` near `t = 0`. -/
theorem t210_uniform {ν : LinfStar} (hν : ν ∈ LinfStarBall) (hνT : Phi ⟨ν, hν⟩ ∈ T01) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ r > 0, ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ t ∈ closedBall (0 : ℂ) r,
      beltramiMul (t • toLinf μ) ν ∈ LinfStarBall ∧
        (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
          (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M := by
  obtain ⟨φ, hΛ, -⟩ := hbL2_harmonic_coordinate hμ
  set δ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hδ
  have hd := delta0_bounds
  have hδ0 : 0 < δ := lt_min (Real.sqrt_pos.mpr (by positivity))
    (div_pos (by linarith [hd.1]) (Real.sqrt_pos.mpr (by positivity)))
  set r : ℝ := δ / (2 * (‖φ‖ + 1)) with hr
  have hr0 : 0 < r := by positivity
  set H : ℝ≥0∞ := ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans ν) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 with hH
  have hHf : H < ∞ := gk_K1_T01 _ hνT ⟨ν, hν⟩ rfl
  set C : ℝ := 2 / (π * (1 - delta0) ^ 4) with hC
  refine ⟨r, hr0, 2 * ENNReal.ofReal (C * δ ^ 2) + 2 * H, ?_, ?_⟩
  · exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (by norm_num) hHf⟩
  intro t ht
  have htn : ‖t‖ ≤ r := by simpa using ht
  have htφ : ‖t • φ‖ < δ := by
    rw [norm_smul]
    have h1 : ‖t‖ * ‖φ‖ ≤ r * ‖φ‖ := mul_le_mul_of_nonneg_right htn (norm_nonneg _)
    have h2 : r * ‖φ‖ < δ := by
      rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg φ]
    linarith
  have hΛt : t • toLinf μ = Lambda (A2toAInf (t • φ)) := by
    rw [← A2toAInfCLM_apply, map_smul, A2toAInfCLM_apply, Lambda_smul, hΛ]
  obtain ⟨hn, -, hsm, -⟩ := gtp_small_a htφ
  have hmem : t • toLinf μ ∈ LinfStarBall := by
    rw [hΛt]
    exact mem_ball_zero_iff.mpr (hsm.trans hd.2)
  have hγ : beltramiMul (t • toLinf μ) ν ∈ LinfStarBall := bg_mul_mem_ball hν hmem
  refine ⟨hγ, ?_⟩
  have hstep := t210_step_bound (κ := ⟨ν, hν⟩) (ν := ⟨t • toLinf μ, hmem⟩) htφ hΛt
  have hS : ENNReal.ofReal (C * ‖t • φ‖ ^ 2) ≤ ENNReal.ofReal (C * δ ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have hC0 : 0 ≤ C := by
      rw [hC]
      have : 0 < 1 - delta0 := by linarith [hd.2]
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htφ.le 2) hC0
  rw [t210_hs_eq hγ]
  calc ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ q in unitDisc ×ˢ unitDisc,
          (2 * (‖kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) q.1 q.2 - kerK1 (fsans ν) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖kerK1 (fsans ν) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
        lintegral_mono fun q => gk_sq_tri _ _
    _ = 2 * (∫⁻ q in unitDisc ×ˢ unitDisc,
            (‖kerK1 (fsans (beltramiMul (t • toLinf μ) ν)) q.1 q.2 - kerK1 (fsans ν) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * H := by
        rw [lintegral_add_right' _ ((gk_kerK1_aemeas hν).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * ENNReal.ofReal (C * δ ^ 2) + 2 * H := by
        gcongr
        exact hstep.trans hS

/-- The entries of `B₁` along the Bers-chart path are holomorphic near `t = 0`. -/
theorem t210_entries {ν : LinfStar} (hν : ν ∈ LinfStarBall) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ r > 0, (∀ t ∈ ball (0 : ℂ) r, beltramiMul (t • toLinf μ) ν ∈ LinfStarBall) ∧
      ∀ m n, DifferentiableOn ℂ (fun t => B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
        (gsans (beltramiMul (t • toLinf μ) ν))) m n) (ball (0 : ℂ) r) := by
  have _h := hμ
  set mh : LinfStar := toLinf μ with hmh
  set r₀ : ℝ := 1 / (‖mh‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hsm : ∀ t ∈ ball (0 : ℂ) r₀, t • mh ∈ LinfStarBall := by
    intro t ht
    have htn : ‖t‖ < r₀ := by simpa using ht
    have h1 : ‖t‖ * (‖mh‖ + 1) < 1 := by
      rw [hr₀, lt_div_iff₀ (by positivity)] at htn; exact htn
    simp only [LinfStarBall, mem_ball_zero_iff, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg mh]
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, beltramiMul (t • mh) ν ∈ LinfStarBall := fun t ht =>
    bg_mul_mem_ball hν (hsm t ht)
  refine ⟨r₀, hr₀pos, hball, ?_⟩
  have hU : IsOpen (ball (0 : ℂ) r₀) := isOpen_ball
  have hpath : DifferentiableOn ℂ (fun t : ℂ => beltramiMul (t • mh) ν) (ball (0 : ℂ) r₀) := by
    intro t ht
    have h1 := ((bd_differentiableOn hν) _ (hsm t ht)).differentiableAt (isOpen_ball.mem_nhds (hsm t ht))
    have h2 : DifferentiableAt ℂ (fun t : ℂ => t • mh) t := (differentiableAt_id.smul_const mh)
    exact (h1.comp t h2).differentiableWithinAt
  have hpm := fun t (ht : t ∈ ball (0 : ℂ) r₀) =>
    AppB.b8_pair_model (AppB.b8_welding_normalized_pair (hball t ht))
  have hbd : ∀ t ∈ ball (0 : ℂ) r₀, ∀ m n,
      ‖B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) m n‖ ≤ 1 := by
    intro t ht m n
    obtain ⟨hs, hle⟩ := (hpm t ht).2.1 m
    have h1 : ‖B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) m n‖ ^ 2 ≤ 1 :=
      (hs.le_tsum n (fun _ _ => sq_nonneg _)).trans hle
    nlinarith [norm_nonneg (B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) m n)]
  intro m n
  let c : ℂ → ℕ → ℕ → ℂ := fun t p q =>
    B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) p q *
      (Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) : ℂ)
  have hc := AppB.b1_df_coeff_diff hU (c := c) (L := fun p q => Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)))
    (ρ1 := 1 / 2) (ρ2 := 1 / 4) (by norm_num) (by norm_num) (fun p q => Real.sqrt_nonneg _)
    (AppB.b1_summable_L (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by
      intro t ht p q
      simp only [c, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc _ ≤ 1 * Real.sqrt (((p : ℝ) + 1) * ((q : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hbd t ht p q) (Real.sqrt_nonneg _)
        _ = _ := one_mul _)
    (by
      intro z w hz hw
      have hz1 : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz]; norm_num)
      have hw1 : w ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hw]; norm_num)
      have hzw : z ≠ w := by
        intro he; rw [he] at hz; rw [hz] at hw; norm_num at hw
      have hdiffK : DifferentiableOn ℂ (fun t : ℂ =>
          (π : ℂ) * kerK1 (fsans (beltramiMul (t • mh) ν)) z w) (ball (0 : ℂ) r₀) := by
        refine DifferentiableOn.const_mul ?_ _
        exact (l27_kerK1_differentiableOn hz1 hw1 hzw).comp hpath (fun t ht => hball t ht)
      refine hdiffK.congr (fun t ht => ?_)
      have hs := ((hpm t ht).2.2.2 z hz1 w hw1 hzw).mul_left (π : ℂ)
      refine (HasSum.tsum_eq ?_)
      refine hs.congr_fun (fun p => ?_)
      have e := AppB.b1_basis_weight p.1 p.2 z w
      calc c t p.1 p.2 * z ^ p.1 * w ^ p.2
          = B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) p.1 p.2 *
            ((Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) : ℂ) * z ^ p.1 * w ^ p.2) := by
            simp only [c]; ring
        _ = B1 (grunsky (fsans (beltramiMul (t • mh) ν)) (gsans (beltramiMul (t • mh) ν))) p.1 p.2 *
            ((π : ℂ) * (basisE p.1 z * basisE p.2 w)) := by rw [e]
        _ = _ := by ring) m n
  have hne : ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hc.div_const ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ)).congr (fun t ht => ?_)
  simp only [c]
  field_simp

/-- The Cauchy-formula kernel of the second-order remainder. -/
theorem t210_remainder_eq {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) (2 * r)))
    {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < r) :
    dslope F 0 t - deriv F 0 =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, r), (t / (ζ ^ 2 * (ζ - t))) • F ζ := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hcl : closure (ball (0 : ℂ) r) = closedBall 0 r := closure_ball 0 hr.ne'
  have hdc : DiffContOnCl ℂ F (ball (0 : ℂ) r) := (hF.mono (hcl ▸ hsub)).diffContOnCl
  have htb : t ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr ht
  have e1 := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul htb
  have e0 := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hr)
  have ed := cderiv_eq_deriv isOpen_ball hF hr hsub
  have hFc : ContinuousOn F (sphere (0 : ℂ) r) := hF.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hne0 : ∀ ζ ∈ sphere (0 : ℂ) r, ζ ≠ 0 := fun ζ hζ h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hζ; exact hr.ne hζ
  have hnet : ∀ ζ ∈ sphere (0 : ℂ) r, ζ - t ≠ 0 := fun ζ hζ h => by
    rw [sub_eq_zero] at h; rw [h, mem_sphere_zero_iff_norm] at hζ; exact ht.ne hζ
  have i1 : CircleIntegrable (fun ζ => (ζ - t)⁻¹ • F ζ) 0 r :=
    ((continuousOn_id.sub continuousOn_const).inv₀ hnet |>.smul hFc).circleIntegrable hr.le
  have i0 : CircleIntegrable (fun ζ => (ζ - 0)⁻¹ • F ζ) 0 r :=
    ((continuousOn_id.sub continuousOn_const).inv₀ (fun ζ hζ => by simpa using hne0 ζ hζ) |>.smul hFc).circleIntegrable hr.le
  have i2 : CircleIntegrable (fun ζ => ((ζ - 0) ^ 2)⁻¹ • F ζ) 0 r :=
    (((continuousOn_id.sub continuousOn_const).pow 2).inv₀
      (fun ζ hζ => pow_ne_zero 2 (by simpa using hne0 ζ hζ)) |>.smul hFc).circleIntegrable hr.le
  have c1 : ContinuousOn (fun ζ => (ζ - t)⁻¹ • F ζ) (sphere (0 : ℂ) r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hnet |>.smul hFc
  have c0 : ContinuousOn (fun ζ => (ζ - 0)⁻¹ • F ζ) (sphere (0 : ℂ) r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun ζ hζ => by simpa using hne0 ζ hζ) |>.smul hFc
  have i3 : CircleIntegrable (fun ζ => t⁻¹ • ((ζ - t)⁻¹ • F ζ - (ζ - 0)⁻¹ • F ζ)) 0 r :=
    (show ContinuousOn (fun ζ => t⁻¹ • ((ζ - t)⁻¹ • F ζ - (ζ - 0)⁻¹ • F ζ)) (sphere (0 : ℂ) r) from
      ContinuousOn.const_smul (c1.sub c0) t⁻¹).circleIntegrable hr.le
  rw [dslope_of_ne _ ht0, slope_def_module, ← e1, ← e0, ← ed, cderiv, sub_zero]
  rw [← smul_sub, ← circleIntegral.integral_sub i1 i0, smul_comm, ← smul_sub,
    ← circleIntegral.integral_smul, ← circleIntegral.integral_sub i3 i2]
  congr 1
  refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
  have h1 := hne0 ζ hζ
  have h2 := hnet ζ hζ
  simp only [smul_eq_mul, sub_zero]
  field_simp
  ring

/-- The real form of the Cauchy estimate: `|R(t)| ≤ (|t|/(π r²)) ∫₀^{2π} |F(r e^{iθ})| dθ`. -/
theorem t210_remainder_le {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) (2 * r)))
    {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ ≤ r / 2) :
    ‖dslope F 0 t - deriv F 0‖ ≤ ‖t‖ / (π * r ^ 2) * ∫ θ in (0 : ℝ)..2 * π, ‖F (circleMap 0 r θ)‖ := by
  have htr : ‖t‖ < r := by linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hFc : ContinuousOn F (sphere (0 : ℂ) r) := hF.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hGc : Continuous fun θ : ℝ => F (circleMap 0 r θ) :=
    hFc.comp_continuous (continuous_circleMap 0 r) (fun θ => circleMap_mem_sphere 0 hr.le θ)
  rw [t210_remainder_eq hr hF ht0 htr, norm_smul, circleIntegral]
  have hpi : 0 < π := Real.pi_pos
  have h2pi : ‖(2 * π * I : ℂ)⁻¹‖ = 1 / (2 * π) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hpi.le]
    ring
  rw [h2pi]
  have hpt : ∀ θ : ℝ, ‖deriv (circleMap 0 r) θ • ((t / (circleMap 0 r θ ^ 2 * (circleMap 0 r θ - t))) •
      F (circleMap 0 r θ))‖ ≤ 2 * ‖t‖ / r ^ 2 * ‖F (circleMap 0 r θ)‖ := by
    intro θ
    set ζ := circleMap 0 r θ with hζ
    have hζn : ‖ζ‖ = r := by rw [hζ, norm_circleMap_zero, abs_of_pos hr]
    have hlow : r / 2 ≤ ‖ζ - t‖ := by
      have := norm_sub_norm_le ζ t
      linarith
    have hpos : 0 < ‖ζ - t‖ := by linarith
    rw [deriv_circleMap, norm_smul, norm_smul, norm_mul, ← hζ, hζn, Complex.norm_I, mul_one, norm_div,
      norm_mul, norm_pow, hζn]
    have hF0 := norm_nonneg (F ζ)
    have key : r * (‖t‖ / (r ^ 2 * ‖ζ - t‖)) ≤ 2 * ‖t‖ / r ^ 2 := by
      rw [show r * (‖t‖ / (r ^ 2 * ‖ζ - t‖)) = ‖t‖ / (r * ‖ζ - t‖) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * ‖t‖ * r)
      nlinarith [norm_nonneg t]
    calc r * (‖t‖ / (r ^ 2 * ‖ζ - t‖) * ‖F ζ‖) = (r * (‖t‖ / (r ^ 2 * ‖ζ - t‖))) * ‖F ζ‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key hF0
  have hint : (∫ θ in (0 : ℝ)..2 * π, ‖deriv (circleMap 0 r) θ •
      ((t / (circleMap 0 r θ ^ 2 * (circleMap 0 r θ - t))) • F (circleMap 0 r θ))‖) ≤
      ∫ θ in (0 : ℝ)..2 * π, 2 * ‖t‖ / r ^ 2 * ‖F (circleMap 0 r θ)‖ := by
    apply intervalIntegral.integral_mono_on (by positivity)
    · apply Continuous.intervalIntegrable
      have hden : ∀ θ : ℝ, circleMap 0 r θ ^ 2 * (circleMap 0 r θ - t) ≠ 0 := by
        intro θ
        have hζn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
        refine mul_ne_zero (pow_ne_zero 2 fun h => ?_) fun h => ?_
        · rw [h, norm_zero] at hζn; exact hr.ne hζn
        · rw [sub_eq_zero] at h; rw [h] at hζn; exact htr.ne hζn
      have hd : Continuous fun θ => deriv (circleMap 0 r) θ := by
        simp only [deriv_circleMap]; exact (continuous_circleMap 0 r).mul continuous_const
      refine (hd.smul ((continuous_const.div ?_ hden).smul hGc)).norm
      exact ((continuous_circleMap 0 r).pow 2).mul ((continuous_circleMap 0 r).sub continuous_const)
    · exact (continuous_const.mul hGc.norm).intervalIntegrable _ _
    · intro θ _
      exact hpt θ
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun θ => deriv (circleMap 0 r) θ • ((t / (circleMap 0 r θ ^ 2 * (circleMap 0 r θ - t))) •
      F (circleMap 0 r θ))) (by positivity : (0 : ℝ) ≤ 2 * π)
  rw [intervalIntegral.integral_const_mul] at hint
  calc 1 / (2 * π) * ‖∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 r) θ •
        ((t / (circleMap 0 r θ ^ 2 * (circleMap 0 r θ - t))) • F (circleMap 0 r θ))‖
      ≤ 1 / (2 * π) * (2 * ‖t‖ / r ^ 2 * ∫ θ in (0 : ℝ)..2 * π, ‖F (circleMap 0 r θ)‖) :=
        mul_le_mul_of_nonneg_left (hnorm.trans hint) (by positivity)
    _ = _ := by field_simp

/-- The Cauchy estimate (2.10) for one function: for `F` holomorphic on `|t| < 2r` and `|t| ≤ r/2`,
`|(F(t) - F(0))/t - F'(0)|² ≤ (2 |t|² / (π r⁴)) ∫₀^{2π} |F(r e^{iθ})|² dθ` (written with `dslope`). -/
theorem t210_cauchy_sq {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) (2 * r)))
    {t : ℂ} (ht : ‖t‖ ≤ r / 2) :
    (‖dslope F 0 t - deriv F 0‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖F (circleMap 0 r θ)‖₊ : ℝ≥0∞) ^ 2 := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [dslope_same]
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hFc : ContinuousOn F (sphere (0 : ℂ) r) := hF.continuousOn.mono (sphere_subset_closedBall.trans hsub)
  have hGc : Continuous fun θ : ℝ => F (circleMap 0 r θ) :=
    hFc.comp_continuous (continuous_circleMap 0 r) (fun θ => circleMap_mem_sphere 0 hr.le θ)
  have hpi : 0 < π := Real.pi_pos
  have hle := t210_remainder_le hr hF ht0 ht
  set c : ℝ := ‖t‖ / (π * r ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set I1 : ℝ := ∫ θ in (0 : ℝ)..2 * π, ‖F (circleMap 0 r θ)‖ with hI1
  have hI1e : ENNReal.ofReal I1 = ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖F (circleMap 0 r θ)‖₊ : ℝ≥0∞) := by
    rw [hI1, intervalIntegral.integral_of_le (by positivity),
      ofReal_integral_eq_lintegral_ofReal (hGc.norm.integrableOn_Ioc) (ae_of_all _ fun θ => norm_nonneg _)]
    refine lintegral_congr fun θ => ?_
    rw [ofReal_norm]
    rfl
  have hcs := TakhtajanTeo.CUI.cui_lintegral_cauchy_schwarz (volume.restrict (Ioc (0 : ℝ) (2 * π)))
    (A := fun _ => (1 : ℝ≥0∞)) (B := fun θ => (‖F (circleMap 0 r θ)‖₊ : ℝ≥0∞)) aemeasurable_const
    hGc.measurable.nnnorm.coe_nnreal_ennreal.aemeasurable
  simp only [one_mul, one_pow, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero] at hcs
  calc (‖dslope F 0 t - deriv F 0‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ‖dslope F 0 t - deriv F 0‖ ^ 2 := by
        rw [ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal (c * I1) ^ 2 := pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hle) 2
    _ = ENNReal.ofReal c ^ 2 * (∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖F (circleMap 0 r θ)‖₊ : ℝ≥0∞)) ^ 2 := by
        rw [ENNReal.ofReal_mul hc0, mul_pow, hI1e]
    _ ≤ ENNReal.ofReal c ^ 2 * (ENNReal.ofReal (2 * π) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖F (circleMap 0 r θ)‖₊ : ℝ≥0∞) ^ 2) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_pow hc0, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hc]
        field_simp

/-- The Hilbert–Schmidt difference quotient of a holomorphic matrix family with a uniform Hilbert–Schmidt bound
converges to the matrix of derivatives. -/
theorem t210_hs_tendsto {c : ℂ → ℕ → ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ m n, DifferentiableOn ℂ (fun t => c t m n) (ball (0 : ℂ) (2 * r)))
    {M : ℝ≥0∞} (hM : M < ∞) (hb : ∀ t ∈ closedBall (0 : ℂ) r, (∑' q : ℕ × ℕ, (‖c t q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M) :
    Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
        (‖(c t q.1 q.2 - c 0 q.1 q.2) / t - deriv (fun s => c s q.1 q.2) 0‖₊ : ℝ≥0∞) ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hpi : 0 < π := Real.pi_pos
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)
  have hmeas : ∀ q : ℕ × ℕ, AEMeasurable (fun θ : ℝ => (‖c (circleMap 0 r θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
    intro q
    have hcont : Continuous fun θ : ℝ => c (circleMap 0 r θ) q.1 q.2 :=
      ((hc q.1 q.2).continuousOn.mono hsub).comp_continuous (continuous_circleMap 0 r) hcm
    exact (hcont.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  have hint : (∫⁻ θ in Ioc (0 : ℝ) (2 * π), ∑' q : ℕ × ℕ, (‖c (circleMap 0 r θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      M * ENNReal.ofReal (2 * π) := by
    calc _ ≤ ∫⁻ _ in Ioc (0 : ℝ) (2 * π), M := lintegral_mono fun θ => hb _ (hcm θ)
      _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hbound : ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ r / 2 →
      (∑' q : ℕ × ℕ, (‖(c t q.1 q.2 - c 0 q.1 q.2) / t - deriv (fun s => c s q.1 q.2) 0‖₊ : ℝ≥0∞) ^ 2) ≤
        ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) * (M * ENNReal.ofReal (2 * π)) := by
    intro t ht0 ht
    have hq : ∀ q : ℕ × ℕ, (‖(c t q.1 q.2 - c 0 q.1 q.2) / t - deriv (fun s => c s q.1 q.2) 0‖₊ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖c (circleMap 0 r θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
      intro q
      have h := t210_cauchy_sq hr (hc q.1 q.2) ht
      have he : dslope (fun s => c s q.1 q.2) 0 t = (c t q.1 q.2 - c 0 q.1 q.2) / t := by
        rw [dslope_of_ne _ ht0, slope_def_field, sub_zero]
      rwa [he] at h
    calc _ ≤ ∑' q : ℕ × ℕ, ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * π), (‖c (circleMap 0 r θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := ENNReal.tsum_le_tsum hq
      _ = ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * π), ∑' q : ℕ × ℕ, (‖c (circleMap 0 r θ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum hmeas]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t : ℂ => ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) * (M * ENNReal.ofReal (2 * π)))
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℂ => ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4))) (𝓝 0) (𝓝 0) := by
      have hc' : Continuous fun t : ℂ => ENNReal.ofReal (2 * ‖t‖ ^ 2 / (π * r ^ 4)) :=
        ENNReal.continuous_ofReal.comp ((continuous_const.mul (continuous_norm.pow 2)).div_const _)
      simpa using hc'.tendsto 0
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.mul_ne_top hM.ne (ENNReal.ofReal_ne_top (r := 2 * π))))
    rw [zero_mul] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 ∧ ‖t‖ ≤ r / 2 := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ ≤ r / 2 := by
      have hb2 : closedBall (0 : ℂ) (r / 2) ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ (by linarith)
      exact nhdsWithin_le_nhds (Filter.mem_of_superset hb2 fun t ht => by simpa using ht)
    exact h1.and h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev] with t ht
  exact hbound t ht.1 ht.2

/-- **Theorem 2.10**, the NEW statement (byte-identical to the corrected `thm_2_10` up to the name). -/
theorem t210_thm_2_10 {ν : LinfStar} (hν : ν ∈ LinfStarBall) (hνT : Phi ⟨ν, hν⟩ ∈ T01) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ D : ℕ → ℕ → ℂ, Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
        (‖(B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2 -
          B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2) / t - D q.1 q.2‖₊ : ℝ≥0∞) ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨r₁, hr₁, -, hd⟩ := t210_entries hν hμ
  obtain ⟨r₂, hr₂, M, hM, hb⟩ := t210_uniform hν hνT hμ
  set r : ℝ := min (r₁ / 2) r₂ with hrdef
  have hr : 0 < r := lt_min (by positivity) hr₂
  set c : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν))
    (gsans (beltramiMul (t • toLinf μ) ν))) with hcdef
  have hc : ∀ m n, DifferentiableOn ℂ (fun t => c t m n) (ball (0 : ℂ) (2 * r)) := fun m n =>
    (hd m n).mono (ball_subset_ball (by rw [hrdef]; linarith [min_le_left (r₁ / 2) r₂]))
  have hb' : ∀ t ∈ closedBall (0 : ℂ) r, (∑' q : ℕ × ℕ, (‖c t q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M := fun t ht =>
    (hb t (closedBall_subset_closedBall (min_le_right _ _) ht)).2
  have h0 : c 0 = B1 (grunsky (fsans ν) (gsans ν)) := by
    simp only [hcdef, zero_smul, grp_zero_mul hν]
  refine ⟨fun m n => deriv (fun s => c s m n) 0, ?_⟩
  have h := t210_hs_tendsto hr hc hM hb'
  rw [h0] at h
  exact h

/-- **Theorem 2.10** (TT:4206–4240). `𝒫` is a holomorphic inclusion of the Hilbert manifold `T₀(1)` into the Hilbert
space `𝒮₂` of Hilbert–Schmidt operators. For `[ν] ∈ T₀(1)` (any representative `ν ∈ L∞(𝔻*)₁`) and
`μ ∈ H^{-1,1}(𝔻*)`, the map `t ↦ B₁(𝖿^{(tμ) * ν})` along the Bers chart of `V_ν` is complex differentiable at `t = 0`
in the Hilbert–Schmidt norm: there is a matrix `D` with `Σ_{m,n} |(B₁(t) - B₁(0))/t - D|²_{mn} → 0`.
- **[CORRECTION 2026-10-28, user-approved]** The Hilbert–Schmidt sum is taken in `ℝ≥0∞`: the real `∑'` is `0` on a
  non-summable family, which made the statement provable by a junk choice of `D` (found by 下属4).
- **[CORRECTION 2026-10-28, user-approved]** The curve is the Bers-chart path `t ↦ [(tμ) * ν]`, the paper's chart
  notion of holomorphy on `T₀(1)` (as in §3), instead of the straight line `t ↦ ν + tμ` (TT:4210). The straight-line
  form needs a uniform Hilbert–Schmidt bound at a general `L²` base, i.e. a quasiconformal distortion lemma for
  harmonic `L²` differentials, which the proof at TT:4236 does not supply: it cites the proof of Theorem 2.6, which
  covers only bases in `𝒪(𝔻*)₁` (found by 下属4). The representative `ν` is arbitrary. -/
theorem thm_2_10 {ν : LinfStar} (hν : ν ∈ LinfStarBall) (hνT : Phi ⟨ν, hν⟩ ∈ T01) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ D : ℕ → ℕ → ℂ, Tendsto (fun t : ℂ => ∑' q : ℕ × ℕ,
        (‖(B1 (grunsky (fsans (beltramiMul (t • toLinf μ) ν)) (gsans (beltramiMul (t • toLinf μ) ν))) q.1 q.2 -
          B1 (grunsky (fsans ν) (gsans ν)) q.1 q.2) / t - D q.1 q.2‖₊ : ℝ≥0∞) ^ 2) (𝓝[≠] 0) (𝓝 0) :=
  t210_thm_2_10 hν hνT hμ

end Ch2

end TakhtajanTeo
