import TakhtajanTeo.Ch2.S4GReductions
import TakhtajanTeo.Ch2.S3SchwarzianVariation
import TakhtajanTeo.Ch1.S7_Curvature
import TakhtajanTeo.Ch2.S3FredholmDerivative
import TakhtajanTeo.Ch2.S3FredholmVariation
import TakhtajanTeo.Ch2.S3Var_Completed
import TakhtajanTeo.Ch1.HilbertManifoldCompleted
import TakhtajanTeo.Ch1.CuiBound
import TakhtajanTeo.Ch1.WPChangeOfVariables

/-! # First variation of `S₂` and `S₁` at off-centre points of a chart (`s4g_`)

The shared wall of `thm_4_1` (下属5) and `thm_3_8` (下属4). In the chart `V_κ`, at the off-centre point
`[a * κ]` (`a` a small harmonic L² differential), the derivative along the chart line `a + tm` equals the derivative
at the centre of `V_{a*κ}` along the push-forward `R(m, a)` (TT:1767, (1.6)), and the pairing with `ϑ` needs no
harmonic projection because `𝒮(g) ∈ A₂(𝔻*)`. GPT's `s3sv_first_variation` is the case `a = 0`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

/-- The quantitative chart step of `t210_step_bound`, for a small harmonic `ν` given directly (not as `Λφ`):
`∬∬ |K₁(𝖿^{ν * κ}) - K₁(𝖿^κ)|² ≤ (1/4π) (√2/(1-‖ν‖)² ‖ν‖₂)²`. -/
theorem s4g_step_bound {κ ν : LinfStarBall} (hharm : (ν : LinfStar) ∈ harmonicBeltrami)
    (hsm : ‖(ν : LinfStar)‖ < delta0) :
    (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (beltramiMul (ν : LinfStar) (κ : LinfStar))) q.1 q.2 -
        kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal (1 / (4 * π)) *
        (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * normL2 unitDiscExterior (ν : LinfStar)) ^ 2 := by
  have hd := delta0_bounds
  have hν1 : ‖(ν : LinfStar)‖ < 1 := hsm.trans hd.2
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
  have hγcont : ContinuousOn γ (Icc 0 1) := fun s hs =>
    (hγ' s hs).1.continuousAt.continuousWithinAt
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
  set B : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * normL2 unitDiscExterior (ν : LinfStar)) ^ 2
    with hB
  have hxbound : ∀ s ∈ Icc (0 : ℝ) 1, normL2 unitDiscExterior (xs s) ≤
      ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * normL2 unitDiscExterior (ν : LinfStar) := by
    intro s hs
    have hsn : ‖(s : ℂ) • (ν : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    have hh : (s : ℂ) • (ν : LinfStar) ∈ harmonicBeltrami := Submodule.smul_mem _ _ hharm
    have hδ : ‖(s : ℂ) • (ν : LinfStar)‖ < delta0 := lt_of_le_of_lt hsn hsm
    have h := (grp_cor_2_6 hh hδ (hsν s hs) (ν : LinfStar)).2
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h1 : 0 < 1 - ‖(ν : LinfStar)‖ := by linarith
    have h2 : 1 - ‖(ν : LinfStar)‖ ≤ 1 - ‖(s : ℂ) • (ν : LinfStar)‖ := by linarith
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
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
  have hpt : ∀ q ∈ D, (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    intro q hq
    have h := gk_ftc_sq (F := fun t => kerK1 (fsans (γ t)) q.1 q.2) (F' := fun s => k s q)
      (hkder q hq) (hkcont q hq)
    refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_))
    simp only [hKdef, Set.indicator_of_mem hq, hcs s hs]
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
  exact hdiff

/-- The chart tangent at an off-centre point (TT:1767, (1.6)): pushed to the centre of `V_{a*κ}`, the derivative of
`l ↦ l * κ` at `a` in the direction `m` is `R(m, a)`. Abstractly from `l * κ = (l * a⁻¹) * (a * κ)`. -/
theorem s4g_tangent {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (m : LinfStar) :
    Rnm (fderiv ℂ (fun l => beltramiMul l κ) a m) (beltramiMul a κ) = Rnm m a := by
  set ai := beltramiInv a with hai_def
  have hai : ai ∈ LinfStarBall := grp_inv_mem ha
  set ν' := beltramiMul a κ with hν'_def
  have hν' : ν' ∈ LinfStarBall := bg_mul_mem_ball hκ ha
  have hdiff : ∀ {μ : LinfStar}, μ ∈ LinfStarBall → ∀ {l : LinfStar}, l ∈ LinfStarBall →
      HasFDerivAt (fun x => beltramiMul x μ) (fderiv ℂ (fun x => beltramiMul x μ) l) l :=
    fun hμ _ hl => ((bd_differentiableOn hμ) _ hl).differentiableAt (isOpen_ball.mem_nhds hl) |>.hasFDerivAt
  have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  set DR := fderiv ℂ (fun l => beltramiMul l ai) a with hDR
  -- `DR` inverts `D₀R_a`
  have hinv : ∀ x : LinfStar, DR (fderiv ℂ (fun σ => beltramiMul σ a) 0 x) = x := by
    have hR' : HasFDerivAt (fun l => beltramiMul l ai) DR (beltramiMul 0 a) := by
      rw [grp_zero_mul ha]
      exact hdiff hai ha
    have hc := hR'.comp (0 : LinfStar) (hdiff ha h0)
    have hid : (fun σ => beltramiMul (beltramiMul σ a) ai) =ᶠ[𝓝 (0 : LinfStar)] id := by
      filter_upwards [isOpen_ball.mem_nhds h0] with σ hσ
      rw [grp_mul_assoc hσ ha hai, hai_def, grp_mul_inv ha, grp_mul_zero hσ]
      rfl
    have hc' : HasFDerivAt id (DR.comp (fderiv ℂ (fun σ => beltramiMul σ a) 0)) (0 : LinfStar) :=
      hc.congr_of_eventuallyEq hid.symm
    have he := hc'.unique (hasFDerivAt_id (0 : LinfStar))
    intro x
    exact congrArg (fun L : LinfStar →L[ℂ] LinfStar => L x) he
  -- `l * κ = (l * a⁻¹) * (a * κ)` near `a`
  have hfun : (fun l => beltramiMul l κ) =ᶠ[𝓝 a] fun l => beltramiMul (beltramiMul l ai) ν' := by
    filter_upwards [isOpen_ball.mem_nhds ha] with l hl
    rw [grp_mul_assoc hl hai hν', hν'_def, ← grp_mul_assoc hai ha hκ, hai_def, grp_inv_mul ha, grp_zero_mul hκ]
  have hS : HasFDerivAt (fun σ => beltramiMul σ ν') (fderiv ℂ (fun σ => beltramiMul σ ν') 0)
      (beltramiMul a ai) := by
    rw [hai_def, grp_mul_inv ha]
    exact hdiff hν' h0
  have hcomp := (hS.comp a (hdiff hai ha)).congr_of_eventuallyEq hfun
  rw [hcomp.fderiv]
  show Rnm (fderiv ℂ (fun σ => beltramiMul σ ν') 0 (DR m)) ν' = Rnm m a
  rw [hb_Rnm_D0Right hν' (DR m)]
  have h1 := hinv (Rnm m a)
  rw [hb_D0Right_Rnm ha m] at h1
  exact h1

/-- `‖a + t m‖₂ ≤ ‖a‖₂ + ‖m‖₂` for `|t| ≤ 1`. -/
theorem s4g_normL2_line (a : LinfStar) {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) {t : ℂ}
    (ht : ‖t‖ ≤ 1) :
    normL2 unitDiscExterior ⇑(a + t • toLinf m) ≤ normL2 unitDiscExterior ⇑a + normL2 unitDiscExterior m := by
  have hmL := d2_harmonicL2_memLp hm
  have hae : (⇑(a + t • toLinf m) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] fun z => a z + t * m z := by
    filter_upwards [Lp.coeFn_add a (t • toLinf m), Lp.coeFn_smul t (toLinf m), bc_toLinf_ae hmL] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
  rw [grp_normL2_congr_ae hae]
  refine (gtp_normL2_add_le (Lp.aestronglyMeasurable a) (hmL.aestronglyMeasurable.const_mul t)).trans (add_le_add le_rfl ?_)
  rw [normL2_const_mul]
  have h1 : (‖t‖₊ : ℝ≥0∞) ≤ 1 := by exact_mod_cast ht
  calc (‖t‖₊ : ℝ≥0∞) * normL2 unitDiscExterior m ≤ 1 * normL2 unitDiscExterior m := by gcongr
    _ = _ := one_mul _

/-- The entries of `B₁` along the off-centre chart line `t ↦ (a + tm) * κ` are holomorphic near `t = 0`. -/
theorem s4g_off_entries {κ a : LinfStar} (hκ : κ ∈ LinfStarBall) (ha : a ∈ LinfStarBall) (mh : LinfStar) :
    ∃ r > 0, (∀ t ∈ ball (0 : ℂ) r, a + t • mh ∈ LinfStarBall) ∧
      ∀ m n, DifferentiableOn ℂ (fun t => B1 (grunsky (fsans (beltramiMul (a + t • mh) κ))
        (gsans (beltramiMul (a + t • mh) κ))) m n) (ball (0 : ℂ) r) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set r₀ : ℝ := (1 - ‖a‖) / (‖mh‖ + 1) with hr₀
  have hr₀pos : 0 < r₀ := div_pos (by linarith) (by positivity)
  have hsm : ∀ t ∈ ball (0 : ℂ) r₀, a + t • mh ∈ LinfStarBall := by
    intro t ht
    have htn : ‖t‖ < r₀ := by simpa using ht
    have h1 : ‖t‖ * (‖mh‖ + 1) < 1 - ‖a‖ := by
      rw [hr₀, lt_div_iff₀ (by positivity)] at htn; exact htn
    simp only [LinfStarBall, mem_ball_zero_iff]
    calc ‖a + t • mh‖ ≤ ‖a‖ + ‖t‖ * ‖mh‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ < 1 := by nlinarith [norm_nonneg t, norm_nonneg mh]
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, beltramiMul (a + t • mh) κ ∈ LinfStarBall := fun t ht =>
    bg_mul_mem_ball hκ (hsm t ht)
  refine ⟨r₀, hr₀pos, hsm, ?_⟩
  have hU : IsOpen (ball (0 : ℂ) r₀) := isOpen_ball
  have hpath : DifferentiableOn ℂ (fun t : ℂ => beltramiMul (a + t • mh) κ) (ball (0 : ℂ) r₀) := by
    intro t ht
    have h1 := ((bd_differentiableOn hκ) _ (hsm t ht)).differentiableAt (isOpen_ball.mem_nhds (hsm t ht))
    have h2 : DifferentiableAt ℂ (fun t : ℂ => a + t • mh) t :=
      (differentiableAt_id.smul_const mh).const_add a
    exact (h1.comp t h2).differentiableWithinAt
  have hpm := fun t (ht : t ∈ ball (0 : ℂ) r₀) =>
    AppB.b8_pair_model (AppB.b8_welding_normalized_pair (hball t ht))
  have hbd : ∀ t ∈ ball (0 : ℂ) r₀, ∀ m n,
      ‖B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) m n‖ ≤ 1 := by
    intro t ht m n
    obtain ⟨hs, hle⟩ := (hpm t ht).2.1 m
    have h1 : ‖B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) m n‖ ^ 2
        ≤ 1 := (hs.le_tsum n (fun _ _ => sq_nonneg _)).trans hle
    nlinarith [norm_nonneg (B1 (grunsky (fsans (beltramiMul (a + t • mh) κ))
      (gsans (beltramiMul (a + t • mh) κ))) m n)]
  intro m n
  let c : ℂ → ℕ → ℕ → ℂ := fun t p q =>
    B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p q *
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
          (π : ℂ) * kerK1 (fsans (beltramiMul (a + t • mh) κ)) z w) (ball (0 : ℂ) r₀) := by
        refine DifferentiableOn.const_mul ?_ _
        exact (l27_kerK1_differentiableOn hz1 hw1 hzw).comp hpath (fun t ht => hball t ht)
      refine hdiffK.congr (fun t ht => ?_)
      have hs := ((hpm t ht).2.2.2 z hz1 w hw1 hzw).mul_left (π : ℂ)
      refine (HasSum.tsum_eq ?_)
      refine hs.congr_fun (fun p => ?_)
      have e := AppB.b1_basis_weight p.1 p.2 z w
      calc c t p.1 p.2 * z ^ p.1 * w ^ p.2
          = B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p.1 p.2 *
            ((Real.sqrt (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) : ℂ) * z ^ p.1 * w ^ p.2) := by
            simp only [c]; ring
        _ = B1 (grunsky (fsans (beltramiMul (a + t • mh) κ)) (gsans (beltramiMul (a + t • mh) κ))) p.1 p.2 *
            ((π : ℂ) * (basisE p.1 z * basisE p.2 w)) := by rw [e]
        _ = _ := by ring) m n
  have hne : ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hc.div_const ((Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ)).congr (fun t ht => ?_)
  simp only [c]
  field_simp

/-- A uniform Hilbert–Schmidt bound for `B₁` along the off-centre chart line `t ↦ (a + tm) * κ`. -/
theorem s4g_off_uniform {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    ∃ r > 0, ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ t ∈ closedBall (0 : ℂ) r,
      a + t • toLinf m ∈ LinfStarBall ∧ ‖a + t • toLinf m‖ < delta0 ∧
        (∑' q : ℕ × ℕ, (‖B1 (grunsky (fsans (beltramiMul (a + t • toLinf m) κ))
          (gsans (beltramiMul (a + t • toLinf m) κ))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M := by
  have hd := delta0_bounds
  set mh := toLinf m with hmh
  have hmhH : mh ∈ harmonicBeltrami := (harmonicL2_subset_harmonic.choose_spec m hm).1
  have hm' := hm
  obtain ⟨-, -, -, hmL⟩ := hm'
  set r : ℝ := min 1 ((delta0 - ‖a‖) / (2 * (‖mh‖ + 1))) with hr
  have hr0 : 0 < r := lt_min one_pos (div_pos (by linarith) (by positivity))
  set H : ℝ≥0∞ := ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 with hH
  have hHf : H < ∞ := gk_K1_T01 _ hκT ⟨κ, hκ⟩ rfl
  set N : ℝ≥0∞ := normL2 unitDiscExterior ⇑a + normL2 unitDiscExterior m with hN
  have hNf : N < ∞ := ENNReal.add_lt_top.2 ⟨haL, hmL⟩
  set S : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - delta0) ^ 2) * N) ^ 2 with hS
  have hSf : S < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hNf))
  refine ⟨r, hr0, 2 * S + 2 * H, ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hSf,
    ENNReal.mul_lt_top (by norm_num) hHf⟩, ?_⟩
  intro t ht
  have htn : ‖t‖ ≤ r := by simpa using ht
  have ht1 : ‖t‖ ≤ 1 := htn.trans (min_le_left _ _)
  have ht2 : ‖t‖ ≤ (delta0 - ‖a‖) / (2 * (‖mh‖ + 1)) := htn.trans (min_le_right _ _)
  have hsm : ‖a + t • mh‖ < delta0 := by
    have h1 : ‖t‖ * (2 * (‖mh‖ + 1)) ≤ delta0 - ‖a‖ := by
      rw [le_div_iff₀ (by positivity)] at ht2; exact ht2
    calc ‖a + t • mh‖ ≤ ‖a‖ + ‖t‖ * ‖mh‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ < delta0 := by nlinarith [norm_nonneg t, norm_nonneg mh]
  have hmem : a + t • mh ∈ LinfStarBall := mem_ball_zero_iff.mpr (hsm.trans hd.2)
  have hharm : a + t • mh ∈ harmonicBeltrami := Submodule.add_mem _ ha (Submodule.smul_mem _ t hmhH)
  have hγ : beltramiMul (a + t • mh) κ ∈ LinfStarBall := bg_mul_mem_ball hκ hmem
  refine ⟨hmem, hsm, ?_⟩
  have hstep := s4g_step_bound (κ := ⟨κ, hκ⟩) (ν := ⟨a + t • mh, hmem⟩) hharm hsm
  have hle : ENNReal.ofReal (1 / (4 * π)) *
      (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖a + t • mh‖) ^ 2) * normL2 unitDiscExterior ⇑(a + t • mh)) ^ 2 ≤ S := by
    have hA : ENNReal.ofReal (Real.sqrt 2 / (1 - ‖a + t • mh‖) ^ 2) ≤
        ENNReal.ofReal (Real.sqrt 2 / (1 - delta0) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have h1 : 0 < 1 - delta0 := by linarith [hd.2]
      have h2 : 1 - delta0 ≤ 1 - ‖a + t • mh‖ := by linarith
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
    have hB : normL2 unitDiscExterior ⇑(a + t • mh) ≤ N := s4g_normL2_line a hm ht1
    rw [hS]
    exact mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (mul_le_mul' hA hB) 2)
  rw [t210_hs_eq hγ]
  calc ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (beltramiMul (a + t • mh) κ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ q in unitDisc ×ˢ unitDisc,
          (2 * (‖kerK1 (fsans (beltramiMul (a + t • mh) κ)) q.1 q.2 - kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
        lintegral_mono fun q => gk_sq_tri _ _
    _ = 2 * (∫⁻ q in unitDisc ×ˢ unitDisc,
            (‖kerK1 (fsans (beltramiMul (a + t • mh) κ)) q.1 q.2 - kerK1 (fsans κ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * H := by
        rw [lintegral_add_right' _ ((gk_kerK1_aemeas hκ).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * S + 2 * H := by
        gcongr
        exact hstep.trans hle

/-- A measurable function of finite weighted `L²` norm has an integrable weighted square. -/
theorem s4g_sq_integrable {R : ℂ → ℂ} (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hR : normL2 unitDiscExterior R < ∞) :
    IntegrableOn (fun z => ‖R z‖ ^ 2 * rho z) unitDiscExterior := by
  have hf : (∫⁻ z in unitDiscExterior,
      (‖R z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp hR
  refine ⟨(hRm.norm.pow 2).mul (wp_rho_continuousOn.aestronglyMeasurable wp_exterior_isOpen.measurableSet), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun z => mul_nonneg (sq_nonneg _) (wp_rho_nonneg z)))]
  simpa only [ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm, enorm_eq_nnnorm] using hf

/-- Absolute integrability of the pairing of `A₂(𝔻*)` with a weighted-`L²` coefficient. -/
theorem s4g_pair_integrable {φ R : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior)) (hR : normL2 unitDiscExterior R < ∞) :
    IntegrableOn (fun z => φ z * R z) unitDiscExterior := by
  have hi := (A2fun.integrable_weighted_sq wp_exterior_isOpen hφ).add (s4g_sq_integrable hRm hR)
  apply hi.mono' ((hφ.1.continuousOn.aestronglyMeasurable wp_exterior_isOpen.measurableSet).mul hRm)
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with z hz
  change ‖φ z * R z‖ ≤ ‖φ z‖ ^ 2 * (rho z)⁻¹ + ‖R z‖ ^ 2 * rho z
  rw [norm_mul]
  exact s3st_weighted_pair_bound ‖φ z‖ ‖R z‖ (wp_rho_pos hz)

/-- Pairings with `A₂(𝔻*)` do not see the harmonic projection: `∬ φ R = ∬ φ P(R)` (TT:551, (1.7)). -/
theorem s4g_proj_pair (R : LinfStar) (hR : normL2 unitDiscExterior ⇑R < ∞) {m' : ℂ → ℂ}
    (hm' : m' ∈ harmonicL2 unitDiscExterior)
    (hP : (⇑(harmonicProj R) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] m')
    {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) :
    ∫ z in unitDiscExterior, φ z * R z = ∫ z in unitDiscExterior, φ z * m' z := by
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  set ψ : ℂ → ℂ := fun z => (rho z : ℂ)⁻¹ * conj (φ z) with hψdef
  have hrep : ∀ z ∈ unitDiscExterior, ψ z = (rho z : ℂ)⁻¹ * conj (φ z) := fun z _ => rfl
  have hcircle : ∀ z ∈ unitDiscExterior, ‖z‖ ≠ 1 := fun z hz => ne_of_gt hz
  have hψ : ψ ∈ harmonicL2 unitDiscExterior := by
    refine ⟨φ, hφ.1, hrep, ?_⟩
    rw [← normA2_eq_normL2_of_harmonic hE hcircle hrep]
    exact hφ.2
  have horth := (harmonicProj_orthogonal R hR).2 ψ hψ
  have hpt : ∀ z ∈ unitDiscExterior, (R z - harmonicProj R z) * conj (ψ z) * rho z =
      φ z * R z - φ z * harmonicProj R z := by
    intro z hz
    have hρ : (rho z : ℂ) ≠ 0 := ofReal_ne_zero.2 (wp_rho_pos hz).ne'
    simp only [hψdef, map_mul, map_inv₀, conj_ofReal, Complex.conj_conj]
    field_simp
  rw [setIntegral_congr_fun hE hpt] at horth
  have hi1 := s4g_pair_integrable hφ (Lp.aestronglyMeasurable R) hR
  have hi2 : IntegrableOn (fun z => φ z * harmonicProj R z) unitDiscExterior := by
    refine (s3st_pair_integrable hφ hm').congr ?_
    filter_upwards [hP] with z hz
    rw [hz]
  rw [integral_sub hi1 hi2, sub_eq_zero] at horth
  rw [horth]
  apply integral_congr_ae
  filter_upwards [hP] with z hz
  rw [hz]

/-- A bounded coefficient of finite weighted `L²` norm represents a point of `T₀(1)` (Cui's bound and Corollary 3.2). -/
theorem s4g_T01_of_L2 {a : LinfStar} (ha : a ∈ LinfStarBall) (haL : normL2 unitDiscExterior ⇑a < ∞) :
    Phi ⟨a, ha⟩ ∈ T01 := by
  rw [cor_3_2]
  show AInf.toFun (bers (Phi ⟨a, ha⟩)) ∈ A2fun unitDisc
  rw [bers_Phi]
  refine ⟨(bersPhi a).2, ?_⟩
  obtain ⟨C, -, hC⟩ := CUI.cui_A2_bound (k := ‖a‖) (norm_nonneg _) (mem_ball_zero_iff.1 ha)
  exact (hC a le_rfl).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top haL)

/-- The off-centre point `[a * κ]` lies in `T₀(1)`. -/
theorem s4g_T01_mul {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hκT : Phi ⟨κ, hκ⟩ ∈ T01) {a : LinfStar}
    (ha : a ∈ LinfStarBall) (haL : normL2 unitDiscExterior ⇑a < ∞) :
    Phi ⟨beltramiMul a κ, bg_mul_mem_ball hκ ha⟩ ∈ T01 := by
  have h := TakhtajanTeo.lemma_3_4.2.1 _ (s4g_T01_of_L2 ha haL) _ hκT
  rwa [gtp_mulT_phi] at h

/-- The verified source-coordinate kernel variation along any coefficient tangent `θ`, transported to the mixed
`K₂`-product integral of `R(θ, ν)` (`s3kv_transport` without the harmonic tangent). -/
theorem s4g_transport {ν : LinfStar} (hν : ν ∈ LinfStarBall) (θ : LinfStar) {z w : ℂ}
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    (1/π^2*(deriv (qcv_planeSolution ν) z*deriv (qcv_planeSolution ν) w)*
      ∫ u in unitDiscExterior, θ u*dz (qcv_planeSolution ν) u^2 /
        ((qcv_planeSolution ν u-qcv_planeSolution ν z)^2*
          (qcv_planeSolution ν u-qcv_planeSolution ν w)^2)) =
      ∫ u in unitDiscExterior, Rnm θ ν u*kerK2 (fsans ν) (gsans ν) z u*kerK2 (fsans ν) (gsans ν) w u := by
  let f := fsans ν
  let g := gsans ν
  let W := qcv_planeSolution ν
  let Q := deriv W z*deriv W w*∫ u in unitDiscExterior,
    θ u*dz W u^2/((W u-W z)^2*(W u-W w)^2)
  let J := ∫ u in unitDiscExterior, Rnm θ ν u*deriv g u^2/((g u-f z)^2*(g u-f w)^2)
  have hf := S2C.s2c_conf_f hν
  have hzf : f z ∈ f '' unitDisc := ⟨z,hz,rfl⟩
  have hwf : f w ∈ f '' unitDisc := ⟨w,hw,rfl⟩
  have hzwf : f z ≠ f w := fun hh => hzw (hf.2.1 hz hw hh)
  have hzInv := hf.2.1.leftInvOn_invFunOn hz
  have hwInv := hf.2.1.leftInvOn_invFunOn hw
  have hdzInv : deriv (Function.invFunOn f unitDisc) (f z) = (deriv f z)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul isOpen_ball hf hz)
  have hdwInv : deriv (Function.invFunOn f unitDisc) (f w) = (deriv f w)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul isOpen_ball hf hw)
  have htr := l27_transport hν θ hzf hwf hzwf
  dsimp only at htr
  rw [hzInv,hwInv,hdzInv,hdwInv,
    l27_g_transport wp_exterior_isOpen (S2C.s2c_conf_g hν)] at htr
  change Q*(deriv f z)⁻¹*(deriv f w)⁻¹ = _ at htr
  have hz1 : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hw1 : deriv f w ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hw
  have hQ : Q = deriv f z*deriv f w*J := by
    calc
      Q = (Q*(deriv f z)⁻¹*(deriv f w)⁻¹)*deriv f z*deriv f w := by field_simp <;> ring
      _ = deriv f z*deriv f w*J := by rw [htr]; ring
  change (1/π^2)*(deriv W z*deriv W w)*_ = _
  calc
    _ = (1/π^2)*Q := by dsimp only [Q]; ring
    _ = ((1/π^2)*deriv f z*deriv f w)*J := by rw [hQ]; ring
    _ = ∫ u in unitDiscExterior, ((1/π^2)*deriv f z*deriv f w)*
        (Rnm θ ν u*deriv g u^2/((g u-f z)^2*(g u-f w)^2)) := (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [f,g]
      rw [kerK2,kerK2,
        show (fsans ν z-gsans ν u)^2 = (gsans ν u-fsans ν z)^2 by ring,
        show (fsans ν w-gsans ν u)^2 = (gsans ν u-fsans ν w)^2 by ring]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring

/-- The product of two mixed kernel rows is an `A₂(𝔻*)` function: it is the diagonal of a rank-one HS matrix. -/
theorem s4g_K2_A2 {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    (fun u => kerK2 (fsans ν) (gsans ν) z u * kerK2 (fsans ν) (gsans ν) w u) ∈ A2fun unitDiscExterior := by
  let C := gopOp (B3 (grunsky (fsans ν) (gsans ν)))
  have h := s3tp_diagonal_A2 (s3tp_rank (C (s3kv_vector z)) (C (s3kv_vector w)))
  refine (ab112_A2fun_congr wp_exterior_isOpen ?_).mp h
  intro u hu
  show s3tp_eval u _ = _
  rw [s3tp_eval_apply, s3tp_rank_diagonal, s3sv_mixed_eval hν hz hu, s3sv_mixed_eval hν hw hu]

/-- The actual HS derivative of `B₁` along the off-centre chart line `t ↦ (a + tm) * κ`, with its kernel:
`K̇(z, w) = ∬_{𝔻*} K₂(z, u) K₂(w, u) R(m, a)(u) d²u` at the base `a * κ`. -/
theorem s4g_off_chart_data {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    ∃ F : ℂ → s3tc_HS, ∃ d : s3tc_HS,
      (∀ᶠ t in 𝓝 (0 : ℂ), beltramiMul (a + t • toLinf m) (κ : LinfStar) ∈ LinfStarBall ∧
        ∀ q : ℕ × ℕ, F t q = B1 (grunsky (fsans (beltramiMul (a + t • toLinf m) (κ : LinfStar)))
          (gsans (beltramiMul (a + t • toLinf m) (κ : LinfStar)))) q.1 q.2) ∧
      HasDerivAt F d 0 ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → s3kv_eval z w d = ∫ u in unitDiscExterior,
        kerK2 (fsans (beltramiMul a (κ : LinfStar))) (gsans (beltramiMul a (κ : LinfStar))) z u *
          kerK2 (fsans (beltramiMul a (κ : LinfStar))) (gsans (beltramiMul a (κ : LinfStar))) w u *
            Rnm (toLinf m) a u := by
  have hd := delta0_bounds
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hν' : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 ha1
  obtain ⟨r₁, hr₁, hball₁, hent⟩ := s4g_off_entries κ.2 ha1 (toLinf m)
  obtain ⟨r₂, hr₂, M, hM, hb⟩ := s4g_off_uniform κ.2 hκ ha has haL hm
  set c : ℂ → ℕ → ℕ → ℂ := fun t => B1 (grunsky (fsans (beltramiMul (a + t • toLinf m) (κ : LinfStar)))
    (gsans (beltramiMul (a + t • toLinf m) (κ : LinfStar)))) with hcdef
  set r : ℝ := min (r₁ / 2) r₂ with hrdef
  have hr : 0 < r := lt_min (by positivity) hr₂
  have hc : ∀ p q, DifferentiableOn ℂ (fun t => c t p q) (ball (0 : ℂ) (2 * r)) :=
    fun p q => (hent p q).mono (ball_subset_ball (by rw [hrdef]; linarith [min_le_left (r₁ / 2) r₂]))
  have hb' : ∀ t ∈ closedBall (0 : ℂ) r, (∑' q : ℕ × ℕ, (‖c t q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤ M := fun t ht =>
    (hb t (closedBall_subset_closedBall (min_le_right _ _) ht)).2.2
  have hlim := t210_hs_tendsto (c := c) hr hc hM hb'
  have hhs : ∀ᶠ t in 𝓝 (0 : ℂ), Summable (fun q : ℕ × ℕ => ‖c t q.1 q.2‖ ^ 2) := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) hr] with t ht
    exact s3fv_hs_of_ennreal ((hb' t ht).trans_lt hM)
  obtain ⟨F, d, he, -, hF⟩ := s3fv_hilbert_derivative (A := c) (D := fun p q => deriv (fun s => c s p q) 0) hhs hlim
  have hbo : ∀ t ∈ ball (0 : ℂ) r₁, beltramiMul (a + t • toLinf m) (κ : LinfStar) ∈ LinfStarBall :=
    fun t ht => bg_mul_mem_ball κ.2 (hball₁ t ht)
  have hpath : HasDerivAt (fun t : ℂ => beltramiMul (a + t • toLinf m) (κ : LinfStar))
      (fderiv ℂ (fun l => beltramiMul l (κ : LinfStar)) a (toLinf m)) 0 := by
    have hL := (((bd_differentiableOn κ.2) a ha1).differentiableAt (isOpen_ball.mem_nhds ha1)).hasFDerivAt
    have hline : HasDerivAt (fun t : ℂ => a + t • toLinf m) (toLinf m) 0 := by
      simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const (toLinf m)).const_add a
    exact hL.comp_hasDerivAt_of_eq 0 hline (by simp)
  refine ⟨F, d, ?_, hF, ?_⟩
  · filter_upwards [he, ball_mem_nhds (0 : ℂ) hr₁] with t ht htr
    exact ⟨hbo t htr, ht⟩
  intro z hz w hw hzw
  have hKo : HasDerivAt (fun t : ℂ => kerK1 (fsans (beltramiMul (a + t • toLinf m) (κ : LinfStar))) z w)
      (s3kv_eval z w d) 0 := by
    have h1 := (s3kv_eval z w).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hF
    apply h1.congr_of_eventuallyEq
    filter_upwards [he, ball_mem_nhds (0 : ℂ) hr₁] with t ht htr
    have hop : s3tc_toOperator (F t) = gopOp (c t) := by
      change gopOp (fun m n => F t (m,n)) = _
      congr 1
      funext p q
      exact ht (p,q)
    change _ = s3kv_eval z w (F t)
    rw [s3kv_eval_apply, hop]
    exact (s3kv_B1_kernel (hbo t htr) hz hw hzw).symm
  have hKν := ((l27_kerK1_differentiableOn hz hw hzw _ hν').differentiableAt
    (isOpen_ball.mem_nhds hν')).hasFDerivAt
  have hc1 := hKν.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hlin : HasDerivAt (fun t : ℂ => beltramiMul a (κ : LinfStar) +
      t • fderiv ℂ (fun l => beltramiMul l (κ : LinfStar)) a (toLinf m))
      (fderiv ℂ (fun l => beltramiMul l (κ : LinfStar)) a (toLinf m)) 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const _).const_add _
  have hc2 := hKν.comp_hasDerivAt_of_eq 0 hlin (by simp)
  have hform := hc2.unique (l27_kerK1_line hν' _ hz hw hzw)
  rw [hKo.unique hc1, hform, s4g_transport hν' _ hz hw hzw, s4g_tangent κ.2 ha1 (toLinf m)]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- **Shared lemma (S₂).** The derivative of `S₂` along the chart line `t ↦ [(a + tm) * κ]` of `V_κ` at `t = 0`:
`-(1/6π) ∬_{𝔻*} 𝒮(g_{a*κ}) R(m, a) d²z`. -/
theorem s4g_S2_offcentre_variation {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    DifferentiableAt ℝ (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
      dz (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 =
        -(1 / (6 * π)) * ∫ z in unitDiscExterior,
          schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z := by
  have hd := delta0_bounds
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hν' : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 ha1
  have hν'T : Phi ⟨beltramiMul a (κ : LinfStar), hν'⟩ ∈ T01 := s4g_T01_mul κ.2 hκ ha1 haL
  have hRL : normL2 unitDiscExterior ⇑(Rnm (toLinf m) a) < ∞ := WPCV.x5_Rnm_L2 hm ha1
  obtain ⟨⟨m', hm', hPm⟩, -⟩ := harmonicProj_orthogonal (Rnm (toLinf m) a) hRL
  obtain ⟨Fc, dc, hec, hFc, -, hkc⟩ := s3kv_chart_data hν' hν'T hm'
  obtain ⟨Fo, d₀, heo, hFo, hko⟩ := s4g_off_chart_data hκ ha has haL hm
  -- equal HS derivatives, by their kernels
  have hdeq : d₀ = dc := by
    apply s3sv_eval_injective
    intro z hz w hw hzw
    rw [hko z hz w hw hzw, s4g_proj_pair (Rnm (toLinf m) a) hRL hm' hPm (s4g_K2_A2 hν' hz hw),
      (hkc z hz w hw hzw).2]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  -- equal HS values at `0`
  have hF0 : Fo 0 = Fc 0 := by
    apply lp.ext
    funext q
    have h1 := (heo.self_of_nhds).2 q
    have h2 := hec.self_of_nhds q
    simp only [zero_smul, add_zero] at h1
    simp only [zero_smul, grp_zero_mul hν'] at h2
    rw [h1, h2]
  have hgap : ‖s3tc_toOperator (Fo 0)‖ < 1 := by
    have hop0 : s3tc_toOperator (Fo 0) = gopOp (B1 (grunsky (fsans (beltramiMul a (κ : LinfStar)))
        (gsans (beltramiMul a (κ : LinfStar))))) := by
      change gopOp (fun m n => Fo 0 (m,n)) = _
      congr 1
      funext p q
      have h1 := (heo.self_of_nhds).2 (p, q)
      simp only [zero_smul, add_zero] at h1
      exact h1
    rw [hop0]
    exact (pgb_norm_lt_one hν').1
  obtain ⟨-, hLog⟩ := s3fd_logSeries_hasFDeriv (Fo 0) hgap
  -- the two `S₂` germs
  have hgo : (fun t => liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar)))) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => s3fd_logSeries (Fo t)) := by
    filter_upwards [heo] with t ht
    rw [ptT, dif_pos ht.1]
    exact (s3fd_liouville_eq ht.1 (Fo t) (fun p q => ht.2 (p,q))).symm
  have hcball : ∀ᶠ t in 𝓝 (0 : ℂ), beltramiMul (t • toLinf m') (beltramiMul a (κ : LinfStar)) ∈ LinfStarBall := by
    have hcont : Continuous (fun t : ℂ => t • toLinf m') := continuous_id.smul continuous_const
    have h0 : (fun t : ℂ => t • toLinf m') 0 ∈ LinfStarBall := by simp [LinfStarBall]
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0)] with t ht
    exact bg_mul_mem_ball hν' ht
  have hgc : (fun t => liouvilleS2 (ptT (beltramiMul (t • toLinf m') (beltramiMul a (κ : LinfStar)))))
      =ᶠ[𝓝 (0 : ℂ)] (fun t => s3fd_logSeries (Fc t)) := by
    filter_upwards [hec, hcball] with t ht hbt
    rw [ptT, dif_pos hbt]
    exact (s3fd_liouville_eq hbt (Fc t) (fun p q => ht (p,q))).symm
  have hDo := (hLog.comp (0 : ℂ) (hFo.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq hgo
  have hFc' : HasDerivAt Fc d₀ 0 := hdeq ▸ hFc
  have hLogc : HasFDerivAt s3fd_logSeries (∑' N, fderiv ℝ (s3fd_coeff N) (Fo 0)) (Fc 0) := hF0 ▸ hLog
  have hDc := (hLogc.comp (0 : ℂ) (hFc'.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq hgc
  have hCo : HasFDerivAt (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar))) : ℂ))
      _ 0 := ((ofRealCLM.hasFDerivAt).comp (0 : ℂ) hDo).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => by simp)
  have hCc : HasFDerivAt (fun e : ℂ => (liouvilleS2 (ptT (beltramiMul (e • toLinf m') (beltramiMul a (κ : LinfStar))))
      : ℂ)) _ 0 := ((ofRealCLM.hasFDerivAt).comp (0 : ℂ) hDc).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => by simp)
  have hdz : dz (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar))) : ℂ)) 0 =
      bersDz liouvilleS2 (beltramiMul a (κ : LinfStar)) m' := by
    show (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2 = (fderiv ℝ _ 0 1 - I * fderiv ℝ _ 0 I) / 2
    rw [hCo.fderiv, hCc.fderiv]
  refine ⟨hCo.differentiableAt, ?_⟩
  rw [hdz, s3sv_first_variation hν' hν'T hm']
  congr 1
  -- `∬ 𝒮(g) m' = ∬ 𝒮(g) R(m, a)`, since `𝒮(g) ∈ A₂(𝔻*)`
  have hS : schwarzianHol (gsans (beltramiMul a (κ : LinfStar))) ∈ A2fun unitDiscExterior := by
    have hv := (vartheta_spec (Phi ⟨_, hν'⟩)).1.1 hν'T
    exact (ab112_A2fun_congr wp_exterior_isOpen ((vartheta_spec (Phi ⟨_, hν'⟩)).2 ⟨_, hν'⟩ rfl)).mpr hv
  rw [← s4g_proj_pair (Rnm (toLinf m) a) hRL hm' hPm hS]
  apply integral_congr_ae
  filter_upwards [WPCV.wpcv_RnmFun_ae ha1 (toLinf m)] with u hu
  rw [hu]

/-- **Consumer form (S₁)**, from the S₂ form and `S₂ = -(1/12π) S₁` on `T₀(1)` (Theorem 3.8, clause 1). -/
theorem s4g_S1_offcentre_variation (h38 : ∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p)
    {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {a : LinfStar}
    (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior) :
    DifferentiableAt ℝ (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
      dz (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 =
        2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z := by
  have hd := delta0_bounds
  obtain ⟨hD, hV⟩ := s4g_S2_offcentre_variation hκ ha has haL hm
  have hm' := hm
  obtain ⟨-, -, -, hmL⟩ := hm'
  -- near `0` the chart points lie in `T₀(1)`, where `S₁ = -12π S₂`
  have hev : (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar))) : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      fun t => (-(12 * π) : ℂ) * (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar))) : ℂ) := by
    have hcont : Continuous (fun t : ℂ => a + t • toLinf m) := continuous_const.add (continuous_id.smul continuous_const)
    have h0 : (fun t : ℂ => a + t • toLinf m) 0 ∈ LinfStarBall := by
      show a + (0 : ℂ) • toLinf m ∈ LinfStarBall
      rw [zero_smul, add_zero]
      exact mem_ball_zero_iff.mpr (has.trans hd.2)
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0),
      closedBall_mem_nhds (0 : ℂ) one_pos] with t ht ht1
    have hbt : a + t • toLinf m ∈ LinfStarBall := ht
    have hL : normL2 unitDiscExterior ⇑(a + t • toLinf m) < ∞ :=
      (s4g_normL2_line a hm (by simpa using ht1)).trans_lt (ENNReal.add_lt_top.2 ⟨haL, hmL⟩)
    have hT := s4g_T01_mul κ.2 hκ hbt hL
    have hpt : ptT (beltramiMul (a + t • toLinf m) (κ : LinfStar)) = Phi ⟨_, bg_mul_mem_ball κ.2 hbt⟩ := by
      unfold ptT
      rw [dif_pos (bg_mul_mem_ball κ.2 hbt)]
    rw [hpt, h38 _ hT]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp
  have hc : (-(12 * π) : ℂ) ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    exact neg_ne_zero.2 (mul_ne_zero (by norm_num) hπ)
  refine ⟨(hD.const_mul _).congr_of_eventuallyEq hev, ?_⟩
  rw [l613_dz_congr hev, e62_dz_const_mul hc, hV]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

end Ch2
end TakhtajanTeo
