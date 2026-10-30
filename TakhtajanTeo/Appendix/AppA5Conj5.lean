import TakhtajanTeo.Appendix.A_HilbertStructure
import TakhtajanTeo.Appendix.BergmanPeriodModel
import TakhtajanTeo.Ch2.S1_Theorem112Completed
import TakhtajanTeo.Ch1.BanachSubmersion
import TakhtajanTeo.Ch1.GroupChain1
import TakhtajanTeo.Ch1.GroupTopology
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch2.S3_Completed
import TakhtajanTeo.Ch1.S2Core
import TakhtajanTeo.Ch2.S2_Completed4
import TakhtajanTeo.Ch1.HilbertBersDifferentialL2

/-!
# Appendix A, Lemma A.5 (ii): openness of `β̂*(T₀(1))` in `Ã₂¹(𝔻*)` (`a55_`, 下属2)

Host: new module `Appendix/AppA5Conj5.lean`. It does not import `AppACompleted2`; there the fifth conjunct of
`lemma_A_5` becomes `a55_conj5 appa2_lemma_A_5_clause appa2_preSchwarzian_cubic` (one import added).

Route (no inverse function theorem: `Ψ*` is injective on `Ã₂¹(𝔻*)`, `PsiOp_injective_on_A21tildeExt`):
1. reduce `β̂*(p, w)` to `𝒜(𝗀_q)`, `q ∈ T₀(1)` (the fourth conjunct, `hclause`);
2. `Ψ*` is continuous on `Ã₂¹(𝔻*)` into `A₂(𝔻*)` (`a55_ptwise_ext`, `a55_deriv_ext`, `a55_mul_ext`, `a55_psi_cont_ext`);
3. reflection `y ↦ \overline{K(\bar y)}`, `K(s) = Ψ*φ(1/s)/s⁴`, from `A₂(𝔻*)` to `A₂(𝔻)`, isometric (`a55_refl`,
   `a55_refl_norm`); on Schwarzians it exchanges `𝗀_μ` and `𝖿^{μ⁻¹}` (`a55_refl_schwarzian`);
4. the Bers image is open (`a55_bers_open`, from `bers_isOpenEmbedding` and `A2toAInf_bounded`), giving `q'` with
   `𝒮(𝖿^{q'})` = the reflected `Ψ*φ`; `q' ∈ T₀(1)` by `thm_1_12`; `p' = q'⁻¹ ∈ T₀(1)` by `lemma_3_4`;
5. `Ψ*φ = 𝒮(𝗀_{p'}) = Ψ*𝒜(𝗀_{p'})` on `𝔻*` and both lie in `Ã₂¹(𝔻*)` (`hcub`, `thm_1_12`), so `φ = 𝒜(𝗀_{p'})`.

Steps 2 and 4 are stated for reuse in `cor_A_2` (disc versions of step 2 to be added then).
Step 2 (`a55_ptwise_ext` … `a55_psi_cont_ext` and helpers) is by 下属4, step 3 (`a55_refl`, `a55_refl_norm`,
`a55_refl_schwarzian`) by 下属3.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC Ch2
namespace AppA

/-! ### Step 2: continuity of `Ψ*` on `Ã₂¹(𝔻*)` -/

/-- Quantitative point evaluation on `A₂¹(𝔻*)`: `(|z|² - 1)|φ(z)| ≤ ‖φ‖_{A₂¹}/√π`. -/
theorem a55_ptwise_ext {φ : ℂ → ℂ} (hφ : φ ∈ A21fun unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (‖z‖ ^ 2 - 1) * ‖φ z‖ ≤ (normA21 unitDiscExterior φ).toReal / Real.sqrt π := by
  have h := lemma_1_3 (Or.inr rfl) hφ z hz
  rw [← ENNReal.ofReal_toReal hφ.2.ne, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt π)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hz1 : 1 < ‖z‖ := hz
  have he : ‖(1 - ‖z‖ ^ 2 : ℂ) * φ z‖ = (‖z‖ ^ 2 - 1) * ‖φ z‖ := by
    rw [norm_mul]
    congr 1
    have : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = (1 - ‖z‖ ^ 2 : ℂ) := by push_cast; ring
    rw [← this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by nlinarith)]
    ring
  have he' : ‖((1 : ℂ) - (‖z‖ : ℂ) ^ 2) * φ z‖ = ‖(1 - ‖z‖ ^ 2 : ℂ) * φ z‖ := rfl
  rw [he', he] at h2
  calc (‖z‖ ^ 2 - 1) * ‖φ z‖ ≤ 1 / Real.sqrt π * (normA21 unitDiscExterior φ).toReal := h2
    _ = _ := by ring

/-- The squared `A₂¹` norm as a lintegral. -/
theorem a55_normA21_sq (D : Set ℂ) (φ : ℂ → ℂ) :
    normA21 D φ ^ 2 = ∫⁻ z in D, (‖φ z‖₊ : ℝ≥0∞) ^ 2 := by
  unfold normA21
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The squared `A₂` norm as a lintegral. -/
theorem a55_normA2_sq (D : Set ℂ) (φ : ℂ → ℂ) :
    normA2 D φ ^ 2 = ∫⁻ z in D, (‖φ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹ := by
  unfold normA2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- From squares to norms in `ℝ≥0∞`. -/
theorem a55_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h1 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h1
  norm_num at h1
  exact h1

/-- `ofReal ‖x‖² = ‖x‖₊²`. -/
theorem a55_ofReal_sq (x : ℂ) : ENNReal.ofReal (‖x‖ ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

/-- The coefficient comparison behind `a55_deriv_ext`. -/
theorem a55_coef_le (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (π / 2) * ((((n : ℝ) + 3) * a) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) ≤
      3 / 2 * (π * a ^ 2 / ((n : ℝ) + 1 + 1)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : (π / 2) * ((((n : ℝ) + 3) * a) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) =
      π * a ^ 2 * (((n : ℝ) + 3) / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    field_simp
  have e2 : 3 / 2 * (π * a ^ 2 / ((n : ℝ) + 1 + 1)) = π * a ^ 2 * (3 / (2 * ((n : ℝ) + 2))) := by
    field_simp
    ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `‖hk‖_{A₂(𝔻*)} ≤ C ‖h‖_{A₂¹(𝔻*)} ‖k‖_{A₂¹(𝔻*)}`. -/
theorem a55_mul_ext : ∃ C : ℝ, ∀ h ∈ A21fun unitDiscExterior, ∀ k ∈ A21fun unitDiscExterior,
    normA2 unitDiscExterior (fun z => h z * k z) ≤
      ENNReal.ofReal C * normA21 unitDiscExterior h * normA21 unitDiscExterior k := by
  refine ⟨1 / (2 * Real.sqrt π), fun h hh k hk => ?_⟩
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set N := (normA21 unitDiscExterior k).toReal with hN
  have hpt : ∀ z ∈ unitDiscExterior, ‖k z‖ ^ 2 * (rho z)⁻¹ ≤ (1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2 := by
    intro z hz
    have h1 := a55_ptwise_ext hk hz
    have hz1 : 1 < ‖z‖ := hz
    have hw : (rho z)⁻¹ = (‖z‖ ^ 2 - 1) ^ 2 / 4 := by
      unfold rho
      rw [inv_div]
      ring
    have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have h0 : 0 ≤ (‖z‖ ^ 2 - 1) * ‖k z‖ := by
      have : 0 ≤ ‖z‖ ^ 2 - 1 := by nlinarith
      positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    rw [hw]
    have e : (1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2 = (N / Real.sqrt π) ^ 2 / 4 := by
      field_simp
      ring
    rw [e]
    calc ‖k z‖ ^ 2 * ((‖z‖ ^ 2 - 1) ^ 2 / 4) = ((‖z‖ ^ 2 - 1) * ‖k z‖) ^ 2 / 4 := by ring
      _ ≤ _ := by gcongr
  apply a55_le_of_sq_le
  rw [a55_normA2_sq, mul_pow, mul_pow, a55_normA21_sq, a55_normA21_sq]
  have hk2 : (∫⁻ z in unitDiscExterior, (‖k z‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (N ^ 2) := by
    rw [← a55_normA21_sq, hN, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hk.2.ne]
  have hR : ENNReal.ofReal (1 / (2 * Real.sqrt π)) ^ 2 * (∫⁻ z in unitDiscExterior, (‖h z‖₊ : ℝ≥0∞) ^ 2) *
      ENNReal.ofReal (N ^ 2) =
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal ((1 / (2 * Real.sqrt π)) ^ 2 * N ^ 2) * (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  rw [hk2, hR]
  refine setLIntegral_mono' hE fun z hz => ?_
  rw [nnnorm_mul, ENNReal.coe_mul, mul_pow, mul_assoc, mul_comm (ENNReal.ofReal _)]
  gcongr
  have hc : ((‖k z‖₊ : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (rho z)⁻¹ = ENNReal.ofReal (‖k z‖ ^ 2 * (rho z)⁻¹) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), a55_ofReal_sq]
  rw [hc]
  exact ENNReal.ofReal_le_ofReal (hpt z hz)

/-- Weighted Taylor polynomial area. -/
theorem a55_taylor_weighted_area (d : ℕ → ℂ) (N : ℕ) :
    (∫ z in unitDisc, ‖(bergmanTaylorPoly d N).eval z‖ ^ 2 * (rho z)⁻¹) =
      (π / 2) * ∑ n ∈ Finset.range N, ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  rw [polynomial_weighted_area]
  congr 1
  have hsub : (bergmanTaylorPoly d N).support ⊆ Finset.range N := by
    intro n hn
    by_contra h
    have hnz := Polynomial.mem_support_iff.mp hn
    exact hnz (by simp [bergmanTaylorPoly_coeff, Finset.mem_range.mpr.mt h])
  calc
    _ = ∑ n ∈ Finset.range N, ‖(bergmanTaylorPoly d N).coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
      apply Finset.sum_subset hsub
      intro n _ hn
      have hc : (bergmanTaylorPoly d N).coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      simp [hc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [bergmanTaylorPoly_coeff, if_pos (Finset.mem_range.mp hn)]

/-- Weighted Fatou bound for a power series on the punctured disc. -/
theorem a55_weighted_le {F : ℂ → ℂ} {d : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc \ {0}, HasSum (fun n => d n * z ^ n) (F z)) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖F z‖ ^ 2 * (rho z)⁻¹)) ≤
      ∑' n, ENNReal.ofReal ((π / 2) * (‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) := by
  let P := bergmanTaylorPoly d
  let G : ℕ → ℂ → ℝ≥0∞ := fun N z => ENNReal.ofReal (‖(P N).eval z‖ ^ 2 * (rho z)⁻¹)
  have hm (N : ℕ) : Measurable (G N) := by
    dsimp [G]
    have : Continuous (fun z => ‖(P N).eval z‖ ^ 2 * (rho z)⁻¹) := by
      simp only [rho, inv_div]
      fun_prop
    exact ENNReal.measurable_ofReal.comp this.measurable
  have ht (z : ℂ) (hz : z ∈ unitDisc \ {0}) : Tendsto (fun N => G N z) atTop
      (𝓝 (ENNReal.ofReal (‖F z‖ ^ 2 * (rho z)⁻¹))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    have hp : Tendsto (fun N => (P N).eval z) atTop (𝓝 (F z)) := by
      simpa only [P, bergmanTaylorPoly_eval] using (hs z hz).tendsto_sum_nat
    exact (hp.norm.pow 2).mul_const _
  have hint (N : ℕ) : IntegrableOn (fun z => ‖(P N).eval z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    have hc : Continuous (fun z => ‖(P N).eval z‖ ^ 2 * (rho z)⁻¹) := by
      simp only [rho, inv_div]
      fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hI (N : ℕ) : (∫⁻ z in unitDisc, G N z) =
      ∑ n ∈ Finset.range N, ENNReal.ofReal ((π / 2) * (‖d n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) := by
    dsimp only [G]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint N)
      (Eventually.of_forall fun z => by simp only [rho, inv_div]; positivity)]
    simp only [P, a55_taylor_weighted_area, Finset.mul_sum]
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  have hlim : Tendsto (fun N => ∫⁻ z in unitDisc, G N z) atTop
      (𝓝 (∑' n, ENNReal.ofReal ((π / 2) * (‖d n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))))) := by
    simp only [hI]
    exact ENNReal.tendsto_nat_tsum _
  have hpunct : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  calc
    _ = ∫⁻ z in unitDisc \ {0}, ENNReal.ofReal (‖F z‖ ^ 2 * (rho z)⁻¹) := (setLIntegral_congr hpunct).symm
    _ = ∫⁻ z in unitDisc \ {0}, liminf (fun N => G N z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((measurableSet_ball).diff (measurableSet_singleton 0))] with z hz
      exact (ht z hz).liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ z in unitDisc \ {0}, G N z) atTop := lintegral_liminf_le hm
    _ = liminf (fun N => ∫⁻ z in unitDisc, G N z) atTop := by
      congr 1
      funext N
      exact setLIntegral_congr hpunct
    _ = _ := hlim.liminf_eq

/-- Series of the transported derivative `h'(1/z)/z⁴ = q' + 2q/z` on the punctured disc. -/
theorem a55_inv_series {h q : ℂ → ℂ} {c : ℕ → ℂ} (hh : h ∈ A21tildeExt)
    (hqeq : EqOn q (fun z => -h z⁻¹ / z ^ 2) (unitDisc \ {0}))
    (hqs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (q z))
    (hq's : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) (deriv q z))
    (hc0 : c 0 = 0) :
    ∀ z ∈ unitDisc \ {0}, HasSum (fun n : ℕ => ((n : ℂ) + 3) * c (n + 1) * z ^ n) (deriv h z⁻¹ / z ^ 4) := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  intro z hz
  have hz0 : z ≠ 0 := hz.2
  have hzD : z ∈ unitDisc := hz.1
  -- `q = -h(1/z)/z²` near `z`
  have hev : q =ᶠ[𝓝 z] fun w => -h w⁻¹ / w ^ 2 := by
    filter_upwards [hU.mem_nhds hz] with w hw using hqeq hw
  have hzi : z⁻¹ ∈ unitDiscExterior := (a21_inversion_conformal.2.2 ▸ mem_image_of_mem _ hz)
  have hhd : HasDerivAt h (deriv h z⁻¹) z⁻¹ :=
    (hh.1.1.differentiableAt (hE.mem_nhds hzi)).hasDerivAt
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz0
  have hcomp : HasDerivAt (fun w => h w⁻¹) (deriv h z⁻¹ * -(z ^ 2)⁻¹) z := hhd.comp z hinv
  have hpow : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hquot : HasDerivAt (fun w => -h w⁻¹ / w ^ 2)
      ((-(deriv h z⁻¹ * -(z ^ 2)⁻¹) * z ^ 2 - -h z⁻¹ * (2 * z)) / (z ^ 2) ^ 2) z :=
    hcomp.neg.div hpow (pow_ne_zero 2 hz0)
  have hdqz : deriv q z = (-(deriv h z⁻¹ * -(z ^ 2)⁻¹) * z ^ 2 - -h z⁻¹ * (2 * z)) / (z ^ 2) ^ 2 := by
    rw [hev.deriv_eq]
    exact hquot.deriv
  have hqz : q z = -h z⁻¹ / z ^ 2 := hqeq hz
  have hval : deriv h z⁻¹ / z ^ 4 = deriv q z + 2 * (q z / z) := by
    rw [hdqz, hqz]
    field_simp
    ring
  -- the series of `q/z`
  have hqz' : HasSum (fun n => c (n + 1) * z ^ n) (q z / z) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr (hqs z hzD)
    simp only [Finset.range_one, Finset.sum_singleton, hc0, zero_mul, sub_zero] at h1
    have h2 := h1.mul_left z⁻¹
    rw [div_eq_inv_mul]
    refine h2.congr_fun fun n => ?_
    rw [pow_succ]
    field_simp
  rw [hval]
  refine ((hq's z hzD).add (hqz'.mul_left 2)).congr_fun fun n => ?_
  ring
/-- The `A₂¹` norm is preserved by the inversion `q = -h(1/z)/z²`. -/
theorem a55_inv_normA21 {h q : ℂ → ℂ} (hqeq : EqOn q (fun z => -h z⁻¹ / z ^ 2) (unitDisc \ {0})) :
    normA21 unitDisc q = normA21 unitDiscExterior h := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hpull := normA21_pullback hU a21_inversion_conformal (ψ := h)
  rw [← hpull]
  have hpunct : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  unfold normA21
  congr 1
  rw [← setLIntegral_congr hpunct]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  rw [hqeq hz]
  dsimp only
  rw [(hasDerivAt_inv hz.2).deriv, div_eq_mul_inv, neg_mul, mul_neg]
/-- The weighted norm of `h'` on `𝔻*` through the inversion. -/
theorem a55_inv_normA2 (h : ℂ → ℂ) :
    normA2 unitDiscExterior (deriv h) ^ 2 =
      ∫⁻ z in unitDisc \ {0}, ENNReal.ofReal (‖deriv h z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹) := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  rw [a55_normA2_sq, ← a21_inversion_conformal.2.2,
    d2_lintegral_image hU a21_inversion_conformal.1 a21_inversion_conformal.2.1]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  have hw := inverted_quadratic_weight (φ := deriv h) hz.2
  rw [hw, ENNReal.ofReal_mul (by unfold rho; positivity), ENNReal.ofReal_mul (by positivity)]
  simp only [a55_ofReal_sq]
  ring
/-- Coefficient comparison: the weighted norm of `Σ (n+3) c_{n+1} zⁿ` is at most `3/2 ‖q‖²`. -/
theorem a55_series_bound {q F : ℂ → ℂ} {c : ℕ → ℂ}
    (hqs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (q z)) (hc0 : c 0 = 0)
    (hK : ∀ z ∈ unitDisc \ {0}, HasSum (fun n : ℕ => ((n : ℂ) + 3) * c (n + 1) * z ^ n) (F z)) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖F z‖ ^ 2 * (rho z)⁻¹)) ≤
      ENNReal.ofReal (3 / 2) * normA21 unitDisc q ^ 2 := by
  have hW := a55_weighted_le (F := F) (d := fun n : ℕ => ((n : ℂ) + 3) * c (n + 1)) hK
  have hcoef : ∀ n : ℕ, ENNReal.ofReal ((π / 2) * (‖((n : ℂ) + 3) * c (n + 1)‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) ≤
      ENNReal.ofReal (3 / 2) * ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    intro n
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hd : ‖((n : ℂ) + 3) * c (n + 1)‖ = ((n : ℝ) + 3) * ‖c (n + 1)‖ := by
      rw [norm_mul]
      congr 1
      have : ((n : ℂ) + 3) = (((n : ℝ) + 3 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hd, Nat.cast_add, Nat.cast_one]
    exact a55_coef_le n _ (norm_nonneg _)
  have hpars := s2c_area_parseval_lintegral hqs
  have hshift : (∑' n, ENNReal.ofReal (π * ‖c n‖ ^ 2 / ((n : ℝ) + 1))) =
      ∑' n : ℕ, ENNReal.ofReal (π * ‖c (n + 1)‖ ^ 2 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    have h0 : (π * ‖c 0‖ ^ 2 / (((0 : ℕ) : ℝ) + 1)) = 0 := by rw [hc0]; simp
    simp only [h0, ENNReal.ofReal_zero, zero_add, Nat.cast_add, Nat.cast_one]
  have hqsq : (∫⁻ z in unitDisc, ENNReal.ofReal (‖q z‖ ^ 2)) = normA21 unitDisc q ^ 2 := by
    rw [a55_normA21_sq]
    exact lintegral_congr fun z => a55_ofReal_sq _
  calc _ ≤ _ := hW
    _ ≤ _ := ENNReal.tsum_le_tsum hcoef
    _ = _ := by rw [ENNReal.tsum_mul_left, ← hshift, ← hpars, hqsq]

/-- `‖h'‖_{A₂(𝔻*)} ≤ C ‖h‖_{A₂¹(𝔻*)}` on `Ã₂¹(𝔻*)` (false on all of `A₂¹(𝔻*)`: `h = z⁻²`). -/
theorem a55_deriv_ext : ∃ C : ℝ, ∀ h ∈ A21tildeExt,
    normA2 unitDiscExterior (deriv h) ≤ ENNReal.ofReal C * normA21 unitDiscExterior h := by
  refine ⟨Real.sqrt (3 / 2), fun h hh => ?_⟩
  obtain ⟨q, hq, hq0, hqeq, -⟩ := A21tildeExt.inverted_extension hh
  -- Taylor coefficients of `q` and of `q'`
  let c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n q 0
  have hqs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (q z) := by
    intro z hz
    have h := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) hq.1 hz
    refine h.congr_fun fun n => ?_
    simp only [c, sub_zero, smul_eq_mul]
    ring
  have hdq : DifferentiableOn ℂ (deriv q) unitDisc := hq.1.deriv isOpen_ball
  have hq's : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) (deriv q z) := by
    intro z hz
    have h := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 1) hdq hz
    refine h.congr_fun fun n => ?_
    simp only [c, sub_zero, smul_eq_mul, ← iteratedDeriv_succ', Nat.factorial_succ]
    push_cast
    field_simp
  have hc0 : c 0 = 0 := by simp [c, hq0]
  have hpunct : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc :=
    sdiff_null_ae_eq_self (measure_singleton 0)
  apply a55_le_of_sq_le
  rw [a55_inv_normA2, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num),
    ← a55_inv_normA21 hqeq]
  calc (∫⁻ z in unitDisc \ {0}, ENNReal.ofReal (‖deriv h z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹))
      = ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv h z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹) :=
        setLIntegral_congr hpunct
    _ ≤ _ := a55_series_bound (F := fun z => deriv h z⁻¹ / z ^ 4) hqs hc0
        (a55_inv_series hh hqeq hqs hq's hc0)

/-- Triangle inequality for the weighted `A₂` norm. -/
theorem a55_normA2_add_le {D : Set ℂ} {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D))
    (hg : AEStronglyMeasurable g (volume.restrict D)) :
    normA2 D (fun z => f z + g z) ≤ normA2 D f + normA2 D g := by
  have hac : rhoInvMeasure D ≪ volume.restrict D := withDensity_absolutelyContinuous _ _
  have hf' := hf.mono_ac hac
  have hg' := hg.mono_ac hac
  show normA2 D (f + g) ≤ normA2 D f + normA2 D g
  rw [normA2_eq_eLpNorm D _ (hf'.add hg'), normA2_eq_eLpNorm D _ hf', normA2_eq_eLpNorm D _ hg']
  exact eLpNorm_add_le (by norm_num)

/-- Triangle inequality for the `A₂¹` norm. -/
theorem a55_normA21_add_le {D : Set ℂ} {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict D))
    (hg : AEStronglyMeasurable g (volume.restrict D)) :
    normA21 D (fun z => f z + g z) ≤ normA21 D f + normA21 D g := by
  have he : ∀ {u : ℂ → ℂ}, AEStronglyMeasurable u (volume.restrict D) →
      normA21 D u = eLpNorm u 2 (volume.restrict D) := by
    intro u hu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hu]
    norm_num [normA21, enorm_eq_nnnorm]
  show normA21 D (f + g) ≤ normA21 D f + normA21 D g
  rw [he (hf.add hg), he hf, he hg]
  exact eLpNorm_add_le (by norm_num)

/-- `Ψ*` is continuous on `Ã₂¹(𝔻*)` into `A₂(𝔻*)`. -/
theorem a55_psi_cont_ext {ψ : ℂ → ℂ} (hψ : ψ ∈ A21tildeExt) :
    ∀ ε > 0, ∃ δ > 0, ∀ φ ∈ A21tildeExt,
      normA21 unitDiscExterior (fun z => φ z - ψ z) < ENNReal.ofReal δ →
        normA2 unitDiscExterior (fun z => PsiOp φ z - PsiOp ψ z) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := a55_deriv_ext
  obtain ⟨C₂, hC₂⟩ := a55_mul_ext
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  set A := (normA21 unitDiscExterior ψ).toReal with hA
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set K := max C₁ 0 + max C₂ 0 * (1 + 2 * A) + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min 1 (ε / K), lt_min one_pos (div_pos hε hK0), fun φ hφ hφψ => ?_⟩
  set h : ℂ → ℂ := fun z => φ z - ψ z with hhdef
  have haes : ∀ {u : ℂ → ℂ}, DifferentiableOn ℂ u unitDiscExterior →
      AEStronglyMeasurable u (volume.restrict unitDiscExterior) :=
    fun hu => hu.continuousOn.aestronglyMeasurable hEm
  have hδ : ENNReal.ofReal (min 1 (ε / K)) < ⊤ := ENNReal.ofReal_lt_top
  have hhfin : normA21 unitDiscExterior h < ⊤ := hφψ.trans hδ
  have hh : h ∈ A21tildeExt := by
    refine ⟨⟨hφ.1.1.sub hψ.1.1, hhfin⟩, ?_⟩
    obtain ⟨Cφ, Rφ, hφd⟩ := hφ.2
    obtain ⟨Cψ, Rψ, hψd⟩ := hψ.2
    refine ⟨Cφ + Cψ, max Rφ Rψ, fun z hz => ?_⟩
    have h1 := hφd z (lt_of_le_of_lt (le_max_left _ _) hz)
    have h2 := hψd z (lt_of_le_of_lt (le_max_right _ _) hz)
    calc ‖h z‖ ≤ ‖φ z‖ + ‖ψ z‖ := norm_sub_le _ _
      _ ≤ Cφ / ‖z‖ ^ 3 + Cψ / ‖z‖ ^ 3 := add_le_add h1 h2
      _ = (Cφ + Cψ) / ‖z‖ ^ 3 := by ring
  -- the algebraic identity on `𝔻*`
  have hid : EqOn (fun z => PsiOp φ z - PsiOp ψ z)
      (fun z => deriv h z + (-(1 / 2 : ℂ)) * (h z * (φ z + ψ z))) unitDiscExterior := by
    intro z hz
    have hφz := hφ.1.1.differentiableAt (hE.mem_nhds hz)
    have hψz := hψ.1.1.differentiableAt (hE.mem_nhds hz)
    have hd : deriv h z = deriv φ z - deriv ψ z := deriv_sub hφz hψz
    simp only [PsiOp]
    rw [hd]
    simp only [h]
    ring
  rw [normA2_congr hEm hid]
  -- bounds
  have hD := hC₁ h hh
  have hsum : (fun z => φ z + ψ z) = fun z => h z + (ψ z + ψ z) := by
    funext z
    simp only [h]
    ring
  have hplus : normA21 unitDiscExterior (fun z => φ z + ψ z) ≤
      normA21 unitDiscExterior h + (normA21 unitDiscExterior ψ + normA21 unitDiscExterior ψ) := by
    rw [hsum]
    refine (a55_normA21_add_le (haes hh.1.1) ((haes hψ.1.1).add (haes hψ.1.1))).trans ?_
    gcongr
    exact a55_normA21_add_le (haes hψ.1.1) (haes hψ.1.1)
  have hplusA : (fun z => φ z + ψ z) ∈ A21fun unitDiscExterior := by
    refine ⟨hφ.1.1.add hψ.1.1, lt_of_le_of_lt hplus ?_⟩
    exact ENNReal.add_lt_top.mpr ⟨hhfin, ENNReal.add_lt_top.mpr ⟨hψ.1.2, hψ.1.2⟩⟩
  have hM := hC₂ h hh.1 (fun z => φ z + ψ z) hplusA
  have hderm : AEStronglyMeasurable (deriv h) (volume.restrict unitDiscExterior) :=
    haes (hh.1.1.deriv hE)
  have hprodm : AEStronglyMeasurable (fun z => (-(1 / 2 : ℂ)) * (h z * (φ z + ψ z)))
      (volume.restrict unitDiscExterior) :=
    (haes (((hh.1.1.mul (hφ.1.1.add hψ.1.1))).const_smul (-(1 / 2 : ℂ))))
  have htri := a55_normA2_add_le hderm hprodm
  rw [normA2_const_mul] at htri
  -- pass to reals
  set t := (normA21 unitDiscExterior h).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hhe : normA21 unitDiscExterior h = ENNReal.ofReal t := (ENNReal.ofReal_toReal hhfin.ne).symm
  have hψe : normA21 unitDiscExterior ψ = ENNReal.ofReal A := (ENNReal.ofReal_toReal hψ.1.2.ne).symm
  have htδ : t < min 1 (ε / K) := by
    rw [hhe] at hφψ
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_min one_pos (div_pos hε hK0))).mp hφψ
  have ht1 : t < 1 := lt_of_lt_of_le htδ (min_le_left _ _)
  have htK : t * K < ε := by
    have := lt_of_lt_of_le htδ (min_le_right _ _)
    rwa [lt_div_iff₀ hK0] at this
  have hC1 : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (max C₁ 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hC2 : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (max C₂ 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hhalf : (‖(-(1 / 2 : ℂ))‖₊ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, norm_neg]
    norm_num
  have hbound : normA2 unitDiscExterior (deriv h) +
      (‖(-(1 / 2 : ℂ))‖₊ : ℝ≥0∞) * normA2 unitDiscExterior (fun z => h z * (φ z + ψ z)) ≤
      ENNReal.ofReal (max C₁ 0 * t + 1 / 2 * (max C₂ 0 * t * (t + (A + A)))) := by
    rw [hhalf]
    have e1 : normA2 unitDiscExterior (deriv h) ≤ ENNReal.ofReal (max C₁ 0 * t) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _), ← hhe]
      exact hD.trans (by gcongr)
    have e2 : normA2 unitDiscExterior (fun z => h z * (φ z + ψ z)) ≤
        ENNReal.ofReal (max C₂ 0 * t * (t + (A + A))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (le_max_right _ _), ← hhe,
        ENNReal.ofReal_add ht0 (by positivity), ENNReal.ofReal_add hA0 hA0, ← hhe, ← hψe]
      exact hM.trans (by gcongr)
    have hb0 : 0 ≤ max C₂ 0 * t * (t + (A + A)) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) ht0) (by linarith)
    calc _ ≤ ENNReal.ofReal (max C₁ 0 * t) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (max C₂ 0 * t * (t + (A + A))) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) ht0) (mul_nonneg (by norm_num) hb0),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine lt_of_le_of_lt (htri.trans hbound) ((ENNReal.ofReal_lt_ofReal_iff hε).mpr ?_)
  have hC1n : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC2n : 0 ≤ max C₂ 0 := le_max_right _ _
  calc max C₁ 0 * t + 1 / 2 * (max C₂ 0 * t * (t + (A + A)))
      ≤ t * K := by
        rw [hK]
        have : t + (A + A) ≤ 1 + 2 * A := by linarith
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hC2n ht0)]
    _ < ε := htK

/-! ### Step 3: reflection -/

/-- `‖x‖₊² = ofReal ‖x‖²` in `ℝ≥0∞`. -/
theorem a55_nnnorm_sq (x : ℂ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

/-- `s ↦ Ψ*φ(1/s)/s⁴` extends holomorphically to `𝔻` (from `A21tildeExt.inverted_extension`). -/
theorem a55_refl {φ : ℂ → ℂ} (hφ : φ ∈ A21tildeExt) :
    ∃ K : ℂ → ℂ, DifferentiableOn ℂ K unitDisc ∧ ∀ s ∈ unitDisc \ {0}, K s = PsiOp φ s⁻¹ / s ^ 4 := by
  obtain ⟨q, hq, hq0, -, hPsi⟩ := A21tildeExt.inverted_extension hφ
  refine ⟨fun s => (deriv q s - 1 / 2 * q s ^ 2) + 2 * dslope q 0 s, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ (dslope q 0) unitDisc :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr hq.1
    exact ((hq.1.deriv isOpen_ball).sub ((hq.1.pow 2).const_mul (1 / 2 : ℂ))).add (hd.const_mul 2)
  · intro s hs
    rw [hPsi s hs]
    have hs0 : s ≠ 0 := hs.2
    show (deriv q s - 1 / 2 * q s ^ 2) + 2 * dslope q 0 s = (deriv q s - 1 / 2 * q s ^ 2) + 2 * q s / s
    rw [dslope_of_ne q hs0, slope_def_field, hq0, sub_zero, sub_zero]
    ring

/-- The reflection `S ↦ (y ↦ \overline{K(\bar y)})`, `K(s) = S(1/s)/s⁴`, is isometric from `A₂(𝔻*)` to `A₂(𝔻)`. -/
theorem a55_refl_norm {S₁ S₂ K₁ K₂ : ℂ → ℂ} (h₁ : ∀ s ∈ unitDisc \ {0}, K₁ s = S₁ s⁻¹ / s ^ 4)
    (h₂ : ∀ s ∈ unitDisc \ {0}, K₂ s = S₂ s⁻¹ / s ^ 4) :
    normA2 unitDisc (fun y => conj (K₁ (conj y)) - conj (K₂ (conj y))) =
      normA2 unitDiscExterior (fun z => S₁ z - S₂ z) := by
  unfold normA2
  congr 1
  obtain ⟨H0, hH0⟩ : ∃ H0 : ℂ → ℝ≥0∞,
      H0 = fun s => (‖K₁ s - K₂ s‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho s)⁻¹ := ⟨_, rfl⟩
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hUm : MeasurableSet (unitDisc \ {(0 : ℂ)}) := hU.measurableSet
  -- the left side: undo the conjugation, then drop the null point `0`
  have hL1 : (∫⁻ y in unitDisc, (‖conj (K₁ (conj y)) - conj (K₂ (conj y))‖₊ : ℝ≥0∞) ^ 2 *
      ENNReal.ofReal (rho y)⁻¹) = ∫⁻ y in unitDisc, H0 (conj y) := by
    apply lintegral_congr
    intro y
    rw [hH0, ← map_sub, RCLike.nnnorm_conj]
    unfold rho
    dsimp only
    rw [Complex.norm_conj]
  have himc : (fun z : ℂ => conj z) '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      show conj v ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.mp hv
    · intro hw
      refine ⟨conj w, ?_, Complex.conj_conj w⟩
      show conj w ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.mp hw
  have hL2 : (∫⁻ y in unitDisc, H0 (conj y)) = ∫⁻ s in unitDisc, H0 s := by
    rw [gzE_conj_measurePreserving.setLIntegral_comp_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding H0 unitDisc, himc]
  have hL3 : (∫⁻ s in unitDisc, H0 s) = ∫⁻ s in unitDisc \ {(0 : ℂ)}, H0 s :=
    setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))).symm
  -- the right side: the inversion `z = 1/s`
  have himg : (fun s : ℂ => s⁻¹) '' (unitDisc \ {(0 : ℂ)}) = unitDiscExterior := a21_inversion_conformal.2.2
  have hR := d2_lintegral_image hU a21_inversion_conformal.1 a21_inversion_conformal.2.1
    (fun z => (‖S₁ z - S₂ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹)
  rw [himg] at hR
  rw [hL1, hL2, hL3, hR]
  apply setLIntegral_congr_fun hUm
  intro s hs
  have hs0 : s ≠ 0 := hs.2
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hs1 : ‖s‖ < 1 := mem_ball_zero_iff.mp hs.1
  rw [hH0]
  dsimp only
  rw [h₁ s hs, h₂ s hs, deriv_inv, ← sub_div, a55_nnnorm_sq, a55_nnnorm_sq, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold rho
  rw [norm_div, norm_pow, norm_neg, norm_inv, norm_pow, norm_inv]
  have h1 : 1 - ‖s‖ ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 - (‖s‖⁻¹) ^ 2 ≠ 0 := by
    have : 1 < ‖s‖⁻¹ := one_lt_inv₀ hsn |>.mpr hs1
    nlinarith
  field_simp
  ring

/-- On Schwarzians the reflection exchanges `𝗀_μ` and `𝖿^{μ⁻¹}` (from `s2c_f_eq_conj`). -/
theorem a55_refl_schwarzian {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {y : ℂ} (hy : y ∈ unitDisc) (hy0 : y ≠ 0) :
    schwarzianHol (fsans (beltramiInv μ)) y = conj (schwarzianHol (gsans μ) (conj y)⁻¹) / y ^ 4 := by
  have hν := bc_beltramiInv_mem_ball hμ
  obtain ⟨φ, b, hφd, hφi, hφ0, -, hb, hbg, hg⟩ :=
    g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hpf := AppB.b8_welding_normalized_pair hν
  have hpg := AppB.b8_welding_normalized_pair hμ
  have hfd : DifferentiableOn ℂ (fsans (beltramiInv μ)) unitDisc := hpf.1
  have hfi : InjOn (fsans (beltramiInv μ)) unitDisc := hpf.2.1
  have hgd : DifferentiableOn ℂ (gsans μ) unitDiscExterior := hpg.2.2.2.2.1.1
  have hgi : InjOn (gsans μ) unitDiscExterior := hpg.2.2.2.2.1.2.1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hry : refl y ∈ unitDiscExterior := (refl_mem_exterior_iff hy0).2 hy
  -- both kernels are continuous through the diagonal, where they are `-𝒮/(6π)`
  have hL : Tendsto (fun u => kerK1 (fsans (beltramiInv μ)) y u) (𝓝[≠] y)
      (𝓝 (kerK1 (fsans (beltramiInv μ)) y y)) :=
    ((AppB.differentiableOn_kerK1_right isOpen_ball hfd hfi hy).continuousOn.continuousAt
      (isOpen_ball.mem_nhds hy)).tendsto.mono_left nhdsWithin_le_nhds
  have hrc : ContinuousAt refl y :=
    (Complex.continuous_conj.continuousAt).inv₀ ((map_ne_zero _).2 hy0)
  have hR0 : ContinuousAt (fun v => kerK1 (gsans μ) (refl y) v) (refl y) :=
    (AppB.differentiableOn_kerK1_right hEo hgd hgi hry).continuousOn.continuousAt (hEo.mem_nhds hry)
  have hRc : ContinuousAt (fun u => (1 / y ^ 2) * (1 / u ^ 2) * conj (kerK1 (gsans μ) (refl y) (refl u))) y :=
    (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hy0))).mul
      (Complex.continuous_conj.continuousAt.comp (hR0.comp hrc))
  have hR := hRc.tendsto.mono_left (nhdsWithin_le_nhds (s := {y}ᶜ))
  have heq : (fun u => kerK1 (fsans (beltramiInv μ)) y u) =ᶠ[𝓝[≠] y]
      fun u => (1 / y ^ 2) * (1 / u ^ 2) * conj (kerK1 (gsans μ) (refl y) (refl u)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hy),
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hy0)] with u hu hu1 hu2
    exact s2c_kerK1_refl hμ hφd hφi hφ0 hb hbg hg hy hu1 hy0 hu2 (Ne.symm hu)
  have hlim := tendsto_nhds_unique (hL.congr' heq) hR
  simp only [kerK1, ↓reduceIte] at hlim
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc6 : conj (6 * (π : ℂ)) = 6 * π := by
    rw [map_mul, Complex.conj_ofReal, map_ofNat]
  rw [map_div₀, map_neg, hc6] at hlim
  have hry' : refl y = (conj y)⁻¹ := rfl
  rw [← hry']
  have hy4 : y ^ 4 ≠ 0 := pow_ne_zero 4 hy0
  field_simp at hlim ⊢
  linear_combination -hlim

/-! ### Step 4: the Bers image is open -/

/-- An `A₂(𝔻)`-neighbourhood of `𝒮(𝖿^{q₀})` consists of Schwarzians `𝒮(𝖿^q)`, `q ∈ T(1)`. -/
theorem a55_bers_open (q₀ : T1) : ∃ ε > 0, ∀ S : ℂ → ℂ, DifferentiableOn ℂ S unitDisc →
    normA2 unitDisc (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) < ENNReal.ofReal ε →
      ∃ q : T1, EqOn S (schwarzianHol (fsans (Quotient.out q : LinfStarBall))) unitDisc := by
  have hcircle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.mp hz).ne
  -- `𝒮(𝖿^μ) = toFun (β[μ])` on `𝔻`
  have hspec : ∀ q : T1, ∀ y ∈ unitDisc,
      AInf.toFun (bers q) y = schwarzianHol (fsans (Quotient.out q : LinfStarBall)) y := by
    intro q y hy
    have hμ := (Quotient.out q : LinfStarBall).2
    obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
    rw [S2C.s2c_fsans_eq hμ]
    exact (schwarzianHol_AInf_spec hfd hfi).1 y hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp bers_isOpenEmbedding.isOpen_range (bers q₀) ⟨q₀, rfl⟩
  have hcpos : 0 < Real.sqrt (12 / π) := Real.sqrt_pos.2 (by positivity)
  refine ⟨r / Real.sqrt (12 / π), div_pos hr hcpos, fun S hS hn => ?_⟩
  have hS₀d : DifferentiableOn ℂ (schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall))) unitDisc :=
    (toAInf unitDisc _).2.congr fun z hz => (hspec q₀ z hz).symm
  have hmem : (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) ∈ A2fun unitDisc :=
    ⟨hS.sub hS₀d, hn.trans ENNReal.ofReal_lt_top⟩
  set φ := toA2 unitDisc (fun y => S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y) with hφ
  have hφn : ‖φ‖ < r / Real.sqrt (12 / π) := by
    have h1 : ENNReal.ofReal ‖φ‖ < ENNReal.ofReal (r / Real.sqrt (12 / π)) := by
      rw [ofReal_norm_eq_enorm]
      exact (hbL2_toA2_norm hmem).trans_lt hn
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hr hcpos)).1 h1
  obtain ⟨hAn, hAf⟩ := A2toAInf_bounded.2 φ
  have hlt : ‖A2toAInf φ‖ < r := by
    calc ‖A2toAInf φ‖ ≤ Real.sqrt (12 / π) * ‖φ‖ := hAn
      _ < Real.sqrt (12 / π) * (r / Real.sqrt (12 / π)) := mul_lt_mul_of_pos_left hφn hcpos
      _ = r := by field_simp
  have hmemb : bers q₀ + A2toAInf φ ∈ ball (bers q₀) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hlt
  obtain ⟨q, hq⟩ := hball hmemb
  refine ⟨q, fun y hy => ?_⟩
  have e2 : AInf.toFun (bers q₀ + A2toAInf φ) y = AInf.toFun (bers q₀) y + AInf.toFun (A2toAInf φ) y := by
    simp only [AInf.toFun, Submodule.coe_add, unweight_add, Pi.add_apply]
  have hφy : A2.toFun φ y = S y - schwarzianHol (fsans (Quotient.out q₀ : LinfStarBall)) y :=
    toA2_spec isOpen_ball hcircle hmem hy
  rw [← hq, hspec q y hy, hspec q₀ y hy, hAf y hy, hφy] at e2
  rw [e2]
  ring

/-! ### Step 5 and assembly -/

/-- Schwarzians only see a neighbourhood: equal maps on an open set have equal Schwarzians there. -/
theorem a55_schwarzian_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : EqOn f g U) :
    EqOn (schwarzianHol f) (schwarzianHol g) U := by
  intro z hz
  have h0 : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hU.mem_nhds hz) h
  have h1 : deriv f =ᶠ[𝓝 z] deriv g := h0.deriv
  have h2 : deriv (deriv f) =ᶠ[𝓝 z] deriv (deriv g) := h1.deriv
  have h3 : (fun w => deriv (deriv f) w / deriv f w) =ᶠ[𝓝 z] fun w => deriv (deriv g) w / deriv g w := by
    filter_upwards [h1, h2] with w hw1 hw2
    rw [hw1, hw2]
  unfold schwarzianHol
  rw [h3.deriv_eq, h2.eq_of_nhds, h1.eq_of_nhds]

/-- `y ↦ \overline{K(\bar y)}` is holomorphic on `𝔻` when `K` is. -/
theorem a55_conj_diff {K : ℂ → ℂ} (hK : DifferentiableOn ℂ K unitDisc) :
    DifferentiableOn ℂ (fun y => conj (K (conj y))) unitDisc := by
  intro y hy
  have hcy : conj y ∈ unitDisc := by simpa [unitDisc] using hy
  have h := (hK.differentiableAt (isOpen_ball.mem_nhds hcy))
  have h' : DifferentiableAt ℂ (conj ∘ K ∘ conj) y := differentiableAt_conj_conj_iff.2 h
  exact h'.differentiableWithinAt

/-- Two holomorphic functions on `𝔻` that agree off `0` agree on `𝔻`. -/
theorem a55_eqOn_disc {F G : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) (hG : DifferentiableOn ℂ G unitDisc)
    (h : EqOn F G (unitDisc \ {0})) : EqOn F G unitDisc := by
  have hcl : unitDisc ⊆ closure (unitDisc \ {(0 : ℂ)}) := by
    have hd : Dense ({(0 : ℂ)}ᶜ : Set ℂ) := (finite_singleton (0 : ℂ)).countable.dense_compl ℝ
    intro w hw
    exact closure_mono (by intro z hz; exact ⟨hz.1, hz.2⟩)
      (hd.open_subset_closure_inter (show IsOpen unitDisc from isOpen_ball) hw)
  exact Set.EqOn.of_subset_closure h hF.continuousOn hG.continuousOn sdiff_subset hcl

/-- `𝒮(𝖿^{q⁻¹}) = \overline{K_g(\bar y)}` on `𝔻` for `K_g(s) = 𝒮(𝗀_q)(1/s)/s⁴`. -/
theorem a55_refl_class {q : T1} {K : ℂ → ℂ} (hKd : DifferentiableOn ℂ K unitDisc)
    (hK : ∀ s ∈ unitDisc \ {0}, K s = schwarzianHol (gsans (Quotient.out q : LinfStarBall)) s⁻¹ / s ^ 4) :
    EqOn (schwarzianHol (fsans (Quotient.out (invT q) : LinfStarBall))) (fun y => conj (K (conj y))) unitDisc := by
  set μ := (Quotient.out q : LinfStarBall) with hμdef
  have hμ := μ.2
  -- `out (q⁻¹)` and `μ⁻¹` represent the same class
  have hcl : Phi (Quotient.out (invT q)) = Phi ⟨beltramiInv (μ : LinfStar), grp_inv_mem hμ⟩ := by
    have e1 : Phi (Quotient.out (invT q)) = invT q := Quotient.out_eq _
    have e2 : Phi μ = q := Quotient.out_eq q
    rw [e1, ← gtp_invT_phi, e2]
  have hf := (s2c_class_pair (Quotient.exact hcl)).1
  have hS := a55_schwarzian_congr isOpen_ball hf
  obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective (grp_inv_mem hμ)
  have hSd : DifferentiableOn ℂ (schwarzianHol (fsans (beltramiInv (μ : LinfStar)))) unitDisc := by
    rw [S2C.s2c_fsans_eq (grp_inv_mem hμ)]
    exact (toAInf unitDisc _).2.congr fun z hz => ((schwarzianHol_AInf_spec hfd hfi).1 z hz).symm
  have hmain : EqOn (schwarzianHol (fsans (beltramiInv (μ : LinfStar)))) (fun y => conj (K (conj y))) unitDisc := by
    refine a55_eqOn_disc hSd (a55_conj_diff hKd) fun y hy => ?_
    have hy0 : y ≠ 0 := hy.2
    have hcy : conj y ∈ unitDisc \ {0} := ⟨by simpa [unitDisc] using hy.1, by simpa using hy0⟩
    rw [a55_refl_schwarzian hμ hy.1 hy0]
    show _ = conj (K (conj y))
    rw [hK _ hcy, map_div₀, map_pow, Complex.conj_conj]
  exact fun y hy => (hS hy).trans (hmain hy)

/-- Openness at `𝒜(𝗀_q)`, `q ∈ T₀(1)`; `hcub` is the cubic decay of `𝒜(g)` for `g` univalent at `∞`
(`appa2_preSchwarzian_cubic`). -/
theorem a55_core (hcub : ∀ {g : ℂ → ℂ}, IsUnivalentAtInfty g →
      ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖preSchwarzian g z‖ ≤ C / ‖z‖ ^ 3) :
    ∀ q ∈ T01, ∃ ε > 0, ∀ φ ∈ A21tildeExt,
      normA21 unitDiscExterior (fun z => φ z - preSchwarzian (gMu (Quotient.out q : LinfStarBall)) z) <
          ENNReal.ofReal ε →
        ∃ p' ∈ T01, EqOn φ (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : MeasurableSet unitDiscExterior := hEo.measurableSet
  -- `𝒜(𝗀_p) ∈ Ã₂¹(𝔻*)` and `Ψ*𝒜(𝗀_p) = 𝒮(𝗀_p)` for `p ∈ T₀(1)`
  have hmemT : ∀ p ∈ T01, preSchwarzian (gMu (Quotient.out p : LinfStarBall)) ∈ A21tildeExt := by
    intro p hp
    have hμ := (Quotient.out p : LinfStarBall).2
    have hA := ((thm_1_12 p).2.2.2).1 hp
    have hU := (AppB.b8_welding_normalized_pair hμ).2.2.2.2.1
    rw [S2C.s2c_gsans_eq hμ] at hA hU
    exact ⟨hA, hcub hU⟩
  have hpsi : ∀ p : T1, EqOn (PsiOp (preSchwarzian (gMu (Quotient.out p : LinfStarBall))))
      (schwarzianHol (gsans (Quotient.out p : LinfStarBall))) unitDiscExterior := by
    intro p z _
    rw [S2C.s2c_gsans_eq (Quotient.out p : LinfStarBall).2]
    rfl
  intro q hq
  have hψ := hmemT q hq
  set ψ := preSchwarzian (gMu (Quotient.out q : LinfStarBall)) with hψdef
  obtain ⟨ε₁, hε₁, hopen⟩ := a55_bers_open (invT q)
  obtain ⟨δ, hδ, hcont⟩ := a55_psi_cont_ext hψ ε₁ hε₁
  refine ⟨δ, hδ, fun φ hφ hn => ?_⟩
  have hA2 := hcont φ hφ hn
  obtain ⟨K, hKd, hK⟩ := a55_refl hφ
  obtain ⟨Kψ, hKψd, hKψ⟩ := a55_refl hψ
  have hKψ' : ∀ s ∈ unitDisc \ {0},
      Kψ s = schwarzianHol (gsans (Quotient.out q : LinfStarBall)) s⁻¹ / s ^ 4 := fun s hs => by
    rw [hKψ s hs, hpsi q (a21_inv_punctured hs)]
  have hbase := a55_refl_class hKψd hKψ'
  -- the reflected `Ψ*φ` is within `ε₁` of `𝒮(𝖿^{q⁻¹})`
  have hnorm : normA2 unitDisc (fun y => conj (K (conj y)) -
      schwarzianHol (fsans (Quotient.out (invT q) : LinfStarBall)) y) < ENNReal.ofReal ε₁ := by
    calc normA2 unitDisc (fun y => conj (K (conj y)) -
          schwarzianHol (fsans (Quotient.out (invT q) : LinfStarBall)) y)
        = normA2 unitDisc (fun y => conj (K (conj y)) - conj (Kψ (conj y))) :=
          normA2_congr measurableSet_ball (fun y hy => by
            show conj (K (conj y)) - schwarzianHol (fsans (Quotient.out (invT q) : LinfStarBall)) y =
              conj (K (conj y)) - conj (Kψ (conj y))
            rw [hbase hy])
      _ = normA2 unitDiscExterior (fun z => PsiOp φ z - PsiOp ψ z) := a55_refl_norm hK hKψ
      _ < ENNReal.ofReal ε₁ := hA2
  obtain ⟨q', hq'⟩ := hopen _ (a55_conj_diff hKd) hnorm
  -- `q' ∈ T₀(1)`
  have hφA2 : PsiOp φ ∈ A2fun unitDiscExterior := lemma_1_5_exterior_of_cubic_decay hφ.1 hφ.2
  have hn0 : normA2 unitDisc (fun y => conj (K (conj y))) = normA2 unitDiscExterior (PsiOp φ) := by
    have h := a55_refl_norm (S₂ := fun _ => 0) (K₂ := fun _ => 0) hK (fun s _ => by simp)
    simpa only [map_zero, sub_zero] using h
  have hq'T : q' ∈ T01 := by
    refine ((thm_1_12 q').1).2 ⟨(a55_conj_diff hKd).congr fun y hy => (hq' hy).symm, ?_⟩
    exact ((normA2_congr measurableSet_ball (fun y hy => (hq' hy).symm)).trans hn0).trans_lt hφA2.2
  -- `p' = q'⁻¹`
  refine ⟨invT q', (TakhtajanTeo.lemma_3_4).2.2 q' hq'T, ?_⟩
  have hp'T : invT q' ∈ T01 := (TakhtajanTeo.lemma_3_4).2.2 q' hq'T
  set ν := (Quotient.out (invT q') : LinfStarBall) with hνdef
  have hν := ν.2
  -- `𝒮(𝗀_ν) = Ψ*φ` on `𝔻*`
  have hcl : Phi ⟨beltramiInv (ν : LinfStar), grp_inv_mem hν⟩ = Phi (Quotient.out q') := by
    have e1 : Phi ν = invT q' := Quotient.out_eq _
    have e2 : Phi (Quotient.out q') = q' := Quotient.out_eq q'
    rw [← gtp_invT_phi, e1, grp_invT_invT, e2]
  have hf := a55_schwarzian_congr isOpen_ball (s2c_class_pair (Quotient.exact hcl)).1
  have hSg : EqOn (schwarzianHol (gsans (ν : LinfStar))) (PsiOp φ) unitDiscExterior := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num [unitDiscExterior] at hz
    set y := conj z⁻¹ with hy
    have hyD : y ∈ unitDisc \ {0} := by
      have h := a21_inv_exterior hz
      exact ⟨by simpa [unitDisc, hy] using h.1, by simpa [hy] using hz0⟩
    have hcy : conj y = z⁻¹ := by rw [hy, Complex.conj_conj]
    have h1 := a55_refl_schwarzian hν hyD.1 hyD.2
    have hval : schwarzianHol (fsans (Quotient.out q' : LinfStarBall)) y = conj (K (conj y)) := (hq' hyD.1).symm
    rw [hf hyD.1, hval, hcy, inv_inv] at h1
    have h2 := hK (conj y) ⟨by rw [hcy]; exact (a21_inv_exterior hz).1, by rw [hcy]; exact inv_ne_zero hz0⟩
    rw [hcy, inv_inv] at h2
    have hy4 : y ^ 4 = conj (z⁻¹ ^ 4) := by rw [hy, map_pow]
    rw [h2, hy4, ← map_div₀] at h1
    have h4 := (starRingEnd ℂ).injective h1
    have hw : z⁻¹ ^ 4 ≠ 0 := pow_ne_zero _ (inv_ne_zero hz0)
    exact ((div_left_inj' hw).1 h4).symm
  exact PsiOp_injective_on_A21tildeExt hφ (hmemT _ hp'T) fun z hz => ((hpsi _ hz).trans (hSg hz)).symm

/-- The fifth conjunct of `lemma_A_5`, from its fourth conjunct (`appa2_lemma_A_5_clause`) and the cubic decay
(`appa2_preSchwarzian_cubic`). -/
theorem a55_conj5
    (hclause : ∀ p ∈ T01, ∀ w ∈ unitDiscExterior, betaHatStar p w ∈ A21tildeExt ∧
      ∃ p' ∈ T01, EqOn (betaHatStar p w) (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior)
    (hcub : ∀ {g : ℂ → ℂ}, IsUnivalentAtInfty g →
      ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖preSchwarzian g z‖ ≤ C / ‖z‖ ^ 3) :
    ∀ p ∈ T01, ∀ w ∈ unitDiscExterior, ∃ ε > 0, ∀ φ ∈ A21tildeExt,
      normA21 unitDiscExterior (fun z => φ z - betaHatStar p w z) < ENNReal.ofReal ε →
        ∃ p' ∈ T01, EqOn φ (preSchwarzian (gMu (Quotient.out p' : LinfStarBall))) unitDiscExterior := by
  intro p hp w hw
  obtain ⟨-, q, hq, heq⟩ := hclause p hp w hw
  obtain ⟨ε, hε, hcore⟩ := a55_core hcub q hq
  refine ⟨ε, hε, fun φ hφ hn => hcore φ hφ ?_⟩
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rwa [normA21_congr_on hE (fun z hz => by
    show φ z - betaHatStar p w z = φ z - preSchwarzian (gMu (Quotient.out q : LinfStarBall)) z
    rw [heq hz])] at hn

end AppA
end TakhtajanTeo
