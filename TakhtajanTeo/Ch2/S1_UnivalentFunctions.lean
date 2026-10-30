import TakhtajanTeo.Ch1.S8_FiniteDimensional
import LiZhongQC.Lemmas.SchottkyDirectD3a

/-!
# Chapter 2, §1 — Hilbert spaces and univalent functions (TT:3490–3796)

* the spaces `A₂¹(𝔻)`, `A₂¹(𝔻*)`, `A∞¹(𝔻)`, `A∞¹(𝔻*)`; the pre-Schwarzian `𝒜(f) = f''/f'`; `Ψ(f) = f' - ½f²`
* Remark 1.2 (distortion, the factorization of the Bers embedding of `𝒯(1)`), Lemma 1.3, Corollary 1.4, Lemma 1.5
* Theorem 1.6 (Becker–Pommerenke), the symmetric homeomorphisms `S` (Gardiner–Sullivan), Corollary 1.8,
  Remark 1.9
* Lemma 1.11 with (1.1)–(1.2), Theorem 1.12 with (1.3)
* Definition 1.13 (the universal Liouville action `S₁`), Remark 1.14

Chapter 2 declarations live in `TakhtajanTeo.Ch2` (the numbering restarts).

**Readings.**
- In Theorem 1.12 (ii) (TT:3742) the OCR prints `A₃¹(𝔻)`; it is `A₂¹(𝔻)`, as in (iv) and in Lemma 1.11.

**Not stated.**
- Remark 1.1 (notation).
- Remark 1.7 (the equivalent form of condition (ii)).
- Remark 1.10 (an open problem).
- "`S` is a topological group" [GS92] (TT:3646), stated for a Banach submanifold structure on `S` that the memoir does
  not describe.
- The sentence on Hilbert structures of `𝒯₀(1)` (TT:3768); it is Appendix A.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- `‖ψ‖₂ = (∬_D |ψ|² d²z)^{1/2}` (TT:3497). -/
def normA21 (D : Set ℂ) (ψ : ℂ → ℂ) : ℝ≥0∞ := (∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)

/-- The Hilbert space `A₂¹(D)` of holomorphic `ψ` on `D` with `∬_D |ψ|² d²z < ∞` (TT:3497), as a set of functions. -/
def A21fun (D : Set ℂ) : Set (ℂ → ℂ) := {ψ | DifferentiableOn ℂ ψ D ∧ normA21 D ψ < ∞}

/-- The Banach space `A∞¹(D)` of holomorphic `ψ` on `D` with `sup_D |(1 - |z|²) ψ(z)| < ∞` (TT:3507). -/
def AInf1fun (D : Set ℂ) : Set (ℂ → ℂ) :=
  {ψ | DifferentiableOn ℂ ψ D ∧ ∃ C, ∀ z ∈ D, ‖(1 - ‖z‖ ^ 2) * ψ z‖ ≤ C}

/-- The pre-Schwarzian `𝒜(f) = f''/f'` (TT:3517). -/
def preSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv f) z / deriv f z

/-- `Ψ(f) = f_z - ½ f²` (TT:3585). -/
def PsiOp (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv f z - (1 / 2) * f z ^ 2

/-- (TT:3588) `𝒮(f) = Ψ(𝒜(f))` for holomorphic `f` with `f' ≠ 0`. -/
theorem schwarzian_eq_Psi_preSchwarzian {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    (hf' : ∀ z ∈ Ω, deriv f z ≠ 0) {z : ℂ} (hz : z ∈ Ω) :
    schwarzianHol f z = PsiOp (preSchwarzian f) z := by
  rfl

/-- Schwarzian scaling needed for the corrected K1/K4 diagonal and TT:6224. -/
theorem schwarzianHol_mul_comp_mul {f : ℂ → ℂ} {a b z : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hf : AnalyticAt ℂ f (b * z))
    (hf' : deriv f (b * z) ≠ 0) :
    schwarzianHol (fun w => a * f (b * w)) z = b ^ 2 * schwarzianHol f (b * z) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => b * w) z := by fun_prop
  have hgd : deriv (fun w : ℂ => b * w) z = b := by simp
  have hcomp : AnalyticAt ℂ (fun w => f (b * w)) z := hf.comp hg
  have hcomp' : deriv (fun w => f (b * w)) z ≠ 0 := by
    have hd := deriv_comp z hf.differentiableAt hg.differentiableAt
    simp only [Function.comp_def, hgd] at hd
    rw [hd]
    exact mul_ne_zero hf' hb
  have hpost := schwarzian_mobius_comp_of_ne hcomp hcomp'
    (a := a) (b := 0) (c := 0) (d := 1) (by simpa using ha) (by simp)
  simp only [zero_mul, zero_add, add_zero, div_one] at hpost
  have hscaled : AnalyticAt ℂ (fun w => a * f (b * w)) z := analyticAt_const.mul hcomp
  rw [schwarzian_of_analyticAt hscaled, schwarzian_of_analyticAt hcomp] at hpost
  have hchain := eq19_1_chain_rule hg (by simpa only [hgd] using hb) hf hf'
  simp only [Function.comp_def] at hchain
  rw [schwarzian_of_analyticAt hcomp, schwarzian_of_analyticAt hf,
    schwarzian_of_analyticAt hg, hgd] at hchain
  have hzero : schwarzianHol (fun w : ℂ => b * w) z = 0 := by
    simp [schwarzianHol]
  rw [hzero, add_zero] at hchain
  rw [hpost, hchain, mul_comm]

-- `remark_1_2` moved to `Ch2/S1_Completed.lean` (2026-10-26).

-- `bers_curve_factorization` moved to `Ch2/S1_Part3.lean` (2026-10-26).

/-- Finite squared area norm for the space in TT:3497, used in Corollary 1.4. -/
theorem a21_sq_lintegral_ne_top {D : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun D) :
    (∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
  intro h
  have hfin := hψ.2
  simp [normA21, h] at hfin

/-- The finite area norm in TT:3497 gives an integrable squared absolute value. -/
theorem a21_integrable_sq {D : Set ℂ} (hD : MeasurableSet D) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun D) : IntegrableOn (fun z => ‖ψ z‖ ^ 2) D := by
  refine ⟨(hψ.1.continuousOn.norm.pow 2).aestronglyMeasurable hD, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg ‖ψ z‖)).mpr
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
    using lt_top_iff_ne_top.mpr (a21_sq_lintegral_ne_top hψ)

/-- The holomorphic area space in TT:3497 maps into the actual measure-theoretic L2 space. -/
theorem a21_memLp_two {D : Set ℂ} (hD : MeasurableSet D) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun D) : MemLp ψ 2 (volume.restrict D) := by
  exact (memLp_two_iff_integrable_sq_norm
    (hψ.1.continuousOn.aestronglyMeasurable hD)).mpr (a21_integrable_sq hD hψ)

/-- Squaring the area norm recovers the area integral, as in TT:3548. -/
theorem a21_norm_sq_eq_integral {D : Set ℂ} (hD : MeasurableSet D) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun D) :
    normA21 D ψ ^ 2 = ENNReal.ofReal (∫ z in D, ‖ψ z‖ ^ 2) := by
  have hn : normA21 D ψ ^ 2 = ∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [normA21, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hn, ofReal_integral_eq_lintegral_ofReal (a21_integrable_sq hD hψ)
    (Eventually.of_forall fun z => sq_nonneg ‖ψ z‖)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

/-- Membership in the holomorphic L2 space of TT:3497 uses the genuine L2 condition. -/
theorem mem_A21fun_iff_memLp {D : Set ℂ} (hD : MeasurableSet D) {ψ : ℂ → ℂ} :
    ψ ∈ A21fun D ↔ DifferentiableOn ℂ ψ D ∧ MemLp ψ 2 (volume.restrict D) := by
  constructor
  · intro hψ
    exact ⟨hψ.1, a21_memLp_two hD hψ⟩
  · rintro ⟨hd, hm⟩
    have hi := (memLp_two_iff_integrable_sq_norm
      (hd.continuousOn.aestronglyMeasurable hD)).mp hm
    have hfin := (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun z => sq_nonneg ‖ψ z‖)).mp hi.2
    have hsq : (∫⁻ z in D, (‖ψ z‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
      simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm] using hfin
    exact ⟨hd, (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hsq⟩

/-- Addition preserves the holomorphic area space in TT:3497. -/
theorem a21_add {D : Set ℂ} (hD : MeasurableSet D) {f g : ℂ → ℂ}
    (hf : f ∈ A21fun D) (hg : g ∈ A21fun D) : (fun z => f z + g z) ∈ A21fun D := by
  apply (mem_A21fun_iff_memLp hD).mpr
  exact ⟨hf.1.add hg.1, (a21_memLp_two hD hf).add (a21_memLp_two hD hg)⟩

/-- Complex scalar multiplication preserves the holomorphic area space in TT:3497. -/
theorem a21_const_mul {D : Set ℂ} (hD : MeasurableSet D) {f : ℂ → ℂ}
    (hf : f ∈ A21fun D) (c : ℂ) : (fun z => c * f z) ∈ A21fun D := by
  apply (mem_A21fun_iff_memLp hD).mpr
  exact ⟨hf.1.const_mul c, (a21_memLp_two hD hf).const_mul c⟩

/-- Squared area submean estimate supporting Corollary 1.4 (TT:3574–3580). -/
theorem a21_submean_sq {D : Set ℂ} {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ D) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ D) :
    ENNReal.ofReal (π * r ^ 2 * ‖ψ c‖ ^ 2) ≤
      ∫⁻ z in ball c r, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 := by
  have h := s82dx_submean hr (f := fun z => ψ z ^ 2)
    ⟨(hψ.pow 2).mono (ball_subset_closedBall.trans hball),
      ((hψ.pow 2).continuousOn.mono hball).mono closure_ball_subset_closedBall⟩
  simp only [norm_pow] at h
  simpa only [ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm] using h

/-- A ball staying on the same side of the unit circle, for Corollary 1.4 (TT:3574–3580). -/
theorem a21_boundary_ball_subset {D : Set ℂ}
    (hD : D = unitDisc ∨ D = unitDiscExterior) {z : ℂ} (hz : z ∈ D) :
    0 < |‖z‖ - 1| / 2 ∧ closedBall z (|‖z‖ - 1| / 2) ⊆ D := by
  rcases hD with rfl | rfl
  · have hz' : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
    rw [abs_of_neg (sub_neg.mpr hz')]
    refine ⟨by linarith, ?_⟩
    intro w hw
    have hdist : ‖w - z‖ ≤ -(‖z‖ - 1) / 2 := by
      simpa [mem_closedBall, dist_eq_norm] using hw
    have hnorm := norm_sub_norm_le w z
    change w ∈ ball 0 1
    rw [mem_ball, dist_zero_right]
    linarith
  · have hz' : 1 < ‖z‖ := hz
    rw [abs_of_pos (sub_pos.mpr hz')]
    refine ⟨by linarith, ?_⟩
    intro w hw
    have hdist : ‖w - z‖ ≤ (‖z‖ - 1) / 2 := by
      simpa [mem_closedBall, dist_eq_norm] using hw
    have hnorm := norm_sub_norm_le z w
    rw [norm_sub_rev] at hnorm
    change 1 < ‖w‖
    linarith

/-- Compare the boundary weight with the local radius in Corollary 1.4 (TT:3574–3580). -/
theorem a21_weight_le_radius {z : ℂ} (hz : ‖z‖ < 2) :
    |1 - ‖z‖ ^ 2| ≤ 6 * (|‖z‖ - 1| / 2) := by
  have hfactor : 1 - ‖z‖ ^ 2 = -(‖z‖ - 1) * (‖z‖ + 1) := by ring
  rw [hfactor, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ‖z‖ + 1)]
  nlinarith [abs_nonneg (‖z‖ - 1)]

/-- **Corollary 1.4** (TT:3574–3580). For `ψ ∈ A₂¹(𝔻)` (resp. `A₂¹(𝔻*)`), `(1 - |z|²) ψ(z) → 0` as `|z| → 1`. -/
theorem cor_1_4 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun D) :
    Tendsto (fun z => (1 - ‖z‖ ^ 2) * ψ z) (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 D) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmass⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (a21_sq_lintegral_ne_top hψ)
    (show ENNReal.ofReal (π * ε ^ 2 / 36) ≠ 0 by positivity)
  have hvolcont : Continuous (fun t : ℝ => ENNReal.ofReal (π * (|t - 1| / 2) ^ 2)) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hvolsmall : ∀ᶠ t : ℝ in 𝓝 1, ENNReal.ofReal (π * (|t - 1| / 2) ^ 2) < δ := by
    have h := (hvolcont.tendsto 1).eventually
      (gt_mem_nhds (show ENNReal.ofReal (π * (|(1 : ℝ) - 1| / 2) ^ 2) < δ by simpa using hδ))
    simpa using h
  rw [Filter.eventually_inf_principal]
  have hn : Tendsto (fun z : ℂ => ‖z‖) (comap (fun z : ℂ => ‖z‖) (𝓝 1)) (𝓝 1) :=
    tendsto_comap
  filter_upwards [hn.eventually hvolsmall,
    hn.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with z hzvol hznorm
  intro hz
  let r : ℝ := |‖z‖ - 1| / 2
  obtain ⟨hr, hclosed⟩ := a21_boundary_ball_subset hD hz
  have hsub : ball z r ⊆ D := ball_subset_closedBall.trans hclosed
  have hvol : volume (ball z r) = ENNReal.ofReal (π * r ^ 2) := by
    rw [Complex.volume_ball]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow (le_of_lt hr)]
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    exact mul_comm _ _
  have hsmall : (volume.restrict D) (ball z r) < δ := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_self_of_subset_left hsub, hvol]
    exact hzvol
  have hm := hmass (ball z r) hsmall
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_self_of_subset_left hsub] at hm
  have hmean := a21_submean_sq hψ.1 hr hclosed
  have hs : ENNReal.ofReal (π * r ^ 2 * ‖ψ z‖ ^ 2) < ENNReal.ofReal (π * ε ^ 2 / 36) :=
    lt_of_le_of_lt hmean hm
  have hsreal : π * r ^ 2 * ‖ψ z‖ ^ 2 < π * ε ^ 2 / 36 := by
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hs
  have hsbound : (r * ‖ψ z‖) ^ 2 < ε ^ 2 / 36 := by
    nlinarith [Real.pi_pos]
  have hprod : 6 * r * ‖ψ z‖ < ε := by
    nlinarith [sq_nonneg (6 * r * ‖ψ z‖ + ε)]
  rw [dist_zero_right, norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (a21_weight_le_radius hznorm) (norm_nonneg _)).trans_lt hprod

/-- The exact central area estimate for the Bergman space in TT:3546–3570. -/
theorem a21_origin_area_bound {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) :
    ENNReal.ofReal (π * ‖ψ 0‖ ^ 2) ≤ ∫⁻ z in unitDisc, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 := by
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (π * r ^ 2 * ‖ψ 0‖ ^ 2))
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (π * ‖ψ 0‖ ^ 2))) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (π * r ^ 2 * ‖ψ 0‖ ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with r hr hr1
  have hsub : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr1)
  exact (a21_submean_sq hψ hr hsub).trans
    (lintegral_mono_set (ball_subset_closedBall.trans hsub))

/-- Central point evaluation has the sharp constant `1/sqrt π` from Lemma 1.3. -/
theorem a21_origin_bound {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    ENNReal.ofReal ‖ψ 0‖ ≤ ENNReal.ofReal (1 / Real.sqrt π) * normA21 unitDisc ψ := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hnorm := a21_norm_sq_eq_integral hD hψ
  have harea := a21_origin_area_bound hψ.1
  have hint : ENNReal.ofReal (∫ z in unitDisc, ‖ψ z‖ ^ 2) =
      ∫⁻ z in unitDisc, (‖ψ z‖₊ : ℝ≥0∞) ^ 2 := by
    rw [ofReal_integral_eq_lintegral_ofReal (a21_integrable_sq hD hψ)
      (Eventually.of_forall fun z => sq_nonneg ‖ψ z‖)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  rw [← hint] at harea
  have hreal : π * ‖ψ 0‖ ^ 2 ≤ ∫ z in unitDisc, ‖ψ z‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun z => sq_nonneg ‖ψ z‖)).mp harea
  have hnormreal : (normA21 unitDisc ψ).toReal ^ 2 = ∫ z in unitDisc, ‖ψ z‖ ^ 2 := by
    have h := congrArg ENNReal.toReal hnorm
    simpa only [ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg ‖ψ z‖)] using h
  have hsqrt : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hprod : (Real.sqrt π * ‖ψ 0‖) ^ 2 = π * ‖ψ 0‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hbound : Real.sqrt π * ‖ψ 0‖ ≤ (normA21 unitDisc ψ).toReal := by
    nlinarith [ENNReal.toReal_nonneg (a := normA21 unitDisc ψ)]
  have heval : ‖ψ 0‖ ≤ (1 / Real.sqrt π) * (normA21 unitDisc ψ).toReal := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    calc
      Real.sqrt π * ‖ψ 0‖ ≤ (normA21 unitDisc ψ).toReal := hbound
      _ = Real.sqrt π * ((1 / Real.sqrt π) * (normA21 unitDisc ψ).toReal) := by
        field_simp
  have he := ENNReal.ofReal_le_ofReal heval
  rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hψ.2.ne] at he

/-- The L2 norm of a holomorphic one-form is conformally invariant (TT:3497, 3546). -/
theorem normA21_pullback {U V : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) (ψ : ℂ → ℂ) :
    normA21 U (fun z => ψ (f z) * deriv f z) = normA21 V ψ := by
  unfold normA21
  congr 1
  rw [lintegral_image_conformal hU hf]
  apply lintegral_congr
  intro z
  simp only [nnnorm_mul, ENNReal.coe_mul, mul_pow, enorm_eq_nnnorm, mul_comm]

/-- Pullback of a holomorphic L2 one-form by a conformal bijection (TT:3497, 3546). -/
theorem a21_pullback {U V : Set ℂ} {f ψ : ℂ → ℂ} (hU : IsOpen U)
    (hf : IsConformalOnto f U V) (hψ : ψ ∈ A21fun V) :
    (fun z => ψ (f z) * deriv f z) ∈ A21fun U := by
  refine ⟨(hψ.1.comp hf.1 ?_).mul (hf.1.deriv hU), ?_⟩
  · intro z hz
    rw [← hf.2.2]
    exact mem_image_of_mem f hz
  · rw [normA21_pullback hU hf]
    exact hψ.2

/-- The disk case of the sharp point-evaluation bound in Lemma 1.3 (TT:3546–3570). -/
theorem a21_disc_pointwise {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ENNReal.ofReal ‖(1 - ‖z‖ ^ 2) * ψ z‖ ≤
      ENNReal.ofReal (1 / Real.sqrt π) * normA21 unitDisc ψ := by
  have hz1 : ‖-z‖ < 1 := by simpa using mem_ball_zero_iff.mp hz
  have hU : IsOpen unitDisc := isOpen_ball
  have hc := isConformalOnto_blaschke hz1
  have hpull := a21_pullback hU hc hψ
  have h := a21_origin_bound hpull
  have hzero : blaschke (-z) 0 = z := by simp [blaschke]
  have hderiv : deriv (blaschke (-z)) 0 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke hz1 (by simp)).deriv]
    simp only [map_neg, mul_neg, neg_mul, neg_neg, mul_zero, sub_zero, one_pow,
      div_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [normA21_pullback hU hc ψ, hzero, hderiv] at h
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow, mul_comm] using h

/-- Absolute continuity of the area norm gives a uniform small-ball estimate (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_small_ball_bound {D : Set ℂ} {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ c r, 0 < r → closedBall c r ⊆ D →
      volume (ball c r) < δ → r * ‖ψ c‖ < ε := by
  obtain ⟨δ, hδ, hmass⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (a21_sq_lintegral_ne_top hψ) (show ENNReal.ofReal (π * ε ^ 2) ≠ 0 by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro c r hr hclosed hvol
  have hsub : ball c r ⊆ D := ball_subset_closedBall.trans hclosed
  have hs : (volume.restrict D) (ball c r) < δ := by
    rwa [Measure.restrict_apply measurableSet_ball, inter_eq_self_of_subset_left hsub]
  have hm := hmass (ball c r) hs
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_self_of_subset_left hsub] at hm
  have hb := (a21_submean_sq hψ.1 hr hclosed).trans_lt hm
  have hb' : π * r ^ 2 * ‖ψ c‖ ^ 2 < π * ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hb
  have hsq : (r * ‖ψ c‖) ^ 2 < ε ^ 2 := by
    nlinarith [Real.pi_pos]
  nlinarith [sq_nonneg (r * ‖ψ c‖ + ε)]

/-- Small balls centered near a puncture avoid it and remain in the unit disk (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_punctured_ball_subset {z : ℂ} (hz : z ≠ 0) (hz1 : ‖z‖ < 1 / 2) :
    closedBall z (‖z‖ / 2) ⊆ unitDisc \ {0} := by
  intro w hw
  have hdist : ‖w - z‖ ≤ ‖z‖ / 2 := by simpa [mem_closedBall, dist_eq_norm] using hw
  have hup := norm_sub_norm_le w z
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
  simp only [mem_singleton_iff]
  intro hw0
  simp only [hw0, zero_sub, norm_neg] at hdist
  linarith

/-- Square integrability forces `|z| |ψ(z)| → 0` at an isolated puncture (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_punctured_decay {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun (unitDisc \ {0})) :
    Tendsto (fun z => ‖z‖ * ‖ψ z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := a21_small_ball_bound hψ (show 0 < ε / 2 by positivity)
  have hvol : Tendsto (fun z : ℂ => ENNReal.ofReal (π * (‖z‖ / 2) ^ 2))
      (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => ENNReal.ofReal (π * (‖z‖ / 2) ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [hvol.eventually (gt_mem_nhds hδ),
    hn.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    self_mem_nhdsWithin] with z hzvol hz1 hz0
  have hz : z ≠ 0 := hz0
  have hr : 0 < ‖z‖ / 2 := half_pos (norm_pos_iff.mpr hz)
  have hball : volume (ball z (‖z‖ / 2)) < δ := by
    rw [Complex.volume_ball]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr.le,
      ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal] at hzvol
    simpa only [mul_comm] using hzvol
  have h := hsmall z (‖z‖ / 2) hr (a21_punctured_ball_subset hz hz1) hball
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  linarith

/-- An L2 holomorphic one-form on the punctured disk extends with the same area norm (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_remove_puncture {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun (unitDisc \ {0})) :
    ∃ g : ℂ → ℂ, g ∈ A21fun unitDisc ∧ EqOn g ψ (unitDisc \ {0}) ∧
      normA21 unitDisc g = normA21 (unitDisc \ {0}) ψ := by
  have hdec : Tendsto (fun z => z * ψ z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_mul] using a21_punctured_decay hψ
  have hc : Tendsto (fun z : ℂ => z * ψ 0) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (continuous_id.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds |>.mul_const (ψ 0)
  have ho : (fun z => ψ z - ψ 0) =o[𝓝[≠] (0 : ℂ)] (fun z => (z - 0)⁻¹) := by
    apply (Asymptotics.isLittleO_iff_tendsto (fun z hz => ?_)).mpr
    · simpa [div_inv_eq_mul, mul_sub, mul_comm] using hdec.sub hc
    · have hz0 : z = 0 := by simpa using hz
      simp [hz0]
  let g : ℂ → ℂ := Function.update ψ 0 (limUnder (𝓝[≠] 0) ψ)
  have hd : DifferentiableOn ℂ g unitDisc :=
    differentiableOn_update_limUnder_of_isLittleO (ball_mem_nhds (0 : ℂ) one_pos) hψ.1 ho
  have hmeasure : volume.restrict (unitDisc \ {(0 : ℂ)}) = volume.restrict unitDisc := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    simp [hz]
  have hnorm : normA21 unitDisc g = normA21 (unitDisc \ {0}) ψ := by
    unfold normA21
    rw [hmeasure]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(volume.restrict unitDisc).ae_ne (0 : ℂ)] with z hz
    simp [g, Function.update_of_ne hz]
  refine ⟨g, ⟨hd, hnorm ▸ hψ.2⟩, ?_, hnorm⟩
  intro z hz
  exact Function.update_of_ne hz.2 _ _

/-- Inversion maps the exterior disk into the punctured disk (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_inv_exterior {z : ℂ} (hz : z ∈ unitDiscExterior) :
    z⁻¹ ∈ unitDisc \ {0} := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz1)
  refine ⟨mem_ball_zero_iff.mpr ?_, inv_ne_zero hz0⟩
  rw [norm_inv]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hz1)).mpr hz1

/-- Inversion maps the punctured disk into the exterior disk (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_inv_punctured {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    z⁻¹ ∈ unitDiscExterior := by
  change 1 < ‖z⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz.2)).mpr (mem_ball_zero_iff.mp hz.1)

/-- The conformal inversion used to transport the area norm to the exterior (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_inversion_conformal :
    IsConformalOnto (fun z : ℂ => z⁻¹) (unitDisc \ {0}) unitDiscExterior := by
  refine ⟨?_, inv_injective.injOn, ?_⟩
  · intro z hz
    exact (differentiableAt_inv hz.2).differentiableWithinAt
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact a21_inv_punctured hz
    · intro hw
      exact ⟨w⁻¹, a21_inv_exterior hw, inv_inv w⟩

/-- The exterior-disk case of the exact bound in Lemma 1.3 (TT:3546–3570) (supporting Lemma 1.3, TT:3546–3570). -/
theorem a21_exterior_pointwise {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDiscExterior)
    {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ENNReal.ofReal ‖(1 - ‖z‖ ^ 2) * ψ z‖ ≤
      ENNReal.ofReal (1 / Real.sqrt π) * normA21 unitDiscExterior ψ := by
  have hU : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hpull := a21_pullback hU a21_inversion_conformal hψ
  obtain ⟨g, hg, heq, hnorm⟩ := a21_remove_puncture hpull
  have hw := a21_inv_exterior hz
  have h := a21_disc_pointwise hg hw.1
  rw [heq hw, hnorm, normA21_pullback hU a21_inversion_conformal ψ] at h
  simp only [deriv_inv, inv_inv, inv_pow] at h
  have hz1 : 1 < ‖z‖ := hz
  have hzn : 0 < ‖z‖ := lt_trans zero_lt_one hz1
  have hzinv : ‖z‖⁻¹ < 1 := (inv_lt_one₀ hzn).mpr hz1
  have hfactor (r : ℝ) : ‖(1 - (r : ℂ) ^ 2)‖ = |1 - r ^ 2| := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  have hweight : ‖(1 - (‖z⁻¹‖ : ℂ) ^ 2)‖ * ‖z‖ ^ 2 = ‖(1 - (‖z‖ : ℂ) ^ 2)‖ := by
    rw [hfactor, hfactor, norm_inv]
    rw [abs_of_pos (by nlinarith [inv_pos.mpr hzn] : 0 < 1 - (‖z‖⁻¹) ^ 2),
      abs_of_neg (by nlinarith : 1 - ‖z‖ ^ 2 < 0)]
    field_simp
    ring
  have hnormeq : ‖(1 - (‖z⁻¹‖ : ℂ) ^ 2) * (ψ z * -(z ^ 2))‖ =
      ‖(1 - (‖z‖ : ℂ) ^ 2) * ψ z‖ := by
    simp only [norm_mul, norm_neg, norm_pow]
    calc
      _ = (‖(1 - (‖z⁻¹‖ : ℂ) ^ 2)‖ * ‖z‖ ^ 2) * ‖ψ z‖ := by ring
      _ = _ := by rw [hweight]
  rwa [hnormeq] at h

/-- **Lemma 1.3** (TT:3546–3570). `A₂¹(D) ⊂ A∞¹(D)` for `D = 𝔻, 𝔻*`, and the inclusion is bounded:
`sup_D |(1 - |z|²) ψ(z)| ≤ ‖ψ‖₂/√π`. -/
theorem lemma_1_3 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun D) :
    ∀ z ∈ D, ENNReal.ofReal ‖(1 - ‖z‖ ^ 2) * ψ z‖ ≤ ENNReal.ofReal (1 / Real.sqrt π) * normA21 D ψ := by
  rcases hD with rfl | rfl
  · intro z hz
    exact a21_disc_pointwise hψ hz
  · intro z hz
    exact a21_exterior_pointwise hψ hz

/-- The holomorphic L2 space is contained in the weighted bounded space (Lemma 1.3, TT:3546). -/
theorem a21_mem_AInf1fun {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun D) : ψ ∈ AInf1fun D := by
  refine ⟨hψ.1, (1 / Real.sqrt π) * (normA21 D ψ).toReal, ?_⟩
  intro z hz
  have h := lemma_1_3 hD hψ z hz
  rw [← ENNReal.ofReal_toReal hψ.2.ne,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt π)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Polynomial area Parseval in the unweighted Bergman space (TT:3548). -/
theorem polynomial_A21_area (p : Polynomial ℂ) :
    (∫ z in unitDisc, ‖p.eval z‖ ^ 2) =
      π * ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1) := by
  rw [integral_unitDisc_circleAverage _ (by fun_prop)]
  have heq : (∫ r in (0 : ℝ)..1, r * Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 r) =
      ∫ r in (0 : ℝ)..1, ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 * r ^ (2 * n + 1) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := (show r ∈ Icc (0 : ℝ) 1 by simpa using hr).1
    dsimp only
    rw [polynomial_circle_average_sq p hr0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_succ]
    ring
  rw [heq, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, pow_succ, mul_zero, sub_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  · intro n hn
    exact (by fun_prop : Continuous (fun r : ℝ => ‖p.coeff n‖ ^ 2 * r ^ (2 * n + 1))).intervalIntegrable _ _

/-- Polynomials are genuine members of the holomorphic area L2 space (TT:3497). -/
theorem polynomial_mem_A21 (p : Polynomial ℂ) : (fun z => p.eval z) ∈ A21fun unitDisc := by
  apply (mem_A21fun_iff_memLp measurableSet_ball).mpr
  refine ⟨p.differentiable.differentiableOn, ?_⟩
  apply (memLp_two_iff_integrable_sq_norm p.continuous.aestronglyMeasurable).mpr
  exact ((by fun_prop : Continuous (fun z : ℂ => ‖p.eval z‖ ^ 2)).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall

/-- The polynomial case of the derivative estimate used in Lemma 1.5 (TT:3605–3609). -/
theorem polynomial_A21_derivative_bound (p : Polynomial ℂ) :
    (∫ z in unitDisc, ‖deriv (fun w => p.eval w) z‖ ^ 2 * (rho z)⁻¹) ≤
      (1 / 2) * ∫ z in unitDisc, ‖p.eval z‖ ^ 2 := by
  have hs : (∑ n ∈ p.derivative.support, ‖p.derivative.coeff n‖ ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) ≤
      ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1) := by
    apply Finset.sum_le_sum_of_injOn (fun n : ℕ => n + 1)
      (by intro n hn m hm hnm; exact Nat.add_right_cancel hnm)
    · intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      exact Polynomial.of_mem_support_derivative hn
    · intro n hn
      have hnat : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by norm_cast
      rw [Polynomial.coeff_derivative, norm_mul, mul_pow, hnat]
      simp only [Nat.cast_add, Nat.cast_one]
      have heq : (‖p.coeff (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) =
          (‖p.coeff (n + 1)‖ ^ 2 / ((n : ℝ) + 2)) * (((n : ℝ) + 1) / ((n : ℝ) + 3)) := by
        field_simp
        <;> ring
      rw [heq]
      have hratio : ((n : ℝ) + 1) / ((n : ℝ) + 3) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      convert mul_le_of_le_one_right (by positivity : 0 ≤ ‖p.coeff (n + 1)‖ ^ 2 / ((n : ℝ) + 2)) hratio using 1 <;> ring
    · intro n hn hnot
      positivity
  simp_rw [p.deriv]
  rw [polynomial_weighted_area, polynomial_A21_area]
  calc
    _ ≤ (π / 2) * ∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Uniform polynomial approximation preserves the unweighted area integral (TT:3548). -/
theorem A21_polynomial_integral_tendsto (p : ℕ → Polynomial ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall 0 1))
    (hU : TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 1)) :
    Tendsto (fun n => ∫ z in unitDisc, ‖(p n).eval z‖ ^ 2) atTop
      (𝓝 (∫ z in unitDisc, ‖f z‖ ^ 2)) := by
  letI : IsFiniteMeasure (volume.restrict unitDisc) := isFiniteMeasure_restrict.mpr
    (by change volume (ball (0 : ℂ) 1) ≠ ∞; exact measure_ball_lt_top.ne)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hnear := (Metric.tendstoUniformlyOn_iff.mp hU) 1 (by norm_num)
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (fun z => ‖(p n).eval z‖ ^ 2) (volume.restrict unitDisc) := by
    exact Eventually.of_forall fun n => (by fun_prop : Continuous (fun z : ℂ => ‖(p n).eval z‖ ^ 2)).aestronglyMeasurable
  have hbound : ∃ K, ∀ᶠ n : ℕ in atTop, ∀ᵐ z ∂(volume.restrict unitDisc),
      ‖‖(p n).eval z‖ ^ 2‖ ≤ K := by
    refine ⟨(C + 1) ^ 2, ?_⟩
    filter_upwards [hnear] with n hn
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
    have hdist : ‖(p n).eval z - f z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hn z hzc
    have hpn : ‖(p n).eval z‖ ≤ C + 1 := by
      have ht := norm_add_le ((p n).eval z - f z) (f z)
      rw [sub_add_cancel] at ht
      linarith [hC z hzc]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hpn 2
  have hlim : ∀ᵐ z ∂(volume.restrict unitDisc),
      Tendsto (fun n => ‖(p n).eval z‖ ^ 2) atTop (𝓝 (‖f z‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (hU.tendsto_at (ball_subset_closedBall hz)).norm.pow 2
  exact tendsto_integral_filter_of_norm_le_const hmeas hbound hlim

/-- Fatou's lemma transfers the polynomial derivative estimate to a uniform holomorphic limit (TT:3592–3618). -/
theorem A21_derivative_bound_of_polynomial_limit (p : ℕ → Polynomial ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall 0 1))
    (hU : TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 1)) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv f z‖ ^ 2 * (rho z)⁻¹)) ≤
      ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) := by
  let F : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖deriv (fun w => (p n).eval w) z‖ ^ 2 * (rho z)⁻¹)
  have hlocal := (hU.mono (show unitDisc ⊆ closedBall 0 1 from ball_subset_closedBall)).tendstoLocallyUniformlyOn
  have hder := hlocal.deriv (Eventually.of_forall fun n => (p n).differentiable.differentiableOn)
    (show IsOpen unitDisc from isOpen_ball)
  have hconv (z : ℂ) (hz : z ∈ unitDisc) :
      Tendsto (fun n => F n z) atTop (𝓝 (ENNReal.ofReal (‖deriv f z‖ ^ 2 * (rho z)⁻¹))) := by
    have h := ((hder.tendsto_at hz).norm.pow 2).mul_const ((rho z)⁻¹)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hcont (n : ℕ) : Continuous (fun z : ℂ => ‖deriv (fun w => (p n).eval w) z‖ ^ 2 * (rho z)⁻¹) := by
    simp only [(p n).deriv, rho, inv_div]
    fun_prop
  have hmeas (n : ℕ) : Measurable (F n) :=
    (ENNReal.continuous_ofReal.comp (hcont n)).measurable
  have hI (n : ℕ) : (∫⁻ z in unitDisc, F n z) ≤
      ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖(p n).eval z‖ ^ 2) := by
    have hint : IntegrableOn (fun z => ‖deriv (fun w => (p n).eval w) z‖ ^ 2 * (rho z)⁻¹)
        unitDisc := ((hcont n).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
    have hnonneg : ∀ᵐ z ∂(volume.restrict unitDisc),
        0 ≤ ‖deriv (fun w => (p n).eval w) z‖ ^ 2 * (rho z)⁻¹ := by
      apply Eventually.of_forall
      intro z
      unfold rho
      positivity
    change (∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (fun w => (p n).eval w) z‖ ^ 2 * (rho z)⁻¹)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    exact ENNReal.ofReal_le_ofReal (polynomial_A21_derivative_bound (p n))
  have hright := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((A21_polynomial_integral_tendsto p hf hU).const_mul (1 / 2))
  calc
    _ = ∫⁻ z in unitDisc, liminf (fun n => F n z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact (hconv z hz).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ z in unitDisc, F n z) atTop := lintegral_liminf_le hmeas
    _ ≤ liminf (fun n => ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖(p n).eval z‖ ^ 2)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hI)
    _ = _ := hright.liminf_eq

/-- The derivative estimate in Lemma 1.5 for functions holomorphic beyond the closed disk (TT:3592–3618). -/
theorem A21_closedDisk_derivative_bound {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv f z‖ ^ 2 * (rho z)⁻¹)) ≤
      ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) := by
  obtain ⟨p, hp⟩ := holomorphic_polynomial_approx_closedBall hR hf
  exact A21_derivative_bound_of_polynomial_limit p
    (hf.continuousOn.mono (closedBall_subset_closedBall hR.le)) hp

/-- Inward dilation controls the unweighted area mass by its Jacobian (TT:3592–3618). -/
theorem A21_dilate_mass_bound {f : ℂ → ℂ} (hf : f ∈ A21fun unitDisc)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ z in unitDisc, ‖f ((s : ℂ) * z)‖ ^ 2) ≤
      (∫ z in unitDisc, ‖f z‖ ^ 2) / s ^ 2 := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hc : IsConformalOnto (fun z : ℂ => (s : ℂ) * z) unitDisc (ball 0 s) := by
    refine ⟨(differentiable_id.const_mul (s : ℂ)).differentiableOn,
      (fun x hx y hy hxy => mul_left_cancel₀ hsC hxy), ?_⟩
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith [mem_ball_zero_iff.mp hz]
    · intro hw
      refine ⟨w / (s : ℂ), ?_, ?_⟩
      · apply mem_ball_zero_iff.mpr
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        exact (div_lt_one hs0).mpr (mem_ball_zero_iff.mp hw)
      · field_simp
  obtain ⟨R, hR, hdiff⟩ := holomorphic_inward_dilate hf.1 hs0 hs1
  have hfs : IntegrableOn (fun z => ‖f ((s : ℂ) * z)‖ ^ 2) unitDisc :=
    (((hdiff.continuousOn.mono (closedBall_subset_closedBall hR.le)).norm.pow 2).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hder (z : ℂ) : deriv (fun w : ℂ => (s : ℂ) * w) z = (s : ℂ) := by simp
  have hchange := lintegral_image_conformal hU hc (fun w => ENNReal.ofReal (‖f w‖ ^ 2))
  simp only [hder, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at hchange
  rw [lintegral_const_mul' _ _ (by finiteness)] at hchange
  have hmass : ENNReal.ofReal (s ^ 2 * ∫ z in unitDisc, ‖f ((s : ℂ) * z)‖ ^ 2) =
      ∫⁻ z in ball (0 : ℂ) s, ENNReal.ofReal (‖f z‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg s), ENNReal.ofReal_pow hs0.le,
      ofReal_integral_eq_lintegral_ofReal hfs (Eventually.of_forall fun z => sq_nonneg _)]
    exact hchange.symm
  have hm : ENNReal.ofReal (s ^ 2 * ∫ z in unitDisc, ‖f ((s : ℂ) * z)‖ ^ 2) ≤
      ENNReal.ofReal (∫ z in unitDisc, ‖f z‖ ^ 2) := by
    rw [hmass, ofReal_integral_eq_lintegral_ofReal
      (a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) hf)
      (Eventually.of_forall fun z => sq_nonneg _)]
    exact lintegral_mono_set (ball_subset_ball hs1.le)
  have hmreal := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun z => sq_nonneg ‖f z‖)).mp hm
  apply (le_div_iff₀ (sq_pos_of_pos hs0)).mpr
  simpa only [mul_comm] using hmreal

/-- Derivative of an inward dilation at an interior disk point (TT:3592–3618). -/
theorem A21_dilate_deriv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv (fun w => f ((s : ℂ) * w)) z = (s : ℂ) * deriv f ((s : ℂ) * z) := by
  have hsz : (s : ℂ) * z ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    exact (mul_le_of_le_one_left (norm_nonneg z) hs1.le).trans_lt (mem_ball_zero_iff.mp hz)
  have hd := deriv_comp z (hf.differentiableAt (isOpen_ball.mem_nhds hsz))
    (differentiableAt_id.const_mul (s : ℂ))
  change deriv (fun w => f ((s : ℂ) * w)) z =
    deriv f ((s : ℂ) * z) * deriv (fun w : ℂ => (s : ℂ) * w) z at hd
  have hlin : deriv (fun w : ℂ => (s : ℂ) * w) z = (s : ℂ) := by simp
  rw [hlin] at hd
  simpa only [mul_comm] using hd

/-- The sharp weighted derivative estimate for every holomorphic area-L2 function on the disk (TT:3592–3618). -/
theorem A21_disk_derivative_bound {f : ℂ → ℂ} (hf : f ∈ A21fun unitDisc) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv f z‖ ^ 2 * (rho z)⁻¹)) ≤
      ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) := by
  let s : ℕ → ℝ := fun n => (n + 1 : ℝ) / (n + 2)
  have hs0 (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs1 (n : ℕ) : s n < 1 := by
    dsimp [s]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hsT : Tendsto s atTop (𝓝 1) := by
    have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [s, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  let g : ℕ → ℂ → ℂ := fun n z => f ((s n : ℂ) * z)
  let F : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖deriv (g n) z‖ ^ 2 * (rho z)⁻¹)
  have hR (n : ℕ) : ∃ R : ℝ, 1 < R ∧ DifferentiableOn ℂ (g n) (closedBall 0 R) :=
    holomorphic_inward_dilate hf.1 (hs0 n) (hs1 n)
  have hmeas (n : ℕ) : AEMeasurable (F n) (volume.restrict unitDisc) := by
    obtain ⟨R, hR1, hd⟩ := hR n
    have hder : ContinuousOn (deriv (g n)) unitDisc :=
      (((hd.mono ball_subset_closedBall).deriv isOpen_ball).continuousOn).mono (ball_subset_ball hR1.le)
    have hc : ContinuousOn (fun z => ‖deriv (g n) z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
      apply (hder.norm.pow 2).mul
      simp only [rho, inv_div]
      fun_prop
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable measurableSet_ball
  have hconv (z : ℂ) (hz : z ∈ unitDisc) :
      Tendsto (fun n => F n z) atTop (𝓝 (ENNReal.ofReal (‖deriv f z‖ ^ 2 * (rho z)⁻¹))) := by
    have hsC := Complex.continuous_ofReal.continuousAt.tendsto.comp hsT
    have harg : Tendsto (fun n => (s n : ℂ) * z) atTop (𝓝 z) := by simpa using hsC.mul_const z
    have hdf : ContinuousAt (deriv f) z :=
      (hf.1.deriv (show IsOpen unitDisc from isOpen_ball)).continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
    have hdlim : Tendsto (fun n => deriv (g n) z) atTop (𝓝 (deriv f z)) := by
      have h := hsC.mul (hdf.tendsto.comp harg)
      simpa only [Function.comp_apply, g, A21_dilate_deriv hf.1 (hs0 _) (hs1 _) hz,
        Complex.ofReal_one, one_mul] using h
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hdlim.norm.pow 2).mul_const ((rho z)⁻¹))
  have hI (n : ℕ) : (∫⁻ z in unitDisc, F n z) ≤
      ENNReal.ofReal (((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) / (s n) ^ 2) := by
    obtain ⟨R, hR1, hd⟩ := hR n
    apply (A21_closedDisk_derivative_bound hR1 hd).trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (A21_dilate_mass_bound hf (hs0 n) (hs1 n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa only [mul_div_assoc] using h
  have hright : Tendsto (fun n => ENNReal.ofReal (((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) / (s n) ^ 2))
      atTop (𝓝 (ENNReal.ofReal ((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2))) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ) * ∫ z in unitDisc, ‖f z‖ ^ 2)).div
      (hsT.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
    simpa only [Function.comp_def, Pi.div_apply, one_pow, div_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  calc
    _ = ∫⁻ z in unitDisc, liminf (fun n => F n z) atTop := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact (hconv z hz).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ z in unitDisc, F n z) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun n => ENNReal.ofReal (((1 / 2) * ∫ z in unitDisc, ‖f z‖ ^ 2) / (s n) ^ 2)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hI)
    _ = _ := hright.liminf_eq

/-- The squared direction has finite weighted area norm, using the proved inclusion of Lemma 1.3 (TT:3592–3618). -/
theorem A21_square_weighted_integrable {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior)
    {f : ℂ → ℂ} (hf : f ∈ A21fun D) :
    IntegrableOn (fun z => ‖f z‖ ^ 4 * (rho z)⁻¹) D := by
  have hDm : MeasurableSet D := by
    rcases hD with rfl | rfl
    · exact measurableSet_ball
    · exact (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨C₀, hC₀⟩ := (a21_mem_AInf1fun hD hf).2
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hpoint (z : ℂ) (hz : z ∈ D) :
      ‖f z‖ ^ 4 * (rho z)⁻¹ ≤ (C ^ 2 / 4) * ‖f z‖ ^ 2 := by
    have hb : |1 - ‖z‖ ^ 2| * ‖f z‖ ≤ C := by
      have h := (hC₀ z hz).trans (le_max_left C₀ 0)
      have hcast : 1 - (‖z‖ : ℂ) ^ 2 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast] at h
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
    have hsq := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hb 2
    rw [mul_pow, sq_abs] at hsq
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖f z‖)
    rw [rho, inv_div]
    nlinarith [hm]
  have hc : ContinuousOn (fun z => ‖f z‖ ^ 4 * (rho z)⁻¹) D := by
    apply (hf.1.continuousOn.norm.pow 4).mul
    simp only [rho, inv_div]
    fun_prop
  apply ((a21_integrable_sq hDm hf).const_mul (C ^ 2 / 4)).mono' (hc.aestronglyMeasurable hDm)
  filter_upwards [ae_restrict_mem hDm] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold rho; positivity)]
  exact hpoint z hz

/-- The derivative of a disk A21 function has integrable squared norm against rho-inverse (TT:3592–3618). -/
theorem A21_disk_derivative_integrable {f : ℂ → ℂ} (hf : f ∈ A21fun unitDisc) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
  have hc : ContinuousOn (fun z => ‖deriv f z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply ((hf.1.deriv (show IsOpen unitDisc from isOpen_ball)).continuousOn.norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  refine ⟨hc.aestronglyMeasurable measurableSet_ball, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
    show 0 ≤ ‖deriv f z‖ ^ 2 * (rho z)⁻¹ by unfold rho; positivity)).mpr
  exact (A21_disk_derivative_bound hf).trans_lt ENNReal.ofReal_lt_top

/-- The disk clause of Lemma 1.5 (TT:3592–3618), independently of its problematic exterior clause. -/
theorem lemma_1_5_disc {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    PsiOp ψ ∈ A2fun unitDisc := by
  have hd : DifferentiableOn ℂ (PsiOp ψ) unitDisc :=
    (hψ.1.deriv (show IsOpen unitDisc from isOpen_ball)).sub ((hψ.1.pow 2).const_mul (1 / 2))
  have hbase := ((A21_disk_derivative_integrable hψ).const_mul 2).add
    ((A21_square_weighted_integrable (Or.inl rfl) hψ).const_mul (1 / 2))
  have hc : ContinuousOn (fun z => ‖PsiOp ψ z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply (hd.continuousOn.norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  have hi : IntegrableOn (fun z => ‖PsiOp ψ z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply hbase.mono' (hc.aestronglyMeasurable measurableSet_ball)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hn : ‖PsiOp ψ z‖ ≤ ‖deriv ψ z‖ + (1 / 2 : ℝ) * ‖ψ z‖ ^ 2 := by
      change ‖deriv ψ z - (1 / 2 : ℂ) * ψ z ^ 2‖ ≤ _
      calc
        _ ≤ ‖deriv ψ z‖ + ‖(1 / 2 : ℂ) * ψ z ^ 2‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, norm_pow]; norm_num
    have hs : ‖PsiOp ψ z‖ ^ 2 ≤ 2 * ‖deriv ψ z‖ ^ 2 + (1 / 2 : ℝ) * ‖ψ z‖ ^ 4 := by
      nlinarith [sq_nonneg (‖deriv ψ z‖ - (1 / 2 : ℝ) * ‖ψ z‖ ^ 2),
        mul_nonneg (sub_nonneg.mpr hn)
          (show 0 ≤ ‖deriv ψ z‖ + (1 / 2 : ℝ) * ‖ψ z‖ ^ 2 + ‖PsiOp ψ z‖ by positivity)]
    have hrho : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
    have hm := mul_le_mul_of_nonneg_right hs hrho
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hrho)]
    change ‖PsiOp ψ z‖ ^ 2 * (rho z)⁻¹ ≤
      2 * (‖deriv ψ z‖ ^ 2 * (rho z)⁻¹) + (1 / 2) * (‖ψ z‖ ^ 4 * (rho z)⁻¹)
    nlinarith [hm]
  have hfin := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
    show 0 ≤ ‖PsiOp ψ z‖ ^ 2 * (rho z)⁻¹ by unfold rho; positivity)).mp hi.2
  have hsq : (∫⁻ z in unitDisc, (‖PsiOp ψ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)⁻¹) < ∞ := by
    simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, enorm_eq_nnnorm] using hfin
  exact ⟨hd, ENNReal.rpow_lt_top_of_nonneg (by norm_num) hsq.ne⟩

/-- The extra term under ordinary one-form pullback explains the exterior-Psi obstruction.
This uses the operator defined at TT:3585, without changing that definition. -/
theorem PsiOp_oneForm_pullback {ψ h : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ (h z)) (hh : DifferentiableAt ℂ h z)
    (hh' : DifferentiableAt ℂ (deriv h) z) :
    PsiOp (fun w => ψ (h w) * deriv h w) z =
      PsiOp ψ (h z) * deriv h z ^ 2 + ψ (h z) * deriv (deriv h) z := by
  have hd := ((hψ.hasDerivAt.comp z hh.hasDerivAt).mul hh'.hasDerivAt).deriv
  change deriv (fun w => ψ (h w) * deriv h w) z = _ at hd
  simp only [Function.comp_apply] at hd
  unfold PsiOp
  rw [hd]
  ring

/-- Cubic decay makes the divided inverted one-form square-integrable at the origin. -/
theorem a21_inverted_cubic {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDiscExterior)
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) :
    (fun z : ℂ => -ψ z⁻¹ / z ^ 3) ∈ A21fun (unitDisc \ {0}) := by
  obtain ⟨C, R, hdecay⟩ := hdecay
  let M : ℝ := max R 1 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right R 1]
  have hRM : R < M := by dsimp [M]; linarith [le_max_left R 1]
  let η : ℂ → ℂ := fun z => ψ z⁻¹ * deriv (fun w : ℂ => w⁻¹) z
  have hη := a21_pullback (show IsOpen (unitDisc \ {0}) from
    isOpen_ball.sdiff isClosed_singleton) a21_inversion_conformal hψ
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hd : DifferentiableOn ℂ (fun z : ℂ => -ψ z⁻¹ / z ^ 3) (unitDisc \ {0}) := by
    intro z hz
    have hp := hψ.1.differentiableAt (resolvent_exterior_isOpen.mem_nhds (a21_inv_punctured hz))
    exact ((hp.comp z (differentiableAt_inv hz.2)).neg.div
      (differentiableAt_id.pow 3) (pow_ne_zero 3 (show z ≠ 0 from hz.2))).differentiableWithinAt
  have hfinite : volume (unitDisc \ {(0 : ℂ)}) ≠ ∞ :=
    (measure_mono Set.sdiff_subset).trans_lt (show volume unitDisc < ∞ from measure_ball_lt_top) |>.ne
  have hiη := a21_integrable_sq hopen.measurableSet hη
  have hib : IntegrableOn (fun z => C ^ 2 + M ^ 2 * ‖η z‖ ^ 2) (unitDisc \ {0}) :=
    (integrableOn_const hfinite).add (hiη.const_mul (M ^ 2))
  have hi : IntegrableOn (fun z : ℂ => ‖-ψ z⁻¹ / z ^ 3‖ ^ 2) (unitDisc \ {0}) := by
    apply hib.mono' ((hd.continuousOn.norm.pow 2).aestronglyMeasurable hopen.measurableSet)
    filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖-ψ z⁻¹ / z ^ 3‖ ^ 2 ≤ C ^ 2 + M ^ 2 * ‖η z‖ ^ 2
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
    have hid : ‖-ψ z⁻¹ / z ^ 3‖ = ‖ψ z⁻¹‖ / ‖z‖ ^ 3 := by simp
    have he : ‖η z‖ = ‖ψ z⁻¹‖ / ‖z‖ ^ 2 := by
      simp [η, deriv_inv, norm_mul, div_eq_mul_inv]
    by_cases hs : ‖z‖ < M⁻¹
    · have hlarge : R < ‖z⁻¹‖ := by
        rw [norm_inv]
        exact hRM.trans ((lt_inv_comm₀ hzpos hM).mp hs)
      have hb := hdecay z⁻¹ hlarge
      rw [norm_inv, inv_pow, div_inv_eq_mul] at hb
      have hb' : ‖-ψ z⁻¹ / z ^ 3‖ ≤ C := by
        rw [hid, div_le_iff₀ (pow_pos hzpos 3)]
        exact hb
      have hC : 0 ≤ C := (norm_nonneg _).trans hb'
      nlinarith [sq_le_sq₀ (norm_nonneg _) hC |>.mpr hb',
        mul_nonneg (sq_nonneg M) (sq_nonneg ‖η z‖)]
    · have hb : ‖-ψ z⁻¹ / z ^ 3‖ ≤ M * ‖η z‖ := by
        rw [hid, he]
        have hzM : 1 ≤ M * ‖z‖ := by
          have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hM.le
          simpa [hM.ne'] using hm
        apply (div_le_iff₀ (pow_pos hzpos 3)).mpr
        have hid' : M * (‖ψ z⁻¹‖ / ‖z‖ ^ 2) * ‖z‖ ^ 3 =
            ‖ψ z⁻¹‖ * (M * ‖z‖) := by field_simp
        rw [hid']
        exact le_mul_of_one_le_right (norm_nonneg _) hzM
      have hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM.le (norm_nonneg (η z))) |>.mpr hb
      nlinarith [sq_nonneg C]
  apply (mem_A21fun_iff_memLp hopen.measurableSet).mpr
  exact ⟨hd, (memLp_two_iff_integrable_sq_norm
    (hd.continuousOn.aestronglyMeasurable hopen.measurableSet)).mpr hi⟩

/-- Multiplication by the disk coordinate preserves the holomorphic area space. -/
theorem A21_disk_mul_id {g : ℂ → ℂ} (hg : g ∈ A21fun unitDisc) :
    (fun z => z * g z) ∈ A21fun unitDisc := by
  have hd : DifferentiableOn ℂ (fun z => z * g z) unitDisc := differentiableOn_id.mul hg.1
  have hi : IntegrableOn (fun z => ‖z * g z‖ ^ 2) unitDisc := by
    apply (a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) hg).mono'
      ((hd.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_ball)
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    change ‖‖z * g z‖ ^ 2‖ ≤ ‖g z‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    exact mul_le_of_le_one_left (sq_nonneg _) hz2
  exact (mem_A21fun_iff_memLp (show MeasurableSet unitDisc from measurableSet_ball)).mpr
    ⟨hd, (memLp_two_iff_integrable_sq_norm
      (hd.continuousOn.aestronglyMeasurable measurableSet_ball)).mpr hi⟩

/-- Disk area-square-integrability implies inverse-density-square-integrability. -/
theorem A21_disk_weighted_integrable {g : ℂ → ℂ} (hg : g ∈ A21fun unitDisc) :
    IntegrableOn (fun z => ‖g z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
  have hc : ContinuousOn (fun z => ‖g z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    apply (hg.1.continuousOn.norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  apply ((a21_integrable_sq (show MeasurableSet unitDisc from measurableSet_ball) hg).const_mul
    (1 / 4 : ℝ)).mono' (hc.aestronglyMeasurable measurableSet_ball)
  filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
  change ‖‖g z‖ ^ 2 * (rho z)⁻¹‖ ≤ (1 / 4) * ‖g z‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (rhoInv_disk_bounds hz).1)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (rhoInv_disk_bounds hz).2 (sq_nonneg ‖g z‖)

/-- Weighted square-integrability is closed under addition. -/
theorem weighted_sq_integrable_add {D : Set ℂ} (hD : MeasurableSet D) {f g : ℂ → ℂ}
    (hf : ContinuousOn f D) (hg : ContinuousOn g D)
    (hfi : IntegrableOn (fun z => ‖f z‖ ^ 2 * (rho z)⁻¹) D)
    (hgi : IntegrableOn (fun z => ‖g z‖ ^ 2 * (rho z)⁻¹) D) :
    IntegrableOn (fun z => ‖f z + g z‖ ^ 2 * (rho z)⁻¹) D := by
  have hc : ContinuousOn (fun z => ‖f z + g z‖ ^ 2 * (rho z)⁻¹) D := by
    apply ((hf.add hg).norm.pow 2).mul
    simp only [rho, inv_div]
    fun_prop
  apply ((hfi.const_mul 2).add (hgi.const_mul 2)).mono' (hc.aestronglyMeasurable hD)
  filter_upwards [ae_restrict_mem hD] with z hz
  have hn := norm_add_le (f z) (g z)
  have hs : ‖f z + g z‖ ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
    have hsq := sq_le_sq₀ (norm_nonneg (f z + g z))
      (add_nonneg (norm_nonneg (f z)) (norm_nonneg (g z))) |>.mpr hn
    nlinarith [sq_nonneg (‖f z‖ - ‖g z‖)]
  have hr : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
  change ‖‖f z + g z‖ ^ 2 * (rho z)⁻¹‖ ≤
    2 * (‖f z‖ ^ 2 * (rho z)⁻¹) + 2 * (‖g z‖ ^ 2 * (rho z)⁻¹)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr)]
  nlinarith [mul_le_mul_of_nonneg_right hs hr]

/-- The inversion law for Psi has a plus sign in its correction term. -/
theorem PsiOp_inversion_identity {ψ g : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ unitDiscExterior)
    (heq : EqOn g (fun z : ℂ => -ψ z⁻¹ / z ^ 3) (unitDisc \ {0}))
    {z : ℂ} (hz : z ∈ unitDisc \ {0}) :
    PsiOp ψ z⁻¹ / z ^ 4 = PsiOp (fun w => w * g w) z + 2 * g z := by
  have hz0 : z ≠ 0 := hz.2
  have hp := hψ.differentiableAt (resolvent_exterior_isOpen.mem_nhds (a21_inv_punctured hz))
  have hdInv : DifferentiableAt ℂ (deriv (fun w : ℂ => w⁻¹)) z := by
    rw [deriv_inv']
    exact ((differentiableAt_id.pow 2).inv (pow_ne_zero 2 hz0)).neg
  have hid := PsiOp_oneForm_pullback hp (differentiableAt_inv hz0) hdInv
  have hevent : (fun w => w * g w) =ᶠ[𝓝 z]
      (fun w => ψ w⁻¹ * deriv (fun u : ℂ => u⁻¹) w) := by
    filter_upwards [(show IsOpen (unitDisc \ {(0 : ℂ)}) from
      isOpen_ball.sdiff isClosed_singleton).mem_nhds hz] with w hw
    rw [heq hw, deriv_inv]
    field_simp
    <;> ring
  have hder := hevent.deriv_eq
  have hval := hevent.self_of_nhds
  have hPsi : PsiOp (fun w => w * g w) z =
      PsiOp (fun w => ψ w⁻¹ * deriv (fun u : ℂ => u⁻¹) w) z := by
    unfold PsiOp
    rw [hder, hval]
  have hsecond : deriv (deriv (fun w : ℂ => w⁻¹)) z = 2 / z ^ 3 := by
    rw [deriv_inv']
    have hh := (((hasDerivAt_id z).pow 2).inv (pow_ne_zero 2 hz0)).neg
    change HasDerivAt (fun w : ℂ => -(w ^ 2)⁻¹) (-(-(2 * z ^ (2 - 1) * 1) / (z ^ 2) ^ 2)) z at hh
    rw [hh.deriv]
    norm_num
    field_simp
    <;> ring
  rw [hPsi, hid, hsecond, deriv_inv, heq hz]
  field_simp
  <;> ring

/-- The normalized exterior clause of Lemma 1.5, with the O(z^-3) condition of TT:5942.
The unrestricted exterior clause is deliberately left unchanged. -/
theorem lemma_1_5_exterior_of_cubic_decay {ψ : ℂ → ℂ}
    (hψ : ψ ∈ A21fun unitDiscExterior)
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) :
    PsiOp ψ ∈ A2fun unitDiscExterior := by
  obtain ⟨g, hg, heq, _⟩ := a21_remove_puncture (a21_inverted_cubic hψ hdecay)
  have hη := A21_disk_mul_id hg
  have hP := lemma_1_5_disc hη
  have h2g : IntegrableOn (fun z => ‖(2 : ℂ) * g z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
    have hh := (A21_disk_weighted_integrable hg).const_mul 4
    apply hh.congr
    filter_upwards [] with z
    simp only [norm_mul]
    norm_num
    ring
  have hi := weighted_sq_integrable_add (show MeasurableSet unitDisc from measurableSet_ball)
    hP.1.continuousOn ((hg.1.const_mul 2).continuousOn)
    (A2fun.integrable_weighted_sq (show IsOpen unitDisc from isOpen_ball) hP) h2g
  have hopen : IsOpen (unitDisc \ {(0 : ℂ)}) := isOpen_ball.sdiff isClosed_singleton
  have hip : IntegrableOn (fun z => ‖PsiOp ψ z⁻¹ / z ^ 4‖ ^ 2 * (rho z)⁻¹)
      (unitDisc \ {0}) := by
    apply (hi.mono_set Set.sdiff_subset).congr
    filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
    rw [PsiOp_inversion_identity hψ.1 heq hz]
  have hc := a21_inversion_conformal
  have hchange := ahP_integrableOn_image hopen hc.1 hc.2.1
    (fun u => ‖PsiOp ψ u‖ ^ 2 * (rho u)⁻¹)
  rw [hc.2.2] at hchange
  have hie : IntegrableOn (fun u => ‖PsiOp ψ u‖ ^ 2 * (rho u)⁻¹) unitDiscExterior := by
    apply hchange.mpr
    apply hip.congr
    filter_upwards [ae_restrict_mem hopen.measurableSet] with z hz
    simpa only [smul_eq_mul, mul_comm] using inverted_quadratic_weight (φ := PsiOp ψ) hz.2
  exact ⟨(hψ.1.deriv resolvent_exterior_isOpen).sub ((hψ.1.pow 2).const_mul (1 / 2)),
    normA2_lt_top_of_integrable_weighted_sq hie⟩

/-- **Lemma 1.5** (TT:3592). `Ψ(A₂¹(𝔻)) ⊂ A₂(𝔻)`, and `Ψ` maps the `ψ ∈ A₂¹(𝔻*)` with `ψ(z) = O(z⁻³)` at `∞` into
`A₂(𝔻*)`.

[CORRECTION 2026-10-25] The exterior clause needs the decay `O(z⁻³)` (as in `Ã₂¹(𝔻*)`, TT:5942). For `ψ = z⁻²`,
`Ψ(ψ) ∉ A₂(𝔻*)` (lean4, `psiOp_not_mem_A2`). -/
theorem lemma_1_5 {D : Set ℂ} (hD : D = unitDisc ∨ D = unitDiscExterior) {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun D)
    (hdecay : D = unitDiscExterior → ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) :
    PsiOp ψ ∈ A2fun D := by
  rcases hD with rfl | rfl
  · exact lemma_1_5_disc hψ
  · exact lemma_1_5_exterior_of_cubic_decay hψ (hdecay rfl)

-- `thm_1_6` moved to `Ch2/S1_BP16Completed.lean` (2026-10-27).

/-- `h : S¹ → S¹` is a symmetric homeomorphism (Gardiner–Sullivan [GS92], TT:3640).
- `h(e^{it}) = e^{iu(t)}`, with `u` continuous, strictly increasing and `u(t + 2π) = u(t) + 2π`.
- `u` is asymptotically symmetric: `(u(x + t) - u(x))/(u(x) - u(x - t)) → 1` as `t → 0⁺`, uniformly in `x`. -/
def IsSymmetricHomeo (h : ℂ → ℂ) : Prop :=
  ∃ u : ℝ → ℝ, Continuous u ∧ StrictMono u ∧ (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
    (∀ t : ℝ, h (exp (t * I)) = exp (u t * I)) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x t : ℝ, 0 < t → t < δ → |(u (x + t) - u x) / (u x - u (x - t)) - 1| < ε

/-- The subgroup `S = Möb(S¹)\Homeo_s(S¹)` of `T(1)` (TT:3643): the classes `[μ]` with `w_μ|S¹` symmetric. -/
def symmetricT : Set T1 := {p | IsSymmetricHomeo (wA (Quotient.out p : LinfStarBall))}

-- `symmetricT_spec` moved unchanged to `Ch2/S1_SymmetricT.lean` (2026-10-28).

-- `cor_1_8` moved to `Ch2/S1_Cor18.lean` (2026-10-27).

-- `remark_1_9` moved to `Ch2/S1_Remark19.lean` (2026-10-27).

/-- **(1.1)** (TT:3676–3683). If `(1 - |z|²)|𝒜| ≤ ½` at `z ∈ 𝔻` and `𝒮 = 𝒜' - ½𝒜²` there, then
`2(1 - |z|²)²|𝒮|² ≥ (1 - |z|²)²|𝒜'|² - ¼|𝒜|²`. -/
theorem eq_1_1_ineq {A A' S : ℂ} {z : ℂ} (hz : z ∈ unitDisc) (hA : (1 - ‖z‖ ^ 2) * ‖A‖ ≤ 1 / 2)
    (hS : S = A' - (1 / 2) * A ^ 2) :
    (1 - ‖z‖ ^ 2) ^ 2 * ‖A'‖ ^ 2 - (1 / 4) * ‖A‖ ^ 2 ≤ 2 * (1 - ‖z‖ ^ 2) ^ 2 * ‖S‖ ^ 2 := by
  have hnorm : ‖A'‖ ≤ ‖S‖ + (1 / 2 : ℝ) * ‖A‖ ^ 2 := by
    calc
      ‖A'‖ = ‖S + (1 / 2 : ℂ) * A ^ 2‖ := by rw [hS]; ring_nf
      _ ≤ ‖S‖ + ‖(1 / 2 : ℂ) * A ^ 2‖ := norm_add_le _ _
      _ = ‖S‖ + (1 / 2 : ℝ) * ‖A‖ ^ 2 := by
        rw [norm_mul, norm_pow]; norm_num
  have hsq : ‖A'‖ ^ 2 ≤ 2 * ‖S‖ ^ 2 + (1 / 2 : ℝ) * (‖A‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (‖S‖ - (1 / 2 : ℝ) * ‖A‖ ^ 2),
      mul_nonneg (sub_nonneg.mpr hnorm)
        (show 0 ≤ ‖S‖ + (1 / 2 : ℝ) * ‖A‖ ^ 2 + ‖A'‖ by positivity)]
  have hweight : 0 ≤ 1 - ‖z‖ ^ 2 := by
    have hz' : ‖z‖ < 1 := by simpa [unitDisc, mem_ball, dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  have hsmall : (1 - ‖z‖ ^ 2) ^ 2 * ‖A‖ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA)
      (show 0 ≤ 1 / 2 + (1 - ‖z‖ ^ 2) * ‖A‖ by positivity)]
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 - ‖z‖ ^ 2))
  have herror := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖A‖)
  nlinarith [sq_nonneg ‖A‖]

/-- The scalar coefficient inequality used to obtain (1.2), TT:3698–3712. -/
theorem eq_1_2_radial_coefficient_bound {n : ℕ} (hn : 2 ≤ n) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    1 / (2 * (n : ℝ)) ≤ ((n : ℝ) - 1) ^ 2 *
      ((r ^ 2)⁻¹ / ((n : ℝ) - 1) - 2 / (n : ℝ) + r ^ 2 / ((n : ℝ) + 1)) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm : (0 : ℝ) < n - 1 := by linarith
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr0
  have hr21 : r ^ 2 < 1 := by nlinarith
  have htail : 0 ≤ (n : ℝ) + 1 - r ^ 2 * ((n : ℝ) - 1) := by
    have h := mul_le_mul_of_nonneg_right hr21.le hnm.le
    nlinarith
  have hid : (r ^ 2)⁻¹ / ((n : ℝ) - 1) - 2 / (n : ℝ) + r ^ 2 / ((n : ℝ) + 1) -
      (1 / ((n : ℝ) - 1) - 2 / (n : ℝ) + 1 / ((n : ℝ) + 1)) =
      (1 - r ^ 2) * ((n : ℝ) + 1 - r ^ 2 * ((n : ℝ) - 1)) /
        (r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) + 1)) := by
    field_simp [hr0.ne', hn0.ne', hnm.ne', hnp.ne']
    <;> ring
  have hnonneg : 0 ≤ (1 - r ^ 2) * ((n : ℝ) + 1 - r ^ 2 * ((n : ℝ) - 1)) /
      (r ^ 2 * ((n : ℝ) - 1) * ((n : ℝ) + 1)) := by positivity
  have hstep : 1 / ((n : ℝ) - 1) - 2 / (n : ℝ) + 1 / ((n : ℝ) + 1) ≤
      (r ^ 2)⁻¹ / ((n : ℝ) - 1) - 2 / (n : ℝ) + r ^ 2 / ((n : ℝ) + 1) := by
    linarith
  have hbase : 1 / (2 * (n : ℝ)) ≤ ((n : ℝ) - 1) ^ 2 *
      (1 / ((n : ℝ) - 1) - 2 / (n : ℝ) + 1 / ((n : ℝ) + 1)) := by
    have hid' : ((n : ℝ) - 1) ^ 2 *
        (1 / ((n : ℝ) - 1) - 2 / (n : ℝ) + 1 / ((n : ℝ) + 1)) - 1 / (2 * (n : ℝ)) =
        (3 * (n : ℝ) - 5) / (2 * (n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp [hn0.ne', hnm.ne', hnp.ne']
      <;> ring
    have hpos : 0 ≤ (3 * (n : ℝ) - 5) / (2 * (n : ℝ) * ((n : ℝ) + 1)) := by
      apply div_nonneg
      · linarith
      · positivity
    linarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hstep (sq_nonneg _))

/-- The polynomial disk integral lower bound underlying (1.2), in rho-inverse normalization. -/
theorem polynomial_A21_derivative_lower_bound (p : Polynomial ℂ) :
    (1 / 8) * (∫ z in unitDisc, ‖p.eval z‖ ^ 2) - π / 8 * ‖p.eval 0‖ ^ 2 ≤
      ∫ z in unitDisc, ‖deriv (fun w => p.eval w) z‖ ^ 2 * (rho z)⁻¹ := by
  have hsum : (∑ n ∈ p.derivative.support, ‖p.coeff (n + 1)‖ ^ 2 / ((n : ℝ) + 2)) =
      ∑ n ∈ p.support.erase 0, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1) := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      exact Finset.mem_erase.mpr ⟨by omega, Polynomial.of_mem_support_derivative hn⟩
    · intro a ha b hb hab
      omega
    · intro n hn
      have hn0 := (Finset.mem_erase.mp hn).1
      have hn1 : 1 ≤ n := by omega
      refine ⟨n - 1, ?_, by omega⟩
      rw [Polynomial.mem_support_derivative, Nat.sub_add_cancel hn1]
      exact (Finset.mem_erase.mp hn).2
    · intro n hn
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      ring
  have hs : (1 / 4 : ℝ) * (∑ n ∈ p.support.erase 0, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1)) ≤
      ∑ n ∈ p.derivative.support, ‖p.derivative.coeff n‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnat : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by norm_cast
    rw [Polynomial.coeff_derivative, norm_mul, mul_pow, hnat]
    have hid : ‖p.coeff (n + 1)‖ ^ 2 * ((n : ℝ) + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) =
        (‖p.coeff (n + 1)‖ ^ 2 / ((n : ℝ) + 2)) * (((n : ℝ) + 1) / ((n : ℝ) + 3)) := by
      field_simp
      <;> ring
    rw [hid]
    have hratio : (1 / 4 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 3) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ ‖p.coeff (n + 1)‖ ^ 2 / ((n : ℝ) + 2) by positivity)
  have hsplit : (∑ n ∈ p.support, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1)) =
      ‖p.coeff 0‖ ^ 2 + ∑ n ∈ p.support.erase 0, ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1) := by
    by_cases h0 : 0 ∈ p.support
    · convert (Finset.add_sum_erase p.support
        (fun n => ‖p.coeff n‖ ^ 2 / ((n : ℝ) + 1)) h0).symm using 1 <;> norm_num
    · have hc : p.coeff 0 = 0 := by simpa using h0
      simp [Finset.erase_eq_of_notMem h0, hc]
  simp_rw [p.deriv]
  rw [polynomial_weighted_area, polynomial_A21_area, hsplit]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ π / 2 by positivity)]

/-- Polynomial approximation together with uniform convergence of first derivatives
on the closed disk, used to pass (1.2) to holomorphic functions. -/
theorem polynomial_approx_closedDisk_with_deriv {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ∃ p : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 1) ∧
      TendstoUniformlyOn (fun n z => (p n).derivative.eval z) (deriv f) atTop (closedBall 0 1) := by
  let Rn : NNReal := ⟨R, by linarith⟩
  let rn : NNReal := ⟨(1 + R) / 2, by linarith⟩
  have hpower := hf.hasFPowerSeriesOnBall (R := Rn) (by change 0 < R; linarith)
  have hsmall : (rn : ℝ≥0∞) < (Rn : ℝ≥0∞) := by
    apply ENNReal.coe_lt_coe.mpr
    change (1 + R) / 2 < R
    linarith
  have hU := hpower.tendstoUniformlyOn hsmall
  let a : ℕ → ℂ := fun n => cauchyPowerSeries f 0 (Rn : ℝ) n (fun _ => 1)
  let p : ℕ → Polynomial ℂ := fun n => ∑ k ∈ Finset.range n, Polynomial.C (a k) * Polynomial.X ^ k
  have heval (n : ℕ) (z : ℂ) : (p n).eval z = (cauchyPowerSeries f 0 (Rn : ℝ)).partialSum n z := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, FormalMultilinearSeries.partialSum]
    apply Finset.sum_congr rfl
    intro k hk
    simp [a, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, mul_comm]
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (rn : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hz (by change 1 < (1 + R) / 2; linarith)
  have hup : TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (ball 0 (rn : ℝ)) := by
    simpa only [← heval, zero_add] using hU
  have hd := hup.tendstoLocallyUniformlyOn.deriv
    (Eventually.of_forall fun n => (p n).differentiable.differentiableOn) isOpen_ball
  refine ⟨p, hup.mono hsub, ?_⟩
  have hd' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall (0 : ℂ) 1)).mp (hd.mono hsub)
  change TendstoUniformlyOn (fun n z => deriv (fun w => (p n).eval w) z)
    (deriv f) atTop (closedBall 0 1) at hd'
  simpa only [Polynomial.deriv] using hd'

/-- The disk integral lower bound for a function holomorphic beyond the boundary. -/
theorem A21_closedDisk_derivative_lower_bound {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    (1 / 8) * (∫ z in unitDisc, ‖f z‖ ^ 2) - π / 8 * ‖f 0‖ ^ 2 ≤
      ∫ z in unitDisc, ‖deriv f z‖ ^ 2 * (rho z)⁻¹ := by
  obtain ⟨p, hp, hpd⟩ := polynomial_approx_closedDisk_with_deriv hR hf
  have hsub : closedBall (0 : ℂ) 1 ⊆ closedBall 0 R := closedBall_subset_closedBall hR.le
  have hfc := hf.continuousOn.mono hsub
  have hdc : ContinuousOn (deriv f) (closedBall 0 1) := by
    apply ((hf.mono ball_subset_closedBall).deriv isOpen_ball).continuousOn.mono
    intro z hz
    exact lt_of_le_of_lt hz hR
  have h0 : (0 : ℂ) ∈ closedBall 0 1 := by simp
  have hleft := ((A21_polynomial_integral_tendsto p hfc hp).const_mul (1 / 8)).sub
    (((hp.tendsto_at h0).norm.pow 2).const_mul (π / 8))
  have hright := weighted_polynomial_integral_tendsto (fun n => (p n).derivative) hdc hpd
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  simpa only [Polynomial.deriv] using polynomial_A21_derivative_lower_bound (p n)

/-- The integral estimate (1.2) for holomorphic functions, before identifying the
constant term from the stated power series. -/
theorem eq_1_2_of_differentiable {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖f z‖ ^ 2) - π / 2 * ‖f 0‖ ^ 2 * r ^ 2 ≤
      ∫ z in ball (0 : ℂ) r, (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv f z‖ ^ 2 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hc : IsConformalOnto (fun z : ℂ => (r : ℂ) * z) unitDisc (ball 0 r) := by
    refine ⟨(differentiable_id.const_mul (r : ℂ)).differentiableOn,
      (fun x hx y hy hxy => mul_left_cancel₀ hrC hxy), ?_⟩
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [mem_ball_zero_iff.mp hz]
    · intro hw
      refine ⟨w / (r : ℂ), ?_, ?_⟩
      · apply mem_ball_zero_iff.mpr
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        exact (div_lt_one hr0).mpr (mem_ball_zero_iff.mp hw)
      · field_simp
  let F : ℂ → ℂ := fun z => f ((r : ℂ) * z)
  obtain ⟨R, hR, hF⟩ := holomorphic_inward_dilate hf hr0 hr1
  have hFd : ContinuousOn (deriv F) (closedBall 0 1) := by
    apply ((hF.mono ball_subset_closedBall).deriv isOpen_ball).continuousOn.mono
    intro z hz
    exact lt_of_le_of_lt hz hR
  have hbase := A21_closedDisk_derivative_lower_bound hR hF
  have hlin (z : ℂ) : deriv (fun w : ℂ => (r : ℂ) * w) z = (r : ℂ) := by simp
  have hmass := ahP_integral_image (show IsOpen unitDisc from isOpen_ball) hc.1 hc.2.1
    (fun z => ‖f z‖ ^ 2)
  rw [hc.2.2] at hmass
  simp only [hlin, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, smul_eq_mul] at hmass
  rw [integral_const_mul] at hmass
  have hweighted := ahP_integral_image (show IsOpen unitDisc from isOpen_ball) hc.1 hc.2.1
    (fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv f z‖ ^ 2)
  rw [hc.2.2] at hweighted
  simp only [hlin, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, smul_eq_mul] at hweighted
  have htrans : (∫ z in ball (0 : ℂ) r, (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv f z‖ ^ 2) =
      ∫ z in unitDisc, (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2 * ‖deriv F z‖ ^ 2 := by
    rw [hweighted]
    apply setIntegral_congr_fun (show MeasurableSet unitDisc from measurableSet_ball)
    intro z hz
    have hd := A21_dilate_deriv hf hr0 hr1 hz
    change deriv F z = _ at hd
    dsimp only
    rw [hd]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, mul_pow]
    ring
  have hlo : IntegrableOn (fun z => 4 * r ^ 2 * (‖deriv F z‖ ^ 2 * (rho z)⁻¹)) unitDisc := by
    have hcont : ContinuousOn (fun z => 4 * r ^ 2 * (‖deriv F z‖ ^ 2 * (rho z)⁻¹))
        (closedBall 0 1) := by
      apply continuousOn_const.mul
      apply (hFd.norm.pow 2).mul
      simp only [rho, inv_div]
      fun_prop
    exact (hcont.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hhi : IntegrableOn (fun z => (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2 * ‖deriv F z‖ ^ 2) unitDisc := by
    have hcont : ContinuousOn (fun z => (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2 * ‖deriv F z‖ ^ 2)
        (closedBall 0 1) := (by fun_prop : ContinuousOn
          (fun z : ℂ => (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2) (closedBall 0 1)).mul (hFd.norm.pow 2)
    exact (hcont.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hle : 4 * r ^ 2 * (∫ z in unitDisc, ‖deriv F z‖ ^ 2 * (rho z)⁻¹) ≤
      ∫ z in unitDisc, (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2 * ‖deriv F z‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hlo hhi (show MeasurableSet unitDisc from measurableSet_ball)
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hprod := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖z‖)
    have hs : (1 - ‖z‖ ^ 2) ^ 2 ≤ (1 - r ^ 2 * ‖z‖ ^ 2) ^ 2 := by nlinarith
    have hs' := mul_le_of_le_one_left (sq_nonneg (1 - ‖z‖ ^ 2)) hr2
    have hm := mul_le_mul_of_nonneg_right (hs'.trans hs) (sq_nonneg ‖deriv F z‖)
    simp only [rho, inv_div]
    nlinarith [hm]
  have hscaled := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 4 * r ^ 2 by positivity)
  rw [hmass, htrans]
  change (1 / 2) * (r ^ 2 * ∫ z in unitDisc, ‖F z‖ ^ 2) - π / 2 * ‖f 0‖ ^ 2 * r ^ 2 ≤ _
  have hF0 : F 0 = f 0 := by simp [F]
  change (1 / 8) * (∫ z in unitDisc, ‖F z‖ ^ 2) - π / 8 * ‖F 0‖ ^ 2 ≤ _ at hbase
  change 4 * r ^ 2 * ((1 / 8) * (∫ z in unitDisc, ‖F z‖ ^ 2) - π / 8 * ‖F 0‖ ^ 2) ≤ _ at hscaled
  rw [hF0] at hscaled
  nlinarith

/-- A convergent scalar power series on the disk defines a holomorphic function there. -/
theorem differentiableOn_of_powerSeries {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hc : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) :
    DifferentiableOn ℂ f unitDisc := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  let r : ℝ := (‖z‖ + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hzr : ‖z‖ < r := by dsimp [r]; linarith
  let rn : NNReal := ⟨r, hr0.le⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hrr : (r : ℂ) ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    simpa [Complex.norm_real, abs_of_pos hr0] using hr1
  have hs := (hc (r : ℂ) hrr).summable.norm
  have hrad : (rn : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    change Summable (fun n => ‖p n‖ * r ^ n)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hs
  have hpower : HasFPowerSeriesOnBall f p 0 rn := by
    refine ⟨hrad, by exact_mod_cast hr0, ?_⟩
    intro y hy
    have hy' : y ∈ unitDisc := by
      rw [Metric.eball_coe] at hy
      exact (ball_subset_ball hr1.le) hy
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hc y hy'
  have hzb : z ∈ Metric.eball (0 : ℂ) (rn : ℝ≥0∞) := by
    rw [Metric.eball_coe]
    exact mem_ball_zero_iff.mpr hzr
  exact (hpower.differentiableOn.differentiableAt
    ((show IsOpen (Metric.eball (0 : ℂ) (rn : ℝ≥0∞)) from Metric.isOpen_eball).mem_nhds hzb)).differentiableWithinAt

/-- **(1.2)** (TT:3698–3712). For `ψ = Σ_{n ≥ 1} n a_n z^{n-1}` holomorphic on `𝔻` and `0 < r < 1`:
`∬_{𝔻_r} (1 - |z|²)² |ψ'|² d²z ≥ ½ ∬_{𝔻_r} |ψ|² d²z - (π/2)|a₁|² r²`. -/
theorem eq_1_2_ineq {ψ : ℂ → ℂ} {a : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) * z ^ n) (ψ z)) {r : ℝ} (hr0 : 0 < r)
    (hr : r < 1) :
    (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖ψ z‖ ^ 2) - π / 2 * ‖a 1‖ ^ 2 * r ^ 2 ≤
      ∫ z in ball (0 : ℂ) r, (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv ψ z‖ ^ 2 := by
  have hψ := differentiableOn_of_powerSeries ha
  have h0 : ψ 0 = a 1 := by
    have hh := (ha 0 (by simp [unitDisc])).tsum_eq
    simpa only [zero_pow_eq, mul_ite, mul_one, mul_zero, tsum_ite_eq, Nat.cast_one,
      zero_add, one_mul, if_pos] using hh.symm
  simpa only [h0] using eq_1_2_of_differentiable hψ hr0 hr

/-- The coercive smaller-disk estimate in the proof of Lemma 1.11 (TT:3666–3734).
The boundary smallness is explicit; it does not follow from univalence alone. -/
theorem lemma_1_11_disk_mass_bound {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A unitDisc)
    (hS : PsiOp A ∈ A2fun unitDisc)
    (hsmall : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ z ∈ unitDisc,
      s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖A z‖ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r < 1 → ∫ z in ball (0 : ℂ) r, ‖A z‖ ^ 2 ≤ C := by
  obtain ⟨s, hs0, hs1, hs⟩ := hsmall
  let H : ℂ → ℝ := fun z => (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv A z‖ ^ 2
  have hH : ContinuousOn H unitDisc :=
    (by fun_prop : ContinuousOn (fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 2) unitDisc).mul
      ((hA.deriv (show IsOpen unitDisc from isOpen_ball)).continuousOn.norm.pow 2)
  have hsub (r : ℝ) (hr : r < 1) : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    (hH.mono (hsub s hs1))
  let J : ℂ → ℝ := fun z => 8 * (‖PsiOp A z‖ ^ 2 * (rho z)⁻¹) + max B 0
  have hJi : IntegrableOn J unitDisc :=
    ((A2fun.integrable_weighted_sq (show IsOpen unitDisc from isOpen_ball) hS).const_mul 8).add
      (integrableOn_const (show volume unitDisc ≠ ∞ from measure_ball_lt_top.ne))
  have hJ0 (z : ℂ) : 0 ≤ J z := by dsimp [J, rho]; positivity
  have hpoint (z : ℂ) (hz : z ∈ unitDisc) : H z ≤ J z + (1 / 4) * ‖A z‖ ^ 2 := by
    by_cases hzs : ‖z‖ ≤ s
    · have hb := hB z (mem_closedBall_zero_iff.mpr hzs)
      have hH0 : 0 ≤ H z := by dsimp [H]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hH0] at hb
      have hpos : 0 ≤ 8 * (‖PsiOp A z‖ ^ 2 * (rho z)⁻¹) := by unfold rho; positivity
      dsimp [J]
      nlinarith [le_max_left B 0, sq_nonneg ‖A z‖]
    · have hp := eq_1_1_ineq hz (hs z hz (lt_of_not_ge hzs)) (A' := deriv A z)
        (S := PsiOp A z) rfl
      dsimp [H, J, rho]
      rw [inv_div]
      nlinarith [le_max_right B 0]
  refine ⟨4 * (∫ z in unitDisc, J z) + 2 * π * ‖A 0‖ ^ 2, ?_⟩
  intro r hr0 hr1
  have hAi : IntegrableOn (fun z => ‖A z‖ ^ 2) (ball (0 : ℂ) r) :=
    (((hA.continuousOn.norm.pow 2).mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hHi : IntegrableOn H (ball (0 : ℂ) r) :=
    ((hH.mono (hsub r hr1)).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
  have hrd : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hJr := hJi.mono_set hrd
  have hupper : (∫ z in ball (0 : ℂ) r, H z) ≤
      (∫ z in unitDisc, J z) + (1 / 4) * ∫ z in ball (0 : ℂ) r, ‖A z‖ ^ 2 := by
    have hi := setIntegral_mono_on hHi (hJr.add (hAi.const_mul (1 / 4))) measurableSet_ball
      (fun z hz => hpoint z (hrd hz))
    simp only [Pi.add_apply] at hi
    rw [integral_add hJr (hAi.const_mul (1 / 4)), integral_const_mul] at hi
    have hJle := setIntegral_mono_set hJi (Eventually.of_forall hJ0) (Eventually.of_forall hrd)
    linarith
  have hlower := eq_1_2_of_differentiable hA hr0 hr1
  change (1 / 2) * (∫ z in ball (0 : ℂ) r, ‖A z‖ ^ 2) - π / 2 * ‖A 0‖ ^ 2 * r ^ 2 ≤
    ∫ z in ball (0 : ℂ) r, H z at hlower
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have herror := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ π / 2 * ‖A 0‖ ^ 2 by positivity)
  nlinarith

/-- Uniform smaller-disk area bounds give genuine A21 membership. -/
theorem a21_of_uniform_disk_mass {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A unitDisc)
    (hbound : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r < 1 → ∫ z in ball (0 : ℂ) r, ‖A z‖ ^ 2 ≤ C) :
    A ∈ A21fun unitDisc := by
  obtain ⟨C, hC⟩ := hbound
  let I := {q : ℚ // 0 < q ∧ q < 1}
  let U : I → Set ℂ := fun q => ball 0 (q.val : ℝ)
  have hdir : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨⟨max a.val b.val, lt_max_iff.mpr (Or.inl a.property.1),
      max_lt a.property.2 b.property.2⟩, ?_, ?_⟩
    · apply ball_subset_ball
      exact_mod_cast le_max_left a.val b.val
    · apply ball_subset_ball
      exact_mod_cast le_max_right a.val b.val
  have hUnion : unitDisc = ⋃ q : I, U q := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hqz, hq1⟩ := exists_rat_btwn (mem_ball_zero_iff.mp hz)
      have hq0 : (0 : ℝ) < q := (norm_nonneg z).trans_lt hqz
      have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
      have hq1' : q < (1 : ℚ) := by exact_mod_cast hq1
      exact mem_iUnion.mpr ⟨⟨q, hq0', hq1'⟩, mem_ball_zero_iff.mpr hqz⟩
    · intro hz
      obtain ⟨q, hq⟩ := mem_iUnion.mp hz
      exact (ball_subset_ball (by exact_mod_cast q.property.2.le)) hq
  have hmass : (∫⁻ z in unitDisc, (‖A z‖₊ : ℝ≥0∞) ^ 2) ≤ ENNReal.ofReal C := by
    rw [hUnion, setLIntegral_iUnion_of_directed _ hdir]
    apply iSup_le
    intro q
    have hq0 : (0 : ℝ) < q.val := by exact_mod_cast q.property.1
    have hq1 : (q.val : ℝ) < 1 := by exact_mod_cast q.property.2
    have hsub : closedBall (0 : ℂ) (q.val : ℝ) ⊆ unitDisc := by
      intro z hz
      exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hq1)
    have hi : IntegrableOn (fun z => ‖A z‖ ^ 2) (U q) :=
      (((hA.continuousOn.norm.pow 2).mono hsub).integrableOn_compact
        (isCompact_closedBall (0 : ℂ) (q.val : ℝ))).mono_set ball_subset_closedBall
    have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z => sq_nonneg ‖A z‖)
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (hC (q.val : ℝ) hq0 hq1)
  exact ⟨hA, ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hmass.trans_lt ENNReal.ofReal_lt_top).ne⟩

/-- The valid analytic implication used in Lemma 1.11, with its needed annulus premise. -/
theorem a21_of_Psi_A2_of_boundary_small {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A unitDisc)
    (hS : PsiOp A ∈ A2fun unitDisc)
    (hsmall : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ z ∈ unitDisc,
      s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖A z‖ ≤ 1 / 2) : A ∈ A21fun unitDisc :=
  a21_of_uniform_disk_mass hA (lemma_1_11_disk_mass_bound hA hS hsmall)

/-- Univalence supplies the actual nonvanishing derivative needed for holomorphy
of the pre-Schwarzian; no boundary regularity is inferred. -/
theorem preSchwarzian_differentiableOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hi : InjOn f D) :
    DifferentiableOn ℂ (preSchwarzian f) D :=
  ((hf.deriv hD).deriv hD).div (hf.deriv hD) (fun z hz => deriv_ne_zero_of_injOn hD hf hi hz)

/-- A valid disk version of Lemma 1.11 with the missing boundary estimate explicit.
The original unqualified declaration remains unchanged because it is false. -/
theorem lemma_1_11_disc_of_boundary_small {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hS : schwarzianHol f ∈ A2fun unitDisc)
    (hsmall : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ z ∈ unitDisc,
      s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖preSchwarzian f z‖ ≤ 1 / 2) :
    preSchwarzian f ∈ A21fun unitDisc := by
  apply a21_of_Psi_A2_of_boundary_small
    (preSchwarzian_differentiableOn (show IsOpen unitDisc from isOpen_ball) hf hi) _ hsmall
  exact hS

/-- Boundary decay supplies exactly the annulus smallness used in (1.1). -/
theorem boundary_small_of_weighted_tendsto_zero {A : ℂ → ℂ}
    (hlim : Tendsto (fun z => (1 - ‖z‖ ^ 2) * A z)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0)) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ z ∈ unitDisc,
      s < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖A z‖ ≤ 1 / 2 := by
  have he := (Metric.tendsto_nhds.mp hlim) (1 / 2) (by norm_num)
  rw [Filter.eventually_inf_principal, Filter.eventually_comap] at he
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨max (1 / 2) (1 - δ / 2), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · apply max_lt (by norm_num)
    linarith
  · intro z hz hzs
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hnear : dist ‖z‖ (1 : ℝ) < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := (le_max_right (1 / 2 : ℝ) (1 - δ / 2)).trans_lt hzs
      linarith
    have hb := hball hnear z rfl hz
    have hnonneg : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    rw [dist_zero_right, norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hb
    exact hb.le

/-- With finite Psi mass, boundary decay is precisely the extra condition needed
by the disk argument in Lemma 1.11. -/
theorem a21_iff_boundary_decay_of_Psi_A2 {A : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A unitDisc) (hS : PsiOp A ∈ A2fun unitDisc) :
    A ∈ A21fun unitDisc ↔ Tendsto (fun z => (1 - ‖z‖ ^ 2) * A z)
      (comap (fun z : ℂ => ‖z‖) (𝓝 1) ⊓ 𝓟 unitDisc) (𝓝 0) := by
  constructor
  · exact fun h => cor_1_4 (Or.inl rfl) h
  · exact fun h => a21_of_Psi_A2_of_boundary_small hA hS (boundary_small_of_weighted_tendsto_zero h)

-- `lemma_1_11` moved to `Ch2/S1_T112Completed.lean` (2026-10-26), with its frozen statement.

-- Original thm_1_12 moved unchanged to Ch2/S1_Theorem112Completed.lean (2026-10-27).

-- `eq_1_3` moved to `Ch2/S1_Part5.lean` (2026-10-26).

/-- **Definition 1.13** (TT:3780–3784). The universal Liouville action `S₁ : T₀(1) → ℝ`:
`S₁([μ]) = ∬_𝔻 |𝒜(𝖿^μ)|² d²z + ∬_{𝔻*} |𝒜(𝗀_μ)|² d²z - 4π log |𝗀_μ'(∞)|`, computed on the representative
`Quotient.out`. -/
def liouvilleS1 (p : T1) : ℝ :=
  let μ : LinfStar := (Quotient.out p : LinfStarBall)
  (∫ z in unitDisc, ‖preSchwarzian (fsans μ) z‖ ^ 2) + (∫ z in unitDiscExterior, ‖preSchwarzian (gsans μ) z‖ ^ 2) -
    4 * π * Real.log ‖derivAtInfty (gsans μ)‖

-- Original liouvilleS1_wellDefined moved unchanged to Ch2/S1_LiouvilleCompleted.lean (2026-10-26).

-- `remark_1_14` moved to `Ch2/S1_Part4.lean` (2026-10-26).

end Ch2

end TakhtajanTeo
