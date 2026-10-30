import TakhtajanTeo.Ch1.HilbertChosenReflection
import TakhtajanTeo.Ch1.Eq22ReproducingFinal
import TakhtajanTeo.Ch1.Eq22BoundaryDomain
import TakhtajanTeo.Ch1.HilbertBersPreimage

/-!
# The Bers reproducing formula (2.2) for weighted-sup differentials

`bsub_reproducing`: for `q` holomorphic on `Ω = 𝖿^μ(𝔻)` with `|q| ≤ M λ_Ω²`, the formula (2.2) of
`eq22_reproducing` (proved there for `A₂(Ω)`) still holds. Route: with `F = 𝖿⁻¹`, the dilates
`q_r = r² (q ∘ 𝖿)(rF) 𝖿'(rF)² F'²` lie in `A₂(Ω)` and satisfy `|q_r| ≤ M λ_Ω²` (`λ_𝔻(rw) ≤ λ_𝔻(w)`); then `r → 1⁻`
by dominated convergence, with dominant `M C/|u - z|⁴` on `Ω*` (separation `eq22_open_separation`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

theorem bsub_r_mem {r : ℝ} (hr : |r| < 1) {w : ℂ} (hw : w ∈ unitDisc) : (r : ℂ) * w ∈ unitDisc := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  apply mem_ball_zero_iff.mpr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |r| * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hr.le (norm_nonneg w)
    _ < 1 := by linarith

theorem bsub_r_deriv_ne {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {s : ℂ}
    (hs : s ∈ unitDisc) : deriv f s ≠ 0 := by
  intro h0
  have h := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hs
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-- The weighted bound pulled back to the disc: `|q(𝖿 s)| |𝖿'(s)|² ≤ 4M/(1 - |s|²)²`. -/
theorem bsub_r_pull_bound {f q : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {M : ℝ}
    (hqb : ∀ v ∈ Ω, ‖q v‖ ≤ M * poincareDensity Ω v ^ 2) {s : ℂ} (hs : s ∈ unitDisc) :
    ‖q (f s)‖ * ‖deriv f s‖ ^ 2 ≤ 4 * M / (1 - ‖s‖ ^ 2) ^ 2 := by
  have hb := hqb (f s) (hf.mapsTo hs)
  rw [eq22_density_formula hf hs] at hb
  have hB : 0 < ‖deriv f s‖ := norm_pos_iff.mpr (bsub_r_deriv_ne hf hs)
  have hs1 : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
  have ha : 0 < 1 - ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
  have he : M * (2 / ((1 - ‖s‖ ^ 2) * ‖deriv f s‖)) ^ 2 * ‖deriv f s‖ ^ 2 = 4 * M / (1 - ‖s‖ ^ 2) ^ 2 := by
    field_simp
    ring
  rw [← he]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

/-- The dilates are holomorphic on `Ω`. -/
theorem bsub_r_diff {f q : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hq : DifferentiableOn ℂ q Ω) {r : ℝ} (hr : |r| < 1) :
    DifferentiableOn ℂ (fun v => (r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2) Ω := by
  have hg := hf.symm isOpen_ball
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hφ : DifferentiableOn ℂ (fun v => (r : ℂ) * Function.invFunOn f unitDisc v) Ω :=
    (differentiableOn_const _).mul hg.1
  have hφm : MapsTo (fun v => (r : ℂ) * Function.invFunOn f unitDisc v) Ω unitDisc :=
    fun v hv => bsub_r_mem hr (hg.mapsTo hv)
  have h1 : DifferentiableOn ℂ (fun v => q (f ((r : ℂ) * Function.invFunOn f unitDisc v))) Ω :=
    (hq.comp hf.1 hf.mapsTo).comp hφ hφm
  have h2 : DifferentiableOn ℂ (fun v => deriv f ((r : ℂ) * Function.invFunOn f unitDisc v)) Ω :=
    (hf.1.deriv isOpen_ball).comp hφ hφm
  have h3 : DifferentiableOn ℂ (deriv (Function.invFunOn f unitDisc)) Ω := hg.1.deriv hΩ
  exact (((differentiableOn_const _).mul h1).mul (h2.pow 2)).mul (h3.pow 2)

/-- The dilates keep the weighted bound `|q_r| ≤ M λ_Ω²`. -/
theorem bsub_r_bound {f q : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {M : ℝ} (hM : 0 ≤ M)
    (hqb : ∀ v ∈ Ω, ‖q v‖ ≤ M * poincareDensity Ω v ^ 2) {r : ℝ} (hr : |r| < 1) :
    ∀ v ∈ Ω, ‖(r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2‖ ≤
        M * poincareDensity Ω v ^ 2 := by
  intro v hv
  have hg := hf.symm isOpen_ball
  set w := Function.invFunOn f unitDisc v with hwdef
  have hw : w ∈ unitDisc := hg.mapsTo hv
  have hfw : f w = v := Function.invFunOn_eq (by rw [← hf.2.2] at hv; exact hv)
  have hd : deriv (Function.invFunOn f unitDisc) v * deriv f w = 1 := by
    have h := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hw
    rwa [hfw] at h
  have hs := bsub_r_mem hr hw
  have hP := bsub_r_pull_bound hf hqb hs
  rw [← hfw, eq22_density_formula hf hw, hfw]
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hb : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hsw : ‖(r : ℂ) * w‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |r| * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hr.le (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  have hab : 1 - ‖w‖ ^ 2 ≤ 1 - ‖(r : ℂ) * w‖ ^ 2 := by
    nlinarith [norm_nonneg ((r : ℂ) * w), norm_nonneg w]
  have hr2 : ‖(r : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg r]
  have hF : 0 < ‖deriv f w‖ := norm_pos_iff.mpr (bsub_r_deriv_ne hf hw)
  have hG : ‖deriv (Function.invFunOn f unitDisc) v‖ = ‖deriv f w‖⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← norm_mul, hd, norm_one])
  set G := ‖deriv (Function.invFunOn f unitDisc) v‖
  set a := 1 - ‖(r : ℂ) * w‖ ^ 2
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hstep1 : ‖(r : ℂ) ^ 2 * q (f ((r : ℂ) * w)) * deriv f ((r : ℂ) * w) ^ 2 *
      deriv (Function.invFunOn f unitDisc) v ^ 2‖ ≤ 4 * M / a ^ 2 * G ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    have hA : ‖q (f ((r : ℂ) * w))‖ * ‖deriv f ((r : ℂ) * w)‖ ^ 2 ≤ 4 * M / a ^ 2 := hP
    calc ‖(r : ℂ)‖ ^ 2 * ‖q (f ((r : ℂ) * w))‖ * ‖deriv f ((r : ℂ) * w)‖ ^ 2 * G ^ 2
        = ‖(r : ℂ)‖ ^ 2 * (‖q (f ((r : ℂ) * w))‖ * ‖deriv f ((r : ℂ) * w)‖ ^ 2) * G ^ 2 := by ring
      _ ≤ 1 * (4 * M / a ^ 2) * G ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul hr2 hA (by positivity) zero_le_one
      _ = 4 * M / a ^ 2 * G ^ 2 := by ring
  have hstep2 : 4 * M / a ^ 2 ≤ 4 * M / (1 - ‖w‖ ^ 2) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hb.le hab 2
  calc _ ≤ 4 * M / a ^ 2 * G ^ 2 := hstep1
    _ ≤ 4 * M / (1 - ‖w‖ ^ 2) ^ 2 * G ^ 2 := mul_le_mul_of_nonneg_right hstep2 (sq_nonneg _)
    _ = M * (2 / ((1 - ‖w‖ ^ 2) * ‖deriv f w‖)) ^ 2 := by
      rw [hG]
      field_simp
      ring

/-- The dilates lie in `A₂(Ω)`, in the form of the hypothesis of `eq22_reproducing`. -/
theorem bsub_r_A2 {f q : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {M : ℝ}
    (hqb : ∀ v ∈ Ω, ‖q v‖ ≤ M * poincareDensity Ω v ^ 2) {r : ℝ} (hr : |r| < 1) :
    ∫⁻ v in Ω, (‖(r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2‖₊ :
        ℝ≥0∞) ^ 2 * ENNReal.ofReal (poincareDensity Ω v ^ 2)⁻¹ < ∞ := by
  set Q : ℂ → ℂ := fun v => (r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2
    with hQ
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hconv : (∫⁻ v in Ω, (‖Q v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (poincareDensity Ω v ^ 2)⁻¹) =
      ∫⁻ v in Ω, ENNReal.ofReal (‖Q v‖ ^ 2 / (poincareDensity Ω v) ^ 2) := by
    apply setLIntegral_congr_fun hΩ.measurableSet
    intro v _
    dsimp only
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg ‖Q v‖),
      ENNReal.ofReal_pow (norm_nonneg (Q v)), ofReal_norm, enorm_eq_nnnorm]
  change (∫⁻ v in Ω, (‖Q v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (poincareDensity Ω v ^ 2)⁻¹) < ∞
  rw [hconv, eq22_pullback_mass hf]
  have hr1 : 0 < 1 - r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
  set K : ℝ := 4 * max M 0 / (1 - r ^ 2) ^ 2 with hK
  have hpt : ∀ w ∈ unitDisc, (‖Q (f w) * deriv f w ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹ ≤
      ENNReal.ofReal (K ^ 2) := by
    intro w hw
    have hleft : Function.invFunOn f unitDisc (f w) = w := hf.2.1.leftInvOn_invFunOn hw
    have hd : deriv (Function.invFunOn f unitDisc) (f w) * deriv f w = 1 :=
      t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hw
    have he : Q (f w) * deriv f w ^ 2 =
        (r : ℂ) ^ 2 * (q (f ((r : ℂ) * w)) * deriv f ((r : ℂ) * w) ^ 2) := by
      simp only [hQ, hleft]
      linear_combination ((r : ℂ) ^ 2 * q (f ((r : ℂ) * w)) * deriv f ((r : ℂ) * w) ^ 2) *
        (deriv (Function.invFunOn f unitDisc) (f w) * deriv f w + 1) * hd
    have hs := bsub_r_mem hr hw
    have hP := bsub_r_pull_bound hf hqb hs
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hs2 : ‖(r : ℂ) * w‖ ^ 2 ≤ r ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
      nlinarith [mul_le_mul_of_nonneg_left hw2 (sq_nonneg r)]
    have hnorm : ‖Q (f w) * deriv f w ^ 2‖ ≤ K := by
      rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_mul, norm_pow]
      have h1 : 4 * M / (1 - ‖(r : ℂ) * w‖ ^ 2) ^ 2 ≤ K := by
        have ha : 0 < 1 - ‖(r : ℂ) * w‖ ^ 2 := by linarith
        calc 4 * M / (1 - ‖(r : ℂ) * w‖ ^ 2) ^ 2 ≤ 4 * max M 0 / (1 - ‖(r : ℂ) * w‖ ^ 2) ^ 2 :=
              div_le_div_of_nonneg_right (by linarith [le_max_left M 0]) (by positivity)
          _ ≤ K := div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_left₀ hr1.le (by linarith) 2)
      have hr21 : r ^ 2 ≤ 1 := by nlinarith [abs_nonneg r, sq_abs r]
      have hK0 : 0 ≤ K := by positivity
      calc r ^ 2 * (‖q (f ((r : ℂ) * w))‖ * ‖deriv f ((r : ℂ) * w)‖ ^ 2) ≤ 1 * K :=
            mul_le_mul hr21 (hP.trans h1) (by positivity) zero_le_one
        _ = K := one_mul K
    have hrho : (rho w)⁻¹ ≤ 1 := by
      unfold rho
      have hb : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      have hb1 : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
      rw [inv_div]
      rw [div_le_one (by norm_num)]
      nlinarith
    calc (‖Q (f w) * deriv f w ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹
        ≤ ENNReal.ofReal (K ^ 2) * 1 := by
          apply mul_le_mul'
          · rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
          · exact ENNReal.ofReal_le_one.mpr hrho
      _ = ENNReal.ofReal (K ^ 2) := mul_one _
  calc (∫⁻ w in unitDisc, (‖Q (f w) * deriv f w ^ 2‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹)
      ≤ ∫⁻ _ in unitDisc, ENNReal.ofReal (K ^ 2) :=
        setLIntegral_mono measurable_const (fun w hw => hpt w hw)
    _ = ENNReal.ofReal (K ^ 2) * volume unitDisc := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Pointwise convergence `q_r(v) → q(v)` as `r → 1⁻`. -/
theorem bsub_r_tendsto {f q : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hq : DifferentiableOn ℂ q Ω) {v : ℂ} (hv : v ∈ Ω) :
    Tendsto (fun r : ℝ => (r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2)
      (𝓝[<] 1) (𝓝 (q v)) := by
  have hg := hf.symm isOpen_ball
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  set w := Function.invFunOn f unitDisc v with hwdef
  have hw : w ∈ unitDisc := hg.mapsTo hv
  have hfw : f w = v := Function.invFunOn_eq (by rw [← hf.2.2] at hv; exact hv)
  have hd : deriv (Function.invFunOn f unitDisc) v * deriv f w = 1 := by
    have h := t1_deriv_invFunOn_mul (U := unitDisc) isOpen_ball hf hw
    rwa [hfw] at h
  have hφ : Continuous (fun r : ℝ => (r : ℂ) * w) := continuous_ofReal.mul continuous_const
  have hqf : ContinuousAt (fun s => q (f s)) w := by
    have h1 : ContinuousAt q (f w) := (hq.differentiableAt (hΩ.mem_nhds (hf.mapsTo hw))).continuousAt
    exact h1.comp (hf.1.differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
  have hdf : ContinuousAt (deriv f) w :=
    ((hf.1.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
  have h1 : ((1 : ℝ) : ℂ) * w = w := by simp
  have hqf' : ContinuousAt (fun r : ℝ => q (f ((r : ℂ) * w))) 1 := by
    apply ContinuousAt.comp (g := fun s => q (f s))
    · rw [h1]; exact hqf
    · exact hφ.continuousAt
  have hdf' : ContinuousAt (fun r : ℝ => deriv f ((r : ℂ) * w)) 1 := by
    apply ContinuousAt.comp (g := deriv f)
    · rw [h1]; exact hdf
    · exact hφ.continuousAt
  have hc : ContinuousAt (fun r : ℝ => (r : ℂ) ^ 2 * q (f ((r : ℂ) * w)) * deriv f ((r : ℂ) * w) ^ 2 *
      deriv (Function.invFunOn f unitDisc) v ^ 2) 1 :=
    (((continuous_ofReal.continuousAt.pow 2).mul hqf').mul (hdf'.pow 2)).mul continuousAt_const
  have hval : ((1 : ℝ) : ℂ) ^ 2 * q (f (((1 : ℝ) : ℂ) * w)) * deriv f (((1 : ℝ) : ℂ) * w) ^ 2 *
      deriv (Function.invFunOn f unitDisc) v ^ 2 = q v := by
    rw [h1, hfw]
    simp only [ofReal_one, one_pow, one_mul]
    linear_combination q v * (deriv f w * deriv (Function.invFunOn f unitDisc) v + 1) * hd
  have ht := hc.tendsto
  rw [hval] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-- `1/t⁴ ≤ ((1 + a)/a)⁴ (1 + t)^{-4}` for `t ≥ a > 0`. -/
theorem bsub_r_kernel_le {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    1 / t ^ 4 ≤ ((1 + a) / a) ^ 4 * (1 + t) ^ (-(4 : ℝ)) := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [Real.rpow_neg (by linarith), show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hq : (1 + t) / t ≤ (1 + a) / a := by
    rw [div_le_div_iff₀ ht ha]
    nlinarith
  have hq0 : 0 ≤ (1 + t) / t := by positivity
  have h4 := pow_le_pow_left₀ hq0 hq 4
  rw [div_pow] at h4
  have h1t : 0 < (1 + t) ^ 4 := by positivity
  calc 1 / t ^ 4 = (1 + t) ^ 4 / t ^ 4 * ((1 + t) ^ 4)⁻¹ := by field_simp
    _ ≤ ((1 + a) / a) ^ 4 * ((1 + t) ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right h4 (inv_nonneg.mpr h1t.le)

/-- The Bers reproducing formula (2.2) for weighted-sup (`A∞`) differentials, for a reflection whose reflected
coefficients are bounded as in `hc6_chosen_raw_coefficient`. -/
theorem bsub_reproducing {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {h : ℂ → ℂ}
    (hh : IsQCReflection (fsans μ '' unitDisc) (gsans μ '' unitDiscExterior) h) {C : ℝ}
    (hbd : ∀ (q : ℂ → ℂ) (M : ℝ), 0 ≤ M → DifferentiableOn ℂ q (fsans μ '' unitDisc) →
        (∀ v ∈ fsans μ '' unitDisc, ‖q v‖ ≤ M * poincareDensity (fsans μ '' unitDisc) v ^ 2) →
        MemLp (hbPre_reflected q h) ⊤ (volume.restrict (gsans μ '' unitDiscExterior)) ∧
          ∀ u ∈ gsans μ '' unitDiscExterior, ‖hbPre_reflected q h u‖ ≤ M * C / 2)
    {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (fsans μ '' unitDisc)) {M : ℝ} (hM : 0 ≤ M)
    (hqb : ∀ v ∈ fsans μ '' unitDisc, ‖q v‖ ≤ M * poincareDensity (fsans μ '' unitDisc) v ^ 2)
    {z : ℂ} (hz : z ∈ fsans μ '' unitDisc) :
    q z = -(3 / π) * ∫ u in gsans μ '' unitDiscExterior, q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4 := by
  have hf := S2C.s2c_conf_f hμ
  have hΩ := hf.isOpen isOpen_ball
  set Ω := fsans μ '' unitDisc with hΩdef
  set E := gsans μ '' unitDiscExterior with hEdef
  set f := fsans μ with hfdef
  obtain ⟨e, heΩ, heE⟩ := eq22_welding_common_chart hμ
  have hdis : Disjoint Ω E := by
    rw [hΩdef, hEdef, heΩ, heE]
    apply Set.disjoint_left.mpr
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have hev : v = u := e.injective he
    subst v
    have hnu := mem_ball_zero_iff.mp hu
    change 1 < ‖u‖ at hv
    linarith
  obtain ⟨a, ha, hsep⟩ := eq22_open_separation hΩ hdis hz
  have hEm : MeasurableSet E := hh.1.choose_spec.1.measurableSet
  let Q : ℝ → ℂ → ℂ := fun r v => (r : ℂ) ^ 2 * q (f ((r : ℂ) * Function.invFunOn f unitDisc v)) *
      deriv f ((r : ℂ) * Function.invFunOn f unitDisc v) ^ 2 * deriv (Function.invFunOn f unitDisc) v ^ 2
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), |r| < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with r hr
    exact abs_lt.mpr hr
  -- the reproducing formula for each dilate
  have hrep : ∀ᶠ r in 𝓝[<] (1 : ℝ), Q r z =
      -(3 / π) * ∫ u in E, Q r (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4 := by
    filter_upwards [hev] with r hr
    exact eq22_reproducing hμ hh (bsub_r_diff hf hq hr) (bsub_r_A2 hf hqb hr) hz
  -- dominated convergence on `E`
  have hform : ∀ (p : ℂ → ℂ) (u : ℂ), p (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4 =
      2 * hbPre_reflected p h u * ((u - z) ^ 4)⁻¹ := by
    intro p u
    unfold hbPre_reflected
    ring
  have hinvm : AEStronglyMeasurable (fun u : ℂ => ((u - z) ^ 4)⁻¹) (volume.restrict E) :=
    (by fun_prop : Measurable (fun u : ℂ => ((u - z) ^ 4)⁻¹)).aestronglyMeasurable
  set K : ℝ := M * C * ((1 + a) / a) ^ 4 with hK
  have hint : Integrable (fun u : ℂ => K * (1 + ‖u - z‖) ^ (-(4 : ℝ))) (volume.restrict E) := by
    have h0 : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(4 : ℝ))) volume :=
      integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    exact ((h0.comp_sub_right z).const_mul K).restrict
  have hlim : Tendsto (fun r : ℝ => ∫ u in E, Q r (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4) (𝓝[<] 1)
      (𝓝 (∫ u in E, q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u => K * (1 + ‖u - z‖) ^ (-(4 : ℝ)))
    · filter_upwards [hev] with r hr
      obtain ⟨hL, -⟩ := hbd (Q r) M hM (bsub_r_diff hf hq hr) (bsub_r_bound hf hM hqb hr)
      have hm := (hL.aestronglyMeasurable.const_mul (2 : ℂ)).mul hinvm
      exact hm.congr (Eventually.of_forall (fun u => (hform (Q r) u).symm))
    · filter_upwards [hev] with r hr
      obtain ⟨-, hB⟩ := hbd (Q r) M hM (bsub_r_diff hf hq hr) (bsub_r_bound hf hM hqb hr)
      filter_upwards [ae_restrict_mem hEm] with u hu
      rw [hform (Q r) u, norm_mul, norm_mul, norm_inv, norm_pow]
      have hau : a ≤ ‖u - z‖ := hsep u hu
      have hpos : 0 < ‖u - z‖ := lt_of_lt_of_le ha hau
      have hk := bsub_r_kernel_le ha hau
      have hb := hB u hu
      have hMC : 0 ≤ M * C / 2 := le_trans (norm_nonneg _) hb
      calc ‖(2 : ℂ)‖ * ‖hbPre_reflected (Q r) h u‖ * (‖u - z‖ ^ 4)⁻¹
          ≤ 2 * (M * C / 2) * (1 / ‖u - z‖ ^ 4) := by
            rw [one_div]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Complex.norm_two]
            exact mul_le_mul_of_nonneg_left hb (by norm_num)
        _ ≤ 2 * (M * C / 2) * (((1 + a) / a) ^ 4 * (1 + ‖u - z‖) ^ (-(4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = K * (1 + ‖u - z‖) ^ (-(4 : ℝ)) := by rw [hK]; ring
    · exact hint
    · filter_upwards [ae_restrict_mem hEm] with u hu
      have ht := bsub_r_tendsto hf hq (hh.2.1 hu)
      exact ((ht.mul_const ((u - h u) ^ 2)).mul_const (dzbar h u)).div_const ((u - z) ^ 4)
  have hL : Tendsto (fun r : ℝ => Q r z) (𝓝[<] 1) (𝓝 (q z)) := bsub_r_tendsto hf hq hz
  have hR : Tendsto (fun r : ℝ => Q r z) (𝓝[<] 1)
      (𝓝 (-(3 / π) * ∫ u in E, q (h u) * (u - h u) ^ 2 * dzbar h u / (u - z) ^ 4)) :=
    (hlim.const_mul _).congr' (hrep.mono (fun r hr => hr.symm))
  exact tendsto_nhds_unique hL hR

end TakhtajanTeo
