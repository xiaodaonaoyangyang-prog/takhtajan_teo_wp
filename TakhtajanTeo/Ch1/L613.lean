import TakhtajanTeo.Ch1.WRegFoundation
import TakhtajanTeo.Ch1.S6_HyperbolicMetricVariation
import TakhtajanTeo.Ch1.HalfPlaneBergman

/-!
# Lemma 1.13 and Lemma 6.1 (Ahlfors): first variation of the hyperbolic metric (host `Ch1/L613.lean`, `l613_`)

Interface by 下属5 (2026-10-27). Statements of `lemma_1_13` (S1_5) and `lemma_6_1` (S6) are copied byte-identically
as `l613_lemma_1_13` / `l613_lemma_6_1`; the originals have no consumers and can be relocated here.

Route for Lemma 1.13 (TT gives no proof; TT derives Cor 1.15 *from* it, so Cor 1.15 cannot be used):
* `R(z,u) = 1/(u-z) + (z-1)/u - z/(u-1)` is the kernel of `F` (`eq_1_22`), and `conj Φ^{(j)}(z) = -(1/π)∫ ∂^jR(z̄,u) μ(u)`.
  The right side `RHS` is the second-order Taylor polynomial of `R(·,u)` at `z̄` evaluated at `z`, and the remainder is
  exactly `(z-z̄)³/((u-z)(u-z̄)³)`. Hence `F - RHS = -(1/π)(z-z̄)³ J(z)` with `J(z) = ∬_𝕌 μ/((u-z)(u-z̄)³)`
  (`l613_diff_integral`).
* Scaling gives `|J(z)| ≤ K/(Im z)²` (`l613_J_bound`), so `|F - RHS| ≤ C Im z`.
* `F` is `C²` on `𝕌` by W-REG (`wr_joint_contDiff_U`, `wr_isHarmonicU_contDiffOn`), so `∂̄F = μ` everywhere on `𝕌`
  (`varF_spec` a.e. plus continuity); `∂̄ RHS = (z-z̄)²/2 · conj Φ''' = μ` by `harmonicProjU_spec`. So `F - RHS` is
  holomorphic on `𝕌`.
* A holomorphic `H` on `𝕌` with `|H| ≤ C Im z` vanishes (Phragmén–Lindelöf for `H/(z+i)`, `l613_vanish`).
Route for Lemma 6.1 (TT:2560–2575): the ε-derivative of `ρ^{εμ}` at `0` (`l613_rho_first_variation`, using W-REG to
commute `∂_ε` and `∂_z`), then Lemma 1.13 and `dz RHS` make it vanish.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Lemma 1.13 -/

/-- Domination of `μ(u)/((u - z)(u - z̄)³)` on `𝕌` by a scaled copy of the majorant of `phiKernel_majorant_integrable`. -/
theorem l613_J_dom {μ : ℂ → ℂ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ u ∈ upperHalf, ‖μ u‖ ≤ M) {z : ℂ}
    (hz : z ∈ upperHalf) :
    ∃ B : ℂ → ℝ, Integrable B ∧ (∀ u, 0 ≤ B u) ∧
      ∫ u, B u = 8 * M * (∫ v : ℂ, ‖v‖⁻¹ * ‖v - 1‖⁻¹ * (1 + ‖v‖)⁻¹) / z.im ^ 2 ∧
      ∀ᵐ u ∂(volume.restrict upperHalf), ‖μ u / ((u - z) * (u - conj z) ^ 3)‖ ≤ B u := by
  have hy : 0 < z.im := hz
  set y := z.im with hydef
  have hU : MeasurableSet upperHalf := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  -- the scaled majorant
  set B : ℂ → ℝ := fun u => 8 * M / y ^ 4 *
    (‖(y⁻¹ : ℝ) • (u - z)‖⁻¹ * ‖(y⁻¹ : ℝ) • (u - z) - 1‖⁻¹ * (1 + ‖(y⁻¹ : ℝ) • (u - z)‖)⁻¹) with hBdef
  have hB0 : ∀ u, 0 ≤ B u := fun u => by positivity
  have hBint : Integrable B := by
    have h := ((phiKernel_majorant_integrable.comp_smul (inv_ne_zero hy.ne')).comp_sub_right z).const_mul
      (8 * M / y ^ 4)
    exact h
  have hBval : ∫ u, B u = 8 * M / y ^ 4 * (y ^ 2 * ∫ v : ℂ, ‖v‖⁻¹ * ‖v - 1‖⁻¹ * (1 + ‖v‖)⁻¹) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_sub_right_eq_self (fun v : ℂ => ‖(y⁻¹ : ℝ) • v‖⁻¹ * ‖(y⁻¹ : ℝ) • v - 1‖⁻¹ *
      (1 + ‖(y⁻¹ : ℝ) • v‖)⁻¹) z]
    rw [Measure.integral_comp_smul volume (fun v : ℂ => ‖v‖⁻¹ * ‖v - 1‖⁻¹ * (1 + ‖v‖)⁻¹) y⁻¹, Complex.finrank_real_complex,
      smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity)]
  -- the pointwise bound off the single point `u = z + y`
  have hpt : ∀ᵐ u ∂(volume.restrict upperHalf), ‖μ u / ((u - z) * (u - conj z) ^ 3)‖ ≤ B u := by
    have hne : ∀ᵐ u ∂(volume.restrict upperHalf), u ≠ z + y :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton _))
    filter_upwards [hne, ae_restrict_mem hU] with u hu1 hu
    have huim : 0 < u.im := hu
    set w : ℂ := (y⁻¹ : ℝ) • (u - z) with hwdef
    have hw' : w = ((y⁻¹ : ℝ) : ℂ) * (u - z) := by rw [hwdef, Complex.real_smul]
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e1 : u - z = (y : ℂ) * w := by
      rw [hw', ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ hyc, one_mul]
    have hzc : z - conj z = 2 * I * (y : ℂ) := by
      rw [Complex.sub_conj, hydef]; push_cast; ring
    have e2 : u - conj z = (y : ℂ) * (w + 2 * I) := by
      have : u - conj z = (u - z) + (z - conj z) := by ring
      rw [this, e1, hzc]; ring
    have hwim : w.im = (u.im - y) / y := by
      rw [hw']; simp [Complex.mul_im, hydef]; field_simp
    have hwim' : -1 < w.im := by
      rw [hwim, lt_div_iff₀ hy]; linarith
    have hc1 : 1 < ‖w + 2 * I‖ := by
      have h := Complex.abs_im_le_norm (w + 2 * I)
      have : (w + 2 * I).im = w.im + 2 := by simp
      rw [this] at h
      linarith [le_abs_self (w.im + 2)]
    have hca : ‖w‖ ≤ ‖w + 2 * I‖ := by
      have h1 : ‖w‖ ^ 2 ≤ ‖w + 2 * I‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        norm_num
        nlinarith
      nlinarith [norm_nonneg w, norm_nonneg (w + 2 * I)]
    by_cases hw0 : w = 0
    · have : u - z = 0 := by rw [e1, hw0, mul_zero]
      rw [this, zero_mul, div_zero, norm_zero]
      exact hB0 u
    have hw1 : w - 1 ≠ 0 := by
      intro h
      apply hu1
      have : w = 1 := sub_eq_zero.mp h
      have : u - z = (y : ℂ) := by rw [e1, this, mul_one]
      linear_combination this
    have ha : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hb : 0 < ‖w - 1‖ := norm_pos_iff.mpr hw1
    have hb' : ‖w - 1‖ ≤ 1 + ‖w‖ := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖w‖ := by rw [norm_one]; ring
    have hc0 : 0 < ‖w + 2 * I‖ := by linarith
    have hkey : ‖w - 1‖ * (1 + ‖w‖) ≤ 8 * ‖w + 2 * I‖ ^ 3 := by
      have h1 : 1 + ‖w‖ ≤ 2 * ‖w + 2 * I‖ := by linarith
      have h2 : ‖w - 1‖ ≤ 2 * ‖w + 2 * I‖ := by linarith
      have h3 : ‖w - 1‖ * (1 + ‖w‖) ≤ 4 * ‖w + 2 * I‖ ^ 2 := by nlinarith [norm_nonneg (w - 1)]
      have h4 : ‖w + 2 * I‖ ^ 2 ≤ ‖w + 2 * I‖ ^ 3 := by
        rw [pow_succ]; nlinarith
      nlinarith
    have hnorm : ‖μ u / ((u - z) * (u - conj z) ^ 3)‖ = ‖μ u‖ / (y ^ 4 * (‖w‖ * ‖w + 2 * I‖ ^ 3)) := by
      rw [e1, e2, norm_div, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy]
      congr 1
      ring
    rw [hnorm]
    show _ ≤ 8 * M / y ^ 4 * (‖w‖⁻¹ * ‖w - 1‖⁻¹ * (1 + ‖w‖)⁻¹)
    have hden : 0 < y ^ 4 * (‖w‖ * ‖w + 2 * I‖ ^ 3) := by positivity
    calc ‖μ u‖ / (y ^ 4 * (‖w‖ * ‖w + 2 * I‖ ^ 3)) ≤ M / (y ^ 4 * (‖w‖ * ‖w + 2 * I‖ ^ 3)) :=
          div_le_div_of_nonneg_right (hM u hu) hden.le
      _ ≤ 8 * M / y ^ 4 * (‖w‖⁻¹ * ‖w - 1‖⁻¹ * (1 + ‖w‖)⁻¹) := by
          rw [div_le_iff₀ hden]
          have e : 8 * M / y ^ 4 * (‖w‖⁻¹ * ‖w - 1‖⁻¹ * (1 + ‖w‖)⁻¹) * (y ^ 4 * (‖w‖ * ‖w + 2 * I‖ ^ 3)) =
              8 * M * ‖w + 2 * I‖ ^ 3 / (‖w - 1‖ * (1 + ‖w‖)) := by
            field_simp
          rw [e, le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hkey hM0]
  refine ⟨B, hBint, hB0, ?_, hpt⟩
  rw [hBval]
  field_simp

/-- `u ↦ μ(u)/(u(u-1)(u - z̄)ⁿ)` is integrable on `𝕌` for bounded measurable `μ`, `z ∈ 𝕌`, `n ≥ 1`. -/
theorem l613_nu_integrable {μ : ℂ → ℂ} {M : ℝ} (hm : AEStronglyMeasurable μ (volume.restrict upperHalf))
    (hM : ∀ u ∈ upperHalf, ‖μ u‖ ≤ M) {z : ℂ} (hz : z ∈ upperHalf) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun u => μ u / (u * (u - 1)) / (u - conj z) ^ n) (volume.restrict upperHalf) := by
  obtain ⟨δ, hδ, c, hc0, hc1, -, hlow⟩ := phiKernel_lower_bound hz
  refine Integrable.mono' ((phiKernel_majorant_integrable.const_mul (|M| / c ^ n)).integrableOn) ?_ ?_
  · exact ((hm.aemeasurable.div (by fun_prop)).div (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_upperHalf_aux] with u hu
    have hui : 0 < u.im := hu
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr fun h => by rw [h] at hui; simp at hui
    have hu1 : 0 < ‖u - 1‖ := norm_pos_iff.mpr fun h => by
      have : u = 1 := sub_eq_zero.mp h
      rw [this] at hui; simp at hui
    have hd := hlow z (mem_ball_self hδ) u hu
    have hnc : ‖u - conj z‖ = ‖conj u - z‖ := by
      rw [← Complex.norm_conj (u - conj z), map_sub, Complex.conj_conj]
    rw [← hnc] at hd
    have hdpos : 0 < c * (1 + ‖u‖) := by positivity
    have hpow : c ^ n * (1 + ‖u‖) ≤ ‖u - conj z‖ ^ n := by
      calc c ^ n * (1 + ‖u‖) ≤ c ^ n * (1 + ‖u‖) ^ n := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact le_self_pow₀ (by linarith [norm_nonneg u]) (by omega)
        _ = (c * (1 + ‖u‖)) ^ n := by rw [mul_pow]
        _ ≤ ‖u - conj z‖ ^ n := pow_le_pow_left₀ hdpos.le hd _
    have hcp : 0 < c ^ n * (1 + ‖u‖) := by positivity
    rw [norm_div, norm_div, norm_mul, norm_pow]
    calc ‖μ u‖ / (‖u‖ * ‖u - 1‖) / ‖u - conj z‖ ^ n
        ≤ |M| / (‖u‖ * ‖u - 1‖) / (c ^ n * (1 + ‖u‖)) := by
          apply div_le_div₀ (by positivity) _ hcp hpow
          exact div_le_div_of_nonneg_right ((hM u hu).trans (le_abs_self M)) (by positivity)
      _ = |M| / c ^ n * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by
          field_simp

/-- `F - RHS` as an integral: the Taylor remainder of the kernel `R(·, u)` at `z̄`. -/
theorem l613_diff_integral {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    varF μ z - ((z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
        (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z)) =
      -(1 / π) * (z - conj z) ^ 3 * ∫ u in upperHalf, μ u / ((u - z) * (u - conj z) ^ 3) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hcm : AEStronglyMeasurable (fun u => conj (μ u)) (volume.restrict upperHalf) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hm
  have hcb : ∀ᵐ u ∂(volume.restrict upperHalf), ‖conj (μ u)‖ ≤ M :=
    (ae_restrict_mem hU).mono fun u hu => by simpa using hM u hu
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  -- `G n w = ∫ conj μ / (ū(ū-1)(ū - w)ⁿ)` and its derivatives
  set G : ℕ → ℂ → ℂ := fun n w =>
    ∫ u in upperHalf, conj (μ u) / (conj u * (conj u - 1)) / (conj u - w) ^ n with hGdef
  have hGd : ∀ n, 1 ≤ n → ∀ w ∈ upperHalf, HasDerivAt (G n) ((n : ℂ) * G (n + 1) w) w :=
    fun n hn w hw => (phiKernel_hasDerivAt hcm hcb n hn hw).2
  set c : ℂ := -(1 / (π : ℂ)) with hcdef
  have hΦ : varPhi μ = fun w => c * (w * (w - 1) * G 1 w) := by
    funext w
    rw [(eq_1_22_of_bounded hM0 hμb w).2]
    have e : ∀ u, kernelRU w (conj u) * conj (μ u) =
        w * (w - 1) * (conj (μ u) / (conj u * (conj u - 1)) / (conj u - w) ^ 1) := fun u => by
      simp only [kernelRU, pow_one, div_eq_mul_inv, mul_inv]; ring
    simp_rw [e, integral_const_mul]
    rfl
  have hd1 : ∀ w ∈ upperHalf, HasDerivAt (varPhi μ) (c * ((2 * w - 1) * G 1 w + w * (w - 1) * G 2 w)) w := by
    intro w hw
    rw [hΦ]
    have h := ((((hasDerivAt_id w).mul ((hasDerivAt_id w).sub_const 1)).mul (hGd 1 le_rfl w hw)).const_mul c)
    convert h using 1
    · funext y; simp only [Pi.mul_apply, id]
    · simp only [Pi.mul_apply, id, Nat.cast_one]; ring
  have hD1 : ∀ w ∈ upperHalf, deriv (varPhi μ) w = c * ((2 * w - 1) * G 1 w + w * (w - 1) * G 2 w) :=
    fun w hw => (hd1 w hw).deriv
  have hd2 : HasDerivAt (fun w => c * ((2 * w - 1) * G 1 w + w * (w - 1) * G 2 w))
      (c * (2 * G 1 z + 2 * (2 * z - 1) * G 2 z + 2 * (z * (z - 1)) * G 3 z)) z := by
    have h1 := (((hasDerivAt_id z).const_mul 2).sub_const 1).mul (hGd 1 le_rfl z hz)
    have h2 := (((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const 1))).mul (hGd 2 (by norm_num) z hz)
    have h := (h1.add h2).const_mul c
    convert h using 1
    · funext y; simp only [Pi.mul_apply, Pi.add_apply, id]
    · simp only [Pi.mul_apply, Pi.add_apply, id]; push_cast; ring
  have hD2 : deriv (deriv (varPhi μ)) z = c * (2 * G 1 z + 2 * (2 * z - 1) * G 2 z + 2 * (z * (z - 1)) * G 3 z) := by
    have heq : deriv (varPhi μ) =ᶠ[𝓝 z] fun w => c * ((2 * w - 1) * G 1 w + w * (w - 1) * G 2 w) := by
      filter_upwards [hUo.mem_nhds hz] with w hw
      exact hD1 w hw
    rw [heq.deriv_eq]
    exact hd2.deriv
  have hD0 : varPhi μ z = c * (z * (z - 1) * G 1 z) := by rw [hΦ]
  -- conjugates
  have hGc : ∀ n, conj (G n z) = ∫ u in upperHalf, μ u / (u * (u - 1)) / (u - conj z) ^ n := by
    intro n
    rw [hGdef, ← integral_conj]
    congr 1
    funext u
    simp only [map_div₀, map_mul, map_sub, map_pow, map_one, Complex.conj_conj]
  have hcc : conj c = c := by
    rw [hcdef, map_neg, map_div₀, map_one, Complex.conj_ofReal]
  have hF : varF μ z = c * ∫ u in upperHalf, kernelRU z u * μ u := by
    rw [(eq_1_22_of_bounded hM0 hμb z).1]
  -- the integral identity
  obtain ⟨B, hBint, -, -, hpt⟩ := l613_J_dom hM0 hM hz
  have iJ : Integrable (fun u => μ u / ((u - z) * (u - conj z) ^ 3)) (volume.restrict upperHalf) :=
    hBint.integrableOn.mono' ((hm.aemeasurable.div (by fun_prop)).aestronglyMeasurable) hpt
  have i1 := l613_nu_integrable hm hM hz 1 le_rfl
  have i2 := l613_nu_integrable hm hM hz 2 (by norm_num)
  have i3 := l613_nu_integrable hm hM hz 3 (by norm_num)
  set a := conj z with hadef
  have hI : ∫ u in upperHalf, kernelRU z u * μ u =
      ((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) *
          (∫ u in upperHalf, μ u / (u * (u - 1)) / (u - a) ^ 1) +
        ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) *
          (∫ u in upperHalf, μ u / (u * (u - 1)) / (u - a) ^ 2) +
        (z - a) ^ 2 * (a * (a - 1)) * (∫ u in upperHalf, μ u / (u * (u - 1)) / (u - a) ^ 3) +
        (z - a) ^ 3 * ∫ u in upperHalf, μ u / ((u - z) * (u - a) ^ 3) := by
    have j1 : Integrable (fun u => ((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) * (μ u / (u * (u - 1)) / (u - a) ^ 1)) (volume.restrict upperHalf) := i1.const_mul _
    have j2 : Integrable (fun u => ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 2)) (volume.restrict upperHalf) := i2.const_mul _
    have j3 : Integrable (fun u => ((z - a) ^ 2 * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 3)) (volume.restrict upperHalf) := i3.const_mul _
    have j4 : Integrable (fun u => (z - a) ^ 3 * (μ u / ((u - z) * (u - a) ^ 3))) (volume.restrict upperHalf) := iJ.const_mul _
    have j12 : Integrable (fun u => ((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) * (μ u / (u * (u - 1)) / (u - a) ^ 1) + ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 2)) (volume.restrict upperHalf) := j1.add j2
    have j123 : Integrable (fun u => ((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) * (μ u / (u * (u - 1)) / (u - a) ^ 1) + ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 2) + ((z - a) ^ 2 * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 3))
        (volume.restrict upperHalf) := j12.add j3
    have hsplit : ∫ u in upperHalf, (((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) * (μ u / (u * (u - 1)) / (u - a) ^ 1) + ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 2) + ((z - a) ^ 2 * (a * (a - 1))) * (μ u / (u * (u - 1)) / (u - a) ^ 3) + (z - a) ^ 3 * (μ u / ((u - z) * (u - a) ^ 3))) =
        ((z - a) ^ 2 + (z - a) * (2 * a - 1) + a * (a - 1)) * (∫ u in upperHalf, (μ u / (u * (u - 1)) / (u - a) ^ 1)) + ((z - a) ^ 2 * (2 * a - 1) + (z - a) * (a * (a - 1))) * (∫ u in upperHalf, (μ u / (u * (u - 1)) / (u - a) ^ 2)) +
          ((z - a) ^ 2 * (a * (a - 1))) * (∫ u in upperHalf, (μ u / (u * (u - 1)) / (u - a) ^ 3)) + (z - a) ^ 3 * ∫ u in upperHalf, (μ u / ((u - z) * (u - a) ^ 3)) := by
      rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
    rw [← hsplit]
    refine integral_congr_ae ?_
    have hne : ∀ᵐ u ∂(volume.restrict upperHalf), u ≠ z :=
      ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton _))
    filter_upwards [hne, ae_restrict_mem hU] with u huz hu
    have hui : 0 < u.im := hu
    have hzi : 0 < z.im := hz
    have hu0 : u ≠ 0 := fun h => by rw [h] at hui; simp at hui
    have hu1 : u - 1 ≠ 0 := fun h => by
      have : u = 1 := sub_eq_zero.mp h
      rw [this] at hui; simp at hui
    have hua : u - a ≠ 0 := fun h => by
      have := congrArg Complex.im h
      simp [hadef] at this
      linarith
    have huz' : u - z ≠ 0 := sub_ne_zero.mpr huz
    simp only [Pi.add_apply, kernelRU]
    field_simp
    ring
  rw [hF, hD2, hD1 z hz, hD0, map_mul, map_mul, map_mul, hcc]
  simp only [map_add, map_mul, map_sub, map_ofNat, map_one, hGc, ← hadef]
  rw [hI]
  simp only [hcdef]
  ring

/-- Scale-invariant bound `|∬_𝕌 μ/((u - z)(u - z̄)³)| ≤ K/(Im z)²`. -/
theorem l613_J_bound {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ∃ K : ℝ, ∀ z ∈ upperHalf, ‖∫ u in upperHalf, μ u / ((u - z) * (u - conj z) ^ 3)‖ ≤ K / z.im ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  refine ⟨8 * M * (∫ v : ℂ, ‖v‖⁻¹ * ‖v - 1‖⁻¹ * (1 + ‖v‖)⁻¹), fun z hz => ?_⟩
  obtain ⟨B, hBint, hB0, hBval, hpt⟩ := l613_J_dom hM0 hM hz
  calc ‖∫ u in upperHalf, μ u / ((u - z) * (u - conj z) ^ 3)‖ ≤ ∫ u in upperHalf, B u :=
        norm_integral_le_of_norm_le hBint.integrableOn hpt
    _ ≤ ∫ u, B u := setIntegral_le_integral hBint (Eventually.of_forall hB0)
    _ = _ := hBval

/-- `F[μ]` is `C²` on `𝕌` (W-REG) and `∂̄F = μ` at every point of `𝕌`. -/
theorem l613_varF_contDiff {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ContDiffOn ℝ 2 (varF μ) upperHalf ∧ ∀ z ∈ upperHalf, dzbar (varF μ) z = μ z := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  -- W-REG: `(ε, z) ↦ w_{εμ}(z)` is `C³`
  have hE2 := wr_joint_contDiff_U hM0 hμb (wr_isHarmonicU_contDiffOn hμ)
  have hSo : IsOpen ({ε : ℂ | ‖ε‖ * M < 1} ×ˢ upperHalf) :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod hUo
  have hmem : ∀ z ∈ upperHalf, ((0 : ℂ), z) ∈ {ε : ℂ | ‖ε‖ * M < 1} ×ˢ upperHalf :=
    fun z hz => ⟨by simp, hz⟩
  have hWd : ∀ z ∈ upperHalf, DifferentiableAt ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z) :=
    fun z hz => (hE2.differentiableOn (by norm_num)).differentiableAt (hSo.mem_nhds (hmem z hz))
  have hchain : ∀ z ∈ upperHalf, ∀ v : ℂ, fderiv ℝ (fun e : ℂ => wU (fun u => e * μ u) z) 0 v =
      fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z) (v, 0) := by
    intro z hz v
    have hi : HasFDerivAt (fun e : ℂ => (e, z)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) (0 : ℂ) :=
      (hasFDerivAt_id (0 : ℂ)).prodMk (hasFDerivAt_const z (0 : ℂ))
    have hc := (hWd z hz).hasFDerivAt.comp (0 : ℂ) hi
    rw [show (fun e : ℂ => wU (fun u => e * μ u) z) =
      (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) ∘ (fun e : ℂ => (e, z)) from rfl, hc.fderiv]
    simp
  have hvarF : ∀ z ∈ upperHalf, varF μ z =
      (fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z) (1, 0) -
        I * fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z) (I, 0)) / 2 := by
    intro z hz
    show (fderiv ℝ (fun e : ℂ => wU (fun u => e * μ u) z) 0 1 -
      I * fderiv ℝ (fun e : ℂ => wU (fun u => e * μ u) z) 0 I) / 2 = _
    rw [hchain z hz 1, hchain z hz I]
  have hDc : ContDiffOn ℝ 2 (fun z : ℂ => fderiv ℝ (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z))
      upperHalf := by
    have h := (hE2.fderiv_of_isOpen hSo (by norm_num : ((2 : ℕ) : WithTop ℕ∞) + 1 ≤ 3))
    exact h.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => hmem z hz)
  have hFc : ContDiffOn ℝ 2 (varF μ) upperHalf :=
    (((hDc.clm_apply contDiffOn_const).sub (contDiffOn_const.mul (hDc.clm_apply contDiffOn_const))).div_const
      2).congr fun z hz => hvarF z hz
  refine ⟨hFc, ?_⟩
  -- `∂̄F = μ` a.e. on `𝕌` (the argument of `varF_spec`, which does not use `k < 1`)
  have hκ := vf_zero_extension_coeff hM0 hμb
  have hd : ∀ n : ℕ, ∀ᵐ z : ℂ, DifferentiableAt ℝ
      (cauchyT ((closedBall (0 : ℂ) ((n : ℝ) + 1)).indicator (upperHalf.indicator μ))) z := by
    intro n
    apply mp_cauchy_differentiable_ae (vf_cutoff_memLp_four hκ ((n : ℝ) + 1))
    apply isBounded_closedBall.subset
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem h (upperHalf.indicator μ))
  have hbar := vf_varF_dzbar_of_cutoff_differentiability hM0 hμb hd
  have hae : dzbar (varF μ) =ᵐ[volume.restrict upperHalf] μ := by
    filter_upwards [ae_restrict_of_ae hbar, self_mem_ae_restrict hU] with z hz hzU
    simpa only [indicator_of_mem hzU] using hz
  -- both sides are continuous on `𝕌`
  have hf' := hFc.continuousOn_fderiv_of_isOpen hUo (by norm_num)
  have hdzc : ContinuousOn (dzbar (varF μ)) upperHalf :=
    ((hf'.clm_apply continuousOn_const).add (continuousOn_const.mul (hf'.clm_apply continuousOn_const))).div_const 2
  exact fun z hz => Measure.eqOn_open_of_ae_eq hae hUo hdzc (harmonicU_continuousOn hμ) hz

theorem l613_dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w + g w) z = dz f z + dz g z ∧ dzbar (fun w => f w + g w) z = dzbar f z + dzbar g z := by
  constructor <;> simp only [dz, dzbar, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply] <;> ring

theorem l613_dz_const (c : ℂ) (z : ℂ) : dz (fun _ : ℂ => c) z = 0 ∧ dzbar (fun _ : ℂ => c) z = 0 := by
  constructor <;> simp [dz, dzbar]

theorem l613_wirt_hol {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    dz f z = deriv f z ∧ dzbar f z = 0 :=
  ⟨dz_eq_deriv hf, (cauchyRiemann_iff.1 hf).2⟩

theorem l613_wirt_conjhol {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℝ (fun w => conj (f w)) z ∧ dz (fun w => conj (f w)) z = 0 ∧
      dzbar (fun w => conj (f w)) z = conj (deriv f z) := by
  have hr := hf.restrictScalars ℝ
  refine ⟨Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hr, ?_, ?_⟩
  · rw [dz_conj hr, (l613_wirt_hol hf).2, map_zero]
  · rw [dzbar_conj hr, (l613_wirt_hol hf).1]

theorem l613_wirt_p (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => w - conj w) z ∧ dz (fun w : ℂ => w - conj w) z = 1 ∧
      dzbar (fun w : ℂ => w - conj w) z = -1 := by
  have hid : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiableAt_id
  have hc : DifferentiableAt ℝ (fun w : ℂ => conj w) z := Complex.conjCLE.toContinuousLinearMap.differentiableAt
  have hcf : fderiv ℝ (fun w : ℂ => conj w) z = Complex.conjCLE.toContinuousLinearMap :=
    Complex.conjCLE.toContinuousLinearMap.fderiv
  have hif : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_id'
  refine ⟨hid.sub hc, ?_, ?_⟩ <;>
  · simp only [dz, dzbar, fderiv_fun_sub hid hc, hcf, hif, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]

theorem l613_wirt_u (z : ℂ) :
    DifferentiableAt ℝ (fun w : ℂ => (w - conj w) ^ 2 / 2) z ∧ dz (fun w : ℂ => (w - conj w) ^ 2 / 2) z = z - conj z ∧
      dzbar (fun w : ℂ => (w - conj w) ^ 2 / 2) z = -(z - conj z) := by
  obtain ⟨hpd, hp1, hp2⟩ := l613_wirt_p z
  have he : (fun w : ℂ => (w - conj w) ^ 2 / 2) =
      fun w => (fun _ : ℂ => (1 / 2 : ℂ)) w * ((w - conj w) * (w - conj w)) := by
    funext w; ring
  have hpp : DifferentiableAt ℝ (fun w : ℂ => (w - conj w) * (w - conj w)) z := hpd.mul hpd
  have hcd : DifferentiableAt ℝ (fun _ : ℂ => (1 / 2 : ℂ)) z := differentiableAt_const _
  rw [he]
  refine ⟨hcd.mul hpp, ?_, ?_⟩
  · rw [dz_mul hcd hpp, dz_mul hpd hpd, hp1, (l613_dz_const _ z).1]; ring
  · rw [dzbar_mul hcd hpp, dzbar_mul hpd hpd, hp2, (l613_dz_const _ z).2]; ring

/-- The right side of Lemma 1.13 is `C²` on `𝕌`, with `∂̄ RHS = μ` and `∂ RHS = (z - z̄) conj Φ'' + conj Φ'`. -/
theorem l613_rhs_wirtinger {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) :
    ContDiffOn ℝ 2 (fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
        (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z)) upperHalf ∧
      ∀ z ∈ upperHalf,
        dzbar (fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
          (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z)) z = μ z ∧
        dz (fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
          (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z)) z =
          (z - conj z) * conj (deriv (deriv (varPhi μ)) z) + conj (deriv (varPhi μ) z) := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hΦ : DifferentiableOn ℂ (varPhi μ) upperHalf := (varPhi_holomorphic_of_bounded hM0 hμb).1
  have hD1 : DifferentiableOn ℂ (deriv (varPhi μ)) upperHalf := hΦ.deriv hUo
  have hD2 : DifferentiableOn ℂ (deriv (deriv (varPhi μ))) upperHalf := hD1.deriv hUo
  refine ⟨?_, fun z hz => ?_⟩
  · have hp : ContDiff ℝ 2 (fun w : ℂ => w - conj w) :=
      contDiff_id.sub Complex.conjCLE.toContinuousLinearMap.contDiff
    have hc : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf → ContDiffOn ℝ 2 (fun w => conj (f w)) upperHalf :=
      fun f hf => Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn
        ((hf.contDiffOn hUo).restrict_scalars ℝ)
    exact ((((hp.contDiffOn.pow 2).div_const 2).mul (hc _ hD2)).add (hp.contDiffOn.mul (hc _ hD1))).add (hc _ hΦ)
  have hat : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf → DifferentiableAt ℂ f z :=
    fun f hf => hf.differentiableAt (hUo.mem_nhds hz)
  obtain ⟨hC0d, hC0z, hC0b⟩ := l613_wirt_conjhol (hat _ hΦ)
  obtain ⟨hC1d, hC1z, hC1b⟩ := l613_wirt_conjhol (hat _ hD1)
  obtain ⟨hC2d, hC2z, hC2b⟩ := l613_wirt_conjhol (hat _ hD2)
  obtain ⟨hpd, hp1, hp2⟩ := l613_wirt_p z
  obtain ⟨hud, hu1, hu2⟩ := l613_wirt_u z
  have hA : DifferentiableAt ℝ (fun w => (w - conj w) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) w)) z :=
    hud.mul hC2d
  have hB : DifferentiableAt ℝ (fun w => (w - conj w) * conj (deriv (varPhi μ) w)) z := hpd.mul hC1d
  have hAB : DifferentiableAt ℝ (fun w => (w - conj w) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) w) +
      (w - conj w) * conj (deriv (varPhi μ) w)) z := hA.add hB
  -- `Φ''' = φ`
  have h3 := (harmonicProjU_spec hμ).2 z hz
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h3
  refine ⟨?_, ?_⟩
  · rw [(l613_dz_add hAB hC0d).2, (l613_dz_add hA hB).2, dzbar_mul hud hC2d, dzbar_mul hpd hC1d, hC0b, hC1b, hC2b,
      hu2, hp2, h3, hμ.2.2 z hz]
    ring
  · rw [(l613_dz_add hAB hC0d).1, (l613_dz_add hA hB).1, dz_mul hud hC2d, dz_mul hpd hC1d, hC0z, hC1z, hC2z,
      hu1, hp1]
    ring

/-- A holomorphic function on `𝕌` with `|H(z)| ≤ C Im z` vanishes (Phragmén–Lindelöf). -/
theorem l613_vanish {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H upperHalf) {C : ℝ}
    (hC : ∀ z ∈ upperHalf, ‖H z‖ ≤ C * z.im) : ∀ z ∈ upperHalf, H z = 0 := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have him : ∀ v : ℂ, (I * v).im = v.re := fun v => by simp [Complex.mul_im]
  -- the rotated quotient `g(v) = H(iv)/(iv + i)` on the right half-plane, `0` elsewhere
  set g : ℂ → ℂ := fun v => if 0 < v.re then H (I * v) / (I * v + I) else 0 with hgdef
  have hden : ∀ v : ℂ, 0 < v.re → ‖I * v + I‖ ≥ v.re + 1 := by
    intro v hv
    have e : I * v + I = I * (v + 1) := by ring
    rw [e, norm_mul, Complex.norm_I, one_mul]
    calc v.re + 1 = (v + 1).re := by simp
      _ ≤ |(v + 1).re| := le_abs_self _
      _ ≤ ‖v + 1‖ := Complex.abs_re_le_norm _
  have hgb : ∀ v : ℂ, ‖g v‖ ≤ |C| * |v.re| ∧ ‖g v‖ ≤ |C| := by
    intro v
    by_cases hv : 0 < v.re
    · have hz : I * v ∈ upperHalf := by show 0 < (I * v).im; rw [him]; exact hv
      have h1 := hC _ hz
      rw [him] at h1
      have hd := hden v hv
      have hdpos : 0 < ‖I * v + I‖ := by linarith
      have hH : ‖H (I * v)‖ ≤ |C| * v.re := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hv.le)
      simp only [hgdef, if_pos hv, norm_div]
      refine ⟨?_, ?_⟩
      · rw [abs_of_pos hv, div_le_iff₀ hdpos]
        have : |C| * v.re ≤ |C| * v.re * ‖I * v + I‖ :=
          le_mul_of_one_le_right (mul_nonneg (abs_nonneg C) hv.le) (by linarith)
        linarith
      · rw [div_le_iff₀ hdpos]
        have : |C| * v.re ≤ |C| * ‖I * v + I‖ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
        linarith
    · simp only [hgdef, if_neg hv, norm_zero]
      exact ⟨by positivity, abs_nonneg _⟩
  have hgd : DifferentiableOn ℂ g {v : ℂ | 0 < v.re} := by
    intro v hv
    have hz : I * v ∈ upperHalf := by show 0 < (I * v).im; rw [him]; exact hv
    have hne : I * v + I ≠ 0 := by
      intro h; have hv' : 0 < v.re := hv; have := hden v hv; rw [h, norm_zero] at this; linarith
    have hHd : DifferentiableAt ℂ (fun v : ℂ => H (I * v)) v :=
      (hH.differentiableAt (hU.mem_nhds hz)).comp v ((differentiableAt_id.const_mul I))
    have hq : DifferentiableAt ℂ (fun v : ℂ => H (I * v) / (I * v + I)) v :=
      hHd.div ((differentiableAt_id.const_mul I).add_const I) hne
    refine (hq.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hv] with u hu
    exact if_pos hu
  have hgc : ContinuousOn g (closure {v : ℂ | 0 < v.re}) := by
    rw [Complex.closure_setOfPred_lt_re]
    intro v hv
    by_cases hv0 : 0 < v.re
    · exact (hgd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hv0)
        ).continuousAt.continuousWithinAt
    · have hre : v.re = 0 := le_antisymm (not_lt.mp hv0) hv
      have hg0 : g v = 0 := by simp only [hgdef, if_neg hv0]
      refine Metric.continuousWithinAt_iff.mpr fun ε hε => ⟨ε / (|C| + 1), by positivity, fun u _ hu => ?_⟩
      rw [hg0, dist_zero_right]
      have h1 := (hgb u).1
      have h2 : |u.re| ≤ dist u v := by
        rw [dist_eq_norm]
        calc |u.re| = |(u - v).re| := by simp [hre]
          _ ≤ ‖u - v‖ := Complex.abs_re_le_norm _
      have h3 : |C| * |u.re| ≤ |C| * (ε / (|C| + 1)) :=
        mul_le_mul_of_nonneg_left (h2.trans hu.le) (abs_nonneg _)
      have h4 : |C| * (ε / (|C| + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]
      linarith
  have hPL : ∀ v : ℂ, 0 ≤ v.re → ‖g v‖ ≤ 0 := by
    intro v hv
    refine PhragmenLindelof.right_half_plane_of_bounded_on_real ⟨hgd, hgc⟩ ?_ ?_ ?_ hv
    · refine ⟨1, by norm_num, 0, ?_⟩
      refine Asymptotics.IsBigO.of_bound |C| (Eventually.of_forall fun w => ?_)
      simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
      exact (hgb w).2
    · exact isBoundedUnder_of ⟨|C|, fun x => (hgb x).2⟩
    · intro x
      have : ¬ 0 < ((x : ℂ) * I).re := by simp
      simp only [hgdef, if_neg this, norm_zero, le_refl]
  intro z hz
  have hz' : 0 < z.im := hz
  have hw : 0 < (-I * z).re := by simpa [Complex.mul_re] using hz'
  have h := hPL (-I * z) hw.le
  have hgz : g (-I * z) = H z / (z + I) := by
    have e : I * (-I * z) = z := by ring_nf; rw [Complex.I_sq]; ring
    simp only [hgdef, if_pos hw, e]
  rw [hgz, norm_le_zero_iff, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exfalso
    have : (z + I).im = 0 := by rw [h]; simp
    simp at this
    linarith

/-- **Lemma 1.13** (Ahlfors [Ahl61]) (TT:1268–1274). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`F[μ](z) = ((z - z̄)²/2) \overline{Φ''(z)} + (z - z̄) \overline{Φ'(z)} + \overline{Φ(z)}`, `Φ = Φ[μ]`. -/
theorem l613_lemma_1_13 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    varF μ z = (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) + (z - conj z) * conj (deriv (varPhi μ) z) +
      conj (varPhi μ z) := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ℂ → ℂ, Rf = fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
      (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z) := ⟨_, rfl⟩
  have hRz : ∀ w, Rf w = (w - conj w) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) w) +
      (w - conj w) * conj (deriv (varPhi μ) w) + conj (varPhi μ w) := fun w => by rw [hRf]
  obtain ⟨hFc, hFb⟩ := l613_varF_contDiff hμ
  have hRc : ContDiffOn ℝ 2 Rf upperHalf := by rw [hRf]; exact (l613_rhs_wirtinger hμ).1
  have hRw : ∀ w ∈ upperHalf, dzbar Rf w = μ w := by
    rw [hRf]; exact fun w hw => ((l613_rhs_wirtinger hμ).2 w hw).1
  have hH : DifferentiableOn ℂ (fun z => varF μ z - Rf z) upperHalf := by
    intro w hw
    have hFd : DifferentiableAt ℝ (varF μ) w :=
      (hFc.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hw)
    have hRd : DifferentiableAt ℝ Rf w := (hRc.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hw)
    refine (cauchyRiemann_iff.mpr ⟨hFd.sub hRd, ?_⟩).differentiableWithinAt
    show dzbar (fun z => varF μ z - Rf z) w = 0
    rw [dzbar, fderiv_fun_sub hFd hRd, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
    have h1 := hFb w hw
    have h2 := hRw w hw
    rw [dzbar] at h1 h2
    linear_combination h1 - h2
  obtain ⟨K, hK⟩ := l613_J_bound hμ
  have hbd : ∀ w ∈ upperHalf, ‖varF μ w - Rf w‖ ≤ (8 * |K| / π) * w.im := by
    intro w hw
    have hy : 0 < w.im := hw
    have hn : ‖w - conj w‖ = 2 * w.im := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [hRz, l613_diff_integral hμ hw, norm_mul, norm_mul, norm_pow, hn]
    have hJ := hK w hw
    have hpi : ‖-(1 / (π : ℂ))‖ = 1 / π := by
      rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hpi]
    have hK' : K / w.im ^ 2 ≤ |K| / w.im ^ 2 := div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
    calc 1 / π * (2 * w.im) ^ 3 * ‖∫ u in upperHalf, μ u / ((u - w) * (u - conj w) ^ 3)‖
        ≤ 1 / π * (2 * w.im) ^ 3 * (|K| / w.im ^ 2) :=
          mul_le_mul_of_nonneg_left (hJ.trans hK') (by positivity)
      _ = (8 * |K| / π) * w.im := by field_simp; ring
  rw [← hRz]
  exact sub_eq_zero.mp (l613_vanish hH hbd z hz)

/-! ## Lemma 6.1 -/

theorem l613_dz_congr {u v : ℂ → ℂ} {w : ℂ} (h : u =ᶠ[𝓝 w] v) : dz u w = dz v w := by
  simp only [dz, h.fderiv_eq]

theorem l613_dz_inv {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => (f y)⁻¹) x ∧ dz (fun y => (f y)⁻¹) x = -(dz f x) / f x ^ 2 := by
  have hi := ((hasDerivAt_inv h0).hasFDerivAt).restrictScalars ℝ
  have hc := hi.comp x hf.hasFDerivAt
  rw [show (fun y => (f y)⁻¹) = (fun y : ℂ => y⁻¹) ∘ f from rfl]
  refine ⟨hc.differentiableAt, ?_⟩
  simp only [dz, hc.fderiv]
  simp
  field_simp
  ring

/-- Partial derivatives in the second variable through the full derivative. -/
theorem l613_fderiv_right {W : ℂ × ℂ → ℂ} {e w : ℂ} (hW : DifferentiableAt ℝ W (e, w)) (v : ℂ) :
    fderiv ℝ (fun w' => W (e, w')) w v = fderiv ℝ W (e, w) (0, v) := by
  have hi : HasFDerivAt (fun w' : ℂ => (e, w')) ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) w :=
    (hasFDerivAt_const e w).prodMk (hasFDerivAt_id w)
  have hc := hW.hasFDerivAt.comp w hi
  rw [show (fun w' => W (e, w')) = W ∘ (fun w' : ℂ => (e, w')) from rfl, hc.fderiv]
  simp

/-- Partial derivatives in the first variable through the full derivative. -/
theorem l613_fderiv_left {W : ℂ × ℂ → ℂ} {e w : ℂ} (hW : DifferentiableAt ℝ W (e, w)) (v : ℂ) :
    fderiv ℝ (fun e' => W (e', w)) e v = fderiv ℝ W (e, w) (v, 0) := by
  have hi : HasFDerivAt (fun e' : ℂ => (e', w)) ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) e :=
    (hasFDerivAt_id e).prodMk (hasFDerivAt_const w e)
  have hc := hW.hasFDerivAt.comp e hi
  rw [show (fun e' => W (e', w)) = W ∘ (fun e' : ℂ => (e', w)) from rfl, hc.fderiv]
  simp

/-- `dz`/`dzbar` of `x ↦ a·A x + b·B x`. -/
theorem l613_dz_lin {A B : ℂ → ℂ} {x : ℂ} (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (a b : ℂ) :
    DifferentiableAt ℝ (fun y => a * A y + b * B y) x ∧
      dz (fun y => a * A y + b * B y) x = a * dz A x + b * dz B x ∧
      dzbar (fun y => a * A y + b * B y) x = a * dzbar A x + b * dzbar B x := by
  have hca : DifferentiableAt ℝ (fun _ : ℂ => a) x := differentiableAt_const _
  have hcb : DifferentiableAt ℝ (fun _ : ℂ => b) x := differentiableAt_const _
  have h1 : DifferentiableAt ℝ (fun y => a * A y) x := hca.mul hA
  have h2 : DifferentiableAt ℝ (fun y => b * B y) x := hcb.mul hB
  refine ⟨h1.add h2, ?_, ?_⟩
  · rw [(l613_dz_add h1 h2).1, dz_mul hca hA, dz_mul hcb hB, (l613_dz_const a x).1, (l613_dz_const b x).1]
    ring
  · rw [(l613_dz_add h1 h2).2, dzbar_mul hca hA, dzbar_mul hcb hB, (l613_dz_const a x).2, (l613_dz_const b x).2]
    ring

/-- Mixed Wirtinger derivatives of a `C²` function of `(ε, z)` commute. -/
theorem l613_wirt_comm {W : ℂ × ℂ → ℂ} {e w : ℂ} (hW : ContDiffAt ℝ 2 W (e, w)) :
    DifferentiableAt ℝ (fun e' => dz (fun w' => W (e', w')) w) e ∧
      dz (fun e' => dz (fun w' => W (e', w')) w) e = dz (fun w' => dz (fun e' => W (e', w')) e) w ∧
      dzbar (fun e' => dz (fun w' => W (e', w')) w) e = dz (fun w' => dzbar (fun e' => W (e', w')) e) w := by
  have hd : ∀ᶠ q in 𝓝 (e, w), DifferentiableAt ℝ W q :=
    (hW.eventually (by norm_num)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ W) (e, w) :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hW.isSymmSndFDerivAt (by simp)
  have hl : ∀ᶠ e' in 𝓝 e, DifferentiableAt ℝ W (e', w) :=
    ((continuous_id.prodMk continuous_const).continuousAt (x := e)).eventually hd
  have hr : ∀ᶠ w' in 𝓝 w, DifferentiableAt ℝ W (e, w') :=
    ((continuous_const.prodMk continuous_id).continuousAt (x := w)).eventually hd
  -- derivatives of `fderiv W (γ x) u` along the coordinate embeddings
  have hL : ∀ u : ℂ × ℂ, DifferentiableAt ℝ (fun e' : ℂ => fderiv ℝ W (e', w) u) e ∧
      ∀ v, fderiv ℝ (fun e' : ℂ => fderiv ℝ W (e', w) u) e v = fderiv ℝ (fderiv ℝ W) (e, w) (v, 0) u := by
    intro u
    have hi : HasFDerivAt (fun e' : ℂ => (e', w)) ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ)) e :=
      (hasFDerivAt_id e).prodMk (hasFDerivAt_const w e)
    have h0 := (hD.hasFDerivAt.comp e hi).clm_apply (hasFDerivAt_const u e)
    have h : HasFDerivAt (fun e' : ℂ => fderiv ℝ W (e', w) u) _ e := h0
    refine ⟨h.differentiableAt, fun v => ?_⟩
    rw [h.fderiv]
    simp
  have hR : ∀ u : ℂ × ℂ, DifferentiableAt ℝ (fun w' : ℂ => fderiv ℝ W (e, w') u) w ∧
      ∀ v, fderiv ℝ (fun w' : ℂ => fderiv ℝ W (e, w') u) w v = fderiv ℝ (fderiv ℝ W) (e, w) (0, v) u := by
    intro u
    have hi : HasFDerivAt (fun w' : ℂ => (e, w')) ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) w :=
      (hasFDerivAt_const e w).prodMk (hasFDerivAt_id w)
    have h0 := (hD.hasFDerivAt.comp w hi).clm_apply (hasFDerivAt_const u w)
    have h : HasFDerivAt (fun w' : ℂ => fderiv ℝ W (e, w') u) _ w := h0
    refine ⟨h.differentiableAt, fun v => ?_⟩
    rw [h.fderiv]
    simp
  -- the germs as linear combinations
  have hgl : (fun e' => dz (fun w' => W (e', w')) w) =ᶠ[𝓝 e]
      fun e' => (1 / 2 : ℂ) * fderiv ℝ W (e', w) (0, 1) + (-(I / 2)) * fderiv ℝ W (e', w) (0, I) := by
    filter_upwards [hl] with e' he'
    simp only [dz, l613_fderiv_right he']
    ring
  have hgr1 : (fun w' => dz (fun e' => W (e', w')) e) =ᶠ[𝓝 w]
      fun w' => (1 / 2 : ℂ) * fderiv ℝ W (e, w') (1, 0) + (-(I / 2)) * fderiv ℝ W (e, w') (I, 0) := by
    filter_upwards [hr] with w' hw'
    simp only [dz, l613_fderiv_left hw']
    ring
  have hgr2 : (fun w' => dzbar (fun e' => W (e', w')) e) =ᶠ[𝓝 w]
      fun w' => (1 / 2 : ℂ) * fderiv ℝ W (e, w') (1, 0) + (I / 2) * fderiv ℝ W (e, w') (I, 0) := by
    filter_upwards [hr] with w' hw'
    simp only [dzbar, l613_fderiv_left hw']
    ring
  obtain ⟨hL1, hL1'⟩ := hL (0, 1)
  obtain ⟨hLI, hLI'⟩ := hL (0, I)
  obtain ⟨hR1, hR1'⟩ := hR (1, 0)
  obtain ⟨hRI, hRI'⟩ := hR (I, 0)
  obtain ⟨hgd, hgz, hgzb⟩ := l613_dz_lin hL1 hLI (1 / 2 : ℂ) (-(I / 2))
  obtain ⟨-, hr1z, -⟩ := l613_dz_lin hR1 hRI (1 / 2 : ℂ) (-(I / 2))
  obtain ⟨-, hr2z, -⟩ := l613_dz_lin hR1 hRI (1 / 2 : ℂ) (I / 2)
  have hdzL : ∀ u : ℂ × ℂ, dz (fun e' : ℂ => fderiv ℝ W (e', w) u) e =
      (fderiv ℝ (fderiv ℝ W) (e, w) (1, 0) u - I * fderiv ℝ (fderiv ℝ W) (e, w) (I, 0) u) / 2 ∧
      dzbar (fun e' : ℂ => fderiv ℝ W (e', w) u) e =
      (fderiv ℝ (fderiv ℝ W) (e, w) (1, 0) u + I * fderiv ℝ (fderiv ℝ W) (e, w) (I, 0) u) / 2 :=
    fun u => ⟨by simp only [dz, (hL u).2], by simp only [dzbar, (hL u).2]⟩
  have hdzR : ∀ u : ℂ × ℂ, dz (fun w' : ℂ => fderiv ℝ W (e, w') u) w =
      (fderiv ℝ (fderiv ℝ W) (e, w) (0, 1) u - I * fderiv ℝ (fderiv ℝ W) (e, w) (0, I) u) / 2 :=
    fun u => by simp only [dz, (hR u).2]
  have hs : ∀ a b : ℂ, fderiv ℝ (fderiv ℝ W) (e, w) (a, 0) (0, b) = fderiv ℝ (fderiv ℝ W) (e, w) (0, b) (a, 0) :=
    fun a b => hsymm _ _
  refine ⟨hgd.congr_of_eventuallyEq hgl, ?_, ?_⟩
  · rw [l613_dz_congr hgl, l613_dz_congr hgr1, hgz, hr1z, (hdzL _).1, (hdzL _).1,
      hdzR, hdzR, hs 1 1, hs 1 I, hs I 1, hs I I]
    ring
  · rw [dzbar_congr_of_eventuallyEq hgl, l613_dz_congr hgr2, hgzb, hr2z, (hdzL _).2, (hdzL _).2,
      hdzR, hdzR, hs 1 1, hs 1 I, hs I 1, hs I I]
    ring

/-- (TT:2563–2570) `L_μ ρ = -4 (F_z + \overline{Φ'})/(z - z̄)² + 8 (F - \overline{Φ})/(z - z̄)³`. -/
theorem l613_rho_first_variation {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => rhoVar μ ε z) 0 =
      -4 * (dz (varF μ) z + conj (deriv (varPhi μ) z)) / (z - conj z) ^ 2 +
        8 * (varF μ z - conj (varPhi μ z)) / (z - conj z) ^ 3 := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hE2 := wr_joint_contDiff_U hM0 hμb (wr_isHarmonicU_contDiffOn hμ)
  have hSo : IsOpen ({ε : ℂ | ‖ε‖ * M < 1} ×ˢ upperHalf) :=
    (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).prod hUo
  have hmem : ((0 : ℂ), z) ∈ {ε : ℂ | ‖ε‖ * M < 1} ×ˢ upperHalf := ⟨by simp, hz⟩
  have hWc : ContDiffAt ℝ 2 (fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (0, z) :=
    (hE2.contDiffAt (hSo.mem_nhds hmem)).of_le (by norm_num)
  have hWd := hWc.differentiableAt (by norm_num)
  obtain ⟨hgd, hgz, hgzb⟩ := l613_wirt_comm hWc
  -- `g ε = (w_{εμ})_z(z)` and `h ε = w_{εμ}(z)`
  have hhd : DifferentiableAt ℝ (fun e : ℂ => wU (fun u => e * μ u) z) 0 :=
    DifferentiableAt.comp (g := fun p : ℂ × ℂ => wU (fun u => p.1 * μ u) p.2) (f := fun e : ℂ => (e, z))
      (0 : ℂ) hWd (by fun_prop)
  have hw0 : wU (fun u => (0 : ℂ) * μ u) = id := by
    rw [show (fun u => (0 : ℂ) * μ u) = (0 : ℂ → ℂ) by funext u; simp]
    exact rhoVar_wU_zero
  have hg0 : dz (wU fun u => (0 : ℂ) * μ u) z = 1 := by rw [hw0]; exact rhoVar_dz_id z
  have hh0 : wU (fun u => (0 : ℂ) * μ u) z = z := by rw [hw0]; rfl
  have hPz : dz (varPhi μ) z = deriv (varPhi μ) z :=
    dz_eq_deriv ((varPhi_holomorphic_of_bounded hM0 hμb).1.differentiableAt (hUo.mem_nhds hz))
  have hgz' : dz (fun e : ℂ => dz (wU fun u => e * μ u) z) 0 = dz (varF μ) z := hgz
  have hgzb' : dzbar (fun e : ℂ => dz (wU fun u => e * μ u) z) 0 = deriv (varPhi μ) z := hgzb.trans hPz
  have hgd' : DifferentiableAt ℝ (fun e : ℂ => dz (wU fun u => e * μ u) z) 0 := hgd
  -- `ρ^{εμ}(z)` as a product
  have hrho : (fun ε => rhoVar μ ε z) = fun e =>
      (-4 * (dz (wU fun u => e * μ u) z * conj (dz (wU fun u => e * μ u) z))) *
        ((1 * wU (fun u => e * μ u) z + (-1) * conj (wU (fun u => e * μ u) z)) *
          (1 * wU (fun u => e * μ u) z + (-1) * conj (wU (fun u => e * μ u) z)))⁻¹ := by
    funext e
    show -4 * ((‖dz (wU fun u => e * μ u) z‖ ^ 2 : ℝ) : ℂ) /
      (wU (fun u => e * μ u) z - conj (wU (fun u => e * μ u) z)) ^ 2 = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, div_eq_mul_inv]
    ring
  rw [hrho]
  -- the pieces
  obtain ⟨hcgd, hcgz⟩ : DifferentiableAt ℝ (fun e : ℂ => conj (dz (wU fun u => e * μ u) z)) 0 ∧
      dz (fun e : ℂ => conj (dz (wU fun u => e * μ u) z)) 0 = conj (deriv (varPhi μ) z) :=
    ⟨Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp 0 hgd', by rw [dz_conj hgd', hgzb']⟩
  obtain ⟨hchd, hchz⟩ : DifferentiableAt ℝ (fun e : ℂ => conj (wU (fun u => e * μ u) z)) 0 ∧
      dz (fun e : ℂ => conj (wU (fun u => e * μ u) z)) 0 = conj (varPhi μ z) :=
    ⟨Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp 0 hhd, by rw [dz_conj hhd]; rfl⟩
  have hhz : dz (fun e : ℂ => wU (fun u => e * μ u) z) 0 = varF μ z := rfl
  have hc4 : DifferentiableAt ℝ (fun _ : ℂ => (-4 : ℂ)) 0 := differentiableAt_const _
  have hgg : DifferentiableAt ℝ (fun e : ℂ => dz (wU fun u => e * μ u) z * conj (dz (wU fun u => e * μ u) z)) 0 :=
    hgd'.mul hcgd
  have hN : DifferentiableAt ℝ (fun e : ℂ =>
      -4 * (dz (wU fun u => e * μ u) z * conj (dz (wU fun u => e * μ u) z))) 0 := hc4.mul hgg
  obtain ⟨hqd, hqz, -⟩ := l613_dz_lin hhd hchd 1 (-1)
  have hqq : DifferentiableAt ℝ (fun e : ℂ =>
      (1 * wU (fun u => e * μ u) z + (-1) * conj (wU (fun u => e * μ u) z)) *
        (1 * wU (fun u => e * μ u) z + (-1) * conj (wU (fun u => e * μ u) z))) 0 := hqd.mul hqd
  have hq0 : (1 * wU (fun u => (0 : ℂ) * μ u) z + (-1) * conj (wU (fun u => (0 : ℂ) * μ u) z)) = z - conj z := by
    rw [hh0]; ring
  have hne : z - conj z ≠ 0 := by
    rw [Complex.sub_conj]
    have hy : 0 < z.im := hz
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) I_ne_zero
  have hqq0 : (1 * wU (fun u => (0 : ℂ) * μ u) z + (-1) * conj (wU (fun u => (0 : ℂ) * μ u) z)) *
      (1 * wU (fun u => (0 : ℂ) * μ u) z + (-1) * conj (wU (fun u => (0 : ℂ) * μ u) z)) ≠ 0 := by
    rw [hq0]; exact mul_ne_zero hne hne
  obtain ⟨hId, hIz⟩ := l613_dz_inv hqq hqq0
  rw [dz_mul hN hId, hIz, dz_mul hqd hqd, hqz, dz_mul hc4 hgg, (l613_dz_const _ _).1, dz_mul hgd' hcgd, hcgz,
    hgz', hhz, hchz, hq0, hg0, map_one]
  field_simp
  ring

/-- **Lemma 6.1** (TT:2554–2557), Ahlfors [Ahl61]. For every `μ ∈ Ω^{-1,1}(𝕌)`, `L_μ ρ = ∂/∂ε|_{ε=0} ρ^{εμ} = 0` on
`𝕌`. -/
theorem l613_lemma_6_1 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => rhoVar μ ε z) 0 = 0 := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have heq : varF μ =ᶠ[𝓝 z] fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
      (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact l613_lemma_1_13 hμ hw
  have hdz : dz (varF μ) z = (z - conj z) * conj (deriv (deriv (varPhi μ)) z) + conj (deriv (varPhi μ) z) := by
    rw [← ((l613_rhs_wirtinger hμ).2 z hz).2]
    simp only [dz, heq.fderiv_eq]
  have hne : z - conj z ≠ 0 := by
    rw [Complex.sub_conj]
    have hy : 0 < z.im := hz
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) I_ne_zero
  rw [l613_rho_first_variation hμ hz, hdz, l613_lemma_1_13 hμ hz]
  field_simp
  ring

/-! ## Remark 1.14 and Corollary 1.15 -/

/-- **Remark 1.14** (TT:1276). `F[μ]_{zzz} = 0` on `𝕌` for `μ ∈ Ω^{-1,1}(𝕌)` (Wirtinger derivatives in `z`). -/
theorem l613_remark_1_14 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dz (dz (varF μ))) z = 0 := by
  obtain ⟨M, hM0, hM⟩ := harmonicU_bounded hμ
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hm : AEStronglyMeasurable μ (volume.restrict upperHalf) :=
    (harmonicU_continuousOn hμ).aestronglyMeasurable hU
  have hμb : IsBeltramiCoeff μ upperHalf M := ⟨hm, (ae_restrict_mem hU).mono fun u hu => hM u hu⟩
  have hΦ : DifferentiableOn ℂ (varPhi μ) upperHalf := (varPhi_holomorphic_of_bounded hM0 hμb).1
  have hD1 : DifferentiableOn ℂ (deriv (varPhi μ)) upperHalf := hΦ.deriv hUo
  have hD2 : DifferentiableOn ℂ (deriv (deriv (varPhi μ))) upperHalf := hD1.deriv hUo
  have hat : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f upperHalf → ∀ w ∈ upperHalf, DifferentiableAt ℂ f w :=
    fun f hf w hw => hf.differentiableAt (hUo.mem_nhds hw)
  -- step 1: `F_z = (z - z̄) conj Φ'' + conj Φ'` on `𝕌`
  have h1 : ∀ w ∈ upperHalf, dz (varF μ) w = (w - conj w) * conj (deriv (deriv (varPhi μ)) w) +
      conj (deriv (varPhi μ) w) := by
    intro w hw
    have heq : varF μ =ᶠ[𝓝 w] fun z => (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) +
        (z - conj z) * conj (deriv (varPhi μ) z) + conj (varPhi μ z) := by
      filter_upwards [hUo.mem_nhds hw] with v hv
      exact l613_lemma_1_13 hμ hv
    rw [l613_dz_congr heq]
    exact ((l613_rhs_wirtinger hμ).2 w hw).2
  -- step 2: `F_zz = conj Φ''` on `𝕌`
  have h2 : ∀ w ∈ upperHalf, dz (dz (varF μ)) w = conj (deriv (deriv (varPhi μ)) w) := by
    intro w hw
    have heq : dz (varF μ) =ᶠ[𝓝 w] fun v => (v - conj v) * conj (deriv (deriv (varPhi μ)) v) +
        conj (deriv (varPhi μ) v) := by
      filter_upwards [hUo.mem_nhds hw] with v hv
      exact h1 v hv
    rw [l613_dz_congr heq]
    obtain ⟨hpd, hp1, -⟩ := l613_wirt_p w
    obtain ⟨hC2d, hC2z, -⟩ := l613_wirt_conjhol (hat _ hD2 w hw)
    obtain ⟨hC1d, hC1z, -⟩ := l613_wirt_conjhol (hat _ hD1 w hw)
    have hA : DifferentiableAt ℝ (fun v => (v - conj v) * conj (deriv (deriv (varPhi μ)) v)) w := hpd.mul hC2d
    rw [(l613_dz_add hA hC1d).1, dz_mul hpd hC2d, hp1, hC2z, hC1z]
    ring
  -- step 3
  have heq : dz (dz (varF μ)) =ᶠ[𝓝 z] fun v => conj (deriv (deriv (varPhi μ)) v) := by
    filter_upwards [hUo.mem_nhds hz] with v hv
    exact h2 v hv
  rw [l613_dz_congr heq]
  exact (l613_wirt_conjhol (hat _ hD2 z hz)).2.1

/-- **Corollary 1.15** (TT:1278–1283). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`∬_𝕌 μ(u)/((u - z)(u - z̄)³) d²u = 0`. -/
theorem l613_cor_1_15 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∫ u in upperHalf, μ u / ((u - z) * (u - conj z) ^ 3) = 0 := by
  have h := l613_diff_integral hμ hz
  rw [← l613_lemma_1_13 hμ hz, sub_self] at h
  have hne : z - conj z ≠ 0 := by
    rw [Complex.sub_conj]
    have hy : 0 < z.im := hz
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) I_ne_zero
  have hc : -(1 / (π : ℂ)) * (z - conj z) ^ 3 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (pow_ne_zero 3 hne)
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- **Lemma 1.13** (Ahlfors [Ahl61]) (TT:1268–1274). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`F[μ](z) = ((z - z̄)²/2) \overline{Φ''(z)} + (z - z̄) \overline{Φ'(z)} + \overline{Φ(z)}`, `Φ = Φ[μ]`. -/
theorem lemma_1_13 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    varF μ z = (z - conj z) ^ 2 / 2 * conj (deriv (deriv (varPhi μ)) z) + (z - conj z) * conj (deriv (varPhi μ) z) +
      conj (varPhi μ z) :=
  l613_lemma_1_13 hμ hz

/-- **Remark 1.14** (TT:1276). `F[μ]_{zzz} = 0` on `𝕌` for `μ ∈ Ω^{-1,1}(𝕌)` (Wirtinger derivatives in `z`). -/
theorem remark_1_14 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (dz (dz (varF μ))) z = 0 :=
  l613_remark_1_14 hμ hz

/-- **Corollary 1.15** (TT:1278–1283). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`∬_𝕌 μ(u)/((u - z)(u - z̄)³) d²u = 0`. -/
theorem cor_1_15 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    ∫ u in upperHalf, μ u / ((u - z) * (u - conj z) ^ 3) = 0 :=
  l613_cor_1_15 hμ hz

/-- **Lemma 6.1** (TT:2554–2557), Ahlfors [Ahl61]. For every `μ ∈ Ω^{-1,1}(𝕌)`, `L_μ ρ = ∂/∂ε|_{ε=0} ρ^{εμ} = 0` on
`𝕌`. -/
theorem lemma_6_1 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    dz (fun ε => rhoVar μ ε z) 0 = 0 :=
  l613_lemma_6_1 hμ hz

end TakhtajanTeo
