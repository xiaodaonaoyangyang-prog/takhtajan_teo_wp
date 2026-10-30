import TakhtajanTeo.Ch1.S7Cor79
import TakhtajanTeo.Ch1.CuiPieces

/-!
# Program G, F3: `thm_7_11` and `cor_7_12` (下属1)

Proof of the sub-interface `F3_711_SUBINTERFACE` (9f337c5b): stubs BSUM, T2, H, T1 are proved
below and `s7g_thm_7_11`, `s7g_cor_7_12` are assembled as in the interface.

Notation: `bₙ = basisMu (n + 2)`; `S(z, w) = Σₙ bₙ(z) b̄ₙ(w) = (3/(4π)) (1 - |z|²)² (1 - |w|²)² / (1 - w z̄)⁴` on `𝔻*`.
By `cor_7_9`, `R_{μ n̄ n ν̄} = -T1ₙ - T2ₙ` with `T1ₙ = (bₙ ν̄, G(μ̄ bₙ))`, `T2ₙ = (ν̄ μ, G|bₙ|²)`.
* (BSUM) `Σₙ bₙ(z) b̄ₙ(w) = S(z, w)` (from `Σ (n³ - n) tⁿ = 6t²/(1 - t)⁴`, `t = 1/(z̄ w)`); `Σₙ |bₙ(z)|² = 3/(4π)`;
* (T2) `Σₙ T2ₙ = (3/(4π)) ⟨μ, ν⟩` (Tonelli, `G` linear and positive, `G 1 = 1` by `RK4`);
* (H) `∫_{𝔻*} G(z, w) μ(w) S(z, w) ρ(w) d²w = μ(z)/(3π)`: with the reproducing formula `wp_harmonic_projection_raw`
  for `μ(w)`, Fubini, and `∫_{𝔻*} G(z, w)(1 - |w|²)²/((1 - v w̄)⁴(1 - w z̄)⁴) d²w = 1/(9(1 - v z̄)⁴)` (`bKernel_closed_form`
  transported from `𝔻` by `w ↦ 1/w`, `G` inversion-invariant); then the reproducing formula again;
* (T1) `Σₙ T1ₙ = (1/(3π)) ⟨μ, ν⟩`: pointwise in `z`, `Σₙ bₙ(z) \overline{G(μ̄ bₙ)(z)} = μ(z)/(3π)` by (BSUM), (H)
  and dominated convergence in `w` (`|bₙ(z) b̄ₙ(w)| ≤ (|bₙ(z)|² + |bₙ(w)|²)/2`); then dominated convergence in `z`
  with the bound `ρ (|ν|² |bₙ|² + |G(μ̄ bₙ)|²)/2`, integrable since `Σₙ ‖G(μ̄ bₙ)‖² ≤ (3/(4π)) ‖μ‖²`
  (Tonelli and `s7rl_contraction`); no density argument is needed;
* `-(1/(3π) + 3/(4π)) = -13/(12π)` (ERRATA W1-05).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- `6 · C(n + 3, 3) = (n + 1)(n + 2)(n + 3)`. -/
theorem s7g_r_choose (n : ℕ) : (((n + 3).choose 3 : ℕ) : ℂ) = ((n : ℂ) + 1) * ((n : ℂ) + 2) * ((n : ℂ) + 3) / 6 := by
  have h : (n + 3).descFactorial 3 = Nat.factorial 3 * (n + 3).choose 3 := Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (n + 3).descFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
    have e1 : n + 3 - 2 = n + 1 := by omega
    have e2 : n + 3 - 1 = n + 2 := by omega
    rw [e1, e2, Nat.sub_zero]
    ring
  rw [h2] at h
  have h3 : ((n + 1) * (n + 2) * (n + 3) : ℕ) = 6 * (n + 3).choose 3 := by
    rw [h]
    rfl
  rw [eq_div_iff (by norm_num : (6 : ℂ) ≠ 0)]
  have h4 := congrArg (fun k : ℕ => (k : ℂ)) h3
  push_cast at h4
  linear_combination -h4

/-- STUB BSUM. The basis kernel on `𝔻*` and its diagonal. -/
theorem s7g_r_bsum {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) :
    HasSum (fun n : ℕ => basisMu (n + 2) z * conj (basisMu (n + 2) w))
        ((3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj z) ^ 4) ∧
      HasSum (fun n : ℕ => ‖basisMu (n + 2) z‖ ^ 2) (3 / (4 * π)) := by
  have hgen : ∀ {z w : ℂ}, z ∈ unitDiscExterior → w ∈ unitDiscExterior →
      HasSum (fun n : ℕ => basisMu (n + 2) z * conj (basisMu (n + 2) w))
        ((3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj z) ^ 4) := by
    intro z w hz hw
    have hz1 : 1 < ‖z‖ := hz
    have hw1 : 1 < ‖w‖ := hw
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have hw0 : w ≠ 0 := norm_pos_iff.1 (by linarith)
    have hp0 : conj z * w ≠ 0 := mul_ne_zero ((map_ne_zero _).2 hz0) hw0
    set t : ℂ := (conj z * w)⁻¹ with htdef
    have ht : ‖t‖ < 1 := by
      rw [htdef, norm_inv, norm_mul, Complex.norm_conj]
      exact inv_lt_one_of_one_lt₀ (by nlinarith)
    have ht1 : (1 : ℂ) - t ≠ 0 := by
      intro h
      have : ‖t‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
      linarith
    have h0 := (hasSum_choose_mul_geometric_of_norm_lt_one 3 ht).mul_left
      ((6 / (8 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * t ^ 4)
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hP1 : (1 : ℂ) - w * conj z ≠ 0 := by
      intro h
      apply ht1
      rw [htdef, show conj z * w = 1 by linear_combination -h, inv_one, sub_self]
    have key : t ^ 4 * (1 / (1 - t) ^ (3 + 1)) = 1 / (1 - w * conj z) ^ 4 := by
      have e : (1 : ℂ) - t = (conj z * w - 1) * t := by
        rw [htdef, sub_mul, mul_inv_cancel₀ hp0, one_mul]
      have ht0 : t ≠ 0 := by rw [htdef]; exact inv_ne_zero hp0
      have e2 : (1 : ℂ) - w * conj z = -(conj z * w - 1) := by ring
      rw [e, e2]
      have hq : conj z * w - 1 ≠ 0 := by
        intro h
        apply hP1
        rw [e2, h, neg_zero]
      field_simp
      ring
    have hval : (6 / (8 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * t ^ 4 * (1 / (1 - t) ^ (3 + 1)) =
        (3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj z) ^ 4 := by
      rw [mul_assoc _ (t ^ 4), key]
      field_simp
      ring
    rw [← hval]
    convert h0 using 1
    funext n
    -- the `n`-th term
    have hc : ((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ) ≥ 0 := by
      push_cast
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    have hs : (Real.sqrt ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π)) : ℂ) *
        (Real.sqrt ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π)) : ℂ) =
        ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π) : ℝ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hc (by positivity))]
    have hzp : conj z ^ (-((n + 2 : ℕ) : ℤ) - 2) * w ^ (-((n + 2 : ℕ) : ℤ) - 2) = t ^ 4 * t ^ n := by
      rw [← mul_zpow, show (-((n + 2 : ℕ) : ℤ) - 2) = -((n + 4 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, ← inv_pow, ← htdef, ← pow_add, add_comm]
    unfold basisMu
    simp only [map_mul, map_neg, Complex.conj_ofReal, map_zpow₀, Complex.conj_conj]
    rw [s7g_r_choose]
    generalize hS : (Real.sqrt ((((n + 2 : ℕ) : ℝ) ^ 3 - ((n + 2 : ℕ) : ℝ)) / (8 * π)) : ℂ) = S at hs ⊢
    push_cast at hs
    generalize hZ : conj z ^ (-((n + 2 : ℕ) : ℤ) - 2) = Z at hzp ⊢
    generalize hW : w ^ (-((n + 2 : ℕ) : ℤ) - 2) = W at hzp ⊢
    generalize hA : ((((1 - ‖z‖ ^ 2) ^ 2 : ℝ)) : ℂ) = A
    generalize hA' : ((((1 - ‖w‖ ^ 2) ^ 2 : ℝ)) : ℂ) = A'
    push_cast
    linear_combination (A * A' * (Z * W)) * hs +
      ((((n : ℂ) + 2) ^ 3 - ((n : ℂ) + 2)) / (8 * π) * A * A') * hzp
  refine ⟨hgen hz hw, ?_⟩
  have h := hgen hz hz
  have e1 : (fun n : ℕ => basisMu (n + 2) z * conj (basisMu (n + 2) z)) =
      fun n : ℕ => ((‖basisMu (n + 2) z‖ ^ 2 : ℝ) : ℂ) :=
    funext fun n => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hz1 : 1 < ‖z‖ := hz
  have hd : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith
  have e2 : (3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) / (1 - z * conj z) ^ 4 =
      ((3 / (4 * π) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hd' : (1 : ℂ) - ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast at hd' ⊢
    field_simp
  rw [e1, e2] at h
  exact Complex.hasSum_ofReal.1 h

/-- `|bₙ(w)|² ≤ 3/(4π)` on `𝔻*`. -/
theorem s7g_r_bd {w : ℂ} (hw : w ∈ unitDiscExterior) (n : ℕ) : ‖basisMu (n + 2) w‖ ^ 2 ≤ 3 / (4 * π) :=
  le_hasSum (s7g_r_bsum hw hw).2 n fun _ _ => sq_nonneg _

/-- `G|bₙ|²(z)` is real, nonnegative, and `Σₙ G|bₙ|²(z) = 3/(4π)` (dominated convergence and `RK4`). -/
theorem s7g_r_Gb {z : ℂ} (hz : z ∈ unitDiscExterior) :
    ∃ r : ℕ → ℝ, (∀ n, 0 ≤ r n) ∧
      (∀ n, resolventStar (fun w => conj (basisMu (n + 2) w) * basisMu (n + 2) w) z = r n) ∧
      HasSum r (3 / (4 * π)) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hK1 : Measurable (resolventKernel z) := measurable_resolventKernel.of_uncurry_left
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior :=
    fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have hnn := resolvent_mass_nonneg_ae (Or.inr rfl) hz
  refine ⟨fun n => ∫ w in unitDiscExterior, resolventKernel z w * ‖basisMu (n + 2) w‖ ^ 2 * rho w,
    fun n => ?_, fun n => ?_, ?_⟩
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hnn] with w hw
    have e : resolventKernel z w * ‖basisMu (n + 2) w‖ ^ 2 * rho w =
        resolventKernel z w * rho w * ‖basisMu (n + 2) w‖ ^ 2 := by ring
    rw [Pi.zero_apply, e]
    positivity
  · show resolventOp unitDiscExterior _ z = _
    unfold resolventOp
    dsimp only
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    rw [mul_comm (conj _), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict unitDiscExterior)
      (F := fun n w => resolventKernel z w * ‖basisMu (n + 2) w‖ ^ 2 * rho w)
      (f := fun w => resolventKernel z w * rho w * (3 / (4 * π)))
      (fun n w => |resolventKernel z w * rho w| * ‖basisMu (n + 2) w‖ ^ 2)
      (fun n => ((hK1.aestronglyMeasurable.mul ((s7pol_harmonic_measurable (hb n)).norm.pow 2)).mul
        hρm.aestronglyMeasurable))
      (fun n => Eventually.of_forall fun w => le_of_eq (by
        rw [Real.norm_eq_abs, show resolventKernel z w * ‖basisMu (n + 2) w‖ ^ 2 * rho w =
          resolventKernel z w * rho w * ‖basisMu (n + 2) w‖ ^ 2 by ring, abs_mul, abs_of_nonneg (sq_nonneg ‖basisMu (n + 2) w‖)]))
      (by
        filter_upwards [ae_restrict_mem hm] with w hw
        exact ((s7g_r_bsum hw hw).2.mul_left _).summable)
      (by
        refine ((resolvent_mass_integrable (Or.inr rfl) hz).abs.mul_const (3 / (4 * π))).congr ?_
        filter_upwards [ae_restrict_mem hm] with w hw
        exact (((s7g_r_bsum hw hw).2.mul_left _).tsum_eq).symm)
      (by
        filter_upwards [ae_restrict_mem hm] with w hw
        convert (s7g_r_bsum hw hw).2.mul_left (resolventKernel z w * rho w) using 1
        funext n
        ring)
    rw [integral_mul_const, RK4 (Or.inr rfl) hz, one_mul] at h
    exact h

/-- STUB T2. `Σₙ (ν̄ μ, G|bₙ|²) = (3/(4π)) ⟨μ, ν⟩`. -/
theorem s7g_r_T2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    HasSum (fun n : ℕ => l2Inner (fun z => conj (ν z) * μ z)
        (resolventStar fun z => conj (basisMu (n + 2) z) * basisMu (n + 2) z)) ((3 / (4 * π) : ℂ) * wpInner μ ν) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior :=
    fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have aμ := s7pol_harmonic_measurable hμ
  have aν := s7pol_harmonic_measurable hν
  set G : ℕ → ℂ → ℂ := fun n => resolventStar fun z => conj (basisMu (n + 2) z) * basisMu (n + 2) z with hG
  have aG : ∀ n, AEStronglyMeasurable (G n) (volume.restrict unitDiscExterior) := by
    intro n
    have ab := s7pol_harmonic_measurable (hb n)
    refine (resolventOp_continuousOn_of_bounded (Or.inr rfl)
      ((Complex.continuous_conj.comp_aestronglyMeasurable ab).mul ab) (C := 3 / (4 * π)) ?_).aestronglyMeasurable hm
    intro w hw
    show ‖conj (basisMu (n + 2) w) * basisMu (n + 2) w‖ ≤ 3 / (4 * π)
    rw [norm_mul, Complex.norm_conj, ← sq]
    exact s7g_r_bd hw n
  have e3 : conj (3 / (4 * π) : ℂ) = 3 / (4 * π) := by
    simp only [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict unitDiscExterior)
    (F := fun n z => conj (ν z) * μ z * conj (G n z) * rho z)
    (f := fun z => conj (ν z) * μ z * conj (3 / (4 * π) : ℂ) * rho z)
    (fun n z => ‖conj (ν z) * μ z * rho z‖ * ‖G n z‖)
    (fun n => (((Complex.continuous_conj.comp_aestronglyMeasurable aν).mul aμ).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (aG n))).mul
        (Complex.measurable_ofReal.comp hρm).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun z => le_of_eq (by
      simp only [norm_mul, Complex.norm_conj]
      ring))
    (by
      filter_upwards [ae_restrict_mem hm] with z hz
      obtain ⟨r, hr0, hrG, hr⟩ := s7g_r_Gb hz
      refine (hr.summable.mul_left ‖conj (ν z) * μ z * rho z‖).congr fun n => ?_
      show _ = ‖conj (ν z) * μ z * rho z‖ * ‖G n z‖
      rw [hG]
      dsimp only
      rw [hrG n, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)])
    (by
      refine ((wpInner_integrable hμ hν).norm.mul_const (3 / (4 * π))).congr ?_
      filter_upwards [ae_restrict_mem hm] with z hz
      obtain ⟨r, hr0, hrG, hr⟩ := s7g_r_Gb hz
      have e : (fun n => ‖conj (ν z) * μ z * rho z‖ * ‖G n z‖) = fun n => ‖conj (ν z) * μ z * rho z‖ * r n := by
        funext n
        rw [hG]
        dsimp only
        rw [hrG n, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
      show _ = ∑' n, ‖conj (ν z) * μ z * rho z‖ * ‖G n z‖
      rw [e, (hr.mul_left _).tsum_eq]
      simp only [norm_mul, Complex.norm_conj]
      ring)
    (by
      filter_upwards [ae_restrict_mem hm] with z hz
      obtain ⟨r, hr0, hrG, hr⟩ := s7g_r_Gb hz
      have hc : HasSum (fun n => G n z) (3 / (4 * π) : ℂ) := by
        have := Complex.hasSum_ofReal.2 hr
        push_cast at this
        refine this.congr_fun fun n => ?_
        rw [hG]
        exact hrG n
      exact ((Complex.hasSum_conj'.2 hc).mul_left (conj (ν z) * μ z)).mul_right _)
  unfold l2Inner
  convert h using 1
  unfold wpInner
  rw [← integral_const_mul]
  congr 1
  funext z
  rw [e3]
  ring

/-- `|x|² = x x̄` in `ℂ`. -/
theorem s7g_r_nsq (x : ℂ) : ((‖x‖ : ℝ) : ℂ) ^ 2 = x * conj x := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The kernel `B` on `𝔻*` with the conjugate pairing: `∫_{𝔻*} G(z, w)(1 - |w|²)²/((1 - w z̄)⁴(1 - v w̄)⁴) d²w
= 1/(9(1 - v z̄)⁴)`, from `bKernel_closed_form` by `w ↦ 1/w` and conjugation (`G` is real). -/
theorem s7g_r_Bext {z v : ℂ} (hz : z ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) /
        ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4)) = 1 / (9 * (1 - v * conj z) ^ 4) := by
  have hz0 := resolvent_exterior_ne_zero hz
  have hv0 := resolvent_exterior_ne_zero hv
  have hz1 : 1 < ‖z‖ := hz
  have hv1 : 1 < ‖v‖ := hv
  have hc : z⁻¹ ∈ unitDisc := mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1)
  have ha : v⁻¹ ∈ unitDisc := mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hv1)
  have hcv := resolvent_inv_exterior_conformal
  have hi := ahP_integral_image (U := unitDiscExterior) resolvent_exterior_isOpen hcv.1 hcv.2.1
    (fun u => conj z⁻¹ ^ 4 * v⁻¹ ^ 4 * ((resolventKernel z⁻¹ u : ℂ) * ((1 - ‖u‖ ^ 2) ^ 2 : ℝ) /
      ((1 - conj z⁻¹ * u) ^ 4 * (1 - v⁻¹ * conj u) ^ 4)))
  rw [hcv.2.2, setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))),
    integral_const_mul] at hi
  -- the disk integral is the conjugate of `bKernel`
  have hB : (∫ u in unitDisc, (resolventKernel z⁻¹ u : ℂ) * ((1 - ‖u‖ ^ 2) ^ 2 : ℝ) /
      ((1 - conj z⁻¹ * u) ^ 4 * (1 - v⁻¹ * conj u) ^ 4)) = conj (bKernel z⁻¹ v⁻¹) := by
    unfold bKernel
    rw [← integral_conj]
    congr 1
    funext u
    simp only [map_div₀, map_mul, map_pow, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [hB, bKernel_closed_form hc ha] at hi
  rw [← setIntegral_congr_fun resolvent_exterior_isOpen.measurableSet (f := fun w =>
      ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2 • (conj z⁻¹ ^ 4 * v⁻¹ ^ 4 * ((resolventKernel z⁻¹ w⁻¹ : ℂ) *
        ((1 - ‖w⁻¹‖ ^ 2) ^ 2 : ℝ) / ((1 - conj z⁻¹ * w⁻¹) ^ 4 * (1 - v⁻¹ * conj w⁻¹) ^ 4)))) ?_, ← hi]
  · have hzc : conj z ≠ 0 := (map_ne_zero _).2 hz0
    have hq' : conj z * v - 1 ≠ 0 := by
      intro h
      have : ‖conj z * v‖ = 1 := by rw [sub_eq_zero.1 h, norm_one]
      rw [norm_mul, Complex.norm_conj] at this
      nlinarith
    have hq'' : (1 : ℂ) - v * conj z ≠ 0 := by
      intro h
      apply hq'
      linear_combination -h
    have hp : conj z * v ≠ 0 := mul_ne_zero hzc hv0
    simp only [map_div₀, map_one, map_pow, map_sub, map_mul, map_inv₀, Complex.conj_conj, map_ofNat]
    rw [show (conj z)⁻¹ ^ 4 * v⁻¹ ^ 4 = ((conj z * v)⁻¹) ^ 4 by rw [mul_inv, mul_pow],
      show (conj z)⁻¹ * v⁻¹ = (conj z * v)⁻¹ from (mul_inv _ _).symm, show v * conj z = conj z * v from mul_comm _ _]
    have h1p : (1 : ℂ) - conj z * v ≠ 0 := by rwa [mul_comm]
    generalize conj z * v = p at hp hq' h1p ⊢
    rw [show (1 : ℂ) - p⁻¹ = (p - 1) / p by field_simp]
    field_simp
    ring
  · intro w hw
    have hw0 := resolvent_exterior_ne_zero hw
    have hw1 : 1 < ‖w‖ := hw
    have hwc : conj w ≠ 0 := (map_ne_zero _).2 hw0
    have hzc : conj z ≠ 0 := (map_ne_zero _).2 hz0
    have hd1 : (1 : ℂ) - w * conj z ≠ 0 := by
      intro h
      have : ‖w * conj z‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
      rw [norm_mul, Complex.norm_conj] at this
      nlinarith
    have hd2 : (1 : ℂ) - v * conj w ≠ 0 := by
      intro h
      have : ‖v * conj w‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
      rw [norm_mul, Complex.norm_conj] at this
      nlinarith
    show ‖deriv (fun z : ℂ => z⁻¹) w‖ ^ 2 • _ = _
    rw [(hasDerivAt_inv hw0).deriv, resolventKernel_inv hz0 hw0, Complex.real_smul]
    simp only [norm_neg, norm_inv, norm_pow, map_inv₀, map_pow]
    push_cast
    simp only [inv_pow, s7g_r_nsq]
    have hww : w * conj w ≠ 0 := mul_ne_zero hw0 hwc
    have hd1' : w * conj z - 1 ≠ 0 := fun h => hd1 (by linear_combination -h)
    have hd2' : v * conj w - 1 ≠ 0 := fun h => hd2 (by linear_combination -h)
    have e1 : (1 : ℂ) - (conj z)⁻¹ * w⁻¹ = (w * conj z - 1) / (w * conj z) := by field_simp
    have e2 : (1 : ℂ) - v⁻¹ * (conj w)⁻¹ = (v * conj w - 1) / (v * conj w) := by field_simp
    have e3 : (1 : ℂ) - (w * conj w)⁻¹ = (w * conj w - 1) / (w * conj w) := by field_simp
    rw [e1, e2, e3]
    field_simp
    ring

/-- The exterior Bergman-type integral `∫_{𝔻*} |1 - v w̄|⁻⁴ d²v = π/(|w|² - 1)²`. -/
theorem s7g_r_berg {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∫⁻ v in unitDiscExterior, ENNReal.ofReal (1 / ‖1 - v * conj w‖ ^ 4) = ENNReal.ofReal (π / (‖w‖ ^ 2 - 1) ^ 2) := by
  have hcv := resolvent_inv_exterior_conformal
  have hwc : conj w ∈ unitDiscExterior := by
    show 1 < ‖conj w‖
    rw [Complex.norm_conj]
    exact hw
  have h := r24_conformal_lintegral (U := unitDiscExterior) resolvent_exterior_isOpen hcv.1 hcv.2.1
    (fun u => ENNReal.ofReal (1 / ‖conj w - u‖ ^ 4))
  rw [hcv.2.2, setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton (0 : ℂ))), CUI.cui_bergman hwc,
    Complex.norm_conj] at h
  rw [h]
  refine setLIntegral_congr_fun resolvent_exterior_isOpen.measurableSet fun v hv => ?_
  have hv0 := resolvent_exterior_ne_zero hv
  rw [(hasDerivAt_inv hv0).deriv, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : conj w - v⁻¹ = -(1 - v * conj w) / v := by field_simp; ring
  rw [e, norm_div, norm_neg, norm_neg, norm_inv, norm_pow]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  by_cases h1 : ‖1 - v * conj w‖ = 0
  · rw [h1]
    simp
  · field_simp

/-- `|1 - w z̄|⁻⁴ ≤ M ρ(w)` on `𝔻*`, `M = 1/(|z|²(|z| - 1)²)`. -/
theorem s7g_r_kbound {z w : ℂ} (hz : z ∈ unitDiscExterior) (hw : w ∈ unitDiscExterior) :
    1 / ‖1 - w * conj z‖ ^ 4 ≤ 1 / (‖z‖ ^ 2 * (‖z‖ - 1) ^ 2) * rho w := by
  have hz1 : 1 < ‖z‖ := hz
  have hw1 : 1 < ‖w‖ := hw
  set d := ‖w‖ * ‖z‖ - 1 with hd
  have hd0 : 0 < d := by rw [hd]; nlinarith
  have hdist : d ≤ ‖1 - w * conj z‖ := by
    have := norm_sub_norm_le (w * conj z) 1
    rw [norm_mul, Complex.norm_conj, norm_one, norm_sub_rev] at this
    linarith
  have h1 : ‖w‖ - 1 ≤ d / ‖z‖ := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have h2 : ‖w‖ + 1 ≤ 2 * d / (‖z‖ - 1) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have h3 : ‖w‖ ^ 2 - 1 ≤ 2 * d ^ 2 / (‖z‖ * (‖z‖ - 1)) := by
    have e : ‖w‖ ^ 2 - 1 = (‖w‖ - 1) * (‖w‖ + 1) := by ring
    rw [e]
    calc (‖w‖ - 1) * (‖w‖ + 1) ≤ d / ‖z‖ * (2 * d / (‖z‖ - 1)) :=
          mul_le_mul h1 h2 (by linarith) (by positivity)
      _ = 2 * d ^ 2 / (‖z‖ * (‖z‖ - 1)) := by field_simp
  have hρ : rho w = 4 / (1 - ‖w‖ ^ 2) ^ 2 := by unfold rho; rfl
  rw [hρ]
  have hA : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
  have hq : (1 - ‖w‖ ^ 2) ^ 2 = (‖w‖ ^ 2 - 1) ^ 2 := by ring
  rw [hq]
  have hz2 : 0 < ‖z‖ - 1 := by linarith
  have h4 : (‖w‖ ^ 2 - 1) ^ 2 ≤ (2 * d ^ 2 / (‖z‖ * (‖z‖ - 1))) ^ 2 := pow_le_pow_left₀ hA.le h3 2
  have h5 : d ^ 4 ≤ ‖1 - w * conj z‖ ^ 4 := pow_le_pow_left₀ hd0.le hdist 4
  have hP : 0 < (‖z‖ * (‖z‖ - 1)) ^ 2 := by positivity
  have h4' : (‖w‖ ^ 2 - 1) ^ 2 * (‖z‖ * (‖z‖ - 1)) ^ 2 ≤ 4 * d ^ 4 := by
    rw [div_pow, le_div_iff₀ hP] at h4
    linarith
  calc 1 / ‖1 - w * conj z‖ ^ 4 ≤ 1 / d ^ 4 := one_div_le_one_div_of_le (by positivity) h5
    _ ≤ 1 / (‖z‖ ^ 2 * (‖z‖ - 1) ^ 2) * (4 / (‖w‖ ^ 2 - 1) ^ 2) := by
      rw [show 1 / (‖z‖ ^ 2 * (‖z‖ - 1) ^ 2) * (4 / (‖w‖ ^ 2 - 1) ^ 2) =
          4 / ((‖w‖ ^ 2 - 1) ^ 2 * (‖z‖ * (‖z‖ - 1)) ^ 2) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith

/-- The Fubini integrand of `H` is integrable on `𝔻* × 𝔻*`. -/
theorem s7g_r_fub {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    Integrable (fun p : ℂ × ℂ => (resolventKernel z p.1 : ℂ) * ((1 - ‖p.1‖ ^ 2) ^ 2 : ℝ) * μ p.2 /
        ((1 - p.1 * conj z) ^ 4 * (1 - p.2 * conj p.1) ^ 4))
      ((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  obtain ⟨C, hb, hC0⟩ : ∃ C : ℝ, (∀ v ∈ unitDiscExterior, ‖μ v‖ ≤ C) ∧ 0 ≤ C :=
    ⟨_, fun v hv => wp_harmonic_pointwise_bound hμ hv, by positivity⟩
  have aμ := s7pol_harmonic_measurable hμ
  have hK1 : Measurable (resolventKernel z) := measurable_resolventKernel.of_uncurry_left
  have hK : Measurable (fun p : ℂ × ℂ => (resolventKernel z p.1 : ℂ)) := by fun_prop
  have hR : Measurable (fun p : ℂ × ℂ => (((1 - ‖p.1‖ ^ 2) ^ 2 : ℝ) : ℂ) /
      ((1 - p.1 * conj z) ^ 4 * (1 - p.2 * conj p.1) ^ 4)) := by fun_prop
  have hF : AEStronglyMeasurable (fun p : ℂ × ℂ => (resolventKernel z p.1 : ℂ) * ((1 - ‖p.1‖ ^ 2) ^ 2 : ℝ) * μ p.2 /
      ((1 - p.1 * conj z) ^ 4 * (1 - p.2 * conj p.1) ^ 4))
      ((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) := by
    refine ((hK.aestronglyMeasurable.mul aμ.comp_snd).mul hR.aestronglyMeasurable).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hz1 : 1 < ‖z‖ := hz
  have hz2 : 0 < ‖z‖ - 1 := by linarith
  obtain ⟨M, hM0, hkb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ unitDiscExterior, 1 / ‖1 - w * conj z‖ ^ 4 ≤ M * rho w :=
    ⟨_, by positivity, fun w hw => s7g_r_kbound hz hw⟩
  refine ⟨hF, ?_⟩
  show ∫⁻ p, ‖(resolventKernel z p.1 : ℂ) * ((1 - ‖p.1‖ ^ 2) ^ 2 : ℝ) * μ p.2 /
      ((1 - p.1 * conj z) ^ 4 * (1 - p.2 * conj p.1) ^ 4)‖ₑ
      ∂((volume.restrict unitDiscExterior).prod (volume.restrict unitDiscExterior)) < ∞
  rw [lintegral_prod _ hF.enorm]
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hfin : ∫⁻ w in unitDiscExterior, ENNReal.ofReal (|resolventKernel z w| * rho w) < ∞ := by
    have h := (resolvent_mass_integrable (Or.inr rfl) hz).hasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) h
    refine lintegral_congr fun w => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (wp_rho_nonneg w)]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun w => ENNReal.ofReal (C * π * M) *
      ENNReal.ofReal (|resolventKernel z w| * rho w)) ?_) ?_
  · filter_upwards [ae_restrict_mem hm] with w hw
    have hw1 : 1 < ‖w‖ := hw
    have hA : 0 < ‖w‖ ^ 2 - 1 := by nlinarith
    set a : ℝ := |resolventKernel z w| * (1 - ‖w‖ ^ 2) ^ 2 * C / ‖1 - w * conj z‖ ^ 4 with ha
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    calc ∫⁻ v in unitDiscExterior, ‖(resolventKernel z (w, v).1 : ℂ) * ((1 - ‖(w, v).1‖ ^ 2) ^ 2 : ℝ) * μ (w, v).2 /
          ((1 - (w, v).1 * conj z) ^ 4 * (1 - (w, v).2 * conj (w, v).1) ^ 4)‖ₑ
        ≤ ∫⁻ v in unitDiscExterior, ENNReal.ofReal a * ENNReal.ofReal (1 / ‖1 - v * conj w‖ ^ 4) := by
          refine setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun v hv => ?_)
          rw [← ENNReal.ofReal_mul ha0, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only
          rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - ‖w‖ ^ 2) ^ 2), ha,
            div_mul_div_comm, mul_one]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb v hv) (by positivity)) (by positivity)
      _ = ENNReal.ofReal a * ENNReal.ofReal (π / (‖w‖ ^ 2 - 1) ^ 2) := by
          rw [lintegral_const_mul _ (by fun_prop), s7g_r_berg hw]
      _ ≤ ENNReal.ofReal (C * π * M) * ENNReal.ofReal (|resolventKernel z w| * rho w) := by
          rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hk := hkb w hw
          rw [ha]
          have e : (1 - ‖w‖ ^ 2) ^ 2 = (‖w‖ ^ 2 - 1) ^ 2 := by ring
          rw [e]
          have hK0 := abs_nonneg (resolventKernel z w)
          calc |resolventKernel z w| * (‖w‖ ^ 2 - 1) ^ 2 * C / ‖1 - w * conj z‖ ^ 4 * (π / (‖w‖ ^ 2 - 1) ^ 2)
              = |resolventKernel z w| * C * π * (1 / ‖1 - w * conj z‖ ^ 4) := by
                field_simp
            _ ≤ |resolventKernel z w| * C * π * (M * rho w) := by gcongr
            _ = C * π * M * (|resolventKernel z w| * rho w) := by ring
  · rw [lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- STUB H. The resolvent against the basis kernel reproduces `μ/(3π)`. -/
theorem s7g_r_H {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∫ w in unitDiscExterior, (resolventKernel z w : ℂ) * μ w *
        ((3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj z) ^ 4) * rho w) =
      μ z / (3 * π) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hrep := wp_harmonic_projection_raw hμ hz
  -- `μ(w)` by the reproducing formula, and `(1 - |w|²)² ρ(w) = 4`
  have hpt : ∀ w ∈ unitDiscExterior, (resolventKernel z w : ℂ) * μ w *
      ((3 / (4 * π) : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) / (1 - w * conj z) ^ 4) * rho w =
      (9 / π ^ 2 : ℂ) * ((1 - ‖z‖ ^ 2) ^ 2 : ℝ) * ∫ v in unitDiscExterior, (resolventKernel z w : ℂ) *
        ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * μ v / ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4) := by
    intro w hw
    have hw1 : 1 < ‖w‖ := hw
    have e : (∫ v in unitDiscExterior, (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * μ v /
        ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4)) = (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) /
          (1 - w * conj z) ^ 4 * ∫ v in unitDiscExterior, μ v / (1 - v * conj w) ^ 4 := by
      rw [← integral_const_mul]
      congr 1
      funext v
      generalize (1 - w * conj z) ^ 4 = D1
      generalize (1 - v * conj w) ^ 4 = D2
      ring
    rw [e, ← wp_harmonic_projection_raw hμ hw, wp_rho_complex w]
    have hA : (1 : ℂ) - w * conj w ≠ 0 := by
      rw [← s7g_r_nsq]
      intro h
      have h2 : ((‖w‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -h
      have h3 : ‖w‖ ^ 2 = 1 := by exact_mod_cast h2
      nlinarith
    push_cast
    simp only [s7g_r_nsq]
    generalize (∫ v in unitDiscExterior, μ v / (1 - v * conj w) ^ 4) = J
    field_simp
    ring
  rw [setIntegral_congr_fun hm hpt, integral_const_mul,
    integral_integral_swap (f := fun w v => (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * μ v /
      ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4)) (s7g_r_fub hμ hz)]
  -- the inner `w`-integral is the kernel `B` on `𝔻*`
  have hin : ∀ v ∈ unitDiscExterior, (∫ w in unitDiscExterior, (resolventKernel z w : ℂ) *
      ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) * μ v / ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4)) =
      μ v / (1 - v * conj z) ^ 4 / 9 := by
    intro v hv
    calc _ = μ v * ∫ w in unitDiscExterior, (resolventKernel z w : ℂ) * ((1 - ‖w‖ ^ 2) ^ 2 : ℝ) /
          ((1 - w * conj z) ^ 4 * (1 - v * conj w) ^ 4) := by
          rw [← integral_const_mul]
          congr 1
          funext w
          generalize (1 - w * conj z) ^ 4 = D1
          generalize (1 - v * conj w) ^ 4 = D2
          ring
      _ = _ := by
          rw [s7g_r_Bext hz hv]
          generalize (1 - v * conj z) ^ 4 = D
          ring
  rw [setIntegral_congr_fun hm hin, integral_div, ← hrep]
  generalize (∫ v in unitDiscExterior, μ v / (1 - v * conj z) ^ 4) = I
  field_simp

/-- The forcing `μ̄ bₙ` is bounded and measurable, hence so is `G(μ̄ bₙ)`. -/
theorem s7g_r_Gm {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (n : ℕ) :
    ∃ C : ℝ, AEStronglyMeasurable (fun w => conj (μ w) * basisMu (n + 2) w) (volume.restrict unitDiscExterior) ∧
      (∀ w ∈ unitDiscExterior, ‖conj (μ w) * basisMu (n + 2) w‖ ≤ C) ∧
      AEStronglyMeasurable (resolventStar fun w => conj (μ w) * basisMu (n + 2) w)
        (volume.restrict unitDiscExterior) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hb : basisMu (n + 2) ∈ harmonicL2 unitDiscExterior := basisMu_orthonormal.1 (n + 2) (by omega)
  obtain ⟨C, hbC, hC0⟩ : ∃ C : ℝ, (∀ v ∈ unitDiscExterior, ‖μ v‖ ≤ C) ∧ 0 ≤ C :=
    ⟨_, fun v hv => wp_harmonic_pointwise_bound hμ hv, by positivity⟩
  have ha : AEStronglyMeasurable (fun w => conj (μ w) * basisMu (n + 2) w) (volume.restrict unitDiscExterior) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (s7pol_harmonic_measurable hμ)).mul
      (s7pol_harmonic_measurable hb)
  have hB : ∀ w ∈ unitDiscExterior, ‖conj (μ w) * basisMu (n + 2) w‖ ≤ C * (1 + 3 / (4 * π)) := by
    intro w hw
    rw [norm_mul, Complex.norm_conj]
    have h1 := s7g_r_bd hw n
    have h2 : ‖basisMu (n + 2) w‖ ≤ 1 + 3 / (4 * π) := by
      nlinarith [sq_nonneg (‖basisMu (n + 2) w‖ - 1 / 2)]
    exact mul_le_mul (hbC w hw) h2 (norm_nonneg _) hC0
  exact ⟨_, ha, hB, (resolventOp_continuousOn_of_bounded (Or.inr rfl) ha hB).aestronglyMeasurable hm⟩

/-- Inner sum of `T1`: `Σₙ bₙ(z) conj (G(μ̄ bₙ)(z)) = μ(z)/(3π)` (dominated convergence, then `H`). -/
theorem s7g_r_T1in {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    HasSum (fun n : ℕ => basisMu (n + 2) z * conj (resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z))
      (μ z / (3 * π)) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hK1 : Measurable (resolventKernel z) := measurable_resolventKernel.of_uncurry_left
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior :=
    fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have aμ := s7pol_harmonic_measurable hμ
  obtain ⟨C, hbC, hC0⟩ : ∃ C : ℝ, (∀ v ∈ unitDiscExterior, ‖μ v‖ ≤ C) ∧ 0 ≤ C :=
    ⟨_, fun v hv => wp_harmonic_pointwise_bound hμ hv, by positivity⟩
  have aK : AEStronglyMeasurable (fun w => (resolventKernel z w : ℂ)) (volume.restrict unitDiscExterior) :=
    (Complex.measurable_ofReal.comp hK1).aestronglyMeasurable
  have aρ : AEStronglyMeasurable (fun w => (rho w : ℂ)) (volume.restrict unitDiscExterior) :=
    (Complex.measurable_ofReal.comp hρm).aestronglyMeasurable
  have hKi : Integrable (fun w => (resolventKernel z w : ℂ) * μ w * rho w) (volume.restrict unitDiscExterior) := by
    refine Integrable.mono' ((resolvent_mass_integrable (Or.inr rfl) hz).abs.const_mul C) ((aK.mul aμ).mul aρ) ?_
    filter_upwards [ae_restrict_mem hm] with w hw
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have := hbC w hw
    have h0 := abs_nonneg (resolventKernel z w)
    have h1 := abs_nonneg (rho w)
    calc |resolventKernel z w| * ‖μ w‖ * |rho w| ≤ |resolventKernel z w| * C * |rho w| := by gcongr
      _ = C * (|resolventKernel z w| * |rho w|) := by ring
  have key : ∀ n : ℕ, basisMu (n + 2) z * conj (resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z) =
      ∫ w in unitDiscExterior, (resolventKernel z w : ℂ) * μ w *
        (basisMu (n + 2) z * conj (basisMu (n + 2) w)) * rho w := by
    intro n
    show basisMu (n + 2) z * conj (resolventOp unitDiscExterior _ z) = _
    unfold resolventOp
    rw [← integral_conj, ← integral_const_mul]
    congr 1
    funext w
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [show (fun n : ℕ => basisMu (n + 2) z * conj (resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z)) =
      fun n : ℕ => ∫ w in unitDiscExterior, (resolventKernel z w : ℂ) * μ w *
        (basisMu (n + 2) z * conj (basisMu (n + 2) w)) * rho w from funext key, ← s7g_r_H hμ hz]
  refine hasSum_integral_of_dominated_convergence
    (fun n w => ‖(resolventKernel z w : ℂ) * μ w * rho w‖ *
      ((‖basisMu (n + 2) z‖ ^ 2 + ‖basisMu (n + 2) w‖ ^ 2) / 2))
    (fun n => ((aK.mul aμ).mul (aestronglyMeasurable_const.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (s7pol_harmonic_measurable (hb n))))).mul aρ)
    (fun n => Eventually.of_forall fun w => ?_) ?_ ?_ ?_
  · rw [show (resolventKernel z w : ℂ) * μ w * (basisMu (n + 2) z * conj (basisMu (n + 2) w)) * rho w =
        ((resolventKernel z w : ℂ) * μ w * rho w) * (basisMu (n + 2) z * conj (basisMu (n + 2) w)) by ring,
      norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖basisMu (n + 2) z‖ - ‖basisMu (n + 2) w‖)]
  · filter_upwards [ae_restrict_mem hm] with w hw
    exact ((((s7g_r_bsum hz hz).2.add (s7g_r_bsum hw hw).2).div_const 2).mul_left _).summable
  · refine (hKi.norm.mul_const (3 / (4 * π))).congr ?_
    filter_upwards [ae_restrict_mem hm] with w hw
    rw [((((s7g_r_bsum hz hz).2.add (s7g_r_bsum hw hw).2).div_const 2).mul_left _).tsum_eq]
    ring
  · filter_upwards [ae_restrict_mem hm] with w hw
    exact ((s7g_r_bsum hz hw).1.mul_left ((resolventKernel z w : ℂ) * μ w)).mul_right (rho w : ℂ)

/-- `Σₙ |G(μ̄ bₙ)|² ρ` is finite a.e. and integrable (Tonelli and `s7rl_contraction`). -/
theorem s7g_r_Gsq {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    (∀ᵐ z ∂(volume.restrict unitDiscExterior),
        Summable (fun n : ℕ => ‖resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z‖ ^ 2 * rho z)) ∧
      Integrable (fun z => ∑' n : ℕ, ‖resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z‖ ^ 2 * rho z)
        (volume.restrict unitDiscExterior) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior :=
    fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have hnorm (v : ℂ) (r : ℝ) (hr : 0 ≤ r) :
      (‖v‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal r = ENNReal.ofReal (‖v‖ ^ 2 * r) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, enorm_eq_nnnorm]
  set g : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (‖resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z‖ ^ 2 * rho z) with hg
  have ag : ∀ n, AEMeasurable (g n) (volume.restrict unitDiscExterior) := by
    intro n
    obtain ⟨C, _, _, hG⟩ := s7g_r_Gm hμ n
    exact ((hG.norm.pow 2).mul hρm.aestronglyMeasurable).aemeasurable.ennreal_ofReal
  have hcontr : ∀ n, ∫⁻ z in unitDiscExterior, g n z ≤
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal (‖μ z‖ ^ 2 * rho z * ‖basisMu (n + 2) z‖ ^ 2) := by
    intro n
    obtain ⟨C, ha, hB, _⟩ := s7g_r_Gm hμ n
    have h := s7rl_contraction (Or.inr rfl) ha (C := C) (by
      filter_upwards [ae_restrict_mem hm] with w hw
      exact hB w hw)
    unfold normL2 at h
    rw [ENNReal.rpow_le_rpow_iff (by norm_num)] at h
    convert h using 1
    · refine lintegral_congr fun z => ?_
      rw [hg, hnorm _ _ (wp_rho_nonneg z)]
      rfl
    · refine lintegral_congr fun z => ?_
      rw [hnorm _ _ (wp_rho_nonneg z), norm_mul, Complex.norm_conj]
      congr 1
      ring
  have hint : Integrable (fun z => ‖μ z‖ ^ 2 * rho z * (3 / (4 * π))) (volume.restrict unitDiscExterior) := by
    refine ((wpInner_integrable hμ hμ).norm.mul_const (3 / (4 * π))).congr (Eventually.of_forall fun z => ?_)
    show ‖μ z * conj (μ z) * rho z‖ * (3 / (4 * π)) = _
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wp_rho_nonneg z)]
    ring
  have hfin : ∫⁻ z in unitDiscExterior, ∑' n, g n z < ∞ := by
    rw [lintegral_tsum ag]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hcontr) ?_
    have ht := lintegral_tsum (μ := volume.restrict unitDiscExterior)
      (f := fun n z => ENNReal.ofReal (‖μ z‖ ^ 2 * rho z * ‖basisMu (n + 2) z‖ ^ 2))
      (fun n => ((((s7pol_harmonic_measurable hμ).norm.pow 2).mul
        hρm.aestronglyMeasurable).mul ((s7pol_harmonic_measurable (hb n)).norm.pow 2)).aemeasurable.ennreal_ofReal)
    rw [← ht]
    refine lt_of_le_of_lt (le_of_eq ?_) hint.lintegral_lt_top
    refine setLIntegral_congr_fun hm fun z hz => ?_
    have hs := (s7g_r_bsum hz hz).2.mul_left (‖μ z‖ ^ 2 * rho z)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := wp_rho_nonneg z; positivity) hs.summable, hs.tsum_eq]
  have agt : AEMeasurable (fun z => ∑' n, g n z) (volume.restrict unitDiscExterior) := AEMeasurable.ennreal_tsum ag
  have he : ∀ z, ∑' n : ℕ, ‖resolventStar (fun w => conj (μ w) * basisMu (n + 2) w) z‖ ^ 2 * rho z =
      (∑' n, g n z).toReal := by
    intro z
    rw [ENNReal.tsum_toReal_eq fun n => ENNReal.ofReal_ne_top]
    refine tsum_congr fun n => ?_
    rw [ENNReal.toReal_ofReal (by have := wp_rho_nonneg z; positivity)]
  refine ⟨?_, (integrable_toReal_of_lintegral_ne_top agt hfin.ne).congr (Eventually.of_forall fun z => (he z).symm)⟩
  filter_upwards [ae_lt_top' agt hfin.ne] with z hz
  refine (ENNReal.summable_toReal hz.ne).congr fun n => ?_
  rw [hg, ENNReal.toReal_ofReal (by have := wp_rho_nonneg z; positivity)]

/-- STUB T1. `Σₙ (bₙ ν̄, G(μ̄ bₙ)) = (1/(3π)) ⟨μ, ν⟩`. -/
theorem s7g_r_T1 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    HasSum (fun n : ℕ => l2Inner (fun z => basisMu (n + 2) z * conj (ν z))
        (resolventStar fun z => conj (μ z) * basisMu (n + 2) z)) ((1 / (3 * π) : ℂ) * wpInner μ ν) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hρm : Measurable rho :=
    measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior :=
    fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have aν := s7pol_harmonic_measurable hν
  obtain ⟨hGs, hGi⟩ := s7g_r_Gsq hμ
  set G : ℕ → ℂ → ℂ := fun n => resolventStar fun w => conj (μ w) * basisMu (n + 2) w with hG
  have aG : ∀ n, AEStronglyMeasurable (G n) (volume.restrict unitDiscExterior) := by
    intro n
    obtain ⟨C, _, _, h⟩ := s7g_r_Gm hμ n
    exact h
  have hνi : Integrable (fun z => ‖ν z‖ ^ 2 * rho z * (3 / (4 * π))) (volume.restrict unitDiscExterior) := by
    refine ((wpInner_integrable hν hν).norm.mul_const (3 / (4 * π))).congr (Eventually.of_forall fun z => ?_)
    show ‖ν z * conj (ν z) * rho z‖ * (3 / (4 * π)) = _
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wp_rho_nonneg z)]
    ring
  have h := hasSum_integral_of_dominated_convergence (μ := volume.restrict unitDiscExterior)
    (F := fun n z => basisMu (n + 2) z * conj (ν z) * conj (G n z) * rho z)
    (f := fun z => conj (ν z) * (μ z / (3 * π)) * rho z)
    (fun n z => (‖ν z‖ ^ 2 * rho z * ‖basisMu (n + 2) z‖ ^ 2 + ‖G n z‖ ^ 2 * rho z) / 2)
    (fun n => (((s7pol_harmonic_measurable (hb n)).mul (Complex.continuous_conj.comp_aestronglyMeasurable aν)).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (aG n))).mul
        (Complex.measurable_ofReal.comp hρm).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun z => by
      have hρ := wp_rho_nonneg z
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ]
      have h2 : ‖basisMu (n + 2) z‖ * ‖ν z‖ * ‖G n z‖ ≤
          (‖ν z‖ ^ 2 * ‖basisMu (n + 2) z‖ ^ 2 + ‖G n z‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖ν z‖ * ‖basisMu (n + 2) z‖ - ‖G n z‖)]
      calc ‖basisMu (n + 2) z‖ * ‖ν z‖ * ‖G n z‖ * rho z
          ≤ (‖ν z‖ ^ 2 * ‖basisMu (n + 2) z‖ ^ 2 + ‖G n z‖ ^ 2) / 2 * rho z := mul_le_mul_of_nonneg_right h2 hρ
        _ = _ := by ring)
    (by
      filter_upwards [ae_restrict_mem hm, hGs] with z hz hs
      exact (((s7g_r_bsum hz hz).2.mul_left (‖ν z‖ ^ 2 * rho z)).summable.add hs).div_const 2)
    (by
      refine ((hνi.add hGi).div_const 2).congr ?_
      filter_upwards [ae_restrict_mem hm, hGs] with z hz hs
      rw [tsum_div_const, Summable.tsum_add ((s7g_r_bsum hz hz).2.mul_left (‖ν z‖ ^ 2 * rho z)).summable hs,
        ((s7g_r_bsum hz hz).2.mul_left (‖ν z‖ ^ 2 * rho z)).tsum_eq]
      rfl)
    (by
      filter_upwards [ae_restrict_mem hm] with z hz
      convert ((s7g_r_T1in hμ hz).mul_left (conj (ν z))).mul_right (rho z : ℂ) using 1
      funext n
      ring)
  unfold l2Inner
  convert h using 1
  unfold wpInner
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-- **Theorem 7.11** (TT:3026–3030). The Ricci tensor at the origin is well defined (the series converges) and
`𝓡_{k l̄} = -(13/(12π)) δ_{kl}`; more generally `𝓡_{μν̄} = -(13/(12π)) g_{μν̄}` for `μ, ν ∈ H^{-1,1}(𝔻*)`. -/
theorem s7g_thm_7_11 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    Summable (fun n : ℕ => riemannR μ (basisMu (n + 2)) (basisMu (n + 2)) ν) ∧
      ricciT μ ν = -(13 / (12 * π)) * wpInner μ ν := by
  have hb : ∀ n : ℕ, basisMu (n + 2) ∈ harmonicL2 unitDiscExterior := fun n => basisMu_orthonormal.1 (n + 2) (by omega)
  have he : (fun n : ℕ => riemannR μ (basisMu (n + 2)) (basisMu (n + 2)) ν) = fun n =>
      -l2Inner (fun z => basisMu (n + 2) z * conj (ν z)) (resolventStar fun z => conj (μ z) * basisMu (n + 2) z) -
        l2Inner (fun z => conj (ν z) * μ z) (resolventStar fun z => conj (basisMu (n + 2) z) * basisMu (n + 2) z) :=
    funext fun n => s7g_cor_7_9 (hb n) hν hμ (hb n)
  have hs := ((s7g_r_T1 hμ hν).neg).sub (s7g_r_T2 hμ hν)
  rw [← he] at hs
  refine ⟨hs.summable, ?_⟩
  unfold ricciT
  rw [hs.tsum_eq]
  field_simp
  ring

/-- **Corollary 7.12** (TT:3104–3108). `T(1)` is Kähler–Einstein with negative constant Ricci curvature:
`Ric_WP = -(13/(12π)) ω_WP`, where `Ric_WP(μ, ν̄) = (i/2) 𝓡_{μν̄}` (TT:3101). Stated at the origin; both forms are
right-invariant. -/
theorem s7g_cor_7_12 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    I / 2 * ricciT μ ν = -(13 / (12 * π)) * omegaWPOrigin μ ν := by
  rw [(s7g_thm_7_11 hμ hν).2]
  unfold omegaWPOrigin
  ring

/-- **Theorem 7.11** (TT:3026–3030). The Ricci tensor at the origin is well defined (the series converges) and
`𝓡_{k l̄} = -(13/(12π)) δ_{kl}`; more generally `𝓡_{μν̄} = -(13/(12π)) g_{μν̄}` for `μ, ν ∈ H^{-1,1}(𝔻*)`. -/
theorem thm_7_11 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    Summable (fun n : ℕ => riemannR μ (basisMu (n + 2)) (basisMu (n + 2)) ν) ∧
      ricciT μ ν = -(13 / (12 * π)) * wpInner μ ν := by
  exact s7g_thm_7_11 hμ hν

/-- **Corollary 7.12** (TT:3104–3108). `T(1)` is Kähler–Einstein with negative constant Ricci curvature:
`Ric_WP = -(13/(12π)) ω_WP`, where `Ric_WP(μ, ν̄) = (i/2) 𝓡_{μν̄}` (TT:3101). Stated at the origin; both forms are
right-invariant. -/
theorem cor_7_12 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    I / 2 * ricciT μ ν = -(13 / (12 * π)) * omegaWPOrigin μ ν := by
  exact s7g_cor_7_12 hμ hν

end TakhtajanTeo
