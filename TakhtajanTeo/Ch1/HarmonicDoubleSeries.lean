import TakhtajanTeo.Ch1.HarmonicAbelKernel

/-! Termwise integration of Abel-damped double kernels (TT:2662–2666). -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_hasSum_double_kernel {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℂ) * q ^ n)
      (((1 - q)⁻¹) ^ 2 + (1 - q)⁻¹) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hq).add
    (hasSum_geometric_of_norm_lt_one hq)
  convert h using 1
  · funext n
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · norm_num [one_div, inv_pow]

theorem wp_double_kernel_coefficient_summable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => (n + 2 : ℝ) * t ^ n) := by
  have ht : ‖t‖ < 1 := by rwa [Real.norm_of_nonneg ht0]
  have h := ((hasSum_choose_mul_geometric_of_norm_lt_one 1 ht).add
    (hasSum_geometric_of_norm_lt_one ht)).summable
  convert h using 1
  funext n
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  ring

theorem wp_damped_double_kernel_hasSum {f g : ℂ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hbf : ∀ u ∈ unitDisc, ‖f u‖ ≤ M) (hbg : ∀ v ∈ unitDisc, ‖g v‖ ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℂ) * (t : ℂ) ^ n *
      ∫ p : ℂ × ℂ, f p.1 * g p.2 * (p.1 * conj p.2) ^ n
        ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)))
      (∫ p : ℂ × ℂ, f p.1 * g p.2 *
        (((1 - (t : ℂ) * (p.1 * conj p.2))⁻¹) ^ 2 + (1 - (t : ℂ) * (p.1 * conj p.2))⁻¹)
        ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) := by
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbf 0 hzero)
  have hN : 0 ≤ N := (norm_nonneg _).trans (hbg 0 hzero)
  have hfinite : volume unitDisc < ∞ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : ℂ) 1).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict unitDisc) := ⟨by simpa using hfinite⟩
  let P : ℕ → ℂ × ℂ → ℂ := fun n p => ((n + 2 : ℕ) : ℂ) * (t : ℂ) ^ n *
    (f p.1 * g p.2 * (p.1 * conj p.2) ^ n)
  have hmem : ∀ᵐ p ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)),
      p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)
  have hq (p : ℂ × ℂ) (hp : p.1 ∈ unitDisc ∧ p.2 ∈ unitDisc) : ‖p.1 * conj p.2‖ < 1 := by
    rw [norm_mul, norm_conj]
    exact lt_of_le_of_lt
      (mul_le_of_le_one_right (norm_nonneg p.1) (mem_ball_zero_iff.mp hp.2).le)
      (mem_ball_zero_iff.mp hp.1)
  have hs := (wp_double_kernel_coefficient_summable ht0 ht1).mul_right (M * N)
  have hi := hasSum_integral_of_dominated_convergence
    (μ := (volume.restrict unitDisc).prod (volume.restrict unitDisc)) (F := P)
    (f := fun p => f p.1 * g p.2 *
      (((1 - (t : ℂ) * (p.1 * conj p.2))⁻¹) ^ 2 + (1 - (t : ℂ) * (p.1 * conj p.2))⁻¹))
    (fun n _ => ((n + 2 : ℝ) * t ^ n) * (M * N))
    (fun n => by dsimp [P]; fun_prop)
    (fun n => by
      filter_upwards [hmem] with p hp
      have hfg : ‖f p.1‖ * ‖g p.2‖ ≤ M * N :=
        mul_le_mul (hbf _ hp.1) (hbg _ hp.2) (norm_nonneg _) hM
      have hpq : ‖p.1 * conj p.2‖ ^ n ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (hq p hp).le
      have hqfg : ‖f p.1 * g p.2 * (p.1 * conj p.2) ^ n‖ ≤ M * N := by
        rw [norm_mul, norm_mul, norm_pow]
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpq).trans hfg
      dsimp only [P]
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0]
      simp only [Nat.cast_add, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left hqfg (by positivity))
    (Filter.Eventually.of_forall fun _ => hs)
    (integrable_const _)
    (by
      filter_upwards [hmem] with p hp
      have hx : ‖(t : ℂ) * (p.1 * conj p.2)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht1.le) (hq p hp)
      have h := (wp_hasSum_double_kernel hx).mul_left (f p.1 * g p.2)
      convert h using 1
      funext n
      dsimp [P]
      rw [mul_pow]
      ring)
  simpa only [P, integral_const_mul] using hi

end TakhtajanTeo


