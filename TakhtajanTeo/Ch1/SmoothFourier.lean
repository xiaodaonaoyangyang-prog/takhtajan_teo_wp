import TakhtajanTeo.Ch1.S1_2_Homogeneous

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Differentiating the Fourier phase in the memoir's normalization (TT:2206–2216). -/
theorem wp_fourier_phase_hasDerivAt (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => exp (-((n : ℂ) * t * I)))
      ((-(n : ℂ) * I) * exp (-((n : ℂ) * θ * I))) θ := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      Complex.ofRealCLM.hasDerivAt (x := θ)
  have hh := ((h.const_mul (n : ℂ)).mul_const I).neg.cexp
  dsimp only [Pi.neg_apply, Pi.mul_apply] at hh
  convert hh using 1 <;> ring

/-- The Fourier coefficient of a periodic derivative is multiplied by in (TT:2206–2216). -/
theorem wp_fourierCoeff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hp : Function.Periodic f (2 * π)) (n : ℤ) :
    fourierCoeff (deriv f) n = (I * n) * fourierCoeff f n := by
  let p : ℝ → ℂ := fun θ => exp (-((n : ℂ) * θ * I))
  have hc : Continuous p := by dsimp [p]; fun_prop
  have hpc : Continuous (fun θ => (-(n : ℂ) * I) * p θ) := continuous_const.mul hc
  have hp0 : p 0 = 1 := by simp [p]
  have hpT : p (2 * π) = 1 := by
    dsimp only [p]
    convert Complex.exp_int_mul_two_pi_mul_I (-n) using 1
    congr 1
    push_cast
    ring
  have hfT : f (2 * π) = f 0 := by simpa using hp 0
  have hi := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := 2 * π)
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => wp_fourier_phase_hasDerivAt n x)
    (hf.continuous_deriv_one.intervalIntegrable _ _) (hpc.intervalIntegrable _ _)
  change (∫ x in (0 : ℝ)..2 * π, deriv f x * p x + f x * ((-(n : ℂ) * I) * p x)) =
    f (2 * π) * p (2 * π) - f 0 * p 0 at hi
  rw [hp0, hpT, hfT, mul_one, sub_self] at hi
  have hi1 : IntervalIntegrable (fun x => deriv f x * p x) volume 0 (2 * π) :=
    (hf.continuous_deriv_one.mul hc).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => f x * ((-(n : ℂ) * I) * p x)) volume 0 (2 * π) :=
    (hf.continuous.mul hpc).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2] at hi
  have he : (fun x => f x * ((-(n : ℂ) * I) * p x)) =
      (fun x => (-(n : ℂ) * I) * (f x * p x)) := by funext x; ring
  rw [he, intervalIntegral.integral_const_mul] at hi
  change (1 / (2 * π) : ℂ) * (∫ x in (0 : ℝ)..2 * π, deriv f x * p x) =
    (I * n) * ((1 / (2 * π) : ℂ) * ∫ x in (0 : ℝ)..2 * π, f x * p x)
  linear_combination (1 / (2 * π) : ℂ) * hi

/-- Periodicity is inherited by the derivative (TT:2206–2216). -/
theorem wp_periodic_deriv {f : ℝ → ℂ} (hf : Differentiable ℝ f) {T : ℝ}
    (hp : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  have he : (fun y => f (y + T)) = f := funext hp
  have ht : HasDerivAt (fun y : ℝ => y + T) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).add_const T
  have h : HasDerivAt (fun y => f (y + T)) (deriv f (x + T)) x := by
    simpa only [one_smul, Function.comp_def] using (hf (x + T)).hasDerivAt.scomp x ht
  rw [he] at h
  exact h.deriv.symm


/-- Iterated derivatives of a smooth function remain smooth (TT:2206–2216). -/
theorem wp_contDiff_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2

/-- Iterated derivatives preserve a smooth function's period (TT:2206–2216). -/
theorem wp_periodic_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {T : ℝ}
    (hp : Function.Periodic f T) (k : ℕ) : Function.Periodic (iteratedDeriv k f) T := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact wp_periodic_deriv ((wp_contDiff_iteratedDeriv hf k).differentiable (by simp)) ih

/-- Every derivative multiplies Fourier coefficients by the same frequency factor (TT:2206–2216). -/
theorem wp_fourierCoeff_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * π)) (k : ℕ) (n : ℤ) :
    fourierCoeff (iteratedDeriv k f) n = (I * n) ^ k * fourierCoeff f n := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
      rw [iteratedDeriv_succ, wp_fourierCoeff_deriv ((wp_contDiff_iteratedDeriv hf k).of_le (by simp))
        (wp_periodic_iteratedDeriv hf hp k), ih, pow_succ]
      ring

/-- Continuous functions have uniformly bounded Fourier coefficients on a period (TT:2206–2216). -/
theorem wp_fourierCoeff_bounded {f : ℝ → ℂ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ‖fourierCoeff f n‖ ≤ C := by
  obtain ⟨C, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * π)) hf.continuousOn
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  refine ⟨C, hC, fun n => ?_⟩
  have he := fourierCoeff_sum_sq_le hf hC hb {n}
  simp only [Finset.sum_singleton] at he
  nlinarith [norm_nonneg (fourierCoeff f n)]

/-- Smooth periodic functions have polynomial Fourier decay of every order (TT:2206–2216). -/
theorem wp_smooth_fourier_decay {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * π)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ k * ‖fourierCoeff f (n : ℤ)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := wp_fourierCoeff_bounded (wp_contDiff_iteratedDeriv hf k).continuous
  refine ⟨C, hC, fun n => ?_⟩
  have hh := hb (n : ℤ)
  rw [wp_fourierCoeff_iteratedDeriv hf hp] at hh
  simpa only [norm_mul, norm_pow, norm_I, one_mul, Int.cast_natCast, Complex.norm_natCast] using hh

/-- Cubically weighted absolute Fourier coefficients of a smooth periodic function are summable (TT:2206–2216). -/
theorem wp_smooth_fourier_cubic_summable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * π)) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ 3 * ‖fourierCoeff f (n + 2)‖) := by
  obtain ⟨C, hC, hb⟩ := wp_smooth_fourier_decay hf hp 6
  have hs : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 3) :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hs.mul_left C).of_nonneg_of_le (fun n => by positivity)
  intro n
  have hx : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  rw [mul_one_div]
  apply (le_div_iff₀ (pow_pos hx 3)).mpr
  convert hb (n + 2) using 1 <;> push_cast <;> ring


/-- The shifted cubic majorant needed to differentiate uPlus three times is summable (TT:2206–2216). -/
theorem wp_smooth_fourier_shifted_cubic_summable {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : Function.Periodic f (2 * π)) :
    Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ 3 * ‖fourierCoeff f (n + 1)‖) := by
  obtain ⟨C, hC, hb⟩ := wp_smooth_fourier_decay hf hp 6
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 3) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hs.mul_left (8 * C)).of_nonneg_of_le (fun n => by positivity)
  intro n
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hN : ((n + 2 : ℕ) : ℝ) ≤ 2 * x := by
    dsimp [x]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hpow : ((n + 2 : ℕ) : ℝ) ^ 3 ≤ 8 * x ^ 3 := by
    calc
      _ ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by positivity) hN 3
      _ = _ := by ring
  have hcoef : x ^ 6 * ‖fourierCoeff f (n + 1)‖ ≤ C := by
    simpa only [x, Nat.cast_add, Nat.cast_one] using hb (n + 1)
  rw [mul_one_div]
  apply (le_div_iff₀ (pow_pos hx 3)).mpr
  have hprod := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg (norm_nonneg (fourierCoeff f (n + 1))) (pow_nonneg hx.le 3))
  change ((n + 2 : ℕ) : ℝ) ^ 3 * ‖fourierCoeff f (n + 1)‖ * x ^ 3 ≤ 8 * C
  nlinarith [hprod, hcoef]

end TakhtajanTeo
