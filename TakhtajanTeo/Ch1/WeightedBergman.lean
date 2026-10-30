import TakhtajanTeo.Ch1.S2_HilbertManifold

/-!
# Weighted Bergman reproducing formula for `A₂` and the projector `P` (TT:548–551, TT:1864–1870)

* `A₂(D)` has the Hilbert norm `∬_D |φ|² ρ⁻¹ d²z`, `ρ⁻¹ = (1 - |z|²)²/4`.
  Its reproducing kernel is `(12/π)(1 - w z̄)⁻⁴` against `ρ⁻¹ d²z`, i.e.
  `φ(w) = (3/π) ∬_D φ(z) (1 - |z|²)² (1 - w z̄)⁻⁴ d²z` on `D = 𝔻` and on `D = 𝔻*`.
* `P μ (z) = (3 (1 - |z|²)²/π) ∬_{𝔻*} μ(ζ) (1 - ζ z̄)⁻⁴ d²ζ` is the orthogonal projection of `L²(𝔻*, ρ⁻¹ d²z)` onto `A₂(𝔻*)`
  (via `f = ρ ar μ`), proved through the Hilbert structure of `A₂` and the reproducing formula.

The disk formula duplicates `wp_bergman_reproduce` (S4_Metrics, lean6), which cannot be imported here (S4 is downstream).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real InnerProductSpace

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-! ## Reproducing formula on the disk and on the exterior -/

/-! ### Proof of the disk formula (monomials → polynomials → closed disk → `A₂(𝔻)`) -/

/-- Orthogonality of monomials for the weight `ρ⁻¹` on the disk. -/
theorem wb_monomial_orthogonal {n m : ℕ} (h : n ≠ m) :
    ∫ z in unitDisc, z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ) = 0 := by
  set F : ℂ → ℂ := fun z => z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ) with hFdef
  have hd : ((n : ℝ) - m) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
  set α : ℝ := π / ((n : ℝ) - m) with hα
  set u : Circle := Circle.exp α with hu
  have hucoe : (u : ℂ) = Complex.exp (α * I) := by simp [hu, Circle.coe_exp]
  have hnorm : ‖(u : ℂ)‖ = 1 := by simp
  have hprod : (u : ℂ) ^ n * conj (u : ℂ) ^ m = -1 := by
    rw [hucoe, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : (n : ℂ) * (α * I) + (m : ℂ) * conj (α * I) = ((π : ℝ) : ℂ) * I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      have hα' : (α : ℂ) * ((n : ℂ) - m) = π := by
        rw [hα]; push_cast
        field_simp [show ((n : ℂ) - m) ≠ 0 from by exact_mod_cast hd]
      linear_combination I * hα'
    rw [this, Complex.exp_pi_mul_I]
  have hrho (z : ℂ) : rho ((u : ℂ) * z) = rho z := by simp [rho, hnorm]
  have hF (z : ℂ) : F ((u : ℂ) * z) = -F z := by
    simp only [hFdef, mul_pow, map_mul, hrho]
    calc (u : ℂ) ^ n * z ^ n * (conj (u : ℂ) ^ m * conj z ^ m) * (((rho z)⁻¹ : ℝ) : ℂ)
        = ((u : ℂ) ^ n * conj (u : ℂ) ^ m) * (z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hprod]; ring
  have hball (z : ℂ) : (u : ℂ) * z ∈ ball (0 : ℂ) 1 ↔ z ∈ ball (0 : ℂ) 1 := by
    simp [mem_ball, dist_zero_right, hnorm]
  have hI : ∫ z in ball (0 : ℂ) 1, F z = - ∫ z in ball (0 : ℂ) 1, F z := by
    rw [← integral_indicator measurableSet_ball]
    set G : ℂ → ℂ := (ball (0 : ℂ) 1).indicator F with hG
    have hGu (z : ℂ) : G ((u : ℂ) * z) = - G z := by
      by_cases hz : z ∈ ball (0 : ℂ) 1
      · rw [hG, indicator_of_mem ((hball z).mpr hz), indicator_of_mem hz, hF]
      · rw [hG, indicator_of_notMem (fun h => hz ((hball z).mp h)), indicator_of_notMem hz, neg_zero]
    have hmp : MeasurePreserving (fun z : ℂ => (u : ℂ) * z) volume volume := by
      have := (rotation u).measurePreserving
      exact this
    have hemb : MeasurableEmbedding (fun z : ℂ => (u : ℂ) * z) := (rotation u).toHomeomorph.measurableEmbedding
    calc ∫ z, G z = ∫ z, G ((u : ℂ) * z) := (hmp.integral_comp hemb G).symm
      _ = ∫ z, -G z := by simp only [hGu]
      _ = _ := integral_neg _
  have := eq_neg_iff_add_eq_zero.mp hI
  have h2 : (2 : ℂ) * ∫ z in ball (0 : ℂ) 1, F z = 0 := by linear_combination this
  have h3 : ∫ z in ball (0 : ℂ) 1, F z = 0 := by simpa using h2
  exact h3

/-- The diagonal pairing of monomials (`ρ⁻¹`-weighted). -/
theorem wb_monomial_diag (n : ℕ) :
    ∫ z in unitDisc, z ^ n * conj z ^ n * (((rho z)⁻¹ : ℝ) : ℂ) =
      ((π / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) : ℝ) : ℂ) := by
  rw [← bergman_monomial_area n, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← map_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Kernel expansion for a fixed point `w` of the disk: `(1 - w z̄)⁻⁴ = ∑ C(m+3,3) (w z̄)^m`, multiplied by
`z^n (1 - |z|²)²`, in terms of the monomial pairings. -/
theorem wb_kernel_hasSum {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => 4 * (((m + 3).choose 3 : ℕ) : ℂ) * w ^ m * (z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ)))
      (z ^ n * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) := by
  have hr : ‖w * conj z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 3 hr).mul_left (z ^ n * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ))
  convert h using 1
  · funext m
    have hρ : (((rho z)⁻¹ : ℝ) : ℂ) = (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / 4 := by
      simp only [rho, inv_div]; push_cast; ring
    rw [hρ, mul_pow]
    ring
  · norm_num
    ring

theorem wb_rhoInv_le {z : ℂ} (hz : ‖z‖ < 1) : (rho z)⁻¹ ≤ 1 / 4 := by
  simp only [rho, inv_div]
  have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
  linarith

/-- The weighted Bergman reproducing formula for monomials on the disk. -/
theorem wb_monomial_reproducing (n : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    w ^ n = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, z ^ n * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
  have hU : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hS : HasSum
      (fun m : ℕ => ∫ z in unitDisc, 4 * (((m + 3).choose 3 : ℕ) : ℂ) * w ^ m * (z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ)))
      (∫ z in unitDisc, z ^ n * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) := by
    refine hasSum_integral_of_dominated_convergence (fun m _ => (((m + 3).choose 3 : ℕ) : ℝ) * ‖w‖ ^ m) ?_ ?_ ?_ ?_ ?_
    · intro m
      refine Measurable.aestronglyMeasurable ?_
      unfold rho
      fun_prop
    · intro m
      filter_upwards [ae_restrict_mem hU] with z hz
      have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
      have hρ := wb_rhoInv_le hzn
      have hρ0 : 0 ≤ (rho z)⁻¹ := by
        simp only [rho, inv_div]; positivity
      have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
      simp only [norm_mul, norm_pow, Complex.norm_conj, h4, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0,
        Complex.norm_natCast]
      have hz1 : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hzn.le
      have hz2 : ‖z‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg z) hzn.le
      have hC : (0 : ℝ) ≤ ((m + 3).choose 3 : ℕ) * ‖w‖ ^ m := by positivity
      calc 4 * (((m + 3).choose 3 : ℕ) : ℝ) * ‖w‖ ^ m * (‖z‖ ^ n * ‖z‖ ^ m * (rho z)⁻¹)
          ≤ 4 * (((m + 3).choose 3 : ℕ) : ℝ) * ‖w‖ ^ m * (1 * 1 * (1 / 4)) := by
            gcongr
        _ = _ := by ring
    · filter_upwards with z
      have := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 3 (r := ‖w‖) (by simpa using hw)).summable
      simpa using this
    · exact integrableOn_const (measure_ball_lt_top (x := (0 : ℂ)) (r := 1)).ne
    · filter_upwards [ae_restrict_mem hU] with z hz
      exact wb_kernel_hasSum hw (by simpa [unitDisc] using hz) n
  have hval : (fun m : ℕ => ∫ z in unitDisc, 4 * (((m + 3).choose 3 : ℕ) : ℂ) * w ^ m *
      (z ^ n * conj z ^ m * (((rho z)⁻¹ : ℝ) : ℂ))) =
      fun m => if m = n then ((π / 3 : ℝ) : ℂ) * w ^ n else 0 := by
    funext m
    rw [integral_const_mul]
    by_cases h : m = n
    · subst h
      rw [wb_monomial_diag, if_pos rfl]
      have h6 := bergman_coefficient_eq_choose m
      have hc : (((m + 3).choose 3 : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) / 6 := by
        linear_combination h6 / 6
      have hP : 0 < ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) := by positivity
      have hreal : (4 : ℝ) * (((m + 3).choose 3 : ℕ) : ℝ) *
          (π / (2 * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)))) = π / 3 := by
        rw [hc]; field_simp; ring
      calc (4 : ℂ) * (((m + 3).choose 3 : ℕ) : ℂ) * w ^ m *
            ((π / (2 * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3))) : ℝ) : ℂ)
          = (((4 : ℝ) * (((m + 3).choose 3 : ℕ) : ℝ) *
            (π / (2 * (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)))) : ℝ) : ℂ) * w ^ m := by
            push_cast; ring
        _ = _ := by rw [hreal]
    · rw [if_neg h, wb_monomial_orthogonal (Ne.symm h), mul_zero]
  rw [hval] at hS
  have hS2 := hasSum_ite_eq n (((π / 3 : ℝ) : ℂ) * w ^ n)
  have heq := hS.unique hS2
  rw [heq]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem wb_kernel_lower {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) : 1 - ‖w‖ ≤ ‖1 - w * conj z‖ := by
  have h1 : ‖w * conj z‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have h2 := norm_sub_norm_le (1 : ℂ) (w * conj z)
  rw [norm_one] at h2
  linarith

/-- Integrability of the Bergman integrand for an a.e. strongly measurable `g` with
`‖g‖ (1 - |z|²)² ≤ M` on the disk. -/
theorem wb_kernel_integrable {g : ℂ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict unitDisc)) {M : ℝ}
    (hM : ∀ z ∈ unitDisc, ‖g z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ M) {w : ℂ} (hw : ‖w‖ < 1) :
    IntegrableOn (fun z => g z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDisc := by
  have hU : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hmeas : AEStronglyMeasurable (fun z => g z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4)
      (volume.restrict unitDisc) :=
    ((hg.aemeasurable.mul (by fun_prop)).div (by fun_prop)).aestronglyMeasurable
  refine Integrable.mono' (integrableOn_const (C := M / (1 - ‖w‖) ^ 4)
    (measure_ball_lt_top (x := (0 : ℂ)) (r := 1)).ne) hmeas ?_
  filter_upwards [ae_restrict_mem hU] with z hz
  have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hl := wb_kernel_lower hw hzn
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hpow : (1 - ‖w‖) ^ 4 ≤ ‖1 - w * conj z‖ ^ 4 := pow_le_pow_left₀ hpos.le hl 4
  have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  calc ‖g z‖ * (1 - ‖z‖ ^ 2) ^ 2 / ‖1 - w * conj z‖ ^ 4 ≤ M / ‖1 - w * conj z‖ ^ 4 := by
        gcongr; exact hM z hz
    _ ≤ M / (1 - ‖w‖) ^ 4 := by
        have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) h0).trans (hM z hz)
        exact div_le_div_of_nonneg_left hM0 (by positivity) hpow

/-- Dominated convergence for the Bergman integral. -/
theorem wb_rhs_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {gn : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (gn n) (volume.restrict unitDisc)) {M : ℝ}
    (hbound : ∀ᶠ n in l, ∀ z ∈ unitDisc, ‖gn n z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ M)
    (hlim : ∀ z ∈ unitDisc, Tendsto (fun n => gn n z) l (𝓝 (g z))) {w : ℂ} (hw : ‖w‖ < 1) :
    Tendsto (fun n => ∫ z in unitDisc, gn n z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) l
      (𝓝 (∫ z in unitDisc, g z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4)) := by
  have hU : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hpos : 0 < 1 - ‖w‖ := by linarith
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M / (1 - ‖w‖) ^ 4) ?_ ?_
    (integrableOn_const (measure_ball_lt_top (x := (0 : ℂ)) (r := 1)).ne) ?_
  · filter_upwards [hmeas] with n hn
    exact ((hn.aemeasurable.mul (by fun_prop)).div (by fun_prop)).aestronglyMeasurable
  · filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem hU] with z hz
    have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have hl := wb_kernel_lower hw hzn
    have hpow : (1 - ‖w‖) ^ 4 ≤ ‖1 - w * conj z‖ ^ 4 := pow_le_pow_left₀ hpos.le hl 4
    have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    have := hn z hz
    calc ‖gn n z‖ * (1 - ‖z‖ ^ 2) ^ 2 / ‖1 - w * conj z‖ ^ 4 ≤ M / ‖1 - w * conj z‖ ^ 4 := by
          gcongr
      _ ≤ M / (1 - ‖w‖) ^ 4 := by
          have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) h0).trans this
          exact div_le_div_of_nonneg_left hM0 (by positivity) hpow
  · filter_upwards [ae_restrict_mem hU] with z hz
    have hne : (1 - w * conj z) ^ 4 ≠ 0 := by
      have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
      have hl := wb_kernel_lower hw hzn
      have : 0 < ‖1 - w * conj z‖ := lt_of_lt_of_le hpos hl
      exact pow_ne_zero _ (norm_pos_iff.mp this)
    exact ((hlim z hz).mul_const _).div_const _

theorem wb_poly_reproducing (p : Polynomial ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    p.eval w = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, p.eval z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
  have hint (k : ℕ) : IntegrableOn (fun z : ℂ => z ^ k * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4)
      unitDisc := by
    refine wb_kernel_integrable (M := 1) (continuous_pow k).aestronglyMeasurable ?_ hw
    intro z hz
    have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h1 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [norm_pow]
    calc ‖z‖ ^ k * (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg z) hzn.le
      _ = 1 := by ring
  have hexp : (fun z : ℂ => p.eval z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) =
      fun z => ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * (z ^ k * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) := by
    funext z
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, integral_finset_sum _ (fun k _ => (hint k).const_mul _), Finset.mul_sum, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, mul_left_comm, ← wb_monomial_reproducing k hw]

/-- Reproducing formula for functions holomorphic on a larger closed disk. -/
theorem wb_closedBall_reproducing {R : ℝ} (hR : 1 < R) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {w : ℂ} (hw : ‖w‖ < 1) :
    f w = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, f z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
  obtain ⟨p, hU⟩ := holomorphic_polynomial_approx_closedBall hR hf
  have hsub : closedBall (0 : ℂ) 1 ⊆ closedBall 0 R := closedBall_subset_closedBall hR.le
  have hfc : ContinuousOn f (closedBall 0 1) := hf.continuousOn.mono hsub
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hfc
  have hwb : w ∈ closedBall (0 : ℂ) 1 := by simp [mem_closedBall, hw.le]
  have h1 : Tendsto (fun n => (p n).eval w) atTop (𝓝 (f w)) := hU.tendsto_at hwb
  have hdisc : ∀ z ∈ unitDisc, z ∈ closedBall (0 : ℂ) 1 := fun z hz => ball_subset_closedBall hz
  have h2 := wb_rhs_tendsto (l := atTop) (gn := fun n z => (p n).eval z) (g := f) (M := B + 1)
    (Eventually.of_forall fun n => (Polynomial.continuous _).aestronglyMeasurable)
    (by
      have := (Metric.tendstoUniformlyOn_iff.mp hU) 1 one_pos
      filter_upwards [this] with n hn z hz
      have hd := hn z (hdisc z hz)
      rw [dist_eq_norm] at hd
      have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
      have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
      have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      have h1' : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := pow_le_one₀ (by nlinarith [norm_nonneg z]) (by nlinarith [norm_nonneg z])
      have hfz := hB z (hdisc z hz)
      have hB0 : 0 ≤ B := (norm_nonneg _).trans hfz
      have : ‖(p n).eval z‖ ≤ B + 1 := by
        have := norm_sub_norm_le ((p n).eval z) (f z)
        rw [norm_sub_rev] at hd
        linarith
      calc ‖(p n).eval z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ (B + 1) * 1 := mul_le_mul this h1' h0 (by linarith)
        _ = B + 1 := by ring)
    (fun z hz => hU.tendsto_at (hdisc z hz)) hw
  have h3 := h2.const_mul (((3 / π : ℝ) : ℂ))
  have h4 : (fun n => ((3 / π : ℝ) : ℂ) * ∫ z in unitDisc, (p n).eval z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
      (1 - w * conj z) ^ 4) = fun n => (p n).eval w := by
    funext n; exact (wb_poly_reproducing (p n) hw).symm
  rw [h4] at h3
  exact tendsto_nhds_unique h1 h3

/-- Pointwise growth bound for `A₂(𝔻)`: `‖φ z‖ (1 - |z|²)² ≤ C`. -/
theorem wb_A2_bound {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) :
    ∃ C : ℝ, ∀ z ∈ unitDisc, ‖φ z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ C := by
  refine ⟨Real.sqrt ((12 / π) * ∫ u in unitDisc, ‖φ u‖ ^ 2 * (rho u)⁻¹), fun z hz => ?_⟩
  have h := A2fun.disk_weighted_evaluation_sq hφ hz
  have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
  refine Real.le_sqrt_of_sq_le ?_
  calc (‖φ z‖ * (1 - ‖z‖ ^ 2) ^ 2) ^ 2 = (1 - ‖z‖ ^ 2) ^ 4 * ‖φ z‖ ^ 2 := by ring
    _ ≤ _ := h

theorem wb_A2_integrable {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    IntegrableOn (fun z => φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDisc := by
  obtain ⟨C, hC⟩ := wb_A2_bound hφ
  exact wb_kernel_integrable (hφ.1.continuousOn.aestronglyMeasurable measurableSet_ball) hC
    (by simpa [unitDisc] using hw)

/-- The weighted Bergman reproducing formula for `A∞(𝔻)`: holomorphic `φ` with `‖φ z‖ (1 - |z|²)² ≤ C`. -/
theorem wb_Ainf_reproducing {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {C : ℝ}
    (hC : ∀ z ∈ unitDisc, ‖φ z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ C) {w : ℂ} (hw : w ∈ unitDisc) :
    φ w = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
  have hwn : ‖w‖ < 1 := by simpa [unitDisc] using hw
  have hU : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hs : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s ∧ s < 1 := by
    have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
    have h2 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h1, h2] with s a b using ⟨b, a⟩
  have hmem (s : ℝ) (hs1 : s < 1) (hs0 : 0 < s) (z : ℂ) (hz : z ∈ unitDisc) : (s : ℂ) * z ∈ unitDisc := by
    have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
    simp only [unitDisc, mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [norm_nonneg z]
  -- the dilated formula
  have hdil : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), φ ((s : ℂ) * w) = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, φ ((s : ℂ) * z) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
    filter_upwards [hs] with s ⟨hs0, hs1⟩
    obtain ⟨R, hR, hfs⟩ := holomorphic_inward_dilate hφ hs0 hs1
    exact wb_closedBall_reproducing hR hfs hwn
  have hlim := wb_rhs_tendsto (l := 𝓝[<] (1 : ℝ)) (gn := fun s z => φ ((s : ℂ) * z)) (g := φ) (M := C)
    (w := w)
    (by
      filter_upwards [hs] with s ⟨hs0, hs1⟩
      refine ContinuousOn.aestronglyMeasurable ?_ hU
      exact hφ.continuousOn.comp (by fun_prop) (fun z hz => hmem s hs1 hs0 z hz))
    (by
      filter_upwards [hs] with s ⟨hs0, hs1⟩ z hz
      have hsz := hC _ (hmem s hs1 hs0 z hz)
      have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz
      have hnorm : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      have hle : ‖(s : ℂ) * z‖ ≤ ‖z‖ := by
        rw [hnorm]; nlinarith [norm_nonneg z]
      have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      have hd : 1 - ‖z‖ ^ 2 ≤ 1 - ‖(s : ℂ) * z‖ ^ 2 := by
        nlinarith [norm_nonneg z, norm_nonneg ((s : ℂ) * z)]
      have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by linarith
      calc ‖φ ((s : ℂ) * z)‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ ‖φ ((s : ℂ) * z)‖ * (1 - ‖(s : ℂ) * z‖ ^ 2) ^ 2 := by
            gcongr
        _ ≤ C := hsz)
    (fun z hz => by
      have hc : ContinuousAt φ z := hφ.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
      have harg₀ : Tendsto (fun s : ℝ => (s : ℂ) * z) (𝓝 1) (𝓝 z) := by
        simpa only [Complex.ofReal_one, one_mul] using (continuous_ofReal.mul_const z).tendsto 1
      exact hc.tendsto.comp (harg₀.mono_left nhdsWithin_le_nhds)) hwn
  have hl1 : Tendsto (fun s : ℝ => φ ((s : ℂ) * w)) (𝓝[<] (1 : ℝ)) (𝓝 (φ w)) := by
    have hc : ContinuousAt φ w := hφ.continuousOn.continuousAt (isOpen_ball.mem_nhds hw)
    have harg₀ : Tendsto (fun s : ℝ => (s : ℂ) * w) (𝓝 1) (𝓝 w) := by
      simpa only [Complex.ofReal_one, one_mul] using (continuous_ofReal.mul_const w).tendsto 1
    exact hc.tendsto.comp (harg₀.mono_left nhdsWithin_le_nhds)
  have hl2 := hlim.const_mul (((3 / π : ℝ) : ℂ))
  exact tendsto_nhds_unique (hl1.congr' hdil) hl2

/-- The weighted Bergman reproducing formula for `A₂(𝔻)`. -/
theorem wb_A2_reproducing {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    φ w = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDisc, φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 :=
  wb_Ainf_reproducing hφ.1 (wb_A2_bound hφ).choose_spec hw

theorem weightedBergman_integrableOn_disc {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    IntegrableOn (fun z => φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDisc :=
  wb_A2_integrable hφ hw

/-- The Bergman reproducing formula for `A₂(𝔻)` (kernel `(12/π)(1 - w z̄)⁻⁴` against `ρ⁻¹ d²z`). -/
theorem weightedBergman_reproducing_disc {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDisc) {w : ℂ} (hw : w ∈ unitDisc) :
    φ w = ((3 / π : ℝ) : ℂ) * ∫ z in unitDisc, φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 :=
  wb_A2_reproducing hφ hw

/-! ### Proof of the exterior formula (inversion `z ↦ 1/z`) -/

/-- Pointwise algebra of the inversion `z ↦ 1/z` for the Bergman integrand. -/
theorem wb_ext_pointwise {ψ : ℂ → ℂ} {z v : ℂ} (hz : z ≠ 0) (hv : v ≠ 0) (hvz : 1 - v * conj z ≠ 0) :
    ‖deriv (fun x : ℂ => x⁻¹) z‖ ^ 2 • (ψ z⁻¹ * (((1 - ‖z⁻¹‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
        (1 - v⁻¹ * conj z⁻¹) ^ 4) =
      v ^ 4 * ((ψ z⁻¹ / z ^ 4) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - v * conj z) ^ 4) := by
  have hz' : conj z ≠ 0 := by simpa using hz
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  have hzz : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
    rw [Complex.mul_conj']
  have hd : deriv (fun x : ℂ => x⁻¹) z = -(z ^ 2)⁻¹ := by
    rw [(hasDerivAt_inv hz).deriv]
  have hnorm2 : ‖deriv (fun x : ℂ => x⁻¹) z‖ ^ 2 = ((‖z‖ : ℝ) ^ 4)⁻¹ := by
    rw [hd, norm_neg, norm_inv, norm_pow]; field_simp
  have hinv : ‖z⁻¹‖ = (‖z‖)⁻¹ := norm_inv z
  have h1 : 1 - v⁻¹ * conj z⁻¹ ≠ 0 := by
    rw [map_inv₀]
    intro h
    apply hvz
    field_simp at h
    linear_combination -h
  rw [hnorm2, hinv, Complex.real_smul]
  push_cast
  rw [map_inv₀] at *
  field_simp
  have h8 : ((‖z‖ : ℝ) : ℂ) ^ 8 = (z * conj z) ^ 4 := by rw [← hzz]; ring
  rw [show (v * conj z - 1) ^ 4 = (1 - v * conj z) ^ 4 by ring, h8, hzz]
  have h4 : (1 - v * conj z) ^ 4 ≠ 0 := pow_ne_zero _ hvz
  have hvz' : 1 - conj z * v ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- Common setup of the inversion `z ↦ 1/z` for the exterior Bergman formula. -/
theorem wb_ext_change {ψ : ℂ → ℂ} {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (∫ z in unitDiscExterior, ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) =
      ∫ z in unitDisc \ {0}, w⁻¹ ^ 4 * ((ψ z⁻¹ / z ^ 4) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
        (1 - w⁻¹ * conj z) ^ 4) ∧
    (IntegrableOn (fun z => ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDiscExterior ↔
      IntegrableOn (fun z => w⁻¹ ^ 4 * ((ψ z⁻¹ / z ^ 4) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
        (1 - w⁻¹ * conj z) ^ 4)) (unitDisc \ {0})) := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hwn : 1 < ‖w‖ := by simpa [unitDiscExterior] using hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwn; linarith
  have hv : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn
  have hpt : ∀ z ∈ unitDisc \ {0}, ‖deriv (fun x : ℂ => x⁻¹) z‖ ^ 2 •
      (ψ z⁻¹ * (((1 - ‖z⁻¹‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z⁻¹) ^ 4) =
      w⁻¹ ^ 4 * ((ψ z⁻¹ / z ^ 4) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4) := by
    intro z hz
    have hzn : ‖z‖ < 1 := by simpa [unitDisc] using hz.1
    have hz0 : z ≠ 0 := hz.2
    have hvz : 1 - w⁻¹ * conj z ≠ 0 := by
      intro h
      have h1 : w⁻¹ * conj z = 1 := by linear_combination -h
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      nlinarith [norm_nonneg z, norm_nonneg w⁻¹]
    have := wb_ext_pointwise (ψ := ψ) hz0 (inv_ne_zero hw0) hvz
    rwa [inv_inv] at this
  have h1 := ahP_integral_image (f := fun z : ℂ => z⁻¹) hopen hc.1 hc.2.1
    (fun z => ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4)
  have h2 := ahP_integrableOn_image (f := fun z : ℂ => z⁻¹) hopen hc.1 hc.2.1
    (fun z => ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4)
  rw [hc.2.2] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact setIntegral_congr_fun hopen.measurableSet hpt
  · rw [h2]
    exact integrableOn_congr_fun hpt hopen.measurableSet

/-- The weighted Bergman reproducing formula on the exterior of the unit disk. -/
theorem wb_ext_reproducing {ψ : ℂ → ℂ} (hψ : ψ ∈ A2fun unitDiscExterior) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ψ w = ((3 / π : ℝ) : ℂ) *
      ∫ z in unitDiscExterior, ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hc := inversion_puncturedDisk_conformal
  have hwn : 1 < ‖w‖ := by simpa [unitDiscExterior] using hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwn; linarith
  have hv : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn
  have hvU : w⁻¹ ∈ unitDisc \ {0} := ⟨by simpa [unitDisc] using hv, inv_ne_zero hw0⟩
  obtain ⟨phi_inv, hphi_inv, heq, -⟩ := exists_inverted_A2 hψ
  have hrep := wb_A2_reproducing hphi_inv hvU.1
  have hnull : (unitDisc \ {0} : Set ℂ) =ᵐ[volume] unitDisc := diff_null_ae_eq_self (by simp)
  have hint : ∫ z in unitDisc \ {0}, phi_inv z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4 =
      ∫ z in unitDisc, phi_inv z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4 :=
    setIntegral_congr_set hnull
  obtain ⟨h1, -⟩ := wb_ext_change (ψ := ψ) hw
  have h3 : ∫ z in unitDisc \ {0}, w⁻¹ ^ 4 * ((ψ z⁻¹ / z ^ 4) * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
        (1 - w⁻¹ * conj z) ^ 4) =
      w⁻¹ ^ 4 * ∫ z in unitDisc \ {0}, phi_inv z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hopen.measurableSet fun z hz => ?_
    rw [heq hz]
  have hφv : phi_inv w⁻¹ = ψ w / w⁻¹ ^ 4 := by
    rw [heq hvU]; simp [inv_inv]
  rw [h1, h3, hint]
  have hI : ∫ z in unitDisc, phi_inv z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4 =
      ((π / 3 : ℝ) : ℂ) * phi_inv w⁻¹ := by
    set I := ∫ z in unitDisc, phi_inv z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w⁻¹ * conj z) ^ 4 with hIdef
    have hone : ((π / 3 : ℝ) : ℂ) * ((3 / π : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have : π / 3 * (3 / π) = 1 := by field_simp
      rw [this]; simp
    calc I = (((π / 3 : ℝ) : ℂ) * ((3 / π : ℝ) : ℂ)) * I := by rw [hone, one_mul]
      _ = ((π / 3 : ℝ) : ℂ) * (((3 / π : ℝ) : ℂ) * I) := by ring
      _ = _ := by rw [← hrep]
  rw [hI, hφv]
  have hv0 : w⁻¹ ≠ 0 := inv_ne_zero hw0
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem wb_ext_integrable {ψ : ℂ → ℂ} (hψ : ψ ∈ A2fun unitDiscExterior) {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IntegrableOn (fun z => ψ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDiscExterior := by
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hwn : 1 < ‖w‖ := by simpa [unitDiscExterior] using hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwn; linarith
  have hv : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwn
  have hvU : w⁻¹ ∈ unitDisc := by simpa [unitDisc] using hv
  obtain ⟨phi_inv, hphi_inv, heq, -⟩ := exists_inverted_A2 hψ
  obtain ⟨-, h2⟩ := wb_ext_change (ψ := ψ) hw
  rw [h2]
  have := ((wb_A2_integrable hphi_inv hvU).mono_set (show (unitDisc \ {0} : Set ℂ) ⊆ unitDisc from Set.diff_subset)).const_mul (w⁻¹ ^ 4)
  exact (integrableOn_congr_fun (fun z hz => by simp only [heq hz]) hopen.measurableSet).mp this

theorem weightedBergman_integrableOn_exterior {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) {w : ℂ}
    (hw : w ∈ unitDiscExterior) :
    IntegrableOn (fun z => φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) unitDiscExterior :=
  wb_ext_integrable hφ hw

/-- The same formula on `𝔻*` (by `z ↦ 1/z`). -/
theorem weightedBergman_reproducing_exterior {φ : ℂ → ℂ} (hφ : φ ∈ A2fun unitDiscExterior) {w : ℂ}
    (hw : w ∈ unitDiscExterior) :
    φ w = ((3 / π : ℝ) : ℂ) * ∫ z in unitDiscExterior, φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4 :=
  wb_ext_reproducing hφ hw

/-! ## The projector `P` as the orthogonal projection onto `A₂(𝔻*)` -/

/-- Conversion of the `L²(ρ⁻¹ d²z)` inner product into a Lebesgue integral. -/
theorem wb_inner_eq {D : Set ℂ} (a b : Lp ℂ 2 (rhoInvMeasure D)) {a' b' : ℂ → ℂ}
    (ha : a =ᵐ[rhoInvMeasure D] a') (hb : b =ᵐ[rhoInvMeasure D] b') :
    ⟪a, b⟫_ℂ = ∫ z in D, (((rho z)⁻¹ : ℝ) : ℂ) * (conj (a' z) * b' z) := by
  rw [L2.inner_def]
  have h1 : ∫ z, ⟪a z, b z⟫_ℂ ∂(rhoInvMeasure D) = ∫ z, ⟪a' z, b' z⟫_ℂ ∂(rhoInvMeasure D) := by
    refine integral_congr_ae ?_
    filter_upwards [ha, hb] with z hza hzb
    rw [hza, hzb]
  rw [h1]
  unfold rhoInvMeasure
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)⁻¹) := by
    unfold rho; fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have h0 : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
  simp only [ENNReal.toReal_ofReal h0, Complex.real_smul]
  rw [RCLike.inner_apply]
  ring

/-- The reproducing kernel `e_w(z) = (12/π)(1 - w̄ z)⁻⁴` of `A₂(𝔻*)` (w.r.t. `ρ⁻¹ d²z`). -/
theorem wb_ew_differentiable {w : ℂ} (hw : w ∈ unitDiscExterior) :
    DifferentiableOn ℂ (fun z : ℂ => ((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) unitDiscExterior := by
  have hwn : 1 < ‖w‖ := by simpa [unitDiscExterior] using hw
  intro z hz
  have hzn : 1 < ‖z‖ := by simpa [unitDiscExterior] using hz
  have hne : 1 - conj w * z ≠ 0 := by
    intro h
    have h1 : conj w * z = 1 := by linear_combination -h
    have := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    nlinarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 - conj w * z) z :=
    (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)
  exact ((differentiableAt_const _).div (h1.pow 4) (pow_ne_zero _ hne)).differentiableWithinAt

theorem wb_ew_bound {w z : ℂ} (hwn : 1 < ‖w‖) (hzn : 1 < ‖z‖) :
    ‖((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4‖ ^ 2 * (rho z)⁻¹ ≤
      ((12 / π) ^ 2 / (4 * (‖w‖ - 1) ^ 8)) * (16 * (1 + ‖z‖) ^ (-(4 : ℝ))) := by
  have hδ : 0 < ‖w‖ - 1 := by linarith
  have hlow : (‖w‖ - 1) * ‖z‖ ≤ ‖1 - conj w * z‖ := by
    have h := norm_sub_norm_le (conj w * z) 1
    rw [norm_mul, Complex.norm_conj, norm_one] at h
    rw [norm_sub_rev]
    nlinarith
  have hz0 : 0 < ‖z‖ := by linarith
  have hpos : 0 < (‖w‖ - 1) * ‖z‖ := by positivity
  have hρ : (rho z)⁻¹ ≤ ‖z‖ ^ 4 / 4 := by
    simp only [rho, inv_div]
    have h0 : 0 ≤ ‖z‖ ^ 2 - 1 := by nlinarith
    have : (1 - ‖z‖ ^ 2) ^ 2 ≤ ‖z‖ ^ 4 := by nlinarith
    linarith
  have hρ0 : 0 ≤ (rho z)⁻¹ := by unfold rho; positivity
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hq : ((‖w‖ - 1) * ‖z‖) ^ 4 ≤ ‖1 - conj w * z‖ ^ 4 := pow_le_pow_left₀ hpos.le hlow 4
  have h1 : (12 / π / ‖1 - conj w * z‖ ^ 4) ^ 2 ≤ (12 / π / ((‖w‖ - 1) * ‖z‖) ^ 4) ^ 2 := by
    gcongr
  have h2 : (1 + ‖z‖) ^ (-(4 : ℝ)) = ((1 + ‖z‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h3 : (1 + ‖z‖) ≤ 2 * ‖z‖ := by linarith
  calc (12 / π / ‖1 - conj w * z‖ ^ 4) ^ 2 * (rho z)⁻¹
      ≤ (12 / π / ((‖w‖ - 1) * ‖z‖) ^ 4) ^ 2 * (‖z‖ ^ 4 / 4) := by gcongr
    _ = (12 / π) ^ 2 / (4 * (‖w‖ - 1) ^ 8) * ‖z‖⁻¹ ^ 4 := by
        field_simp
    _ ≤ (12 / π) ^ 2 / (4 * (‖w‖ - 1) ^ 8) * (16 * ((1 + ‖z‖) ^ 4)⁻¹) := by
        gcongr
        have h4 : (1 + ‖z‖) ^ 4 ≤ (2 * ‖z‖) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
        rw [inv_pow, ← inv_pow]
        have : ((2 * ‖z‖) ^ 4)⁻¹ ≤ ((1 + ‖z‖) ^ 4)⁻¹ := inv_anti₀ (by positivity) h4
        calc ‖z‖⁻¹ ^ 4 = 16 * ((2 * ‖z‖) ^ 4)⁻¹ := by field_simp <;> ring
          _ ≤ _ := by gcongr
    _ = _ := by rw [h2]

theorem wb_ew_mem {w : ℂ} (hw : w ∈ unitDiscExterior) :
    (fun z : ℂ => ((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) ∈ A2fun unitDiscExterior := by
  have hwn : 1 < ‖w‖ := by simpa [unitDiscExterior] using hw
  refine ⟨wb_ew_differentiable hw, ?_⟩
  unfold normA2
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hint : IntegrableOn (fun z : ℂ => ((12 / π) ^ 2 / (4 * (‖w‖ - 1) ^ 8)) * (16 * (1 + ‖z‖) ^ (-(4 : ℝ))))
      unitDiscExterior := by
    have hfin : (Module.finrank ℝ ℂ : ℝ) < 4 := by simp; norm_num
    exact ((integrable_one_add_norm (μ := volume) hfin).const_mul 16 |>.const_mul _).integrableOn
  have hlt := hint.integrable.lintegral_lt_top
  refine ne_of_lt (lt_of_le_of_lt ?_ hlt)
  refine setLIntegral_mono' resolvent_exterior_isOpen.measurableSet fun z hz => ?_
  have hzn : 1 < ‖z‖ := by simpa [unitDiscExterior] using hz
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using wb_ew_bound hwn hzn

theorem wb_ext_circle : ∀ z ∈ unitDiscExterior, ‖z‖ ≠ 1 := by
  intro z hz
  have : 1 < ‖z‖ := by simpa [unitDiscExterior] using hz
  exact ne_of_gt this

/-- The Bergman projection as an orthogonal projection in `L²(𝔻*, ρ⁻¹ d²z)`: for every `L²` function `f` there is
`φ ∈ A₂(𝔻*)` with `f - φ ⊥ A₂(𝔻*)`, and `φ(w) = ⟨e_w, f⟩ = ∬ ρ⁻¹ \overline{e_w} f`. -/
theorem wb_proj_exists {f : ℂ → ℂ} (hf : MemLp f 2 (rhoInvMeasure unitDiscExterior)) :
    ∃ φ ∈ A2fun unitDiscExterior,
      (∀ ψ ∈ A2fun unitDiscExterior,
        ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) * (conj (ψ z) * (f z - φ z)) = 0) ∧
      ∀ w ∈ unitDiscExterior, φ w = ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
        (conj (((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) * f z) := by
  have hO : IsOpen unitDiscExterior := resolvent_exterior_isOpen
  set K := A2 unitDiscExterior with hK
  set fL : Lp ℂ 2 (rhoInvMeasure unitDiscExterior) := hf.toLp f with hfL
  set P : K := ⟨K.starProjection fL, K.starProjection_apply_mem fL⟩ with hP
  set φ : ℂ → ℂ := A2.toFun P with hφdef
  have hφ : φ ∈ A2fun unitDiscExterior := A2.toFun_mem P
  have hfae : fL =ᵐ[rhoInvMeasure unitDiscExterior] f := hf.coeFn_toLp
  have hφae : (P : Lp ℂ 2 (rhoInvMeasure unitDiscExterior)) =ᵐ[rhoInvMeasure unitDiscExterior] φ :=
    (A2.toFun_spec P).2
  have hker : ∀ k : K, ⟪(k : Lp ℂ 2 (rhoInvMeasure unitDiscExterior)), fL - (P : Lp ℂ 2 (rhoInvMeasure unitDiscExterior))⟫_ℂ = 0 :=
    fun k => Submodule.inner_right_of_mem_orthogonal k.2 (Submodule.sub_starProjection_mem_orthogonal fL)
  have hsub : (fL - (P : Lp ℂ 2 (rhoInvMeasure unitDiscExterior))) =ᵐ[rhoInvMeasure unitDiscExterior]
      (fun z => f z - φ z) := by
    filter_upwards [Lp.coeFn_sub fL (P : Lp ℂ 2 (rhoInvMeasure unitDiscExterior)), hfae, hφae] with z h1 h2 h3
    rw [h1]; simp only [Pi.sub_apply, h2, h3]
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨kψ, hkψ⟩ := exists_A2_representative hO wb_ext_circle hψ
    have h := hker kψ
    rw [wb_inner_eq (a' := A2.toFun kψ) _ _ (A2.toFun_spec kψ).2 hsub] at h
    rw [← h]
    refine setIntegral_congr_fun hO.measurableSet fun z hz => ?_
    simp only [hkψ hz]
  · intro w hw
    obtain ⟨kw, hkw⟩ := exists_A2_representative hO wb_ext_circle (wb_ew_mem hw)
    have h := hker kw
    rw [inner_sub_right, sub_eq_zero] at h
    rw [wb_inner_eq (a' := A2.toFun kw) _ _ (A2.toFun_spec kw).2 hfae,
      wb_inner_eq (a' := A2.toFun kw) _ _ (A2.toFun_spec kw).2 hφae] at h
    have hrep := wb_ext_reproducing hφ hw
    have halg : ∀ z ∈ unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
        (conj (((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) * φ z) =
        ((3 / π : ℝ) : ℂ) * (φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) / (1 - w * conj z) ^ 4) := by
      intro z hz
      simp only [rho, inv_div, map_div₀, Complex.conj_ofReal, map_pow, map_sub, map_one, map_mul,
        Complex.conj_conj]
      push_cast
      ring
    calc φ w = ((3 / π : ℝ) : ℂ) * ∫ z in unitDiscExterior, φ z * (((1 - ‖z‖ ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) /
          (1 - w * conj z) ^ 4 := hrep
      _ = ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
          (conj (((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) * φ z) := by
        rw [← integral_const_mul]
        exact (setIntegral_congr_fun hO.measurableSet fun z hz => (halg z hz).symm)
      _ = _ := by
        have e1 : ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
            (conj (A2.toFun kw z) * φ z) = ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
            (conj (((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) * φ z) :=
          setIntegral_congr_fun hO.measurableSet fun z hz => by simp only [hkw hz]
        have e2 : ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
            (conj (A2.toFun kw z) * f z) = ∫ z in unitDiscExterior, (((rho z)⁻¹ : ℝ) : ℂ) *
            (conj (((12 / π : ℝ) : ℂ) / (1 - conj w * z) ^ 4) * f z) :=
          setIntegral_congr_fun hO.measurableSet fun z hz => by simp only [hkw hz]
        rw [← e1, ← e2, h] 

theorem wb_harmonicProj_orthogonal (μ : LinfStar) (hμ : normL2 unitDiscExterior μ < ∞) :
    (⇑(harmonicProj μ) : ℂ → ℂ) ∈ {ν | ∃ ν' ∈ harmonicL2 unitDiscExterior, ν =ᵐ[volume.restrict unitDiscExterior] ν'} ∧
      ∀ ν ∈ harmonicL2 unitDiscExterior,
        ∫ z in unitDiscExterior, (μ z - harmonicProj μ z) * conj (ν z) * rho z = 0 := by
  have hO : IsOpen unitDiscExterior := resolvent_exterior_isOpen
  have hrho : ∀ z ∈ unitDiscExterior, 0 < rho z := fun z hz => rho_pos_of_norm_ne_one (wb_ext_circle z hz)
  -- the function `f = ρ ar μ` lies in `L²(ρ⁻¹ d²z)`
  set f : ℂ → ℂ := fun ζ => ((rho ζ : ℝ) : ℂ) * conj (μ ζ) with hfdef
  have hμrep : ∀ z ∈ unitDiscExterior, (μ z) = ((rho z : ℝ) : ℂ)⁻¹ * conj (f z) := by
    intro z hz
    have : (rho z : ℝ) ≠ 0 := (hrho z hz).ne'
    have hc : ((rho z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
    simp only [hfdef, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
  have hfm : AEStronglyMeasurable f (rhoInvMeasure unitDiscExterior) := by
    have h1 : AEStronglyMeasurable (fun ζ => conj (μ ζ)) (volume.restrict unitDiscExterior) :=
      continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable μ)
    have h2 : AEStronglyMeasurable f (volume.restrict unitDiscExterior) := by
      refine AEStronglyMeasurable.mul ?_ h1
      refine Measurable.aestronglyMeasurable ?_
      unfold rho; fun_prop
    exact h2.mono_ac (withDensity_absolutelyContinuous _ _)
  have hnorm : normA2 unitDiscExterior f = normL2 unitDiscExterior μ :=
    normA2_eq_normL2_of_harmonic hO.measurableSet wb_ext_circle (fun z hz => by
      have := hμrep z hz
      simpa using this)
  have hf : MemLp f 2 (rhoInvMeasure unitDiscExterior) := by
    have h2 : eLpNorm f 2 (rhoInvMeasure unitDiscExterior) < ∞ := by
      rw [← normA2_eq_eLpNorm _ _ hfm, hnorm]; exact hμ
    change eLpNorm f 2 (rhoInvMeasure unitDiscExterior) < ∞
    exact h2
  obtain ⟨φ, hφ, horth, hrepr⟩ := wb_proj_exists hf
  set F : ℂ → ℂ := fun z => 3 * (1 - ‖z‖ ^ 2) ^ 2 / π * ∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4 with hF
  have hFφ : ∀ z ∈ unitDiscExterior, F z = ((rho z : ℝ) : ℂ)⁻¹ * conj (φ z) := by
    intro z hz
    have hzn : 1 < ‖z‖ := by simpa [unitDiscExterior] using hz
    have hconj : conj (φ z) = ((12 / π : ℝ) : ℂ) * ∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4 := by
      rw [hrepr z hz, ← integral_conj]
      have hint : ∀ ζ ∈ unitDiscExterior, conj ((((rho ζ)⁻¹ : ℝ) : ℂ) *
          (conj (((12 / π : ℝ) : ℂ) / (1 - conj z * ζ) ^ 4) * f ζ)) =
          ((12 / π : ℝ) : ℂ) * (μ ζ / (1 - ζ * conj z) ^ 4) := by
        intro ζ hζ
        have hζn : 1 < ‖ζ‖ := by simpa [unitDiscExterior] using hζ
        have h0 : (rho ζ : ℝ) ≠ 0 := (hrho ζ hζ).ne'
        have hc : ((rho ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
        have hD : 1 - ζ * conj z ≠ 0 := by
          intro h
          have h1 : ζ * conj z = 1 := by linear_combination -h
          have := congrArg norm h1
          rw [norm_mul, Complex.norm_conj, norm_one] at this
          nlinarith
        have hD' : 1 - z * conj ζ ≠ 0 := by
          intro h
          have h1 : z * conj ζ = 1 := by linear_combination -h
          have := congrArg norm h1
          rw [norm_mul, Complex.norm_conj, norm_one] at this
          nlinarith
        have hD'' : 1 - conj z * ζ ≠ 0 := by rwa [mul_comm]
        simp only [hfdef, map_mul, map_div₀, Complex.conj_ofReal, map_pow, map_sub, map_one, Complex.conj_conj]
        push_cast
        rw [show (1 - ζ * conj z) = (1 - conj z * ζ) by ring]
        field_simp
      rw [setIntegral_congr_fun hO.measurableSet hint, integral_const_mul]
    rw [hconj]
    simp only [hF]
    generalize (∫ ζ in unitDiscExterior, μ ζ / (1 - ζ * conj z) ^ 4) = I
    simp only [rho, inv_div]
    have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  -- boundedness
  have hbound : ∃ B : ℝ, ∀ z ∈ unitDiscExterior, ‖F z‖ ≤ B := by
    refine ⟨Real.sqrt (12 / π) * (normA2 unitDiscExterior φ).toReal / 4, fun z hz => ?_⟩
    have h := lemma_2_1_exterior hφ z hz
    have hfin : normA2 unitDiscExterior φ ≠ ⊤ := hφ.2.ne
    have h2 : (1 - ‖z‖ ^ 2) ^ 2 * ‖φ z‖ ≤ Real.sqrt (12 / π) * (normA2 unitDiscExterior φ).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
      rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
      exact this
    rw [hFφ z hz]
    have hr := hrho z hz
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_conj]
    simp only [rho, inv_div]
    nlinarith [norm_nonneg (φ z)]
  obtain ⟨B, hB⟩ := hbound
  have hFmeas : AEStronglyMeasurable F (volume.restrict unitDiscExterior) := by
    have : AEStronglyMeasurable (fun z => ((rho z : ℝ) : ℂ)⁻¹ * conj (φ z)) (volume.restrict unitDiscExterior) := by
      have hc : ContinuousOn (fun z => ((rho z : ℝ) : ℂ)⁻¹ * conj (φ z)) unitDiscExterior := by
        refine ContinuousOn.mul ?_ (continuous_conj.comp_continuousOn hφ.1.continuousOn)
        refine ContinuousOn.inv₀ ?_ (fun z hz => by exact_mod_cast (hrho z hz).ne')
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        unfold rho
        refine ContinuousOn.div continuousOn_const (by fun_prop) (fun z hz => ?_)
        have h1 : 1 < ‖z‖ := by simpa [unitDiscExterior] using hz
        exact pow_ne_zero 2 (fun h => by nlinarith)
      exact hc.aestronglyMeasurable hO.measurableSet
    refine this.congr ?_
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact (hFφ z hz).symm
  have hmem : MemLp F ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound hFmeas B (by
      filter_upwards [ae_restrict_mem hO.measurableSet] with z hz using hB z hz)
  have hproj : harmonicProj μ = hmem.toLp F := by
    unfold harmonicProj toLinf
    exact dif_pos hmem
  have hae : (⇑(harmonicProj μ) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] F := by
    rw [hproj]; exact hmem.coeFn_toLp
  have hFharm : F ∈ harmonicL2 unitDiscExterior := by
    refine ⟨φ, hφ.1, fun z hz => hFφ z hz, ?_⟩
    rw [← normA2_eq_normL2_of_harmonic hO.measurableSet wb_ext_circle (fun z hz => hFφ z hz)]
    exact hφ.2
  refine ⟨⟨F, hFharm, hae⟩, ?_⟩
  intro ν hν
  obtain ⟨ψ, hψd, hνrep, hν2⟩ := hν
  have hψ : ψ ∈ A2fun unitDiscExterior := by
    refine ⟨hψd, ?_⟩
    rw [normA2_eq_normL2_of_harmonic hO.measurableSet wb_ext_circle hνrep]; exact hν2
  have h0 := horth ψ hψ
  have hconj := congrArg conj h0
  rw [map_zero, ← integral_conj] at hconj
  rw [← hconj]
  have hcongr : (fun z => (μ z - (harmonicProj μ) z) * conj (ν z) * (rho z : ℂ)) =ᵐ[volume.restrict unitDiscExterior]
      fun z => conj ((((rho z)⁻¹ : ℝ) : ℂ) * (conj (ψ z) * (f z - φ z))) := by
    filter_upwards [hae, ae_restrict_mem hO.measurableSet] with z hz1 hz2
    have hr : (rho z : ℝ) ≠ 0 := (hrho z hz2).ne'
    rw [hz1, hFφ z hz2, hνrep z hz2, hμrep z hz2]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_sub, Complex.conj_conj]
    push_cast
    field_simp
  exact integral_congr_ae hcongr

/-! ## The orthogonal projector (relocated from `S2_HilbertManifold`) -/

/-- (TT:1864–1870) On the Hilbert manifold, `P` (1.7) is the orthogonal projector of `L²(𝔻*, ρ d²z)` onto
`H^{-1,1}(𝔻*)`. For bounded `μ` with `‖μ‖₂ < ∞`:
- `Pμ ∈ H^{-1,1}(𝔻*)`;
- `μ - Pμ` is orthogonal to `H^{-1,1}(𝔻*)` in `L²(𝔻*, ρ d²z)`.

The vector field `∂/∂ε_ν`, `ν ∈ H^{-1,1}(𝔻*)`, is then given in Bers coordinates by the same formula (1.5)
(`eq_1_5`). -/
theorem harmonicProj_orthogonal (μ : LinfStar) (hμ : normL2 unitDiscExterior μ < ∞) :
    (⇑(harmonicProj μ) : ℂ → ℂ) ∈ {ν | ∃ ν' ∈ harmonicL2 unitDiscExterior, ν =ᵐ[volume.restrict unitDiscExterior] ν'} ∧
      ∀ ν ∈ harmonicL2 unitDiscExterior,
        ∫ z in unitDiscExterior, (μ z - harmonicProj μ z) * conj (ν z) * rho z = 0 :=
  wb_harmonicProj_orthogonal μ hμ

end TakhtajanTeo
