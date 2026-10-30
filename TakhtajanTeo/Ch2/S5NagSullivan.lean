import TakhtajanTeo.Ch2.S5ContinuousAction
import LiZhongQC.Lemmas.DiscAutomorphism

/-!
# Nag–Sullivan action on continuous `H^{1/2}` representatives (Program G, 下属6)

Host of the corrected `nag_sullivan` (D-NS, approved 2026-10-28): every input is a continuous representative on `S¹`,
and the first clause carries the `H^{1/2}` bound, so `Π̂(γ)` is the unique bounded extension (`s5ca_completed`).

* N0 `s5ns_circle`: `γ` maps `S¹` continuously into `S¹`.
* N1 `s5ns_approx`, `s5ns_bound`: smooth approximants (uniformly and in energy); the uniform `H^{1/2}` bound.
* N2 `s5ns_real`: reality.
* N3 `s5ns_theta_smooth`, `s5ns_theta`: symplecticity on `C¹` data, then on continuous `HC`.
* N4 `s5ns_right`: right action.
* N5 `s5ns_mobius_preserves`, `s5ns_preserves_mobius`: `W±` preserved iff Möbius.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- Points `e^{iθ}` lie on `S¹`. -/
theorem s5ns_exp_mem (θ : ℝ) : exp (θ * I) ∈ unitCircle := by
  change ‖exp ((θ : ℂ) * I)‖ = 1
  simp [Complex.norm_exp]

/-- N0. A sense-preserving circle homeomorphism maps `S¹` into `S¹` and is continuous there. -/
theorem s5ns_circle {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    MapsTo γ unitCircle unitCircle ∧ ContinuousOn γ unitCircle := by
  obtain ⟨K, Γ, hΓ, _, he⟩ := s5qc_extension hγ
  refine ⟨fun z hz => ?_, (continuousOn_univ.mp hΓ.2.2.1.1).continuousOn.congr he.symm⟩
  obtain ⟨u, -, -, -, hu⟩ := hγ.1
  have hz' : exp (arg z * I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at h
    simpa using h
  rw [← hz', hu]
  exact s5ns_exp_mem _

/-- Continuous circle data composed with `γ` have continuous traces. -/
theorem s5ns_comp_trace {γ f : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (hf : ContinuousOn f unitCircle) :
    Continuous (fun θ : ℝ => f (γ (exp (θ * I)))) :=
  hf.comp_continuous (s5ca_circle_continuous hγ) (fun θ => (s5ns_circle hγ).1 (s5ns_exp_mem θ))

/-- Away from the zero mode, centering does not change the coefficients of `f ∘ γ`. -/
theorem s5ns_piHat_coeff {γ f : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (hf : ContinuousOn f unitCircle)
    {k : ℤ} (hk : k ≠ 0) : circleCoeff (piHat γ f) k = circleCoeff (f ∘ γ) k :=
  s5ca_center_coeff (F := f ∘ γ) (s5ns_comp_trace hγ hf) _ hk

/-- The Abel–truncated polynomial is a constant plus a finite harmonic polynomial with data
`s5ca_coeff F b n · r^{n+1}`. -/
theorem s5ns_poly_eq (F : ℂ → ℂ) (r : ℝ) (N : ℕ) :
    s5ct_poly F r N = fun z => circleCoeff F 0 + s5qc_harmonic (Finset.range N)
      (fun n => s5ca_coeff F false n * (r : ℂ) ^ (n + 1))
      (fun n => s5ca_coeff F true n * (r : ℂ) ^ (n + 1)) z := by
  funext z
  rw [s5qc_harmonic_sum]
  simp only [s5ct_poly, s5ct_term, s5ca_coeff, Bool.false_eq_true, ite_false, ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have hs : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  simp only [map_mul, Complex.conj_ofReal]
  field_simp
  ring

/-- The normalized data of the approximant are dominated by the energy of `F`. -/
theorem s5ns_data_le {F : ℂ → ℂ} (hF : F ∈ HC) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, (‖s5ca_coeff F false n * (r : ℂ) ^ (n + 1)‖ ^ 2 +
      ‖s5ca_coeff F true n * (r : ℂ) ^ (n + 1)‖ ^ 2) ≤
      ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n‖ ^ 2 := by
  have hE := s5ca_coordinates_energy hF
  rw [gop_norm_sq, gop_norm_sq] at hE
  have hp (b : Bool) (n : ℕ) :
      ‖s5ca_coeff F b n * (r : ℂ) ^ (n + 1)‖ ^ 2 ≤ ‖s5ca_coeff F b n‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0, mul_pow]
    have h1 : (r ^ (n + 1)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hr0 hr1)
    nlinarith [sq_nonneg ‖s5ca_coeff F b n‖]
  rw [← hE, Finset.sum_add_distrib]
  apply add_le_add
  · exact (Finset.sum_le_sum fun n _ => hp false n).trans
      ((s5ca_coeff_l2 hF false).sum_le_tsum _ fun n _ => sq_nonneg _)
  · exact (Finset.sum_le_sum fun n _ => hp true n).trans
      ((s5ca_coeff_l2 hF true).sum_le_tsum _ fun n _ => sq_nonneg _)

/-- N1. The uniform `H^{1/2}` bound of literal composition on continuous representatives. The bounds of the finite
harmonic approximants (`s5qc_finite_action`) pass to each finite coefficient window by uniform convergence. -/
theorem s5ns_bound {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ C : ℝ, ∀ f ∈ HC, ContinuousOn f unitCircle → piHat γ f ∈ HC ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ f) n‖ ^ 2) ≤ C * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2 := by
  obtain ⟨K, Γ, hΓ, -, -, hA⟩ := s5qc_finite_action hγ
  have hK0 : 0 ≤ K := zero_le_one.trans hΓ.2.1
  refine ⟨K, fun f hf hc => ?_⟩
  obtain ⟨N, -, hu⟩ := s5ct_uniform_approximation hc
  let x : ℕ → ℕ → ℂ := fun j n => s5ca_coeff f false n * (s5ct_radius j : ℂ) ^ (n + 1)
  let y : ℕ → ℕ → ℂ := fun j n => s5ca_coeff f true n * (s5ct_radius j : ℂ) ^ (n + 1)
  let H : ℕ → ℂ → ℂ := fun j => s5qc_harmonic (Finset.range (N j)) (x j) (y j)
  have hP (j : ℕ) : s5ct_poly f (s5ct_radius j) (N j) = fun z => circleCoeff f 0 + H j z :=
    s5ns_poly_eq f (s5ct_radius j) (N j)
  have hHc (j : ℕ) : Continuous (H j) := (s5qc_harmonic_contDiff _ _ _).continuous
  have hcoefP (j : ℕ) {k : ℤ} (hk : k ≠ 0) :
      circleCoeff (piHat γ (H j)) k = circleCoeff (s5ct_poly f (s5ct_radius j) (N j) ∘ γ) k := by
    rw [s5ca_piHat_coeff hγ (hHc j) hk, hP j,
      ← s5ca_center_coeff (F := H j ∘ γ) ((hHc j).comp (s5ca_circle_continuous hγ)) (-circleCoeff f 0) hk]
    congr 1
    funext z
    simp only [Function.comp_apply]
    ring
  have hlim {k : ℤ} (hk : k ≠ 0) :
      Tendsto (fun j => circleCoeff (piHat γ (H j)) k) atTop (𝓝 (circleCoeff (piHat γ f) k)) := by
    have he : (fun j => circleCoeff (piHat γ (H j)) k) =
        fun j => circleCoeff (s5ct_poly f (s5ct_radius j) (N j) ∘ γ) k := funext fun j => hcoefP j hk
    rw [he, s5ns_piHat_coeff hγ hc hk]
    have hu' : TendstoUniformlyOn (fun j => s5ct_poly f (s5ct_radius j) (N j) ∘ γ) (f ∘ γ) atTop unitCircle :=
      (hu.comp γ).mono (fun z hz => (s5ns_circle hγ).1 hz)
    exact s5ct_coeff_uniform
      (fun j => (s5ct_poly_contDiff f (s5ct_radius j) (N j)).continuous.comp_continuousOn (s5ns_circle hγ).2) hu' k
  have hbd (j : ℕ) : (∑' k : ℤ, |(k : ℝ)| * ‖circleCoeff (piHat γ (H j)) k‖ ^ 2) ≤
      K * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2 := by
    obtain ⟨-, -, hB⟩ := hA (Finset.range (N j)) (x j) (y j)
    have hr := s5ct_radius_spec.1 j
    exact hB.trans (mul_le_mul_of_nonneg_left (s5ns_data_le hf hr.1 hr.2.le (N j)) hK0)
  have hsumH (j : ℕ) : Summable (fun k : ℤ => |(k : ℝ)| * ‖circleCoeff (piHat γ (H j)) k‖ ^ 2) :=
    (hA (Finset.range (N j)) (x j) (y j)).2.1.2
  have hfin (S : Finset ℤ) : ∑ k ∈ S, |(k : ℝ)| * ‖circleCoeff (piHat γ f) k‖ ^ 2 ≤
      K * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2 := by
    have ht : Tendsto (fun j => ∑ k ∈ S, |(k : ℝ)| * ‖circleCoeff (piHat γ (H j)) k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, |(k : ℝ)| * ‖circleCoeff (piHat γ f) k‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro k _
      by_cases hk : k = 0
      · subst hk
        simp only [Int.cast_zero, abs_zero, zero_mul]
        exact tendsto_const_nhds
      · exact tendsto_const_nhds.mul (((hlim hk).norm).pow 2)
    exact le_of_tendsto' ht fun j =>
      ((hsumH j).sum_le_tsum S (fun k _ => by positivity)).trans (hbd j)
  have hs : Summable (fun k : ℤ => |(k : ℝ)| * ‖circleCoeff (piHat γ f) k‖ ^ 2) :=
    summable_of_sum_le (fun k => by positivity) hfin
  refine ⟨⟨?_, hs⟩, Real.tsum_le_of_sum_le (fun k => by positivity) hfin⟩
  exact ((s5ns_comp_trace hγ hc).sub continuous_const).intervalIntegrable _ _

/-- Circle coefficients of a positive monomial. -/
theorem s5ns_coeff_pow (n : ℕ) (k : ℤ) :
    circleCoeff (fun z : ℂ => z ^ (n + 1)) k = if k = (n : ℤ) + 1 then 1 else 0 := by
  have h : (fun z : ℂ => z ^ (n + 1)) = fun z : ℂ => z ^ ((n : ℤ) + 1) := by
    funext z
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [h, circleCoeff_zpow]

/-- Circle coefficients of a conjugate monomial: on `S¹`, `z̄ = z⁻¹`. -/
theorem s5ns_coeff_conj_pow (n : ℕ) (k : ℤ) :
    circleCoeff (fun z : ℂ => conj z ^ (n + 1)) k = if k = -((n : ℤ) + 1) then 1 else 0 := by
  have h : EqOn (fun z : ℂ => conj z ^ (n + 1)) (fun z : ℂ => z ^ (-((n : ℤ) + 1))) unitCircle := by
    intro z hz
    simp only
    rw [← Complex.inv_eq_conj hz, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, inv_pow]
  rw [s5qc_coeff_congr h, circleCoeff_zpow]

/-- The Abel–truncated polynomial, expanded. -/
theorem s5ns_poly_expand (F : ℂ → ℂ) (r : ℝ) (N : ℕ) :
    s5ct_poly F r N = fun z => circleCoeff F 0 + ∑ n ∈ Finset.range N,
      ((circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1)) * z ^ (n + 1) +
        (circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1)) * conj z ^ (n + 1)) := by
  funext z
  simp only [s5ct_poly, s5ct_term, map_mul, Complex.conj_ofReal, mul_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Coefficients of the Abel–truncated polynomial. -/
theorem s5ns_poly_coeff (F : ℂ → ℂ) (r : ℝ) (N : ℕ) (k : ℤ) :
    circleCoeff (s5ct_poly F r N) k = (if k = 0 then circleCoeff F 0 else 0) +
      ∑ n ∈ Finset.range N,
        (circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1) * (if k = (n : ℤ) + 1 then 1 else 0) +
          circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1) * (if k = -((n : ℤ) + 1) then 1 else 0)) := by
  have hc0 : Continuous (fun θ : ℝ => (fun _ : ℂ => circleCoeff F 0) (exp (θ * I))) := continuous_const
  have hcp (n : ℕ) : Continuous (fun θ : ℝ => (exp (θ * I)) ^ (n + 1)) := by fun_prop
  have hcc (n : ℕ) : Continuous (fun θ : ℝ => conj (exp (θ * I)) ^ (n + 1)) :=
    (Complex.continuous_conj.comp (by fun_prop)).pow _
  have hct (n : ℕ) : Continuous (fun θ : ℝ =>
      (circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1)) * (exp (θ * I)) ^ (n + 1) +
        (circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1)) * conj (exp (θ * I)) ^ (n + 1)) :=
    Continuous.add (continuous_const.mul (hcp n) :
        Continuous (fun θ : ℝ => (circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1)) * (exp (θ * I)) ^ (n + 1)))
      (continuous_const.mul (hcc n) :
        Continuous (fun θ : ℝ => (circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1)) * conj (exp (θ * I)) ^ (n + 1)))
  rw [s5ns_poly_expand, s5ca_coeff_add hc0 (continuous_finsetSum _ fun n _ => hct n),
    s5ca_coeff_sum _ _ (fun n _ => hct n)]
  congr 1
  · have h := s5ca_coeff_mul (fun _ : ℂ => (1 : ℂ)) (circleCoeff F 0) k
    simp only [mul_one] at h
    rw [h]
    have h1 := circleCoeff_zpow 0 k
    simp only [zpow_zero] at h1
    rw [h1]
    split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro n _
    rw [s5ca_coeff_add (F := fun z : ℂ => (circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1)) * z ^ (n + 1))
      (G := fun z : ℂ => (circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1)) * conj z ^ (n + 1))
      (continuous_const.mul (hcp n)) (continuous_const.mul (hcc n)),
      s5ca_coeff_mul (fun z : ℂ => z ^ (n + 1)), s5ca_coeff_mul (fun z : ℂ => conj z ^ (n + 1)),
      s5ns_coeff_pow, s5ns_coeff_conj_pow]

/-- Away from the zero mode, the approximant multiplies `c_k(F)` by the Abel–truncation weight. -/
theorem s5ns_poly_coeff_ne (F : ℂ → ℂ) (r : ℝ) (N : ℕ) {k : ℤ} (hk : k ≠ 0) :
    circleCoeff (s5ct_poly F r N) k =
      circleCoeff F k * ((r : ℂ) ^ k.natAbs * if k.natAbs ≤ N then 1 else 0) := by
  rw [s5ns_poly_coeff, if_neg hk, zero_add]
  have hterm (n : ℕ) :
      circleCoeff F ((n : ℤ) + 1) * (r : ℂ) ^ (n + 1) * (if k = (n : ℤ) + 1 then 1 else 0) +
        circleCoeff F (-((n : ℤ) + 1)) * (r : ℂ) ^ (n + 1) * (if k = -((n : ℤ) + 1) then 1 else 0) =
      circleCoeff F k * (r : ℂ) ^ k.natAbs * (if n = k.natAbs - 1 then 1 else 0) := by
    by_cases hp : k = (n : ℤ) + 1
    · have h2 : k ≠ -((n : ℤ) + 1) := by omega
      have h3 : n = k.natAbs - 1 := by omega
      have h4 : k.natAbs = n + 1 := by omega
      rw [if_pos hp, if_neg h2, if_pos h3, h4, ← hp]
      ring
    · by_cases hm : k = -((n : ℤ) + 1)
      · have h3 : n = k.natAbs - 1 := by omega
        have h4 : k.natAbs = n + 1 := by omega
        rw [if_neg hp, if_pos hm, if_pos h3, h4, ← hm]
        ring
      · have h3 : n ≠ k.natAbs - 1 := by omega
        rw [if_neg hp, if_neg hm, if_neg h3]
        ring
  simp only [hterm]
  rw [← Finset.mul_sum, Finset.sum_ite_eq' (Finset.range N) (k.natAbs - 1)]
  have hiff : k.natAbs - 1 ∈ Finset.range N ↔ k.natAbs ≤ N := by
    rw [Finset.mem_range]
    omega
  by_cases h : k.natAbs ≤ N
  · rw [if_pos (hiff.mpr h), if_pos h]
    ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    ring

/-- N1a. A continuous `HC` function is the uniform limit on `S¹` of `C¹` functions in `HC` whose difference with it
has energy tending to `0`. The approximants are the Abel–truncated Fourier polynomials of `s5ct_uniform_approximation`;
the energy statement is dominated convergence, coefficient by coefficient. -/
theorem s5ns_approx {f : ℂ → ℂ} (hf : f ∈ HC) (hc : ContinuousOn f unitCircle) :
    ∃ P : ℕ → ℂ → ℂ, (∀ j, ContDiff ℝ 1 (P j)) ∧ (∀ j, P j ∈ HC) ∧
      TendstoUniformlyOn P f atTop unitCircle ∧
      Tendsto (fun j => ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (fun z => P j z - f z) n‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨N, hNj, hu⟩ := s5ct_uniform_approximation hc
  have hfc : Continuous (fun θ : ℝ => f (exp (θ * I))) :=
    hc.comp_continuous (by fun_prop) (fun θ => by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [Complex.norm_exp])
  set P : ℕ → ℂ → ℂ := fun j => s5ct_poly f (s5ct_radius j) (N j) with hPdef
  have hPc (j : ℕ) : Continuous (P j) := (s5ct_poly_contDiff f _ _).continuous
  have hr (j : ℕ) := s5ct_radius_spec.1 j
  -- the Abel–truncation weight
  set w : ℕ → ℤ → ℝ := fun j k => s5ct_radius j ^ k.natAbs * if k.natAbs ≤ N j then 1 else 0 with hw
  have hw01 (j : ℕ) (k : ℤ) : 0 ≤ w j k ∧ w j k ≤ 1 := by
    have h0 := (hr j).1
    have h1 : s5ct_radius j ^ k.natAbs ≤ 1 := pow_le_one₀ h0 (hr j).2.le
    simp only [hw]
    split_ifs <;> constructor <;> simp only [mul_one, mul_zero] <;> first | positivity | linarith | norm_num
  have hcoef (j : ℕ) {k : ℤ} (hk : k ≠ 0) : circleCoeff (P j) k = circleCoeff f k * (w j k : ℂ) := by
    rw [s5ns_poly_coeff_ne _ _ _ hk]
    simp only [hw]
    push_cast
    split_ifs <;> simp
  have hdiff (j : ℕ) (k : ℤ) :
      |(k : ℝ)| * ‖circleCoeff (fun z => P j z - f z) k‖ ^ 2 =
        |(k : ℝ)| * (‖circleCoeff f k‖ ^ 2 * (1 - w j k) ^ 2) := by
    by_cases hk : k = 0
    · subst hk
      simp
    have hs : (fun z => P j z - f z) = fun z => P j z + (-1 : ℂ) * f z := by
      funext z
      ring
    have hfc' : Continuous (fun θ : ℝ => (fun z => (-1 : ℂ) * f z) (exp (θ * I))) :=
      continuous_const.mul hfc
    rw [hs, s5ca_coeff_add ((hPc j).comp (by fun_prop)) hfc', s5ca_coeff_mul, hcoef j hk]
    congr 1
    have he : circleCoeff f k * (w j k : ℂ) + -1 * circleCoeff f k = circleCoeff f k * ((w j k - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  refine ⟨P, fun j => s5ct_poly_contDiff f _ _, fun j => ⟨((hPc j).comp (by fun_prop)).intervalIntegrable _ _, ?_⟩,
    hu, ?_⟩
  · apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hf.2
    by_cases hk : k = 0
    · subst hk
      simp
    rw [hcoef j hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw01 j k).1, mul_pow]
    have h1 : w j k ^ 2 ≤ 1 := pow_le_one₀ (hw01 j k).1 (hw01 j k).2
    have h2 : 0 ≤ |(k : ℝ)| * ‖circleCoeff f k‖ ^ 2 := by positivity
    nlinarith
  · simp only [hdiff]
    have hz : (∑' _ : ℤ, (0 : ℝ)) = 0 := tsum_zero
    rw [← hz]
    apply tendsto_tsum_of_dominated_convergence hf.2
    · intro k
      by_cases hk : k = 0
      · subst hk
        simp
      have hev : ∀ᶠ j in atTop, w j k = s5ct_radius j ^ k.natAbs := by
        filter_upwards [eventually_ge_atTop k.natAbs] with j hj
        simp only [hw, if_pos (hj.trans (hNj j)), mul_one]
      have hlimw : Tendsto (fun j => w j k) atTop (𝓝 1) := by
        have h := (s5ct_radius_spec.2).pow k.natAbs
        rw [one_pow] at h
        exact h.congr' (hev.mono fun j hj => hj.symm)
      have h : Tendsto (fun j => |(k : ℝ)| * (‖circleCoeff f k‖ ^ 2 * (1 - w j k) ^ 2)) atTop
          (𝓝 (|(k : ℝ)| * (‖circleCoeff f k‖ ^ 2 * (1 - 1) ^ 2))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hlimw).pow 2))
      simpa using h
    · refine Eventually.of_forall fun j k => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1 - w j k) ^ 2 ≤ 1 := by nlinarith [hw01 j k]
      have h2 : 0 ≤ |(k : ℝ)| * ‖circleCoeff f k‖ ^ 2 := by positivity
      nlinarith [sq_nonneg (1 - w j k)]

/-- The zero mode of `F - c` for `F` with continuous circle trace. -/
theorem s5ns_coeff_zero_sub {F : ℂ → ℂ} (hF : Continuous (fun θ : ℝ => F (exp (θ * I)))) (c : ℂ) :
    circleCoeff (fun z => F z - c) 0 = circleCoeff F 0 - c := by
  have h := s5ca_coeff_add (F := F) (G := fun _ => -c) hF continuous_const 0
  have hc := s5ca_coeff_mul (fun _ : ℂ => (1 : ℂ)) (-c) 0
  have h1 := circleCoeff_zpow 0 0
  simp only [zpow_zero, if_true] at h1
  simp only [mul_one] at hc
  rw [hc, h1, mul_one] at h
  simpa only [sub_eq_add_neg] using h

/-- N4. Right action. All zero modes are of continuous circle traces, so no totalized value occurs. -/
theorem s5ns_right {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∀ γ' : ℂ → ℂ, IsQSCircleHomeo γ' → ∀ f ∈ HC, ContinuousOn f unitCircle → ∀ z ∈ unitCircle,
      piHat (γ ∘ γ') f z = piHat γ' (piHat γ f) z := by
  intro γ' hγ' f _ hc z _
  have hfg : ContinuousOn (f ∘ γ) unitCircle := hc.comp (s5ns_circle hγ).2 (s5ns_circle hγ).1
  have ht := s5ns_comp_trace hγ' hfg
  have h0 := s5ns_coeff_zero_sub (F := (f ∘ γ) ∘ γ') ht (circleCoeff (f ∘ γ) 0)
  show f (γ (γ' z)) - circleCoeff (f ∘ (γ ∘ γ')) 0 =
    (f (γ (γ' z)) - circleCoeff (f ∘ γ) 0) -
      circleCoeff (fun w => ((f ∘ γ) ∘ γ') w - circleCoeff (f ∘ γ) 0) 0
  rw [h0, show f ∘ (γ ∘ γ') = (f ∘ γ) ∘ γ' from rfl]
  ring

/-- N2. Reality: `f ∘ γ` is real on `S¹` because `γ(S¹) ⊆ S¹`, and its zero mode is real. -/
theorem s5ns_real {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∀ f ∈ HR, ContinuousOn f unitCircle → piHat γ f ∈ HR := by
  intro f hf hc
  obtain ⟨C, hC⟩ := s5ns_bound hγ
  refine ⟨(hC f hf.1 hc).1, fun z hz => ?_⟩
  have hr : ∀ w ∈ unitCircle, ((f ∘ γ) w).im = 0 := fun w hw => hf.2 _ ((s5ns_circle hγ).1 hw)
  have h0 := circleCoeff_neg_of_real hr 0
  rw [neg_zero, eq_comm, Complex.conj_eq_iff_im] at h0
  simp only [piHat, sub_im, hf.2 _ ((s5ns_circle hγ).1 hz)]
  rw [h0, sub_zero]

/-- A lift `u` of a circle homeomorphism satisfies `u(t + 2πk) = u(t) + 2πk`. -/
theorem s5ns_lift_int {u : ℝ → ℝ} (hp : ∀ t, u (t + 2 * π) = u t + 2 * π) (k : ℤ) (t : ℝ) :
    u (t + k * (2 * π)) = u t + k * (2 * π) := by
  have hg : Function.Periodic (fun t => u t - t) (2 * π) := by
    intro t
    show u (t + 2 * π) - (t + 2 * π) = u t - t
    rw [hp]
    ring
  have h : u (t + k * (2 * π)) - (t + k * (2 * π)) = u t - t := (hg.int_mul k) t
  linarith

/-- A continuous lift is surjective. -/
theorem s5ns_lift_surj {u : ℝ → ℝ} (hc : Continuous u) (hp : ∀ t, u (t + 2 * π) = u t + 2 * π) :
    Function.Surjective u := by
  intro s
  set k : ℤ := ⌊(s - u 0) / (2 * π)⌋
  have hπ : 0 < 2 * π := by positivity
  have ha : u ((k : ℝ) * (2 * π)) = u 0 + k * (2 * π) := by
    simpa using s5ns_lift_int hp k 0
  have hb : u (((k + 1 : ℤ) : ℝ) * (2 * π)) = u 0 + ((k + 1 : ℤ) : ℝ) * (2 * π) := by
    simpa using s5ns_lift_int hp (k + 1) 0
  have h1 : (k : ℝ) ≤ (s - u 0) / (2 * π) := Int.floor_le _
  have h2 : (s - u 0) / (2 * π) < (k : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hπ] at h1
  rw [div_lt_iff₀ hπ] at h2
  have hab : (k : ℝ) * (2 * π) ≤ ((k + 1 : ℤ) : ℝ) * (2 * π) := by push_cast; nlinarith
  have hs : s ∈ Icc (u ((k : ℝ) * (2 * π))) (u (((k + 1 : ℤ) : ℝ) * (2 * π))) := by
    rw [ha, hb]
    push_cast
    constructor <;> linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hab hc.continuousOn hs
  exact ⟨t, ht⟩

/-- The Lebesgue–Stieltjes measure of a continuous strictly increasing lift pushes forward to Lebesgue measure. -/
theorem s5ns_lift_map (f : StieltjesFunction ℝ) (hc : Continuous f) (hm : StrictMono f)
    (hp : ∀ t, f (t + 2 * π) = f t + 2 * π) :
    Measure.map f f.measure = volume := by
  have hs := s5ns_lift_surj hc hp
  set e := StrictMono.orderIsoOfSurjective f hm hs
  have he : (e : ℝ → ℝ) = f := StrictMono.coe_orderIsoOfSurjective _ _ _
  symm
  apply Measure.ext_of_Ioc
  intro a b _
  rw [Measure.map_apply hc.measurable measurableSet_Ioc, ← he, OrderIso.preimage_Ioc, f.measure_Ioc,
    Real.volume_Ioc]
  congr 1
  have h1 : f (e.symm b) = b := StrictMono.orderIsoOfSurjective_self_symm_apply f hm hs b
  have h2 : f (e.symm a) = a := StrictMono.orderIsoOfSurjective_self_symm_apply f hm hs a
  rw [h1, h2]

/-- Change of variables along the lift. -/
theorem s5ns_lift_cov (f : StieltjesFunction ℝ) (hc : Continuous f) (hm : StrictMono f)
    (hp : ∀ t, f (t + 2 * π) = f t + 2 * π) {H : ℝ → ℂ} (hH : Continuous H) (a b : ℝ) :
    ∫ t in Ioc a b, H (f t) ∂f.measure = ∫ s in Ioc (f a) (f b), H s := by
  conv_rhs => rw [← s5ns_lift_map f hc hm hp]
  rw [setIntegral_map measurableSet_Ioc hH.aestronglyMeasurable hc.measurable.aemeasurable]
  have hpre : (f : ℝ → ℝ) ⁻¹' Ioc (f a) (f b) = Ioc a b := by
    ext t
    simp only [mem_preimage, mem_Ioc, hm.lt_iff_lt, hm.le_iff_le]
  rw [hpre]

/-- `μ_f(0, 2π]` is finite. -/
theorem s5ns_lift_finite (f : StieltjesFunction ℝ) :
    IsFiniteMeasure (f.measure.restrict (Ioc 0 (2 * π))) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, f.measure_Ioc]
  exact ENNReal.ofReal_lt_top

/-- Integration by parts against the Stieltjes measure of the lift: the distributional derivative of `Ψ ∘ f` has
Fourier coefficients `i n c_n(Ψ ∘ f)`. Proof: `Ψ(f t) = Ψ(f 0) + ∫_{(0,t]} Ψ'(f τ) dμ_f(τ)`, then Fubini. -/
theorem s5ns_lift_ibp (f : StieltjesFunction ℝ) (hc : Continuous f) (hm : StrictMono f)
    (hp : ∀ t, f (t + 2 * π) = f t + 2 * π) {Ψ Ψ' : ℝ → ℂ} (hΨ : ∀ s, HasDerivAt Ψ (Ψ' s) s)
    (hΨ' : Continuous Ψ') (hper : ∀ s, Ψ (s + 2 * π) = Ψ s) (n : ℤ) :
    ∫ t in Ioc 0 (2 * π), exp (-(n * t * I)) * Ψ' (f t) ∂f.measure =
      I * n * ∫ t in (0 : ℝ)..2 * π, Ψ (f t) * exp (-(n * t * I)) := by
  have hπ : 0 < 2 * π := by positivity
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun s => (hΨ s).continuousAt
  -- FTC along the lift
  have hftc (t : ℝ) (ht : 0 ≤ t) : ∫ τ in Ioc 0 t, Ψ' (f τ) ∂f.measure = Ψ (f t) - Ψ (f 0) := by
    rw [s5ns_lift_cov f hc hm hp hΨ' 0 t, ← intervalIntegral.integral_of_le (hm.monotone ht)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hΨ x) (hΨ'.intervalIntegrable _ _)
  have htot : ∫ τ in Ioc 0 (2 * π), Ψ' (f τ) ∂f.measure = 0 := by
    rw [hftc _ hπ.le]
    have := hp 0
    rw [zero_add] at this
    rw [this, hper, sub_self]
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, mul_zero]
    exact htot
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  set c : ℂ := -(n * I) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, neg_ne_zero]
    exact mul_ne_zero hn' I_ne_zero
  have he (t : ℝ) : exp (-(n * t * I)) = exp (c * t) := by
    congr 1
    rw [hcdef]
    ring
  have h2π : exp (c * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [hcdef]
    have := Complex.exp_int_mul_two_pi_mul_I (-n)
    rw [← this]
    congr 1
    push_cast
    ring
  have he' (t : ℝ) : ‖exp (c * t)‖ = 1 := by
    rw [← he, Complex.norm_exp]
    simp
  -- notation
  set μ := f.measure.restrict (Ioc 0 (2 * π)) with hμ
  have : IsFiniteMeasure μ := s5ns_lift_finite f
  set g : ℝ → ℂ := fun τ => Ψ' (f τ) with hg
  have hgc : Continuous g := hΨ'.comp hc
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hgc.continuousOn
  set F : ℝ → ℝ → ℂ := fun t τ => if τ ≤ t then g τ * exp (c * t) else 0 with hF
  have hFm : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    · exact ((hgc.comp continuous_snd).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))).measurable
    · exact measurable_const
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 (2 * π))).prod μ) := by
    refine Integrable.mono' (integrable_const (max M 0)) hFm.aestronglyMeasurable ?_
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp'
    obtain ⟨-, hτ⟩ := hp'
    simp only [Function.uncurry, hF]
    split_ifs
    · rw [norm_mul, he' p.1, mul_one]
      exact (hM p.2 (Ioc_subset_Icc_self hτ)).trans (le_max_left _ _)
    · simp
  -- the inner integral in `τ`, for fixed `t ∈ (0, 2π]`
  have hin (t : ℝ) (ht : t ∈ Ioc 0 (2 * π)) :
      ∫ τ, F t τ ∂μ = exp (c * t) * (Ψ (f t) - Ψ (f 0)) := by
    have hfun : (fun τ => F t τ) = (Iic t).indicator (fun τ => g τ * exp (c * t)) := by
      funext τ
      simp only [hF, indicator_apply, mem_Iic]
    rw [hfun, integral_indicator measurableSet_Iic, hμ, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_of_le ht.2, integral_mul_const, hftc t ht.1.le]
    ring
  -- the inner integral in `t`, for fixed `τ ∈ (0, 2π]`
  have hout (τ : ℝ) (hτ : τ ∈ Ioc 0 (2 * π)) :
      ∫ t in Ioc 0 (2 * π), F t τ = g τ * ((1 - exp (c * τ)) / c) := by
    have hfun : (fun t => F t τ) = (Ici τ).indicator (fun t => g τ * exp (c * t)) := by
      funext t
      simp only [hF, indicator_apply, mem_Ici]
    have hset : Ici τ ∩ Ioc 0 (2 * π) = Icc τ (2 * π) := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, hτ.1.trans_le h1, h3⟩
    rw [hfun, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.2, intervalIntegral.integral_const_mul,
      integral_exp_mul_complex hc0, h2π]
  -- the right-hand side through the FTC
  have hR : ∫ t in (0 : ℝ)..2 * π, Ψ (f t) * exp (-(n * t * I)) =
      ∫ t in Ioc 0 (2 * π), (Ψ (f 0) * exp (c * t) + ∫ τ, F t τ ∂μ) := by
    rw [intervalIntegral.integral_of_le hπ.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only
    rw [hin t ht, he]
    ring
  have hexp0 : ∫ t in Ioc 0 (2 * π), Ψ (f 0) * exp (c * t) = 0 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hπ.le, integral_exp_mul_complex hc0, h2π]
    simp
  have hint1 : IntegrableOn (fun t : ℝ => Ψ (f 0) * exp (c * t)) (Ioc 0 (2 * π)) :=
    (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrableOn_Ioc
  have hint2 : Integrable (fun t => ∫ τ, F t τ ∂μ) (volume.restrict (Ioc 0 (2 * π))) :=
    hFi.integral_prod_left
  have hgi : Integrable g μ :=
    (hgc.continuousOn.integrableOn_Icc (μ := f.measure)).mono_set Ioc_subset_Icc_self
  have hgei : Integrable (fun τ => g τ * exp (c * τ)) μ :=
    ((hgc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).continuousOn.integrableOn_Icc
      (μ := f.measure)).mono_set Ioc_subset_Icc_self
  rw [hR, integral_add hint1 hint2, hexp0, zero_add, integral_integral_swap hFi]
  have hswap : ∫ τ, (∫ t in Ioc 0 (2 * π), F t τ) ∂μ = ∫ τ, g τ * ((1 - exp (c * τ)) / c) ∂μ := by
    apply integral_congr_ae
    rw [hμ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact hout τ hτ
  rw [hswap]
  have hsplit : (fun τ => g τ * ((1 - exp (c * τ)) / c)) = fun τ => (g τ - g τ * exp (c * τ)) / c := by
    funext τ
    ring
  rw [hsplit, integral_div, integral_sub hgi hgei]
  have hg0 : ∫ τ, g τ ∂μ = 0 := htot
  rw [hg0, zero_sub]
  have hL : ∫ t in Ioc 0 (2 * π), exp (-(n * t * I)) * Ψ' (f t) ∂f.measure = ∫ τ, g τ * exp (c * τ) ∂μ := by
    rw [hμ]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by simp only [hg, he]; ring
  rw [hL, hcdef]
  field_simp

/-- The identity is a quasisymmetric circle homeomorphism. -/
theorem s5ns_qs_id : IsQSCircleHomeo id :=
  ⟨⟨id, continuous_id, strictMono_id, fun _ => rfl, fun _ => rfl⟩,
    ⟨id, injOn_id _, strictMonoOn_id, continuousOn_id, rfl, fun _ _ _ _ _ _ _ => le_rfl⟩⟩

/-- The lift of `γ` as a Stieltjes function. -/
theorem s5ns_qs_lift {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∃ f : StieltjesFunction ℝ, Continuous f ∧ StrictMono f ∧ (∀ t, f (t + 2 * π) = f t + 2 * π) ∧
      ∀ t : ℝ, γ (exp (t * I)) = exp (f t * I) := by
  obtain ⟨u, hc, hm, hp, hu⟩ := hγ.1
  exact ⟨⟨u, hm.monotone, fun x => hc.continuousWithinAt⟩, hc, hm, hp, hu⟩

/-- The circle trace `s ↦ ψ(e^{is})` of a `C¹` function: derivative, continuity, periodicity. -/
theorem s5ns_trace_deriv {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    (∀ s : ℝ, HasDerivAt (fun s : ℝ => ψ (exp (s * I))) (fderiv ℝ ψ (exp (s * I)) (exp (s * I) * I)) s) ∧
      Continuous (fun s : ℝ => fderiv ℝ ψ (exp (s * I)) (exp (s * I) * I)) ∧
      ∀ s : ℝ, ψ (exp (((s + 2 * π : ℝ) : ℂ) * I)) = ψ (exp (s * I)) := by
  have he : Continuous (fun s : ℝ => exp (s * I)) := by fun_prop
  refine ⟨fun s => ?_, ?_, fun s => ?_⟩
  · have h1 : HasDerivAt (fun s : ℝ => exp (s * I)) (exp (s * I) * I) s := by
      have h := ((hasDerivAt_id s).ofReal_comp.mul_const I).cexp
      simpa using h
    exact ((hψ.differentiable one_ne_zero) (exp (s * I))).hasFDerivAt.comp_hasDerivAt s h1
  · exact ((hψ.continuous_fderiv one_ne_zero).comp he).clm_apply (he.mul continuous_const)
  · congr 1
    rw [show (((s + 2 * π : ℝ) : ℂ) * I) = s * I + 2 * π * I by push_cast; ring]
    exact Complex.exp_periodic _

/-- The symplectic form of the composed `C¹` traces as an integral over the target circle. The series `thetaSymp` is
a `tsum`; its terms `i n c_n(ψ∘γ) c_{-n}(φ∘γ)` are absolutely summable because both compositions lie in `HC`
(`s5qc_piHat_smooth`; `|n||a_n||b_{-n}| ≤ (|n||a_n|² + |n||b_{-n}|²)/2`), so the `tsum` is a genuine sum and no
junk value `0` occurs. Route: `μ_u`-integration by parts (`s5ns_lift_ibp`) identifies `i n c_n(ψ∘γ)` with the
Fourier coefficients of the measure `Ψ'(u) dμ_u`; pairing with the Abel–truncated approximants of `φ∘γ` and passing
to the limit gives `(1/2π) ∫ (φ∘γ) Ψ'(u) dμ_u`, which the push-forward `u_* μ_u = ds` turns into the stated integral. -/
theorem s5ns_theta_formula {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) {ψ φ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hφ : ContDiff ℝ 1 φ) :
    thetaSymp (piHat γ ψ) (piHat γ φ) =
      (1 / (2 * π)) * ∫ s in (0 : ℝ)..2 * π, φ (exp (s * I)) * fderiv ℝ ψ (exp (s * I)) (exp (s * I) * I) := by
  have hπ : 0 < 2 * π := by positivity
  have hπ' : (2 * π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  obtain ⟨f, hc, hm, hp, hu⟩ := s5ns_qs_lift hγ
  obtain ⟨hΨ, hΨ'c, hper⟩ := s5ns_trace_deriv hψ
  set Ψ' : ℝ → ℂ := fun s => fderiv ℝ ψ (exp (s * I)) (exp (s * I) * I) with hΨ'
  set a : ℤ → ℂ := fun n => circleCoeff (ψ ∘ γ) n with ha
  set b : ℤ → ℂ := fun n => circleCoeff (φ ∘ γ) n with hb
  set T : ℤ → ℂ := fun n => I * n * a n * b (-n) with hT
  -- integration by parts along the lift
  have hX (n : ℤ) : ∫ t in Ioc 0 (2 * π), exp (-(n * t * I)) * Ψ' (f t) ∂f.measure = 2 * π * (I * n * a n) := by
    rw [s5ns_lift_ibp f hc hm hp hΨ hΨ'c hper n]
    have hF : a n = (1 / (2 * π)) * ∫ t in (0 : ℝ)..2 * π, ψ (exp (f t * I)) * exp (-(n * t * I)) := by
      simp only [ha, circleCoeff, fourierCoeff, Function.comp_apply, hu]
    rw [hF]
    field_simp
  -- the symplectic form is the series of `T`
  have hθ : thetaSymp (piHat γ ψ) (piHat γ φ) = ∑' n, T n := by
    unfold thetaSymp
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hT]
    rw [s5ca_piHat_coeff hγ hψ.continuous hn, s5ca_piHat_coeff hγ hφ.continuous (neg_ne_zero.mpr hn)]
    simp only [hT, ha, hb]
    ring
  -- energies of the compositions
  obtain ⟨K, -, hK⟩ := s5qc_piHat_smooth hγ
  have hE (χ : ℂ → ℂ) (hχ : ContDiff ℝ 1 χ) :
      Summable (fun n : ℤ => |(n : ℝ)| * ‖circleCoeff (χ ∘ γ) n‖ ^ 2) := by
    apply ((hK χ hχ).1.2).congr
    intro n
    by_cases hn : n = 0
    · subst hn
      simp
    rw [s5ca_piHat_coeff hγ hχ.continuous hn]
  have hEb' : Summable (fun n : ℤ => |(n : ℝ)| * ‖b (-n)‖ ^ 2) := by
    have h := (hE φ hφ).comp_injective neg_injective
    apply h.congr
    intro n
    simp [hb]
  have hTs : Summable (fun n => ‖T n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (((hE ψ hψ).add hEb').div_const 2)
    intro n
    have h1 : ‖T n‖ = |(n : ℝ)| * (‖a n‖ * ‖b (-n)‖) := by
      simp only [hT, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
      ring
    rw [h1]
    have h2 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    nlinarith [sq_nonneg (‖a n‖ - ‖b (-n)‖), mul_nonneg h2 (sq_nonneg (‖a n‖ - ‖b (-n)‖))]
  have hT0 : T 0 = 0 := by simp [hT]
  -- `ℕ`-reindexed series
  set S : ℕ → ℂ := fun n => T ((n : ℤ) + 1) + T (-((n : ℤ) + 1)) with hS
  have hTp : Summable (fun n : ℕ => ‖T ((n : ℤ) + 1)‖) :=
    hTs.comp_injective (fun x y h => by simpa using h)
  have hTm : Summable (fun n : ℕ => ‖T (-((n : ℤ) + 1))‖) :=
    hTs.comp_injective (fun x y h => by simpa using h)
  have hSs : Summable (fun n => ‖S n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _) (hTp.add hTm)
  have hTS : ∑' n, T n = ∑' n, S n := by
    rw [tsum_of_add_one_of_neg_add_one hTp.of_norm hTm.of_norm, hT0, add_zero,
      ← Summable.tsum_add hTp.of_norm hTm.of_norm]
  -- approximants of `g = φ ∘ γ`
  set g : ℂ → ℂ := φ ∘ γ with hg
  have hgc : ContinuousOn g unitCircle :=
    hφ.continuous.comp_continuousOn (s5ns_circle hγ).2
  obtain ⟨N, hNj, hconv⟩ := s5ct_uniform_approximation hgc
  set r := s5ct_radius
  set P : ℕ → ℂ → ℂ := fun j => s5ct_poly g (r j) (N j) with hP
  set μ := f.measure.restrict (Ioc 0 (2 * π)) with hμ
  have : IsFiniteMeasure μ := s5ns_lift_finite f
  have hIc (χ : ℝ → ℂ) (hχ : Continuous χ) : Integrable χ μ :=
    (hχ.continuousOn.integrableOn_Icc (μ := f.measure)).mono_set Ioc_subset_Icc_self
  have hexpc (m : ℤ) : Continuous (fun t : ℝ => exp (-(m * t * I))) := by fun_prop
  have hfc : Continuous (fun t => Ψ' (f t)) := hΨ'c.comp hc
  -- (b) the approximant pairings
  have hpow (n : ℕ) (t : ℝ) : exp (t * I) ^ (n + 1) = exp (-(((-((n : ℤ) + 1) : ℤ) : ℂ) * t * I)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcpow (n : ℕ) (t : ℝ) : conj (exp (t * I)) ^ (n + 1) = exp (-((((n : ℤ) + 1 : ℤ) : ℂ) * t * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hLj (j : ℕ) : ∫ t, P j (exp (t * I)) * Ψ' (f t) ∂μ =
      2 * π * ∑ n ∈ Finset.range (N j), ((r j : ℂ) ^ (n + 1)) * S n := by
    have hpt : (fun t : ℝ => P j (exp (t * I)) * Ψ' (f t)) = fun t : ℝ =>
        circleCoeff g 0 * (exp (-(((0 : ℤ) : ℂ) * t * I)) * Ψ' (f t)) +
          ∑ n ∈ Finset.range (N j),
            ((circleCoeff g ((n : ℤ) + 1) * (r j : ℂ) ^ (n + 1)) *
                (exp (-(((-((n : ℤ) + 1) : ℤ) : ℂ) * t * I)) * Ψ' (f t)) +
              (circleCoeff g (-((n : ℤ) + 1)) * (r j : ℂ) ^ (n + 1)) *
                (exp (-((((n : ℤ) + 1 : ℤ) : ℂ) * t * I)) * Ψ' (f t))) := by
      funext t
      rw [hP]
      simp only
      rw [s5ns_poly_expand]
      simp only [hpow, hcpow, Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, add_mul,
        Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hi (m : ℤ) : Integrable (fun t : ℝ => exp (-((m : ℂ) * t * I)) * Ψ' (f t)) μ :=
      hIc _ ((hexpc m).mul hfc)
    have hterm (n : ℕ) : Integrable (fun t : ℝ =>
        (circleCoeff g ((n : ℤ) + 1) * (r j : ℂ) ^ (n + 1)) *
            (exp (-(((-((n : ℤ) + 1) : ℤ) : ℂ) * t * I)) * Ψ' (f t)) +
          (circleCoeff g (-((n : ℤ) + 1)) * (r j : ℂ) ^ (n + 1)) *
            (exp (-((((n : ℤ) + 1 : ℤ) : ℂ) * t * I)) * Ψ' (f t))) μ :=
      ((hi _).const_mul _).add ((hi _).const_mul _)
    rw [hpt, integral_add ((hi 0).const_mul _) (integrable_finset_sum _ fun n _ => hterm n),
      integral_finset_sum _ fun n _ => hterm n, integral_const_mul, hX 0]
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_add ((hi _).const_mul _) ((hi _).const_mul _), integral_const_mul, integral_const_mul, hX, hX]
    simp only [hS, hT, ha, hb, neg_neg]
    push_cast
    ring
  -- (c) the limit of the pairings is the series
  have hr := s5ct_radius_spec
  have hlimS : Tendsto (fun j => ∑ n ∈ Finset.range (N j), ((r j : ℂ) ^ (n + 1)) * S n) atTop
      (𝓝 (∑' n, S n)) := by
    have heq (j : ℕ) : ∑ n ∈ Finset.range (N j), ((r j : ℂ) ^ (n + 1)) * S n =
        ∑' n, (if n < N j then (r j : ℂ) ^ (n + 1) else 0) * S n := by
      rw [tsum_eq_sum (s := Finset.range (N j))]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (Finset.mem_range.mp hn)]
      · intro n hn
        rw [if_neg (fun h => hn (Finset.mem_range.mpr h)), zero_mul]
    simp only [heq]
    apply tendsto_tsum_of_dominated_convergence hSs
    · intro n
      have hev : ∀ᶠ j in atTop,
          (if n < N j then (r j : ℂ) ^ (n + 1) else 0) * S n = (r j : ℂ) ^ (n + 1) * S n := by
        filter_upwards [eventually_ge_atTop (n + 1)] with j hj
        rw [if_pos (by have := hNj j; omega)]
      have hl : Tendsto (fun j => (r j : ℂ) ^ (n + 1) * S n) atTop (𝓝 (1 ^ (n + 1) * S n)) := by
        have h1 : Tendsto (fun j => (r j : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 1).comp hr.2
        rw [Complex.ofReal_one] at h1
        exact (h1.pow (n + 1)).mul tendsto_const_nhds
      rw [one_pow, one_mul] at hl
      exact hl.congr' (hev.mono fun j h => h.symm)
    · refine Eventually.of_forall fun j n => ?_
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      split_ifs
      · rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr.1 j).1]
        exact pow_le_one₀ (hr.1 j).1 (hr.1 j).2.le
      · simp
  -- (a) the pairings converge to the pairing with `g`
  have hS1 : unitCircle = sphere (0 : ℂ) 1 := by
    ext z
    simp [unitCircle]
  obtain ⟨Bg, hBg⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn (hS1 ▸ hgc)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hfc.continuousOn
  have hmem (t : ℝ) : exp (t * I) ∈ unitCircle := by
    change ‖exp ((t : ℂ) * I)‖ = 1
    simp [Complex.norm_exp]
  have hlimL : Tendsto (fun j => ∫ t, P j (exp (t * I)) * Ψ' (f t) ∂μ) atTop
      (𝓝 (∫ t, g (exp (t * I)) * Ψ' (f t) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (Bg + 1) * M)
    · exact Eventually.of_forall fun j =>
        (((s5ct_poly_contDiff g (r j) (N j)).continuous.comp
          (by fun_prop : Continuous fun t : ℝ => exp (t * I))).mul hfc).aestronglyMeasurable
    · have hu1 := (Metric.tendstoUniformlyOn_iff.mp hconv) 1 one_pos
      filter_upwards [hu1] with j hj
      rw [hμ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      have h1 : ‖P j (exp (t * I))‖ ≤ Bg + 1 := by
        have hd := hj _ (hmem t)
        rw [dist_eq_norm] at hd
        have hb' := hBg _ (hS1 ▸ hmem t)
        have h3 := norm_sub_norm_le (P j (exp (t * I))) (g (exp (t * I)))
        rw [norm_sub_rev] at hd
        linarith
      have h2 : ‖Ψ' (f t)‖ ≤ M := hM t (Ioc_subset_Icc_self ht)
      have hB0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg _ (hS1 ▸ hmem t))
      exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    · exact integrable_const _
    · exact Eventually.of_forall fun t =>
        (hconv.tendsto_at (hmem t)).mul tendsto_const_nhds
  -- conclusion
  have hlim2 : Tendsto (fun j => ∫ t, P j (exp (t * I)) * Ψ' (f t) ∂μ) atTop (𝓝 (2 * π * ∑' n, S n)) := by
    simp only [hLj]
    exact tendsto_const_nhds.mul hlimS
  have hL := tendsto_nhds_unique hlimL hlim2
  rw [hθ, hTS]
  have hcov : ∫ t, g (exp (t * I)) * Ψ' (f t) ∂μ =
      ∫ s in (0 : ℝ)..2 * π, φ (exp (s * I)) * Ψ' s := by
    have hH : Continuous (fun s : ℝ => φ (exp (s * I)) * Ψ' s) :=
      (hφ.continuous.comp (by fun_prop)).mul hΨ'c
    have h1 : ∫ t, g (exp (t * I)) * Ψ' (f t) ∂μ =
        ∫ t in Ioc 0 (2 * π), (fun s : ℝ => φ (exp (s * I)) * Ψ' s) (f t) ∂f.measure := by
      rw [hμ]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by simp only [hg, Function.comp_apply, hu]
    rw [h1, s5ns_lift_cov f hc hm hp hH, ← intervalIntegral.integral_of_le (hm.monotone hπ.le)]
    have h2 : f (2 * π) = f 0 + 2 * π := by simpa using hp 0
    rw [h2]
    have hper' : Function.Periodic (fun s : ℝ => φ (exp (s * I)) * Ψ' s) (2 * π) := by
      intro s
      simp only [hΨ']
      push_cast
      rw [show ((s : ℂ) + 2 * π) * I = s * I + 2 * π * I by ring, Complex.exp_periodic]
    have := hper'.intervalIntegral_add_eq (f 0) 0
    rw [zero_add] at this
    exact this
  rw [← hcov, hL]
  field_simp

/-- N3a. Symplecticity on `C¹` data. Both sides are the integral `(1/2π)∮ φ dψ` (`s5ns_theta_formula` for `γ` and for
the identity). The series `thetaSymp` is a `tsum`; for `C¹` data its terms are absolutely summable (both arguments lie
in `HC`, Cauchy–Schwarz with weight `|n|`), so it is a genuine sum, not the junk value `0`. -/
theorem s5ns_theta_smooth {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) {ψ φ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hφ : ContDiff ℝ 1 φ) :
    thetaSymp (piHat γ ψ) (piHat γ φ) = thetaSymp ψ φ := by
  rw [s5ns_theta_formula hγ hψ hφ, ← s5ns_theta_formula s5ns_qs_id hψ hφ]
  unfold thetaSymp
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  rw [s5ca_piHat_coeff s5ns_qs_id hψ.continuous hn,
    s5ca_piHat_coeff s5ns_qs_id hφ.continuous (neg_ne_zero.mpr hn)]
  rfl

/-- Coefficients of a difference of functions with continuous circle traces. -/
theorem s5ns_coeff_sub {F G : ℂ → ℂ} (hF : Continuous (fun θ : ℝ => F (exp (θ * I))))
    (hG : Continuous (fun θ : ℝ => G (exp (θ * I)))) (n : ℤ) :
    circleCoeff (fun z => F z - G z) n = circleCoeff F n - circleCoeff G n := by
  have h := s5ca_coeff_add (F := F) (G := fun z => (-1 : ℂ) * G z) hF (continuous_const.mul hG) n
  rw [s5ca_coeff_mul] at h
  have he : (fun z => F z - G z) = fun z => F z + (-1 : ℂ) * G z := by
    funext z
    ring
  rw [he, h]
  ring

/-- Weighted energies are closed under differences. -/
theorem s5ns_energy_sub {x y : ℤ → ℂ} (hx : Summable (fun n : ℤ => |(n : ℝ)| * ‖x n‖ ^ 2))
    (hy : Summable (fun n : ℤ => |(n : ℝ)| * ‖y n‖ ^ 2)) :
    Summable (fun n : ℤ => |(n : ℝ)| * ‖x n - y n‖ ^ 2) ∧
      ∀ n : ℤ, |(n : ℝ)| * ‖x n - y n‖ ^ 2 ≤ 2 * (|(n : ℝ)| * ‖x n‖ ^ 2) + 2 * (|(n : ℝ)| * ‖y n‖ ^ 2) := by
  have hle (n : ℤ) : |(n : ℝ)| * ‖x n - y n‖ ^ 2 ≤ 2 * (|(n : ℝ)| * ‖x n‖ ^ 2) + 2 * (|(n : ℝ)| * ‖y n‖ ^ 2) := by
    have h1 : ‖x n - y n‖ ^ 2 ≤ 2 * ‖x n‖ ^ 2 + 2 * ‖y n‖ ^ 2 := by
      nlinarith [norm_sub_le (x n) (y n), norm_nonneg (x n - y n), sq_nonneg (‖x n‖ - ‖y n‖),
        norm_nonneg (x n), norm_nonneg (y n)]
    have h2 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    nlinarith
  exact ⟨Summable.of_nonneg_of_le (fun n => by positivity) hle ((hx.mul_left 2).add (hy.mul_left 2)), hle⟩

/-- Cauchy–Schwarz for the symplectic pairing of coefficient sequences. -/
theorem s5ns_pair_cs (x y : ℤ → ℂ) (hx : Summable (fun n : ℤ => |(n : ℝ)| * ‖x n‖ ^ 2))
    (hy : Summable (fun n : ℤ => |(n : ℝ)| * ‖y n‖ ^ 2)) :
    Summable (fun n : ℤ => (n : ℂ) * x n * y (-n)) ∧
      ‖∑' n : ℤ, (n : ℂ) * x n * y (-n)‖ ≤
        Real.sqrt (∑' n : ℤ, |(n : ℝ)| * ‖x n‖ ^ 2) * Real.sqrt (∑' n : ℤ, |(n : ℝ)| * ‖y n‖ ^ 2) := by
  set u : ℤ → ℝ := fun n => Real.sqrt |(n : ℝ)| * ‖x n‖ with hu
  set v : ℤ → ℝ := fun n => Real.sqrt |(n : ℝ)| * ‖y (-n)‖ with hv
  have hu2 (n : ℤ) : u n ^ (2 : ℝ) = |(n : ℝ)| * ‖x n‖ ^ 2 := by
    rw [Real.rpow_two, hu, mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have hv2 (n : ℤ) : v n ^ (2 : ℝ) = |(n : ℝ)| * ‖y (-n)‖ ^ 2 := by
    rw [Real.rpow_two, hv, mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have hyn : Summable (fun n : ℤ => |(n : ℝ)| * ‖y (-n)‖ ^ 2) := by
    have h := hy.comp_injective neg_injective
    apply h.congr
    intro n
    simp
  have hyt : ∑' n : ℤ, |(n : ℝ)| * ‖y (-n)‖ ^ 2 = ∑' n : ℤ, |(n : ℝ)| * ‖y n‖ ^ 2 := by
    have h := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => |(n : ℝ)| * ‖y n‖ ^ 2)
    rw [← h]
    apply tsum_congr
    intro n
    simp
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := u) (g := v) (fun n => by positivity) (fun n => by positivity)
    (by simpa only [hu2] using hx) (by simpa only [hv2] using hyn)
  simp only [hu2, hv2, hyt] at hle
  have hnorm (n : ℤ) : ‖(n : ℂ) * x n * y (-n)‖ = u n * v n := by
    simp only [hu, hv, norm_mul, Complex.norm_intCast]
    have : Real.sqrt |(n : ℝ)| * Real.sqrt |(n : ℝ)| = |(n : ℝ)| := Real.mul_self_sqrt (abs_nonneg _)
    linear_combination (-(‖x n‖ * ‖y (-n)‖)) * this
  have hs' : Summable (fun n : ℤ => ‖(n : ℂ) * x n * y (-n)‖) := by simpa only [hnorm] using hs
  refine ⟨hs'.of_norm, (norm_tsum_le_tsum_norm hs').trans ?_⟩
  simp only [hnorm]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert hle using 2 <;> norm_num

/-- Continuity of the symplectic pairing under convergence in energy. -/
theorem s5ns_pair_tendsto {a b : ℤ → ℂ} {A B : ℕ → ℤ → ℂ}
    (ha : Summable (fun n : ℤ => |(n : ℝ)| * ‖a n‖ ^ 2)) (hb : Summable (fun n : ℤ => |(n : ℝ)| * ‖b n‖ ^ 2))
    (hA : ∀ j, Summable (fun n : ℤ => |(n : ℝ)| * ‖A j n‖ ^ 2))
    (hB : ∀ j, Summable (fun n : ℤ => |(n : ℝ)| * ‖B j n‖ ^ 2))
    (hAt : Tendsto (fun j => ∑' n : ℤ, |(n : ℝ)| * ‖A j n - a n‖ ^ 2) atTop (𝓝 0))
    (hBt : Tendsto (fun j => ∑' n : ℤ, |(n : ℝ)| * ‖B j n - b n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => ∑' n : ℤ, (n : ℂ) * A j n * B j (-n)) atTop (𝓝 (∑' n : ℤ, (n : ℂ) * a n * b (-n))) := by
  set E : (ℤ → ℂ) → ℝ := fun z => ∑' n : ℤ, |(n : ℝ)| * ‖z n‖ ^ 2 with hE
  have hdA (j : ℕ) := s5ns_energy_sub (hA j) ha
  have hdB (j : ℕ) := s5ns_energy_sub (hB j) hb
  -- the decomposition `P(A,B) - P(a,b) = P(A-a, B) + P(a, B-b)`
  have hdec (j : ℕ) : (∑' n : ℤ, (n : ℂ) * A j n * B j (-n)) - ∑' n : ℤ, (n : ℂ) * a n * b (-n) =
      (∑' n : ℤ, (n : ℂ) * (A j n - a n) * B j (-n)) + ∑' n : ℤ, (n : ℂ) * a n * (B j (-n) - b (-n)) := by
    have h1 := (s5ns_pair_cs (fun n => A j n - a n) (B j) (hdA j).1 (hB j)).1
    have h2 := (s5ns_pair_cs a (fun n => B j n - b n) ha (hdB j).1).1
    have h3 := (s5ns_pair_cs (A j) (B j) (hA j) (hB j)).1
    have h4 := (s5ns_pair_cs a b ha hb).1
    rw [← h1.tsum_add h2, ← h3.tsum_sub h4]
    apply tsum_congr
    intro n
    ring
  have hbound (j : ℕ) : ‖(∑' n : ℤ, (n : ℂ) * A j n * B j (-n)) - ∑' n : ℤ, (n : ℂ) * a n * b (-n)‖ ≤
      Real.sqrt (E (fun n => A j n - a n)) * Real.sqrt (2 * E (fun n => B j n - b n) + 2 * E b) +
        Real.sqrt (E a) * Real.sqrt (E (fun n => B j n - b n)) := by
    rw [hdec]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (s5ns_pair_cs (fun n => A j n - a n) (B j) (hdA j).1 (hB j)).2.trans ?_
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      have hBj := s5ns_energy_sub (hdB j).1 hb
      have hsum : (fun n : ℤ => |(n : ℝ)| * ‖B j n‖ ^ 2) =
          fun n : ℤ => |(n : ℝ)| * ‖(B j n - b n) - (-b n)‖ ^ 2 := by
        funext n
        congr 2
        ring
      have hnb : Summable (fun n : ℤ => |(n : ℝ)| * ‖-b n‖ ^ 2) := by simpa only [norm_neg] using hb
      have hle := (s5ns_energy_sub (hdB j).1 hnb).2
      simp only [hE, hsum]
      calc ∑' n : ℤ, |(n : ℝ)| * ‖(B j n - b n) - (-b n)‖ ^ 2
          ≤ ∑' n : ℤ, (2 * (|(n : ℝ)| * ‖B j n - b n‖ ^ 2) + 2 * (|(n : ℝ)| * ‖-b n‖ ^ 2)) :=
            (s5ns_energy_sub (hdB j).1 hnb).1.tsum_le_tsum hle
              ((((hdB j).1).mul_left 2).add (hnb.mul_left 2))
        _ = 2 * ∑' n : ℤ, |(n : ℝ)| * ‖B j n - b n‖ ^ 2 + 2 * ∑' n : ℤ, |(n : ℝ)| * ‖b n‖ ^ 2 := by
            rw [(((hdB j).1).mul_left 2).tsum_add (hnb.mul_left 2), tsum_mul_left, tsum_mul_left]
            simp only [norm_neg]
    · have h := (s5ns_pair_cs a (fun n => B j n - b n) ha (hdB j).1).2
      exact h
  have hlim : Tendsto (fun j => Real.sqrt (E (fun n => A j n - a n)) * Real.sqrt (2 * E (fun n => B j n - b n) + 2 * E b) +
      Real.sqrt (E a) * Real.sqrt (E (fun n => B j n - b n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => Real.sqrt (E (fun n => A j n - a n))) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hAt
      rw [Real.sqrt_zero] at h
      exact h
    have h2 : Tendsto (fun j => Real.sqrt (E (fun n => B j n - b n))) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hBt
      rw [Real.sqrt_zero] at h
      exact h
    have h3 : Tendsto (fun j => Real.sqrt (2 * E (fun n => B j n - b n) + 2 * E b)) atTop
        (𝓝 (Real.sqrt (2 * 0 + 2 * E b))) :=
      (Real.continuous_sqrt.tendsto _).comp ((hBt.const_mul 2).add tendsto_const_nhds)
    simpa using (h1.mul h3).add (tendsto_const_nhds.mul h2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun j => norm_nonneg _) hbound hlim

/-- N3. Symplecticity on continuous `HC` data: approximate both arguments by `C¹` functions (N1a), use N3a, and pass to
the limit on both sides (N1 for the composed differences, `s5ns_pair_tendsto`). -/
theorem s5ns_theta {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ∀ f ∈ HC, ∀ g ∈ HC, ContinuousOn f unitCircle → ContinuousOn g unitCircle →
      thetaSymp (piHat γ f) (piHat γ g) = thetaSymp f g := by
  intro f hf g hg hfc hgc
  obtain ⟨C, hC⟩ := s5ns_bound hγ
  obtain ⟨P, hPd, hPH, -, hPE⟩ := s5ns_approx hf hfc
  obtain ⟨Q, hQd, hQH, -, hQE⟩ := s5ns_approx hg hgc
  have htr {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle) : Continuous (fun θ : ℝ => F (exp (θ * I))) :=
    hF.comp_continuous (by fun_prop) (fun θ => by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [Complex.norm_exp])
  have hPc (j : ℕ) : ContinuousOn (P j) unitCircle := (hPd j).continuous.continuousOn
  have hQc (j : ℕ) : ContinuousOn (Q j) unitCircle := (hQd j).continuous.continuousOn
  -- the differences are continuous `HC` functions
  have hdiff {F G : ℂ → ℂ} (hF : F ∈ HC) (hG : G ∈ HC) (hFc : ContinuousOn F unitCircle)
      (hGc : ContinuousOn G unitCircle) :
      (fun z => F z - G z) ∈ HC ∧ ContinuousOn (fun z => F z - G z) unitCircle := by
    refine ⟨⟨((htr hFc).sub (htr hGc)).intervalIntegrable _ _, ?_⟩, hFc.sub hGc⟩
    simpa only [s5ns_coeff_sub (htr hFc) (htr hGc)] using (s5ns_energy_sub hF.2 hG.2).1
  -- energy of the composed differences
  have hcomp {F G : ℂ → ℂ} (hF : F ∈ HC) (hG : G ∈ HC) (hFc : ContinuousOn F unitCircle)
      (hGc : ContinuousOn G unitCircle) :
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ F) n - circleCoeff (piHat γ G) n‖ ^ 2) ≤
        C * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (fun z => F z - G z) n‖ ^ 2 := by
    obtain ⟨hD, hDc⟩ := hdiff hF hG hFc hGc
    refine le_of_eq_of_le ?_ (hC _ hD hDc).2
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst hn
      simp
    rw [s5ns_piHat_coeff hγ hFc hn, s5ns_piHat_coeff hγ hGc hn, s5ns_piHat_coeff hγ hDc hn]
    congr 3
    exact (s5ns_coeff_sub (s5ns_comp_trace hγ hFc) (s5ns_comp_trace hγ hGc) n).symm
  have hsq {F G : ℂ → ℂ} (hFc : ContinuousOn F unitCircle) (hGc : ContinuousOn G unitCircle) :
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff F n - circleCoeff G n‖ ^ 2) =
        ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (fun z => F z - G z) n‖ ^ 2 := by
    simp only [s5ns_coeff_sub (htr hFc) (htr hGc)]
  have hzero {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (hle : ∀ j, e j ≤ C * ∑' n : ℤ, |(n : ℝ)| *
      ‖circleCoeff (fun z => P j z - f z) n‖ ^ 2) : Tendsto e atTop (𝓝 0) := by
    have h := hPE.const_mul C
    rw [mul_zero] at h
    exact squeeze_zero he0 hle h
  -- the two limits
  have hL : Tendsto (fun j => thetaSymp (P j) (Q j)) atTop (𝓝 (thetaSymp f g)) := by
    unfold thetaSymp
    refine tendsto_const_nhds.mul (s5ns_pair_tendsto hf.2 hg.2 (fun j => (hPH j).2) (fun j => (hQH j).2) ?_ ?_)
    · simpa only [hsq (hPc _) hfc] using hPE
    · simpa only [hsq (hQc _) hgc] using hQE
  have hR : Tendsto (fun j => thetaSymp (piHat γ (P j)) (piHat γ (Q j))) atTop
      (𝓝 (thetaSymp (piHat γ f) (piHat γ g))) := by
    unfold thetaSymp
    refine tendsto_const_nhds.mul (s5ns_pair_tendsto (hC f hf hfc).1.2 (hC g hg hgc).1.2
      (fun j => (hC _ (hPH j) (hPc j)).1.2) (fun j => (hC _ (hQH j) (hQc j)).1.2) ?_ ?_)
    · have h := hPE.const_mul C
      rw [mul_zero] at h
      exact squeeze_zero (fun j => tsum_nonneg fun n => by positivity)
        (fun j => hcomp (hPH j) hf (hPc j) hfc) h
    · have h := hQE.const_mul C
      rw [mul_zero] at h
      exact squeeze_zero (fun j => tsum_nonneg fun n => by positivity)
        (fun j => hcomp (hQH j) hg (hQc j) hgc) h
  have heq (j : ℕ) : thetaSymp (piHat γ (P j)) (piHat γ (Q j)) = thetaSymp (P j) (Q j) :=
    s5ns_theta_smooth hγ (hPd j) (hQd j)
  simp only [heq] at hR
  exact tendsto_nhds_unique hR hL

/-- Coefficients of the complex conjugate. -/
theorem s5ns_coeff_conj (F : ℂ → ℂ) (n : ℤ) :
    circleCoeff (fun z => conj (F z)) n = conj (circleCoeff F (-n)) := by
  unfold circleCoeff fourierCoeff
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hπ, map_mul, ← integral_conj]
  congr 1
  · simp only [map_div₀, map_one, map_mul, Complex.conj_ofReal, map_ofNat]
  · congr 1
    funext θ
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_neg, map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I, Int.cast_neg]
    ring

/-- A continuous circle function without negative frequencies is the boundary value of a function holomorphic in `𝔻`
and continuous on `𝔻̄` (its Poisson extension). -/
theorem s5ns_holo_ext {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle)
    (hneg : ∀ n : ℕ, circleCoeff F (-((n : ℤ) + 1)) = 0) :
    ∃ U : ℂ → ℂ, ContinuousOn U (closedBall 0 1) ∧ EqOn U F unitCircle ∧ DifferentiableOn ℂ U unitDisc := by
  obtain ⟨U, P, Q, hUc, hUF, hP, hQ, hU⟩ := s5ct_poisson_decomposition hF
  obtain ⟨a, ha⟩ := s5ct_holo_series hP
  obtain ⟨b, hb⟩ := s5ct_holo_series hQ
  obtain ⟨-, hm, -⟩ := s5ct_boundary_coefficients hUc hUF hP.continuousOn hQ.continuousOn hU ha hb
  have hb0 (n : ℕ) : b (n + 1) = 0 := by
    have h := hm n
    rw [hneg n] at h
    exact (map_eq_zero _).mp h.symm
  have hQc (z : ℂ) (hz : z ∈ unitDisc) : Q z = b 0 := by
    have h := (hb z hz).unique (hasSum_single 0 (fun n hn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hb0 k, zero_mul]))
    simpa using h
  refine ⟨U, hUc, hUF, (hP.add_const (conj (b 0))).congr fun z hz => ?_⟩
  rw [hU hz]
  simp only [hQc z hz]

/-- Negative coefficients of a function holomorphic in `𝔻` and continuous on `𝔻̄` vanish (Cauchy). -/
theorem s5ns_coeff_neg_holo {H : ℂ → ℂ} (hc : ContinuousOn H (closedBall 0 1))
    (hd : DifferentiableOn ℂ H unitDisc) (m : ℕ) : circleCoeff H (-((m : ℤ) + 1)) = 0 := by
  have hI := s5st_circle_monomial H m
  have h0 : (∮ z in C(0, 1), H z * z ^ m) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one countable_empty
      (hc.mul (continuous_pow m).continuousOn)
    intro z hz
    exact (hd.differentiableAt (isOpen_ball.mem_nhds hz.1)).mul (differentiableAt_pow m)
  rw [h0] at hI
  have hne : (2 * π * I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have h := (mul_eq_zero.mp hI.symm).resolve_left hne
  unfold circleCoeff
  exact h

/-- A circle Möbius map is a fractional linear map with no pole on `𝔻̄`, mapping `𝔻` into `𝔻`, and equal to `γ` on
`S¹`. -/
theorem s5ns_mobius_data {γ : ℂ → ℂ} (hm : IsCircleMobius γ) :
    ∃ A B C D : ℂ, (∀ z ∈ closedBall (0 : ℂ) 1, C * z + D ≠ 0) ∧
      (∀ z ∈ unitDisc, (A * z + B) / (C * z + D) ∈ unitDisc) ∧
      ∀ z ∈ unitCircle, (A * z + B) / (C * z + D) = γ z := by
  obtain ⟨α, ⟨⟨A, B, C, D, -, rfl⟩, himg⟩, hα⟩ := hm
  have hval (z : ℂ) : mobiusExt A B C D (z : ExtPlane) =
      if C * z + D = 0 then extInf else (((A * z + B) / (C * z + D) : ℂ) : ExtPlane) := rfl
  have hdisc (z : ℂ) (hz : z ∈ unitDisc) : C * z + D ≠ 0 ∧ (A * z + B) / (C * z + D) ∈ unitDisc := by
    have hmem : mobiusExt A B C D (z : ExtPlane) ∈ toExt unitDisc := by
      rw [← himg]
      exact mem_image_of_mem _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hmem
    rw [hval] at hwe
    split_ifs at hwe with h0
    · exact absurd hwe (OnePoint.coe_ne_infty w)
    · exact ⟨h0, (OnePoint.coe_injective hwe) ▸ hw⟩
  have hcirc (z : ℂ) (hz : z ∈ unitCircle) : C * z + D ≠ 0 ∧ (A * z + B) / (C * z + D) = γ z := by
    have h := hα z hz
    rw [hval] at h
    split_ifs at h with h0
    · exact absurd h (OnePoint.coe_ne_infty _)
    · exact ⟨h0, (OnePoint.coe_injective h).symm⟩
  refine ⟨A, B, C, D, fun z hz => ?_, fun z hz => (hdisc z hz).2, fun z hz => (hcirc z hz).2⟩
  rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with h | h
  · exact (hdisc z (mem_ball_zero_iff.mpr h)).1
  · exact (hcirc z h).1

/-- Composition with a circle Möbius map keeps the negative frequencies zero. -/
theorem s5ns_mobius_neg {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (hm : IsCircleMobius γ) {F : ℂ → ℂ}
    (hF : ContinuousOn F unitCircle) (hneg : ∀ n : ℕ, circleCoeff F (-((n : ℤ) + 1)) = 0) (n : ℕ) :
    circleCoeff (F ∘ γ) (-((n : ℤ) + 1)) = 0 := by
  obtain ⟨U, hUc, hUF, hUd⟩ := s5ns_holo_ext hF hneg
  obtain ⟨A, B, C, D, hden, hD, hγe⟩ := s5ns_mobius_data hm
  set m : ℂ → ℂ := fun z => (A * z + B) / (C * z + D) with hmdef
  have hmc : ContinuousOn m (closedBall 0 1) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn.div
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn hden
  have hmaps : MapsTo m (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with h | h
    · exact ball_subset_closedBall (hD z (mem_ball_zero_iff.mpr h))
    · have hz' : z ∈ unitCircle := h
      rw [show m z = γ z from hγe z hz']
      exact mem_closedBall_zero_iff.mpr ((s5ns_circle hγ).1 hz').le
  have hHc : ContinuousOn (U ∘ m) (closedBall 0 1) := hUc.comp hmc hmaps
  have hHd : DifferentiableOn ℂ (U ∘ m) unitDisc := by
    intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
    have hmd : DifferentiableAt ℂ m z :=
      ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)).div
        ((differentiableAt_const _).mul differentiableAt_id |>.add (differentiableAt_const _)) (hden z hz')
    exact ((hUd.differentiableAt (isOpen_ball.mem_nhds (hD z hz))).comp z hmd).differentiableWithinAt
  have he : EqOn (U ∘ m) (F ∘ γ) unitCircle := by
    intro z hz
    simp only [Function.comp_apply]
    rw [show m z = γ z from hγe z hz]
    exact hUF ((s5ns_circle hγ).1 hz)
  rw [← s5qc_coeff_congr he]
  exact s5ns_coeff_neg_holo hHc hHd n

/-- N5a. A circle Möbius map preserves `W₊` and `W₋`. -/
theorem s5ns_mobius_preserves {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) (hm : IsCircleMobius γ) :
    (∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus) ∧
      (∀ f ∈ Wminus, ContinuousOn f unitCircle → piHat γ f ∈ Wminus) := by
  obtain ⟨Cb, hCb⟩ := s5ns_bound hγ
  have h0 {f : ℂ → ℂ} (hc : ContinuousOn f unitCircle) : circleCoeff (piHat γ f) 0 = 0 := by
    have h := s5ns_coeff_zero_sub (F := f ∘ γ) (s5ns_comp_trace hγ hc) (circleCoeff (f ∘ γ) 0)
    rw [sub_self] at h
    exact h
  constructor
  · intro f hf hc
    refine ⟨(hCb f hf.1 hc).1, fun n hn => ?_⟩
    rcases hn.lt_or_eq with h | h
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      rw [s5ns_piHat_coeff hγ hc (by omega)]
      exact s5ns_mobius_neg hγ hm hc (fun k => hf.2 _ (by omega)) k
    · rw [h]
      exact h0 hc
  · intro f hf hc
    refine ⟨(hCb f hf.1 hc).1, fun n hn => ?_⟩
    rcases hn.lt_or_eq with h | h
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
      rw [s5ns_piHat_coeff hγ hc (by omega)]
      have hcc : ContinuousOn (fun z => conj (f z)) unitCircle :=
        Complex.continuous_conj.comp_continuousOn hc
      have hneg (j : ℕ) : circleCoeff (fun z => conj (f z)) (-((j : ℤ) + 1)) = 0 := by
        rw [s5ns_coeff_conj, neg_neg, hf.2 _ (by omega), map_zero]
      have h1 := s5ns_mobius_neg hγ hm hcc hneg k
      have h2 : circleCoeff ((fun z => conj (f z)) ∘ γ) (-((k : ℤ) + 1)) =
          conj (circleCoeff (f ∘ γ) ((k : ℤ) + 1)) := by
        rw [show ((fun z => conj (f z)) ∘ γ) = fun z => conj ((f ∘ γ) z) from rfl, s5ns_coeff_conj, neg_neg]
      rw [h2, map_eq_zero] at h1
      exact h1
    · rw [← h]
      exact h0 hc

/-- If `Π̂(γ)` preserves `W₊`, the powers `γ^M` (`M ≥ 1`) have no negative frequencies. -/
theorem s5ns_wplus_pow {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (hp : ∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus) (M : ℕ) (hM : 0 < M) (k : ℕ) :
    circleCoeff (fun z => γ z ^ M) (-((k : ℤ) + 1)) = 0 := by
  have hW : (fun z : ℂ => z ^ (M : ℤ) / 1) ∈ Wplus := zpow_div_mem_Wplus (by exact_mod_cast hM) 1
  have hc : ContinuousOn (fun z : ℂ => z ^ (M : ℤ) / 1) unitCircle := by
    simp only [zpow_natCast, div_one]
    exact (continuous_pow M).continuousOn
  have h := (hp _ hW hc).2 (-((k : ℤ) + 1)) (by omega)
  rw [s5ns_piHat_coeff hγ hc (by omega)] at h
  simpa [Function.comp_def, zpow_natCast] using h

/-- The inverse of `γ` on `S¹`: continuous, circle-valued, two-sided inverse. -/
theorem s5ns_inv_data {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    ContinuousOn (Function.invFunOn γ unitCircle) unitCircle ∧
      MapsTo (Function.invFunOn γ unitCircle) unitCircle unitCircle ∧
      (∀ z ∈ unitCircle, γ (Function.invFunOn γ unitCircle z) = z) ∧
      (∀ z ∈ unitCircle, Function.invFunOn γ unitCircle (γ z) = z) ∧ InjOn γ unitCircle := by
  have hS1 : unitCircle = sphere (0 : ℂ) 1 := by
    ext z
    simp [unitCircle]
  obtain ⟨lam, hq⟩ := hγ.2
  have hinj : InjOn γ unitCircle := by
    rw [hS1]
    exact hq.1
  have himg : γ '' unitCircle = unitCircle := by
    refine subset_antisymm (image_subset_iff.mpr (s5ns_circle hγ).1) (fun z hz => ?_)
    obtain ⟨f, hc, hm, hp, hu⟩ := s5ns_qs_lift hγ
    obtain ⟨t, ht⟩ := s5ns_lift_surj hc hp (arg z)
    refine ⟨exp (t * I), s5ns_exp_mem t, ?_⟩
    rw [hu, ht]
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [show ‖z‖ = 1 from hz] at h
    simpa using h
  have hK : IsCompact unitCircle := by
    rw [hS1]
    exact isCompact_sphere 0 1
  have hcont := continuousOn_invFunOn_image_of_isCompact hK (s5ns_circle hγ).2 hinj
  rw [himg] at hcont
  refine ⟨hcont, fun z hz => ?_, fun z hz => ?_, fun z hz => hinj.leftInvOn_invFunOn hz, hinj⟩
  · have hz' : z ∈ γ '' unitCircle := by rw [himg]; exact hz
    exact Function.invFunOn_mem hz'
  · have hz' : z ∈ γ '' unitCircle := by rw [himg]; exact hz
    exact Function.invFunOn_eq hz'

/-- If `Π̂(γ)` preserves `W₊`, then `γ⁻¹` has no negative frequencies. Substituting `s = u(t)` turns
`c_{-M}(γ⁻¹)` into `∫ e^{it} e^{iMu(t)} dμ_u(t)`, which the `μ_u`-integration by parts identifies with a multiple of
`c_{-1}(γ^M) = 0`. -/
theorem s5ns_inv_neg {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (hp : ∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus) (m : ℕ) :
    circleCoeff (Function.invFunOn γ unitCircle) (-((m : ℤ) + 1)) = 0 := by
  have hπ : 0 < 2 * π := by positivity
  obtain ⟨f, hc, hm, hp', hu⟩ := s5ns_qs_lift hγ
  have hs := s5ns_lift_surj hc hp'
  set e := StrictMono.orderIsoOfSurjective f hm hs
  have hfe (s : ℝ) : f (e.symm s) = s := StrictMono.orderIsoOfSurjective_self_symm_apply f hm hs s
  have hef (t : ℝ) : e.symm (f t) = t := StrictMono.orderIsoOfSurjective_symm_apply_self f hm hs t
  have hper (s : ℝ) : e.symm (s + 2 * π) = e.symm s + 2 * π := by
    apply hm.injective
    rw [hfe, hp', hfe]
  obtain ⟨-, -, -, hGγ, -⟩ := s5ns_inv_data hγ
  have hGe (θ : ℝ) : Function.invFunOn γ unitCircle (exp (θ * I)) = exp (e.symm θ * I) := by
    have h1 : γ (exp (e.symm θ * I)) = exp (θ * I) := by rw [hu, hfe]
    rw [← h1]
    exact hGγ _ (s5ns_exp_mem _)
  set M : ℕ := m + 1 with hMdef
  have hM : ((M : ℂ) * I) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) I_ne_zero
  -- the coefficient of `γ^M` at `-1` vanishes
  have hL1 := s5ns_wplus_pow hγ hp M (Nat.succ_pos m) 0
  have hint0 : ∫ t in (0 : ℝ)..2 * π, exp (((M : ℂ) * I) * (f t : ℂ)) * exp (t * I) = 0 := by
    unfold circleCoeff fourierCoeff at hL1
    have hne : (1 / (2 * π) : ℂ) ≠ 0 := by
      apply one_div_ne_zero
      exact_mod_cast hπ.ne'
    have h := (mul_eq_zero.mp hL1).resolve_left hne
    rw [← h]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hu, ← Complex.exp_nat_mul]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  -- integration by parts with `Ψ(s) = e^{iMs}/(iM)`
  have hΨ (s : ℝ) : HasDerivAt (fun s : ℝ => exp (((M : ℂ) * I) * (s : ℂ)) / ((M : ℂ) * I))
      (exp (((M : ℂ) * I) * (s : ℂ))) s := by
    have h := (((hasDerivAt_id s).ofReal_comp.const_mul ((M : ℂ) * I)).cexp).div_const ((M : ℂ) * I)
    convert h using 1
    · rfl
    · show exp ((M : ℂ) * I * (s : ℂ)) =
        exp ((M : ℂ) * I * (s : ℂ)) * ((M : ℂ) * I * ((1 : ℝ) : ℂ)) / ((M : ℂ) * I)
      rw [Complex.ofReal_one, mul_one, mul_div_assoc, div_self hM, mul_one]
  have hΨ'c : Continuous (fun s : ℝ => exp (((M : ℂ) * I) * (s : ℂ))) := by fun_prop
  have hexpper (s : ℝ) : exp (((M : ℂ) * I) * (((s + 2 * π : ℝ)) : ℂ)) = exp (((M : ℂ) * I) * (s : ℂ)) := by
    rw [show ((M : ℂ) * I) * (((s + 2 * π : ℝ)) : ℂ) = ((M : ℂ) * I) * (s : ℂ) + (M : ℕ) * (2 * π * I) by
      push_cast; ring]
    exact (Complex.exp_periodic.nat_mul M) _
  have hΨper (s : ℝ) : exp (((M : ℂ) * I) * (((s + 2 * π : ℝ)) : ℂ)) / ((M : ℂ) * I) =
      exp (((M : ℂ) * I) * (s : ℂ)) / ((M : ℂ) * I) := by rw [hexpper]
  have hibp := s5ns_lift_ibp f hc hm hp' hΨ hΨ'c hΨper (-1)
  have hR : ∫ t in (0 : ℝ)..2 * π, exp (((M : ℂ) * I) * ((f t : ℝ) : ℂ)) / ((M : ℂ) * I) *
      exp (-(((-1 : ℤ) : ℂ) * t * I)) = 0 := by
    rw [show (∫ t in (0 : ℝ)..2 * π, exp (((M : ℂ) * I) * ((f t : ℝ) : ℂ)) / ((M : ℂ) * I) *
        exp (-(((-1 : ℤ) : ℂ) * t * I))) =
        (∫ t in (0 : ℝ)..2 * π, exp (((M : ℂ) * I) * (f t : ℂ)) * exp (t * I)) / ((M : ℂ) * I) by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro t _
      simp only
      push_cast
      ring_nf, hint0, zero_div]
  rw [hR, mul_zero] at hibp
  -- back to the coefficient of `γ⁻¹`
  set H : ℝ → ℂ := fun θ => exp (e.symm θ * I) * exp (-(((-((m : ℤ) + 1) : ℤ) : ℂ) * θ * I)) with hH
  have hHc : Continuous H :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp e.symm.continuous).mul continuous_const)).mul
      (by fun_prop)
  have hHp : Function.Periodic H (2 * π) := by
    intro θ
    simp only [hH, hper]
    congr 1
    · rw [show ((e.symm θ + 2 * π : ℝ) : ℂ) * I = (e.symm θ : ℂ) * I + 2 * π * I by push_cast; ring]
      exact Complex.exp_periodic _
    · rw [show -(((-((m : ℤ) + 1) : ℤ) : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) =
          -(((-((m : ℤ) + 1) : ℤ) : ℂ) * (θ : ℂ) * I) + (M : ℕ) * (2 * π * I) by
        simp only [hMdef]
        push_cast
        ring]
      exact (Complex.exp_periodic.nat_mul M) _
  have hcoef : circleCoeff (Function.invFunOn γ unitCircle) (-((m : ℤ) + 1)) =
      (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π, H θ := by
    unfold circleCoeff fourierCoeff
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [hH, hGe]
  rw [hcoef]
  have hshift := hHp.intervalIntegral_add_eq 0 (f 0)
  rw [zero_add] at hshift
  rw [hshift, intervalIntegral.integral_of_le (by linarith), ← show f (2 * π) = f 0 + 2 * π by
    simpa using hp' 0, ← s5ns_lift_cov f hc hm hp' hHc 0 (2 * π)]
  rw [show (∫ t in Ioc 0 (2 * π), H (f t) ∂f.measure) =
      ∫ t in Ioc 0 (2 * π), exp (-(((-1 : ℤ) : ℂ) * t * I)) * exp (((M : ℂ) * I) * (f t : ℂ)) ∂f.measure by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [hH, hef]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [hMdef]
      push_cast
      ring]
  rw [hibp, mul_zero]

/-- N5b. Preserving `W₊` and `W₋` forces `γ ∈ Möb(S¹)`. Both `γ` and `γ⁻¹` extend holomorphically into `𝔻`
(`s5ns_holo_ext`, `s5ns_inv_neg`); the maximum principle makes the extensions mutually inverse self-maps of `𝔻`, and
the classification of disc automorphisms (`exists_rotation_blaschke_of_isConformalOnto_unitDisc`) makes `γ` a Blaschke
factor on `S¹`. -/
theorem s5ns_preserves_mobius {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ)
    (hp : ∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus)
    (hn : ∀ f ∈ Wminus, ContinuousOn f unitCircle → piHat γ f ∈ Wminus) :
    IsCircleMobius γ := by
  have hS1 : unitCircle = sphere (0 : ℂ) 1 := by
    ext z
    simp [unitCircle]
  have hUD : unitDisc = ball (0 : ℂ) 1 := rfl
  have hball : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hfr : frontier (ball (0 : ℂ) 1) = sphere 0 1 := frontier_ball 0 one_ne_zero
  have hcb : unitCircle ⊆ closedBall (0 : ℂ) 1 := fun z hz => mem_closedBall_zero_iff.mpr (le_of_eq hz)
  -- holomorphic extensions of `γ` and `γ⁻¹`
  have hneg1 (k : ℕ) : circleCoeff γ (-((k : ℤ) + 1)) = 0 := by
    have h := s5ns_wplus_pow hγ hp 1 one_pos k
    simpa using h
  obtain ⟨φ, hφc, hφe, hφd⟩ := s5ns_holo_ext (s5ns_circle hγ).2 hneg1
  obtain ⟨hGc, hGm, hγG, hGγ, hinj⟩ := s5ns_inv_data hγ
  obtain ⟨ψ, hψc, hψe, hψd⟩ := s5ns_holo_ext hGc (s5ns_inv_neg hγ hp)
  have hdc {F : ℂ → ℂ} (hc : ContinuousOn F (closedBall 0 1)) (hd : DifferentiableOn ℂ F unitDisc) :
      DiffContOnCl ℂ F (ball 0 1) := ⟨hd, by rw [hball]; exact hc⟩
  have hle {F : ℂ → ℂ} (hc : ContinuousOn F (closedBall 0 1)) (hd : DifferentiableOn ℂ F unitDisc)
      (hb : ∀ z ∈ unitCircle, ‖F z‖ ≤ 1) : ∀ z ∈ closedBall (0 : ℂ) 1, ‖F z‖ ≤ 1 := fun z hz =>
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdc hc hd)
      (fun w hw => hb w (by rw [hfr] at hw; rw [hS1]; exact hw)) (by rw [hball]; exact hz)
  have hφ1 := hle hφc hφd (fun z hz => by rw [hφe hz]; exact le_of_eq ((s5ns_circle hγ).1 hz))
  have hψ1 := hle hψc hψd (fun z hz => by rw [hψe hz]; exact le_of_eq (hGm hz))
  -- the extensions map `𝔻` into `𝔻`
  have hstrict {F : ℂ → ℂ} (hc : ContinuousOn F (closedBall 0 1)) (hd : DifferentiableOn ℂ F unitDisc)
      (h1 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖F z‖ ≤ 1) (hne : F 1 ≠ F (-1)) : MapsTo F unitDisc unitDisc := by
    intro z hz
    by_contra hcon
    have hz1 : ‖F z‖ = 1 := le_antisymm (h1 z (ball_subset_closedBall hz))
      (not_lt.mp fun h => hcon (mem_ball_zero_iff.mpr h))
    have hmax : IsMaxOn (norm ∘ F) (ball (0 : ℂ) 1) z := isMaxOn_iff.mpr fun w hw => by
      simp only [Function.comp_apply, hz1]
      exact h1 w (ball_subset_closedBall hw)
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) 1).isPreconnected
      isOpen_ball hd hz hmax
    have hcl : EqOn F (Function.const ℂ (F z)) (closedBall 0 1) :=
      hconst.of_subset_closure hc continuousOn_const ball_subset_closedBall (by rw [hball])
    apply hne
    rw [hcl (show (1 : ℂ) ∈ closedBall 0 1 by simp), hcl (show (-1 : ℂ) ∈ closedBall 0 1 by simp)]
    rfl
  have hm1 : (1 : ℂ) ∈ unitCircle := by simp [unitCircle]
  have hm1' : (-1 : ℂ) ∈ unitCircle := by simp [unitCircle]
  have hφD : MapsTo φ unitDisc unitDisc := hstrict hφc hφd hφ1 (by
    rw [hφe hm1, hφe hm1']
    intro h
    have h3 := congrArg Complex.re (hinj hm1 hm1' h)
    norm_num at h3)
  have hψD : MapsTo ψ unitDisc unitDisc := hstrict hψc hψd hψ1 (by
    rw [hψe hm1, hψe hm1']
    intro h
    have h2 := congrArg γ h
    rw [hγG _ hm1, hγG _ hm1'] at h2
    have h3 := congrArg Complex.re h2
    norm_num at h3)
  have hmapsB {F : ℂ → ℂ} (h1 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖F z‖ ≤ 1) : MapsTo F (closedBall 0 1) (closedBall 0 1) :=
    fun z hz => mem_closedBall_zero_iff.mpr (h1 z hz)
  -- the extensions are mutually inverse on `𝔻`
  have hcomp {F K : ℂ → ℂ} (hFc : ContinuousOn F (closedBall 0 1)) (hFd : DifferentiableOn ℂ F unitDisc)
      (hKc : ContinuousOn K (closedBall 0 1)) (hKd : DifferentiableOn ℂ K unitDisc)
      (hF1 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖F z‖ ≤ 1) (hFD : MapsTo F unitDisc unitDisc)
      (hfront : ∀ z ∈ unitCircle, K (F z) = z) : ∀ z ∈ unitDisc, K (F z) = z := by
    have hd : DiffContOnCl ℂ (K ∘ F) (ball 0 1) := by
      refine hdc (hKc.comp hFc (hmapsB hF1)) fun z hz => ?_
      exact ((hKd.differentiableAt (isOpen_ball.mem_nhds (hFD hz))).comp z
        (hFd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
    have h := Complex.eqOn_of_eqOn_frontier isBounded_ball hd (hdc continuousOn_id differentiableOn_id)
      (fun z hz => by
        rw [hfr] at hz
        exact hfront z (by rw [hS1]; exact hz))
    exact fun z hz => h hz
  have hψφ := hcomp hφc hφd hψc hψd hφ1 hφD (fun z hz => by rw [hφe hz, hψe ((s5ns_circle hγ).1 hz), hGγ z hz])
  have hφψ := hcomp hψc hψd hφc hφd hψ1 hψD (fun z hz => by rw [hψe hz, hφe (hGm hz), hγG z hz])
  have hconf : IsConformalOnto φ unitDisc unitDisc := by
    refine ⟨hφd, fun x hx y hy hxy => by rw [← hψφ x hx, ← hψφ y hy, hxy], ?_⟩
    exact subset_antisymm (image_subset_iff.mpr hφD) (fun w hw => ⟨ψ w, hψD hw, hφψ w hw⟩)
  obtain ⟨c, a, hc1, ha, heq⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hconf
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc1
    norm_num at hc1
  -- the Blaschke factor on `𝔻̄`
  have hden (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : (1 : ℂ) - conj a * z ≠ 0 := by
    intro h
    have hlt : ‖conj a * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      have := mem_closedBall_zero_iff.mp hz
      nlinarith [norm_nonneg a, norm_nonneg z]
    have h' : conj a * z = 1 := by linear_combination -h
    rw [h', norm_one] at hlt
    exact lt_irrefl _ hlt
  have hcont : ContinuousOn (fun z => c * blaschke a z) (closedBall 0 1) := by
    simp only [blaschke]
    exact continuousOn_const.mul ((continuous_id.sub continuous_const).continuousOn.div
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn hden)
  have hcl : EqOn φ (fun z => c * blaschke a z) (closedBall 0 1) :=
    heq.of_subset_closure hφc hcont ball_subset_closedBall (by rw [hUD, hball])
  -- the Möbius transformation
  have hval (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      mobiusExt c (-(c * a)) (-conj a) 1 (z : ExtPlane) = ((c * blaschke a z : ℂ) : ExtPlane) := by
    have hd2 : -conj a * z + 1 ≠ 0 := by
      intro h
      exact hden z hz (by linear_combination h)
    change (if -conj a * z + 1 = 0 then extInf else (((c * z + -(c * a)) / (-conj a * z + 1) : ℂ) : ExtPlane)) = _
    rw [if_neg hd2, blaschke]
    congr 1
    have := hden z hz
    field_simp
    ring
  refine ⟨mobiusExt c (-(c * a)) (-conj a) 1, ⟨⟨c, -(c * a), -conj a, 1, ?_, rfl⟩, ?_⟩, fun z hz => ?_⟩
  · rw [show c * 1 - -(c * a) * -conj a = c * (1 - a * conj a) by ring]
    exact mul_ne_zero hc0 (one_sub_mul_conj_ne_zero ha)
  · apply subset_antisymm
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hval z (ball_subset_closedBall hz)]
      refine ⟨_, ?_, rfl⟩
      rw [hUD, mem_ball_zero_iff, norm_mul, hc1, one_mul]
      exact blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp hz)
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : ‖conj c * w‖ < 1 := by
        rw [norm_mul, Complex.norm_conj, hc1, one_mul]
        exact mem_ball_zero_iff.mp hw
      have hza : ‖-a‖ < 1 := by simpa using ha
      set z := blaschke (-a) (conj c * w)
      have hz : z ∈ unitDisc := mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hza hw')
      refine ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, ?_⟩
      rw [hval z (ball_subset_closedBall hz), blaschke_blaschke_neg ha hw']
      congr 1
      rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
      simp
  · rw [hval z (hcb hz)]
    congr 1
    rw [← hφe hz]
    exact hcl (hcb hz)

/-- (TT:5478–5486, [NS95]) For `γ ∈ Homeo_qs(S¹)`, `Π̂(γ)` is a bounded symplectomorphism of `𝓗_ℂ`, real on `𝓗`.
`γ ↦ Π̂(γ)` is a right action. `Π̂(γ)` preserves `W₊` and `W₋` iff `γ ∈ Möb(S¹)`.
[CORRECTION 2026-10-28, Program G] Composition with a (possibly singular) quasisymmetric map is not defined on
a.e.-classes, so the literal composition `piHat` is stated on continuous representatives, which are dense in `𝓗_ℂ`. The
`H^{1/2}` bound (first clause) then determines the action on all of `𝓗_ℂ` as the unique bounded extension
(`s5ca_completed`, `s5ca_completed_unique`). -/
theorem s5ns_nag_sullivan {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∃ C : ℝ, ∀ f ∈ HC, ContinuousOn f unitCircle → piHat γ f ∈ HC ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ f) n‖ ^ 2) ≤ C * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2) ∧
    (∀ f ∈ HR, ContinuousOn f unitCircle → piHat γ f ∈ HR) ∧
    (∀ f ∈ HC, ∀ g ∈ HC, ContinuousOn f unitCircle → ContinuousOn g unitCircle →
      thetaSymp (piHat γ f) (piHat γ g) = thetaSymp f g) ∧
    (∀ γ' : ℂ → ℂ, IsQSCircleHomeo γ' → ∀ f ∈ HC, ContinuousOn f unitCircle → ∀ z ∈ unitCircle,
      piHat (γ ∘ γ') f z = piHat γ' (piHat γ f) z) ∧
    ((∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus) ∧
      (∀ f ∈ Wminus, ContinuousOn f unitCircle → piHat γ f ∈ Wminus) ↔ IsCircleMobius γ) :=
  ⟨s5ns_bound hγ, s5ns_real hγ, s5ns_theta hγ, s5ns_right hγ,
    ⟨fun h => s5ns_preserves_mobius hγ h.1 h.2, s5ns_mobius_preserves hγ⟩⟩

/-- (TT:5478–5486, [NS95]) For `γ ∈ Homeo_qs(S¹)`, `Π̂(γ)` is a bounded symplectomorphism of `𝓗_ℂ`, real on `𝓗`.
`γ ↦ Π̂(γ)` is a right action. `Π̂(γ)` preserves `W₊` and `W₋` iff `γ ∈ Möb(S¹)`.
[CORRECTION 2026-10-28, Program G] Composition with a (possibly singular) quasisymmetric map is not defined on
a.e.-classes, so the literal composition `piHat` is stated on continuous representatives, which are dense in `𝓗_ℂ`. The
`H^{1/2}` bound (first clause) then determines the action on all of `𝓗_ℂ` as the unique bounded extension
(`s5ca_completed`, `s5ca_completed_unique`). -/
theorem nag_sullivan {γ : ℂ → ℂ} (hγ : IsQSCircleHomeo γ) :
    (∃ C : ℝ, ∀ f ∈ HC, ContinuousOn f unitCircle → piHat γ f ∈ HC ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff (piHat γ f) n‖ ^ 2) ≤ C * ∑' n : ℤ, |(n : ℝ)| * ‖circleCoeff f n‖ ^ 2) ∧
    (∀ f ∈ HR, ContinuousOn f unitCircle → piHat γ f ∈ HR) ∧
    (∀ f ∈ HC, ∀ g ∈ HC, ContinuousOn f unitCircle → ContinuousOn g unitCircle →
      thetaSymp (piHat γ f) (piHat γ g) = thetaSymp f g) ∧
    (∀ γ' : ℂ → ℂ, IsQSCircleHomeo γ' → ∀ f ∈ HC, ContinuousOn f unitCircle → ∀ z ∈ unitCircle,
      piHat (γ ∘ γ') f z = piHat γ' (piHat γ f) z) ∧
    ((∀ f ∈ Wplus, ContinuousOn f unitCircle → piHat γ f ∈ Wplus) ∧
      (∀ f ∈ Wminus, ContinuousOn f unitCircle → piHat γ f ∈ Wminus) ↔ IsCircleMobius γ) :=
  s5ns_nag_sullivan hγ

end TakhtajanTeo.Ch2
