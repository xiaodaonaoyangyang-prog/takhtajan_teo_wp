import TakhtajanTeo.Ch1.QCVariationBers

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Real BoundedContinuousFunction
open LiZhongQC

noncomputable section

namespace TakhtajanTeo
namespace QCV

/-- radial integral -/
theorem qcv_radial (n : ℕ) :
    ∫ r in Ioi (1 : ℝ), r * (r ^ 2 - 1) ^ 2 * (r ^ (2 * n + 8))⁻¹ = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hx : ∀ r ∈ Ioi (1 : ℝ), r * (r ^ 2 - 1) ^ 2 * (r ^ (2 * n + 8))⁻¹ =
      r ^ (-(2 * n + 3 : ℝ)) - 2 * r ^ (-(2 * n + 5 : ℝ)) + r ^ (-(2 * n + 7 : ℝ)) := by
    intro r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    have e : ∀ k : ℝ, r ^ (-k) = (r ^ k)⁻¹ := fun k => Real.rpow_neg hr0.le k
    rw [e, e, e]
    have h3 : r ^ (2 * n + 3 : ℝ) = r ^ (2 * n + 3) := by
      rw [show (2 * n + 3 : ℝ) = ((2 * n + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h5 : r ^ (2 * n + 5 : ℝ) = r ^ (2 * n + 5) := by
      rw [show (2 * n + 5 : ℝ) = ((2 * n + 5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h7 : r ^ (2 * n + 7 : ℝ) = r ^ (2 * n + 7) := by
      rw [show (2 * n + 7 : ℝ) = ((2 * n + 7 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [h3, h5, h7]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hx]
  have i3 : IntegrableOn (fun r : ℝ => r ^ (-(2 * n + 3 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos
  have i5 : IntegrableOn (fun r : ℝ => r ^ (-(2 * n + 5 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos
  have i7 : IntegrableOn (fun r : ℝ => r ^ (-(2 * n + 7 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos
  have i35 : IntegrableOn (fun r : ℝ => r ^ (-(2 * n + 3 : ℝ)) - 2 * r ^ (-(2 * n + 5 : ℝ))) (Ioi 1) :=
    i3.sub (i5.const_mul 2)
  rw [integral_add i35 i7, integral_sub i3 (i5.const_mul 2), integral_const_mul,
    integral_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos,
    integral_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos,
    integral_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos]
  simp only [Real.one_rpow]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have a1 : -(2 * (n : ℝ) + 3) + 1 = -(2 * (n + 1)) := by ring
  have a2 : -(2 * (n : ℝ) + 5) + 1 = -(2 * (n + 2)) := by ring
  have a3 : -(2 * (n : ℝ) + 7) + 1 = -(2 * (n + 3)) := by ring
  rw [a1, a2, a3]
  field_simp
  ring


theorem qcv_angular (k : ℤ) :
    ∫ θ in Ioo (-π) π, Complex.exp (Complex.I * (k : ℂ) * (θ : ℂ)) = if k = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases hk : k = 0
  · subst hk
    simp
    ring
  · rw [if_neg hk]
    have hc : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (Complex.I * (k : ℂ) * (π : ℂ)) = (-1 : ℂ) ^ k := by
      rw [show Complex.I * (k : ℂ) * (π : ℂ) = (k : ℂ) * ((π : ℂ) * Complex.I) by ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have h2 : Complex.exp (Complex.I * (k : ℂ) * ((-π : ℝ) : ℂ)) = (-1 : ℂ) ^ k := by
      rw [show Complex.I * (k : ℂ) * ((-π : ℝ) : ℂ) = (k : ℂ) * (((-π : ℝ) : ℂ) * Complex.I) by ring,
        Complex.exp_int_mul]
      push_cast
      rw [show -(π : ℂ) * Complex.I = -((π : ℂ) * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]
      simp
    rw [h1, h2]; simp


theorem qcv_polar_mono (n m : ℕ) :
    ∫ ζ in unitDiscExterior, (((‖ζ‖ ^ 2 - 1) ^ 2 : ℝ) : ℂ) * ((conj ζ ^ (n + 4))⁻¹ * (ζ ^ (m + 4))⁻¹) =
      if n = m then ((2 * π / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℝ) : ℂ) else 0 := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  let h : ℝ → ℝ := fun r => r * (r ^ 2 - 1) ^ 2 * (r ^ (n + m + 8))⁻¹
  have key : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • unitDiscExterior.indicator (fun ζ : ℂ => (((‖ζ‖ ^ 2 - 1) ^ 2 : ℝ) : ℂ) *
        ((conj ζ ^ (n + 4))⁻¹ * (ζ ^ (m + 4))⁻¹)) (Complex.polarCoord.symm p) =
      ((Set.indicator (Ioi 1) h p.1 : ℝ) : ℂ) * Complex.exp (Complex.I * (((n : ℤ) - m : ℤ) : ℂ) * (p.2 : ℂ)) := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [mem_Ioi] at hr
    have hζ : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr
    have hE : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    by_cases h1 : 1 < r
    · have hmem : Complex.polarCoord.symm (r, θ) ∈ unitDiscExterior := by
        show 1 < ‖Complex.polarCoord.symm (r, θ)‖
        rw [hnorm]; exact h1
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show r ∈ Ioi (1 : ℝ) from h1), hnorm]
      have hc : conj (Complex.polarCoord.symm (r, θ)) = (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ := by
        rw [hζ, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
        simp [← Complex.exp_neg]
      have hexp : Complex.exp (Complex.I * (((n : ℤ) - m : ℤ) : ℂ) * (θ : ℂ)) =
          Complex.exp ((θ : ℂ) * Complex.I) ^ n * (Complex.exp ((θ : ℂ) * Complex.I) ^ m)⁻¹ := by
        rw [show Complex.I * (((n : ℤ) - m : ℤ) : ℂ) * (θ : ℂ) = (((n : ℤ) - m : ℤ) : ℂ) * ((θ : ℂ) * Complex.I) by ring,
          Complex.exp_int_mul, zpow_sub₀ hE]
        simp [div_eq_mul_inv]
      rw [hexp, hc, hζ]
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      simp only [h, Complex.real_smul]
      push_cast
      generalize Complex.exp ((θ : ℂ) * Complex.I) = E at *
      have a1 : ((↑r * E⁻¹) ^ (n + 4))⁻¹ = ((r : ℂ) ^ (n + 4))⁻¹ * E ^ (n + 4) := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv]
      have a2 : ((↑r * E) ^ (m + 4))⁻¹ = ((r : ℂ) ^ (m + 4))⁻¹ * (E ^ (m + 4))⁻¹ := by
        rw [mul_pow, mul_inv]
      rw [a1, a2]
      field_simp
      ring
    · have hmem : Complex.polarCoord.symm (r, θ) ∉ unitDiscExterior := by
        show ¬ 1 < ‖Complex.polarCoord.symm (r, θ)‖
        rw [hnorm]; exact h1
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show r ∉ Ioi (1 : ℝ) from h1)]
      simp
  rw [← integral_indicator hmeas, ← Complex.integral_comp_polarCoord_symm, polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun r : ℝ => ((Set.indicator (Ioi 1) h r : ℝ) : ℂ))
    (fun θ : ℝ => Complex.exp (Complex.I * (((n : ℤ) - m : ℤ) : ℂ) * (θ : ℂ)))]
  rw [qcv_angular]
  by_cases hnm : n = m
  · subst hnm
    simp only [sub_self, if_true]
    rw [integral_complex_ofReal, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi]
    simp only [max_eq_right zero_le_one] at *
    have hr := qcv_radial n
    have hh : ∫ x in Ioi (1 : ℝ), h x = 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
      rw [← hr]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [h]
      rw [show n + n + 8 = 2 * n + 8 by ring]
    rw [hh, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · have : ((n : ℤ) - m) ≠ 0 := by omega
    simp [this, hnm]


/-! ### Series expansion -/

def qcvW (n m : ℕ) (ζ : ℂ) : ℂ := (((‖ζ‖ ^ 2 - 1) ^ 2 : ℝ) : ℂ) * ((conj ζ ^ (n + 4))⁻¹ * (ζ ^ (m + 4))⁻¹)

theorem qcv_w_bound (n m : ℕ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) : ‖qcvW n m ζ‖ ≤ 16 * (1 + ‖ζ‖) ^ (-4 : ℝ) := by
  set a : ℝ := ‖ζ‖ with ha
  have ha0 : 0 < a := by linarith
  have hn : ‖qcvW n m ζ‖ = (a ^ 2 - 1) ^ 2 * ((a ^ (n + 4))⁻¹ * (a ^ (m + 4))⁻¹) := by
    unfold qcvW
    rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, norm_pow, Complex.norm_real, Complex.norm_conj, ← ha,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : (a ^ 2 - 1) ^ 2 ≤ a ^ 4 := by nlinarith [sq_nonneg a]
  have h2 : (a ^ (n + 4))⁻¹ ≤ (a ^ 4)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hζ.le (by omega))
  have h3 : (a ^ (m + 4))⁻¹ ≤ (a ^ 4)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hζ.le (by omega))
  have h4 : (a ^ 2 - 1) ^ 2 * ((a ^ (n + 4))⁻¹ * (a ^ (m + 4))⁻¹) ≤ a ^ 4 * ((a ^ 4)⁻¹ * (a ^ 4)⁻¹) := by
    gcongr
  have h5 : a ^ 4 * ((a ^ 4)⁻¹ * (a ^ 4)⁻¹) = (a ^ 4)⁻¹ := by field_simp
  have h6 : (a ^ 4)⁻¹ ≤ 16 * (1 + a) ^ (-4 : ℝ) := by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have this : (1 + a) ^ 4 ≤ 16 * a ^ 4 := by nlinarith [pow_pos ha0 2, pow_pos ha0 3, pow_pos ha0 4, sq_nonneg (a - 1)]
    calc (a ^ 4)⁻¹ = 16 * (16 * a ^ 4)⁻¹ := by field_simp
      _ ≤ 16 * ((1 + a) ^ 4)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) this) (by norm_num)
  rw [hn]
  exact h4.trans (h5.le.trans h6)


theorem qcv_choose3 (n : ℕ) : (((n + 3).choose 3 : ℕ) : ℂ) = ((n : ℂ) + 1) * ((n : ℂ) + 2) * ((n : ℂ) + 3) / 6 := by
  have h1 := Nat.add_one_mul_choose_eq (n + 2) 2
  have h2 := Nat.add_one_mul_choose_eq (n + 1) 1
  have h3 : (n + 1).choose 1 = n + 1 := by simp
  rw [h3] at h2
  have e : ((n + 3).choose 3) * 6 = (n + 1) * (n + 2) * (n + 3) := by
    have a1 : (n + 3).choose 3 * 3 = (n + 2 + 1) * (n + 2).choose 2 := by
      simpa [mul_comm] using h1.symm
    have a2 : (n + 2).choose 2 * 2 = (n + 1 + 1) * (n + 1) := by
      simpa [mul_comm] using h2.symm
    nlinarith [a1, a2]
  have : (((n + 3).choose 3 : ℕ) : ℂ) * 6 = ((n : ℂ) + 1) * ((n : ℂ) + 2) * ((n : ℂ) + 3) := by exact_mod_cast e
  field_simp
  linear_combination this

theorem qcv_series_int {c : ℕ → ℂ} (hc : Summable fun n => ‖c n‖) {φ0 : ℂ → ℂ}
    (hφ : ∀ u : ℂ, ‖u‖ < 1 → HasSum (fun n => c n * u ^ n) (φ0 u)) {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4
      = -((π : ℂ) / 6) * ∑' n, c n * z ^ n := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set μ : Measure ℂ := volume.restrict unitDiscExterior with hμ
  let a : ℕ × ℕ → ℂ := fun p => -(1 / 2 : ℂ) * c p.1 * (((p.2 + 3).choose 3 : ℕ) : ℂ) * z ^ p.2
  let g : ℕ × ℕ → ℂ → ℂ := fun p ζ => a p * qcvW p.1 p.2 ζ
  have hB : Integrable (fun ζ : ℂ => 16 * (1 + ‖ζ‖) ^ (-4 : ℝ)) μ := by
    have := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 4) (by simp [Complex.finrank_real_complex]; norm_num)
    exact (this.const_mul 16).integrableOn
  have hwint : ∀ n m : ℕ, Integrable (qcvW n m) μ := by
    intro n m
    refine hB.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ hmeas
      intro ζ hζ
      have hζ0 : ζ ≠ 0 := by
        intro h; rw [h] at hζ; simp [unitDiscExterior] at hζ; norm_num at hζ
      unfold qcvW
      refine ContinuousAt.continuousWithinAt ?_
      have : ContinuousAt (fun ζ : ℂ => conj ζ) ζ := (Complex.continuous_conj).continuousAt
      fun_prop (disch := simp [hζ0])
    · filter_upwards [ae_restrict_mem hmeas] with ζ hζ
      exact qcv_w_bound n m hζ
  have hgint : ∀ p, Integrable (g p) μ := fun p => (hwint p.1 p.2).const_mul (a p)
  have hch : Summable fun m : ℕ => (((m + 3).choose 3 : ℕ) : ℝ) * ‖z‖ ^ m :=
    summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 3 (r := ‖z‖) (by simpa using hz)
  have hsa : Summable fun p : ℕ × ℕ => ‖a p‖ := by
    have := (hc.mul_of_nonneg hch (fun _ => norm_nonneg _) (fun _ => by positivity)).mul_left (1 / 2 : ℝ)
    refine this.congr ?_
    intro p
    simp only [a, norm_mul, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_natCast]
    norm_num
    ring
  have hnorm_int : ∀ p, ∫ ζ, ‖g p ζ‖ ∂μ ≤ ‖a p‖ * ∫ ζ, 16 * (1 + ‖ζ‖) ^ (-4 : ℝ) ∂μ := by
    intro p
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hB.const_mul _) ?_
    filter_upwards [ae_restrict_mem hmeas] with ζ hζ
    simp only [g, norm_mul]
    exact mul_le_mul_of_nonneg_left (qcv_w_bound p.1 p.2 hζ) (norm_nonneg _)
  have hsum : Summable fun p => ∫ ζ, ‖g p ζ‖ ∂μ :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) hnorm_int (hsa.mul_right _)
  have hpt : ∀ ζ ∈ unitDiscExterior, HasSum (fun p => g p ζ)
      ((-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4) := by
    intro ζ hζ
    have hζ1 : 1 < ‖ζ‖ := hζ
    have hζ0 : ζ ≠ 0 := norm_pos_iff.1 (by linarith)
    have hcz : conj ζ ≠ 0 := by simpa using hζ0
    have hu : ‖(conj ζ)⁻¹‖ < 1 := by
      rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hζ1
    have hr : ‖z / ζ‖ < 1 := by
      rw [norm_div, div_lt_one (by linarith)]; linarith
    have hs1 := hφ _ hu
    have hs2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 3 hr
    have hf : Summable fun n : ℕ => ‖c n * ((conj ζ)⁻¹) ^ n‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hc
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hu.le)
    have hh : Summable fun m : ℕ => ‖(((m + 3).choose 3 : ℕ) : ℂ) * (z / ζ) ^ m‖ := by
      have := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 3 (r := ‖z / ζ‖) (by rwa [norm_norm])
      refine this.congr fun m => ?_
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hsumm : Summable fun p : ℕ × ℕ => (c p.1 * ((conj ζ)⁻¹) ^ p.1) * ((((p.2 + 3).choose 3 : ℕ) : ℂ) * (z / ζ) ^ p.2) := by
      refine Summable.of_norm ?_
      have := hf.mul_of_nonneg hh (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      refine this.congr fun p => ?_
      simp only [norm_mul, mul_assoc]
    have hs := (hs1.mul hs2 hsumm).mul_left (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) / (conj ζ ^ 4 * ζ ^ 4))
    have hz1 : 1 - z / ζ ≠ 0 := by
      intro h
      have : z / ζ = 1 := by linear_combination -h
      rw [this] at hr; simp at hr
    have e1 : (fun p : ℕ × ℕ => g p ζ) = fun p : ℕ × ℕ =>
        (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) / (conj ζ ^ 4 * ζ ^ 4)) *
          ((c p.1 * ((conj ζ)⁻¹) ^ p.1) * ((((p.2 + 3).choose 3 : ℕ) : ℂ) * (z / ζ) ^ p.2)) := by
      funext p
      simp only [g, a, qcvW]
      have : (((‖ζ‖ ^ 2 - 1) ^ 2 : ℝ) : ℂ) = (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
        congr 1; ring
      rw [this]
      simp only [pow_add, mul_inv, div_pow, inv_pow]
      field_simp
    have e2 : (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4 =
        (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) / (conj ζ ^ 4 * ζ ^ 4)) *
          (φ0 ((conj ζ)⁻¹) * (1 / (1 - z / ζ) ^ (3 + 1))) := by
      have hz2 : ζ - z ≠ 0 := by
        intro h
        apply hz1
        have : z = ζ := by linear_combination -h
        rw [this]; field_simp; ring
      field_simp
      simp only [div_pow]
      field_simp
      ring
    rw [e1, e2]
    exact hs
  have h1 := integral_tsum_of_summable_integral_norm hgint hsum
  have hdiag : ∀ p : ℕ × ℕ, p ∉ Set.range (fun n : ℕ => (n, n)) → ∫ ζ, g p ζ ∂μ = 0 := by
    rintro ⟨n, m⟩ hp
    have hnm : n ≠ m := fun h => hp ⟨n, by simp [h]⟩
    have := qcv_polar_mono n m
    simp only [g, integral_const_mul]
    rw [show (∫ ζ, qcvW n m ζ ∂μ) = 0 by
      simpa [qcvW, hnm] using this]
    simp
  have hdiagsum : ∑' p, ∫ ζ, g p ζ ∂μ = ∑' n : ℕ, ∫ ζ, g (n, n) ζ ∂μ :=
    (Function.Injective.tsum_eq (g := fun n : ℕ => (n, n)) (fun x y h => (Prod.mk.inj h).1)
      (fun p hp => by
        by_contra hh
        exact hp (hdiag p hh))).symm
  calc ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4
      = ∫ ζ, ∑' p, g p ζ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hmeas] with ζ hζ
        exact (hpt ζ hζ).tsum_eq.symm
    _ = ∑' p, ∫ ζ, g p ζ ∂μ := h1.symm
    _ = ∑' n : ℕ, ∫ ζ, g (n, n) ζ ∂μ := hdiagsum
    _ = ∑' n : ℕ, (-((π : ℂ) / 6)) * (c n * z ^ n) := by
        refine tsum_congr fun n => ?_
        simp only [g, integral_const_mul]
        rw [show (∫ ζ, qcvW n n ζ ∂μ) = ((2 * π / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℝ) : ℂ) by
          simpa [qcvW] using qcv_polar_mono n n]
        simp only [a, qcv_choose3]
        push_cast
        have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have h2 : ((n : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
        have h3 : ((n : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : n + 3 ≠ 0)
        field_simp
    _ = -((π : ℂ) / 6) * ∑' n, c n * z ^ n := tsum_mul_left

/-- Reproducing formula for functions holomorphic on a ball of radius `> 1`. -/
theorem qcv_reproduce_ball {φ0 : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hd : DifferentiableOn ℂ φ0 (ball 0 R))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * φ0 ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4
      = -((π : ℂ) / 6) * φ0 z := by
  set ρ : ℝ := (1 + R) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hρR : ρ < R := by rw [hρ]; linarith
  set ρ' : NNReal := ⟨ρ, by linarith⟩ with hρ'
  have hρ'pos : 0 < ρ' := by
    show (0 : NNReal) < ⟨ρ, _⟩
    exact_mod_cast (by linarith : (0 : ℝ) < ρ)
  have hdc : DifferentiableOn ℂ φ0 (closedBall 0 (ρ' : ℝ)) :=
    hd.mono (closedBall_subset_ball hρR)
  have hps := hdc.hasFPowerSeriesOnBall hρ'pos
  set p := cauchyPowerSeries φ0 0 (ρ' : ℝ) with hp
  have hrad : ((1 : NNReal) : ENNReal) < p.radius := by
    refine lt_of_lt_of_le ?_ hps.r_le
    exact_mod_cast hρ1
  have hc : Summable fun n => ‖p.coeff n‖ := by
    have := p.summable_norm_mul_pow hrad
    simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef] using this
  have hφ : ∀ u : ℂ, ‖u‖ < 1 → HasSum (fun n => p.coeff n * u ^ n) (φ0 u) := by
    intro u hu
    have hmem : u ∈ Metric.eball (0 : ℂ) ρ' := by
      rw [Metric.mem_eball, edist_zero_right]
      have : (‖u‖₊ : ℝ) < ρ := by simp only [coe_nnnorm]; linarith
      exact_mod_cast this
    have := hps.hasSum hmem
    simp only [zero_add] at this
    have e : (fun n => p n (fun _ => u)) = fun n => p.coeff n * u ^ n := by
      funext n
      rw [p.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
    rw [e] at this
    exact this
  rw [qcv_series_int hc hφ hz, (hφ z hz).tsum_eq]


theorem qcv_inv4 {a : ℝ} (ha : 1 < a) : (a ^ 4)⁻¹ ≤ 16 * (1 + a) ^ (-4 : ℝ) := by
  have ha0 : 0 < a := by linarith
  rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have this : (1 + a) ^ 4 ≤ 16 * a ^ 4 := by
    nlinarith [pow_pos ha0 2, pow_pos ha0 3, pow_pos ha0 4, sq_nonneg (a - 1)]
  calc (a ^ 4)⁻¹ = 16 * (16 * a ^ 4)⁻¹ := by field_simp
    _ ≤ 16 * ((1 + a) ^ 4)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) this) (by norm_num)

theorem qcv_dil_bound (φ : AInf unitDisc) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    ‖-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((s : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4‖
      ≤ ‖φ‖ / 2 := by
  set a : ℝ := ‖ζ‖ with ha
  have ha0 : 0 < a := by linarith
  have hw : ‖(conj ζ)⁻¹‖ = a⁻¹ := by rw [norm_inv, Complex.norm_conj]
  set x : ℂ := (s : ℂ) * (conj ζ)⁻¹ with hx
  have hxn : ‖x‖ = s * a⁻¹ := by
    rw [hx, norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hinv : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ hζ
  have hxlt : ‖x‖ < 1 := by
    rw [hxn]
    calc s * a⁻¹ ≤ 1 * a⁻¹ := by gcongr
      _ < 1 := by simpa using hinv
  have hxD : x ∈ unitDisc := mem_ball_zero_iff.2 hxlt
  have hden : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hkey : a ^ 2 - 1 ≤ a ^ 2 * (1 - ‖x‖ ^ 2) := by
    rw [hxn]
    have : a ^ 2 * (1 - (s * a⁻¹) ^ 2) = a ^ 2 - s ^ 2 := by field_simp
    rw [this]; nlinarith
  have hfx : ‖AInf.toFun φ x‖ = ‖φ.1 ⟨x, hxD⟩‖ / (1 - ‖x‖ ^ 2) ^ 2 := by
    simp only [AInf.toFun, unweight, dif_pos hxD, norm_div, norm_pow]
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg hden.le]
  have hbd : ‖φ.1 ⟨x, hxD⟩‖ ≤ ‖φ‖ := φ.1.norm_coe_le_norm ⟨x, hxD⟩
  have hn : ‖-(1 / 2 : ℂ) * (((1 - a ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ x / conj ζ ^ 4‖ =
      (1 / 2) * ((a ^ 2 - 1) ^ 2 * (‖φ.1 ⟨x, hxD⟩‖ / (1 - ‖x‖ ^ 2) ^ 2) / a ^ 4) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_conj, hfx, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)]
    have : (1 - a ^ 2) ^ 2 = (a ^ 2 - 1) ^ 2 := by ring
    rw [this]
    simp
    ring
  have hr : (a ^ 2 - 1) ^ 2 / ((1 - ‖x‖ ^ 2) ^ 2 * a ^ 4) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : 0 ≤ a ^ 2 - 1 := by nlinarith
    have : (a ^ 2 - 1) ^ 2 ≤ (a ^ 2 * (1 - ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ h1 hkey 2
    nlinarith
  rw [show (1 - ‖ζ‖ ^ 2) ^ 2 = (1 - a ^ 2) ^ 2 by rw [ha], hn]
  have : (a ^ 2 - 1) ^ 2 * (‖φ.1 ⟨x, hxD⟩‖ / (1 - ‖x‖ ^ 2) ^ 2) / a ^ 4 =
      ‖φ.1 ⟨x, hxD⟩‖ * ((a ^ 2 - 1) ^ 2 / ((1 - ‖x‖ ^ 2) ^ 2 * a ^ 4)) := by
    field_simp
  rw [this]
  calc 1 / 2 * (‖φ.1 ⟨x, hxD⟩‖ * ((a ^ 2 - 1) ^ 2 / ((1 - ‖x‖ ^ 2) ^ 2 * a ^ 4)))
      ≤ 1 / 2 * (‖φ.1 ⟨x, hxD⟩‖ * 1) := by gcongr
    _ ≤ ‖φ‖ / 2 := by nlinarith


theorem qcv_hB_int : Integrable (fun ζ : ℂ => 16 * (1 + ‖ζ‖) ^ (-4 : ℝ)) (volume.restrict unitDiscExterior) := by
  have := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 4) (by simp [Complex.finrank_real_complex]; norm_num)
  exact (this.const_mul 16).integrableOn

set_option maxHeartbeats 1600000 in
theorem qcv_dil_dom (φ : AInf unitDisc) {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {ζ : ℂ} (hζ1 : 1 < ‖ζ‖) :
    ‖(-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((s : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4‖
      ≤ (‖φ‖ / 2) * (((1 - ‖z‖) ^ 4)⁻¹ * (16 * (1 + ‖ζ‖) ^ (-4 : ℝ))) := by
  have hnum := qcv_dil_bound φ hs0 hs1 hζ1
  have hz0 : 0 < 1 - ‖z‖ := by linarith
  have hdz : (1 - ‖z‖) * ‖ζ‖ ≤ ‖ζ - z‖ := by
    have := norm_sub_norm_le ζ z
    nlinarith [norm_nonneg z]
  have hdz0 : 0 < (1 - ‖z‖) * ‖ζ‖ := by
    have : 0 < ‖ζ‖ := by linarith
    positivity
  have h4 : ((1 - ‖z‖) * ‖ζ‖) ^ 4 ≤ ‖ζ - z‖ ^ 4 := pow_le_pow_left₀ hdz0.le hdz 4
  have hφn : 0 ≤ ‖φ‖ / 2 := by positivity
  rw [norm_div, norm_pow]
  calc ‖-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((s : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4‖ /
        ‖ζ - z‖ ^ 4 ≤ (‖φ‖ / 2) / ‖ζ - z‖ ^ 4 := by
        exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (‖φ‖ / 2) / (((1 - ‖z‖) * ‖ζ‖) ^ 4) := by
        exact div_le_div_of_nonneg_left hφn (by positivity) h4
    _ = (‖φ‖ / 2) * (((1 - ‖z‖) ^ 4)⁻¹ * (‖ζ‖ ^ 4)⁻¹) := by
        have h1z : (1 - ‖z‖) ≠ 0 := hz0.ne'
        have hn0 : ‖ζ‖ ≠ 0 := by linarith
        rw [mul_pow]; field_simp
    _ ≤ (‖φ‖ / 2) * (((1 - ‖z‖) ^ 4)⁻¹ * (16 * (1 + ‖ζ‖) ^ (-4 : ℝ))) := by
        have := qcv_inv4 hζ1
        have h0 : 0 ≤ ((1 - ‖z‖) ^ 4)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this h0) hφn

theorem qcv_dil_cont (φ : AInf unitDisc) {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContinuousOn (fun ζ : ℂ => (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((s : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4) unitDiscExterior := by
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDisc := φ.property
  have hext0 : ∀ ζ ∈ unitDiscExterior, ζ ≠ 0 := by
    intro ζ hζ h; rw [h] at hζ; simp [unitDiscExterior] at hζ; norm_num at hζ
  have hr : ContinuousOn (fun ζ : ℂ => (conj ζ)⁻¹) unitDiscExterior :=
    continuous_conj.continuousOn.inv₀ fun ζ hζ => (map_ne_zero (starRingEnd ℂ)).mpr (hext0 ζ hζ)
  have hm : MapsTo (fun ζ : ℂ => (s : ℂ) * (conj ζ)⁻¹) unitDiscExterior unitDisc := by
    intro ζ hζ
    have hζ1 : 1 < ‖ζ‖ := hζ
    refine mem_ball_zero_iff.2 ?_
    show ‖(s : ℂ) * (conj ζ)⁻¹‖ < 1
    rw [norm_mul, norm_inv, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have hb := inv_lt_one_of_one_lt₀ hζ1
    have hb0 : 0 < ‖ζ‖⁻¹ := by positivity
    nlinarith
  have hf : ContinuousOn (fun ζ : ℂ => AInf.toFun φ ((s : ℂ) * (conj ζ)⁻¹)) unitDiscExterior :=
    hφd.continuousOn.comp (continuousOn_const.mul hr) hm
  have hw : Continuous (fun ζ : ℂ => -(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ)) := by fun_prop
  refine ((hw.continuousOn.mul hf).div (continuous_conj.pow 4).continuousOn
    fun ζ hζ => pow_ne_zero 4 ((map_ne_zero (starRingEnd ℂ)).mpr (hext0 ζ hζ))).div
    (by fun_prop) ?_
  intro ζ hζ h
  have hζ1 : 1 < ‖ζ‖ := hζ
  have : ζ = z := by
    have := pow_eq_zero_iff (n := 4) (by norm_num) |>.1 h
    linear_combination this
  rw [this] at hζ1; linarith

theorem qcv_reproduce_AInf (φ : AInf unitDisc) {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4
      = -((π : ℂ) / 6) * AInf.toFun φ z := by
  have hmeas : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hφd : DifferentiableOn ℂ (AInf.toFun φ) unitDisc := φ.property
  let sq : ℕ → ℝ := fun k => 1 - (1 / 2) * (1 / ((k : ℝ) + 1))
  have hs0 : ∀ k, 0 < sq k := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    simp only [sq]; linarith
  have hs1 : ∀ k, sq k < 1 := fun k => by
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [sq]; linarith
  have hslim : Tendsto sq atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub this
    simpa [sq] using this
  have hFint : ∀ k, ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((sq k : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4
        = -((π : ℂ) / 6) * AInf.toFun φ ((sq k : ℂ) * z) := by
    intro k
    have hR : 1 < 1 / sq k := by rw [lt_div_iff₀ (hs0 k)]; linarith [hs1 k]
    have hd : DifferentiableOn ℂ (fun u => AInf.toFun φ ((sq k : ℂ) * u)) (ball 0 (1 / sq k)) := by
      refine hφd.comp (differentiableOn_const _ |>.mul differentiableOn_id) ?_
      intro u hu
      rw [mem_ball_zero_iff] at hu
      refine mem_ball_zero_iff.2 ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs0 k).le]
      calc sq k * ‖u‖ < sq k * (1 / sq k) := mul_lt_mul_of_pos_left hu (hs0 k)
        _ = 1 := mul_one_div_cancel (hs0 k).ne'
    exact qcv_reproduce_ball hR hd hz
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict unitDiscExterior)
    (F := fun k ζ => (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
      AInf.toFun φ ((sq k : ℂ) * (conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4)
    (f := fun ζ => (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4)
    (fun ζ => (‖φ‖ / 2) * (((1 - ‖z‖) ^ 4)⁻¹ * (16 * (1 + ‖ζ‖) ^ (-4 : ℝ))))
    (fun k => (qcv_dil_cont φ hz (hs0 k) (hs1 k)).aestronglyMeasurable hmeas)
    ((qcv_hB_int.const_mul (((1 - ‖z‖) ^ 4)⁻¹)).const_mul (‖φ‖ / 2))
    (fun k => by
      filter_upwards [ae_restrict_mem hmeas] with ζ hζ
      exact qcv_dil_dom φ hz (hs0 k) (hs1 k).le hζ)
    (by
      filter_upwards [ae_restrict_mem hmeas] with ζ hζ
      have hζ1 : 1 < ‖ζ‖ := hζ
      have hw : ‖(conj ζ)⁻¹‖ < 1 := by
        rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hζ1
      have hc : ContinuousAt (AInf.toFun φ) ((conj ζ)⁻¹) :=
        hφd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hw))
      have h1 : Tendsto (fun k => (sq k : ℂ) * (conj ζ)⁻¹) atTop (𝓝 ((conj ζ)⁻¹)) := by
        have := ((Complex.continuous_ofReal.tendsto 1).comp hslim).mul_const ((conj ζ)⁻¹)
        simpa using this
      have hG : ContinuousAt (fun w : ℂ => (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
          AInf.toFun φ w / conj ζ ^ 4) / (ζ - z) ^ 4) ((conj ζ)⁻¹) :=
        ((hc.const_mul _).div_const _).div_const _
      exact hG.tendsto.comp h1)
  simp_rw [hFint] at hlim
  have hc : ContinuousAt (AInf.toFun φ) z :=
    hφd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz))
  have h1 : Tendsto (fun k => (sq k : ℂ) * z) atTop (𝓝 z) := by
    have := ((Complex.continuous_ofReal.tendsto 1).comp hslim).mul_const z
    simpa using this
  have hlim2 : Tendsto (fun k => -((π : ℂ) / 6) * AInf.toFun φ ((sq k : ℂ) * z)) atTop
      (𝓝 (-((π : ℂ) / 6) * AInf.toFun φ z)) := (hc.tendsto.comp h1).const_mul _
  exact tendsto_nhds_unique hlim2 hlim |>.symm

theorem qcv_D0_Lambda (φ : AInf unitDisc) : fderiv ℂ bersPhi 0 (Lambda φ) = φ := by
  apply AInf.ext_toFun_disc
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [qcv_eq_1_4 (Lambda φ) z hz]
  have h := qcv_reproduce_AInf φ hz1
  have hint : ∫ ζ in unitDiscExterior, (Lambda φ) ζ / (ζ - z) ^ 4 =
      ∫ ζ in unitDiscExterior, (-(1 / 2 : ℂ) * (((1 - ‖ζ‖ ^ 2) ^ 2 : ℝ) : ℂ) * AInf.toFun φ ((conj ζ)⁻¹) / conj ζ ^ 4) / (ζ - z) ^ 4 := by
    refine integral_congr_ae ?_
    filter_upwards [Lambda_coe_ae φ] with ζ hζ
    rw [hζ]
    push_cast
    rfl
  rw [hint, h]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

theorem qcv_lambda_inverse_D0bers :
    (∀ φ, Lambda φ ∈ harmonicBeltrami) ∧ (∀ φ, fderiv ℂ bersPhi 0 (Lambda φ) = φ) ∧
      ∀ μ ∈ harmonicBeltrami, Lambda (fderiv ℂ bersPhi 0 μ) = μ := by
  refine ⟨Lambda_mem_harmonic, qcv_D0_Lambda, ?_⟩
  intro μ hμ
  obtain ⟨φ, rfl⟩ := Lambda_surjective_harmonic hμ
  rw [qcv_D0_Lambda]

theorem qcv_D0bers_bijective_on_harmonic :
    Function.Bijective (fun μ : harmonicBeltrami => fderiv ℂ bersPhi 0 (μ : LinfStar)) := by
  obtain ⟨h1, h2, h3⟩ := qcv_lambda_inverse_D0bers
  constructor
  · intro μ ν h
    apply Subtype.ext
    have := congrArg Lambda h
    simp only at this
    rw [h3 _ μ.2, h3 _ ν.2] at this
    exact this
  · intro φ
    exact ⟨⟨Lambda φ, h1 φ⟩, h2 φ⟩

end QCV

/-! ### Originals relocated from `S1_1` (2026-10-25) -/

/-- **(1.4)** (TT:495). The differential of the Bers embedding at the origin:
`D₀β(μ)(z) = -(6/π) ∬_{𝔻*} μ(ζ)/(ζ - z)⁴ d²ζ` for `z ∈ 𝔻`. -/
theorem eq_1_4 (μ : LinfStar) (z : ℂ) (hz : z ∈ unitDisc) :
    AInf.toFun (fderiv ℂ bersPhi 0 μ) z = -(6 / π) * ∫ ζ in unitDiscExterior, μ ζ / (ζ - z) ^ 4 :=
  QCV.qcv_eq_1_4 μ z hz

/-- (TT:498) `D₀β` restricted to `Ω^{-1,1}(𝔻*)` is an isomorphism onto `A∞(𝔻)`. -/
theorem D0bers_bijective_on_harmonic :
    Function.Bijective (fun μ : harmonicBeltrami => fderiv ℂ bersPhi 0 (μ : LinfStar)) :=
  QCV.qcv_D0bers_bijective_on_harmonic

/-- (TT:498) `Λ` takes values in `Ω^{-1,1}(𝔻*)` and is the inverse of `D₀β` there. -/
theorem lambda_inverse_D0bers :
    (∀ φ, Lambda φ ∈ harmonicBeltrami) ∧ (∀ φ, fderiv ℂ bersPhi 0 (Lambda φ) = φ) ∧
      ∀ μ ∈ harmonicBeltrami, Lambda (fderiv ℂ bersPhi 0 μ) = μ :=
  QCV.qcv_lambda_inverse_D0bers

end TakhtajanTeo
