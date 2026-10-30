import TakhtajanTeo.Ch1.WeightedPowerSeries
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Density route (4a): polynomials are dense in `A₂(𝔻)` (下属6, work file)

Weighted analogue of `Ch2/BergmanSeries`: the partial coefficient masses are bounded by the weighted area
(inward dilation, `wp_scalarSeries_weighted_area`, `A2fun.inward_dilate_mass_le`), so the Taylor coefficients have
summable weighted mass; Fatou bounds the weighted area of the Taylor remainder by the coefficient tail.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

theorem s3d_rhoInv_continuous : Continuous (fun z : ℂ => (rho z)⁻¹) := by
  simp only [rho, inv_div]
  fun_prop

theorem s3d_poly_integrable (p : Polynomial ℂ) :
    IntegrableOn (fun z => ‖p.eval z‖ ^ 2 * (rho z)⁻¹) unitDisc := by
  have hc : Continuous (fun z => ‖p.eval z‖ ^ 2 * (rho z)⁻¹) :=
    (p.continuous.norm.pow 2).mul s3d_rhoInv_continuous
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall

/-- Weighted Parseval for an inward dilation. -/
theorem s3d_dilate_area {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ z in unitDisc, ‖f ((r : ℂ) * z)‖ ^ 2 * (rho z)⁻¹) =
      (π / 2) * ∑' n, ‖c n * (r : ℂ) ^ n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hrD : (r : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hr0] using hr1
  have ha : Summable (fun n => ‖c n * (r : ℂ) ^ n‖) := (hs (r : ℂ) hrD).summable.norm
  rw [← wp_scalarSeries_weighted_area ha]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hzD : (r : ℂ) * z ∈ unitDisc := by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz1.le hr0.le
      _ < 1 := by linarith
  have he : (∑' n, c n * (r : ℂ) ^ n * z ^ n) = f ((r : ℂ) * z) := by
    simpa [mul_pow, mul_assoc] using (hs _ hzD).tsum_eq
  rw [he]

/-- Every finite weighted coefficient mass is bounded by the weighted area. -/
theorem s3d_coeff_partial_bound {f : ℂ → ℂ} {c : ℕ → ℂ} (hf : f ∈ A2fun unitDisc)
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z)) (N : ℕ) :
    (π / 2) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) ≤
      ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ := by
  set W := ∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹ with hW
  have hL : Tendsto (fun r : ℝ => (π / 2) * ∑ n ∈ Finset.range N,
      ‖c n * (r : ℂ) ^ n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) (𝓝[<] 1)
      (𝓝 ((π / 2) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))) := by
    have hc : Continuous (fun r : ℝ => (π / 2) * ∑ n ∈ Finset.range N,
        ‖c n * (r : ℂ) ^ n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by fun_prop
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * W) (𝓝[<] 1) (𝓝 W) := by
    have hc : ContinuousAt (fun r : ℝ => (r ^ 2)⁻¹ * W) 1 :=
      ((continuousAt_id.pow 2).inv₀ (by norm_num)).mul continuousAt_const
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hrD : (r : ℂ) ∈ unitDisc := by simpa [unitDisc, abs_of_pos hr.1] using hr.2
  have ha : Summable (fun n => ‖c n * (r : ℂ) ^ n‖) := (hs (r : ℂ) hrD).summable.norm
  have hb := (wp_scalarSeries_energy_summable ha).sum_le_tsum (Finset.range N) (fun n _ => by positivity)
  calc _ ≤ (π / 2) * ∑' n, ‖c n * (r : ℂ) ^ n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := (s3d_dilate_area hs hr.1 hr.2).symm
    _ ≤ _ := A2fun.inward_dilate_mass_le hf hr.1 hr.2

/-- Fatou: the weighted area of a disk power series is bounded by its weighted coefficient mass. -/
theorem s3d_series_area_le {g : ℂ → ℂ} {d : ℕ → ℂ}
    (hs : ∀ z ∈ unitDisc, HasSum (fun n => d n * z ^ n) (g z))
    (hd : Summable (fun n => ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))))
    (hi : IntegrableOn (fun z => ‖g z‖ ^ 2 * (rho z)⁻¹) unitDisc) :
    (∫ z in unitDisc, ‖g z‖ ^ 2 * (rho z)⁻¹) ≤
      (π / 2) * ∑' n, ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  let P := wp_scalarSeriesPolynomial d
  let F : ℕ → ℂ → ℝ≥0∞ := fun N z => ENNReal.ofReal (‖(P N).eval z‖ ^ 2 * (rho z)⁻¹)
  have hm (N : ℕ) : Measurable (F N) := by
    have hcN : Continuous (fun z => ‖(P N).eval z‖ ^ 2 * (rho z)⁻¹) :=
      ((P N).continuous.norm.pow 2).mul s3d_rhoInv_continuous
    exact ENNReal.measurable_ofReal.comp hcN.measurable
  have ht (z : ℂ) (hz : z ∈ unitDisc) : Tendsto (fun N => F N z) atTop
      (𝓝 (ENNReal.ofReal (‖g z‖ ^ 2 * (rho z)⁻¹))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    have hp : Tendsto (fun N => (P N).eval z) atTop (𝓝 (g z)) := by
      simpa only [P, wp_scalarSeriesPolynomial_eval] using (hs z hz).tendsto_sum_nat
    exact (hp.norm.pow 2).mul_const _
  have hI (N : ℕ) : (∫⁻ z in unitDisc, F N z) = ENNReal.ofReal ((π / 2) * ∑ n ∈ Finset.range N,
      ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
    dsimp only [F]
    rw [← ofReal_integral_eq_lintegral_ofReal (s3d_poly_integrable (P N))
      (Eventually.of_forall fun z => by unfold rho; positivity)]
    rw [wp_scalarSeriesPolynomial_area]
  have hlim : Tendsto (fun N => ∫⁻ z in unitDisc, F N z) atTop
      (𝓝 (ENNReal.ofReal ((π / 2) * ∑' n, ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))))) := by
    simp only [hI]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.hasSum.tendsto_sum_nat.const_mul _)
  have hle : (∫⁻ z in unitDisc, ENNReal.ofReal (‖g z‖ ^ 2 * (rho z)⁻¹)) ≤
      ENNReal.ofReal ((π / 2) * ∑' n, ‖d n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
    calc
      _ = ∫⁻ z in unitDisc, liminf (fun N => F N z) atTop := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
        exact (ht z hz).liminf_eq.symm
      _ ≤ liminf (fun N => ∫⁻ z in unitDisc, F N z) atTop := lintegral_liminf_le hm
      _ = _ := hlim.liminf_eq
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z => by unfold rho; positivity)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
    (tsum_nonneg fun n => by positivity))).1 hle

/-- **(4a) Polynomial density in `A₂(𝔻)`.** -/
theorem s3d_poly_dense (ψ : A2 unitDisc) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ' z = q.eval z) ∧ ‖ψ - ψ'‖ < η := by
  have hcirc : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.1 hz).ne
  set f := A2.toFun ψ with hfdef
  have hfd : DifferentiableOn ℂ f unitDisc := (A2.toFun_spec ψ).1
  have hfA : f ∈ A2fun unitDisc := ⟨hfd, by rw [hfdef, A2.norm_toFun]; exact ENNReal.coe_lt_top⟩
  set c : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 with hcdef
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (f z) := by
    intro z hz
    simpa only [hcdef, smul_eq_mul, sub_zero, mul_assoc, mul_comm, mul_left_comm] using
      Complex.hasSum_taylorSeries_on_ball hfd hz
  set ω : ℕ → ℝ := fun n => ‖c n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) with hω
  have hω0 : ∀ n, 0 ≤ ω n := fun n => div_nonneg (sq_nonneg _) (by positivity)
  have hωs : Summable ω := by
    refine summable_of_sum_range_le (c := (∫ z in unitDisc, ‖f z‖ ^ 2 * (rho z)⁻¹) / (π / 2)) hω0
      fun N => ?_
    exact (le_div_iff₀' (by positivity)).2 (s3d_coeff_partial_bound hfA hs N)
  have hite : ∀ N, HasSum (fun n => if n < N then ω n else 0) (∑ n ∈ Finset.range N, ω n) := by
    intro N
    have h : HasSum (fun n => if n < N then ω n else 0)
        (∑ n ∈ Finset.range N, (if n < N then ω n else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => if_neg (by simpa using hn))
    convert h using 1
    exact Finset.sum_congr rfl fun n hn => (if_pos (Finset.mem_range.1 hn)).symm
  have htailHas : ∀ N, HasSum (fun n => if n < N then 0 else ω n)
      (∑' n, ω n - ∑ n ∈ Finset.range N, ω n) := by
    intro N
    convert hωs.hasSum.sub (hite N) using 1
    funext n
    split_ifs <;> simp
  have htail : Tendsto (fun N => (π / 2) * ∑' n, (if n < N then 0 else ω n)) atTop (𝓝 0) := by
    simp only [fun N => (htailHas N).tsum_eq]
    have h := ((hωs.hasSum.tendsto_sum_nat).const_sub (∑' n, ω n)).const_mul (π / 2)
    simpa using h
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds (pow_pos hη 2))).exists
  set S : Polynomial ℂ := wp_scalarSeriesPolynomial c N with hS
  have hSA : (fun z => S.eval z) ∈ A2fun unitDisc :=
    ⟨S.differentiable.differentiableOn, normA2_lt_top_of_integrable_weighted_sq (s3d_poly_integrable S)⟩
  set ψ' : A2 unitDisc := toA2 unitDisc (fun z => S.eval z) with hψ'def
  have hψ' : EqOn (A2.toFun ψ') (fun z => S.eval z) unitDisc := toA2_spec (D := unitDisc) isOpen_ball hcirc hSA
  have hsub := A2.toFun_sub (D := unitDisc) isOpen_ball hcirc ψ ψ'
  have heqg : EqOn (A2.toFun (ψ - ψ')) (fun z => f z - S.eval z) unitDisc := fun z hz => by
    rw [hsub hz, Pi.sub_apply, hψ' hz]
  have hgA : A2.toFun (ψ - ψ') ∈ A2fun unitDisc :=
    ⟨(A2.toFun_spec _).1, by rw [A2.norm_toFun]; exact ENNReal.coe_lt_top⟩
  have hint : IntegrableOn (fun z => ‖f z - S.eval z‖ ^ 2 * (rho z)⁻¹) unitDisc :=
    (A2fun.integrable_weighted_sq (D := unitDisc) isOpen_ball hgA).congr_fun
      (fun z hz => by simp only [heqg hz]) measurableSet_ball
  have hsg : ∀ z ∈ unitDisc, HasSum (fun n => (if n < N then 0 else c n) * z ^ n) (f z - S.eval z) := by
    intro z hz
    have hfin : HasSum (fun n => if n < N then c n * z ^ n else 0) (S.eval z) := by
      rw [hS, wp_scalarSeriesPolynomial_eval]
      have h : HasSum (fun n => if n < N then c n * z ^ n else 0)
          (∑ n ∈ Finset.range N, (if n < N then c n * z ^ n else 0)) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => if_neg (by simpa using hn))
      convert h using 1
      exact Finset.sum_congr rfl fun n hn => (if_pos (Finset.mem_range.1 hn)).symm
    convert (hs z hz).sub hfin using 1
    funext n
    split_ifs <;> simp
  have heqd : (fun n => ‖(if n < N then 0 else c n)‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) =
      fun n => if n < N then 0 else ω n := by
    funext n
    split_ifs <;> simp [hω]
  have hW := s3d_series_area_le hsg (heqd ▸ (htailHas N).summable) hint
  rw [heqd] at hW
  have hsq : ‖ψ - ψ'‖ ^ 2 = ∫ z in unitDisc, ‖A2.toFun (ψ - ψ') z‖ ^ 2 * (rho z)⁻¹ := by
    have h1 := A2fun.normA2_sq (D := unitDisc) isOpen_ball hgA
    rw [A2.norm_toFun] at h1
    have h2 := congrArg ENNReal.toReal h1
    have hnn : 0 ≤ ∫ z in unitDisc, ‖A2.toFun (ψ - ψ') z‖ ^ 2 * (rho z)⁻¹ :=
      setIntegral_nonneg measurableSet_ball fun z _ => by unfold rho; positivity
    rwa [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_ofReal hnn] at h2
  have hcg : (∫ z in unitDisc, ‖A2.toFun (ψ - ψ') z‖ ^ 2 * (rho z)⁻¹) =
      ∫ z in unitDisc, ‖f z - S.eval z‖ ^ 2 * (rho z)⁻¹ :=
    setIntegral_congr_fun measurableSet_ball fun z hz => by simp only [heqg hz]
  refine ⟨ψ', ⟨S, fun z hz => hψ' hz⟩, ?_⟩
  have hlt : ‖ψ - ψ'‖ ^ 2 < η ^ 2 := by
    rw [hsq, hcg]
    exact lt_of_le_of_lt hW hN
  exact lt_of_pow_lt_pow_left₀ 2 hη.le hlt

end TakhtajanTeo.Ch2
