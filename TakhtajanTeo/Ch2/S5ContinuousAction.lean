import TakhtajanTeo.Ch2.S5CompletedAction
import TakhtajanTeo.Ch1.HarmonicResolventSeries
import LiZhongQC.Lemmas.PoissonExtension
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Normed.Group.Tannery

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

theorem s5ct_poisson_decomposition {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle) :
    ∃ U P Q : ℂ → ℂ, ContinuousOn U (closedBall 0 1) ∧ EqOn U F unitCircle ∧
      DifferentiableOn ℂ P unitDisc ∧ DifferentiableOn ℂ Q unitDisc ∧
      EqOn U (fun z => P z + conj (Q z)) unitDisc := by
  have hS : unitCircle = sphere (0 : ℂ) 1 := by ext z; simp [unitCircle]
  have hRe : ContinuousOn (fun z => (F z).re) (sphere (0 : ℂ) 1) := by
    rw [← hS]; exact Complex.continuous_re.comp_continuousOn hF
  have hIm : ContinuousOn (fun z => (F z).im) (sphere (0 : ℂ) 1) := by
    rw [← hS]; exact Complex.continuous_im.comp_continuousOn hF
  obtain ⟨u, hu, huc, hue⟩ := exists_harmonicOnNhd_continuousOn_closedBall_eqOn_sphere zero_lt_one hRe
  obtain ⟨v, hv, hvc, hve⟩ := exists_harmonicOnNhd_continuousOn_closedBall_eqOn_sphere zero_lt_one hIm
  obtain ⟨A, hA, hAu⟩ := hu.exists_analyticOnNhd_ball_re_eq
  obtain ⟨B, hB, hBv⟩ := hv.exists_analyticOnNhd_ball_re_eq
  let U : ℂ → ℂ := fun z => (u z : ℂ) + I * (v z : ℂ)
  let P : ℂ → ℂ := fun z => (A z + I * B z) / 2
  let Q : ℂ → ℂ := fun z => (A z - I * B z) / 2
  refine ⟨U, P, Q, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp_continuousOn huc).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hvc))
  · intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := hS ▸ hz
    dsimp [U]
    rw [hue hz', hve hz']
    apply Complex.ext <;> simp
  · exact (hA.differentiableOn.add (hB.differentiableOn.const_mul I)).div_const 2
  · exact (hA.differentiableOn.sub (hB.differentiableOn.const_mul I)).div_const 2
  · intro z hz
    have ha := hAu hz
    have hb := hBv hz
    dsimp only at ha hb
    have halg (a b : ℂ) : (a + I * b) / 2 + conj ((a - I * b) / 2) =
        (a.re : ℂ) + I * (b.re : ℂ) := by
      apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring
    change (u z : ℂ) + I * (v z : ℂ) = (A z + I * B z) / 2 + conj ((A z - I * B z) / 2)
    rw [halg, ha, hb]

theorem s5ct_holo_series {P : ℂ → ℂ} (hP : DifferentiableOn ℂ P unitDisc) :
    ∃ a : ℕ → ℂ, ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (P z) := by
  refine ⟨fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n P 0, ?_⟩
  intro z hz
  simpa only [smul_eq_mul, sub_zero, mul_assoc, mul_comm, mul_left_comm] using
    Complex.hasSum_taylorSeries_on_ball hP hz

theorem s5ct_radial_uniform {U F : ℂ → ℂ} {r : ℕ → ℝ}
    (hU : ContinuousOn U (closedBall 0 1)) (hUF : EqOn U F unitCircle)
    (hr : ∀ j, 0 ≤ r j ∧ r j ≤ 1) (ht : Tendsto r atTop (𝓝 1)) :
    TendstoUniformlyOn (fun j z => U ((r j : ℂ) * z)) F atTop unitCircle := by
  have hUC := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  have ht' := (Metric.tendsto_nhds.mp ht) δ hδ
  filter_upwards [ht'] with j hj z hz
  have hz1 : ‖z‖ = 1 := hz
  have hzK : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz1.le
  have hrz : (r j : ℂ) * z ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_mul, hz1, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hr j).1]
    exact (hr j).2
  have hd : dist z ((r j : ℂ) * z) < δ := by
    rw [dist_eq_norm, show z - (r j : ℂ) * z = ((1 - r j : ℝ) : ℂ) * z by push_cast; ring,
      norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Real.dist_eq, abs_sub_comm] using hj
  rw [← hUF hz]
  exact hδU z hzK _ hrz hd

theorem s5ct_coeff_uniform {F : ℂ → ℂ} {Fj : ℕ → ℂ → ℂ}
    (hc : ∀ j, ContinuousOn (Fj j) unitCircle)
    (hu : TendstoUniformlyOn Fj F atTop unitCircle) (k : ℤ) :
    Tendsto (fun j => circleCoeff (Fj j) k) atTop (𝓝 (circleCoeff F k)) := by
  have hmem (θ : ℝ) : exp (θ * I) ∈ unitCircle := by
    change ‖exp ((θ : ℂ) * I)‖ = 1; simp [norm_exp]
  have hjc (j : ℕ) : Continuous (fun θ : ℝ => Fj j (exp (θ * I)) * exp (-(k * θ * I))) :=
    ((hc j).comp_continuous (by fun_prop) hmem).mul (by fun_prop)
  have huw : TendstoUniformlyOn
      (fun (j : ℕ) (θ : ℝ) => Fj j (exp (θ * I)) * exp (-(k * θ * I)))
      (fun θ : ℝ => F (exp (θ * I)) * exp (-(k * θ * I))) atTop (uIcc 0 (2 * π)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with j hj θ hθ
    rw [dist_eq_norm, ← sub_mul, norm_mul]
    have he : ‖exp (-(k * θ * I))‖ = 1 := by simp [norm_exp]
    rw [he, mul_one]
    simpa only [dist_eq_norm] using hj _ (hmem θ)
  have h := huw.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall fun j => (hjc j).continuousOn)
  exact h.const_mul (1 / (2 * π : ℂ))

def s5ct_radius (j : ℕ) : ℝ := 1 - 1 / ((j : ℝ) + 1)

theorem s5ct_radius_spec :
    (∀ j, 0 ≤ s5ct_radius j ∧ s5ct_radius j < 1) ∧ Tendsto s5ct_radius atTop (𝓝 1) := by
  constructor
  · intro j
    have hpos : 0 < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simp only [le_add_iff_nonneg_left]
      positivity
    dsimp [s5ct_radius]
    constructor <;> linarith
  · have h : Tendsto (fun j : ℕ => (1 : ℝ) - 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    change Tendsto (fun j : ℕ => (1 : ℝ) - 1 / ((j : ℝ) + 1)) atTop (𝓝 1)
    simpa only [sub_zero] using h

theorem s5ct_disk_coeff {P : ℂ → ℂ} {a : ℕ → ℂ}
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (P z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℤ) :
    fourierCoeff (fun θ : ℝ => P ((r : ℂ) * exp (θ * I))) k =
      if 0 ≤ k then a k.toNat * (r : ℂ) ^ k.toNat else 0 := by
  by_cases hk : 0 ≤ k
  · have h := disk_series_fourierCoeff ha hr0 hr1 k.toNat
    rw [Int.toNat_of_nonneg hk] at h
    simpa only [ite_eq_left hk] using h
  · simpa only [ite_eq_right hk] using
      wp_disk_series_fourierCoeff_negative ha hr0 hr1 (lt_of_not_ge hk)

theorem s5ct_dilate_continuous {U : ℂ → ℂ} (hU : ContinuousOn U (closedBall 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ContinuousOn (fun z => U ((r : ℂ) * z)) unitCircle := by
  apply hU.comp (continuous_const.mul continuous_id).continuousOn
  intro z hz
  apply mem_closedBall_zero_iff.mpr
  dsimp only [Pi.mul_apply, id_eq]
  rw [norm_mul, show ‖z‖ = 1 from hz, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr0]
  exact hr1

theorem s5ct_radial_coeff {U P Q : ℂ → ℂ} {a b : ℕ → ℂ}
    (hP : ContinuousOn P unitDisc) (hQ : ContinuousOn Q unitDisc)
    (hU : EqOn U (fun z => P z + conj (Q z)) unitDisc)
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (P z))
    (hb : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ n) (Q z))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℤ) :
    circleCoeff (fun z => U ((r : ℂ) * z)) k =
      (if 0 ≤ k then a k.toNat * (r : ℂ) ^ k.toNat else 0) +
      conj (if 0 ≤ -k then b (-k).toNat * (r : ℂ) ^ (-k).toNat else 0) := by
  have hz (θ : ℝ) : (r : ℂ) * exp (θ * I) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hr0]
    exact hr1
  have hcP : Continuous (fun θ : ℝ => P ((r : ℂ) * exp (θ * I))) :=
    hP.comp_continuous (by fun_prop) hz
  have hcQ : Continuous (fun θ : ℝ => Q ((r : ℂ) * exp (θ * I))) :=
    hQ.comp_continuous (by fun_prop) hz
  have hcQc : Continuous (fun θ : ℝ => conj (Q ((r : ℂ) * exp (θ * I)))) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp hcQ
  have he : (fun θ : ℝ => U ((r : ℂ) * exp (θ * I))) =
      fun θ : ℝ => P ((r : ℂ) * exp (θ * I)) + conj (Q ((r : ℂ) * exp (θ * I))) :=
    funext fun θ => hU (hz θ)
  change fourierCoeff (fun θ : ℝ => U ((r : ℂ) * exp (θ * I))) k = _
  rw [he, fourierCoeff_add_continuous hcP hcQc, ts2_fc_conj,
    s5ct_disk_coeff ha hr0 hr1, s5ct_disk_coeff hb hr0 hr1]

theorem s5ct_boundary_coefficients {F U P Q : ℂ → ℂ} {a b : ℕ → ℂ}
    (hUc : ContinuousOn U (closedBall 0 1)) (hUF : EqOn U F unitCircle)
    (hP : ContinuousOn P unitDisc) (hQ : ContinuousOn Q unitDisc)
    (hU : EqOn U (fun z => P z + conj (Q z)) unitDisc)
    (ha : ∀ z ∈ unitDisc, HasSum (fun n => a n * z ^ n) (P z))
    (hb : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ n) (Q z)) :
    (∀ n : ℕ, circleCoeff F (n + 1 : ℤ) = a (n + 1)) ∧
    (∀ n : ℕ, circleCoeff F (-(n + 1 : ℤ)) = conj (b (n + 1))) ∧
      circleCoeff F 0 = a 0 + conj (b 0) := by
  have hr0 (j : ℕ) := (s5ct_radius_spec.1 j).1
  have hr1 (j : ℕ) := (s5ct_radius_spec.1 j).2
  have hu := s5ct_radial_uniform hUc hUF (fun j => ⟨hr0 j, (hr1 j).le⟩) s5ct_radius_spec.2
  have hcoeff (k : ℤ) := s5ct_coeff_uniform
    (fun j => s5ct_dilate_continuous hUc (hr0 j) (hr1 j).le) hu k
  have ht : Tendsto (fun j => (s5ct_radius j : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 1).comp s5ct_radius_spec.2
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have he (j : ℕ) : circleCoeff (fun z => U ((s5ct_radius j : ℂ) * z)) (n + 1 : ℤ) =
        a (n + 1) * (s5ct_radius j : ℂ) ^ (n + 1) := by
      have hpos : (0 : ℤ) ≤ n + 1 := by omega
      have hneg : ¬ (0 : ℤ) ≤ -(n + 1 : ℤ) := by omega
      have h := s5ct_radial_coeff hP hQ hU ha hb (hr0 j) (hr1 j) (n + 1 : ℤ)
      rw [ite_eq_left hpos, ite_eq_right hneg] at h
      simpa using h
    have hlim : Tendsto (fun j => a (n + 1) * (s5ct_radius j : ℂ) ^ (n + 1)) atTop (𝓝 (a (n + 1))) := by
      simpa using (ht.pow (n + 1)).const_mul (a (n + 1))
    exact tendsto_nhds_unique ((hcoeff (n + 1 : ℤ)).congr he) hlim
  · intro n
    have he (j : ℕ) : circleCoeff (fun z => U ((s5ct_radius j : ℂ) * z)) (-(n + 1 : ℤ)) =
        conj (b (n + 1)) * (s5ct_radius j : ℂ) ^ (n + 1) := by
      have hpos : (0 : ℤ) ≤ n + 1 := by omega
      have hneg : ¬ (0 : ℤ) ≤ -(n + 1 : ℤ) := by omega
      have h := s5ct_radial_coeff hP hQ hU ha hb (hr0 j) (hr1 j) (-(n + 1 : ℤ))
      rw [neg_neg, ite_eq_right hneg, ite_eq_left hpos] at h
      simpa [map_mul, map_pow] using h
    have hlim : Tendsto (fun j => conj (b (n + 1)) * (s5ct_radius j : ℂ) ^ (n + 1)) atTop
        (𝓝 (conj (b (n + 1)))) := by
      simpa using (ht.pow (n + 1)).const_mul (conj (b (n + 1)))
    exact tendsto_nhds_unique ((hcoeff (-(n + 1 : ℤ))).congr he) hlim
  · have he (j : ℕ) : circleCoeff (fun z => U ((s5ct_radius j : ℂ) * z)) 0 = a 0 + conj (b 0) := by
      simpa using s5ct_radial_coeff hP hQ hU ha hb (hr0 j) (hr1 j) 0
    exact tendsto_nhds_unique ((hcoeff 0).congr he) tendsto_const_nhds

def s5ct_term (F : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  circleCoeff F (n + 1 : ℤ) * z ^ (n + 1) + circleCoeff F (-(n + 1 : ℤ)) * conj z ^ (n + 1)

def s5ct_poly (F : ℂ → ℂ) (r : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  circleCoeff F 0 + ∑ n ∈ Finset.range N, s5ct_term F n ((r : ℂ) * z)

theorem s5ct_poisson_series {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle) :
    ∃ U : ℂ → ℂ, ContinuousOn U (closedBall 0 1) ∧ EqOn U F unitCircle ∧
      ∀ z ∈ unitDisc, HasSum (fun n => s5ct_term F n z) (U z - circleCoeff F 0) := by
  obtain ⟨U, P, Q, hUc, hUF, hP, hQ, hU⟩ := s5ct_poisson_decomposition hF
  obtain ⟨a, ha⟩ := s5ct_holo_series hP
  obtain ⟨b, hb⟩ := s5ct_holo_series hQ
  obtain ⟨hpa, hqb, hzero⟩ := s5ct_boundary_coefficients hUc hUF hP.continuousOn hQ.continuousOn hU ha hb
  refine ⟨U, hUc, hUF, ?_⟩
  intro z hz
  have hp : HasSum (fun n => a (n + 1) * z ^ (n + 1)) (P z - a 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (ha z hz)
  have hq : HasSum (fun n => b (n + 1) * z ^ (n + 1)) (Q z - b 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (hb z hz)
  have hqc : HasSum (fun n => conj (b (n + 1)) * conj z ^ (n + 1)) (conj (Q z) - conj (b 0)) := by
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasSum hq
    change HasSum (fun n => conj (b (n + 1) * z ^ (n + 1))) (conj (Q z - b 0)) at h
    simpa only [map_mul, map_pow, map_sub] using h
  have hf : (fun n => s5ct_term F n z) =
      fun n => a (n + 1) * z ^ (n + 1) + conj (b (n + 1)) * conj z ^ (n + 1) := by
    funext n
    simp only [s5ct_term, hpa, hqb]
  have he : U z - circleCoeff F 0 = (P z - a 0) + (conj (Q z) - conj (b 0)) := by
    rw [hU hz, hzero]
    dsimp only
    ring
  rw [hf, he]
  exact hp.add hqc

theorem s5ct_coeff_bound {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℤ, ‖circleCoeff F k‖ ≤ M := by
  have hc : Continuous (fun θ : ℝ => F (exp (θ * I))) := hF.comp_continuous (by fun_prop)
    (fun θ => by change ‖exp ((θ : ℂ) * I)‖ = 1; simp [norm_exp])
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro k
  have h := fourierCoeff_sum_sq_le hc (le_max_right M 0)
    (fun θ hθ => (hM θ hθ).trans (le_max_left M 0)) {k}
  simp only [Finset.sum_singleton] at h
  change ‖fourierCoeff (fun θ : ℝ => F (exp (θ * I))) k‖ ≤ max M 0
  nlinarith [norm_nonneg (fourierCoeff (fun θ : ℝ => F (exp (θ * I))) k), le_max_right M 0]

theorem s5ct_poly_uniform {F U : ℂ → ℂ}
    (hF : ContinuousOn F unitCircle)
    (hS : ∀ z ∈ unitDisc, HasSum (fun n => s5ct_term F n z) (U z - circleCoeff F 0))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N => s5ct_poly F r N) (fun z => U ((r : ℂ) * z)) atTop unitCircle := by
  obtain ⟨M, hM0, hM⟩ := s5ct_coeff_bound hF
  have hzN (z : ℂ) (hz : z ∈ unitCircle) : ‖(r : ℂ) * z‖ = r := by
    rw [norm_mul, show ‖z‖ = 1 from hz, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]
  have hg : Summable (fun n : ℕ => (2 * M) * r ^ (n + 1)) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)).mul_left _
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ unitCircle) :
      ‖s5ct_term F n ((r : ℂ) * z)‖ ≤ (2 * M) * r ^ (n + 1) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_pow, norm_conj, hzN z hz]
    have h1 := mul_le_mul_of_nonneg_right (hM (n + 1 : ℤ)) (pow_nonneg hr0 (n + 1))
    have h2 := mul_le_mul_of_nonneg_right (hM (-(n + 1 : ℤ))) (pow_nonneg hr0 (n + 1))
    linarith
  have hc := tendstoUniformlyOn_tsum_nat hg hb
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hc) ε hε] with N hN z hz
  have hzD : (r : ℂ) * z ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, hzN z hz]
    exact hr1
  have he := (hS _ hzD).tsum_eq
  have h := hN z hz
  rw [he] at h
  simpa only [s5ct_poly, dist_eq_norm, sub_add_eq_sub_sub] using h

theorem s5ct_poly_contDiff (F : ℂ → ℂ) (r : ℝ) (N : ℕ) : ContDiff ℝ 1 (s5ct_poly F r N) := by
  have hc : ContDiff ℝ 1 (fun z : ℂ => conj ((r : ℂ) * z)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_const.mul contDiff_id)
  have ht (n : ℕ) : ContDiff ℝ 1 (fun z => s5ct_term F n ((r : ℂ) * z)) :=
    (contDiff_const.mul ((contDiff_const.mul contDiff_id).pow (n + 1))).add
      (contDiff_const.mul (hc.pow (n + 1)))
  exact contDiff_const.add (ContDiff.sum (fun n _ => ht n))

theorem s5ct_uniform_approximation {F : ℂ → ℂ} (hF : ContinuousOn F unitCircle) :
    ∃ N : ℕ → ℕ, (∀ j, j ≤ N j) ∧
      TendstoUniformlyOn (fun j => s5ct_poly F (s5ct_radius j) (N j)) F atTop unitCircle := by
  obtain ⟨U, hUc, hUF, hS⟩ := s5ct_poisson_series hF
  have hN (j : ℕ) : ∃ N : ℕ, j ≤ N ∧ ∀ z ∈ unitCircle,
      dist (U ((s5ct_radius j : ℂ) * z)) (s5ct_poly F (s5ct_radius j) N z) < 1 / ((j : ℝ) + 1) := by
    have h := (Metric.tendstoUniformlyOn_iff.mp
      (s5ct_poly_uniform hF hS (s5ct_radius_spec.1 j).1 (s5ct_radius_spec.1 j).2))
      (1 / ((j : ℝ) + 1)) (by positivity)
    exact ((eventually_ge_atTop j).and h).exists
  choose N hNj hN using hN
  refine ⟨N, hNj, ?_⟩
  have hu := s5ct_radial_uniform hUc hUF
    (fun j => ⟨(s5ct_radius_spec.1 j).1, (s5ct_radius_spec.1 j).2.le⟩) s5ct_radius_spec.2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hs := tendsto_one_div_add_atTop_nhds_zero_nat.eventually
    (eventually_lt_nhds (half_pos hε))
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) (ε / 2) (half_pos hε), hs]
    with j hj hjε z hz
  apply (dist_triangle _ (U ((s5ct_radius j : ℂ) * z)) _).trans_lt
  have h1 := hj z hz
  have h2 := hN j z hz
  linarith

end TakhtajanTeo.Ch2
