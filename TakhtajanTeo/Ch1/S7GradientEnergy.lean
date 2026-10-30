import TakhtajanTeo.Ch1.S7Caccioppoli
import TakhtajanTeo.Ch1.S7CutoffGradient
import TakhtajanTeo.Ch1.HarmonicKernelIntegrability

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def s7ge_density (h : ℂ → ℂ) : ℂ → ℝ :=
  unitDisc.indicator (fun z => ‖h z‖ ^ 2 * rho z)

theorem s7ge_density_nonneg (h : ℂ → ℂ) (z : ℂ) : 0 ≤ s7ge_density h z := by
  by_cases hz : z ∈ unitDisc
  · simp only [s7ge_density, indicator_of_mem hz]
    exact mul_nonneg (sq_nonneg _) (by unfold rho; positivity)
  · simp [s7ge_density, hz]

theorem s7ge_density_integrable {h : ℂ → ℂ}
    (hm : AEStronglyMeasurable h (volume.restrict unitDisc)) (hL : normL2 unitDisc h < ∞) :
    Integrable (s7ge_density h) := by
  have hr : Measurable rho := by unfold rho; fun_prop
  apply (integrable_indicator_iff measurableSet_ball).2
  refine ⟨(hm.norm.pow 2).mul hr.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun z => mul_nonneg (sq_nonneg _) (show 0 ≤ rho z by unfold rho; positivity)))]
  have hi := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 hL
  change (∫⁻ z in unitDisc, (‖h z‖₊ : ℝ≥0∞)^2 * ENNReal.ofReal (rho z)) < ∞ at hi
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, enorm_eq_nnnorm, unitDisc] using hi

theorem s7ge_cutoff_outside (n : ℕ) {z : ℂ} (hz : z ∉ unitDisc) :
    s7dc_cutoff n z = 0 ∧ dzbar (fun w => (s7dc_cutoff n w : ℂ)) z = 0 := by
  have hs : tsupport (fun w => (s7dc_cutoff n w : ℂ)) ⊆ unitDisc := by
    have he : tsupport (fun w => (s7dc_cutoff n w : ℂ)) = tsupport (s7dc_cutoff n) := by
      unfold tsupport
      congr 1
      ext w
      simp
    rw [he]
    exact (s7dc_compact n).2
  exact ⟨image_eq_zero_of_notMem_tsupport (fun ht => hz ((s7dc_compact n).2 ht)),
    image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (s7ca_dzbar_support _ ht)))⟩

theorem s7ge_forcing_bound (h : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    ‖(s7dc_cutoff n z : ℂ)^2 * h z * conj (laplace0 h z) * (rho z : ℂ)‖ ≤
      s7ge_density h z + s7ge_density (laplace0 h) z := by
  by_cases hz : z ∈ unitDisc
  · have hr : 0 ≤ rho z := by unfold rho; positivity
    have hc : ‖(s7dc_cutoff n z : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (s7dc_bounds n z).1] using (s7dc_bounds n z).2
    simp only [norm_mul, norm_pow, norm_conj, Complex.norm_real,
      Real.norm_eq_abs (rho z), abs_of_nonneg hr, s7ge_density, indicator_of_mem hz]
    calc
      _ ≤ 1 ^ 2 * ‖h z‖ * ‖laplace0 h z‖ * rho z := by
        gcongr
        simpa only [Complex.norm_real] using hc
      _ ≤ (‖h z‖ ^ 2 + ‖laplace0 h z‖ ^ 2) * rho z := by
        gcongr
        nlinarith [sq_nonneg (‖h z‖ - ‖laplace0 h z‖)]
      _ = _ := by ring
  · simp [s7ge_density, hz, (s7ge_cutoff_outside n hz).1]

theorem s7ge_boundary_bound (h : ℂ → ℂ) {C : ℝ} (n : ℕ)
    (hb : ∀ z ∈ unitDisc,
      ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ ^ 2 ≤ C * rho z) (z : ℂ) :
    ‖h z * dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖ ^ 2 ≤ C * s7ge_density h z := by
  by_cases hz : z ∈ unitDisc
  · simp only [norm_mul, mul_pow, s7ge_density, indicator_of_mem hz]
    calc
      _ ≤ ‖h z‖ ^ 2 * (C * rho z) := mul_le_mul_of_nonneg_left (hb z hz) (sq_nonneg _)
      _ = _ := by ring
  · simp [s7ge_density, hz, (s7ge_cutoff_outside n hz).2]

/-- A uniform cutoff energy bound derived from h and Delta h in weighted L2. -/
theorem s7ge_uniform {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    ∃ M : ℝ, ∀ n : ℕ, (∫ z, ‖(s7dc_cutoff n z : ℂ) * dzbar h z‖ ^ 2) ≤ M := by
  have hH := s7ge_density_integrable (hh.continuousOn.aestronglyMeasurable measurableSet_ball) hL
  have hr : Measurable (fun z => (rho z : ℂ)) := by unfold rho; fun_prop
  have hDm : Measurable (laplace0 h) := (hr.inv.mul (measurable_dz (dzbar h))).neg
  have hD := s7ge_density_integrable hDm.aestronglyMeasurable hDL
  obtain ⟨C,hC,hCb⟩ := s7cg_cutoff_gradient_bound
  refine ⟨2 * (∫ z, s7ge_density h z + s7ge_density (laplace0 h) z) +
    4 * (∫ z, C * s7ge_density h z), fun n => ?_⟩
  obtain ⟨hA,hB,hP,he⟩ := s7cc_compact_estimate hh n
  dsimp only at hA hB hP he
  have hPb := (norm_integral_le_integral_norm _).trans
    (integral_mono hP.norm (hH.add hD) (s7ge_forcing_bound h n))
  have hBb := integral_mono hB (hH.const_mul C) (s7ge_boundary_bound h n (hCb n))
  simp only [Pi.add_apply] at hPb
  linarith

/-- True unweighted derivative energy finiteness; no gradient-energy hypothesis is used. -/
theorem s7ge_dzbar_integrable {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    IntegrableOn (fun z => ‖dzbar h z‖ ^ 2) unitDisc := by
  obtain ⟨M,hM⟩ := s7ge_uniform hh hL hDL
  let P : ℕ → ℂ → ℝ := fun n z => ‖(s7dc_cutoff n z : ℂ) * dzbar h z‖ ^ 2
  let F : ℂ → ℝ := unitDisc.indicator (fun z => ‖dzbar h z‖ ^ 2)
  have hi (n : ℕ) : Integrable (P n) := (s7cc_energy_integrable hh n).1
  have hl : ∀ᵐ z ∂volume, Tendsto (fun n => P n z) atTop (𝓝 (F z)) := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ unitDisc
    · have he : (fun n => P n z) =ᶠ[atTop] (fun _ => F z) := by
        filter_upwards [s7dc_eventually_one hz] with n hn
        simp [P, F, hz, hn.self_of_nhds]
      exact (tendsto_congr' he).2 tendsto_const_nhds
    · have he : (fun n => P n z) = (fun _ => F z) := by
        funext n
        simp [P, F, hz, (s7ge_cutoff_outside n hz).1]
      rw [he]
      exact tendsto_const_nhds
  have hb (n : ℕ) : (∫ z, ‖P n z‖) ≤ M := by
    simpa [P, Real.norm_eq_abs] using hM n
  have hF : Integrable F := wp_integrable_of_uniform_integral_bound hi hl hb
  exact (integrable_indicator_iff measurableSet_ball).1 hF

end TakhtajanTeo
