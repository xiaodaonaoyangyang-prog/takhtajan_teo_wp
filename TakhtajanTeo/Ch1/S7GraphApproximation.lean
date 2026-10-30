import TakhtajanTeo.Ch1.S7GraphProduct

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def s7ga_majorant (h : ℂ → ℂ) (L C : ℝ) (z : ℂ) : ℝ :=
  4 * (‖laplace0 h z‖^2*rho z + L^2*‖h z‖^2*rho z + C*(‖dz h z‖^2+‖dzbar h z‖^2))

theorem s7ga_error_bound {h : ℂ → ℂ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    {L C : ℝ} (n : ℕ) {z : ℂ} (hz : z ∈ unitDisc)
    (hL : ‖laplace0 (fun w => (s7dc_cutoff n w : ℂ)) z‖ ≤ L)
    (hC : ‖dzbar (fun w => (s7dc_cutoff n w : ℂ)) z‖^2 ≤ C*rho z) :
    ‖laplace0 (fun w => (s7dc_cutoff n w : ℂ)*h w) z - laplace0 h z‖^2*rho z ≤
      s7ga_majorant h L C z := by
  let c : ℂ → ℂ := fun w => (s7dc_cutoff n w : ℂ)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp (s7dc_smooth n)
  have hr : 0 < rho z := rho_pos_of_norm_ne_one
    (ne_of_lt (by simpa [unitDisc, mem_ball, dist_zero_right] using hz : ‖z‖ < 1))
  have he : laplace0 (fun w => c w*h w) z - laplace0 h z =
      (c z*laplace0 h z-laplace0 h z) + h z*laplace0 c z -
      (rho z : ℂ)⁻¹*dz c z*dzbar h z - (rho z : ℂ)⁻¹*dzbar c z*dz h z := by
    rw [s7ga_laplace_mul hc.contDiffOn hh hz]
    ring
  have ha1 := mul_self_le_mul_self (norm_nonneg _)
    (s7ap_error_bound n (laplace0 h) z)
  have ha := mul_le_mul_of_nonneg_right ha1 hr.le
  have hb1 := mul_self_le_mul_self (norm_nonneg _) hL
  have hb2 := mul_le_mul_of_nonneg_left hb1 (mul_nonneg (sq_nonneg ‖h z‖) hr.le)
  have hb : ‖h z*laplace0 c z‖^2*rho z ≤ L^2*‖h z‖^2*rho z := by
    rw [norm_mul, mul_pow]
    change _ ≤ _ at hb2
    nlinarith
  have hu := s7ga_weighted_cross hr (dz c z) (dzbar h z)
    (by simpa only [c, s7ga_cutoff_dz_norm] using hC)
  have hv := s7ga_weighted_cross hr (dzbar c z) (dz h z) hC
  have h4 := mul_le_mul_of_nonneg_right
    (s7ga_four_sq (c z*laplace0 h z-laplace0 h z) (h z*laplace0 c z)
      ((rho z : ℂ)⁻¹*dz c z*dzbar h z) ((rho z : ℂ)⁻¹*dzbar c z*dz h z)) hr.le
  change ‖laplace0 (fun w => c w*h w) z-laplace0 h z‖^2*rho z ≤ _
  rw [he]
  dsimp only [s7ga_majorant]
  change (‖c z*laplace0 h z-laplace0 h z‖*‖c z*laplace0 h z-laplace0 h z‖)*rho z ≤ _ at ha
  nlinarith

private theorem measurable_laplace (h : ℂ → ℂ) : Measurable (laplace0 h) := by
  have hr : Measurable (fun z => (rho z : ℂ)) := by unfold rho; fun_prop
  exact (hr.inv.mul (measurable_dz (dzbar h))).neg

theorem s7ga_majorant_integrable {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) (L C : ℝ) :
    IntegrableOn (s7ga_majorant h L C) unitDisc := by
  have hH := (integrable_indicator_iff measurableSet_ball).1
    (s7ge_density_integrable (hh.continuousOn.aestronglyMeasurable measurableSet_ball) hL)
  have hD := (integrable_indicator_iff measurableSet_ball).1
    (s7ge_density_integrable (measurable_laplace h).aestronglyMeasurable hDL)
  have hz := s7ge_dz_integrable hh hL hDL
  have hb := s7ge_dzbar_integrable hh hL hDL
  have hsum := ((hD.add (hH.const_mul (L^2))).add ((hz.add hb).const_mul C)).const_mul 4
  change Integrable (fun z => 4 * (‖laplace0 h z‖^2*rho z + L^2*‖h z‖^2*rho z +
    C*(‖dz h z‖^2+‖dzbar h z‖^2))) (volume.restrict unitDisc)
  simpa only [unitDisc, Pi.add_apply, mul_assoc] using hsum

/-- Actual convergence of Laplacians of the compact cutoff products. -/
theorem s7ga_laplace_error_tendsto {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    Tendsto (fun n => normL2 unitDisc (fun z =>
      laplace0 (fun w => (s7dc_cutoff n w : ℂ)*h w) z-laplace0 h z)) atTop (𝓝 0) := by
  obtain ⟨L,hL0,hLb⟩ := s7dc_laplace_bound
  obtain ⟨C,hC0,hCb⟩ := s7cg_cutoff_gradient_bound
  let F : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal
    (‖laplace0 (fun w => (s7dc_cutoff n w : ℂ)*h w) z-laplace0 h z‖^2) * ENNReal.ofReal (rho z)
  let B : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (s7ga_majorant h L C z)
  have hB := s7ga_majorant_integrable hh hL hDL L C
  have hBn : 0 ≤ᵐ[volume.restrict unitDisc] s7ga_majorant h L C := by
    apply Filter.Eventually.of_forall
    intro z
    dsimp [s7ga_majorant]
    have hr : 0 ≤ rho z := by unfold rho; positivity
    positivity
  have hfin : (∫⁻ z in unitDisc, B z) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal hBn).1 hB.2).ne
  have hr : Measurable (fun z => ENNReal.ofReal (rho z)) := by unfold rho; fun_prop
  have hm (n : ℕ) : AEMeasurable (F n) (volume.restrict unitDisc) :=
    (((measurable_laplace (fun w => (s7dc_cutoff n w : ℂ)*h w)).sub
      (measurable_laplace h)).norm.pow_const 2).ennreal_ofReal.aemeasurable.mul hr.aemeasurable
  have hb (n : ℕ) : F n ≤ᵐ[volume.restrict unitDisc] B := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    dsimp [F,B]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (s7ga_error_bound hh n hz (hLb n z hz) (hCb n z hz))
  have ht : ∀ᵐ z ∂(volume.restrict unitDisc), Tendsto (fun n => F n z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have he : (fun n => F n z) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [s7ga_eventually_laplace_eq h hz] with n hn
      simp [F, hn]
    exact (tendsto_congr' he).2 tendsto_const_nhds
  have hi := tendsto_lintegral_of_dominated_convergence' B hm hb hfin ht
  have hi0 : Tendsto (fun n => ∫⁻ z in unitDisc, F n z) atTop (𝓝 0) := by simpa using hi
  have hrp := hi0.ennrpow_const (1/2 : ℝ)
  have hnorm (v : ℂ) : (‖v‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (‖v‖^2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, enorm_eq_nnnorm]
  simpa only [normL2, hnorm, F, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<1/2)] using hrp

/-- Explicit smooth compact approximation in the actual weighted Laplacian graph norm. -/
theorem s7ga_graph_approximation {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc)
    (hL : normL2 unitDisc h < ∞) (hDL : normL2 unitDisc (laplace0 h) < ∞) :
    (∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (fun z => (s7dc_cutoff n z : ℂ)*h z) ∧
      HasCompactSupport (fun z => (s7dc_cutoff n z : ℂ)*h z) ∧
      tsupport (fun z => (s7dc_cutoff n z : ℂ)*h z) ⊆ unitDisc) ∧
    Tendsto (fun n => normL2 unitDisc (fun z => (s7dc_cutoff n z : ℂ)*h z-h z))
      atTop (𝓝 0) ∧
    Tendsto (fun n => normL2 unitDisc (fun z =>
      laplace0 (fun w => (s7dc_cutoff n w : ℂ)*h w) z-laplace0 h z)) atTop (𝓝 0) := by
  exact ⟨s7ap_compact_test hh,
    s7ap_normL2_error_tendsto (hh.continuousOn.aestronglyMeasurable measurableSet_ball) hL,
    s7ga_laplace_error_tendsto hh hL hDL⟩

end TakhtajanTeo
