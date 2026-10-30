import TakhtajanTeo.Ch1.S7DiskCutoffBounds

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual cutoff products are valid global smooth compact test functions. -/
theorem s7ap_compact_test {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitDisc) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (s7dc_cutoff n z : ℂ) * h z) ∧
    HasCompactSupport (fun z => (s7dc_cutoff n z : ℂ) * h z) ∧
    tsupport (fun z => (s7dc_cutoff n z : ℂ) * h z) ⊆ unitDisc := by
  have he : tsupport (fun z => (s7dc_cutoff n z : ℂ)) = tsupport (s7dc_cutoff n) := by
    unfold tsupport
    congr 1
    ext z
    simp
  have hc : HasCompactSupport (fun z => (s7dc_cutoff n z : ℂ)) := by
    change IsCompact _
    rw [he]
    exact (s7dc_compact n).1
  have hs : tsupport (fun z => (s7dc_cutoff n z : ℂ)) ⊆ unitDisc := by
    rw [he]
    exact (s7dc_compact n).2
  exact ⟨sp_contDiff_mul isOpen_ball hh
    (Complex.ofRealCLM.contDiff.comp (s7dc_smooth n)) hs,
    hc.mul_right, tsupport_mul_subset_left.trans hs⟩

theorem s7ap_error_bound (n : ℕ) (h : ℂ → ℂ) (z : ℂ) :
    ‖(s7dc_cutoff n z : ℂ) * h z - h z‖ ≤ ‖h z‖ := by
  have he : (s7dc_cutoff n z : ℂ) * h z - h z =
      ((s7dc_cutoff n z - 1 : ℝ) : ℂ) * h z := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (s7dc_bounds n z).2)]
  nlinarith [(s7dc_bounds n z).1, norm_nonneg (h z)]

/-- Genuine weighted L2 convergence of the compact cutoff products. -/
theorem s7ap_normL2_error_tendsto {h : ℂ → ℂ}
    (hh : AEStronglyMeasurable h (volume.restrict unitDisc))
    (hL : normL2 unitDisc h < ∞) :
    Tendsto (fun n => normL2 unitDisc (fun z => (s7dc_cutoff n z : ℂ) * h z - h z))
      atTop (𝓝 0) := by
  let B : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖h z‖ ^ 2) * ENNReal.ofReal (rho z)
  let F : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (‖(s7dc_cutoff n z : ℂ) * h z - h z‖ ^ 2) * ENNReal.ofReal (rho z)
  have hr : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by unfold rho; fun_prop
  have hnorm (v : ℂ) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, enorm_eq_nnnorm]
  have hfin : ∫⁻ z in unitDisc, B z ≠ ∞ := by
    unfold normL2 at hL
    simp_rw [hnorm] at hL
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 hL).ne
  have hm (n : ℕ) : AEMeasurable (F n) (volume.restrict unitDisc) := by
    have hc : Continuous (fun z => (s7dc_cutoff n z : ℂ)) :=
      Complex.ofRealCLM.continuous.comp (s7dc_smooth n).continuous
    exact (((hc.aestronglyMeasurable.mul hh).sub hh).norm.pow 2).aemeasurable.ennreal_ofReal.mul
      hr.aemeasurable
  have hb (n : ℕ) : F n ≤ᵐ[volume.restrict unitDisc] B := by
    apply Filter.Eventually.of_forall
    intro z
    dsimp [F, B]
    gcongr
    exact s7ap_error_bound n h z
  have ht : ∀ᵐ z ∂(volume.restrict unitDisc), Tendsto (fun n => F n z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have he : (fun n => F n z) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [s7dc_eventually_one hz] with n hn
      simp [F, hn.self_of_nhds]
    exact (tendsto_congr' he).2 tendsto_const_nhds
  have htI := tendsto_lintegral_of_dominated_convergence' B hm hb hfin ht
  have ht0 : Tendsto (fun n => ∫⁻ z in unitDisc, F n z) atTop (𝓝 0) := by simpa using htI
  have htR := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp ht0
  simpa only [Function.comp_def, normL2, hnorm, F,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using htR

end TakhtajanTeo
