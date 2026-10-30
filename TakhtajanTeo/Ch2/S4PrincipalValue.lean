import TakhtajanTeo.Ch2.S4HolomorphicVariation
import TakhtajanTeo.Ch1.S7First

/-! # Genuine Euclidean-cutoff principal values for the S4 kernel (`s4hv_`) -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

-- H7
theorem s4hv_pv_quadratic {U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {r L : ℝ}
    (hr : 0 < r) (hball : ball z r ⊆ U) (hg : ContinuousOn g (ball z r))
    (hLip : ∀ w ∈ ball z r, ‖g w - g z‖ ≤ L * ‖w - z‖)
    (hfar : IntegrableOn (fun w => g w / (w - z) ^ 2) (U \ ball z r)) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun w => g w / (w - z) ^ 2) (U \ ball z δ)) ∧
      ∃ v : ℂ, Tendsto (fun δ : ℝ => ∫ w in U \ ball z δ, g w / (w - z) ^ 2)
        (𝓝[>] 0) (𝓝 v) := by
  have hcm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  set F : ℂ → ℂ := fun v => g v / (v - z) ^ 2 with hFd
  set rem : ℂ → ℂ := fun v => F v - g z * ((v - z + 0 * conj (v - z)) ^ 2)⁻¹ with hremd
  have hgm : AEStronglyMeasurable g (volume.restrict (ball z r)) := hg.aestronglyMeasurable measurableSet_ball
  have hFm : AEStronglyMeasurable F (volume.restrict (ball z r)) :=
    hgm.mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hrem : IntegrableOn rem (ball z r) := by
    have hmod : Measurable fun v => g z * ((v - z + 0 * conj (v - z)) ^ 2)⁻¹ := by fun_prop
    refine ((e124p_invnorm_int z r).const_mul L).mono' (hFm.sub hmod.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton z))] with v hv hvu
    have hvu' : v - z ≠ 0 := sub_ne_zero.mpr hvu
    have hp : 0 < ‖v - z‖ := norm_pos_iff.mpr hvu'
    have e : rem v = (g v - g z) / (v - z) ^ 2 := by
      simp only [hremd, hFd, zero_mul, add_zero]
      field_simp
    rw [e, norm_div, norm_pow]
    calc ‖g v - g z‖ / ‖v - z‖ ^ 2 ≤ L * ‖v - z‖ / ‖v - z‖ ^ 2 :=
          div_le_div_of_nonneg_right (hLip v hv) (by positivity)
      _ = L * ‖v - z‖⁻¹ := by field_simp
  have hann : ∀ δ : ℝ, 0 < δ → δ ≤ r → IntegrableOn F (ball z r \ ball z δ) := by
    intro δ hδ hδr
    obtain ⟨hmi, -⟩ := e124p_model_zero (g z) 0 z (by simp) hδ hδr
    have h := (hrem.mono_set sdiff_subset).add hmi
    refine h.congr_fun (fun v _ => ?_) (measurableSet_ball.diff measurableSet_ball)
    rw [Pi.add_apply]
    simp only [hremd]
    ring
  have hsplit : ∀ δ : ℝ, δ ≤ r → U \ ball z δ = (U \ ball z r) ∪ (ball z r \ ball z δ) := by
    intro δ hδr
    ext v
    constructor
    · rintro ⟨hvU, hvδ⟩
      by_cases hvr : v ∈ ball z r
      · exact Or.inr ⟨hvr, hvδ⟩
      · exact Or.inl ⟨hvU, hvr⟩
    · rintro (⟨hvU, hvr⟩ | ⟨hvr, hvδ⟩)
      · exact ⟨hvU, fun h => hvr (ball_subset_ball hδr h)⟩
      · exact ⟨hball hvr, hvδ⟩
  have hint : ∀ δ : ℝ, 0 < δ → IntegrableOn F (U \ ball z δ) := by
    intro δ hδ
    rcases le_total δ r with h | h
    · rw [hsplit δ h]; exact hfar.union (hann δ hδ h)
    · exact hfar.mono_set (sdiff_subset_sdiff_right (ball_subset_ball h))
  refine ⟨hint, (∫ v in U \ ball z r, F v) + ∫ v in ball z r, rem v, ?_⟩
  have hT := e124p_rem_tendsto hrem (X := fun δ => ball z δ) (fun δ => measurableSet_ball) (fun v hv => by
    have hp : 0 < ‖v - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
    filter_upwards [Ioo_mem_nhdsGT hp] with δ hδ
    rw [mem_ball, dist_eq_norm, not_lt]
    exact hδ.2.le)
  refine (tendsto_const_nhds.add hT).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
  have hdisj : Disjoint (U \ ball z r) (ball z r \ ball z δ) :=
    disjoint_left.mpr fun v h1 h2 => h1.2 h2.1
  obtain ⟨hmi, hm0⟩ := e124p_model_zero (g z) 0 z (by simp) hδ.1 hδ.2.le
  have hFa := hann δ hδ.1 hδ.2.le
  show _ = ∫ v in U \ ball z δ, F v
  rw [hsplit δ hδ.2.le, setIntegral_union hdisj (measurableSet_ball.diff measurableSet_ball) hfar hFa]
  congr 1
  have e : ∫ v in ball z r \ ball z δ, rem v =
      (∫ v in ball z r \ ball z δ, F v) - ∫ v in ball z r \ ball z δ, g z * ((v - z + 0 * conj (v - z)) ^ 2)⁻¹ :=
    integral_sub hFa hmi
  rw [e, hm0, sub_zero]

-- H8
theorem s4hv_bounded_Bergman_trunc {ν K : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hK : K ∈ A21fun unitDiscExterior) (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun w => ν w * K w / (w - z) ^ 2) (unitDiscExterior \ ball z δ) := by
  let M := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal
  have hmeas : MeasurableSet (unitDiscExterior \ ball z δ) :=
    wp_exterior_isOpen.measurableSet.diff measurableSet_ball
  have hc : ContinuousOn (fun w => ν w * K w / (w - z) ^ 2) (unitDiscExterior \ ball z δ) :=
    (((wp_harmonic_continuousOn hν).mul hK.1.continuousOn).mono sdiff_subset).div
      ((continuousOn_id.sub continuousOn_const).pow 2) (fun w hw => pow_ne_zero 2 (sub_ne_zero.mpr (by
        intro heq
        subst w
        exact hw.2 (mem_ball_self hδ))))
  apply ((e212_trunc_int wp_exterior_isOpen hK z hδ).norm.const_mul M).mono'
    (hc.aestronglyMeasurable hmeas)
  filter_upwards [ae_restrict_mem hmeas] with w hw
  simp only [norm_div, norm_mul, norm_pow, norm_conj]
  rw [norm_sub_rev z w]
  calc ‖ν w‖ * ‖K w‖ / ‖w - z‖ ^ 2 ≤ M * ‖K w‖ / ‖w - z‖ ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (wp_harmonic_pointwise_bound hν hw.1) (norm_nonneg _)) (sq_nonneg _)
    _ = M * (‖K w‖ / ‖w - z‖ ^ 2) := by ring

-- H9
theorem s4hv_Bergman_square_integrable {ν K : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hK : K ∈ A21fun unitDiscExterior) :
    IntegrableOn (fun w => ν w * K w ^ 2) unitDiscExterior := by
  let M := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal
  have hc := (wp_harmonic_continuousOn hν).mul (hK.1.continuousOn.pow 2)
  apply ((e212_sq_integrable wp_exterior_isOpen hK).const_mul M).mono'
    (hc.aestronglyMeasurable wp_exterior_isOpen.measurableSet)
  filter_upwards [ae_restrict_mem wp_exterior_isOpen.measurableSet] with w hw
  change ‖ν w * K w ^ 2‖ ≤ M * ‖K w‖ ^ 2
  simp only [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (wp_harmonic_pointwise_bound hν hw) (sq_nonneg _)

-- H10
theorem s4hv_actual_kernel_pv {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ν : ℂ → ℂ}
    (hν : ν ∈ harmonicL2 unitDiscExterior) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (∀ δ : ℝ, 0 < δ → IntegrableOn (fun w => ν w * s4hv_kernel (gsans κ) w z)
      (unitDiscExterior \ ball z δ)) ∧
    ∃ v : ℂ,
      Tendsto (fun δ : ℝ => ∫ w in unitDiscExterior \ ball z δ,
        ν w * kerK4 (gsans κ) w z / (w - z) ^ 2) (𝓝[>] 0) (𝓝 v) ∧
      Tendsto (fun δ : ℝ => ∫ w in unitDiscExterior \ ball z δ,
        ν w * s4hv_kernel (gsans κ) w z) (𝓝[>] 0)
        (𝓝 ((π : ℂ) ^ 2 * (∫ w in unitDiscExterior, ν w * kerK4 (gsans κ) w z ^ 2) - 2 * π * v)) := by
  let K := fun w => kerK4 (gsans κ) w z
  have hK : K ∈ A21fun unitDiscExterior := s4hv_K4_column_A21 hκ hz
  have hg : ContDiffAt ℝ 1 (fun w => ν w * K w) z :=
    (((s4hv_harmonic_smooth hν).contDiffAt (wp_exterior_isOpen.mem_nhds hz)).of_le (by simp)).mul
      (((s4hv_K4_analytic hκ hz) z hz).contDiffAt.restrict_scalars ℝ)
  obtain ⟨L, t, ht, hLt⟩ := hg.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (wp_exterior_isOpen.mem_nhds hz))
  have hball : ball z r ⊆ unitDiscExterior := fun w hw => (hrt hw).2
  have hcont : ContinuousOn (fun w => ν w * K w) (ball z r) :=
    ((wp_harmonic_continuousOn hν).mul hK.1.continuousOn).mono hball
  have hLip : ∀ w ∈ ball z r, ‖ν w * K w - ν z * K z‖ ≤ (L : ℝ) * ‖w - z‖ :=
    fun w hw => hLt.norm_sub_le (hrt hw).1 (mem_of_mem_nhds ht)
  obtain ⟨hquad, v, hTv⟩ := s4hv_pv_quadratic hr hball hcont hLip
    (s4hv_bounded_Bergman_trunc hν hK z hr)
  have hreg := s4hv_Bergman_square_integrable hν hK
  have hTreg := e124p_rem_tendsto hreg (X := fun δ => ball z δ) (fun _ => measurableSet_ball)
    (fun w hw => by
      have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      rw [mem_ball, dist_eq_norm, not_lt]
      exact hδ.2.le)
  have hpoint : ∀ δ : ℝ, 0 < δ → ∀ w ∈ unitDiscExterior \ ball z δ,
      ν w * s4hv_kernel (gsans κ) w z =
        (π : ℂ) ^ 2 * (ν w * K w ^ 2) - (2 * π) * (ν w * K w / (w - z) ^ 2) := by
    intro δ hδ w hw
    have hwz : w ≠ z := by
      intro heq
      subst w
      exact hw.2 (mem_ball_self hδ)
    dsimp only [K]
    rw [s4hv_kernel_factorization _ hwz]
    ring
  have hint : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun w => ν w * s4hv_kernel (gsans κ) w z)
      (unitDiscExterior \ ball z δ) := by
    intro δ hδ
    have hsum : IntegrableOn (fun w => (π : ℂ) ^ 2 * (ν w * K w ^ 2) -
        (2 * π) * (ν w * K w / (w - z) ^ 2)) (unitDiscExterior \ ball z δ) :=
      ((hreg.mono_set sdiff_subset).const_mul ((π : ℂ) ^ 2)).sub
        ((hquad δ hδ).const_mul (2 * π : ℂ))
    exact hsum.congr_fun
      (fun w hw => (hpoint δ hδ w hw).symm) (wp_exterior_isOpen.measurableSet.diff measurableSet_ball)
  have hInt : ∀ δ : ℝ, 0 < δ →
      (∫ w in unitDiscExterior \ ball z δ, ν w * s4hv_kernel (gsans κ) w z) =
        (π : ℂ) ^ 2 * (∫ w in unitDiscExterior \ ball z δ, ν w * K w ^ 2) -
          (2 * π) * ∫ w in unitDiscExterior \ ball z δ, ν w * K w / (w - z) ^ 2 := by
    intro δ hδ
    rw [setIntegral_congr_fun (wp_exterior_isOpen.measurableSet.diff measurableSet_ball) (hpoint δ hδ),
      integral_sub ((hreg.mono_set sdiff_subset).const_mul ((π : ℂ) ^ 2))
        ((hquad δ hδ).const_mul (2 * π : ℂ)), integral_const_mul, integral_const_mul]
  refine ⟨hint, v, hTv, ?_⟩
  apply ((hTreg.const_mul ((π : ℂ) ^ 2)).sub (hTv.const_mul (2 * π : ℂ))).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hInt δ hδ).symm

end Ch2
end TakhtajanTeo
