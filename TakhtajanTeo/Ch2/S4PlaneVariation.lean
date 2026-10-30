import TakhtajanTeo.Ch2.S4ReflectedKernel
import TakhtajanTeo.Ch1.QCVariationSchwarzianBasePoint

/-! # Actual plane-solution Schwarzian variation off the coefficient support -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC QCV
namespace Ch2

-- L8
theorem s4v_linear_coeff {m : ℂ → ℂ} {k : ℝ}
    (hm : IsBeltramiCoeff m univ k) (t : ℂ) :
    IsBeltramiCoeff (fun u => t * m u) univ (‖t‖ * k) := by
  refine ⟨hm.1.const_mul t, ?_⟩
  filter_upwards [hm.2] with u hu
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg t)

-- L9
theorem s4v_normalized_first_variation {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : IsBeltramiCoeff m univ k) (z : ℂ) :
    HasDerivAt (fun t : ℂ => normalizedSolution (fun u => t * m u) z) (ahVar m z) 0 := by
  have hzero : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Eventually.of_forall fun u => by simp⟩
  obtain ⟨L, hL, hLv⟩ := qcv_plane_two_param_hasFDerivAt hk le_rfl hm hzero
    (p₀ := (0, 0)) (by simp) z
  have hline : HasDerivAt (fun t : ℂ => (t, (0 : ℂ))) ((1 : ℂ), (0 : ℂ)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hd := hL.comp_hasDerivAt (f := fun t : ℂ => (t, (0 : ℂ))) 0 hline
  have hv : L (1, 0) = ahVar m z := by
    rw [hLv]
    simp only [zero_mul, one_mul, Pi.zero_apply, add_zero]
    change -(1 / π : ℂ) * (∫ u, m u * ahKer (normalizedSolution 0 z)
      (normalizedSolution 0 u) * dz (normalizedSolution 0) u ^ 2) = _
    rw [bB_l_normalizedSolution_zero]
    simp only [id_eq, dz, fderiv_id, ContinuousLinearMap.id_apply]
    norm_num [ahVar]
  simpa only [Function.comp_def, Pi.zero_apply, mul_zero, add_zero, hv] using hd

-- L10
theorem s4v_normalized_holo {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : IsBeltramiCoeff m univ k) {U : Set ℂ} (hU : IsOpen U)
    (hzero : ∀ u ∈ U, m u = 0) {t : ℂ} (ht : ‖t‖ * k < 1) :
    DifferentiableOn ℂ (normalizedSolution (fun u => t * m u)) U ∧
      Function.Injective (normalizedSolution (fun u => t * m u)) := by
  have hN := qcv_ns_spec (mul_nonneg (norm_nonneg t) hk) ht (s4v_linear_coeff hm t)
  obtain ⟨⟨K, hK⟩, _, _, _, hchar⟩ := hN
  have hz : ∀ᵐ u ∂(volume.restrict U),
      complexDilatation (normalizedSolution (fun v => t * m v)) u = 0 := by
    filter_upwards [ae_restrict_of_ae hchar, ae_restrict_mem hU.measurableSet] with u hu huU
    rw [hu, hzero u huU, mul_zero]
  exact ⟨nx_differentiableOn_of_dilatation_zero
    (nx_isKQC_restrict hK hU (subset_univ _)) hz,
    fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab⟩

-- L11
theorem s4v_normalized_joint_cont {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : IsBeltramiCoeff m univ k) :
    ContinuousOn (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * m u) p.2)
      ({t : ℂ | ‖t‖ * k < 1} ×ˢ univ) := by
  have hzero : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
    ⟨aestronglyMeasurable_zero, Eventually.of_forall fun u => by simp⟩
  let W : Set (ℂ × ℂ) := {p | k * ‖p‖ < 1}
  have hW : IsOpen W := isOpen_lt (continuous_const.mul continuous_norm) continuous_const
  have hb : ∀ p ∈ W, ∃ c < 1, IsBeltramiCoeff (fun u => p.1 * m u + p.2 * (0 : ℂ → ℂ) u) univ c := by
    intro p hp
    refine ⟨k * ‖p‖, hp, ?_⟩
    simpa only [abs_of_nonneg hk, abs_zero, add_zero] using wr_coeff_lin hm hzero p
  have hc := wr_ns2_cont hm hzero hW hb
  have he : ContinuousOn (fun p : ℂ × ℂ => ((p.1, (0 : ℂ)), p.2))
      ({t : ℂ | ‖t‖ * k < 1} ×ˢ univ) := by fun_prop
  have hmap : MapsTo (fun p : ℂ × ℂ => ((p.1, (0 : ℂ)), p.2))
      ({t : ℂ | ‖t‖ * k < 1} ×ˢ univ) (W ×ˢ univ) := by
    rintro ⟨t, z⟩ ⟨ht, _⟩
    refine ⟨?_, mem_univ _⟩
    simpa only [W, mem_ofPred_eq, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg t), mul_comm] using ht
  simpa only [Function.comp_def, Pi.zero_apply, mul_zero, add_zero] using hc.comp he hmap

-- L12
theorem s4v_normalized_schwarzian_variation {m : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : IsBeltramiCoeff m univ k) {U : Set ℂ} (hU : IsOpen U)
    (hzero : ∀ u ∈ U, m u = 0) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun t : ℂ => schwarzianHol (normalizedSolution (fun u => t * m u)) z)
      (-(6 / π : ℂ) * ∫ u, m u / (u - z) ^ 4) 0 := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z hz
  let r : ℝ := 1 / (2 * (k + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrk : r * (k + 1) = 1 / 2 := by dsimp [r]; field_simp
  have hsmall : ∀ t ∈ closedBall (0 : ℂ) r, ‖t‖ * k < 1 := by
    intro t ht
    have ht' : ‖t‖ ≤ r := mem_closedBall_zero_iff.mp ht
    have htk := mul_le_mul_of_nonneg_right ht' hk
    nlinarith
  have hc : ContinuousOn (fun p : ℂ × ℂ => normalizedSolution (fun u => p.1 * m u) p.2)
      (closedBall (0 : ℂ) r ×ˢ closedBall z R) :=
    (s4v_normalized_joint_cont hk hm).mono fun p hp => ⟨hsmall p.1 hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) r).prod (isCompact_closedBall z R)).exists_bound_of_continuousOn hc
  have hspace : ∀ t ∈ ball (0 : ℂ) r,
      DifferentiableOn ℂ (normalizedSolution (fun u => t * m u)) (ball z R) := by
    intro t ht
    exact (s4v_normalized_holo hk hm hU hzero (hsmall t (ball_subset_closedBall ht))).1.mono hRU
  have hparam : ∀ u ∈ ball z R,
      DifferentiableOn ℂ (fun t : ℂ => normalizedSolution (fun v => t * m v) u) (ball 0 r) := by
    intro u _ t ht
    have hzBC : IsBeltramiCoeff (0 : ℂ → ℂ) univ 0 :=
      ⟨aestronglyMeasurable_zero, Eventually.of_forall fun v => by simp⟩
    obtain ⟨L, hL, _⟩ := qcv_plane_two_param_hasFDerivAt hk le_rfl hm hzBC
      (p₀ := (t, 0)) (by simpa using hsmall t (ball_subset_closedBall ht)) u
    have he : DifferentiableAt ℂ (fun s : ℂ => (s, (0 : ℂ))) t := by fun_prop
    have hd := hL.differentiableAt.comp t he
    simpa only [Function.comp_def, Pi.zero_apply, mul_zero, add_zero] using hd.differentiableWithinAt
  have hbound : ∀ t ∈ ball (0 : ℂ) r, ∀ u ∈ ball z R,
      ‖normalizedSolution (fun v => t * m v) u‖ ≤ M := by
    intro t ht u hu
    exact hM (t, u) ⟨ball_subset_closedBall ht, ball_subset_closedBall hu⟩
  have h0 : normalizedSolution (fun u => (0 : ℂ) * m u) = id := by
    simp only [zero_mul]
    exact bB_l_normalizedSolution_zero
  have hne : ∀ t ∈ ball (0 : ℂ) r, deriv (normalizedSolution (fun u => t * m u)) z ≠ 0 := by
    intro t ht
    obtain ⟨hh, hi⟩ := s4v_normalized_holo hk hm hU hzero (hsmall t (ball_subset_closedBall ht))
    exact deriv_ne_zero_of_injOn hU hh hi.injOn hz
  have hs := qcv_param_schwarzian_id hr hR hspace hparam hbound h0 hne
  have hfirst : (fun u => deriv (fun t : ℂ => normalizedSolution (fun v => t * m v) u) 0) = ahVar m :=
    funext fun u => (s4v_normalized_first_variation hk hm u).deriv
  rwa [hfirst, qcv_ahVar_iter3 hk hm hU hzero hz] at hs

end Ch2
end TakhtajanTeo
