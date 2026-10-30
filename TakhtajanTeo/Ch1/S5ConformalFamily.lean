import TakhtajanTeo.Ch1.S5WeldingRegularity
import TakhtajanTeo.Ch1.BanachHolomorphicAnalytic

/-! Complexification of the actual normalized welding families. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_linear_family_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E → ℂ → ℂ) (hT : ∀ v, IsBeltramiCoeff (T v) univ ‖v‖)
    (hlin : ∀ (a : ℂ) v w, T (a • v + w) =ᵐ[volume] fun z => a * T v z + T w z)
    (z : ℂ) : DifferentiableOn ℂ (fun v => normalizedSolution (T v) z) (ball 0 1) := by
  intro v₀ hv₀
  have hk : ‖v₀‖ < 1 := mem_ball_zero_iff.mp hv₀
  obtain ⟨f₀, hf₀, -, -⟩ := thm13_7_normalized_existence (norm_nonneg v₀) hk (hT v₀)
  have hT' : ∀ v, IsBeltramiCoeff (T v) univ (1 * ‖v‖) := by simpa using hT
  obtain ⟨L, -, hL⟩ := QCV.qcv_plane_hasFDerivAt (norm_nonneg v₀) hk (hT v₀) hf₀
    T zero_le_one hT' hlin z
  refine DifferentiableAt.differentiableWithinAt ⟨L, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h := hasFDerivAt_iff_isLittleO_nhds_zero.1 hL
  have key : ∀ v : E, ‖v‖ < (1 - ‖v₀‖) / 2 →
      normalizedSolution (fun u => T v₀ u + T v u) = normalizedSolution (T (v₀ + v)) := by
    intro v hv
    have hk' : ‖v₀ + v‖ < 1 := by linarith [norm_add_le v₀ v]
    have hae : T (v₀ + v) =ᵐ[volume] fun u => T v₀ u + T v u := by
      simpa using hlin 1 v₀ v
    exact (QCV.qcv_ns_congr_ae (norm_nonneg _) hk' (hT (v₀ + v)) hae).symm
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Metric.ball_mem_nhds (0 : E) (show 0 < (1 - ‖v₀‖) / 2 by linarith)] with v hv
  rw [mem_ball_zero_iff] at hv
  have h0 : ‖(0 : E)‖ < (1 - ‖v₀‖) / 2 := by simp; linarith
  simp only [zero_add]
  rw [key v hv, key 0 h0, add_zero]

-- L2
theorem s5cf_linear_family_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E → ℂ → ℂ) (hT : ∀ v, IsBeltramiCoeff (T v) univ ‖v‖)
    (hlin : ∀ (a : ℂ) v w, T (a • v + w) =ᵐ[volume] fun z => a * T v z + T w z)
    (z : ℂ) : AnalyticOnNhd ℂ (fun v => normalizedSolution (T v) z) (ball 0 1) := by
  exact bha_analyticOnNhd isOpen_ball (s5cf_linear_family_differentiableOn T hT hlin z)

-- L3
theorem s5cf_section_analytic (p : T1) :
    ∃ s : AInf unitDisc → LinfStar, ∃ U : Set (AInf unitDisc),
      IsOpen U ∧ bers p ∈ U ∧ AnalyticOnNhd ℂ s U ∧
      s (bers p) = ((Quotient.out p : LinfStarBall) : LinfStar) ∧
      ∀ χ ∈ U, ∃ h : s χ ∈ LinfStarBall, bers (Phi ⟨s χ, h⟩) = χ := by
  obtain ⟨s, U, hU, hp, hs, hs0, he⟩ := s5wr_section p
  exact ⟨s, U, hU, hp, bha_analyticOnNhd hU hs, hs0, he⟩

/-- Independent exterior and reflected-interior Beltrami parameters. -/
def s5cf_coeff (p : LinfStar × LinfStar) (z : ℂ) : ℂ :=
  if z ∈ unitDisc then extB p.2 (refl z) * z ^ 2 / conj z ^ 2 else extB p.1 z

-- L4
theorem s5cf_coeff_bound (p : LinfStar × LinfStar) :
    IsBeltramiCoeff (s5cf_coeff p) univ ‖p‖ := by
  have h1 := extB_isBeltramiCoeff p.1
  have h2 := extB_isBeltramiCoeff p.2
  rw [IsBeltramiCoeff, Measure.restrict_univ] at h1 h2 ⊢
  have hg : AEStronglyMeasurable
      (fun z : ℂ => extB p.2 (refl z) * z ^ 2 / conj z ^ 2) volume :=
    ((aestronglyMeasurable_comp_refl h2.1).mul
      (by fun_prop : AEStronglyMeasurable (fun z : ℂ => z ^ 2) volume)).div₀
      (by fun_prop : AEStronglyMeasurable (fun z : ℂ => conj z ^ 2) volume)
  refine ⟨hg.restrict.piecewise isOpen_ball.measurableSet h1.1.restrict, ?_⟩
  filter_upwards [h1.2, ae_refl h2.2] with z hz1 hz2
  by_cases hz : z ∈ unitDisc
  · rw [s5cf_coeff, if_pos hz, norm_div, norm_mul, norm_pow, norm_pow, norm_conj]
    by_cases hz0 : z = 0
    · simp [hz0]
    · rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz0))]
      exact hz2.trans (norm_snd_le p)
  · rw [s5cf_coeff, if_neg hz]
    exact hz1.trans (norm_fst_le p)

-- L5
theorem s5cf_coeff_linear (a : ℂ) (p q : LinfStar × LinfStar) :
    s5cf_coeff (a • p + q) =ᵐ[volume] fun z => a * s5cf_coeff p z + s5cf_coeff q z := by
  filter_upwards [QCV.qcv_extB_lin a p.1 q.1, ae_refl (QCV.qcv_extB_lin a p.2 q.2)] with z h1 h2
  by_cases hz : z ∈ unitDisc
  · simp only [s5cf_coeff, if_pos hz]
    change extB (a • p.2 + q.2) (refl z) * z ^ 2 / conj z ^ 2 = _
    rw [h2]
    ring
  · simp only [s5cf_coeff, if_neg hz]
    change extB (a • p.1 + q.1) z = _
    exact h1

-- L6
theorem s5cf_coeff_plane_analytic (z : ℂ) :
    AnalyticOnNhd ℂ (fun p : LinfStar × LinfStar => normalizedSolution (s5cf_coeff p) z)
      (ball 0 1) := by
  exact s5cf_linear_family_analytic s5cf_coeff s5cf_coeff_bound s5cf_coeff_linear z

-- L7
theorem s5cf_coeff_diagonal (μ : LinfStar) :
    s5cf_coeff (μ, star μ) =ᵐ[volume] extA μ := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hs : extB (star μ) =ᵐ[volume] fun z => conj (extB μ z) := by
    filter_upwards [(ae_restrict_iff' hE).mp (Lp.coeFn_star μ)] with z hz
    by_cases he : z ∈ unitDiscExterior
    · simpa [extB, he] using hz he
    · simp [extB, he]
  filter_upwards [ae_refl hs] with z hz
  by_cases hD : z ∈ unitDisc
  · have hdn : ‖z‖ < 1 := mem_ball_zero_iff.mp hD
    have hen : ¬ 1 < ‖z‖ := by linarith
    by_cases hz0 : z = 0
    · subst z; norm_num [s5cf_coeff, hD, extA]
    · have hr := (refl_mem_exterior_iff hz0).mpr hD
      change (if z ∈ unitDisc then extB (star μ) (refl z) * z ^ 2 / conj z ^ 2
        else extB μ z) = _
      rw [if_pos hD, hz]
      simp only [extB, indicator_of_mem hr, extA, if_neg hen, if_pos hdn]
  · have hdn : ¬ ‖z‖ < 1 := fun h => hD (mem_ball_zero_iff.mpr h)
    by_cases hE' : z ∈ unitDiscExterior
    · simp [s5cf_coeff, hD, extA, extB, hE', show 1 < ‖z‖ from hE']
    · simp [s5cf_coeff, hD, extA, extB, hE', show ¬ 1 < ‖z‖ from hE', hdn]

-- L8
theorem s5cf_plane_diagonal {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    normalizedSolution (s5cf_coeff (μ, star μ)) = normalizedSolution (extA μ) := by
  exact (QCV.qcv_ns_congr_ae (norm_nonneg μ) (mem_ball_zero_iff.mp hμ)
    (extA_isBeltramiCoeff μ) (s5cf_coeff_diagonal μ).symm).symm

end TakhtajanTeo
