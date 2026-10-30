import TakhtajanTeo.Ch1.BeltramiCompose
import TakhtajanTeo.Ch1.QCVariationPlane

/-! # Actual L-infinity collar cutoffs and their normalized solutions

The cutoff removes a neighborhood of the unit circle from an exterior
coefficient. Its support is separated from the circle; no Euclidean
compact-support claim at infinity is made.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace AppB

def b9CollarCutoff (μ : LinfStar) (R : ℝ) : LinfStar :=
  toLinf ({z : ℂ | R ≤ ‖z‖}.indicator μ)

theorem b9_collar_memLp (μ : LinfStar) (R : ℝ) :
    MemLp ({z : ℂ | R ≤ ‖z‖}.indicator μ) ∞ (volume.restrict unitDiscExterior) :=
  (Lp.memLp μ).indicator (measurableSet_le measurable_const measurable_norm)

theorem b9_collar_ae (μ : LinfStar) (R : ℝ) :
    (b9CollarCutoff μ R : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior]
      {z : ℂ | R ≤ ‖z‖}.indicator μ := bc_toLinf_ae (b9_collar_memLp μ R)

theorem b9_collar_norm_le (μ : LinfStar) (R : ℝ) : ‖b9CollarCutoff μ R‖ ≤ ‖μ‖ := by
  apply bc_Lp_norm_le _ (norm_nonneg _)
  filter_upwards [b9_collar_ae μ R, LinfStar_ae_norm_le μ] with z hz hb
  rw [hz]
  by_cases h : R ≤ ‖z‖
  · simpa [Set.indicator, h] using hb
  · simp [Set.indicator, h, norm_nonneg μ]

theorem b9_collar_ball {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (R : ℝ) :
    b9CollarCutoff μ R ∈ LinfStarBall := by
  apply mem_ball_zero_iff.mpr
  exact (b9_collar_norm_le μ R).trans_lt (bc_norm_lt_one hμ)

theorem b9_collar_error_le {μ : LinfStar} {R ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < R → ‖μ z‖ ≤ ε) :
    ‖b9CollarCutoff μ R - μ‖ ≤ ε := by
  apply bc_Lp_norm_le _ hε
  filter_upwards [b9_collar_ae μ R, Lp.coeFn_sub (b9CollarCutoff μ R) μ, hsmall] with z hz hs hb
  rw [hs]
  dsimp only [Pi.sub_apply]
  rw [hz]
  by_cases h : R ≤ ‖z‖
  · simpa [Set.indicator,h] using hε
  · simpa [Set.indicator,h] using hb (not_le.mp h)

/-- The quotient-valued cutoffs converge in the genuine L-infinity norm. -/
theorem b9_collar_tendsto {μ : LinfStar}
    (hvan : ∀ ε > 0, ∃ R > 1,
      ∀ᵐ z ∂(volume.restrict unitDiscExterior), ‖z‖ < R → ‖μ z‖ ≤ ε)
    {R : ℕ → ℝ} (hR : Tendsto R atTop (𝓝 1)) :
    Tendsto (fun n => b9CollarCutoff μ (R n)) atTop (𝓝 μ) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨S,hS,hs⟩ := hvan (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hR.eventually (gt_mem_nhds hS))
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hb : ‖b9CollarCutoff μ (R n) - μ‖ ≤ ε/2 := by
    apply b9_collar_error_le (by positivity)
    filter_upwards [hs] with z hz
    exact fun hzR => hz (hzR.trans (hN n hn))
  linarith

/-- The plane coefficient is exactly the cutoff of the original zero
extension, almost everywhere. This identifies the actual coefficient class. -/
theorem b9_collar_extB_ae (μ : LinfStar) (R : ℝ) :
    extB (b9CollarCutoff μ R) =ᵐ[volume]
      {z : ℂ | R ≤ ‖z‖}.indicator (extB μ) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  have ha := (ae_restrict_iff' hE).mp (b9_collar_ae μ R)
  filter_upwards [ha] with z hz
  by_cases h : z ∈ unitDiscExterior
  · simp only [extB, indicator_of_mem h]
    rw [hz h]
    by_cases hR : R ≤ ‖z‖ <;> simp [Set.indicator,hR,h]
  · simp [extB,Set.indicator,h]

theorem b9_collar_extB_zero {μ : LinfStar} {R : ℝ} :
    extB (b9CollarCutoff μ R) =ᵐ[volume.restrict (ball (0 : ℂ) R)] 0 := by
  filter_upwards [ae_restrict_of_ae (b9_collar_extB_ae μ R),
    ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) R))] with z hz hzR
  rw [hz]
  have hn : z ∉ {z : ℂ | R ≤ ‖z‖} := not_le.mpr (mem_ball_zero_iff.mp hzR)
  exact indicator_of_notMem hn (extB μ)

/-- The actual normalized solution for a collar cutoff is holomorphic on
the enlarged disk, with no extra extension assumption. -/
theorem b9_collar_solution_holomorphic {μ : LinfStar} {R : ℝ} {W : ℂ → ℂ}
    (hW : IsNormalizedSolution W (extB (b9CollarCutoff μ R))) :
    DifferentiableOn ℂ W (ball 0 R) := by
  obtain ⟨⟨K,hK⟩,hs,h0,h1,hchar⟩ := hW
  have hz : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) R)), complexDilatation W z = 0 := by
    filter_upwards [ae_restrict_of_ae hchar, b9_collar_extB_zero (μ := μ) (R := R)] with z hz he
    exact hz.trans he
  exact nx_differentiableOn_of_dilatation_zero
    (nx_isKQC_restrict hK isOpen_ball (subset_univ _)) hz

theorem b9_collar_normalizedSolution_holomorphic {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (R : ℝ) :
    DifferentiableOn ℂ (normalizedSolution (extB (b9CollarCutoff μ R))) (ball 0 R) := by
  exact b9_collar_solution_holomorphic (QCV.qcv_ns_spec
    (norm_nonneg _) (bc_norm_lt_one (b9_collar_ball hμ R)) (extB_isBeltramiCoeff _))

end AppB
end TakhtajanTeo
