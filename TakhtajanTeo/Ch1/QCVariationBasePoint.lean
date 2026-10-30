import TakhtajanTeo.Ch1.QCVariationCovariance

/-! # Actual first variations at arbitrary Beltrami base points -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

/-- The derivative of the actual coefficient-parametrized plane solution,
with its explicit normalized first-variation value. -/
theorem qcv_planeSolution_base_hasFDerivAt {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (z : ℂ) :
    ∃ L : LinfStar →L[ℂ] ℂ,
      (∀ ν, L ν = ahVar
        (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) (qcv_planeSolution μ z)) ∧
      HasFDerivAt (fun v => qcv_planeSolution (μ + v) z) L 0 := by
  have hk := bc_norm_lt_one hμ
  have hN := (qcv_W_props hk).1
  have hT : ∀ v : LinfStar, IsBeltramiCoeff (extB v) univ (1 * ‖v‖) :=
    fun v => by simpa using extB_isBeltramiCoeff v
  obtain ⟨L, hL, hd⟩ := qcv_plane_hasFDerivAt (norm_nonneg μ) hk
    (extB_isBeltramiCoeff μ) hN extB zero_le_one hT qcv_extB_lin z
  refine ⟨L, hL, hd.congr_of_eventuallyEq ?_⟩
  filter_upwards [ball_mem_nhds (0 : LinfStar)
    (show 0 < (1 - ‖μ‖) / 2 by linarith)] with v hv
  have hvn : ‖v‖ < (1 - ‖μ‖) / 2 := mem_ball_zero_iff.mp hv
  have hsmall : ‖μ + v‖ < 1 := by
    have hh := norm_add_le μ v
    linarith
  have he : extB (μ + v) =ᵐ[volume] (fun u => extB μ u + extB v u) := by
    simpa only [one_smul, one_mul] using qcv_extB_lin 1 μ v
  exact congrFun (qcv_ns_congr_ae (norm_nonneg _) hsmall
    (extB_isBeltramiCoeff (μ + v)) he) z

theorem qcv_planeSolution_base_hasDerivAt {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) (z : ℂ) :
    HasDerivAt (fun t : ℂ => qcv_planeSolution (μ + t • ν) z)
      (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ))
        (qcv_planeSolution μ z)) 0 := by
  obtain ⟨L, hL, hd⟩ := qcv_planeSolution_base_hasFDerivAt hμ z
  have ht : HasDerivAt (fun t : ℂ => t • ν) ν 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const ν
  have hd' : HasFDerivAt (fun v => qcv_planeSolution (μ + v) z) L ((0 : ℂ) • ν) := by
    simpa using hd
  simpa only [Function.comp_def, hL ν] using hd'.comp_hasDerivAt 0 ht

/-- The source-coordinate first-variation integral at every base point. -/
theorem qcv_planeSolution_base_variation {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) (z : ℂ) :
    HasDerivAt (fun t : ℂ => qcv_planeSolution (μ + t • ν) z)
      (-(1 / Real.pi : ℂ) * ∫ u in unitDiscExterior,
        ν u * ahKer (qcv_planeSolution μ z) (qcv_planeSolution μ u) *
          dz (qcv_planeSolution μ) u ^ 2) 0 := by
  have hd := qcv_planeSolution_base_hasDerivAt hμ ν z
  have he := qcv_var_source (norm_nonneg μ) (bc_norm_lt_one hμ)
    (extB_isBeltramiCoeff μ) (qcv_W_props (bc_norm_lt_one hμ)).1
    (extB_isBeltramiCoeff ν) (qcv_planeSolution μ z)
  have hI : (∫ u, extB ν u * ahKer (qcv_planeSolution μ z) (qcv_planeSolution μ u) *
      dz (qcv_planeSolution μ) u ^ 2) =
      ∫ u in unitDiscExterior, ν u * ahKer (qcv_planeSolution μ z) (qcv_planeSolution μ u) *
        dz (qcv_planeSolution μ) u ^ 2 := by
    rw [← integral_indicator bc_hEo.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      by_cases hu : u ∈ unitDiscExterior <;> simp [extB, hu]
  change ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ))
    (qcv_planeSolution μ z) = -(1 / Real.pi : ℂ) *
      ∫ u, extB ν u * ahKer (qcv_planeSolution μ z) (qcv_planeSolution μ u) *
        dz (qcv_planeSolution μ) u ^ 2 at he
  rw [hI] at he
  exact hd.congr_deriv he

/-- The actual transition has first variation based at the identity on the moving disk. -/
theorem qcv_planeTransition_base_hasDerivAt {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) (y : ℂ) :
    HasDerivAt (fun t : ℂ => qcv_planeTransition (μ + t • ν) μ y)
      (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) y) 0 := by
  have hd := qcv_planeSolution_base_hasDerivAt hμ ν
    (Function.invFun (qcv_planeSolution μ) y)
  have he := Function.invFun_eq ((qcv_planeSolution_bijective hμ).2 y)
  simpa only [qcv_planeTransition, Function.comp_apply, he] using hd

/-- Source-coordinate form of the transition's first variation. -/
theorem qcv_planeTransition_base_variation {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) (y : ℂ) :
    HasDerivAt (fun t : ℂ => qcv_planeTransition (μ + t • ν) μ y)
      (-(1 / Real.pi : ℂ) * ∫ u in unitDiscExterior,
        ν u * ahKer y (qcv_planeSolution μ u) * dz (qcv_planeSolution μ) u ^ 2) 0 := by
  have hd := qcv_planeSolution_base_variation hμ ν
    (Function.invFun (qcv_planeSolution μ) y)
  have he := Function.invFun_eq ((qcv_planeSolution_bijective hμ).2 y)
  simpa only [qcv_planeTransition, Function.comp_apply, he] using hd

/-- The transported coefficient is genuinely zero on the moving disk. -/
theorem qcv_base_dot_zero_on_disk {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {y : ℂ} (hy : y ∈ qcv_planeDisk μ) :
    ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ) y = 0 := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hi := (qcv_planeSolution_bijective hμ).1.injOn.leftInvOn_invFunOn (mem_univ z)
  have hzE : z ∉ unitDiscExterior := by
    have hh := mem_ball_zero_iff.mp hz
    exact not_lt_of_ge hh.le
  simp only [ahT_dot, hi, extB, indicator_of_notMem hzE, zero_div, zero_mul]

/-- The transformed first-variation coefficient stays bounded on the whole plane. -/
theorem qcv_base_dot_isBeltramiCoeff {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    IsBeltramiCoeff (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) univ
      (‖ν‖ / (1 - ‖μ‖ ^ 2)) := by
  have hN := (qcv_W_props (bc_norm_lt_one hμ)).1
  exact qcv_dot_beltrami (norm_nonneg μ) (bc_norm_lt_one hμ)
    (extB_isBeltramiCoeff μ) hN.1 hN.2.1 (extB_isBeltramiCoeff ν)

end QCV
end TakhtajanTeo
