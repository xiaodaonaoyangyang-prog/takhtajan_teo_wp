import TakhtajanTeo.Ch1.QCVariationSchwarzianBasePoint

/-! # Differential covariance of the actual Bers map at every base point -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

theorem qcv_bers_base_pointwise {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun t : ℂ => AInf.toFun (bersPhi (μ + t • ν)) z)
      (AInf.toFun (fderiv ℂ bersPhi μ ν) z) 0 := by
  have ht : HasDerivAt (fun t : ℂ => μ + t • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const ν).const_add μ
  have hb := (qcv_bersPhi_differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds hμ)).hasFDerivAt
  have hb' : HasFDerivAt bersPhi (fderiv ℂ bersPhi μ) (μ + (0 : ℂ) • ν) := by
    simpa using hb
  have hline := hb'.comp_hasDerivAt 0 ht
  let ev : AInf unitDisc →L[ℂ] ℂ :=
    ((1 - ‖z‖ ^ 2 : ℂ) ^ 2)⁻¹ • ((BoundedContinuousFunction.evalCLM ℂ (⟨z, hz⟩ : unitDisc)).comp
      (Submodule.subtypeL _))
  have hev : ∀ φ : AInf unitDisc, ev φ = AInf.toFun φ z := by
    intro φ
    simp [ev, AInf.toFun, unweight, dite_eq_left hz, div_eq_inv_mul]
  simpa only [Function.comp_def, hev] using ev.hasFDerivAt.comp_hasDerivAt 0 hline

/-- General-base differential covariance, derived from the actual nonlinear
transition and justified parameter/space differentiation. -/
theorem qcv_bers_differential_covariance {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (fderiv ℂ bersPhi μ ν) z =
      iteratedDeriv 3 (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)))
        (qcv_planeSolution μ z) * deriv (qcv_planeSolution μ) z ^ 2 := by
  have hy : qcv_planeSolution μ z ∈ qcv_planeDisk μ := ⟨z, hz, rfl⟩
  have hs := ((qcv_planeTransition_schwarzian_variation hμ ν hy).mul_const
    (deriv (qcv_planeSolution μ) z ^ 2)).add_const (AInf.toFun (bersPhi μ) z)
  have hr : 0 < (1 - ‖μ‖) / (2 * (‖ν‖ + 1)) := by
    have := bc_norm_lt_one hμ
    positivity
  have he : (fun t : ℂ => AInf.toFun (bersPhi (μ + t • ν)) z) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => schwarzianHol (qcv_planeTransition (μ + t • ν) μ) (qcv_planeSolution μ z) *
        deriv (qcv_planeSolution μ) z ^ 2 + AInf.toFun (bersPhi μ) z) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    exact sub_eq_iff_eq_add.mp (qcv_bers_covariance hμ
      (qcv_affine_curve_mem_ball hμ ν (mem_ball_zero_iff.mp ht)) hz)
  exact (qcv_bers_base_pointwise hμ ν hz).unique (hs.congr_of_eventuallyEq he)

/-- The same exact formula along the actual Beltrami right-translation tangent. -/
theorem qcv_translatedBers_differential_covariance {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (qcv_translatedBersDerivative μ ν) z =
      iteratedDeriv 3 (ahVar (ahT_dot (extB (qcv_rightDerivative μ ν))
        (extB μ) (qcv_planeSolution μ))) (qcv_planeSolution μ z) *
          deriv (qcv_planeSolution μ) z ^ 2 := by
  rw [qcv_translatedBersDerivative_apply hμ]
  exact qcv_bers_differential_covariance hμ _ hz

/-- An exact analytic characterization of the actual general-base Bers kernel. -/
theorem qcv_bers_kernel_iff_third_variation_zero {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    fderiv ℂ bersPhi μ ν = 0 ↔
      ∀ y ∈ qcv_planeDisk μ,
        iteratedDeriv 3 (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ))) y = 0 := by
  constructor
  · intro hν y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hh := qcv_bers_differential_covariance hμ ν hz
    rw [hν] at hh
    have hz0 : AInf.toFun (0 : AInf unitDisc) z = 0 := by
      simp [AInf.toFun, unweight, hz]
    rw [hz0] at hh
    have hW := qcv_planeSolution_conformal hμ
    have hd := deriv_ne_zero_of_injOn isOpen_ball hW.1 hW.2.1 hz
    exact (mul_eq_zero.mp hh.symm).resolve_right (pow_ne_zero 2 hd)
  · intro hh
    apply AInf.ext_toFun_disc
    intro z hz
    rw [qcv_bers_differential_covariance hμ ν hz, hh _ ⟨z, hz, rfl⟩, zero_mul]
    simp [AInf.toFun, unweight, hz]

end QCV
end TakhtajanTeo
