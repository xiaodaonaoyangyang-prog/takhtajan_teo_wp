import TakhtajanTeo.Ch1.QCVariationBasePoint

/-! # Schwarzian variation at arbitrary base points via actual moving-domain transitions -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

theorem qcv_affine_curve_mem_ball {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar)
    {t : ℂ} (ht : ‖t‖ < (1 - ‖μ‖) / (2 * (‖ν‖ + 1))) :
    μ + t • ν ∈ LinfStarBall := by
  have hk := bc_norm_lt_one hμ
  have hh := norm_add_le μ (t • ν)
  rw [norm_smul] at hh
  rw [lt_div_iff₀ (by positivity)] at ht
  have hn : ‖μ + t • ν‖ < 1 := by nlinarith [norm_nonneg t, norm_nonneg ν]
  simpa [LinfStarBall] using hn

/-- Cauchy estimates justify the derivative of the Schwarzian for a bounded
holomorphic family based at the identity. -/
theorem qcv_param_schwarzian_id {F : ℂ → ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hζ : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (F t) (ball c R))
    (ht : ∀ ζ ∈ ball c R, DifferentiableOn ℂ (fun t => F t ζ) (ball (0 : ℂ) r))
    (hM : ∀ t ∈ ball (0 : ℂ) r, ∀ ζ ∈ ball c R, ‖F t ζ‖ ≤ M)
    (h0 : F 0 = id) (hne : ∀ t ∈ ball (0 : ℂ) r, deriv (F t) c ≠ 0) :
    HasDerivAt (fun t => schwarzianHol (F t) c)
      (iteratedDeriv 3 (fun ζ => deriv (fun t => F t ζ) 0) c) 0 := by
  let V : ℂ → ℂ := fun ζ => deriv (fun t => F t ζ) 0
  have hj := fun j => qcv_param_hasDerivAt_iter j hr hR hζ ht hM
  have i1 : iteratedDeriv 1 (F 0) c = 1 := by rw [h0]; simp
  have i2 : iteratedDeriv 2 (F 0) c = 0 := by rw [h0]; simp [iteratedDeriv_succ']
  have i3 : iteratedDeriv 3 (F 0) c = 0 := by rw [h0]; simp [iteratedDeriv_succ']
  have hq1 : HasDerivAt (fun t => iteratedDeriv 3 (F t) c / iteratedDeriv 1 (F t) c)
      (iteratedDeriv 3 V c) 0 := by
    have h := (hj 3).div (hj 1) (by rw [i1]; exact one_ne_zero)
    refine h.congr_deriv ?_
    rw [i1, i3]
    ring
  have hq2 : HasDerivAt (fun t => iteratedDeriv 2 (F t) c / iteratedDeriv 1 (F t) c)
      (iteratedDeriv 2 V c) 0 := by
    have h := (hj 2).div (hj 1) (by rw [i1]; exact one_ne_zero)
    refine h.congr_deriv ?_
    rw [i1, i2]
    ring
  have hq2' : HasDerivAt (fun t => (iteratedDeriv 2 (F t) c / iteratedDeriv 1 (F t) c) ^ 2)
      0 0 := by
    refine (hq2.pow 2).congr_deriv ?_
    simp [i1, i2]
  have hs := hq1.sub (hq2'.const_mul (3 / 2 : ℂ))
  have he : (fun t => schwarzianHol (F t) c) =ᶠ[𝓝 (0 : ℂ)]
      (fun t => iteratedDeriv 3 (F t) c / iteratedDeriv 1 (F t) c -
        3 / 2 * (iteratedDeriv 2 (F t) c / iteratedDeriv 1 (F t) c) ^ 2) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t htr
    rw [qcv_schwarzianHol_iter ((hζ t htr).analyticAt (ball_mem_nhds _ hR)) (hne t htr),
      iteratedDeriv_one]
  simpa using hs.congr_of_eventuallyEq he

/-- The actual transition's nonlinear Schwarzian differentiates to the third
space derivative of its normalized first variation, at every base point. -/
theorem qcv_planeTransition_schwarzian_variation {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) (ν : LinfStar) {y : ℂ} (hy : y ∈ qcv_planeDisk μ) :
    HasDerivAt (fun t : ℂ => schwarzianHol (qcv_planeTransition (μ + t • ν) μ) y)
      (iteratedDeriv 3 (ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ))) y) 0 := by
  let z := Function.invFun (qcv_planeSolution μ) y
  have hz : z ∈ unitDisc := qcv_planeSolution_inv_mem hμ hy
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  let ρ : ℝ := (1 + ‖z‖) / 2
  have hzρ : ‖z‖ < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hic : ContinuousAt (Function.invFun (qcv_planeSolution μ)) y :=
    (qcv_planeSolution_inv_differentiableOn hμ).continuousOn.continuousAt
      ((qcv_planeDisk_isOpen hμ).mem_nhds hy)
  have hnear : {p : ℂ | p ∈ qcv_planeDisk μ ∧
      ‖Function.invFun (qcv_planeSolution μ) p‖ < ρ} ∈ 𝓝 y := by
    exact inter_mem ((qcv_planeDisk_isOpen hμ).mem_nhds hy)
      (hic ((isOpen_lt continuous_norm continuous_const).mem_nhds hzρ))
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r₀ : ℝ := (1 - ‖μ‖) / (2 * (‖ν‖ + 1))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; have := bc_norm_lt_one hμ; positivity
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : ∀ t ∈ ball (0 : ℂ) r₀, μ + t • ν ∈ LinfStarBall :=
    fun t ht => qcv_affine_curve_mem_ball hμ ν (mem_ball_zero_iff.mp ht)
  have hrsub : closedBall (0 : ℂ) r ⊆ ball 0 r₀ :=
    closedBall_subset_ball (by dsimp [r]; linarith)
  have hsmall : ball (0 : ℂ) r ⊆ ball 0 r₀ := ball_subset_closedBall.trans hrsub
  have hWt : ∀ p : ℂ, DifferentiableOn ℂ
      (fun t => qcv_planeSolution (μ + t • ν) p) (ball (0 : ℂ) r₀) := by
    intro p
    exact (qcv_planeB_differentiableOn p).comp
      ((differentiableOn_const μ).add (differentiableOn_id.smul_const ν)) hball
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    ((hWt 2).continuousOn.mono hrsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hr.le))
  let H : ℂ → ℂ → ℂ := fun t => qcv_planeTransition (μ + t • ν) μ
  have hHζ : ∀ t ∈ ball (0 : ℂ) r, DifferentiableOn ℂ (H t) (ball y R) := by
    intro t ht
    exact (qcv_planeTransition_conformal hμ (hball t (hsmall ht))).1.mono
      (fun p hp => (hRsub hp).1)
  have hHt : ∀ p ∈ ball y R, DifferentiableOn ℂ (fun t => H t p) (ball (0 : ℂ) r) := by
    intro p hp
    exact (hWt (Function.invFun (qcv_planeSolution μ) p)).mono hsmall
  have hM : ∀ t ∈ ball (0 : ℂ) r, ∀ p ∈ ball y R,
      ‖H t p‖ ≤ 4 * B * (ρ / (1 - ρ) ^ 2) := by
    intro t ht p hp
    have hpr := (hRsub hp).2
    have hp1 : ‖Function.invFun (qcv_planeSolution μ) p‖ < 1 := hpr.trans hρ1
    have hb := qcv_W_koebe (bc_norm_lt_one (hball t (hsmall ht))) hp1
    refine hb.trans ?_
    have hm := qcv_mono_koebe (norm_nonneg _) hpr.le hρ1
    have hBt := hB t (ball_subset_closedBall ht)
    calc 4 * ‖qcv_planeSolution (μ + t • ν) 2‖ *
          (‖Function.invFun (qcv_planeSolution μ) p‖ /
            (1 - ‖Function.invFun (qcv_planeSolution μ) p‖) ^ 2)
        ≤ 4 * B * (‖Function.invFun (qcv_planeSolution μ) p‖ /
            (1 - ‖Function.invFun (qcv_planeSolution μ) p‖) ^ 2) := by gcongr
      _ ≤ _ := by gcongr
  have hH0 : H 0 = id := by simpa [H] using qcv_planeTransition_self hμ
  have hne : ∀ t ∈ ball (0 : ℂ) r, deriv (H t) y ≠ 0 := by
    intro t ht
    have hh := qcv_planeTransition_conformal hμ (hball t (hsmall ht))
    exact deriv_ne_zero_of_injOn (qcv_planeDisk_isOpen hμ) hh.1 hh.2.1 hy
  have hs := qcv_param_schwarzian_id hr hR hHζ hHt hM hH0 hne
  have he : (fun p => deriv (fun t => H t p) 0) =
      ahVar (ahT_dot (extB ν) (extB μ) (qcv_planeSolution μ)) := by
    ext p
    exact (qcv_planeTransition_base_hasDerivAt hμ ν p).deriv
  rwa [he] at hs

end QCV
end TakhtajanTeo
