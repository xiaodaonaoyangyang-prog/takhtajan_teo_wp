import TakhtajanTeo.Ch1.QCVariationTransportCriteria

/-!
# Actual Schwarzian covariance on the moving plane-normalized disk

The maps used here are the installed normalized solutions, rather than chosen
welding representatives. Möbius invariance already identifies their Schwarzians
with `bersPhi`. In particular no Model A composition theorem is assumed.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical

noncomputable section

namespace TakhtajanTeo
namespace QCV

open LiZhongQC

def qcv_planeSolution (μ : LinfStar) : ℂ → ℂ := normalizedSolution (extB μ)

def qcv_planeDisk (μ : LinfStar) : Set ℂ := qcv_planeSolution μ '' unitDisc

def qcv_planeTransition (ν μ : LinfStar) : ℂ → ℂ :=
  qcv_planeSolution ν ∘ Function.invFun (qcv_planeSolution μ)

theorem qcv_planeSolution_bijective {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Function.Bijective (qcv_planeSolution μ) := by
  obtain ⟨hN, _, hi, _⟩ := qcv_W_props (bc_norm_lt_one hμ)
  refine ⟨fun x y h => hi (mem_univ _) (mem_univ _) h, ?_⟩
  intro y
  have hy : y ∈ qcv_planeSolution μ '' univ := by
    rw [show qcv_planeSolution μ '' univ = univ from hN.2.1]
    exact mem_univ y
  obtain ⟨x, _, hx⟩ := hy
  exact ⟨x, hx⟩

theorem qcv_planeSolution_conformal {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsConformalOnto (qcv_planeSolution μ) unitDisc (qcv_planeDisk μ) :=
  ⟨(qcv_W_props (bc_norm_lt_one hμ)).2.1, (qcv_planeSolution_bijective hμ).1.injOn, rfl⟩

theorem qcv_planeDisk_isOpen {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    IsOpen (qcv_planeDisk μ) := (qcv_planeSolution_conformal hμ).isOpen isOpen_ball

theorem qcv_planeSolution_inv_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {y : ℂ} (hy : y ∈ qcv_planeDisk μ) :
    Function.invFun (qcv_planeSolution μ) y ∈ unitDisc := by
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [Function.leftInverse_invFun (qcv_planeSolution_bijective hμ).1]

theorem qcv_planeSolution_inv_differentiableOn {μ : LinfStar}
    (hμ : μ ∈ LinfStarBall) :
    DifferentiableOn ℂ (Function.invFun (qcv_planeSolution μ)) (qcv_planeDisk μ) := by
  have hd := ((qcv_planeSolution_conformal hμ).symm isOpen_ball).1
  apply hd.congr
  rintro _ ⟨x, hx, rfl⟩
  rw [Function.leftInverse_invFun (qcv_planeSolution_bijective hμ).1]
  exact ((qcv_planeSolution_bijective hμ).1.injOn.leftInvOn_invFunOn hx).symm

theorem qcv_planeTransition_comp {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ν : LinfStar) :
    qcv_planeTransition ν μ ∘ qcv_planeSolution μ = qcv_planeSolution ν := by
  ext z
  exact congrArg (qcv_planeSolution ν)
    (Function.leftInverse_invFun (qcv_planeSolution_bijective hμ).1 z)

theorem qcv_planeTransition_self {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    qcv_planeTransition μ μ = id := by
  ext y
  exact Function.invFun_eq ((qcv_planeSolution_bijective hμ).2 y)

theorem qcv_planeTransition_conformal {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall) :
    IsConformalOnto (qcv_planeTransition ν μ) (qcv_planeDisk μ) (qcv_planeDisk ν) := by
  have hInv : Function.Injective (Function.invFun (qcv_planeSolution μ)) := by
    intro x y he
    have hh := congrArg (qcv_planeSolution μ) he
    simpa only [Function.invFun_eq ((qcv_planeSolution_bijective hμ).2 _)] using hh
  refine ⟨(qcv_planeSolution_conformal hν).1.comp
    (qcv_planeSolution_inv_differentiableOn hμ) (fun _ hy => qcv_planeSolution_inv_mem hμ hy),
    ((qcv_planeSolution_bijective hν).1.comp hInv).injOn, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, qcv_planeSolution_inv_mem hμ hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨qcv_planeSolution μ x, ⟨x, hx, rfl⟩, ?_⟩
    exact congrFun (qcv_planeTransition_comp hμ ν) x

/-- Genuine finite-base-point Bers covariance, with no welding premise. -/
theorem qcv_bers_covariance {μ ν : LinfStar}
    (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (bersPhi ν) z - AInf.toFun (bersPhi μ) z =
      schwarzianHol (qcv_planeTransition ν μ) (qcv_planeSolution μ z) *
        deriv (qcv_planeSolution μ) z ^ 2 := by
  have hW := qcv_planeSolution_conformal hμ
  have hV := qcv_planeSolution_conformal hν
  have hT := qcv_planeTransition_conformal hμ hν
  have hy : qcv_planeSolution μ z ∈ qcv_planeDisk μ := ⟨z, hz, rfl⟩
  have hWa := hW.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hVa := hV.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hTa := hT.1.analyticAt ((qcv_planeDisk_isOpen hμ).mem_nhds hy)
  have hWd := deriv_ne_zero_of_injOn isOpen_ball hW.1 hW.2.1 hz
  have hTd := deriv_ne_zero_of_injOn (qcv_planeDisk_isOpen hμ) hT.1 hT.2.1 hy
  have hh := eq19_1_chain_rule hWa hWd hTa hTd
  rw [qcv_planeTransition_comp hμ ν, schwarzian_of_analyticAt hVa,
    schwarzian_of_analyticAt hTa, schwarzian_of_analyticAt hWa] at hh
  rw [(bersPhi_spec hν).1 z hz, (bersPhi_spec hμ).1 z hz,
    qcv_schwarzian_fB_eq hν hz, qcv_schwarzian_fB_eq hμ hz]
  exact sub_eq_iff_eq_add.mpr hh

/-- Actual transitions compose on their common normalized-plane chart. -/
theorem qcv_planeTransition_cocycle {ν : LinfStar} (hν : ν ∈ LinfStarBall)
    (κ μ : LinfStar) :
    qcv_planeTransition κ ν ∘ qcv_planeTransition ν μ = qcv_planeTransition κ μ := by
  ext y
  exact congrArg (qcv_planeSolution κ)
    (Function.leftInverse_invFun (qcv_planeSolution_bijective hν).1
      (Function.invFun (qcv_planeSolution μ) y))

end QCV
end TakhtajanTeo
