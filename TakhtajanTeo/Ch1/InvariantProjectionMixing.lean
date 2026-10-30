import TakhtajanTeo.Ch1.DiagonalMixing
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open Filter Topology Matrix Set Metric
open scoped MatrixGroups InnerProductSpace
noncomputable section
namespace TakhtajanTeo

def fixedVectors {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ρ : G →* H ≃ₗᵢ[ℝ] H) : ClosedSubmodule ℝ H where
  carrier := {x | ∀ g, ρ g x = x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy g; simp [map_add, hx g, hy g]
  smul_mem' := by intro c x hx g; simp [map_smul, hx g]
  isClosed' := by
    simp only [setOf_forall]
    exact isClosed_iInter fun g => isClosed_eq (ρ g).continuous continuous_id

def invariantProjection {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (ρ : G →* H ≃ₗᵢ[ℝ] H) : H →L[ℝ] H :=
  (fixedVectors ρ).toSubmodule.starProjection

theorem inner_fixed_translate {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (ρ : G →* H ≃ₗᵢ[ℝ] H) {z : H}
    (hz : z ∈ fixedVectors ρ) (g : G) (x : H) : inner ℝ z (ρ g x) = inner ℝ z x := by
  calc
    inner ℝ z (ρ g x) = inner ℝ (ρ g z) (ρ g x) := by rw [hz g]
    _ = inner ℝ z x := (ρ g).inner_map_map _ _

/-- A diagonal weak limit is uniquely identified as the actual orthogonal
projection onto invariant vectors. No ergodicity hypothesis is required. -/
theorem diagonal_weak_limit_eq_projection {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    {l : Filter I} [l.NeBot] {s : I → ℝ} (hs : Tendsto s l (𝓝[≠] 0)) {x y : H}
    (hw : ∀ f : H →L[ℝ] ℝ,
      Tendsto (fun i => f (ρ ((mautnerDiag (s i))⁻¹) x)) l (𝓝 (f y))) :
    y = invariantProjection ρ x := by
  have hy : y ∈ fixedVectors ρ :=
    mautner_diagonal_weak_limit_fixed_of_tendsto ρ hρ hs hw
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy
  intro z hz
  have ht := hw (InnerProductSpace.toDual ℝ H z)
  change Tendsto (fun i => inner ℝ z (ρ ((mautnerDiag (s i))⁻¹) x)) l (𝓝 (inner ℝ z y)) at ht
  have he : inner ℝ z y = inner ℝ z x := by
    apply tendsto_nhds_unique ht
    simpa only [inner_fixed_translate ρ hz] using
      (tendsto_const_nhds : Tendsto (fun _ : I => inner ℝ z x) l (𝓝 (inner ℝ z x)))
  rw [inner_sub_left, ← real_inner_comm x z, ← real_inner_comm y z, he, sub_self]

/-- The weak diagonal limit for any continuous isometric real Hilbert representation
is the projection onto its closed invariant subspace. -/
theorem diagonal_rieszWeak_tendsto_projection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2)) (x : H) :
    Tendsto (fun s : ℝ => rieszWeak (ρ ((mautnerDiag s)⁻¹) x))
      (𝓝[≠] 0) (𝓝 (rieszWeak (invariantProjection ρ x))) := by
  let F : ℝ → WeakDual ℝ H := fun s => rieszWeak (ρ ((mautnerDiag s)⁻¹) x)
  have hC := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) ‖x‖
  have hmem : ∀ᶠ s in 𝓝[≠] (0 : ℝ),
      F s ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ H) ‖x‖ := by
    apply Eventually.of_forall
    intro s
    change dist (F s).toStrongDual 0 ≤ ‖x‖
    simp [F, rieszWeak, dist_zero_right]
  apply hC.tendsto_nhds_of_unique_mapClusterPt hmem
  intro q _hq hc
  let L : Filter ℝ := comap F (𝓝 q) ⊓ 𝓝[≠] 0
  haveI : L.NeBot := neBot_inf_comap_iff_map'.mpr hc
  have hF : Tendsto F L (𝓝 q) := tendsto_comap.mono_left inf_le_left
  have hs : Tendsto (fun s : ℝ => s) L (𝓝[≠] 0) := inf_le_right
  have hw : ∀ f : H →L[ℝ] ℝ,
      Tendsto (fun s : ℝ => f (ρ ((mautnerDiag s)⁻¹) x)) L
        (𝓝 (f ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual))) :=
    fun f => rieszWeak_tendsto_dual hF f
  have hy := diagonal_weak_limit_eq_projection ρ hρ hs hw
  apply WeakDual.toStrongDual.injective
  have he := (InnerProductSpace.toDual ℝ H).apply_symm_apply q.toStrongDual
  rw [hy] at he
  exact he.symm

theorem diagonal_matrix_coeff_tendsto_projection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2)) (x y : H) :
    Tendsto (fun s : ℝ => inner ℝ y (ρ ((mautnerDiag s)⁻¹) x))
      (𝓝[≠] 0) (𝓝 (inner ℝ y (invariantProjection ρ x))) := by
  have h := rieszWeak_tendsto_dual (diagonal_rieszWeak_tendsto_projection ρ hρ x)
    (InnerProductSpace.toDual ℝ H y)
  simpa only [rieszWeak, StrongDual.toStrongDual_toWeakDual,
    LinearIsometryEquiv.symm_apply_apply, InnerProductSpace.toDual_apply_apply] using h

end TakhtajanTeo
