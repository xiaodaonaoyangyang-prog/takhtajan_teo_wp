import TakhtajanTeo.Ch1.MautnerWeakLimit
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

open Filter Topology Matrix Set Metric
open scoped MatrixGroups InnerProductSpace
noncomputable section
namespace TakhtajanTeo

def rieszWeak {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : H) : WeakDual ℝ H :=
  StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H x)

theorem rieszWeak_tendsto_dual {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {l : Filter I} {v : I → H}
    {q : WeakDual ℝ H} (hv : Tendsto (fun i => rieszWeak (v i)) l (𝓝 q))
    (f : H →L[ℝ] ℝ) :
    Tendsto (fun i => f (v i)) l
      (𝓝 (f ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual))) := by
  let z := (InnerProductSpace.toDual ℝ H).symm f
  have h := ((WeakDual.eval_continuous z).tendsto q).comp hv
  have he (w : H) : rieszWeak w z = f w := by
    change inner ℝ w z = f w
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hq : q z = f ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual) := by
    rw [← WeakDual.toStrongDual_apply, ← InnerProductSpace.toDual_symm_apply,
      real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [Function.comp_def, he, hq] using h

/-- Weak compactness supplies convergence, not merely a conditional assertion
about a weak limit. The orbit stays in the Riesz image of a Hilbert ball. -/
theorem diagonal_rieszWeak_tendsto_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    (hfixed : ∀ y, (∀ g, ρ g y = y) → y = 0) (x : H) :
    Tendsto (fun s : ℝ => rieszWeak (ρ ((mautnerDiag s)⁻¹) x))
      (𝓝[≠] 0) (𝓝 (0 : WeakDual ℝ H)) := by
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
  have hz := mautner_diagonal_weak_limit_zero_of_tendsto ρ hρ hfixed hs hw
  apply WeakDual.toStrongDual.injective
  have he := (InnerProductSpace.toDual ℝ H).apply_symm_apply q.toStrongDual
  rw [hz] at he
  simpa only [map_zero] using he.symm

theorem diagonal_dual_coeff_tendsto_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    (hfixed : ∀ y, (∀ g, ρ g y = y) → y = 0) (x : H) (f : H →L[ℝ] ℝ) :
    Tendsto (fun s : ℝ => f (ρ ((mautnerDiag s)⁻¹) x)) (𝓝[≠] 0) (𝓝 0) := by
  simpa only [map_zero] using
    rieszWeak_tendsto_dual (diagonal_rieszWeak_tendsto_zero ρ hρ hfixed x) f

theorem diagonal_matrix_coeff_tendsto_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    (hfixed : ∀ y, (∀ g, ρ g y = y) → y = 0) (x y : H) :
    Tendsto (fun s : ℝ => inner ℝ y (ρ ((mautnerDiag s)⁻¹) x))
      (𝓝[≠] 0) (𝓝 0) :=
  diagonal_dual_coeff_tendsto_zero ρ hρ hfixed x (InnerProductSpace.toDual ℝ H y)

end TakhtajanTeo
