import TakhtajanTeo.Ch1.Mautner
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.LinearIsometry

open Filter Topology Matrix
open scoped MatrixGroups
noncomputable section
namespace TakhtajanTeo

/-- Weak limits of translates are fixed by elements whose conjugates contract
to the identity. This statement does not assert existence of a weak limit. -/
theorem mautner_weak_limit_fixed {G H I : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : G →* H ≃ₗᵢ[ℝ] H) (hρ : ∀ x, Continuous (fun g => ρ g x))
    {l : Filter I} [l.NeBot] {a : I → G} {g : G} {x y : H}
    (hw : ∀ f : H →L[ℝ] ℝ, Tendsto (fun i => f (ρ (a i) x)) l (𝓝 (f y)))
    (hc : Tendsto (fun i => (a i)⁻¹ * g * a i) l (𝓝 1)) : ρ g y = y := by
  have he (i : I) : ρ g (ρ (a i) x) = ρ (a i) (ρ ((a i)⁻¹ * g * a i) x) := by
    simp [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
  have hd : Tendsto (fun i => dist (ρ g (ρ (a i) x)) (ρ (a i) x)) l (𝓝 0) := by
    have ht : Tendsto (fun i => ρ ((a i)⁻¹ * g * a i) x) l (𝓝 x) := by
      simpa only [Function.comp_def, map_one, LinearIsometryEquiv.coe_one, id_eq] using
        (hρ x).continuousAt.tendsto.comp hc
    have ht' := ht.dist (tendsto_const_nhds (x := x))
    simpa only [he, LinearIsometryEquiv.dist_map, dist_self] using ht'
  have hz : Tendsto (fun i => ρ g (ρ (a i) x) - ρ (a i) x) l (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hd
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro f
  have ht : Tendsto (fun i => f (ρ g (ρ (a i) x) - ρ (a i) x)) l
      (𝓝 (f (ρ g y - y))) := by
    have hf := hw (f.comp (ρ g).toContinuousLinearEquiv.toContinuousLinearMap)
    change Tendsto (fun i => f (ρ g (ρ (a i) x))) l (𝓝 (f (ρ g y))) at hf
    simpa only [map_sub] using hf.sub (hw f)
  have ht0 : Tendsto (fun i => f (ρ g (ρ (a i) x) - ρ (a i) x)) l (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (f.continuous.tendsto 0).comp hz
  exact tendsto_nhds_unique ht ht0

theorem mautner_upper_conjugation {s : ℝ} (hs : s ≠ 0) (b : ℝ) :
    mautnerDiag s * mautnerUpper b * (mautnerDiag s)⁻¹ = mautnerUpper (b * s ^ 2) := by
  simp only [mautnerDiag, dif_pos hs, SpecialLinearGroup.diag2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mautnerUpper, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [hs] <;> ring

theorem mautner_upper_conjugation_tendsto (b : ℝ) :
    Tendsto (fun s : ℝ => mautnerDiag s * mautnerUpper b * (mautnerDiag s)⁻¹)
      (𝓝[≠] 0) (𝓝 1) := by
  have hct : Continuous (fun s : ℝ => mautnerUpper (b * s ^ 2)) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun s : ℝ =>
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + Matrix.single 0 1 (b * s ^ 2))
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single] <;>
      first | exact continuous_const | exact continuous_const.mul (continuous_id.pow 2)
  have ht : Tendsto (fun s : ℝ => mautnerUpper (b * s ^ 2)) (𝓝[≠] 0) (𝓝 1) := by
    have he : mautnerUpper (b * (0 : ℝ) ^ 2) = 1 := by
      simp [mautnerUpper, SpecialLinearGroup.transvection_coeff_zero]
    rw [← he]
    exact (hct.tendsto 0).mono_left inf_le_left
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (mautner_upper_conjugation hs b).symm

/-- Every weak limit along the diverging inverse diagonal is a group-fixed vector.
Weak compactness and the vanishing of matrix coefficients are separate steps. -/
theorem mautner_diagonal_weak_limit_fixed_of_tendsto {H I : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    {l : Filter I} [l.NeBot] {s : I → ℝ} (hs : Tendsto s l (𝓝[≠] 0)) {x y : H}
    (hw : ∀ f : H →L[ℝ] ℝ,
      Tendsto (fun i => f (ρ ((mautnerDiag (s i))⁻¹) x)) l (𝓝 (f y)))
    (g : SL(2, ℝ)) : ρ g y = y := by
  letI : MulAction SL(2, ℝ) H := {
    smul := fun a z => ρ a z
    one_smul := fun z => by
      change ρ 1 z = z
      simp
    mul_smul := fun a b z => by
      change ρ (a * b) z = ρ a (ρ b z)
      simp [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply] }
  letI : IsIsometricSMul SL(2, ℝ) H := ⟨fun a => (ρ a).isometry⟩
  letI : ContinuousSMul SL(2, ℝ) H := ⟨hρ⟩
  have hu : ∀ t, mautnerUpper t • y = y := by
    intro t
    apply mautner_weak_limit_fixed ρ (fun z => hρ.comp (continuous_id.prodMk continuous_const)) hw
    simpa only [Function.comp_def, inv_inv] using (mautner_upper_conjugation_tendsto t).comp hs
  exact mautner_fixed_of_upper hu g

theorem mautner_diagonal_weak_limit_zero_of_tendsto {H I : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : SL(2, ℝ) →* H ≃ₗᵢ[ℝ] H)
    (hρ : Continuous (fun p : SL(2, ℝ) × H => ρ p.1 p.2))
    (hfixed : ∀ y, (∀ g, ρ g y = y) → y = 0)
    {l : Filter I} [l.NeBot] {s : I → ℝ} (hs : Tendsto s l (𝓝[≠] 0)) {x y : H}
    (hw : ∀ f : H →L[ℝ] ℝ,
      Tendsto (fun i => f (ρ ((mautnerDiag (s i))⁻¹) x)) l (𝓝 (f y))) : y = 0 :=
  hfixed y (mautner_diagonal_weak_limit_fixed_of_tendsto ρ hρ hs hw)

end TakhtajanTeo
