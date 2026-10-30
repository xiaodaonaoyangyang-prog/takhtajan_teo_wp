import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open Filter Topology Matrix
open scoped MatrixGroups
noncomputable section
namespace TakhtajanTeo

/-- An isometric action turns a convergent sandwich by stabilizers into a
stabilizer. No compactness, mixing, or lattice asymptotic is assumed here. -/
theorem mautner_sandwich_fixed {G X I : Type*} [Group G] [TopologicalSpace G]
    [MetricSpace X] [MulAction G X] [IsIsometricSMul G X] [ContinuousSMul G X]
    {l : Filter I} [l.NeBot] {u v w : I → G} {g : G} {x : X}
    (hu : ∀ i, u i • x = x) (hw : ∀ i, w i • x = x)
    (hv : Tendsto v l (𝓝 1))
    (hp : Tendsto (fun i => u i * v i * w i) l (𝓝 g)) : g • x = x := by
  have he : (fun i => dist ((u i * v i * w i) • x) x) =
      (fun i => dist (v i • x) x) := by
    funext i
    calc
      dist ((u i * v i * w i) • x) x =
          dist (u i • (v i • x)) (u i • x) := by rw [mul_smul, mul_smul, hw, hu]
      _ = dist (v i • x) x := dist_smul _ _ _
  have h₁ : Tendsto (fun i => dist ((u i * v i * w i) • x) x) l
      (𝓝 (dist (g • x) x)) := (hp.smul tendsto_const_nhds).dist tendsto_const_nhds
  have h₂ : Tendsto (fun i => dist (v i • x) x) l (𝓝 (dist ((1 : G) • x) x)) :=
    (hv.smul tendsto_const_nhds).dist tendsto_const_nhds
  rw [he] at h₁
  have hz : dist (g • x) x = 0 := by
    simpa only [one_smul, dist_self] using tendsto_nhds_unique h₁ h₂
  exact dist_eq_zero.mp hz

def mautnerUpper (t : ℝ) : SL(2, ℝ) :=
  SpecialLinearGroup.transvection zero_ne_one t

def mautnerLower (t : ℝ) : SL(2, ℝ) :=
  SpecialLinearGroup.transvection one_ne_zero t

def mautnerLowerDiag (a : ℝ) (ha : a ≠ 0) (s : ℝ) : SL(2, ℝ) :=
  ⟨!![a, 0; s, a⁻¹], by simp [det_fin_two, ha]⟩

theorem mautner_sandwich_matrix {a s : ℝ} (ha : a ≠ 0) (hs : s ≠ 0) :
    mautnerUpper ((a - 1) / s) * mautnerLower s * mautnerUpper ((a⁻¹ - 1) / s) =
      mautnerLowerDiag a ha s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mautnerUpper, mautnerLower, mautnerLowerDiag, SpecialLinearGroup.transvection_coe,
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [ha, hs] <;> ring

theorem mautner_diagonal_fixed_of_upper {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    {x : X} (hx : ∀ t : ℝ, mautnerUpper t • x = x) {a : ℝ} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2 a ha • x = x := by
  have hlow : Continuous mautnerLower := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) + Matrix.single 1 0 t)
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single, Matrix.one_apply] <;> fun_prop
  have hdiag : Continuous (mautnerLowerDiag a ha) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun s : ℝ => (!![a, 0; s, a⁻¹] : Matrix (Fin 2) (Fin 2) ℝ))
    fun_prop
  have hv : Tendsto mautnerLower (𝓝[≠] (0 : ℝ)) (𝓝 (1 : SL(2, ℝ))) := by
    have hv0 : mautnerLower 0 = 1 := SpecialLinearGroup.transvection_coeff_zero _
    rw [← hv0]
    exact (hlow.tendsto 0).mono_left inf_le_left
  have hd0 : mautnerLowerDiag a ha 0 = SpecialLinearGroup.diag2 a ha := by
    apply Subtype.ext
    simp [mautnerLowerDiag, SpecialLinearGroup.diag2_coe']
  have hp : Tendsto (fun s : ℝ =>
      mautnerUpper ((a - 1) / s) * mautnerLower s * mautnerUpper ((a⁻¹ - 1) / s))
      (𝓝[≠] 0) (𝓝 (SpecialLinearGroup.diag2 a ha)) := by
    have hd := hdiag.continuousAt.tendsto.mono_left (inf_le_left : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    rw [hd0] at hd
    apply hd.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (mautner_sandwich_matrix ha hs).symm
  exact mautner_sandwich_fixed (fun s => hx ((a - 1) / s))
    (fun s => hx ((a⁻¹ - 1) / s)) hv hp

def mautnerDiag (a : ℝ) : SL(2, ℝ) :=
  if ha : a ≠ 0 then SpecialLinearGroup.diag2 a ha else 1

theorem mautner_lower_conjugation {s : ℝ} (hs : s ≠ 0) (b : ℝ) :
    mautnerDiag s * mautnerLower (b * s ^ 2) * (mautnerDiag s)⁻¹ = mautnerLower b := by
  simp only [mautnerDiag, dif_pos hs, SpecialLinearGroup.diag2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mautnerLower, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    field_simp [hs] <;> ring

theorem mautner_lower_fixed_of_upper {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    {x : X} (hx : ∀ t : ℝ, mautnerUpper t • x = x) (b : ℝ) :
    mautnerLower b • x = x := by
  have hd : ∀ s, mautnerDiag s • x = x := by
    intro s
    by_cases hs : s ≠ 0
    · simpa only [mautnerDiag, dif_pos hs] using mautner_diagonal_fixed_of_upper hx hs
    · simp [mautnerDiag, hs]
  have hi : ∀ s, (mautnerDiag s)⁻¹ • x = x := by
    intro s
    calc
      (mautnerDiag s)⁻¹ • x = (mautnerDiag s)⁻¹ • (mautnerDiag s • x) := by rw [hd]
      _ = x := inv_smul_smul _ _
  have hc : Continuous (fun s : ℝ => mautnerLower (b * s ^ 2)) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun s : ℝ =>
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + Matrix.single 1 0 (b * s ^ 2))
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single, Matrix.one_apply] <;>
      first | exact continuous_const | exact continuous_const.mul (continuous_id.pow 2)
  have hv : Tendsto (fun s : ℝ => mautnerLower (b * s ^ 2))
      (𝓝[≠] 0) (𝓝 (1 : SL(2, ℝ))) := by
    have hv0 : mautnerLower (b * (0 : ℝ) ^ 2) = 1 := by
      simp [mautnerLower, SpecialLinearGroup.transvection_coeff_zero]
    rw [← hv0]
    exact (hc.tendsto 0).mono_left inf_le_left
  have hp : Tendsto (fun s : ℝ =>
      mautnerDiag s * mautnerLower (b * s ^ 2) * (mautnerDiag s)⁻¹)
      (𝓝[≠] 0) (𝓝 (mautnerLower b)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (mautner_lower_conjugation hs b).symm
  exact mautner_sandwich_fixed hd hi hv hp

/-- Mautner fixed-point lemma for continuous isometric SL₂(ℝ) actions.
This does not assert mixing or the Patterson lattice-count asymptotic. -/
theorem mautner_fixed_of_upper {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X]
    {x : X} (hx : ∀ t : ℝ, mautnerUpper t • x = x) (g : SL(2, ℝ)) : g • x = x := by
  apply Matrix.SL2.transvection_induction (fun A => A • x = x) _ _ g
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hx c
    · exact mautner_lower_fixed_of_upper hx c
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [mul_smul, hB, hA]

end TakhtajanTeo

