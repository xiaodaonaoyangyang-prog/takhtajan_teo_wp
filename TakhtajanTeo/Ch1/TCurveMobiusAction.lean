import TakhtajanTeo.Ch1.TCurveLocalRepresentatives

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The Poincare area density is invariant under disk conformal automorphisms. -/
theorem tcg_density_pullback {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) : rho (S z) * ‖deriv S z‖ ^ 2 = rho z := by
  have h := grp25c_density hS hz
  dsimp [rho]
  linear_combination 4 * h

/-- The quadratic differential weight transforms with the inverse Jacobian. -/
theorem tcg_weight_pullback {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv S z‖ ^ 4 * (rho z)⁻¹ = ‖deriv S z‖ ^ 2 * (rho (S z))⁻¹ := by
  have hd : ‖deriv S z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (deriv_ne_zero_of_injOn isOpen_ball hS.1 hS.2.1 hz)
  rw [← tcg_density_pullback hS hz, mul_inv_rev]
  field_simp [hd]

/-- Pullback by a disk conformal automorphism preserves the exact weighted A2 norm. -/
theorem tcg_normA2_pullback {S : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    (φ : ℂ → ℂ) :
    normA2 unitDisc (fun z => φ (S z) * deriv S z ^ 2) = normA2 unitDisc φ := by
  unfold normA2
  congr 1
  rw [lintegral_image_conformal isOpen_ball hS
    (fun w => (‖φ w‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho w)⁻¹)]
  apply setLIntegral_congr_fun isOpen_ball.measurableSet
  intro z hz
  dsimp only
  have he := congrArg ENNReal.ofReal (tcg_weight_pullback hS hz)
  have hrz : 0 < rho z := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hz).ne
  have hrs : 0 < rho (S z) := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp (hS.mapsTo hz)).ne
  simp only [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg (deriv S z)) 4),
    ENNReal.ofReal_mul (pow_nonneg (norm_nonneg (deriv S z)) 2),
    ENNReal.ofReal_pow (norm_nonneg (deriv S z)),
    ENNReal.ofReal_inv_of_pos hrz, ENNReal.ofReal_inv_of_pos hrs, ofReal_norm,
    enorm_eq_nnnorm] at he
  simp only [nnnorm_mul, nnnorm_pow, ENNReal.coe_mul, ENNReal.coe_pow, mul_pow,
    enorm_eq_nnnorm]
  rw [ENNReal.ofReal_inv_of_pos hrz, ENNReal.ofReal_inv_of_pos hrs]
  rw [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, mul_assoc, he]
  ring

/-- Disk conformal pullback preserves the genuine holomorphic A2 space. -/
theorem tcg_A2fun_pullback {S φ : ℂ → ℂ} (hS : IsConformalOnto S unitDisc unitDisc)
    (hφ : φ ∈ A2fun unitDisc) :
    (fun z => φ (S z) * deriv S z ^ 2) ∈ A2fun unitDisc := by
  refine ⟨(hφ.1.comp hS.1 ?_).mul ((hS.1.deriv isOpen_ball).pow 2), ?_⟩
  · intro z hz
    rw [← hS.2.2]
    exact mem_image_of_mem S hz
  · rw [tcg_normA2_pullback hS]
    exact hφ.2

#print axioms tcg_normA2_pullback
#print axioms tcg_A2fun_pullback
end TakhtajanTeo
