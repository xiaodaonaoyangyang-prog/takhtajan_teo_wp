import LiZhongQC.Ch01.S07_GeometricDefinition

/-! The modulus endpoint for the K_n → 1 limit argument in the group chain.
This does not assert convergence or nondegeneracy of a varying family. -/

open Complex Set Filter Topology
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Distortion bounds for every K>1 force the exact K=1 modulus bound. -/
theorem kn6_one_of_forall_gt {f : ℂ → ℂ} {D : Set ℂ}
    (hf : ∀ K : ℝ, 1 < K → IsKQC f D K) : IsKQC f D 1 := by
  have h2 := hf 2 (by norm_num)
  refine ⟨h2.1, le_rfl, h2.2.2.1, ?_⟩
  intro Q hQ
  obtain ⟨Q', himage, -⟩ := h2.2.2.2 Q hQ
  refine ⟨Q', himage, ?_⟩
  have hratio : Q'.modulus / Q.modulus ≤ 1 := by
    apply le_of_forall_gt
    intro K hK
    let R : ℝ := (1 + K) / 2
    have hR : 1 < R := by dsimp [R]; linarith
    obtain ⟨QK, hKimage, hbound⟩ := (hf R hR).2.2.2 Q hQ
    rw [hKimage.unique himage] at hbound
    exact lt_of_le_of_lt ((div_le_iff₀ (modulus_pos Q)).mpr hbound) (by dsimp [R]; linarith)
  simpa only [one_mul] using (div_le_iff₀ (modulus_pos Q)).mp hratio

/-- The endpoint supplied to the varying-map K_n → 1 argument. -/
theorem kn6_conformal_of_forall_gt {f : ℂ → ℂ} {D : Set ℂ}
    (hf : ∀ K : ℝ, 1 < K → IsKQC f D K) : IsConformalOnto f D (f '' D) :=
  thm7_3_one_qc_conformal (kn6_one_of_forall_gt hf)

end TakhtajanTeo
