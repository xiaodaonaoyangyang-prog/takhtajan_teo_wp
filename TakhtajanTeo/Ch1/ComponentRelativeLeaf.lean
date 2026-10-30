import TakhtajanTeo.Ch1.ComponentSliceTransport
import TakhtajanTeo.Ch1.HilbertManifoldCompleted

/-! The actual relative-L2 representative leaf is the Hilbert component at a
groupO base. This does not assume or prove the general affine-slice lifting. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real ComplexConjugate
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem csl_L2leaf_eq_component (μ : LinfStarBall)
    (hμ : (μ : LinfStar) ∈ groupO) :
    cst_L2leaf μ = componentT (Phi μ) := by
  apply Subset.antisymm ?_ (cst_component_subset_L2leaf μ hμ)
  rintro p ⟨ν,hν,hL⟩
  let μi : LinfStarBall := ⟨beltramiInv (μ : LinfStar),grp_inv_mem μ.2⟩
  let ω : LinfStarBall := ⟨beltramiMul (ν : LinfStar) (beltramiInv (μ : LinfStar)),
    grp_mul_mem ν.2 (grp_inv_mem μ.2)⟩
  have hωL : normL2 unitDiscExterior (ω : LinfStar) < ∞ := by
    have h := cst_coeff_right_finite (groupO_inv_mem hμ) μ.2 ν.2 hL
    rw [grp_mul_inv μ.2,sub_zero] at h
    exact h
  have hA := cst_bers_mul_sub_mem_A2
    (show (0 : LinfStar) ∈ LinfStarBall from mem_ball_self one_pos) ω.2 hωL
  rw [grp_mul_zero ω.2,QCV.qs_bersPhi_zero,sub_zero] at hA
  have hωT : Phi ω ∈ T01 := by
    rw [cor_3_2]
    change AInf.toFun (bers (Phi ω)) ∈ A2fun unitDisc
    rwa [bers_Phi]
  have hωp : Phi ω = rightTrans μi p := by
    rw [← hν]
    exact (bt_rightTrans_phi μi ν).symm
  rw [← grp_image_T01 μ]
  refine ⟨Phi ω,hωT,?_⟩
  rw [hωp]
  exact bt_rightTrans_inv_right μ (grp_inv_mem μ.2) p

end TakhtajanTeo
