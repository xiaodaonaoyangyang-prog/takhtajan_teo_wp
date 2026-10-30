import TakhtajanTeo.Ch2.S4_WPPotential
import TakhtajanTeo.Ch1.ComponentTBasics
import TakhtajanTeo.Ch1.GroupAlgebra
import TakhtajanTeo.Ch1.GroupChain1
import TakhtajanTeo.Ch1.S1_1_Completed

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `[μ] * [μ]⁻¹ = 0` in `T(1)`, on representatives: `[μ̂ * (μ⁻¹)^] = 0`. -/
theorem s4c_mul_invT_out (b : T1)
    (h : beltramiMul (Quotient.out b : LinfStarBall) (Quotient.out (invT b) : LinfStarBall) ∈ LinfStarBall) :
    Phi ⟨_, h⟩ = originT := by
  have hb := (Quotient.out b).2
  let m : LinfStarBall := ⟨beltramiInv (Quotient.out b : LinfStarBall), grp_inv_mem hb⟩
  have hinv : invT b = Phi m := by
    unfold invT
    exact dite_eq_left (grp_inv_mem hb)
  have hs : teichSetoid (Quotient.out (invT b)) m := by
    rw [hinv]
    exact Quotient.mk_out m
  apply Quotient.sound
  show ∀ z ∈ unitCircle, wA (beltramiMul (Quotient.out b : LinfStarBall) (Quotient.out (invT b) : LinfStarBall)) z =
    wA (0 : LinfStar) z
  intro z hz
  rw [beltramiMul_respects (teichSetoid.iseqv.refl (Quotient.out b)) hs z hz]
  show wA (beltramiMul (Quotient.out b : LinfStarBall) (beltramiInv (Quotient.out b : LinfStarBall))) z = wA 0 z
  rw [grp_mul_inv hb]

/-- (TT:5398) The components of `T(1)`:
- each `T_α(1)` is the right translate `R_{μ_α} T₀(1)` of `T₀(1)`, so `[ν * μ_α⁻¹] ∈ T₀(1)` for `[ν] ∈ T_α(1)`;
- the base point lies in the component and depends only on it.
Proved here as `s4c_componentBase_spec`; statement identical to `componentBase_spec`. -/
theorem s4c_componentBase_spec (p : T1) :
    componentBase p ∈ componentT p ∧ (∀ q ∈ componentT p, componentBase q = componentBase p) ∧
      mulT p (invT (componentBase p)) ∈ T01 := by
  have hmem : componentBase p ∈ componentT p := by
    unfold componentBase
    split_ifs with h
    · rw [h]
      exact TakhtajanTeo.lemma_3_4.1
    · exact Classical.epsilon_spec ⟨p, @mem_connectedComponent _ hilbertTopology p⟩
  refine ⟨hmem, ?_, ?_⟩
  · intro q hq
    have hc : componentT q = componentT p := (@connectedComponent_eq _ hilbertTopology _ _ hq).symm
    unfold componentBase
    rw [hc]
  · set b := componentBase p with hbdef
    have hcb : componentT p = componentT b := @connectedComponent_eq _ hilbertTopology _ _ hmem
    obtain ⟨h, himg⟩ := ctb_componentT_spec_two b (Quotient.out (invT b))
    have hp : p ∈ componentT b := hcb ▸ @mem_connectedComponent _ hilbertTopology p
    have hr : rightTrans (Quotient.out (invT b)) p ∈ componentT (Phi ⟨_, h⟩) := himg ▸ mem_image_of_mem _ hp
    rw [s4c_mul_invT_out b h] at hr
    exact hr

/-- (TT:5398) The components of `T(1)`:
- each `T_α(1)` is the right translate `R_{μ_α} T₀(1)` of `T₀(1)`, so `[ν * μ_α⁻¹] ∈ T₀(1)` for `[ν] ∈ T_α(1)`;
- the base point lies in the component and depends only on it. -/
theorem componentBase_spec (p : T1) :
    componentBase p ∈ componentT p ∧ (∀ q ∈ componentT p, componentBase q = componentBase p) ∧
      mulT p (invT (componentBase p)) ∈ T01 :=
  s4c_componentBase_spec p

end Ch2

end TakhtajanTeo
