import TakhtajanTeo.Ch1.TCurvePlaneExtensions
import TakhtajanTeo.Ch1.TCurveSchwarzianTransport

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The first component of the actual group operation has the expected Bers
pullback, for any conformal-disk plane extension of its sphere parameter. -/
theorem tcg_mul_bers_with_sigma {a b : T1 × ExtPlane}
    (ha : a ∈ TCurve) (hb : b ∈ TCurve)
    (R : ℂ ≃ₜ ℂ) {KR : ℝ} (hR : IsKQC (⇑R) univ KR)
    (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart
      (sigmaSphere (Function.invFun (normalizedWeldingSphere (Quotient.out b.1 : LinfStarBall)) b.2)
        (z : ExtPlane))) unitCircle)
    {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (bers (tcurveMulInv a b).1) z =
      AInf.toFun (bers (mulT a.1 (invT b.1))) (R.symm z) * deriv (⇑R.symm) z ^ 2 := by
  let μ : LinfStar := (Quotient.out b.1 : LinfStarBall)
  let ν : LinfStar := (Quotient.out a.1 : LinfStarBall)
  have hμ : μ ∈ LinfStarBall := (Quotient.out b.1 : LinfStarBall).2
  have hν : ν ∈ LinfStarBall := (Quotient.out a.1 : LinfStarBall).2
  obtain ⟨e, K, ξ, he, heE, heC, heb, hm1, hmI, h1, hξae, hξclass⟩ := tcg_normalized_extension hμ
  have hνclass : Phi ⟨ν, hν⟩ = a.1 := Quotient.out_eq a.1
  have hξp : Phi ξ = b.1 := hξclass.trans (Quotient.out_eq b.1)
  have hG : IsQuasiconformal (⇑(e.trans R)) univ ∧ (e.trans R) '' univ = univ ∧
      EqOn (⇑(e.trans R)) (fun w : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere μ) b.2) (gammaMu μ w))) unitCircle := by
    refine ⟨⟨K * KR, ?_⟩, image_univ.trans (e.trans R).surjective.range_eq, ?_⟩
    · change IsKQC ((⇑R) ∘ (⇑e)) univ (K * KR)
      exact thm7_1_comp he hR (subset_univ _)
    · intro w hw
      change R (e w) = _
      rw [heb hw]
      obtain ⟨hγ, hn⟩ := tce_gamma_circle hμ hw
      rw [hRb (show wA μ w ∈ unitCircle from hn)]
      dsimp only
      rw [hγ]
  obtain ⟨hl, hres⟩ := tcg_mul_eq_of_extension ha hb hG
  have hlaw : tcurveLambda ν (e.trans R) =
      tcurveLambda (beltramiMul ν (beltramiInv (ξ : LinfStar))) R := by
    rw [tcg_lambda_comp hν e R he hR heE hRE,
      tcg_lambda_eq_group ξ.2 hν e he heC hm1 hmI h1 hξae]
  have hκ := grp_mul_mem hν (grp_inv_mem ξ.2)
  have hκp : Phi ⟨beltramiMul ν (beltramiInv (ξ : LinfStar)), hκ⟩ = mulT a.1 (invT b.1) := by
    rw [← hνclass, ← hξp, gtp_invT_phi, gtp_mulT_phi]
  rw [hres]
  change AInf.toFun (bers (Phi ⟨tcurveLambda ν (e.trans R), hl⟩)) z = _
  rw [bers_Phi]
  change AInf.toFun (bersPhi (tcurveLambda ν (e.trans R))) z = _
  rw [hlaw]
  rw [tcg_lambda_bers hκ R hR hRE hRD hz]
  have hbκ := bers_Phi (⟨beltramiMul ν (beltramiInv (ξ : LinfStar)), hκ⟩ : LinfStarBall)
  rw [hκp] at hbκ
  rw [hbκ]

/-- The exact weighted norm is that of the base group quotient. -/
theorem tcg_mul_bers_norm {a b : T1 × ExtPlane} (ha : a ∈ TCurve) (hb : b ∈ TCurve) :
    normA2 unitDisc (AInf.toFun (bers (tcurveMulInv a b).1)) =
      normA2 unitDisc (AInf.toFun (bers (mulT a.1 (invT b.1)))) := by
  have hu := tcg_parameter_mem (Quotient.out b.1 : LinfStarBall).2 hb
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hu
  have heq := normA2_congr (D := unitDisc) isOpen_ball.measurableSet
    (fun z hz => tcg_mul_bers_with_sigma ha hb R hR hRE hRD hRb hz)
  exact heq.trans (tcg_normA2_pullback hRD _)

/-- Proposition 3.9, closure clause, for the original operation and original set. -/
theorem tcg_mul_mem_curve0 {a b : T1 × ExtPlane} (ha : a ∈ TCurve0) (hb : b ∈ TCurve0) :
    tcurveMulInv a b ∈ TCurve0 := by
  refine ⟨tcg_mul_mem_curve ha.1 hb.1, ?_⟩
  have hbase := lemma_3_4.2.1 a.1 ha.2 (invT b.1) (lemma_3_4.2.2 b.1 hb.2)
  rw [cor_3_2] at hbase ⊢
  change AInf.toFun (bers (tcurveMulInv a b).1) ∈ A2fun unitDisc
  refine ⟨(bers (tcurveMulInv a b).1).property, ?_⟩
  rw [tcg_mul_bers_norm ha.1 hb.1]
  exact hbase.2

#print axioms tcg_mul_bers_with_sigma
#print axioms tcg_mul_bers_norm
#print axioms tcg_mul_mem_curve0
end TakhtajanTeo
