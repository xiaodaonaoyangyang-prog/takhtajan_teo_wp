import TakhtajanTeo.Ch1.TCurveFiberTransport
import TakhtajanTeo.Ch1.TCurveBaseContinuity

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual output fibre is a Mobius transform of the class-invariant
exterior welding expression. The transform is characterized on the disk
by the two actual normalized interior maps. -/
theorem tcg_mul_fibre_with_sigma {p q : T1 × ExtPlane}
    (hp : p ∈ TCurve) (hq : q ∈ TCurve)
    (R : ℂ ≃ₜ ℂ) {KR : ℝ} (hR : IsKQC (⇑R) univ KR)
    (hRE : R '' unitDiscExterior = unitDiscExterior)
    (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart
      (sigmaSphere (Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2)
        (z : ExtPlane))) unitCircle) :
    ∃ B : ExtPlane → ExtPlane, IsMobius B ∧
      (tcurveMulInv p q).2 = B
        (normalizedWeldingSphere (Quotient.out (mulT p.1 (invT q.1)) : LinfStarBall)
          (Function.invFun (normalizedWeldingSphere (Quotient.out p.1 : LinfStarBall)) p.2)) ∧
      ∀ z ∈ unitDisc,
        B (fB (Quotient.out (mulT p.1 (invT q.1)) : LinfStarBall) z : ExtPlane) =
          (fB (Quotient.out (tcurveMulInv p q).1 : LinfStarBall) (R z) : ExtPlane) := by
  let μ : LinfStar := (Quotient.out q.1 : LinfStarBall)
  let ν : LinfStar := (Quotient.out p.1 : LinfStarBall)
  have hμ : μ ∈ LinfStarBall := (Quotient.out q.1 : LinfStarBall).2
  have hν : ν ∈ LinfStarBall := (Quotient.out p.1 : LinfStarBall).2
  obtain ⟨e, K, ξ, he, heE, heC, heb, hm1, hmI, h1, hξae, hξclass⟩ := tcg_normalized_extension hμ
  have hνclass : Phi ⟨ν, hν⟩ = p.1 := Quotient.out_eq p.1
  have hξp : Phi ξ = q.1 := hξclass.trans (Quotient.out_eq q.1)
  have hG : IsQuasiconformal (⇑(e.trans R)) univ ∧ (e.trans R) '' univ = univ ∧
      EqOn (⇑(e.trans R)) (fun w : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere μ) q.2) (gammaMu μ w))) unitCircle := by
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
  obtain ⟨hl, hres⟩ := tcg_mul_eq_of_extension hp hq hG
  let κ := beltramiMul ν (beltramiInv (ξ : LinfStar))
  have hκ : κ ∈ LinfStarBall := grp_mul_mem hν (grp_inv_mem ξ.2)
  have hκp : Phi ⟨κ, hκ⟩ = mulT p.1 (invT q.1) := by
    rw [← hνclass, ← hξp, gtp_invT_phi, gtp_mulT_phi]
  have hlaw : tcurveLambda ν (e.trans R) = tcurveLambda κ R := by
    rw [tcg_lambda_comp hν e R he hR heE hRE,
      tcg_lambda_eq_group ξ.2 hν e he heC hm1 hmI h1 hξae]
  have hRs : R '' univ = univ := image_univ.trans R.surjective.range_eq
  have hL := (tmi_lambda_props hκ hR hRs hRE).1
  have hfst : (tcurveMulInv p q).1 = Phi ⟨tcurveLambda κ R, hL⟩ := by
    rw [hres]
    apply congrArg Phi
    exact Subtype.ext hlaw
  have hκrel : teichSetoid (⟨κ, hκ⟩ : LinfStarBall)
      (Quotient.out (mulT p.1 (invT q.1)) : LinfStarBall) :=
    Quotient.exact (hκp.trans (Quotient.out_eq _).symm)
  have hLrel : teichSetoid (⟨tcurveLambda κ R, hL⟩ : LinfStarBall)
      (Quotient.out (tcurveMulInv p q).1 : LinfStarBall) :=
    Quotient.exact (hfst.symm.trans (Quotient.out_eq _).symm)
  obtain ⟨B, hB, hBR⟩ := tcg_transport_mobius hκ R hR hRE hRD
  refine ⟨B, hB, ?_, ?_⟩
  · have hmap : OnePoint.map (e.trans R) = (OnePoint.map R) ∘ (OnePoint.map e) := by
      funext v
      induction v using OnePoint.rec <;> rfl
    have hZ : (tcurveMulInv p q).2 = B (normalizedWeldingSphere κ
        (Function.invFun (normalizedWeldingSphere ν) p.2)) := by
      rw [hres]
      change wB (tcurveLambda ν (e.trans R))
        (OnePoint.map (e.trans R) (Function.invFun (wB ν) p.2)) = _
      rw [hlaw, hmap, Function.comp_apply, hBR]
      exact congrArg B (tcg_normalized_fibre_quotient ξ.2 hν e he heC hm1 hmI h1 hξae hp)
    rw [hZ]
    apply congrArg B
    exact tcg_welding_congr hκrel (tcg_parameter_mem hν hp)
  · intro z hz
    have hRconf : IsConformalOnto (⇑R) unitDisc unitDisc := tcg_inverse_disk_conformal R.symm hRD
    have h := hBR (z : ExtPlane)
    change wB (tcurveLambda κ R) ((R z : ℂ) : ExtPlane) = B (wB κ (z : ExtPlane)) at h
    rw [wB_disc_eq_fB hL (hRconf.mapsTo hz), wB_disc_eq_fB hκ hz,
      (modelA_iff_modelB _ _).mp hLrel (R z) (hRconf.mapsTo hz),
      (modelA_iff_modelB _ _).mp hκrel z hz] at h
    exact h.symm

#print axioms tcg_mul_fibre_with_sigma
end TakhtajanTeo
