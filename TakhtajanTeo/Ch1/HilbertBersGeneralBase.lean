import TakhtajanTeo.Ch1.HilbertBersIsomorphism

/-! Remove the groupO restriction by equality of the ACTUAL derivative under
a change of representative of the base class. The groupO analytic theorem
is used only at the proved representative supplied by ctb_exists_groupO_rep. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Equivalent base coefficients give the same actual nonlinear Bers maps
on the coefficient ball, hence the same derivative at zero. -/
theorem hbGeneral_derivative_eq {μ ν : LinfStarBall} (he : Phi μ = Phi ν) :
    D0BersR μ = D0BersR ν := by
  have hm : (fun l : LinfStar => bersPhi (beltramiMul l μ)) =ᶠ[𝓝 0]
      (fun l : LinfStar => bersPhi (beltramiMul l ν)) := by
    have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
    filter_upwards [isOpen_ball.mem_nhds h0] with l hl
    have hp : Phi ⟨beltramiMul l μ, bg_mul_mem_ball μ.2 hl⟩ =
        Phi ⟨beltramiMul l ν, bg_mul_mem_ball ν.2 hl⟩ := by
      apply Quotient.sound
      exact bc_beltramiMul_respects (l₁ := ⟨l, hl⟩) (l₂ := ⟨l, hl⟩)
        (fun _ _ => rfl) (Quotient.exact he)
    have hb := congrArg bers hp
    simpa only [bers_Phi] using hb
  exact hm.fderiv_eq

theorem hbGeneral_operator_eq {μ ν : LinfStarBall} (he : Phi μ = Phi ν) :
    hbL2_bersOperator μ = hbL2_bersOperator ν := by
  apply ContinuousLinearMap.ext
  intro φ
  apply A2toAInf_injective
  rw [hbL2_bersOperator_spec, hbL2_bersOperator_spec, hbGeneral_derivative_eq he]

/-- Every actual Hilbert Bers operator is bijective: choose a groupO
representative, prove equality of operators, and use its genuine isomorphism. -/
theorem hbGeneral_bijective (μ : LinfStarBall) :
    Function.Bijective (hbL2_bersOperator μ) := by
  obtain ⟨ν, hν, he⟩ := ctb_exists_groupO_rep (Phi μ)
  rw [hbGeneral_operator_eq he]
  exact hbSurj_bijective_groupO ν hν

/-- The exact unrestricted Theorem 2.3 conclusion, with all analytic inputs proved. -/
theorem hbGeneral_thm_2_3 {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    ∃ C C' : ℝ,
      (∀ ν ∈ harmonicL2 unitDiscExterior, AInf.toFun (D0BersR μ (toLinf ν)) ∈ A2fun unitDisc ∧
        normA2 unitDisc (AInf.toFun (D0BersR μ (toLinf ν))) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν) ∧
      (∀ ν₁ ∈ harmonicL2 unitDiscExterior, ∀ ν₂ ∈ harmonicL2 unitDiscExterior,
        D0BersR μ (toLinf ν₁) = D0BersR μ (toLinf ν₂) → EqOn ν₁ ν₂ unitDiscExterior) ∧
      ∀ φ ∈ A2fun unitDisc, ∃ ν ∈ harmonicL2 unitDiscExterior,
        (∀ z ∈ unitDisc, AInf.toFun (D0BersR μ (toLinf ν)) z = φ z) ∧
        normL2 unitDiscExterior ν ≤ ENNReal.ofReal C' * normA2 unitDisc φ :=
  hbL2_thm_2_3_of_bijective ⟨μ, hμ⟩ (hbGeneral_bijective ⟨μ, hμ⟩)

#print axioms hbGeneral_derivative_eq
#print axioms hbGeneral_operator_eq
#print axioms hbGeneral_bijective
#print axioms hbGeneral_thm_2_3
end TakhtajanTeo
