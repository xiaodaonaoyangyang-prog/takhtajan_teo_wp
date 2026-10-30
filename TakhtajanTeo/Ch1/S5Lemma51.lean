import TakhtajanTeo.Ch1.S5FiberParameterRegularity
import TakhtajanTeo.Ch1.TCurveLocalRepresentatives

/-! Descent of the actual analytic fibre metric and the complete original Lemma 5.1. -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

-- L1
theorem s5cf_invFunOn_congr {α β : Type*} [Nonempty α] {f g : α → β} {s : Set α}
    (he : EqOn f g s) (hi : InjOn f s) : Function.invFunOn f s = Function.invFunOn g s := by
  funext b
  by_cases hf : ∃ a ∈ s, f a = b
  · have hg : ∃ a ∈ s, g a = b := by
      obtain ⟨a, ha, hab⟩ := hf
      exact ⟨a, ha, (he ha).symm.trans hab⟩
    have hfp := Function.invFunOn_pos hf
    have hgp := Function.invFunOn_pos hg
    apply hi hfp.1 hgp.1
    exact hfp.2.trans ((he hgp.1).trans hgp.2).symm
  · have hg : ¬ ∃ a ∈ s, g a = b := by
      rintro ⟨a, ha, hab⟩
      exact hf ⟨a, ha, (he ha).trans hab⟩
    simp only [Function.invFunOn, dif_neg hf, dif_neg hg]

-- L2
theorem s5cf_gMu_congr {μ ν : LinfStarBall} (h : teichSetoid μ ν) :
    EqOn (gMu μ) (gMu ν) unitDiscExterior := by
  intro w hw
  have hE : (w : ExtPlane) ∈ extDiscExterior := Or.inl ⟨w, hw, rfl⟩
  have hh := tcg_welding_congr h hE
  change wB μ (Function.invFun (wAS μ) (w : ExtPlane)) =
    wB ν (Function.invFun (wAS ν) (w : ExtPlane)) at hh
  rw [← gMu_sphere_factorization μ.2 hw, ← gMu_sphere_factorization ν.2 hw] at hh
  exact OnePoint.coe_injective hh

-- L3
theorem s5cf_uniformizer_congr {μ ν : LinfStarBall} (h : teichSetoid μ ν) :
    fiberUniformizer μ = fiberUniformizer ν := by
  have hg : IsUnivalentAtInfty (gMu μ) := (gMu_isWelding μ.2).2.2.2.2.2.2
  have hi := s5cf_invFunOn_congr (s5cf_gMu_congr h) hg.2.1
  funext ζ
  simp only [fiberUniformizer, hi]

-- L4
theorem s5cf_metric_coord_of_representative (μ : LinfStarBall) {ζ : ℂ}
    (hx : (bers (Phi μ), ζ) ∈ tcCoord '' TCurve) :
    logNormSq (tcCoordInv (bers (Phi μ), ζ)) =
      Real.log (4 * ‖deriv (fiberUniformizer μ) ζ‖ ^ 2 / (1 - ‖fiberUniformizer μ ζ‖ ^ 2) ^ 2) := by
  rw [s5fg_coordInv_fiber hx]
  have hclass : teichSetoid μ (Quotient.out (Phi μ)) := by
    apply Quotient.exact
    exact (Quotient.out_eq (Phi μ)).symm
  have hf := s5cf_uniformizer_congr hclass
  have hm := congrArg (fun G : ℂ → ℂ => Real.log (4 * ‖deriv G ζ‖ ^ 2 / (1 - ‖G ζ‖ ^ 2) ^ 2)) hf.symm
  simpa [logNormSq, finPart, tcc_inversion_invol] using hm

-- L5
theorem s5cf_logNormSq_coord_analytic :
    AnalyticOnNhd ℝ (fun x => logNormSq (tcCoordInv x)) (tcCoord '' TCurve) := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨s, U, hU, hp, hs, hs0, hsec⟩ := s5cf_section_analytic q.1
  have hM := s5cf_metric_parameter_analytic (Quotient.out q.1 : LinfStarBall).2
    (s5fg_actual_fiber_condition hq)
  have hS : AnalyticAt ℝ s (bers q.1) := (hs _ hp).restrictScalars
  have hmap : AnalyticAt ℝ (fun x : AInf unitDisc × ℂ => (s x.1, x.2)) (tcCoord q) :=
    (hS.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd
  apply (hM.comp_of_eq hmap (by simp only [tcCoord, hs0])).congr
  filter_upwards [tcCoord_chart.2.mem_nhds (show tcCoord q ∈ tcCoord '' TCurve from ⟨q, hq, rfl⟩),
    (continuous_fst.tendsto (tcCoord q)).eventually (hU.mem_nhds hp)] with x hx hxU
  obtain ⟨h, hB⟩ := hsec x.1 hxU
  have hcoord : (bers (Phi ⟨s x.1, h⟩), x.2) ∈ tcCoord '' TCurve := by
    rw [hB]
    exact hx
  have he := s5cf_metric_coord_of_representative ⟨s x.1, h⟩ hcoord
  rw [hB] at he
  exact he.symm

-- L6: exact original statement.
theorem s5cf_lemma_5_1 :
    AnalyticOnNhd ℝ (fun x => potentialK (tcCoordInv x)) (tcCoord '' TCurve) ∧
      ∀ (p : T1) (w : ℂ), w ∈ unitDiscExterior →
        potentialK (p, (gMu (Quotient.out p : LinfStarBall) w : ExtPlane)) =
          Real.log ‖derivAtInfty (fun z => lambdaW (-1 / gMu (Quotient.out p : LinfStarBall) w)
            (gMu (Quotient.out p : LinfStarBall) (Function.invFun (sigmaW w) z)))‖ := by
  refine ⟨?_, s5wr_lemma_5_1_formula⟩
  intro x hx
  change AnalyticAt ℝ (fun x => logNormSq (tcCoordInv x) / 2 - Real.log 2) x
  exact ((s5cf_logNormSq_coord_analytic x hx).div analyticAt_const (by norm_num)).sub analyticAt_const

end TakhtajanTeo

