import TakhtajanTeo.Ch1.TCurveSigmaCoordinates

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Actual first-component formula with explicit continuous sphere coordinates,
eliminating the arbitrary plane extension from the formula. -/
theorem tcg_mul_bers_coordinate {p q : T1 × ExtPlane}
    (hp : p ∈ TCurve) (hq : q ∈ TCurve) {z : ℂ} (hz : z ∈ unitDisc) :
    let u := Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2
    let a := conj (finPart (mobiusExt 0 1 1 0 u))
    let c := (1 - conj a) / (1 - a)
    let S : ℂ → ℂ := fun w => blaschke (-a) (conj c * w)
    AInf.toFun (bers (tcurveMulInv p q).1) z =
      AInf.toFun (bers (mulT p.1 (invT q.1))) (S z) * deriv S z ^ 2 := by
  let u := Function.invFun (normalizedWeldingSphere (Quotient.out q.1 : LinfStarBall)) q.2
  have hu : u ∈ extDiscExterior := tcg_parameter_mem (Quotient.out q.1 : LinfStarBall).2 hq
  obtain ⟨R, K, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hu
  have he := tcg_sigma_inverse_formula hu R hRD hRb
  have hg : (⇑R.symm) =ᶠ[𝓝 z]
      (fun w => blaschke (-conj (finPart (mobiusExt 0 1 1 0 u)))
        (conj ((1 - conj (conj (finPart (mobiusExt 0 1 1 0 u)))) /
          (1 - conj (finPart (mobiusExt 0 1 1 0 u)))) * w)) :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun w hw => he hw)
  dsimp only
  rw [tcg_mul_bers_with_sigma hp hq R hR hRE hRD hRb hz, hg.eq_of_nhds, hg.deriv_eq]

/-- The actual A2 coordinate of Bers is continuous on T01 with its Hilbert topology. -/
theorem tcg_A2_bers_continuous :
    @ContinuousOn T1 (A2 unitDisc) hilbertTopology inferInstance
      (fun p => toA2 unitDisc (AInf.toFun (bers p))) T01 := by
  let _ : TopologicalSpace T1 := hilbertTopology
  let _ : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  have hi : Topology.IsOpenEmbedding A2toAInf := by
    simpa only [zero_add] using hib_affine_openEmbedding (0 : AInf unitDisc)
  apply hi.isEmbedding.isInducing.continuousOn_iff.mpr
  have he : EqOn (A2toAInf ∘ fun p => toA2 unitDisc (AInf.toFun (bers p))) bers T01 := by
    intro p hp
    have hpA : AInf.toFun (bers p) ∈ A2fun unitDisc := by
      rw [cor_3_2] at hp
      exact hp
    exact ctb_A2toAInf_toA2 hpA
  exact ctb_bers_continuous_hilbert.continuousOn.congr (fun p hp => he hp)

/-- First-component continuity for arbitrary continuous families of genuine
TCurve0 points. This uses the Hilbert topology, not just the Banach topology. -/
theorem tcg_mul_fst_continuous_family {X : Type*} [TopologicalSpace X]
    (p q : X → T1 × ExtPlane)
    (hp : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) p)
    (hq : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) q)
    (hp0 : ∀ x, p x ∈ TCurve0) (hq0 : ∀ x, q x ∈ TCurve0) :
    @Continuous X T1 inferInstance hilbertTopology (fun x => (tcurveMulInv (p x) (q x)).1) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  let b : X → T1 := fun x => mulT (p x).1 (invT (q x).1)
  have hb : Continuous b := thm_3_8.comp_continuous
    (f := fun x : X => ((p x).1, (q x).1)) (hp.fst.prodMk hq.fst)
    (fun x => ⟨(hp0 x).2, (hq0 x).2⟩)
  have hb0 : ∀ x, b x ∈ T01 := fun x =>
    lemma_3_4.2.1 _ (hp0 x).2 _ (lemma_3_4.2.2 _ (hq0 x).2)
  let f : X → A2 unitDisc := fun x => toA2 unitDisc (AInf.toFun (bers (b x)))
  have hf : Continuous f := tcg_A2_bers_continuous.comp_continuous (f := b) hb hb0
  let u : X → extDiscExterior := fun x =>
    ⟨Function.invFun (normalizedWeldingSphere (Quotient.out (q x).1 : LinfStarBall)) (q x).2,
      tcg_parameter_mem (Quotient.out (q x).1 : LinfStarBall).2 (hq0 x).1⟩
  have hu : Continuous u :=
    (tcg_fibre_parameter_continuous.comp_continuous (f := q) hq (fun x => (hq0 x).1)).subtype_mk _
  let a : X → ℂ := fun x => conj (finPart (mobiusExt 0 1 1 0 (u x : ExtPlane)))
  let c : X → ℂ := fun x => (1 - conj (a x)) / (1 - a x)
  let S : X → ℂ → ℂ := fun x z => blaschke (-a x) (conj (c x) * z)
  let P : X → A2 unitDisc := fun x =>
    toA2 unitDisc (fun z => A2.toFun (f x) (S x z) * deriv (S x) z ^ 2)
  have hP : Continuous P := tcg_sigma_pullback_continuous.comp
    (f := fun x : X => (f x, u x)) (hf.prodMk hu)
  have hPa : ∀ x, IsConformalOnto (S x) unitDisc unitDisc := by
    intro x
    have ha : ‖a x‖ < 1 := tcg_sigma_coordinate_mem (u x).2
    have hc : ‖c x‖ = 1 := tcg_sigma_rotation_norm ha
    exact (isConformalOnto_blaschke (by simpa only [norm_neg] using ha)).comp
      (isConformalOnto_rot (by simpa only [norm_conj] using hc))
  have heq : (fun x => bers (tcurveMulInv (p x) (q x)).1) = A2toAInf ∘ P := by
    funext x
    apply AInf.ext_of_toFun_eqOn (D := unitDisc) (fun z hz => (mem_ball_zero_iff.mp hz).ne)
    intro z hz
    change AInf.toFun (bers (tcurveMulInv (p x) (q x)).1) z = AInf.toFun (A2toAInf (P x)) z
    rw [(A2toAInf_bounded.2 (P x)).2 z hz]
    have hfval := toA2_spec (D := unitDisc) isOpen_ball
      (fun w hw => (mem_ball_zero_iff.mp hw).ne)
      (show AInf.toFun (bers (b x)) ∈ A2fun unitDisc from by
        have h := hb0 x; rw [cor_3_2] at h; exact h)
    have hPval := toA2_spec (D := unitDisc) isOpen_ball
      (fun w hw => (mem_ball_zero_iff.mp hw).ne) (tcg_A2fun_pullback (hPa x) (A2.toFun_mem (f x)))
    change AInf.toFun (bers (tcurveMulInv (p x) (q x)).1) z = A2.toFun (P x) z
    rw [hPval hz]
    dsimp only
    rw [hfval ((hPa x).mapsTo hz)]
    exact tcg_mul_bers_coordinate (hp0 x).1 (hq0 x).1 hz
  let _ : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  apply hbSurj_bers_openEmbedding.isEmbedding.isInducing.continuous_iff.mpr
  change Continuous (fun x => bers (tcurveMulInv (p x) (q x)).1)
  rw [heq]
  have hinc : Continuous A2toAInf := by
    simpa only [zero_add] using hib_affine_continuous (0 : AInf unitDisc)
  exact hinc.comp hP

#print axioms tcg_mul_bers_coordinate
#print axioms tcg_A2_bers_continuous
#print axioms tcg_mul_fst_continuous_family
end TakhtajanTeo
