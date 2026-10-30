import TakhtajanTeo.Ch1.TCurveWeldingContinuity
import TakhtajanTeo.Ch1.TCurveFiberFormula
import TakhtajanTeo.Ch1.TCurveThreePointContinuity
import TakhtajanTeo.Ch1.TCurveSigmaForward

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual output fibre is continuous; the chosen plane extensions are
eliminated by the Mobius comparison and three moving interior evaluations. -/
theorem tcg_mul_snd_continuous_family {X : Type*} [TopologicalSpace X]
    (p q : X → T1 × ExtPlane)
    (hp : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) p)
    (hq : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) q)
    (hp0 : ∀ x, p x ∈ TCurve0) (hq0 : ∀ x, q x ∈ TCurve0) :
    Continuous (fun x => (tcurveMulInv (p x) (q x)).2) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  let k : X → T1 := fun x => mulT (p x).1 (invT (q x).1)
  let l : X → T1 := fun x => (tcurveMulInv (p x) (q x)).1
  have hk : Continuous k := thm_3_8.comp_continuous
    (f := fun x : X => ((p x).1, (q x).1)) (hp.fst.prodMk hq.fst)
    (fun x => ⟨(hp0 x).2, (hq0 x).2⟩)
  have hl : Continuous l := tcg_mul_fst_continuous_family p q hp hq hp0 hq0
  let u : X → extDiscExterior := fun x =>
    ⟨Function.invFun (normalizedWeldingSphere (Quotient.out (q x).1 : LinfStarBall)) (q x).2,
      tcg_parameter_mem (Quotient.out (q x).1 : LinfStarBall).2 (hq0 x).1⟩
  have hu : Continuous u :=
    (tcg_fibre_parameter_continuous.comp_continuous (f := q) hq (fun x => (hq0 x).1)).subtype_mk _
  let a : X → ℂ := fun x => conj (finPart (mobiusExt 0 1 1 0 (u x : ExtPlane)))
  let c : X → ℂ := fun x => (1 - conj (a x)) / (1 - a x)
  let F : X → ℂ → ℂ := fun x z => c x * blaschke (a x) z
  have hF : ∀ x, IsConformalOnto (F x) unitDisc unitDisc := fun x =>
    (isConformalOnto_rot (tcg_sigma_rotation_norm (tcg_sigma_coordinate_mem (u x).2))).comp
      (isConformalOnto_blaschke (tcg_sigma_coordinate_mem (u x).2))
  have hFcont : ∀ z ∈ unitDisc, Continuous (fun x => F x z) := by
    intro z hz
    exact (tcg_sigma_forward_continuous hz).comp (f := u) hu
  choose R K hR hRE hRD hRb using (fun x => tcg_sigma_extension (u x).2)
  choose B hB hZ hval using (fun x => tcg_mul_fibre_with_sigma (hp0 x).1 (hq0 x).1
    (R x) (hR x) (hRE x) (hRD x) (hRb x))
  have hRF : ∀ x, EqOn (⇑(R x)) (F x) unitDisc := fun x =>
    tcg_sigma_forward_formula (u x).2 (R x) (hRD x) (hRb x)
  let PZ : ℂ → X → ℂ := fun z x => fB (Quotient.out (k x) : LinfStarBall) z
  let QZ : ℂ → X → ℂ := fun z x => fB (Quotient.out (l x) : LinfStarBall) (F x z)
  have hPZ : ∀ z ∈ unitDisc, Continuous (PZ z) := fun z hz =>
    tcg_fB_class_continuous_family k (fun _ => z) hk continuous_const (fun _ => hz)
  have hQZ : ∀ z ∈ unitDisc, Continuous (QZ z) := fun z hz =>
    tcg_fB_class_continuous_family l (fun x => F x z) hl (hFcont z hz) (fun x => (hF x).mapsTo hz)
  have hPne : ∀ z₁ z₂, z₁ ∈ unitDisc → z₂ ∈ unitDisc → z₁ ≠ z₂ → ∀ x, PZ z₁ x ≠ PZ z₂ x := by
    intro z₁ z₂ hz₁ hz₂ hne x heq
    exact hne ((fB_holomorphic_injective (Quotient.out (k x) : LinfStarBall).2).2 hz₁ hz₂ heq)
  have hQne : ∀ z₁ z₂, z₁ ∈ unitDisc → z₂ ∈ unitDisc → z₁ ≠ z₂ → ∀ x, QZ z₁ x ≠ QZ z₂ x := by
    intro z₁ z₂ hz₁ hz₂ hne x heq
    have he := (fB_holomorphic_injective (Quotient.out (l x) : LinfStarBall).2).2
      ((hF x).mapsTo hz₁) ((hF x).mapsTo hz₂) heq
    exact hne ((hF x).2.1 hz₁ hz₂ he)
  have hBZ : ∀ z ∈ unitDisc, ∀ x, B x (PZ z x : ExtPlane) = (QZ z x : ExtPlane) := by
    intro z hz x
    have h := hval x z hz
    rw [hRF x hz] at h
    exact h
  let v : X → ExtPlane := fun x =>
    Function.invFun (normalizedWeldingSphere (Quotient.out (p x).1 : LinfStarBall)) (p x).2
  have hv : Continuous v := tcg_fibre_parameter_continuous.comp_continuous
    (f := p) hp (fun x => (hp0 x).1)
  have hvE : ∀ x, v x ∈ extDiscExterior := fun x =>
    tcg_parameter_mem (Quotient.out (p x).1 : LinfStarBall).2 (hp0 x).1
  let w : X → ExtPlane := fun x => normalizedWeldingSphere (Quotient.out (k x) : LinfStarBall) (v x)
  have hw : Continuous w := tcg_welding_class_continuous_family k v hk hv hvE
  have hz₁ : (-1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, norm_div]
  have hz₂ : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hz₃ : (1 / 2 : ℂ) ∈ unitDisc := by norm_num [unitDisc, norm_div]
  have hn12 : (-1 / 2 : ℂ) ≠ 0 := by norm_num
  have hn13 : (-1 / 2 : ℂ) ≠ 1 / 2 := by norm_num
  have hn23 : (0 : ℂ) ≠ 1 / 2 := by norm_num
  have hcont := tcg_mobius_three_continuous B hB
    (PZ (-1 / 2)) (PZ 0) (PZ (1 / 2)) (QZ (-1 / 2)) (QZ 0) (QZ (1 / 2))
    (hPZ _ hz₁) (hPZ _ hz₂) (hPZ _ hz₃) (hQZ _ hz₁) (hQZ _ hz₂) (hQZ _ hz₃)
    (hPne _ _ hz₁ hz₂ hn12) (hPne _ _ hz₁ hz₃ hn13) (hPne _ _ hz₂ hz₃ hn23)
    (hQne _ _ hz₁ hz₂ hn12) (hQne _ _ hz₁ hz₃ hn13) (hQne _ _ hz₂ hz₃ hn23)
    (hBZ _ hz₁) (hBZ _ hz₂) (hBZ _ hz₃) w hw
  have heq : (fun x => (tcurveMulInv (p x) (q x)).2) = (fun x => B x (w x)) := funext hZ
  rw [heq]
  exact hcont

theorem tcg_mul_continuous_family {X : Type*} [TopologicalSpace X]
    (p q : X → T1 × ExtPlane)
    (hp : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) p)
    (hq : @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance) q)
    (hp0 : ∀ x, p x ∈ TCurve0) (hq0 : ∀ x, q x ∈ TCurve0) :
    @Continuous X (T1 × ExtPlane) inferInstance
      (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
      (fun x => tcurveMulInv (p x) (q x)) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  exact (tcg_mul_fst_continuous_family p q hp hq hp0 hq0).prodMk
    (tcg_mul_snd_continuous_family p q hp hq hp0 hq0)

/-- Proposition 3.9 with the original operation, set, and Hilbert-product topology. -/
theorem tcg_prop_3_9 :
    (∀ a ∈ TCurve0, ∀ b ∈ TCurve0, tcurveMulInv a b ∈ TCurve0) ∧
      @ContinuousOn _ _
        (@instTopologicalSpaceProd _ _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
          (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance))
        (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (fun ab : (T1 × ExtPlane) × (T1 × ExtPlane) => tcurveMulInv ab.1 ab.2) (TCurve0 ×ˢ TCurve0) := by
  refine ⟨fun a ha b hb => tcg_mul_mem_curve0 ha hb, ?_⟩
  let _ : TopologicalSpace T1 := hilbertTopology
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact tcg_mul_continuous_family
    (fun x : TCurve0 ×ˢ TCurve0 => x.1.1) (fun x : TCurve0 ×ˢ TCurve0 => x.1.2)
    (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
    (fun x => x.2.1) (fun x => x.2.2)

#print axioms tcg_mul_snd_continuous_family
#print axioms tcg_mul_continuous_family
#print axioms tcg_prop_3_9
/-- **Proposition 3.9** (TT:2086–2120). The Hilbert manifold `𝒯₀(1)` is a topological group:
- `𝒯₀(1)` is closed under `(𝛾₁, 𝛾₂) ↦ 𝛾₁ * 𝛾₂⁻¹`;
- this map is continuous on `𝒯₀(1) × 𝒯₀(1)` (topology of `T(1) × ℂ̄`, Hilbert manifold topology on `T(1)`). -/
theorem prop_3_9 :
    (∀ a ∈ TCurve0, ∀ b ∈ TCurve0, tcurveMulInv a b ∈ TCurve0) ∧
      @ContinuousOn _ _
        (@instTopologicalSpaceProd _ _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
          (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance))
        (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (fun ab : (T1 × ExtPlane) × (T1 × ExtPlane) => tcurveMulInv ab.1 ab.2) (TCurve0 ×ˢ TCurve0) := tcg_prop_3_9

end TakhtajanTeo
