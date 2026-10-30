import TakhtajanTeo.Ch1.TCurveIndependent
import TakhtajanTeo.Ch1.FiberSphereWelding
import TakhtajanTeo.Ch1.GroupTopGroup
import TakhtajanTeo.Appendix.AppACont

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Exterior sphere welding has the same image as the Model B exterior. -/
theorem tcg_welding_image {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    normalizedWeldingSphere μ '' extDiscExterior = wB μ '' extDiscExterior := by
  have he : ∀ p : ExtPlane, p ∈ extDiscExterior ↔ wAS μ p ∈ extDiscExterior := by
    intro p
    rw [fi_extDiscExterior_eq_compl]
    exact not_congr (wAS_closed_iff hμ p)
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Function.invFun (wAS μ) p, ?_, rfl⟩
    rw [he, Function.invFun_eq ((wAS_bijective μ).2 p)]
    exact hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨wAS μ p, (he p).mp hp, ?_⟩
    change wB μ (Function.invFun (wAS μ) (wAS μ p)) = wB μ p
    rw [Function.leftInverse_invFun (wAS_bijective μ).1 p]

/-- The fibre parameter used by the actual definition is always admissible. -/
theorem tcg_parameter_mem {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ExtPlane}
    (hz : z ∈ wB μ '' extDiscExterior) :
    Function.invFun (normalizedWeldingSphere μ) z ∈ extDiscExterior := by
  rw [← tcg_welding_image hμ] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  rwa [Function.leftInverse_invFun (normalizedWeldingSphere_bijective μ).1]

/-- An extension exists for every genuine fibre parameter, including infinity. -/
theorem tcg_extension_exists {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane}
    (hu : u ∈ extDiscExterior) :
    ∃ G : ℂ → ℂ, IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle := by
  obtain ⟨H, ⟨K, hK⟩, hHs, hHa⟩ := wA_hasQCExtension_closed hμ
  induction u using OnePoint.rec with
  | infty =>
    refine ⟨H, ⟨K, hK⟩, hHs, ?_⟩
    intro z hz
    dsimp only
    rw [hHa (mem_closedBall_zero_iff.mpr (show ‖z‖ ≤ 1 from le_of_eq hz)),
      (tce_gamma_circle hμ hz).1]
    rfl
  | coe u =>
    have hu' : u ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hu
    obtain ⟨R, ⟨KR, hKR⟩, hRs, hRa⟩ := sigmaW_closed_extension hu'
    refine ⟨R ∘ H, ⟨K * KR, thm7_1_comp hK hKR (subset_univ _)⟩, ?_, ?_⟩
    · rw [image_comp, hHs, hRs]
    · intro z hz
      dsimp only
      obtain ⟨hg, hn⟩ := tce_gamma_circle hμ hz
      have hne : wA μ z ≠ u := by
        intro he
        have : 1 < ‖u‖ := hu'
        rw [← he, hn] at this
        exact lt_irrefl _ this
      rw [Function.comp_apply, hHa (mem_closedBall_zero_iff.mpr (le_of_eq hz)),
        hRa (mem_closedBall_zero_iff.mpr hn.le), hg, sigmaSphere_coe_eq hu' hne]
      rfl

/-- A valid extension sends the whole exterior sphere to itself. -/
theorem tcg_extension_exterior {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane}
    (hu : u ∈ extDiscExterior) {G : ℂ → ℂ}
    (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    MapsTo (OnePoint.map G) extDiscExterior extDiscExterior := by
  obtain ⟨K, e, hK, he, hE, hC, hS⟩ := tmi_G_data hμ hu hG
  intro p hp
  rw [fi_extDiscExterior_eq_compl] at hp ⊢
  rw [← he] at hC ⊢
  exact fun h => hp ((tmi_map_iff (tmi_cb_iff hC) p).mpr h)

/-- Replace the choice of extension in the definition by any valid extension. -/
theorem tcg_mul_eq_of_extension {a b : T1 × ExtPlane} (ha : a ∈ TCurve) (hb : b ∈ TCurve)
    {G : ℂ → ℂ}
    (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere (Quotient.out b.1 : LinfStarBall)) b.2)
          (gammaMu (Quotient.out b.1 : LinfStarBall) z))) unitCircle) :
    ∃ hl : tcurveLambda (Quotient.out a.1 : LinfStarBall) G ∈ LinfStarBall,
      tcurveMulInv a b = (Phi ⟨_, hl⟩,
        tcurveZ (Quotient.out a.1 : LinfStarBall) G
          (tcurveLambda (Quotient.out a.1 : LinfStarBall) G) a.2) := by
  let μ : LinfStar := (Quotient.out b.1 : LinfStarBall)
  let ν : LinfStar := (Quotient.out a.1 : LinfStarBall)
  let u := Function.invFun (normalizedWeldingSphere μ) b.2
  have hμ : μ ∈ LinfStarBall := (Quotient.out b.1 : LinfStarBall).2
  have hν : ν ∈ LinfStarBall := (Quotient.out a.1 : LinfStarBall).2
  have hu : u ∈ extDiscExterior := tcg_parameter_mem hμ hb
  have hex := tcg_extension_exists hμ hu
  obtain ⟨hl1, hl2, hc, he⟩ := tmi_main hμ hν hu hex.choose_spec hG
  refine ⟨hl2, ?_⟩
  dsimp only [μ, ν, u] at hex hl1
  simp only [tcurveMulInv, dite_eq_left hex, dite_eq_left hl1]
  apply Prod.ext
  · apply Quotient.sound
    intro z hz
    exact congrArg finPart (hc z hz)
  · exact (tcurve_mul_independent hμ hν hu hex.choose_spec hG).2 a.2 ha

/-- The corrected, choice-based operation really lands in the universal curve. -/
theorem tcg_mul_mem_curve {a b : T1 × ExtPlane} (ha : a ∈ TCurve) (hb : b ∈ TCurve) :
    tcurveMulInv a b ∈ TCurve := by
  have hμ := (Quotient.out b.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμ hb
  obtain ⟨G, hG⟩ := tcg_extension_exists hμ hu
  obtain ⟨hl, hres⟩ := tcg_mul_eq_of_extension ha hb hG
  rw [hres]
  change tcurveZ _ G _ a.2 ∈ wB (Quotient.out (Phi ⟨_, hl⟩) : LinfStarBall) '' extDiscExterior
  have hfi := fiber_independent (Quotient.mk_out (s := teichSetoid) ⟨_, hl⟩)
  have himage : tcurveZ (Quotient.out a.1 : LinfStarBall) G
      (tcurveLambda (Quotient.out a.1 : LinfStarBall) G) a.2 ∈
      wB (tcurveLambda (Quotient.out a.1 : LinfStarBall) G) '' extDiscExterior := by
    obtain ⟨p, hp, hpa⟩ := ha
    refine ⟨OnePoint.map G p, tcg_extension_exterior hμ hu hG hp, ?_⟩
    rw [← hpa]
    change wB _ (OnePoint.map G p) = wB _ (OnePoint.map G
      (Function.invFun (wB (Quotient.out a.1 : LinfStarBall))
        (wB (Quotient.out a.1 : LinfStarBall) p)))
    rw [Function.leftInverse_invFun (wB_bijective _).1 p]
  exact hfi.symm ▸ himage

#print axioms tcg_mul_eq_of_extension
#print axioms tcg_mul_mem_curve
end TakhtajanTeo
