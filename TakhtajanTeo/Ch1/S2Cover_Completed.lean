import TakhtajanTeo.Ch1.S2Chart_Completed
import TakhtajanTeo.Ch1.BersAtlas
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.BeltramiDerivative
import TakhtajanTeo.Ch1.HilbertBersDifferential

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Right translations are continuous on `T(1)` (quotient topology). -/
theorem hc_rightTrans_continuous (ν : LinfStarBall) : Continuous (rightTrans ν) := by
  have hq : IsQuotientMap (Phi : LinfStarBall → T1) := isQuotientMap_quotient_mk'
  rw [hq.continuous_iff]
  have h1 : Continuous fun l : LinfStarBall => beltramiMul (l : LinfStar) (ν : LinfStar) :=
    (bd_differentiableOn ν.2).continuousOn.comp_continuous continuous_subtype_val (fun l => l.2)
  have h2 : Continuous fun l : LinfStarBall =>
      (⟨beltramiMul (l : LinfStar) (ν : LinfStar), bg_mul_mem_ball ν.2 l.2⟩ : LinfStarBall) :=
    h1.subtype_mk _
  have h3 : (rightTrans ν) ∘ Phi =
      Phi ∘ fun l : LinfStarBall =>
        (⟨beltramiMul (l : LinfStar) (ν : LinfStar), bg_mul_mem_ball ν.2 l.2⟩ : LinfStarBall) :=
    funext fun l => bt_rightTrans_phi ν l
  rw [h3]
  exact hq.continuous.comp h2

/-- The Bers embedding is continuous on `T(1)` (quotient topology, Banach norm on `A∞`). -/
theorem hc_bers_continuous : Continuous bers := by
  have hq : IsQuotientMap (Phi : LinfStarBall → T1) := isQuotientMap_quotient_mk'
  rw [hq.continuous_iff]
  have h3 : bers ∘ Phi = fun l : LinfStarBall => bersPhi (l : LinfStar) := funext fun l => bers_Phi l
  rw [h3]
  exact bersPhi_differentiableOn.continuousOn.comp_continuous continuous_subtype_val (fun l => l.2)

/-- Left cancellation on classes: `[c] = [a * b]` gives `[b] = [a⁻¹ * c]`. -/
theorem hc_left_cancel (a b c : LinfStarBall)
    (h : Phi c = Phi ⟨beltramiMul (a : LinfStar) (b : LinfStar), bg_mul_mem_ball b.2 a.2⟩) :
    Phi b = Phi ⟨beltramiMul (beltramiInv (a : LinfStar)) (c : LinfStar),
      bg_mul_mem_ball c.2 (bc_beltramiInv_mem_ball a.2)⟩ := by
  have hc := Quotient.exact h
  apply Quotient.sound
  intro z hz
  have hz1 : ‖z‖ = 1 := hz
  have hcz := hc z hz
  obtain ⟨-, hc1⟩ := bg_circle_val c.2 hz1
  obtain ⟨-, hab1⟩ := bg_circle_val (bg_mul_mem_ball b.2 a.2) hz1
  have e1 : wAS (c : LinfStar) (z : ExtPlane) =
      wAS (beltramiMul (a : LinfStar) (b : LinfStar)) (z : ExtPlane) := by
    rw [hc1, hab1]
    exact congrArg _ hcz
  have e2 := congrFun (bc_wA_mul b.2 a.2).2.1 (z : ExtPlane)
  have e3 := congrFun (bc_wA_mul c.2 (bc_beltramiInv_mem_ball a.2)).2.1 (z : ExtPlane)
  have e4 := congrFun (bc_wA_mul a.2 a.2).2.2.2.2 (wAS (b : LinfStar) (z : ExtPlane))
  show finPart (wAS (b : LinfStar) (z : ExtPlane)) =
    finPart (wAS (beltramiMul (beltramiInv (a : LinfStar)) (c : LinfStar)) (z : ExtPlane))
  rw [e3]
  simp only [Function.comp_apply] at e2 e4 ⊢
  rw [e1, e2, e4]
  rfl

/-- (TT:1847) The domains `V_μ`, `μ ∈ 𝒪(𝔻*)₁`, cover `T(1)`. -/
theorem s2c_hilbertChartDomain_cover :
    (⋃ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO}, hilbertChartDomain μ.1) = univ := by
  set H : Set T1 := {p | ∃ μ : LinfStarBall, (μ : LinfStar) ∈ groupO ∧ p = Phi μ} with hHdef
  have hz0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
  have hH0 : Phi ⟨0, hz0⟩ ∈ H := ⟨⟨0, hz0⟩, zero_mem_groupO, rfl⟩
  have hHmul : ∀ p ∈ H, ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO → rightTrans μ p ∈ H := by
    rintro p ⟨l, hl, rfl⟩ μ hμ
    exact ⟨⟨beltramiMul (l : LinfStar) μ, bg_mul_mem_ball μ.2 l.2⟩, groupO_mul_mem hl hμ,
      bt_rightTrans_phi μ l⟩
  -- the Bers norm ball of radius `r = 2 δ₀` consists of classes of small harmonic differentials
  set r : ℝ := 2 * delta0 with hr
  have hδ := delta0_bounds
  have hU : ∀ q : T1, ‖bers q‖ < r → ∃ a : LinfStarBall, (a : LinfStar) ∈ groupO ∧ q = Phi a := by
    intro q hq
    have hφ2 : ‖bers q‖ < 2 := by rw [hr] at hq; linarith [hδ.2]
    obtain ⟨h, hφq⟩ := ahlfors_weill hφ2
    refine ⟨⟨Lambda (bers q), h⟩, ?_, ?_⟩
    · exact groupO_mem_of_harmonic (Lambda_mem_harmonic _)
        (lt_of_le_of_lt (Lambda_norm_le _) (by rw [hr] at hq; linarith))
    · exact bers_injective (by rw [hφq])
  have hbers0 : bers (Phi ⟨0, hz0⟩) = 0 := by
    have h0 : Lambda (0 : AInf unitDisc) = 0 := by
      have := Lambda_smul 0 (0 : AInf unitDisc)
      simpa using this
    obtain ⟨h, hφ⟩ := ahlfors_weill (φ := (0 : AInf unitDisc)) (by simp)
    have : (⟨Lambda (0 : AInf unitDisc), h⟩ : LinfStarBall) = ⟨0, hz0⟩ := Subtype.ext h0
    rw [this] at hφ
    exact hφ
  -- the neighbourhood of `Phi ν` in which `R_{ν⁻¹}` has small Bers norm
  have hNopen : ∀ ν : LinfStarBall, IsOpen {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := fun ν =>
    isOpen_lt (continuous_norm.comp (hc_bers_continuous.comp (hc_rightTrans_continuous _)))
      continuous_const
  have hNmem : ∀ ν : LinfStarBall, Phi ν ∈ {q : T1 |
      ‖bers (rightTrans ⟨_, bc_beltramiInv_mem_ball ν.2⟩ q)‖ < r} := by
    intro ν
    have hi := bc_beltramiInv_mem_ball ν.2
    have e1 : Phi ν = rightTrans ν (Phi ⟨0, hz0⟩) := by
      rw [bt_rightTrans_phi]
      exact congrArg Phi (Subtype.ext (hb_zero_mul ν.2).symm)
    show ‖bers (rightTrans ⟨_, hi⟩ (Phi ν))‖ < r
    rw [e1, bt_rightTrans_inv_left ν hi, hbers0, norm_zero]
    rw [hr]; linarith [hδ.1]
  have hopen : IsOpen H := by
    rw [isOpen_iff_forall_mem_open]
    rintro q ⟨ν, hν, rfl⟩
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro q' hq'
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hqa⟩ := hU _ hq'
    have : q' = rightTrans ν (Phi a) := by
      rw [← hqa, bt_rightTrans_inv_right ν hi]
    rw [this]
    exact hHmul _ ⟨a, ha, rfl⟩ ν hν
  have hclosed : IsClosed H := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨ν, rfl⟩ := Quotient.exists_rep p
    change Phi ν ∉ H at hp
    refine ⟨_, ?_, hNopen ν, hNmem ν⟩
    intro y hy hyH
    have hi := bc_beltramiInv_mem_ball ν.2
    obtain ⟨a, ha, hya⟩ := hU _ hy
    obtain ⟨μ', hμ', hyμ⟩ := hyH
    have hy2 : y = Phi ⟨beltramiMul (a : LinfStar) ν, bg_mul_mem_ball ν.2 a.2⟩ := by
      have : y = rightTrans ν (rightTrans ⟨_, hi⟩ y) := (bt_rightTrans_inv_right ν hi y).symm
      rw [this, hya, bt_rightTrans_phi]
    have hcl := hc_left_cancel a ν μ' (by rw [← hyμ, hy2])
    apply hp
    refine ⟨⟨beltramiMul (beltramiInv (a : LinfStar)) (μ' : LinfStar),
      bg_mul_mem_ball μ'.2 (bc_beltramiInv_mem_ball a.2)⟩, ?_, hcl⟩
    exact groupO_mul_mem (groupO_inv_mem ha) hμ'
  have hconn : PreconnectedSpace T1 := by
    have hb : IsPreconnected (LinfStarBall : Set LinfStar) :=
      (convex_ball (0 : LinfStar) 1).isPreconnected
    have hb' : PreconnectedSpace LinfStarBall := isPreconnected_iff_preconnectedSpace.1 hb
    have hr : IsPreconnected (range (Phi : LinfStarBall → T1)) :=
      isPreconnected_range isQuotientMap_quotient_mk'.continuous
    have hrange : range (Phi : LinfStarBall → T1) = univ :=
      Set.range_eq_univ.2 (Quotient.mk_surjective (s := teichSetoid))
    exact ⟨hrange ▸ hr⟩
  have hall : H = univ := by
    have := hconn
    exact (show IsClopen H from ⟨hclosed, hopen⟩).eq_univ ⟨_, hH0⟩
  apply eq_univ_of_forall
  intro p
  have hp : p ∈ H := by rw [hall]; trivial
  obtain ⟨μ, hμ, rfl⟩ := hp
  refine mem_iUnion.mpr ⟨⟨μ, hμ⟩, 0, mem_ball_self (by positivity), ?_⟩
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  show bersChartInv μ (A2toAInf 0) = Phi μ
  rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
  exact congrArg Phi (Subtype.ext (by simp only [hz, hb_zero_mul μ.2]))

/-! ### Original relocated (2026-10-26) -/

/-- (TT:1847) The domains `V_μ`, `μ ∈ 𝒪(𝔻*)₁`, cover `T(1)`. -/
theorem hilbertChartDomain_cover :
    (⋃ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO}, hilbertChartDomain μ.1) = univ :=
  s2c_hilbertChartDomain_cover

end TakhtajanTeo
