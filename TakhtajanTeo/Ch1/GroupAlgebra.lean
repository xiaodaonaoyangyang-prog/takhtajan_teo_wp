import TakhtajanTeo.Ch1.S3_TopologicalGroup
import TakhtajanTeo.Ch1.S1_1_Completed
import TakhtajanTeo.Ch1.BeltramiGroup

/-!
# Group-law algebra on `L∞(𝔻*)₁` (helpers for the `𝒪(𝔻*)₁` chain)  [下属2]

* `grp_wAS_zero`, `grp_wAS_injective`: `wAS 0 = id`, and `wAS` determines the Beltrami differential.
* `grp_mul_mem`, `grp_inv_mem`, `grp_wAS_mul`, `grp_wAS_inv_left/right`: `wA_mul` unpacked.
* `grp_mul_assoc`, `grp_mul_inv`, `grp_inv_mul`, `grp_zero_mul`, `grp_mul_zero`, `grp_inv_inv`, `grp_inv_mul_rev`: the group
  axioms on `L∞(𝔻*)₁` as identities of elements of `LinfStar`.
* `grp_groupO_induction`: induction principle for `groupO`.
* `grp_inv_respects`, `grp_invT_invT`: inversion respects `teichSetoid`, and `invT (invT p) = p`.
All helpers are public theorems prefixed `grp_`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem grp_wAS_zero : wAS (0 : LinfStar) = id := by
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      simp [mobiusFn]
  have hnorm : IsNormalizedA 0 id := by
    refine ⟨id, ⟨1, 0, 0, 1, by norm_num, hid.symm⟩, _root_.id,
      ⟨⟨1, isKQC_one_of_conformal isOpen_univ (isConformalOnto_id univ)⟩, image_id _, rfl, rfl, ?_⟩,
      fun z => rfl, rfl, rfl, rfl, rfl⟩
    filter_upwards [extA_ae_norm_le (0 : LinfStar)] with z hz
    have he : extA 0 z = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa only [norm_zero] using hz) (norm_nonneg _))
    rw [td_complexDilatation_id, he]
  exact (wA_unique (by simp [LinfStarBall]) hnorm).symm

theorem grp_wAS_injective {μ ν : LinfStar} (hμ : μ ∈ LinfStarBall) (hν : ν ∈ LinfStarBall)
    (h : wAS μ = wAS ν) : μ = ν := by
  have hw : wA μ = wA ν := by
    funext z
    simp only [wA, h]
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  refine Lp.ext ?_
  filter_upwards [ae_restrict_of_ae (bc_wA_ae hμ), ae_restrict_of_ae (bc_wA_ae hν),
    ae_restrict_mem hE] with z h1 h2 hz
  have e1 := h1.2.2.1
  have e2 := h2.2.2.1
  rw [hw] at e1
  have h3 : extA μ z = extA ν z := e1.symm.trans e2
  have hz' : 1 < ‖z‖ := hz
  unfold extA at h3
  rwa [if_pos hz', if_pos hz'] at h3

theorem grp_mul_mem {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall) :
    beltramiMul a b ∈ LinfStarBall := (wA_mul hb ha).1

theorem grp_inv_mem {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiInv a ∈ LinfStarBall :=
  (wA_mul ha ha).2.2.1

theorem grp_wAS_mul {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall) :
    wAS (beltramiMul a b) = wAS a ∘ wAS b := (wA_mul hb ha).2.1

theorem grp_wAS_inv_left {a : LinfStar} (ha : a ∈ LinfStarBall) :
    wAS a ∘ wAS (beltramiInv a) = id := (wA_mul ha ha).2.2.2.1

theorem grp_wAS_inv_right {a : LinfStar} (ha : a ∈ LinfStarBall) :
    wAS (beltramiInv a) ∘ wAS a = id := (wA_mul ha ha).2.2.2.2

theorem grp_mul_assoc {l a b : LinfStar} (hl : l ∈ LinfStarBall) (ha : a ∈ LinfStarBall)
    (hb : b ∈ LinfStarBall) :
    beltramiMul (beltramiMul l a) b = beltramiMul l (beltramiMul a b) := by
  refine grp_wAS_injective (grp_mul_mem (grp_mul_mem hl ha) hb) (grp_mul_mem hl (grp_mul_mem ha hb)) ?_
  rw [grp_wAS_mul (grp_mul_mem hl ha) hb, grp_wAS_mul hl ha, grp_wAS_mul hl (grp_mul_mem ha hb),
    grp_wAS_mul ha hb]
  rfl

theorem grp_mul_inv {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiMul a (beltramiInv a) = 0 := by
  refine grp_wAS_injective (grp_mul_mem ha (grp_inv_mem ha)) (by simp [LinfStarBall]) ?_
  rw [grp_wAS_mul ha (grp_inv_mem ha), grp_wAS_inv_left ha, grp_wAS_zero]

theorem grp_inv_mul {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiMul (beltramiInv a) a = 0 := by
  refine grp_wAS_injective (grp_mul_mem (grp_inv_mem ha) ha) (by simp [LinfStarBall]) ?_
  rw [grp_wAS_mul (grp_inv_mem ha) ha, grp_wAS_inv_right ha, grp_wAS_zero]

theorem grp_zero_mul {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiMul 0 a = a := by
  refine grp_wAS_injective (grp_mul_mem (by simp [LinfStarBall]) ha) ha ?_
  rw [grp_wAS_mul (by simp [LinfStarBall]) ha, grp_wAS_zero]
  rfl

theorem grp_mul_zero {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiMul a 0 = a := by
  refine grp_wAS_injective (grp_mul_mem ha (by simp [LinfStarBall])) ha ?_
  rw [grp_wAS_mul ha (by simp [LinfStarBall]), grp_wAS_zero]
  rfl

theorem grp_inv_inv {a : LinfStar} (ha : a ∈ LinfStarBall) : beltramiInv (beltramiInv a) = a := by
  refine grp_wAS_injective (grp_inv_mem (grp_inv_mem ha)) ha ?_
  have hbij : Function.Bijective (wAS (beltramiInv a)) := wAS_bijective _
  funext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have h1 := congrFun (grp_wAS_inv_right (grp_inv_mem ha)) y
  have h2 := congrFun (grp_wAS_inv_left ha) y
  simp only [Function.comp_apply, id] at h1 h2
  rw [h1, h2]

theorem grp_inv_mul_rev {a b : LinfStar} (ha : a ∈ LinfStarBall) (hb : b ∈ LinfStarBall) :
    beltramiInv (beltramiMul a b) = beltramiMul (beltramiInv b) (beltramiInv a) := by
  have hab := grp_mul_mem ha hb
  refine grp_wAS_injective (grp_inv_mem hab) (grp_mul_mem (grp_inv_mem hb) (grp_inv_mem ha)) ?_
  have hbij : Function.Bijective (wAS (beltramiMul a b)) := wAS_bijective _
  funext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have h1 := congrFun (grp_wAS_inv_right hab) y
  simp only [Function.comp_apply, id] at h1
  rw [h1, grp_wAS_mul (grp_inv_mem hb) (grp_inv_mem ha)]
  simp only [Function.comp_apply]
  rw [grp_wAS_mul ha hb]
  simp only [Function.comp_apply]
  have h2 := congrFun (grp_wAS_inv_right ha) (wAS b y)
  have h3 := congrFun (grp_wAS_inv_right hb) y
  simp only [Function.comp_apply, id] at h2 h3
  rw [h2, h3]

theorem grp_groupO_induction {P : LinfStar → Prop}
    (hgen : ∀ ν ∈ harmonicBeltrami, ‖ν‖ < delta0 → P ν)
    (hmul : ∀ a b, a ∈ LinfStarBall → b ∈ LinfStarBall → P a → P b → P (beltramiMul a b))
    (hinv : ∀ a, a ∈ LinfStarBall → P a → P (beltramiInv a)) :
    ∀ μ ∈ groupO, μ ∈ LinfStarBall ∧ P μ := by
  intro μ hμ
  have := hμ {x | x ∈ LinfStarBall ∧ P x} (fun x hx => hx.1)
    (fun ν hν hs => ⟨?_, hgen ν hν hs⟩) (fun a ha b hb => ⟨grp_mul_mem ha.1 hb.1, hmul a b ha.1 hb.1 ha.2 hb.2⟩)
    (fun a ha => ⟨grp_inv_mem ha.1, hinv a ha.1 ha.2⟩)
  · exact this
  · have h1 : ‖ν‖ < 1 := hs.trans delta0_bounds.2
    simpa [LinfStarBall] using h1

theorem grp_inv_respects {a b : LinfStarBall} (h : teichSetoid a b) :
    teichSetoid ⟨beltramiInv a, grp_inv_mem a.2⟩ ⟨beltramiInv b, grp_inv_mem b.2⟩ := by
  intro z hz
  have hz1 : ‖z‖ = 1 := hz
  have ha := a.2
  have hb := b.2
  show wA (beltramiInv a) z = wA (beltramiInv b) z
  obtain ⟨hu1, hu2⟩ := bg_circle_val (grp_inv_mem ha) hz1
  have e1 : wAS a (((wA (beltramiInv a) z : ℂ)) : ExtPlane) = (z : ExtPlane) := by
    have := congrFun (grp_wAS_inv_left ha) (z : ExtPlane)
    simp only [Function.comp_apply, id] at this
    rw [hu2] at this
    exact this
  have e2 : wA a (wA (beltramiInv a) z) = z := by
    show finPart (wAS a (((wA (beltramiInv a) z : ℂ)) : ExtPlane)) = z
    rw [e1]
    rfl
  have e3 : wA b (wA (beltramiInv a) z) = z := (h _ hu1).symm.trans e2
  obtain ⟨-, hb2⟩ := bg_circle_val hb hu1
  have e4 : wAS b (((wA (beltramiInv a) z : ℂ)) : ExtPlane) = (z : ExtPlane) := by rw [hb2, e3]
  have e5 := congrFun (grp_wAS_inv_right hb) (((wA (beltramiInv a) z : ℂ)) : ExtPlane)
  simp only [Function.comp_apply, id] at e5
  rw [e4] at e5
  simp only [wA, e5]
  rfl

theorem grp_invT_invT (p : T1) : invT (invT p) = p := by
  set a : LinfStarBall := Quotient.out p with ha
  have h1 : invT p = Phi ⟨beltramiInv a, grp_inv_mem a.2⟩ := by
    unfold invT
    exact dif_pos (grp_inv_mem a.2)
  set b : LinfStarBall := ⟨beltramiInv a, grp_inv_mem a.2⟩ with hbdef
  have h2 : invT (Phi b) = Phi ⟨beltramiInv (Quotient.out (Phi b) : LinfStarBall),
      grp_inv_mem (Quotient.out (Phi b)).2⟩ := by
    unfold invT
    exact dif_pos (grp_inv_mem (Quotient.out (Phi b)).2)
  rw [h1, h2]
  have hq : teichSetoid (Quotient.out (Phi b)) b := Quotient.mk_out (s := teichSetoid) b
  have hr := grp_inv_respects hq
  have hbb : (⟨beltramiInv b, grp_inv_mem b.2⟩ : LinfStarBall) = a :=
    Subtype.ext (grp_inv_inv a.2)
  calc Phi ⟨beltramiInv (Quotient.out (Phi b) : LinfStarBall), grp_inv_mem (Quotient.out (Phi b)).2⟩
      = Phi ⟨beltramiInv b, grp_inv_mem b.2⟩ := Quotient.sound hr
    _ = Phi a := by rw [hbb]
    _ = p := Quotient.out_eq p

end TakhtajanTeo
