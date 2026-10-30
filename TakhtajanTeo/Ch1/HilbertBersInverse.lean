import TakhtajanTeo.Ch1.ComponentTC
import TakhtajanTeo.Ch1.BanachHolomorphic
import TakhtajanTeo.Ch1.Thm31Completed
import TakhtajanTeo.Ch1.HilbertBersDifferentialL2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The actual Hilbert coordinate expression of the Bers embedding. -/
abbrev hib_chart (μ : LinfStarBall) (φ : A2 unitDisc) : A2 unitDisc :=
  toA2 unitDisc (AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ))

/-- External analytic obligation, to be proved from the genuine reproducing/differential
theorems. No theorem here asserts this input without a proof. -/
def hibDerivativeIso : Prop := ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
  ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
    ∃ e : A2 unitDisc ≃L[ℂ] A2 unitDisc,
      fderiv ℂ (hib_chart μ) φ = (e : A2 unitDisc →L[ℂ] A2 unitDisc)

/-- Minimal input from the Hilbert differential lane; other chart points are
handled below by the already-proved holomorphic coordinate changes. -/
def hibOriginDerivativeIso : Prop := ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
  ∃ e : A2 unitDisc ≃L[ℂ] A2 unitDisc,
    fderiv ℂ (hib_chart μ) 0 = (e : A2 unitDisc →L[ℂ] A2 unitDisc)

section Banach
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

-- L1
theorem hib_holomorphic_local_inverse {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U)
    (e : E ≃L[ℂ] F) (he : fderiv ℂ f x = (e : E →L[ℂ] F)) :
    ∃ g : F → E, ContinuousAt g (f x) ∧
      (∀ᶠ y in 𝓝 x, g (f y) = y) ∧ (∀ᶠ z in 𝓝 (f x), f (g z) = z) ∧
      HasStrictFDerivAt g (e.symm : F →L[ℂ] E) (f x) := by
  have hs := bh_hasStrictFDerivAt hU hf hx
  rw [he] at hs
  exact ⟨hs.localInverse f e x, hs.localInverse_continuousAt,
    hs.eventually_left_inverse, hs.eventually_right_inverse, hs.to_localInverse⟩

-- L2
theorem hib_holomorphic_image_open {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hiso : ∀ x ∈ U, ∃ e : E ≃L[ℂ] F, fderiv ℂ f x = (e : E →L[ℂ] F))
    {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) : IsOpen (f '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, he⟩ := hiso x (hVU hx)
  have hs := bh_hasStrictFDerivAt hU hf (hVU hx)
  rw [he] at hs
  rw [← hs.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (hV.mem_nhds hx)
end Banach

-- L3, continuity part
theorem hib_affine_continuous (a : AInf unitDisc) :
    @Continuous (A2 unitDisc) (AInf unitDisc) inferInstance hilbertTopologyA
      (fun x => a + A2toAInf x) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_iSup (fun b : AInf unitDisc =>
    TopologicalSpace.coinduced (fun x : A2 unitDisc => b + A2toAInf x) inferInstance) a

-- L3, open-image part
theorem hib_affine_image_open (a : AInf unitDisc) {U : Set (A2 unitDisc)} (hU : IsOpen U) :
    @IsOpen (AInf unitDisc) hilbertTopologyA ((fun x => a + A2toAInf x) '' U) := by
  have hadd : ∀ x y : A2 unitDisc, A2toAInf (x + y) = A2toAInf x + A2toAInf y :=
    fun x y => map_add A2toAInfCLM x y
  have hsub : ∀ x y : A2 unitDisc, A2toAInf (x - y) = A2toAInf x - A2toAInf y :=
    fun x y => map_sub A2toAInfCLM x y
  unfold hilbertTopologyA
  apply isOpen_iSup_iff.mpr
  intro b
  rw [isOpen_coinduced]
  by_cases hab : ∃ w : A2 unitDisc, b = a + A2toAInf w
  · obtain ⟨w, rfl⟩ := hab
    have he : (fun x : A2 unitDisc => a + A2toAInf w + A2toAInf x) ⁻¹'
        ((fun y => a + A2toAInf y) '' U) = (fun x => w + x) ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y, hy, heq⟩
        dsimp only at heq
        have hJ : A2toAInf y = A2toAInf (w + x) := by
          rw [hadd]
          exact add_left_cancel (by simpa only [add_assoc] using heq)
        change w + x ∈ U
        rwa [← A2toAInf_injective hJ]
      · intro hx
        exact ⟨w + x, hx, by dsimp only; rw [hadd]; abel⟩
    rw [he]
    exact hU.preimage (continuous_const.add continuous_id)
  · have he : (fun x : A2 unitDisc => b + A2toAInf x) ⁻¹'
        ((fun y => a + A2toAInf y) '' U) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨y, -, heq⟩
      apply hab
      refine ⟨y - x, ?_⟩
      rw [hsub]
      dsimp only at heq
      rw [← add_sub_assoc, heq, add_sub_cancel_right]
    rw [he]
    exact isOpen_empty

-- L3
theorem hib_affine_openEmbedding (a : AInf unitDisc) :
    @Topology.IsOpenEmbedding (A2 unitDisc) (AInf unitDisc) inferInstance hilbertTopologyA
      (fun x => a + A2toAInf x) := by
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (hib_affine_continuous a)
    (fun x y h => A2toAInf_injective (add_left_cancel h)) (fun U hU => hib_affine_image_open a hU)

-- L4
theorem hib_chart_strict {μ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    {x : A2 unitDisc} (hx : x ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    HasStrictFDerivAt (hib_chart μ) (fderiv ℂ (hib_chart μ) x) x := by
  exact bh_hasStrictFDerivAt isOpen_ball (ctb_thm_2_13_b12 μ hμ).2 hx

-- L5
theorem hib_chart_value {μ : LinfStarBall} (hμ : (μ : LinfStar) ∈ groupO)
    {x : A2 unitDisc} (hx : x ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    bers (bersChartInv μ (A2toAInf x)) = bersPhi μ + A2toAInf (hib_chart μ x) := by
  rw [hib_chart, ctb_A2toAInf_toA2 ((ctb_thm_2_13_b12 μ hμ).1 x hx)]
  abel

-- L6
theorem hib_bers_chart_image_open (hiso : hibDerivativeIso) {μ : LinfStarBall}
    (hμ : (μ : LinfStar) ∈ groupO) {V : Set (A2 unitDisc)} (hV : IsOpen V)
    (hVB : V ⊆ ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :
    @IsOpen (AInf unitDisc) hilbertTopologyA
      (bers '' ((fun x => bersChartInv μ (A2toAInf x)) '' V)) := by
  have hHV := hib_holomorphic_image_open isOpen_ball (ctb_thm_2_13_b12 μ hμ).2
    (hiso μ hμ) hV hVB
  have he : bers '' ((fun x => bersChartInv μ (A2toAInf x)) '' V) =
      (fun y => bersPhi μ + A2toAInf y) '' (hib_chart μ '' V) := by
    rw [image_image, image_image]
    exact image_congr (fun x hx => hib_chart_value hμ (hVB hx))
  rw [he]
  exact hib_affine_image_open _ hHV

-- L7, open-map part
theorem hib_bers_isOpenMap (hiso : hibDerivativeIso) :
    @IsOpenMap T1 (AInf unitDisc) hilbertTopology hilbertTopologyA bers := by
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  intro O hO
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨p, hp, rfl⟩
  have hpcover : p ∈ ⋃ μ : {μ : LinfStarBall // (μ : LinfStar) ∈ groupO}, hilbertChartDomain μ.1 := by
    rw [hilbertChartDomain_cover]
    exact mem_univ _
  obtain ⟨μ, x, hx, hxp⟩ := mem_iUnion.mp hpcover
  dsimp only at hxp
  let V : Set (A2 unitDisc) := Subtype.val ''
    ((fun y : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf y)) ⁻¹' O)
  have hpre : IsOpen ((fun y : ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) =>
      bersChartInv μ.1 (A2toAInf y)) ⁻¹' O) :=
    isOpen_coinduced.mp (isOpen_iSup_iff.mp (show @IsOpen T1 hilbertTopology O from hO) μ)
  have hV : IsOpen V := isOpen_ball.isOpenMap_subtype_val _ hpre
  have hVB : V ⊆ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) := by
    rintro y ⟨z, -, rfl⟩
    exact z.2
  refine ⟨bers '' ((fun y => bersChartInv μ.1 (A2toAInf y)) '' V), ?_,
    hib_bers_chart_image_open hiso μ.2 hV hVB, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, hy, rfl⟩
  · refine ⟨p, ⟨x, ?_, hxp⟩, rfl⟩
    exact ⟨⟨x, hx⟩, by change bersChartInv μ.1 (A2toAInf x) ∈ O; rwa [hxp], rfl⟩

-- L7
theorem hib_bers_openEmbedding (hiso : hibDerivativeIso) :
    @Topology.IsOpenEmbedding T1 (AInf unitDisc) hilbertTopology hilbertTopologyA bers := by
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    ctb_bers_continuous_hilbert bers_injective (hib_bers_isOpenMap hiso)

-- L8: explicitly conditional until the real derivative isomorphism is supplied.
theorem hib_thm_2_13_of_iso (hiso : hibDerivativeIso) :
    (∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
      (∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        AInf.toFun (bers (bersChartInv μ (A2toAInf φ)) - bersPhi μ) ∈ A2fun unitDisc) ∧
      DifferentiableOn ℂ (hib_chart μ) (ball 0 (Real.sqrt (π / 3))) ∧
      ∀ φ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)),
        Function.Bijective (fderiv ℂ (hib_chart μ) φ)) ∧
      @IsOpen (AInf unitDisc) hilbertTopologyA (range bers) := by
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  refine ⟨fun μ hμ => ⟨(ctb_thm_2_13_b12 μ hμ).1, (ctb_thm_2_13_b12 μ hμ).2,
    fun φ hφ => ?_⟩, (hib_bers_openEmbedding hiso).isOpen_range⟩
  obtain ⟨e, he⟩ := hiso μ hμ φ hφ
  rw [he]
  exact e.bijective

-- L9
theorem hib_cor_3_2_of_iso (hiso : hibDerivativeIso) :
    T01 = {p | AInf.toFun (bers p) ∈ A2fun unitDisc} := by
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  have hpre := thm_3_1.isPreconnected.preimage_of_isOpenMap bers_injective
    (hib_bers_isOpenMap hiso) inter_subset_left
  have h0 : Phi ⟨0, mem_ball_self one_pos⟩ ∈
      bers ⁻¹' (range bers ∩ {a | AInf.toFun a ∈ A2fun unitDisc}) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [c32_bers_origin]
    exact ctc_mem_range.mpr ⟨0, A2toAInf_zero⟩
  ext p
  constructor
  · intro hp
    have h := (ctd_componentT_spec_one_subset (Phi ⟨0, mem_ball_self one_pos⟩)) ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ := h.1
    rw [c32_bers_origin, zero_add] at hx
    exact ctc_mem_range.mpr ⟨x, hx.symm⟩
  · intro hp
    exact hpre.subset_connectedComponent h0 ⟨⟨p, rfl⟩, hp⟩

-- L10: the general affine-slice connectedness obligation is explicit.
theorem hib_component_image_of_preconnected (hiso : hibDerivativeIso) (p : T1)
    (hS : @IsPreconnected (AInf unitDisc) hilbertTopologyA
      ({a | ∃ x : A2 unitDisc, a = bers p + A2toAInf x} ∩ range bers)) :
    bers '' componentT p = {a | ∃ x : A2 unitDisc, a = bers p + A2toAInf x} ∩ range bers := by
  letI : TopologicalSpace T1 := hilbertTopology
  letI : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  apply Subset.antisymm (ctd_componentT_spec_one_subset p)
  rintro a ⟨ha, q, rfl⟩
  have hpre := hS.preimage_of_isOpenMap bers_injective (hib_bers_isOpenMap hiso) inter_subset_right
  have hp : p ∈ bers ⁻¹' ({a | ∃ x : A2 unitDisc, a = bers p + A2toAInf x} ∩ range bers) :=
    ⟨⟨0, by rw [A2toAInf_zero, add_zero]⟩, ⟨p, rfl⟩⟩
  exact ⟨q, hpre.subset_connectedComponent hp ⟨ha, q, rfl⟩, rfl⟩

-- L11
theorem hib_fderiv_bijective_of_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : F → E} {x : E}
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g (f x))
    (hgf : g ∘ f =ᶠ[𝓝 x] id) (hfg : f ∘ g =ᶠ[𝓝 (f x)] id) :
    Function.Bijective (fderiv ℂ f x) := by
  have h0 : g (f x) = x := hgf.self_of_nhds
  have hL : (fderiv ℂ g (f x)).comp (fderiv ℂ f x) = ContinuousLinearMap.id ℂ E := by
    rw [← fderiv_comp x hg hf, hgf.fderiv_eq, fderiv_id]
  have hf' : DifferentiableAt ℂ f (g (f x)) := by rwa [h0]
  have hR := fderiv_comp (f x) hf' hg
  rw [hfg.fderiv_eq, fderiv_id, h0] at hR
  have hleft : Function.LeftInverse (fderiv ℂ g (f x)) (fderiv ℂ f x) := fun v =>
    congrArg (fun L : E →L[ℂ] E => L v) hL
  have hright : Function.RightInverse (fderiv ℂ g (f x)) (fderiv ℂ f x) := fun v =>
    congrArg (fun L : F →L[ℂ] F => L v) hR.symm
  exact ⟨hleft.injective, hright.surjective⟩

-- L12
theorem hib_transition_left (μ ν : LinfStarBall) {x : A2 unitDisc}
    (hx : x ∈ hilbertChart μ '' (hilbertChartDomain ν ∩ hilbertChartDomain μ)) :
    hilbertChart μ (bersChartInv ν (A2toAInf
      (hilbertChart ν (bersChartInv μ (A2toAInf x))))) = x := by
  obtain ⟨hxB, y, hyB, hyx⟩ := (ctc_image_iff ν μ x).mp hx
  dsimp only at hyx
  rw [← hyx, ctc_chart_left_inv ν y hyB, hyx, ctc_chart_left_inv μ x hxB]

-- L13
theorem hib_iso_of_origin (hzero : hibOriginDerivativeIso) : hibDerivativeIso := by
  intro μ hμ x hx
  have hB0 : (0 : A2 unitDisc) ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) :=
    mem_ball_self (by positivity)
  have hchart0 : ∀ m : LinfStarBall, bersChartInv m (A2toAInf 0) = Phi m := by
    intro m
    have hΛ : Lambda (0 : AInf unitDisc) = 0 := by
      simpa using (Lambda_smul 0 (0 : AInf unitDisc))
    rw [A2toAInf_zero, ct_bersChartInv_eq (by simp), bt_rightTrans_phi]
    exact congrArg Phi (Subtype.ext (by
      change beltramiMul (Lambda 0) (m : LinfStar) = (m : LinfStar)
      rw [hΛ, hb_zero_mul m.2]))
  obtain ⟨ν, hν, hrep⟩ := ctb_exists_groupO_rep (bersChartInv μ (A2toAInf x))
  have he0 : bersChartInv ν (A2toAInf 0) = bersChartInv μ (A2toAInf x) :=
    (hchart0 ν).trans hrep.symm
  let T : A2 unitDisc → A2 unitDisc := fun y => hilbertChart μ (bersChartInv ν (A2toAInf y))
  let S : A2 unitDisc → A2 unitDisc := fun y => hilbertChart ν (bersChartInv μ (A2toAInf y))
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [he0, ctc_chart_left_inv μ x hx]
  have hxS : x ∈ hilbertChart μ '' (hilbertChartDomain ν ∩ hilbertChartDomain μ) :=
    (ctc_image_iff ν μ x).mpr ⟨hx, 0, hB0, he0⟩
  have h0T : (0 : A2 unitDisc) ∈ hilbertChart ν '' (hilbertChartDomain μ ∩ hilbertChartDomain ν) :=
    (ctc_image_iff μ ν 0).mpr ⟨hB0, x, hx, he0.symm⟩
  obtain ⟨hTo, hTdOn⟩ := ctc_one_side μ ν hμ hν
  obtain ⟨hSo, hSdOn⟩ := ctc_one_side ν μ hν hμ
  have hTd : DifferentiableAt ℂ T 0 := hTdOn.differentiableAt (hTo.mem_nhds h0T)
  have hSd : DifferentiableAt ℂ S (T 0) := by
    rw [hT0]
    exact hSdOn.differentiableAt (hSo.mem_nhds hxS)
  have hST : S ∘ T =ᶠ[𝓝 (0 : A2 unitDisc)] id := by
    filter_upwards [hTo.mem_nhds h0T] with y hy
    exact hib_transition_left ν μ hy
  have hTS : T ∘ S =ᶠ[𝓝 (T 0)] id := by
    rw [hT0]
    filter_upwards [hSo.mem_nhds hxS] with y hy
    exact hib_transition_left μ ν hy
  have hDT := hib_fderiv_bijective_of_local_inverse hTd hSd hST hTS
  have hβν : bersPhi (ν : LinfStar) = bers (bersChartInv μ (A2toAInf x)) := by
    rw [← bers_Phi ν]
    exact congrArg bers hrep.symm
  have hadd : ∀ a b : A2 unitDisc, A2toAInf (a + b) = A2toAInf a + A2toAInf b :=
    fun a b => map_add A2toAInfCLM a b
  have he : (hib_chart μ ∘ T) =ᶠ[𝓝 (0 : A2 unitDisc)]
      (fun y => hib_chart ν y + hib_chart μ x) := by
    filter_upwards [hTo.mem_nhds h0T] with y hy
    obtain ⟨hyB, z, hzB, hzy⟩ := (ctc_image_iff μ ν y).mp hy
    dsimp only at hzy
    have hTy : T y = z := by
      dsimp only [T]
      rw [← hzy, ctc_chart_left_inv μ z hzB]
    change hib_chart μ (T y) = hib_chart ν y + hib_chart μ x
    apply A2toAInf_injective
    rw [hTy, hadd]
    apply add_left_cancel (a := bersPhi (μ : LinfStar))
    calc _ = bers (bersChartInv μ (A2toAInf z)) := (hib_chart_value hμ hzB).symm
      _ = bers (bersChartInv ν (A2toAInf y)) := congrArg bers hzy
      _ = bersPhi (ν : LinfStar) + A2toAInf (hib_chart ν y) := hib_chart_value hν hyB
      _ = _ := by rw [hβν, hib_chart_value hμ hx]; abel
  have hHμ : DifferentiableAt ℂ (hib_chart μ) (T 0) := by
    rw [hT0]
    exact (ctb_thm_2_13_b12 μ hμ).2.differentiableAt (isOpen_ball.mem_nhds hx)
  have hHν : DifferentiableAt ℂ (hib_chart ν) 0 :=
    (ctb_thm_2_13_b12 ν hν).2.differentiableAt (isOpen_ball.mem_nhds hB0)
  have hchain := fderiv_comp (0 : A2 unitDisc) hHμ hTd
  have hEq : fderiv ℂ (hib_chart μ ∘ T) 0 = fderiv ℂ (hib_chart ν) 0 :=
    he.fderiv_eq.trans (hHν.hasFDerivAt.add_const (hib_chart μ x)).fderiv
  rw [hEq, hT0] at hchain
  obtain ⟨e, heq⟩ := hzero ν hν
  have hcomp : Function.Bijective ((fderiv ℂ (hib_chart μ) x) ∘ (fderiv ℂ T 0)) := by
    change Function.Bijective ((fderiv ℂ (hib_chart μ) x).comp (fderiv ℂ T 0))
    rw [← hchain, heq]
    exact e.bijective
  have hbij := (Function.Bijective.of_comp_iff _ hDT).mp hcomp
  refine ⟨ContinuousLinearEquiv.ofBijective (fderiv ℂ (hib_chart μ) x)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), ?_⟩
  ext v
  rfl

-- L14: consume the real derivative identification; bijectivity remains external.
theorem hib_origin_of_bersOperator_bijective
    (hbij : ∀ μ : LinfStarBall, (μ : LinfStar) ∈ groupO →
      Function.Bijective (hbL2_bersOperator μ)) : hibOriginDerivativeIso := by
  intro μ hμ
  refine ⟨hbL2_equivOfBijective μ (hbij μ hμ), ?_⟩
  calc fderiv ℂ (hib_chart μ) 0 = hbL2_bersOperator μ := hbL2_chart_fderiv_zero μ hμ
    _ = _ := by ext v; rfl

end TakhtajanTeo
