import TakhtajanTeo.Ch1.FiberSphereWelding
import TakhtajanTeo.Ch1.CircleQuasisymmetry
import DouadyEarle.Extension

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem circle_increasingLift_continuous {φ : Circle → Circle}
    (hs : Function.Surjective φ) (h : HasIncreasingLift φ) :
    ∃ u : ℝ → ℝ, Continuous u ∧ StrictMono u ∧
      (∀ t, u (t + 2 * π) = u t + 2 * π) ∧
      ∀ t : ℝ, (φ (Circle.exp t) : ℂ) = exp (u t * I) := by
  obtain ⟨u, hm, hp, he⟩ := h
  have hu : Function.Surjective u := by
    intro y
    obtain ⟨ζ, hζ⟩ := hs (Circle.exp y)
    obtain ⟨t, rfl⟩ := Circle.exp_surjective ζ
    have hex : exp (u t * I) = exp (y * I) := by rw [← he, hζ, Circle.coe_exp]
    obtain ⟨n, hn⟩ := CircleLift.sub_eq_int_mul_two_pi hex
    refine ⟨t + ((-n : ℤ) : ℝ) * (2 * π), ?_⟩
    have hperiod : ∀ t, u (t + 2 * π) = u t + (1 : ℤ) * (2 * π) := by simpa using hp
    rw [CircleLift.lift_per_int hperiod]
    push_cast
    linarith
  exact ⟨u, hm.monotone.continuous_of_surjective hu, hm, hp, he⟩

theorem wA_circle_sensePreserving {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    Pommerenke1992.IsSensePreservingCircleHomeo (wA μ) := by
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖wA μ z‖ = 1 := by
    intro z hz
    obtain ⟨u, hu, he⟩ := wAS_maps_circle hμ hz
    have ha : wA μ z = u := congrArg finPart he
    rwa [ha]
  let φ : Circle → Circle := fun ζ => ⟨wA μ ζ, mem_sphere_zero_iff_norm.mpr (hnorm ζ (Circle.norm_coe ζ))⟩
  have hcoe : ∀ ζ : Circle, ((φ ζ : Circle) : ℂ) = wA μ ζ := fun _ => rfl
  have hAS : ∀ ζ : Circle, (wA μ ζ : ExtPlane) = wAS μ (ζ : ℂ) := by
    intro ζ
    obtain ⟨u, -, he⟩ := wAS_maps_circle hμ (Circle.norm_coe ζ)
    unfold wA
    rw [he]
    rfl
  have hb : Function.Bijective φ := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply OnePoint.coe_injective
      apply (wAS_bijective μ).1
      rw [← hAS, ← hAS]
      exact congrArg (fun ζ : Circle => ((ζ : ℂ) : ExtPlane)) he
    · intro ζ
      have he : ((ζ : ℂ) : ExtPlane) ∈ wAS μ '' toExt unitCircle := by
        rw [(wA_mapsTo hμ).2.2]
        exact ⟨ζ, Circle.norm_coe ζ, rfl⟩
      obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := he
      refine ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, ?_⟩
      apply Subtype.ext
      exact congrArg finPart he
  have hc : Continuous φ := by
    obtain ⟨H, ⟨K, hK⟩, hHs, hHa⟩ := wA_hasQCExtension_closed hμ
    obtain ⟨e, he⟩ := t1_homeomorph hK hHs
    have hcont : Continuous (fun ζ : Circle => H (ζ : ℂ)) := by rw [← he]; fun_prop
    apply Continuous.subtype_mk
    apply hcont.congr
    intro ζ
    exact hHa (mem_closedBall_zero_iff.mpr (Circle.norm_coe ζ).le)
  obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hp1⟩ := wA_spec hμ
  have hfix1 : wA μ 1 = 1 := congrArg finPart hp1
  have hfixm : wA μ (-1) = -1 := congrArg finPart hm1
  have hfixI : wA μ (-I) = -I := congrArg finPart hmI
  let ψ : Circle → Circle := fun ζ => (φ ζ⁻¹)⁻¹
  have hψb : Function.Bijective ψ := inv_involutive.bijective.comp (hb.comp inv_involutive.bijective)
  have hψc : Continuous ψ := (hc.comp continuous_inv).inv
  have hψ1 : ψ 1 = 1 := by
    apply Subtype.ext
    simp only [ψ, coe_circle_inv, hcoe]
    simp [hfix1]
  have hψI : ψ (Circle.exp (π / 2)) = Circle.exp (π / 2) := by
    apply Subtype.ext
    simp only [ψ, coe_circle_inv, hcoe]
    simp [Circle.coe_exp, Complex.exp_mul_I, hfixI]
  have hψm : ψ (Circle.exp π) = Circle.exp π := by
    apply Subtype.ext
    simp only [ψ, coe_circle_inv, hcoe]
    simp [hfixm]
  obtain ⟨u, hu, hm, hp, he⟩ := circle_increasingLift_continuous hψb.2
    (CircleLift.hasIncreasingLift_of_fixes ψ hψb hψc hψ1 hψI hψm)
  refine ⟨fun t => -u (-t), (hu.comp continuous_neg).neg, ?_, ?_, ?_⟩
  · intro x y hxy
    exact neg_lt_neg (hm (neg_lt_neg hxy))
  · intro t
    have hh := hp (-(t + 2 * π))
    have heq : -(t + 2 * π) + 2 * π = -t := by ring
    rw [heq] at hh
    linarith
  · intro t
    have hpoint : (Circle.exp (-t))⁻¹ = Circle.exp t := by
      rw [Circle.exp_neg, inv_inv]
    have hh := he (-t)
    change (((φ ((Circle.exp (-t))⁻¹))⁻¹ : Circle) : ℂ) = exp (u (-t) * I) at hh
    rw [hpoint, Circle.coe_inv] at hh
    have hinv := congrArg (fun z : ℂ => z⁻¹) hh
    simpa only [inv_inv, hcoe, Circle.coe_exp, ← Complex.exp_neg,
      Complex.ofReal_neg, neg_mul] using hinv

theorem sigmaW_circle_sensePreserving {w : ℂ} (hw : w ∈ unitDiscExterior) :
    Pommerenke1992.IsSensePreservingCircleHomeo (sigmaW w) := by
  obtain ⟨c, a, hc, ha, he⟩ := sigmaW_blaschke_closed hw
  let g : ℂ → ℂ := fun z => c * blaschke a z
  have hg : IsDiskAutPlus g := ⟨c, a, hc, ha, fun z => rfl⟩
  let φ := diskAutToCircle g (Or.inl hg)
  obtain ⟨u, hu, hm, hp, hφ⟩ := circle_increasingLift_continuous
    (bijective_diskAutToCircle g hg (Or.inl hg)).2
    (CircleLift.hasIncreasingLift_of_isDiskAutPlus hg φ (fun _ => rfl))
  refine ⟨u, hu, hm, hp, fun t => ?_⟩
  rw [he (mem_closedBall_zero_iff.mpr (Complex.norm_exp_ofReal_mul_I t).le)]
  exact hφ t

theorem fiber_circle_oneFixedQS {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    IsOneFixedQS (fun z => sigmaW w (finPart (gammaMu μ z))) := by
  have heq : (fun z => sigmaW w (finPart (gammaMu μ z))) = (sigmaW w) ∘ wA μ := by
    funext z
    simp only [gammaMu, alphaMu_eq_id, id_eq, Function.comp_apply, wA]
  rw [heq]
  obtain ⟨u, huc, hum, hup, hue⟩ := wA_circle_sensePreserving hμ
  obtain ⟨v, hvc, hvm, hvp, hve⟩ := sigmaW_circle_sensePreserving hw
  refine ⟨⟨⟨v ∘ u, hvc.comp huc, hvm.comp hum, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro t
    simp only [Function.comp_apply, hup, hvp]
  · intro t
    simp only [Function.comp_apply, hue, hve]
  · obtain ⟨a, b, c, d, hdet, hs⟩ := sigmaSphere_isMobius hw
    have hn : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ w := by
      intro z hz he
      have hh := mem_sphere_zero_iff_norm.mp hz
      rw [he] at hh
      exact (ne_of_gt hw) hh
    have hd : ∀ z ∈ sphere (0 : ℂ) 1, c * z + d ≠ 0 := by
      intro z hz hh
      have hv := sigmaSphere_coe_eq hw (hn z hz)
      rw [hs, mobiusExt_coe_of_eq_zero hh] at hv
      exact OnePoint.coe_ne_infty _ hv.symm
    have hmap : MapsTo (wA μ) (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
      intro z hz
      obtain ⟨x, hx, he⟩ := wAS_maps_circle hμ (mem_sphere_zero_iff_norm.mp hz)
      have hh : wA μ z = x := congrArg finPart he
      rw [hh]
      exact mem_sphere_zero_iff_norm.mpr hx
    apply circleQS_congr (circleQS_mobius_postcompose (wA_circle_quasisymmetric hμ) hmap hdet hd)
    intro z hz
    have hv := sigmaSphere_coe_eq hw (hn _ (hmap hz))
    rw [hs, mobiusExt_coe (hd _ (hmap hz))] at hv
    exact (OnePoint.coe_injective hv).symm
  · obtain ⟨M, hM, W, hW, hwf, hwi, hm1, hmI, hp1⟩ := wA_spec hμ
    have hf : wA μ 1 = 1 := congrArg finPart hp1
    have hw1 : 1 - w ≠ 0 := by
      intro hh
      have hh' := sub_eq_zero.mp hh
      rw [← hh'] at hw
      norm_num [unitDiscExterior] at hw
    have hcw1 : 1 - conj w ≠ 0 := by
      intro hh
      apply hw1
      simpa using congrArg (starRingEnd ℂ) hh
    simp only [Function.comp_apply, hf, sigmaW, one_mul]
    field_simp

theorem fiber_welding_sphere_candidate {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    {w : ℂ} (hw : w ∈ unitDiscExterior) :
    let c := -1 / gMu μ w
    IsOneFixedQS (fun z => sigmaW w (finPart (gammaMu μ z))) ∧
      IsWeldingPrime (fun z => sigmaW w (finPart (gammaMu μ z)))
        (fun z => lambdaW c (fB μ z))
        (fun z => finPart (mobiusExt 1 0 c 1
          (normalizedWeldingSphere μ (sigmaInvSphere (w : ExtPlane) (z : ExtPlane))))) ∧
      c = -(1 / 2) * (deriv (deriv fun z => lambdaW c (fB μ z)) 0 -
        deriv (deriv (fB μ)) 0) / deriv (fun z => lambdaW c (fB μ z)) 0 :=
  ⟨fiber_circle_oneFixedQS hμ hw, fiberWeldingPrime_sphere hμ hw,
    fiber_welding_derivative_identity hμ _⟩

end TakhtajanTeo

#print axioms TakhtajanTeo.fiber_welding_sphere_candidate
