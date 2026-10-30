import TakhtajanTeo.Ch2.S1_SymmetricLift
import TakhtajanTeo.Ch1.GroupAlgebra

/-! # Symmetric boundary maps form a subgroup -/
open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC GardinerLakic2000
namespace Ch2

/-- The absolute-ratio definition implies Gardiner--Lakic vanishing distortion. -/
theorem symt_vanishing {h : ℂ → ℂ} (hs : IsSymmetricHomeo h) : HasVanishingRatioDistortion h := by
  obtain ⟨v,hl,hv⟩ := symt_normalized_lift hs
  apply gl16_circle_vanishing hl
  obtain ⟨ε,hε,hb⟩ := gl16_vanishing_of_bounds (R := qsRatio v) (P := fun _ => True)
    (fun t ht _ => gl16_lift_incr_cmp hl.1 hl.2.1 hl.2.2.2.2.1 ht) (by
      intro η hη
      have hp : 0 < 1+η := by linarith
      obtain ⟨δ,hδ,hδb⟩ := hv (η/(1+η)) (div_pos hη hp)
      refine ⟨δ,hδ,fun t ht htδ => ⟨trivial,fun x => ?_⟩⟩
      have h := abs_lt.mp (hδb x t ht htδ)
      have hR : 0 < qsRatio v x t := div_pos (sub_pos.mpr (hl.2.1 (by linarith)))
        (sub_pos.mpr (hl.2.1 (by linarith)))
      have hsmall : η/(1+η) ≤ η := (div_le_iff₀ hp).mpr (by nlinarith)
      have hid : 1-η/(1+η) = 1/(1+η) := by field_simp; ring
      have hlow : 1/(1+η) ≤ qsRatio v x t := by change _ ≤ (v (x+t)-v x)/(v x-v (x-t)); linarith
      have hinv : (qsRatio v x t)⁻¹ ≤ 1+η := by
        rw [inv_eq_one_div, div_le_iff₀ hR]
        have hh := (div_le_iff₀ hp).mp hlow
        nlinarith
      have hup : qsRatio v x t ≤ 1+η := by
        change (v (x+t)-v x)/(v x-v (x-t)) ≤ _
        linarith
      have hm := max_le hup hinv
      linarith)
  exact ⟨ε,hε,fun x t ht => hb x t ht trivial⟩

/-- Gardiner--Lakic vanishing distortion gives the project's angular-ratio definition. -/
theorem symt_of_vanishing {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hv : HasVanishingRatioDistortion h) : IsSymmetricHomeo h := by
  obtain ⟨v,hl⟩ := gl16_cl_lift hh
  obtain ⟨ε,hε,hb⟩ := gl16_lift_vanishing hl hv
  have hπ : (0 : ℝ) < 2 * π := by positivity
  let u : ℝ → ℝ := fun t => 2 * π * v (t/(2*π))
  refine ⟨u, continuous_const.mul (hl.1.comp (continuous_id.div_const _)), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact mul_lt_mul_of_pos_left (hl.2.1 (div_lt_div_of_pos_right hab hπ)) hπ
  · intro t
    dsimp only [u]
    rw [show (t+2*π)/(2*π) = t/(2*π)+1 by field_simp,hl.2.2.2.2.1]
    ring
  · intro t
    have he : (t : ℂ)*I = 2*π*I*((t/(2*π) : ℝ) : ℂ) := by push_cast; field_simp
    rw [he,← hl.2.2.2.2.2]
    congr 1
    dsimp only [u]
    push_cast
    ring
  · intro η hη
    obtain ⟨δ,hδ,hδb⟩ := Metric.tendsto_nhdsWithin_nhds.mp hε (min (η/2) (1/2)) (by positivity)
    refine ⟨2*π*δ,mul_pos hπ hδ,fun x t ht htδ => ?_⟩
    have ht0 : 0 < t/(2*π) := div_pos ht hπ
    have htD : t/(2*π) < δ := (div_lt_iff₀ hπ).mpr (by nlinarith)
    have hs := hδb ht0 (by rw [Real.dist_eq,sub_zero,abs_of_pos ht0]; exact htD)
    rw [Real.dist_eq,sub_zero] at hs
    have hs1 : |ε (t/(2*π))| < 1/2 := lt_of_lt_of_le hs (min_le_right _ _)
    have hsη : |ε (t/(2*π))| < η/2 := lt_of_lt_of_le hs (min_le_left _ _)
    have hse := abs_lt.mp hs1
    have hseη := abs_lt.mp hsη
    obtain ⟨hlo,hup⟩ := hb (x/(2*π)) (t/(2*π)) ht0
    have hden : 0 < 1+ε (t/(2*π)) := by linarith
    have hnum : 1-ε (t/(2*π)) ≤ 1/(1+ε (t/(2*π))) :=
      (le_div_iff₀ hden).mpr (by nlinarith [sq_nonneg (ε (t/(2*π)))])
    have heq : (u (x+t)-u x)/(u x-u (x-t)) = qsRatio v (x/(2*π)) (t/(2*π)) := by
      dsimp only [u,qsRatio]
      rw [show (x+t)/(2*π) = x/(2*π)+t/(2*π) by ring,
        show (x-t)/(2*π) = x/(2*π)-t/(2*π) by ring,
        ← mul_sub,← mul_sub,mul_div_mul_left _ _ hπ.ne']
    rw [heq,abs_lt]
    constructor <;> linarith

theorem symt_congr {h g : ℂ → ℂ} (hs : IsSymmetricHomeo h) (he : EqOn g h unitCircle) :
    IsSymmetricHomeo g := by
  obtain ⟨u,hc,hm,hp,hb,hr⟩ := hs
  refine ⟨u,hc,hm,hp,fun t => ?_,hr⟩
  rw [he (norm_exp_ofReal_mul_I t),hb]

theorem symt_comp {f g : ℂ → ℂ} (hf : IsSymmetricHomeo f) (hg : IsSymmetricHomeo g) :
    IsSymmetricHomeo (f ∘ g) := by
  obtain ⟨fl,hfl,-⟩ := symt_normalized_lift hf
  obtain ⟨gl,hgl,-⟩ := symt_normalized_lift hg
  exact symt_of_vanishing (gl16_sy_homeo_of_lift (gl16_sy_comp_lift hfl hgl))
    (gl16_sy_comp_vanishing (gl16_sy_homeo_of_lift hfl) (gl16_sy_homeo_of_lift hgl)
      (symt_vanishing hf) (symt_vanishing hg))

theorem symt_inv {f : ℂ → ℂ} (hf : IsSymmetricHomeo f) :
    IsSymmetricHomeo (Function.invFunOn f (sphere (0 : ℂ) 1)) := by
  obtain ⟨fl,hfl,-⟩ := symt_normalized_lift hf
  obtain ⟨hi,hic,him,hli,hil⟩ := gl16_cl_lift_inv hfl
  exact symt_of_vanishing (gl16_sy_homeo_of_lift (gl16_sy_inv_lift hfl hic him hli hil))
    (gl16_sy_inv_vanishing (gl16_sy_homeo_of_lift hfl) (symt_vanishing hf))

/-- Symmetry is invariant under passing to the quotient's selected representative. -/
theorem symt_Phi_iff (a : LinfStarBall) : Phi a ∈ symmetricT ↔ IsSymmetricHomeo (wA a) := by
  have he : teichSetoid (Quotient.out (Phi a)) a := Quotient.mk_out (s := teichSetoid) a
  constructor
  · intro h
    exact symt_congr h (fun z hz => (he z hz).symm)
  · intro h
    exact symt_congr h he

theorem symt_mulT {p q : T1} (hp : p ∈ symmetricT) (hq : q ∈ symmetricT) : mulT p q ∈ symmetricT := by
  let a := (Quotient.out p : LinfStarBall)
  let b := (Quotient.out q : LinfStarBall)
  have hm := grp_mul_mem a.2 b.2
  have he : EqOn (wA (beltramiMul a b)) (wA a ∘ wA b) unitCircle := by
    intro z hz
    obtain ⟨-,hval⟩ := bg_circle_val b.2 hz
    simp only [wA,grp_wAS_mul a.2 b.2,Function.comp_apply]
    rw [hval]
    rfl
  have hh : IsSymmetricHomeo (wA (beltramiMul a b)) := symt_congr (symt_comp hp hq) he
  change (if h : beltramiMul a b ∈ LinfStarBall then Phi ⟨_,h⟩ else p) ∈ symmetricT
  rw [dif_pos hm]
  exact (symt_Phi_iff ⟨_,hm⟩).mpr hh

theorem symt_invT {p : T1} (hp : p ∈ symmetricT) : invT p ∈ symmetricT := by
  let a := (Quotient.out p : LinfStarBall)
  have hm := grp_inv_mem a.2
  have he : EqOn (wA (beltramiInv a)) (Function.invFunOn (wA a) (sphere (0 : ℂ) 1)) unitCircle := by
    intro z hz
    obtain ⟨hc,hval⟩ := bg_circle_val hm hz
    have heS := congrFun (grp_wAS_inv_left a.2) (z : ExtPlane)
    simp only [Function.comp_apply,id] at heS
    rw [hval] at heS
    have heA : wA a (wA (beltramiInv a) z) = z := by
      change finPart (wAS a (wA (beltramiInv a) z : ExtPlane)) = z
      rw [heS]; rfl
    have hia := (wA_circle_quasisymmetric a.2).choose_spec.1
    have hi := hia.leftInvOn_invFunOn (mem_sphere_zero_iff_norm.mpr hc)
    rw [heA] at hi
    exact hi.symm
  have hh : IsSymmetricHomeo (wA (beltramiInv a)) := symt_congr (symt_inv hp) he
  change (if h : beltramiInv a ∈ LinfStarBall then Phi ⟨_,h⟩ else p) ∈ symmetricT
  rw [dif_pos hm]
  exact (symt_Phi_iff ⟨_,hm⟩).mpr hh

end Ch2
end TakhtajanTeo
