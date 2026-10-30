import TakhtajanTeo.Ch1.TCurveMobiusContinuity

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The sphere coordinate a=conj(1/u) is a disk parameter, also at infinity. -/
theorem tcg_sigma_coordinate_mem {u : ExtPlane} (hu : u ∈ extDiscExterior) :
    ‖conj (finPart (mobiusExt 0 1 1 0 u))‖ < 1 := by
  induction u using OnePoint.rec with
  | infty => norm_num [mobiusExt, finPart]
  | coe u =>
    have huE : 1 < ‖u‖ := by simpa [extDiscExterior, toExt, unitDiscExterior] using hu
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one huE))
    rw [mobiusExt_coe (by simpa using hu0)]
    simpa [mobiusFn, finPart] using (inv_lt_one₀ (lt_trans zero_lt_one huE)).mpr huE

/-- The normalization at 1 gives a unit-modulus rotation factor. -/
theorem tcg_sigma_rotation_norm {a : ℂ} (ha : ‖a‖ < 1) :
    ‖(1 - conj a) / (1 - a)‖ = 1 := by
  have hd : 1 - a ≠ 0 := by
    intro h
    have ha1 := sub_eq_zero.mp h
    rw [← ha1, norm_one] at ha
    exact lt_irrefl _ ha
  rw [show (1 : ℂ) - conj a = conj (1 - a) by simp, norm_div, norm_conj,
    div_self (norm_ne_zero_iff.mpr hd)]

/-- Explicit normalized Blaschke expression for sigma_u on the closed disk. -/
theorem tcg_sigma_coordinate_formula {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    sigmaSphere u (z : ExtPlane) =
      (((1 - conj (conj (finPart (mobiusExt 0 1 1 0 u)))) /
        (1 - conj (finPart (mobiusExt 0 1 1 0 u))) *
        blaschke (conj (finPart (mobiusExt 0 1 1 0 u))) z : ℂ) : ExtPlane) := by
  induction u using OnePoint.rec with
  | infty => simp [sigmaSphere, mobiusExt, finPart, blaschke]
  | coe u =>
    have huE : u ∈ unitDiscExterior := by simpa [extDiscExterior, toExt] using hu
    have huN : 1 < ‖u‖ := huE
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one huN))
    have hcu0 : conj u ≠ 0 := by simpa using hu0
    have hu1 : u ≠ 1 := by intro h; rw [h, norm_one] at huN; exact lt_irrefl _ huN
    have hcu1 : conj u ≠ 1 := by
      intro h
      apply hu1
      simpa using congrArg conj h
    have hzu : z ≠ u := by intro h; rw [h] at hz; exact (not_le_of_gt huN) hz
    have ha : ‖(conj u)⁻¹‖ < 1 := by
      rw [norm_inv, norm_conj]
      exact (inv_lt_one₀ (lt_trans zero_lt_one huN)).mpr huN
    rw [sigmaSphere_coe_eq huE hzu, mobiusExt_coe (by simpa using hu0)]
    simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero, finPart, one_div, map_inv₀, conj_conj]
    apply congrArg (fun w : ℂ => (w : ExtPlane))
    dsimp [sigmaW, blaschke]
    simp only [map_inv₀, conj_conj]
    have hd1 : 1 - (conj u)⁻¹ ≠ 0 := by
      intro h
      have h' : (conj u)⁻¹ = 1 := (sub_eq_zero.mp h).symm
      exact hcu1 (inv_eq_one.mp h')
    have hd2 : 1 - u⁻¹ * z ≠ 0 := by
      simpa only [map_inv₀, conj_conj] using blaschke_den_closed ha hz
    field_simp [hu0, hcu0, hd1, hd2, sub_ne_zero.mpr hzu, sub_ne_zero.mpr hcu1.symm]
    <;> ring

/-- Continuity of the sphere-to-disk parameter on its full exterior domain. -/
theorem tcg_sigma_coordinate_continuous :
    Continuous (fun u : extDiscExterior => conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane)))) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hn : mobiusExt 0 1 1 0 (u : ExtPlane) ≠ extInf := by
    have hu := u.2
    generalize he : (u : ExtPlane) = v at hu ⊢
    induction v using OnePoint.rec with
    | infty => simp [mobiusExt, extInf]
    | coe v =>
      have hv : 1 < ‖v‖ := by simpa [extDiscExterior, toExt, unitDiscExterior] using hu
      have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one hv))
      rw [mobiusExt_coe (by simpa using hv0)]
      exact OnePoint.coe_ne_infty _
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hn
  have hfin : ContinuousAt finPart (mobiusExt 0 1 1 0 (u : ExtPlane)) := by
    rw [← hz]
    exact OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp
      (continuousAt_id : ContinuousAt (fun x : ℂ => x) z)
  have hi : Continuous (fun u : extDiscExterior => mobiusExt 0 1 1 0 (u : ExtPlane)) :=
    (continuous_mobiusExt (a := 0) (b := 1) (c := 1) (d := 0) (by norm_num)).comp continuous_subtype_val
  exact Complex.continuous_conj.continuousAt.comp
    (hfin.comp (f := fun u : extDiscExterior => mobiusExt 0 1 1 0 (u : ExtPlane)) hi.continuousAt)

/-- The rotation coefficient is continuous through the sphere point infinity. -/
theorem tcg_sigma_rotation_continuous :
    Continuous (fun u : extDiscExterior =>
      (1 - conj (conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane)))) ) /
        (1 - conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane))))) := by
  apply (continuous_const.sub (Complex.continuous_conj.comp tcg_sigma_coordinate_continuous)).div
    (continuous_const.sub tcg_sigma_coordinate_continuous)
  intro u h
  have ha := tcg_sigma_coordinate_mem u.2
  have he := sub_eq_zero.mp h
  dsimp only at he
  rw [← he, norm_one] at ha
  exact lt_irrefl _ ha

/-- Strong joint continuity for the original sphere sigma parameter,
including its point at infinity. -/
theorem tcg_sigma_pullback_continuous :
    let a : extDiscExterior → ℂ := fun u => conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane)))
    let c : extDiscExterior → ℂ := fun u => (1 - conj (a u)) / (1 - a u)
    let S : extDiscExterior → ℂ → ℂ := fun u z => blaschke (-a u) (conj (c u) * z)
    Continuous (fun p : A2 unitDisc × extDiscExterior =>
      toA2 unitDisc (fun z => A2.toFun p.1 (S p.2 z) * deriv (S p.2) z ^ 2)) := by
  let a : extDiscExterior → ℂ := fun u => conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane)))
  let c : extDiscExterior → ℂ := fun u => (1 - conj (a u)) / (1 - a u)
  have ha : ∀ u, ‖a u‖ < 1 := fun u => tcg_sigma_coordinate_mem u.2
  have hc : ∀ u, ‖c u‖ = 1 := fun u => tcg_sigma_rotation_norm (ha u)
  exact tcg_mobius_pullback_continuous c a tcg_sigma_rotation_continuous
    tcg_sigma_coordinate_continuous hc ha

/-- The inverse of any conformal-disk plane extension is the explicit disk
Mobius map. Boundary equality is promoted by holomorphic uniqueness. -/
theorem tcg_sigma_inverse_formula {u : ExtPlane} (hu : u ∈ extDiscExterior)
    (R : ℂ ≃ₜ ℂ) (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart (sigmaSphere u (z : ExtPlane))) unitCircle) :
    let a := conj (finPart (mobiusExt 0 1 1 0 u))
    let c := (1 - conj a) / (1 - a)
    EqOn (⇑R.symm) (fun z => blaschke (-a) (conj c * z)) unitDisc := by
  let a := conj (finPart (mobiusExt 0 1 1 0 u))
  let c := (1 - conj a) / (1 - a)
  have ha : ‖a‖ < 1 := tcg_sigma_coordinate_mem hu
  have hc : ‖c‖ = 1 := tcg_sigma_rotation_norm ha
  have hRconf : IsConformalOnto (⇑R) unitDisc unitDisc :=
    tcg_inverse_disk_conformal R.symm hRD
  have hFconf := (isConformalOnto_rot hc).comp (isConformalOnto_blaschke ha)
  have hb : EqOn (⇑R) (fun z => c * blaschke a z) (frontier unitDisc) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [unitDisc, frontier_ball (0 : ℂ) one_ne_zero] using hz
    rw [hRb (show z ∈ unitCircle from hz1)]
    exact congrArg finPart (tcg_sigma_coordinate_formula hu hz1.le)
  have hFcl : ContinuousOn (fun z => c * blaschke a z) (closure unitDisc) := by
    rw [unitDisc, closure_ball _ one_ne_zero]
    exact (blaschke_closed_properties ha).1.const_mul c
  have heq : EqOn (⇑R) (fun z => c * blaschke a z) unitDisc :=
    Complex.eqOn_of_eqOn_frontier isBounded_ball ⟨hRconf.1, R.continuous.continuousOn⟩
      ⟨hFconf.1, hFcl⟩ hb
  have hS : IsConformalOnto (fun z => blaschke (-a) (conj c * z)) unitDisc unitDisc :=
    (isConformalOnto_blaschke (by simpa only [norm_neg] using ha)).comp
      (isConformalOnto_rot (by simpa only [norm_conj] using hc))
  change EqOn (⇑R.symm) (fun z => blaschke (-a) (conj c * z)) unitDisc
  intro z hz
  apply R.injective
  rw [R.apply_symm_apply, heq (hS.mapsTo hz)]
  have hcz : ‖conj c * z‖ < 1 := by
    simpa only [norm_mul, norm_conj, hc, one_mul] using mem_ball_zero_iff.mp hz
  have hi := blaschke_neg_blaschke (a := -a) (by simpa only [norm_neg] using ha) hcz
  rw [neg_neg] at hi
  dsimp only
  rw [hi, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  simp

#print axioms tcg_sigma_coordinate_formula
#print axioms tcg_sigma_coordinate_continuous
#print axioms tcg_sigma_rotation_continuous
#print axioms tcg_sigma_pullback_continuous
#print axioms tcg_sigma_inverse_formula
end TakhtajanTeo
