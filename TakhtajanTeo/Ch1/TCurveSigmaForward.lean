import TakhtajanTeo.Ch1.TCurveSigmaCoordinates

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Classical
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- Forward disk formula for every admissible plane extension of sigma_u. -/
theorem tcg_sigma_forward_formula {u : ExtPlane} (hu : u ∈ extDiscExterior)
    (R : ℂ ≃ₜ ℂ) (hRD : IsConformalOnto (⇑R.symm) unitDisc unitDisc)
    (hRb : EqOn (⇑R) (fun z : ℂ => finPart (sigmaSphere u (z : ExtPlane))) unitCircle) :
    let a := conj (finPart (mobiusExt 0 1 1 0 u))
    let c := (1 - conj a) / (1 - a)
    EqOn (⇑R) (fun z => c * blaschke a z) unitDisc := by
  let a := conj (finPart (mobiusExt 0 1 1 0 u))
  let c := (1 - conj a) / (1 - a)
  have ha : ‖a‖ < 1 := tcg_sigma_coordinate_mem hu
  have hc : ‖c‖ = 1 := tcg_sigma_rotation_norm ha
  have hF : IsConformalOnto (fun z => c * blaschke a z) unitDisc unitDisc :=
    (isConformalOnto_rot hc).comp (isConformalOnto_blaschke ha)
  have hcc : conj c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  change EqOn (⇑R) (fun z => c * blaschke a z) unitDisc
  intro z hz
  apply R.symm.injective
  rw [R.symm_apply_apply, tcg_sigma_inverse_formula hu R hRD hRb (hF.mapsTo hz)]
  change z = blaschke (-a) (conj c * (c * blaschke a z))
  rw [← mul_assoc, hcc, one_mul, blaschke_neg_blaschke ha (mem_ball_zero_iff.mp hz)]

/-- Fixed-point evaluation of sigma_u is continuous in the full sphere parameter. -/
theorem tcg_sigma_forward_continuous {z : ℂ} (hz : z ∈ unitDisc) :
    let a : extDiscExterior → ℂ := fun u => conj (finPart (mobiusExt 0 1 1 0 (u : ExtPlane)))
    let c : extDiscExterior → ℂ := fun u => (1 - conj (a u)) / (1 - a u)
    Continuous (fun u => c u * blaschke (a u) z) := by
  exact tcg_sigma_rotation_continuous.mul
    ((continuous_const.sub tcg_sigma_coordinate_continuous).div
      (continuous_const.sub ((Complex.continuous_conj.comp tcg_sigma_coordinate_continuous).mul_const z))
      (fun u => blaschke_den_ne_zero (tcg_sigma_coordinate_mem u.2) (mem_ball_zero_iff.mp hz)))

#print axioms tcg_sigma_forward_formula
#print axioms tcg_sigma_forward_continuous
end TakhtajanTeo
