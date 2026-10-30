import TakhtajanTeo.Ch1.GroupChain2
import TakhtajanTeo.Ch1.S7_Curvature

/-! Local primitive algebra for the Bers reproducing kernel. Weak derivatives and
boundary limits are separate analytic obligations. -/
open Complex Set MeasureTheory Filter Topology
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

def eq22Primitive (h Q1 Q2 Q3 : ℂ → ℂ) (z u : ℂ) : ℂ :=
  (Q1 (h u) * (u-h u)^2 + 2 * (Q2 (h u) * (u-h u)) + 2 * Q3 (h u)) / (u-z)^4

-- L1
 theorem eq22_numerator_dzbar {h Q1 Q2 Q3 : ℂ → ℂ} {u a : ℂ}
    (hh : DifferentiableAt ℝ h u) (h1 : HasDerivAt Q1 a (h u))
    (h2 : HasDerivAt Q2 (Q1 (h u)) (h u)) (h3 : HasDerivAt Q3 (Q2 (h u)) (h u)) :
    let N := fun v => Q1 (h v) * (v-h v)^2 + 2 * (Q2 (h v) * (v-h v)) + 2 * Q3 (h v)
    DifferentiableAt ℝ N u ∧ dzbar N u = a * (u-h u)^2 * dzbar h u := by
  let d : ℂ → ℂ := fun v => v-h v
  have hid : DifferentiableAt ℝ (fun v : ℂ => v) u := differentiableAt_id
  have hd : DifferentiableAt ℝ d u := hid.sub hh
  have hd2 : DifferentiableAt ℝ (fun v => d v^2) u := hd.pow 2
  have hQ1 : DifferentiableAt ℝ (fun v => Q1 (h v)) u :=
    (h1.differentiableAt.restrictScalars ℝ).comp u hh
  have hQ2 : DifferentiableAt ℝ (fun v => Q2 (h v)) u :=
    (h2.differentiableAt.restrictScalars ℝ).comp u hh
  have hQ3 : DifferentiableAt ℝ (fun v => Q3 (h v)) u :=
    (h3.differentiableAt.restrictScalars ℝ).comp u hh
  have hdbar : dzbar d u = -dzbar h u := by
    dsimp only [d]
    have hIdbar : dzbar (fun v : ℂ => v) u = 0 := by simp [dzbar]
    rw [wp_dzbar_sub hid hh, hIdbar, zero_sub]
  have hA : DifferentiableAt ℝ (fun v => Q1 (h v) * d v^2) u := hQ1.mul hd2
  have hQ2d : DifferentiableAt ℝ (fun v => Q2 (h v) * d v) u := hQ2.mul hd
  have hB : DifferentiableAt ℝ (fun v => 2 * (Q2 (h v) * d v)) u := hQ2d.const_mul (2 : ℂ)
  have hC : DifferentiableAt ℝ (fun v => 2 * Q3 (h v)) u := hQ3.const_mul (2 : ℂ)
  have hAB : DifferentiableAt ℝ (fun v => Q1 (h v) * d v^2 + 2 * (Q2 (h v) * d v)) u := hA.add hB
  refine ⟨(hA.add hB).add hC, ?_⟩
  change dzbar (fun v => Q1 (h v) * d v^2 + 2 * (Q2 (h v) * d v) + 2 * Q3 (h v)) u = _
  rw [wp_dzbar_add hAB hC, wp_dzbar_add hA hB,
    wp_dzbar_const_mul hQ3, wp_dzbar_const_mul hQ2d,
    dzbar_mul hQ1 hd2, dzbar_mul hQ2 hd, wp_dzbar_pow hd,
    grp_dzbar_comp_holo hh h1.differentiableAt,
    grp_dzbar_comp_holo hh h2.differentiableAt,
    grp_dzbar_comp_holo hh h3.differentiableAt,
    h1.deriv, h2.deriv, h3.deriv, hdbar]
  norm_num
  dsimp only [d]
  ring

-- L2
 theorem eq22_primitive_dzbar {h Q1 Q2 Q3 : ℂ → ℂ} {z u a : ℂ}
    (hh : DifferentiableAt ℝ h u) (h1 : HasDerivAt Q1 a (h u))
    (h2 : HasDerivAt Q2 (Q1 (h u)) (h u)) (h3 : HasDerivAt Q3 (Q2 (h u)) (h u))
    (huz : u ≠ z) :
    DifferentiableAt ℝ (eq22Primitive h Q1 Q2 Q3 z) u ∧
      dzbar (eq22Primitive h Q1 Q2 Q3 z) u = a * (u-h u)^2 * dzbar h u / (u-z)^4 := by
  obtain ⟨hN, hdN⟩ := eq22_numerator_dzbar hh h1 h2 h3
  have hk : DifferentiableAt ℂ (fun v : ℂ => ((v-z)^4)⁻¹) u :=
    ((differentiableAt_id.sub_const z).pow 4).inv (pow_ne_zero 4 (sub_ne_zero.mpr huz))
  unfold eq22Primitive
  simp only [div_eq_mul_inv]
  refine ⟨hN.mul (hk.restrictScalars ℝ), ?_⟩
  rw [dzbar_mul hN (hk.restrictScalars ℝ), (cauchyRiemann_iff.mp hk).2, hdN]
  ring

-- L3
 theorem eq22_primitive_boundary {h Q1 Q2 Q3 : ℂ → ℂ} {z u : ℂ} (hu : h u = u) :
    eq22Primitive h Q1 Q2 Q3 z u = 2 * Q3 u / (u-z)^4 := by
  simp [eq22Primitive, hu]

end TakhtajanTeo
