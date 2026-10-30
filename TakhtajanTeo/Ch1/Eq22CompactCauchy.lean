import LiZhongQC.Ch02.S11_IntegralOperators

open Complex Set MeasureTheory Filter Topology
open scoped Real
namespace TakhtajanTeo
open LiZhongQC

theorem eq22_cutoff_product_contDiff {D : Set ℂ} {q χ : ℂ → ℂ}
    (hD : IsOpen D) (hq : DifferentiableOn ℂ q D) (hχ : ContDiff ℝ 1 χ)
    (hs : tsupport χ ⊆ D) : ContDiff ℝ 1 (fun u => χ u*q u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ D
  · exact hχ.contDiffAt.mul (((hq.contDiffOn hD).contDiffAt (hD.mem_nhds hu)).restrict_scalars ℝ)
  · have hn : u ∉ tsupport χ := fun h => hu (hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (show ContDiffAt ℝ 1 (fun _ : ℂ => (0 : ℂ)) u from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [he] with v hv
    simp [hv]

theorem eq22_cutoff_product_dzbar {D : Set ℂ} {q χ : ℂ → ℂ}
    (hD : IsOpen D) (hq : DifferentiableOn ℂ q D) (hχ : ContDiff ℝ 1 χ)
    (hs : tsupport χ ⊆ D) (u : ℂ) :
    dzbar (fun v => χ v*q v) u = q u*dzbar χ u := by
  by_cases hu : u ∈ D
  · have hqu := hq.differentiableAt (hD.mem_nhds hu)
    rw [dzbar_mul (hχ.differentiable one_ne_zero u) (hqu.restrictScalars ℝ),
      (cauchyRiemann_iff.mp hqu).2]
    ring
  · have hn : u ∉ tsupport χ := fun h => hu (hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    have hp : (fun v => χ v*q v) =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [he] with v hv
      simp [hv]
    rw [dzbar_congr_of_eventuallyEq hp, dzbar_congr_of_eventuallyEq he]
    simp [dzbar]

theorem eq22_compact_cauchy {D : Set ℂ} {q χ : ℂ → ℂ}
    (hD : IsOpen D) (hq : DifferentiableOn ℂ q D) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ D) (z : ℂ) :
    Integrable (fun u => q u*dzbar χ u/(u-z)) ∧
    (∫ u, q u*dzbar χ u/(u-z)) = -(π : ℂ)*χ z*q z := by
  let f : ℂ → ℂ := fun u => χ u*q u
  have hf : ContDiff ℝ 1 f := eq22_cutoff_product_contDiff hD hq hχ hs
  have hfc : HasCompactSupport f := hc.mul_right
  have hdc : HasCompactSupport (dzbar f) := by
    exact (hfc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + I*L I)/2) (by simp)
  have he : dzbar f = fun u => q u*dzbar χ u := by
    funext u
    exact eq22_cutoff_product_dzbar hD hq hχ hs u
  have hi := integrable_div_sub_of_hasCompactSupport (continuous_dzbar hf) hdc z
  rw [he] at hi
  refine ⟨hi, ?_⟩
  have ht := cauchyT_dzbar_eq hf hfc z
  rw [cauchyT, he] at ht
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    (∫ u, q u*dzbar χ u/(u-z)) =
        -(π : ℂ)* (-(1/π : ℂ)*(∫ u, q u*dzbar χ u/(u-z))) := by field_simp
    _ = -(π : ℂ)*χ z*q z := by rw [ht]; dsimp [f]; ring

end TakhtajanTeo
