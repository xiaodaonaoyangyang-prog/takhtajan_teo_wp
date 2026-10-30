import TakhtajanTeo.Ch1.SquareMorreyFour

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem mp_l4_error_triangle {μ : Measure ℂ} {v g : ℂ → ℂ} {a : ℂ}
    (hv : MemLp v 4 μ) (hg : MemLp g 4 μ) (ha : MemLp (fun _ : ℂ => a) 4 μ) :
    (eLpNorm (fun z => v z - a) 4 μ).toReal ≤
      (eLpNorm (fun z => v z - g z) 4 μ).toReal +
        (eLpNorm (fun z => g z - a) 4 μ).toReal := by
  have hvg : MemLp (fun z => v z - g z) 4 μ := hv.sub hg
  have hga : MemLp (fun z => g z - a) 4 μ := hg.sub ha
  have h := mp_l4_add_le hvg hga
  simpa only [sub_add_sub_cancel] using h

/-- The local Morrey remainder estimate passes to generalized L4 partials by
their defining C1 approximation. No classical differentiability is assumed. -/
theorem mp_genPartials_square_morrey_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η f g h : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → HasGenPartials f g h univ 4 →
      ∀ A : ℂ →L[ℝ] ℂ, tsupport η ⊆ mp_complexSquare →
      (∀ z, ‖η z‖ ≤ 1) → ∀ K : ℝ, 0 ≤ K → (∀ z, ‖dzbar η z‖ ≤ K) →
      ∀ x y : ℂ, η x = 1 → η y = 1 →
      ‖f x - f y - A (x - y)‖ ≤ C * (1 + 2 * K) *
        ((eLpNorm (fun z => g z - A 1) 4 (volume.restrict mp_complexSquare)).toReal +
          (eLpNorm (fun z => h z - A I) 4 (volume.restrict mp_complexSquare)).toReal) *
        ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_complex_square_morrey_four
  refine ⟨C, hC, fun η f g h hη hc hgp A hs hηbound K hK hderiv x y hx hy => ?_⟩
  obtain ⟨hM, fn, hfn, hconv, hconvD⟩ := hgp
  have hfn' : ∀ n, ContDiff ℝ 1 (fn n) := fun n => contDiffOn_univ.mp (hfn n)
  obtain ⟨hg, hh⟩ := hM mp_complexSquare (subset_univ _) mp_complexSquare_compact
  obtain ⟨hEx, hEy⟩ := hconvD mp_complexSquare (subset_univ _) mp_complexSquare_compact
  have hEx' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEx
  have hEy' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEy
  simp only [ENNReal.toReal_zero] at hEx' hEy'
  let G := (eLpNorm (fun z => g z - A 1) 4 (volume.restrict mp_complexSquare)).toReal
  let H := (eLpNorm (fun z => h z - A I) 4 (volume.restrict mp_complexSquare)).toReal
  let Ex := fun n => (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z)
    4 (volume.restrict mp_complexSquare)).toReal
  let Ey := fun n => (eLpNorm (fun z => fderiv ℝ (fn n) z I - h z)
    4 (volume.restrict mp_complexSquare)).toReal
  have hboundx : ∀ n, (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - A 1)
      4 (volume.restrict mp_complexSquare)).toReal ≤ Ex n + G := by
    intro n
    exact mp_l4_error_triangle
      (mp_complex_square_memLp (((hfn' n).continuous_fderiv one_ne_zero).clm_apply continuous_const))
      hg (mp_complex_square_memLp continuous_const)
  have hboundy : ∀ n, (eLpNorm (fun z => fderiv ℝ (fn n) z I - A I)
      4 (volume.restrict mp_complexSquare)).toReal ≤ Ey n + H := by
    intro n
    exact mp_l4_error_triangle
      (mp_complex_square_memLp (((hfn' n).continuous_fderiv one_ne_zero).clm_apply continuous_const))
      hh (mp_complex_square_memLp continuous_const)
  have hineq : ∀ n, ‖fn n x - fn n y - A (x - y)‖ ≤
      C * (1 + 2 * K) * ((Ex n + G) + (Ey n + H)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    intro n
    refine (hest η (fn n) hη hc (hfn' n) A hs hηbound K hK hderiv x y hx hy).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add (hboundx n) (hboundy n)) (mul_nonneg hC (by positivity)))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hleft : Tendsto (fun n => ‖fn n x - fn n y - A (x - y)‖) atTop
      (𝓝 ‖f x - f y - A (x - y)‖) :=
    (((hconv.tendsto_at (mem_univ x)).sub (hconv.tendsto_at (mem_univ y))).sub_const _).norm
  have hsum : Tendsto (fun n => (Ex n + G) + (Ey n + H)) atTop (𝓝 (G + H)) := by
    simpa only [Ex, Ey, Function.comp_def, zero_add] using
      (hEx'.add_const G).add (hEy'.add_const H)
  have hright : Tendsto (fun n => C * (1 + 2 * K) * ((Ex n + G) + (Ey n + H)) *
      ‖x - y‖ ^ (1 / 2 : ℝ)) atTop
      (𝓝 (C * (1 + 2 * K) * (G + H) * ‖x - y‖ ^ (1 / 2 : ℝ))) :=
    (hsum.const_mul _).mul_const _
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hineq)

/-- Actual Cauchy transforms satisfy the local affine-remainder estimate with
their proved generalized gradient. This does not assert a classical derivative. -/
theorem mp_cauchy_square_remainder_four :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η κ : ℂ → ℂ,
      ContDiff ℝ 1 η → HasCompactSupport η → MemLp κ 4 →
      Bornology.IsBounded (Function.support κ) →
      ∀ A : ℂ →L[ℝ] ℂ, tsupport η ⊆ mp_complexSquare →
      (∀ z, ‖η z‖ ≤ 1) → ∀ K : ℝ, 0 ≤ K → (∀ z, ‖dzbar η z‖ ≤ K) →
      ∀ x y : ℂ, η x = 1 → η y = 1 →
      ‖cauchyT κ x - cauchyT κ y - A (x - y)‖ ≤ C * (1 + 2 * K) *
        ((eLpNorm (fun z => hilbertH κ z + κ z - A 1)
          4 (volume.restrict mp_complexSquare)).toReal +
          (eLpNorm (fun z => I * (hilbertH κ z - κ z) - A I)
          4 (volume.restrict mp_complexSquare)).toReal) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hest⟩ := mp_genPartials_square_morrey_four
  refine ⟨C, hC, fun η κ hη hc hκ hκsupp A hs hηbound K hK hderiv x y hx hy => ?_⟩
  have hgp : HasGenPartials (cauchyT κ) (fun z => hilbertH κ z + κ z)
      (fun z => I * (hilbertH κ z - κ z)) univ 4 := by
    simpa using (thm11_1 (p := 4) (by norm_num) (by simpa using hκ) hκsupp).1
  exact hest η (cauchyT κ) _ _ hη hc hgp A hs hηbound K hK hderiv x y hx hy

end TakhtajanTeo

