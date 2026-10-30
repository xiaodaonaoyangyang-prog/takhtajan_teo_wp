import TakhtajanTeo.Ch1.QuasidiskKernel

/-!
# Two pieces of Cui's bound (C3g, C5), proved for `Ch1/CuiBound`

- `cui_area_bound_gen` (C3g): the Koebe area bound, from Koebe 1/4 at a point (`r24_koebe_point`), the change of
  variables through the q.c. map `W` (`qcv_lintegral_image_eq`) and `∬_{|ξ - c| ≥ R} |ξ - c|⁻⁴ ≤ π/R²`.
- `cui_bergman` (C5): `∬_𝔻 |w - z|⁻⁴ dA(z) = π/(|w|² - 1)²`, by the change of variables `v = 1/(z - w)`, which
  maps `𝔻` onto the disc of radius `1/(|w|² - 1)` and has `|dv/dz|² = |z - w|⁻⁴`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real NNReal

noncomputable section

namespace TakhtajanTeo
namespace CUI

open QCV LiZhongQC

/-- `(‖v‖₊)⁻¹⁴` in `ofReal` form. -/
theorem cuip_ker {v : ℂ} (hv : v ≠ 0) : (‖v‖₊ : ℝ≥0∞)⁻¹ ^ 4 = ENNReal.ofReal (1 / ‖v‖ ^ 4) := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hp.le, ← ENNReal.inv_pow,
    ofReal_norm, enorm_eq_nnnorm]

/-- (C3g) Koebe area bound: with `c_z = (1 - |z'|²)|f'(z')|` the hyperbolic weight of `f 𝔻 ⊆ Ω` at
`z = f z'`, `(|W'(z)| c_z)² ∬_{Ωᶜ} J_W/|W - W(z)|⁴ ≤ 16π`. -/
theorem cui_area_bound_gen {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hWΩ : DifferentiableOn ℂ W Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc) (hfΩ : f '' unitDisc ⊆ Ω)
    {z' : ℂ} (hz' : z' ∈ unitDisc) :
    ENNReal.ofReal (‖deriv W (f z')‖ ^ 2 * ((1 - ‖z'‖ ^ 2) * ‖deriv f z'‖) ^ 2) *
        ∫⁻ w in Ωᶜ, ENNReal.ofReal (jacobian W w / ‖W w - W (f z')‖ ^ 4) ≤
      ENNReal.ofReal (16 * π) := by
  have hWc : ContinuousOn W univ := hW.2.2.1.1
  have hWi : InjOn W univ := hW.2.2.1.2.1
  have hz1 : ‖z'‖ < 1 := mem_ball_zero_iff.mp hz'
  have hs : (0 : ℝ) < 1 - ‖z'‖ ^ 2 := by nlinarith [norm_nonneg z']
  have hfz : f z' ∈ Ω := hfΩ ⟨z', hz', rfl⟩
  -- `W ∘ f` is univalent on `𝔻`
  have hWfd : DifferentiableOn ℂ (W ∘ f) unitDisc := hWΩ.comp hf (fun x hx => hfΩ ⟨x, hx, rfl⟩)
  have hWfi : InjOn (W ∘ f) unitDisc := fun a ha b hb h => hfi ha hb (hWi (mem_univ _) (mem_univ _) h)
  have hder : deriv (W ∘ f) z' = deriv W (f z') * deriv f z' :=
    deriv_comp z' (hWΩ.differentiableAt (hΩ.mem_nhds hfz)) (hf.differentiableAt (isOpen_ball.mem_nhds hz'))
  have hne : deriv (W ∘ f) z' ≠ 0 := kb_deriv_ne_zero_of_injOn isOpen_ball hWfd hWfi hz'
  have hW'0 : deriv W (f z') ≠ 0 := by rw [hder] at hne; exact left_ne_zero_of_mul hne
  have hf'0 : deriv f z' ≠ 0 := by rw [hder] at hne; exact right_ne_zero_of_mul hne
  set R : ℝ := ‖deriv (W ∘ f) z'‖ * (1 - ‖z'‖ ^ 2) / 4 with hR
  have hR0 : 0 < R := by rw [hR]; have := norm_pos_iff.mpr hne; positivity
  have hball := r24_koebe_point hWfd hWfi hz'
  set a : ℂ := W (f z') with ha
  -- points of `W(Ωᶜ)` stay at distance `≥ R` from `a`
  have hout : ∀ v ∈ W '' Ωᶜ, R ≤ ‖v - a‖ := by
    rintro _ ⟨w, hw, rfl⟩
    by_contra hlt
    push_neg at hlt
    have hb : W w ∈ ball ((W ∘ f) z') R := by
      rw [mem_ball, dist_eq_norm]; exact hlt
    obtain ⟨x, hx, hxe⟩ := hball hb
    have : f x = w := hWi (mem_univ _) (mem_univ _) hxe
    exact hw (this ▸ hfΩ ⟨x, hx, rfl⟩)
  have hm : MeasurableSet (W '' Ωᶜ) :=
    hΩ.isClosed_compl.measurableSet.image_of_continuousOn_injOn (hWc.mono (subset_univ _))
      (hWi.mono (subset_univ _))
  -- change of variables through `W`
  have hcov := qcv_lintegral_image_eq hW ((W '' Ωᶜ).indicator fun v => (‖v - a‖₊ : ℝ≥0∞)⁻¹ ^ 4)
  have hI : ∫⁻ w in Ωᶜ, ENNReal.ofReal (jacobian W w / ‖W w - a‖ ^ 4) ≤ ENNReal.ofReal (π / R ^ 2) := by
    calc ∫⁻ w in Ωᶜ, ENNReal.ofReal (jacobian W w / ‖W w - a‖ ^ 4)
        = ∫⁻ w, ENNReal.ofReal (jacobian W w) *
            (W '' Ωᶜ).indicator (fun v => (‖v - a‖₊ : ℝ≥0∞)⁻¹ ^ 4) (W w) := by
          rw [← lintegral_indicator hΩ.isClosed_compl.measurableSet]
          apply lintegral_congr
          intro w
          by_cases hw : w ∈ Ωᶜ
          · have hmem : W w ∈ W '' Ωᶜ := ⟨w, hw, rfl⟩
            rw [indicator_of_mem hw, indicator_of_mem hmem]
            have hd : W w - a ≠ 0 := by
              intro h
              have : w = f z' := hWi (mem_univ _) (mem_univ _) (sub_eq_zero.mp h)
              exact hw (this ▸ hfz)
            have hp : 0 ≤ 1 / ‖W w - a‖ ^ 4 := by positivity
            rw [cuip_ker hd, ← ENNReal.ofReal_mul' hp, div_eq_mul_one_div]
          · have hnot : W w ∉ W '' Ωᶜ := by
              rintro ⟨u, hu, hue⟩
              exact hw (hWi (mem_univ _) (mem_univ _) hue ▸ hu)
            rw [indicator_of_notMem hw, indicator_of_notMem hnot, mul_zero]
      _ = ∫⁻ v in W '' univ, (W '' Ωᶜ).indicator (fun v => (‖v - a‖₊ : ℝ≥0∞)⁻¹ ^ 4) v := by
          rw [hcov, Measure.restrict_univ]
      _ ≤ ∫⁻ v, (W '' Ωᶜ).indicator (fun v => (‖v - a‖₊ : ℝ≥0∞)⁻¹ ^ 4) v := setLIntegral_le_lintegral _ _
      _ = ∫⁻ v in W '' Ωᶜ, (‖v - a‖₊ : ℝ≥0∞)⁻¹ ^ 4 := lintegral_indicator hm _
      _ ≤ ENNReal.ofReal (π / R ^ 2) := r24_lintegral_outside hR0 hout
  calc ENNReal.ofReal (‖deriv W (f z')‖ ^ 2 * ((1 - ‖z'‖ ^ 2) * ‖deriv f z'‖) ^ 2) *
        ∫⁻ w in Ωᶜ, ENNReal.ofReal (jacobian W w / ‖W w - W (f z')‖ ^ 4)
      ≤ ENNReal.ofReal (‖deriv W (f z')‖ ^ 2 * ((1 - ‖z'‖ ^ 2) * ‖deriv f z'‖) ^ 2) *
          ENNReal.ofReal (π / R ^ 2) := mul_le_mul' le_rfl hI
    _ = ENNReal.ofReal (16 * π) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hR, hder, norm_mul]
      have h1 : ‖deriv W (f z')‖ ≠ 0 := norm_ne_zero_iff.mpr hW'0
      have h2 : ‖deriv f z'‖ ≠ 0 := norm_ne_zero_iff.mpr hf'0
      have h3 : (1 : ℝ) - ‖z'‖ ^ 2 ≠ 0 := hs.ne'
      field_simp
      try ring

/-- (C5) The Bergman-type integral `∬_𝔻 |w - z|⁻⁴ dA(z) = π/(|w|²-1)²` for `w ∈ 𝔻*`. -/
theorem cui_bergman {w : ℂ} (hw : w ∈ unitDiscExterior) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (1 / ‖w - z‖ ^ 4) = ENNReal.ofReal (π / (‖w‖ ^ 2 - 1) ^ 2) := by
  have hw1 : 1 < ‖w‖ := hw
  set A : ℝ := ‖w‖ ^ 2 - 1 with hA
  have hA0 : 0 < A := by rw [hA]; nlinarith
  set T : ℂ → ℂ := fun z => (z - w)⁻¹ with hT
  have hzw : ∀ z ∈ unitDisc, z - w ≠ 0 := by
    intro z hz h
    have h1 := mem_ball_zero_iff.mp hz
    rw [sub_eq_zero.mp h] at h1; linarith
  have hTd : DifferentiableOn ℂ T unitDisc := fun z hz =>
    ((differentiableAt_id.sub_const w).inv (hzw z hz)).differentiableWithinAt
  have hTi : InjOn T unitDisc := fun z₁ _ z₂ _ he => sub_left_injective (inv_injective he)
  have hcov := r24_conformal_lintegral (U := unitDisc) isOpen_ball hTd hTi (fun _ => 1)
  -- the image disc
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
  have key : ∀ v : ℂ, v ≠ 0 → (w + v⁻¹ ∈ unitDisc ↔ v ∈ ball (-(conj w) / (A : ℂ)) (1 / A)) := by
    intro v hv
    change w + v⁻¹ ∈ ball (0 : ℂ) 1 ↔ v ∈ ball (-(conj w) / (A : ℂ)) (1 / A)
    rw [mem_ball_zero_iff, mem_ball, dist_eq_norm]
    have e1 : ‖w + v⁻¹‖ = ‖w * v + 1‖ / ‖v‖ := by
      rw [← norm_div]; congr 1; field_simp
    have e2 : ‖v - -(conj w) / (A : ℂ)‖ = ‖(A : ℂ) * v + conj w‖ / A := by
      rw [show v - -(conj w) / (A : ℂ) = ((A : ℂ) * v + conj w) / A by field_simp; ring, norm_div,
        Complex.norm_real, Real.norm_of_nonneg hA0.le]
    rw [e1, e2, div_lt_one (norm_pos_iff.mpr hv), div_lt_div_iff_of_pos_right hA0]
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← sq_lt_sq₀ (norm_nonneg _) zero_le_one]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    have hw2 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    rw [hA, hw2]
    constructor <;> intro h <;> nlinarith [sq_nonneg v.re, sq_nonneg v.im]
  have himg : T '' unitDisc = ball (-(conj w) / (A : ℂ)) (1 / A) := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hv : T z ≠ 0 := inv_ne_zero (hzw z hz)
      refine (key _ hv).mp ?_
      simpa [hT] using hz
    · intro hv
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [mem_ball, dist_eq_norm, zero_sub, norm_neg, norm_div, norm_neg, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg hA0.le, div_lt_div_iff_of_pos_right hA0] at hv
        linarith
      refine ⟨w + v⁻¹, (key v hv0).mpr hv, ?_⟩
      simp [hT]
  rw [himg, setLIntegral_const, one_mul, Complex.volume_ball] at hcov
  have hpt : ∫⁻ z in unitDisc, ENNReal.ofReal (1 / ‖w - z‖ ^ 4) =
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv T z‖ ^ 2) * (fun _ => (1 : ℝ≥0∞)) (T z) := by
    apply setLIntegral_congr_fun isOpen_ball.measurableSet
    intro z hz
    simp only [mul_one]
    congr 1
    have hd : deriv T z = -((z - w) ^ 2)⁻¹ := by
      have h := ((hasDerivAt_id z).sub_const w).inv (hzw z hz)
      simpa only [T, Pi.inv_def, id_eq, neg_div, one_div] using h.deriv
    rw [hd, norm_neg, norm_inv, norm_pow, inv_pow, ← pow_mul, one_div, norm_sub_rev]
  rw [hpt, ← hcov, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end CUI
end TakhtajanTeo

