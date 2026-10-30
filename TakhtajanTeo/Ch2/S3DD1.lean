import TakhtajanTeo.Ch2.S3DBase
import TakhtajanTeo.Ch2.S4ReflectedKernel
import TakhtajanTeo.Appendix.AppACompleted2

/-! # Density route: (D1) the `f`-side term (Program G) -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- [(D1) helper] Separation: `f(𝔻)` is a neighbourhood of `f(w)` disjoint from `g(𝔻*)`, so `g(𝔻*)` stays at positive
distance from `f(w)`. -/
theorem s3d1_sep {f g : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hf' : ∀ w ∈ unitDisc, deriv f w ≠ 0)
    (hdisj : Disjoint (f '' unitDisc) (g '' unitDiscExterior)) {w : ℂ} (hw : w ∈ unitDisc) :
    ∃ δ > 0, ∀ u ∈ unitDiscExterior, 2 * δ ≤ ‖g u - f w‖ := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hst : HasStrictDerivAt f (deriv f w) w :=
    ((hfd.analyticAt (hD.mem_nhds hw)).hasStrictDerivAt)
  have hmap := hst.map_nhds_eq (hf' w hw)
  have hmem : f '' unitDisc ∈ 𝓝 (f w) := by
    rw [← hmap]
    exact Filter.image_mem_map (hD.mem_nhds hw)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε / 2, by positivity, fun u hu => ?_⟩
  have hnot : g u ∉ ball (f w) ε := fun h => Set.disjoint_left.1 hdisj (hball h) ⟨u, hu, rfl⟩
  rw [mem_ball, dist_eq_norm, not_lt] at hnot
  linarith

/-- [(D1) helper] Uniform `O(|u|⁻³)` bounds for the Model B kernel and its first two `ζ`-derivatives, for `ζ` near a
point `ζ₀` from which `g(𝔻*)` keeps distance `2δ`. -/
theorem s3d1_dom {g : ℂ → ℂ} {ζ0 : ℂ} {δ c C M : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hfar : ∀ u : ℂ, 4 ≤ ‖u‖ → c * ‖u‖ ≤ ‖g u‖ ∧ ‖deriv g u‖ ≤ C)
    (hM : ∀ u ∈ unitDiscExterior, ‖deriv g u‖ ≤ M) (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖)
    (hsep : ∀ u ∈ unitDiscExterior, 2 * δ ≤ ‖g u - ζ0‖) :
    ∃ K : ℝ, ∀ u ∈ unitDiscExterior, ∀ ζ ∈ ball ζ0 δ,
      ‖deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹ ∧
      ‖deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹ ∧
      ‖deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹ := by
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖ζ0‖ + δ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 4 + 2 * Z / c := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hU4 : 4 ≤ U := by rw [hU]; have : 0 ≤ 2 * Z / c := by positivity
                         linarith
  have hM0 : 0 ≤ M := by
    have h := hM 2 (show (1 : ℝ) < ‖(2 : ℂ)‖ by norm_num)
    exact (norm_nonneg _).trans h
  -- near bound
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = M ^ 2 * (1 / δ + 4 + 16 * Z + (1 / δ ^ 2 + 16) + 2 / δ ^ 3) := ⟨_, rfl⟩
  -- far bound
  obtain ⟨L', hL'⟩ : ∃ L' : ℝ, L' = 8 * M ^ 2 * (2 * Z ^ 2 + 12 * Z + 16) / c ^ 3 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hL'0 : 0 ≤ L' := by rw [hL']; positivity
  refine ⟨L * (1 + U) ^ 3 + L', fun u hu ζ hζ => ?_⟩
  have hu1 : 1 < ‖u‖ := hu
  have hζZ : ‖ζ‖ ≤ Z := by
    rw [mem_ball, dist_eq_norm] at hζ
    have := norm_le_norm_add_norm_sub' ζ ζ0
    rw [hZ]
    linarith [norm_sub_rev ζ ζ0]
  have hGζ : δ ≤ ‖g u - ζ‖ := by
    rw [mem_ball, dist_eq_norm] at hζ
    have h1 := hsep u hu
    have h2 := norm_sub_le_norm_sub_add_norm_sub (g u) ζ ζ0
    linarith
  have hGk := hk u hu
  have hG0 : g u ≠ 0 := fun h => by rw [h, norm_zero] at hGk; linarith
  have hGζ0 : g u - ζ ≠ 0 := fun h => by rw [h, norm_zero] at hGζ; linarith
  have hgM := hM u hu
  have hpos : 0 < 1 + ‖u‖ := by positivity
  have hw : 0 < ((1 + ‖u‖) ^ 3)⁻¹ := by positivity
  have hd2 : ‖deriv g u ^ 2‖ ≤ M ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hgM 2
  by_cases hfu : U ≤ ‖u‖
  · -- far: `|g| ≥ c|u| ≥ 2Z`
    obtain ⟨hgc, -⟩ := hfar u (le_trans hU4 hfu)
    have hcu : 2 * Z ≤ c * ‖u‖ := by
      have : 2 * Z / c * c = 2 * Z := div_mul_cancel₀ _ hc.ne'
      nlinarith [hU]
    have hGn : c * ‖u‖ ≤ ‖g u‖ := hgc
    have hGz : c * ‖u‖ / 2 ≤ ‖g u - ζ‖ := by
      have := norm_sub_norm_le (g u) ζ
      linarith
    have hu0 : 0 < ‖u‖ := by linarith
    have hcu0 : 0 < c * ‖u‖ := by positivity
    have h8 : ((‖u‖ ^ 3)⁻¹) ≤ 8 * ((1 + ‖u‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ hpos.le (by linarith : 1 + ‖u‖ ≤ 2 * ‖u‖) 3]
    have e0 : 1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2 = ζ ^ 2 / (g u ^ 2 * (g u - ζ)) := by
      field_simp
      ring
    have e1 : 1 / (g u - ζ) ^ 2 - 1 / g u ^ 2 = ζ * (2 * g u - ζ) / (g u ^ 2 * (g u - ζ) ^ 2) := by
      field_simp
      ring
    have hA : ‖ζ ^ 2 / (g u ^ 2 * (g u - ζ))‖ ≤ 2 * Z ^ 2 / c ^ 3 * (‖u‖ ^ 3)⁻¹ := by
      rw [norm_div, norm_mul, norm_pow, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖ζ‖ ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζZ 2
        _ = 2 * Z ^ 2 / c ^ 3 * (‖u‖ ^ 3)⁻¹ * ((c * ‖u‖) ^ 2 * (c * ‖u‖ / 2)) := by field_simp
        _ ≤ _ := by gcongr
    have hB : ‖ζ * (2 * g u - ζ) / (g u ^ 2 * (g u - ζ) ^ 2)‖ ≤ 12 * Z / c ^ 3 * (‖u‖ ^ 3)⁻¹ := by
      have h2g : ‖2 * g u - ζ‖ ≤ 3 * ‖g u‖ := by
        calc ‖2 * g u - ζ‖ ≤ ‖2 * g u‖ + ‖ζ‖ := norm_sub_le _ _
          _ ≤ 3 * ‖g u‖ := by rw [norm_mul, Complex.norm_two]; linarith
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖ζ‖ * ‖2 * g u - ζ‖ ≤ Z * (3 * ‖g u‖) := mul_le_mul hζZ h2g (norm_nonneg _) hZ0
        _ = 12 * Z / c ^ 3 * (‖u‖ ^ 3)⁻¹ * ((c * ‖u‖) * (c * ‖u‖ / 2) ^ 2) * ‖g u‖ := by field_simp; ring
        _ ≤ 12 * Z / c ^ 3 * (‖u‖ ^ 3)⁻¹ * (‖g u‖ * ‖g u - ζ‖ ^ 2) * ‖g u‖ := by gcongr
        _ = _ := by ring
    have hC : ‖(2 : ℂ) / (g u - ζ) ^ 3‖ ≤ 16 / c ^ 3 * (‖u‖ ^ 3)⁻¹ := by
      rw [norm_div, norm_pow, Complex.norm_two, div_le_iff₀ (by positivity)]
      calc (2 : ℝ) = 16 / c ^ 3 * (‖u‖ ^ 3)⁻¹ * (c * ‖u‖ / 2) ^ 3 := by field_simp; ring
        _ ≤ _ := by gcongr
    have hfin : ∀ X : ℝ, 0 ≤ X → X ≤ 16 + 12 * Z + 2 * Z ^ 2 → M ^ 2 * (X / c ^ 3 * (‖u‖ ^ 3)⁻¹) ≤
        (L * (1 + U) ^ 3 + L') * ((1 + ‖u‖) ^ 3)⁻¹ := by
      intro X hX0 hX
      have h1 : M ^ 2 * (X / c ^ 3 * (‖u‖ ^ 3)⁻¹) ≤ M ^ 2 * (X / c ^ 3 * (8 * ((1 + ‖u‖) ^ 3)⁻¹)) := by gcongr
      have h2 : M ^ 2 * (X / c ^ 3 * (8 * ((1 + ‖u‖) ^ 3)⁻¹)) ≤ L' * ((1 + ‖u‖) ^ 3)⁻¹ := by
        rw [hL']
        have : M ^ 2 * (X / c ^ 3 * (8 * ((1 + ‖u‖) ^ 3)⁻¹)) =
          8 * M ^ 2 * X / c ^ 3 * ((1 + ‖u‖) ^ 3)⁻¹ := by ring
        rw [this]
        gcongr
        linarith
      have h3 : 0 ≤ L * (1 + U) ^ 3 * ((1 + ‖u‖) ^ 3)⁻¹ := by positivity
      nlinarith
    have hZ1 : 0 ≤ 12 * Z := by positivity
    have hZ2 : 0 ≤ 2 * Z ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, norm_mul]
      refine le_trans (mul_le_mul hd2 hA (norm_nonneg _) (by positivity)) ?_
      have := hfin (2 * Z ^ 2) hZ2 (by linarith)
      calc M ^ 2 * (2 * Z ^ 2 / c ^ 3 * (‖u‖ ^ 3)⁻¹) = M ^ 2 * ((2 * Z ^ 2) / c ^ 3 * (‖u‖ ^ 3)⁻¹) := rfl
        _ ≤ _ := this
    · rw [e1, norm_mul]
      refine le_trans (mul_le_mul hd2 hB (norm_nonneg _) (by positivity)) ?_
      exact hfin (12 * Z) hZ1 (by linarith)
    · rw [norm_mul]
      refine le_trans (mul_le_mul hd2 hC (norm_nonneg _) (by positivity)) ?_
      exact hfin 16 (by norm_num) (by linarith)
  · -- near: `|u| < U`
    rw [not_le] at hfu
    have hcmp : 1 ≤ (1 + U) ^ 3 * ((1 + ‖u‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hpos.le (by linarith) 3
    have hnear : ∀ X : ℝ, 0 ≤ X → X ≤ L → X ≤ (L * (1 + U) ^ 3 + L') * ((1 + ‖u‖) ^ 3)⁻¹ := by
      intro X hX0 hX
      have h1 : L ≤ L * ((1 + U) ^ 3 * ((1 + ‖u‖) ^ 3)⁻¹) := le_mul_of_one_le_right hL0 hcmp
      have h2 : 0 ≤ L' * ((1 + ‖u‖) ^ 3)⁻¹ := by positivity
      nlinarith
    have hi1 : ‖1 / (g u - ζ)‖ ≤ 1 / δ := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hδ hGζ
    have hi2 : ‖1 / g u‖ ≤ 4 := by
      rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
      linarith
    have hi3 : ‖ζ / g u ^ 2‖ ≤ 16 * Z := by
      rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
      calc ‖ζ‖ ≤ Z := hζZ
        _ = 16 * Z * (1 / 4) ^ 2 := by ring
        _ ≤ 16 * Z * ‖g u‖ ^ 2 := by gcongr
    have hi4 : ‖1 / (g u - ζ) ^ 2‖ ≤ 1 / δ ^ 2 := by
      rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hδ.le hGζ 2)
    have hi5 : ‖1 / g u ^ 2‖ ≤ 16 := by
      rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = 16 * (1 / 4) ^ 2 := by norm_num
        _ ≤ 16 * ‖g u‖ ^ 2 := by gcongr
    have hi6 : ‖(2 : ℂ) / (g u - ζ) ^ 3‖ ≤ 2 / δ ^ 3 := by
      rw [norm_div, norm_pow, Complex.norm_two]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hδ.le hGζ 3)
    have hLb : M ^ 2 * (1 / δ + 4 + 16 * Z) ≤ L ∧ M ^ 2 * (1 / δ ^ 2 + 16) ≤ L ∧ M ^ 2 * (2 / δ ^ 3) ≤ L := by
      rw [hL]
      have h1 : 0 ≤ 1 / δ := by positivity
      have h2 : 0 ≤ 1 / δ ^ 2 := by positivity
      have h3 : 0 ≤ 2 / δ ^ 3 := by positivity
      refine ⟨?_, ?_, ?_⟩ <;> apply mul_le_mul_of_nonneg_left _ (by positivity) <;> linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]
      refine hnear _ (by positivity) (le_trans (mul_le_mul hd2 ?_ (norm_nonneg _) (by positivity)) hLb.1)
      calc ‖1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2‖ ≤ ‖1 / (g u - ζ)‖ + ‖1 / g u‖ + ‖ζ / g u ^ 2‖ :=
            (norm_sub_le _ _).trans (by linarith [norm_sub_le (1 / (g u - ζ)) (1 / g u)])
        _ ≤ 1 / δ + 4 + 16 * Z := by linarith
    · rw [norm_mul]
      refine hnear _ (by positivity) (le_trans (mul_le_mul hd2 ?_ (norm_nonneg _) (by positivity)) hLb.2.1)
      exact (norm_sub_le _ _).trans (by linarith)
    · rw [norm_mul]
      exact hnear _ (by positivity) (le_trans (mul_le_mul hd2 hi6 (norm_nonneg _) (by positivity)) hLb.2.2)

/-- [(D1) helper] `(f²)' = 2 f f'`. -/
theorem s3d1_sq {f : ℂ → ℂ} {f' x : ℂ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun w => f w ^ 2) (2 * f x * f') x := by
  have h := hf.mul hf
  convert h using 1
  · funext w
    show f w ^ 2 = f w * f w
    ring
  · ring

/-- [(D1) helper] Differentiation of the Model B variation `V̇(ζ) = ∫_{𝔻*} R g'² (1/(g - ζ) - 1/g - ζ/g²)` twice under
the integral sign at a point `ζ₀` from which `g(𝔻*)` keeps distance `2δ`. -/
theorem s3d1_Vdot {g R : ℂ → ℂ} {Rb δ K : ℝ} {ζ0 : ℂ} (hδ : 0 < δ)
    (hgc : ContinuousOn g unitDiscExterior) (hg'c : ContinuousOn (deriv g) unitDiscExterior)
    (hRm : AEStronglyMeasurable R (volume.restrict unitDiscExterior))
    (hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ‖R u‖ ≤ Rb)
    (hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖g u‖) (hsep : ∀ u ∈ unitDiscExterior, 2 * δ ≤ ‖g u - ζ0‖)
    (hK : ∀ u ∈ unitDiscExterior, ∀ ζ ∈ ball ζ0 δ,
      ‖deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹ ∧
      ‖deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹ ∧
      ‖deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)‖ ≤ K * ((1 + ‖u‖) ^ 3)⁻¹) :
    Integrable (fun u => R u * deriv g u ^ 2 * (1 / (g u - ζ0) - 1 / g u - ζ0 / g u ^ 2))
        (volume.restrict unitDiscExterior) ∧
      HasDerivAt (fun ζ => ∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2))
        (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - ζ0) ^ 2 - 1 / g u ^ 2)) ζ0 ∧
      HasDerivAt (fun ζ => ∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2))
        (∫ u in unitDiscExterior, R u * deriv g u ^ 2 * (2 / (g u - ζ0) ^ 3)) ζ0 ∧
      Integrable (fun u => R u * deriv g u ^ 2 * (2 / (g u - ζ0) ^ 3)) (volume.restrict unitDiscExterior) := by
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : MeasurableSet unitDiscExterior := hE.measurableSet
  -- the dominating function
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℝ, B = fun u => max Rb 0 * (K * ((1 + ‖u‖) ^ 3)⁻¹) := ⟨_, rfl⟩
  have hBi : Integrable B (volume.restrict unitDiscExterior) := by
    have h3 : Integrable (fun u : ℂ => (1 + ‖u‖) ^ (-(3 : ℝ))) :=
      integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    have e : (fun u : ℂ => (1 + ‖u‖) ^ (-(3 : ℝ))) = fun u => ((1 + ‖u‖) ^ 3)⁻¹ := by
      funext u
      rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h3
    rw [hB]
    exact ((h3.const_mul K).const_mul (max Rb 0)).integrableOn
  -- nonvanishing on `𝔻*`
  have hne : ∀ u ∈ unitDiscExterior, ∀ ζ ∈ ball ζ0 δ, g u - ζ ≠ 0 ∧ g u ≠ 0 := by
    intro u hu ζ hζ
    rw [mem_ball, dist_eq_norm] at hζ
    have h1 := hsep u hu
    have h2 := norm_sub_le_norm_sub_add_norm_sub (g u) ζ ζ0
    have h3 := hk u hu
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, norm_zero] at h2
      linarith
    · rw [h, norm_zero] at h3
      linarith
  -- measurability
  have hcont : ∀ ζ ∈ ball ζ0 δ, ContinuousOn (fun u => deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2))
      unitDiscExterior ∧ ContinuousOn (fun u => deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2)) unitDiscExterior ∧
      ContinuousOn (fun u => deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)) unitDiscExterior := by
    intro ζ hζ
    have h1 : ∀ u ∈ unitDiscExterior, g u - ζ ≠ 0 := fun u hu => (hne u hu ζ hζ).1
    have h2 : ∀ u ∈ unitDiscExterior, g u ≠ 0 := fun u hu => (hne u hu ζ hζ).2
    have hs : ContinuousOn (fun u => g u - ζ) unitDiscExterior := hgc.sub continuousOn_const
    refine ⟨(hg'c.pow 2).mul (((continuousOn_const.div hs h1).sub (continuousOn_const.div hgc h2)).sub
        (continuousOn_const.div (hgc.pow 2) fun u hu => pow_ne_zero 2 (h2 u hu))), ?_, ?_⟩
    · exact (hg'c.pow 2).mul ((continuousOn_const.div (hs.pow 2) fun u hu => pow_ne_zero 2 (h1 u hu)).sub
        (continuousOn_const.div (hgc.pow 2) fun u hu => pow_ne_zero 2 (h2 u hu)))
    · exact (hg'c.pow 2).mul (continuousOn_const.div (hs.pow 3) fun u hu => pow_ne_zero 3 (h1 u hu))
  have hR2 : AEStronglyMeasurable (fun u => R u) (volume.restrict unitDiscExterior) := hRm
  have hmeas : ∀ ζ ∈ ball ζ0 δ,
      AEStronglyMeasurable (fun u => R u * deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2))
        (volume.restrict unitDiscExterior) ∧
      AEStronglyMeasurable (fun u => R u * deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2))
        (volume.restrict unitDiscExterior) ∧
      AEStronglyMeasurable (fun u => R u * deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)) (volume.restrict unitDiscExterior) := by
    intro ζ hζ
    obtain ⟨c1, c2, c3⟩ := hcont ζ hζ
    refine ⟨?_, ?_, ?_⟩
    · have h := hR2.mul (c1.aestronglyMeasurable hEm)
      refine h.congr (Eventually.of_forall fun u => ?_)
      show R u * (deriv g u ^ 2 * _) = _
      ring
    · have h := hR2.mul (c2.aestronglyMeasurable hEm)
      refine h.congr (Eventually.of_forall fun u => ?_)
      show R u * (deriv g u ^ 2 * _) = _
      ring
    · have h := hR2.mul (c3.aestronglyMeasurable hEm)
      refine h.congr (Eventually.of_forall fun u => ?_)
      show R u * (deriv g u ^ 2 * _) = _
      ring
  -- bounds
  have hbd : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ∀ ζ ∈ ball ζ0 δ,
      ‖R u * deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2)‖ ≤ B u ∧
      ‖R u * deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2)‖ ≤ B u ∧
      ‖R u * deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)‖ ≤ B u := by
    filter_upwards [hRb, ae_restrict_mem hEm] with u hu hmem ζ hζ
    obtain ⟨k1, k2, k3⟩ := hK u hmem ζ hζ
    have hRu : ‖R u‖ ≤ max Rb 0 := hu.trans (le_max_left _ _)
    rw [hB]
    refine ⟨?_, ?_, ?_⟩ <;> rw [mul_assoc, norm_mul] <;>
      exact mul_le_mul hRu (by assumption) (norm_nonneg _) (le_max_right _ _)
  -- pointwise derivatives
  have hder : ∀ᵐ u ∂(volume.restrict unitDiscExterior), ∀ ζ ∈ ball ζ0 δ,
      HasDerivAt (fun ζ => R u * deriv g u ^ 2 * (1 / (g u - ζ) - 1 / g u - ζ / g u ^ 2))
        (R u * deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2)) ζ ∧
      HasDerivAt (fun ζ => R u * deriv g u ^ 2 * (1 / (g u - ζ) ^ 2 - 1 / g u ^ 2))
        (R u * deriv g u ^ 2 * (2 / (g u - ζ) ^ 3)) ζ := by
    filter_upwards [ae_restrict_mem hEm] with u hmem ζ hζ
    obtain ⟨h1, h2⟩ := hne u hmem ζ hζ
    have hd : HasDerivAt (fun y => g u - y) (-1) ζ := (hasDerivAt_id' ζ).const_sub (g u)
    have hinv := hd.inv h1
    have hinv2 := (hd.pow 2).inv (pow_ne_zero 2 h1)
    refine ⟨?_, ?_⟩
    · have key := ((hinv.sub_const (g u)⁻¹).sub ((hasDerivAt_id' ζ).mul_const ((g u ^ 2)⁻¹))).const_mul
        (R u * deriv g u ^ 2)
      convert key using 1
      · funext y
        simp only [Pi.sub_apply, Pi.inv_apply, one_div, div_eq_mul_inv, one_mul]
      · field_simp
    · have key := (hinv2.sub_const ((g u ^ 2)⁻¹)).const_mul (R u * deriv g u ^ 2)
      convert key using 1
      · funext y
        simp only [Pi.sub_apply, Pi.inv_apply, Pi.pow_apply, one_div]
      · simp only [Pi.pow_apply]
        field_simp
        ring
  have hδb : ball ζ0 δ ∈ 𝓝 ζ0 := ball_mem_nhds ζ0 hδ
  have hmem0 : ζ0 ∈ ball ζ0 δ := mem_ball_self hδ
  have hi0 : Integrable (fun u => R u * deriv g u ^ 2 * (1 / (g u - ζ0) - 1 / g u - ζ0 / g u ^ 2))
      (volume.restrict unitDiscExterior) :=
    Integrable.mono' hBi (hmeas ζ0 hmem0).1 (hbd.mono fun u h => (h ζ0 hmem0).1)
  have hi1 : Integrable (fun u => R u * deriv g u ^ 2 * (1 / (g u - ζ0) ^ 2 - 1 / g u ^ 2))
      (volume.restrict unitDiscExterior) :=
    Integrable.mono' hBi (hmeas ζ0 hmem0).2.1 (hbd.mono fun u h => (h ζ0 hmem0).2.1)
  have hD1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le hδb
    (Filter.mem_of_superset hδb fun ζ hζ => (hmeas ζ hζ).1) hi0 (hmeas ζ0 hmem0).2.1
    (hbd.mono fun u h ζ hζ => (h ζ hζ).2.1) hBi (hder.mono fun u h ζ hζ => (h ζ hζ).1)
  have hD2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le hδb
    (Filter.mem_of_superset hδb fun ζ hζ => (hmeas ζ hζ).2.1) hi1 (hmeas ζ0 hmem0).2.2
    (hbd.mono fun u h ζ hζ => (h ζ hζ).2.2) hBi (hder.mono fun u h ζ hζ => (h ζ hζ).2)
  exact ⟨hi0, hD1.2, hD2.2, hD2.1⟩

/-- **(D1)** Interior pre-Schwarzian, pointwise on `𝔻`: `𝒜(f_t) = 𝒜(W_t) ∘ f · f' + 𝒜(f)`, `Ẇ'' = V̇'' + 2 ∂P`,
`V̇''(ζ) = -(2/π) ∫_{𝔻*} R g'²/(g - ζ)³` (push-forward by `g`), `∂_t̄ V = 0`.
At `κ = 0, a = 0` (`f = g = id`, `b = 1`): `𝖿_t = M_t ∘ normalizedSolution (t • extB m)`, so
`dz = ∂_z² ahVar (extB m) + 2 c₂` (`s4v_normalized_first_variation`; `M_t(ζ) = ζ + t c₂ ζ² + …` since the Model A
pole is `p_t ≈ 1/(t c₂)`, `γ̇ ≈ c₂ z²` at `∞` by D0), `dzbar = 2 c₂'`; consistent at `z = 0`. -/
theorem s3d_D1 {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∀ z ∈ unitDisc,
      Integrable (fun ζ => RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 /
        (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3) (volume.restrict unitDiscExterior) ∧
      DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0 ∧
      dz (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
        deriv (fsans (beltramiMul a κ)) z *
          ((-(2 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 /
              (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3) +
            2 * ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) /
              derivAtInfty (gsans (beltramiMul a κ))) ∧
      dzbar (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z) 0 =
        deriv (fsans (beltramiMul a κ)) z *
          (2 * ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
              ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ))) := by
  intro z hz
  have hd := delta0_bounds
  have haB : a ∈ LinfStarBall := mem_ball_zero_iff.2 (has.trans hd.2)
  have hμ : beltramiMul a (κ : LinfStar) ∈ LinfStarBall := bg_mul_mem_ball κ.2 haB
  have hpair := AppB.b8_welding_normalized_pair hμ
  obtain ⟨r, hr, ρ, hρ, R0, hR0, F, G, H, -, -, -, -, -, -, -, ht⟩ := s3g_D_ext hκ hκD ha has haL haD hm hmD
  have hV := (s3d_pair_variation hκ hκD ha has haL haD hm hmD).2.2.1
  have hD : IsOpen unitDisc := isOpen_ball
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hO : IsOpen {z : ℂ | ρ < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hDF : unitDisc ⊆ ball (0 : ℂ) R0 := ball_subset_ball hR0.le
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  -- the interior maps
  have hFt : ∀ t : ℂ, ‖t‖ < r →
      DifferentiableOn ℂ (fsans (beltramiMul (a + t • toLinf m) κ)) unitDisc := by
    intro t htr
    obtain ⟨⟨hFd, -, -, hFe⟩, -, -⟩ := ht t (mem_ball_zero_iff.2 htr)
    exact (hFd.mono hDF).congr fun w hw => (hFe hw).symm
  have h0 : a + (0 : ℂ) • toLinf m = a := by rw [zero_smul, add_zero]
  have hfD : DifferentiableOn ℂ (fsans (beltramiMul a κ)) unitDisc := by
    have h := hFt 0 (by rw [norm_zero]; exact hr)
    rwa [h0] at h
  have hf' : ∀ w ∈ unitDisc, deriv (fsans (beltramiMul a κ)) w ≠ 0 := by
    intro w hw
    obtain ⟨⟨-, -, hFd', hFe⟩, -, -⟩ := ht 0 (mem_ball_self hr)
    rw [h0] at hFe
    have heq : F 0 =ᶠ[𝓝 w] fsans (beltramiMul a κ) := Filter.mem_of_superset (hD.mem_nhds hw) fun v hv => hFe hv
    rw [← heq.deriv_eq]
    exact hFd' w (hDF hw)
  -- the exterior map
  obtain ⟨-, ⟨hGd, hGi, hGd', hGg⟩, -⟩ := ht 0 (mem_ball_self hr)
  simp only [zero_smul, add_zero] at hGg
  obtain ⟨hgD, hg'D, -, hg'G, -⟩ := d2e_basic hρ hGd hGi hGd' hGg
  have hk : ∀ u ∈ unitDiscExterior, 1 / 4 ≤ ‖gsans (beltramiMul a κ) u‖ := fun u hu => d2e_koebe hpair hu
  obtain ⟨c, hc, C, hfar⟩ := d2e_growth hpair
  have hMb : ∃ M : ℝ, ∀ u ∈ unitDiscExterior, ‖deriv (gsans (beltramiMul a κ)) u‖ ≤ M := by
    have hKc : IsCompact {u : ℂ | 1 ≤ ‖u‖ ∧ ‖u‖ ≤ 4} :=
      Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
        (isBounded_closedBall.subset fun u hu => mem_closedBall_zero_iff.2 hu.2)
    have hKO : {u : ℂ | 1 ≤ ‖u‖ ∧ ‖u‖ ≤ 4} ⊆ {z : ℂ | ρ < ‖z‖} := fun u hu => show ρ < ‖u‖ by linarith [hu.1]
    obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn ((hGd.deriv hO).continuousOn.mono hKO)
    refine ⟨max M1 C, fun u hu => ?_⟩
    by_cases h4 : ‖u‖ ≤ 4
    · rw [hg'G u hu]
      exact (hM1 u ⟨(hu : 1 < ‖u‖).le, h4⟩).trans (le_max_left _ _)
    · exact ((hfar u (le_of_lt (not_le.1 h4))).2).trans (le_max_right _ _)
  obtain ⟨M, hM⟩ := hMb
  have hRm : AEStronglyMeasurable (RnmFun (toLinf m) a) (volume.restrict unitDiscExterior) :=
    (bc_Rnm_memLp haB (toLinf m)).aestronglyMeasurable
  have hRb : ∀ᵐ u ∂(volume.restrict unitDiscExterior),
      ‖RnmFun (toLinf m) a u‖ ≤ (1 / (1 - ‖a‖ ^ 2)) * ‖toLinf m‖ :=
    bc_invFun_pullback_ae haB (bc_Rnm_integrand_bound haB (toLinf m))
  have hdisj : Disjoint (fsans (beltramiMul a κ) '' unitDisc) (gsans (beltramiMul a κ) '' unitDiscExterior) :=
    hpair.2.2.2.2.2
  -- the Model B variation and its derivatives
  obtain ⟨V0, hV0⟩ : ∃ V : ℂ → ℂ, ∀ ζ, V ζ = ∫ u in unitDiscExterior, RnmFun (toLinf m) a u *
      deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - ζ) - 1 / gsans (beltramiMul a κ) u -
        ζ / gsans (beltramiMul a κ) u ^ 2) := ⟨_, fun ζ => rfl⟩
  obtain ⟨V1, hV1⟩ : ∃ V : ℂ → ℂ, ∀ ζ, V ζ = ∫ u in unitDiscExterior, RnmFun (toLinf m) a u *
      deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - ζ) ^ 2 -
        1 / gsans (beltramiMul a κ) u ^ 2) := ⟨_, fun ζ => rfl⟩
  obtain ⟨V2, hV2⟩ : ∃ V : ℂ → ℂ, ∀ ζ, V ζ = ∫ u in unitDiscExterior, RnmFun (toLinf m) a u *
      deriv (gsans (beltramiMul a κ)) u ^ 2 * (2 / (gsans (beltramiMul a κ) u - ζ) ^ 3) := ⟨_, fun ζ => rfl⟩
  have hVd : ∀ w ∈ unitDisc, HasDerivAt V0 (V1 (fsans (beltramiMul a κ) w)) (fsans (beltramiMul a κ) w) ∧
      HasDerivAt V1 (V2 (fsans (beltramiMul a κ) w)) (fsans (beltramiMul a κ) w) ∧
      Integrable (fun u => RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
        (2 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) w) ^ 3)) (volume.restrict unitDiscExterior) := by
    intro w hw
    obtain ⟨δ, hδ, hsep⟩ := s3d1_sep hfD hf' hdisj hw
    obtain ⟨K, hK⟩ := s3d1_dom hδ hc hfar hM hk hsep
    obtain ⟨-, h1, h2, h3⟩ := s3d1_Vdot hδ hgD.continuousOn hg'D.continuousOn hRm hRb hk hsep hK
    have e0 : V0 = fun ζ => ∫ u in unitDiscExterior, RnmFun (toLinf m) a u *
        deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - ζ) - 1 / gsans (beltramiMul a κ) u -
          ζ / gsans (beltramiMul a κ) u ^ 2) := funext hV0
    have e1 : V1 = fun ζ => ∫ u in unitDiscExterior, RnmFun (toLinf m) a u *
        deriv (gsans (beltramiMul a κ)) u ^ 2 * (1 / (gsans (beltramiMul a κ) u - ζ) ^ 2 -
          1 / gsans (beltramiMul a κ) u ^ 2) := funext hV1
    refine ⟨?_, ?_, h3⟩
    · rw [e0, hV1]
      exact h1
    · rw [e1, hV2]
      exact h2
  -- the `t`- and `t̄`-variations of `f`
  obtain ⟨c2, hc2⟩ : ∃ c : ℂ, c = ((1 / π : ℂ) * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ /
      ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) := ⟨_, rfl⟩
  obtain ⟨c2', hc2'⟩ : ∃ c : ℂ, c = ((1 / π : ℂ) * ∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) *
      ζ ^ 2 / conj ζ ^ 2 / ((ζ + 1) * (ζ + I) * (ζ - 1))) / derivAtInfty (gsans (beltramiMul a κ)) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℂ → ℂ, X = fun w => -(1 / π : ℂ) * V0 (fsans (beltramiMul a κ) w) +
      c2 * fsans (beltramiMul a κ) w ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℂ → ℂ, Y = fun w => c2' * fsans (beltramiMul a κ) w ^ 2 := ⟨_, rfl⟩
  have hfa : ∀ w ∈ unitDisc, HasDerivAt (fsans (beltramiMul a κ)) (deriv (fsans (beltramiMul a κ)) w) w :=
    fun w hw => (hfD.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hf'a : ∀ w ∈ unitDisc, HasDerivAt (deriv (fsans (beltramiMul a κ)))
      (deriv (deriv (fsans (beltramiMul a κ))) w) w :=
    fun w hw => ((hfD.deriv hD).differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hV0f : ∀ w ∈ unitDisc, HasDerivAt (fun w => V0 (fsans (beltramiMul a κ) w))
      (V1 (fsans (beltramiMul a κ) w) * deriv (fsans (beltramiMul a κ)) w) w :=
    fun w hw => (hVd w hw).1.comp w (hfa w hw)
  have hV1f : ∀ w ∈ unitDisc, HasDerivAt (fun w => V1 (fsans (beltramiMul a κ) w))
      (V2 (fsans (beltramiMul a κ) w) * deriv (fsans (beltramiMul a κ)) w) w :=
    fun w hw => (hVd w hw).2.1.comp w (hfa w hw)
  have hXa : ∀ w ∈ unitDisc, HasDerivAt X (-(1 / π : ℂ) * (V1 (fsans (beltramiMul a κ) w) *
      deriv (fsans (beltramiMul a κ)) w) + c2 * (2 * fsans (beltramiMul a κ) w * deriv (fsans (beltramiMul a κ)) w)) w := by
    intro w hw
    rw [hX]
    exact ((hV0f w hw).const_mul _).add ((s3d1_sq (hfa w hw)).const_mul c2)
  have hYa : ∀ w ∈ unitDisc, HasDerivAt Y (c2' * (2 * fsans (beltramiMul a κ) w * deriv (fsans (beltramiMul a κ)) w))
      w := by
    intro w hw
    rw [hY]
    exact (s3d1_sq (hfa w hw)).const_mul c2'
  have hXd : DifferentiableOn ℂ X unitDisc := fun w hw => (hXa w hw).differentiableAt.differentiableWithinAt
  have hYd : DifferentiableOn ℂ Y unitDisc := fun w hw => (hYa w hw).differentiableAt.differentiableWithinAt
  have hX2 : deriv (deriv X) z = -(1 / π : ℂ) * (V2 (fsans (beltramiMul a κ) z) * deriv (fsans (beltramiMul a κ)) z *
      deriv (fsans (beltramiMul a κ)) z + V1 (fsans (beltramiMul a κ) z) * deriv (deriv (fsans (beltramiMul a κ))) z) +
      c2 * (2 * (deriv (fsans (beltramiMul a κ)) z * deriv (fsans (beltramiMul a κ)) z +
        fsans (beltramiMul a κ) z * deriv (deriv (fsans (beltramiMul a κ))) z)) := by
    have heq : deriv X =ᶠ[𝓝 z] fun w => -(1 / π : ℂ) * (V1 (fsans (beltramiMul a κ) w) *
        deriv (fsans (beltramiMul a κ)) w) + c2 * (2 * fsans (beltramiMul a κ) w * deriv (fsans (beltramiMul a κ)) w) :=
      Filter.mem_of_superset (hD.mem_nhds hz) fun w hw => (hXa w hw).deriv
    have h1 := ((hV1f z hz).mul (hf'a z hz)).const_mul (-(1 / π : ℂ))
    have h2 := (((hfa z hz).const_mul (2 : ℂ)).mul (hf'a z hz)).const_mul c2
    rw [heq.deriv_eq]
    convert (h1.add h2).deriv using 1
    ring
  have hY2 : deriv (deriv Y) z = c2' * (2 * (deriv (fsans (beltramiMul a κ)) z * deriv (fsans (beltramiMul a κ)) z +
      fsans (beltramiMul a κ) z * deriv (deriv (fsans (beltramiMul a κ))) z)) := by
    have heq : deriv Y =ᶠ[𝓝 z] fun w => c2' * (2 * fsans (beltramiMul a κ) w * deriv (fsans (beltramiMul a κ)) w) :=
      Filter.mem_of_superset (hD.mem_nhds hz) fun w hw => (hYa w hw).deriv
    have h2 := (((hfa z hz).const_mul (2 : ℂ)).mul (hf'a z hz)).const_mul c2'
    rw [heq.deriv_eq]
    convert h2.deriv using 1
    ring
  -- the uniform expansion of (V) near `z`
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = (1 - ‖z‖) / 8 := ⟨_, rfl⟩
  have hs0p : 0 < s0 := by rw [hs0]; linarith
  have hball : ball z (3 * (2 * s0)) ⊆ unitDisc := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    show w ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    have h1 := norm_le_norm_add_norm_sub' w z
    linarith
  have hball2 : ball z (3 * s0) ⊆ unitDisc := (ball_subset_ball (by linarith)).trans hball
  have hV2' : ∀ ε > 0, ∃ δ > 0, ∀ t : ℂ, ‖t‖ < δ → ∀ w ∈ closedBall z (2 * (2 * s0)),
      ‖fsans (beltramiMul (a + t • toLinf m) κ) w - fsans (beltramiMul a κ) w - (t * X w + conj t * Y w)‖ ≤
        ε * ‖t‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hV (‖z‖ + 4 * s0) (by rw [hs0]; linarith) ε hε
    refine ⟨δ, hδ, fun t htd w hw => ?_⟩
    have hw' : w ∈ closedBall (0 : ℂ) (‖z‖ + 4 * s0) := by
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_closedBall_zero_iff]
      have h1 := norm_le_norm_add_norm_sub' w z
      linarith
    have h3 := hb t htd w hw'
    rw [hX, hY]
    beta_reduce
    rw [hV0, hc2, hc2']
    exact h3
  -- Cauchy estimates
  have hd1 := s3d2u_step (G := fun t => fsans (beltramiMul (a + t • toLinf m) κ)) (G0 := fsans (beltramiMul a κ))
    (X := X) (Y := Y) (c := z) (s := 2 * s0) (r := r) (by positivity) hr (fun t htr => (hFt t htr).mono hball)
    (hfD.mono hball) (hXd.mono hball) (hYd.mono hball) hV2'
  have hd2 := s3d2u_step (G := fun t => deriv (fsans (beltramiMul (a + t • toLinf m) κ)))
    (G0 := deriv (fsans (beltramiMul a κ))) (X := deriv X) (Y := deriv Y) (c := z) (s := s0) (r := r) hs0p hr
    (fun t htr => ((hFt t htr).deriv hD).mono hball2) ((hfD.deriv hD).mono hball2) ((hXd.deriv hD).mono hball2)
    ((hYd.deriv hD).mono hball2) hd1
  obtain ⟨hF1z, hF1⟩ := s3d2u_hasFDeriv (F := fun t => deriv (fsans (beltramiMul (a + t • toLinf m) κ)) z)
    (c0 := deriv (fsans (beltramiMul a κ)) z) (A := deriv X z) (B := deriv Y z) (fun ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hd1 ε hε
      exact ⟨δ, hδ, fun t htd => hb t htd z (mem_closedBall_self (by positivity))⟩)
  obtain ⟨hF2z, hF2⟩ := s3d2u_hasFDeriv
    (F := fun t => deriv (deriv (fsans (beltramiMul (a + t • toLinf m) κ))) z)
    (c0 := deriv (deriv (fsans (beltramiMul a κ))) z) (A := deriv (deriv X) z) (B := deriv (deriv Y) z)
    (fun ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hd2 ε hε
      exact ⟨δ, hδ, fun t htd => hb t htd z (mem_closedBall_self hs0p.le)⟩)
  have hPS : HasFDerivAt (fun t : ℂ => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z)
      (((deriv (deriv X) z * deriv (fsans (beltramiMul a κ)) z - deriv X z * deriv (deriv (fsans (beltramiMul a κ))) z) /
          deriv (fsans (beltramiMul a κ)) z ^ 2) • (1 : ℂ →L[ℝ] ℂ) +
        ((deriv (deriv Y) z * deriv (fsans (beltramiMul a κ)) z - deriv Y z * deriv (deriv (fsans (beltramiMul a κ))) z) /
          deriv (fsans (beltramiMul a κ)) z ^ 2) • (conjCLE : ℂ →L[ℝ] ℂ)) 0 :=
    s3d2u_div hF1 hF2 hF1z hF2z (hf' z hz)
  obtain ⟨hdz, hdzb⟩ := s3d2u_dz hPS
  -- `V̇''(f(z)) = 2 ∫ R g'²/(g - f(z))³`
  have hV2i : V2 (fsans (beltramiMul a κ) z) = 2 * ∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ *
      deriv (gsans (beltramiMul a κ)) ζ ^ 2 / (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3 := by
    rw [hV2, ← integral_const_mul]
    congr 1
    funext u
    ring
  have hf0 := hf' z hz
  refine ⟨?_, hPS.differentiableAt, ?_, ?_⟩
  · have h := ((hVd z hz).2.2).const_mul (1 / 2 : ℂ)
    refine h.congr (Eventually.of_forall fun u => ?_)
    show 1 / 2 * (RnmFun (toLinf m) a u * deriv (gsans (beltramiMul a κ)) u ^ 2 *
      (2 / (gsans (beltramiMul a κ) u - fsans (beltramiMul a κ) z) ^ 3)) = _
    ring
  · rw [hdz, hX2, (hXa z hz).deriv, hV2i, hc2]
    generalize (∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ / ((ζ + 1) * (ζ + I) * (ζ - 1))) = IA
    generalize (∫ ζ in unitDiscExterior, RnmFun (toLinf m) a ζ * deriv (gsans (beltramiMul a κ)) ζ ^ 2 /
      (gsans (beltramiMul a κ) ζ - fsans (beltramiMul a κ) z) ^ 3) = IB
    field_simp
    ring
  · rw [hdzb, hY2, (hYa z hz).deriv, hc2']
    generalize (∫ ζ in unitDisc, conj (RnmFun (toLinf m) a (1 / conj ζ)) * ζ ^ 2 / conj ζ ^ 2 /
      ((ζ + 1) * (ζ + I) * (ζ - 1))) = IC
    field_simp
    ring

end TakhtajanTeo.Ch2
