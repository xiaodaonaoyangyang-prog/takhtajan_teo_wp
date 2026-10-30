import TakhtajanTeo.Ch2.S1_UnivalentFunctions

/-!
# Ch2 §1 completed originals: Theorem 1.6 (Becker–Pommerenke), `ab16_` helpers

The cycle `(i) ⇒ (iii) ⇒ (ii) ⇒ (i)` of Theorem 1.6.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-- `ε`–`r` form of a limit as `|z| → 1⁻`. -/
theorem ab16_tendsto_iff {g : ℂ → ℂ} :
    Tendsto g (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) ↔
      ∀ ε > 0, ∃ r < (1 : ℝ), ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → ‖g z‖ < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h1 := h ε hε
    rw [Filter.eventually_comap] at h1
    obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 h1
    refine ⟨l, hl, fun z hz1 hz2 => ?_⟩
    have h2 := hsub (show ‖z‖ ∈ Ioo l 1 from ⟨hz1, hz2⟩) z rfl
    simpa using h2
  · intro h ε hε
    obtain ⟨r, hr, hz⟩ := h ε hε
    rw [Filter.eventually_comap]
    filter_upwards [Ioo_mem_nhdsLT hr] with t ht z hzt
    have h2 := hz z (hzt ▸ ht.1) (hzt ▸ ht.2)
    simpa using h2

theorem ab16_norm_mul {r : ℝ} (hr : 0 ≤ 1 - r ^ 2) (w : ℂ) :
    ‖((1 : ℂ) - (r : ℂ) ^ 2) * w‖ = (1 - r ^ 2) * ‖w‖ := by
  have h : ((1 : ℂ) - (r : ℂ) ^ 2) = ((1 - r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

theorem ab16_norm_mul_sq {r : ℝ} (hr : 0 ≤ 1 - r ^ 2) (w : ℂ) :
    ‖(((1 : ℂ) - (r : ℂ) ^ 2) ^ 2) * w‖ = (1 - r ^ 2) ^ 2 * ‖w‖ := by
  have h : (((1 : ℂ) - (r : ℂ) ^ 2) ^ 2) = (((1 - r ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

/-- **(iii) ⇒ (ii)** of Theorem 1.6: `(1 - |z|²) 𝒜(f) → 0` gives `(1 - |z|²)² 𝒮(f) → 0` (Cauchy estimate for `𝒜'`
on the hyperbolic discs `|ζ - z| ≤ (1 - |z|)/2`). -/
theorem ab16_iii_imp_ii {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hA : Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  have hAd : DifferentiableOn ℂ (preSchwarzian f) unitDisc :=
    preSchwarzian_differentiableOn isOpen_ball hf hinj
  rw [ab16_tendsto_iff] at hA ⊢
  intro ε hε
  set ε' : ℝ := min 1 (ε / 17) with hε'
  have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'2 : ε' ≤ ε / 17 := min_le_right _ _
  obtain ⟨r0, hr0, hsm⟩ := hA ε' hε'0
  refine ⟨max ((2 * r0 + 1) / 3) 0, max_lt (by linarith) one_pos, fun z hz1 hz2 => ?_⟩
  have hzr : (2 * r0 + 1) / 3 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz1
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hzr0 : r0 < ‖z‖ := by linarith
  set ρ : ℝ := (1 - ‖z‖) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hsub : closedBall z ρ ⊆ unitDisc := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    have h1 := norm_sub_norm_le w z
    rw [unitDisc, mem_ball_zero_iff]
    linarith
  have hdc : DiffContOnCl ℂ (preSchwarzian f) (ball z ρ) :=
    ⟨hAd.mono (ball_subset_closedBall.trans hsub), by
      rw [closure_ball _ hρ0.ne']
      exact hAd.continuousOn.mono hsub⟩
  have hC : ∀ ζ ∈ sphere z ρ, ‖preSchwarzian f ζ‖ ≤ 2 * ε' / (1 - ‖z‖) := by
    intro ζ hζ
    rw [mem_sphere_iff_norm] at hζ
    have h1 := norm_sub_norm_le ζ z
    have h2 := norm_sub_norm_le z ζ
    rw [norm_sub_rev] at h2
    have hζ1 : ‖ζ‖ < 1 := by linarith
    have hζr : r0 < ‖ζ‖ := by linarith
    have hs := hsm ζ hζr hζ1
    have hnn : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    rw [ab16_norm_mul hnn] at hs
    have hlow : (1 - ‖z‖) / 2 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    have ht : 0 < 1 - ‖z‖ := by linarith
    rw [le_div_iff₀ ht]
    have hAn := norm_nonneg (preSchwarzian f ζ)
    nlinarith
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hdc hC
  have ht : 0 < 1 - ‖z‖ := by linarith
  have hD : ‖deriv (preSchwarzian f) z‖ ≤ 4 * ε' / (1 - ‖z‖) ^ 2 := by
    refine hcau.trans (le_of_eq ?_)
    rw [hρ]
    field_simp
    ring
  have hzs : ‖(1 - ‖z‖ ^ 2 : ℂ) * preSchwarzian f z‖ < ε' := hsm z hzr0 hz2
  have hnn : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  have hzs' : (1 - ‖z‖ ^ 2) * ‖preSchwarzian f z‖ < ε' := by
    rwa [ab16_norm_mul hnn] at hzs
  have eS : schwarzianHol f z =
      deriv (preSchwarzian f) z - (1 / 2) * preSchwarzian f z ^ 2 := rfl
  rw [ab16_norm_mul_sq hnn, eS]
  have hnS : ‖deriv (preSchwarzian f) z - (1 / 2) * preSchwarzian f z ^ 2‖ ≤
      ‖deriv (preSchwarzian f) z‖ + (1 / 2) * ‖preSchwarzian f z‖ ^ 2 := by
    calc _ ≤ ‖deriv (preSchwarzian f) z‖ + ‖(1 / 2 : ℂ) * preSchwarzian f z ^ 2‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_pow]; norm_num
  have hq : (1 - ‖z‖ ^ 2) ^ 2 ≤ 4 * (1 - ‖z‖) ^ 2 := by nlinarith
  have h1 : (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (preSchwarzian f) z‖ ≤ 16 * ε' := by
    calc (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (preSchwarzian f) z‖
        ≤ (4 * (1 - ‖z‖) ^ 2) * (4 * ε' / (1 - ‖z‖) ^ 2) :=
          mul_le_mul hq hD (norm_nonneg _) (by positivity)
      _ = 16 * ε' := by field_simp; ring
  have h2 : (1 - ‖z‖ ^ 2) ^ 2 * ((1 / 2) * ‖preSchwarzian f z‖ ^ 2) ≤ ε' / 2 := by
    have hb := norm_nonneg (preSchwarzian f z)
    have : ((1 - ‖z‖ ^ 2) * ‖preSchwarzian f z‖) ^ 2 ≤ ε' ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hzs'.le
    nlinarith
  calc (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (preSchwarzian f) z - 1 / 2 * preSchwarzian f z ^ 2‖
      ≤ (1 - ‖z‖ ^ 2) ^ 2 * (‖deriv (preSchwarzian f) z‖ + (1 / 2) * ‖preSchwarzian f z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnS (sq_nonneg _)
    _ = (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv (preSchwarzian f) z‖ +
          (1 - ‖z‖ ^ 2) ^ 2 * ((1 / 2) * ‖preSchwarzian f z‖ ^ 2) := by ring
    _ < ε := by linarith

/-! ### P0: `(ii) ⇒ (iii)` of Theorem 1.6 by a Riccati argument along radii -/

/-- One backward step for `X = (1 - t²)(4 - b)/b`: if `b` is bounded away from `0` and `‖(4 - b)/b‖ ≤ V0 + 1`
on `[t, t₂]`, then `‖4 - b t‖ ≤ y ‖b t‖` with the explicit `y`. -/
theorem ab16_stab_step {b D τ : ℝ → ℂ} {t1 t2 ε V0 : ℝ} (ht1 : 0 ≤ t1) (ht2 : t2 < 1)
    (hd : ∀ t ∈ Icc t1 t2, HasDerivAt b (D t) t)
    (hode : ∀ t ∈ Icc t1 t2,
      ((1 - t ^ 2 : ℝ) : ℂ) * D t = (1 / 2) * b t ^ 2 - 2 * (t : ℂ) * b t + τ t)
    (hτ : ∀ t ∈ Icc t1 t2, ‖τ t‖ ≤ ε) (hε : 0 ≤ ε) (hV0 : 0 ≤ V0)
    (hend : ‖4 - b t2‖ ≤ V0 * ‖b t2‖) {t : ℝ} (ht : t ∈ Icc t1 t2)
    (hP : ∀ s ∈ Icc t t2, ‖4 - b s‖ ≤ (V0 + 1) * ‖b s‖) :
    ‖4 - b t‖ ≤ (V0 * (1 - t2 ^ 2) / (1 - t ^ 2) +
      (2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2)) * ‖b t‖ := by
  have ht0 : 0 ≤ t := le_trans ht1 ht.1
  have ht1' : t < 1 := lt_of_le_of_lt ht.2 ht2
  have hbne : ∀ s ∈ Icc t t2, b s ≠ 0 := fun s hs h0 => by
    have := hP s hs
    rw [h0, norm_zero, mul_zero] at this
    norm_num at this
  have hlow : ∀ s ∈ Icc t t2, 4 / (V0 + 2) ≤ ‖b s‖ := by
    intro s hs
    have h1 := hP s hs
    have h2 : (4 : ℝ) ≤ ‖4 - b s‖ + ‖b s‖ := by
      calc (4 : ℝ) = ‖(4 : ℂ)‖ := by norm_num
        _ = ‖(4 - b s) + b s‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (b s)]
  set X : ℝ → ℂ := fun s => ((1 - s ^ 2 : ℝ) : ℂ) * ((4 - b s) / b s) with hX
  have hXd : ∀ s ∈ Icc t t2,
      HasDerivAt X (-(2 * ((1 - s : ℝ) : ℂ)) - 4 * τ s / b s ^ 2) s := by
    intro s hs
    have hs' : s ∈ Icc t1 t2 := ⟨le_trans ht.1 hs.1, hs.2⟩
    have hsl1 : s < 1 := lt_of_le_of_lt hs.2 ht2
    have hb1 := hd s hs'
    have h1r : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
      have := (hasDerivAt_pow 2 s).const_sub (1 : ℝ)
      simpa using this
    have h1 : HasDerivAt (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ)) (((-(2 * s) : ℝ)) : ℂ) s :=
      h1r.ofReal_comp
    have h2 : HasDerivAt (fun s => (4 - b s) / b s)
        (((0 - D s) * b s - (4 - b s) * D s) / b s ^ 2) s :=
      ((hasDerivAt_const s (4 : ℂ)).sub hb1).div hb1 (hbne s hs)
    have h3 := h1.mul h2
    have hD : D s = ((1 / 2) * b s ^ 2 - 2 * (s : ℂ) * b s + τ s) / ((1 - s ^ 2 : ℝ) : ℂ) := by
      rw [eq_div_iff, mul_comm]
      · exact hode s hs'
      · have : (1 - s ^ 2 : ℝ) ≠ 0 := by nlinarith [hs.1, ht0]
        exact_mod_cast this
    have hne : ((1 - s ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (1 - s ^ 2 : ℝ) ≠ 0 := by nlinarith [hs.1, ht0]
      exact_mod_cast this
    have hbs := hbne s hs
    have hne' : (1 - (s : ℂ) ^ 2) ≠ 0 := by
      have h0 := hne
      push_cast at h0
      exact h0
    convert h3 using 1
    rw [hD]
    push_cast
    field_simp
    ring
  set C : ℝ := 2 * (1 - t) + ε / 4 * (V0 + 2) ^ 2 with hC
  have hbound : ∀ s ∈ Ico t t2, ‖-(2 * ((1 - s : ℝ) : ℂ)) - 4 * τ s / b s ^ 2‖ ≤ C := by
    intro s hs
    have hs' : s ∈ Icc t1 t2 := ⟨le_trans ht.1 hs.1, hs.2.le⟩
    have hsI : s ∈ Icc t t2 := ⟨hs.1, hs.2.le⟩
    have hbl := hlow s hsI
    have hV2 : 0 < V0 + 2 := by linarith
    have hb0 : 0 < ‖b s‖ := norm_pos_iff.2 (hbne s hsI)
    have hsl1 : s < 1 := lt_trans hs.2 ht2
    calc ‖-(2 * ((1 - s : ℝ) : ℂ)) - 4 * τ s / b s ^ 2‖
        ≤ ‖-(2 * ((1 - s : ℝ) : ℂ))‖ + ‖4 * τ s / b s ^ 2‖ := norm_sub_le _ _
      _ = 2 * (1 - s) + 4 * ‖τ s‖ / ‖b s‖ ^ 2 := by
          have h0 : (0 : ℝ) ≤ 1 - s := by linarith
          have e : ‖((1 - s : ℝ) : ℂ)‖ = 1 - s := by
            rw [Complex.norm_real, Real.norm_of_nonneg h0]
          rw [norm_neg, norm_mul, e, norm_div, norm_mul, norm_pow]
          norm_num
      _ ≤ 2 * (1 - t) + ε / 4 * (V0 + 2) ^ 2 := by
          have h1 : 1 - s ≤ 1 - t := by linarith [hs.1]
          have h2 : 4 * ‖τ s‖ / ‖b s‖ ^ 2 ≤ ε / 4 * (V0 + 2) ^ 2 := by
            have hb2 : (4 / (V0 + 2)) ^ 2 ≤ ‖b s‖ ^ 2 := pow_le_pow_left₀ (by positivity) hbl 2
            have hpos : 0 < (4 / (V0 + 2)) ^ 2 := by positivity
            calc 4 * ‖τ s‖ / ‖b s‖ ^ 2 ≤ 4 * ε / (4 / (V0 + 2)) ^ 2 := by
                  apply div_le_div₀ (by positivity) (by nlinarith [hτ s hs']) hpos hb2
              _ = ε / 4 * (V0 + 2) ^ 2 := by field_simp
          linarith
  have hmvt := (norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hXd s hs).hasDerivWithinAt) hbound) t2 ⟨ht.2, le_rfl⟩
  -- the value at `t₂`
  have hXt2 : ‖X t2‖ ≤ (1 - t2 ^ 2) * V0 := by
    have hb2 := hbne t2 ⟨ht.2, le_rfl⟩
    have hpos : 0 < ‖b t2‖ := norm_pos_iff.2 hb2
    have h1 : 0 ≤ 1 - t2 ^ 2 := by nlinarith [ht.2, ht0]
    simp only [hX]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg h1]
    apply mul_le_mul_of_nonneg_left _ h1
    rw [div_le_iff₀ hpos]; exact hend
  have hX0 : ‖X t‖ = (1 - t ^ 2) * (‖4 - b t‖ / ‖b t‖) := by
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith
    simp only [hX]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg h1]
  have hbt : 0 < ‖b t‖ := norm_pos_iff.2 (hbne t ⟨le_rfl, ht.2⟩)
  have hden : 0 < 1 - t ^ 2 := by nlinarith
  have hsum : ‖X t‖ ≤ (1 - t2 ^ 2) * V0 + C * (t2 - t) := by
    have := norm_sub_norm_le (X t) (X t2)
    rw [norm_sub_rev] at this
    linarith [hmvt, norm_nonneg (X t2)]
  rw [hX0] at hsum
  have hCt : C * (t2 - t) / (1 - t ^ 2) ≤ 2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2 := by
    rw [div_le_iff₀ hden]
    have h1 : t2 - t ≤ 1 - t := by linarith
    have h2 : 0 ≤ C := by
      rw [hC]; have : 0 ≤ 1 - t := by linarith
      positivity
    have h3 : 0 ≤ 1 - t := by linarith
    have h4 : (1 - t) ≤ (1 - t1) := by linarith [ht.1]
    have e : (1 - t ^ 2) = (1 - t) * (1 + t) := by ring
    calc C * (t2 - t) ≤ C * (1 - t) := mul_le_mul_of_nonneg_left h1 h2
      _ = (2 * (1 - t) + ε / 4 * (V0 + 2) ^ 2) * (1 - t) := by rw [hC]
      _ ≤ (2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2) * ((1 - t) * (1 + t)) := by
          have : ε / 4 * (V0 + 2) ^ 2 ≥ 0 := by positivity
          nlinarith [mul_nonneg h3 ht0, mul_nonneg h3 (sub_nonneg.2 h4)]
      _ = _ := by rw [e]
  have key : ‖4 - b t‖ / ‖b t‖ ≤ V0 * (1 - t2 ^ 2) / (1 - t ^ 2) +
      (2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2) := by
    have h5 : ‖4 - b t‖ / ‖b t‖ ≤ ((1 - t2 ^ 2) * V0 + C * (t2 - t)) / (1 - t ^ 2) := by
      rw [le_div_iff₀ hden, mul_comm]; exact hsum
    calc _ ≤ _ := h5
      _ = V0 * (1 - t2 ^ 2) / (1 - t ^ 2) + C * (t2 - t) / (1 - t ^ 2) := by ring
      _ ≤ _ := by linarith
  rw [div_le_iff₀ hbt] at key
  exact key

/-- Backward stability of the Riccati equation `(1 - t²) b' = ½ b² - 2 t b + τ` near the repelling point `b = 4`:
if `‖(4 - b)/b‖ ≤ V0` at `t₂` and `|τ| ≤ ε` is small, then `‖(4 - b)/b‖` stays small on `[t₁, t₂]` as long as
`V0 (1 - t₂²)/(1 - t²)` is small. -/
theorem ab16_stab {b D τ : ℝ → ℂ} {t1 t2 ε V0 : ℝ} (ht12 : t1 ≤ t2) (ht2 : t2 < 1) (ht1 : 0 ≤ t1)
    (hd : ∀ t ∈ Icc t1 t2, HasDerivAt b (D t) t)
    (hode : ∀ t ∈ Icc t1 t2,
      ((1 - t ^ 2 : ℝ) : ℂ) * D t = (1 / 2) * b t ^ 2 - 2 * (t : ℂ) * b t + τ t)
    (hτ : ∀ t ∈ Icc t1 t2, ‖τ t‖ ≤ ε) (hε : 0 ≤ ε) (hV0 : 0 ≤ V0)
    (hend : ‖4 - b t2‖ ≤ V0 * ‖b t2‖)
    (hsmall : 2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2 < 1) :
    ∀ t ∈ Icc t1 t2, ‖4 - b t‖ ≤
      (V0 * (1 - t2 ^ 2) / (1 - t ^ 2) + (2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2)) * ‖b t‖ := by
  set rest : ℝ := 2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2 with hrest
  have hbc : ContinuousOn b (Icc t1 t2) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hbcat : ∀ t ∈ Icc t1 t2, ContinuousAt b t := fun t ht => (hd t ht).continuousAt
  set Sset : Set ℝ := {t | t ∈ Icc t1 t2 ∧ ∀ s ∈ Icc t t2, ‖4 - b s‖ ≤ (V0 + 1) * ‖b s‖} with hSset
  have ht2S : t2 ∈ Sset := by
    refine ⟨⟨ht12, le_rfl⟩, fun s hs => ?_⟩
    have : s = t2 := le_antisymm hs.2 hs.1
    subst this
    nlinarith [hend, norm_nonneg (b s)]
  have hne : Sset.Nonempty := ⟨t2, ht2S⟩
  have hbdd : BddBelow Sset := ⟨t1, fun t ht => ht.1.1⟩
  set T := sInf Sset with hT
  have hT1 : t1 ≤ T := le_csInf hne (fun t ht => ht.1.1)
  have hTt2 : T ≤ t2 := csInf_le hbdd ht2S
  have hPopen : ∀ s ∈ Ioc T t2, ‖4 - b s‖ ≤ (V0 + 1) * ‖b s‖ := by
    intro s hs
    obtain ⟨u, huS, hu⟩ := exists_lt_of_csInf_lt hne hs.1
    exact huS.2 s ⟨hu.le, hs.2⟩
  have hPT : ‖4 - b T‖ ≤ (V0 + 1) * ‖b T‖ := by
    rcases eq_or_lt_of_le hTt2 with h | h
    · rw [h]
      exact ht2S.2 t2 ⟨le_rfl, le_rfl⟩
    · have hcl : T ∈ closure (Ioc T t2) := by
        rw [closure_Ioc h.ne]
        exact ⟨le_rfl, h.le⟩
      have hcw : ContinuousWithinAt b (Ioc T t2) T :=
        (hbc T ⟨hT1, hTt2⟩).mono (fun s hs => ⟨le_trans hT1 hs.1.le, hs.2⟩)
      have hf1 : ContinuousWithinAt (fun s => ‖4 - b s‖) (Ioc T t2) T :=
        (continuousWithinAt_const.sub hcw).norm
      have hf2 : ContinuousWithinAt (fun s => (V0 + 1) * ‖b s‖) (Ioc T t2) T :=
        continuousWithinAt_const.mul hcw.norm
      exact ContinuousWithinAt.closure_le hcl hf1 hf2 hPopen
  have hTS : T ∈ Sset := by
    refine ⟨⟨hT1, hTt2⟩, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hPT
    · exact hPopen s ⟨h, hs.2⟩
  have hTeq : T = t1 := by
    by_contra hne1
    have hT1' : t1 < T := lt_of_le_of_ne hT1 (Ne.symm hne1)
    have hTmem : T ∈ Icc t1 t2 := ⟨hT1, hTt2⟩
    have hstep := ab16_stab_step ht1 ht2 hd hode hτ hε hV0 hend hTmem hTS.2
    have hT0 : 0 ≤ T := le_trans ht1 hT1
    have hTl1 : T < 1 := lt_of_le_of_lt hTt2 ht2
    have hbT : b T ≠ 0 := by
      intro h0
      have := hPT
      rw [h0, norm_zero, mul_zero] at this
      norm_num at this
    have hbTp : 0 < ‖b T‖ := norm_pos_iff.2 hbT
    have hden : 0 < 1 - T ^ 2 := by nlinarith
    have hy : V0 * (1 - t2 ^ 2) / (1 - T ^ 2) ≤ V0 := by
      rw [div_le_iff₀ hden]
      have : 1 - t2 ^ 2 ≤ 1 - T ^ 2 := by nlinarith
      nlinarith
    have hstrict : ‖4 - b T‖ < (V0 + 1) * ‖b T‖ := by
      calc ‖4 - b T‖ ≤ (V0 * (1 - t2 ^ 2) / (1 - T ^ 2) + rest) * ‖b T‖ := hstep
        _ ≤ (V0 + rest) * ‖b T‖ := by gcongr
        _ < (V0 + 1) * ‖b T‖ := by
          apply mul_lt_mul_of_pos_right _ hbTp
          linarith
    have hg : ContinuousAt (fun s => (V0 + 1) * ‖b s‖ - ‖4 - b s‖) T :=
      (continuousAt_const.mul (hbcat T hTmem).norm).sub (continuousAt_const.sub (hbcat T hTmem)).norm
    have hgpos : ∀ᶠ s in 𝓝 T, 0 < (V0 + 1) * ‖b s‖ - ‖4 - b s‖ :=
      hg.eventually (lt_mem_nhds (by linarith))
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hgpos
    set δ' : ℝ := min (η / 2) ((T - t1) / 2) with hδ'
    have hδ'0 : 0 < δ' := lt_min (by linarith) (by linarith)
    have hmemS : T - δ' ∈ Sset := by
      refine ⟨⟨by have := min_le_right (η / 2) ((T - t1) / 2); linarith, by linarith⟩, fun s hs => ?_⟩
      rcases le_or_gt T s with h | h
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [← h']; exact hPT
        · exact hPopen s ⟨h', hs.2⟩
      · have hdist : dist s T < η := by
          rw [Real.dist_eq, abs_lt]
          have := min_le_left (η / 2) ((T - t1) / 2)
          constructor <;> linarith [hs.1]
        have := hball hdist
        linarith
    have := csInf_le hbdd hmemS
    linarith
  intro t ht
  refine ab16_stab_step ht1 ht2 hd hode hτ hε hV0 hend ht (fun s hs => ?_)
  exact hTS.2 s ⟨by rw [hTeq]; exact le_trans ht.1 hs.1, hs.2⟩

theorem ab16_radial_ode {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hF1 : ∀ z ∈ unitDisc, deriv f z ≠ 0) {ζ0 : ℂ} (hζ : ‖ζ0‖ = 1) :
    ∃ D : ℝ → ℂ, ∀ t : ℝ, 0 ≤ t → t < 1 →
      HasDerivAt (fun t : ℝ => ((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0))) (D t) t ∧
      ((1 - t ^ 2 : ℝ) : ℂ) * D t =
        (1 / 2) * (((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0))) ^ 2 -
          2 * (t : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0))) +
          ((1 - t ^ 2 : ℝ) : ℂ) ^ 2 * ζ0 ^ 2 * schwarzianHol f ((t : ℂ) * ζ0) := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hf' : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv hD
  have hf'' : DifferentiableOn ℂ (deriv (deriv f)) unitDisc := hf'.deriv hD
  have hAd : DifferentiableOn ℂ (preSchwarzian f) unitDisc := hf''.div hf' hF1
  refine ⟨fun t => (((-(2 * t) : ℝ)) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0)) +
    ((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * ((1 * ζ0) • deriv (preSchwarzian f) ((t : ℂ) * ζ0))), fun t ht0 ht1 => ?_⟩
  have hw : (t : ℂ) * ζ0 ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hζ, Complex.norm_real, mul_one,
      Real.norm_of_nonneg ht0]
    exact ht1
  have hAt : HasDerivAt (preSchwarzian f) (deriv (preSchwarzian f) ((t : ℂ) * ζ0)) ((t : ℂ) * ζ0) :=
    (hAd.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hin : HasDerivAt (fun y : ℝ => (y : ℂ) * ζ0) (1 * ζ0) t := by
    have : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    exact this.mul_const ζ0
  have hcomp := hAt.scomp t hin
  have h1r : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_sub (1 : ℝ)
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ)) (((-(2 * t) : ℝ)) : ℂ) t :=
    h1r.ofReal_comp
  have h2 := h1.mul (hcomp.const_mul ζ0)
  have hsch : schwarzianHol f ((t : ℂ) * ζ0) =
      deriv (preSchwarzian f) ((t : ℂ) * ζ0) - (1 / 2) * preSchwarzian f ((t : ℂ) * ζ0) ^ 2 := rfl
  refine ⟨h2, ?_⟩
  rw [hsch]
  simp only [smul_eq_mul]
  have hz2 : ζ0 ^ 2 = ζ0 * ζ0 := by ring
  push_cast
  ring

theorem ab16_radial_growth {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hF1 : ∀ z ∈ unitDisc, deriv f z ≠ 0) {ζ0 : ℂ} (hζ : ‖ζ0‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (fun t : ℝ => ‖deriv f ((t : ℂ) * ζ0)‖ ^ 2 * ((1 - t) ^ 3 * (1 + t)))
      (‖deriv f ((t : ℂ) * ζ0)‖ ^ 2 * (1 - t) ^ 2 *
        (2 * (((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0))).re - 2 - 4 * t)) t := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hf' : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv hD
  have hw : (t : ℂ) * ζ0 ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hζ, Complex.norm_real, mul_one,
      Real.norm_of_nonneg ht0]
    exact ht1
  have hAt : HasDerivAt (deriv f) (deriv (deriv f) ((t : ℂ) * ζ0)) ((t : ℂ) * ζ0) :=
    (hf'.differentiableAt (hD.mem_nhds hw)).hasDerivAt
  have hin : HasDerivAt (fun y : ℝ => (y : ℂ) * ζ0) (1 * ζ0) t := by
    have : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    exact this.mul_const ζ0
  have hcomp := hAt.scomp t hin
  have hn := hcomp.norm_sq
  have hp : HasDerivAt (fun s : ℝ => (1 - s) ^ 3 * (1 + s)) (-(1 - t) ^ 2 * (2 + 4 * t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (1 - s) ^ 3) (-3 * (1 - t) ^ 2) t := by
      have hh : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_id' t).const_sub (1 : ℝ)
      have h := (hasDerivAt_pow 3 (1 - t)).comp t hh
      exact h.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    have := h1.mul h2
    convert this using 1
    ring
  have h3 := hn.mul hp
  refine h3.congr_deriv ?_
  have hF : deriv f ((t : ℂ) * ζ0) ≠ 0 := hF1 _ hw
  have hrel : deriv (deriv f) ((t : ℂ) * ζ0) =
      preSchwarzian f ((t : ℂ) * ζ0) * deriv f ((t : ℂ) * ζ0) := by
    unfold preSchwarzian
    field_simp
  rw [hrel]
  simp only [smul_eq_mul, Complex.inner, Function.comp_apply]
  set g := deriv f ((t : ℂ) * ζ0) with hg
  set A := preSchwarzian f ((t : ℂ) * ζ0) with hA
  have e1 : (1 * ζ0 * (A * g) * (starRingEnd ℂ) g) =
      (ζ0 * A) * ((Complex.normSq g : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e1, Complex.re_mul_ofReal]
  have e2 : ((((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * A))).re = (1 - t ^ 2) * (ζ0 * A).re := by
    rw [Complex.re_ofReal_mul]
  rw [e2, Complex.sq_norm]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- **(ii) ⇒ (iii)** of Theorem 1.6 (Becker–Pommerenke), for locally univalent bounded `f` (no Jordan hypothesis is
needed): a Riccati argument along radii.  Boundedness is used only through the Cauchy bound
`(1 - |z|²)|f'(z)| ≤ 4M`, which excludes the alternative `(1 - |z|²) 𝒜(f) ≈ 4` (a pole at the boundary point). -/
theorem ab16_ii_imp_iii {f : ℂ → ℂ} {M : ℝ} (hf : DifferentiableOn ℂ f unitDisc)
    (hF1 : ∀ z ∈ unitDisc, deriv f z ≠ 0) (hM : ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    (hS : Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) : ℂ) * preSchwarzian f z)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self one_pos))
  have hcauchy : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖deriv f z‖ ≤ 4 * M := by
    intro z hz
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    set ρ : ℝ := (1 - ‖z‖) / 2 with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; linarith
    have hsub : closedBall z ρ ⊆ unitDisc := by
      intro w hw
      rw [mem_closedBall_iff_norm] at hw
      have := norm_sub_norm_le w z
      rw [unitDisc, mem_ball_zero_iff]
      linarith
    have hdc : DiffContOnCl ℂ f (ball z ρ) :=
      ⟨hf.mono (ball_subset_closedBall.trans hsub), by
        rw [closure_ball _ hρ0.ne']
        exact hf.continuousOn.mono hsub⟩
    have hC : ∀ w ∈ sphere z ρ, ‖f w‖ ≤ M := fun w hw =>
      hM w (hsub (sphere_subset_closedBall hw))
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ0 hdc hC
    have hnn : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h1s : 1 - ‖z‖ ≠ 0 := by linarith
    calc (1 - ‖z‖ ^ 2) * ‖deriv f z‖ ≤ (1 - ‖z‖ ^ 2) * (M / ρ) :=
          mul_le_mul_of_nonneg_left hc hnn
      _ = 2 * (1 + ‖z‖) * M := by
          rw [hρ]
          field_simp
          ring
      _ ≤ 4 * M := by nlinarith [norm_nonneg z]
  rw [ab16_tendsto_iff] at hS ⊢
  intro δ hδ
  by_contra hcon
  push_neg at hcon
  set V0 : ℝ := 4 / δ + 1 with hV0
  have hV01 : 1 ≤ V0 := by
    have : 0 < 4 / δ := by positivity
    rw [hV0]; linarith
  set ε : ℝ := 1 / (8 * (V0 + 2) ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  have hεV : ε / 4 * (V0 + 2) ^ 2 = 1 / 32 := by
    rw [hε]
    have : (V0 + 2) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  obtain ⟨r0, hr0, hsm⟩ := hS ε hε0
  set t1 : ℝ := max ((r0 + 1) / 2) (63 / 64) with ht1
  have ht1lt : t1 < 1 := max_lt (by linarith) (by norm_num)
  have ht1ge : 63 / 64 ≤ t1 := le_max_right _ _
  have ht1r0 : r0 < t1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ht10 : 0 < t1 := by linarith
  have hsph : sphere (0 : ℂ) t1 ⊆ unitDisc := fun w hw => by
    rw [unitDisc, mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hw]
    exact ht1lt
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : ℂ) t1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 ht10.le)
    (((hf.deriv hD).continuousOn.mono hsph).norm)
  set m1 : ℝ := ‖deriv f x0‖ with hm1
  have hm1pos : 0 < m1 := norm_pos_iff.2 (hF1 x0 (hsph hx0))
  have h1t1 : 0 < 1 - t1 := by linarith
  set c1 : ℝ := m1 ^ 2 * ((1 - t1) ^ 3 * (1 + t1)) with hc1
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  set Mp : ℝ := M + 1 with hMp
  have hMp0 : 0 < Mp := by rw [hMp]; linarith
  have h1t12 : 0 < 1 - t1 ^ 2 := by nlinarith
  set η : ℝ := min (c1 / (1024 * Mp ^ 2 * V0)) (min ((1 - t1 ^ 2) / (32 * V0)) (1 / 2)) with hη
  have hη0 : 0 < η := by
    rw [hη]
    refine lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hη1 : η ≤ c1 / (1024 * Mp ^ 2 * V0) := min_le_left _ _
  have hη2 : η ≤ (1 - t1 ^ 2) / (32 * V0) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη3 : η ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨z, hz1, hz2, hzδ⟩ := hcon (max t1 (1 - η)) (max_lt ht1lt (by linarith))
  set t2 : ℝ := ‖z‖ with ht2
  have ht2t1 : t1 < t2 := lt_of_le_of_lt (le_max_left _ _) hz1
  have ht2η : 1 - η < t2 := lt_of_le_of_lt (le_max_right _ _) hz1
  have ht2lt : t2 < 1 := hz2
  have ht20 : 0 < t2 := by linarith
  have h1t2 : 1 - t2 ^ 2 ≤ 2 * η := by nlinarith
  have h1t2pos : 0 < 1 - t2 ^ 2 := by nlinarith
  -- the radius
  set ζ0 : ℂ := ((t2 : ℝ) : ℂ)⁻¹ * z with hζ0
  have hζ : ‖ζ0‖ = 1 := by
    rw [hζ0, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht20.le, ← ht2]
    exact inv_mul_cancel₀ ht20.ne'
  have hzζ : (t2 : ℂ) * ζ0 = z := by
    rw [hζ0, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ht20.ne'), one_mul]
  obtain ⟨D, hDd⟩ := ab16_radial_ode hf hF1 hζ
  set b : ℝ → ℂ := fun t => ((1 - t ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f ((t : ℂ) * ζ0)) with hb
  set τ : ℝ → ℂ := fun t => ((1 - t ^ 2 : ℝ) : ℂ) ^ 2 * ζ0 ^ 2 * schwarzianHol f ((t : ℂ) * ζ0) with hτdef
  have hnorm_w : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ) * ζ0‖ = t := fun t ht => by
    rw [norm_mul, hζ, Complex.norm_real, mul_one, Real.norm_of_nonneg ht]
  have hτb : ∀ t ∈ Icc t1 t2, ‖τ t‖ ≤ ε := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ht1' : t < 1 := lt_of_le_of_lt ht.2 ht2lt
    have hw : ‖(t : ℂ) * ζ0‖ = t := hnorm_w t ht0
    have := hsm ((t : ℂ) * ζ0) (by rw [hw]; linarith [ht.1]) (by rw [hw]; exact ht1')
    rw [hw] at this
    have e : τ t = ((1 - (t : ℂ) ^ 2) ^ 2 * schwarzianHol f ((t : ℂ) * ζ0)) * ζ0 ^ 2 := by
      simp only [hτdef]
      push_cast
      ring
    rw [e, norm_mul, norm_pow, hζ, one_pow, mul_one]
    exact this.le
  have hbt2 : b t2 = ((1 - t2 ^ 2 : ℝ) : ℂ) * (ζ0 * preSchwarzian f z) := by
    simp only [hb]; rw [hzζ]
  have hnb : δ ≤ ‖b t2‖ := by
    rw [hbt2, norm_mul, norm_mul, hζ, one_mul, Complex.norm_real,
      Real.norm_of_nonneg h1t2pos.le]
    have h := hzδ
    have e : ((1 - (‖z‖ : ℂ) ^ 2) * preSchwarzian f z) =
        ((1 - t2 ^ 2 : ℝ) : ℂ) * preSchwarzian f z := by
      simp only [ht2]; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1t2pos.le] at h
    exact h
  have hend : ‖4 - b t2‖ ≤ V0 * ‖b t2‖ := by
    have h1 : ‖4 - b t2‖ ≤ 4 + ‖b t2‖ := by
      calc ‖4 - b t2‖ ≤ ‖(4 : ℂ)‖ + ‖b t2‖ := norm_sub_le _ _
        _ = 4 + ‖b t2‖ := by norm_num
    have h2 : 4 ≤ 4 / δ * ‖b t2‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    rw [hV0]
    nlinarith
  have hsmall : 2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2 < 1 := by
    rw [hεV]
    have : 1 - t1 ≤ 1 / 64 := by linarith
    linarith
  have hstab := ab16_stab (b := b) (D := D) (τ := τ) ht2t1.le ht2lt ht10.le
    (fun t ht => (hDd t (by linarith [ht.1]) (lt_of_le_of_lt ht.2 ht2lt)).1)
    (fun t ht => (hDd t (by linarith [ht.1]) (lt_of_le_of_lt ht.2 ht2lt)).2)
    hτb hε0.le (by linarith) hend hsmall
  -- the point `t₃` with `1 - t₃² = 16 V0 (1 - t₂²)`
  set w2 : ℝ := 16 * V0 * (1 - t2 ^ 2) with hw2
  have hw2a : w2 ≤ 1 - t1 ^ 2 := by
    have : 16 * V0 * (1 - t2 ^ 2) ≤ 16 * V0 * (2 * η) :=
      mul_le_mul_of_nonneg_left h1t2 (by positivity)
    have h2 : 32 * V0 * η ≤ 1 - t1 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hη2 (show (0 : ℝ) ≤ 32 * V0 by positivity)
      rwa [mul_div_cancel₀ _ (by positivity)] at this
    rw [hw2]; nlinarith
  have hw2b : 1 - t2 ^ 2 ≤ w2 := by
    rw [hw2]; nlinarith
  have hw20 : 0 ≤ w2 := by rw [hw2]; positivity
  set t3 : ℝ := Real.sqrt (1 - w2) with ht3
  have ht3sq : t3 ^ 2 = 1 - w2 := Real.sq_sqrt (by linarith [sq_nonneg t1])
  have ht30 : 0 ≤ t3 := Real.sqrt_nonneg _
  have ht3t1 : t1 ≤ t3 := by
    apply le_of_sq_le_sq _ ht30
    rw [ht3sq]; linarith
  have ht3t2 : t3 ≤ t2 := by
    apply le_of_sq_le_sq _ ht20.le
    rw [ht3sq]; linarith
  have ht3lt : t3 < 1 := lt_of_le_of_lt ht3t2 ht2lt
  -- `Re b ≥ 3` on `[t₁, t₃]`
  have hre : ∀ t ∈ Icc t1 t3, 3 ≤ (b t).re := by
    intro t ht
    have htI : t ∈ Icc t1 t2 := ⟨ht.1, le_trans ht.2 ht3t2⟩
    have hb := hstab t htI
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ht1' : t < 1 := lt_of_le_of_lt (le_trans ht.2 ht3t2) ht2lt
    have hden : 0 < 1 - t ^ 2 := by nlinarith
    have hden3 : 1 - t3 ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.2]
    have hq : V0 * (1 - t2 ^ 2) / (1 - t ^ 2) ≤ 1 / 16 := by
      rw [div_le_iff₀ hden]
      have h16 : (1 - t3 ^ 2) = 16 * V0 * (1 - t2 ^ 2) := by rw [ht3sq, hw2]; ring
      have : 16 * V0 * (1 - t2 ^ 2) ≤ 16 * V0 * (1 - t2 ^ 2) := le_rfl
      nlinarith [mul_pos (show (0 : ℝ) < V0 by linarith) h1t2pos]
    have hrest : 2 * (1 - t1) + ε / 4 * (V0 + 2) ^ 2 ≤ 1 / 16 := by
      rw [hεV]
      have : 1 - t1 ≤ 1 / 64 := by linarith
      linarith
    have h8 : ‖4 - b t‖ ≤ (1 / 8) * ‖b t‖ := by
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      linarith
    have hbn : ‖b t‖ ≤ 4 + ‖4 - b t‖ := by
      calc ‖b t‖ = ‖(4 : ℂ) - (4 - b t)‖ := by ring_nf
        _ ≤ ‖(4 : ℂ)‖ + ‖4 - b t‖ := norm_sub_le _ _
        _ = _ := by norm_num
    have hre4 : 4 - ‖4 - b t‖ ≤ (b t).re := by
      have h := Complex.abs_re_le_norm (4 - b t)
      have : (4 - b t).re = 4 - (b t).re := by simp
      rw [this] at h
      have := (abs_le.1 h).2
      linarith
    nlinarith [norm_nonneg (b t), norm_nonneg (4 - b t)]
  -- monotonicity of `Φ`
  set Φ : ℝ → ℝ := fun t => ‖deriv f ((t : ℂ) * ζ0)‖ ^ 2 * ((1 - t) ^ 3 * (1 + t)) with hΦ
  have hΦd : ∀ t ∈ Icc t1 t3, HasDerivAt Φ
      (‖deriv f ((t : ℂ) * ζ0)‖ ^ 2 * (1 - t) ^ 2 * (2 * (b t).re - 2 - 4 * t)) t := by
    intro t ht
    exact ab16_radial_growth hf hF1 hζ (by linarith [ht.1]) (lt_of_le_of_lt (ht.2.trans ht3t2) ht2lt)
  have hmono : MonotoneOn Φ (Icc t1 t3) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t1 t3)
      (f' := fun t => ‖deriv f ((t : ℂ) * ζ0)‖ ^ 2 * (1 - t) ^ 2 * (2 * (b t).re - 2 - 4 * t))
    · intro t ht; exact (hΦd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hΦd t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Icc t1 t3 := ⟨ht.1.le, ht.2.le⟩
      have h1 := hre t htI
      have ht1' : t < 1 := lt_of_lt_of_le ht.2 (ht3t2.trans ht2lt.le)
      have : 0 ≤ 2 * (b t).re - 2 - 4 * t := by linarith
      positivity
  have hlow : c1 ≤ Φ t1 := by
    have hn : ‖(t1 : ℂ) * ζ0‖ = t1 := hnorm_w t1 ht10.le
    have hs : (t1 : ℂ) * ζ0 ∈ sphere (0 : ℂ) t1 := by
      rw [mem_sphere_zero_iff_norm]; exact hn
    have := (isMinOn_iff.1 hmin) _ hs
    simp only [hΦ]
    rw [hc1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hm1pos.le this 2
  have hup : Φ t3 ≤ 16 * M ^ 2 * w2 := by
    have hn : ‖(t3 : ℂ) * ζ0‖ = t3 := hnorm_w t3 ht30
    have hmem : (t3 : ℂ) * ζ0 ∈ unitDisc := by
      rw [unitDisc, mem_ball_zero_iff, hn]; exact ht3lt
    have hc := hcauchy _ hmem
    rw [hn] at hc
    simp only [hΦ]
    have h1 : 0 ≤ 1 - t3 := by linarith
    have h2 : 0 ≤ ‖deriv f ((t3 : ℂ) * ζ0)‖ := norm_nonneg _
    have h3 : (1 - t3 ^ 2) = (1 - t3) * (1 + t3) := by ring
    have h4 : ‖deriv f ((t3 : ℂ) * ζ0)‖ ^ 2 * ((1 - t3) ^ 3 * (1 + t3)) =
        ((1 - t3 ^ 2) * ‖deriv f ((t3 : ℂ) * ζ0)‖) ^ 2 * ((1 - t3) / (1 + t3)) := by
      rw [h3]; field_simp
    rw [h4]
    have h5 : ((1 - t3 ^ 2) * ‖deriv f ((t3 : ℂ) * ζ0)‖) ^ 2 ≤ (4 * M) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) hc 2
    have h6 : (1 - t3) / (1 + t3) ≤ w2 := by
      rw [div_le_iff₀ (by linarith)]
      have : 1 - t3 ^ 2 = w2 := by rw [ht3sq]; ring
      nlinarith
    calc _ ≤ (4 * M) ^ 2 * ((1 - t3) / (1 + t3)) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ ≤ (4 * M) ^ 2 * w2 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 16 * M ^ 2 * w2 := by ring
  have hchain : c1 ≤ 16 * M ^ 2 * w2 :=
    le_trans hlow (le_trans (hmono ⟨le_rfl, ht3t1⟩ ⟨ht3t1, le_rfl⟩ ht3t1) hup)
  -- contradiction
  have hw2c : 16 * M ^ 2 * w2 ≤ c1 / 2 := by
    have h1 : w2 ≤ 32 * V0 * η := by
      rw [hw2]
      nlinarith
    have h2 : 32 * V0 * η ≤ 32 * V0 * (c1 / (1024 * Mp ^ 2 * V0)) :=
      mul_le_mul_of_nonneg_left hη1 (by positivity)
    have h3 : 32 * V0 * (c1 / (1024 * Mp ^ 2 * V0)) = c1 / (32 * Mp ^ 2) := by
      field_simp
      ring
    have hMM : M ^ 2 ≤ Mp ^ 2 := by
      rw [hMp]; nlinarith
    have hA : 16 * M ^ 2 ≤ 16 * Mp ^ 2 := by linarith
    have hB : w2 ≤ c1 / (32 * Mp ^ 2) := by linarith
    have hC0 : 0 ≤ 16 * Mp ^ 2 := by positivity
    have hAB : 16 * M ^ 2 * w2 ≤ 16 * Mp ^ 2 * (c1 / (32 * Mp ^ 2)) :=
      mul_le_mul hA hB hw20 hC0
    have hE : 16 * Mp ^ 2 * (c1 / (32 * Mp ^ 2)) = c1 / 2 := by
      have : Mp ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    exact hAB.trans hE.le
  linarith

end Ch2
end TakhtajanTeo
