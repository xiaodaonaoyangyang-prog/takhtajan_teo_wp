import TakhtajanTeo.Basic
import TakhtajanTeo.Ch1.QCVariationPlane
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Weak holomorphy (`wh_`, 下属3, Program G; shared with Ch1 S4 `remark_4_3`)

Host: new module `TakhtajanTeo/Ch1/WeakHolomorphy.lean`.

* `wh_differentiableOn`: a continuous map `f : ℂ → F` into a Banach space is holomorphic as soon as `ℓ ∘ f` is
  holomorphic for every `ℓ` in a separating family of functionals (Cauchy integral formula, tested on the family).
* `wh_lp_continuousOn`: a locally bounded map `ℂ → ℓ²` with holomorphic coordinates is continuous (Cauchy formula for
  each coordinate, Cauchy–Schwarz on the circle, and summation).
* `wh_lp_differentiableOn`: hence it is holomorphic.
* `wh_lp_banach`: the same over a Banach domain, from local bounds (via `QCV.qcv_gateaux_to_frechet`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace TakhtajanTeo

/-- Continuous linear maps commute with circle integrals. -/
theorem wh_clm_circleIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (ℓ : F →L[ℂ] ℂ) {h : ℂ → F} {c : ℂ} {R : ℝ} (hh : CircleIntegrable h c R) :
    ℓ (∮ z in C(c, R), h z) = ∮ z in C(c, R), ℓ (h z) := by
  unfold circleIntegral
  rw [← ℓ.intervalIntegral_comp_comm hh.out]
  simp only [map_smul]

/-- **Weak ⇒ strong holomorphy** (one variable). A continuous `f : ℂ → F` such that `ℓ ∘ f` is holomorphic for every `ℓ`
in a separating family `S` is holomorphic. -/
theorem wh_differentiableOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn f U) (S : Set (F →L[ℂ] ℂ))
    (hS : ∀ x : F, (∀ ℓ ∈ S, ℓ x = 0) → x = 0) (hd : ∀ ℓ ∈ S, DifferentiableOn ℂ (fun t => ℓ (f t)) U) :
    DifferentiableOn ℂ f U := by
  intro t₀ ht₀
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU t₀ ht₀
  set R : ℝ≥0 := ⟨r / 2, by positivity⟩ with hRdef
  have hR : (0 : ℝ≥0) < R := by
    rw [← NNReal.coe_lt_coe]
    show (0 : ℝ) < r / 2
    positivity
  have hRr : (R : ℝ) < r := by
    show r / 2 < r
    linarith
  have hcl : closedBall t₀ (R : ℝ) ⊆ U := (closedBall_subset_ball hRr).trans hsub
  have hcR : ContinuousOn f (closedBall t₀ (R : ℝ)) := hc.mono hcl
  have hint : CircleIntegrable f t₀ R := (hcR.mono sphere_subset_closedBall).circleIntegrable R.2
  have hps := hasFPowerSeriesOn_cauchy_integral hint hR
  have heq : ∀ w ∈ ball t₀ (R : ℝ),
      (2 * π * I : ℂ)⁻¹ • (∮ z in C(t₀, R), (z - w)⁻¹ • f z) = f w := by
    intro w hw
    have hne : ∀ z ∈ sphere t₀ (R : ℝ), z - w ≠ 0 := by
      intro z hz h0
      rw [sub_eq_zero] at h0
      subst h0
      rw [mem_ball, mem_sphere.mp hz] at hw
      exact lt_irrefl _ hw
    have hint' : CircleIntegrable (fun z => (z - w)⁻¹ • f z) t₀ R := by
      refine ContinuousOn.circleIntegrable R.2 ?_
      exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul (hcR.mono sphere_subset_closedBall)
    rw [← sub_eq_zero]
    apply hS
    intro ℓ hℓ
    rw [map_sub, map_smul, wh_clm_circleIntegral ℓ hint', sub_eq_zero]
    simp only [map_smul]
    have hcℓ : ContinuousOn (fun t => ℓ (f t)) (closedBall t₀ (R : ℝ)) := ℓ.continuous.comp_continuousOn hcR
    have hdℓ : ∀ x ∈ ball t₀ (R : ℝ) \ (∅ : Set ℂ), DifferentiableAt ℂ (fun t => ℓ (f t)) x := by
      intro x hx
      exact (hd ℓ hℓ).differentiableAt (hU.mem_nhds (hsub ((ball_subset_ball hRr.le) hx.1)))
    exact two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
      hcℓ hdℓ
  have hev : (fun w => (2 * π * I : ℂ)⁻¹ • (∮ z in C(t₀, R), (z - w)⁻¹ • f z)) =ᶠ[𝓝 t₀] f := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (show (0 : ℝ) < R from hR))] with w hw
    exact heq w hw
  exact (hps.analyticAt.differentiableAt.congr_of_eventuallyEq hev.symm).differentiableWithinAt

/-- Cauchy difference bound: for `h` holomorphic near `closedBall t₀ (2r)` and `‖t - t₀‖ < r`,
`‖h t - h t₀‖ ≤ ‖t - t₀‖/(2π r) ∫₀^{2π} ‖h(t₀ + 2r e^{iθ})‖ dθ`. -/
theorem wh_cauchy_diff {h : ℂ → ℂ} {t₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn h (closedBall t₀ (2 * r))) (hd : ∀ x ∈ ball t₀ (2 * r), DifferentiableAt ℂ h x)
    (ht : ‖t - t₀‖ < r) :
    ‖h t - h t₀‖ ≤ ‖t - t₀‖ / (2 * π * r) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap t₀ (2 * r) θ)‖ := by
  have hρ : 0 ≤ 2 * r := by positivity
  have hdiff : ∀ x ∈ ball t₀ (2 * r) \ (∅ : Set ℂ), DifferentiableAt ℂ h x := fun x hx => hd x hx.1
  have htb : t ∈ ball t₀ (2 * r) := by rw [mem_ball, dist_eq_norm]; linarith
  have ht₀b : t₀ ∈ ball t₀ (2 * r) := mem_ball_self (by positivity)
  have e1 := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
    htb hc hdiff
  have e0 := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
    ht₀b hc hdiff
  have hzt : ∀ z ∈ sphere t₀ (2 * r), r ≤ ‖z - t‖ := by
    intro z hz
    have h1 : ‖z - t₀‖ = 2 * r := by rw [← dist_eq_norm]; exact mem_sphere.mp hz
    have h2 : ‖z - t₀‖ ≤ ‖z - t‖ + ‖t - t₀‖ := by
      calc ‖z - t₀‖ = ‖(z - t) + (t - t₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hne : ∀ w ∈ ball t₀ (2 * r), ∀ z ∈ sphere t₀ (2 * r), z - w ≠ 0 := by
    intro w hw z hz h0
    rw [sub_eq_zero] at h0
    subst h0
    rw [mem_ball, mem_sphere.mp hz] at hw
    exact lt_irrefl _ hw
  have hci : ∀ w ∈ ball t₀ (2 * r), CircleIntegrable (fun z => (z - w)⁻¹ • h z) t₀ (2 * r) := by
    intro w hw
    refine ContinuousOn.circleIntegrable hρ ?_
    exact ((continuousOn_id.sub continuousOn_const).inv₀ (hne w hw)).smul (hc.mono sphere_subset_closedBall)
  have hsub : h t - h t₀ = (2 * π * I : ℂ)⁻¹ •
      ∮ z in C(t₀, 2 * r), ((z - t)⁻¹ • h z - (z - t₀)⁻¹ • h z) := by
    rw [circleIntegral.integral_sub (hci t htb) (hci t₀ ht₀b), smul_sub, e1, e0]
  rw [hsub, norm_smul]
  have hI : ‖(2 * π * I : ℂ)⁻¹‖ = 1 / (2 * π) := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hI]
  have hint : ‖∮ z in C(t₀, 2 * r), ((z - t)⁻¹ • h z - (z - t₀)⁻¹ • h z)‖ ≤
      ∫ θ in (0 : ℝ)..2 * π, ‖t - t₀‖ / r * ‖h (circleMap t₀ (2 * r) θ)‖ := by
    unfold circleIntegral
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ ?_
    · exact ((hci t htb).sub (hci t₀ ht₀b)).out.norm
    · refine (Continuous.intervalIntegrable ?_ _ _)
      exact continuous_const.mul ((hc.mono sphere_subset_closedBall).norm.comp_continuous
        (continuous_circleMap _ _) (circleMap_mem_sphere _ hρ))
    · intro θ _
      set z := circleMap t₀ (2 * r) θ with hz
      have hzs : z ∈ sphere t₀ (2 * r) := circleMap_mem_sphere _ hρ _
      have hz0 : ‖z - t₀‖ = 2 * r := by rw [← dist_eq_norm]; exact mem_sphere.mp hzs
      have hzt' := hzt z hzs
      have hA : z - t ≠ 0 := hne t htb z hzs
      have hB : z - t₀ ≠ 0 := hne t₀ ht₀b z hzs
      have hk : (z - t)⁻¹ • h z - (z - t₀)⁻¹ • h z = ((t - t₀) / ((z - t) * (z - t₀))) * h z := by
        rw [smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      rw [deriv_circleMap, norm_smul]
      beta_reduce
      rw [hk]
      simp only [norm_mul, norm_div, Complex.norm_I, norm_circleMap_zero, abs_of_nonneg hρ, hz0, mul_one]
      have hpos : 0 < ‖z - t‖ := norm_pos_iff.mpr hA
      have hh := norm_nonneg (h z)
      have hd' := norm_nonneg (t - t₀)
      calc _ = ‖t - t₀‖ / ‖z - t‖ * ‖h z‖ := by field_simp
        _ ≤ ‖t - t₀‖ / r * ‖h z‖ := by gcongr
  calc 1 / (2 * π) * ‖∮ z in C(t₀, 2 * r), ((z - t)⁻¹ • h z - (z - t₀)⁻¹ • h z)‖
      ≤ 1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖t - t₀‖ / r * ‖h (circleMap t₀ (2 * r) θ)‖ := by
        gcongr
    _ = ‖t - t₀‖ / (2 * π * r) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap t₀ (2 * r) θ)‖ := by
        rw [intervalIntegral.integral_const_mul]
        field_simp

/-- Cauchy–Schwarz on `[0, 2π]`: `(∫ g)² ≤ 2π ∫ g²`. -/
theorem wh_cs {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ θ in (0 : ℝ)..2 * π, g θ) ^ 2 ≤ 2 * π * ∫ θ in (0 : ℝ)..2 * π, g θ ^ 2 := by
  set A := ∫ θ in (0 : ℝ)..2 * π, g θ with hA
  set m := A / (2 * π) with hm
  have hpi : 0 < 2 * π := by positivity
  have h0 : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, (g θ - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ => sq_nonneg _)
  have hexp : (fun θ => (g θ - m) ^ 2) = fun θ => g θ ^ 2 - 2 * m * g θ + m ^ 2 := by
    funext θ
    ring
  have hi1 : IntervalIntegrable (fun θ => g θ ^ 2) volume 0 (2 * π) := (hg.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => 2 * m * g θ) volume 0 (2 * π) :=
    (continuous_const.mul hg).intervalIntegrable _ _
  rw [hexp, intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
    intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, ← hA] at h0
  have hmA : m * (2 * π) = A := by rw [hm]; field_simp
  nlinarith [hmA]

/-- **Continuity of `ℓ²`-valued maps with holomorphic coordinates.** A map `f : ℂ → ℓ²` with `‖f‖ ≤ M` on an open
`U` and holomorphic coordinates is continuous on `U`, with `‖f t - f t₀‖ ≤ M ‖t - t₀‖ / r` when
`closedBall t₀ (2r) ⊆ U` and `‖t - t₀‖ < r`. -/
theorem wh_lp_continuousOn {f : ℂ → lp (fun _ : ℕ => ℂ) 2} {U : Set ℂ} (hU : IsOpen U) {M : ℝ}
    (hb : ∀ t ∈ U, ‖f t‖ ≤ M) (hd : ∀ n, DifferentiableOn ℂ (fun t => f t n) U) : ContinuousOn f U := by
  intro t₀ ht₀
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU t₀ ht₀
  set r := ε / 4 with hrdef
  have hr : 0 < r := by positivity
  have hcl : closedBall t₀ (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hsub
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb t₀ ht₀)
  -- the coordinate estimate, summed
  have hkey : ∀ t, ‖t - t₀‖ < r → ‖f t - f t₀‖ ≤ M * ‖t - t₀‖ / r := by
    intro t ht
    set d := ‖t - t₀‖ with hddef
    have hcoord : ∀ n, ‖f t n - f t₀ n‖ ^ 2 ≤
        d ^ 2 / (2 * π * r ^ 2) * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2 := by
      intro n
      have hcn : ContinuousOn (fun t => f t n) (closedBall t₀ (2 * r)) := ((hd n).mono hcl).continuousOn
      have hdn : ∀ x ∈ ball t₀ (2 * r), DifferentiableAt ℂ (fun t => f t n) x := fun x hx =>
        (hd n).differentiableAt (hU.mem_nhds (hcl (ball_subset_closedBall hx)))
      have h1 := wh_cauchy_diff hr hcn hdn ht
      have hg : Continuous fun θ => ‖f (circleMap t₀ (2 * r) θ) n‖ :=
        (hcn.mono sphere_subset_closedBall).norm.comp_continuous (continuous_circleMap _ _)
          (circleMap_mem_sphere _ (by positivity))
      have h2 := wh_cs hg
      have hI0 : 0 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖ :=
        intervalIntegral.integral_nonneg (by positivity) (fun _ _ => norm_nonneg _)
      have h1' : ‖f t n - f t₀ n‖ ^ 2 ≤
          (d / (2 * π * r) * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ‖f t n - f t₀ n‖ ^ 2
          ≤ (d / (2 * π * r)) ^ 2 * (∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖) ^ 2 := by
            rw [← mul_pow]; exact h1'
        _ ≤ (d / (2 * π * r)) ^ 2 * (2 * π * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2) := by
            gcongr
        _ = _ := by field_simp
    -- partial sums
    have hsumN : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖f t n - f t₀ n‖ ^ 2 ≤ (M * d / r) ^ 2 := by
      intro N
      have hpt : ∀ θ, ∑ n ∈ Finset.range N, ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2 ≤ M ^ 2 := by
        intro θ
        set x := f (circleMap t₀ (2 * r) θ)
        have hx : ‖x‖ ≤ M := hb _ (hcl (sphere_subset_closedBall (circleMap_mem_sphere _ (by positivity) θ)))
        have hs : Summable fun n => ‖x n‖ ^ 2 := by
          have := (lp.memℓp x).summable (p := 2) (by norm_num)
          simpa using this
        have hn : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
          have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
          simpa using this
        calc ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 ≤ ∑' n, ‖x n‖ ^ 2 :=
              hs.sum_le_tsum _ (fun n _ => by positivity)
          _ = ‖x‖ ^ 2 := hn.symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      have hcont : ∀ n, Continuous (fun θ => ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2) := by
        intro n
        have hcn : ContinuousOn (fun t => f t n) (closedBall t₀ (2 * r)) := ((hd n).mono hcl).continuousOn
        exact ((hcn.mono sphere_subset_closedBall).norm.comp_continuous (continuous_circleMap _ _)
          (circleMap_mem_sphere _ (by positivity))).pow 2
      have hint : ∀ n, IntervalIntegrable (fun θ => ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2) volume 0 (2 * π) :=
        fun n => (hcont n).intervalIntegrable _ _
      calc ∑ n ∈ Finset.range N, ‖f t n - f t₀ n‖ ^ 2
          ≤ ∑ n ∈ Finset.range N, d ^ 2 / (2 * π * r ^ 2) *
              ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2 :=
            Finset.sum_le_sum fun n _ => hcoord n
        _ = d ^ 2 / (2 * π * r ^ 2) *
              ∫ θ in (0 : ℝ)..2 * π, ∑ n ∈ Finset.range N, ‖f (circleMap t₀ (2 * r) θ) n‖ ^ 2 := by
            rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum (fun n _ => hint n)]
        _ ≤ d ^ 2 / (2 * π * r ^ 2) * ∫ θ in (0 : ℝ)..2 * π, M ^ 2 := by
            gcongr
            exact intervalIntegral.integral_mono_on (by positivity)
              ((continuous_finset_sum _ fun n _ => hcont n).intervalIntegrable _ _) intervalIntegrable_const
              (fun θ _ => hpt θ)
        _ = (M * d / r) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
            field_simp
    have hsd : Summable fun n => ‖(f t - f t₀) n‖ ^ 2 := by
      have := (lp.memℓp (f t - f t₀)).summable (p := 2) (by norm_num)
      simpa using this
    have hn : ‖f t - f t₀‖ ^ 2 = ∑' n, ‖(f t - f t₀) n‖ ^ 2 := by
      have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (f t - f t₀)
      simpa using this
    have hle : ‖f t - f t₀‖ ^ 2 ≤ (M * d / r) ^ 2 := by
      rw [hn]
      refine hsd.tsum_le_of_sum_range_le fun N => ?_
      simpa only [lp.coeFn_sub, Pi.sub_apply] using hsumN N
    have hpos : 0 ≤ M * d / r := by positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos (by norm_num)).mp hle
  -- conclude
  refine Metric.continuousWithinAt_iff.mpr fun e he => ?_
  refine ⟨min r (e * r / (M + 1)), by positivity, fun t _ htd => ?_⟩
  rw [dist_eq_norm] at htd ⊢
  have h1 : ‖t - t₀‖ < r := lt_of_lt_of_le htd (min_le_left _ _)
  have h2 : ‖t - t₀‖ < e * r / (M + 1) := lt_of_lt_of_le htd (min_le_right _ _)
  calc ‖f t - f t₀‖ ≤ M * ‖t - t₀‖ / r := hkey t h1
    _ ≤ (M + 1) * ‖t - t₀‖ / r := by gcongr; linarith
    _ < (M + 1) * (e * r / (M + 1)) / r := by gcongr
    _ = e := by field_simp

/-- **`ℓ²`-valued holomorphy from coordinates.** A locally bounded map `ℂ → ℓ²` with holomorphic coordinates is
holomorphic. -/
theorem wh_lp_differentiableOn {f : ℂ → lp (fun _ : ℕ => ℂ) 2} {U : Set ℂ} (hU : IsOpen U) {M : ℝ}
    (hb : ∀ t ∈ U, ‖f t‖ ≤ M) (hd : ∀ n, DifferentiableOn ℂ (fun t => f t n) U) :
    DifferentiableOn ℂ f U := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  refine wh_differentiableOn hU (wh_lp_continuousOn hU hb hd)
    (range fun n : ℕ => lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n) ?_ ?_
  · intro x hx
    ext n
    exact hx _ ⟨n, rfl⟩
  · rintro ℓ ⟨n, rfl⟩
    exact hd n

/-- **`ℓ²`-valued holomorphy over a Banach domain.** A locally bounded map `E → ℓ²` with holomorphic coordinates is
holomorphic (`wh_lp_differentiableOn` on complex lines, then `QCV.qcv_gateaux_to_frechet`). -/
theorem wh_lp_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : E → lp (fun _ : ℕ => ℂ) 2} {U : Set E} (hU : IsOpen U)
    (hloc : ∀ x ∈ U, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ ball x r, ‖f y‖ ≤ C)
    (hd : ∀ n, DifferentiableOn ℂ (fun x => f x n) U) : DifferentiableOn ℂ f U := by
  refine QCV.qcv_gateaux_to_frechet hU hloc fun x hx v => ?_
  obtain ⟨r, hr, C, hC⟩ := hloc x hx
  obtain ⟨r', hr', hsub⟩ := Metric.isOpen_iff.mp hU x hx
  set ρ := min r r' with hρ
  have hρ0 : 0 < ρ := lt_min hr hr'
  set δ := ρ / (‖v‖ + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hline : ∀ t ∈ ball (0 : ℂ) δ, x + t • v ∈ ball x ρ := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [mem_ball, dist_zero_right] at ht
    have hv := norm_nonneg v
    calc ‖t‖ * ‖v‖ ≤ ‖t‖ * (‖v‖ + 1) := by gcongr; linarith
      _ < δ * (‖v‖ + 1) := by gcongr
      _ = ρ := by rw [hδ]; field_simp
  have hU' : ∀ t ∈ ball (0 : ℂ) δ, x + t • v ∈ U := fun t ht =>
    hsub (ball_subset_ball (min_le_right r r') (hline t ht))
  have hb : ∀ t ∈ ball (0 : ℂ) δ, ‖f (x + t • v)‖ ≤ C := fun t ht =>
    hC _ (ball_subset_ball (min_le_left r r') (hline t ht))
  have hdl : ∀ n, DifferentiableOn ℂ (fun t : ℂ => f (x + t • v) n) (ball (0 : ℂ) δ) := by
    intro n
    have ha : DifferentiableOn ℂ (fun t : ℂ => x + t • v) (ball (0 : ℂ) δ) :=
      (differentiableOn_const _).add (differentiableOn_id.smul_const v)
    exact (hd n).comp ha (fun t ht => hU' t ht)
  have h := wh_lp_differentiableOn (f := fun t : ℂ => f (x + t • v)) isOpen_ball hb hdl
  exact h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ0))

end TakhtajanTeo
