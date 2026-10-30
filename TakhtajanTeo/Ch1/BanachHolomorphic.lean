import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.MeanValue

open Complex Set Metric Filter Topology

noncomputable section

namespace TakhtajanTeo

/-! ## Fréchet-holomorphic maps on a Banach domain are strictly differentiable (`bh_` prefix) -/

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- Cauchy estimate for the derivative along a complex line. -/
theorem bh_line_deriv_le {f : E → F} {a h : E} {R C : ℝ} (hR : 0 < R)
    (hd : ∀ ζ ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f (a + ζ • h))
    (hC : ∀ ζ ∈ sphere (0 : ℂ) R, ‖f (a + ζ • h)‖ ≤ C) :
    ‖fderiv ℂ f a h‖ ≤ C / R := by
  let g : ℂ → F := fun ζ => f (a + ζ • h)
  have hlin : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => a + ζ • h) h ζ := by
    intro ζ
    simpa using ((hasDerivAt_id ζ).smul_const h).const_add a
  have hg : ∀ ζ ∈ closedBall (0 : ℂ) R, HasDerivAt g (fderiv ℂ f (a + ζ • h) h) ζ := by
    intro ζ hζ
    exact (hd ζ hζ).hasFDerivAt.comp_hasDerivAt ζ (hlin ζ)
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hR.ne']
    exact fun ζ hζ => (hg ζ hζ).differentiableAt.differentiableWithinAt
  have h0 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc hC
  have h1 : deriv g 0 = fderiv ℂ f a h := by
    have := (hg 0 (mem_closedBall_self hR.le)).deriv
    simpa using this
  rwa [h1] at h0

/-- A holomorphic map on an open subset of a complex normed space is strictly differentiable. -/
theorem bh_hasStrictFDerivAt {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) : HasStrictFDerivAt f (fderiv ℂ f x) x := by
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.mp hU x hx
  have hcont : ContinuousAt f x := (hf.differentiableAt (hU.mem_nhds hx)).continuousAt
  obtain ⟨r1, hr1, hM⟩ : ∃ r1 > 0, ∀ a ∈ ball x r1, ‖f a‖ ≤ ‖f x‖ + 1 := by
    have h1 : ∀ᶠ a in 𝓝 x, ‖f a‖ < ‖f x‖ + 1 :=
      hcont.norm.eventually (gt_mem_nhds (by linarith))
    obtain ⟨r1, hr1, h⟩ := Metric.eventually_nhds_iff_ball.mp h1
    exact ⟨r1, hr1, fun a ha => (h a ha).le⟩
  set M : ℝ := ‖f x‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  set r : ℝ := min r0 r1 / 8 with hrdef
  have hr : 0 < r := by positivity
  have hr0' : 8 * r ≤ r0 := by
    have := min_le_left r0 r1
    simp only [hrdef]; linarith
  have hr1' : 8 * r ≤ r1 := by
    have := min_le_right r0 r1
    simp only [hrdef]; linarith
  have hdiffU : ∀ a ∈ ball x r0, DifferentiableAt ℂ f a :=
    fun a ha => hf.differentiableAt (hU.mem_nhds (hball0 ha))
  -- derivative bound on `ball x (2r)`
  have hder : ∀ a ∈ ball x (2 * r), ‖fderiv ℂ f a‖ ≤ M / (2 * r) := by
    intro a ha
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    by_cases hh : h = 0
    · simp [hh]
    have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hR : 0 < 2 * r / ‖h‖ := by positivity
    have hax : dist a x < 2 * r := ha
    have hpt : ∀ ζ : ℂ, ‖ζ‖ ≤ 2 * r / ‖h‖ → a + ζ • h ∈ ball x r0 := by
      intro ζ hζ
      rw [mem_ball, dist_eq_norm]
      have : ‖ζ • h‖ ≤ 2 * r := by
        rw [norm_smul]
        calc ‖ζ‖ * ‖h‖ ≤ 2 * r / ‖h‖ * ‖h‖ := by gcongr
          _ = 2 * r := by field_simp
      have h2 : ‖a + ζ • h - x‖ ≤ ‖a - x‖ + ‖ζ • h‖ := by
        calc ‖a + ζ • h - x‖ = ‖(a - x) + ζ • h‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖a - x‖ < 2 * r := by rwa [dist_eq_norm] at hax
      linarith
    have hpt1 : ∀ ζ ∈ sphere (0 : ℂ) (2 * r / ‖h‖), ‖f (a + ζ • h)‖ ≤ M := by
      intro ζ hζ
      have hζn : ‖ζ‖ = 2 * r / ‖h‖ := by simpa using hζ
      apply hM
      rw [mem_ball, dist_eq_norm]
      have : ‖ζ • h‖ = 2 * r := by
        rw [norm_smul, hζn]; field_simp
      have h2 : ‖a + ζ • h - x‖ ≤ ‖a - x‖ + ‖ζ • h‖ := by
        calc ‖a + ζ • h - x‖ = ‖(a - x) + ζ • h‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖a - x‖ < 2 * r := by rwa [dist_eq_norm] at hax
      linarith
    have hb := bh_line_deriv_le hR
      (fun ζ hζ => hdiffU _ (hpt ζ (by simpa using hζ))) hpt1
    calc ‖fderiv ℂ f a h‖ ≤ M / (2 * r / ‖h‖) := hb
      _ = M / (2 * r) * ‖h‖ := by field_simp
  -- Lipschitz on `ball x (2r)`
  have hlip : ∀ a ∈ ball x (2 * r), ∀ b ∈ ball x (2 * r), ‖f b - f a‖ ≤ M / (2 * r) * ‖b - a‖ := by
    intro a ha b hb
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
      (fun y hy => hdiffU y (ball_subset_ball (by linarith) hy)) hder (convex_ball x (2 * r)) ha hb
  -- Lipschitz bound for the derivative on `ball x r`
  have hlipder : ∀ y ∈ ball x r, ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ (M / (2 * r) / r) * ‖y - x‖ := by
    intro y hy
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    by_cases hh : h = 0
    · simp [hh]
    have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hR : 0 < r / ‖h‖ := by positivity
    have hyx : ‖y - x‖ < r := by rwa [mem_ball, dist_eq_norm] at hy
    let φ : E → F := fun w => f (w + (y - x)) - f w
    have hζ : ∀ ζ : ℂ, ‖ζ‖ ≤ r / ‖h‖ → ‖ζ • h‖ ≤ r := by
      intro ζ hζ'
      rw [norm_smul]
      calc ‖ζ‖ * ‖h‖ ≤ r / ‖h‖ * ‖h‖ := by gcongr
        _ = r := by field_simp
    have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ r / ‖h‖ → x + ζ • h ∈ ball x (2 * r) ∧
        x + ζ • h + (y - x) ∈ ball x (2 * r) := by
      intro ζ hζ'
      have h1 := hζ ζ hζ'
      constructor
      · rw [mem_ball, dist_eq_norm]
        have : x + ζ • h - x = ζ • h := by abel
        rw [this]; linarith
      · rw [mem_ball, dist_eq_norm]
        have : x + ζ • h + (y - x) - x = ζ • h + (y - x) := by abel
        rw [this]
        calc ‖ζ • h + (y - x)‖ ≤ ‖ζ • h‖ + ‖y - x‖ := norm_add_le _ _
          _ < 2 * r := by linarith
    have hφd : ∀ ζ ∈ closedBall (0 : ℂ) (r / ‖h‖), DifferentiableAt ℂ φ (x + ζ • h) := by
      intro ζ hζ'
      have hz : ‖ζ‖ ≤ r / ‖h‖ := by simpa using hζ'
      obtain ⟨m1, m2⟩ := hmem ζ hz
      have d1 := hdiffU _ (ball_subset_ball (by linarith) m1)
      have d2 : DifferentiableAt ℂ f (x + ζ • h + (y - x)) :=
        hdiffU _ (ball_subset_ball (by linarith) m2)
      exact (d2.comp (x + ζ • h) (differentiableAt_id.add_const _)).sub d1
    have hφb : ∀ ζ ∈ sphere (0 : ℂ) (r / ‖h‖), ‖φ (x + ζ • h)‖ ≤ M / (2 * r) * ‖y - x‖ := by
      intro ζ hζ'
      have hz : ‖ζ‖ ≤ r / ‖h‖ := by simpa using hζ'.le
      obtain ⟨m1, m2⟩ := hmem ζ hz
      have := hlip _ m1 _ m2
      simpa [φ, add_sub_cancel_left] using this
    have hb := bh_line_deriv_le hR hφd hφb
    have hfd : fderiv ℂ φ x = fderiv ℂ f y - fderiv ℂ f x := by
      have d1 : DifferentiableAt ℂ (fun w => f (w + (y - x))) x := by
        have := hdiffU (x + (y - x)) (by
          rw [mem_ball, dist_eq_norm]; simp only [add_sub_cancel]; linarith)
        exact this.comp x (differentiableAt_id.add_const _)
      have d2 : DifferentiableAt ℂ f x := hdiffU x (mem_ball_self hr0)
      simp only [φ]
      rw [fderiv_fun_sub d1 d2, fderiv_comp_add_right]
      simp
    rw [hfd] at hb
    calc ‖(fderiv ℂ f y - fderiv ℂ f x) h‖ ≤ M / (2 * r) * ‖y - x‖ / (r / ‖h‖) := hb
      _ = M / (2 * r) / r * ‖y - x‖ * ‖h‖ := by field_simp
  -- continuity of the derivative at `x`
  have hcontD : ContinuousAt (fderiv ℂ f) x := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    set K : ℝ := M / (2 * r) / r with hK
    have hK0 : 0 ≤ K := by positivity
    refine ⟨min r (ε / (K + 1)), lt_min hr (by positivity), fun y hy => ?_⟩
    have hy1 : dist y x < r := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y x < ε / (K + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    have h1 := hlipder y hy1
    rw [dist_eq_norm] at hy2 ⊢
    calc ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ K * ‖y - x‖ := h1
      _ ≤ (K + 1) * ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
      _ < ε := by
        rw [lt_div_iff₀ (by positivity)] at hy2
        linarith
  exact hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
      (hf.differentiableAt (hU.mem_nhds hy)).hasFDerivAt) hcontD

end

end TakhtajanTeo
