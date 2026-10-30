import TakhtajanTeo.Ch1.QCVariationBers

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.QCV
open LiZhongQC

/-- A uniform Cauchy estimate on a smaller ball. -/
theorem qcv_cauchy_shrink {A B : ℂ → ℂ} {y : ℂ} {R r M : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ ball y (R + r), HasDerivAt A (B z) z)
    (hb : ∀ z ∈ ball y (R + r), ‖A z‖ ≤ M) :
    ∀ z ∈ ball y R, ‖B z‖ ≤ M / r := by
  intro z hz
  have hsub : closedBall z r ⊆ ball y (R + r) := by
    intro w hw
    have htri := dist_triangle w z y
    rw [mem_closedBall] at hw
    rw [mem_ball] at hz ⊢
    linarith
  have hz' : z ∈ ball y (R + r) := hsub (mem_closedBall_self hr.le)
  rw [← (hd z hz').deriv]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · have hA : DifferentiableOn ℂ A (closure (ball z r)) := by
      rw [closure_ball _ hr.ne']
      exact fun w hw => (hd w (hsub hw)).differentiableAt.differentiableWithinAt
    exact hA.diffContOnCl
  · intro w hw
    exact hb w (hsub (sphere_subset_closedBall hw))

/-- The normalized kernel at `I` is a single integrable majorant for a whole parameter ball
when the integration point stays outside a larger ball. -/
theorem qcv_ahKer_ball_bound {y : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, u ≠ 0 → u ≠ 1 → u ≠ I → 8 * r ≤ ‖u - y‖ →
      ∀ z ∈ ball y (4 * r), ‖ahKer z u‖ ≤ C * ‖ahKer I u‖ := by
  let L : ℝ := ‖y‖ + 4 * r + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hI1 : I - (1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hIn : 0 < ‖I * (I - 1)‖ := norm_pos_iff.mpr (mul_ne_zero I_ne_zero hI1)
  refine ⟨L ^ 2 * (1 + L / r) / ‖I * (I - 1)‖, by positivity, ?_⟩
  intro u hu0 hu1 huI huy z hz
  have hzy : ‖z - y‖ < 4 * r := by simpa [mem_ball, dist_eq_norm] using hz
  have huz : r ≤ ‖u - z‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub u z y
    linarith
  have huz0 : u - z ≠ 0 := norm_pos_iff.mp (hr.trans_le huz)
  have hzL : ‖z‖ ≤ L := by
    have := norm_le_norm_add_norm_sub' z y
    dsimp [L]
    linarith
  have hz1L : ‖z - 1‖ ≤ L := by
    calc ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z (1 : ℂ)
         _ ≤ L := by
           have := norm_le_norm_add_norm_sub' z y
           dsimp [L]
           linarith
  have hzIL : ‖z - I‖ ≤ L := by
    calc ‖z - I‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z I
         _ ≤ L := by
           have := norm_le_norm_add_norm_sub' z y
           dsimp [L]
           linarith
  have hratio : ‖u - I‖ / ‖u - z‖ ≤ 1 + L / r := by
    have htri := norm_sub_le_norm_sub_add_norm_sub u z I
    calc ‖u - I‖ / ‖u - z‖ ≤ (‖u - z‖ + L) / ‖u - z‖ := by gcongr; linarith
         _ = 1 + L / ‖u - z‖ := by rw [add_div, div_self (ne_of_gt (hr.trans_le huz))]
         _ ≤ 1 + L / r := by gcongr
  have he : ahKer z u = (z * (z - 1) / (I * (I - 1))) *
      ((u - I) / (u - z)) * ahKer I u := by
    unfold ahKer
    field_simp [hu0, sub_ne_zero.mpr hu1, sub_ne_zero.mpr huI, huz0, I_ne_zero, hI1]
    <;> ring
  rw [he, norm_mul, norm_mul, norm_div, norm_div, norm_mul]
  calc (‖z‖ * ‖z - 1‖ / ‖I * (I - 1)‖) * (‖u - I‖ / ‖u - z‖) * ‖ahKer I u‖ ≤
      (L * L / ‖I * (I - 1)‖) * (1 + L / r) * ‖ahKer I u‖ := by gcongr
    _ = _ := by ring

theorem qcv_kernel_ball_majorant {y : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, u ≠ 0 → u ≠ 1 → u ≠ I → 8 * r ≤ ‖u - y‖ →
      ∀ z ∈ ball y r,
        ‖ahKer z u‖ ≤ C * ‖ahKer I u‖ ∧ ‖kerD1 z u‖ ≤ C * ‖ahKer I u‖ ∧
        ‖kerD2 z u‖ ≤ C * ‖ahKer I u‖ ∧ ‖kerD3 z u‖ ≤ C * ‖ahKer I u‖ := by
  obtain ⟨C₀, hC₀, hbase⟩ := qcv_ahKer_ball_bound (y := y) hr
  let C := C₀ + C₀ / r + C₀ / r / r + C₀ / r / r / r
  have hp1 : 0 ≤ C₀ / r := by positivity
  have hp2 : 0 ≤ C₀ / r / r := by positivity
  have hp3 : 0 ≤ C₀ / r / r / r := by positivity
  have hc0 : C₀ ≤ C := by dsimp [C]; linarith
  have hc1 : C₀ / r ≤ C := by dsimp [C]; linarith
  have hc2 : C₀ / r / r ≤ C := by dsimp [C]; linarith
  have hc3 : C₀ / r / r / r ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC₀.le.trans hc0, ?_⟩
  intro u hu0 hu1 huI huy
  have hne : ∀ z ∈ ball y (4 * r), u ≠ z := by
    intro z hz he
    subst u
    have : ‖z - y‖ < 4 * r := by simpa [mem_ball, dist_eq_norm] using hz
    linarith
  have hd0 : ∀ z ∈ ball y (4 * r), HasDerivAt (fun x => ahKer x u) (kerD1 z u) z :=
    fun z hz => qcv_hasDerivAt_ahKer hu0 hu1 (hne z hz)
  have h0 := hbase u hu0 hu1 huI huy
  have h4 : 3 * r + r = 4 * r := by ring
  have h3 : 2 * r + r = 3 * r := by ring
  have h2 : r + r = 2 * r := by ring
  have h1 := qcv_cauchy_shrink (R := 3 * r) hr
    (by simpa only [h4] using hd0) (by simpa only [h4] using h0)
  have hd1 : ∀ z ∈ ball y (3 * r), HasDerivAt (fun x => kerD1 x u) (kerD2 z u) z :=
    fun z hz => qcv_hasDerivAt_kerD1 (hne z (ball_subset_ball (by linarith) hz))
  have htwo := qcv_cauchy_shrink (R := 2 * r) hr
    (by simpa only [h3] using hd1) (by simpa only [h3] using h1)
  have hd2 : ∀ z ∈ ball y (2 * r), HasDerivAt (fun x => kerD2 x u) (kerD3 z u) z :=
    fun z hz => qcv_hasDerivAt_kerD2 (hne z (ball_subset_ball (by linarith) hz))
  have hthree := qcv_cauchy_shrink (R := r) hr
    (by simpa only [h2] using hd2) (by simpa only [h2] using htwo)
  intro z hz
  refine ⟨(h0 z (ball_subset_ball (by linarith) hz)).trans (by gcongr), ?_, ?_, ?_⟩
  · calc ‖kerD1 z u‖ ≤ (C₀ * ‖ahKer I u‖) / r := h1 z (ball_subset_ball (by linarith) hz)
         _ = (C₀ / r) * ‖ahKer I u‖ := by ring
         _ ≤ C * ‖ahKer I u‖ := by gcongr
  · calc ‖kerD2 z u‖ ≤ (C₀ * ‖ahKer I u‖) / r / r := htwo z (ball_subset_ball (by linarith) hz)
         _ = (C₀ / r / r) * ‖ahKer I u‖ := by ring
         _ ≤ C * ‖ahKer I u‖ := by gcongr
  · calc ‖kerD3 z u‖ ≤ (C₀ * ‖ahKer I u‖) / r / r / r := hthree z hz
         _ = (C₀ / r / r / r) * ‖ahKer I u‖ := by ring
         _ ≤ C * ‖ahKer I u‖ := by gcongr

theorem qcv_integral_deriv_off_support {κ : ℂ → ℂ} {k r C : ℝ} {y : ℂ}
    (hk : 0 ≤ k) (hr : 0 < r) (hC : 0 ≤ C) (hκ : IsBeltramiCoeff κ univ k)
    (hzero : ∀ u ∈ ball y (8 * r), κ u = 0) {A B : ℂ → ℂ → ℂ}
    (hAm : ∀ z, Measurable (A z)) (hBm : ∀ z, Measurable (B z))
    (hbound : ∀ u : ℂ, u ≠ 0 → u ≠ 1 → u ≠ I → 8 * r ≤ ‖u - y‖ →
      ∀ z ∈ ball y r, ‖A z u‖ ≤ C * ‖ahKer I u‖ ∧ ‖B z u‖ ≤ C * ‖ahKer I u‖)
    (hd : ∀ u : ℂ, u ≠ 0 → u ≠ 1 → u ≠ I → 8 * r ≤ ‖u - y‖ →
      ∀ z ∈ ball y r, HasDerivAt (fun x => A x u) (B z u) z) :
    ∀ z ∈ ball y r, HasDerivAt (fun x => ∫ u, κ u * A x u) (∫ u, κ u * B z u) z := by
  have hκm : AEStronglyMeasurable κ volume := by simpa using hκ.1
  have hκb : ∀ᵐ u : ℂ, ‖κ u‖ ≤ k := by simpa using hκ.2
  have hgood : ∀ᵐ u : ℂ, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ I := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (show volume ({0} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({1} : Set ℂ) = 0 by simp),
      measure_eq_zero_iff_ae_notMem.mp (show volume ({I} : Set ℂ) = 0 by simp)] with u h0 h1 hI
    exact ⟨h0, h1, hI⟩
  have hfar : ∀ u, κ u ≠ 0 → 8 * r ≤ ‖u - y‖ := by
    intro u hu
    by_contra h
    exact hu (hzero u (by simpa [mem_ball, dist_eq_norm] using lt_of_not_ge h))
  have hbound' : ∀ᵐ u : ℂ, ∀ z ∈ ball y r,
      ‖κ u * A z u‖ ≤ k * (C * ‖ahKer I u‖) ∧ ‖κ u * B z u‖ ≤ k * (C * ‖ahKer I u‖) := by
    filter_upwards [hκb, hgood] with u hκu hu
    intro z hz
    by_cases h0 : κ u = 0
    · simp only [h0, zero_mul, norm_zero]
      exact ⟨by positivity, by positivity⟩
    · obtain ⟨hA, hB⟩ := hbound u hu.1 hu.2.1 hu.2.2 (hfar u h0) z hz
      simp only [norm_mul]
      exact ⟨mul_le_mul hκu hA (norm_nonneg _) hk, mul_le_mul hκu hB (norm_nonneg _) hk⟩
  have hdom : Integrable (fun u => k * (C * ‖ahKer I u‖)) :=
    ((ah_ker_integrable I).norm.const_mul C).const_mul k
  have hAi : ∀ z ∈ ball y r, Integrable (fun u => κ u * A z u) := by
    intro z hz
    apply hdom.mono' (hκm.mul (hAm z).aestronglyMeasurable)
    filter_upwards [hbound'] with u hu using (hu z hz).1
  intro z hz
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x u => κ u * A x u) (F' := fun x u => κ u * B x u)
    (bound := fun u => k * (C * ‖ahKer I u‖)) (isOpen_ball.mem_nhds hz)
    (by filter_upwards [isOpen_ball.mem_nhds hz] with x hx using (hAi x hx).aestronglyMeasurable)
    (hAi z hz) (hκm.mul (hBm z).aestronglyMeasurable)
    (by filter_upwards [hbound'] with u hu using fun x hx => (hu x hx).2)
    hdom ?_).2
  filter_upwards [hgood] with u hu
  intro x hx
  by_cases h0 : κ u = 0
  · simpa only [h0, zero_mul] using hasDerivAt_const x (0 : ℂ)
  · exact (hd u hu.1 hu.2.1 hu.2.2 (hfar u h0) x hx).const_mul (κ u)

/-- Three successive differentiations under the integral on an arbitrary open zero set
of a bounded coefficient. The bounds above are uniform on a neighborhood of each point. -/
theorem qcv_ahVar_kernel_derivatives {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ}
    (hk : 0 ≤ k) (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U)
    (hzero : ∀ u ∈ U, κ u = 0) {y : ℂ} (hy : y ∈ U) :
    HasDerivAt (fun z => ∫ u, κ u * ahKer z u) (∫ u, κ u * kerD1 y u) y ∧
      HasDerivAt (fun z => ∫ u, κ u * kerD1 z u) (∫ u, κ u * kerD2 y u) y ∧
      HasDerivAt (fun z => ∫ u, κ u * kerD2 z u) (∫ u, κ u * kerD3 y u) y := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hy
  let r := ε / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have h8 : 8 * r = ε := by dsimp [r]; ring
  have hzero8 : ∀ u ∈ ball y (8 * r), κ u = 0 := by
    intro u hu
    exact hzero u (hball (by simpa only [h8] using hu))
  obtain ⟨C, hC, hmaj⟩ := qcv_kernel_ball_majorant (y := y) hr
  have hne : ∀ u : ℂ, 8 * r ≤ ‖u - y‖ → ∀ z ∈ ball y r, u ≠ z := by
    intro u hu z hz he
    subst u
    have : ‖z - y‖ < r := by simpa [mem_ball, dist_eq_norm] using hz
    linarith
  have hm0 : ∀ z : ℂ, Measurable (ahKer z) := ahK_measurable
  have hm1 : ∀ z : ℂ, Measurable (kerD1 z) := fun z => by unfold kerD1; fun_prop
  have hm2 : ∀ z : ℂ, Measurable (kerD2 z) := fun z => by unfold kerD2; fun_prop
  have hm3 : ∀ z : ℂ, Measurable (kerD3 z) := fun z => by unfold kerD3; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · apply qcv_integral_deriv_off_support hk hr hC hκ hzero8 hm0 hm1
      (fun u h0 h1 hI hu z hz => ⟨(hmaj u h0 h1 hI hu z hz).1, (hmaj u h0 h1 hI hu z hz).2.1⟩)
      (fun u h0 h1 _ hu z hz => qcv_hasDerivAt_ahKer h0 h1 (hne u hu z hz)) y (mem_ball_self hr)
  · apply qcv_integral_deriv_off_support hk hr hC hκ hzero8 hm1 hm2
      (fun u h0 h1 hI hu z hz => ⟨(hmaj u h0 h1 hI hu z hz).2.1, (hmaj u h0 h1 hI hu z hz).2.2.1⟩)
      (fun u _ _ _ hu z hz => qcv_hasDerivAt_kerD1 (hne u hu z hz)) y (mem_ball_self hr)
  · apply qcv_integral_deriv_off_support hk hr hC hκ hzero8 hm2 hm3
      (fun u h0 h1 hI hu z hz => (hmaj u h0 h1 hI hu z hz).2.2)
      (fun u _ _ _ hu z hz => qcv_hasDerivAt_kerD2 (hne u hu z hz)) y (mem_ball_self hr)

theorem qcv_ahVar_holomorphic {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ}
    (hk : 0 ≤ k) (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U)
    (hzero : ∀ u ∈ U, κ u = 0) : DifferentiableOn ℂ (ahVar κ) U := by
  intro y hy
  exact ((qcv_ahVar_kernel_derivatives hk hκ hU hzero hy).1.const_mul
    (-(1 / π : ℂ))).differentiableAt.differentiableWithinAt

/-- The universal fourth-kernel formula, with no special shape or boundedness assumption on U. -/
theorem qcv_ahVar_iter3 {κ : ℂ → ℂ} {k : ℝ} {U : Set ℂ}
    (hk : 0 ≤ k) (hκ : IsBeltramiCoeff κ univ k) (hU : IsOpen U)
    (hzero : ∀ u ∈ U, κ u = 0) {y : ℂ} (hy : y ∈ U) :
    iteratedDeriv 3 (ahVar κ) y = -(6 / π) * ∫ u, κ u / (u - y) ^ 4 := by
  have e1 : deriv (fun z => ∫ u, κ u * ahKer z u) =ᶠ[𝓝 y]
      (fun z => ∫ u, κ u * kerD1 z u) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (qcv_ahVar_kernel_derivatives hk hκ hU hzero hz).1.deriv
  have e2 : deriv (fun z => ∫ u, κ u * kerD1 z u) =ᶠ[𝓝 y]
      (fun z => ∫ u, κ u * kerD2 z u) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (qcv_ahVar_kernel_derivatives hk hκ hU hzero hz).2.1.deriv
  have e3 := (qcv_ahVar_kernel_derivatives hk hκ hU hzero hy).2.2.deriv
  have h3 : iteratedDeriv 3 (fun z => ∫ u, κ u * ahKer z u) y =
      ∫ u, κ u * kerD3 y u := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero]
    exact (e1.deriv.trans e2).deriv_eq.trans e3
  have hI : (∫ u, κ u * kerD3 y u) = 6 * ∫ u, κ u / (u - y) ^ 4 := by
    rw [← integral_const_mul]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro u
    simp only [kerD3]
    ring
  unfold ahVar
  rw [iteratedDeriv_const_mul_field, h3, hI]
  ring

end TakhtajanTeo.QCV
