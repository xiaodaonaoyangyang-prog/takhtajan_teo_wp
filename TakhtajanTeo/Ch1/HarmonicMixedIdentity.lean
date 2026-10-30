import TakhtajanTeo.Ch1.HarmonicDiagonalIdentity

/-!
# Mixed diagonal identity for the centered resolvent kernel (Corollary 6.4 support)

Four-term polarization of `wp_diagonal_kernel_identity`: for weighted-bounded disk holomorphic `F, G`,
the double integral of `conj F ρ⁻¹ ⊗ G ρ⁻¹` against `(1 - u v̄)⁻² + (1 - u v̄)⁻¹` equals
`(π²/2)` times the centered resolvent pairing `∫ G(0, w) conj F G ρ⁻¹`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

theorem wp_conj_mul_self (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Four-term polarization of `conj x * y` through squared norms. -/
theorem wp_polar_pt (x y : ℂ) :
    conj x * y = (1 / 4 : ℂ) * (((‖x + y‖ ^ 2 : ℝ) : ℂ) - ((‖x - y‖ ^ 2 : ℝ) : ℂ) -
      I * ((‖x + I * y‖ ^ 2 : ℝ) : ℂ) + I * ((‖x - I * y‖ ^ 2 : ℝ) : ℂ)) := by
  rw [← wp_conj_mul_self, ← wp_conj_mul_self, ← wp_conj_mul_self, ← wp_conj_mul_self]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem wp_polar_double_pt (a b c d : ℂ) :
    conj a * d = (1 / 4 : ℂ) * (conj (a + c) * (b + d) - conj (a - c) * (b - d) -
      I * (conj (a + I * c) * (b + I * d)) + I * (conj (a - I * c) * (b - I * d))) := by
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem wp_weighted_linear_bound {F G : ℂ → ℂ} {M N : ℝ}
    (hF : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    (hG : ∀ w ∈ unitDisc, ‖G w‖ * (rho w)⁻¹ ≤ N) (α β : ℂ) :
    ∀ w ∈ unitDisc, ‖α * F w + β * G w‖ * (rho w)⁻¹ ≤ ‖α‖ * M + ‖β‖ * N := by
  intro w hw
  have hr : 0 ≤ (rho w)⁻¹ := by unfold rho; positivity
  calc
    _ ≤ (‖α * F w‖ + ‖β * G w‖) * (rho w)⁻¹ :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) hr
    _ = ‖α‖ * (‖F w‖ * (rho w)⁻¹) + ‖β‖ * (‖G w‖ * (rho w)⁻¹) := by
      simp only [norm_mul]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hF w hw) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hG w hw) (norm_nonneg _))

theorem wp_linear_series_combination {F G : ℂ → ℂ} {c d : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hd : ∀ w ∈ unitDisc, HasSum (fun n => d n * w ^ n) (G w)) (α β : ℂ) :
    ∀ w ∈ unitDisc, HasSum (fun n => (α * c n + β * d n) * w ^ n) (α * F w + β * G w) := by
  intro w hw
  convert ((hc w hw).mul_left α).add ((hd w hw).mul_left β) using 1
  funext n
  ring

/-- Integrability of the diagonal double-kernel integrand. -/
theorem wp_diag_pair_integrable {F : ℂ → ℂ} (hf : Measurable F) {M : ℝ}
    (hB : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M) :
    Integrable (fun p : ℂ × ℂ => (conj (F p.1) * (rho p.1 : ℂ)⁻¹) *
      (F p.2 * (rho p.2 : ℂ)⁻¹) *
        (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹))
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
  have hρ : Measurable (fun w : ℂ => (rho w : ℂ)⁻¹) := by
    have : Measurable rho :=
      measurable_const.div ((measurable_const.sub (measurable_norm.pow_const 2)).pow_const 2)
    exact (Complex.measurable_ofReal.comp this).inv
  have hfb (w : ℂ) (hw : w ∈ unitDisc) : ‖conj (F w) * (rho w : ℂ)⁻¹‖ ≤ M := by
    have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
    simpa only [norm_mul, norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hB w hw
  have hgb (w : ℂ) (hw : w ∈ unitDisc) : ‖F w * (rho w : ℂ)⁻¹‖ ≤ M := by
    have hr := rho_pos_of_norm_ne_one (mem_ball_zero_iff.mp hw).ne
    simpa only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hB w hw
  have hfm : Measurable (fun u => conj (F u) * (rho u : ℂ)⁻¹) :=
    (Complex.continuous_conj.measurable.comp hf).mul hρ
  have hgm : Measurable (fun u => F u * (rho u : ℂ)⁻¹) := hf.mul hρ
  exact wp_double_kernel_weighted_integrable (f := fun u => conj (F u) * (rho u : ℂ)⁻¹)
    (g := fun u => F u * (rho u : ℂ)⁻¹) hfm hgm hfb hgb

/-- All hypotheses of the diagonal identity for `F + β G`. -/
theorem wp_diag_combo {F G : ℂ → ℂ} {c d : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hd : ∀ w ∈ unitDisc, HasSum (fun n => d n * w ^ n) (G w))
    (hFc : ContinuousOn F unitDisc) (hGc : ContinuousOn G unitDisc)
    (hFm : Measurable F) (hGm : Measurable G) {M N : ℝ}
    (hBF : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    (hBG : ∀ w ∈ unitDisc, ‖G w‖ * (rho w)⁻¹ ≤ N) (β : ℂ) :
    Integrable (fun p : ℂ × ℂ => (conj (F p.1 + β * G p.1) * (rho p.1 : ℂ)⁻¹) *
      ((F p.2 + β * G p.2) * (rho p.2 : ℂ)⁻¹) *
        (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹))
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) ∧
    (∫ p : ℂ × ℂ, (conj (F p.1 + β * G p.1) * (rho p.1 : ℂ)⁻¹) *
      ((F p.2 + β * G p.2) * (rho p.2 : ℂ)⁻¹) *
        (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      (π ^ 2 / 2 : ℂ) * ((∫ w in unitDisc,
        resolventKernel 0 w * ‖F w + β * G w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ) := by
  have hs := wp_linear_series_combination hc hd 1 β
  have hB := wp_weighted_linear_bound hBF hBG 1 β
  have hm : Measurable (fun w => 1 * F w + β * G w) :=
    (measurable_const.mul hFm).add (measurable_const.mul hGm)
  have hcont : ContinuousOn (fun w => 1 * F w + β * G w) unitDisc :=
    (continuousOn_const.mul hFc).add (continuousOn_const.mul hGc)
  have h1 := wp_diag_pair_integrable hm hB
  have h2 := wp_diagonal_kernel_identity hs hcont hm hB
  simp only [one_mul] at h1 h2
  exact ⟨h1, h2⟩

theorem wp_integral_four_term {X : Type*} [MeasurableSpace X] {m : Measure X}
    (T1 T2 T3 T4 : X → ℂ) (h1 : Integrable T1 m) (h2 : Integrable T2 m)
    (h3 : Integrable T3 m) (h4 : Integrable T4 m) :
    (∫ x, (1 / 4 : ℂ) * (T1 x - T2 x - I * T3 x + I * T4 x) ∂m) =
      (1 / 4 : ℂ) * ((∫ x, T1 x ∂m) - (∫ x, T2 x ∂m) - I * (∫ x, T3 x ∂m) +
        I * (∫ x, T4 x ∂m)) := by
  have h12 : Integrable (fun x => T1 x - T2 x) m := h1.sub h2
  have h3' : Integrable (fun x => I * T3 x) m := h3.const_mul I
  have h4' : Integrable (fun x => I * T4 x) m := h4.const_mul I
  have h123 : Integrable (fun x => T1 x - T2 x - I * T3 x) m := h12.sub h3'
  rw [integral_const_mul, integral_add h123 h4', integral_sub h12 h3', integral_sub h1 h2,
    integral_const_mul, integral_const_mul]

theorem wp_comb_quad_int {F G : ℂ → ℂ} (hFm : Measurable F) (hGm : Measurable G) {M N : ℝ}
    (hBF : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    (hBG : ∀ w ∈ unitDisc, ‖G w‖ * (rho w)⁻¹ ≤ N) (β : ℂ) :
    Integrable (fun w => resolventKernel 0 w * ‖F w + β * G w‖ ^ 2 * (rho w)⁻¹)
      (volume.restrict unitDisc) := by
  have hzero : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hB := wp_weighted_linear_bound hBF hBG 1 β
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (by unfold rho; positivity)).trans (hBF 0 hzero)
  have hN0 : 0 ≤ N := (mul_nonneg (norm_nonneg _) (by unfold rho; positivity)).trans (hBG 0 hzero)
  have hm : Measurable (fun w => F w + β * G w) := hFm.add (measurable_const.mul hGm)
  exact wp_resolvent_quadratic_integrable (F := fun w => F w + β * G w) hm
    (M := ‖(1 : ℂ)‖ * M + ‖β‖ * N) (by positivity) (by simpa using hB) hzero

theorem wp_mixed_diagonal_kernel_identity {F G : ℂ → ℂ} {c d : ℕ → ℂ}
    (hc : ∀ w ∈ unitDisc, HasSum (fun n => c n * w ^ n) (F w))
    (hd : ∀ w ∈ unitDisc, HasSum (fun n => d n * w ^ n) (G w))
    (hFc : ContinuousOn F unitDisc) (hGc : ContinuousOn G unitDisc)
    (hFm : Measurable F) (hGm : Measurable G) {M N : ℝ}
    (hBF : ∀ w ∈ unitDisc, ‖F w‖ * (rho w)⁻¹ ≤ M)
    (hBG : ∀ w ∈ unitDisc, ‖G w‖ * (rho w)⁻¹ ≤ N) :
    (∫ p : ℂ × ℂ, (conj (F p.1) * (rho p.1 : ℂ)⁻¹) * (G p.2 * (rho p.2 : ℂ)⁻¹) *
      (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)
      ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc))) =
      (π ^ 2 / 2 : ℂ) * ∫ w in unitDisc,
        (resolventKernel 0 w : ℂ) * (conj (F w) * G w) * (rho w : ℂ)⁻¹ := by
  obtain ⟨i1, e1⟩ := wp_diag_combo hc hd hFc hGc hFm hGm hBF hBG 1
  obtain ⟨i2, e2⟩ := wp_diag_combo hc hd hFc hGc hFm hGm hBF hBG (-1)
  obtain ⟨i3, e3⟩ := wp_diag_combo hc hd hFc hGc hFm hGm hBF hBG I
  obtain ⟨i4, e4⟩ := wp_diag_combo hc hd hFc hGc hFm hGm hBF hBG (-I)
  have hpt : ∀ p : ℂ × ℂ, (conj (F p.1) * (rho p.1 : ℂ)⁻¹) * (G p.2 * (rho p.2 : ℂ)⁻¹) *
      (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹) =
      (1 / 4 : ℂ) * (
        ((conj (F p.1 + 1 * G p.1) * (rho p.1 : ℂ)⁻¹) * ((F p.2 + 1 * G p.2) * (rho p.2 : ℂ)⁻¹) *
          (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)) -
        ((conj (F p.1 + (-1) * G p.1) * (rho p.1 : ℂ)⁻¹) *
          ((F p.2 + (-1) * G p.2) * (rho p.2 : ℂ)⁻¹) *
          (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)) -
        I * ((conj (F p.1 + I * G p.1) * (rho p.1 : ℂ)⁻¹) *
          ((F p.2 + I * G p.2) * (rho p.2 : ℂ)⁻¹) *
          (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹)) +
        I * ((conj (F p.1 + (-I) * G p.1) * (rho p.1 : ℂ)⁻¹) *
          ((F p.2 + (-I) * G p.2) * (rho p.2 : ℂ)⁻¹) *
          (((1 - p.1 * conj p.2)⁻¹) ^ 2 + (1 - p.1 * conj p.2)⁻¹))) := by
    intro p
    have hr1 : conj ((rho p.1 : ℂ)⁻¹) = (rho p.1 : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I, hr1]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hsc : ∀ w : ℂ, (resolventKernel 0 w : ℂ) * (conj (F w) * G w) * (rho w : ℂ)⁻¹ =
      (1 / 4 : ℂ) * (
        ((resolventKernel 0 w * ‖F w + 1 * G w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ) -
        ((resolventKernel 0 w * ‖F w + (-1) * G w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ) -
        I * ((resolventKernel 0 w * ‖F w + I * G w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ) +
        I * ((resolventKernel 0 w * ‖F w + (-I) * G w‖ ^ 2 * (rho w)⁻¹ : ℝ) : ℂ)) := by
    intro w
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    rw [← wp_conj_mul_self (F w + 1 * G w), ← wp_conj_mul_self (F w + (-1) * G w),
      ← wp_conj_mul_self (F w + I * G w), ← wp_conj_mul_self (F w + (-I) * G w)]
    simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]
    ring
  have q1 := (wp_comb_quad_int hFm hGm hBF hBG 1).ofReal (𝕜 := ℂ)
  have q2 := (wp_comb_quad_int hFm hGm hBF hBG (-1)).ofReal (𝕜 := ℂ)
  have q3 := (wp_comb_quad_int hFm hGm hBF hBG I).ofReal (𝕜 := ℂ)
  have q4 := (wp_comb_quad_int hFm hGm hBF hBG (-I)).ofReal (𝕜 := ℂ)
  have hL := wp_integral_four_term _ _ _ _ i1 i2 i3 i4
  have hR := wp_integral_four_term _ _ _ _ q1 q2 q3 q4
  rw [(integral_congr_ae (ae_of_all _ hpt)).trans hL,
    (integral_congr_ae (ae_of_all _ hsc)).trans hR, e1, e2, e3, e4]
  simp only [integral_ofReal]
  have key : ∀ a b c d : ℂ, (1 / 4 : ℂ) * ((π ^ 2 / 2 : ℂ) * a - (π ^ 2 / 2 : ℂ) * b -
      I * ((π ^ 2 / 2 : ℂ) * c) + I * ((π ^ 2 / 2 : ℂ) * d)) =
      (π ^ 2 / 2 : ℂ) * ((1 / 4 : ℂ) * (a - b - I * c + I * d)) := by
    intro a b c d
    ring
  exact key _ _ _ _

end TakhtajanTeo
