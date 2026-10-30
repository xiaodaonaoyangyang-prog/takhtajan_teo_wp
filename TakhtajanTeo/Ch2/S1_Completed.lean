import TakhtajanTeo.Ch2.S1_UnivalentFunctions

/-!
# Ch2 §1 completed originals (`s2c_` copies)

`s2c_<name>` copies of `S1_UnivalentFunctions` originals, with byte-identical statements, proved downstream so that
`S1_UnivalentFunctions` does not change. The leader relocates each proved statement at an integration window.

Contents: Remark 1.2 (`s2c_remark_1_2`): `𝒜(f) ∈ A∞¹` for `f` univalent on `𝔻` (Koebe/Bieberbach), for `g` univalent at
`∞` (Bieberbach on discs around `u` near the circle, decay `O(z⁻²)` from the inverted function `1/g(1/s)` near `∞`), and
`Ψ(A∞¹) ⊂ A∞` on `𝔻` and, with `O(z⁻³)` decay, on `𝔻*` (Cauchy estimates).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo.Ch2
open LiZhongQC

/-- Cauchy estimate on a closed disc inside an open set. -/
theorem s2c_deriv_bound {ψ : ℂ → ℂ} {U : Set ℂ} (hψ : DifferentiableOn ℂ ψ U)
    {c : ℂ} {r M : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ U)
    (hM : ∀ u ∈ sphere c r, ‖ψ u‖ ≤ M) : ‖deriv ψ c‖ ≤ M / r := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr _ hM
  have : DifferentiableOn ℂ ψ (closure (ball c r)) := by
    rw [closure_ball c hr.ne']
    exact hψ.mono hsub
  exact this.diffContOnCl

/-- The weighted norm `‖(1 - |z|²) x‖` as a product of norms. -/
theorem s2c_wnorm (z x : ℂ) : ‖(1 - (‖z‖ : ℂ) ^ 2) * x‖ = |1 - ‖z‖ ^ 2| * ‖x‖ := by
  have : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Weighted derivative bound on the disc. -/
theorem s2c_psi_deriv_disc {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ unitDisc) {C0 : ℝ}
    (hC0 : ∀ z ∈ unitDisc, ‖(1 - (‖z‖ : ℂ) ^ 2) * ψ z‖ ≤ C0) {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv ψ z‖ ≤ 16 * C0 := by
  have ht : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht0 := norm_nonneg z
  have hC0nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 0 (mem_ball_self one_pos))
  set r : ℝ := (1 - ‖z‖) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hsub : closedBall z r ⊆ unitDisc := by
    intro u hu
    have h1 : ‖u - z‖ ≤ r := by simpa [dist_eq_norm] using hu
    have h2 : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by
      calc ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
    exact mem_ball_zero_iff.mpr (by rw [hr] at h1; linarith)
  have hsph : ∀ u ∈ sphere z r, ‖ψ u‖ ≤ C0 / r := by
    intro u hu
    have hu' : u ∈ unitDisc := hsub (sphere_subset_closedBall hu)
    have h1 : ‖u - z‖ = r := by simpa [dist_eq_norm] using hu
    have h2 : ‖u‖ ≤ ‖z‖ + r := by
      calc ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + r := by rw [h1]; ring
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu'
    have hw := hC0 u hu'
    rw [s2c_wnorm, abs_of_nonneg (by nlinarith [norm_nonneg u])] at hw
    have hpos : r ≤ 1 - ‖u‖ ^ 2 := by
      have h3 : 0 ≤ ‖u‖ * (1 - ‖u‖) := mul_nonneg (norm_nonneg _) (by linarith)
      have h4 : r ≤ 1 - ‖u‖ := by rw [hr] at h2 ⊢; linarith
      nlinarith
    rw [le_div_iff₀ hr0]
    calc ‖ψ u‖ * r ≤ ‖ψ u‖ * (1 - ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hpos (norm_nonneg _)
      _ = (1 - ‖u‖ ^ 2) * ‖ψ u‖ := by ring
      _ ≤ C0 := hw
  have hder := s2c_deriv_bound hd hr0 hsub hsph
  have h1t : 0 < 1 - ‖z‖ := by linarith
  calc (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv ψ z‖ ≤ (1 - ‖z‖ ^ 2) ^ 2 * (C0 / r / r) :=
        mul_le_mul_of_nonneg_left hder (sq_nonneg _)
    _ = 4 * C0 * (1 + ‖z‖) ^ 2 := by rw [hr]; field_simp; ring
    _ ≤ 16 * C0 := by
        have h4 : (1 + ‖z‖) ^ 2 ≤ 4 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h4 hC0nn]

/-- Clause 1 of `remark_1_2`. -/
theorem s2c_remark_1_2_univalent_disc {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hi : InjOn f unitDisc) : preSchwarzian f ∈ AInf1fun unitDisc := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hA : AnalyticOnNhd ℂ f unitDisc := hf.analyticOnNhd hU
  have hne : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hU hf hi hz
  refine ⟨?_, 6, ?_⟩
  · intro z hz
    have h1 : AnalyticAt ℂ (deriv (deriv f)) z := (hA z hz).deriv.deriv
    have h2 : AnalyticAt ℂ (deriv f) z := (hA z hz).deriv
    exact (h1.div h2 (hne z hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hk := kb_koebe_transform_ineq hf hi hz
    have ht : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have e : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z = (1 - (‖z‖ : ℂ) ^ 2) * preSchwarzian f z := by
      unfold preSchwarzian
      push_cast
      ring
    rw [e] at hk
    have h2 : ‖2 * (starRingEnd ℂ) z‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_conj]
      norm_num
      linarith
    calc ‖(1 - (‖z‖ : ℂ) ^ 2) * preSchwarzian f z‖
        = ‖((1 - (‖z‖ : ℂ) ^ 2) * preSchwarzian f z - 2 * (starRingEnd ℂ) z) + 2 * (starRingEnd ℂ) z‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖(1 - (‖z‖ : ℂ) ^ 2) * preSchwarzian f z - 2 * (starRingEnd ℂ) z‖ + ‖2 * (starRingEnd ℂ) z‖ :=
          norm_add_le _ _
      _ ≤ 6 := by linarith

/-- The squared weight as a product of norms. -/
theorem s2c_wnorm2 (z x : ℂ) : ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * x‖ = (1 - ‖z‖ ^ 2) ^ 2 * ‖x‖ := by
  have h : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- `Ψ(ψ)` is holomorphic when `ψ` is. -/
theorem s2c_PsiOp_differentiableOn {ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ ψ U) :
    DifferentiableOn ℂ (PsiOp ψ) U := by
  have hA : AnalyticOnNhd ℂ ψ U := hd.analyticOnNhd hU
  intro z hz
  have h1 : AnalyticAt ℂ (deriv ψ) z := (hA z hz).deriv
  have h2 : AnalyticAt ℂ ψ z := hA z hz
  unfold PsiOp
  exact (h1.sub (analyticAt_const.mul (h2.pow 2))).differentiableAt.differentiableWithinAt

/-- The weighted derivative bound gives the `A∞` representative of `Ψ(ψ)` on the disc (clause 3). -/
theorem s2c_remark_1_2_psi_disc {ψ : ℂ → ℂ} (hψ : ψ ∈ AInf1fun unitDisc) :
    ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = PsiOp ψ z := by
  obtain ⟨hd, C0, hC0⟩ := hψ
  have hC0nn : 0 ≤ C0 := le_trans (norm_nonneg _) (hC0 0 (mem_ball_self one_pos))
  have hPd := s2c_PsiOp_differentiableOn (isOpen_ball : IsOpen unitDisc) hd
  have hbound : ∀ z ∈ unitDisc, ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * PsiOp ψ z‖ ≤ 16 * C0 + C0 ^ 2 / 2 := by
    intro z hz
    have ht : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hw := hC0 z hz
    rw [s2c_wnorm, abs_of_nonneg (by nlinarith [norm_nonneg z])] at hw
    have hder := s2c_psi_deriv_disc hd hC0 hz
    rw [s2c_wnorm2]
    have hP : ‖PsiOp ψ z‖ ≤ ‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2 := by
      unfold PsiOp
      calc ‖deriv ψ z - 1 / 2 * ψ z ^ 2‖ ≤ ‖deriv ψ z‖ + ‖1 / 2 * ψ z ^ 2‖ := norm_sub_le _ _
        _ = ‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2 := by
          rw [norm_mul, norm_pow]; norm_num; ring
    have hsq : ((1 - ‖z‖ ^ 2) * ‖ψ z‖) ^ 2 ≤ C0 ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by nlinarith [norm_nonneg z]) (norm_nonneg _)) hw 2
    have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
    calc (1 - ‖z‖ ^ 2) ^ 2 * ‖PsiOp ψ z‖
        ≤ (1 - ‖z‖ ^ 2) ^ 2 * (‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2) := mul_le_mul_of_nonneg_left hP h0
      _ = (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv ψ z‖ + ((1 - ‖z‖ ^ 2) * ‖ψ z‖) ^ 2 / 2 := by ring
      _ ≤ 16 * C0 + C0 ^ 2 / 2 := by linarith
  obtain ⟨f, hf, -⟩ := TakhtajanTeo.exists_AInf_representative_of_bound (D := unitDisc)
    (fun z hz => ne_of_lt (mem_ball_zero_iff.mp hz)) hPd (C := 16 * C0 + C0 ^ 2 / 2)
    (by positivity) hbound
  exact ⟨f, hf⟩

/-- Weighted derivative bound on the exterior, near the circle. -/
theorem s2c_psi_deriv_ext_near {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ unitDiscExterior) {C0 : ℝ}
    (hC0 : ∀ z ∈ unitDiscExterior, ‖(1 - (‖z‖ : ℂ) ^ 2) * ψ z‖ ≤ C0) {z : ℂ}
    (hz : z ∈ unitDiscExterior) :
    (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ ≤ 4 * C0 * (‖z‖ + 1) ^ 2 := by
  have ht : 1 < ‖z‖ := hz
  have hC0nn : 0 ≤ C0 := by
    have := hC0 (2 : ℂ) (by show 1 < ‖(2 : ℂ)‖; norm_num)
    exact le_trans (norm_nonneg _) this
  set r : ℝ := (‖z‖ - 1) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hlow : ∀ u ∈ closedBall z r, (‖z‖ + 1) / 2 ≤ ‖u‖ := by
    intro u hu
    have h1 : ‖u - z‖ ≤ r := by simpa [dist_eq_norm] using hu
    have h2 : ‖z‖ ≤ ‖u‖ + ‖u - z‖ := by
      calc ‖z‖ = ‖u - (u - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - z‖ := by simpa using norm_sub_le u (u - z)
    rw [hr] at h1
    linarith
  have hsub : closedBall z r ⊆ unitDiscExterior := by
    intro u hu
    have := hlow u hu
    show 1 < ‖u‖
    linarith
  have hsph : ∀ u ∈ sphere z r, ‖ψ u‖ ≤ C0 / r := by
    intro u hu
    have hu' : u ∈ unitDiscExterior := hsub (sphere_subset_closedBall hu)
    have hu1 : 1 < ‖u‖ := hu'
    have hlo := hlow u (sphere_subset_closedBall hu)
    have hw := hC0 u hu'
    rw [s2c_wnorm, abs_of_nonpos (by nlinarith)] at hw
    have hpos : r ≤ ‖u‖ ^ 2 - 1 := by
      have h3 : 0 ≤ (‖u‖ - 1) * ‖u‖ := mul_nonneg (by linarith) (by linarith)
      have h4 : r ≤ ‖u‖ - 1 := by rw [hr]; linarith
      nlinarith
    rw [le_div_iff₀ hr0]
    calc ‖ψ u‖ * r ≤ ‖ψ u‖ * (‖u‖ ^ 2 - 1) := mul_le_mul_of_nonneg_left hpos (norm_nonneg _)
      _ = -(1 - ‖u‖ ^ 2) * ‖ψ u‖ := by ring
      _ ≤ C0 := hw
  have hder := s2c_deriv_bound hd hr0 hsub hsph
  have h1t : 0 < ‖z‖ - 1 := by linarith
  calc (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ ≤ (‖z‖ ^ 2 - 1) ^ 2 * (C0 / r / r) :=
        mul_le_mul_of_nonneg_left hder (sq_nonneg _)
    _ = 4 * C0 * (‖z‖ + 1) ^ 2 := by rw [hr]; field_simp; ring
    _ ≤ 4 * C0 * (‖z‖ + 1) ^ 2 := le_refl _

/-- Weighted derivative bound on the exterior, far from the circle, under `O(z⁻³)` decay. -/
theorem s2c_psi_deriv_ext_far {ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ ψ unitDiscExterior) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hdec : ∀ u : ℂ, R < ‖u‖ → ‖ψ u‖ ≤ C / ‖u‖ ^ 3) {z : ℂ}
    (hz : 2 * R < ‖z‖) : (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ ≤ 16 * C := by
  have hz0 : 0 < ‖z‖ := by linarith
  set r : ℝ := ‖z‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hlow : ∀ u ∈ closedBall z r, ‖z‖ / 2 ≤ ‖u‖ := by
    intro u hu
    have h1 : ‖u - z‖ ≤ r := by simpa [dist_eq_norm] using hu
    have h2 : ‖z‖ ≤ ‖u‖ + ‖u - z‖ := by
      calc ‖z‖ = ‖u - (u - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖u‖ + ‖u - z‖ := by simpa using norm_sub_le u (u - z)
    rw [hr] at h1
    linarith
  have hsub : closedBall z r ⊆ unitDiscExterior := by
    intro u hu
    have := hlow u hu
    show 1 < ‖u‖
    linarith
  have hsph : ∀ u ∈ sphere z r, ‖ψ u‖ ≤ (8 * C / ‖z‖ ^ 3) := by
    intro u hu
    have hlo := hlow u (sphere_subset_closedBall hu)
    have hRu : R < ‖u‖ := by linarith
    have h1 := hdec u hRu
    have hu0 : 0 < ‖u‖ := by linarith
    calc ‖ψ u‖ ≤ C / ‖u‖ ^ 3 := h1
      _ ≤ C / (‖z‖ / 2) ^ 3 := by
        apply div_le_div_of_nonneg_left hC (by positivity)
        exact pow_le_pow_left₀ (by positivity) hlo 3
      _ = 8 * C / ‖z‖ ^ 3 := by field_simp; ring
  have hder := s2c_deriv_bound hd hr0 hsub hsph
  calc (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ ≤ ‖z‖ ^ 4 * ‖deriv ψ z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have : 1 ≤ ‖z‖ ^ 2 := by nlinarith
        nlinarith
    _ ≤ ‖z‖ ^ 4 * (8 * C / ‖z‖ ^ 3 / r) :=
        mul_le_mul_of_nonneg_left hder (by positivity)
    _ = 16 * C := by rw [hr]; field_simp; ring

/-- Clause 4 of `remark_1_2`. -/
theorem s2c_remark_1_2_psi_ext {ψ : ℂ → ℂ} (hψ : ψ ∈ AInf1fun unitDiscExterior)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) :
    ∃ φ : AInf unitDiscExterior, ∀ z ∈ unitDiscExterior, AInf.toFun φ z = PsiOp ψ z := by
  obtain ⟨hd, C0, hC0⟩ := hψ
  obtain ⟨C, R, hdec⟩ := hdec
  have hC0nn : 0 ≤ C0 := by
    have := hC0 (2 : ℂ) (by show 1 < ‖(2 : ℂ)‖; norm_num)
    exact le_trans (norm_nonneg _) this
  have hPd := s2c_PsiOp_differentiableOn (isOpen_lt continuous_const continuous_norm :
    IsOpen {x : ℂ | 1 < ‖x‖}) hd
  set R1 : ℝ := max R 1 with hR1
  set C1 : ℝ := max C 0 with hC1
  have hR1' : 1 ≤ R1 := le_max_right _ _
  have hC1' : 0 ≤ C1 := le_max_right _ _
  have hdec' : ∀ u : ℂ, R1 < ‖u‖ → ‖ψ u‖ ≤ C1 / ‖u‖ ^ 3 := by
    intro u hu
    have h1 : R < ‖u‖ := lt_of_le_of_lt (le_max_left _ _) hu
    have h0 : 0 < ‖u‖ := by linarith
    exact (hdec u h1).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  set K : ℝ := max (4 * C0 * (2 * R1 + 1) ^ 2) (16 * C1) with hK
  have hbound : ∀ z ∈ unitDiscExterior,
      ‖(1 - (‖z‖ : ℂ) ^ 2) ^ 2 * PsiOp ψ z‖ ≤ K + C0 ^ 2 / 2 := by
    intro z hz
    have ht : 1 < ‖z‖ := hz
    have hw := hC0 z hz
    rw [s2c_wnorm, abs_of_nonpos (by nlinarith)] at hw
    have hder : (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ ≤ K := by
      by_cases hfar : 2 * R1 < ‖z‖
      · exact (s2c_psi_deriv_ext_far hd hC1' hR1' hdec' hfar).trans (le_trans (by linarith) (le_max_right _ _))
      · have hfar := not_lt.1 hfar
        have := s2c_psi_deriv_ext_near hd hC0 hz
        refine this.trans (le_trans ?_ (le_max_left _ _))
        have h2 : (‖z‖ + 1) ^ 2 ≤ (2 * R1 + 1) ^ 2 := by
          apply pow_le_pow_left₀ (by linarith) (by linarith)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [s2c_wnorm2]
    have hP : ‖PsiOp ψ z‖ ≤ ‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2 := by
      unfold PsiOp
      calc ‖deriv ψ z - 1 / 2 * ψ z ^ 2‖ ≤ ‖deriv ψ z‖ + ‖1 / 2 * ψ z ^ 2‖ := norm_sub_le _ _
        _ = ‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2 := by
          rw [norm_mul, norm_pow]; norm_num; ring
    have hsq : ((‖z‖ ^ 2 - 1) * ‖ψ z‖) ^ 2 ≤ C0 ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg (by nlinarith) (norm_nonneg _))
      nlinarith
    have h0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 2 := sq_nonneg _
    have e : (1 - ‖z‖ ^ 2) ^ 2 = (‖z‖ ^ 2 - 1) ^ 2 := by ring
    rw [e]
    calc (‖z‖ ^ 2 - 1) ^ 2 * ‖PsiOp ψ z‖
        ≤ (‖z‖ ^ 2 - 1) ^ 2 * (‖deriv ψ z‖ + ‖ψ z‖ ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hP (sq_nonneg _)
      _ = (‖z‖ ^ 2 - 1) ^ 2 * ‖deriv ψ z‖ + ((‖z‖ ^ 2 - 1) * ‖ψ z‖) ^ 2 / 2 := by ring
      _ ≤ K + C0 ^ 2 / 2 := by linarith
  have hKnn : 0 ≤ K + C0 ^ 2 / 2 := by
    have : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
    positivity
  obtain ⟨f, hf, -⟩ := TakhtajanTeo.exists_AInf_representative_of_bound (D := unitDiscExterior)
    (fun z hz => ne_of_gt hz) hPd hKnn hbound
  exact ⟨f, hf⟩

/-- A function tending to `∞` at `∞` is eventually large. -/
theorem s2c_inf_large {g : ℂ → ℂ} (htend : Tendsto g (cocompact ℂ) (cocompact ℂ)) (M : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → M ≤ ‖g z‖ := by
  have h1 : Tendsto (fun z => ‖g z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop.comp htend
  have h2 : ∀ᶠ z in cocompact ℂ, M ≤ ‖g z‖ := h1.eventually (eventually_ge_atTop M)
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 h2
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  exact ⟨R, fun z hz => hKs (fun hzK => absurd (hR z hzK) (not_le.2 hz))⟩

/-- The inverted function `φ(s) = 1 / g(1/s)` extends holomorphically and injectively across `0`. -/
theorem s2c_phi_exists {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDiscExterior)
    (hi : InjOn g unitDiscExterior) (htend : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball 0 ρ) ∧ φ 0 = 0 ∧
      (∀ s ∈ ball (0 : ℂ) ρ, s ≠ 0 → s⁻¹ ∈ unitDiscExterior ∧ g s⁻¹ ≠ 0 ∧ φ s = (g s⁻¹)⁻¹) ∧
      InjOn φ (ball 0 ρ) := by
  obtain ⟨R0, hR0⟩ := s2c_inf_large htend 1
  set R : ℝ := max R0 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR : ∀ z : ℂ, R < ‖z‖ → 1 ≤ ‖g z‖ := fun z hz => hR0 z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hR0' : 0 < R := by linarith
  set ρ : ℝ := 1 / R with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hR0']; exact hR1
  have hbig : ∀ s ∈ ball (0 : ℂ) ρ, s ≠ 0 → R < ‖s⁻¹‖ := by
    intro s hs hs0
    have h1 : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
    have h2 : 0 < ‖s‖ := norm_pos_iff.2 hs0
    rw [norm_inv, hρ] at *
    rw [lt_inv_comm₀ hR0' h2]
    simpa [one_div] using h1
  have hmemE : ∀ s ∈ ball (0 : ℂ) ρ, s ≠ 0 → s⁻¹ ∈ unitDiscExterior := by
    intro s hs hs0
    show 1 < ‖s⁻¹‖
    exact lt_of_le_of_lt hR1 (hbig s hs hs0)
  have hgne : ∀ s ∈ ball (0 : ℂ) ρ, s ≠ 0 → g s⁻¹ ≠ 0 := by
    intro s hs hs0 h0
    have := hR _ (hbig s hs hs0)
    rw [h0, norm_zero] at this
    exact absurd this (by norm_num)
  have hd0 : DifferentiableOn ℂ (fun s : ℂ => (g s⁻¹)⁻¹) (ball (0 : ℂ) ρ \ {0}) := by
    have hc : DifferentiableOn ℂ (fun s : ℂ => g s⁻¹) (ball (0 : ℂ) ρ \ {0}) :=
      hg.comp (differentiableOn_inv.mono (fun s hs => hs.2)) (fun s hs => hmemE s hs.1 hs.2)
    exact hc.inv (fun s hs => hgne s hs.1 hs.2)
  have hbdd : BddAbove (norm ∘ (fun s : ℂ => (g s⁻¹)⁻¹) '' (ball (0 : ℂ) ρ \ {0})) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have h1 := hR _ (hbig s hs.1 hs.2)
    simp only [Function.comp_apply, norm_inv]
    exact inv_le_one_of_one_le₀ h1
  have hlim : Tendsto (fun s : ℂ => (g s⁻¹)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨RM, hRM⟩ := s2c_inf_large htend (2 / ε)
    set T : ℝ := max (max RM R) 1 with hT
    have hT1 : 1 ≤ T := le_max_right _ _
    refine ⟨1 / (T + 1), by positivity, fun s hs0 hsd => ?_⟩
    have hs0' : s ≠ 0 := hs0
    have hsn : ‖s‖ < 1 / (T + 1) := by simpa using hsd
    have hsp : 0 < ‖s‖ := norm_pos_iff.2 hs0'
    have hinv : T + 1 < ‖s⁻¹‖ := by
      rw [norm_inv, lt_inv_comm₀ (by linarith) hsp]
      simpa [one_div] using hsn
    have hge : 2 / ε ≤ ‖g s⁻¹‖ := hRM _ (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) (by linarith))
    have hpos : 0 < ‖g s⁻¹‖ := lt_of_lt_of_le (by positivity) hge
    rw [dist_zero_right, norm_inv]
    calc (‖g s⁻¹‖)⁻¹ ≤ (2 / ε)⁻¹ := inv_anti₀ (by positivity) hge
      _ = ε / 2 := by rw [inv_div]
      _ < ε := by linarith
  let φ : ℂ → ℂ := Function.update (fun s : ℂ => (g s⁻¹)⁻¹) 0
    (limUnder (𝓝[≠] (0 : ℂ)) (fun s : ℂ => (g s⁻¹)⁻¹))
  have hφd : DifferentiableOn ℂ φ (ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (isOpen_ball.mem_nhds (mem_ball_self hρ0)) hd0 hbdd
  have hφ0 : φ 0 = 0 := by
    simp only [φ, Function.update_self]
    exact hlim.limUnder_eq
  have hφs : ∀ s ∈ ball (0 : ℂ) ρ, s ≠ 0 → φ s = (g s⁻¹)⁻¹ := by
    intro s _ hs0
    simp [φ, Function.update_of_ne hs0]
  refine ⟨ρ, hρ0, hρ1, φ, hφd, hφ0, fun s hs hs0 => ⟨hmemE s hs hs0, hgne s hs hs0, hφs s hs hs0⟩, ?_⟩
  intro s hs t ht he
  by_cases hs0 : s = 0
  · by_cases ht0 : t = 0
    · rw [hs0, ht0]
    · exfalso
      rw [hs0, hφ0, hφs t ht ht0] at he
      exact inv_ne_zero (hgne t ht ht0) he.symm
  · by_cases ht0 : t = 0
    · exfalso
      rw [ht0, hφ0, hφs s hs hs0] at he
      exact inv_ne_zero (hgne s hs hs0) he
    · rw [hφs s hs hs0, hφs t ht ht0, inv_inj] at he
      exact inv_injective (hi (hmemE s hs hs0) (hmemE t ht ht0) he)

/-- Near-field bound for `g''/g'` on the exterior, by Bieberbach's bound on a disc around `u`. -/
theorem s2c_pre_ext_near {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDiscExterior)
    (hi : InjOn g unitDiscExterior) {u : ℂ} (hu : u ∈ unitDiscExterior) :
    (‖u‖ ^ 2 - 1) * ‖preSchwarzian g u‖ ≤ 4 * (‖u‖ + 1) := by
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hu1 : 1 < ‖u‖ := hu
  set r : ℝ := ‖u‖ - 1 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hgu : deriv g u ≠ 0 := deriv_ne_zero_of_injOn hU hg hi hu
  have hmem : ∀ w ∈ ball (0 : ℂ) 1, u + (r : ℂ) * w ∈ unitDiscExterior := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    show 1 < ‖u + (r : ℂ) * w‖
    have h1 : ‖u‖ - ‖(r : ℂ) * w‖ ≤ ‖u + (r : ℂ) * w‖ := by
      have := norm_sub_norm_le u (-((r : ℂ) * w))
      simpa [sub_neg_eq_add] using this
    have h2 : ‖(r : ℂ) * w‖ = r * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    nlinarith
  have hrne : (r : ℂ) * deriv g u ≠ 0 := mul_ne_zero hr' hgu
  let F : ℂ → ℂ := fun w => (g (u + (r : ℂ) * w) - g u) / ((r : ℂ) * deriv g u)
  have hin : ∀ w : ℂ, HasDerivAt (fun w : ℂ => u + (r : ℂ) * w) (r : ℂ) w := by
    intro w
    simpa using ((hasDerivAt_id w).const_mul (r : ℂ)).const_add u
  have hFderiv : ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt F (deriv g (u + (r : ℂ) * w) / deriv g u) w := by
    intro w hw
    have hm := hmem w hw
    have hgd : HasDerivAt g (deriv g (u + (r : ℂ) * w)) (u + (r : ℂ) * w) :=
      (hg.differentiableAt (hU.mem_nhds hm)).hasDerivAt
    have hc : HasDerivAt F (deriv g (u + (r : ℂ) * w) * (r : ℂ) / ((r : ℂ) * deriv g u)) w :=
      ((hgd.comp w (hin w)).sub_const (g u)).div_const ((r : ℂ) * deriv g u)
    have e : deriv g (u + (r : ℂ) * w) * (r : ℂ) / ((r : ℂ) * deriv g u) =
        deriv g (u + (r : ℂ) * w) / deriv g u := by field_simp
    rwa [e] at hc
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    fun w hw => (hFderiv w hw).differentiableAt.differentiableWithinAt
  have hFi : InjOn F (ball 0 1) := by
    intro w1 hw1 w2 hw2 he
    have h1 := (div_left_inj' hrne).1 he
    have h2 : g (u + (r : ℂ) * w1) = g (u + (r : ℂ) * w2) := sub_left_injective h1
    have h3 := hi (hmem w1 hw1) (hmem w2 hw2) h2
    exact mul_left_cancel₀ hr' (add_left_cancel h3)
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hF0 : F 0 = 0 := by simp [F]
  have hF1 : deriv F 0 = 1 := by
    rw [(hFderiv 0 h0ball).deriv]
    simp [div_self hgu]
  have hB := koebe_bieberbach hFd hFi hF0 hF1
  have hgg : HasDerivAt (deriv g) (deriv (deriv g) u) u :=
    ((hg.analyticOnNhd hU u hu).deriv.differentiableAt).hasDerivAt
  have hFF : deriv (deriv F) 0 = (r : ℂ) * deriv (deriv g) u / deriv g u := by
    have hev : deriv F =ᶠ[𝓝 0] fun w => deriv g (u + (r : ℂ) * w) / deriv g u := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with w hw using (hFderiv w hw).deriv
    rw [hev.deriv_eq]
    have hc : HasDerivAt (fun w : ℂ => deriv g (u + (r : ℂ) * w) / deriv g u)
        (deriv (deriv g) u * (r : ℂ) / deriv g u) 0 :=
      (HasDerivAt.comp_of_eq (x := (0 : ℂ)) hgg (hin 0) (by simp)).div_const (deriv g u)
    rw [hc.deriv]
    ring
  rw [hFF] at hB
  have hmul : ‖(r : ℂ) * preSchwarzian g u‖ ≤ 4 := by
    have : (r : ℂ) * preSchwarzian g u = (r : ℂ) * deriv (deriv g) u / deriv g u := by
      unfold preSchwarzian; ring
    rw [this]; exact hB
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hmul
  calc (‖u‖ ^ 2 - 1) * ‖preSchwarzian g u‖ = (‖u‖ + 1) * (r * ‖preSchwarzian g u‖) := by rw [hr]; ring
    _ ≤ (‖u‖ + 1) * 4 := mul_le_mul_of_nonneg_left hmul (by linarith)
    _ = 4 * (‖u‖ + 1) := by ring

/-- Exact formula for `g''/g'` at `1/s` in terms of the inverted function `φ`, `q = φ(s)/s`. -/
theorem s2c_pre_ext_formula {g φ : ℂ → ℂ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hφd : DifferentiableOn ℂ φ (ball 0 ρ))
    (hφne : ∀ t ∈ ball (0 : ℂ) ρ, deriv φ t ≠ 0)
    (hφq : ∀ t ∈ ball (0 : ℂ) ρ, φ t = t * dslope φ 0 t)
    (hq0 : ∀ t ∈ ball (0 : ℂ) ρ, dslope φ 0 t ≠ 0)
    (hrel : ∀ t ∈ ball (0 : ℂ) ρ, t ≠ 0 → g t⁻¹ ≠ 0 ∧ φ t = (g t⁻¹)⁻¹)
    {s : ℂ} (hs : s ∈ ball (0 : ℂ) ρ) (hs0 : s ≠ 0) :
    preSchwarzian g s⁻¹ = -(s ^ 2) *
      (deriv (deriv φ) s / deriv φ s - 2 * (deriv (dslope φ 0) s / dslope φ 0 s)) := by
  have hsn : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.2 hs0
  let W : Set ℂ := {w : ℂ | 1 / ρ < ‖w‖}
  have hWo : IsOpen W := isOpen_lt continuous_const continuous_norm
  have hzW : s⁻¹ ∈ W := by
    show 1 / ρ < ‖s⁻¹‖
    rw [norm_inv, one_div, inv_lt_inv₀ hρ0 hspos]
    exact hsn
  have hWmem : ∀ w ∈ W, w⁻¹ ∈ ball (0 : ℂ) ρ ∧ w⁻¹ ≠ 0 ∧ w ≠ 0 := by
    intro w hw
    have hw' : 1 / ρ < ‖w‖ := hw
    have hwp : 0 < ‖w‖ := lt_trans (by positivity) hw'
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwp
    refine ⟨mem_ball_zero_iff.2 ?_, inv_ne_zero hw0, hw0⟩
    rw [norm_inv, inv_lt_comm₀ hwp hρ0]
    simpa [one_div] using hw'
  have hG : ∀ w ∈ W, g w = (φ w⁻¹)⁻¹ := by
    intro w hw
    obtain ⟨hm, hn, _⟩ := hWmem w hw
    have := (hrel w⁻¹ hm hn).2
    rw [inv_inv] at this
    rw [this, inv_inv]
  have hφne0 : ∀ w ∈ W, φ w⁻¹ ≠ 0 := by
    intro w hw
    obtain ⟨hm, hn, _⟩ := hWmem w hw
    have h1 := hrel w⁻¹ hm hn
    rw [inv_inv] at h1
    rw [h1.2]
    exact inv_ne_zero h1.1
  have hφdiffAt : ∀ t ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ φ t :=
    fun t ht => hφd.differentiableAt (isOpen_ball.mem_nhds ht)
  have hφ'diffAt : ∀ t ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ (deriv φ) t :=
    fun t ht => ((hφd.analyticOnNhd isOpen_ball t ht).deriv).differentiableAt
  have hc : ∀ w ∈ W, HasDerivAt (fun w => φ w⁻¹) (deriv φ w⁻¹ * (-(w ^ 2)⁻¹)) w := by
    intro w hw
    obtain ⟨hm, hn, hw0⟩ := hWmem w hw
    exact (hφdiffAt _ hm).hasDerivAt.comp w (hasDerivAt_inv hw0)
  have hder : ∀ w ∈ W, deriv g w = deriv φ w⁻¹ * (w ^ 2)⁻¹ / φ w⁻¹ ^ 2 := by
    intro w hw
    have hev : g =ᶠ[𝓝 w] fun w => (φ w⁻¹)⁻¹ := by
      filter_upwards [hWo.mem_nhds hw] with x hx using hG x hx
    have hi : HasDerivAt (fun w => (φ w⁻¹)⁻¹) (-(deriv φ w⁻¹ * -(w ^ 2)⁻¹) / φ w⁻¹ ^ 2) w :=
      (hc w hw).inv (hφne0 w hw)
    rw [hev.deriv_eq, hi.deriv]
    ring
  have hz0 : s⁻¹ ≠ 0 := inv_ne_zero hs0
  have hEev : deriv g =ᶠ[𝓝 s⁻¹] fun w => deriv φ w⁻¹ * (w ^ 2)⁻¹ / φ w⁻¹ ^ 2 := by
    filter_upwards [hWo.mem_nhds hzW] with x hx using hder x hx
  have hP : HasDerivAt (fun w : ℂ => deriv φ w⁻¹) (deriv (deriv φ) s * (-(s⁻¹ ^ 2)⁻¹)) s⁻¹ :=
    HasDerivAt.comp_of_eq (x := s⁻¹) (hφ'diffAt s hs).hasDerivAt (hasDerivAt_inv hz0) (inv_inv s).symm
  have hQ : HasDerivAt (fun w : ℂ => (w ^ 2)⁻¹) (-(2 * s⁻¹) / (s⁻¹ ^ 2) ^ 2) s⁻¹ := by
    have := (hasDerivAt_pow 2 s⁻¹).inv (pow_ne_zero 2 hz0)
    convert this using 1
    norm_num
  have hSd : HasDerivAt (fun w : ℂ => φ w⁻¹) (deriv φ s * (-(s⁻¹ ^ 2)⁻¹)) s⁻¹ :=
    HasDerivAt.comp_of_eq (x := s⁻¹) (hφdiffAt s hs).hasDerivAt (hasDerivAt_inv hz0) (inv_inv s).symm
  have hS : HasDerivAt (fun w : ℂ => φ w⁻¹ ^ 2) (2 * φ s * (deriv φ s * (-(s⁻¹ ^ 2)⁻¹))) s⁻¹ := by
    have := hSd.pow 2
    simp only [inv_inv] at this ⊢
    convert this using 1
    simp
  have hφs : φ s ≠ 0 := by
    have := hφne0 s⁻¹ hzW
    rwa [inv_inv] at this
  have hSne : φ s⁻¹⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (by rw [inv_inv]; exact hφs)
  have hE0 := (hP.mul hQ).div hS (by simpa only [inv_inv] using hSne)
  have hE : HasDerivAt (fun w : ℂ => deriv φ w⁻¹ * (w ^ 2)⁻¹ / φ w⁻¹ ^ 2) _ s⁻¹ := hE0
  have hqd : DifferentiableOn ℂ (dslope φ 0) (ball 0 ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hρ0))).2 hφd
  have hqdiff : DifferentiableAt ℂ (dslope φ 0) s := hqd.differentiableAt (isOpen_ball.mem_nhds hs)
  have hb' : deriv φ s = dslope φ 0 s + s * deriv (dslope φ 0) s := by
    have hev : φ =ᶠ[𝓝 s] fun t => t * dslope φ 0 t := by
      filter_upwards [isOpen_ball.mem_nhds hs] with t ht using hφq t ht
    rw [hev.deriv_eq]
    have hmul : HasDerivAt (fun t => t * dslope φ 0 t)
        (1 * dslope φ 0 s + s * deriv (dslope φ 0) s) s := (hasDerivAt_id' s).mul hqdiff.hasDerivAt
    rw [hmul.deriv]
    ring
  have hq0s := hq0 s hs
  have hbne : dslope φ 0 s + s * deriv (dslope φ 0) s ≠ 0 := by
    rw [← hb']; exact hφne s hs
  have ha : φ s = s * dslope φ 0 s := hφq s hs
  have hmain : preSchwarzian g s⁻¹ = deriv (deriv g) s⁻¹ / deriv g s⁻¹ := rfl
  rw [hmain, hEev.deriv_eq, hE.deriv, hder s⁻¹ hzW]
  simp only [inv_inv, Pi.mul_apply]
  rw [ha, hb'] at *
  generalize deriv (deriv φ) s = c
  generalize deriv (dslope φ 0) s = q1 at *
  generalize dslope φ 0 s = q at *
  field_simp
  ring

/-- Far-field decay `g''/g' = O(z⁻²)` for a function univalent at `∞`. -/
theorem s2c_pre_ext_far {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDiscExterior)
    (hi : InjOn g unitDiscExterior) (htend : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ M R2 : ℝ, 0 ≤ M ∧ 1 ≤ R2 ∧ ∀ z : ℂ, R2 < ‖z‖ → ‖preSchwarzian g z‖ ≤ M / ‖z‖ ^ 2 := by
  obtain ⟨ρ, hρ0, hρ1, φ, hφd, hφ0, hrel, hφi⟩ := s2c_phi_exists hg hi htend
  have hU : IsOpen (ball (0 : ℂ) ρ) := isOpen_ball
  have hφne : ∀ t ∈ ball (0 : ℂ) ρ, deriv φ t ≠ 0 := fun t ht => deriv_ne_zero_of_injOn hU hφd hφi ht
  have hrel' : ∀ t ∈ ball (0 : ℂ) ρ, t ≠ 0 → g t⁻¹ ≠ 0 ∧ φ t = (g t⁻¹)⁻¹ :=
    fun t ht ht0 => ⟨(hrel t ht ht0).2.1, (hrel t ht ht0).2.2⟩
  have hqt : ∀ t : ℂ, t ≠ 0 → dslope φ 0 t = φ t / t := by
    intro t ht
    rw [dslope_of_ne φ ht, slope_def_field, hφ0]
    simp
  have hφt0 : ∀ t ∈ ball (0 : ℂ) ρ, t ≠ 0 → φ t ≠ 0 := by
    intro t ht ht0
    rw [(hrel t ht ht0).2.2]
    exact inv_ne_zero (hrel t ht ht0).2.1
  have hq0 : ∀ t ∈ ball (0 : ℂ) ρ, dslope φ 0 t ≠ 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, dslope_same]
      exact hφne 0 (mem_ball_self hρ0)
    · rw [hqt t ht0]
      exact div_ne_zero (hφt0 t ht ht0) ht0
  have hφq : ∀ t ∈ ball (0 : ℂ) ρ, φ t = t * dslope φ 0 t := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, hφ0]; simp
    · rw [hqt t ht0]; field_simp
  have hqd : DifferentiableOn ℂ (dslope φ 0) (ball 0 ρ) :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (mem_ball_self hρ0))).2 hφd
  have hBd : DifferentiableOn ℂ (fun s => deriv (deriv φ) s / deriv φ s -
      2 * (deriv (dslope φ 0) s / dslope φ 0 s)) (ball 0 ρ) := by
    intro t ht
    have h1 : AnalyticAt ℂ (deriv (deriv φ)) t := (hφd.analyticOnNhd hU t ht).deriv.deriv
    have h2 : AnalyticAt ℂ (deriv φ) t := (hφd.analyticOnNhd hU t ht).deriv
    have h3 : AnalyticAt ℂ (deriv (dslope φ 0)) t := (hqd.analyticOnNhd hU t ht).deriv
    have h4 : AnalyticAt ℂ (dslope φ 0) t := hqd.analyticOnNhd hU t ht
    exact ((h1.div h2 (hφne t ht)).sub (analyticAt_const.mul (h3.div h4 (hq0 t ht)))).differentiableAt.differentiableWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
    (hBd.continuousOn.mono (closedBall_subset_ball (by linarith)))
  refine ⟨max M 0, max (2 / ρ) 1, le_max_right _ _, le_max_right _ _, fun z hz => ?_⟩
  have hz2 : 2 / ρ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz2.le
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hsn : ‖z⁻¹‖ ≤ ρ / 2 := by
    rw [norm_inv]
    rw [inv_le_comm₀ hzpos (by positivity), inv_div]
    exact hz2.le
  have hs : z⁻¹ ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.2 (lt_of_le_of_lt hsn (by linarith))
  have hform := s2c_pre_ext_formula hρ0 hφd hφne hφq hq0 hrel' hs (inv_ne_zero hz0)
  rw [inv_inv] at hform
  rw [hform, norm_mul, norm_neg, norm_pow]
  have hB := hM z⁻¹ (mem_closedBall_zero_iff.2 hsn)
  calc ‖z⁻¹‖ ^ 2 * ‖deriv (deriv φ) z⁻¹ / deriv φ z⁻¹ - 2 * (deriv (dslope φ 0) z⁻¹ / dslope φ 0 z⁻¹)‖
      ≤ ‖z⁻¹‖ ^ 2 * max M 0 := mul_le_mul_of_nonneg_left (hB.trans (le_max_left _ _)) (sq_nonneg _)
    _ = max M 0 / ‖z‖ ^ 2 := by rw [norm_inv]; field_simp

/-- Clause 2 of `remark_1_2`. -/
theorem s2c_remark_1_2_univalent_ext {g : ℂ → ℂ} (h : IsUnivalentAtInfty g) :
    preSchwarzian g ∈ AInf1fun unitDiscExterior := by
  obtain ⟨hg, hi, htend⟩ := h
  have hU : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hA : AnalyticOnNhd ℂ g unitDiscExterior := hg.analyticOnNhd hU
  have hne : ∀ z ∈ unitDiscExterior, deriv g z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hU hg hi hz
  obtain ⟨M, R2, hM0, hR2, hfar⟩ := s2c_pre_ext_far hg hi htend
  refine ⟨?_, max (4 * (R2 + 1)) M, ?_⟩
  · intro z hz
    have h1 : AnalyticAt ℂ (deriv (deriv g)) z := (hA z hz).deriv.deriv
    have h2 : AnalyticAt ℂ (deriv g) z := (hA z hz).deriv
    exact (h1.div h2 (hne z hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have ht : 1 < ‖z‖ := hz
    rw [s2c_wnorm, abs_of_nonpos (by nlinarith)]
    by_cases hfar' : R2 < ‖z‖
    · have := hfar z hfar'
      have hzp : 0 < ‖z‖ ^ 2 := by positivity
      calc -(1 - ‖z‖ ^ 2) * ‖preSchwarzian g z‖ ≤ ‖z‖ ^ 2 * (M / ‖z‖ ^ 2) := by
            apply mul_le_mul (by linarith) this (norm_nonneg _) hzp.le
        _ = M := by field_simp
        _ ≤ _ := le_max_right _ _
    · have hfar' := not_lt.1 hfar'
      have := s2c_pre_ext_near hg hi hz
      calc -(1 - ‖z‖ ^ 2) * ‖preSchwarzian g z‖ = (‖z‖ ^ 2 - 1) * ‖preSchwarzian g z‖ := by ring
        _ ≤ 4 * (‖z‖ + 1) := this
        _ ≤ 4 * (R2 + 1) := by linarith
        _ ≤ _ := le_max_left _ _

/-- **Remark 1.2** (TT:3520–3542).
- (Distortion theorem) For univalent `f` on `𝔻` and `g` on `𝔻*` with `g(∞) = ∞`, `𝒜(f) ∈ A∞¹(𝔻)` and
  `𝒜(g) ∈ A∞¹(𝔻*)`.
- ([Teo04]) `Ψ(A∞¹(𝔻)) ⊂ A∞(𝔻)`, and `Ψ` maps the `ψ ∈ A∞¹(𝔻*)` with `ψ(z) = O(z⁻³)` at `∞` into `A∞(𝔻*)`.

[CORRECTION 2026-10-25]
- The exterior distortion clause needs `g(∞) = ∞`: for `g(z) = 1/z`, `𝒜(g) = -2/z ∉ A∞¹(𝔻*)`.
- The exterior `Ψ` clause needs the decay `O(z⁻³)` of the normalized pre-Schwarzians `𝒜(g)`,
  `g(z) = bz + b₀ + O(1/z)` (cf. `Ã₂¹(𝔻*)`, TT:5942). For `ψ = z⁻²`, `Ψ(ψ) ∉ A∞(𝔻*)` (lean4,
  `collaboration/lean4/PsiExteriorDiagnostic.lean`). The memoir (TT:3588, arXiv math/0406408 Lemma 2.5) states the
  unrestricted version. 
Proved here as `s2c_remark_1_2`; statement identical to `remark_1_2`. -/
theorem s2c_remark_1_2 :
    (∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc → preSchwarzian f ∈ AInf1fun unitDisc) ∧
      (∀ g : ℂ → ℂ, IsUnivalentAtInfty g → preSchwarzian g ∈ AInf1fun unitDiscExterior) ∧
      (∀ ψ ∈ AInf1fun unitDisc, ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = PsiOp ψ z) ∧
      ∀ ψ ∈ AInf1fun unitDiscExterior, (∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) →
        ∃ φ : AInf unitDiscExterior, ∀ z ∈ unitDiscExterior, AInf.toFun φ z = PsiOp ψ z := by
  exact ⟨fun f hf hi => s2c_remark_1_2_univalent_disc hf hi,
    fun g hg => s2c_remark_1_2_univalent_ext hg,
    fun ψ hψ => s2c_remark_1_2_psi_disc hψ,
    fun ψ hψ hdec => s2c_remark_1_2_psi_ext hψ hdec⟩

/-! ### Original relocated (2026-10-26) -/

/-- **Remark 1.2** (TT:3520–3542).
- (Distortion theorem) For univalent `f` on `𝔻` and `g` on `𝔻*` with `g(∞) = ∞`, `𝒜(f) ∈ A∞¹(𝔻)` and
  `𝒜(g) ∈ A∞¹(𝔻*)`.
- ([Teo04]) `Ψ(A∞¹(𝔻)) ⊂ A∞(𝔻)`, and `Ψ` maps the `ψ ∈ A∞¹(𝔻*)` with `ψ(z) = O(z⁻³)` at `∞` into `A∞(𝔻*)`.

[CORRECTION 2026-10-25]
- The exterior distortion clause needs `g(∞) = ∞`: for `g(z) = 1/z`, `𝒜(g) = -2/z ∉ A∞¹(𝔻*)`.
- The exterior `Ψ` clause needs the decay `O(z⁻³)` of the normalized pre-Schwarzians `𝒜(g)`,
  `g(z) = bz + b₀ + O(1/z)` (cf. `Ã₂¹(𝔻*)`, TT:5942). For `ψ = z⁻²`, `Ψ(ψ) ∉ A∞(𝔻*)` (lean4,
  `collaboration/lean4/PsiExteriorDiagnostic.lean`). The memoir (TT:3588, arXiv math/0406408 Lemma 2.5) states the
  unrestricted version. -/
theorem remark_1_2 :
    (∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc → preSchwarzian f ∈ AInf1fun unitDisc) ∧
      (∀ g : ℂ → ℂ, IsUnivalentAtInfty g → preSchwarzian g ∈ AInf1fun unitDiscExterior) ∧
      (∀ ψ ∈ AInf1fun unitDisc, ∃ φ : AInf unitDisc, ∀ z ∈ unitDisc, AInf.toFun φ z = PsiOp ψ z) ∧
      ∀ ψ ∈ AInf1fun unitDiscExterior, (∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖ψ z‖ ≤ C / ‖z‖ ^ 3) →
        ∃ φ : AInf unitDiscExterior, ∀ z ∈ unitDiscExterior, AInf.toFun φ z = PsiOp ψ z :=
  s2c_remark_1_2

end TakhtajanTeo.Ch2
