import TakhtajanTeo.Ch1.L613

/-!
# Lemma 1.12 (下属5, 2026-10-28)

Host: new module `TakhtajanTeo/Ch1/L112.lean`, prefix `l112_`, importing `TakhtajanTeo.Ch1.L613`. The target
`l112_lemma_1_12` is `lemma_1_12` (S1_5) with the prefixed name and a byte-identical statement (relocated at round
end).

**Route** (no derivatives of singular integrals, no Stokes on unbounded sets). Fix `z ∈ 𝕌` and `r > 0` with
`closedBall z r ⊆ 𝕌`, and `k ≥ 4`.
* (A) **Circle mean of `F`.** By `lemma_1_13`, on the circle `|ζ - z| = r` the function
  `(ζ - z)^{k-1} · conj F(ζ)` equals `N(ζ)`, a holomorphic function on a neighbourhood of the closed disc
  (use `conj(ζ - z) = r²/(ζ - z)`) with `N(z) = 0` (it carries the factor `(ζ - z)^{k-3}`). Cauchy's formula gives
  `∮ F(ζ)/(ζ - z)^k dζ = 0`.
* (B) **Kernel on the circle.** For `u ∉ {0, 1}` off the circle,
  `∮ R(ζ, u)/(ζ - z)^k dζ = 2πi/(u - z)^k` if `|u - z| > r`, and `0` if `|u - z| < r`. This uses the partial
  fractions of `1/((u - ζ)(ζ - z)^k)`; the affine part of `R` integrates to `0`.
* (C) **Fubini.** Insert `F(ζ) = -(1/π) ∫_𝕌 R(ζ, u) μ(u)` (`eq_1_22_of_bounded`) and swap. Integrability on
  `[0, 2π] × 𝕌` follows from Tonelli with a bound on `∫_𝕌 |R(ζ, u)|` uniform in `ζ` on the circle: near `u = ζ` it
  is `1/|u - ζ|`, elsewhere the majorant is `phiKernel_majorant_integrable`.
* (D) `0 = (A) = (C) = -2i ∫_{𝕌 \ B(z, r)} μ/(u - z)^k`; the circle is null. Hence the truncated integral is
  **exactly `0`** for every `r < Im z`, and the limits in `lemma_1_12` are trivial.

`wp_harmonicPVKernel_cutoff_zero` (the `eq_6_3` route) does not transfer: after the Cayley map the excised
Euclidean disc is a non-centred disc, and against `v⁻⁴` the mismatch crescent contributes `O(1/s)`, not `o(1)`.

No new definitions, no `set_option`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- Cauchy's theorem on a circle, from Cauchy's formula applied to `(ζ - z) g(ζ)`. -/
theorem l112_cauchy_zero {g : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall z r)) :
    (∮ ζ in C(z, r), g ζ) = 0 := by
  have h := (show DifferentiableOn ℂ (fun ζ => (ζ - z) * g ζ) (closedBall z r) from
    (differentiableOn_id.sub_const z).mul hg).circleIntegral_sub_inv_smul (mem_ball_self hr)
  simp only [sub_self, zero_mul, smul_zero] at h
  rw [← h]
  refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
  have hne : ζ - z ≠ 0 := by
    intro h0
    rw [mem_sphere, dist_eq_norm, h0, norm_zero] at hζ
    linarith
  show g ζ = (ζ - z)⁻¹ • ((ζ - z) * g ζ)
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- On the circle `|ζ - z| = r`, `conj (ζ - z) = r²/(ζ - z)`. -/
theorem l112_conj_sphere {z ζ : ℂ} {r : ℝ} (hr : 0 < r) (hζ : ζ ∈ sphere z r) :
    ζ - z ≠ 0 ∧ conj (ζ - z) = (r : ℂ) ^ 2 / (ζ - z) := by
  rw [mem_sphere, dist_eq_norm] at hζ
  have hne : ζ - z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hζ; linarith
  refine ⟨hne, ?_⟩
  rw [eq_div_iff hne, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
  push_cast
  ring

/-- Conjugating a circle integral: `conj ∮ f = -r² ∮ conj f/(ζ - z)²`. -/
theorem l112_conj_circle (f : ℂ → ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    conj (∮ ζ in C(z, r), f ζ) = -(r : ℂ) ^ 2 * ∮ ζ in C(z, r), conj (f ζ) / (ζ - z) ^ 2 := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  simp only [circleIntegral, intervalIntegral.integral_of_le h2π]
  rw [← integral_conj, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  obtain ⟨hne, hc⟩ := l112_conj_sphere hr (circleMap_mem_sphere z hr.le θ)
  simp only [deriv_circleMap, smul_eq_mul, map_mul, Complex.conj_I]
  rw [← circleMap_sub_center, hc]
  field_simp

/-- (A) The circle integral of `F[μ]/(ζ - z)^k` vanishes for harmonic `μ`, `k ≥ 4`, on a circle inside `𝕌`
(`lemma_1_13` plus Cauchy's formula). -/
theorem l112_circle_varF_zero {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ upperHalf) {k : ℕ} (hk : 4 ≤ k) :
    (∮ ζ in C(z, r), varF μ ζ / (ζ - z) ^ k) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  obtain ⟨C₀, hC₀, hCb⟩ := harmonicU_bounded hμ
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hμb : IsBeltramiCoeff μ upperHalf C₀ :=
    ⟨(harmonicU_continuousOn hμ).aestronglyMeasurable hU.measurableSet,
      (ae_restrict_mem hU.measurableSet).mono fun u hu => hCb u hu⟩
  have hΦ : DifferentiableOn ℂ (varPhi μ) upperHalf := (varPhi_holomorphic_of_bounded hC₀ hμb).1
  have hΦ1 : DifferentiableOn ℂ (deriv (varPhi μ)) upperHalf := hΦ.deriv hU
  have hΦ2 : DifferentiableOn ℂ (deriv (deriv (varPhi μ))) upperHalf := hΦ1.deriv hU
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = z - conj z := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ → ℂ, N = fun ζ => ((r : ℂ) ^ (2 * (m + 4)))⁻¹ *
      (((r : ℂ) ^ 2 - A * (ζ - z) - (ζ - z) ^ 2) ^ 2 / 2 * deriv (deriv (varPhi μ)) ζ * (ζ - z) ^ m +
        ((r : ℂ) ^ 2 - A * (ζ - z) - (ζ - z) ^ 2) * deriv (varPhi μ) ζ * (ζ - z) ^ (m + 1) +
        varPhi μ ζ * (ζ - z) ^ (m + 2)) := ⟨_, rfl⟩
  have hNd : DifferentiableOn ℂ N (closedBall z r) := by
    rw [hN]
    have hw : DifferentiableOn ℂ (fun ζ : ℂ => ζ - z) (closedBall z r) := differentiableOn_id.sub_const z
    have hq : DifferentiableOn ℂ (fun ζ : ℂ => (r : ℂ) ^ 2 - A * (ζ - z) - (ζ - z) ^ 2) (closedBall z r) :=
      ((differentiableOn_const _).sub (hw.const_mul A)).sub (hw.pow 2)
    exact (differentiableOn_const _).mul (((((hq.pow 2).div_const 2).mul (hΦ2.mono hB)).mul (hw.pow m)).add
      ((hq.mul (hΦ1.mono hB)).mul (hw.pow (m + 1))) |>.add ((hΦ.mono hB).mul (hw.pow (m + 2))))
  have hN0 := l112_cauchy_zero hr hNd
  have hc := l112_conj_circle (fun ζ => varF μ ζ / (ζ - z) ^ (m + 4)) z hr
  have heq : (∮ ζ in C(z, r), conj (varF μ ζ / (ζ - z) ^ (m + 4)) / (ζ - z) ^ 2) = ∮ ζ in C(z, r), N ζ := by
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    obtain ⟨hne, hcs⟩ := l112_conj_sphere hr hζ
    have hζU : ζ ∈ upperHalf := hB (sphere_subset_closedBall hζ)
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    show conj (varF μ ζ / (ζ - z) ^ (m + 4)) / (ζ - z) ^ 2 = N ζ
    rw [lemma_1_13 hμ hζU, hN]
    obtain ⟨w, rfl⟩ : ∃ w, ζ = z + w := ⟨ζ - z, by ring⟩
    simp only [add_sub_cancel_left] at hne hcs ⊢
    simp only [map_div₀, map_mul, map_add, map_pow, map_sub, Complex.conj_conj, map_ofNat, add_sub_cancel_left]
    rw [hcs, hA, div_pow, pow_mul]
    field_simp
    ring
  rw [heq, hN0, mul_zero, map_eq_zero] at hc
  exact hc

/-- `∮ (ζ - u)⁻¹` on a circle missing `u`. -/
theorem l112_inv_sub_circle {z u : ℂ} {r : ℝ} (hr : 0 < r) (hus : u ∉ sphere z r) :
    (∮ ζ in C(z, r), (ζ - u)⁻¹) = if r < ‖u - z‖ then 0 else 2 * π * I := by
  split_ifs with h
  · refine l112_cauchy_zero hr fun ζ hζ => ?_
    have hne : ζ - u ≠ 0 := by
      intro h0
      rw [mem_closedBall, dist_eq_norm] at hζ
      have he : u - z = ζ - z := by linear_combination -h0
      rw [he] at h
      linarith
    exact ((differentiableAt_id.sub_const u).inv hne).differentiableWithinAt
  · have hlt : ‖u - z‖ < r := by
      rcases (not_lt.mp h).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (by rw [mem_sphere, dist_eq_norm, h']) hus
    exact circleIntegral.integral_sub_inv_of_mem_ball (by rw [mem_ball, dist_eq_norm]; exact hlt)

/-- `∮ ((ζ - z)^n)⁻¹ = 2πi` if `n = 1` and `0` if `n ≥ 2`. -/
theorem l112_pow_circle (z : ℂ) {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) :
    (∮ ζ in C(z, r), ((ζ - z) ^ n)⁻¹) = if n = 1 then 2 * π * I else 0 := by
  split_ifs with h
  · subst h
    simp only [pow_one]
    exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)
  · have h' := circleIntegral.integral_sub_zpow_of_ne (n := -(n : ℤ)) (by omega) z z r
    simpa only [zpow_neg, zpow_natCast] using h'

/-- `∮ (u - ζ)⁻¹ (ζ - z)^{-k} = (u - z)^{-k} · 2πi [|u - z| > r]` for `k ≥ 1`. -/
theorem l112_cauchy_kernel_circle {z u : ℂ} {r : ℝ} (hr : 0 < r) (hus : u ∉ sphere z r) :
    ∀ k : ℕ, 1 ≤ k → (∮ ζ in C(z, r), (u - ζ)⁻¹ * ((ζ - z) ^ k)⁻¹) =
      ((u - z) ^ k)⁻¹ * if r < ‖u - z‖ then 2 * π * I else 0 := by
  have hsph : ∀ ζ ∈ sphere z r, u - ζ ≠ 0 ∧ ζ - z ≠ 0 := fun ζ hζ =>
    ⟨fun h0 => hus (by rw [show u = ζ by linear_combination h0]; exact hζ), (l112_conj_sphere hr hζ).1⟩
  have hint : ∀ k : ℕ, CircleIntegrable (fun ζ => (u - ζ)⁻¹ * ((ζ - z) ^ k)⁻¹) z r := fun k =>
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      (((continuousAt_const.sub continuousAt_id).inv₀ (hsph ζ hζ).1).mul
        (((continuousAt_id.sub continuousAt_const).pow k).inv₀ (pow_ne_zero _ (hsph ζ hζ).2))).continuousWithinAt
  have hintp : ∀ k : ℕ, CircleIntegrable (fun ζ => ((ζ - z) ^ k)⁻¹) z r := fun k =>
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      (((continuousAt_id.sub continuousAt_const).pow k).inv₀ (pow_ne_zero _ (hsph ζ hζ).2)).continuousWithinAt
  by_cases huz : u = z
  · intro k hk
    subst huz
    have hr' : ¬ r < ‖u - u‖ := by rw [sub_self, norm_zero]; linarith
    rw [if_neg hr', mul_zero]
    have h := l112_pow_circle u hr (n := k + 1) (by omega)
    rw [if_neg (show ¬ (k + 1 = 1) by omega)] at h
    rw [← neg_eq_zero, ← h, show ∀ x : ℂ, -x = (-1 : ℂ) * x from fun x => by ring, ← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    have hne := (hsph ζ hζ).2
    rw [show u - ζ = -(ζ - u) by ring]
    field_simp
    ring
  have hstep : ∀ k : ℕ, (∮ ζ in C(z, r), (u - ζ)⁻¹ * ((ζ - z) ^ (k + 1))⁻¹) =
      (u - z)⁻¹ * ((∮ ζ in C(z, r), (u - ζ)⁻¹ * ((ζ - z) ^ k)⁻¹) + ∮ ζ in C(z, r), ((ζ - z) ^ (k + 1))⁻¹) := by
    intro k
    rw [← circleIntegral.integral_add (hint k) (hintp (k + 1)), ← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    obtain ⟨h1, h2⟩ := hsph ζ hζ
    have ha : u - z ≠ 0 := sub_ne_zero.mpr huz
    show (u - ζ)⁻¹ * ((ζ - z) ^ (k + 1))⁻¹ = (u - z)⁻¹ * ((u - ζ)⁻¹ * ((ζ - z) ^ k)⁻¹ + ((ζ - z) ^ (k + 1))⁻¹)
    field_simp
    ring
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rw [hstep n]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : (∮ ζ in C(z, r), (u - ζ)⁻¹ * ((ζ - z) ^ 0)⁻¹) = -(if r < ‖u - z‖ then 0 else 2 * π * I) := by
        rw [← l112_inv_sub_circle hr hus, show ∀ x : ℂ, -x = (-1 : ℂ) * x from fun x => by ring,
          ← circleIntegral.integral_const_mul]
        refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
        simp only [pow_zero, inv_one, mul_one]
        rw [show ζ - u = -(u - ζ) by ring, inv_neg]
        ring
      rw [h0, l112_pow_circle z hr (n := 0 + 1) le_rfl, if_pos rfl]
      split_ifs <;> ring
    · rw [ih hn, l112_pow_circle z hr (n := n + 1) (by omega), if_neg (show ¬ (n + 1 = 1) by omega), add_zero, pow_succ, mul_inv]
      ring

/-- (B) The `eq_1_22` kernel against `(ζ - z)^{-k}` on a circle (`k ≥ 3`). -/
theorem l112_kernel_circle {z u : ℂ} {r : ℝ} (hr : 0 < r) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hus : u ∉ sphere z r) {k : ℕ} (hk : 3 ≤ k) :
    (∮ ζ in C(z, r), kernelRU ζ u / (ζ - z) ^ k) =
      if r < ‖u - z‖ then 2 * π * I / (u - z) ^ k else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = (z - 1) / u - z / (u - 1) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = 1 / u - 1 / (u - 1) := ⟨_, rfl⟩
  have hsph : ∀ ζ ∈ sphere z r, u - ζ ≠ 0 ∧ ζ - z ≠ 0 := fun ζ hζ =>
    ⟨fun h0 => hus (by rw [show u = ζ by linear_combination h0]; exact hζ), (l112_conj_sphere hr hζ).1⟩
  have hint : CircleIntegrable (fun ζ => (u - ζ)⁻¹ * ((ζ - z) ^ (m + 3))⁻¹) z r :=
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      (((continuousAt_const.sub continuousAt_id).inv₀ (hsph ζ hζ).1).mul
        (((continuousAt_id.sub continuousAt_const).pow _).inv₀ (pow_ne_zero _ (hsph ζ hζ).2))).continuousWithinAt
  have hintc : CircleIntegrable (fun ζ => α * ((ζ - z) ^ (m + 3))⁻¹ + β * ((ζ - z) ^ (m + 2))⁻¹) z r :=
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      ((continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).pow _).inv₀
        (pow_ne_zero _ (hsph ζ hζ).2))).add (continuousAt_const.mul (((continuousAt_id.sub
          continuousAt_const).pow _).inv₀ (pow_ne_zero _ (hsph ζ hζ).2)))).continuousWithinAt
  have hintα : CircleIntegrable (fun ζ => α * ((ζ - z) ^ (m + 3))⁻¹) z r :=
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      (continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).pow _).inv₀
        (pow_ne_zero _ (hsph ζ hζ).2))).continuousWithinAt
  have hintβ : CircleIntegrable (fun ζ => β * ((ζ - z) ^ (m + 2))⁻¹) z r :=
    ContinuousOn.circleIntegrable hr.le fun ζ hζ =>
      (continuousAt_const.mul (((continuousAt_id.sub continuousAt_const).pow _).inv₀
        (pow_ne_zero _ (hsph ζ hζ).2))).continuousWithinAt
  have hsplit : (∮ ζ in C(z, r), kernelRU ζ u / (ζ - z) ^ (m + 3)) =
      (∮ ζ in C(z, r), (u - ζ)⁻¹ * ((ζ - z) ^ (m + 3))⁻¹) +
        (α * (∮ ζ in C(z, r), ((ζ - z) ^ (m + 3))⁻¹) + β * ∮ ζ in C(z, r), ((ζ - z) ^ (m + 2))⁻¹) := by
    rw [← circleIntegral.integral_const_mul, ← circleIntegral.integral_const_mul,
      ← circleIntegral.integral_add hintα hintβ, ← circleIntegral.integral_add hint hintc]
    refine circleIntegral.integral_congr hr.le fun ζ hζ => ?_
    obtain ⟨h1, h2⟩ := hsph ζ hζ
    have hu : u ≠ ζ := fun h => h1 (sub_eq_zero.mpr h)
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    show kernelRU ζ u / (ζ - z) ^ (m + 3) = (u - ζ)⁻¹ * ((ζ - z) ^ (m + 3))⁻¹ +
      (α * ((ζ - z) ^ (m + 3))⁻¹ + β * ((ζ - z) ^ (m + 2))⁻¹)
    rw [kernelRU_partial_fractions hu hu0 hu1, hα, hβ]
    field_simp
    ring
  rw [hsplit, l112_cauchy_kernel_circle hr hus (m + 3) (by omega), l112_pow_circle z hr (n := m + 3) (by omega),
    l112_pow_circle z hr (n := m + 2) (by omega), if_neg (show ¬ (m + 3 = 1) by omega),
    if_neg (show ¬ (m + 2 = 1) by omega)]
  split_ifs with h
  · have ha : u - z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
    field_simp
    ring
  · ring

/-- A uniform majorant of the `eq_1_22` kernel for `ζ` in a set with `Im ζ ≥ 2η`, `‖ζ‖ ≤ L`, `0 < η ≤ 1/2`:
`‖R(ζ, u)‖ ≤ D (𝟙_{B(ζ, η)}(u) ‖u - ζ‖⁻¹ + ‖u‖⁻¹ ‖u - 1‖⁻¹ (1 + ‖u‖)⁻¹)` on `𝕌`. -/
theorem l112_R_bound {L η : ℝ} (hη : 0 < η) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ζ : ℂ, ‖ζ‖ ≤ L → 2 * η ≤ ζ.im → ∀ u ∈ upperHalf, ‖kernelRU ζ u‖ ≤
      D * ((ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u + ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by
  refine ⟨L * (L + 1) * max (1 / η ^ 2) ((1 + L) / η + 1), by positivity, fun ζ hζL hζη u hu => ?_⟩
  have hu' : (0 : ℝ) < u.im := hu
  have hRn : ‖kernelRU ζ u‖ = ‖ζ‖ * ‖ζ - 1‖ * (‖u - ζ‖⁻¹ * ‖u‖⁻¹ * ‖u - 1‖⁻¹) := by
    unfold kernelRU
    rw [norm_div]
    simp only [norm_mul]
    rw [div_eq_mul_inv, mul_inv, mul_inv]
  have hζ1 : ‖ζ - 1‖ ≤ L + 1 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hA : ‖ζ‖ * ‖ζ - 1‖ ≤ L * (L + 1) := mul_le_mul hζL hζ1 (norm_nonneg _) hL
  have hm0 : 0 ≤ ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ := by positivity
  have hi0 : 0 ≤ (ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u :=
    Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hM1 : 1 / η ^ 2 ≤ max (1 / η ^ 2) ((1 + L) / η + 1) := le_max_left _ _
  have hM2 : (1 + L) / η + 1 ≤ max (1 / η ^ 2) ((1 + L) / η + 1) := le_max_right _ _
  rw [hRn]
  by_cases hb : u ∈ ball ζ η
  · rw [Set.indicator_of_mem hb]
    rw [mem_ball, dist_eq_norm] at hb
    have him : η ≤ u.im := by
      have h1 : |(u - ζ).im| ≤ ‖u - ζ‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im, abs_le] at h1
      linarith
    have hu0 : η ≤ ‖u‖ := him.trans (Complex.im_le_norm u)
    have hu1 : η ≤ ‖u - 1‖ := by
      have := Complex.im_le_norm (u - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have h1 : ‖u‖⁻¹ * ‖u - 1‖⁻¹ ≤ 1 / η ^ 2 := by
      rw [one_div, pow_two, mul_inv]
      exact mul_le_mul (inv_anti₀ hη hu0) (inv_anti₀ hη hu1) (by positivity) (by positivity)
    have h2 : ‖u - ζ‖⁻¹ * ‖u‖⁻¹ * ‖u - 1‖⁻¹ ≤ max (1 / η ^ 2) ((1 + L) / η + 1) * ‖u - ζ‖⁻¹ := by
      rw [mul_assoc, mul_comm]
      exact mul_le_mul_of_nonneg_right (h1.trans hM1) (by positivity)
    calc ‖ζ‖ * ‖ζ - 1‖ * (‖u - ζ‖⁻¹ * ‖u‖⁻¹ * ‖u - 1‖⁻¹)
        ≤ L * (L + 1) * (max (1 / η ^ 2) ((1 + L) / η + 1) * ‖u - ζ‖⁻¹) :=
          mul_le_mul hA h2 (by positivity) (by positivity)
      _ = L * (L + 1) * max (1 / η ^ 2) ((1 + L) / η + 1) * ‖u - ζ‖⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hm0) (by positivity)
  · rw [Set.indicator_of_notMem hb, zero_add]
    rw [mem_ball, dist_eq_norm, not_lt] at hb
    have hpos : 0 < ‖u - ζ‖ := hη.trans_le hb
    have h1 : 1 + ‖u‖ ≤ ((1 + L) / η + 1) * ‖u - ζ‖ := by
      have e1 : ‖u‖ ≤ ‖u - ζ‖ + ‖ζ‖ := by
        have := norm_add_le (u - ζ) ζ; rwa [sub_add_cancel] at this
      have e2 : (1 + L) ≤ (1 + L) / η * ‖u - ζ‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hη]
        exact mul_le_mul_of_nonneg_left hb (by linarith)
      nlinarith
    have h2 : ‖u - ζ‖⁻¹ ≤ ((1 + L) / η + 1) * (1 + ‖u‖)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      have h3 : 0 < 1 + ‖u‖ := by positivity
      calc (1 : ℝ) = (1 + ‖u‖) * (1 + ‖u‖)⁻¹ := (mul_inv_cancel₀ h3.ne').symm
        _ ≤ ((1 + L) / η + 1) * ‖u - ζ‖ * (1 + ‖u‖)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by ring
    have h4 : ‖u - ζ‖⁻¹ * ‖u‖⁻¹ * ‖u - 1‖⁻¹ ≤
        max (1 / η ^ 2) ((1 + L) / η + 1) * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹) := by
      have := mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_right hM2 (by positivity)))
        (by positivity : (0 : ℝ) ≤ ‖u‖⁻¹ * ‖u - 1‖⁻¹)
      calc _ = ‖u - ζ‖⁻¹ * (‖u‖⁻¹ * ‖u - 1‖⁻¹) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    calc ‖ζ‖ * ‖ζ - 1‖ * (‖u - ζ‖⁻¹ * ‖u‖⁻¹ * ‖u - 1‖⁻¹)
        ≤ L * (L + 1) * (max (1 / η ^ 2) ((1 + L) / η + 1) * (‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹)) :=
          mul_le_mul hA h4 (by positivity) (by positivity)
      _ = _ := by ring

/-- (C) Fubini: the circle integral of `F[μ]/(ζ - z)^k` through the integral representation `eq_1_22`. -/
theorem l112_fubini {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ upperHalf) (k : ℕ) :
    (∮ ζ in C(z, r), varF μ ζ / (ζ - z) ^ k) =
      -(1 / π : ℂ) * ∫ u in upperHalf, μ u * ∮ ζ in C(z, r), kernelRU ζ u / (ζ - z) ^ k := by
  obtain ⟨C₀, hC₀, hCb⟩ := harmonicU_bounded hμ
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hμb : IsBeltramiCoeff μ upperHalf C₀ :=
    ⟨(harmonicU_continuousOn hμ).aestronglyMeasurable hU.measurableSet,
      (ae_restrict_mem hU.measurableSet).mono fun u hu => hCb u hu⟩
  have hrep : ∀ ζ, varF μ ζ = -(1 / π) * ∫ u in upperHalf, kernelRU ζ u * μ u := fun ζ =>
    (eq_1_22_of_bounded hC₀ hμb ζ).1
  -- geometry of the circle
  have hzr : r < z.im := by
    have hm : z - (r : ℂ) * I ∈ closedBall z r := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_of_nonneg hr.le]
    have h := hB hm
    have h' : (z - (r : ℂ) * I).im = z.im - r := by simp
    have h'' : (0 : ℝ) < (z - (r : ℂ) * I).im := h
    linarith
  obtain ⟨η, hηd⟩ : ∃ η : ℝ, η = min (1 / 2) ((z.im - r) / 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηd]; exact lt_min (by norm_num) (by linarith)
  have hη2 : η ≤ 1 / 2 := by rw [hηd]; exact min_le_left _ _
  have hηz : 2 * η ≤ z.im - r := by
    have : η ≤ (z.im - r) / 2 := by rw [hηd]; exact min_le_right _ _
    linarith
  have hL : 0 ≤ ‖z‖ + r := by positivity
  obtain ⟨D, hD0, hD⟩ := l112_R_bound hη hL
  have hcirc : ∀ θ : ℝ, ‖circleMap z r θ‖ ≤ ‖z‖ + r ∧ 2 * η ≤ (circleMap z r θ).im ∧
      ‖circleMap z r θ - z‖ = r := by
    intro θ
    have hs : ‖circleMap z r θ - z‖ = r := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    refine ⟨?_, ?_, hs⟩
    · have := norm_add_le z (circleMap z r θ - z)
      rw [add_sub_cancel, hs] at this
      exact this
    · have h1 : |(circleMap z r θ - z).im| ≤ ‖circleMap z r θ - z‖ := Complex.abs_im_le_norm _
      rw [hs, Complex.sub_im, abs_le] at h1
      linarith
  -- the majorant
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℂ → ℝ, m₀ = fun u => ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ := ⟨_, rfl⟩
  have hm₀i : Integrable m₀ := by rw [hm₀]; exact phiKernel_majorant_integrable
  have hb0 : Integrable ((ball (0 : ℂ) η).indicator fun v : ℂ => ‖v‖⁻¹) :=
    (integrable_indicator_iff measurableSet_ball).2
      (phiKernel_inv_norm_integrableOn.mono_set (ball_subset_ball hη2))
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∫ v, (ball (0 : ℂ) η).indicator (fun v : ℂ => ‖v‖⁻¹) v := ⟨_, rfl⟩
  have hgs : ∀ ζ : ℂ, (fun u => (ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u) =
      fun u => (ball (0 : ℂ) η).indicator (fun v : ℂ => ‖v‖⁻¹) (u - ζ) := by
    intro ζ; funext u
    by_cases h : u ∈ ball ζ η
    · have h' : u - ζ ∈ ball (0 : ℂ) η := by rw [mem_ball, dist_eq_norm, sub_zero]; rw [mem_ball, dist_eq_norm] at h; exact h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : u - ζ ∉ ball (0 : ℂ) η := by rw [mem_ball, dist_eq_norm, sub_zero]; rw [mem_ball, dist_eq_norm] at h; exact h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hgi : ∀ ζ : ℂ, Integrable (fun u => (ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u) := fun ζ => by
    rw [hgs ζ]; exact hb0.comp_sub_right ζ
  have hgJ : ∀ ζ : ℂ, ∫ u, (ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u = J := fun ζ => by
    rw [hgs ζ, hJ]; exact integral_sub_right_eq_self _ ζ
  have hMaj : ∀ ζ : ℂ, Integrable (fun u => C₀ * D * ((ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u + m₀ u)) :=
    fun ζ => ((hgi ζ).add hm₀i).const_mul _
  -- the integrand on `[0, 2π] × 𝕌`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ → ℂ, G = fun θ u => circleMap 0 r θ * I * (-(1 / π : ℂ)) *
      (kernelRU (circleMap z r θ) u * μ u) / (circleMap z r θ - z) ^ k := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = r * (1 / π) / r ^ k := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hGb : ∀ θ, ∀ u ∈ upperHalf, ‖G θ u‖ ≤
      c₁ * (C₀ * D * ((ball (circleMap z r θ) η).indicator (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u)) := by
    intro θ u hu
    obtain ⟨h1, h2, h3⟩ := hcirc θ
    have hR := hD _ h1 h2 u hu
    have hm₀u : m₀ u = ‖u‖⁻¹ * ‖u - 1‖⁻¹ * (1 + ‖u‖)⁻¹ := by rw [hm₀]
    rw [← hm₀u] at hR
    have hμu := hCb u hu
    rw [hG]
    simp only
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_pow, h3, norm_circleMap_zero,
      abs_of_pos hr, Complex.norm_I, mul_one, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, hc₁]
    have hrk : 0 < r ^ k := pow_pos hr k
    rw [div_le_iff₀ hrk]
    have hRμ : ‖kernelRU (circleMap z r θ) u‖ * ‖μ u‖ ≤
        C₀ * D * ((ball (circleMap z r θ) η).indicator (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u) := by
      have hpos : 0 ≤ D * ((ball (circleMap z r θ) η).indicator (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u) :=
        (norm_nonneg _).trans hR
      calc _ ≤ D * ((ball (circleMap z r θ) η).indicator (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u) * C₀ :=
            mul_le_mul hR hμu (norm_nonneg _) hpos
        _ = _ := by ring
    calc r * (1 / π) * (‖kernelRU (circleMap z r θ) u‖ * ‖μ u‖)
        ≤ r * (1 / π) * (C₀ * D * ((ball (circleMap z r θ) η).indicator
            (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u)) :=
          mul_le_mul_of_nonneg_left hRμ (by positivity)
      _ = _ := by field_simp
  have hKm : ∀ θ : ℝ, Measurable fun u => kernelRU (circleMap z r θ) u := fun θ => by
    unfold kernelRU
    exact measurable_const.div (((measurable_id.sub measurable_const).mul measurable_id).mul
      (measurable_id.sub measurable_const))
  have hμm : AEStronglyMeasurable μ (volume.restrict upperHalf) := hμb.1
  have hGθm : ∀ θ, AEStronglyMeasurable (G θ) (volume.restrict upperHalf) := fun θ => by
    have e : G θ = fun u => circleMap 0 r θ * I * (-(1 / π : ℂ)) * (kernelRU (circleMap z r θ) u * μ u) *
        ((circleMap z r θ - z) ^ k)⁻¹ := by
      rw [hG]; funext u; exact div_eq_mul_inv _ _
    rw [e]
    exact (aestronglyMeasurable_const.mul ((hKm θ).aestronglyMeasurable.mul hμm)).mul aestronglyMeasurable_const
  have hGm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict upperHalf)) := by
    have hc : Continuous fun p : ℝ × ℂ => circleMap z r p.1 := (continuous_circleMap z r).comp continuous_fst
    have hK : Measurable fun p : ℝ × ℂ => kernelRU (circleMap z r p.1) p.2 := by
      unfold kernelRU
      exact (hc.measurable.mul (hc.measurable.sub measurable_const)).div
        (((measurable_snd.sub hc.measurable).mul measurable_snd).mul (measurable_snd.sub measurable_const))
    have hμ2 : AEStronglyMeasurable (fun p : ℝ × ℂ => μ p.2)
        ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict upperHalf)) :=
      hμm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h1 : Continuous fun p : ℝ × ℂ => circleMap 0 r p.1 * I * (-(1 / π : ℂ)) :=
      (((continuous_circleMap 0 r).comp continuous_fst).mul continuous_const).mul continuous_const
    have h3 : Continuous fun p : ℝ × ℂ => ((circleMap z r p.1 - z) ^ k)⁻¹ :=
      ((hc.sub continuous_const).pow k).inv₀ fun p => pow_ne_zero _ (by
        intro h0; have := (hcirc p.1).2.2; rw [show circleMap z r p.1 - z = 0 from h0, norm_zero] at this; linarith)
    have e : Function.uncurry G = fun p : ℝ × ℂ => circleMap 0 r p.1 * I * (-(1 / π : ℂ)) *
        (kernelRU (circleMap z r p.1) p.2 * μ p.2) * ((circleMap z r p.1 - z) ^ k)⁻¹ := by
      rw [hG]; funext p; rw [Function.uncurry_apply_pair, div_eq_mul_inv]
    rw [e]
    exact (h1.aestronglyMeasurable.mul (hK.aestronglyMeasurable.mul hμ2)).mul h3.aestronglyMeasurable
  have hgnn : ∀ ζ u, 0 ≤ C₀ * D * ((ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u + m₀ u) := fun ζ u => by
    have h1 : 0 ≤ (ball ζ η).indicator (fun u => ‖u - ζ‖⁻¹) u :=
      Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
    have h2 : 0 ≤ m₀ u := by rw [hm₀]; positivity
    positivity
  have hGθi : ∀ θ, Integrable (G θ) (volume.restrict upperHalf) := fun θ =>
    Integrable.mono' (((hMaj (circleMap z r θ)).const_mul c₁).restrict) (hGθm θ)
      ((ae_restrict_mem hU.measurableSet).mono fun u hu => hGb θ u hu)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = c₁ * (C₀ * D * (J + ∫ u, m₀ u)) := ⟨_, rfl⟩
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) (2 * π))).prod (volume.restrict upperHalf)) := by
    rw [integrable_prod_iff hGm]
    refine ⟨Eventually.of_forall fun θ => hGθi θ, ?_⟩
    refine Integrable.mono' (integrable_const K) hGm.norm.integral_prod_right'
      (Eventually.of_forall fun θ => ?_)
    have hnn : 0 ≤ ∫ u in upperHalf, ‖Function.uncurry G (θ, u)‖ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    have hmi := (hMaj (circleMap z r θ)).const_mul c₁
    calc ∫ u in upperHalf, ‖Function.uncurry G (θ, u)‖
        ≤ ∫ u in upperHalf, c₁ * (C₀ * D * ((ball (circleMap z r θ) η).indicator
            (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u)) :=
          integral_mono_ae (hGθi θ).norm hmi.restrict
            ((ae_restrict_mem hU.measurableSet).mono fun u hu => hGb θ u hu)
      _ ≤ ∫ u, c₁ * (C₀ * D * ((ball (circleMap z r θ) η).indicator
            (fun u => ‖u - circleMap z r θ‖⁻¹) u + m₀ u)) :=
          setIntegral_le_integral hmi (Eventually.of_forall fun u => mul_nonneg hc₁0 (hgnn _ u))
      _ = K := by
          rw [integral_const_mul, integral_const_mul, integral_add (hgi _) hm₀i, hgJ, hK]
  -- both sides as iterated integrals of `G`
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hL : (∮ ζ in C(z, r), varF μ ζ / (ζ - z) ^ k) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ u in upperHalf, G θ u := by
    simp only [circleIntegral, intervalIntegral.integral_of_le h2π]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [deriv_circleMap, smul_eq_mul]
    rw [hrep, hG]
    simp only
    rw [integral_div, integral_const_mul]
    ring
  have hR : (-(1 / π : ℂ) * ∫ u in upperHalf, μ u * ∮ ζ in C(z, r), kernelRU ζ u / (ζ - z) ^ k) =
      ∫ u in upperHalf, ∫ θ in Ioc (0 : ℝ) (2 * π), G θ u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [circleIntegral, intervalIntegral.integral_of_le h2π]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [deriv_circleMap, smul_eq_mul]
    rw [hG]
    simp only
    ring
  rw [hL, hR]
  exact integral_integral_swap hint

/-- (D) The truncated integrals vanish exactly for every `r` with `closedBall z r ⊆ 𝕌` (`k ≥ 4`). -/
theorem l112_punct_zero {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : closedBall z r ⊆ upperHalf) {k : ℕ} (hk : 4 ≤ k) :
    ∫ u in upperHalfPunct z r, μ u / (u - z) ^ k = 0 := by
  have hA := l112_circle_varF_zero hμ hr hB hk
  rw [l112_fubini hμ hr hB k] at hA
  have hs : volume (sphere z r) = 0 := Measure.addHaar_sphere volume z r
  have hae : ∀ᵐ u ∂(volume.restrict upperHalf), μ u * (∮ ζ in C(z, r), kernelRU ζ u / (ζ - z) ^ k) =
      (upperHalf \ ball z r).indicator (fun u => 2 * π * I * (μ u / (u - z) ^ k)) u := by
    have hns : ∀ᵐ u ∂(volume.restrict upperHalf), u ∉ sphere z r :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hs)
    filter_upwards [hns, ae_restrict_mem measurableSet_upperHalf_aux] with u hus hu
    have hu' : (0 : ℝ) < u.im := hu
    have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_im] at hu'; exact lt_irrefl _ hu'
    have hu1 : u ≠ 1 := fun h => by rw [h, Complex.one_im] at hu'; exact lt_irrefl _ hu'
    rw [l112_kernel_circle hr hu0 hu1 hus (by omega)]
    split_ifs with h
    · have hm : u ∈ upperHalf \ ball z r := ⟨hu, by rw [mem_ball, dist_eq_norm, not_lt]; exact h.le⟩
      rw [Set.indicator_of_mem hm]
      ring
    · have hlt : ‖u - z‖ < r := by
        rcases (not_lt.mp h).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (by rw [mem_sphere, dist_eq_norm, h']) hus
      have hm : u ∉ upperHalf \ ball z r := fun hm => hm.2 (by rw [mem_ball, dist_eq_norm]; exact hlt)
      rw [Set.indicator_of_notMem hm, mul_zero]
  rw [integral_congr_ae hae, setIntegral_indicator (measurableSet_upperHalf_aux.diff measurableSet_ball),
    inter_eq_right.mpr diff_subset, integral_const_mul] at hA
  have hc : -(1 / π : ℂ) * (2 * π * I) ≠ 0 := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [hπ, I_ne_zero]
  rw [← mul_assoc] at hA
  exact (mul_eq_zero.mp hA).resolve_left hc

/-- **Lemma 1.12** (TT:1250–1256). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`lim_{ε → 0} ∬_{𝕌(z, ε)} μ(u)/(u - z)⁴ d²u = lim_{ε → 0} ∬_{𝕌(z, ε)} μ(u)/(u - z)⁵ d²u = 0`. -/
theorem l112_lemma_1_12 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun ε : ℝ => ∫ u in upperHalfPunct z ε, μ u / (u - z) ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => ∫ u in upperHalfPunct z ε, μ u / (u - z) ^ 5) (𝓝[>] 0) (𝓝 0) := by
  have hz' : (0 : ℝ) < z.im := hz
  have hB : ∀ ε ∈ Ioo (0 : ℝ) z.im, closedBall z ε ⊆ upperHalf := fun ε hε v hv => by
    have h1 : |(v - z).im| ≤ ‖v - z‖ := Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hv
    rw [Complex.sub_im, abs_le] at h1
    show 0 < v.im
    linarith [hε.2]
  have hev : ∀ k : ℕ, 4 ≤ k → (fun ε : ℝ => ∫ u in upperHalfPunct z ε, μ u / (u - z) ^ k) =ᶠ[𝓝[>] 0]
      fun _ => 0 := fun k hk => by
    filter_upwards [Ioo_mem_nhdsGT hz'] with ε hε
    exact l112_punct_zero hμ hε.1 (hB ε hε) hk
  exact ⟨tendsto_const_nhds.congr' (hev 4 le_rfl).symm, tendsto_const_nhds.congr' (hev 5 (by norm_num)).symm⟩

/-- **Lemma 1.12** (TT:1250–1256). For `μ ∈ Ω^{-1,1}(𝕌)` and `z ∈ 𝕌`,
`lim_{ε → 0} ∬_{𝕌(z, ε)} μ(u)/(u - z)⁴ d²u = lim_{ε → 0} ∬_{𝕌(z, ε)} μ(u)/(u - z)⁵ d²u = 0`. -/
theorem lemma_1_12 {μ φ : ℂ → ℂ} (hμ : IsHarmonicU μ φ) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun ε : ℝ => ∫ u in upperHalfPunct z ε, μ u / (u - z) ^ 4) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => ∫ u in upperHalfPunct z ε, μ u / (u - z) ^ 5) (𝓝[>] 0) (𝓝 0) :=
  l112_lemma_1_12 hμ hz

end TakhtajanTeo
