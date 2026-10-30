import TakhtajanTeo.Ch1.S7Prop71
import TakhtajanTeo.Ch1.WPChangeOfVariables
import TakhtajanTeo.Ch1.S7First
import TakhtajanTeo.Ch1.S7FirstVarL1
import TakhtajanTeo.Ch1.HarmonicL2Bers

/-!
# Program G, F1: the first variation of `g_{μν̄}` (下属1)

Proof of the frozen stub `s7g_first_variation` (interface `S7Thm74_INTERFACE`, 56ff35a2) through the
sub-interface `S7FirstVar_SUBINTERFACE` (b5c9cb02), Option B (line version):
* generic **Hartogs-lite** (`s7g_h_*`): a separately holomorphic, locally bounded function on an open subset of
  `ℂ²` is `C^n` over `ℂ`; holomorphy of, and differentiation under, a parameter integral with a uniform `L¹`
  bound (Cauchy's formula plus Fubini on `[0, 2π] × T`);
* **T2/L2** (`s7g_t2`, `s7g_l2`): `g_{μν̄}(εκ)` as a double kernel integral, transported to `𝕌` by the Cayley
  chart; the kernel is that of the two-coefficient family `W_P` at `P = (ε̄, ε)`;
* **L3** (`s7g_l3_*`): weights, joint continuity, the `L¹` bound from `R1` (`s7g_L1`), and the core
  `s7g_l3_core`;
* **R4a** `s7g_line_C2`, **R4b** `s7g_first_dz`, and `s7g_first_variation`.
-/

open Complex Set MeasureTheory Metric Filter Topology Asymptotics
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC WPCV

/-- Local bounds can be taken on balls inside the open set. -/
theorem s7g_h_loc {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × ℂ} (hp : p ∈ U) :
    ∃ ρ > 0, ∃ M : ℝ, 0 ≤ M ∧ ball p ρ ⊆ U ∧ ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M := by
  obtain ⟨ρ1, hρ1, M, hM⟩ := hb p hp
  obtain ⟨ρ2, hρ2, hsub⟩ := Metric.isOpen_iff.1 hU p hp
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, M, (norm_nonneg _).trans (hM p (mem_ball_self hρ1)),
    (ball_subset_ball (min_le_right _ _)).trans hsub, fun q hq => hM q (ball_subset_ball (min_le_left _ _) hq)⟩

/-- Cauchy estimates in the first variable on a ball of half the radius. -/
theorem s7g_h_slice {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    {p : ℂ × ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hpU : ball p ρ ⊆ U) (hM : ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M)
    {q : ℂ × ℂ} (hq : dist q p < ρ / 2) :
    ‖deriv (fun z => Φ (z, q.2)) q.1‖ ≤ 2 * M / (ρ / 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ ρ / 2 → ‖Φ (q.1 + t, q.2) - Φ q‖ ≤ 2 * M * ‖t‖ / (ρ / 2)) ∧
      ∀ t : ℂ, ‖t‖ ≤ ρ / 2 →
        ‖Φ (q.1 + t, q.2) - Φ q - t * deriv (fun z => Φ (z, q.2)) q.1‖ ≤ 4 * M * ‖t‖ ^ 2 / (ρ / 2) ^ 2 := by
  have hq' := hq
  rw [Prod.dist_eq, max_lt_iff] at hq'
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (ρ / 2), (q.1 + t, q.2) ∈ ball p ρ := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · calc dist (q.1 + t) p.1 ≤ dist (q.1 + t) q.1 + dist q.1 p.1 := dist_triangle _ _ _
        _ < ρ := by
          rw [dist_eq_norm, add_sub_cancel_left]
          linarith [hq'.1]
    · show dist q.2 p.2 < ρ
      linarith [hq'.2]
  set φ : ℂ → ℂ := fun t => Φ (q.1 + t, q.2) with hφ
  have hd : DifferentiableOn ℂ φ (closedBall 0 (ρ / 2)) := by
    intro t ht
    have h := h1 (q.1 + t, q.2) (hpU (hmem t ht))
    have hadd : DifferentiableAt ℂ (fun s : ℂ => q.1 + s) t := (differentiableAt_const _).add differentiableAt_id
    exact (DifferentiableAt.comp t h hadd).differentiableWithinAt
  have hM' : ∀ t ∈ closedBall (0 : ℂ) (ρ / 2), ‖φ t‖ ≤ M := fun t ht => hM _ (hmem t ht)
  obtain ⟨ha, hb, hc⟩ := QCV.qcv_taylor2 (half_pos hρ) hd hM'
  have hder : deriv φ 0 = deriv (fun z => Φ (z, q.2)) q.1 := by
    rw [hφ, deriv_comp_const_add (fun z => Φ (z, q.2)) q.1 0, add_zero]
  have hφ0 : φ 0 = Φ q := by
    simp only [hφ, add_zero]
  refine ⟨hder ▸ ha, fun t ht => ?_, fun t ht => ?_⟩
  · have h := hb t (mem_closedBall_zero_iff.2 ht)
    rwa [hφ0] at h
  · have h := hc t (mem_closedBall_zero_iff.2 ht)
    rwa [hφ0, hder, smul_eq_mul] at h

/-- The partial derivative in the first variable is holomorphic in the second variable
(locally uniform limit of difference quotients). -/
theorem s7g_h_dw {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × ℂ} (hp : p ∈ U) :
    DifferentiableAt ℂ (fun w => deriv (fun z => Φ (z, w)) p.1) p.2 := by
  obtain ⟨ρ, hρ, M, hM0, hpU, hM⟩ := s7g_h_loc hU hb hp
  set R : ℝ := ρ / 2 with hR
  have hR0 : 0 < R := half_pos hρ
  set S : Set ℂ := ball p.2 R with hS
  have hqS : ∀ w ∈ S, dist ((p.1, w) : ℂ × ℂ) p < R := by
    intro w hw
    rw [Prod.dist_eq, max_lt_iff, dist_self]
    exact ⟨hR0, hw⟩
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℂ), h ≠ 0 ∧ ‖h‖ < R := by
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hR0)] with h hh hb
    exact ⟨hh, mem_ball_zero_iff.1 hb⟩
  have hT : TendstoUniformlyOn (fun h w => (Φ (p.1 + h, w) - Φ (p.1, w)) / h)
      (fun w => deriv (fun z => Φ (z, w)) p.1) (𝓝[≠] (0 : ℂ)) S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hδ : 0 < ε * R ^ 2 / (4 * (M + 1)) := by positivity
    have hev2 : ∀ᶠ h in 𝓝[≠] (0 : ℂ), ‖h‖ < ε * R ^ 2 / (4 * (M + 1)) :=
      nhdsWithin_le_nhds (by
        filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with h hh
        exact mem_ball_zero_iff.1 hh)
    filter_upwards [hev, hev2] with h hh hh2
    intro w hw
    obtain ⟨-, -, hc⟩ := s7g_h_slice h1 hρ hpU hM (hqS w hw)
    have hc' := hc h (le_of_lt (by rw [hR] at hh; exact hh.2))
    simp only at hc'
    have hn : 0 < ‖h‖ := norm_pos_iff.2 hh.1
    have heq : deriv (fun z => Φ (z, w)) p.1 - (Φ (p.1 + h, w) - Φ (p.1, w)) / h =
        -((Φ (p.1 + h, w) - Φ (p.1, w) - h * deriv (fun z => Φ (z, w)) p.1) / h) := by
      field_simp [hh.1]
      ring
    rw [dist_eq_norm, heq, norm_neg, norm_div, div_lt_iff₀ hn]
    calc _ ≤ 4 * M * ‖h‖ ^ 2 / (ρ / 2) ^ 2 := hc'
      _ < ε * ‖h‖ := by
        rw [← hR, div_lt_iff₀ (by positivity)]
        have h4 : 4 * (M + 1) * ‖h‖ < ε * R ^ 2 := by
          rw [lt_div_iff₀ (by positivity)] at hh2
          linarith
        nlinarith
  have hF : ∀ᶠ h in 𝓝[≠] (0 : ℂ), DifferentiableOn ℂ (fun w => (Φ (p.1 + h, w) - Φ (p.1, w)) / h) S := by
    filter_upwards [hev] with h hh
    intro w hw
    have hq := hqS w hw
    have hin1 : ((p.1 + h, w) : ℂ × ℂ) ∈ U := by
      apply hpU
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, add_sub_cancel_left]
      rw [Prod.dist_eq, max_lt_iff] at hq
      constructor <;> linarith [hh.2, hq.2]
    have hin0 : ((p.1, w) : ℂ × ℂ) ∈ U := by
      apply hpU
      rw [mem_ball]
      linarith
    exact (((h2 (p.1 + h, w) hin1).sub (h2 (p.1, w) hin0)).div_const h).differentiableWithinAt
  have hD := hT.tendstoLocallyUniformlyOn.differentiableOn hF isOpen_ball
  exact hD.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0))

/-- The partial derivative in the first variable is holomorphic in the first variable. -/
theorem s7g_h_dz {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1) {p : ℂ × ℂ} (hp : p ∈ U) :
    DifferentiableAt ℂ (fun z => deriv (fun z' => Φ (z', p.2)) z) p.1 := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hU p hp
  have hin : ∀ z ∈ ball p.1 ρ, ((z, p.2) : ℂ × ℂ) ∈ U := by
    intro z hz
    apply hsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_self]
    exact ⟨hz, hρ⟩
  have hd : DifferentiableOn ℂ (fun z => Φ (z, p.2)) (ball p.1 ρ) :=
    fun z hz => (h1 _ (hin z hz)).differentiableWithinAt
  exact (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))

/-- Local bound for the partial derivative in the first variable. -/
theorem s7g_h_dbound {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × ℂ} (hp : p ∈ U) :
    ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖deriv (fun z => Φ (z, q.2)) q.1‖ ≤ M := by
  obtain ⟨ρ, hρ, M, -, hpU, hM⟩ := s7g_h_loc hU hb hp
  exact ⟨ρ / 2, half_pos hρ, 2 * M / (ρ / 2), fun q hq => (s7g_h_slice h1 hρ hpU hM (mem_ball.1 hq)).1⟩

/-- **Joint differentiability** with the derivative given by the two partials. -/
theorem s7g_h_fderiv {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × ℂ} (hp : p ∈ U) :
    HasFDerivAt Φ (deriv (fun z => Φ (z, p.2)) p.1 • ContinuousLinearMap.fst ℂ ℂ ℂ +
      deriv (fun w => Φ (p.1, w)) p.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  obtain ⟨ρ, hρ, M, hM0, hpU, hM⟩ := s7g_h_loc hU hb hp
  set R : ℝ := ρ / 2 with hR
  have hR0 : 0 < R := half_pos hρ
  set k : ℂ → ℂ := fun w => deriv (fun z => Φ (z, w)) p.1 with hk
  set d2 : ℂ := deriv (fun w => Φ (p.1, w)) p.2 with hd2
  have hkc : ContinuousAt k p.2 := (s7g_h_dw hU h1 h2 hb hp).continuousAt
  have hs : Tendsto (fun h : ℂ × ℂ => h.2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_snd.tendsto (0 : ℂ × ℂ))
  have hkt : Tendsto (fun h : ℂ × ℂ => k (p.2 + h.2)) (𝓝 0) (𝓝 (k p.2)) :=
    hkc.tendsto.comp ((continuous_const.add continuous_snd).tendsto' 0 p.2 (by simp))
  have hC := (hasDerivAt_iff_isLittleO_nhds_zero.1 (h2 p hp).hasDerivAt)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hc3 : 0 < c / 3 := by positivity
  have hδ : 0 < c * R ^ 2 / (12 * (M + 1)) := by positivity
  have evA : ∀ᶠ h in 𝓝 (0 : ℂ × ℂ), ‖h‖ < min R (c * R ^ 2 / (12 * (M + 1))) := by
    filter_upwards [ball_mem_nhds (0 : ℂ × ℂ) (lt_min hR0 hδ)] with h hh
    exact mem_ball_zero_iff.1 hh
  have evB : ∀ᶠ h in 𝓝 (0 : ℂ × ℂ), dist (k (p.2 + h.2)) (k p.2) < c / 3 :=
    Metric.tendsto_nhds.1 hkt _ hc3
  have evC : ∀ᶠ h in 𝓝 (0 : ℂ × ℂ),
      ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - h.2 • d2‖ ≤ c / 3 * ‖h.2‖ :=
    hs.eventually (hC.def hc3)
  filter_upwards [evA, evB, evC] with h hA hB hCh
  have hA1 := lt_of_lt_of_le hA (min_le_left _ _)
  have hA2 := lt_of_lt_of_le hA (min_le_right _ _)
  have h1n : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have h2n : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have hqd : dist ((p.1, p.2 + h.2) : ℂ × ℂ) p < ρ / 2 := by
    rw [Prod.dist_eq, max_lt_iff, dist_self, dist_eq_norm, add_sub_cancel_left]
    exact ⟨hR0, by linarith⟩
  obtain ⟨-, -, hT⟩ := s7g_h_slice h1 hρ hpU hM hqd
  have hTA := hT h.1 (by linarith)
  simp only at hTA
  have hph : p + h = (p.1 + h.1, p.2 + h.2) := rfl
  have hpp : Φ p = Φ (p.1, p.2) := rfl
  have hlin : (deriv (fun z => Φ (z, p.2)) p.1 • ContinuousLinearMap.fst ℂ ℂ ℂ +
      d2 • ContinuousLinearMap.snd ℂ ℂ ℂ) h = k p.2 * h.1 + d2 * h.2 := by
    simp [hk]
  rw [hlin, hph, hpp]
  have hsplit : Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2) - (k p.2 * h.1 + d2 * h.2) =
      (Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2 + h.2) - h.1 * k (p.2 + h.2)) +
        h.1 * (k (p.2 + h.2) - k p.2) + (Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - h.2 • d2) := by
    rw [smul_eq_mul]
    ring
  rw [hsplit]
  have bA : ‖Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2 + h.2) - h.1 * k (p.2 + h.2)‖ ≤ c / 3 * ‖h‖ := by
    refine hTA.trans ?_
    rw [← hR, div_le_iff₀ (by positivity)]
    have h4 : 12 * (M + 1) * ‖h‖ ≤ c * R ^ 2 := by
      rw [lt_div_iff₀ (by positivity)] at hA2
      linarith
    have hh0 := norm_nonneg h
    have h1sq : ‖h.1‖ ^ 2 ≤ ‖h‖ ^ 2 := by gcongr
    nlinarith
  have bB : ‖h.1 * (k (p.2 + h.2) - k p.2)‖ ≤ c / 3 * ‖h‖ := by
    rw [norm_mul, ← dist_eq_norm, mul_comm]
    exact mul_le_mul hB.le h1n (norm_nonneg _) hc3.le
  have bC : ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - h.2 • d2‖ ≤ c / 3 * ‖h‖ :=
    hCh.trans (by gcongr)
  calc _ ≤ ‖Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2 + h.2) - h.1 * k (p.2 + h.2)‖ +
        ‖h.1 * (k (p.2 + h.2) - k p.2)‖ + ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - h.2 • d2‖ := norm_add₃_le
    _ ≤ c / 3 * ‖h‖ + c / 3 * ‖h‖ + c / 3 * ‖h‖ := by gcongr
    _ = c * ‖h‖ := by ring

/-- Swapping the variables preserves the hypotheses. -/
theorem s7g_h_swap {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ Prod.swap ⁻¹' U, DifferentiableAt ℂ (fun z => Φ (p.2, z)) p.1) ∧
      (∀ p ∈ Prod.swap ⁻¹' U, DifferentiableAt ℂ (fun w => Φ (w, p.1)) p.2) ∧
      ∀ p ∈ Prod.swap ⁻¹' U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ (q.2, q.1)‖ ≤ M := by
  refine ⟨fun p hp => h2 p.swap hp, fun p hp => h1 p.swap hp, fun p hp => ?_⟩
  obtain ⟨ρ, hρ, M, hM⟩ := hb p.swap hp
  refine ⟨ρ, hρ, M, fun q hq => hM q.swap ?_⟩
  simpa [mem_ball, Prod.dist_eq, max_comm] using hq

/-- The partial derivatives satisfy the same hypotheses (first variable). -/
theorem s7g_h_d1_class {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ U, DifferentiableAt ℂ (fun z => deriv (fun z' => Φ (z', p.2)) z) p.1) ∧
      (∀ p ∈ U, DifferentiableAt ℂ (fun w => deriv (fun z => Φ (z, w)) p.1) p.2) ∧
      ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖deriv (fun z => Φ (z, q.2)) q.1‖ ≤ M :=
  ⟨fun _ hp => s7g_h_dz hU h1 hp, fun _ hp => s7g_h_dw hU h1 h2 hb hp, fun _ hp => s7g_h_dbound hU h1 hb hp⟩

/-- The partial derivatives satisfy the same hypotheses (second variable). -/
theorem s7g_h_d2_class {Φ : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ U, DifferentiableAt ℂ (fun z => deriv (fun w => Φ (z, w)) p.2) p.1) ∧
      (∀ p ∈ U, DifferentiableAt ℂ (fun w => deriv (fun w' => Φ (p.1, w')) w) p.2) ∧
      ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖deriv (fun w => Φ (q.1, w)) q.2‖ ≤ M := by
  obtain ⟨g1, g2, gb⟩ := s7g_h_swap h1 h2 hb
  have hU' : IsOpen (Prod.swap ⁻¹' U) := hU.preimage continuous_swap
  obtain ⟨k1, k2, kb⟩ := s7g_h_d1_class (Φ := fun q => Φ (q.2, q.1)) hU' g1 g2 gb
  refine ⟨fun p hp => k2 p.swap (by simpa using hp), fun p hp => k1 p.swap (by simpa using hp), fun p hp => ?_⟩
  obtain ⟨ρ, hρ, M, hM⟩ := kb p.swap (by simpa using hp)
  refine ⟨ρ, hρ, M, fun q hq => hM q.swap ?_⟩
  simpa [mem_ball, Prod.dist_eq, max_comm] using hq

/-- **Hartogs-lite**: separately holomorphic and locally bounded implies `C^n` over `ℂ`. -/
theorem s7g_h_contDiffOn {U : Set (ℂ × ℂ)} (hU : IsOpen U) (n : ℕ) :
    ∀ Φ : ℂ × ℂ → ℂ, (∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1) →
      (∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2) →
      (∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) → ContDiffOn ℂ n Φ U := by
  induction n with
  | zero =>
    intro Φ h1 h2 hb
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (s7g_h_fderiv hU h1 h2 hb hp).continuousAt.continuousWithinAt
  | succ n ih =>
    intro Φ h1 h2 hb
    obtain ⟨a1, a2, ab⟩ := s7g_h_d1_class hU h1 h2 hb
    obtain ⟨b1, b2, bb⟩ := s7g_h_d2_class hU h1 h2 hb
    have hD1 := ih (fun p => deriv (fun z => Φ (z, p.2)) p.1) a1 a2 ab
    have hD2 := ih (fun p => deriv (fun w => Φ (p.1, w)) p.2) b1 b2 bb
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (s7g_h_fderiv hU h1 h2 hb hp).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine ((hD1.smul (contDiffOn_const (c := ContinuousLinearMap.fst ℂ ℂ ℂ))).add
      (hD2.smul (contDiffOn_const (c := ContinuousLinearMap.snd ℂ ℂ ℂ)))).congr fun p hp => ?_
    exact (s7g_h_fderiv hU h1 h2 hb hp).fderiv

/-- The circle-parametrised family is integrable on `[0, 2π] × T` under a uniform `L¹(T)` bound. -/
theorem s7g_h_Gint {F : ℂ → ℂ × ℂ → ℂ} {T : Set (ℂ × ℂ)} (hT : MeasurableSet T) {c : ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => F p.1 p.2) (closedBall c R ×ˢ T))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ≤ ENNReal.ofReal M) :
    MeasureTheory.Integrable (fun q : ℝ × (ℂ × ℂ) => F (circleMap c r q.1) q.2)
      ((MeasureTheory.volume.restrict (Ioc 0 (2 * Real.pi))).prod (MeasureTheory.volume.restrict T)) := by
  have hcm : ∀ θ : ℝ, circleMap c r θ ∈ closedBall c R := fun θ =>
    closedBall_subset_closedBall hrR (circleMap_mem_closedBall c hr.le θ)
  have hcont : ContinuousOn (fun q : ℝ × (ℂ × ℂ) => F (circleMap c r q.1) q.2) (Ioc 0 (2 * Real.pi) ×ˢ T) :=
    hc.comp (((continuous_circleMap c r).comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨hcm q.1, hq.2⟩)
  refine ⟨?_, ?_⟩
  · rw [MeasureTheory.Measure.prod_restrict]
    exact hcont.aestronglyMeasurable (measurableSet_Ioc.prod hT)
  · calc _ ≤ ∫⁻ θ in Ioc 0 (2 * Real.pi), ∫⁻ x in T, ‖F (circleMap c r θ) x‖ₑ :=
          MeasureTheory.lintegral_prod_le _
      _ ≤ ∫⁻ _θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal M := MeasureTheory.lintegral_mono fun θ => hM _ (hcm θ)
      _ < ⊤ := by
          rw [MeasureTheory.setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top

/-- Cauchy's formula under the integral sign (Fubini on `[0, 2π] × T`). -/
theorem s7g_h_cauchy {F : ℂ → ℂ × ℂ → ℂ} {T : Set (ℂ × ℂ)} (hT : MeasurableSet T) {c : ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hc : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => F p.1 p.2) (closedBall c R ×ˢ T))
    (hhol : ∀ x ∈ T, DifferentiableOn ℂ (fun a => F a x) (ball c R))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ≤ ENNReal.ofReal M) {a : ℂ} (ha : a ∈ ball c r) :
    (2 * Real.pi * I : ℂ) • ∫ x in T, F a x = ∮ z in C(c, r), (z - a)⁻¹ • ∫ x in T, F z x := by
  have hG := s7g_h_Gint hT hr hrR.le hc hM
  have hda : dist a c < r := ha
  set k : ℝ → ℂ := fun θ => deriv (circleMap c r) θ * (circleMap c r θ - a)⁻¹ with hk
  have hdist : ∀ θ : ℝ, ‖circleMap c r θ - c‖ = r := fun θ => by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
  have hge : ∀ θ : ℝ, r - dist a c ≤ ‖circleMap c r θ - a‖ := by
    intro θ
    have h := norm_sub_norm_le (circleMap c r θ - c) (a - c)
    rw [hdist θ, sub_sub_sub_cancel_right, ← dist_eq_norm] at h
    exact h
  have hne : ∀ θ : ℝ, circleMap c r θ - a ≠ 0 := fun θ h => by
    have := hge θ
    rw [h, norm_zero] at this
    linarith
  have hkc : Continuous k := by
    have e : k = fun θ => circleMap 0 r θ * I * (circleMap c r θ - a)⁻¹ := by
      rw [hk]
      funext θ
      rw [deriv_circleMap]
    rw [e]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul
      (((continuous_circleMap c r).sub continuous_const).inv₀ hne)
  have hkb : ∀ θ : ℝ, ‖k θ‖ ≤ r * (r - dist a c)⁻¹ := by
    intro θ
    rw [hk]
    simp only []
    rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr, norm_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (sub_pos.2 hda) (hge θ)) hr.le
  have hH : MeasureTheory.Integrable (fun q : ℝ × (ℂ × ℂ) => k q.1 * F (circleMap c r q.1) q.2)
      ((MeasureTheory.volume.restrict (Ioc 0 (2 * Real.pi))).prod (MeasureTheory.volume.restrict T)) :=
    hG.bdd_mul (hkc.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun q => hkb q.1)
  have hswap := MeasureTheory.integral_integral_swap (f := fun θ x => k θ * F (circleMap c r θ) x) hH
  have e1 : (∮ z in C(c, r), (z - a)⁻¹ • ∫ x in T, F z x) =
      ∫ θ in Ioc 0 (2 * Real.pi), ∫ x in T, k θ * F (circleMap c r θ) x := by
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    ring
  have e2 : ∀ x ∈ T, ∫ θ in Ioc 0 (2 * Real.pi), k θ * F (circleMap c r θ) x = (2 * Real.pi * I : ℂ) * F a x := by
    intro x hx
    have hd : DifferentiableOn ℂ (fun z => F z x) (closedBall c r) := (hhol x hx).mono (closedBall_subset_ball hrR)
    have h := hd.circleIntegral_sub_inv_smul ha
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
    refine Eq.trans ?_ (h.trans (smul_eq_mul _ _))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    ring
  rw [e1, hswap, ← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun hT fun x hx => ?_
  simp only [smul_eq_mul]
  rw [e2 x hx]

/-- **Holomorphy of a parameter integral** under joint continuity, pointwise holomorphy and a uniform `L¹`
bound. -/
theorem s7g_h_param {F : ℂ → ℂ × ℂ → ℂ} {T : Set (ℂ × ℂ)} (hT : MeasurableSet T) {c : ℂ} {R : ℝ}
    (hc : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => F p.1 p.2) (closedBall c R ×ˢ T))
    (hhol : ∀ x ∈ T, DifferentiableOn ℂ (fun a => F a x) (ball c R))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ≤ ENNReal.ofReal M) :
    DifferentiableOn ℂ (fun a => ∫ x in T, F a x) (ball c R) := by
  intro a ha
  have hda : dist a c < R := ha
  have hd0 := dist_nonneg (x := a) (y := c)
  set r : ℝ := (dist a c + R) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R := by rw [hrdef]; linarith
  have har : a ∈ ball c r := by rw [mem_ball, hrdef]; linarith
  have hG := s7g_h_Gint hT hr0 hrR.le hc hM
  have hci : CircleIntegrable (fun z => ∫ x in T, F z x) c r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).2 hG.integral_prod_left
  set r' : NNReal := ⟨r, hr0.le⟩ with hr'
  have hps := hasFPowerSeriesOn_cauchy_integral (R := r') hci (by
    show (0 : ℝ) < r
    exact hr0)
  have hmem : a ∈ Metric.eball c (r' : ENNReal) := by
    rw [Metric.eball_coe]
    exact har
  have hdo := (hps.differentiableOn a hmem).differentiableAt (Metric.isOpen_eball.mem_nhds hmem)
  have hev : (fun a' => ∫ x in T, F a' x) =ᶠ[𝓝 a]
      fun w => (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, (r' : ℝ)), (z - w)⁻¹ • ∫ x in T, F z x := by
    filter_upwards [isOpen_ball.mem_nhds har] with w hw
    rw [show ((r' : ℝ)) = r from rfl, ← s7g_h_cauchy hT hr0 hrR hc hhol hM hw, smul_smul,
      inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul]
  exact (hdo.congr_of_eventuallyEq hev).differentiableWithinAt

/-- **Differentiation under the integral sign** at the centre, for a holomorphic parameter integral as in
`s7g_h_param` (Cauchy's formula for the derivative plus Fubini on `[0, 2π] × T`). -/
theorem s7g_h_deriv {F : ℂ → ℂ × ℂ → ℂ} {T : Set (ℂ × ℂ)} (hT : MeasurableSet T) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (fun p : ℂ × (ℂ × ℂ) => F p.1 p.2) (closedBall c R ×ˢ T))
    (hhol : ∀ x ∈ T, DifferentiableOn ℂ (fun a => F a x) (ball c R))
    {M : ℝ} (hM : ∀ a ∈ closedBall c R, ∫⁻ x in T, ‖F a x‖ₑ ≤ ENNReal.ofReal M) :
    MeasureTheory.IntegrableOn (fun x => deriv (fun a => F a x) c) T ∧
      deriv (fun a => ∫ x in T, F a x) c = ∫ x in T, deriv (fun a => F a x) c := by
  set r : ℝ := R / 2 with hrdef
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hG := s7g_h_Gint hT hr hrR.le hc hM
  set k : ℝ → ℂ := fun θ => deriv (circleMap c r) θ * (1 / (circleMap c r θ - c) ^ 2) with hk
  have hkc : Continuous k := by
    have e : k = fun θ => circleMap 0 r θ * I * (1 / (circleMap 0 r θ) ^ 2) := by
      rw [hk]
      funext θ
      rw [deriv_circleMap, circleMap_sub_center]
    have hne : ∀ θ : ℝ, circleMap 0 r θ ^ 2 ≠ 0 := fun θ => pow_ne_zero _ (by
      intro h
      have := norm_circleMap_zero r θ
      rw [h, norm_zero, abs_of_pos hr] at this
      linarith)
    rw [e]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul
      (continuous_const.div ((continuous_circleMap 0 r).pow 2) hne)
  have hkb : ∀ θ : ℝ, ‖k θ‖ ≤ 1 / r := by
    intro θ
    rw [hk]
    simp only []
    rw [deriv_circleMap, circleMap_sub_center, norm_mul, norm_mul, norm_I, mul_one, norm_div, norm_one, norm_pow,
      norm_circleMap_zero, abs_of_pos hr]
    apply le_of_eq
    field_simp
  have hH : MeasureTheory.Integrable (fun q : ℝ × (ℂ × ℂ) => k q.1 * F (circleMap c r q.1) q.2)
      ((MeasureTheory.volume.restrict (Ioc 0 (2 * Real.pi))).prod (MeasureTheory.volume.restrict T)) :=
    hG.bdd_mul (hkc.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun q => hkb q.1)
  have hswap := MeasureTheory.integral_integral_swap (f := fun θ x => k θ * F (circleMap c r θ) x) hH
  have hΦ : DifferentiableOn ℂ (fun a => ∫ x in T, F a x) (closedBall c r) :=
    (s7g_h_param hT hc hhol hM).mono (closedBall_subset_ball hrR)
  have e1 : (2 * Real.pi * I : ℂ) • deriv (fun a => ∫ x in T, F a x) c =
      ∫ θ in Ioc 0 (2 * Real.pi), ∫ x in T, k θ * F (circleMap c r θ) x := by
    rw [← hΦ.deriv_eq_smul_circleIntegral hr, circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
    ring
  have e2 : ∀ x ∈ T, ∫ θ in Ioc 0 (2 * Real.pi), k θ * F (circleMap c r θ) x =
      (2 * Real.pi * I : ℂ) * deriv (fun a => F a x) c := by
    intro x hx
    have hd : DifferentiableOn ℂ (fun z => F z x) (closedBall c r) := (hhol x hx).mono (closedBall_subset_ball hrR)
    have h := hd.deriv_eq_smul_circleIntegral hr
    rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
    refine Eq.trans ?_ (h.trans (smul_eq_mul _ _))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hk, smul_eq_mul]
    ring
  have hint := hH.integral_prod_right
  have hne : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hae : (fun x => deriv (fun a => F a x) c) =ᵐ[MeasureTheory.volume.restrict T]
      fun x => (2 * Real.pi * I : ℂ)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), k θ * F (circleMap c r θ) x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hT] with x hx
    rw [e2 x hx, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  refine ⟨(hint.const_mul _).congr hae.symm, ?_⟩
  have h3 : deriv (fun a => ∫ x in T, F a x) c =
      (2 * Real.pi * I : ℂ)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), ∫ x in T, k θ * F (circleMap c r θ) x := by
    rw [← e1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [h3, hswap, MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]


/-- (WM2 for every small `ε`, extracted from `p71_wm_Q`.) With `V = w_U(ε̄ m')`:
`w_A(εκ)(S x) = S(V x)` and `∂w_A(εκ)(z) = S'(V(S⁻¹z)) ∂V(S⁻¹ z) (S⁻¹)'(z)` off the poles. -/
theorem s7g_l2_conj {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgκ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), κ z = g z) {m' : ℂ → ℂ}
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {C : ℝ} (hC0 : 0 ≤ C) (hmB : IsBeltramiCoeff m' upperHalf C)
    {ε : ℂ} (hε1 : ‖ε‖ * ‖κ‖ < 1) (hε2 : ‖conj ε‖ * C < 1) :
    (∀ x', x' + I ≠ 0 → wU (fun u => conj ε * m' u) x' + I ≠ 0 →
        wA (ε • κ) (cayley x') = cayley (wU (fun u => conj ε * m' u) x')) ∧
      (∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → wU (fun u => conj ε * m' u) (cayleyInv z0) + I ≠ 0 →
        dz (wA (ε • κ)) z0 = 2 * I / (wU (fun u => conj ε * m' u) (cayleyInv z0) + I) ^ 2 *
          (dz (wU (fun u => conj ε * m' u)) (cayleyInv z0) * (2 * I / (1 - z0) ^ 2))) := by
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨hVc, -, -, -⟩ := p71_V_facts hC0 hmB hε2
  have hconjU : ∀ u : ℂ, u.im < 0 → conj u ∈ upperHalf := fun u hu => by
    show 0 < (conj u).im
    rw [Complex.conj_im]
    linarith
  have hconjI : ∀ u : ℂ, u ≠ -I → conj u ≠ I := fun u h1 h => by
    apply h1
    have := congrArg conj h
    rwa [Complex.conj_conj, Complex.conj_I] at this
  have hV2 : wU (fun u => conj ε * (conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))) = wU (fun u => conj ε * m' u) := by
    show normalizedSolution _ = normalizedSolution _
    refine p71_ns_congr ?_
    filter_upwards [Measure.ae_ne volume I, Measure.ae_ne volume (-I)] with u h1 h2
    unfold extU
    split_ifs with ha hb
    · simp only [hm' u ha h1]
    · simp only [hm' (conj u) (hconjU u hb) (hconjI u h2)]
    · rfl
  set V := wU (fun u => conj ε * m' u) with hVdef
  have hF1 : ∀ x', x' + I ≠ 0 → V x' + I ≠ 0 → wA (ε • κ) (cayley x') = cayley (V x') := by
    intro x' h1 h2
    have h := p71_wm_conj hκ hg hgκ hε1 x'
    rw [hV2, p71_S_coe h1, p71_S_coe h2] at h
    show finPart (wAS (ε • κ) ((cayley x' : ℂ) : ExtPlane)) = _
    rw [h]
    rfl
  refine ⟨hF1, ?_⟩
  have hcinvc : ∀ z0 : ℂ, z0 ≠ 1 → ContinuousAt cayleyInv z0 := fun z0 h => (p71_cinv_hasDeriv h).continuousAt
  have hloc : ∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → V (cayleyInv z0) + I ≠ 0 →
      wA (ε • κ) =ᶠ[𝓝 z0] fun z' => cayley (V (cayleyInv z')) := by
    intro z0 h0 h1 h2
    have hc1 : ContinuousAt (fun z' => cayleyInv z' + I) z0 := (hcinvc z0 h0).add continuousAt_const
    have hc2 : ContinuousAt (fun z' => V (cayleyInv z') + I) z0 :=
      (hVc.continuousAt.comp (hcinvc z0 h0)).add continuousAt_const
    filter_upwards [hc1.eventually_ne h1, hc2.eventually_ne h2, continuousAt_id.eventually_ne h0]
      with z' e1 e2 e3
    have := hF1 (cayleyInv z') e1 e2
    rwa [p71_cay_cinv (show z' ≠ 1 from e3)] at this
  intro z0 h0 h1 h2
  have e0 : dz (wA (ε • κ)) z0 = dz (fun z' => cayley (V (cayleyInv z'))) z0 := by
    simp only [dz, (hloc z0 h0 h1 h2).fderiv_eq]
  have hL := s23_wirtinger_comp_left (g := fun z' => V (cayleyInv z')) (h := cayley) (k := cayleyInv) (z := z0)
    (hVc.continuousAt.comp (hcinvc z0 h0)) (p71_cay_hasDeriv h2).differentiableAt
    (p71_cinv_hasDeriv (p71_cay_ne_one h2)).differentiableAt
    (by
      filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne h2] with w hw
      exact p71_cinv_cay hw)
  have hR := s23_wirtinger_comp_right (g := V) (T := cayleyInv) (S := cayley) (z := z0)
    (p71_cinv_hasDeriv h0).differentiableAt (p71_cay_hasDeriv h1).differentiableAt
    (by
      filter_upwards [continuousAt_id.eventually_ne h0] with w hw
      exact p71_cay_cinv hw)
    (by
      filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne h1] with w hw
      exact p71_cinv_cay hw)
  rw [e0, show (fun z' => cayley (V (cayleyInv z'))) = cayley ∘ (fun z' => V (cayleyInv z')) from rfl, hL.1,
    show (fun z' => V (cayleyInv z')) = V ∘ cayleyInv from rfl, hR.1, (p71_cay_hasDeriv h2).deriv,
    (p71_cinv_hasDeriv h0).deriv]

/-- `2i/(1 - S(x))² = (x + i)²/(2i)` for the Cayley map `S`. -/
theorem s7g_l2_dt {x : ℂ} (hx : x + I ≠ 0) : 2 * I / (1 - cayley x) ^ 2 = (x + I) ^ 2 / (2 * I) := by
  have h : 1 - cayley x = 2 * I / (x + I) := by
    unfold cayley
    field_simp
    ring
  rw [h]
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp

/-- `1 - S(x̄₁) \overline{S(x̄₂)} = 2i (x₂ - x̄₁)/((x̄₁ + i)(x₂ - i))`. -/
theorem s7g_l2_den {a b : ℂ} (ha : conj a + I ≠ 0) (hb : conj b + I ≠ 0) :
    1 - cayley (conj b) * conj (cayley (conj a)) = 2 * I * (a - conj b) / ((conj b + I) * (a - I)) := by
  have ha' : a - I ≠ 0 := by
    intro h
    apply ha
    have := congrArg conj h
    simp only [map_sub, Complex.conj_I, map_zero] at this
    linear_combination this
  have ha'' : -I + a ≠ 0 := by rwa [neg_add_eq_sub]
  have hb' : conj b + I ≠ 0 := hb
  have hb'' : I + conj b ≠ 0 := by rwa [add_comm]
  unfold cayley
  simp only [map_div₀, map_sub, map_add, Complex.conj_conj, Complex.conj_I, sub_neg_eq_add]
  rw [div_mul_div_comm, one_sub_div (mul_ne_zero hb (by simpa [sub_eq_add_neg] using ha'))]
  congr 1
  ring

/-- **The Cayley algebra of the transport.** -/
theorem s7g_l2_alg {s t a b ds dt M N : ℂ} (hs : conj s + I ≠ 0) (ht : conj t + I ≠ 0)
    (ha : conj a + I ≠ 0) (hb : conj b + I ≠ 0) (hab : b - conj a ≠ 0) :
    ((‖2 * I / (conj s + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
        (M * (2 * I / (conj a + I) ^ 2 * (conj ds * (2 * I / (1 - cayley (conj s)) ^ 2))) ^ 2 *
          conj (((‖2 * I / (conj t + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
            (N * (2 * I / (conj b + I) ^ 2 * (conj dt * (2 * I / (1 - cayley (conj t)) ^ 2))) ^ 2 /
              (1 - cayley (conj b) * conj (cayley (conj a))) ^ 4))) =
      M * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) *
        (conj (N * (conj (2 * I / (conj t + I) ^ 2) / (2 * I / (conj t + I) ^ 2))) *
          (dt * conj ds / (b - conj a) ^ 2) ^ 2) := by
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hneg : ∀ x : ℂ, conj x + I ≠ 0 → x - I ≠ 0 := by
    intro x hx h; apply hx
    have := congrArg conj h
    simp only [map_sub, Complex.conj_I, map_zero, sub_neg_eq_add] at this
    exact this
  have hsc := hneg s hs
  have htc := hneg t ht
  have hac := hneg a ha
  have hbc := hneg b hb
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, hn, s7g_l2_dt hs, s7g_l2_dt ht, s7g_l2_den ha hb]
  simp only [map_mul, map_div₀, map_pow, map_neg, map_add, map_sub, Complex.conj_conj, Complex.conj_I,
    map_ofNat, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [show conj a - b = -(b - conj a) by ring]
  generalize (2 : ℂ) * I = c at hI ⊢
  generalize conj s + I = p at hs ⊢
  generalize s - I = p' at hsc ⊢
  generalize conj t + I = q at ht ⊢
  generalize t - I = q' at htc ⊢
  generalize conj a + I = A at ha ⊢
  generalize a - I = A' at hac ⊢
  generalize conj b + I = B at hb ⊢
  generalize b - I = B' at hbc ⊢
  generalize b - conj a = D at hab ⊢
  field_simp

/-- Inner change of variables `ζ = w_η(ξ)` in the kernel integral of `P(R(ν, η))`. -/
theorem s7g_t2_inner {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior) {η : LinfStar} (hη : η ∈ LinfStarBall)
    (y : ℂ) :
    (∫ ζ in unitDiscExterior, RnmFun (toLinf ν) η ζ / (1 - ζ * conj y) ^ 4) =
      ∫ ξ in unitDiscExterior, ν ξ * dz (wA η) ξ ^ 2 / (1 - wA η ξ * conj y) ^ 4 := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  set m : ℂ → ℂ := ⇑(Rnm (toLinf ν) η) with hm
  have h1 : (∫ ζ in unitDiscExterior, RnmFun (toLinf ν) η ζ / (1 - ζ * conj y) ^ 4) =
      ∫ ζ in unitDiscExterior, m ζ / (1 - ζ * conj y) ^ 4 := by
    apply integral_congr_ae
    filter_upwards [wpcv_RnmFun_ae hη (toLinf ν)] with ζ hζ
    rw [hm, hζ]
  have hmm : Measurable m := (Lp.stronglyMeasurable _).measurable
  have hG : Measurable fun ζ : ℂ => m ζ / (1 - ζ * conj y) ^ 4 := hmm.div (by fun_prop)
  rw [h1, wpcv_cov hη _ hG]
  have hR1 := bc_pullback_ae hη (wpcv_RnmFun_ae hη (toLinf ν))
  have hw := bc_wA_ae hη
  have hwE := bc_pullback_ae hη (ae_restrict_mem hE)
  apply integral_congr_ae
  filter_upwards [hR1, ae_restrict_of_ae hw, ae_restrict_mem hE, hwE, wp_harmonic_toLinf_ae hν] with
    z hz1 hz3 hzE hzw hzν
  obtain ⟨-, hdz, hdil, hlt⟩ := hz3
  have hext : extA η z = η z := by
    have : 1 < ‖z‖ := by simpa [unitDiscExterior] using hzE
    simp [extA, this]
  have hjac : jacobian (wA η) z = (1 - ‖η z‖ ^ 2) * ‖dz (wA η) z‖ ^ 2 := by
    have hdb : dzbar (wA η) z = η z * dz (wA η) z := by
      have := hdil
      unfold complexDilatation at this
      rw [hext] at this
      field_simp at this
      rw [mul_comm]
      exact this
    unfold jacobian
    rw [hdb, norm_mul]
    ring
  have hηlt : ‖η z‖ < 1 := by
    have := hlt
    rw [hdil, hext] at this
    exact this
  have hne : (1 - ‖η z‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg (η z)]
  have hwn : wA η z ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hzw
  have hc : conj (dz (wA η) z) ≠ 0 := by simpa using hdz
  have hRz : m (wA η z) = ν z / (1 - ‖η z‖ ^ 2) * (dz (wA η) z / conj (dz (wA η) z)) := by
    have h1' : m (wA η z) = RnmFun (toLinf ν) η (wA η z) := hz1
    rw [h1']
    show (fun u => (toLinf ν) u / (1 - ‖η u‖ ^ 2) * (dz (wA η) u / conj (dz (wA η) u)))
      (Function.invFun (wA η) (wA η z)) = _
    rw [bc_invFun_wA hwn]
    simp only [hzν]
  have hne' : ((1 - ‖η z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hsq : ((‖dz (wA η) z‖ : ℂ)) ^ 2 = dz (wA η) z * conj (dz (wA η) z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  change ((jacobian (wA η) z : ℝ) : ℂ) * (m (wA η z) / (1 - wA η z * conj y) ^ 4) = _
  rw [hjac, hRz]
  push_cast at hne' ⊢
  rw [hsq]
  field_simp

/-- **T2**: the `𝔻*`-model double-integral formula for `g_{μν̄}(η)`. -/
theorem s7g_t2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {η : LinfStar} (hη : η ∈ LinfStarBall) :
    gWP μ ν η = (12 / π : ℂ) * ∫ z in unitDiscExterior, μ z * dz (wA η) z ^ 2 *
      conj (∫ ξ in unitDiscExterior, ν ξ * dz (wA η) ξ ^ 2 / (1 - wA η ξ * conj (wA η z)) ^ 4) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [x5_line2 hμ hν hη, ← integral_const_mul]
  have hwE := bc_pullback_ae hη (ae_restrict_mem hE)
  apply integral_congr_ae
  filter_upwards [hwE] with z hzw
  have hy : 1 < ‖wA η z‖ := by simpa [unitDiscExterior] using hzw
  set y := wA η z with hyd
  set d := dz (wA η) z with hdd
  have hI := s7g_t2_inner hν hη y
  have hQ : Qfun (toLinf ν) η z = (3 * (1 - ‖y‖ ^ 2) ^ 2 / π : ℝ) *
      (∫ ζ in unitDiscExterior, RnmFun (toLinf ν) η ζ / (1 - ζ * conj y) ^ 4) * (conj d / d) := by
    show harmonicProjFun (RnmFun (toLinf ν) η) y * (conj d / d) = _
    unfold harmonicProjFun
    push_cast
    ring
  rw [hQ, hI]
  have hr : (rho y : ℂ) * ((3 * (1 - ‖y‖ ^ 2) ^ 2 / π : ℝ) : ℂ) = (12 / π : ℂ) := by
    unfold rho
    have h1 : (1 - ‖y‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg y]
    have h1c : (1 - (‖y‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1
    push_cast
    field_simp
    try ring
  set J := ∫ ξ in unitDiscExterior, ν ξ * dz (wA η) ξ ^ 2 / (1 - wA η ξ * conj y) ^ 4 with hJ
  by_cases hd : d = 0
  · simp [hd]
  have hsq : ((‖d‖ : ℂ)) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hcd : conj d ≠ 0 := by simpa using hd
  simp only [map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  rw [hsq]
  calc μ z * (((3 * (1 - (‖y‖ : ℂ) ^ 2) ^ 2 / (π : ℂ))) * conj J * (d / conj d)) *
        ((rho y : ℂ) * (d * conj d))
      = μ z * d ^ 2 * conj J * ((rho y : ℂ) * ((3 * (1 - (‖y‖ : ℂ) ^ 2) ^ 2 / (π : ℂ)))) := by
        field_simp
        try ring
    _ = _ := by
        rw [show ((3 * (1 - (‖y‖ : ℂ) ^ 2) ^ 2 / (π : ℂ))) = ((3 * (1 - ‖y‖ ^ 2) ^ 2 / π : ℝ) : ℂ) by push_cast; ring,
          hr]
        ring

/-- **L2**: the transport of `g_{μν̄}(εκ)` to the model `𝕌`, as a double integral of the `W_P`-kernel at
`P = (ε̄, ε)`, with the pulled-back weights `A_μ(s) = μ(S s̄) \overline{S'(s̄)}/S'(s̄)`. -/
theorem s7g_l2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgκ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), κ z = g z) {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ')
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {C : ℝ} (hC0 : 0 ≤ C) (hCb : ∀ u ∈ upperHalf, ‖m' u‖ ≤ C)
    {ε : ℂ} (hε1 : ‖ε‖ * ‖κ‖ < 1) (hε2 : ‖conj ε‖ * C < 1) :
    gWP μ ν (ε • κ) = (12 / π : ℂ) * ∫ s in upperHalf,
      μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) *
        ∫ t in upperHalf, conj (ν (cayley (conj t)) * (conj (2 * I / (conj t + I) ^ 2) / (2 * I / (conj t + I) ^ 2))) *
          (dz (wU fun u => conj ε * m' u) t * dz (wU fun u => conj ε * m' u) (conj s) /
            (wU (fun u => conj ε * m' u) t - wU (fun u => conj ε * m' u) (conj s)) ^ 2) ^ 2 := by
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  obtain ⟨hF1, hdzw⟩ := s7g_l2_conj hκ hg hgκ hm' hC0 hmB hε1 hε2
  obtain ⟨-, hVbij, hVs, -⟩ := p71_V_facts hC0 hmB hε2
  set V := wU (fun u => conj ε * m' u) with hVdef
  have hjoint := wr_joint_contDiff_U hC0 hmB (wr_isHarmonicU_contDiffOn hharm)
  have hVd : DifferentiableOn ℝ V upperHalf :=
    (hjoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun u hu => (⟨hε2, hu⟩ : (conj ε, u) ∈ {ε : ℂ | ‖ε‖ * C < 1} ×ˢ upperHalf))).differentiableOn
      (by norm_num)
  have hVup : ∀ u ∈ upperHalf, V u ∈ upperHalf := fun u hu => e124_wU_upper hC0 hmB hε2 hu
  have hdzs : ∀ u ∈ upperHalf, dz V (conj u) = conj (dz V u) := by
    intro u hu
    have hd : DifferentiableAt ℝ V (conj (conj u)) := by
      rw [Complex.conj_conj]
      exact hVd.differentiableAt (hUo.mem_nhds hu)
    have h := (abR_x_dz_dzbar_conj hd).2.1
    have hfun : (fun w => conj (V (conj w))) = V := funext fun w => by rw [hVs, Complex.conj_conj]
    rwa [hfun, Complex.conj_conj] at h
  have hη : ε • κ ∈ LinfStarBall := by
    show ε • κ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact hε1
  -- pointwise facts at a point of `𝕌` away from `i` and `V⁻¹(i)`
  have hpt : ∀ x ∈ upperHalf, x ≠ I → x ≠ Function.invFun V I →
      conj x + I ≠ 0 ∧ conj (V x) + I ≠ 0 ∧
        wA (ε • κ) (cayley (conj x)) = cayley (conj (V x)) ∧
        dz (wA (ε • κ)) (cayley (conj x)) =
          2 * I / (conj (V x) + I) ^ 2 * (conj (dz V x) * (2 * I / (1 - cayley (conj x)) ^ 2)) := by
    intro x hx hxI hxV
    have hc : conj x + I ≠ 0 := by
      intro h; apply hxI
      have := congrArg conj h
      simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
      linear_combination this
    have hVxI : V x ≠ I := by
      intro h; apply hxV
      have := Function.leftInverse_invFun hVbij.1 x
      rw [h] at this
      exact this.symm
    have ha : conj (V x) + I ≠ 0 := by
      intro h; apply hVxI
      have := congrArg conj h
      simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
      linear_combination this
    have hVc : V (conj x) = conj (V x) := hVs x
    have hz0 : cayley (conj x) ≠ 1 := p71_cay_ne_one hc
    have hci : cayleyInv (cayley (conj x)) = conj x := p71_cinv_cay hc
    refine ⟨hc, ha, ?_, ?_⟩
    · rw [hF1 (conj x) hc (by rw [hVc]; exact ha), hVc]
    · rw [hdzw _ hz0 (by rw [hci]; exact hc) (by rw [hci, hVc]; exact ha), hci, hVc, hdzs x hx]
  rw [s7g_t2 hμ hν hη]
  congr 1
  rw [p71_cov]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I),
    ae_restrict_of_ae (Measure.ae_ne volume (Function.invFun V I))] with s hs hsI hsV
  obtain ⟨hcs, has, hws, hdzws⟩ := hpt s hs hsI hsV
  rw [p71_cov, ← integral_conj, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I),
    ae_restrict_of_ae (Measure.ae_ne volume (Function.invFun V I))] with t ht htI htV
  obtain ⟨hct, hat, hwt, hdzwt⟩ := hpt t ht htI htV
  have hab : V t - conj (V s) ≠ 0 := by
    intro h
    have h1 : 0 < (V t).im := hVup t ht
    have h2 : 0 < (V s).im := hVup s hs
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  rw [hwt, hdzwt, hws, hdzws, hVs s, hdzs s hs]
  exact s7g_l2_alg hcs hct has hat hab


/-- `ℝ≥0∞` version of `p71_cov`: the Cayley chart `η ↦ S(η̄)` from `𝕌` onto `𝔻*`. -/
theorem s7g_l3_cov (G : ℂ → ℝ≥0∞) :
    ∫⁻ ζ in unitDiscExterior, G ζ =
      ∫⁻ η in upperHalf, ENNReal.ofReal (‖2 * I / (conj η + I) ^ 2‖ ^ 2) * G (cayley (conj η)) := by
  have hU := measurableSet_upperHalf_aux
  have hd : ∀ w : ℂ, w ≠ -I → w + I ≠ 0 := fun w hw h => hw (by linear_combination h)
  have hLo : IsOpen ({w : ℂ | w.im < 0} \ {-I}) :=
    (isOpen_lt Complex.continuous_im continuous_const).sdiff isClosed_singleton
  have hdiff : DifferentiableOn ℂ cayley ({w : ℂ | w.im < 0} \ {-I}) := fun w hw =>
    (p71_cay_hasDeriv (hd w hw.2)).differentiableAt.differentiableWithinAt
  have hinj : InjOn cayley ({w : ℂ | w.im < 0} \ {-I}) := fun a ha b hb hab => by
    rw [← p71_cinv_cay (hd a ha.2), hab, p71_cinv_cay (hd b hb.2)]
  have himg : cayley '' ({w : ℂ | w.im < 0} \ {-I}) = unitDiscExterior := by
    ext ζ
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact p71_cay_ext hw.1 (hd w hw.2)
    · intro hζ
      have hζ' : (1 : ℝ) < ‖ζ‖ := hζ
      have hζ1 : ζ ≠ 1 := by
        intro h
        rw [h, norm_one] at hζ'
        exact lt_irrefl _ hζ'
      refine ⟨cayleyInv ζ, ⟨p71_cinv_im hζ', fun h => ?_⟩, p71_cay_cinv hζ1⟩
      have e := p71_cay_cinv hζ1
      rw [mem_singleton_iff.mp h] at e
      have h0 : cayley (-I) = 0 := by
        show (-I - I) / (-I + I) = 0
        simp
      rw [h0] at e
      rw [← e, norm_zero] at hζ'
      linarith
  have hpre : (⇑Complex.conjLIE) ⁻¹' ({w : ℂ | w.im < 0} \ {-I}) = upperHalf \ {I} := by
    ext w
    simp only [mem_preimage, Set.mem_sdiff, mem_ofPred_eq, mem_singleton_iff, Complex.conjLIE_apply,
      Complex.conj_im]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨show 0 < w.im by linarith, fun h => h2 (by rw [h, Complex.conj_I])⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith [show 0 < w.im from h1], fun h => h2 ?_⟩
      have := congrArg conj h
      simpa using this
  have hnull : (upperHalf \ {I} : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  have hemb : MeasurableEmbedding (⇑Complex.conjLIE) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have h := (Complex.conjLIE.measurePreserving).setLIntegral_comp_preimage_emb hemb
    (fun z => ENNReal.ofReal (‖deriv cayley z‖ ^ 2) * G (cayley z)) ({w : ℂ | w.im < 0} \ {-I})
  rw [← himg, d2_lintegral_image hLo hdiff hinj, ← h, hpre, ← setLIntegral_congr hnull]
  refine setLIntegral_congr_fun (hU.diff (measurableSet_singleton I)) fun v hv => ?_
  have hvd : conj v + I ≠ 0 := fun h => hv.2 (mem_singleton_iff.2 (by
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this))
  simp only [Complex.conjLIE_apply]
  rw [(p71_cay_hasDeriv hvd).deriv]

/-- `conj s + i ≠ 0` on `𝕌 ∖ {i}`. -/
theorem s7g_l3_cne {s : ℂ} (hs : s ≠ I) : conj s + I ≠ 0 := fun h => hs (by
  have := congrArg conj h
  simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
  linear_combination this)

/-- Finite weighted `L²` norm of a pulled-back weight. -/
theorem s7g_l3_L2fin {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {m : ℂ → ℂ}
    (hm : ∀ u ∈ upperHalf, u ≠ I → ‖m u‖ = ‖μ (cayley (conj u))‖) :
    ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞ := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨-, -, -, hfin⟩ := hμ
  have hfin' : (∫⁻ z in unitDiscExterior, (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) < ∞ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    have : normL2 unitDiscExterior μ = ⊤ := by
      unfold normL2
      rw [hc, ENNReal.top_rpow_of_pos (by norm_num)]
    rw [this] at hfin
    exact lt_irrefl _ hfin
  rw [s7g_l3_cov] at hfin'
  have hnull : (upperHalf \ {I} : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  refine lt_of_le_of_lt (le_of_eq ?_) hfin'
  rw [← setLIntegral_congr hnull, ← setLIntegral_congr hnull]
  refine setLIntegral_congr_fun (hU.diff (measurableSet_singleton I)) fun u hu => ?_
  have hrho := (p71r_iso hu.1 hu.1 hu.2 hu.2).2
  have hr0 : 0 ≤ rho (cayley (conj u)) := by unfold rho; positivity
  rw [enorm_eq_nnnorm, d2_nnnorm_sq, d2_nnnorm_sq, hm u hu.1 hu.2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hrho]
  congr 1
  ring

/-- The pulled-back weight `A_μ(s) = μ(S s̄) \overline{S'(s̄)}/S'(s̄)` has the modulus of `μ(S s̄)`. -/
theorem s7g_l3_Anorm (μ : ℂ → ℂ) {s : ℂ} (hs : s ≠ I) :
    ‖μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2))‖ =
      ‖μ (cayley (conj s))‖ := by
  have hd : 2 * I / (conj s + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (s7g_l3_cne hs))
  rw [norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd), mul_one]

/-- Continuity of the pulled-back weight on `𝕌 ∖ {i}`. -/
theorem s7g_l3_Acont {μ : ℂ → ℂ} (hμ : ContinuousOn μ unitDiscExterior) :
    ContinuousOn (fun s => μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)))
      (upperHalf \ {I}) := by
  have hne : ∀ s ∈ upperHalf \ {I}, conj s + I ≠ 0 := fun s hs => s7g_l3_cne hs.2
  have hcay : ContinuousOn (fun s : ℂ => cayley (conj s)) (upperHalf \ {I}) := by
    show ContinuousOn (fun s : ℂ => (conj s - I) / (conj s + I)) (upperHalf \ {I})
    exact ((Complex.continuous_conj.sub continuous_const).continuousOn).div
      ((Complex.continuous_conj.add continuous_const).continuousOn) hne
  have hmaps : MapsTo (fun s : ℂ => cayley (conj s)) (upperHalf \ {I}) unitDiscExterior := by
    intro s hs
    have h1 : (conj s).im < 0 := by
      rw [Complex.conj_im]
      exact neg_neg_of_pos hs.1
    exact p71_cay_ext h1 (hne s hs)
  have hS : ContinuousOn (fun s : ℂ => 2 * I / (conj s + I) ^ 2) (upperHalf \ {I}) :=
    continuousOn_const.div ((Complex.continuous_conj.add continuous_const).pow 2).continuousOn
      fun s hs => pow_ne_zero _ (hne s hs)
  have hS0 : ∀ s ∈ upperHalf \ {I}, 2 * I / (conj s + I) ^ 2 ≠ 0 := fun s hs =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ (hne s hs))
  exact (hμ.comp hcay hmaps).mul ((Complex.continuous_conj.comp_continuousOn hS).div hS hS0)

/-- The harmonic weight on `𝕌` attached to `μ ∈ harmonicL2`, with `|m(u)| = |μ(S ū)|`. -/
theorem s7g_l3_weight {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ∃ m φ : ℂ → ℂ, IsHarmonicU m φ ∧
      (∀ u ∈ upperHalf, u ≠ I → m u = conj (μ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) ∧
      ∀ u ∈ upperHalf, u ≠ I → ‖m u‖ = ‖μ (cayley (conj u))‖ := by
  obtain ⟨C, hC⟩ := harmonicL2_subset_harmonic
  obtain ⟨m, φ, hm, hmf⟩ := p71_wm_harm (hC μ hμ).1 (wp_harmonic_continuousOn hμ) (wp_harmonic_toLinf_ae hμ)
  refine ⟨m, φ, hm, hmf, fun u hu huI => ?_⟩
  rw [hmf u hu huI, norm_mul, norm_mul, (p71_AB_norm hu huI).1, (p71_AB_norm hu huI).2, mul_one, mul_one,
    Complex.norm_conj]

/-- The phase identity `\overline{\overline{S'(s̄)}/S'(s̄)} = S(s)²/\overline{S(s)}² · \overline{S'(s)}/S'(s)`. -/
theorem s7g_l3_phase {s : ℂ} (hs : s ∈ upperHalf) (hsI : s ≠ I) :
    conj (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) =
      cayley s ^ 2 / conj (cayley s) ^ 2 * (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2)) := by
  have h0 : 0 < s.im := hs
  have h1 : s + I ≠ 0 := cayley_den_ne_zero h0
  have h2 : conj s + I ≠ 0 := s7g_l3_cne hsI
  have h3 : s - I ≠ 0 := sub_ne_zero.mpr hsI
  have h4 : conj s - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.I_im, Complex.zero_im] at this
    linarith
  unfold cayley
  simp only [map_div₀, map_mul, map_pow, map_add, map_sub, map_neg, Complex.conj_conj, Complex.conj_I, map_ofNat,
    sub_neg_eq_add, ← sub_eq_add_neg]
  have hI : I ≠ 0 := I_ne_zero
  generalize (starRingEnd ℂ) s + I = q at h2 ⊢
  generalize (starRingEnd ℂ) s - I = q' at h4 ⊢
  generalize s + I = p at h1 ⊢
  generalize s - I = p' at h3 ⊢
  field_simp

/-- `A_μ(s) = \overline{m_μ(s)}` on `𝕌 ∖ {i}`. -/
theorem s7g_l3_Aconj (μ : ℂ → ℂ) {m : ℂ → ℂ} {s : ℂ} (hs : s ∈ upperHalf) (hsI : s ≠ I)
    (hmf : m s = conj (μ (cayley (conj s))) * (cayley s ^ 2 / conj (cayley s) ^ 2) *
      (conj (2 * I / (s + I) ^ 2) / (2 * I / (s + I) ^ 2))) :
    μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) = conj (m s) := by
  rw [hmf, map_mul, map_mul, Complex.conj_conj, mul_assoc, ← map_mul, ← s7g_l3_phase hs hsI, Complex.conj_conj]

/-- `∂_z` of `y ↦ H(ȳ, y)` is the second partial derivative of a jointly holomorphic `H`. -/
theorem s7g_dz_partial {H : ℂ × ℂ → ℂ} {y : ℂ} (hH : DifferentiableAt ℂ H (conj y, y)) :
    dz (fun y => H (conj y, y)) y = deriv (fun b => H (conj y, b)) y := by
  set D := fderiv ℂ H (conj y, y) with hDd
  have hd : HasFDerivAt (fun y : ℂ => H (conj y, y))
      ((D.restrictScalars ℝ).comp ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.prod
        (ContinuousLinearMap.id ℝ ℂ))) y :=
    HasFDerivAt.comp (g := H) (f := fun y : ℂ => (conj y, y)) y (hH.hasFDerivAt.restrictScalars ℝ)
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.prodMk (hasFDerivAt_id y))
  have hb : HasDerivAt (fun b => H (conj y, b)) (D (0, 1)) y :=
    (hH.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (conj y) y)).hasDerivAt
  rw [hb.deriv]
  unfold dz
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    ContinuousLinearMap.coe_restrictScalars', map_one, Complex.conj_I]
  have e1 : ((1 : ℂ), (1 : ℂ)) = ((1 : ℂ), (0 : ℂ)) + ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  have e2 : (-I, I) = (-I) • ((1 : ℂ), (0 : ℂ)) + I • ((0 : ℂ), (1 : ℂ)) := by ext <;> simp
  rw [e1, e2, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Joint continuity of the double-kernel integrand on `closed polydisc × S × S`. -/
theorem s7g_l3_cont {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {S : Set ℂ} (hS : S ⊆ upperHalf) {A B : ℂ → ℂ} (hA : ContinuousOn A S) (hB : ContinuousOn B S)
    {R : ℝ} (hRk : R * k < 1) :
    ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => A p.2.1 * (conj (B p.2.2) *
      (dz (W p.1) p.2.2 * dz (W p.1) (conj p.2.1) / (W p.1 p.2.2 - W p.1 (conj p.2.1)) ^ 2) ^ 2))
      ((closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (S ×ˢ S)) := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hmk hms hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hk hmk hms hW
  have hsub := e64_polydisc_sub hk hRk
  obtain ⟨T, hT⟩ : ∃ T : Set ((ℂ × ℂ) × (ℂ × ℂ)),
      T = (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ×ˢ (S ×ˢ S) := ⟨_, rfl⟩
  rw [← hT]
  have hmem : ∀ p ∈ T, p.1 ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S := by
    rw [hT]
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  have hcomp : ∀ g : (ℂ × ℂ) × (ℂ × ℂ) → ℂ, Continuous g → (∀ p ∈ T, (g p).im ≠ 0) →
      ContinuousOn (fun p => W p.1 (g p)) T ∧ ContinuousOn (fun p => dz (W p.1) (g p)) T := by
    intro g hg hgi
    have hm : MapsTo (fun p : (ℂ × ℂ) × (ℂ × ℂ) => (p.1, g p)) T
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) :=
      fun p hp => ⟨hsub (hmem p hp).1, hgi p hp⟩
    have hc : Continuous fun p : (ℂ × ℂ) × (ℂ × ℂ) => (p.1, g p) := continuous_fst.prodMk hg
    have h1 := hWc.comp hc.continuousOn hm
    have h2 := hDc.comp hc.continuousOn hm
    simp only [Function.comp_def] at h1 h2
    exact ⟨h1, h2⟩
  have him : ∀ p ∈ T, 0 < p.2.1.im ∧ 0 < p.2.2.im := fun p hp =>
    ⟨hS (hmem p hp).2.1, hS (hmem p hp).2.2⟩
  obtain ⟨hWt, hDt⟩ := hcomp (fun p => p.2.2) (continuous_snd.comp continuous_snd) fun p hp =>
    ne_of_gt (him p hp).2
  obtain ⟨hWs, hDs⟩ := hcomp (fun p => conj p.2.1) (Complex.continuous_conj.comp (continuous_fst.comp continuous_snd))
    fun p hp => by rw [Complex.conj_im]; linarith [(him p hp).1]
  have hAc : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => A p.2.1) T :=
    hA.comp (continuous_fst.comp continuous_snd).continuousOn fun p hp => (hmem p hp).2.1
  have hBc : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => conj (B p.2.2)) T :=
    Complex.continuous_conj.comp_continuousOn
      (hB.comp (continuous_snd.comp continuous_snd).continuousOn fun p hp => (hmem p hp).2.2)
  have hne : ∀ p ∈ T, (W p.1 p.2.2 - W p.1 (conj p.2.1)) ^ 2 ≠ 0 := by
    intro p hp
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj p.1 (hsub (hmem p hp).1) h
    have h2 : p.2.2.im = (conj p.2.1).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith [(him p hp).1, (him p hp).2]
  exact hAc.mul (hBc.mul (((hDt.mul hDs).div ((hWt.sub hWs).pow 2) hne).pow 2))

/-- The `W`-family of `s71_b2_*` is the `b = 0` slice of the `R1` family. -/
theorem s7g_l3_Weq (m' : ℂ → ℂ) (a b : ℂ) :
    (normalizedSolution fun u =>
      (a, b).1 * (if 0 < u.im then m' u else 0) + (a, b).2 * (if u.im < 0 then conj (m' (conj u)) else 0)) =
    normalizedSolution fun u =>
      (if 0 < u.im then ((a, (0 : ℂ)), (b, (0 : ℂ))).1.1 * m' u + ((a, (0 : ℂ)), (b, (0 : ℂ))).1.2 * (fun _ => (0 : ℂ)) u
        else 0) +
      (if u.im < 0 then ((a, (0 : ℂ)), (b, (0 : ℂ))).2.1 * conj (m' (conj u)) +
        ((a, (0 : ℂ)), (b, (0 : ℂ))).2.2 * conj ((fun _ => (0 : ℂ)) (conj u)) else 0) := by
  congr 1
  funext u
  split_ifs <;> simp

/-- **Uniform `L¹(S × S)` bound** on the closed polydisc, from `R1`. -/
theorem s7g_l3_L1 {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {S : Set ℂ} (hSm : MeasurableSet S) (hS : S ⊆ upperHalf) {A B m₁ m₂ φ₁ φ₂ : ℂ → ℂ} (h₁ : IsHarmonicU m₁ φ₁) (h₂ : IsHarmonicU m₂ φ₂)
    (hf₁ : ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hf₂ : ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hA : ∀ s ∈ S, ‖A s‖ = ‖m₁ s‖) (hB : ∀ t ∈ S, ‖B t‖ = ‖m₂ t‖)
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) :
    ∃ M : ℝ, ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      ∫⁻ x in S ×ˢ S, ‖A x.1 * (conj (B x.2) *
        (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal M := by
  have hzero : IsBeltramiCoeff (fun _ : ℂ => (0 : ℂ)) upperHalf k :=
    ⟨aestronglyMeasurable_const, Eventually.of_forall fun _ => by simpa using hk⟩
  obtain ⟨M, hMt, hM⟩ := s7g_L1 (a := m') (b := fun _ => (0 : ℂ)) hk hmk hzero hms contDiffOn_const hR hRk rfl
    h₁.1 h₁.2.2 hf₁ h₂.1 h₂.2.2 hf₂
  refine ⟨M.toReal, fun P hP => ?_⟩
  rw [ENNReal.ofReal_toReal hMt.ne]
  have hP' : ((P.1, (0 : ℂ)), (P.2, (0 : ℂ))) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R := by
    obtain ⟨h1, h2⟩ := hP
    rw [mem_closedBall_zero_iff] at h1 h2 ⊢
    simp only [Prod.norm_def, norm_zero]
    exact max_le (max_le h1 hR) (max_le h2 hR)
  have hWP : W P = normalizedSolution fun u =>
      (if 0 < u.im then ((P.1, (0 : ℂ)), (P.2, (0 : ℂ))).1.1 * m' u +
          ((P.1, (0 : ℂ)), (P.2, (0 : ℂ))).1.2 * (fun _ => (0 : ℂ)) u else 0) +
        (if u.im < 0 then ((P.1, (0 : ℂ)), (P.2, (0 : ℂ))).2.1 * conj (m' (conj u)) +
          ((P.1, (0 : ℂ)), (P.2, (0 : ℂ))).2.2 * conj ((fun _ => (0 : ℂ)) (conj u)) else 0) := by
    rw [hW, ← s7g_l3_Weq m' P.1 P.2]
  have e : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => (ofReal_norm z).symm
  calc _ ≤ ∫⁻ s in S, ∫⁻ t in S, ‖A s * (conj (B t) *
          (dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2) ^ 2)‖ₑ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_le _
    _ = ∫⁻ s in S, ∫⁻ t in S, ‖m₁ s‖ₑ * ‖m₂ t‖ₑ *
          ‖dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2‖ₑ ^ 2 := by
        refine setLIntegral_congr_fun hSm fun s hs => ?_
        refine setLIntegral_congr_fun hSm fun t ht => ?_
        simp only [e]
        rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, hA s hs, hB t ht]
        ring
    _ ≤ ∫⁻ s in upperHalf, ∫⁻ t in upperHalf, ‖m₁ s‖ₑ * ‖m₂ t‖ₑ *
          ‖dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2‖ₑ ^ 2 :=
        (lintegral_mono fun s => lintegral_mono_set hS).trans (lintegral_mono_set hS)
    _ ≤ M := by
        rw [hWP]
        exact hM _ hP'


/-- **The `𝕌`-model core of R4a/R4b.** With the harmonic weights `m_μ, m_ν` and the coefficient `m'` of `κ`
transported to `𝕌`, `g_{μν̄}(εκ) = (12/π) Φ(ε̄, ε)` near `0` for a function `Φ` which is `C²` over `ℂ` on a
polydisc, and `∂_b Φ(0, b)|₀ = ∫_𝕌 \overline{m_μ(s)} ∂_ε̄ J_s(0)`, `J_s(e) = ∫_𝕌 m_ν(t) K̄_{e m'}(t, s)²`. -/
theorem s7g_l3_core {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgκ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), κ z = g z) {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ')
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {mμ φμ mν φν : ℂ → ℂ} (hμh : IsHarmonicU mμ φμ)
    (hμf : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (μ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hνh : IsHarmonicU mν φν)
    (hνf : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (ν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∃ Φ : ℂ × ℂ → ℂ, ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) ∧
      (∃ r : ℝ, 0 < r ∧ r ≤ R0 ∧ ∀ ε ∈ ball (0 : ℂ) r, gWP μ ν (ε • κ) = (12 / π : ℂ) * Φ (conj ε, ε)) ∧
      deriv (fun b => Φ (0, b)) 0 = ∫ s in upperHalf, conj (mμ s) *
        dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hms := wr_isHarmonicU_contDiffOn hharm
  have hμn : ∀ u ∈ upperHalf, u ≠ I → ‖mμ u‖ = ‖μ (cayley (conj u))‖ := fun u hu huI => by
    rw [hμf u hu huI, norm_mul, norm_mul, (p71_AB_norm hu huI).1, (p71_AB_norm hu huI).2, mul_one, mul_one,
      Complex.norm_conj]
  have hνn : ∀ u ∈ upperHalf, u ≠ I → ‖mν u‖ = ‖ν (cayley (conj u))‖ := fun u hu huI => by
    rw [hνf u hu huI, norm_mul, norm_mul, (p71_AB_norm hu huI).1, (p71_AB_norm hu huI).2, mul_one, mul_one,
      Complex.norm_conj]
  have hfμ := s7g_l3_L2fin hμ hμn
  have hfν := s7g_l3_L2fin hν hνn
  obtain ⟨S, hSdef⟩ : ∃ S : Set ℂ, S = upperHalf \ {I} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by rw [hSdef]; exact hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := by rw [hSdef]; exact sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := by
    rw [hSdef]
    exact sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ → ℂ, A = fun s =>
      μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ → ℂ, B = fun s =>
      ν (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2)) := ⟨_, rfl⟩
  have hAc : ContinuousOn A S := by rw [hAdef, hSdef]; exact s7g_l3_Acont (wp_harmonic_continuousOn hμ)
  have hBc : ContinuousOn B S := by rw [hBdef, hSdef]; exact s7g_l3_Acont (wp_harmonic_continuousOn hν)
  have hAconj : ∀ s ∈ S, A s = conj (mμ s) := by
    intro s hs
    rw [hSdef] at hs
    rw [hAdef]
    exact s7g_l3_Aconj μ hs.1 hs.2 (hμf s hs.1 hs.2)
  have hBconj : ∀ s ∈ S, conj (B s) = mν s := by
    intro s hs
    rw [hSdef] at hs
    rw [hBdef]
    simp only []
    rw [s7g_l3_Aconj ν hs.1 hs.2 (hνf s hs.1 hs.2), Complex.conj_conj]
  have hAn : ∀ s ∈ S, ‖A s‖ = ‖mμ s‖ := fun s hs => by rw [hAconj s hs, Complex.norm_conj]
  have hBn : ∀ s ∈ S, ‖B s‖ = ‖mν s‖ := fun s hs => by rw [← hBconj s hs, Complex.norm_conj]
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = 1 / (4 * (C + 1)) := ⟨_, rfl⟩
  have hR0p : 0 < R0 := by rw [hR0]; positivity
  have hR0k2 : 2 * R0 * C < 1 := by
    rw [hR0, show 2 * (1 / (4 * (C + 1))) * C = C / (2 * (C + 1)) by field_simp; ring,
      div_lt_one (by positivity)]
    linarith
  have hR0k : R0 * C < 1 := by nlinarith
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ × ℂ → ℂ, F = fun P x => A x.1 * (conj (B x.2) *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  have hcont : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 p.2)
      ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ (S ×ˢ S)) := by
    rw [hF]
    exact s7g_l3_cont hC0 hmB hms hW hSU hAc hBc hR0k
  obtain ⟨M, hM⟩ := s7g_l3_L1 hC0 hmB hms hW hSm hSU hμh hνh hfμ hfν hAn hBn hR0p.le hR0k2
  have hM' : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ∫⁻ x in S ×ˢ S, ‖F P x‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    rw [hF]
    exact hM P hP
  have hTm : MeasurableSet (S ×ˢ S) := hSm.prod hSm
  have hhol : ∀ x ∈ S ×ˢ S,
      (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R0)) ∧
        ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R0) := by
    intro x hx
    have h := s71_b2_holo (μ := fun t => A x.1 * conj (B t)) hC0 hmB hms (hSU hx.1) hR0k hW rfl (hSU hx.2)
    refine ⟨fun b hb => (h.1 b hb).congr fun a _ => ?_, fun a ha => (h.2 a ha).congr fun b _ => ?_⟩
    · rw [hF]
      ring
    · rw [hF]
      ring
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ, Φ = fun P => ∫ x in S ×ˢ S, F P x := ⟨_, rfl⟩
  have hbd : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ‖Φ P‖ ≤ max M 0 := by
    intro P hP
    have h1 := (enorm_integral_le_lintegral_enorm (μ := volume.restrict (S ×ˢ S)) (F P)).trans (hM' P hP)
    have h2 : ENNReal.ofReal ‖Φ P‖ ≤ ENNReal.ofReal (max M 0) := by
      rw [ofReal_norm, hΦ]
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2
  have hpar1 : ∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => Φ (a, b)) (ball (0 : ℂ) R0) := by
    intro b hb
    rw [hΦ]
    refine s7g_h_param (F := fun a x => F (a, b) x) hTm (c := 0) (R := R0) ?_ (fun x hx => (hhol x hx).1 b hb)
      (M := M) (fun a ha => hM' (a, b) ⟨ha, hb⟩)
    exact hcont.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨⟨hp.1, hb⟩, hp.2⟩)
  have hcont2 : ∀ a ∈ closedBall (0 : ℂ) R0, ContinuousOn (fun p : ℂ × (ℂ × ℂ) => F (a, p.1) p.2)
      (closedBall (0 : ℂ) R0 ×ˢ (S ×ˢ S)) := fun a ha =>
    hcont.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨⟨ha, hp.1⟩, hp.2⟩)
  have hpar2 : ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => Φ (a, b)) (ball (0 : ℂ) R0) := by
    intro a ha
    rw [hΦ]
    exact s7g_h_param (F := fun b x => F (a, b) x) hTm (c := 0) (R := R0) (hcont2 a ha)
      (fun x hx => (hhol x hx).2 a ha) (M := M) (fun b hb => hM' (a, b) ⟨ha, hb⟩)
  have hUo : IsOpen (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := isOpen_ball.prod isOpen_ball
  have h1 : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1 :=
    fun p hp => (hpar1 p.2 (ball_subset_closedBall hp.2)).differentiableAt (isOpen_ball.mem_nhds hp.1)
  have h2 : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2 :=
    fun p hp => (hpar2 p.1 (ball_subset_closedBall hp.1)).differentiableAt (isOpen_ball.mem_nhds hp.2)
  have hb : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, ∃ ρ > 0, ∃ M' : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M' := by
    intro p hp
    obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hUo p hp
    exact ⟨ρ, hρ, max M 0, fun q hq =>
      hbd q ⟨ball_subset_closedBall (hsub hq).1, ball_subset_closedBall (hsub hq).2⟩⟩
  have hΦ2 : ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := by
    simpa using s7g_h_contDiffOn hUo 2 Φ h1 h2 hb
  -- the transport identity on a small disc
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (1 / (‖κ‖ + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  have hEq : ∀ ε ∈ ball (0 : ℂ) r, gWP μ ν (ε • κ) = (12 / π : ℂ) * Φ (conj ε, ε) := by
    intro ε hε
    have hεr : ‖ε‖ < r := mem_ball_zero_iff.1 hε
    have hεR : ‖ε‖ < R0 := lt_of_lt_of_le hεr hrR
    have hεκ : ‖ε‖ < 1 / (‖κ‖ + 1) := lt_of_lt_of_le hεr (by rw [hr]; exact min_le_right _ _)
    have hε1 : ‖ε‖ * ‖κ‖ < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hεκ
      nlinarith [norm_nonneg ε, norm_nonneg κ]
    have hε2 : ‖conj ε‖ * C < 1 := by
      rw [Complex.norm_conj]
      nlinarith [norm_nonneg ε]
    have hPmem : ((conj ε, ε) : ℂ × ℂ) ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 :=
      ⟨mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact hεR.le), mem_closedBall_zero_iff.2 hεR.le⟩
    rw [s7g_l2 hμ hν hκ hg hgκ hharm hm' hC0 hCb hε1 hε2]
    congr 1
    have hV : (wU fun u => conj ε * m' u) = W (conj ε, ε) := by
      rw [wr_wU_eq, Complex.conj_conj, hW]
    rw [hV]
    have hint : Integrable (F (conj ε, ε)) ((volume.restrict S).prod (volume.restrict S)) := by
      rw [Measure.prod_restrict]
      refine ⟨?_, lt_of_le_of_lt (hM' _ hPmem) ENNReal.ofReal_lt_top⟩
      exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨hPmem, hx⟩)).aestronglyMeasurable hTm
    have hprod := integral_prod (F (conj ε, ε)) hint
    have e2 : Φ (conj ε, ε) = ∫ s in S, ∫ t in S, F (conj ε, ε) (s, t) := by
      rw [← hprod, Measure.prod_restrict, hΦ]
      rfl
    rw [e2, ← setIntegral_congr_set hnull]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only []
    rw [← setIntegral_congr_set hnull, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [hF, hAdef, hBdef]
  -- the derivative in the second slot at the origin
  have h00 : (0 : ℂ) ∈ closedBall (0 : ℂ) R0 := mem_closedBall_self hR0p.le
  have hDer := s7g_h_deriv (F := fun b x => F (0, b) x) hTm (c := 0) (R := R0) hR0p (hcont2 0 h00)
    (fun x hx => (hhol x hx).2 0 h00) (M := M) (fun b hb => hM' (0, b) ⟨h00, hb⟩)
  have hpt : ∀ s ∈ S, ∀ t ∈ S, deriv (fun b => F (0, b) (s, t)) 0 =
      conj (mμ s) * dzbar (fun e => mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
    intro s hs t ht
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ → ℂ, Ψ = fun P u =>
        mν u * (dz (W P) u * dz (W P) (conj s) / (W P u - W P (conj s)) ^ 2) ^ 2 := ⟨_, rfl⟩
    have hFΨ : ∀ b, F (0, b) (s, t) = conj (mμ s) * Ψ (0, b) t := by
      intro b
      rw [hF, hΨ]
      simp only []
      rw [hAconj s hs, hBconj t ht]
    obtain ⟨hh1, hh2⟩ := s71_b2_holo (μ := mν) hC0 hmB hms (hSU hs) hR0k hW hΨ (hSU ht)
    have hcΨ := s71_b2_cont (μ := mν) hC0 hmB hms (harmonicU_continuousOn hνh) (hSU hs) hR0k hW hΨ
    obtain ⟨Bd, hBd⟩ := ((isCompact_closedBall (0 : ℂ) R0).prod (isCompact_closedBall (0 : ℂ) R0)).exists_bound_of_continuousOn
      (hcΨ.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun P hP => (⟨hP, hSU ht⟩ : (P, t) ∈ (closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ upperHalf)))
    have k1 : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, DifferentiableAt ℂ (fun z => Ψ (z, p.2) t) p.1 :=
      fun p hp => (hh1 p.2 (ball_subset_closedBall hp.2)).differentiableAt (isOpen_ball.mem_nhds hp.1)
    have k2 : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, DifferentiableAt ℂ (fun w => Ψ (p.1, w) t) p.2 :=
      fun p hp => (hh2 p.1 (ball_subset_closedBall hp.1)).differentiableAt (isOpen_ball.mem_nhds hp.2)
    have kb : ∀ p ∈ ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0, ∃ ρ > 0, ∃ M' : ℝ, ∀ q ∈ ball p ρ, ‖Ψ q t‖ ≤ M' := by
      intro p hp
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hUo p hp
      exact ⟨ρ, hρ, Bd, fun q hq =>
        hBd q ⟨ball_subset_closedBall (hsub hq).1, ball_subset_closedBall (hsub hq).2⟩⟩
    have hfd := s7g_h_fderiv (Φ := fun P => Ψ P t) hUo k1 k2 kb (p := ((0 : ℂ), (0 : ℂ)))
      ⟨mem_ball_self hR0p, mem_ball_self hR0p⟩
    have hdiff : DifferentiableAt ℂ (fun P => Ψ P t) ((0 : ℂ), conj (0 : ℂ)) := by
      rw [map_zero]
      exact hfd.differentiableAt
    have hpar := p71_dzbar_partial hdiff
    rw [map_zero] at hpar
    have hev : (fun y => Ψ (y, conj y) t) =ᶠ[𝓝 (0 : ℂ)] fun e => mν t * kernelKbar (fun y => e * m' y) t s ^ 2 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / (C + 1) by positivity)] with e he
      have he' : ‖e‖ * C < 1 := by
        rw [mem_ball_zero_iff, lt_div_iff₀ (by positivity)] at he
        nlinarith [norm_nonneg e]
      exact s71_b2_diag hC0 hmB hW hΨ he' t
    rw [← p71_dzbar_congr hev, hpar]
    have hcongr : (fun b => F (0, b) (s, t)) = fun b => conj (mμ s) * Ψ (0, b) t := funext hFΨ
    rw [hcongr, deriv_const_mul _ ((hh2 0 h00).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR0p)))]
  have hderΦ : deriv (fun b => Φ (0, b)) 0 = ∫ s in upperHalf, conj (mμ s) *
      dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
    have e0 : (fun b => Φ (0, b)) = fun b => ∫ x in S ×ˢ S, F (0, b) x := by rw [hΦ]
    rw [e0, hDer.2]
    have hint : Integrable (fun x => deriv (fun b => F (0, b) x) 0) ((volume.restrict S).prod (volume.restrict S)) := by
      rw [Measure.prod_restrict]
      exact hDer.1
    have e1 : (∫ x in S ×ˢ S, deriv (fun b => F (0, b) x) 0) =
        ∫ x, deriv (fun b => F (0, b) x) 0 ∂((volume.restrict S).prod (volume.restrict S)) := by
      rw [Measure.prod_restrict]
      rfl
    rw [e1, integral_prod _ hint, ← setIntegral_congr_set hnull]
    refine setIntegral_congr_fun hSm fun s hs => ?_
    rw [setIntegral_congr_fun hSm (fun t ht => hpt s hs t ht), integral_const_mul, setIntegral_congr_set hnull,
      ← (s71_J_deriv hνh hharm (hSU hs)).2.2]
  exact ⟨R0, hR0p, Φ, hΦ2, ⟨r, hr0, hrR, hEq⟩, hderΦ⟩

/-- **R4a (line)**: `ε ↦ g_{μν̄}(εκ)` is `C²` near the origin. -/
theorem s7g_line_C2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 2 (fun ε : ℂ => gWP μ ν (ε • κ)) (ball 0 r) := by
  obtain ⟨g, hgs, hgκ⟩ := wr_harm_rep hκ
  have hg : ContinuousOn g unitDiscExterior := hgs.continuousOn
  obtain ⟨m', φ', hharm, hm'⟩ := p71_wm_harm hκ hg hgκ
  obtain ⟨mμ, φμ, hμh, hμf, -⟩ := s7g_l3_weight hμ
  obtain ⟨mν, φν, hνh, hνf, -⟩ := s7g_l3_weight hν
  obtain ⟨R0, hR0p, Φ, hΦ2, ⟨r, hr0, hrR, hEq⟩, -⟩ := s7g_l3_core hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf
  refine ⟨r, hr0, ?_⟩
  have hmap : ContDiff ℝ 2 (fun ε : ℂ => ((conj ε, ε) : ℂ × ℂ)) :=
    Complex.conjCLE.contDiff.prodMk contDiff_id
  have hGc : ContDiffOn ℝ 2 (fun ε : ℂ => (12 / π : ℂ) * Φ (conj ε, ε)) (ball 0 r) := by
    refine contDiffOn_const.mul ((hΦ2.restrict_scalars ℝ).comp hmap.contDiffOn fun ε hε => ?_)
    have h' : ‖ε‖ < R0 := lt_of_lt_of_le (mem_ball_zero_iff.1 hε) hrR
    exact ⟨mem_ball_zero_iff.2 (by rwa [Complex.norm_conj]), mem_ball_zero_iff.2 h'⟩
  exact hGc.congr fun ε hε => hEq ε hε

/-- **R4b**: `∂_ε g_{μν̄}(εκ)|₀ = \overline{(Q̇(ν)[κ], μ)}`. Route: `∂_ε (12/π) Φ(ε̄, ε)|₀ = (12/π) ∂_b Φ(0, 0)`
(`s7g_dz_partial`), the core's formula, `s71_Q_quot` (`ρ Q̇ = (12/π) ∂_ε̄ J`), and the Cayley transport of `Q̇`
(`p71_wm_Q`, `p71_wm_eps`, `p71_cov`). -/
theorem s7g_first_dz {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    dz (fun ε => gWP μ ν (ε • κ)) 0 = conj (l2Inner (Qdot (toLinf ν) κ) μ) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨g, hgs, hgκ⟩ := wr_harm_rep hκ
  have hg : ContinuousOn g unitDiscExterior := hgs.continuousOn
  obtain ⟨m', φ', hharm, hm'⟩ := p71_wm_harm hκ hg hgκ
  obtain ⟨mμ, φμ, hμh, hμf, -⟩ := s7g_l3_weight hμ
  obtain ⟨mν, φν, hνh, hνf, -⟩ := s7g_l3_weight hν
  obtain ⟨R0, hR0p, Φ, hΦ2, ⟨r, hr0, -, hEq⟩, hderΦ⟩ :=
    s7g_l3_core hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf
  have hev : (fun ε => gWP μ ν (ε • κ)) =ᶠ[𝓝 (0 : ℂ)] fun ε => (12 / π : ℂ) * Φ (conj ε, ε) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr0] with ε hε
    exact hEq ε hε
  have hdz : dz (fun ε => gWP μ ν (ε • κ)) 0 = dz (fun ε => (12 / π : ℂ) * Φ (conj ε, ε)) 0 := by
    simp only [dz, hev.fderiv_eq]
  have hΦd : DifferentiableAt ℂ Φ ((0 : ℂ), (0 : ℂ)) :=
    (hΦ2.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hR0p, mem_ball_self hR0p⟩)
  have hH : DifferentiableAt ℂ (fun P => (12 / π : ℂ) * Φ P) (conj (0 : ℂ), (0 : ℂ)) := by
    rw [map_zero]
    exact (differentiableAt_const _).mul hΦd
  have hslice : DifferentiableAt ℂ (fun b => Φ ((0 : ℂ), b)) 0 :=
    DifferentiableAt.comp (g := Φ) (0 : ℂ) hΦd ((differentiableAt_const _).prodMk differentiableAt_id)
  rw [hdz, s7g_dz_partial hH]
  simp only [map_zero]
  rw [deriv_const_mul _ hslice, hderΦ]
  -- transport to `𝔻*`
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  unfold l2Inner
  rw [← integral_conj, p71_cov, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hη hηI
  have hc : conj η + I ≠ 0 := s7g_l3_cne hηI
  have hz : cayley (conj η) ∈ unitDiscExterior := by
    have h1 : (conj η).im < 0 := by
      rw [Complex.conj_im]
      exact neg_neg_of_pos hη
    exact p71_cay_ext h1 hc
  have hci : cayleyInv (cayley (conj η)) = conj η := p71_cinv_cay hc
  have hy : conj (cayleyInv (cayley (conj η))) = η := by rw [hci, Complex.conj_conj]
  have hd := (p71_prop_7_1U hνh hharm hη).1
  have hQ := p71_wm_Q (hCc ν hν).1 hκ (wp_harmonic_continuousOn hν) (wp_harmonic_toLinf_ae hν) hg hgκ hνf hm' hz
  rw [hy] at hQ
  have hE := (p71_wm_eps (G := fun e => QfunU mν (fun u => e * m' u) η) hQ hd).2
  rw [hci] at hE
  have hqq := (s71_Q_quot hνh hharm hη).2
  have hrho : rhoVar m' 0 η = (rhoU η : ℂ) := by rw [s71_rho0, rhoU_complex]
  have hr0' : (rhoU η : ℂ) ≠ 0 := by
    rw [rhoU_complex]
    have : η - conj η ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      linarith [show 0 < η.im from hη]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ this)
  rw [hrho] at hqq
  have hJ : (12 / π : ℂ) * dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t η ^ 2) 0 =
      (rhoU η : ℂ) * dzbar (fun e => QfunU mν (fun u => e * m' u) η) 0 := by
    rw [hqq]
    field_simp
  have hA := s7g_l3_Aconj μ hη hηI (hμf η hη hηI)
  have hiso := (p71r_iso hη hη hηI hηI).2
  show (12 / π : ℂ) * (conj (mμ η) *
      dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t η ^ 2) 0) =
    ((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
      conj (Qdot (toLinf ν) κ (cayley (conj η)) * conj (μ (cayley (conj η))) * (rho (cayley (conj η)) : ℂ))
  have hQd : Qdot (toLinf ν) κ (cayley (conj η)) = 2 * I / (conj η + I) ^ 2 / conj (2 * I / (conj η + I) ^ 2) *
      conj (dzbar (fun e => QfunU mν (fun u => e * m' u) η) 0) := hE
  rw [hQd]
  rw [show (12 / π : ℂ) * (conj (mμ η) *
      dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t η ^ 2) 0) =
      conj (mμ η) * ((12 / π : ℂ) *
        dzbar (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t η ^ 2) 0) by ring, hJ, ← hA,
    ← hiso]
  simp only [map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  ring


/-- FROZEN stub of `S7Thm74_INTERFACE` (56ff35a2), assembled from R4a and R4b. -/
theorem s7g_first_variation {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    DifferentiableAt ℝ (fun ε : ℂ => gWP μ ν (ε • κ)) 0 ∧
      dz (fun ε => gWP μ ν (ε • κ)) 0 = conj (l2Inner (Qdot (toLinf ν) κ) μ) := by
  obtain ⟨r, hr, hC⟩ := s7g_line_C2 hμ hν hκ
  have hd : DifferentiableAt ℝ (fun ε : ℂ => gWP μ ν (ε • κ)) 0 :=
    (hC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  exact ⟨hd, s7g_first_dz hμ hν hκ⟩

end TakhtajanTeo
