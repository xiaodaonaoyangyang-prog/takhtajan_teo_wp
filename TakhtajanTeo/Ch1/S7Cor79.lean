import TakhtajanTeo.Ch1.S7SecondVariation

/-!
# Program G: the `ℂ⁴` extension and `cor_7_9` (下属1)

Proof of the sub-interface `C79_SUBINTERFACE` (ed6c4494): stubs H4, CORE4, POL, LIN, SES, SYM are
proved below, `s7g_c79_C2` and `s7g_cor_7_9` are as in the interface.

`riemannR μ ν κ l = -∂_{e₁}∂̄_{e₂} F(0)`, `F(e₁, e₂) = g_{μν̄}(e₁ κ + e₂ l)`. Route (polarization of `thm_7_7`):
* (C4) `F` is real `C²` near `0` in `ℂ²`: `F(e) = Φ(ē, e)` for a `Φ` on a polydisc in `ℂ⁴`, separately
  holomorphic in each coordinate and bounded (CORE4, the 4-parameter `W_Q`-family of `s7g_L1` in the line-2
  representation `s7g_l2`; each one-coordinate slice is a 2-parameter family `t A + 1·B`, so the existing
  `wr_*`/`e64_*` two-parameter tools apply), then a 4-variable Hartogs-lite (H4);
* (POL) for `C²` `F`: `4 ∂_{e₁}∂̄_{e₂}F(0) = Σ_{c ∈ {1, i, -1, -i}} c · ∂∂̄[ε ↦ F(ε, cε)](0)`;
* (LIN) `F(ε, cε) = g(ε (κ + c l))`, so each term is `thm_7_7` for `κ + c l`;
* (SES) the right side of `thm_7_7` for `κ + c l` is `Q(κ) + c̄ B + c B' + |c|² Q(l)`, with
  `B = (μ l̄, G(ν κ̄)) + (μ ν̄, G(κ̄ l))`; so `∂_{e₁}∂̄_{e₂}F(0) = B`;
* (SYM) `(μ ν̄, G(κ̄ l)) = (κ l̄, G(μ̄ ν))` (self-adjointness of `G`, `resolvent_bilinear_swap`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-! ### H4: Hartogs-lite in four variables

Route: the two-variable argument of `s7g_h_fderiv`, with the second variable in a normed space `E`
(`s7g_c79_hfd`), applied three times (`s7g_c79_hjoint`) gives joint differentiability; the class is stable under
the coordinate partial derivatives (`s7g_c79_hd1` + coordinate transpositions), and `Cⁿ` follows by induction. -/

/-- Local bounds can be taken on balls inside the open set (`ℂ × E` version of `s7g_h_loc`). -/
theorem s7g_c79_hlc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : ℂ × E → ℂ} {U : Set (ℂ × E)}
    (hU : IsOpen U) (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × E} (hp : p ∈ U) :
    ∃ ρ > 0, ∃ M : ℝ, 0 ≤ M ∧ ball p ρ ⊆ U ∧ ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M := by
  obtain ⟨ρ1, hρ1, M, hM⟩ := hb p hp
  obtain ⟨ρ2, hρ2, hsub⟩ := Metric.isOpen_iff.1 hU p hp
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, M, (norm_nonneg _).trans (hM p (mem_ball_self hρ1)),
    (ball_subset_ball (min_le_right _ _)).trans hsub, fun q hq => hM q (ball_subset_ball (min_le_left _ _) hq)⟩

/-- The Cauchy–Taylor estimate in the first variable (`ℂ × E` version of `s7g_h_slice`). -/
theorem s7g_c79_hsl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : ℂ × E → ℂ} {U : Set (ℂ × E)}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    {p : ℂ × E} {ρ M : ℝ} (hρ : 0 < ρ) (hpU : ball p ρ ⊆ U) (hM : ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M)
    {q : ℂ × E} (hq : dist q p < ρ / 2) :
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
  obtain ⟨-, -, hc⟩ := QCV.qcv_taylor2 (half_pos hρ) hd hM'
  have hder : deriv φ 0 = deriv (fun z => Φ (z, q.2)) q.1 := by
    rw [hφ, deriv_comp_const_add (fun z => Φ (z, q.2)) q.1 0, add_zero]
  have hφ0 : φ 0 = Φ q := by
    simp only [hφ, add_zero]
  intro t ht
  have h := hc t (mem_closedBall_zero_iff.2 ht)
  rwa [hφ0, hder, smul_eq_mul] at h

/-- The first partial derivative is continuous in the second variable (uniform limit of difference quotients). -/
theorem s7g_c79_hkc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : ℂ × E → ℂ} {U : Set (ℂ × E)}
    (hU : IsOpen U) (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × E} (hp : p ∈ U) :
    ContinuousAt (fun w => deriv (fun z => Φ (z, w)) p.1) p.2 := by
  obtain ⟨ρ, hρ, M, hM0, hpU, hM⟩ := s7g_c79_hlc hU hb hp
  set R : ℝ := ρ / 2 with hR
  have hR0 : 0 < R := half_pos hρ
  set S : Set E := ball p.2 R with hS
  have hqS : ∀ w ∈ S, dist ((p.1, w) : ℂ × E) p < R := by
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
    have hc' := s7g_c79_hsl h1 hρ hpU hM (hqS w hw) h (le_of_lt (by rw [hR] at hh; exact hh.2))
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
  have hF : ∀ᶠ h in 𝓝[≠] (0 : ℂ), ContinuousOn (fun w => (Φ (p.1 + h, w) - Φ (p.1, w)) / h) S := by
    filter_upwards [hev] with h hh
    intro w hw
    have hq := hqS w hw
    have hin1 : ((p.1 + h, w) : ℂ × E) ∈ U := by
      apply hpU
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, add_sub_cancel_left]
      rw [Prod.dist_eq, max_lt_iff] at hq
      constructor <;> linarith [hh.2, hq.2]
    have hin0 : ((p.1, w) : ℂ × E) ∈ U := by
      apply hpU
      rw [mem_ball]
      linarith
    exact (((h2 (p.1 + h, w) hin1).continuousAt.sub (h2 (p.1, w) hin0).continuousAt).div_const h).continuousWithinAt
  exact (hT.continuousOn hF.frequently).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR0))

/-- **Joint differentiability** on `ℂ × E` from holomorphy in `z`, differentiability in `w ∈ E` and local
bounds (the argument of `s7g_h_fderiv`). -/
theorem s7g_c79_hfd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : ℂ × E → ℂ} {U : Set (ℂ × E)}
    (hU : IsOpen U) (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (z, p.2)) p.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun w => Φ (p.1, w)) p.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : ℂ × E} (hp : p ∈ U) :
    DifferentiableAt ℂ Φ p := by
  obtain ⟨ρ, hρ, M, hM0, hpU, hM⟩ := s7g_c79_hlc hU hb hp
  set R : ℝ := ρ / 2 with hR
  have hR0 : 0 < R := half_pos hρ
  set k : E → ℂ := fun w => deriv (fun z => Φ (z, w)) p.1 with hk
  set D2 : E →L[ℂ] ℂ := fderiv ℂ (fun w => Φ (p.1, w)) p.2 with hD2
  have hkc : ContinuousAt k p.2 := s7g_c79_hkc hU h1 h2 hb hp
  have hs : Tendsto (fun h : ℂ × E => h.2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_snd.tendsto (0 : ℂ × E))
  have hkt : Tendsto (fun h : ℂ × E => k (p.2 + h.2)) (𝓝 0) (𝓝 (k p.2)) :=
    hkc.tendsto.comp ((continuous_const.add continuous_snd).tendsto' 0 p.2 (by simp))
  have hC := hasFDerivAt_iff_isLittleO_nhds_zero.1 (h2 p hp).hasFDerivAt
  refine ⟨deriv (fun z => Φ (z, p.2)) p.1 • ContinuousLinearMap.fst ℂ ℂ E + D2.comp (ContinuousLinearMap.snd ℂ ℂ E), ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hc3 : 0 < c / 3 := by positivity
  have hδ : 0 < c * R ^ 2 / (12 * (M + 1)) := by positivity
  have evA : ∀ᶠ h in 𝓝 (0 : ℂ × E), ‖h‖ < min R (c * R ^ 2 / (12 * (M + 1))) := by
    filter_upwards [ball_mem_nhds (0 : ℂ × E) (lt_min hR0 hδ)] with h hh
    exact mem_ball_zero_iff.1 hh
  have evB : ∀ᶠ h in 𝓝 (0 : ℂ × E), dist (k (p.2 + h.2)) (k p.2) < c / 3 :=
    Metric.tendsto_nhds.1 hkt _ hc3
  have evC : ∀ᶠ h in 𝓝 (0 : ℂ × E),
      ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - D2 h.2‖ ≤ c / 3 * ‖h.2‖ :=
    hs.eventually (hC.def hc3)
  filter_upwards [evA, evB, evC] with h hA hB hCh
  have hA1 := lt_of_lt_of_le hA (min_le_left _ _)
  have hA2 := lt_of_lt_of_le hA (min_le_right _ _)
  have h1n : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have h2n : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have hqd : dist ((p.1, p.2 + h.2) : ℂ × E) p < ρ / 2 := by
    rw [Prod.dist_eq, max_lt_iff, dist_self, dist_eq_norm, add_sub_cancel_left]
    exact ⟨hR0, by linarith⟩
  have hTA := s7g_c79_hsl h1 hρ hpU hM hqd h.1 (by linarith)
  simp only at hTA
  have hph : p + h = (p.1 + h.1, p.2 + h.2) := rfl
  have hpp : Φ p = Φ (p.1, p.2) := rfl
  have hlin : (deriv (fun z => Φ (z, p.2)) p.1 • ContinuousLinearMap.fst ℂ ℂ E +
      D2.comp (ContinuousLinearMap.snd ℂ ℂ E)) h = k p.2 * h.1 + D2 h.2 := by
    simp [hk]
  rw [hlin, hph, hpp]
  have hsplit : Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2) - (k p.2 * h.1 + D2 h.2) =
      (Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2 + h.2) - h.1 * k (p.2 + h.2)) +
        h.1 * (k (p.2 + h.2) - k p.2) + (Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - D2 h.2) := by
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
  have bC : ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - D2 h.2‖ ≤ c / 3 * ‖h‖ :=
    hCh.trans (by gcongr)
  calc _ ≤ ‖Φ (p.1 + h.1, p.2 + h.2) - Φ (p.1, p.2 + h.2) - h.1 * k (p.2 + h.2)‖ +
        ‖h.1 * (k (p.2 + h.2) - k p.2)‖ + ‖Φ (p.1, p.2 + h.2) - Φ (p.1, p.2) - D2 h.2‖ := norm_add₃_le
    _ ≤ c / 3 * ‖h‖ + c / 3 * ‖h‖ + c / 3 * ‖h‖ := by gcongr
    _ = c * ‖h‖ := by ring

/-- Local bounds pass to a `1`-Lipschitz reparametrisation. -/
theorem s7g_c79_hbt {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {Φ : X → ℂ} {U : Set X}
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {ι : Y → X}
    (hι : ∀ x y, dist (ι x) (ι y) ≤ dist x y) :
    ∀ x ∈ ι ⁻¹' U, ∃ ρ > 0, ∃ M : ℝ, ∀ y ∈ ball x ρ, ‖Φ (ι y)‖ ≤ M := by
  intro x hx
  obtain ⟨ρ, hρ, M, hM⟩ := hb _ hx
  exact ⟨ρ, hρ, M, fun y hy => hM _ (lt_of_le_of_lt (hι y x) hy)⟩

/-- Joint complex differentiability of a separately holomorphic, locally bounded function of four variables. -/
theorem s7g_c79_hjoint {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hU : IsOpen U) {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) {p : (ℂ × ℂ) × (ℂ × ℂ)} (hp : p ∈ U) :
    DifferentiableAt ℂ Φ p := by
  have J2 : ∀ q ∈ U, DifferentiableAt ℂ (fun w : ℂ × ℂ => Φ (q.1, w)) q.2 := by
    intro q hq
    have hU2 : IsOpen {w : ℂ × ℂ | (q.1, w) ∈ U} := hU.preimage (continuous_const.prodMk continuous_id)
    exact (s7g_h_fderiv (Φ := fun w : ℂ × ℂ => Φ (q.1, w)) hU2 (fun w hw => h3 (q.1, w) hw)
      (fun w hw => h4 (q.1, w) hw) (s7g_c79_hbt hb (ι := fun w : ℂ × ℂ => (q.1, w)) fun x y => by
        rw [Prod.dist_eq, dist_self]
        exact max_le dist_nonneg le_rfl) hq).differentiableAt
  have J3 : ∀ q ∈ U, DifferentiableAt ℂ (fun x : ℂ × (ℂ × ℂ) => Φ ((q.1.1, x.1), x.2)) (q.1.2, q.2) := by
    intro q hq
    have hU3 : IsOpen {x : ℂ × (ℂ × ℂ) | ((q.1.1, x.1), x.2) ∈ U} := hU.preimage (by fun_prop)
    exact s7g_c79_hfd (Φ := fun x : ℂ × (ℂ × ℂ) => Φ ((q.1.1, x.1), x.2)) hU3 (fun x hx => h2 _ hx)
      (fun x hx => J2 _ hx) (s7g_c79_hbt hb (ι := fun x : ℂ × (ℂ × ℂ) => ((q.1.1, x.1), x.2)) fun x y => by
        simp only [Prod.dist_eq, dist_self]
        exact max_le_max (max_le dist_nonneg le_rfl) le_rfl) hq
  have hU4 : IsOpen {x : ℂ × (ℂ × (ℂ × ℂ)) | ((x.1, x.2.1), x.2.2) ∈ U} := hU.preimage (by fun_prop)
  have H := s7g_c79_hfd (Φ := fun x : ℂ × (ℂ × (ℂ × ℂ)) => Φ ((x.1, x.2.1), x.2.2)) hU4 (fun x hx => h1 _ hx)
    (fun x hx => J3 _ hx) (s7g_c79_hbt hb (ι := fun x : ℂ × (ℂ × (ℂ × ℂ)) => ((x.1, x.2.1), x.2.2)) fun x y => by
      simp only [Prod.dist_eq]
      exact (max_assoc _ _ _).le) (p := (p.1.1, (p.1.2, p.2))) hp
  have hg : DifferentiableAt ℂ (fun q : (ℂ × ℂ) × (ℂ × ℂ) => (q.1.1, (q.1.2, q.2))) p := by fun_prop
  have hc := DifferentiableAt.comp (g := fun x : ℂ × (ℂ × (ℂ × ℂ)) => Φ ((x.1, x.2.1), x.2.2))
    (f := fun q : (ℂ × ℂ) × (ℂ × ℂ) => (q.1.1, (q.1.2, q.2))) p H hg
  exact hc

/-- The first partial derivative of a separately holomorphic, locally bounded function of four variables is again
separately holomorphic and locally bounded. -/
theorem s7g_c79_hd1 {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hU : IsOpen U) {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M)
    {D : (ℂ × ℂ) × (ℂ × ℂ) → ℂ} (hD : D = fun q => deriv (fun z => Φ ((z, q.1.2), q.2)) q.1.1) :
    (∀ p ∈ U, DifferentiableAt ℂ (fun z => D ((z, p.1.2), p.2)) p.1.1) ∧
      (∀ p ∈ U, DifferentiableAt ℂ (fun z => D ((p.1.1, z), p.2)) p.1.2) ∧
      (∀ p ∈ U, DifferentiableAt ℂ (fun z => D (p.1, (z, p.2.2))) p.2.1) ∧
      (∀ p ∈ U, DifferentiableAt ℂ (fun z => D (p.1, (p.2.1, z))) p.2.2) ∧
      ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖D q‖ ≤ M := by
  subst hD
  have lipA : ∀ c : ℂ × ℂ, ∀ x y : ℂ × ℂ,
      dist (((x.1, x.2), c) : (ℂ × ℂ) × (ℂ × ℂ)) ((y.1, y.2), c) ≤ dist x y := by
    intro c x y
    simp only [Prod.dist_eq, dist_self]
    exact max_le le_rfl (dist_nonneg.trans (le_max_left _ _))
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have hU' : IsOpen {x : ℂ × ℂ | ((x.1, x.2), p.2) ∈ U} := hU.preimage (by fun_prop)
    exact s7g_h_dz (Φ := fun x : ℂ × ℂ => Φ ((x.1, x.2), p.2)) hU' (fun x hx => h1 _ hx) (p := (p.1.1, p.1.2)) hp
  · have hU' : IsOpen {x : ℂ × ℂ | ((x.1, x.2), p.2) ∈ U} := hU.preimage (by fun_prop)
    exact s7g_h_dw (Φ := fun x : ℂ × ℂ => Φ ((x.1, x.2), p.2)) hU' (fun x hx => h1 _ hx) (fun x hx => h2 _ hx)
      (s7g_c79_hbt hb (ι := fun x : ℂ × ℂ => ((x.1, x.2), p.2)) (lipA p.2)) (p := (p.1.1, p.1.2)) hp
  · have hU' : IsOpen {x : ℂ × ℂ | ((x.1, p.1.2), (x.2, p.2.2)) ∈ U} := hU.preimage (by fun_prop)
    exact s7g_h_dw (Φ := fun x : ℂ × ℂ => Φ ((x.1, p.1.2), (x.2, p.2.2))) hU' (fun x hx => h1 _ hx)
      (fun x hx => h3 _ hx) (s7g_c79_hbt hb (ι := fun x : ℂ × ℂ => ((x.1, p.1.2), (x.2, p.2.2))) fun x y => by
        simp only [Prod.dist_eq, dist_self]
        exact max_le_max (max_le le_rfl dist_nonneg) (max_le le_rfl dist_nonneg)) (p := (p.1.1, p.2.1)) hp
  · have hU' : IsOpen {x : ℂ × ℂ | ((x.1, p.1.2), (p.2.1, x.2)) ∈ U} := hU.preimage (by fun_prop)
    exact s7g_h_dw (Φ := fun x : ℂ × ℂ => Φ ((x.1, p.1.2), (p.2.1, x.2))) hU' (fun x hx => h1 _ hx)
      (fun x hx => h4 _ hx) (s7g_c79_hbt hb (ι := fun x : ℂ × ℂ => ((x.1, p.1.2), (p.2.1, x.2))) fun x y => by
        simp only [Prod.dist_eq, dist_self]
        exact max_le_max (max_le le_rfl dist_nonneg) (max_le dist_nonneg le_rfl)) (p := (p.1.1, p.2.2)) hp
  · obtain ⟨ρ1, hρ1, M, hM⟩ := hb p hp
    obtain ⟨ρ2, hρ2, hsub⟩ := Metric.isOpen_iff.1 hU p hp
    set ρ := min ρ1 ρ2 with hρdef
    have hρ : 0 < ρ := lt_min hρ1 hρ2
    have hpU : ball p ρ ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hsub
    have hMb : ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M := fun q hq => hM q (ball_subset_ball (min_le_left _ _) hq)
    refine ⟨ρ / 2, half_pos hρ, 2 * M / (ρ / 2 / 2), fun q hq => ?_⟩
    have hqp : dist q p < ρ / 2 := hq
    have hin : ∀ x ∈ ball ((q.1.1, q.1.2) : ℂ × ℂ) (ρ / 2), (((x.1, x.2), q.2) : (ℂ × ℂ) × (ℂ × ℂ)) ∈ ball p ρ := by
      intro x hx
      have hd : dist (((x.1, x.2), q.2) : (ℂ × ℂ) × (ℂ × ℂ)) q ≤ dist x (q.1.1, q.1.2) := lipA q.2 x (q.1.1, q.1.2)
      have hx' : dist x (q.1.1, q.1.2) < ρ / 2 := hx
      rw [mem_ball]
      linarith [dist_triangle (((x.1, x.2), q.2) : (ℂ × ℂ) × (ℂ × ℂ)) q p]
    have hU' : ball ((q.1.1, q.1.2) : ℂ × ℂ) (ρ / 2) ⊆ {x : ℂ × ℂ | ((x.1, x.2), q.2) ∈ U} :=
      fun x hx => hpU (hin x hx)
    have h1' : ∀ x ∈ {x : ℂ × ℂ | ((x.1, x.2), q.2) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((z, x.2), q.2)) x.1 := fun x hx => h1 _ hx
    exact (s7g_h_slice (Φ := fun x : ℂ × ℂ => Φ ((x.1, x.2), q.2)) h1' (half_pos hρ) hU'
      (fun x hx => hMb _ (hin x hx)) (q := (q.1.1, q.1.2)) (by rw [dist_self]; positivity)).1

/-- Separate holomorphy and local bounds are preserved by swapping the coordinates `1 ↔ 2`. -/
theorem s7g_c79_htr12 {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.1.2, z), p.2)) p.1.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((z, p.1.1), p.2)) p.1.2) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.1.2, p.1.1), (z, p.2.2))) p.2.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.1.2, p.1.1), (p.2.1, z))) p.2.2) ∧
      ∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U},
        ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ ((q.1.2, q.1.1), q.2)‖ ≤ M := by
  refine ⟨fun p hp => h2 _ hp, fun p hp => h1 _ hp, fun p hp => h3 _ hp, fun p hp => h4 _ hp,
    s7g_c79_hbt hb (ι := fun q : (ℂ × ℂ) × (ℂ × ℂ) => ((q.1.2, q.1.1), q.2)) fun x y => ?_⟩
  simp only [Prod.dist_eq]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> simp only [le_max_iff, le_refl, true_or, or_true]

/-- Separate holomorphy and local bounds are preserved by swapping the coordinates `1 ↔ 3`. -/
theorem s7g_c79_htr13 {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.1, p.1.2), (z, p.2.2))) p.1.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.1, z), (p.1.1, p.2.2))) p.1.2) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), (p.1.1, p.2.2))) p.2.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.1, p.1.2), (p.1.1, z))) p.2.2) ∧
      ∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U},
        ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ ((q.2.1, q.1.2), (q.1.1, q.2.2))‖ ≤ M := by
  refine ⟨fun p hp => h3 _ hp, fun p hp => h2 _ hp, fun p hp => h1 _ hp, fun p hp => h4 _ hp,
    s7g_c79_hbt hb (ι := fun q : (ℂ × ℂ) × (ℂ × ℂ) => ((q.2.1, q.1.2), (q.1.1, q.2.2))) fun x y => ?_⟩
  simp only [Prod.dist_eq]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> simp only [le_max_iff, le_refl, true_or, or_true]

/-- Separate holomorphy and local bounds are preserved by swapping the coordinates `1 ↔ 4`. -/
theorem s7g_c79_htr14 {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) :
    (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.2, p.1.2), (p.2.1, z))) p.1.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.2, z), (p.2.1, p.1.1))) p.1.2) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((p.2.2, p.1.2), (z, p.1.1))) p.2.1) ∧
      (∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U},
        DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), (p.2.1, p.1.1))) p.2.2) ∧
      ∀ p ∈ {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U},
        ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ ((q.2.2, q.1.2), (q.2.1, q.1.1))‖ ≤ M := by
  refine ⟨fun p hp => h4 _ hp, fun p hp => h2 _ hp, fun p hp => h3 _ hp, fun p hp => h1 _ hp,
    s7g_c79_hbt hb (ι := fun q : (ℂ × ℂ) × (ℂ × ℂ) => ((q.2.2, q.1.2), (q.2.1, q.1.1))) fun x y => ?_⟩
  simp only [Prod.dist_eq]
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> simp only [le_max_iff, le_refl, true_or, or_true]

/-- The derivative of a jointly differentiable function of four variables is the sum of its partials. -/
theorem s7g_c79_hfderiv {Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ} {p : (ℂ × ℂ) × (ℂ × ℂ)} (hΦ : DifferentiableAt ℂ Φ p) :
    fderiv ℂ Φ p =
      deriv (fun z => Φ ((z, p.1.2), p.2)) p.1.1 •
          (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)) +
        deriv (fun z => Φ ((p.1.1, z), p.2)) p.1.2 •
          (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)) +
        deriv (fun z => Φ (p.1, (z, p.2.2))) p.2.1 •
          (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)) +
        deriv (fun z => Φ (p.1, (p.2.1, z))) p.2.2 •
          (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)) := by
  have hF := hΦ.hasFDerivAt
  have e1 : deriv (fun z => Φ ((z, p.1.2), p.2)) p.1.1 = fderiv ℂ Φ p (((1 : ℂ), (0 : ℂ)), (0 : ℂ × ℂ)) :=
    (hF.comp_hasDerivAt p.1.1 (((hasDerivAt_id p.1.1).prodMk (hasDerivAt_const p.1.1 p.1.2)).prodMk
      (hasDerivAt_const p.1.1 p.2))).deriv
  have e2 : deriv (fun z => Φ ((p.1.1, z), p.2)) p.1.2 = fderiv ℂ Φ p (((0 : ℂ), (1 : ℂ)), (0 : ℂ × ℂ)) :=
    (hF.comp_hasDerivAt p.1.2 (((hasDerivAt_const p.1.2 p.1.1).prodMk (hasDerivAt_id p.1.2)).prodMk
      (hasDerivAt_const p.1.2 p.2))).deriv
  have e3 : deriv (fun z => Φ (p.1, (z, p.2.2))) p.2.1 = fderiv ℂ Φ p ((0 : ℂ × ℂ), ((1 : ℂ), (0 : ℂ))) :=
    (hF.comp_hasDerivAt p.2.1 ((hasDerivAt_const p.2.1 p.1).prodMk ((hasDerivAt_id p.2.1).prodMk
      (hasDerivAt_const p.2.1 p.2.2)))).deriv
  have e4 : deriv (fun z => Φ (p.1, (p.2.1, z))) p.2.2 = fderiv ℂ Φ p ((0 : ℂ × ℂ), ((0 : ℂ), (1 : ℂ))) :=
    (hF.comp_hasDerivAt p.2.2 ((hasDerivAt_const p.2.2 p.1).prodMk ((hasDerivAt_const p.2.2 p.2.1).prodMk
      (hasDerivAt_id p.2.2)))).deriv
  rw [e1, e2, e3, e4]
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1.1 • ((((1 : ℂ), (0 : ℂ)), (0 : ℂ × ℂ)) : (ℂ × ℂ) × (ℂ × ℂ)) +
      v.1.2 • ((((0 : ℂ), (1 : ℂ)), (0 : ℂ × ℂ)) : (ℂ × ℂ) × (ℂ × ℂ)) +
      v.2.1 • (((0 : ℂ × ℂ), ((1 : ℂ), (0 : ℂ))) : (ℂ × ℂ) × (ℂ × ℂ)) +
      v.2.2 • (((0 : ℂ × ℂ), ((0 : ℂ), (1 : ℂ))) : (ℂ × ℂ) × (ℂ × ℂ)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  ring

/-- STUB H4. Hartogs-lite in four variables: separately holomorphic and locally bounded implies `Cⁿ` over `ℂ`. -/
theorem s7g_c79_hartogs {U : Set ((ℂ × ℂ) × (ℂ × ℂ))} (hU : IsOpen U) (n : ℕ) (Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ)
    (h1 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1)
    (h2 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2)
    (h3 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1)
    (h4 : ∀ p ∈ U, DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2)
    (hb : ∀ p ∈ U, ∃ ρ > 0, ∃ M : ℝ, ∀ q ∈ ball p ρ, ‖Φ q‖ ≤ M) : ContDiffOn ℂ n Φ U := by
  revert Φ
  induction n with
  | zero =>
    intro Φ h1 h2 h3 h4 hb
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (s7g_c79_hjoint hU h1 h2 h3 h4 hb hp).continuousAt.continuousWithinAt
  | succ n ih =>
    intro Φ h1 h2 h3 h4 hb
    -- the four partial derivatives are again in the class
    obtain ⟨a1, a2, a3, a4, ab⟩ := s7g_c79_hd1 hU h1 h2 h3 h4 hb rfl
    have hD1 : ContDiffOn ℂ n (fun q : (ℂ × ℂ) × (ℂ × ℂ) => deriv (fun z => Φ ((z, q.1.2), q.2)) q.1.1) U :=
      ih _ a1 a2 a3 a4 ab
    have hU12 : IsOpen {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.1.2, q.1.1), q.2) ∈ U} := hU.preimage (by fun_prop)
    obtain ⟨t1, t2, t3, t4, tb⟩ := s7g_c79_htr12 h1 h2 h3 h4 hb
    obtain ⟨c1, c2, c3, c4, cb⟩ := s7g_c79_hd1 hU12 t1 t2 t3 t4 tb rfl
    obtain ⟨d1, d2, d3, d4, db⟩ := s7g_c79_htr12 c1 c2 c3 c4 cb
    have hD2 : ContDiffOn ℂ n (fun q : (ℂ × ℂ) × (ℂ × ℂ) => deriv (fun z => Φ ((q.1.1, z), q.2)) q.1.2) U :=
      ih _ (fun p hp => d1 p hp) (fun p hp => d2 p hp) (fun p hp => d3 p hp) (fun p hp => d4 p hp)
        (fun p hp => db p hp)
    have hU13 : IsOpen {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.1, q.1.2), (q.1.1, q.2.2)) ∈ U} := hU.preimage (by fun_prop)
    obtain ⟨t1, t2, t3, t4, tb⟩ := s7g_c79_htr13 h1 h2 h3 h4 hb
    obtain ⟨c1, c2, c3, c4, cb⟩ := s7g_c79_hd1 hU13 t1 t2 t3 t4 tb rfl
    obtain ⟨d1, d2, d3, d4, db⟩ := s7g_c79_htr13 c1 c2 c3 c4 cb
    have hD3 : ContDiffOn ℂ n (fun q : (ℂ × ℂ) × (ℂ × ℂ) => deriv (fun z => Φ (q.1, (z, q.2.2))) q.2.1) U :=
      ih _ (fun p hp => d1 p hp) (fun p hp => d2 p hp) (fun p hp => d3 p hp) (fun p hp => d4 p hp)
        (fun p hp => db p hp)
    have hU14 : IsOpen {q : (ℂ × ℂ) × (ℂ × ℂ) | ((q.2.2, q.1.2), (q.2.1, q.1.1)) ∈ U} := hU.preimage (by fun_prop)
    obtain ⟨t1, t2, t3, t4, tb⟩ := s7g_c79_htr14 h1 h2 h3 h4 hb
    obtain ⟨c1, c2, c3, c4, cb⟩ := s7g_c79_hd1 hU14 t1 t2 t3 t4 tb rfl
    obtain ⟨d1, d2, d3, d4, db⟩ := s7g_c79_htr14 c1 c2 c3 c4 cb
    have hD4 : ContDiffOn ℂ n (fun q : (ℂ × ℂ) × (ℂ × ℂ) => deriv (fun z => Φ (q.1, (q.2.1, z))) q.2.2) U :=
      ih _ (fun p hp => d1 p hp) (fun p hp => d2 p hp) (fun p hp => d3 p hp) (fun p hp => d4 p hp)
        (fun p hp => db p hp)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (s7g_c79_hjoint hU h1 h2 h3 h4 hb hp).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine ((((hD1.smul (contDiffOn_const (c := (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
        (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))))).add
      (hD2.smul (contDiffOn_const (c := (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)))))).add
      (hD3.smul (contDiffOn_const (c := (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)))))).add
      (hD4.smul (contDiffOn_const (c := (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
        (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)))))).congr fun p hp => ?_
    exact s7g_c79_hfderiv (s7g_c79_hjoint hU h1 h2 h3 h4 hb hp)

/-! ### CORE4: the 4-parameter line-2 representation -/

/-- The two-parameter family `P ↦ W_P = w[P₁ m₁ + P₂ m₂]` on an open parameter set `V` where the coefficient stays
`< 1`: joint continuity of `W_P(y)` and `∂W_P(y)` off `ℝ`, injectivity, and holomorphy in `P₁` of both. -/
theorem s7g_c79_slice {m₁ m₂ : ℂ → ℂ} {k₁ k₂ : ℝ} (hm₁ : IsBeltramiCoeff m₁ univ k₁)
    (hm₂ : IsBeltramiCoeff m₂ univ k₂) (hs₁ : ContDiffOn ℝ (⊤ : ℕ∞) m₁ {u : ℂ | u.im ≠ 0})
    (hs₂ : ContDiffOn ℝ (⊤ : ℕ∞) m₂ {u : ℂ | u.im ≠ 0}) {V : Set (ℂ × ℂ)} (hV : IsOpen V)
    (hVk : ∀ P ∈ V, ∃ k < 1, IsBeltramiCoeff (fun u => P.1 * m₁ u + P.2 * m₂ u) univ k) :
    ContinuousOn (fun q : (ℂ × ℂ) × ℂ => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
        (V ×ˢ {u : ℂ | u.im ≠ 0}) ∧
      ContinuousOn (fun q : (ℂ × ℂ) × ℂ => dz (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2)
        (V ×ˢ {u : ℂ | u.im ≠ 0}) ∧
      (∀ P ∈ V, Function.Injective (normalizedSolution fun u => P.1 * m₁ u + P.2 * m₂ u)) ∧
      ∀ P ∈ V, ∀ y : ℂ, y.im ≠ 0 →
        DifferentiableAt ℂ (fun a => normalizedSolution (fun u => a * m₁ u + P.2 * m₂ u) y) P.1 ∧
        DifferentiableAt ℂ (fun a => dz (normalizedSolution fun u => a * m₁ u + P.2 * m₂ u) y) P.1 := by
  have hΩ : IsOpen {u : ℂ | u.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hC := wr_local_joint_contDiff hm₁ hm₂ hΩ hs₁ hs₂ hV hVk
  have hO := hV.prod hΩ
  have hhol : ∀ y : ℂ, ∀ P ∈ V, DifferentiableAt ℂ
      (fun Q : ℂ × ℂ => normalizedSolution (fun u => Q.1 * m₁ u + Q.2 * m₂ u) y) P := by
    intro y P hP
    obtain ⟨k', hk', hP'⟩ := hVk P hP
    exact wr_ns2_diffAt hm₁ hm₂ hk' hP' y
  set F : (ℂ × ℂ) × ℂ → ℂ := fun q => normalizedSolution (fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2 with hF
  have hfd : ContinuousOn (fderiv ℝ F) (V ×ˢ {u : ℂ | u.im ≠ 0}) :=
    hC.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hpart : ∀ q ∈ V ×ˢ {u : ℂ | u.im ≠ 0}, ∀ v : ℂ,
      fderiv ℝ (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2 v = fderiv ℝ F q (0, v) := by
    intro q hq v
    have hFd : DifferentiableAt ℝ F (q.1, q.2) :=
      (hC.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
    have hi : HasFDerivAt (fun y : ℂ => (q.1, y)) (ContinuousLinearMap.inr ℝ (ℂ × ℂ) ℂ) q.2 :=
      hasFDerivAt_prodMk_right q.1 q.2
    have hcomp := hFd.hasFDerivAt.comp q.2 hi
    have he : (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) = F ∘ fun y : ℂ => (q.1, y) := rfl
    rw [he, hcomp.fderiv]
    rfl
  refine ⟨hC.continuousOn, ?_, ?_, ?_⟩
  · have h2 : ContinuousOn (fun q : (ℂ × ℂ) × ℂ =>
        (fderiv ℝ F q ((0 : ℂ × ℂ), (1 : ℂ)) - I * fderiv ℝ F q ((0 : ℂ × ℂ), I)) / 2)
        (V ×ˢ {u : ℂ | u.im ≠ 0}) :=
      ((hfd.clm_apply continuousOn_const).sub (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _
    refine h2.congr fun q hq => ?_
    show (fderiv ℝ (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2 1 -
      I * fderiv ℝ (normalizedSolution fun u => q.1.1 * m₁ u + q.1.2 * m₂ u) q.2 I) / 2 = _
    rw [hpart q hq, hpart q hq]
  · intro P hP
    obtain ⟨k', hk', hP'⟩ := hVk P hP
    obtain ⟨h0, hk0, hk1⟩ := wr_coeff_nonneg hk' hP'
    have h := wr_ns_qc hk0 hk1 h0 le_rfl
    obtain ⟨e, he⟩ := t1_homeomorph h.1 h.2.1
    intro x y hxy
    apply e.injective
    rw [he]
    exact hxy
  · intro P hP y hy
    have hsl : ∀ w' : ℂ, DifferentiableAt ℂ (fun a => normalizedSolution (fun u => a * m₁ u + P.2 * m₂ u) w') P.1 := by
      intro w'
      have h1 := DifferentiableAt.comp (𝕜 := ℂ) (f := fun a : ℂ => ((a, P.2) : ℂ × ℂ)) P.1 (hhol w' P hP)
        (by fun_prop)
      simp only [Function.comp_def] at h1
      exact h1
    refine ⟨hsl y, ?_⟩
    have hCa : ContDiffAt ℝ 3 F (P, y) := hC.contDiffAt (hO.mem_nhds ⟨hP, hy⟩)
    set G : ℂ × ℂ → ℂ := fun p => normalizedSolution (fun u => p.1 * m₁ u + P.2 * m₂ u) p.2 with hG
    have hGa : ContDiffAt ℝ 2 G (P.1, y) := by
      have hm : ContDiffAt ℝ 3 (fun p : ℂ × ℂ => ((p.1, P.2), p.2)) (P.1, y) :=
        ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
      exact (ContDiffAt.comp (g := F) (P.1, y) hCa hm).of_le (by norm_num)
    obtain ⟨hd, -, hbar⟩ := l613_wirt_comm hGa
    have h0 : (fun w' => dzbar (fun e' => G (e', w')) P.1) = fun _ => (0 : ℂ) := by
      funext w'
      exact (cauchyRiemann_iff.1 (hsl w')).2
    rw [h0] at hbar
    have hz : dz (fun _ : ℂ => (0 : ℂ)) y = 0 := by simp [dz]
    rw [hz] at hbar
    exact cauchyRiemann_iff.2 ⟨hd, hbar⟩

/-- A linear combination of harmonic weights on `𝕌` is harmonic. -/
theorem s7g_c79_harm_comb {a b φa φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) (c₁ c₂ : ℂ) :
    IsHarmonicU (fun u => c₁ * a u + c₂ * b u) (fun u => conj c₁ * φa u + conj c₂ * φb u) := by
  obtain ⟨ha1, ⟨Ca, hCa⟩, ha3⟩ := ha
  obtain ⟨hb1, ⟨Cb, hCb⟩, hb3⟩ := hb
  refine ⟨(ha1.const_mul _).add (hb1.const_mul _), ⟨‖c₁‖ * Ca + ‖c₂‖ * Cb, fun z hz => ?_⟩, fun z hz => ?_⟩
  · calc ‖z.im ^ 2 * (conj c₁ * φa z + conj c₂ * φb z)‖
        = ‖conj c₁ * (z.im ^ 2 * φa z) + conj c₂ * (z.im ^ 2 * φb z)‖ := by ring_nf
      _ ≤ ‖c₁‖ * ‖z.im ^ 2 * φa z‖ + ‖c₂‖ * ‖z.im ^ 2 * φb z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul (conj c₁), norm_mul (conj c₂), Complex.norm_conj, Complex.norm_conj]
      _ ≤ ‖c₁‖ * Ca + ‖c₂‖ * Cb := by
          gcongr
          · exact hCa z hz
          · exact hCb z hz
  · show c₁ * a z + c₂ * b z = _
    rw [ha3 z hz, hb3 z hz]
    simp only [map_add, map_mul, Complex.conj_conj]
    ring

/-- `toLinf` is linear on `H^{-1,1}(𝔻*)`. -/
theorem s7g_c79_toLinf_lin {κ l : ℂ → ℂ} (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior)
    (c₁ c₂ : ℂ) : toLinf (fun z => c₁ * κ z + c₂ * l z) = c₁ • toLinf κ + c₂ • toLinf l := by
  have hc : (fun z => c₁ * κ z + c₂ * l z) ∈ harmonicL2 unitDiscExterior :=
    s7pol_harmonic_add (s7pol_harmonic_smul hκ c₁) (s7pol_harmonic_smul hl c₂)
  apply Lp.ext
  filter_upwards [wp_harmonic_toLinf_ae hc, Lp.coeFn_add (c₁ • toLinf κ) (c₂ • toLinf l),
    Lp.coeFn_smul c₁ (toLinf κ), Lp.coeFn_smul c₂ (toLinf l), wp_harmonic_toLinf_ae hκ,
    wp_harmonic_toLinf_ae hl] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, smul_eq_mul, smul_eq_mul]

/-- The model map of a two-direction coefficient is the `((ā₁, ā₂), (a₁, a₂))`-member of the 4-parameter family. -/
theorem s7g_c79_wU (a b : ℂ → ℂ) (p : ℂ × ℂ) :
    (wU fun u => conj p.1 * a u + conj p.2 * b u) = normalizedSolution fun u =>
      (if 0 < u.im then ((conj p.1, conj p.2), p).1.1 * a u + ((conj p.1, conj p.2), p).1.2 * b u else 0) +
        (if u.im < 0 then ((conj p.1, conj p.2), p).2.1 * conj (a (conj u)) +
          ((conj p.1, conj p.2), p).2.2 * conj (b (conj u)) else 0) := by
  show normalizedSolution (extU _) = _
  congr 1
  funext u
  unfold extU
  by_cases h1 : 0 < u.im
  · have h2 : ¬ u.im < 0 := by linarith
    simp [h1, h2]
  · by_cases h2 : u.im < 0
    · simp [h1, h2]
    · simp [h1, h2]

/-- The uniform `L¹` bound of the line-2 double integrand for the 4-parameter family on `S × S` (from `s7g_L1`). -/
theorem s7g_c79_L1 {a b φa φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0))
    {S : Set ℂ} (hSm : MeasurableSet S) (hS : S ⊆ upperHalf) {A B m₁ m₂ φ₁ φ₂ : ℂ → ℂ} (h₁ : IsHarmonicU m₁ φ₁)
    (h₂ : IsHarmonicU m₂ φ₂)
    (hf₁ : ∫⁻ u in upperHalf, ‖m₁ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hf₂ : ∫⁻ u in upperHalf, ‖m₂ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hA : ∀ s ∈ S, ‖A s‖ = ‖m₁ s‖) (hB : ∀ t ∈ S, ‖B t‖ = ‖m₂ t‖)
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) :
    ∃ M : ℝ, ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R,
      ∫⁻ x in S ×ˢ S, ‖A x.1 * (conj (B x.2) *
        (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal M := by
  have hU := measurableSet_upperHalf_aux
  have hak' : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hak u hu⟩
  have hbk' : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hbk u hu⟩
  obtain ⟨M, hMt, hM⟩ := s7g_L1 hk hak' hbk' (wr_isHarmonicU_contDiffOn ha) (wr_isHarmonicU_contDiffOn hb) hR hRk hW
    h₁.1 h₁.2.2 hf₁ h₂.1 h₂.2.2 hf₂
  refine ⟨M.toReal, fun P hP => ?_⟩
  rw [ENNReal.ofReal_toReal hMt.ne]
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
    _ ≤ M := hM P hP

/-- The coefficient `σ_Q` of the 4-parameter family: Beltrami on `ℂ` with bound `‖Q‖·2k`, smooth off `ℝ`, and
linear in `Q`. -/
theorem s7g_c79_sig {a b φa φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hσ : σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * b u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u)) else 0)) :
    (∀ Q, IsBeltramiCoeff (σ Q) univ (‖Q‖ * (2 * k))) ∧
      (∀ Q, ContDiffOn ℝ (⊤ : ℕ∞) (σ Q) {u : ℂ | u.im ≠ 0}) ∧
      ∀ (Q Q' : (ℂ × ℂ) × (ℂ × ℂ)) (c c' : ℂ), (fun u => c * σ Q u + c' * σ Q' u) = σ (c • Q + c' • Q') := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hL : IsOpen {u : ℂ | u.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hUm := measurableSet_upperHalf_aux
  have hak' : IsBeltramiCoeff a upperHalf k :=
    ⟨(harmonicU_continuousOn ha).aestronglyMeasurable hUm, by
      filter_upwards [ae_restrict_mem hUm] with u hu
      exact hak u hu⟩
  have hbk' : IsBeltramiCoeff b upperHalf k :=
    ⟨(harmonicU_continuousOn hb).aestronglyMeasurable hUm, by
      filter_upwards [ae_restrict_mem hUm] with u hu
      exact hbk u hu⟩
  have hsa := wr_isHarmonicU_contDiffOn ha
  have hsb := wr_isHarmonicU_contDiffOn hb
  obtain ⟨hA1, hA2, -, -, -⟩ := wr_U_coeffs hk hak' hsa
  obtain ⟨hB1, hB2, -, -, -⟩ := wr_U_coeffs hk hbk' hsb
  have hcj : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℂ => conj v) := Complex.conjCLE.contDiff
  refine ⟨fun Q => ⟨?_, ?_⟩, fun Q u hu => ?_, fun Q Q' c c' => ?_⟩
  · have e : σ Q = fun u => Q.1.1 * (if 0 < u.im then a u else 0) + Q.1.2 * (if 0 < u.im then b u else 0) +
        Q.2.1 * (if u.im < 0 then conj (a (conj u)) else 0) + Q.2.2 * (if u.im < 0 then conj (b (conj u)) else 0) := by
      rw [hσ]
      funext u
      dsimp only
      split_ifs <;> ring
    rw [e]
    exact (((hA1.1.const_mul _).add (hB1.1.const_mul _)).add (hA2.1.const_mul _)).add (hB2.1.const_mul _)
  · refine Eventually.of_forall fun u => ?_
    have h11 : ‖Q.1.1‖ ≤ ‖Q‖ := (norm_fst_le Q.1).trans (norm_fst_le Q)
    have h12 : ‖Q.1.2‖ ≤ ‖Q‖ := (norm_snd_le Q.1).trans (norm_fst_le Q)
    have h21 : ‖Q.2.1‖ ≤ ‖Q‖ := (norm_fst_le Q.2).trans (norm_snd_le Q)
    have h22 : ‖Q.2.2‖ ≤ ‖Q‖ := (norm_snd_le Q.2).trans (norm_snd_le Q)
    have hQ := norm_nonneg Q
    rw [hσ]
    dsimp only
    by_cases h1 : 0 < u.im
    · have h2 : ¬ u.im < 0 := by linarith
      rw [if_pos h1, if_neg h2, add_zero]
      calc ‖Q.1.1 * a u + Q.1.2 * b u‖ ≤ ‖Q.1.1‖ * ‖a u‖ + ‖Q.1.2‖ * ‖b u‖ := by
            rw [← norm_mul, ← norm_mul]
            exact norm_add_le _ _
        _ ≤ ‖Q‖ * k + ‖Q‖ * k :=
            add_le_add (mul_le_mul h11 (hak u h1) (norm_nonneg _) hQ) (mul_le_mul h12 (hbk u h1) (norm_nonneg _) hQ)
        _ = ‖Q‖ * (2 * k) := by ring
    · by_cases h2 : u.im < 0
      · have hc : conj u ∈ upperHalf := by
          show 0 < (conj u).im
          rw [Complex.conj_im]
          linarith
        rw [if_neg h1, if_pos h2, zero_add]
        calc ‖Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u))‖
              ≤ ‖Q.2.1‖ * ‖a (conj u)‖ + ‖Q.2.2‖ * ‖b (conj u)‖ := by
              rw [← Complex.norm_conj (a (conj u)), ← Complex.norm_conj (b (conj u)), ← norm_mul, ← norm_mul]
              exact norm_add_le _ _
          _ ≤ ‖Q‖ * k + ‖Q‖ * k :=
              add_le_add (mul_le_mul h21 (hak _ hc) (norm_nonneg _) hQ) (mul_le_mul h22 (hbk _ hc) (norm_nonneg _) hQ)
          _ = ‖Q‖ * (2 * k) := by ring
      · rw [if_neg h1, if_neg h2, add_zero, norm_zero]
        positivity
  · have hu' : u.im ≠ 0 := hu
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_gt_of_ne hu' with h | h
    · have hc : conj u ∈ upperHalf := by
        show 0 < (conj u).im
        rw [Complex.conj_im]
        linarith
      have ga : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => conj (a (conj v))) u :=
        hcj.contDiffAt.comp u ((hsa.contDiffAt (hU.mem_nhds hc)).comp u hcj.contDiffAt)
      have gb : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => conj (b (conj v))) u :=
        hcj.contDiffAt.comp u ((hsb.contDiffAt (hU.mem_nhds hc)).comp u hcj.contDiffAt)
      refine (((contDiffAt_const (c := Q.2.1)).mul ga).add ((contDiffAt_const (c := Q.2.2)).mul gb)).congr_of_eventuallyEq ?_
      filter_upwards [hL.mem_nhds h] with v hv
      have hv' : v.im < 0 := hv
      rw [hσ]
      dsimp only
      rw [if_neg (by linarith), if_pos hv', zero_add]
    · have ga : ContDiffAt ℝ (⊤ : ℕ∞) a u := hsa.contDiffAt (hU.mem_nhds h)
      have gb : ContDiffAt ℝ (⊤ : ℕ∞) b u := hsb.contDiffAt (hU.mem_nhds h)
      refine (((contDiffAt_const (c := Q.1.1)).mul ga).add ((contDiffAt_const (c := Q.1.2)).mul gb)).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds h] with v hv
      have hv' : 0 < v.im := hv
      rw [hσ]
      dsimp only
      rw [if_pos hv', if_neg (by linarith), add_zero]
  · rw [hσ]
    funext u
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    split_ifs <;> ring

/-- Holomorphy of the line-2 double integral of the 4-parameter family along a complex line `t ↦ Q₀ + t e`. -/
theorem s7g_c79_dir {a b φa φb : ℂ → ℂ} (ha : IsHarmonicU a φa) (hb : IsHarmonicU b φb) {k : ℝ} (hk : 0 ≤ k)
    (hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k) (hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k)
    {σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hσ : σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * b u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u)) else 0))
    {W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ} (hW : W = fun Q => normalizedSolution (σ Q))
    {S : Set ℂ} (hSm : MeasurableSet S) (hSU : S ⊆ upperHalf) {A B : ℂ → ℂ} (hAc : ContinuousOn A S)
    (hBc : ContinuousOn B S) {Q₀ e : (ℂ × ℂ) × (ℂ × ℂ)} {c : ℂ} {ρ : ℝ}
    (hρ : ∀ t ∈ closedBall c ρ, ‖Q₀ + t • e‖ * (2 * k) < 1) {M : ℝ}
    (hM : ∀ t ∈ closedBall c ρ, ∫⁻ x in S ×ˢ S, ‖A x.1 * (conj (B x.2) *
      (dz (W (Q₀ + t • e)) x.2 * dz (W (Q₀ + t • e)) (conj x.1) /
        (W (Q₀ + t • e) x.2 - W (Q₀ + t • e) (conj x.1)) ^ 2) ^ 2)‖ₑ ≤ ENNReal.ofReal M) :
    ContinuousOn (fun q : ℂ × (ℂ × ℂ) => A q.2.1 * (conj (B q.2.2) *
      (dz (W (Q₀ + q.1 • e)) q.2.2 * dz (W (Q₀ + q.1 • e)) (conj q.2.1) /
        (W (Q₀ + q.1 • e) q.2.2 - W (Q₀ + q.1 • e) (conj q.2.1)) ^ 2) ^ 2)) (closedBall c ρ ×ˢ (S ×ˢ S)) ∧
    DifferentiableOn ℂ (fun t => ∫ x in S ×ˢ S, A x.1 * (conj (B x.2) *
      (dz (W (Q₀ + t • e)) x.2 * dz (W (Q₀ + t • e)) (conj x.1) /
        (W (Q₀ + t • e) x.2 - W (Q₀ + t • e) (conj x.1)) ^ 2) ^ 2)) (ball c ρ) := by
  obtain ⟨hσB, hσs, hσl⟩ := s7g_c79_sig ha hb hk hak hbk hσ
  have hWt : ∀ t : ℂ, W (Q₀ + t • e) = normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u := by
    intro t
    rw [hW]
    show normalizedSolution (σ (Q₀ + t • e)) = _
    rw [hσl, one_smul, add_comm]
  simp only [hWt] at hM ⊢
  set V : Set (ℂ × ℂ) := {P | ‖P.1 • e + P.2 • Q₀‖ * (2 * k) < 1} with hVdef
  have hV : IsOpen V :=
    isOpen_lt (((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)).norm.mul
      continuous_const) continuous_const
  have hVk : ∀ P ∈ V, ∃ k' < 1, IsBeltramiCoeff (fun u => P.1 * σ e u + P.2 * σ Q₀ u) univ k' := by
    intro P hP
    refine ⟨_, hP, ?_⟩
    rw [hσl]
    exact hσB _
  obtain ⟨hWc, hDc, hinj, hhol⟩ := s7g_c79_slice (hσB e) (hσB Q₀) (hσs e) (hσs Q₀) hV hVk
  have hVt : ∀ t ∈ closedBall c ρ, ((t, (1 : ℂ)) : ℂ × ℂ) ∈ V := by
    intro t ht
    show ‖t • e + (1 : ℂ) • Q₀‖ * (2 * k) < 1
    rw [one_smul, add_comm]
    exact hρ t ht
  have him1 : ∀ x ∈ S ×ˢ S, x.2.im ≠ 0 := fun x hx => (hSU hx.2 : 0 < x.2.im).ne'
  have him2 : ∀ x ∈ S ×ˢ S, (conj x.1).im ≠ 0 := fun x hx => by
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr (hSU hx.1 : 0 < x.1.im).ne'
  have hne : ∀ t ∈ closedBall c ρ, ∀ x ∈ S ×ˢ S,
      ((normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u) x.2 -
        (normalizedSolution fun u => t * σ e u + 1 * σ Q₀ u) (conj x.1)) ^ 2 ≠ 0 := by
    intro t ht x hx
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have h' := hinj (t, 1) (hVt t ht) h
    have h2 : x.2.im = (conj x.1).im := by rw [h']
    rw [Complex.conj_im] at h2
    have h3 : 0 < x.1.im := hSU hx.1
    have h4 : 0 < x.2.im := hSU hx.2
    linarith
  have hT := hSm.prod hSm
  have hcont : ContinuousOn (fun q : ℂ × (ℂ × ℂ) => A q.2.1 * (conj (B q.2.2) *
      (dz (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) q.2.2 *
        dz (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) (conj q.2.1) /
        ((normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) q.2.2 -
          (normalizedSolution fun u => q.1 * σ e u + 1 * σ Q₀ u) (conj q.2.1)) ^ 2) ^ 2))
      (closedBall c ρ ×ˢ (S ×ˢ S)) := by
    have m2 : MapsTo (fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), q.2.2)) (closedBall c ρ ×ˢ (S ×ˢ S))
        (V ×ˢ {u : ℂ | u.im ≠ 0}) := fun q hq => ⟨hVt q.1 hq.1, him1 q.2 hq.2⟩
    have m1 : MapsTo (fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), conj q.2.1)) (closedBall c ρ ×ˢ (S ×ˢ S))
        (V ×ˢ {u : ℂ | u.im ≠ 0}) := fun q hq => ⟨hVt q.1 hq.1, him2 q.2 hq.2⟩
    have c2 : Continuous fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), q.2.2) := by fun_prop
    have c1 : Continuous fun q : ℂ × (ℂ × ℂ) => (((q.1, (1 : ℂ)) : ℂ × ℂ), conj q.2.1) := by fun_prop
    have hW2 := hWc.comp c2.continuousOn m2
    have hW1 := hWc.comp c1.continuousOn m1
    have hD2 := hDc.comp c2.continuousOn m2
    have hD1 := hDc.comp c1.continuousOn m1
    have hA := hAc.comp continuous_snd.fst.continuousOn (fun q (hq : q ∈ closedBall c ρ ×ˢ (S ×ˢ S)) => hq.2.1)
    have hB := Complex.continuous_conj.comp_continuousOn
      (hBc.comp continuous_snd.snd.continuousOn (fun q (hq : q ∈ closedBall c ρ ×ˢ (S ×ˢ S)) => hq.2.2))
    exact hA.mul (hB.mul (((hD2.mul hD1).div ((hW2.sub hW1).pow 2) fun q hq => hne q.1 hq.1 q.2 hq.2).pow 2))
  refine ⟨hcont, s7g_f2_param (m := volume) hT hcont ?_ hM⟩
  intro x hx t ht
  have hP := hVt t (ball_subset_closedBall ht)
  obtain ⟨h1, h2⟩ := hhol (t, 1) hP x.2 (him1 x hx)
  obtain ⟨h3, h4⟩ := hhol (t, 1) hP (conj x.1) (him2 x hx)
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).mul (((h2.mul h4).div ((h1.sub h3).pow 2)
    (hne t (ball_subset_closedBall ht) x hx)).pow 2))).differentiableWithinAt

/-- STUB CORE4. The two-direction holomorphic extension: near `0`, `g_{μν̄}(e₁ κ + e₂ l) = Φ((ē₁, ē₂), (e₁, e₂))`
for a `Φ` that is separately holomorphic in each coordinate and bounded on a polydisc of `ℂ⁴`. -/
theorem s7g_c79_core {μ ν κ l : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∃ Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ,
      (∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, DifferentiableAt ℂ (fun z => Φ ((z, p.1.2), p.2)) p.1.1 ∧
        DifferentiableAt ℂ (fun z => Φ ((p.1.1, z), p.2)) p.1.2 ∧
        DifferentiableAt ℂ (fun z => Φ (p.1, (z, p.2.2))) p.2.1 ∧
        DifferentiableAt ℂ (fun z => Φ (p.1, (p.2.1, z))) p.2.2) ∧
      (∃ M : ℝ, ∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ‖Φ p‖ ≤ M) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ R0 ∧ ∀ p : ℂ × ℂ, ‖p‖ < r →
        gWP μ ν (p.1 • toLinf κ + p.2 • toLinf l) = Φ ((conj p.1, conj p.2), p) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  -- harmonic weights of the directions and of `μ, ν`
  obtain ⟨a, φa, ha, haf⟩ := p71_wm_harm (hCc κ hκ).1 (wp_harmonic_continuousOn hκ) (wp_harmonic_toLinf_ae hκ)
  obtain ⟨b, φb, hb, hbf⟩ := p71_wm_harm (hCc l hl).1 (wp_harmonic_continuousOn hl) (wp_harmonic_toLinf_ae hl)
  obtain ⟨Ca, hCa0, hCa⟩ := harmonicU_bounded ha
  obtain ⟨Cb, hCb0, hCb⟩ := harmonicU_bounded hb
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = max Ca Cb := ⟨_, rfl⟩
  have hk : 0 ≤ k := by rw [hkdef]; exact le_max_of_le_left hCa0
  have hak : ∀ u ∈ upperHalf, ‖a u‖ ≤ k := fun u hu => by rw [hkdef]; exact (hCa u hu).trans (le_max_left _ _)
  have hbk : ∀ u ∈ upperHalf, ‖b u‖ ≤ k := fun u hu => by rw [hkdef]; exact (hCb u hu).trans (le_max_right _ _)
  obtain ⟨mμ, φμ, hμh, hμf, hμn⟩ := s7g_l3_weight hμ
  obtain ⟨mν, φν, hνh, hνf, hνn⟩ := s7g_l3_weight hν
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
  have hAn : ∀ s ∈ S, ‖A s‖ = ‖mμ s‖ := by
    intro s hs
    rw [hSdef] at hs
    rw [hAdef]
    show ‖μ (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2))‖ = _
    rw [s7g_l3_Aconj μ hs.1 hs.2 (hμf s hs.1 hs.2), Complex.norm_conj]
  have hBn : ∀ s ∈ S, ‖B s‖ = ‖mν s‖ := by
    intro s hs
    rw [hSdef] at hs
    rw [hBdef]
    show ‖ν (cayley (conj s)) * (conj (2 * I / (conj s + I) ^ 2) / (2 * I / (conj s + I) ^ 2))‖ = _
    rw [s7g_l3_Aconj ν hs.1 hs.2 (hνf s hs.1 hs.2), Complex.norm_conj]
  -- the 4-parameter family
  obtain ⟨σ, hσ⟩ : ∃ σ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, σ = fun Q u =>
      (if 0 < u.im then Q.1.1 * a u + Q.1.2 * b u else 0) +
        (if u.im < 0 then Q.2.1 * conj (a (conj u)) + Q.2.2 * conj (b (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : (ℂ × ℂ) × (ℂ × ℂ) → ℂ → ℂ, W = fun Q => normalizedSolution (σ Q) := ⟨_, rfl⟩
  have hW' : W = fun P => normalizedSolution fun u =>
      (if 0 < u.im then P.1.1 * a u + P.1.2 * b u else 0) +
        (if u.im < 0 then P.2.1 * conj (a (conj u)) + P.2.2 * conj (b (conj u)) else 0) := by
    rw [hW, hσ]
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = 1 / (4 * (k + 1)) := ⟨_, rfl⟩
  have hR0p : 0 < R0 := by rw [hR0]; positivity
  have hR0k2 : 2 * R0 * k < 1 := by
    rw [hR0, show 2 * (1 / (4 * (k + 1))) * k = k / (2 * (k + 1)) by field_simp; ring,
      div_lt_one (by positivity)]
    linarith
  obtain ⟨M, hM⟩ := s7g_c79_L1 ha hb hk hak hbk hW' hSm hSU hμh hνh hfμ hfν hAn hBn hR0p.le hR0k2
  obtain ⟨F, hF⟩ : ∃ F : (ℂ × ℂ) × (ℂ × ℂ) → ℂ × ℂ → ℂ, F = fun P x => A x.1 * (conj (B x.2) *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  have hM' : ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ∫⁻ x in S ×ˢ S, ‖F P x‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    rw [hF]
    exact hM P hP
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (ℂ × ℂ) × (ℂ × ℂ) → ℂ, Φ = fun Q => (12 / π : ℂ) * ∫ x in S ×ˢ S, F Q x := ⟨_, rfl⟩
  have hTm : MeasurableSet (S ×ˢ S) := hSm.prod hSm
  have hρk : ∀ P ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ‖P‖ * (2 * k) < 1 := by
    intro P hP
    have h := mem_closedBall_zero_iff.1 hP
    calc ‖P‖ * (2 * k) ≤ R0 * (2 * k) := mul_le_mul_of_nonneg_right h (by positivity)
      _ < 1 := by linarith
  -- separate holomorphy along complex lines
  have hline : ∀ (L : ℂ → (ℂ × ℂ) × (ℂ × ℂ)) (Q₀ e : (ℂ × ℂ) × (ℂ × ℂ)), (∀ t, L t = Q₀ + t • e) →
      ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → (∀ t ∈ closedBall c ρ, ‖L t‖ ≤ R0) → DifferentiableAt ℂ (fun t => Φ (L t)) c := by
    intro L Q₀ e hL c ρ hρ hc
    have hmem : ∀ t ∈ closedBall c ρ, Q₀ + t • e ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := fun t ht => by
      rw [← hL]
      exact mem_closedBall_zero_iff.2 (hc t ht)
    obtain ⟨-, hd⟩ := s7g_c79_dir ha hb hk hak hbk hσ hW hSm hSU hAc hBc (Q₀ := Q₀) (e := e) (c := c) (ρ := ρ)
      (fun t ht => hρk _ (hmem t ht)) (M := M) (fun t ht => hM _ (hmem t ht))
    have hd' := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
    have e1 : (fun t => Φ (L t)) = fun t => (12 / π : ℂ) * ∫ x in S ×ˢ S, F (Q₀ + t • e) x := by
      funext t
      rw [hΦ, hL]
    rw [e1, hF]
    exact (differentiableAt_const _).mul hd'
  have hRp : ∀ p ∈ ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0, ∀ x : ℂ, ‖x‖ ≤ ‖p‖ →
      ∀ t ∈ closedBall x ((R0 - ‖p‖) / 2), ‖t‖ ≤ R0 := by
    intro p hp x hx t ht
    have hp' := mem_ball_zero_iff.1 hp
    have h1 : ‖t‖ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by
      have := mem_closedBall.1 ht
      rw [dist_eq_norm] at this
      calc ‖t‖ = ‖x + (t - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖t - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + (R0 - ‖p‖) / 2 := by linarith
    linarith
  refine ⟨R0, hR0p, Φ, fun p hp => ?_, ⟨‖(12 / π : ℂ)‖ * max M 0, fun p hp => ?_⟩, ?_⟩
  · -- the four coordinate slices
    have hp' : ‖p‖ < R0 := mem_ball_zero_iff.1 hp
    have hρ : 0 < (R0 - ‖p‖) / 2 := by linarith
    have hpR : ‖p‖ ≤ R0 := hp'.le
    have h11 : ‖p.1.1‖ ≤ ‖p‖ := (norm_fst_le p.1).trans (norm_fst_le p)
    have h12 : ‖p.1.2‖ ≤ ‖p‖ := (norm_snd_le p.1).trans (norm_fst_le p)
    have h21 : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
    have h22 : ‖p.2.2‖ ≤ ‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
    have h1' : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have h2' : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine hline (fun z => ((z, p.1.2), p.2)) ((0, p.1.2), p.2) ((1, 0), (0, 0)) (fun t => by ext <;> simp)
        p.1.1 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨hRp p hp _ h11 t ht, h12.trans hpR⟩, h2'.trans hpR⟩
    · refine hline (fun z => ((p.1.1, z), p.2)) ((p.1.1, 0), p.2) ((0, 1), (0, 0)) (fun t => by ext <;> simp)
        p.1.2 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨h11.trans hpR, hRp p hp _ h12 t ht⟩, h2'.trans hpR⟩
    · refine hline (fun z => (p.1, (z, p.2.2))) (p.1, (0, p.2.2)) ((0, 0), (1, 0)) (fun t => by ext <;> simp)
        p.2.1 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨h1'.trans hpR, norm_prod_le_iff.2 ⟨hRp p hp _ h21 t ht, h22.trans hpR⟩⟩
    · refine hline (fun z => (p.1, (p.2.1, z))) (p.1, (p.2.1, 0)) ((0, 0), (0, 1)) (fun t => by ext <;> simp)
        p.2.2 _ hρ fun t ht => ?_
      exact norm_prod_le_iff.2 ⟨h1'.trans hpR, norm_prod_le_iff.2 ⟨h21.trans hpR, hRp p hp _ h22 t ht⟩⟩
  · -- the bound
    have h1 := (enorm_integral_le_lintegral_enorm (μ := volume.restrict (S ×ˢ S)) (F p)).trans
      (hM' p (ball_subset_closedBall hp))
    have h2 : ENNReal.ofReal ‖∫ x in S ×ˢ S, F p x‖ ≤ ENNReal.ofReal (max M 0) := by
      rw [ofReal_norm]
      exact h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [hΦ]
    show ‖(12 / π : ℂ) * ∫ x in S ×ˢ S, F p x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2) (norm_nonneg _)
  -- the representation on a small ball
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (1 / (‖toLinf κ‖ + ‖toLinf l‖ + 2 * k + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  refine ⟨r, hr0, hrR, fun p hp => ?_⟩
  have hpR : ‖p‖ < R0 := lt_of_lt_of_le hp hrR
  have hpD : ‖p‖ * (‖toLinf κ‖ + ‖toLinf l‖ + 2 * k + 1) < 1 := by
    have h := lt_of_lt_of_le hp (show r ≤ 1 / (‖toLinf κ‖ + ‖toLinf l‖ + 2 * k + 1) by rw [hr]; exact min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at h
  have hn1 := norm_fst_le p
  have hn2 := norm_snd_le p
  have hnp := norm_nonneg p
  have hNκ := norm_nonneg (toLinf κ)
  have hNl := norm_nonneg (toLinf l)
  have hc : (fun z => p.1 * κ z + p.2 * l z) ∈ harmonicL2 unitDiscExterior :=
    s7pol_harmonic_add (s7pol_harmonic_smul hκ p.1) (s7pol_harmonic_smul hl p.2)
  have hharm := s7g_c79_harm_comb ha hb (conj p.1) (conj p.2)
  have hm' : ∀ u ∈ upperHalf, u ≠ I → (fun u => conj p.1 * a u + conj p.2 * b u) u =
      conj ((fun z => p.1 * κ z + p.2 * l z) (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)) := by
    intro u hu huI
    show conj p.1 * a u + conj p.2 * b u = conj (p.1 * κ (cayley (conj u)) + p.2 * l (cayley (conj u))) * _ * _
    rw [haf u hu huI, hbf u hu huI, map_add, map_mul, map_mul]
    ring
  have hC0 : 0 ≤ ‖p.1‖ * k + ‖p.2‖ * k := by positivity
  have hCb' : ∀ u ∈ upperHalf, ‖(fun u => conj p.1 * a u + conj p.2 * b u) u‖ ≤ ‖p.1‖ * k + ‖p.2‖ * k := by
    intro u hu
    show ‖conj p.1 * a u + conj p.2 * b u‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    exact add_le_add (mul_le_mul_of_nonneg_left (hak u hu) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hbk u hu) (norm_nonneg _))
  have hε1 : ‖(1 : ℂ)‖ * ‖toLinf fun z => p.1 * κ z + p.2 * l z‖ < 1 := by
    rw [s7g_c79_toLinf_lin hκ hl, norm_one, one_mul]
    calc ‖p.1 • toLinf κ + p.2 • toLinf l‖ ≤ ‖p.1‖ * ‖toLinf κ‖ + ‖p.2‖ * ‖toLinf l‖ := by
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ ‖p‖ * ‖toLinf κ‖ + ‖p‖ * ‖toLinf l‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hn1 hNκ) (mul_le_mul_of_nonneg_right hn2 hNl)
      _ < 1 := by nlinarith
  have hε2 : ‖conj (1 : ℂ)‖ * (‖p.1‖ * k + ‖p.2‖ * k) < 1 := by
    rw [map_one, norm_one, one_mul]
    calc ‖p.1‖ * k + ‖p.2‖ * k ≤ ‖p‖ * k + ‖p‖ * k :=
          add_le_add (mul_le_mul_of_nonneg_right hn1 hk) (mul_le_mul_of_nonneg_right hn2 hk)
      _ < 1 := by nlinarith
  rw [← s7g_c79_toLinf_lin hκ hl, ← one_smul ℂ (toLinf fun z => p.1 * κ z + p.2 * l z),
    s7g_l2 hμ hν (hCc _ hc).1 (wp_harmonic_continuousOn hc) (wp_harmonic_toLinf_ae hc) hharm hm' hC0 hCb' hε1 hε2]
  simp only [map_one, one_mul]
  have hV : W ((conj p.1, conj p.2), p) = wU fun u => conj p.1 * a u + conj p.2 * b u := by
    rw [s7g_c79_wU, hW, hσ]
  rw [← hV]
  have hPmem : ((conj p.1, conj p.2), p) ∈ closedBall (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0 := by
    refine mem_closedBall_zero_iff.2 (norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, hpR.le⟩)
    · rw [Complex.norm_conj]
      linarith
    · rw [Complex.norm_conj]
      linarith
  -- joint continuity of the integrand at the parameter, from the line lemma with `e = 0`
  obtain ⟨hcP, -⟩ := s7g_c79_dir ha hb hk hak hbk hσ hW hSm hSU hAc hBc (Q₀ := ((conj p.1, conj p.2), p))
    (e := 0) (c := 0) (ρ := 1) (fun t _ => by rw [smul_zero, add_zero]; exact hρk _ hPmem) (M := M)
    (fun t _ => by rw [smul_zero, add_zero]; exact hM _ hPmem)
  simp only [smul_zero, add_zero] at hcP
  have hcF : ContinuousOn (F ((conj p.1, conj p.2), p)) (S ×ˢ S) := by
    have h := hcP.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => (⟨mem_closedBall_self zero_le_one, hx⟩ : ((0 : ℂ), x) ∈ closedBall (0 : ℂ) 1 ×ˢ (S ×ˢ S)))
    rw [hF]
    exact h
  have hint : Integrable (F ((conj p.1, conj p.2), p)) ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact ⟨hcF.aestronglyMeasurable hTm, lt_of_le_of_lt (hM' _ hPmem) ENNReal.ofReal_lt_top⟩
  have hprod := integral_prod (F ((conj p.1, conj p.2), p)) hint
  have e2 : (∫ x in S ×ˢ S, F ((conj p.1, conj p.2), p) x) =
      ∫ s in S, ∫ t in S, F ((conj p.1, conj p.2), p) (s, t) := by
    rw [← hprod, Measure.prod_restrict]
    rfl
  rw [hΦ]
  show _ = (12 / π : ℂ) * ∫ x in S ×ˢ S, F ((conj p.1, conj p.2), p) x
  congr 1
  rw [e2, ← setIntegral_congr_set hnull]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [← setIntegral_congr_set hnull, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [hF, hAdef, hBdef]

/-- (C4) `(e₁, e₂) ↦ g_{μν̄}(e₁ κ + e₂ l)` is real `C²` near `0`. -/
theorem s7g_c79_C2 {μ ν κ l : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior) :
    ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 2 (fun p : ℂ × ℂ => gWP μ ν (p.1 • toLinf κ + p.2 • toLinf l)) (ball 0 r) := by
  obtain ⟨R0, hR0, Φ, hhol, ⟨M, hM⟩, r, hr, hrR, hEq⟩ := s7g_c79_core hμ hν hκ hl
  have hU : IsOpen (ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0) := isOpen_ball
  have hΦ : ContDiffOn ℂ 2 Φ (ball (0 : (ℂ × ℂ) × (ℂ × ℂ)) R0) :=
    s7g_c79_hartogs hU 2 Φ (fun p hp => (hhol p hp).1) (fun p hp => (hhol p hp).2.1)
      (fun p hp => (hhol p hp).2.2.1) (fun p hp => (hhol p hp).2.2.2)
      (fun p hp => by
        obtain ⟨ρ, hρ, hs⟩ := Metric.isOpen_iff.1 hU p hp
        exact ⟨ρ, hρ, M, fun q hq => hM q (hs hq)⟩)
  have hmap : ContDiff ℝ 2 (fun p : ℂ × ℂ => (((conj p.1, conj p.2), p) : (ℂ × ℂ) × (ℂ × ℂ))) :=
    ((Complex.conjCLE.contDiff.comp contDiff_fst).prodMk (Complex.conjCLE.contDiff.comp contDiff_snd)).prodMk
      contDiff_id
  refine ⟨r, hr, ((hΦ.restrict_scalars ℝ).comp hmap.contDiffOn fun p hp => ?_).congr fun p hp => hEq p ?_⟩
  · have h1 : ‖p‖ < r := mem_ball_zero_iff.1 hp
    rw [mem_ball_zero_iff]
    simp only [Prod.norm_def, Complex.norm_conj] at h1 ⊢
    rw [max_self]
    exact lt_of_lt_of_le h1 hrR
  · exact mem_ball_zero_iff.1 hp

/-! ### POL, LIN, SES, SYM -/

/-- The mixed Wirtinger derivative `∂_{e₁}(∂̄_{e₂} F(P e₁ + Q e₂))|₀` of a real `C²` function along two real-linear
maps, in terms of the second derivative `B = D²F(0)`. -/
theorem s7g_c79_dd {F : ℂ × ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : ContDiffOn ℝ 2 F (ball 0 r))
    (P Q : ℂ →L[ℝ] ℂ × ℂ) :
    dz (fun e₁ => dzbar (fun e₂ => F (P e₁ + Q e₂)) 0) 0 =
      ((fderiv ℝ (fderiv ℝ F) 0 (P 1) (Q 1) + I * fderiv ℝ (fderiv ℝ F) 0 (P 1) (Q I)) -
        I * (fderiv ℝ (fderiv ℝ F) 0 (P I) (Q 1) + I * fderiv ℝ (fderiv ℝ F) 0 (P I) (Q I))) / 4 := by
  set B := fderiv ℝ (fderiv ℝ F) 0 with hB
  have hdiff : ∀ x ∈ ball (0 : ℂ × ℂ) r, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hx)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    ((hF.fderiv_of_isOpen isOpen_ball (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hev : (fun e₁ => dzbar (fun e₂ => F (P e₁ + Q e₂)) 0) =ᶠ[𝓝 0]
      fun e₁ => (fderiv ℝ F (P e₁) (Q 1) + I * fderiv ℝ F (P e₁) (Q I)) / 2 := by
    have hc : Tendsto (fun e₁ => P e₁) (𝓝 0) (𝓝 0) := by
      simpa using P.continuous.tendsto 0
    filter_upwards [hc (ball_mem_nhds 0 hr)] with e₁ he₁
    have he : P e₁ + Q 0 ∈ ball (0 : ℂ × ℂ) r := by
      rw [map_zero, add_zero]
      exact he₁
    have h := (hdiff _ he).hasFDerivAt.comp (0 : ℂ) ((hasFDerivAt_const (P e₁) (0 : ℂ)).add Q.hasFDerivAt)
    rw [map_zero, add_zero, zero_add] at h
    have h' : fderiv ℝ (fun e₂ => F (P e₁ + Q e₂)) 0 = (fderiv ℝ F (P e₁)).comp Q := h.fderiv
    show (fderiv ℝ (fun e₂ => F (P e₁ + Q e₂)) 0 1 + I * fderiv ℝ (fun e₂ => F (P e₁ + Q e₂)) 0 I) / 2 = _
    rw [h']
    rfl
  have hD' : HasFDerivAt (fderiv ℝ F) B (P 0) := by
    rw [map_zero]
    exact hD.hasFDerivAt
  have hg := hD'.comp (0 : ℂ) P.hasFDerivAt
  have hw : ∀ w : ℂ × ℂ, HasFDerivAt (fun e₁ => fderiv ℝ F (P e₁) w)
      ((fderiv ℝ F (P 0)).comp (0 : ℂ →L[ℝ] ℂ × ℂ) + (B.comp P).flip w) 0 := fun w =>
    hg.clm_apply (hasFDerivAt_const w 0)
  have hN := (hw (Q 1)).add ((hw (Q I)).const_mul I)
  have hψ := hN.mul_const (2 : ℂ)⁻¹
  have e1 : (fun e₁ => (fderiv ℝ F (P e₁) (Q 1) + I * fderiv ℝ F (P e₁) (Q I)) / 2) =
      fun e₁ => (fderiv ℝ F (P e₁) (Q 1) + I * fderiv ℝ F (P e₁) (Q I)) * (2 : ℂ)⁻¹ :=
    funext fun e₁ => div_eq_mul_inv _ _
  have hdz : dz (fun e₁ => dzbar (fun e₂ => F (P e₁ + Q e₂)) 0) 0 =
      dz (fun e₁ => (fderiv ℝ F (P e₁) (Q 1) + I * fderiv ℝ F (P e₁) (Q I)) / 2) 0 := by
    simp only [dz, hev.fderiv_eq]
  rw [hdz, e1]
  unfold dz
  have hψ' : HasFDerivAt (fun e₁ => (fderiv ℝ F (P e₁) (Q 1) + I * fderiv ℝ F (P e₁) (Q I)) * (2 : ℂ)⁻¹)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ F (P 0)).comp (0 : ℂ →L[ℝ] ℂ × ℂ) + (B.comp P).flip (Q 1) +
        I • ((fderiv ℝ F (P 0)).comp (0 : ℂ →L[ℝ] ℂ × ℂ) + (B.comp P).flip (Q I)))) 0 := hψ
  rw [hψ'.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply, map_zero, smul_eq_mul, zero_add]
  ring

/-- Translation form of `∂̄`. -/
theorem s7g_c79_dzbar_shift (G : ℂ → ℂ) (ε : ℂ) : dzbar G ε = dzbar (fun e => G (ε + e)) 0 := by
  unfold dzbar
  rw [fderiv_comp_add_left, add_zero]

/-- STUB POL. Polarization of the Levi form of a real `C²` function of two complex variables. -/
theorem s7g_c79_pol {F : ℂ × ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hF : ContDiffOn ℝ 2 F (ball 0 r)) :
    4 * dz (fun e₁ => dzbar (fun e₂ => F (e₁, e₂)) 0) 0 =
      1 * dz (dzbar fun ε => F (ε, 1 * ε)) 0 + I * dz (dzbar fun ε => F (ε, I * ε)) 0 +
        (-1) * dz (dzbar fun ε => F (ε, (-1) * ε)) 0 + (-I) * dz (dzbar fun ε => F (ε, (-I) * ε)) 0 := by
  have hline : ∀ c : ℂ, (dzbar fun ε => F (ε, c * ε)) = fun e₁ =>
      dzbar (fun e₂ => F (((ContinuousLinearMap.id ℝ ℂ).prod (ContinuousLinearMap.mul ℝ ℂ c)) e₁ +
        ((ContinuousLinearMap.id ℝ ℂ).prod (ContinuousLinearMap.mul ℝ ℂ c)) e₂)) 0 := by
    intro c
    funext e₁
    rw [s7g_c79_dzbar_shift]
    congr 1
    funext e₂
    congr 1
    ext <;> simp [mul_add]
  have hL : (fun e₁ => dzbar (fun e₂ => F (e₁, e₂)) 0) = fun e₁ =>
      dzbar (fun e₂ => F (ContinuousLinearMap.inl ℝ ℂ ℂ e₁ + ContinuousLinearMap.inr ℝ ℂ ℂ e₂)) 0 := by
    funext e₁
    congr 1
    funext e₂
    congr 1
    ext <;> simp
  rw [hL, hline, hline, hline, hline, s7g_c79_dd hr hF, s7g_c79_dd hr hF, s7g_c79_dd hr hF, s7g_c79_dd hr hF,
    s7g_c79_dd hr hF]
  set B := fderiv ℝ (fderiv ℝ F) 0
  have hv : ∀ c v : ℂ, ((ContinuousLinearMap.id ℝ ℂ).prod (ContinuousLinearMap.mul ℝ ℂ c)) v =
      ContinuousLinearMap.inl ℝ ℂ ℂ v + ContinuousLinearMap.inr ℝ ℂ ℂ (c * v) := by
    intro c v
    ext <;> simp
  simp only [hv]
  simp only [map_add, ContinuousLinearMap.add_apply, one_mul, mul_one, Complex.I_mul_I, neg_mul, mul_neg,
    neg_neg, map_neg, ContinuousLinearMap.neg_apply]
  have h3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  have h4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  ring_nf
  simp only [Complex.I_sq, h3, h4]
  ring

/-- STUB LIN. Linearity of `toLinf` on the directions. -/
theorem s7g_c79_lin {κ l : ℂ → ℂ} (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior)
    (c ε : ℂ) : ε • toLinf κ + (c * ε) • toLinf l = ε • toLinf (fun z => κ z + c * l z) := by
  have e : (fun z => κ z + c * l z) = fun z => 1 * κ z + c * l z := funext fun z => by ring
  rw [e, s7g_c79_toLinf_lin hκ hl, smul_add, smul_smul, smul_smul, mul_one, mul_comm ε c]

/-- `G` only sees its input almost everywhere on `𝔻*`. -/
theorem s7g_c79_Gcongr {f g : ℂ → ℂ} (h : f =ᵐ[volume.restrict unitDiscExterior] g) :
    resolventStar f = resolventStar g := by
  funext z
  unfold resolventStar resolventOp
  refine integral_congr_ae ?_
  filter_upwards [h] with w hw
  rw [hw]

/-- Linearity of `G` at a point, for inputs with integrable kernel products. -/
theorem s7g_c79_G2 {f₁ f₂ : ℂ → ℂ} {z : ℂ}
    (h₁ : Integrable (fun w => (resolventKernel z w : ℂ) * f₁ w * rho w) (volume.restrict unitDiscExterior))
    (h₂ : Integrable (fun w => (resolventKernel z w : ℂ) * f₂ w * rho w) (volume.restrict unitDiscExterior))
    (a : ℂ) : resolventStar (fun w => f₁ w + a * f₂ w) z = resolventStar f₁ z + a * resolventStar f₂ z := by
  unfold resolventStar resolventOp
  rw [← integral_const_mul, ← integral_add h₁ (h₂.const_mul a)]
  congr 1
  funext w
  ring

/-- Linearity of `G` at a point, four inputs. -/
theorem s7g_c79_G4 {f₁ f₂ f₃ f₄ : ℂ → ℂ} {z : ℂ}
    (h₁ : Integrable (fun w => (resolventKernel z w : ℂ) * f₁ w * rho w) (volume.restrict unitDiscExterior))
    (h₂ : Integrable (fun w => (resolventKernel z w : ℂ) * f₂ w * rho w) (volume.restrict unitDiscExterior))
    (h₃ : Integrable (fun w => (resolventKernel z w : ℂ) * f₃ w * rho w) (volume.restrict unitDiscExterior))
    (h₄ : Integrable (fun w => (resolventKernel z w : ℂ) * f₄ w * rho w) (volume.restrict unitDiscExterior))
    (a b d : ℂ) :
    resolventStar (fun w => f₁ w + a * f₂ w + b * f₃ w + d * f₄ w) z =
      resolventStar f₁ z + a * resolventStar f₂ z + b * resolventStar f₃ z + d * resolventStar f₄ z := by
  have i12 : Integrable (fun w => (resolventKernel z w : ℂ) * (f₁ w + a * f₂ w) * rho w)
      (volume.restrict unitDiscExterior) :=
    (h₁.add (h₂.const_mul a)).congr (Eventually.of_forall fun w => by simp only [Pi.add_apply]; ring)
  have i123 : Integrable (fun w => (resolventKernel z w : ℂ) * (f₁ w + a * f₂ w + b * f₃ w) * rho w)
      (volume.restrict unitDiscExterior) :=
    (i12.add (h₃.const_mul b)).congr (Eventually.of_forall fun w => by simp only [Pi.add_apply]; ring)
  rw [s7g_c79_G2 i123 h₄ d, s7g_c79_G2 i12 h₃ b, s7g_c79_G2 h₁ h₂ a]

/-- Conjugate-linearity of the pairing in the second slot. -/
theorem s7g_c79_l2 {f u₁ u₂ : ℂ → ℂ}
    (h₁ : Integrable (fun z => f z * conj (u₁ z) * rho z) (volume.restrict unitDiscExterior))
    (h₂ : Integrable (fun z => f z * conj (u₂ z) * rho z) (volume.restrict unitDiscExterior)) (a : ℂ) :
    l2Inner f (fun z => u₁ z + a * u₂ z) = l2Inner f u₁ + conj a * l2Inner f u₂ := by
  unfold l2Inner
  rw [← integral_const_mul, ← integral_add h₁ (h₂.const_mul _)]
  congr 1
  funext z
  simp only [map_add, map_mul]
  ring

/-- Conjugate-linearity of the pairing in the second slot, four terms. -/
theorem s7g_c79_l4 {f u₁ u₂ u₃ u₄ : ℂ → ℂ}
    (h₁ : Integrable (fun z => f z * conj (u₁ z) * rho z) (volume.restrict unitDiscExterior))
    (h₂ : Integrable (fun z => f z * conj (u₂ z) * rho z) (volume.restrict unitDiscExterior))
    (h₃ : Integrable (fun z => f z * conj (u₃ z) * rho z) (volume.restrict unitDiscExterior))
    (h₄ : Integrable (fun z => f z * conj (u₄ z) * rho z) (volume.restrict unitDiscExterior)) (a b d : ℂ) :
    l2Inner f (fun z => u₁ z + a * u₂ z + b * u₃ z + d * u₄ z) =
      l2Inner f u₁ + conj a * l2Inner f u₂ + conj b * l2Inner f u₃ + conj d * l2Inner f u₄ := by
  have i12 : Integrable (fun z => f z * conj (u₁ z + a * u₂ z) * rho z) (volume.restrict unitDiscExterior) :=
    (h₁.add (h₂.const_mul (conj a))).congr (Eventually.of_forall fun z => by
      simp only [Pi.add_apply, map_add, map_mul]
      ring)
  have i123 : Integrable (fun z => f z * conj (u₁ z + a * u₂ z + b * u₃ z) * rho z)
      (volume.restrict unitDiscExterior) :=
    (i12.add (h₃.const_mul (conj b))).congr (Eventually.of_forall fun z => by
      simp only [Pi.add_apply, map_add, map_mul]
      ring)
  rw [s7g_c79_l2 i123 h₄ d, s7g_c79_l2 i12 h₃ b, s7g_c79_l2 h₁ h₂ a]

/-- STUB SES. The right side of `thm_7_7` along `κ + c l` is a Hermitian quadratic polynomial in `c` whose
`c̄`-coefficient is `B = (μ l̄, G(ν κ̄)) + (μ ν̄, G(κ̄ l))`. -/
theorem s7g_c79_ses {μ ν κ l : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior) :
    ∃ B' : ℂ, ∀ c : ℂ,
      l2Inner (fun z => μ z * conj (toLinf (fun z => κ z + c * l z) z))
          (resolventStar fun z => ν z * conj (toLinf (fun z => κ z + c * l z) z)) +
        l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖toLinf (fun z => κ z + c * l z) z‖ ^ 2 : ℝ)) =
      (l2Inner (fun z => μ z * conj (toLinf κ z)) (resolventStar fun z => ν z * conj (toLinf κ z)) +
          l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖toLinf κ z‖ ^ 2 : ℝ))) +
        conj c * (l2Inner (fun z => μ z * conj (l z)) (resolventStar fun z => ν z * conj (κ z)) +
          l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => conj (κ z) * l z)) +
        c * B' +
        c * conj c * (l2Inner (fun z => μ z * conj (toLinf l z)) (resolventStar fun z => ν z * conj (toLinf l z)) +
          l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖toLinf l z‖ ^ 2 : ℝ))) := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  have hKb := (hCc κ hκ).1
  have hLb := (hCc l hl).1
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have aeK := wp_harmonic_toLinf_ae hκ
  have aeL := wp_harmonic_toLinf_ae hl
  have pνK := s7pol_potential_data hν hKb
  have pνL := s7pol_potential_data hν hLb
  have pκK := s7pol_potential_data hκ hKb
  have pκL := s7pol_potential_data hκ hLb
  have plK := s7pol_potential_data hl hKb
  have plL := s7pol_potential_data hl hLb
  have aG : ∀ g : ℂ → ℂ, resolventStar g ∈ BCinf unitDiscExterior →
      AEStronglyMeasurable (resolventStar g) (volume.restrict unitDiscExterior) :=
    fun g h => h.1.continuousOn.aestronglyMeasurable hm
  have hμn : normL2 unitDiscExterior μ < ∞ := by
    obtain ⟨-, -, -, h⟩ := hμ
    exact h
  have aF : AEStronglyMeasurable (fun z => μ z * conj (ν z)) (volume.restrict unitDiscExterior) :=
    (s7pol_harmonic_measurable hμ).mul (Complex.continuous_conj.comp_aestronglyMeasurable
      (s7pol_harmonic_measurable hν))
  have hFn : normL2 unitDiscExterior (fun z => μ z * conj (ν z)) < ∞ := by
    refine s7ed_product_finite hμn (M := (Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior ν).toReal) ?_
    filter_upwards [ae_restrict_mem hm] with z hz
    exact wp_harmonic_pointwise_bound hν hz
  set K := toLinf κ with hKdef
  set L := toLinf l with hLdef
  refine ⟨l2Inner (fun z => μ z * conj (K z)) (resolventStar fun w => ν w * conj (L w)) +
    l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun w => κ w * conj (L w)), fun c => ?_⟩
  have hKc : toLinf (fun z => κ z + c * l z) = K + c • L := by
    rw [show (fun z => κ z + c * l z) = fun z => 1 * κ z + c * l z from funext fun z => by ring,
      s7g_c79_toLinf_lin hκ hl, one_smul]
  have aeKc : ∀ᵐ z ∂(volume.restrict unitDiscExterior), toLinf (fun z => κ z + c * l z) z = K z + c * L z := by
    rw [hKc]
    filter_upwards [Lp.coeFn_add K (c • L), Lp.coeFn_smul c L] with z h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  -- the first pairing
  have hT1 : l2Inner (fun z => μ z * conj (toLinf (fun z => κ z + c * l z) z))
      (resolventStar fun z => ν z * conj (toLinf (fun z => κ z + c * l z) z)) =
      l2Inner (fun z => μ z * conj (K z) + conj c * (μ z * conj (L z)))
        (fun z => resolventStar (fun w => ν w * conj (K w)) z + conj c * resolventStar (fun w => ν w * conj (L w)) z) := by
    apply s7pol_pair_congr
    · filter_upwards [aeKc] with z hz
      rw [hz, map_add, map_mul]
      ring
    · rw [s7g_c79_Gcongr (g := fun w => ν w * conj (K w) + conj c * (ν w * conj (L w))) (by
        filter_upwards [aeKc] with w hw
        rw [hw, map_add, map_mul]
        ring)]
      filter_upwards [ae_restrict_mem hm] with z hz
      exact s7g_c79_G2 (pνK.2.2 z hz) (pνL.2.2 z hz) _
  rw [hT1, s7pol_pair_comb (s7pol_forcing_measurable hμ K) (s7pol_forcing_measurable hμ L) (aG _ pνK.1) (aG _ pνL.1)
    (s7ed_forcing_finite hμ K) (s7ed_forcing_finite hμ L) pνK.2.1 pνL.2.1 (conj c)]
  -- the second pairing
  have hT2 : l2Inner (fun z => μ z * conj (ν z))
      (resolventStar fun z => ((‖toLinf (fun z => κ z + c * l z) z‖ ^ 2 : ℝ) : ℂ)) =
      l2Inner (fun z => μ z * conj (ν z)) (fun z => resolventStar (fun w => κ w * conj (K w)) z +
        conj c * resolventStar (fun w => κ w * conj (L w)) z + c * resolventStar (fun w => l w * conj (K w)) z +
        (c * conj c) * resolventStar (fun w => l w * conj (L w)) z) := by
    apply s7pol_pair_congr EventuallyEq.rfl
    rw [s7g_c79_Gcongr (g := fun w => κ w * conj (K w) + conj c * (κ w * conj (L w)) + c * (l w * conj (K w)) +
      (c * conj c) * (l w * conj (L w))) (by
        filter_upwards [aeKc, aeK, aeL] with w h1 h2 h3
        have e : ((‖K w + c * L w‖ ^ 2 : ℝ) : ℂ) = (K w + c * L w) * conj (K w + c * L w) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [h1, e, ← h2, ← h3, map_add, map_mul]
        ring)]
    filter_upwards [ae_restrict_mem hm] with z hz
    exact s7g_c79_G4 (pκK.2.2 z hz) (pκL.2.2 z hz) (plK.2.2 z hz) (plL.2.2 z hz) _ _ _
  rw [hT2, s7g_c79_l4 (s7pc_pairing_integrable aF (aG _ pκK.1) hFn pκK.2.1)
    (s7pc_pairing_integrable aF (aG _ pκL.1) hFn pκL.2.1) (s7pc_pairing_integrable aF (aG _ plK.1) hFn plK.2.1)
    (s7pc_pairing_integrable aF (aG _ plL.1) hFn plL.2.1)]
  -- identify the coefficients
  have hX1 : l2Inner (fun z => μ z * conj (L z)) (resolventStar fun w => ν w * conj (K w)) =
      l2Inner (fun z => μ z * conj (l z)) (resolventStar fun z => ν z * conj (κ z)) := by
    rw [s7g_c79_Gcongr (f := fun w => ν w * conj (K w)) (g := fun z => ν z * conj (κ z)) (by
      filter_upwards [aeK] with z hz
      rw [hz])]
    exact s7pol_pair_congr (by filter_upwards [aeL] with z hz; rw [hz]) EventuallyEq.rfl
  have hX2 : (resolventStar fun w => l w * conj (K w)) = resolventStar fun z => conj (κ z) * l z :=
    s7g_c79_Gcongr (by filter_upwards [aeK] with z hz; rw [hz, mul_comm])
  have h0 : (resolventStar fun z => ((‖K z‖ ^ 2 : ℝ) : ℂ)) = resolventStar fun w => κ w * conj (K w) :=
    s7g_c79_Gcongr (by
      filter_upwards [aeK] with z hz
      rw [← hz, Complex.mul_conj, Complex.normSq_eq_norm_sq])
  have h4 : (resolventStar fun z => ((‖L z‖ ^ 2 : ℝ) : ℂ)) = resolventStar fun w => l w * conj (L w) :=
    s7g_c79_Gcongr (by
      filter_upwards [aeL] with z hz
      rw [← hz, Complex.mul_conj, Complex.normSq_eq_norm_sq])
  rw [hX1, hX2, h0, h4]
  simp only [Complex.conj_conj, map_mul]
  ring

/-- The resolvent kernel is real: `\overline{G f} = G \bar f`. -/
theorem s7g_c79_rconj (f : ℂ → ℂ) (z : ℂ) :
    conj (resolventStar f z) = resolventStar (fun w => conj (f w)) z := by
  unfold resolventStar resolventOp
  rw [← integral_conj]
  congr 1
  funext w
  simp only [map_mul, Complex.conj_ofReal]

/-- STUB SYM. Self-adjointness of `G` on the pairing: `(μ ν̄, G(κ̄ l)) = (κ l̄, G(μ̄ ν))`. -/
theorem s7g_c79_sym {μ ν κ l : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior) :
    l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => conj (κ z) * l z) =
      l2Inner (fun z => κ z * conj (l z)) (resolventStar fun z => conj (μ z) * ν z) := by
  have hm : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have aμ := s7pol_harmonic_measurable hμ
  have aν := s7pol_harmonic_measurable hν
  have aκ := s7pol_harmonic_measurable hκ
  have al := s7pol_harmonic_measurable hl
  have hf : AEStronglyMeasurable (fun z => κ z * conj (l z)) (volume.restrict unitDiscExterior) :=
    aκ.mul (Complex.continuous_conj.comp_aestronglyMeasurable al)
  have hψ : AEStronglyMeasurable (fun z => μ z * conj (ν z)) (volume.restrict unitDiscExterior) :=
    aμ.mul (Complex.continuous_conj.comp_aestronglyMeasurable aν)
  have hb : ∀ w ∈ unitDiscExterior, ‖κ w * conj (l w)‖ ≤
      ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior κ).toReal) *
        ((Real.sqrt (12 / π) / 4) * (normL2 unitDiscExterior l).toReal) := by
    intro w hw
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (wp_harmonic_pointwise_bound hκ hw) (wp_harmonic_pointwise_bound hl hw) (norm_nonneg _)
      (by positivity)
  obtain ⟨-, -, -, hμn⟩ := hμ
  obtain ⟨-, -, -, hνn⟩ := hν
  have hψi : IntegrableOn (fun z => μ z * conj (ν z) * (rho z : ℂ)) unitDiscExterior :=
    s7pc_pairing_integrable aμ aν hμn hνn
  have hsw := resolvent_bilinear_swap (Or.inr rfl) hf hψ hb hψi
  have e1 : ∀ z, conj (resolventStar (fun z => conj (κ z) * l z) z) =
      resolventOp unitDiscExterior (fun z => κ z * conj (l z)) z := by
    intro z
    rw [s7g_c79_rconj]
    unfold resolventStar
    congr 1
    funext w
    simp only [map_mul, Complex.conj_conj]
  have e2 : ∀ z, conj (resolventStar (fun z => conj (μ z) * ν z) z) =
      resolventOp unitDiscExterior (fun z => μ z * conj (ν z)) z := by
    intro z
    rw [s7g_c79_rconj]
    unfold resolventStar
    congr 1
    funext w
    simp only [map_mul, Complex.conj_conj]
  unfold l2Inner
  calc (∫ z in unitDiscExterior, μ z * conj (ν z) * conj (resolventStar (fun z => conj (κ z) * l z) z) * rho z)
      = ∫ z in unitDiscExterior, resolventOp unitDiscExterior (fun z => κ z * conj (l z)) z *
          (μ z * conj (ν z)) * rho z := by
        congr 1
        funext z
        rw [e1 z]
        ring
    _ = ∫ w in unitDiscExterior, κ w * conj (l w) * resolventOp unitDiscExterior (fun z => μ z * conj (ν z)) w *
          rho w := hsw
    _ = _ := by
        congr 1
        funext z
        rw [e2 z]

/-- `cor_7_9`, assembled from the stubs and `thm_7_7`. -/
theorem s7g_cor_7_9 {κ l μ ν : ℂ → ℂ} (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior)
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    riemannR μ ν κ l =
      -l2Inner (fun z => κ z * conj (l z)) (resolventStar fun z => conj (μ z) * ν z) -
        l2Inner (fun z => conj (l z) * μ z) (resolventStar fun z => conj (κ z) * ν z) := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  obtain ⟨r, hr, hC⟩ := s7g_c79_C2 hμ hν hκ hl
  have hpol := s7g_c79_pol hr hC
  obtain ⟨B', hB'⟩ := s7g_c79_ses hμ hν hκ hl
  have hS : ∀ c : ℂ, dz (dzbar fun ε => gWP μ ν ((ε, c * ε).1 • toLinf κ + (ε, c * ε).2 • toLinf l)) 0 =
      l2Inner (fun z => μ z * conj (toLinf (fun z => κ z + c * l z) z))
          (resolventStar fun z => ν z * conj (toLinf (fun z => κ z + c * l z) z)) +
        l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖toLinf (fun z => κ z + c * l z) z‖ ^ 2 : ℝ)) := by
    intro c
    have hκc := s7pol_harmonic_add hκ (s7pol_harmonic_smul hl c)
    have e : (fun ε : ℂ => gWP μ ν ((ε, c * ε).1 • toLinf κ + (ε, c * ε).2 • toLinf l)) =
        fun ε => gWP μ ν (ε • toLinf (fun z => κ z + c * l z)) := funext fun ε => by
      simp only []
      rw [s7g_c79_lin hκ hl c ε]
    rw [e]
    exact thm_7_7 hμ hν (hCc _ hκc).1
  have hrie : riemannR μ ν κ l =
      -dz (fun e₁ => dzbar (fun e₂ => gWP μ ν ((e₁, e₂).1 • toLinf κ + (e₁, e₂).2 • toLinf l)) 0) 0 := rfl
  rw [hS, hS, hS, hS, hB', hB', hB', hB'] at hpol
  simp only [map_one, Complex.conj_I, map_neg] at hpol
  rw [hrie, ← s7g_c79_sym hμ hν hκ hl]
  have e2 : (fun z => conj (l z) * μ z) = fun z => μ z * conj (l z) := funext fun z => mul_comm _ _
  have e3 : (fun z => conj (κ z) * ν z) = fun z => ν z * conj (κ z) := funext fun z => mul_comm _ _
  rw [e2, e3]
  linear_combination (-1 / 4 : ℂ) * hpol +
    ((l2Inner (fun z => μ z * conj (l z)) (resolventStar fun z => ν z * conj (κ z)) +
      l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => conj (κ z) * l z)) / 2 - B' / 2) * Complex.I_sq

/-- **Corollary 7.9** (TT:2998–3010). At the origin of `T(1)`, for `κ, λ, μ, ν ∈ H^{-1,1}(𝔻*)`:
`R_{κ λ̄ μ ν̄} = -(κλ̄, G(μ̄ν)) - (λ̄μ, G(κ̄ν))`. For the basis: `R_{k l̄ m n̄} = -(μ_k μ̄_l, G(μ̄_m μ_n)) - (μ̄_l μ_m, G(μ̄_k μ_n))`. -/
theorem cor_7_9 {κ l μ ν : ℂ → ℂ} (hκ : κ ∈ harmonicL2 unitDiscExterior) (hl : l ∈ harmonicL2 unitDiscExterior)
    (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior) :
    riemannR μ ν κ l =
      -l2Inner (fun z => κ z * conj (l z)) (resolventStar fun z => conj (μ z) * ν z) -
        l2Inner (fun z => conj (l z) * μ z) (resolventStar fun z => conj (κ z) * ν z) := by
  exact s7g_cor_7_9 hκ hl hμ hν

end TakhtajanTeo
