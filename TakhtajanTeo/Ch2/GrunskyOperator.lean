import TakhtajanTeo.Ch2.S2_Grunsky
import TakhtajanTeo.Ch2.BergmanSeries
import TakhtajanTeo.Ch1.ResolventPlanarGreen

/-!
# Chapter 2, §2 — Grunsky operator foundation (lane 下属4)

Helper module. Imports point downward (`S2_Grunsky`, `Ch1.ResolventPlanarGreen`); no cycles.
Interface (stubs) frozen after the leader's audit:
* `faber_exists` (G0): Faber polynomials of a normalized disjoint pair;
* `isGrunskyCoeff_exists` (G1): clauses 1–2 of `grunsky_spec`;
* `green_exterior_image` (G2a): Green/area identity on `ℂ ∖ f(𝔻_ρ)`, proved with a smooth cutoff and
  `resolvent_green_disk`;
* `grunsky_B1_bound` (G2b): single-function Grunsky inequality, `ℓ²` form;
* `kerK1_opNorm_le` (G2c): operator form on `A₂¹(𝔻)`, the shape used by Appendix B (`kerOpNorm`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2


/-- Wirtinger chain rule for a holomorphic inner map: `∂_{z̄}(Ψ ∘ g) = (∂_{z̄}Ψ ∘ g) · conj g'`. -/
theorem g2_dzbar_comp {Ψ g : ℂ → ℂ} {z : ℂ} (hΨ : DifferentiableAt ℝ Ψ (g z))
    (hg : DifferentiableAt ℂ g z) :
    dzbar (fun w => Ψ (g w)) z = dzbar Ψ (g z) * conj (deriv g z) := by
  have hgR : DifferentiableAt ℝ g z := hg.restrictScalars ℝ
  have hfd : fderiv ℝ (fun w => Ψ (g w)) z = (fderiv ℝ Ψ (g z)).comp (fderiv ℝ g z) :=
    fderiv_comp z hΨ hgR
  have hgl : ∀ v : ℂ, fderiv ℝ g z v = deriv g z * v := by
    intro v
    have h := (hg.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
    rw [h]
    simp [mul_comm]
  set a := deriv g z with ha
  set L := fderiv ℝ Ψ (g z) with hL
  have e1 : fderiv ℝ (fun w => Ψ (g w)) z 1 = L a := by
    rw [hfd]; simp [hgl]
  have e2 : fderiv ℝ (fun w => Ψ (g w)) z I = L (a * I) := by
    rw [hfd]; simp [hgl]
  have hdec : ∀ v : ℂ, L v = (v.re : ℝ) • L 1 + (v.im : ℝ) • L I := by
    intro v
    conv_lhs => rw [show v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I by
      apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  simp only [dzbar, e1, e2]
  rw [hdec a, hdec (a * I)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

/-- Green's identity on the whole plane for a `C¹` function whose `∂_{z̄}` is integrable and whose circle
integrals tend to `0`. -/
theorem g2_green_global {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hint : Integrable (dzbar Φ))
    (hbd : Tendsto (fun R : ℝ => ∮ z in C(0, R), Φ z) atTop (𝓝 0)) : ∫ w, dzbar Φ w = 0 := by
  have hlim : Tendsto (fun R : ℝ => ∫ w in ball (0 : ℂ) R, dzbar Φ w) atTop (𝓝 (∫ w, dzbar Φ w)) := by
    have := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun R w => (ball (0 : ℂ) R).indicator (dzbar Φ) w) (f := dzbar Φ)
      (bound := fun w => ‖dzbar Φ w‖)
      (Eventually.of_forall fun R => hint.aestronglyMeasurable.indicator measurableSet_ball)
      (Eventually.of_forall fun R => Eventually.of_forall fun w => norm_indicator_le_norm_self _ _)
      hint.norm
      (Eventually.of_forall fun w => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop ‖w‖] with R hR
        rw [indicator_of_mem (by simpa using hR)])
    simpa [integral_indicator measurableSet_ball] using this
  have heq : ∀ R : ℝ, 0 ≤ R → ∮ z in C(0, R), Φ z = 2 * I * ∫ w in ball (0 : ℂ) R, dzbar Φ w :=
    fun R hR => green_disc_dzbar hΦ 0 hR
  have h2 : Tendsto (fun R : ℝ => 2 * I * ∫ w in ball (0 : ℂ) R, dzbar Φ w) atTop (𝓝 0) := by
    refine hbd.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact heq R hR
  have h3 : Tendsto (fun R : ℝ => 2 * I * ∫ w in ball (0 : ℂ) R, dzbar Φ w) atTop
      (𝓝 (2 * I * ∫ w, dzbar Φ w)) := hlim.const_mul _
  have := tendsto_nhds_unique h3 h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (by simp)
  · exact h

/-- A function holomorphic off `0` with `h' = O(w⁻²)` at `∞` is bounded near `∞`. -/
theorem g2_bdd_infty {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h {0}ᶜ) {C R : ℝ}
    (hC : ∀ w : ℂ, R < ‖w‖ → ‖deriv h w‖ ≤ C / ‖w‖ ^ 2) :
    ∃ M R' : ℝ, 0 < R' ∧ ∀ w : ℂ, R' < ‖w‖ → ‖h w‖ ≤ M := by
  set R1 : ℝ := max R 1 with hR1
  have hR1pos : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε : ℝ := 1 / R1 with hε
  have hεpos : 0 < ε := by positivity
  set r0 : ℝ := ε / 2 with hr0
  have hr0pos : 0 < r0 := by positivity
  let k : ℂ → ℂ := fun s => h s⁻¹
  have hkd : ∀ s : ℂ, s ≠ 0 → HasDerivAt k (deriv h s⁻¹ * (-(s ^ 2)⁻¹)) s := by
    intro s hs0
    have hsi : s⁻¹ ≠ 0 := inv_ne_zero hs0
    have hat : DifferentiableAt ℂ h s⁻¹ :=
      hh.differentiableAt (isOpen_compl_singleton.mem_nhds hsi)
    have := hat.hasDerivAt.scomp s (hasDerivAt_inv hs0)
    exact this.congr_deriv (by rw [smul_eq_mul, mul_comm])
  have hkb : ∀ s : ℂ, s ≠ 0 → ‖s‖ < ε → ‖deriv h s⁻¹ * (-(s ^ 2)⁻¹)‖ ≤ C := by
    intro s hs0 hsε
    have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have hbig : R < ‖s⁻¹‖ := by
      rw [norm_inv]
      have : R1 < ‖s‖⁻¹ := by
        rw [hε] at hsε
        rw [lt_inv_comm₀ hR1pos hspos]
        simpa [one_div] using hsε
      exact lt_of_le_of_lt (le_max_left _ _) this
    have h1 := hC s⁻¹ hbig
    rw [norm_inv] at h1
    rw [norm_mul, norm_neg, norm_inv, norm_pow]
    calc ‖deriv h s⁻¹‖ * (‖s‖ ^ 2)⁻¹ ≤ (C / (‖s‖⁻¹) ^ 2) * (‖s‖ ^ 2)⁻¹ := by
          gcongr
      _ = C := by field_simp
  -- bound on the reference circle
  have hkc : ContinuousOn k (sphere (0 : ℂ) r0) := by
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0] at hs; simp at hs; linarith
    exact (hkd s hs0).continuousAt.continuousWithinAt
  obtain ⟨M0, hM0⟩ := (isCompact_sphere (0 : ℂ) r0).exists_bound_of_continuousOn hkc
  refine ⟨|M0| + 2 * C * ε + 1, R1, hR1pos, ?_⟩
  intro w hw
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0] at hw; simp at hw; linarith
  set s : ℂ := w⁻¹ with hs
  have hs0 : s ≠ 0 := inv_ne_zero hw0
  have hsn : ‖s‖ < ε := by
    rw [hs, norm_inv, hε, one_div, inv_lt_inv₀ (by linarith) hR1pos]
    exact hw
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set s0 : ℂ := ((r0 / ‖s‖ : ℝ) : ℂ) * s with hs0def
  have hs0n : ‖s0‖ = r0 := by
    rw [hs0def, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hs0mem : s0 ∈ sphere (0 : ℂ) r0 := by simpa using hs0n
  have hseg : ∀ x ∈ segment ℝ s s0, x ≠ 0 ∧ ‖x‖ < ε := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    have hform : a • s + b • s0 = (((a + b * (r0 / ‖s‖) : ℝ)) : ℂ) * s := by
      rw [hs0def]
      simp only [Complex.real_smul]
      push_cast
      ring
    have hcoef : 0 < a + b * (r0 / ‖s‖) := by
      rcases ha.eq_or_lt with h | h
      · have : b = 1 := by linarith
        rw [← h, this]; positivity
      · have : 0 ≤ b * (r0 / ‖s‖) := by positivity
        linarith
    rw [hform]
    refine ⟨mul_ne_zero (by exact_mod_cast hcoef.ne') hs0, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoef.le]
    have : a + b * (r0 / ‖s‖) ≤ max 1 (r0 / ‖s‖) := by
      have h1 : a + b * (r0 / ‖s‖) ≤ a * max 1 (r0 / ‖s‖) + b * max 1 (r0 / ‖s‖) :=
        add_le_add (le_mul_of_one_le_right ha (le_max_left _ _))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      calc a + b * (r0 / ‖s‖) ≤ a * max 1 (r0 / ‖s‖) + b * max 1 (r0 / ‖s‖) := h1
        _ = max 1 (r0 / ‖s‖) := by rw [← add_mul, hab, one_mul]
    calc (a + b * (r0 / ‖s‖)) * ‖s‖ ≤ max 1 (r0 / ‖s‖) * ‖s‖ := by gcongr
      _ < ε := by
        rcases le_total 1 (r0 / ‖s‖) with h | h
        · rw [max_eq_right h, div_mul_cancel₀ _ hspos.ne']; linarith
        · rw [max_eq_left h, one_mul]; exact hsn
  have hlip : ‖k s - k s0‖ ≤ C * ‖s - s0‖ := by
    apply (convex_segment s s0).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun x => deriv h x⁻¹ * (-(x ^ 2)⁻¹))
    · intro x hx
      exact (hkd x (hseg x hx).1).hasDerivWithinAt
    · intro x hx
      exact hkb x (hseg x hx).1 (hseg x hx).2
    · exact right_mem_segment ℝ s s0
    · exact left_mem_segment ℝ s s0
  have hCnn : 0 ≤ C := by
    have := hkb s hs0 hsn
    exact (norm_nonneg _).trans this
  have hdist : ‖s - s0‖ ≤ 2 * ε := by
    calc ‖s - s0‖ ≤ ‖s‖ + ‖s0‖ := norm_sub_le _ _
      _ ≤ ε + ε := by rw [hs0n]; linarith
      _ = 2 * ε := by ring
  have hkw : h w = k s := by simp [k, hs]
  rw [hkw]
  calc ‖k s‖ ≤ ‖k s0‖ + ‖k s - k s0‖ := by simpa using norm_add_le (k s0) (k s - k s0)
    _ ≤ |M0| + C * (2 * ε) := by
        have h1 := hM0 s0 hs0mem
        have h2 : ‖k s - k s0‖ ≤ C * (2 * ε) := hlip.trans (by gcongr)
        have h3 : ‖k s0‖ ≤ |M0| := h1.trans (le_abs_self _)
        linarith
    _ ≤ |M0| + 2 * C * ε + 1 := by nlinarith

/-- The circle integrals of `conj h · h'` tend to `0`. -/
theorem g2_circle_tendsto {Φ h : ℂ → ℂ} (hh : DifferentiableOn ℂ h {0}ᶜ) {C R R0 : ℝ}
    (hC : ∀ w : ℂ, R < ‖w‖ → ‖deriv h w‖ ≤ C / ‖w‖ ^ 2)
    (hΦ : ∀ w : ℂ, R0 < ‖w‖ → Φ w = conj (h w) * deriv h w) :
    Tendsto (fun r : ℝ => ∮ z in C(0, r), Φ z) atTop (𝓝 0) := by
  obtain ⟨M, R', hR'pos, hM⟩ := g2_bdd_infty hh hC
  have hM0 : 0 ≤ M := by
    have := hM ((R' + 1 : ℝ) : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith)
    exact (norm_nonneg _).trans this
  set T : ℝ := max (max R R0) R' + 1 with hT
  have hTpos : 0 < T := by
    have := le_max_right (max R R0) R'
    have h2 : 0 < R' := hR'pos
    linarith
  have hbound : ∀ᶠ r : ℝ in atTop, ‖∮ z in C(0, r), Φ z‖ ≤ 2 * π * M * (|C| : ℝ) / r := by
    filter_upwards [eventually_ge_atTop T] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le hTpos hr
    have hRr : R < r := by
      have := le_max_left R R0; have := le_max_left (max R R0) R'; linarith
    have hR0r : R0 < r := by
      have := le_max_right R R0; have := le_max_left (max R R0) R'; linarith
    have hR'r : R' < r := by
      have := le_max_right (max R R0) R'; linarith
    have hcirc : ∀ z ∈ sphere (0 : ℂ) r, ‖Φ z‖ ≤ M * (|C| / r ^ 2) := by
      intro z hz
      have hzn : ‖z‖ = r := by simpa using hz
      rw [hΦ z (by rw [hzn]; exact hR0r), norm_mul, Complex.norm_conj]
      have h1 := hM z (by rw [hzn]; exact hR'r)
      have h2 := hC z (by rw [hzn]; exact hRr)
      rw [hzn] at h2
      calc ‖h z‖ * ‖deriv h z‖ ≤ M * (C / r ^ 2) := mul_le_mul h1 h2 (norm_nonneg _) hM0
        _ ≤ M * (|C| / r ^ 2) := by gcongr; exact le_abs_self C
    have := circleIntegral.norm_integral_le_of_norm_le_const hrpos.le hcirc
    calc ‖∮ z in C(0, r), Φ z‖ ≤ 2 * π * r * (M * (|C| / r ^ 2)) := this
      _ = 2 * π * M * |C| / r := by field_simp
  have hlim : Tendsto (fun r : ℝ => 2 * π * M * (|C| : ℝ) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero_norm' hbound hlim

/-- `∂_{z̄}(conj h · h') = |h'|²` at points where `h` is holomorphic. -/
theorem g2_dzbar_conj_mul {h : ℂ → ℂ} {w : ℂ} (hh : DifferentiableAt ℂ h w)
    (hh' : DifferentiableAt ℂ (deriv h) w) :
    dzbar (fun u => conj (h u) * deriv h u) w = ((‖deriv h w‖ ^ 2 : ℝ) : ℂ) := by
  have hhR : DifferentiableAt ℝ h w := hh.restrictScalars ℝ
  have hcR : DifferentiableAt ℝ (fun u => conj (h u)) w :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp w hhR
  have hdR : DifferentiableAt ℝ (deriv h) w := hh'.restrictScalars ℝ
  rw [dzbar_mul hcR hdR, (cauchyRiemann_iff.1 hh').2, ← (eq6_3 hhR).1, dz_eq_deriv hh]
  rw [mul_zero, zero_add, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Integrability of a continuous function that is `O(‖w‖⁻⁴)` at infinity. -/
theorem g2_integrable_of_decay {F : ℂ → ℂ} (hF : Continuous F) {K R : ℝ}
    (hb : ∀ w : ℂ, R < ‖w‖ → ‖F w‖ ≤ K / ‖w‖ ^ 4) : Integrable F := by
  set R1 : ℝ := max R 1 with hR1
  have hR1pos : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hin : IntegrableOn F (closedBall (0 : ℂ) R1) volume :=
    hF.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hout : IntegrableOn F (closedBall (0 : ℂ) R1)ᶜ volume := by
    have hg : Integrable (fun w : ℂ => (1 + ‖w‖) ^ (-(4 : ℝ))) volume :=
      integrable_one_add_norm (by simp [Complex.finrank_real_complex]; norm_num)
    refine (hg.integrableOn.const_mul (16 * |K|)).mono' hF.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' (measurableSet_closedBall.compl)]
    refine Eventually.of_forall fun w hw => ?_
    have hwn : R1 < ‖w‖ := by simpa using hw
    have hwpos : 0 < ‖w‖ := lt_trans hR1pos hwn
    have h1 := hb w (lt_of_le_of_lt (le_max_left _ _) hwn)
    have h2 : (1 + ‖w‖) ≤ 2 * ‖w‖ := by
      have : 1 ≤ ‖w‖ := le_trans (le_max_right _ _) hwn.le
      linarith
    have h4 : (1 + ‖w‖) ^ 4 ≤ 16 * ‖w‖ ^ 4 := by
      calc (1 + ‖w‖) ^ 4 ≤ (2 * ‖w‖) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
        _ = 16 * ‖w‖ ^ 4 := by ring
    have hpos4 : 0 < (1 + ‖w‖) ^ 4 := by positivity
    have hrp : (1 + ‖w‖) ^ (-(4 : ℝ)) = ((1 + ‖w‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [hrp]
    have hw4 : 0 < ‖w‖ ^ 4 := by positivity
    calc ‖F w‖ ≤ K / ‖w‖ ^ 4 := h1
      _ ≤ |K| / ‖w‖ ^ 4 := by gcongr; exact le_abs_self K
      _ ≤ 16 * |K| * ((1 + ‖w‖) ^ 4)⁻¹ := by
        rw [div_le_iff₀ hw4]
        have h5 : 1 ≤ 16 * ‖w‖ ^ 4 / (1 + ‖w‖) ^ 4 := by
          rw [le_div_iff₀ hpos4]; linarith [h4]
        calc |K| = |K| * 1 := by ring
          _ ≤ |K| * (16 * ‖w‖ ^ 4 / (1 + ‖w‖) ^ 4) := by gcongr
          _ = 16 * |K| * ((1 + ‖w‖) ^ 4)⁻¹ * ‖w‖ ^ 4 := by field_simp
  have := hin.union hout
  rwa [union_compl_self, integrableOn_univ] at this

/-- A smooth radial cutoff `0` on `‖z‖ ≤ ρ/2` and `1` on `‖z‖ ≥ ρ`. -/
theorem g2_cut {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∃ c : ℂ → ℂ, ContDiff ℝ 1 c ∧ (∀ z : ℂ, ‖z‖ ≤ ρ / 2 → c z = 0) ∧ (∀ z : ℂ, ρ ≤ ‖z‖ → c z = 1) := by
  have hden : 0 < ρ ^ 2 - (ρ / 2) ^ 2 := by nlinarith
  refine ⟨fun z => ((Real.smoothTransition ((‖z‖ ^ 2 - (ρ / 2) ^ 2) / (ρ ^ 2 - (ρ / 2) ^ 2)) : ℝ) : ℂ),
    ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 1 (fun z : ℂ => (‖z‖ ^ 2 - (ρ / 2) ^ 2) / (ρ ^ 2 - (ρ / 2) ^ 2)) :=
      (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _)
    exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp h1)
  · intro z hz
    have : ‖z‖ ^ 2 - (ρ / 2) ^ 2 ≤ 0 := by nlinarith [norm_nonneg z]
    show ((Real.smoothTransition ((‖z‖ ^ 2 - (ρ / 2) ^ 2) / (ρ ^ 2 - (ρ / 2) ^ 2)) : ℝ) : ℂ) = 0
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg this hden.le)]
    simp
  · intro z hz
    have : ρ ^ 2 - (ρ / 2) ^ 2 ≤ ‖z‖ ^ 2 - (ρ / 2) ^ 2 := by nlinarith [norm_nonneg z]
    show ((Real.smoothTransition ((‖z‖ ^ 2 - (ρ / 2) ^ 2) / (ρ ^ 2 - (ρ / 2) ^ 2)) : ℝ) : ℂ) = 1
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hden).mpr this)]
    simp

/-- (G2a) Green identity on the exterior of `f(𝔻_ρ)` for `h` holomorphic off `0` with `h' = O(w⁻²)` at `∞`:
`∬_{ℂ ∖ f(𝔻_ρ)} |h'|² = -½ ∫₀^{2π} conj(H) H' ρe^{iθ} dθ`, `H = h ∘ f` on `|z| = ρ` (the boundary term
`-(1/2i) ∮ h̄ dh` pulled back by `f`). -/
theorem green_exterior_image {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h {0}ᶜ) (hdecay : ∃ C R : ℝ, ∀ w : ℂ, R < ‖w‖ → ‖deriv h w‖ ≤ C / ‖w‖ ^ 2) :
    (((∫ w in (f '' closedBall (0 : ℂ) ρ)ᶜ, ‖deriv h w‖ ^ 2 : ℝ)) : ℂ) =
      -(1 / 2 : ℂ) * ∫ θ in (0 : ℝ)..2 * π,
        conj (h (f (circleMap 0 ρ θ))) * deriv (fun z => h (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
  obtain ⟨C, R, hC⟩ := hdecay
  have hUo : IsOpen unitDisc := isOpen_ball
  have hcbD : closedBall (0 : ℂ) ρ ⊆ unitDisc := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ1)
  have hbD : ball (0 : ℂ) ρ ⊆ unitDisc := ball_subset_closedBall.trans hcbD
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- injectivity and openness
  have hne : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hUo hf hi hz
  have hfz0 : ∀ z ∈ unitDisc, z ≠ 0 → f z ≠ 0 := by
    intro z hz hz0 h0
    exact hz0 (hi hz h0D (by rw [h0, hf0]))
  have hfD := RMT.differentiableOn_invFunOn_of_injOn hUo hf hi
  have hfDopen : IsOpen (f '' unitDisc) := hfD.1
  set finv := Function.invFunOn f unitDisc with hfinv
  have hleft : ∀ z ∈ unitDisc, finv (f z) = z := fun z hz => hi.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ f '' unitDisc, f (finv w) = w := fun w hw =>
    Function.invFunOn_eq (by simpa using hw)
  have hfinvD : ∀ w ∈ f '' unitDisc, finv w ∈ unitDisc := fun w hw =>
    Function.invFunOn_mem (by simpa using hw)
  -- the cutoff
  obtain ⟨c, hcs, hc0, hc1⟩ := g2_cut hρ0
  -- smoothness of h and h'
  have hh' : DifferentiableOn ℂ (deriv h) {0}ᶜ := hh.deriv isOpen_compl_singleton
  have hhs : ContDiffOn ℝ 1 h {0}ᶜ :=
    (hh.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hhs' : ContDiffOn ℝ 1 (deriv h) {0}ᶜ :=
    (hh'.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ
  have hphis : ContDiffOn ℝ 1 (fun w => conj (h w) * deriv h w) {0}ᶜ :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hhs).mul hhs'
  -- Ψ on the disk
  have hW : IsOpen (unitDisc \ {0}) := hUo.sdiff isClosed_singleton
  have hHd : DifferentiableOn ℂ (fun u => h (f u)) (unitDisc \ {0}) := by
    intro z hz
    have h1 : DifferentiableAt ℂ h (f z) :=
      hh.differentiableAt (isOpen_compl_singleton.mem_nhds (hfz0 z hz.1 hz.2))
    exact (h1.comp z (hf.differentiableAt (hUo.mem_nhds hz.1))).differentiableWithinAt
  have hHs : ContDiffOn ℝ 1 (fun u => h (f u)) (unitDisc \ {0}) :=
    (hHd.contDiffOn hW).restrict_scalars ℝ
  have hHs' : ContDiffOn ℝ 1 (deriv (fun u => h (f u))) (unitDisc \ {0}) :=
    ((hHd.deriv hW).contDiffOn hW).restrict_scalars ℝ
  let Ψ : ℂ → ℂ := fun z => c z * (conj (h (f z)) * deriv (fun u => h (f u)) z)
  have hΨs : ContDiffOn ℝ 1 Ψ unitDisc := by
    have hA : ContDiffOn ℝ 1 Ψ (unitDisc \ {0}) :=
      hcs.contDiffOn.mul (((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hHs).mul hHs')
    have hB : ContDiffOn ℝ 1 Ψ (ball (0 : ℂ) (ρ / 2)) := by
      refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
      intro z hz
      simp [Ψ, hc0 z (mem_ball_zero_iff.mp hz).le]
    have hU := hA.union_of_isOpen hB hW isOpen_ball
    refine hU.mono ?_
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inr (by simp [hz0]; positivity)
    · exact Or.inl ⟨hz, hz0⟩
  -- Φ on the plane
  let χ : ℂ → ℂ := fun w => if w ∈ f '' ball (0 : ℂ) ρ then c (finv w) else 1
  let Φ : ℂ → ℂ := fun w => χ w * (conj (h w) * deriv h w)
  have hballopen : ∀ r : ℝ, r ≤ 1 → IsOpen (f '' ball (0 : ℂ) r) := fun r hr =>
    (RMT.differentiableOn_invFunOn_of_injOn isOpen_ball (hf.mono (ball_subset_ball hr))
      (hi.mono (ball_subset_ball hr))).1
  have hKcompact : IsCompact (f '' closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall (0 : ℂ) ρ).image_of_continuousOn (hf.continuousOn.mono hcbD)
  have hKclosed : IsClosed (f '' closedBall (0 : ℂ) ρ) := hKcompact.isClosed
  have hKsubD : f '' closedBall (0 : ℂ) ρ ⊆ f '' unitDisc := image_mono hcbD
  have hballsub : f '' ball (0 : ℂ) ρ ⊆ f '' closedBall (0 : ℂ) ρ := image_mono ball_subset_closedBall
  have hχD : ∀ w ∈ f '' unitDisc, χ w = c (finv w) := by
    rintro w ⟨z, hz, rfl⟩
    simp only [χ]
    split_ifs with hm
    · rfl
    · have : ρ ≤ ‖z‖ := by
        by_contra hlt
        push_neg at hlt
        exact hm ⟨z, mem_ball_zero_iff.mpr hlt, rfl⟩
      rw [hleft z hz, hc1 z this]
  have hA1 : IsOpen (f '' ball (0 : ℂ) (ρ / 2)) := hballopen (ρ / 2) (by linarith)
  have hA2 : IsOpen (f '' unitDisc ∩ {0}ᶜ) := hfDopen.inter isOpen_compl_singleton
  have hA3 : IsOpen (f '' closedBall (0 : ℂ) ρ)ᶜ := hKclosed.isOpen_compl
  have h0K : (0 : ℂ) ∈ f '' closedBall (0 : ℂ) ρ := ⟨0, by simp [hρ0.le], hf0⟩
  have hP1 : ContDiffOn ℝ 1 Φ (f '' ball (0 : ℂ) (ρ / 2)) := by
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    rintro w ⟨z, hz, rfl⟩
    have hzn : ‖z‖ < ρ / 2 := mem_ball_zero_iff.mp hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
    simp only [Φ]
    rw [hχD _ ⟨z, hzD, rfl⟩, hleft z hzD, hc0 z hzn.le, zero_mul]
  have hphisub : ∀ s : Set ℂ, s ⊆ {0}ᶜ → ContDiffOn ℝ 1 (fun w => conj (h w) * deriv h w) s :=
    fun s hs => hphis.mono hs
  have hP2 : ContDiffOn ℝ 1 Φ (f '' unitDisc ∩ {0}ᶜ) := by
    have hfinvs : ContDiffOn ℝ 1 finv (f '' unitDisc) :=
      (hfD.2.contDiffOn hfDopen).restrict_scalars ℝ
    have hcf : ContDiffOn ℝ 1 (fun w => c (finv w)) (f '' unitDisc) := hcs.comp_contDiffOn hfinvs
    refine ((hcf.mono inter_subset_left).mul (hphisub _ inter_subset_right)).congr ?_
    intro w hw
    simp only [Φ]
    rw [hχD w hw.1]
  have hP3 : ContDiffOn ℝ 1 Φ (f '' closedBall (0 : ℂ) ρ)ᶜ := by
    have hsub : (f '' closedBall (0 : ℂ) ρ)ᶜ ⊆ {0}ᶜ := by
      intro w hw h0
      exact hw (by rw [mem_singleton_iff.mp h0]; exact h0K)
    refine (hphisub _ hsub).congr ?_
    intro w hw
    have : w ∉ f '' ball (0 : ℂ) ρ := fun hm => hw (hballsub hm)
    simp only [Φ, χ, if_neg this, one_mul]
  have hΦ : ContDiff ℝ 1 Φ := by
    have hU := ((hP1.union_of_isOpen hP2 hA1 hA2).union_of_isOpen hP3 (hA1.union hA2) hA3)
    refine contDiffOn_univ.mp (hU.mono ?_)
    intro w _
    by_cases hw3 : w ∈ (f '' closedBall (0 : ℂ) ρ)ᶜ
    · exact Or.inr hw3
    · have hwK : w ∈ f '' closedBall (0 : ℂ) ρ := not_not.mp hw3
      by_cases hw0 : w = 0
      · refine Or.inl (Or.inl ?_)
        exact ⟨0, by simp [hρ0], by rw [hw0, hf0]⟩
      · exact Or.inl (Or.inr ⟨hKsubD hwK, hw0⟩)
  -- the exterior region
  obtain ⟨R0, hR0⟩ := hKcompact.isBounded.subset_closedBall (0 : ℂ)
  have hΦout : ∀ w : ℂ, R0 < ‖w‖ → Φ w = conj (h w) * deriv h w := by
    intro w hw
    have hwK : w ∉ f '' closedBall (0 : ℂ) ρ := fun hm => by
      have := mem_closedBall_zero_iff.mp (hR0 hm)
      linarith
    have : w ∉ f '' ball (0 : ℂ) ρ := fun hm => hwK (hballsub hm)
    simp only [Φ, χ, if_neg this, one_mul]
  have hdz_out : ∀ w ∈ (f '' closedBall (0 : ℂ) ρ)ᶜ,
      dzbar Φ w = ((‖deriv h w‖ ^ 2 : ℝ) : ℂ) := by
    intro w hw
    have hsub : w ≠ 0 := fun h0 => hw (by rw [h0]; exact h0K)
    have hev : Φ =ᶠ[𝓝 w] fun u => conj (h u) * deriv h u := by
      filter_upwards [hA3.mem_nhds hw] with u hu
      have : u ∉ f '' ball (0 : ℂ) ρ := fun hm => hu (hballsub hm)
      simp only [Φ, χ, if_neg this, one_mul]
    rw [dzbar_congr_of_eventuallyEq hev]
    exact g2_dzbar_conj_mul (hh.differentiableAt (isOpen_compl_singleton.mem_nhds hsub))
      (hh'.differentiableAt (isOpen_compl_singleton.mem_nhds hsub))
  have hint : Integrable (dzbar Φ) := by
    refine g2_integrable_of_decay (continuous_dzbar hΦ) (K := C ^ 2) (R := max R R0) ?_
    intro w hw
    have hwR : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
    have hwR0 : R0 < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hw
    have hwK : w ∈ (f '' closedBall (0 : ℂ) ρ)ᶜ := fun hm => by
      have := mem_closedBall_zero_iff.mp (hR0 hm)
      linarith
    rw [hdz_out w hwK, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := hC w hwR
    calc ‖deriv h w‖ ^ 2 ≤ (C / ‖w‖ ^ 2) ^ 2 := by gcongr
      _ = C ^ 2 / ‖w‖ ^ 4 := by ring
  have hglob : ∫ w, dzbar Φ w = 0 :=
    g2_green_global hΦ hint (g2_circle_tendsto hh hC (fun w hw => hΦout w hw))
  have hsplit := integral_add_compl hKclosed.measurableSet hint
  have hcompl : ∫ x in (f '' closedBall (0 : ℂ) ρ)ᶜ, dzbar Φ x =
      (((∫ w in (f '' closedBall (0 : ℂ) ρ)ᶜ, ‖deriv h w‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun hKclosed.measurableSet.compl (fun w hw => hdz_out w hw)
  -- change of variables on the closed disk
  have hΨeq : ∀ u ∈ unitDisc, Ψ u = Φ (f u) * deriv f u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      have h1 : Ψ 0 = 0 := by simp [Ψ, hc0 0 (by simp; positivity)]
      have h2 : Φ (f 0) = 0 := by
        simp only [Φ]
        rw [hχD _ ⟨0, hu, rfl⟩, hleft 0 hu, hc0 0 (by simp; positivity), zero_mul]
      rw [h1, h2, zero_mul]
    · have hfu : DifferentiableAt ℂ h (f u) :=
        hh.differentiableAt (isOpen_compl_singleton.mem_nhds (hfz0 u hu hu0))
      have hfd : DifferentiableAt ℂ f u := hf.differentiableAt (hUo.mem_nhds hu)
      have hchain : deriv (fun v => h (f v)) u = deriv h (f u) * deriv f u := deriv_comp u hfu hfd
      simp only [Ψ, Φ]
      rw [hχD _ ⟨u, hu, rfl⟩, hleft u hu, hchain]
      ring
  have hpt : ∀ z ∈ closedBall (0 : ℂ) ρ, |(fderiv ℝ f z).det| • dzbar Φ (f z) = dzbar Ψ z := by
    intro z hz
    have hzD := hcbD hz
    have hfC : DifferentiableAt ℂ f z := hf.differentiableAt (hUo.mem_nhds hzD)
    have hfR : DifferentiableAt ℝ f z := hfC.restrictScalars ℝ
    have hdet : (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
      have h1 := det_fderiv_eq_jacobian hfR
      rw [jacobian, (cauchyRiemann_iff.1 hfC).2, dz_eq_deriv hfC, norm_zero] at h1
      rw [ContinuousLinearMap.det, h1]
      ring
    have hev : Ψ =ᶠ[𝓝 z] fun u => Φ (f u) * deriv f u := by
      filter_upwards [hUo.mem_nhds hzD] with u hu using hΨeq u hu
    have hd' : DifferentiableAt ℂ (deriv f) z :=
      (hf.deriv hUo).differentiableAt (hUo.mem_nhds hzD)
    have hΦR : DifferentiableAt ℝ Φ (f z) := (hΦ.differentiable one_ne_zero).differentiableAt
    have hcomp : DifferentiableAt ℝ (fun u => Φ (f u)) z := hΦR.comp z hfR
    rw [dzbar_congr_of_eventuallyEq hev, dzbar_mul hcomp (hd'.restrictScalars ℝ),
      (cauchyRiemann_iff.1 hd').2, g2_dzbar_comp hΦR hfC, hdet,
      abs_of_nonneg (by positivity), Complex.real_smul, mul_zero, zero_add,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_closedBall (x := (0 : ℂ)) (ε := ρ)) (f' := fun x => fderiv ℝ f x)
    (fun x hx => ((hf.differentiableAt (hUo.mem_nhds (hcbD hx))).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt)
    (hi.mono hcbD) (dzbar Φ)
  have hKint : ∫ x in f '' closedBall (0 : ℂ) ρ, dzbar Φ x = ∫ z in closedBall (0 : ℂ) ρ, dzbar Ψ z := by
    rw [hcov]
    exact setIntegral_congr_fun measurableSet_closedBall (fun z hz => hpt z hz)
  have hsph : volume (sphere (0 : ℂ) ρ) = 0 := Measure.addHaar_sphere volume 0 ρ
  have hae : ball (0 : ℂ) ρ =ᵐ[volume] closedBall (0 : ℂ) ρ := by
    rw [← ball_union_sphere]
    exact (union_ae_eq_left_iff_ae_subset.mpr (ae_le_set.mpr (measure_mono_null diff_subset hsph))).symm
  have hball : ∫ z in closedBall (0 : ℂ) ρ, dzbar Ψ z = ∫ z in ball (0 : ℂ) ρ, dzbar Ψ z :=
    (setIntegral_congr_set hae).symm
  have hgreen := green_disc_dzbar_of_contDiffOn hUo hΨs (0 : ℂ) hρ0.le hcbD
  have hcirc : ∮ z in C(0, ρ), Ψ z = I * ∫ θ in (0 : ℝ)..2 * π,
      conj (h (f (circleMap 0 ρ θ))) * deriv (fun z => h (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [smul_eq_mul, Ψ]
    rw [deriv_circleMap, hc1 _ (by rw [norm_circleMap_zero, abs_of_pos hρ0])]
    ring
  rw [hKint, hball, hcompl, hglob] at hsplit
  set A : ℂ := ∫ θ in (0 : ℝ)..2 * π,
      conj (h (f (circleMap 0 ρ θ))) * deriv (fun z => h (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ with hA
  set B : ℂ := ∫ z in ball (0 : ℂ) ρ, dzbar Ψ z with hB
  have hBA : B = A / 2 := by
    have h2 : 2 * I * B = I * A := hgreen.symm.trans hcirc
    have h3 : I * (2 * B) = I * A := by rw [← h2]; ring
    have := mul_left_cancel₀ Complex.I_ne_zero h3
    linear_combination this / 2
  linear_combination hsplit - hBA

theorem g2_zpow_le_max {r1 r2 x : ℝ} (hr1 : 0 < r1) (h1 : r1 ≤ x) (h2 : x ≤ r2) (n : ℤ) :
    x ^ n ≤ max (r1 ^ n) (r2 ^ n) := by
  rcases le_total 0 n with hn | hn
  · exact (zpow_le_zpow_left₀ hn (hr1.le.trans h1) h2).trans (le_max_right _ _)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    simp only [zpow_neg, zpow_natCast]
    exact (inv_anti₀ (pow_pos hr1 m) (pow_le_pow_left₀ hr1.le h1 m)).trans (le_max_left _ _)

/-- The termwise derivative of a Laurent series on an annulus. -/
theorem g2_laurent_deriv {d : ℤ → ℂ} {r1 r2 : ℝ} (hr1 : 0 < r1)
    (hs : Summable fun n : ℤ => ‖d n‖ * max (r1 ^ n) (r2 ^ n)) {z : ℂ} (hz1 : r1 < ‖z‖)
    (hz2 : ‖z‖ < r2) :
    HasSum (fun n : ℤ => d n * z ^ n) (∑' n : ℤ, d n * z ^ n) ∧
      HasSum (fun n : ℤ => d n * ((n : ℂ) * z ^ (n - 1)))
        (deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) z) := by
  let U : Set ℂ := {w | r1 < ‖w‖ ∧ ‖w‖ < r2}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hzU : z ∈ U := ⟨hz1, hz2⟩
  have h0 : (0 : ℂ) ∉ U := fun h => by
    have := h.1
    simp at this
    linarith
  have hF : ∀ n : ℤ, DifferentiableOn ℂ (fun w : ℂ => d n * w ^ n) U := fun n =>
    (differentiableOn_const _).mul (differentiableOn_zpow n U (Or.inl h0))
  have hle : ∀ (n : ℤ) (w : ℂ), w ∈ U → ‖d n * w ^ n‖ ≤ ‖d n‖ * max (r1 ^ n) (r2 ^ n) := by
    intro n w hw
    rw [norm_mul, norm_zpow]
    gcongr
    exact g2_zpow_le_max hr1 hw.1.le hw.2.le n
  refine ⟨(Summable.of_norm_bounded hs (fun n => hle n z hzU)).hasSum, ?_⟩
  have := Complex.hasSum_deriv_of_summable_norm hs hF hU hle hzU
  refine this.congr_fun ?_
  intro n
  simp [deriv_zpow]

/-- Parseval-type formula on a circle for a Laurent series (with the weight `n`). -/
theorem g2_laurent_parseval {d : ℤ → ℂ} {r1 ρ r2 : ℝ} (hr1 : 0 < r1) (h1 : r1 < ρ) (h2 : ρ < r2)
    (hs : Summable fun n : ℤ => ‖d n‖ * max (r1 ^ n) (r2 ^ n))
    (hs1 : Summable fun n : ℤ => |(n : ℝ)| * ‖d n‖ * ρ ^ n) :
    ∫ θ in (0 : ℝ)..2 * π, conj (∑' n : ℤ, d n * (circleMap 0 ρ θ) ^ n) *
        deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) (circleMap 0 ρ θ) * circleMap 0 ρ θ =
      2 * π * ∑' n : ℤ, (n : ℂ) * ((‖d n‖ ^ 2 * ρ ^ (2 * n) : ℝ) : ℂ) := by
  have hρ0 : 0 < ρ := hr1.trans h1
  have hs0 : Summable fun n : ℤ => ‖d n‖ * ρ ^ n :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by gcongr; exact g2_zpow_le_max hr1 h1.le h2.le n) hs
  have hz0 : ∀ θ : ℝ, circleMap 0 ρ θ ≠ 0 := fun θ => by
    simp [circleMap, hρ0.ne']
  have hzn : ∀ θ : ℝ, ‖circleMap 0 ρ θ‖ = ρ := fun θ => by simp [abs_of_pos hρ0]
  -- the integrand as a double series
  let a : ℤ × ℤ → ℂ := fun p => conj (d p.1) * ((ρ ^ (2 * p.1) : ℝ) : ℂ) * ((p.2 : ℂ) * d p.2)
  let T : ℤ × ℤ → ℝ → ℂ := fun p θ => a p * (circleMap 0 ρ θ) ^ (p.2 - p.1)
  have hnormT : ∀ (p : ℤ × ℤ) (θ : ℝ), ‖T p θ‖ = (‖d p.1‖ * ρ ^ p.1) * (|(p.2 : ℝ)| * ‖d p.2‖ * ρ ^ p.2) := by
    intro p θ
    simp only [T, a, norm_mul, norm_zpow, hzn, Complex.norm_conj, Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs]
    rw [abs_of_pos hρ0]
    have e : (ρ ^ (2 * p.1)) * ρ ^ (p.2 - p.1) = ρ ^ p.1 * ρ ^ p.2 := by
      rw [← zpow_add₀ hρ0.ne', ← zpow_add₀ hρ0.ne']
      congr 1
      ring
    calc _ = ‖d p.1‖ * (|(p.2 : ℝ)| * ‖d p.2‖) * (ρ ^ (2 * p.1) * ρ ^ (p.2 - p.1)) := by ring
      _ = _ := by rw [e]; ring
  have hdouble : ∀ θ : ℝ, conj (∑' n : ℤ, d n * (circleMap 0 ρ θ) ^ n) *
        deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) (circleMap 0 ρ θ) * circleMap 0 ρ θ =
      ∑' p : ℤ × ℤ, T p θ := by
    intro θ
    set z : ℂ := circleMap 0 ρ θ with hz
    have hzne : z ≠ 0 := hz0 θ
    have hzr : ‖z‖ = ρ := hzn θ
    obtain ⟨hHs, hDs⟩ := g2_laurent_deriv hr1 hs (z := z) (by rw [hzr]; exact h1) (by rw [hzr]; exact h2)
    have hconj : conj (∑' n : ℤ, d n * z ^ n) = ∑' m : ℤ, conj (d m) * ((ρ ^ (2 * m) : ℝ) : ℂ) * z ^ (-m) := by
      rw [Complex.conj_tsum]
      refine tsum_congr (fun m => ?_)
      have hcz : conj z = ((ρ ^ 2 : ℝ) : ℂ) * z⁻¹ := by
        have h := Complex.mul_conj z
        rw [Complex.normSq_eq_norm_sq, hzr] at h
        field_simp
        rw [mul_comm]; exact_mod_cast h
      have e1 : (((ρ ^ 2 : ℝ) : ℂ)) ^ m = ((ρ ^ (2 * m) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_zpow]
        congr 1
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
      have e2 : (z⁻¹) ^ m = z ^ (-m) := by rw [zpow_neg, inv_zpow]
      rw [map_mul, map_zpow₀, hcz, mul_zpow, e1, e2]
      ring
    have hzD : z * deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) z = ∑' n : ℤ, ((n : ℂ) * d n) * z ^ n := by
      rw [← hDs.tsum_eq, ← tsum_mul_left]
      refine tsum_congr (fun n => ?_)
      rw [zpow_sub_one₀ hzne]
      field_simp
    have hA : Summable fun m : ℤ => ‖conj (d m) * ((ρ ^ (2 * m) : ℝ) : ℂ) * z ^ (-m)‖ := by
      refine hs0.congr (fun m => ?_)
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, norm_zpow, hzr, Real.norm_eq_abs]
      rw [abs_of_pos hρ0]
      have : ρ ^ (2 * m) * ρ ^ (-m) = ρ ^ m := by
        rw [← zpow_add₀ hρ0.ne']; congr 1; ring
      calc ‖d m‖ * ρ ^ m = ‖d m‖ * (ρ ^ (2 * m) * ρ ^ (-m)) := by rw [this]
        _ = _ := by ring
    have hB : Summable fun n : ℤ => ‖((n : ℂ) * d n) * z ^ n‖ := by
      refine hs1.congr (fun n => ?_)
      simp only [norm_mul, norm_zpow, hzr, Complex.norm_intCast]
    calc conj (∑' n : ℤ, d n * z ^ n) * deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) z * z
        = conj (∑' n : ℤ, d n * z ^ n) * (z * deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) z) := by ring
      _ = (∑' m : ℤ, conj (d m) * ((ρ ^ (2 * m) : ℝ) : ℂ) * z ^ (-m)) *
            ∑' n : ℤ, ((n : ℂ) * d n) * z ^ n := by rw [hconj, hzD]
      _ = ∑' p : ℤ × ℤ, (conj (d p.1) * ((ρ ^ (2 * p.1) : ℝ) : ℂ) * z ^ (-p.1)) *
            (((p.2 : ℂ) * d p.2) * z ^ p.2) := tsum_mul_tsum_of_summable_norm hA hB
      _ = ∑' p : ℤ × ℤ, T p θ := by
        refine tsum_congr (fun p => ?_)
        simp only [T, a]
        rw [zpow_sub₀ hzne, zpow_neg]
        field_simp
  -- orthogonality
  have hort : ∀ k : ℤ, ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ) ^ k = if k = 0 then 2 * π else 0 := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, if_false]
      have h := circleIntegral.integral_sub_zpow_of_ne (show k - 1 ≠ -1 by omega) (0 : ℂ) (0 : ℂ) ρ
      rw [circleIntegral] at h
      simp only [sub_zero, smul_eq_mul, deriv_circleMap] at h
      have h2 : ∫ θ in (0 : ℝ)..2 * π, circleMap 0 ρ θ * I * (circleMap 0 ρ θ) ^ (k - 1) =
          I * ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ) ^ k := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        have hzθ := hz0 θ
        rw [zpow_sub_one₀ hzθ]
        field_simp
      rw [h2] at h
      exact (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  have hcont : ∀ p : ℤ × ℤ, Continuous (T p) := by
    intro p
    have hc : Continuous fun θ : ℝ => circleMap 0 ρ θ := continuous_circleMap 0 ρ
    exact continuous_const.mul (hc.zpow₀ _ (fun θ => Or.inl (hz0 θ)))
  have hint : ∀ p : ℤ × ℤ, Integrable (T p) (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    fun p => (hcont p).integrableOn_Ioc
  have hsum : Summable fun p : ℤ × ℤ => ∫ θ in Ioc (0 : ℝ) (2 * π), ‖T p θ‖ := by
    have hf : Summable fun p : ℤ × ℤ => (‖d p.1‖ * ρ ^ p.1) * (|(p.2 : ℝ)| * ‖d p.2‖ * ρ ^ p.2) :=
      Summable.mul_of_nonneg hs0 hs1 (fun n => by positivity) (fun n => by positivity)
    refine (hf.mul_right (2 * π)).congr (fun p => ?_)
    simp only [hnormT, integral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc, smul_eq_mul]
    simp [Real.pi_pos.le]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hdouble θ),
    intervalIntegral.integral_of_le (by positivity),
    ← integral_tsum_of_summable_integral_norm hint hsum]
  have hI : ∀ p : ℤ × ℤ, ∫ θ in Ioc (0 : ℝ) (2 * π), T p θ =
      if p.2 - p.1 = 0 then 2 * π * a p else 0 := by
    intro p
    rw [← intervalIntegral.integral_of_le (by positivity)]
    simp only [T]
    rw [intervalIntegral.integral_const_mul, hort]
    split_ifs <;> simp [mul_comm]
  simp_rw [hI]
  have hinj : Function.Injective (fun n : ℤ => ((n, n) : ℤ × ℤ)) := fun m n h => by
    simpa using congrArg Prod.fst h
  rw [← hinj.tsum_eq (f := fun p : ℤ × ℤ => if p.2 - p.1 = 0 then 2 * π * a p else 0) (by
    intro p hp
    by_contra hnr
    apply hp
    have : p.2 - p.1 ≠ 0 := by
      intro h0
      apply hnr
      exact ⟨p.1, by ext <;> simp; linarith⟩
    simp [this])]
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  simp only [sub_self, if_true, a]
  have h := Complex.conj_mul' (d n)
  push_cast
  linear_combination (2 * (π : ℂ) * (n : ℂ) * ((ρ : ℂ) ^ (2 * n))) * h

/-- The circle average of `u^m` (integer `m`) over `|u| = R`. -/
theorem g2_circleAverage_zpow {R : ℝ} (hR : 0 < R) (m : ℤ) :
    Real.circleAverage (fun u : ℂ => u ^ m) 0 R = if m = 0 then 1 else 0 := by
  have hz0 : ∀ θ : ℝ, circleMap 0 R θ ≠ 0 := fun θ => by simp [circleMap, hR.ne']
  by_cases hm : m = 0
  · simp [hm, Real.circleAverage_const]
  · simp only [hm, ite_false]
    rw [Real.circleAverage_def]
    have h := circleIntegral.integral_sub_zpow_of_ne (show m - 1 ≠ -1 by omega) (0 : ℂ) (0 : ℂ) R
    rw [circleIntegral] at h
    simp only [sub_zero, smul_eq_mul, deriv_circleMap] at h
    have h2 : ∫ θ in (0 : ℝ)..2 * π, circleMap 0 R θ * I * (circleMap 0 R θ) ^ (m - 1) =
        I * ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 R θ) ^ m := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      have hzθ := hz0 θ
      rw [zpow_sub_one₀ hzθ]
      field_simp
    rw [h2] at h
    have := (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
    simp [this]

/-- Cauchy coefficient extraction for a uniformly dominated power series on a circle. -/
theorem g2_circle_coeff {s : ℕ → ℂ} {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (k : ℕ) {B : ℕ → ℝ}
    (hB : Summable B) (hbd : ∀ q : ℕ, ∀ u ∈ sphere (0 : ℂ) |R|, ‖s q * u ^ q‖ ≤ B q)
    (hF : ∀ u ∈ sphere (0 : ℂ) |R|, HasSum (fun q => s q * u ^ q) (F u)) :
    Real.circleAverage (fun u => F u / u ^ k) 0 R = s k := by
  have hne : ∀ u ∈ sphere (0 : ℂ) |R|, u ≠ 0 := by
    intro u hu h0
    rw [h0] at hu
    simp [abs_of_pos hR] at hu
    linarith
  have hT : ∀ q : ℕ, CircleIntegrable (fun u => s q * u ^ q / u ^ k) 0 R := by
    intro q
    have hc : ContinuousOn (fun u : ℂ => s q * u ^ q / u ^ k) (sphere (0 : ℂ) |R|) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      exact pow_ne_zero _ (hne u hu)
    exact (hc.comp (continuous_circleMap 0 R).continuousOn
      (fun θ _ => circleMap_mem_sphere' 0 R θ)).intervalIntegrable
  have key := circleAverage_hasSum_of_bound (T := fun q u => s q * u ^ q / u ^ k)
    (K := fun u => F u / u ^ k) (B := fun q => B q / |R| ^ k) hT
    (hB.div_const _) (by
      intro q u hu
      have hun : ‖u‖ = |R| := by simpa using hu
      rw [norm_div, norm_pow, hun]
      exact div_le_div_of_nonneg_right (hbd q u hu) (by positivity))
    (fun u hu => (hF u hu).div_const _)
  have hq : ∀ q : ℕ, Real.circleAverage (fun u => s q * u ^ q / u ^ k) 0 R = if q = k then s q else 0 := by
    intro q
    have e : ∀ u : ℂ, u ≠ 0 → s q * u ^ q / u ^ k = s q * u ^ ((q : ℤ) - k) := by
      intro u hu
      rw [zpow_sub₀ hu]
      simp [zpow_natCast, div_eq_mul_inv]
      ring
    have hci : Real.circleAverage (fun u => s q * u ^ q / u ^ k) 0 R =
        Real.circleAverage (fun u => s q * u ^ ((q : ℤ) - k)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro u hu
      exact e u (hne u (by simpa using hu))
    have hsm := Real.circleAverage_fun_smul (a := s q) (f := fun u : ℂ => u ^ ((q : ℤ) - k)) (c := 0) (R := R)
    simp only [smul_eq_mul] at hsm
    rw [hci, hsm, g2_circleAverage_zpow hR]
    by_cases h : q = k
    · simp [h]
    · have : (q : ℤ) - k ≠ 0 := by omega
      simp [h, this]
  simp_rw [hq] at key
  have h2 := hasSum_single (f := fun i : ℕ => if i = k then s i else 0) k (fun i hi => by simp [hi])
  simpa using key.unique h2

/-- Geometric domination of a power series that converges at one point of modulus `r'`. -/
theorem g2_geom_bound {c : ℕ → ℂ} {w0 : ℂ} (hw0 : w0 ≠ 0)
    (hs : Summable fun j => c j * w0 ^ j) :
    ∃ C : ℝ, ∀ j : ℕ, ‖c j‖ * ‖w0‖ ^ j ≤ C := by
  obtain ⟨C, hC⟩ := hs.tendsto_atTop_zero.norm.bddAbove_range
  exact ⟨C, fun j => by simpa [norm_mul, norm_pow] using hC ⟨j, rfl⟩⟩

/-- The Taylor coefficient of `f^l / ζ^k` on a circle of radius `r < 1`. -/
theorem g2_circle_coeff_pow {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hf0 : f 0 = 0)
    (l k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ => f ζ ^ l / ζ ^ k) 0 r =
      if l ≤ k then (((k - l).factorial : ℂ))⁻¹ *
        iteratedDeriv (k - l) (fun ζ => dslope f 0 ζ ^ l) 0 else 0 := by
  have hg : DifferentiableOn ℂ (dslope f 0) unitDisc :=
    (differentiableOn_dslope (ball_mem_nhds (0 : ℂ) one_pos)).mpr hf
  have hgl : DifferentiableOn ℂ (fun ζ => dslope f 0 ζ ^ l) (ball (0 : ℂ) 1) := hg.pow l
  have hfu : ∀ u : ℂ, f u = u * dslope f 0 u := by
    intro u
    have := sub_smul_dslope f 0 u
    simp only [sub_zero, smul_eq_mul, hf0] at this
    exact this.symm
  set γ : ℕ → ℂ := fun j => ((j.factorial : ℂ))⁻¹ * iteratedDeriv j (fun ζ => dslope f 0 ζ ^ l) 0 with hγ
  have hTaylor : ∀ w ∈ ball (0 : ℂ) 1, HasSum (fun j => γ j * w ^ j) (dslope f 0 w ^ l) := by
    intro w hw
    have := Complex.hasSum_taylorSeries_on_ball hgl hw
    refine this.congr_fun ?_
    intro j
    simp only [hγ, smul_eq_mul, sub_zero]
    ring
  obtain ⟨r', hrr', hr'1⟩ := exists_between hr1
  have hr'0 : 0 < r' := hr0.trans hrr'
  have hr'mem : ((r' : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr'0.le]; exact hr'1
  obtain ⟨C, hC⟩ := g2_geom_bound (by exact_mod_cast hr'0.ne') (hTaylor _ hr'mem).summable
  simp only [Complex.norm_real, Real.norm_of_nonneg hr'0.le] at hC
  let s : ℕ → ℂ := fun q => if l ≤ q then γ (q - l) else 0
  have hsum : ∀ u ∈ ball (0 : ℂ) 1, HasSum (fun q => s q * u ^ q) (f u ^ l) := by
    intro u hu
    have h1 := (hTaylor u hu).mul_left (u ^ l)
    have hfl : f u ^ l = u ^ l * dslope f 0 u ^ l := by rw [hfu u, mul_pow]
    rw [hfl]
    let gg : ℕ → ℕ := fun j => j + l
    have hgi : Function.Injective gg := fun a b h => by simpa [gg] using h
    have hz : ∀ q ∉ Set.range gg, (fun q => s q * u ^ q) q = 0 := by
      intro q hq
      have : ¬ l ≤ q := fun hlq => hq ⟨q - l, by simp [gg]; omega⟩
      simp [s, this]
    refine (hgi.hasSum_iff hz).mp ?_
    refine h1.congr_fun ?_
    intro j
    simp only [Function.comp_apply, gg, s, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel]
    ring
  have hC0 : 0 ≤ C := (by positivity : (0:ℝ) ≤ ‖γ 0‖ * r' ^ 0).trans (hC 0)
  set θ : ℝ := r / r' with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := (div_lt_one hr'0).mpr hrr'
  have hbd : ∀ q : ℕ, ∀ u ∈ sphere (0 : ℂ) |r|, ‖s q * u ^ q‖ ≤ (C * r ^ l / θ ^ l) * θ ^ q := by
    intro q u hu
    have hun : ‖u‖ = r := by simpa [abs_of_pos hr0] using hu
    by_cases hlq : l ≤ q
    · simp only [s, hlq, if_true, norm_mul, norm_pow, hun]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hlq
      simp only [Nat.add_sub_cancel_left]
      have h1 := hC j
      have hr'j : 0 < r' ^ j := pow_pos hr'0 j
      calc ‖γ j‖ * r ^ (l + j) = (‖γ j‖ * r' ^ j) * (θ ^ j) * r ^ l := by
            rw [hθ, div_pow]; field_simp; ring
        _ ≤ C * θ ^ j * r ^ l := by gcongr
        _ = C * r ^ l / θ ^ l * θ ^ (l + j) := by
            rw [pow_add]; field_simp
    · simp only [s, hlq, if_false, zero_mul, norm_zero]
      positivity
  have hB : Summable fun q : ℕ => (C * r ^ l / θ ^ l) * θ ^ q :=
    (summable_geometric_of_lt_one hθ0.le hθ1).mul_left _
  have := g2_circle_coeff hr0 k hB hbd (F := fun u => f u ^ l)
    (fun u hu => hsum u (by
      rw [mem_ball_zero_iff]
      have : ‖u‖ = r := by simpa [abs_of_pos hr0] using hu
      rw [this]; exact hr1))
  rw [this]

set_option maxHeartbeats 1000000 in
/-- The Faber–Grunsky identity for one function: `Σ_{l ≤ k} φ_{lk}/(l f(z)^l) = z^{-k}/k + Σ_p a_{pk} z^p`. -/
theorem g2_faber_identity {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hf0 : f 0 = 0)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    {φ : ℕ → ℕ → ℂ}
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun ζ => f ζ ^ l / ζ ^ k) 0 r = φ l k)
    (hφ0 : ∀ l k : ℕ, k < l → φ l k = 0)
    {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) (hfz : f z ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun p : ℕ => a p k * z ^ p) ∧
      ∑ l ∈ Finset.Icc 1 k, φ l k / ((l : ℂ) * f z ^ l) = 1 / ((k : ℂ) * z ^ k) + ∑' p : ℕ, a p k * z ^ p := by
  set W : ℂ := f z with hW
  have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hWpos : 0 < ‖W‖ := norm_pos_iff.mpr hfz
  -- choice of δ
  have hcont : ContinuousAt f 0 := (hf.differentiableAt (ball_mem_nhds (0 : ℂ) one_pos)).continuousAt
  obtain ⟨δ0, hδ0, hδ0f⟩ : ∃ δ0 > 0, ∀ ζ : ℂ, ‖ζ‖ ≤ δ0 → ‖f ζ‖ ≤ ‖W‖ / 2 := by
    have h := Metric.continuousAt_iff.mp hcont (‖W‖ / 2) (by positivity)
    obtain ⟨δ, hδ, hδh⟩ := h
    refine ⟨δ / 2, by positivity, fun ζ hζ => ?_⟩
    have := hδh (show dist ζ 0 < δ by rw [dist_zero_right]; linarith)
    rw [hf0, dist_zero_right] at this
    exact this.le
  set δ : ℝ := min δ0 (min (‖z‖ / 2) (1 / 2)) with hδ
  have hδpos : 0 < δ := lt_min hδ0 (lt_min (by positivity) (by norm_num))
  have hδz : δ ≤ ‖z‖ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδf : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ‖f ζ‖ ≤ ‖W‖ / 2 := fun ζ hζ => hδ0f ζ (hζ.trans (min_le_left _ _))
  have hballD : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ζ ∈ unitDisc := fun ζ hζ =>
    mem_ball_zero_iff.mpr (by linarith)
  have hneq : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → z ≠ ζ := fun ζ hζ h => by
    rw [← h] at hζ; linarith
  have hS : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * ζ ^ p.2) S ∧
        (W - f ζ) / (z - ζ) = exp (b00 - S) :=
    fun ζ hζ => hexp z hz ζ (hballD ζ hζ) (hneq ζ hζ)
  have hnorm : Summable (fun p : ℕ × ℕ => ‖a p.1 p.2 * z ^ p.1‖ * δ ^ p.2) := by
    obtain ⟨S, hS1, -⟩ := hS (δ : ℂ) (by simp [abs_of_pos hδpos])
    refine hS1.summable.norm.congr (fun p => ?_)
    simp [norm_mul, norm_pow, abs_of_pos hδpos]
  have hnormT : Summable (fun p : ℕ × ℕ => ‖a p.2 p.1 * z ^ p.2‖ * δ ^ p.1) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hnorm
  have hrowN : ∀ q : ℕ, Summable (fun p : ℕ => ‖a p q * z ^ p‖) := by
    intro q
    have h1 : Summable (fun p : ℕ => ‖a p q * z ^ p‖ * δ ^ q) :=
      hnorm.comp_injective (i := fun p : ℕ => ((p, q) : ℕ × ℕ)) (fun x y h => by simpa using congrArg Prod.fst h)
    exact (summable_mul_right_iff (pow_ne_zero q hδpos.ne')).mp h1
  have hrow : ∀ q : ℕ, Summable (fun p : ℕ => a p q * z ^ p) := fun q => (hrowN q).of_norm
  set sq : ℕ → ℂ := fun q => ∑' p : ℕ, a p q * z ^ p with hsq
  let U : ℕ → ℝ := fun q => ∑' p : ℕ, ‖a p q * z ^ p‖ * δ ^ q
  have hU : Summable U := hnormT.prod
  have hsqU : ∀ q : ℕ, ‖sq q‖ * δ ^ q ≤ U q := by
    intro q
    have h1 : ‖sq q‖ ≤ ∑' p : ℕ, ‖a p q * z ^ p‖ := norm_tsum_le_tsum_norm (hrowN q)
    calc ‖sq q‖ * δ ^ q ≤ (∑' p : ℕ, ‖a p q * z ^ p‖) * δ ^ q := by gcongr
      _ = U q := by simp only [U]; rw [tsum_mul_right]
  have hSsum : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ∃ S : ℂ, HasSum (fun q : ℕ => sq q * ζ ^ q) S ∧
      (W - f ζ) / (z - ζ) = exp (b00 - S) := by
    intro ζ hζ
    obtain ⟨S, hS1, hSe⟩ := hS ζ hζ
    refine ⟨S, ?_, hSe⟩
    have h2 : HasSum (fun p : ℕ × ℕ => a p.2 p.1 * z ^ p.2 * ζ ^ p.1) S :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS1
    exact h2.prod_fiberwise (fun q => (hrow q).hasSum.mul_right (ζ ^ q))
  let Sfun : ℂ → ℂ := fun ζ => ∑' q : ℕ, sq q * ζ ^ q
  have hSf : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → HasSum (fun q : ℕ => sq q * ζ ^ q) (Sfun ζ) ∧
      (W - f ζ) / (z - ζ) = exp (b00 - Sfun ζ) := by
    intro ζ hζ
    obtain ⟨S, hS1, hSe⟩ := hSsum ζ hζ
    have : Sfun ζ = S := hS1.tsum_eq
    rw [this]
    exact ⟨hS1, hSe⟩
  have hScont : ContinuousOn Sfun (closedBall (0 : ℂ) δ) := by
    apply continuousOn_tsum (u := U) (fun q => by fun_prop) hU
    intro q ζ hζ
    have hζn : ‖ζ‖ ≤ δ := mem_closedBall_zero_iff.mp hζ
    calc ‖sq q * ζ ^ q‖ = ‖sq q‖ * ‖ζ‖ ^ q := by rw [norm_mul, norm_pow]
      _ ≤ ‖sq q‖ * δ ^ q := by gcongr
      _ ≤ U q := hsqU q
  have hS0 : Sfun 0 = sq 0 := by
    simp only [Sfun]
    rw [tsum_eq_single 0 (fun q hq => by simp [hq])]
    simp
  have hslit : ∀ t : ℂ, ‖t‖ < 1 → (1 - t) ∈ Complex.slitPlane := by
    intro t ht
    rw [Complex.mem_slitPlane_iff]
    left
    have := Complex.abs_re_le_norm t
    simp only [Complex.sub_re, Complex.one_re]
    linarith [le_abs_self t.re]
  have hzt : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ‖ζ / z‖ ≤ 1 / 2 := by
    intro ζ hζ
    rw [norm_div, div_le_iff₀ hzpos]
    linarith
  have hft : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → ‖f ζ / W‖ ≤ 1 / 2 := by
    intro ζ hζ
    rw [norm_div, div_le_iff₀ hWpos]
    have := hδf ζ hζ
    linarith
  let K : ℂ → ℂ := fun ζ => (Sfun ζ - Sfun 0) - Complex.log (1 - ζ / z)
  let E : ℂ → ℂ := fun ζ => -Complex.log (1 - f ζ / W)
  have hexpKE : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → exp (-K ζ) = exp (-E ζ) := by
    intro ζ hζ
    have h1 : 1 - ζ / z ≠ 0 := Complex.slitPlane_ne_zero (hslit _ (by linarith [hzt ζ hζ]))
    have h2 : 1 - f ζ / W ≠ 0 := Complex.slitPlane_ne_zero (hslit _ (by linarith [hft ζ hζ]))
    have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr (hneq ζ hζ)
    have hS0e := (hSf 0 (by simp [hδpos.le])).2
    have hSζe := (hSf ζ hζ).2
    simp only [hf0, sub_zero] at hS0e
    have e1 : exp (-K ζ) = exp (b00 - Sfun ζ) / exp (b00 - Sfun 0) * (1 - ζ / z) := by
      have : -K ζ = ((b00 - Sfun ζ) - (b00 - Sfun 0)) + Complex.log (1 - ζ / z) := by
        simp only [K]; ring
      rw [this, Complex.exp_add, Complex.exp_sub, Complex.exp_log h1]
    have e2 : exp (-E ζ) = 1 - f ζ / W := by
      simp only [E, neg_neg]
      exact Complex.exp_log h2
    rw [e1, e2, ← hSζe, ← hS0e]
    field_simp
  have hKc : ContinuousOn K (closedBall (0 : ℂ) δ) := by
    have h1 : ContinuousOn (fun ζ : ℂ => Complex.log (1 - ζ / z)) (closedBall (0 : ℂ) δ) := by
      intro ζ hζ
      have := hslit _ (show ‖ζ / z‖ < 1 by linarith [hzt ζ (mem_closedBall_zero_iff.mp hζ)])
      exact (ContinuousAt.comp (f := fun ζ : ℂ => 1 - ζ / z) (x := ζ) (continuousAt_clog this)
        (by fun_prop)).continuousWithinAt
    exact (hScont.sub continuousOn_const).sub h1
  have hEc : ContinuousOn E (closedBall (0 : ℂ) δ) := by
    have hfc : ContinuousOn f (closedBall (0 : ℂ) δ) :=
      hf.continuousOn.mono (fun ζ hζ => hballD ζ (mem_closedBall_zero_iff.mp hζ))
    intro ζ hζ
    have := hslit _ (show ‖f ζ / W‖ < 1 by linarith [hft ζ (mem_closedBall_zero_iff.mp hζ)])
    have h2 : ContinuousWithinAt (fun ζ => f ζ / W) (closedBall (0 : ℂ) δ) ζ :=
      (hfc ζ hζ).div_const W
    have h3 : ContinuousWithinAt (fun ζ => 1 - f ζ / W) (closedBall (0 : ℂ) δ) ζ :=
      continuousWithinAt_const.sub h2
    exact (ContinuousAt.comp_continuousWithinAt (f := fun ζ => 1 - f ζ / W) (continuousAt_clog this) h3).neg
  have hKE : ∀ ζ : ℂ, ‖ζ‖ < δ → K ζ = E ζ := by
    have hconn : IsPreconnected (ball (0 : ℂ) δ) := (convex_ball (0 : ℂ) δ).isPreconnected
    haveI : PreconnectedSpace (ball (0 : ℂ) δ) := isPreconnected_iff_preconnectedSpace.mp hconn
    have hc1 : Continuous (fun x : ball (0 : ℂ) δ => K (x : ℂ)) :=
      hKc.comp_continuous continuous_subtype_val (fun x => ball_subset_closedBall x.2)
    have hc2 : Continuous (fun x : ball (0 : ℂ) δ => E (x : ℂ)) :=
      hEc.comp_continuous continuous_subtype_val (fun x => ball_subset_closedBall x.2)
    have := continuous_exp_lift_unique (X := ball (0 : ℂ) δ) hc1 hc2 (by
      intro x
      have hx : ‖(x : ℂ)‖ ≤ δ := (mem_ball_zero_iff.mp x.2).le
      have := hexpKE x hx
      rw [← inv_inj, ← Complex.exp_neg, ← Complex.exp_neg]
      exact this)
      (x₀ := ⟨0, mem_ball_self hδpos⟩) (by
        simp only [K, E, sub_self, zero_div, sub_zero, Complex.log_one, hf0, neg_zero])
    intro ζ hζ
    exact congrFun this ⟨ζ, mem_ball_zero_iff.mpr hζ⟩
  -- the circle of radius r
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrδ : r < δ := by rw [hr]; linarith
  have hr1 : r < 1 := by linarith
  have hsph : ∀ u ∈ sphere (0 : ℂ) |r|, ‖u‖ = r := fun u hu => by simpa [abs_of_pos hr0] using hu
  have hune : ∀ u ∈ sphere (0 : ℂ) |r|, u ≠ 0 := fun u hu h0 => by
    have := hsph u hu; rw [h0, norm_zero] at this; linarith
  -- expansion of K
  let c' : ℕ → ℂ := fun q => if q = 0 then 0 else sq q + ((q : ℂ) * z ^ q)⁻¹
  have hKser : ∀ ζ : ℂ, ‖ζ‖ ≤ δ → HasSum (fun q : ℕ => c' q * ζ ^ q) (K ζ) := by
    intro ζ hζ
    have h1 := (hSf ζ hζ).1.sub (hasSum_ite_eq 0 (sq 0))
    rw [← hS0] at h1
    have h2 := Complex.hasSum_taylorSeries_neg_log (show ‖ζ / z‖ < 1 by linarith [hzt ζ hζ])
    have h3 := h1.add h2
    have hval : Sfun ζ - Sfun 0 + -Complex.log (1 - ζ / z) = K ζ := by simp only [K]; ring
    rw [hval] at h3
    refine h3.congr_fun ?_
    intro q
    by_cases hq : q = 0
    · subst hq
      simp [c', hS0]
    · simp only [c', hq, if_false, if_neg hq]
      rw [div_pow, add_mul]
      have hzq : z ^ q ≠ 0 := pow_ne_zero q hz0
      have hqq : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      field_simp
      ring
  -- Cauchy coefficient of K
  have hKcirc : Real.circleAverage (fun u => K u / u ^ k) 0 r = c' k := by
    apply g2_circle_coeff hr0 k (B := fun q => U q + (1 / 2 : ℝ) ^ q)
    · exact hU.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    · intro q u hu
      have hun := hsph u hu
      by_cases hq : q = 0
      · subst hq
        have hU0 : 0 ≤ U 0 := tsum_nonneg (fun p => by positivity)
        have h12 : (0 : ℝ) ≤ (1 / 2) ^ 0 := by positivity
        simp only [c', if_true, zero_mul, norm_zero]
        linarith
      · simp only [c', hq, if_false, norm_mul, norm_pow, hun]
        have h1 : ‖sq q + ((q : ℂ) * z ^ q)⁻¹‖ ≤ ‖sq q‖ + ‖((q : ℂ) * z ^ q)⁻¹‖ := norm_add_le _ _
        have h2 : ‖((q : ℂ) * z ^ q)⁻¹‖ * r ^ q ≤ (1 / 2 : ℝ) ^ q := by
          rw [norm_inv, norm_mul, norm_pow, Complex.norm_natCast]
          have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
          have hrz : r / ‖z‖ ≤ 1 / 2 := by
            rw [div_le_iff₀ hzpos]; linarith
          have hz1 : 0 < ‖z‖ ^ q := pow_pos hzpos q
          calc (↑q * ‖z‖ ^ q)⁻¹ * r ^ q ≤ (‖z‖ ^ q)⁻¹ * r ^ q := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact inv_anti₀ hz1 (le_mul_of_one_le_left hz1.le hq1)
            _ = (r / ‖z‖) ^ q := by rw [div_pow, div_eq_inv_mul]
            _ ≤ (1 / 2) ^ q := pow_le_pow_left₀ (by positivity) hrz q
        have h3 : ‖sq q‖ * r ^ q ≤ U q :=
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hrδ.le q) (norm_nonneg _)).trans (hsqU q)
        calc ‖sq q + ((q : ℂ) * z ^ q)⁻¹‖ * r ^ q ≤ (‖sq q‖ + ‖((q : ℂ) * z ^ q)⁻¹‖) * r ^ q := by gcongr
          _ = ‖sq q‖ * r ^ q + ‖((q : ℂ) * z ^ q)⁻¹‖ * r ^ q := by ring
          _ ≤ U q + (1 / 2 : ℝ) ^ q := add_le_add h3 h2
    · intro u hu
      exact hKser u (by rw [hsph u hu]; exact hrδ.le)
  -- Cauchy coefficient of E
  have hEcirc : Real.circleAverage (fun u => E u / u ^ k) 0 r =
      ∑ l ∈ Finset.Icc 1 k, φ l k / ((l : ℂ) * W ^ l) := by
    have hfc : ContinuousOn f (closedBall (0 : ℂ) δ) :=
      hf.continuousOn.mono (fun ζ hζ => hballD ζ (mem_closedBall_zero_iff.mp hζ))
    have hsphδ : ∀ u ∈ sphere (0 : ℂ) |r|, u ∈ closedBall (0 : ℂ) δ := fun u hu => by
      rw [mem_closedBall_zero_iff, hsph u hu]; exact hrδ.le
    have hfn : ∀ u ∈ sphere (0 : ℂ) |r|, ‖f u / W‖ ≤ 1 / 2 := fun u hu => hft u (by rw [hsph u hu]; exact hrδ.le)
    have hT : ∀ n : ℕ, CircleIntegrable (fun u => ((f u / W) ^ n / n) / u ^ k) 0 r := by
      intro n
      have hc : ContinuousOn (fun u : ℂ => ((f u / W) ^ n / n) / u ^ k) (sphere (0 : ℂ) |r|) := by
        apply ContinuousOn.div
        · exact (((hfc.mono hsphδ).div_const W).pow n).div_const _
        · fun_prop
        · intro u hu; exact pow_ne_zero _ (hune u hu)
      exact (hc.comp (continuous_circleMap 0 r).continuousOn
        (fun θ _ => circleMap_mem_sphere' 0 r θ)).intervalIntegrable
    have key := circleAverage_hasSum_of_bound (ι := ℕ) (T := fun (n : ℕ) (u : ℂ) => ((f u / W) ^ n / (n : ℂ)) / u ^ k)
      (K := fun u => E u / u ^ k) (B := fun n => (1 / 2 : ℝ) ^ n / r ^ k) hT
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const _) (by
        intro n u hu
        rw [norm_div, norm_div, norm_pow, norm_pow, hsph u hu, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ (by positivity)
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp
        · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
          calc ‖f u / W‖ ^ n / (n : ℝ) ≤ ‖f u / W‖ ^ n := div_le_self (by positivity) hn1
            _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (norm_nonneg _) (hfn u hu) n)
      (by
        intro u hu
        have := Complex.hasSum_taylorSeries_neg_log (show ‖f u / W‖ < 1 by linarith [hfn u hu])
        exact this.div_const (u ^ k))
    have hTavg : ∀ n : ℕ, Real.circleAverage (fun u => ((f u / W) ^ n / n) / u ^ k) 0 r =
        ((n : ℂ) * W ^ n)⁻¹ * φ n k := by
      intro n
      have e : (fun u : ℂ => ((f u / W) ^ n / n) / u ^ k) =
          fun u => ((n : ℂ) * W ^ n)⁻¹ * (f u ^ n / u ^ k) := by
        funext u
        rw [div_pow]
        ring
      rw [e]
      have hsm := Real.circleAverage_fun_smul (a := ((n : ℂ) * W ^ n)⁻¹)
        (f := fun u : ℂ => f u ^ n / u ^ k) (c := 0) (R := r)
      simp only [smul_eq_mul] at hsm
      rw [hsm, hφ n k r hr0 hr1]
    simp_rw [hTavg] at key
    have hfin : HasSum (fun n : ℕ => ((n : ℂ) * W ^ n)⁻¹ * φ n k)
        (∑ n ∈ Finset.range (k + 1), ((n : ℂ) * W ^ n)⁻¹ * φ n k) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        have : k < n := by simpa using hn
        simp [hφ0 n k this])
    rw [key.unique hfin]
    rw [← Finset.sum_subset (s₁ := Finset.Icc 1 k) (s₂ := Finset.range (k + 1))
      (fun n hn => by simp at hn ⊢; omega) (fun n hn hn' => by
        have : n = 0 := by simp at hn hn'; omega
        simp [this])]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [div_eq_inv_mul]
  have hfinal : Real.circleAverage (fun u => K u / u ^ k) 0 r =
      Real.circleAverage (fun u => E u / u ^ k) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro u hu
    simp only
    rw [hKE u (by rw [hsph u hu]; exact hrδ)]
  rw [hKcirc, hEcirc] at hfinal
  refine ⟨hrow k, ?_⟩
  have hk0 : k ≠ 0 := by omega
  simp only [c', hk0, if_false] at hfinal
  rw [← hfinal, one_div, add_comm]

/-- The Taylor coefficients `φ_{lk} = [ζ^k] f^l` of the powers of `f`, as an explicit expression. -/
theorem g2_phi_exists {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hf0 : f 0 = 0) :
    ∃ φ : ℕ → ℕ → ℂ, (∀ l k : ℕ, ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun ζ => f ζ ^ l / ζ ^ k) 0 r = φ l k) ∧ ∀ l k : ℕ, k < l → φ l k = 0 := by
  refine ⟨fun l k => if l ≤ k then (((k - l).factorial : ℂ))⁻¹ *
      iteratedDeriv (k - l) (fun ζ => dslope f 0 ζ ^ l) 0 else 0, ?_, ?_⟩
  · intro l k r hr0 hr1
    exact g2_circle_coeff_pow hf hf0 l k hr0 hr1
  · intro l k hlk
    have : ¬ l ≤ k := by omega
    simp [this]

/-- The Laurent expansion of `h ∘ f` for `h = Σ ν_l w^{-l}` in terms of the Grunsky array. -/
theorem g2_laurent_of_faber {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    {φ : ℕ → ℕ → ℂ}
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun ζ => f ζ ^ l / ζ ^ k) 0 r = φ l k)
    (hφ0 : ∀ l k : ℕ, k < l → φ l k = 0) (N : ℕ) (μ : ℕ → ℂ)
    {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    Summable (fun p : ℕ => (∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a p k) * z ^ p) ∧
      ∑ l ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * φ l k / (l : ℂ)) * (f z) ^ (-(l : ℤ)) =
        ∑ k ∈ Finset.Icc 1 N, μ k * z ^ (-(k : ℤ)) +
          ∑' p : ℕ, (∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a p k) * z ^ p := by
  have hfz : f z ≠ 0 := fun h0 => hz0 (hi hz (mem_ball_self one_pos) (by rw [h0, hf0]))
  have hid : ∀ k ∈ Finset.Icc 1 N, Summable (fun p : ℕ => a p k * z ^ p) ∧
      ∑ l ∈ Finset.Icc 1 k, φ l k / ((l : ℂ) * f z ^ l) =
        1 / ((k : ℂ) * z ^ k) + ∑' p : ℕ, a p k * z ^ p := fun k hk =>
    g2_faber_identity hf hf0 hexp hφ hφ0 hz hz0 hfz (Finset.mem_Icc.mp hk).1
  have hterm : ∀ p : ℕ, (∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a p k) * z ^ p =
      ∑ k ∈ Finset.Icc 1 N, ((k : ℂ) * μ k) * (a p k * z ^ p) := by
    intro p
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  have hsum : Summable (fun p : ℕ => ∑ k ∈ Finset.Icc 1 N, ((k : ℂ) * μ k) * (a p k * z ^ p)) :=
    summable_sum (fun k hk => (hid k hk).1.mul_left _)
  refine ⟨by simpa only [hterm] using hsum, ?_⟩
  simp only [hterm]
  rw [Summable.tsum_finsetSum (fun k hk => (hid k hk).1.mul_left _)]
  have hW : ∀ l : ℕ, (f z) ^ (-(l : ℤ)) = ((f z) ^ l)⁻¹ := fun l => by rw [zpow_neg, zpow_natCast]
  have hk : ∀ k ∈ Finset.Icc 1 N,
      ∑ l ∈ Finset.Icc 1 N, ((k : ℂ) * μ k * φ l k / (l : ℂ)) * (f z) ^ (-(l : ℤ)) =
        (k : ℂ) * μ k * (1 / ((k : ℂ) * z ^ k) + ∑' p : ℕ, a p k * z ^ p) := by
    intro k hkm
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkm).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hkm).2
    rw [← (hid k hkm).2, Finset.mul_sum]
    rw [← Finset.sum_subset (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc 1 N)
      (fun l hl => by simp at hl ⊢; omega) (fun l hl hl' => by
        have : k < l := by simp at hl hl'; omega
        simp [hφ0 l k this])]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hW l]
    ring
  calc ∑ l ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * φ l k / (l : ℂ)) * (f z) ^ (-(l : ℤ))
      = ∑ k ∈ Finset.Icc 1 N, ∑ l ∈ Finset.Icc 1 N,
          ((k : ℂ) * μ k * φ l k / (l : ℂ)) * (f z) ^ (-(l : ℤ)) := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 N, (μ k * z ^ (-(k : ℤ)) + ∑' p : ℕ, ((k : ℂ) * μ k) * (a p k * z ^ p)) := by
        refine Finset.sum_congr rfl (fun k hkm => ?_)
        rw [hk k hkm, tsum_mul_left]
        have hk1 : (k : ℂ) ≠ 0 := by
          have := (Finset.mem_Icc.mp hkm).1
          exact_mod_cast (by omega : k ≠ 0)
        have hzk : z ^ k ≠ 0 := pow_ne_zero k hz0
        rw [zpow_neg, zpow_natCast]
        field_simp
    _ = _ := Finset.sum_add_distrib

set_option maxHeartbeats 2000000 in
/-- The finite Grunsky inequality at radius `ρ < 1`. -/
theorem g2_grunsky_finite {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (μ : ℕ → ℂ) :
    Summable (fun p : ℕ => ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1))) ∧
      ∑' p : ℕ, ((p + 1 : ℕ) : ℝ) * ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 *
          ρ ^ (2 * (p + 1)) ≤
        ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖μ k‖ ^ 2 * (ρ ^ (2 * k))⁻¹ := by
  obtain ⟨φ, hφ, hφ0⟩ := g2_phi_exists hf hf0
  set c : ℕ → ℂ := fun p => ∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a p k with hc
  set ν : ℕ → ℂ := fun l => ∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * φ l k / (l : ℂ) with hν
  let h : ℂ → ℂ := fun w => ∑ l ∈ Finset.Icc 1 N, ν l * w ^ (-(l : ℤ))
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1pos : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2pos : 0 < r2 := by linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  let d : ℤ → ℂ := fun n => if 0 ≤ n then c n.toNat else if (-n).toNat ≤ N then μ (-n).toNat else 0
  -- Laurent expansion
  have hdpos : ∀ n : ℕ, d (n : ℤ) = c n := fun n => by simp [d]
  have hdneg : ∀ m : ℕ, d (-((m : ℤ) + 1)) = if m + 1 ≤ N then μ (m + 1) else 0 := fun m => by
    have h1 : ¬ (0 : ℤ) ≤ -((m : ℤ) + 1) := by omega
    have h2 : (-(-((m : ℤ) + 1))).toNat = m + 1 := by omega
    show (if (0 : ℤ) ≤ -((m : ℤ) + 1) then c (-((m : ℤ) + 1)).toNat
      else if (-(-((m : ℤ) + 1))).toNat ≤ N then μ (-(-((m : ℤ) + 1))).toNat else 0) = _
    rw [if_neg h1, h2]
  have hlaurent : ∀ z : ℂ, r1 < ‖z‖ → ‖z‖ < r2 → h (f z) = ∑' n : ℤ, d n * z ^ n := by
    intro z hz1 hz2
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (hz2.trans hr2one)
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz1; linarith
    obtain ⟨hsc, hF⟩ := g2_laurent_of_faber hf hi hf0 hexp hφ hφ0 N μ hzD hz0
    have hpos : Summable (fun n : ℕ => d (n : ℤ) * z ^ (n : ℤ)) := by
      refine hsc.congr (fun n => ?_)
      rw [hdpos, zpow_natCast]
    have hneg : Summable (fun n : ℕ => d (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1))) := by
      refine summable_of_ne_finset_zero (s := Finset.range N) (fun m hm => ?_)
      have : ¬ m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_neg this, zero_mul]
    rw [tsum_of_nat_of_neg_add_one hpos hneg]
    have e1 : ∑' n : ℕ, d (n : ℤ) * z ^ (n : ℤ) = ∑' p : ℕ, c p * z ^ p := by
      refine tsum_congr (fun n => ?_)
      rw [hdpos, zpow_natCast]
    have e2 : ∑' n : ℕ, d (-((n : ℤ) + 1)) * z ^ (-((n : ℤ) + 1)) =
        ∑ k ∈ Finset.Icc 1 N, μ k * z ^ (-(k : ℤ)) := by
      rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by
        have : ¬ m + 1 ≤ N := by simp at hm; omega
        rw [hdneg, if_neg this, zero_mul])]
      refine Finset.sum_nbij' (fun m => m + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro m hm; simp at hm ⊢; omega
      · intro k hk; simp at hk ⊢; omega
      · intro m _; simp
      · intro k hk; simp at hk; omega
      · intro m hm
        have : m + 1 ≤ N := by simp at hm; omega
        rw [hdneg, if_pos this]
        push_cast
        rfl
    rw [e1, e2, add_comm]
    exact hF
  have hcs : Summable (fun n : ℕ => ‖c n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hr20 : ((r2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < r2 := by linarith
      exact_mod_cast this.ne'
    have := (g2_laurent_of_faber hf hi hf0 hexp hφ hφ0 N μ hr2D hr20).1
    have h2 := (summable_norm_iff.mpr this)
    refine h2.congr (fun n => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnegfin : ∀ (g : ℕ → ℝ), (∀ m : ℕ, N < m → g m = 0) → Summable g := fun g hg =>
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) (fun m hm => hg m (by simpa using hm))
  have hdnegzero : ∀ m : ℕ, N < m → d (-(m : ℤ)) = 0 := fun m hm => by
    have h1 : ¬ (0 : ℤ) ≤ -(m : ℤ) := by omega
    have h2 : (-(-(m : ℤ))).toNat = m := by omega
    show (if (0 : ℤ) ≤ -(m : ℤ) then c (-(m : ℤ)).toNat
      else if (-(-(m : ℤ))).toNat ≤ N then μ (-(-(m : ℤ))).toNat else 0) = 0
    rw [if_neg h1, h2, if_neg (by omega)]
  have hs : Summable fun n : ℤ => ‖d n‖ * max (r1 ^ n) (r2 ^ n) := by
    rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · refine hcs.congr (fun n => ?_)
      rw [hdpos]
      have : max (r1 ^ (n : ℤ)) (r2 ^ (n : ℤ)) = r2 ^ n := by
        rw [zpow_natCast, zpow_natCast]
        exact max_eq_right (pow_le_pow_left₀ hr1pos.le (by linarith) n)
      rw [this]
    · refine hnegfin _ (fun m hm => ?_)
      rw [hdnegzero m hm, norm_zero, zero_mul]
  have hs1 : Summable fun n : ℤ => |(n : ℝ)| * ‖d n‖ * ρ ^ n := by
    rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hcs.tendsto_atTop_zero.bddAbove_range
      have hgeo : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (ρ / r2) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by
          rw [Real.norm_of_nonneg (by positivity)]
          exact (div_lt_one (by linarith)).mpr hρr2)
      refine (hgeo.mul_left (|C|)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      rw [hdpos]
      have h1 : ‖c n‖ * r2 ^ n ≤ |C| := (hC ⟨n, rfl⟩).trans (le_abs_self C)
      have h2 : (0 : ℝ) < r2 ^ n := pow_pos (by linarith) n
      simp only [Int.cast_natCast, Nat.abs_cast, zpow_natCast, pow_one]
      calc (n : ℝ) * ‖c n‖ * ρ ^ n = (n : ℝ) * ((‖c n‖ * r2 ^ n) * (ρ / r2) ^ n) := by
            rw [div_pow]; field_simp
        _ ≤ (n : ℝ) * (|C| * (ρ / r2) ^ n) := by gcongr
        _ = |C| * ((n : ℝ) * (ρ / r2) ^ n) := by ring
    · refine hnegfin _ (fun m hm => ?_)
      rw [hdnegzero m hm, norm_zero, mul_zero, zero_mul]
  -- decay of h'
  have hderiv : ∀ w : ℂ, w ≠ 0 → deriv h w =
      ∑ l ∈ Finset.Icc 1 N, ν l * (((-(l : ℤ) : ℤ) : ℂ) * w ^ (-(l : ℤ) - 1)) := by
    intro w hw
    have hd : HasDerivAt h (∑ l ∈ Finset.Icc 1 N, ν l * (((-(l : ℤ) : ℤ) : ℂ) * w ^ (-(l : ℤ) - 1))) w := by
      apply HasDerivAt.fun_sum
      intro l _
      exact (hasDerivAt_zpow (-(l : ℤ)) w (Or.inl hw)).const_mul (ν l)
    exact hd.deriv
  have hdecay : ∃ C R : ℝ, ∀ w : ℂ, R < ‖w‖ → ‖deriv h w‖ ≤ C / ‖w‖ ^ 2 := by
    refine ⟨∑ l ∈ Finset.Icc 1 N, (l : ℝ) * ‖ν l‖, 1, fun w hw => ?_⟩
    have hw0 : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw; linarith
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rw [hderiv w hw0]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    rw [norm_mul, norm_mul, norm_zpow, Complex.norm_intCast]
    have hzp : ‖w‖ ^ (-(l : ℤ) - 1) ≤ ‖w‖ ^ (-(2 : ℤ)) :=
      zpow_le_zpow_right₀ hw.le (by omega)
    have : ‖w‖ ^ (-(2 : ℤ)) = 1 / ‖w‖ ^ 2 := by
      rw [zpow_neg, zpow_ofNat, one_div]
    rw [this] at hzp
    calc ‖ν l‖ * (|((-(l : ℤ) : ℤ) : ℝ)| * ‖w‖ ^ (-(l : ℤ) - 1))
        ≤ ‖ν l‖ * ((l : ℝ) * (1 / ‖w‖ ^ 2)) := by
          gcongr
          simp
        _ = (l : ℝ) * ‖ν l‖ / ‖w‖ ^ 2 := by ring
  have hh : DifferentiableOn ℂ h {0}ᶜ := by
    apply DifferentiableOn.fun_sum
    intro l _
    exact (differentiableOn_const _).mul (differentiableOn_zpow _ _ (Or.inl (by simp)))
  have hG := green_exterior_image hf hi hf0 hρ0 hρ1 hh hdecay
  have hP := g2_laurent_parseval hr1pos hr1ρ hρr2 hs hs1
  -- identify the two integrals
  have hcirc : ∀ θ : ℝ, r1 < ‖circleMap 0 ρ θ‖ ∧ ‖circleMap 0 ρ θ‖ < r2 := fun θ => by
    simp only [norm_circleMap_zero, abs_of_pos hρ0]
    exact ⟨hr1ρ, hρr2⟩
  have hint : ∫ θ in (0 : ℝ)..2 * π, conj (h (f (circleMap 0 ρ θ))) *
        deriv (fun z => h (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ =
      ∫ θ in (0 : ℝ)..2 * π, conj (∑' n : ℤ, d n * (circleMap 0 ρ θ) ^ n) *
        deriv (fun w : ℂ => ∑' n : ℤ, d n * w ^ n) (circleMap 0 ρ θ) * circleMap 0 ρ θ := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hU : IsOpen {w : ℂ | r1 < ‖w‖ ∧ ‖w‖ < r2} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hev : (fun z => h (f z)) =ᶠ[𝓝 (circleMap 0 ρ θ)] fun w : ℂ => ∑' n : ℤ, d n * w ^ n := by
      filter_upwards [hU.mem_nhds (hcirc θ)] with w hw
      exact hlaurent w hw.1 hw.2
    rw [hev.deriv_eq, hlaurent _ (hcirc θ).1 (hcirc θ).2]
  rw [hint, hP] at hG
  -- real-valued weights
  have hs0 : Summable fun n : ℤ => ‖d n‖ * ρ ^ n :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by gcongr; exact g2_zpow_le_max hr1pos hr1ρ.le hρr2.le n) hs
  have hB : ∀ n : ℤ, ‖d n‖ * ρ ^ n ≤ ∑' m : ℤ, ‖d m‖ * ρ ^ m := fun n =>
    hs0.le_tsum n (fun m _ => by positivity)
  have hgs : Summable fun n : ℤ => (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) := by
    refine ((hs1.mul_left (∑' m : ℤ, ‖d m‖ * ρ ^ m)).of_norm_bounded (fun n => ?_))
    have e : (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) =
        ((n : ℝ) * (‖d n‖ * ρ ^ n)) * (‖d n‖ * ρ ^ n) := by
      rw [show 2 * n = n + n by ring, zpow_add₀ hρ0.ne']; ring
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n),
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖d n‖ * ρ ^ n)]
    calc |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (‖d n‖ * ρ ^ n)
        ≤ |(n : ℝ)| * (‖d n‖ * ρ ^ n) * (∑' m : ℤ, ‖d m‖ * ρ ^ m) := by
          gcongr; exact hB n
      _ = (∑' m : ℤ, ‖d m‖ * ρ ^ m) * (|(n : ℝ)| * ‖d n‖ * ρ ^ n) := by ring
  have hT : ((∑' n : ℤ, (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) : ℝ) : ℂ) =
      ∑' n : ℤ, (n : ℂ) * ((‖d n‖ ^ 2 * ρ ^ (2 * n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  rw [← hT] at hG
  have hJ : (0 : ℝ) ≤ ∫ w in (f '' closedBall (0 : ℂ) ρ)ᶜ, ‖deriv h w‖ ^ 2 :=
    integral_nonneg (fun w => by positivity)
  have hTle : ∑' n : ℤ, (n : ℝ) * (‖d n‖ ^ 2 * ρ ^ (2 * n)) ≤ 0 := by
    have hre := congrArg Complex.re hG
    simp at hre
    have hπ : 0 < π := Real.pi_pos
    nlinarith
  -- split
  have hgn : Summable fun n : ℕ => ((n : ℤ) : ℝ) * (‖d (n : ℤ)‖ ^ 2 * ρ ^ (2 * (n : ℤ))) :=
    hgs.comp_injective Nat.cast_injective
  have hgm : Summable fun n : ℕ => ((-((n : ℤ) + 1) : ℤ) : ℝ) *
      (‖d (-((n : ℤ) + 1))‖ ^ 2 * ρ ^ (2 * (-((n : ℤ) + 1)))) :=
    hnegfin _ (fun m hm => by
      have := hdnegzero (m + 1) (by omega)
      rw [show (-(((m + 1 : ℕ) : ℤ))) = -((m : ℤ) + 1) by push_cast; ring] at this
      rw [this]; simp)
  rw [tsum_of_nat_of_neg_add_one hgn hgm] at hTle
  have hpos' : (fun p : ℕ => ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1))) =
      fun p : ℕ => ((((p + 1 : ℕ) : ℤ) : ℝ)) *
        (‖d (((p + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((p + 1 : ℕ) : ℤ)))) := by
    funext p
    rw [hdpos, show (2 * (((p + 1 : ℕ) : ℤ))) = (((2 * (p + 1) : ℕ)) : ℤ) by push_cast; ring,
      zpow_natCast]
    push_cast; ring
  have hsum1 : Summable (fun p : ℕ => ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1))) := by
    rw [hpos']
    exact (summable_nat_add_iff 1).mpr hgn
  refine ⟨hsum1, ?_⟩
  have hnegval : ∑' n : ℕ, ((-((n : ℤ) + 1) : ℤ) : ℝ) *
      (‖d (-((n : ℤ) + 1))‖ ^ 2 * ρ ^ (2 * (-((n : ℤ) + 1)))) =
      -∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖μ k‖ ^ 2 * (ρ ^ (2 * k))⁻¹ := by
    rw [tsum_eq_sum (s := Finset.range N) (fun m hm => by
      have : ¬ m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_neg this]; simp)]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun m => m + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk ⊢; omega
    · intro m _; simp
    · intro k hk; simp at hk; omega
    · intro m hm
      have : m + 1 ≤ N := by simp at hm; omega
      rw [hdneg, if_pos this]
      have e : ρ ^ (2 * (-((m : ℤ) + 1))) = (ρ ^ (2 * (m + 1)))⁻¹ := by
        rw [show 2 * (-((m : ℤ) + 1)) = -((2 * (m + 1) : ℕ) : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast]
      rw [e]; push_cast; ring
  rw [hnegval, hgn.tsum_eq_zero_add] at hTle
  have h0 : ((((0 : ℕ) : ℤ) : ℝ)) * (‖d (((0 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((0 : ℕ) : ℤ)))) = 0 := by simp
  rw [h0, zero_add] at hTle
  have : ∑' p : ℕ, ((((p + 1 : ℕ) : ℤ) : ℝ)) *
        (‖d (((p + 1 : ℕ) : ℤ))‖ ^ 2 * ρ ^ (2 * (((p + 1 : ℕ) : ℤ)))) =
      ∑' p : ℕ, ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1)) := by
    exact (congrArg tsum hpos').symm
  rw [this] at hTle
  linarith

theorem g2_sum_Icc_range (N : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 N, F k = ∑ n ∈ Finset.range N, F (n + 1) := by
  refine Finset.sum_nbij' (fun k => k - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp at hk ⊢; omega
  · intro n hn; simp at hn ⊢; omega
  · intro k hk; simp at hk; omega
  · intro n _; simp
  · intro k hk; simp at hk
    congr 1; omega

theorem g2_sum_Icc_range_real (N : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N, F k = ∑ n ∈ Finset.range N, F (n + 1) := by
  refine Finset.sum_nbij' (fun k => k - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp at hk ⊢; omega
  · intro n hn; simp at hn ⊢; omega
  · intro k hk; simp at hk; omega
  · intro n _; simp
  · intro k hk; simp at hk
    congr 1; omega

/-- finite-support Grunsky inequality, row partial sums. -/
theorem g2_B1_finite {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℕ → ℂ} {b00 : ℂ}
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
        (f z - f w) / (z - w) = exp (b00 - S))
    (N P : ℕ) (x : ℕ → ℂ) :
    ∑ p ∈ Finset.range P, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2 ≤
      ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 := by
  set μ : ℕ → ℂ := fun k => x (k - 1) / ((Real.sqrt (k : ℝ) : ℝ) : ℂ) with hμ
  have hsq : ∀ n : ℕ, ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2 = (n : ℂ) + 1 := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  have hne : ∀ n : ℕ, ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := fun n => by
    have : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  -- the inner sums
  have hE : ∀ p : ℕ, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2 =
      ((p : ℝ) + 1) * ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 := by
    intro p
    rw [g2_sum_Icc_range]
    have h1 : ∑ n ∈ Finset.range N, ((Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℝ) : ℂ) *
          a (p + 1) (n + 1) * x n =
        ((Real.sqrt ((p : ℝ) + 1) : ℝ) : ℂ) *
          ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℂ) * μ (n + 1) * a (p + 1) (n + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Real.sqrt_mul (by positivity)]
      simp only [hμ, Nat.add_sub_cancel]
      push_cast
      have := hsq n
      have h2 := hne n
      have h3 : ((n : ℂ) + 1) = ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2 := this.symm
      rw [h3]
      field_simp
    rw [h1, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity)]
  have hR : ∀ ρ : ℝ, ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖μ k‖ ^ 2 * (ρ ^ (2 * k))⁻¹ =
      ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 * (ρ ^ (2 * (n + 1)))⁻¹ := by
    intro ρ
    rw [g2_sum_Icc_range_real]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hμ, Nat.add_sub_cancel, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    push_cast
    have h2 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  -- for each ρ
  have hρ : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∑ p ∈ Finset.range P, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2 *
          ρ ^ (2 * (p + 1)) ≤
      ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 * (ρ ^ (2 * (n + 1)))⁻¹ := by
    intro ρ h0 h1
    obtain ⟨hsum, hle⟩ := g2_grunsky_finite hf hi hf0 hexp h0 h1 N μ
    rw [hR] at hle
    refine le_trans ?_ hle
    have hnn : ∀ p : ℕ, 0 ≤ ((p + 1 : ℕ) : ℝ) *
        ‖∑ k ∈ Finset.Icc 1 N, (k : ℂ) * μ k * a (p + 1) k‖ ^ 2 * ρ ^ (2 * (p + 1)) :=
      fun p => by positivity
    refine le_trans (le_of_eq ?_) (hsum.sum_le_tsum (Finset.range P) (fun p _ => hnn p))
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hE p]; push_cast; ring
  -- limit ρ → 1
  have hlim1 : Tendsto (fun ρ : ℝ => ∑ p ∈ Finset.range P, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2 *
          ρ ^ (2 * (p + 1))) (𝓝[<] 1)
      (𝓝 (∑ p ∈ Finset.range P, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    have : Continuous (fun ρ : ℝ => ∑ p ∈ Finset.range P, ‖∑ n ∈ Finset.range N,
        (Real.sqrt (((p : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (p + 1) (n + 1) * x n‖ ^ 2 *
          ρ ^ (2 * (p + 1))) := by fun_prop
    simpa using this.tendsto 1
  have hlim2 : Tendsto (fun ρ : ℝ => ∑ n ∈ Finset.range N, ‖x n‖ ^ 2 * (ρ ^ (2 * (n + 1)))⁻¹) (𝓝[<] 1)
      (𝓝 (∑ n ∈ Finset.range N, ‖x n‖ ^ 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    refine tendsto_finset_sum _ (fun n _ => ?_)
    have : ContinuousAt (fun ρ : ℝ => (ρ ^ (2 * (n + 1)))⁻¹) 1 :=
      ContinuousAt.inv₀ (by fun_prop) (by simp)
    simpa using this.tendsto.const_mul (‖x n‖ ^ 2)
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρm
  exact hρ ρ hρm.1 hρm.2

theorem g2_B1_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsymm : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧ (f z - f w) / (z - w) = exp (b00 - S))
    (x : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) :
    (∑' m : ℕ, ‖∑' n : ℕ, (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1) * x n‖ ^ 2) ≤
      ∑' n : ℕ, ‖x n‖ ^ 2 := by
  set c : ℕ → ℕ → ℂ := fun m n => (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1)
    with hc
  have hcs : ∀ m n, c m n = c n m := fun m n => by
    simp only [hc, hsymm (m + 1) (n + 1), mul_comm ((m : ℝ) + 1)]
  have hcol : ∀ n P : ℕ, ∑ p ∈ Finset.range P, ‖c p n‖ ^ 2 ≤ 1 := by
    intro n P
    have h := g2_B1_finite hf hi hf0 hexp (n + 1) P (fun j => if j = n then 1 else 0)
    have e1 : ∀ p : ℕ, ∑ j ∈ Finset.range (n + 1),
        (Real.sqrt (((p : ℝ) + 1) * ((j : ℝ) + 1)) : ℂ) * a (p + 1) (j + 1) *
          (if j = n then (1 : ℂ) else 0) = c p n := fun p => by
      rw [Finset.sum_eq_single n]
      · simp [hc]
      · intro j _ hj; simp [hj]
      · intro hn; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn
    have h' : ∑ p ∈ Finset.range P, ‖c p n‖ ^ 2 ≤
        ∑ j ∈ Finset.range (n + 1), ‖(if j = n then (1 : ℂ) else 0)‖ ^ 2 := by
      simpa only [e1] using h
    refine h'.trans (le_of_eq ?_)
    rw [Finset.sum_eq_single n]
    · simp
    · intro j _ hj; simp [hj]
    · intro hn; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn
  have hrow : ∀ m : ℕ, Summable fun n : ℕ => ‖c m n‖ ^ 2 := fun m =>
    summable_of_sum_range_le (fun _ => sq_nonneg _) (c := 1) (fun P => by
      simpa [hcs m] using hcol m P)
  have hconv : ∀ m : ℕ, Summable fun n : ℕ => ‖c m n * x n‖ := fun m => by
    refine (((hrow m).add hx).div_const 2).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖c m n‖ - ‖x n‖)]
  have hhas : ∀ m : ℕ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, c m n * x n) atTop
      (𝓝 (∑' n : ℕ, c m n * x n)) := fun m =>
    (hconv m).of_norm.hasSum.tendsto_sum_nat
  refine Real.tsum_le_of_sum_range_le (fun m => sq_nonneg _) (fun M => ?_)
  have T : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, c m n * x n‖ ^ 2)
      atTop (𝓝 (∑ m ∈ Finset.range M, ‖∑' n : ℕ, c m n * x n‖ ^ 2)) :=
    tendsto_finset_sum _ (fun m _ => (((continuous_norm.tendsto _).comp (hhas m)).pow 2))
  refine le_of_tendsto T (Eventually.of_forall fun N => ?_)
  exact (g2_B1_finite hf hi hf0 hexp N M x).trans
    (Summable.sum_le_tsum (Finset.range N) (fun _ _ => sq_nonneg _) hx)

theorem g2_B1_general {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsymm : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧ (f z - f w) / (z - w) = exp (b00 - S))
    (x : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) :
    (∑' m : ℕ, ‖∑' n : ℕ, (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1) * x n‖ ^ 2) ≤
      ∑' n : ℕ, ‖x n‖ ^ 2 := by
  refine g2_B1_zero (f := fun z => f z - f 0) (b00 := b00) (hf.sub_const _) ?_ (by simp) hsymm ?_ x hx
  · intro z hz w hw hzw
    exact hi hz hw (sub_left_injective hzw)
  · intro z hz w hw hzw
    obtain ⟨S, h1, h2⟩ := hexp z hz w hw hzw
    refine ⟨S, h1, ?_⟩
    rw [← h2]
    congr 1
    ring

/-- (G2b) Grunsky's inequality `‖B₁‖ ≤ 1` for a single normalized univalent `f` (`ℓ²` form), for any array `a`
(`a m n = b_{-m,-n}`) with the defining expansion of `(f z - f w)/(z - w)`. -/
theorem grunsky_B1_bound {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : deriv f 0 = 1) {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsymm : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧ (f z - f w) / (z - w) = exp (b00 - S))
    (x : ℕ → ℂ) (hx : Summable fun n => ‖x n‖ ^ 2) :
    (∑' m : ℕ, ‖∑' n : ℕ, (Real.sqrt (((m : ℝ) + 1) * ((n : ℝ) + 1)) : ℂ) * a (m + 1) (n + 1) * x n‖ ^ 2) ≤
      ∑' n : ℕ, ‖x n‖ ^ 2 :=
  g2_B1_general hf hi hsymm hexp x hx

/-- Termwise differentiation for a countable family of monomials, using convergence
on one larger circle to supply the uniform summable bound. -/
theorem g2c_monomial_deriv {ι : Type*} [Countable ι] {d : ι → ℂ} {k : ι → ℕ}
    {R : ℝ} (hR : 0 < R) (hs : Summable (fun i => d i * (R : ℂ) ^ k i))
    {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun i => d i * (k i : ℂ) * z ^ (k i - 1))
      (deriv (fun u => ∑' i, d i * u ^ k i) z) := by
  have hb : Summable (fun i => ‖d i‖ * R ^ k i) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR] using hs.norm
  have hd : ∀ i, DifferentiableOn ℂ (fun u => d i * u ^ k i) (ball 0 R) :=
    fun i => ((differentiable_const (d i)).mul (differentiable_id.pow _)).differentiableOn
  have hbound : ∀ i (u : ℂ), u ∈ ball 0 R → ‖d i * u ^ k i‖ ≤ ‖d i‖ * R ^ k i := by
    intro i u hu
    rw [norm_mul, norm_pow]
    gcongr
    exact (mem_ball_zero_iff.mp hu).le
  have h := Complex.hasSum_deriv_of_summable_norm hb hd isOpen_ball hbound
    (mem_ball_zero_iff.mpr hz)
  simpa only [deriv_const_mul_field, deriv_pow_field, mul_assoc] using h

/-- First partial derivative of an actual double power series on the bidisk. -/
theorem g2c_double_series_deriv_left {a : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun p : ℕ × ℕ => a p.1 p.2 * (p.1 : ℂ) * z ^ (p.1 - 1) * w ^ p.2)
      (deriv (fun u => F u w) z) := by
  obtain ⟨R, hzR, hR1⟩ := exists_between (mem_ball_zero_iff.mp hz)
  have hR : 0 < R := (norm_nonneg z).trans_lt hzR
  have hRD : (R : ℂ) ∈ unitDisc := by
    simpa [unitDisc, abs_of_pos hR] using hR1
  have hsum : Summable (fun p : ℕ × ℕ => (a p.1 p.2 * w ^ p.2) * (R : ℂ) ^ p.1) := by
    convert (hs (R : ℂ) hRD w hw).summable using 1
    funext p; ring
  have hd := g2c_monomial_deriv (d := fun p : ℕ × ℕ => a p.1 p.2 * w ^ p.2)
    (k := Prod.fst) hR hsum hzR
  have he : (fun u => ∑' p : ℕ × ℕ, (a p.1 p.2 * w ^ p.2) * u ^ p.1) =ᶠ[𝓝 z]
      (fun u => F u w) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz] with u hu
    convert (hs u hu w hw).tsum_eq using 1
    congr 1; funext p; ring
  rw [he.deriv_eq] at hd
  exact hd.congr_fun (fun p => by ring)

/-- The mixed derivative is the genuinely convergent, twice differentiated double series. -/
theorem g2c_double_series_deriv_mixed {a : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun p : ℕ × ℕ => a p.1 p.2 * (p.1 : ℂ) * (p.2 : ℂ) *
      z ^ (p.1 - 1) * w ^ (p.2 - 1))
      (deriv (fun v => deriv (fun u => F u v) z) w) := by
  obtain ⟨R, hwR, hR1⟩ := exists_between (mem_ball_zero_iff.mp hw)
  have hR : 0 < R := (norm_nonneg w).trans_lt hwR
  have hRD : (R : ℂ) ∈ unitDisc := by
    simpa [unitDisc, abs_of_pos hR] using hR1
  have hd := g2c_monomial_deriv
    (d := fun p : ℕ × ℕ => a p.1 p.2 * (p.1 : ℂ) * z ^ (p.1 - 1))
    (k := Prod.snd) hR (g2c_double_series_deriv_left hs hz hRD).summable hwR
  have he : (fun v => ∑' p : ℕ × ℕ, a p.1 p.2 * (p.1 : ℂ) * z ^ (p.1 - 1) * v ^ p.2)
      =ᶠ[𝓝 w] (fun v => deriv (fun u => F u v) z) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hw] with v hv
    exact (g2c_double_series_deriv_left hs hz hv).tsum_eq
  rw [he.deriv_eq] at hd
  exact hd.congr_fun (fun p => by ring)

/-- The first logarithmic derivative of the divided difference, off the diagonal. -/
theorem g2c_log_dslope_deriv {f : ℂ → ℂ} {L : ℂ × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hL : DifferentiableOn ℂ L (unitDisc ×ˢ unitDisc))
    (he : ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = dslope f p.1 p.2)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    deriv (fun u => L (u, w)) z = deriv f z / (f z - f w) - 1 / (z - w) := by
  have hzn : z - w ≠ 0 := sub_ne_zero.mpr hzw
  have hfn : f z - f w ≠ 0 := sub_ne_zero.mpr (fun h => hzw (hi hz hw h))
  have hLf : DifferentiableAt ℂ (fun u => L (u, w)) z :=
    (hL.differentiableAt (x := (z,w))
      ((show IsOpen (unitDisc ×ˢ unitDisc) from isOpen_ball.prod isOpen_ball).mem_nhds ⟨hz, hw⟩)).comp z
      (differentiableAt_id.prodMk (differentiableAt_const w))
  have hExp := hLf.hasDerivAt.cexp
  have hQ := ((hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f w)).div
    ((hasDerivAt_id z).sub_const w) hzn
  have hev : (fun u => exp (L (u, w))) =ᶠ[𝓝 z] (fun u => (f u - f w) / (u - w)) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hz,
      eventually_ne_nhds hzw] with u hu huw
    rw [he (u,w) ⟨hu,hw⟩, dslope_swap, dslope_of_ne f huw, slope_def_field]
  have hder := hExp.unique (hQ.congr_of_eventuallyEq hev)
  have hez : exp (L (z,w)) = (f z - f w) / (z - w) := hev.eq_of_nhds
  rw [hez] at hder
  calc
    deriv (fun u => L (u,w)) z =
        ((deriv f z * (z-w) - (f z-f w) * 1) / (z-w)^2) / ((f z-f w)/(z-w)) := by
      apply (eq_div_iff (div_ne_zero hfn hzn)).mpr
      simpa [mul_comm] using hder
    _ = deriv f z / (f z-f w) - 1/(z-w) := by field_simp [hfn, hzn]

/-- The mixed logarithmic derivative equals the defining quotient for the Grunsky kernel. -/
theorem g2c_log_dslope_deriv_mixed {f : ℂ → ℂ} {L : ℂ × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hL : DifferentiableOn ℂ L (unitDisc ×ˢ unitDisc))
    (he : ∀ p ∈ unitDisc ×ˢ unitDisc, exp (L p) = dslope f p.1 p.2)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    deriv (fun v => deriv (fun u => L (u,v)) z) w =
      deriv f z * deriv f w / (f z-f w)^2 - 1/(z-w)^2 := by
  have hzn : z-w ≠ 0 := sub_ne_zero.mpr hzw
  have hfn : f z-f w ≠ 0 := sub_ne_zero.mpr (fun h => hzw (hi hz hw h))
  have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hd := ((hasDerivAt_const w (deriv f z)).div (hfd.const_sub (f z)) hfn).sub
    ((hasDerivAt_const w (1 : ℂ)).div ((hasDerivAt_id w).const_sub z) hzn)
  have hev : (fun v => deriv (fun u => L (u,v)) z) =ᶠ[𝓝 w]
      (fun v => deriv f z / (f z-f v) - 1/(z-v)) := by
    filter_upwards [(isOpen_ball : IsOpen unitDisc).mem_nhds hw,
      eventually_ne_nhds (Ne.symm hzw)] with v hv hvz
    exact g2c_log_dslope_deriv hf hi hL he hz hv (Ne.symm hvz)
  rw [hev.deriv_eq]
  convert hd.deriv using 1 <;> simp [Pi.sub_def, Pi.div_def]

/-- Reindex the mixed derivative after dropping the zero row and zero column. -/
theorem g2c_double_series_deriv_mixed_succ {a : ℕ → ℕ → ℂ} {F : ℂ → ℂ → ℂ}
    (hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (F z w))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    HasSum (fun p : ℕ × ℕ => a (p.1+1) (p.2+1) * ((p.1+1 : ℕ) : ℂ) *
      ((p.2+1 : ℕ) : ℂ) * z ^ p.1 * w ^ p.2)
      (deriv (fun v => deriv (fun u => F u v) z) w) := by
  let shift : ℕ × ℕ → ℕ × ℕ := fun p => (p.1+1,p.2+1)
  have hinj : Function.Injective shift := by
    intro p q hpq
    simpa [shift, Prod.ext_iff] using hpq
  have hzero : ∀ p ∉ Set.range shift,
      a p.1 p.2 * (p.1 : ℂ) * (p.2 : ℂ) * z ^ (p.1-1) * w ^ (p.2-1) = 0 := by
    rintro ⟨m,n⟩ hp
    cases m with
    | zero => simp
    | succ m =>
      cases n with
      | zero => simp
      | succ n => exact False.elim (hp ⟨(m,n),rfl⟩)
  have h := (hinj.hasSum_iff hzero).mpr (g2c_double_series_deriv_mixed hs hz hw)
  simpa [shift, Function.comp_def] using h

/-- A normalized univalent function admits one symmetric coefficient array whose
convergent mixed derivative is the actual Grunsky kernel off the diagonal. -/
theorem g2c_normalized_kernel_series_exists {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1) :
    ∃ a : ℕ → ℕ → ℂ, (∀ m n, a m n = a n m) ∧
      (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
        HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) S ∧
          (f z-f w)/(z-w) = exp (0-S)) ∧
      ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
        HasSum (fun p : ℕ × ℕ => a (p.1+1) (p.2+1) * ((p.1+1 : ℕ) : ℂ) *
          ((p.2+1 : ℕ) : ℂ) * z ^ p.1 * w ^ p.2) ((π : ℂ) * kerK1 f z w) := by
  obtain ⟨L,hLd,hL0,hLe⟩ := exists_bidisk_divided_difference_log hf hi hf0
  let a := bidiskCauchyCoeff (fun p => -L p) (1/2)
  have hs : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2 * z ^ p.1 * w ^ p.2) (-L (z,w)) :=
    fun z hz w hw => hasSum_bidiskCauchyCoeff_unitDisc hLd.neg hz hw
  refine ⟨a, ?_, ?_, ?_⟩
  · apply double_powerSeries_symm hs
    intro z hz w hw
    rw [bidisk_divided_difference_log_symm hLd.continuousOn hLe z hz w hw]
  · intro z hz w hw hzw
    refine ⟨-L (z,w), hs z hz w hw, ?_⟩
    have he := hLe (z,w) ⟨hz,hw⟩
    rw [dslope_swap, dslope_of_ne f hzw, slope_def_field] at he
    simpa using he.symm
  · intro z hz w hw hzw
    have hd := g2c_double_series_deriv_mixed_succ hs hz hw
    simp only [deriv.fun_neg] at hd
    rw [g2c_log_dslope_deriv_mixed hf hi hLd hLe hz hw hzw] at hd
    convert hd using 1
    rw [kerK1_of_ne f hzw]
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    <;> ring

/-- Affine postcomposition does not change the off-diagonal kernel. -/
theorem g2c_kerK1_affine_of_ne {f : ℂ → ℂ} {α c z w : ℂ} (hα : α ≠ 0)
    (hfz : DifferentiableAt ℂ f z) (hfw : DifferentiableAt ℂ f w) (hzw : z ≠ w) :
    kerK1 (fun u => α * f u + c) z w = kerK1 f z w := by
  rw [kerK1_of_ne _ hzw, kerK1_of_ne _ hzw,
    (hfz.hasDerivAt.const_mul α |>.add_const c).deriv,
    (hfw.hasDerivAt.const_mul α |>.add_const c).deriv]
  rw [show α*f z+c-(α*f w+c) = α*(f z-f w) by ring, mul_pow,
    show α*deriv f z*(α*deriv f w) = α^2*(deriv f z*deriv f w) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hα)]

/-- The affine kernel equality holds almost everywhere on the disk, including
the situation needed by the integral operator. -/
theorem g2c_kerK1_affine_ae {f : ℂ → ℂ} {α c : ℂ} (hα : α ≠ 0)
    (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    kerK1 (fun u => α*f u+c) z =ᵐ[volume.restrict unitDisc] kerK1 f z := by
  filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
    (volume.restrict unitDisc).ae_ne z] with w hw hwz
  exact g2c_kerK1_affine_of_ne hα (hf.differentiableAt (isOpen_ball.mem_nhds hz))
    (hf.differentiableAt (isOpen_ball.mem_nhds hw)) (Ne.symm hwz)

/-- Consequently every kernel integral, without an extra integrability premise,
is invariant under nondegenerate affine postcomposition. -/
theorem g2c_kerK1_affine_integral {f : ℂ → ℂ} {α c : ℂ} (hα : α ≠ 0)
    (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : z ∈ unitDisc) (ψ : ℂ → ℂ) :
    (∫ w in unitDisc, kerK1 (fun u => α*f u+c) z w * conj (ψ w)) =
      ∫ w in unitDisc, kerK1 f z w * conj (ψ w) := by
  apply integral_congr_ae
  filter_upwards [g2c_kerK1_affine_ae (c := c) hα hf hz] with w hw
  rw [hw]

/-- Reduction of an arbitrary univalent map to derivative one at the origin,
preserving its integral kernel almost everywhere. -/
theorem g2c_univalent_normalization {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ InjOn F unitDisc ∧ deriv F 0 = 1 ∧
      ∀ z ∈ unitDisc, kerK1 F z =ᵐ[volume.restrict unitDisc] kerK1 f z := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd0 : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf hi h0
  let α : ℂ := (deriv f 0)⁻¹
  have hα : α ≠ 0 := inv_ne_zero hd0
  refine ⟨fun u => α*f u+0, ((differentiableOn_const α).mul hf).add_const 0, ?_, ?_, ?_⟩
  · intro z hz w hw he
    apply hi hz hw
    exact mul_left_cancel₀ hα (by simpa using he)
  · rw [((hf.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.const_mul α |>.add_const 0).deriv]
    exact inv_mul_cancel₀ hd0
  · intro z hz
    exact g2c_kerK1_affine_ae hα hf hz

/-- Finite matrix contraction controls actual square-summable outputs, including
the summability that a bare real-valued `tsum` inequality would not assert. -/
theorem g2c_matrix_contraction {B : ℕ → ℕ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hfinite : ∀ N M (x : ℕ → ℂ),
      (∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, B m n*x n‖^2) ≤
        ∑ n ∈ Finset.range N, ‖x n‖^2) :
    (∀ m, Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1) ∧
    ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖^2) →
      (∀ m, Summable (fun n => ‖B m n*x n‖)) ∧
      Summable (fun m => ‖∑' n, B m n*x n‖^2) ∧
      (∑' m, ‖∑' n, B m n*x n‖^2) ≤ ∑' n, ‖x n‖^2 := by
  have hcol (n M : ℕ) : ∑ m ∈ Finset.range M, ‖B m n‖^2 ≤ 1 := by
    have hh := hfinite (n+1) M (fun j => if j=n then 1 else 0)
    have he (m : ℕ) : (∑ j ∈ Finset.range (n+1), B m j*(if j=n then 1 else 0)) = B m n := by
      simp [Finset.sum_ite_eq', Finset.mem_range]
    simpa only [he, apply_ite (fun z : ℂ => ‖z‖^2), norm_one, one_pow,
      norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq',
      Finset.mem_range, Nat.lt_succ_self, if_true] using hh
  have hrow (m : ℕ) : Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1 := by
    have hb (N : ℕ) : ∑ n ∈ Finset.range N, ‖B m n‖^2 ≤ 1 := by
      simpa only [hsym m] using hcol m N
    exact ⟨summable_of_sum_range_le (fun _ => sq_nonneg _) hb,
      Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hb⟩
  refine ⟨hrow, ?_⟩
  intro x hx
  have hconv (m : ℕ) : Summable (fun n => ‖B m n*x n‖) :=
    bergman_pair_summable (hrow m).1 hx
  have hb (M : ℕ) : (∑ m ∈ Finset.range M, ‖∑' n, B m n*x n‖^2) ≤ ∑' n, ‖x n‖^2 := by
    have ht : Tendsto (fun N => ∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, B m n*x n‖^2)
        atTop (𝓝 (∑ m ∈ Finset.range M, ‖∑' n, B m n*x n‖^2)) := by
      apply tendsto_finsetSum
      intro m _
      exact (hconv m).of_norm.hasSum.tendsto_sum_nat.norm.pow 2
    apply le_of_tendsto ht
    exact Eventually.of_forall fun N => (hfinite N M x).trans
      (hx.sum_le_tsum (Finset.range N) (fun _ _ => sq_nonneg _))
  exact ⟨hconv, summable_of_sum_range_le (fun _ => sq_nonneg _) hb,
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hb⟩

/-- The proved finite Grunsky inequality supplies the hypotheses of the honest
ell2 matrix contraction interface. No Faber or kernel placeholder is used. -/
theorem g2c_grunsky_matrix_contraction {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsym : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧
        (f z-f w)/(z-w) = exp (b00-S)) :
    let B : ℕ → ℕ → ℂ := fun m n =>
      (Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ)*a (m+1) (n+1)
    (∀ m, Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1) ∧
    ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖^2) →
      (∀ m, Summable (fun n => ‖B m n*x n‖)) ∧
      Summable (fun m => ‖∑' n, B m n*x n‖^2) ∧
      (∑' m, ‖∑' n, B m n*x n‖^2) ≤ ∑' n, ‖x n‖^2 := by
  apply g2c_matrix_contraction
  · intro m n
    simp only [hsym (m+1) (n+1), mul_comm ((m : ℝ)+1)]
  · intro N M x
    have hfi : InjOn (fun z => f z-f 0) unitDisc := by
      intro z hz w hw he
      exact hi hz hw (sub_left_injective he)
    apply g2_B1_finite (f := fun z => f z-f 0) (b00 := b00) (hf.sub_const _) hfi (sub_self _) ?_ N M x
    intro z hz w hw hzw
    obtain ⟨S,hS,he⟩ := hexp z hz w hw hzw
    refine ⟨S,hS,?_⟩
    rw [← he]
    congr 1
    ring

theorem g2c_basis_weight (a : ℕ → ℕ → ℂ) (m n : ℕ) (z w : ℂ) :
    (Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ)*a (m+1) (n+1)*basisE m z*basisE n w =
      (a (m+1) (n+1)*((m+1 : ℕ) : ℂ)*((n+1 : ℕ) : ℂ)*z^m*w^n)/(π : ℂ) := by
  have hr : Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) * Real.sqrt (((m : ℝ)+1)/π) *
      Real.sqrt (((n : ℝ)+1)/π) = ((m : ℝ)+1)*((n : ℝ)+1)/π := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    calc
      _ = (Real.sqrt ((m : ℝ)+1)^2 * Real.sqrt ((n : ℝ)+1)^2) / Real.sqrt π^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt Real.pi_pos.le]
  have hc : (Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ) *
      (Real.sqrt (((m : ℝ)+1)/π) : ℂ)*(Real.sqrt (((n : ℝ)+1)/π) : ℂ) =
        ((m+1 : ℕ) : ℂ)*((n+1 : ℕ) : ℂ)/(π : ℂ) := by exact_mod_cast hr
  dsimp only [basisE]
  calc
    _ = ((Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ) *
      (Real.sqrt (((m : ℝ)+1)/π) : ℂ)*(Real.sqrt (((n : ℝ)+1)/π) : ℂ))*
        a (m+1) (n+1)*z^m*w^n := by ring
    _ = _ := by rw [hc]; ring

/-- Absolute convergence for the matrix/evaluation/input pairing, needed for Fubini. -/
theorem g2c_matrix_pair_absolute {B : ℕ → ℕ → ℂ}
    (hrow : ∀ m, Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1)
    {x e : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖^2)) (he : Summable (fun m => ‖e m‖)) :
    Summable (fun p : ℕ × ℕ => ‖B p.1 p.2*x p.2*e p.1‖) := by
  have hconv (m : ℕ) := bergman_pair_summable (hrow m).1 hx
  let C : ℝ := (1+(∑' n, ‖x n‖^2))/2
  have hb (m : ℕ) : (∑' n, ‖B m n*x n‖) ≤ C := by
    calc
      _ ≤ ∑' n, (‖B m n‖^2+‖x n‖^2)/2 := by
        apply (hconv m).tsum_le_tsum _ (((hrow m).1.add hx).div_const 2)
        intro n
        rw [norm_mul]
        nlinarith [sq_nonneg (‖B m n‖-‖x n‖)]
      _ = ((∑' n, ‖B m n‖^2)+(∑' n, ‖x n‖^2))/2 := by
        rw [tsum_div_const, (hrow m).1.tsum_add hx]
      _ ≤ C := by dsimp [C]; linarith [(hrow m).2]
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  constructor
  · intro m
    simpa only [norm_mul] using (hconv m).mul_right ‖e m‖
  · apply (he.mul_right C).of_nonneg_of_le (fun m => tsum_nonneg (fun n => norm_nonneg _))
    intro m
    simp only [norm_mul]
    rw [tsum_mul_right]
    simpa only [norm_mul, mul_comm C] using mul_le_mul_of_nonneg_right (hb m) (norm_nonneg (e m))

/-- Symmetry identifies the two absolutely convergent coefficient pairings. -/
theorem g2c_matrix_pair_comm {B : ℕ → ℕ → ℂ} (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1)
    {x e : ℕ → ℂ} (hx : Summable (fun n => ‖x n‖^2)) (he : Summable (fun m => ‖e m‖)) :
    (∑' n, (∑' m, B n m*e m)*x n) = (∑' m, (∑' n, B m n*x n)*e m) := by
  have h := (g2c_matrix_pair_absolute hrow hx he).of_norm
  simp only [← tsum_mul_right]
  calc
    _ = ∑' n, ∑' m, B m n*x n*e m := by
      apply tsum_congr; intro n
      apply tsum_congr; intro m
      rw [hsym n m]; ring
    _ = _ := h.tsum_comm

theorem g2c_kernel_row_series {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2*basisE p.1 z*basisE p.2 w) (K z w))
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w)
    (hconv : ∀ n, Summable (fun m => B n m*basisE m z)) :
    HasSum (fun n => (∑' m, B n m*basisE m z)*basisE n w) (K z w) := by
  have hswap : HasSum (fun p : ℕ × ℕ => B p.2 p.1*basisE p.2 z*basisE p.1 w) (K z w) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (hK z hz w hw hzw)
  apply hswap.prod_fiberwise
  intro n
  apply ((hconv n).hasSum.mul_right (basisE n w)).congr_fun
  intro m
  rw [hsym m n]

/-- A symmetric contractive coefficient matrix with an actual off-diagonal
Bergman kernel series yields the corresponding integral-operator norm bound. -/
theorem g2c_bergman_kernel_contraction {B : ℕ → ℕ → ℂ} {K : ℂ → ℂ → ℂ}
    (hsym : ∀ m n, B m n = B n m)
    (hrow : ∀ m, Summable (fun n => ‖B m n‖^2) ∧ (∑' n, ‖B m n‖^2) ≤ 1)
    (hout : ∀ x : ℕ → ℂ, Summable (fun n => ‖x n‖^2) →
      Summable (fun m => ‖∑' n, B m n*x n‖^2) ∧
        (∑' m, ‖∑' n, B m n*x n‖^2) ≤ ∑' n, ‖x n‖^2)
    (hK : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w →
      HasSum (fun p : ℕ × ℕ => B p.1 p.2*basisE p.1 z*basisE p.2 w) (K z w))
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    normA21 unitDisc (fun z => ∫ w in unitDisc, K z w*conj (ψ w)) ≤ normA21 unitDisc ψ := by
  obtain ⟨x,hx,hxe,hxm⟩ := A21_exists_ell2_expansion hψ
  have hxc : Summable (fun n => ‖conj (x n)‖^2) := by simpa only [Complex.norm_conj] using hx
  let y : ℕ → ℂ := fun m => ∑' n, B m n*conj (x n)
  have hy := hout (fun n => conj (x n)) hxc
  let T : ℂ → ℂ := fun z => ∑' m, y m*basisE m z
  have hT : T ∈ A21fun unitDisc ∧ HasSum (fun m => ‖y m‖^2) (∫ z in unitDisc, ‖T z‖^2) :=
    bergman_ell2_series hy.1
  have heq : ∀ z ∈ unitDisc, (∫ w in unitDisc, K z w*conj (ψ w)) = T z := by
    intro z hz
    let d : ℕ → ℂ := fun n => ∑' m, B n m*basisE m z
    have hd := hout (fun m => basisE m z) (basisE_sq_summable hz)
    let H : ℂ → ℂ := fun w => ∑' n, d n*basisE n w
    have hH : H ∈ A21fun unitDisc := (bergman_ell2_series hd.1).1
    have hHexp : ∀ w ∈ unitDisc, HasSum (fun n => d n*basisE n w) (H w) :=
      fun w hw => (bergman_pair_summable hd.1 (basisE_sq_summable hw)).of_norm.hasSum
    have hconv (n : ℕ) : Summable (fun m => B n m*basisE m z) :=
      (bergman_pair_summable (hrow n).1 (basisE_sq_summable hz)).of_norm
    have hAE : K z =ᵐ[volume.restrict unitDisc] H := by
      filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball),
        (volume.restrict unitDisc).ae_ne z] with w hw hwz
      exact (g2c_kernel_row_series hsym hK hz hw (Ne.symm hwz) hconv).tsum_eq.symm
    calc
      _ = ∫ w in unitDisc, H w*conj (ψ w) := by
        apply integral_congr_ae
        filter_upwards [hAE] with w hw
        rw [hw]
      _ = ∑' n, d n*conj (x n) := (A21_basis_pairing hH hψ hHexp hxe).tsum_eq.symm
      _ = T z := g2c_matrix_pair_comm hsym hrow hxc (basisE_norm_summable hz)
  have hnorm : normA21 unitDisc (fun z => ∫ w in unitDisc, K z w*conj (ψ w)) =
      normA21 unitDisc T := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    rw [heq z hz]
  rw [hnorm]
  apply (ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < 2 by norm_num)).mp
  simp only [ENNReal.rpow_two]
  rw [A21_ell2_norm_sq hT.1 hT.2, A21_ell2_norm_sq hψ hxm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Complex.norm_conj] using hy.2

theorem g2c_normalized_opNorm_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : deriv f 0 = 1)
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 f z w*conj (ψ w)) ≤ normA21 unitDisc ψ := by
  obtain ⟨a,hsym,hexp,hker⟩ := g2c_normalized_kernel_series_exists hf hi hf0
  let B : ℕ → ℕ → ℂ := fun m n =>
    (Real.sqrt (((m : ℝ)+1)*((n : ℝ)+1)) : ℂ)*a (m+1) (n+1)
  have hB := g2c_grunsky_matrix_contraction hf hi hsym hexp
  apply g2c_bergman_kernel_contraction (B := B) (K := kerK1 f) ?_ hB.1 ?_ ?_ hψ
  · intro m n
    simp only [B, hsym (m+1) (n+1), mul_comm ((m : ℝ)+1)]
  · intro x hx
    exact (hB.2 x hx).2
  · intro z hz w hw hzw
    have hsum := (hker z hz w hw hzw).div_const (π : ℂ)
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have he : ((π : ℂ)*kerK1 f z w)/(π : ℂ) = kerK1 f z w := by field_simp
    rw [he] at hsum
    exact hsum.congr_fun (fun p => g2c_basis_weight a p.1 p.2 z w)

/-- (G2c) `‖K₁(f)‖ ≤ 1` on `A₂¹(𝔻)` for any univalent `f` (no normalization; `K₁` is invariant under affine
post-composition). Operator form used by Appendix B (`kerOpNorm`). -/
theorem kerK1_opNorm_le {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    {ψ : ℂ → ℂ} (hψ : ψ ∈ A21fun unitDisc) :
    normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 f z w * conj (ψ w)) ≤ normA21 unitDisc ψ := by
  obtain ⟨F,hFd,hFi,hF0,hK⟩ := g2c_univalent_normalization hf hi
  have hnorm : normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 f z w*conj (ψ w)) =
      normA21 unitDisc (fun z => ∫ w in unitDisc, kerK1 F z w*conj (ψ w)) := by
    unfold normA21
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet unitDisc from measurableSet_ball)] with z hz
    have he : (∫ w in unitDisc, kerK1 f z w*conj (ψ w)) =
        ∫ w in unitDisc, kerK1 F z w*conj (ψ w) := by
      apply integral_congr_ae
      filter_upwards [hK z hz] with w hw
      rw [hw]
    rw [he]
  rw [hnorm]
  exact g2c_normalized_opNorm_le hFd hFi hF0 hψ

/-- The finite polynomial determined by the Taylor coefficients of powers. -/
def faberPolynomial (φ a : ℕ → ℕ → ℂ) (k : ℕ) : Polynomial ℂ :=
  (∑ l ∈ Finset.Icc 1 k, Polynomial.monomial l ((k : ℂ)*φ l k/(l : ℂ))) -
    Polynomial.C ((k : ℂ)*a 0 k)

theorem faberPolynomial_coeff (φ a : ℕ → ℕ → ℂ) (k n : ℕ) :
    (faberPolynomial φ a k).coeff n =
      (if n ∈ Finset.Icc 1 k then (k : ℂ)*φ n k/(n : ℂ) else 0) -
        (if n=0 then (k : ℂ)*a 0 k else 0) := by
  simp [faberPolynomial, Polynomial.coeff_monomial, Polynomial.coeff_C]

theorem faberPolynomial_natDegree {φ a : ℕ → ℕ → ℂ} {k : ℕ}
    (hk : 1 ≤ k) (hdiag : φ k k = 1) : (faberPolynomial φ a k).natDegree = k := by
  have hk0 : k ≠ 0 := by omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simp [faberPolynomial_coeff, Finset.mem_Icc, not_le.mpr hn, hn0]
  · simp [faberPolynomial_coeff, Finset.mem_Icc, hk, hk0, hdiag, hkC]

theorem faberPolynomial_eval_inv (φ a : ℕ → ℕ → ℂ) (k : ℕ) (w : ℂ) :
    (faberPolynomial φ a k).eval w⁻¹ =
      (k : ℂ)*(∑ l ∈ Finset.Icc 1 k, φ l k/((l : ℂ)*w^l)) - (k : ℂ)*a 0 k := by
  simp only [faberPolynomial, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Polynomial.eval_C, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Actual Faber polynomials for the negative branch of any normalized disk map
with a symmetric logarithmic coefficient array. -/
theorem faber_negative_polynomials {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc)
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    {a : ℕ → ℕ → ℂ} {b00 : ℂ} (hsym : ∀ m n, a m n = a n m)
    (hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧
        (f z-f w)/(z-w) = exp (b00-S)) :
    ∃ Q : ℕ → Polynomial ℂ, (∀ n, (Q (n+1)).natDegree = n+1) ∧
      ∀ n, ∀ z ∈ unitDisc, z ≠ 0 →
        HasSum (fun m => ((n+1 : ℕ) : ℂ)*a (n+1) (m+1)*z^(m+1))
          ((Q (n+1)).eval (f z)⁻¹-z^(-((n+1 : ℕ) : ℤ))) := by
  obtain ⟨φ,hφ,hφ0⟩ := g2_phi_exists hf hf0
  have hdiag (k : ℕ) : φ k k = 1 := by
    rw [← hφ k k (1/2) (by norm_num) (by norm_num),
      g2_circle_coeff_pow hf hf0 k k (by norm_num : (0 : ℝ)<1/2) (by norm_num : (1/2 : ℝ)<1)]
    simp [iteratedDeriv_zero, dslope_same, hf1]
  refine ⟨faberPolynomial φ a, fun n => faberPolynomial_natDegree (by omega) (hdiag _), ?_⟩
  intro n z hz hz0
  have hfz : f z ≠ 0 := fun he => hz0 (hi hz (mem_ball_self one_pos) (by rw [he,hf0]))
  obtain ⟨hrow,hident⟩ := g2_faber_identity hf hf0 hexp hφ hφ0 hz hz0 hfz (show 1 ≤ n+1 by omega)
  have hshift : HasSum (fun m => a (m+1) (n+1)*z^(m+1))
      ((∑' p, a p (n+1)*z^p)-a 0 (n+1)) := by
    simpa only [Finset.sum_range_one, pow_zero, mul_one] using
      (hasSum_nat_add_iff' 1).mpr hrow.hasSum
  have hs : HasSum (fun m => ((n+1 : ℕ) : ℂ)*a (n+1) (m+1)*z^(m+1))
      (((n+1 : ℕ) : ℂ)*((∑' p, a p (n+1)*z^p)-a 0 (n+1))) := by
    apply (hshift.mul_left ((n+1 : ℕ) : ℂ)).congr_fun
    intro m
    rw [hsym (n+1) (m+1)]
    ring
  convert hs using 1
  rw [faberPolynomial_eval_inv, hident, zpow_neg, zpow_natCast]
  have hk : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  field_simp
  <;> ring

def faberFillAxes (C : ℕ → ℕ → ℂ) (d : ℕ → ℂ) (m n : ℕ) : ℂ :=
  (if m=0 ∨ n=0 then 0 else C (m-1) (n-1)) +
    (if n=0 then d m else 0) + (if m=0 then d n else 0)

theorem faberFillAxes_succ (C : ℕ → ℕ → ℂ) (d : ℕ → ℂ) (m n : ℕ) :
    faberFillAxes C d (m+1) (n+1) = C m n := by simp [faberFillAxes]

theorem faberFillAxes_symm {C : ℕ → ℕ → ℂ} (d : ℕ → ℂ)
    (hC : ∀ m n, C m n = C n m) (m n : ℕ) :
    faberFillAxes C d m n = faberFillAxes C d n m := by
  by_cases hm : m=0 <;> by_cases hn : n=0 <;> simp [faberFillAxes, hm, hn, hC]

theorem faber_axis_hasSum {d : ℕ → ℂ} {z w A : ℂ}
    (h : HasSum (fun n => d n*z^n) A) :
    HasSum (fun p : ℕ × ℕ => (if p.2=0 then d p.1 else 0)*z^p.1*w^p.2) A := by
  let j : ℕ → ℕ × ℕ := fun n => (n,0)
  have hj : Function.Injective j := fun m n he => congrArg Prod.fst he
  have hzero : ∀ p ∉ Set.range j, (if p.2=0 then d p.1 else 0)*z^p.1*w^p.2 = 0 := by
    rintro ⟨m,n⟩ hp
    have hn : n ≠ 0 := by
      intro hn
      exact hp ⟨m, by simp [j,hn]⟩
    simp [hn]
  apply (hj.hasSum_iff hzero).mp
  simpa [j, Function.comp_def] using h

theorem faberFillAxes_hasSum {C : ℕ → ℕ → ℂ} {d : ℕ → ℂ} {z w S A B : ℂ}
    (hC : HasSum (fun p : ℕ × ℕ => C p.1 p.2*z^(p.1+1)*w^(p.2+1)) S)
    (hA : HasSum (fun n => d n*z^n) A) (hB : HasSum (fun n => d n*w^n) B) :
    HasSum (fun p : ℕ × ℕ => faberFillAxes C d p.1 p.2*z^p.1*w^p.2) (S+A+B) := by
  let j : ℕ × ℕ → ℕ × ℕ := fun p => (p.1+1,p.2+1)
  have hj : Function.Injective j := by intro p q he; simpa [j,Prod.ext_iff] using he
  have hzero : ∀ p ∉ Set.range j,
      (if p.1=0 ∨ p.2=0 then 0 else C (p.1-1) (p.2-1))*z^p.1*w^p.2 = 0 := by
    rintro ⟨m,n⟩ hp
    cases m with
    | zero => simp
    | succ m =>
      cases n with
      | zero => simp
      | succ n => exact False.elim (hp ⟨(m,n),rfl⟩)
  have hmain : HasSum (fun p : ℕ × ℕ =>
      (if p.1=0 ∨ p.2=0 then 0 else C (p.1-1) (p.2-1))*z^p.1*w^p.2) S := by
    apply (hj.hasSum_iff hzero).mp
    simpa [j, Function.comp_def] using hC
  have hleft := faber_axis_hasSum (w := w) hA
  have hright : HasSum (fun p : ℕ × ℕ => (if p.1=0 then d p.2 else 0)*z^p.1*w^p.2) B := by
    apply ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr (faber_axis_hasSum (w := z) hB)).congr_fun
    intro p
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    by_cases hp : p.1=0 <;> simp [hp,mul_comm,mul_left_comm,mul_assoc]
  apply ((hmain.add hleft).add hright).congr_fun
  intro p
  dsimp [faberFillAxes]
  ring

/-- The actual exterior Grunsky series after inversion, with its two axis factors. -/
theorem faber_inverted_exterior_series {f g φ : ℂ → ℂ} {b : ℂ}
    (h : IsNormalizedDisjointPair f g) (hφd : DifferentiableOn ℂ φ unitDisc)
    (hφi : InjOn φ unitDisc) (hφ0 : φ 0 = 0) (hφ1 : deriv φ 0 = 1)
    (hb : b ≠ 0) (hbg : derivAtInfty g = b)
    (hg : ∀ s ∈ unitDisc, s ≠ 0 → g (1/s) = b/φ s)
    {s t : ℂ} (hs : s ∈ unitDisc) (ht : t ∈ unitDisc) (hst : s ≠ t) :
    ∃ S : ℂ, HasSum (fun p : ℕ × ℕ => grunsky f g (p.1+1) (p.2+1)*s^(p.1+1)*t^(p.2+1)) S ∧
      exp (-S)*dslope φ 0 s*dslope φ 0 t = dslope φ s t := by
  by_cases hs0 : s=0
  · subst s
    refine ⟨0, ?_, ?_⟩
    · simpa using (hasSum_zero : HasSum (fun _ : ℕ × ℕ => (0 : ℂ)) 0)
    · simp [dslope_same,hφ1]
  by_cases ht0 : t=0
  · subst t
    refine ⟨0, ?_, ?_⟩
    · simpa using (hasSum_zero : HasSum (fun _ : ℕ × ℕ => (0 : ℂ)) 0)
    · simp [dslope_same,hφ1,dslope_swap φ s 0]
  have hcoeff := (grunsky_spec h).1
  obtain ⟨S,hS,he⟩ := hcoeff.2.1 s⁻¹ (a21_inv_punctured ⟨hs,hs0⟩)
    t⁻¹ (a21_inv_punctured ⟨ht,ht0⟩) (inv_injective.ne hst)
  refine ⟨S, ?_, ?_⟩
  · simpa only [g1_zpow_neg_succ, inv_inv] using hS
  have hφs : φ s ≠ 0 := fun he => hs0 (hφi hs (mem_ball_self one_pos) (by rw [he,hφ0]))
  have hφt : φ t ≠ 0 := fun he => ht0 (hφi ht (mem_ball_self one_pos) (by rw [he,hφ0]))
  have hgs : g s⁻¹ = b/φ s := by simpa only [one_div] using hg s hs hs0
  have hgt : g t⁻¹ = b/φ t := by simpa only [one_div] using hg t ht ht0
  have hds : dslope φ 0 s = φ s/s := by rw [dslope_of_ne φ hs0,slope_def_field,hφ0,sub_zero,sub_zero]
  have hdt : dslope φ 0 t = φ t/t := by rw [dslope_of_ne φ ht0,slope_def_field,hφ0,sub_zero,sub_zero]
  have hdst : dslope φ s t = (φ t-φ s)/(t-s) := by rw [dslope_of_ne φ (Ne.symm hst),slope_def_field]
  rw [hgs,hgt,g1_alg_ext b (φ s) (φ t) s t hs0 ht0 hst hφs hφt,
    exp_sub,hcoeff.1,hbg] at he
  have he' : b*((dslope φ 0 s)⁻¹*(dslope φ 0 t)⁻¹*dslope φ s t) = b*exp (-S) := by
    simpa only [hds,hdt,hdst,exp_neg,div_eq_mul_inv] using he
  have hc := mul_left_cancel₀ hb he'
  have hds0 := univalent_dslope_ne_zero hφd hφi (mem_ball_self one_pos) hs
  have hdt0 := univalent_dslope_ne_zero hφd hφi (mem_ball_self one_pos) ht
  rw [← hc]
  field_simp

/-- Positive-branch Faber polynomials obtained by inversion and the disk construction. -/
theorem faber_positive_polynomials {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ P : ℕ → Polynomial ℂ, (∀ n, (P (n+1)).natDegree = n+1) ∧
      ∀ n, ∀ z ∈ unitDiscExterior,
        HasSum (fun m : ℕ => ((n+1 : ℕ) : ℂ)*grunsky f g (n+1) (m+1)*z^(-(m+1 : ℤ)))
          ((P (n+1)).eval (g z)-z^(n+1)) := by
  obtain ⟨φ,b,hφd,hφi,hφ0,hφ1,hb,hbg,hg⟩ := g1_inverted_exterior h
  obtain ⟨d,hd0,hd⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
  let C : ℕ → ℕ → ℂ := fun m n => grunsky f g (m+1) (n+1)
  let a := faberFillAxes C d
  have hsym : ∀ m n, a m n = a n m :=
    faberFillAxes_symm d (fun m n => ((grunsky_spec h).2 m n).1)
  have hexp : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, z ≠ w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧
        (φ z-φ w)/(z-w) = exp (0-S) := by
    intro z hz w hw hzw
    obtain ⟨S,hS,hE⟩ := faber_inverted_exterior_series h hφd hφi hφ0 hφ1 hb hbg hg hz hw hzw
    obtain ⟨A,hA,hEA⟩ := hd z hz
    obtain ⟨B,hB,hEB⟩ := hd w hw
    refine ⟨S+A+B, faberFillAxes_hasSum hS hA hB, ?_⟩
    have he : (φ z-φ w)/(z-w) = dslope φ z w := by
      rw [dslope_swap,dslope_of_ne φ hzw,slope_def_field]
    rw [he, ← hE, ← hEA, ← hEB]
    simp only [zero_sub, ← exp_add]
    congr 1
    ring
  obtain ⟨R,hRdeg,hR⟩ := faber_negative_polynomials hφd hφi hφ0 hφ1 hsym hexp
  let P : ℕ → Polynomial ℂ := fun n => (R n).comp (Polynomial.C b⁻¹*Polynomial.X)
  refine ⟨P, ?_, ?_⟩
  · intro n
    simp only [P,Polynomial.natDegree_comp,Polynomial.natDegree_C_mul_X b⁻¹ (inv_ne_zero hb),hRdeg,mul_one]
  · intro n z hz
    have hs := a21_inv_exterior hz
    have hrel := hR n z⁻¹ hs.1 hs.2
    have hgz : g z = b/φ z⁻¹ := by simpa only [one_div,inv_inv] using hg z⁻¹ hs.1 hs.2
    have harg : b⁻¹*g z = (φ z⁻¹)⁻¹ := by rw [hgz]; field_simp
    simp_rw [g1_zpow_neg_succ]
    simpa only [P,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      harg,a,faberFillAxes_succ,C,g1_zpow_neg_succ,zpow_neg,zpow_natCast,inv_pow,inv_inv] using hrel

/-- (G0) Generalized Faber polynomials of a normalized disjoint pair exist (TT:4506–4524). -/
theorem faber_exists {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) :
    ∃ P Q : ℕ → Polynomial ℂ, IsFaber f g P Q := by
  have hspec := grunsky_spec h
  obtain ⟨P,hPd,hP⟩ := faber_positive_polynomials h
  obtain ⟨Q,hQd,hQ⟩ := faber_negative_polynomials h.1 h.2.1 h.2.2.1 h.2.2.2.1
    (a := fun m n => grunsky f g (-(m : ℤ)) (-(n : ℤ)))
    (fun m n => (hspec.2 m n).2) hspec.1.2.2.2.1
  refine ⟨P,Q,fun n => ⟨hPd n,hQd n⟩,hP,?_⟩
  intro n z hz hz0
  simpa only [Nat.cast_add,Nat.cast_one] using hQ n z hz hz0

theorem polynomial_eq_of_injOn_eval {U : Set ℂ} {F : ℂ → ℂ}
    (hU : U.Infinite) (hF : InjOn F U) {p q : Polynomial ℂ}
    (he : ∀ z ∈ U, p.eval (F z) = q.eval (F z)) : p=q := by
  apply p.eq_of_infinite_eval_eq q
  apply (hU.image hF).mono
  rintro _ ⟨z,hz,rfl⟩
  exact he z hz

/-- The defining Grunsky expansions uniquely determine every positive-degree
Faber polynomial. Index zero remains unconstrained by `IsFaber`. -/
theorem IsFaber.unique_pos {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q P' Q' : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (hPQ' : IsFaber f g P' Q') :
    ∀ n, P (n+1)=P' (n+1) ∧ Q (n+1)=Q' (n+1) := by
  have hD : unitDisc.Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds _ one_pos)
  have hE : unitDiscExterior.Infinite := by
    apply infinite_of_mem_nhds (2 : ℂ)
    apply (isOpen_lt continuous_const continuous_norm).mem_nhds
    norm_num
  intro n
  constructor
  · apply polynomial_eq_of_injOn_eval hE h.2.2.2.2.1.2.1
    intro z hz
    exact sub_left_injective ((hPQ.2.1 n z hz).unique (hPQ'.2.1 n z hz))
  · apply polynomial_eq_of_injOn_eval (hD.sdiff (finite_singleton 0))
      (F := fun z => (f z)⁻¹)
    · intro z hz w hw he
      exact h.2.1 hz.1 hw.1 (inv_injective he)
    · intro z hz
      exact sub_left_injective ((hPQ.2.2 n z hz.1 hz.2).unique (hPQ'.2.2 n z hz.1 hz.2))

/-- Extract a nonconstant coefficient from an actual logarithmic generating
series. The logarithm/geometric-series interchange uses a uniform geometric
majorant on a sufficiently small Cauchy circle. -/
theorem faber_log_coefficient {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hf0 : f 0 = 0) {c : ℕ → ℂ} {W : ℂ}
    (hc : ∀ z ∈ unitDisc, Summable (fun n => c n*z^n))
    (he : ∀ z ∈ unitDisc, exp (c 0-∑' n, c n*z^n) = 1-W*f z)
    {φ : ℕ → ℕ → ℂ}
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 →
      Real.circleAverage (fun z => f z^l/z^k) 0 r = φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) {k : ℕ} (hk : 1≤k) :
    c k = ∑ l ∈ Finset.Icc 1 k, W^l/(l : ℂ)*φ l k := by
  have hcont : ContinuousAt (fun z => W*f z) 0 :=
    ((hf.differentiableAt (ball_mem_nhds _ one_pos)).continuousAt).const_mul W
  obtain ⟨δ0,hδ0,hsmall⟩ := Metric.continuousAt_iff.mp hcont (1/2) (by norm_num)
  let δ : ℝ := min (δ0/2) (1/2)
  have hδ : 0<δ := lt_min (half_pos hδ0) (by norm_num)
  have hδ1 : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδsmall : ∀ z : ℂ, ‖z‖≤δ → ‖W*f z‖≤1/2 := by
    intro z hz
    have hzδ : dist z 0<δ0 := by
      rw [dist_zero_right]
      have := hz.trans (min_le_left (δ0/2) (1/2))
      linarith
    simpa only [hf0,mul_zero,dist_zero_right] using (hsmall hzδ).le
  have hball : ∀ z : ℂ, ‖z‖≤δ → z∈unitDisc := fun z hz => mem_ball_zero_iff.mpr (hz.trans_lt hδ1)
  let S : ℂ → ℂ := fun z => ∑' n, c n*z^n
  have hSd : DifferentiableOn ℂ S unitDisc :=
    differentiableOn_of_powerSeries (fun z hz => (hc z hz).hasSum)
  have hS0 : S 0=c 0 := by simp [S,zero_pow_eq]
  let K : ℂ → ℂ := fun z => S z-c 0
  let E : ℂ → ℂ := fun z => -log (1-W*f z)
  have hslit : ∀ z : ℂ, ‖z‖≤δ → 1-W*f z∈Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    left
    have ht := (le_abs_self (W*f z).re).trans (Complex.abs_re_le_norm (W*f z))
    simp only [Complex.sub_re,Complex.one_re]
    linarith [hδsmall z hz]
  have hKc : ContinuousOn K (closedBall (0 : ℂ) δ) :=
    (hSd.continuousOn.sub continuousOn_const).mono (fun z hz => hball z (mem_closedBall_zero_iff.mp hz))
  have hEc : ContinuousOn E (closedBall (0 : ℂ) δ) := by
    intro z hz
    have hfc := (hf.continuousOn.mono (fun z hz => hball z (mem_closedBall_zero_iff.mp hz))) z hz
    exact (ContinuousAt.comp_continuousWithinAt (f := fun z => 1-W*f z)
      (continuousAt_clog (hslit z (mem_closedBall_zero_iff.mp hz)))
      (continuousWithinAt_const.sub (hfc.const_mul W))).neg
  have hKE : ∀ z : ℂ, ‖z‖<δ → K z=E z := by
    haveI : PreconnectedSpace (ball (0 : ℂ) δ) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : ℂ) δ).isPreconnected
    have h1 : Continuous (fun z : ball (0 : ℂ) δ => K z) :=
      hKc.comp_continuous continuous_subtype_val (fun z => ball_subset_closedBall z.2)
    have h2 : Continuous (fun z : ball (0 : ℂ) δ => E z) :=
      hEc.comp_continuous continuous_subtype_val (fun z => ball_subset_closedBall z.2)
    have huniq := continuous_exp_lift_unique h1 h2 (by
      intro z
      have hz : ‖(z : ℂ)‖≤δ := (mem_ball_zero_iff.mp z.2).le
      rw [← inv_inj, ← exp_neg, ← exp_neg]
      have hleft : exp (-K z)=1-W*f z := by simpa only [K,S,neg_sub] using he z (hball z hz)
      rw [hleft]
      simp only [E,neg_neg]
      exact (exp_log (Complex.slitPlane_ne_zero (hslit z hz))).symm)
      (x₀ := ⟨0,mem_ball_self hδ⟩) (by simp [K,E,hS0,hf0])
    intro z hz
    exact congrFun huniq ⟨z,mem_ball_zero_iff.mpr hz⟩
  let r : ℝ := δ/2
  have hr : 0<r := half_pos hδ
  have hrδ : r<δ := by dsimp [r]; linarith
  have hr1 : r<1 := hrδ.trans hδ1
  have hsph : ∀ z∈sphere (0 : ℂ) |r|, ‖z‖=r := fun z hz => by simpa [abs_of_pos hr] using hz
  have hne : ∀ z∈sphere (0 : ℂ) |r|, z≠0 := by
    intro z hz hez
    have := hsph z hz
    rw [hez,norm_zero] at this
    linarith
  have hδD : (δ : ℂ)∈unitDisc := by simpa [unitDisc,abs_of_pos hδ] using hδ1
  have hbound : Summable (fun n => ‖c n‖*δ^n) := by
    simpa [norm_mul,norm_pow,abs_of_pos hδ] using (hc (δ : ℂ) hδD).norm
  let c' : ℕ → ℂ := fun n => if n=0 then 0 else c n
  have hKsum (z : ℂ) (hz : z∈unitDisc) : HasSum (fun n => c' n*z^n) (K z) := by
    apply ((hc z hz).hasSum.sub (hasSum_ite_eq 0 (c 0))).congr_fun
    intro n
    by_cases hn : n=0 <;> simp [c',hn]
  have hKavg : Real.circleAverage (fun z => K z/z^k) 0 r = c k := by
    have hh : Real.circleAverage (fun z => K z/z^k) 0 r = c' k := by
      apply g2_circle_coeff hr k (B := fun n => ‖c n‖*δ^n) hbound
      · intro n z hz
        by_cases hn : n=0
        · simp [c',hn]
        · simp only [c',hn,if_false,norm_mul,norm_pow,hsph z hz]
          gcongr
      · intro z hz
        exact hKsum z (hball z (by rw [hsph z hz]; exact hrδ.le))
    simpa [c',show k≠0 by omega] using hh
  have hfc : ContinuousOn f (sphere (0 : ℂ) |r|) :=
    hf.continuousOn.mono (fun z hz => hball z (by rw [hsph z hz]; exact hrδ.le))
  have hT (n : ℕ) : CircleIntegrable (fun z => ((W*f z)^n/(n : ℂ))/z^k) 0 r := by
    have hcT : ContinuousOn (fun z => ((W*f z)^n/(n : ℂ))/z^k) (sphere (0 : ℂ) |r|) :=
      (((hfc.const_mul W).pow n).div_const _).div (by fun_prop) (fun z hz => pow_ne_zero _ (hne z hz))
    exact (hcT.comp (continuous_circleMap 0 r).continuousOn
      (fun θ _ => circleMap_mem_sphere' 0 r θ)).intervalIntegrable
  have hEa := circleAverage_hasSum_of_bound (ι := ℕ) (T := fun (n : ℕ) z => ((W*f z)^n/(n : ℂ))/z^k)
    (K := fun z => E z/z^k) (B := fun n => (1/2 : ℝ)^n/r^k) hT
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const _) (by
      intro n z hz
      rw [norm_div,norm_div,norm_pow,norm_pow,hsph z hz,Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst n; simp
      · calc
          ‖W*f z‖^n/(n : ℝ) ≤ ‖W*f z‖^n := div_le_self (by positivity) (by exact_mod_cast hn)
          _ ≤ (1/2 : ℝ)^n := pow_le_pow_left₀ (norm_nonneg _) (hδsmall z (by rw [hsph z hz]; exact hrδ.le)) n)
    (by
      intro z hz
      have hn : ‖W*f z‖<1 := lt_of_le_of_lt (hδsmall z (by rw [hsph z hz]; exact hrδ.le)) (by norm_num)
      exact (Complex.hasSum_taylorSeries_neg_log hn).div_const (z^k))
  have hTavg (n : ℕ) : Real.circleAverage (fun z => ((W*f z)^n/(n : ℂ))/z^k) 0 r =
      W^n/(n : ℂ)*φ n k := by
    have heq : (fun z => ((W*f z)^n/(n : ℂ))/z^k) = fun z => (W^n/(n : ℂ))*(f z^n/z^k) := by
      funext z
      rw [mul_pow]
      ring
    rw [heq]
    have hh := Real.circleAverage_fun_smul (a := W^n/(n : ℂ)) (f := fun z => f z^n/z^k) (c := 0) (R := r)
    simp only [smul_eq_mul] at hh
    rw [hh,hφ n k r hr hr1]
  simp_rw [hTavg] at hEa
  have hfin : HasSum (fun n : ℕ => W^n/(n : ℂ)*φ n k)
      (∑ n ∈ Finset.Icc 1 k, W^n/(n : ℂ)*φ n k) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      by_cases hn0 : n=0
      · simp [hn0]
      · have hkn : k<n := by simp only [Finset.mem_Icc,not_and_or,not_le] at hn; omega
        simp [hφ0 n k hkn])
  have heq : Real.circleAverage (fun z => K z/z^k) 0 r = Real.circleAverage (fun z => E z/z^k) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    change K z/z^k=E z/z^k
    rw [hKE z (by rw [hsph z hz]; exact hrδ)]
  rw [hKavg, hEa.unique hfin] at heq
  exact heq

theorem faberPolynomial_disk_series {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hi : InjOn f unitDisc) (hf0 : f 0=0)
    {a φ : ℕ → ℕ → ℂ} {b00 : ℂ} (hsym : ∀ m n, a m n=a n m)
    (hexp : ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (f z-f w)/(z-w)=exp (b00-S))
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) {k : ℕ} (hk : 1≤k)
    {z : ℂ} (hz : z∈unitDisc) (hz0 : z≠0) :
    HasSum (fun m : ℕ => (k : ℂ)*a k (m+1)*z^(m+1))
      ((faberPolynomial φ a k).eval (f z)⁻¹-z^(-(k : ℤ))) := by
  have hfz : f z≠0 := fun he => hz0 (hi hz (mem_ball_self one_pos) (by rw [he,hf0]))
  obtain ⟨hrow,hident⟩ := g2_faber_identity hf hf0 hexp hφ hφ0 hz hz0 hfz hk
  have hshift : HasSum (fun m => a (m+1) k*z^(m+1)) ((∑' p, a p k*z^p)-a 0 k) := by
    simpa only [Finset.sum_range_one,pow_zero,mul_one] using (hasSum_nat_add_iff' 1).mpr hrow.hasSum
  have hs : HasSum (fun m : ℕ => (k : ℂ)*a k (m+1)*z^(m+1))
      ((k : ℂ)*((∑' p, a p k*z^p)-a 0 k)) := by
    apply (hshift.mul_left (k : ℂ)).congr_fun
    intro m
    rw [hsym k (m+1)]
    ring
  convert hs using 1
  rw [faberPolynomial_eval_inv,hident,zpow_neg,zpow_natCast]
  have hk0 : (k : ℂ)≠0 := by exact_mod_cast (show k≠0 by omega)
  field_simp
  <;> ring

theorem IsFaber.negative_polynomial_eq {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) {φ : ℕ → ℕ → ℂ}
    (hφ : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => f z^l/z^k) 0 r=φ l k)
    (hφ0 : ∀ l k : ℕ, k<l → φ l k=0) (n : ℕ) :
    Q (n+1) = faberPolynomial φ (fun m k => grunsky f g (-(m : ℤ)) (-(k : ℤ))) (n+1) := by
  have hD : unitDisc.Infinite := infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds _ one_pos)
  apply polynomial_eq_of_injOn_eval (hD.sdiff (finite_singleton 0)) (F := fun z => (f z)⁻¹)
  · intro z hz w hw he
    exact h.2.1 hz.1 hw.1 (inv_injective he)
  · intro z hz
    have hspec := grunsky_spec h
    have hS := faberPolynomial_disk_series h.1 h.2.1 h.2.2.1
      (a := fun m k => grunsky f g (-(m : ℤ)) (-(k : ℤ)))
      (fun m k => (hspec.2 m k).2) hspec.1.2.2.2.1 hφ hφ0 (show 1≤n+1 by omega) hz.1 hz.2
    have hQ := hPQ.2.2 n z hz.1 hz.2
    simp only [Nat.cast_add,Nat.cast_one] at hS hQ
    exact sub_left_injective (hQ.unique hS)

/-- Regroup the actual mixed block into scalar power series in the disk variable. -/
theorem faber_mixed_interior_rows {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {z : ℂ} (hz : z∈unitDiscExterior) :
    let c : ℕ → ℂ := fun m => ∑' n : ℕ, grunsky f g (n+1) (-(m : ℤ))*z^(-(n+1 : ℤ))
    (∀ m : ℕ, Summable (fun n : ℕ => grunsky f g (n+1) (-(m : ℤ))*z^(-(n+1 : ℤ)))) ∧
      ∀ w∈unitDisc, ∃ S : ℂ, HasSum (fun m : ℕ => c m*w^m) S ∧
        (g z-f w)/(derivAtInfty g*z)=exp (-S) := by
  have hb := (grunsky_spec h).1.2.2.1
  obtain ⟨S0,hS0,_⟩ := hb z hz (1/2) (by norm_num [unitDisc,Complex.norm_div])
  have hrows (m : ℕ) : Summable (fun n : ℕ => grunsky f g (n+1) (-(m : ℤ))*z^(-(n+1 : ℤ))) := by
    exact (summable_mul_right_iff (pow_ne_zero m (by norm_num : (1/2 : ℂ)≠0))).mp
      (hS0.summable.prod_symm.prod_factor m)
  refine ⟨hrows,?_⟩
  intro w hw
  obtain ⟨S,hS,hE⟩ := hb z hz w hw
  refine ⟨S,?_,hE⟩
  apply ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS).prod_fiberwise
  intro m
  exact (hrows m).hasSum.mul_right (w^m)

theorem faber_grunsky_negative {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDiscExterior) :
    HasSum (fun m : ℕ => ((n+1 : ℕ) : ℂ)*grunsky f g (m+1) (-(n+1 : ℤ))*z^(-(m+1 : ℤ)))
      ((Q (n+1)).eval (g z)⁻¹+((n+1 : ℕ) : ℂ)*grunsky f g (-(n+1 : ℤ)) 0) := by
  let c : ℕ → ℂ := fun m => ∑' j : ℕ, grunsky f g (j+1) (-(m : ℤ))*z^(-(j+1 : ℤ))
  obtain ⟨hrows,hseries⟩ := faber_mixed_interior_rows h hz
  have hc : ∀ w∈unitDisc, Summable (fun m => c m*w^m) := by
    intro w hw
    obtain ⟨S,hS,_⟩ := hseries w hw
    exact hS.summable
  have hE : ∀ w∈unitDisc, (g z-f w)/(derivAtInfty g*z)=exp (-∑' m, c m*w^m) := by
    intro w hw
    obtain ⟨S,hS,he⟩ := hseries w hw
    rwa [hS.tsum_eq]
  have hE0 : g z/(derivAtInfty g*z)=exp (-c 0) := by
    simpa only [h.2.2.1,sub_zero,zero_pow_eq,mul_ite,mul_one,mul_zero,tsum_ite_eq] using
      hE 0 (mem_ball_self one_pos)
  have hgz : g z≠0 := by
    intro he
    exact Set.disjoint_left.mp h.2.2.2.2.2 ⟨0,mem_ball_self one_pos,h.2.2.1⟩ ⟨z,hz,he⟩
  have hb : derivAtInfty g≠0 := by rw [← (grunsky_spec h).1.1]; exact exp_ne_zero _
  have hz0 : z≠0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  have hexp : ∀ w∈unitDisc, exp (c 0-∑' m, c m*w^m)=1-(g z)⁻¹*f w := by
    intro w hw
    rw [show c 0-(∑' m, c m*w^m) = (-(∑' m, c m*w^m))-(-c 0) by ring,
      exp_sub,← hE w hw,← hE0]
    field_simp
  obtain ⟨φ,hφ,hφ0⟩ := g2_phi_exists h.1 h.2.2.1
  have hcoef := faber_log_coefficient h.1 h.2.2.1 hc hexp hφ hφ0 (show 1≤n+1 by omega)
  have hfinite : (∑ l∈Finset.Icc 1 (n+1), φ l (n+1)/((l : ℂ)*g z^l))=c (n+1) := by
    rw [hcoef]
    apply Finset.sum_congr rfl
    intro l _
    simp only [inv_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  have hval : (Q (n+1)).eval (g z)⁻¹+((n+1 : ℕ) : ℂ)*grunsky f g (-(n+1 : ℤ)) 0 =
      ((n+1 : ℕ) : ℂ)*c (n+1) := by
    rw [hPQ.negative_polynomial_eq h hφ hφ0 n,faberPolynomial_eval_inv,hfinite]
    have haxis := ((grunsky_spec h).2 0 (n+1)).2
    simp only [Nat.cast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at haxis ⊢
    rw [haxis]
    ring
  rw [hval]
  have hs := (hrows (n+1)).hasSum.mul_left ((n+1 : ℕ) : ℂ)
  simpa only [c,Nat.cast_add,Nat.cast_one,mul_assoc] using hs

theorem faber_inverted_full_series {f g φ : ℂ → ℂ} {b : ℂ} {d : ℕ → ℂ}
    (h : IsNormalizedDisjointPair f g) (hφd : DifferentiableOn ℂ φ unitDisc)
    (hφi : InjOn φ unitDisc) (hφ0 : φ 0=0) (hφ1 : deriv φ 0=1)
    (hb : b≠0) (hbg : derivAtInfty g=b) (hg : ∀ s∈unitDisc, s≠0 → g (1/s)=b/φ s)
    (hd : ∀ s∈unitDisc, ∃ S : ℂ, HasSum (fun n => d n*s^n) S ∧ exp (-S)=dslope φ 0 s) :
    let a := faberFillAxes (fun m n => grunsky f g (m+1) (n+1)) d
    ∀ z∈unitDisc, ∀ w∈unitDisc, z≠w → ∃ S : ℂ,
      HasSum (fun p : ℕ × ℕ => a p.1 p.2*z^p.1*w^p.2) S ∧ (φ z-φ w)/(z-w)=exp (0-S) := by
  intro a z hz w hw hzw
  obtain ⟨S,hS,hE⟩ := faber_inverted_exterior_series h hφd hφi hφ0 hφ1 hb hbg hg hz hw hzw
  obtain ⟨A,hA,hEA⟩ := hd z hz
  obtain ⟨B,hB,hEB⟩ := hd w hw
  refine ⟨S+A+B,faberFillAxes_hasSum hS hA hB,?_⟩
  have he : (φ z-φ w)/(z-w)=dslope φ z w := by rw [dslope_swap,dslope_of_ne φ hzw,slope_def_field]
  rw [he,← hE,← hEA,← hEB]
  simp only [zero_sub,← exp_add]
  congr 1
  ring

theorem IsFaber.positive_polynomial_eq {f g φ : ℂ → ℂ} {b : ℂ} {d : ℕ → ℂ}
    (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q)
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφi : InjOn φ unitDisc) (hφ0 : φ 0=0) (hφ1 : deriv φ 0=1)
    (hb : b≠0) (hbg : derivAtInfty g=b) (hg : ∀ s∈unitDisc, s≠0 → g (1/s)=b/φ s)
    (hd : ∀ s∈unitDisc, ∃ S : ℂ, HasSum (fun n => d n*s^n) S ∧ exp (-S)=dslope φ 0 s)
    {η : ℕ → ℕ → ℂ}
    (hη : ∀ l k : ℕ, ∀ r : ℝ, 0<r → r<1 → Real.circleAverage (fun z => φ z^l/z^k) 0 r=η l k)
    (hη0 : ∀ l k : ℕ, k<l → η l k=0) (n : ℕ) :
    P (n+1) = (faberPolynomial η (faberFillAxes (fun m k => grunsky f g (m+1) (k+1)) d) (n+1)).comp
      (Polynomial.C b⁻¹*Polynomial.X) := by
  let a := faberFillAxes (fun m k => grunsky f g (m+1) (k+1)) d
  have hsym : ∀ m k, a m k=a k m := faberFillAxes_symm d (fun m k => ((grunsky_spec h).2 m k).1)
  have hexp := faber_inverted_full_series h hφd hφi hφ0 hφ1 hb hbg hg hd
  have hE : unitDiscExterior.Infinite := by
    apply infinite_of_mem_nhds (2 : ℂ)
    apply (isOpen_lt continuous_const continuous_norm).mem_nhds
    norm_num
  apply polynomial_eq_of_injOn_eval hE h.2.2.2.2.1.2.1
  intro z hz
  have hs := a21_inv_exterior hz
  have hS := faberPolynomial_disk_series hφd hφi hφ0 hsym hexp hη hη0
    (show 1≤n+1 by omega) hs.1 hs.2
  have hgz : g z=b/φ z⁻¹ := by simpa only [one_div,inv_inv] using hg z⁻¹ hs.1 hs.2
  have harg : b⁻¹*g z=(φ z⁻¹)⁻¹ := by rw [hgz]; field_simp
  have hS' : HasSum (fun m : ℕ => ((n+1 : ℕ) : ℂ)*grunsky f g (n+1) (m+1)*z^(-(m+1 : ℤ)))
      (((faberPolynomial η a (n+1)).comp (Polynomial.C b⁻¹*Polynomial.X)).eval (g z)-z^(n+1)) := by
    simp_rw [g1_zpow_neg_succ]
    simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      harg,a,faberFillAxes_succ,zpow_neg,zpow_natCast,inv_pow,inv_inv] using hS
  exact sub_left_injective ((hPQ.2.1 n z hz).unique hS')

/-- Regroup the mixed block in its exterior variable while retaining absolute summability. -/
theorem faber_mixed_exterior_rows {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {w : ℂ} (hw : w∈unitDisc) :
    let r : ℕ → ℂ := fun n => ∑' m : ℕ, grunsky f g (n+1) (-(m : ℤ))*w^m
    (∀ n : ℕ, Summable (fun m : ℕ => grunsky f g (n+1) (-(m : ℤ))*w^m)) ∧
      ∀ z∈unitDiscExterior, ∃ S : ℂ, HasSum (fun n : ℕ => r n*z^(-(n+1 : ℤ))) S ∧
        (g z-f w)/(derivAtInfty g*z)=exp (-S) := by
  have hb := (grunsky_spec h).1.2.2.1
  obtain ⟨S0,hS0,_⟩ := hb 2 (by norm_num [unitDiscExterior]) w hw
  have hrows (n : ℕ) : Summable (fun m : ℕ => grunsky f g (n+1) (-(m : ℤ))*w^m) := by
    have hh : Summable (fun m : ℕ => (2 : ℂ)^(-(n+1 : ℤ))*(grunsky f g (n+1) (-(m : ℤ))*w^m)) :=
      (hS0.summable.prod_factor n).congr (fun m => by ring)
    exact (summable_mul_left_iff (zpow_ne_zero _ (by norm_num : (2 : ℂ)≠0))).mp hh
  refine ⟨hrows,?_⟩
  intro z hz
  obtain ⟨S,hS,hE⟩ := hb z hz w hw
  refine ⟨S,?_,hE⟩
  apply hS.prod_fiberwise
  intro n
  apply ((hrows n).hasSum.mul_right (z^(-(n+1 : ℤ)))).congr_fun
  intro m
  ring

theorem faber_positive_scalar_series {f g φ : ℂ → ℂ} {b : ℂ}
    (h : IsNormalizedDisjointPair f g) (hφi : InjOn φ unitDisc) (hφ0 : φ 0=0) (hφ1 : deriv φ 0=1)
    (hb : b≠0) (hbg : derivAtInfty g=b) (hg : ∀ s∈unitDisc, s≠0 → g (1/s)=b/φ s)
    {w : ℂ} (hw : w∈unitDisc) :
    let r : ℕ → ℂ := fun n => ∑' m : ℕ, grunsky f g (n+1) (-(m : ℤ))*w^m
    let c : ℕ → ℂ := fun m => if m=0 then 0 else r (m-1)
    ∀ s∈unitDisc, ∃ S : ℂ, HasSum (fun m => c m*s^m) S ∧
      exp (-S)=(dslope φ 0 s)⁻¹*(1-(f w/b)*φ s) := by
  intro r c s hs
  by_cases hs0 : s=0
  · subst s
    refine ⟨0,?_,?_⟩
    · apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0).congr_fun
      intro m
      by_cases hm : m=0 <;> simp [c,hm]
    · simp [dslope_same,hφ1,hφ0]
  obtain ⟨_,hseries⟩ := faber_mixed_exterior_rows h hw
  obtain ⟨S,hS,hE⟩ := hseries s⁻¹ (a21_inv_punctured ⟨hs,hs0⟩)
  have hshift : HasSum (fun m : ℕ => c (m+1)*s^(m+1)) S := by
    simpa only [c,Nat.add_sub_cancel,show ∀ m : ℕ, ¬m+1=0 by omega,if_false,
      g1_zpow_neg_succ,inv_inv] using hS
  have hfull : HasSum (fun m => c m*s^m) S := by
    simpa [c] using (hasSum_nat_add_iff (f := fun m => c m*s^m) 1).mp hshift
  refine ⟨S,hfull,?_⟩
  have hφs : φ s≠0 := fun he => hs0 (hφi hs (mem_ball_self one_pos) (by rw [he,hφ0]))
  have hgs : g s⁻¹=b/φ s := by simpa only [one_div] using hg s hs hs0
  have hds : dslope φ 0 s=φ s/s := by rw [dslope_of_ne φ hs0,slope_def_field,hφ0,sub_zero,sub_zero]
  rw [hbg,hgs,g1_alg_mix b (φ s) (f w) s hb hs0 hφs] at hE
  rw [← hE,hds]
  ring

theorem faber_grunsky_positive {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g)
    {P Q : ℕ → Polynomial ℂ} (hPQ : IsFaber f g P Q) (n : ℕ)
    {z : ℂ} (hz : z∈unitDisc) :
    HasSum (fun m : ℕ => ((n+1 : ℕ) : ℂ)*grunsky f g (n+1) (-(m+1 : ℤ))*z^(m+1))
      ((P (n+1)).eval (f z)-((n+1 : ℕ) : ℂ)*grunsky f g (n+1) 0) := by
  obtain ⟨φ,b,hφd,hφi,hφ0,hφ1,hb,hbg,hg⟩ := g1_inverted_exterior h
  obtain ⟨d,hd0,hd'⟩ := disk_axis_coefficients_exist hφd hφi hφ1 0
  have hd : ∀ s∈unitDisc, ∃ S : ℂ, HasSum (fun m => d m*s^m) S ∧ exp (-S)=dslope φ 0 s := by
    intro s hs
    simpa only [zero_sub] using hd' s hs
  obtain ⟨η,hη,hη0⟩ := g2_phi_exists hφd hφ0
  let r : ℕ → ℂ := fun j => ∑' m : ℕ, grunsky f g (j+1) (-(m : ℤ))*z^m
  let c : ℕ → ℂ := fun m => if m=0 then 0 else r (m-1)
  have hcS := faber_positive_scalar_series h hφi hφ0 hφ1 hb hbg hg hz
  have hc : ∀ s∈unitDisc, Summable (fun m => c m*s^m) := by
    intro s hs
    obtain ⟨S,hS,_⟩ := hcS s hs
    exact hS.summable
  have hdc : ∀ s∈unitDisc, Summable (fun m => d m*s^m) := by
    intro s hs
    obtain ⟨S,hS,_⟩ := hd s hs
    exact hS.summable
  have hec : ∀ s∈unitDisc, exp (-∑' m, c m*s^m)=(dslope φ 0 s)⁻¹*(1-(f z/b)*φ s) := by
    intro s hs
    obtain ⟨S,hS,hE⟩ := hcS s hs
    rwa [hS.tsum_eq]
  have hed : ∀ s∈unitDisc, exp (-∑' m, d m*s^m)=dslope φ 0 s := by
    intro s hs
    obtain ⟨S,hS,hE⟩ := hd s hs
    rwa [hS.tsum_eq]
  let e : ℕ → ℂ := fun m => c m+d m
  have hecS : ∀ s∈unitDisc, Summable (fun m => e m*s^m) := by
    intro s hs
    simpa only [e,add_mul] using (hc s hs).add (hdc s hs)
  have he : ∀ s∈unitDisc, exp (e 0-∑' m, e m*s^m)=1-(f z/b)*φ s := by
    intro s hs
    have he0 : e 0=0 := by simp [e,c,hd0]
    have hsum : (∑' m, e m*s^m)=(∑' m, c m*s^m)+(∑' m, d m*s^m) := by
      simp only [e,add_mul]
      exact (hc s hs).tsum_add (hdc s hs)
    rw [he0,zero_sub,hsum,neg_add,exp_add,hec s hs,hed s hs]
    have hds := univalent_dslope_ne_zero hφd hφi (mem_ball_self one_pos) hs
    field_simp
  have hcoef := faber_log_coefficient hφd hφ0 hecS he hη hη0 (show 1≤n+1 by omega)
  have hval : (P (n+1)).eval (f z)=((n+1 : ℕ) : ℂ)*r n := by
    rw [hPQ.positive_polynomial_eq h hφd hφi hφ0 hφ1 hb hbg hg hd hη hη0 n,
      Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    have heval : (faberPolynomial η (faberFillAxes (fun m k => grunsky f g (m+1) (k+1)) d) (n+1)).eval
        (b⁻¹*f z) = ((n+1 : ℕ) : ℂ)*(∑ l∈Finset.Icc 1 (n+1), (f z/b)^l/(l : ℂ)*η l (n+1)) -
          ((n+1 : ℕ) : ℂ)*d (n+1) := by
      simp only [faberPolynomial,Polynomial.eval_sub,Polynomial.eval_finsetSum,
        Polynomial.eval_monomial,Polynomial.eval_C]
      rw [show faberFillAxes (fun m k => grunsky f g (m+1) (k+1)) d 0 (n+1)=d (n+1) by simp [faberFillAxes]]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      simp only [div_eq_mul_inv,mul_comm b⁻¹]
      ring
    rw [heval,← hcoef]
    simp [e,c,mul_add]
  obtain ⟨hrows,_⟩ := faber_mixed_exterior_rows h hz
  have hshift : HasSum (fun m : ℕ => grunsky f g (n+1) (-((m+1 : ℕ) : ℤ))*z^(m+1))
      (r n-grunsky f g (n+1) 0) := by
    simpa only [Finset.sum_range_one,Nat.cast_zero,neg_zero,pow_zero,mul_one] using
      (hasSum_nat_add_iff' 1).mpr (hrows n).hasSum
  rw [hval]
  simpa only [Nat.cast_add,Nat.cast_one,mul_sub,mul_assoc] using hshift.mul_left ((n+1 : ℕ) : ℂ)

/-- (TT:4535) The remaining Faber–Grunsky relations:
- `P_n(f(z)) = n b_{n,0} + n Σ_{m ≥ 1} b_{n,-m} z^m` on `𝔻`;
- `Q_n(g(z)) = -n b_{-n,0} + n Σ_{m ≥ 1} b_{m,-n} z^{-m}` on `𝔻*`. -/
theorem faber_grunsky {f g : ℂ → ℂ} (h : IsNormalizedDisjointPair f g) {P Q : ℕ → Polynomial ℂ}
    (hPQ : IsFaber f g P Q) (n : ℕ) :
    (∀ z ∈ unitDisc, HasSum (fun m : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) (-(m + 1 : ℤ)) * z ^ (m + 1))
        ((P (n + 1)).eval (f z) - ((n + 1 : ℕ) : ℂ) * grunsky f g (n + 1) 0)) ∧
      ∀ z ∈ unitDiscExterior, HasSum (fun m : ℕ => ((n + 1 : ℕ) : ℂ) * grunsky f g (m + 1) (-(n + 1 : ℤ)) * z ^ (-(m + 1 : ℤ)))
        ((Q (n + 1)).eval (g z)⁻¹ + ((n + 1 : ℕ) : ℂ) * grunsky f g (-(n + 1 : ℤ)) 0) := by
  exact ⟨fun _ hz => faber_grunsky_positive h hPQ n hz,
    fun _ hz => faber_grunsky_negative h hPQ n hz⟩

end Ch2

end TakhtajanTeo
