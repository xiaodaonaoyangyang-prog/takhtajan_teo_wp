import TakhtajanTeo.Ch1.WPChangeOfVariables
import TakhtajanTeo.Ch1.GroupChainCompleted
import TakhtajanTeo.Appendix.AppACont

/-!
# Chapter 1, §4 — Lemma 4.2, continuity of the Weil–Petersson metric (`l42_`, 下属1)

`l42_lemma_4_2` is a byte-identical copy of `lemma_4_2` (S4; relocated by the leader).

**Route.** `g_{μμ̄}(κ) = ‖P R(μ, κ)‖₂²` and `g_{μμ̄}(0) = ‖μ‖₂²` (`gWP_origin`).
- (P) `P` is the orthogonal projection onto `H^{-1,1}`, so `‖P f - μ‖₂ ≤ ‖f - μ‖₂` and
  `|g(κ) - g(0)| ≤ d (d + 2‖μ‖₂)` with `d = ‖R(μ, κ) - μ‖₂`.
- (R) `R(μ, κ) → μ` in `L²(𝔻*, ρ)` as `κ → 0` in `Ω^{-1,1}(𝔻*)`. This is the step the memoir skips (TT:2176–2184,
  DIFF 3-20):
  - a uniform bound `‖R(ν, κ)‖₂ ≤ C ‖ν‖₂` for small harmonic `κ` (change of variables `wpcv_R_lintegral` and the
    Jacobian–density comparison of Lemma 2.5);
  - density of continuous cut-offs `η` with compact support in `𝔻*`;
  - for such `η`, the pull-back by `w_κ` and `|w_z/\overline{w_z} - 1| |w_z| ≤ 2 |w_z - 1|`;
  - `w_z → 1` in `L²` on closed balls of `𝔻*` (W), from the energy bound `∫ |w_z|² ≤ K |w(B)|` and
    `∫ w_z χ = -∫ w χ_z → ∫ χ` (integration by parts for q.c. maps, `w_κ → id` locally uniformly).
- `Λ` is continuous linear with `Λ 0 = 0` and values in `Ω^{-1,1}(𝔻*)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `ρ ≥ 0`. -/
theorem l42_rho_nonneg (z : ℂ) : 0 ≤ rho z := by
  unfold rho
  positivity

/-- A function with finite `‖ ‖₂` on `𝔻*` lies in `L²(𝔻*, ρ d²z)`, written as `L²` of the measure `ρ d²z`. -/
theorem l42_memLp {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hn : normL2 unitDiscExterior f < ∞) :
    MemLp f 2 ((volume.restrict unitDiscExterior).withDensity (fun z => ENNReal.ofReal (rho z))) :=
  memLp_iff.2 (by rw [← grp_normL2_eq _ hf]; exact hn)

/-- `‖f‖₂` is the norm of the corresponding element of `L²(𝔻*, ρ d²z)`. -/
theorem l42_norm {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hn : normL2 unitDiscExterior f < ∞) :
    normL2 unitDiscExterior f = ENNReal.ofReal ‖(l42_memLp hf hn).toLp f‖ := by
  rw [Lp.norm_toLp, ENNReal.ofReal_toReal (l42_memLp hf hn).ne, ← grp_normL2_eq _ hf]

/-- `∬_{𝔻*} f ḡ ρ d²z = ⟨g, f⟩` in `L²(𝔻*, ρ d²z)`. -/
theorem l42_inner {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hfn : normL2 unitDiscExterior f < ∞) (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior))
    (hgn : normL2 unitDiscExterior g < ∞) :
    (∫ z in unitDiscExterior, f z * conj (g z) * rho z) =
      inner ℂ ((l42_memLp hg hgn).toLp g) ((l42_memLp hf hfn).toLp f) := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by unfold rho; fun_prop
  rw [L2.inner_def]
  have h1 := (l42_memLp hf hfn).coeFn_toLp
  have h2 := (l42_memLp hg hgn).coeFn_toLp
  rw [integral_congr_ae (h1.mp (h2.mono fun z hz2 hz1 => by rw [hz1, hz2]))]
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [ENNReal.toReal_ofReal (l42_rho_nonneg z), RCLike.inner_apply, Complex.real_smul]
  ring

/-- `f - g` in `L²(𝔻*, ρ d²z)`. -/
theorem l42_toLp_sub {a b : ℂ → ℂ} (ha : AEStronglyMeasurable a (volume.restrict unitDiscExterior))
    (hb : AEStronglyMeasurable b (volume.restrict unitDiscExterior)) (hna : normL2 unitDiscExterior a < ∞)
    (hnb : normL2 unitDiscExterior b < ∞)
    (hab : AEStronglyMeasurable (fun z => a z - b z) (volume.restrict unitDiscExterior))
    (hn : normL2 unitDiscExterior (fun z => a z - b z) < ∞) :
    (l42_memLp hab hn).toLp (fun z => a z - b z) = (l42_memLp ha hna).toLp a - (l42_memLp hb hnb).toLp b := by
  rw [← MemLp.toLp_sub]
  rfl

/-- `P f` has finite `‖ ‖₂` when `f` has. -/
theorem l42_P_fin {f : LinfStar} (hf : normL2 unitDiscExterior f < ∞) :
    normL2 unitDiscExterior (harmonicProj f) < ∞ := by
  obtain ⟨⟨ν', hν', he⟩, -⟩ := harmonicProj_orthogonal f hf
  rw [grp_normL2_congr_ae he]
  obtain ⟨-, -, -, h⟩ := hν'
  exact h

/-- Measurability of a harmonic `μ ∈ H^{-1,1}(𝔻*)` on `𝔻*`. -/
theorem l42_aesm {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    AEStronglyMeasurable μ (volume.restrict unitDiscExterior) :=
  (wp_harmonic_continuousOn hμ).aestronglyMeasurable wp_exterior_isOpen.measurableSet

/-- `‖μ‖₂ < ∞` for `μ ∈ H^{-1,1}(𝔻*)`. -/
theorem l42_fin {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : normL2 unitDiscExterior μ < ∞ := by
  obtain ⟨-, -, -, h⟩ := hμ
  exact h

/-- The normed form of (P): `‖P f - μ‖ ≤ ‖f - μ‖` in `L²(𝔻*, ρ d²z)`. -/
theorem l42_P_dist_norm {f : LinfStar} (hf : normL2 unitDiscExterior f < ∞) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    ‖(l42_memLp (Lp.aestronglyMeasurable (harmonicProj f)) (l42_P_fin hf)).toLp (harmonicProj f) -
        (l42_memLp (l42_aesm hμ) (l42_fin hμ)).toLp μ‖ ≤
      ‖(l42_memLp (Lp.aestronglyMeasurable f) hf).toLp f - (l42_memLp (l42_aesm hμ) (l42_fin hμ)).toLp μ‖ := by
  obtain ⟨⟨ν', hν', he⟩, horth⟩ := harmonicProj_orthogonal f hf
  set F := (l42_memLp (Lp.aestronglyMeasurable f) hf).toLp f with hF
  set Q := (l42_memLp (Lp.aestronglyMeasurable (harmonicProj f)) (l42_P_fin hf)).toLp (harmonicProj f) with hQ
  set M := (l42_memLp (l42_aesm hμ) (l42_fin hμ)).toLp μ with hM
  have hd : AEStronglyMeasurable (fun z => f z - harmonicProj f z) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable (harmonicProj f))
  have hdn : normL2 unitDiscExterior (fun z => f z - harmonicProj f z) < ∞ :=
    lt_of_le_of_lt (grp_normL2_sub_le (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable (harmonicProj f)))
      (ENNReal.add_lt_top.2 ⟨hf, l42_P_fin hf⟩)
  have hFQ : (l42_memLp hd hdn).toLp (fun z => f z - harmonicProj f z) = F - Q := by
    rw [hF, hQ, ← MemLp.toLp_sub]
    rfl
  have hν'a := l42_aesm hν'
  have hQν : Q = (l42_memLp hν'a (l42_fin hν')).toLp ν' := by
    rw [hQ]
    exact MemLp.toLp_congr _ _ (he.filter_mono (withDensity_absolutelyContinuous _ _).ae_le)
  have hz1 : inner ℂ Q (F - Q) = 0 := by
    rw [← hFQ, hQν, ← l42_inner hd hdn hν'a (l42_fin hν')]
    exact horth ν' hν'
  have hz2 : inner ℂ M (F - Q) = 0 := by
    rw [← hFQ, ← l42_inner hd hdn (l42_aesm hμ) (l42_fin hμ)]
    exact horth μ hμ
  have hz : inner ℂ (Q - M) (F - Q) = 0 := by rw [inner_sub_left, hz1, hz2, sub_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Q - M) (F - Q) hz
  have he2 : Q - M + (F - Q) = F - M := by abel
  rw [he2] at hp
  have h0 : 0 ≤ ‖F - Q‖ * ‖F - Q‖ := mul_self_nonneg _
  nlinarith [norm_nonneg (Q - M), norm_nonneg (F - M), h0, hp]

/-- (P) `P` moves no `L²` function farther from `H^{-1,1}(𝔻*)`: `‖P f - μ‖₂ ≤ ‖f - μ‖₂` for `μ ∈ H^{-1,1}(𝔻*)`. -/
theorem l42_P_dist {f : LinfStar} (hf : normL2 unitDiscExterior f < ∞) {μ : ℂ → ℂ}
    (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    normL2 unitDiscExterior (fun z => harmonicProj f z - μ z) ≤ normL2 unitDiscExterior (fun z => f z - μ z) := by
  have hd := l42_P_dist_norm hf hμ
  have h1 : AEStronglyMeasurable (fun z => harmonicProj f z - μ z) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable (harmonicProj f)).sub (l42_aesm hμ)
  have h1n : normL2 unitDiscExterior (fun z => harmonicProj f z - μ z) < ∞ :=
    lt_of_le_of_lt (grp_normL2_sub_le (Lp.aestronglyMeasurable (harmonicProj f)) (l42_aesm hμ))
      (ENNReal.add_lt_top.2 ⟨l42_P_fin hf, l42_fin hμ⟩)
  have h2 : AEStronglyMeasurable (fun z => f z - μ z) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable f).sub (l42_aesm hμ)
  have h2n : normL2 unitDiscExterior (fun z => f z - μ z) < ∞ :=
    lt_of_le_of_lt (grp_normL2_sub_le (Lp.aestronglyMeasurable f) (l42_aesm hμ))
      (ENNReal.add_lt_top.2 ⟨hf, l42_fin hμ⟩)
  rw [l42_norm h1 h1n, l42_norm h2 h2n, l42_toLp_sub (Lp.aestronglyMeasurable _) (l42_aesm hμ) (l42_P_fin hf) (l42_fin hμ) h1 h1n,
    l42_toLp_sub (Lp.aestronglyMeasurable _) (l42_aesm hμ) hf (l42_fin hμ) h2 h2n]
  exact ENNReal.ofReal_le_ofReal hd

/-- `‖R(μ, κ)‖₂ < ∞` and measurability, packaged. -/
theorem l42_R_fin {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    normL2 unitDiscExterior (Rnm (toLinf μ) κ) < ∞ :=
  WPCV.x5_Rnm_L2 hμ hκ

/-- (P) `|g_{μμ̄}(κ) - g_{μμ̄}(0)| ≤ d (d + 2‖μ‖₂)` with `d = ‖R(μ, κ) - μ‖₂`. -/
theorem l42_gWP_near {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ‖gWP μ μ κ - wpInner μ μ‖ ≤ (normL2 unitDiscExterior (fun z => Rnm (toLinf μ) κ z - μ z)).toReal *
      ((normL2 unitDiscExterior (fun z => Rnm (toLinf μ) κ z - μ z)).toReal +
        2 * (normL2 unitDiscExterior μ).toReal) := by
  set R := Rnm (toLinf μ) κ with hRd
  have hR := l42_R_fin hμ hκ
  have hPa := Lp.aestronglyMeasurable (harmonicProj R)
  have hPn := l42_P_fin hR
  have hd := l42_P_dist_norm hR hμ
  set Q := (l42_memLp hPa hPn).toLp (harmonicProj R) with hQ
  set M := (l42_memLp (l42_aesm hμ) (l42_fin hμ)).toLp μ with hM
  set F := (l42_memLp (Lp.aestronglyMeasurable R) hR).toLp R with hF
  have h2 : AEStronglyMeasurable (fun z => R z - μ z) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable R).sub (l42_aesm hμ)
  have h2n : normL2 unitDiscExterior (fun z => R z - μ z) < ∞ :=
    lt_of_le_of_lt (grp_normL2_sub_le (Lp.aestronglyMeasurable R) (l42_aesm hμ))
      (ENNReal.add_lt_top.2 ⟨hR, l42_fin hμ⟩)
  have hdist : (normL2 unitDiscExterior (fun z => R z - μ z)).toReal = ‖F - M‖ := by
    rw [l42_norm h2 h2n, l42_toLp_sub (Lp.aestronglyMeasurable _) (l42_aesm hμ) hR (l42_fin hμ) h2 h2n, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hm : (normL2 unitDiscExterior μ).toReal = ‖M‖ := by
    rw [l42_norm (l42_aesm hμ) (l42_fin hμ), ENNReal.toReal_ofReal (norm_nonneg _)]
  have hg : gWP μ μ κ = ((‖Q‖ ^ 2 : ℝ) : ℂ) := by
    unfold gWP
    rw [l42_inner hPa hPn hPa hPn, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hw : wpInner μ μ = ((‖M‖ ^ 2 : ℝ) : ℂ) := by
    unfold wpInner
    rw [l42_inner (l42_aesm hμ) (l42_fin hμ) (l42_aesm hμ) (l42_fin hμ), inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hdist, hm, hg, hw, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hQM : ‖Q - M‖ ≤ ‖F - M‖ := hd
  have t1 : |‖Q‖ - ‖M‖| ≤ ‖Q - M‖ := abs_norm_sub_norm_le Q M
  have t2 : ‖Q‖ + ‖M‖ ≤ ‖Q - M‖ + 2 * ‖M‖ := by
    have := norm_le_norm_add_norm_sub' Q M
    linarith
  rw [show ‖Q‖ ^ 2 - ‖M‖ ^ 2 = (‖Q‖ - ‖M‖) * (‖Q‖ + ‖M‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Q‖ + ‖M‖)]
  calc |‖Q‖ - ‖M‖| * (‖Q‖ + ‖M‖) ≤ ‖Q - M‖ * (‖Q - M‖ + 2 * ‖M‖) :=
        mul_le_mul t1 t2 (by positivity) (norm_nonneg _)
    _ ≤ ‖F - M‖ * (‖F - M‖ + 2 * ‖M‖) :=
        mul_le_mul hQM (by linarith) (by positivity) (norm_nonneg _)

/-- `toLinf ν = ν` for `ν ∈ L∞(𝔻*)` (its own representative). -/
theorem l42_toLinf_coe (ν : LinfStar) : toLinf (ν : ℂ → ℂ) = ν := by
  unfold toLinf
  rw [dif_pos (Lp.memLp ν)]
  exact Lp.toLp_coeFn ν (Lp.memLp ν)

/-- Off the pole, `w_κ` has a finite value: `w_κ(z) ≠ 0` for `|w_κ(z)| > 1` forces `w_κ(z) ≠ ∞`. -/
theorem l42_wAS_ne {κ : LinfStar} {z : ℂ} (h : wA κ z ≠ 0) : wAS κ (z : ExtPlane) ≠ extInf := by
  intro he
  apply h
  show finPart (wAS κ (z : ExtPlane)) = 0
  rw [he]
  rfl

/-- The Jacobian–density comparison of Lemma 2.5 (`ε = 1`): `|w_z|² ρ(w) ≤ 2 ρ(z)`. -/
theorem l42_dens_le {δ : ℝ} (hδ : Lemma25Prop 1 δ) {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) (hκδ : ‖κ‖ < δ)
    {z : ℂ} (hz : z ∈ unitDiscExterior) (hw : wA κ z ≠ 0) :
    ‖dz (wA κ) z‖ ^ 2 * rho (wA κ z) ≤ 2 * rho z := by
  obtain ⟨-, -, hP⟩ := hδ
  have hl := (hP κ hκ hκδ z (Or.inr hz)).1 (l42_wAS_ne hw)
  have hX := (abs_lt.1 hl).2
  unfold rho
  calc ‖dz (wA κ) z‖ ^ 2 * (4 / (1 - ‖wA κ z‖ ^ 2) ^ 2) = 4 * (‖dz (wA κ) z‖ ^ 2 / (1 - ‖wA κ z‖ ^ 2) ^ 2) := by
        ring
    _ ≤ 4 * (2 * (1 / (1 - ‖z‖ ^ 2) ^ 2)) := by linarith
    _ = 2 * (4 / (1 - ‖z‖ ^ 2) ^ 2) := by ring

/-- (R1) A uniform `L²(𝔻*, ρ)` bound for `ν ↦ R(ν, κ)`, `κ` small and harmonic (Lemma 2.5). -/
theorem l42_R_bound : ∃ δ > 0, ∃ C : ℝ, ∀ κ ∈ harmonicBeltrami, ‖κ‖ < δ → ∀ ν : LinfStar,
    normL2 unitDiscExterior (Rnm ν κ) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ν := by
  obtain ⟨δ, hδ⟩ := lemma_2_5 (one_pos : (0 : ℝ) < 1)
  have hδ' := hδ
  obtain ⟨hδ0, hδ1, -⟩ := hδ'
  have hK0 : 0 ≤ 2 / (1 - δ ^ 2) := div_nonneg (by norm_num) (by nlinarith)
  refine ⟨δ, hδ0, (2 / (1 - δ ^ 2)) ^ (1 / 2 : ℝ), fun κ hκ hκδ ν => ?_⟩
  have hκb : κ ∈ LinfStarBall := mem_ball_zero_iff.2 (by linarith)
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hto : (toLinf (ν : ℂ → ℂ) : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] ν := by
    rw [l42_toLinf_coe]
  have h := WPCV.wpcv_R_lintegral hto hκb
  rw [l42_toLinf_coe] at h
  have h2 : ∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (‖dz (wA κ) z‖ ^ 2 * rho (wA κ z)) ≤
      ∫⁻ z in unitDiscExterior, ENNReal.ofReal 2 * ((‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) := by
    apply lintegral_mono_ae
    filter_upwards [WPCV.wpcv_ae_facts hκb, ae_restrict_mem hE] with z hz hzE
    obtain ⟨hw1, -, -, -⟩ := hz
    have hw : wA κ z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw1
      linarith
    rw [mul_left_comm, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (l42_dens_le hδ hκ hκδ hzE hw)) (zero_le)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have hc : ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * ENNReal.ofReal 2 ≤ ENNReal.ofReal (2 / (1 - δ ^ 2)) := by
    have hk1 : 0 < 1 - δ ^ 2 := by nlinarith
    have hk2 : 1 - δ ^ 2 ≤ 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith))]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div_mul_eq_div, div_le_div_iff_of_pos_left (by norm_num) (by linarith) hk1]
    exact hk2
  have h3 : ∫⁻ z in unitDiscExterior, (‖(Rnm ν κ : ℂ → ℂ) z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
      ENNReal.ofReal (2 / (1 - δ ^ 2)) *
        ∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) :=
    calc _ ≤ _ := h
      _ ≤ ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * (ENNReal.ofReal 2 *
            ∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) :=
          mul_le_mul_of_nonneg_left h2 (zero_le)
      _ = ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * ENNReal.ofReal 2 *
            ∫⁻ z in unitDiscExterior, (‖ν z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (zero_le)
  unfold normL2
  rw [← ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow h3 (by norm_num)

/-- The radial cut-off `g_n(z) = min(1, max(0, n(|z| - 1) - 1)) · min(1, max(0, n + 1 - |z|))` is continuous. -/
theorem l42_cut_cont (n : ℝ) :
    Continuous fun z : ℂ => min 1 (max 0 (n * (‖z‖ - 1) - 1)) * min 1 (max 0 (n + 1 - ‖z‖)) :=
  (continuous_const.min (continuous_const.max
    ((continuous_const.mul (continuous_norm.sub continuous_const)).sub continuous_const))).mul
    (continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm)))

/-- `0 ≤ g_n ≤ 1`. -/
theorem l42_cut_bounds (n : ℝ) (z : ℂ) :
    0 ≤ min 1 (max 0 (n * (‖z‖ - 1) - 1)) * min 1 (max 0 (n + 1 - ‖z‖)) ∧
      min 1 (max 0 (n * (‖z‖ - 1) - 1)) * min 1 (max 0 (n + 1 - ‖z‖)) ≤ 1 := by
  have a0 : 0 ≤ min 1 (max 0 (n * (‖z‖ - 1) - 1)) := le_min zero_le_one (le_max_left _ _)
  have a1 : min 1 (max 0 (n * (‖z‖ - 1) - 1)) ≤ 1 := min_le_left _ _
  have b0 : 0 ≤ min 1 (max 0 (n + 1 - ‖z‖)) := le_min zero_le_one (le_max_left _ _)
  have b1 : min 1 (max 0 (n + 1 - ‖z‖)) ≤ 1 := min_le_left _ _
  exact ⟨mul_nonneg a0 b0, mul_le_one₀ a1 b0 b1⟩

/-- `g_n` vanishes for `n(|z| - 1) ≤ 1` and for `|z| ≥ n + 1`. -/
theorem l42_cut_zero {n : ℝ} {z : ℂ} (h : n * (‖z‖ - 1) ≤ 1 ∨ n + 1 ≤ ‖z‖) :
    min 1 (max 0 (n * (‖z‖ - 1) - 1)) * min 1 (max 0 (n + 1 - ‖z‖)) = 0 := by
  rcases h with h | h
  · rw [max_eq_left (by linarith), min_eq_right zero_le_one, zero_mul]
  · rw [max_eq_left (show n + 1 - ‖z‖ ≤ 0 by linarith), min_eq_right zero_le_one, mul_zero]

/-- `g_n(z) = 1` for `n(|z| - 1) ≥ 2` and `|z| ≤ n`. -/
theorem l42_cut_one {n : ℝ} {z : ℂ} (h1 : 2 ≤ n * (‖z‖ - 1)) (h2 : ‖z‖ ≤ n) :
    min 1 (max 0 (n * (‖z‖ - 1) - 1)) * min 1 (max 0 (n + 1 - ‖z‖)) = 1 := by
  rw [max_eq_right (by linarith), min_eq_left (by linarith), max_eq_right (by linarith),
    min_eq_left (by linarith), one_mul]

/-- (R2) Continuous cut-offs with compact support in `𝔻*` are dense in `H^{-1,1}(𝔻*)` for `‖ ‖₂`. -/
theorem l42_cutoff {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) {e : ℝ} (he : 0 < e) :
    ∃ η : ℂ → ℂ, Continuous η ∧ HasCompactSupport η ∧ tsupport η ⊆ unitDiscExterior ∧
      normL2 unitDiscExterior (fun z => μ z - η z) < ENNReal.ofReal e := by
  have hcont : ContinuousOn μ unitDiscExterior := wp_harmonic_continuousOn hμ
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  set g : ℕ → ℂ → ℝ := fun n z => min 1 (max 0 ((n : ℝ) * (‖z‖ - 1) - 1)) * min 1 (max 0 ((n : ℝ) + 1 - ‖z‖))
    with hgd
  -- the limit
  have hlim : Tendsto (fun n : ℕ => ∫⁻ z in unitDiscExterior,
      (‖μ z - μ z * (g n z : ℂ)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)) atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ z in unitDiscExterior, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence' (fun z => (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z))
      (fun n => ?_) (fun n => Eventually.of_forall fun z => ?_) ?_ ?_
    · have hgm : Measurable (g n) := (l42_cut_cont n).measurable
      have hm : AEStronglyMeasurable (fun z => μ z - μ z * (g n z : ℂ)) (volume.restrict unitDiscExterior) :=
        (l42_aesm hμ).sub ((l42_aesm hμ).mul (Complex.measurable_ofReal.comp hgm).aestronglyMeasurable)
      have hr : Measurable fun z : ℂ => ENNReal.ofReal (rho z) := by unfold rho; fun_prop
      exact ((hm.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2).mul hr.aemeasurable
    · show (‖μ z - μ z * (g n z : ℂ)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) ≤
        (‖μ z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z)
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le ?_ 2) zero_le
      rw [show μ z - μ z * (g n z : ℂ) = μ z * ((1 - g n z : ℝ) : ℂ) by push_cast; ring, nnnorm_mul]
      have hb := l42_cut_bounds (n : ℝ) z
      have h1 : ‖((1 - g n z : ℝ) : ℂ)‖₊ ≤ 1 := by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        push_cast
        linarith
      exact ENNReal.coe_le_coe.2 (mul_le_of_le_one_right zero_le h1)
    · have h := l42_fin hμ
      unfold normL2 at h
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h |>.ne
    · filter_upwards [ae_restrict_mem hE] with z hz
      have hz1 : 1 < ‖z‖ := hz
      have hev : ∀ᶠ n : ℕ in atTop, g n z = 1 := by
        obtain ⟨N1, hN1⟩ := exists_nat_ge (2 / (‖z‖ - 1))
        obtain ⟨N2, hN2⟩ := exists_nat_ge ‖z‖
        filter_upwards [eventually_ge_atTop (max N1 N2)] with n hn
        have hn1 : (N1 : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
        have hn2 : (N2 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
        apply l42_cut_one
        · have : 2 / (‖z‖ - 1) ≤ n := hN1.trans hn1
          rwa [div_le_iff₀ (by linarith)] at this
        · linarith
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [hn]
      simp
  have hlim' : Tendsto (fun n : ℕ => normL2 unitDiscExterior (fun z => μ z - μ z * (g n z : ℂ))) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0 |>.comp hlim
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  obtain ⟨n, hn, hn1⟩ := ((hlim'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 he))).and
    (eventually_ge_atTop 1)).exists
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- the cut-off and its support
  set K : Set ℂ := {z | 1 + 1 / (n : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ n + 1} with hKd
  have hKc : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hKcpt : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := n + 1)).subset
      fun z hz => by simpa using hz.2)
  have hKE : K ⊆ unitDiscExterior := fun z hz => by
    show 1 < ‖z‖
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith [hz.1]
  have hsupp : Function.support (fun z => μ z * (g n z : ℂ)) ⊆ K := by
    intro z hz
    by_contra hzK
    apply hz
    have h0 : g n z = 0 := by
      apply l42_cut_zero
      simp only [hKd, mem_ofPred_eq, not_and_or, not_le] at hzK
      rcases hzK with h | h
      · left
        have : ‖z‖ - 1 < 1 / (n : ℝ) := by linarith
        rw [lt_div_iff₀ (by linarith)] at this
        nlinarith
      · right
        linarith
    simp [h0]
  refine ⟨fun z => μ z * (g n z : ℂ), ?_, ?_, ?_, hn⟩
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : 1 < ‖z‖
    · exact ((hcont.continuousAt (wp_exterior_isOpen.mem_nhds hz)).mul
        (Complex.continuous_ofReal.comp (l42_cut_cont n)).continuousAt)
    · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
      have hnb : {y : ℂ | ‖y‖ < 1 + 1 / (n : ℝ)} ∈ 𝓝 z :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds (by
          have : 0 < 1 / (n : ℝ) := by positivity
          show ‖z‖ < 1 + 1 / (n : ℝ)
          linarith [not_lt.1 hz])
      filter_upwards [hnb] with y hy
      have : y ∉ K := fun hyK => by
        have := hyK.1
        exact absurd hy (not_lt.2 this)
      exact (Function.notMem_support.1 fun h => this (hsupp h)).symm
  · exact HasCompactSupport.intro hKcpt fun z hz => Function.notMem_support.1 fun h => hz (hsupp h)
  · exact (closure_minimal hsupp hKc).trans hKE

/-- `w_κ` is quasiconformal on an open set containing every point where its value is not the junk `0`. -/
theorem l42_wA_kqc {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    ∃ (V : Set ℂ) (K : ℝ), IsOpen V ∧ (∀ z, wA κ z ≠ 0 → z ∈ V) ∧ IsKQC (wA κ) V K := by
  obtain ⟨a, b, c, d, W, hdet, hW, hform, -⟩ := bc_wA_form hκ
  obtain ⟨K, hK⟩ := hW.1
  have hWc : Continuous W := by
    have := hK.2.2.1.1
    rwa [continuousOn_univ] at this
  set V : Set ℂ := {z | c * W z + d ≠ 0} with hV
  have hVo : IsOpen V := isOpen_ne_fun ((continuous_const.mul hWc).add continuous_const) continuous_const
  have hWV : IsKQC W V K := t3b_isKQC_restrict hK hVo (subset_univ _)
  have hWVo : IsOpen (W '' V) := isOpen_image_of_isKQC hWV
  have hVden : ∀ z ∈ W '' V, c * z + d ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hconf : IsConformalOnto (mobiusFn a b c d) (W '' V) (mobiusFn a b c d '' (W '' V)) := by
    refine ⟨fun z hz => ?_, bc_mobiusFn_injOn hdet hVden, rfl⟩
    exact (bc_mobiusFn_hasDerivAt (hVden z hz)).differentiableAt.differentiableWithinAt
  have hg : IsKQC (mobiusFn a b c d) (W '' V) 1 := isKQC_one_of_conformal hWVo hconf
  have hcomp := thm7_1_comp hWV hg (subset_refl _)
  have hfun : wA κ = mobiusFn a b c d ∘ W := funext hform
  refine ⟨V, K * 1, hVo, fun z hz => ?_, by rw [hfun]; exact hcomp⟩
  show c * W z + d ≠ 0
  intro h0
  apply hz
  rw [hform z]
  simp [mobiusFn, h0]

/-- Integration by parts against `∂_z` for a quasiconformal map (the `∂_z` twin of `abW_ibp`). -/
theorem l42_ibp_dz {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
    ∫ z in U, f z * dz ψ z = -∫ z in U, ψ z * dz f z := by
  have hU : IsOpen U := hf.1
  have hv := (thm9_5_L2_derivatives hf).1
  obtain ⟨h1, hI⟩ := sp_ibp hU hv hψ hcψ hsψ
  have hKc : IsCompact (tsupport ψ) := hcψ.isCompact
  have hKm : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
  have hψ0 : ∀ z ∉ tsupport ψ, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hfc : ContinuousOn f U := hf.2.2.1.1
  have hint1 : ∀ e : ℂ, IntegrableOn (fun z => fderiv ℝ ψ z e * f z) U := by
    intro e
    have hdψc : Continuous (fun z => fderiv ℝ ψ z e) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine (sp_ibp_integrable_of_support hKm ?_ fun z hz => by
      rw [sp_fderiv_eq_zero_of_notMem_tsupport hz e, zero_mul]).integrableOn
    exact (hdψc.continuousOn.mul (hfc.mono hsψ)).integrableOn_compact hKc
  have hψL : MemLp ψ 2 (volume.restrict (tsupport ψ)) :=
    (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hcψ).restrict _
  have hint2 : ∀ g : ℂ → ℂ, MemLp g 2 (volume.restrict (tsupport ψ)) →
      IntegrableOn (fun z => ψ z * g z) U := fun g hg =>
    (sp_ibp_integrable_of_support hKm (hψL.integrable_mul hg) fun z hz => by
      rw [Pi.mul_apply, hψ0 z hz, zero_mul]).integrableOn
  have hgx := hint2 _ (hv.1 _ hsψ hKc).1
  have hgy := hint2 _ (hv.1 _ hsψ hKc).2
  have hae : ∀ᵐ z ∂(volume.restrict U), ψ z * dz f z =
      (ψ z * partialX f z - I * (ψ z * partialY f z)) / 2 := by
    filter_upwards [thm9_3_differentiable_ae hf] with z hz
    rw [partialX_eq_of_differentiableAt hz, partialY_eq_of_differentiableAt hz]
    unfold dz
    ring
  have hL : ∫ z in U, f z * dz ψ z =
      ((∫ z in U, fderiv ℝ ψ z 1 * f z) - I * ∫ z in U, fderiv ℝ ψ z I * f z) / 2 := by
    rw [← integral_const_mul, ← integral_sub (hint1 1) ((hint1 I).const_mul I), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [dz]
    ring
  have hR : ∫ z in U, ψ z * dz f z =
      ((∫ z in U, ψ z * partialX f z) - I * ∫ z in U, ψ z * partialY f z) / 2 := by
    rw [integral_congr_ae hae, ← integral_const_mul, ← integral_sub hgx (hgy.const_mul I),
      ← integral_div]
  rw [hL, hR, h1, hI]
  ring

/-- The energy bound `∫_S |(w_κ)_z|² ≤ (1 - ‖κ‖²)⁻¹ |T|` for `w_κ(S) ⊆ T`. -/
theorem l42_energy {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {S T : Set ℂ} (hS : MeasurableSet S)
    (hSE : S ⊆ unitDiscExterior) (hT : MeasurableSet T) (hST : ∀ z ∈ S, wA κ z ∈ T) :
    ∫⁻ z in S, ‖dz (wA κ) z‖ₑ ^ 2 ≤ ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * volume T := by
  have hk := WPCV.wpcv_norm_lt_one hκ
  have hk0 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hl := WPCV.wpcv_lcov hκ (T.indicator 1)
  rw [lintegral_indicator_one hT] at hl
  have h1 : ∫⁻ z in S, ‖dz (wA κ) z‖ₑ ^ 2 =
      ∫⁻ z in unitDiscExterior, S.indicator (fun z => ‖dz (wA κ) z‖ₑ ^ 2) z := by
    rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.2 hSE]
  rw [h1]
  calc ∫⁻ z in unitDiscExterior, S.indicator (fun z => ‖dz (wA κ) z‖ₑ ^ 2) z
      ≤ ∫⁻ z in unitDiscExterior, ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) *
          (ENNReal.ofReal (jacobian (wA κ) z) * T.indicator 1 (wA κ z)) := by
        apply lintegral_mono_ae
        filter_upwards [WPCV.wpcv_ae_facts hκ] with z hz
        obtain ⟨-, hj, hkz, -⟩ := hz
        by_cases hzS : z ∈ S
        · rw [indicator_of_mem hzS, indicator_of_mem (hST z hzS), Pi.one_apply, mul_one,
            ← ENNReal.ofReal_mul (div_nonneg zero_le_one hk0.le), ← ofReal_norm_eq_enorm,
            ← ENNReal.ofReal_pow (norm_nonneg _), hj]
          apply ENNReal.ofReal_le_ofReal
          have h2 : 1 - ‖κ‖ ^ 2 ≤ 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
          rw [one_div, ← mul_assoc, ← div_eq_inv_mul]
          exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_div hk0).2 h2)
        · rw [indicator_of_notMem hzS]
          exact zero_le
    _ = ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * (volume.restrict unitDiscExterior) T := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hl]
    _ ≤ ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * volume T :=
        mul_le_mul_of_nonneg_left (Measure.restrict_apply_le _ _) zero_le

/-- `∂_z ψ = 0` off the support of `ψ`. -/
theorem l42_dz_zero {ψ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport ψ) : dz ψ z = 0 := by
  unfold dz
  rw [sp_fderiv_eq_zero_of_notMem_tsupport hz, sp_fderiv_eq_zero_of_notMem_tsupport hz]
  ring

/-- `|a - 1|² = |a|² - 2 Re a + 1`. -/
theorem l42_sq_norm_sub_one (a : ℂ) : ‖a - 1‖ ^ 2 = ‖a‖ ^ 2 - 2 * a.re + 1 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one]
  simp
  ring

/-- `∂_z z = 1`. -/
theorem l42_dz_id (z : ℂ) : dz (fun u : ℂ => u) z = 1 := by
  unfold dz
  rw [show (fun u : ℂ => u) = id from rfl, fderiv_id]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  rw [I_mul_I]
  norm_num

/-- The identity is `1`-q.c. on `ℂ`. -/
theorem l42_id_kqc : IsKQC (fun u : ℂ => u) univ 1 :=
  isKQC_one_of_conformal isOpen_univ ⟨differentiableOn_id, injOn_id _, image_id _⟩

/-- The `L²` estimate behind (W), for one `κ`: with a bump `χ` (`= 1` on `B(c, r)`, supported in `B̄(c, t)` inside
`𝔻*`) and `|w_κ - id| < ε₁` on `B̄(c, t)`,
`∫_{B(c,r)} |(w_κ)_z - 1|² ≤ (1 - ‖κ‖²)⁻¹ π (t + ε₁)² - π r² + 2 ε₁ ∫ |∂_z χ|`. -/
theorem l42_wz_est {c : ℂ} (χ : ContDiffBump c) (hSE : closedBall c χ.rOut ⊆ unitDiscExterior) {κ : LinfStar}
    (hκ : κ ∈ LinfStarBall) {ε₁ : ℝ} (hε₁ : ε₁ ≤ 1 / 2) (hnear : ∀ z ∈ closedBall c χ.rOut, ‖wA κ z - z‖ < ε₁) :
    ∫⁻ z in closedBall c χ.rIn, ‖dz (wA κ) z - 1‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2) * (π * (χ.rOut + ε₁) ^ 2) - π * χ.rIn ^ 2 +
        2 * ε₁ * ∫ z in closedBall c χ.rOut, ‖dz (fun u => ((χ u : ℝ) : ℂ)) z‖) := by
  have hr : 0 < χ.rIn := χ.rIn_pos
  have hrt : χ.rIn < χ.rOut := χ.rIn_lt_rOut
  set r := χ.rIn with hrd
  set t := χ.rOut with htd
  set S := closedBall c t with hSd
  set B := closedBall c r with hBd
  set f := dz (wA κ) with hfd
  set ψ : ℂ → ℂ := fun u => ((χ u : ℝ) : ℂ) with hψd
  have hε0 : 0 < ε₁ := lt_of_le_of_lt (norm_nonneg _) (hnear c (mem_closedBall_self (by linarith)))
  have hk := WPCV.wpcv_norm_lt_one hκ
  have hk0 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBS : B ⊆ S := closedBall_subset_closedBall hrt.le
  have hSc : IsCompact S := isCompact_closedBall c t
  have hSfin : volume S ≠ ∞ := measure_closedBall_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  -- the bump
  have hψc : ContDiff ℝ 1 ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hψs : HasCompactSupport ψ := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψt : tsupport ψ ⊆ S := by
    have h := tsupport_comp_subset Complex.ofReal_zero (⇑χ)
    rw [χ.tsupport_eq] at h
    exact h
  have hψ0 : ∀ z ∉ S, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport fun h => hz (hψt h)
  have hdψ0 : ∀ z ∉ S, dz ψ z = 0 := fun z hz => l42_dz_zero fun h => hz (hψt h)
  have hdψc : Continuous (dz ψ) := by
    have h1 : Continuous fun z => fderiv ℝ ψ z 1 := (hψc.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h2 : Continuous fun z => fderiv ℝ ψ z I := (hψc.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (h1.sub (continuous_const.mul h2)).div_const 2
  have hχc : Continuous (⇑χ) := χ.continuous
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => χ.nonneg
  have hχ1 : ∀ z, χ z ≤ 1 := fun z => χ.le_one
  -- the map near the identity
  obtain ⟨V, K, hVo, hVmem, hVk⟩ := l42_wA_kqc hκ
  have hwne : ∀ z ∈ S, wA κ z ≠ 0 := by
    intro z hz h0
    have h1 : 1 < ‖z‖ := hSE hz
    have h2 := hnear z hz
    rw [h0, zero_sub, norm_neg] at h2
    linarith
  have hSV : S ⊆ V := fun z hz => hVmem z (hwne z hz)
  have hwm : Measurable (wA κ) := bc_wA_measurable hκ
  -- energy
  have hT : ∀ z ∈ S, wA κ z ∈ closedBall c (t + ε₁) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hnear z hz
    have h2 : ‖z - c‖ ≤ t := by rw [← dist_eq_norm]; exact hz
    calc ‖wA κ z - c‖ = ‖(wA κ z - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖wA κ z - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ t + ε₁ := by linarith
  have hE := l42_energy hκ hSm hSE measurableSet_closedBall hT
  have hvolT : (volume (closedBall c (t + ε₁))).toReal = π * (t + ε₁) ^ 2 := by
    rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith), ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  have hEfin : ∫⁻ z in S, ‖f z‖ₑ ^ 2 < ∞ :=
    lt_of_le_of_lt hE (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
  -- integrability
  have hfm : Measurable f := measurable_dz _
  have hf2 : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict S) := by
    refine ⟨(hfm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    show ∫⁻ z in S, ‖‖f z‖ ^ 2‖ₑ < ∞
    simpa only [enorm_pow, enorm_norm] using hEfin
  have hf1 : Integrable f (volume.restrict S) := by
    refine (hf2.add (integrable_const (1 : ℝ))).mono' hfm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    show ‖f z‖ ≤ ‖f z‖ ^ 2 + 1
    nlinarith [sq_nonneg (‖f z‖ - 1), norm_nonneg (f z)]
  have hψf : Integrable (fun z => ψ z * f z) (volume.restrict S) := by
    refine hf1.norm.mono' ((Complex.measurable_ofReal.comp hχc.measurable).mul hfm).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ0 z)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)
  have hdψi : Integrable (fun z => ‖dz ψ z‖) (volume.restrict S) :=
    (hdψc.norm.continuousOn.integrableOn_compact hSc)
  have hzi : Integrable (fun z => z * dz ψ z) (volume.restrict S) :=
    ((continuous_id.mul hdψc).continuousOn.integrableOn_compact hSc)
  have hwzi : Integrable (fun z => (wA κ z - z) * dz ψ z) (volume.restrict S) := by
    refine (hdψi.const_mul ε₁).mono' ((hwm.sub measurable_id).mul hdψc.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hnear z hz).le (norm_nonneg _)
  have hwi : Integrable (fun z => wA κ z * dz ψ z) (volume.restrict S) := by
    refine (hzi.add hwzi).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  -- integration by parts
  have hconv : ∀ (U : Set ℂ) (g : ℂ → ℂ), S ⊆ U → (∀ x ∉ S, g x = 0) → ∫ x in U, g x = ∫ x in S, g x := by
    intro U g hSU hg
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hg x fun h => hx (hSU h)),
      setIntegral_eq_integral_of_forall_compl_eq_zero hg]
  have h1 : ∫ z in S, wA κ z * dz ψ z = -∫ z in S, ψ z * f z := by
    have h := l42_ibp_dz hVk hψc hψs (hψt.trans hSV)
    rw [hconv V _ hSV (fun x hx => by rw [hdψ0 x hx, mul_zero]),
      hconv V _ hSV (fun x hx => by rw [hψ0 x hx, zero_mul])] at h
    exact h
  have h2 : ∫ z in S, z * dz ψ z = -∫ z in S, ψ z := by
    have h := l42_ibp_dz l42_id_kqc hψc hψs (subset_univ _)
    simp only [l42_dz_id, mul_one] at h
    rw [hconv univ _ (subset_univ _) (fun x hx => by rw [hdψ0 x hx, mul_zero]),
      hconv univ _ (subset_univ _) hψ0] at h
    exact h
  have h3 : ∫ z in S, wA κ z * dz ψ z = (∫ z in S, z * dz ψ z) + ∫ z in S, (wA κ z - z) * dz ψ z := by
    rw [← integral_add hzi hwzi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hA : ∫ z in S, ψ z * f z = (∫ z in S, ψ z) - ∫ z in S, (wA κ z - z) * dz ψ z := by
    linear_combination h1 - h3 - h2
  have hX : ‖∫ z in S, (wA κ z - z) * dz ψ z‖ ≤ ε₁ * ∫ z in S, ‖dz ψ z‖ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hdψi.const_mul ε₁) ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hnear z hz).le (norm_nonneg _)
  have hχS : ∫ z in S, ψ z = ((∫ z in S, χ z : ℝ) : ℂ) := integral_complex_ofReal
  have hχi : Integrable (fun z => χ z) (volume.restrict S) := hχc.continuousOn.integrableOn_compact hSc
  have hre : ∫ z in S, χ z * (f z).re = (∫ z in S, ψ z * f z).re := by
    rw [show (∫ z in S, ψ z * f z).re = RCLike.re (∫ z in S, ψ z * f z) from rfl, ← integral_re hψf]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show _ = (ψ z * f z).re
    simp only [hψd, Complex.re_ofReal_mul]
  have hRe : (∫ z in S, χ z) - ε₁ * (∫ z in S, ‖dz ψ z‖) ≤ ∫ z in S, χ z * (f z).re := by
    rw [hre, hA, Complex.sub_re, hχS, Complex.ofReal_re]
    have := (Complex.re_le_norm (∫ z in S, (wA κ z - z) * dz ψ z)).trans hX
    linarith
  -- the three pieces
  have hF5 : ∫ z in S, χ z * ‖f z‖ ^ 2 ≤ 1 / (1 - ‖κ‖ ^ 2) * (π * (t + ε₁) ^ 2) := by
    have hint : Integrable (fun z => χ z * ‖f z‖ ^ 2) (volume.restrict S) :=
      hf2.mono' (hχc.measurable.mul (hfm.norm.pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (mul_nonneg (hχ0 z) (sq_nonneg _))]
        exact mul_le_of_le_one_left (sq_nonneg _) (hχ1 z))
    calc ∫ z in S, χ z * ‖f z‖ ^ 2 ≤ ∫ z in S, ‖f z‖ ^ 2 :=
          integral_mono hint hf2 fun z => mul_le_of_le_one_left (sq_nonneg _) (hχ1 z)
      _ = (∫⁻ z in S, ‖f z‖ₑ ^ 2).toReal := by
          rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _)
            (hfm.norm.pow_const 2).aestronglyMeasurable]
          congr 1
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ (ENNReal.ofReal (1 / (1 - ‖κ‖ ^ 2)) * volume (closedBall c (t + ε₁))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne) hE
      _ = 1 / (1 - ‖κ‖ ^ 2) * (π * (t + ε₁) ^ 2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg zero_le_one hk0.le), hvolT]
  have hF6 : π * r ^ 2 ≤ ∫ z in S, χ z := by
    have hB1 : ∫ z in B, χ z = π * r ^ 2 := by
      rw [setIntegral_congr_fun hBm (fun z hz => χ.one_of_mem_closedBall hz), setIntegral_const, smul_eq_mul,
        mul_one, Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
      ring
    rw [← hB1]
    exact setIntegral_mono_set hχi (Eventually.of_forall fun z => hχ0 z) (Eventually.of_forall hBS)
  -- assembly
  have hpt : ∀ z, χ z * ‖f z - 1‖ ^ 2 = χ z * ‖f z‖ ^ 2 - 2 * (χ z * (f z).re) + χ z := by
    intro z
    rw [l42_sq_norm_sub_one]
    ring
  have hi1 : Integrable (fun z => χ z * ‖f z‖ ^ 2) (volume.restrict S) :=
    hf2.mono' (hχc.measurable.mul (hfm.norm.pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (mul_nonneg (hχ0 z) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (hχ1 z))
  have hi2 : Integrable (fun z => χ z * (f z).re) (volume.restrict S) :=
    hf1.norm.mono' (hχc.measurable.mul (Complex.measurable_re.comp hfm)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [norm_mul, Real.norm_of_nonneg (hχ0 z)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hχ1 z)).trans (Complex.abs_re_le_norm _))
  have hJ : ∫ z in S, χ z * ‖f z - 1‖ ^ 2 =
      (∫ z in S, χ z * ‖f z‖ ^ 2) - 2 * (∫ z in S, χ z * (f z).re) + ∫ z in S, χ z := by
    have e1 := integral_add (hi1.sub (hi2.const_mul 2)) hχi
    have e2 := integral_sub hi1 (hi2.const_mul 2)
    have e3 := integral_const_mul (μ := volume.restrict S) (2 : ℝ) (fun z => χ z * (f z).re)
    simp only [Pi.sub_apply, Pi.add_apply] at e1 e2
    rw [integral_congr_ae (Eventually.of_forall hpt), e1, e2, e3]
  have hJi : Integrable (fun z => χ z * ‖f z - 1‖ ^ 2) (volume.restrict S) :=
    ((hi1.sub (hi2.const_mul 2)).add hχi).congr (Eventually.of_forall fun z => (hpt z).symm)
  calc ∫⁻ z in B, ‖f z - 1‖ₑ ^ 2 = ∫⁻ z in B, ENNReal.ofReal (χ z * ‖f z - 1‖ ^ 2) := by
        refine setLIntegral_congr_fun hBm fun z hz => ?_
        rw [χ.one_of_mem_closedBall hz, one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (χ z * ‖f z - 1‖ ^ 2) := lintegral_mono_set hBS
    _ = ENNReal.ofReal (∫ z in S, χ z * ‖f z - 1‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hJi
          (Eventually.of_forall fun z => mul_nonneg (hχ0 z) (sq_nonneg _))).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hJ]
        linarith

/-- The arithmetic closing (W). -/
theorem l42_arith {q τ p r s s0 ε C η : ℝ} (hp : 0 < p) (hr : 0 < r) (hs : 0 < s) (hs1 : s ≤ s0 / 2) (hs2 : s ≤ 1)
    (hs3 : s * (40 * p * (r + 1)) ≤ η) (hτ : τ * (10 * p * (r + s0 + 1) ^ 2) = η) (hτ0 : 0 ≤ τ) (hε0 : 0 ≤ ε)
    (hεs : ε ≤ s) (hεC : ε * (20 * (C + 1)) ≤ η) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq : q ≤ 1 + τ) :
    q * (p * (r + s + ε) ^ 2) - p * r ^ 2 + 2 * ε * C ≤ η := by
  have hA1 : (r + s + ε) ^ 2 ≤ (r + 2 * s) ^ 2 := by nlinarith
  have hA2 : p * (r + 2 * s) ^ 2 - p * r ^ 2 ≤ η / 10 := by
    have e1 : p * (r + 2 * s) ^ 2 - p * r ^ 2 = 4 * p * s * (r + s) := by ring
    have e2 : 4 * p * s * (r + s) ≤ 4 * p * s * (r + 1) := by
      have h1 : r + s ≤ r + 1 := by linarith
      nlinarith [mul_pos hp hs]
    have e3 : s * (40 * p * (r + 1)) = 10 * (4 * p * s * (r + 1)) := by ring
    linarith
  have hA3 : τ * (p * (r + 2 * s) ^ 2) ≤ η / 10 := by
    have h0 : 0 ≤ s0 := by linarith
    have h1 : (r + 2 * s) ^ 2 ≤ (r + s0 + 1) ^ 2 := by nlinarith
    have h2 : τ * (p * (r + 2 * s) ^ 2) ≤ τ * (p * (r + s0 + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hp.le) hτ0
    have e : τ * (10 * p * (r + s0 + 1) ^ 2) = 10 * (τ * (p * (r + s0 + 1) ^ 2)) := by ring
    linarith
  have hA4 : 2 * ε * C ≤ η / 10 := by
    have e : ε * (20 * (C + 1)) = 10 * (2 * ε * C) + 20 * ε := by ring
    linarith
  have hA5 : q * (p * (r + s + ε) ^ 2) ≤ (1 + τ) * (p * (r + 2 * s) ^ 2) :=
    mul_le_mul hq (mul_le_mul_of_nonneg_left hA1 hp.le) (by positivity) (by positivity)
  have e : (1 + τ) * (p * (r + 2 * s) ^ 2) = p * (r + 2 * s) ^ 2 + τ * (p * (r + 2 * s) ^ 2) := by ring
  have hη : 0 ≤ η := le_trans (by positivity) hs3
  linarith

/-- (W) `(w_κ)_z → 1` in `L²` on every closed ball of `𝔻*` as `κ → 0`. -/
theorem l42_wz_ball {c : ℂ} {r : ℝ} (hr : closedBall c r ⊆ unitDiscExterior) :
    Tendsto (fun κ : LinfStar => ∫⁻ z in closedBall c r, ‖dz (wA κ) z - 1‖ₑ ^ 2) (𝓝[LinfStarBall] 0) (𝓝 0) := by
  have hEo : IsOpen unitDiscExterior := wp_exterior_isOpen
  rcases lt_or_ge r 0 with hr0 | hr0
  · rw [closedBall_eq_empty.2 hr0]
    simp only [Measure.restrict_empty, lintegral_zero_measure]
    exact tendsto_const_nhds
  rcases hr0.eq_or_lt with hr0 | hr0
  · subst hr0
    have h0 : volume (closedBall c 0) = 0 := by
      rw [closedBall_zero]
      exact measure_singleton c
    simp only [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    exact tendsto_const_nhds
  obtain ⟨s0, hs0, hs0E⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open hEo hr
  rw [cthickening_closedBall hs0.le hr0.le] at hs0E
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | het
  · exact Eventually.of_forall fun _ => le_top
  have hη : 0 < e.toReal := ENNReal.toReal_pos he.ne' het
  set η := e.toReal with hηd
  have hπ : 0 < π := Real.pi_pos
  set s : ℝ := min (s0 / 2) (min 1 (η / (40 * π * (r + 1)))) with hsd
  have hs : 0 < s := lt_min (half_pos hs0) (lt_min one_pos (div_pos hη (by positivity)))
  have hs1 : s ≤ s0 / 2 := min_le_left _ _
  have hs2 : s ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ η / (40 * π * (r + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  set χ : ContDiffBump c := ⟨r, r + s, hr0, by linarith⟩ with hχd
  have hSE : closedBall c χ.rOut ⊆ unitDiscExterior :=
    (closedBall_subset_closedBall (show r + s ≤ s0 + r by linarith)).trans hs0E
  set Cψ := ∫ z in closedBall c χ.rOut, ‖dz (fun u => ((χ u : ℝ) : ℂ)) z‖ with hCψ
  have hC0 : 0 ≤ Cψ := integral_nonneg fun _ => norm_nonneg _
  set τ := η / (10 * π * (r + s0 + 1) ^ 2) with hτd
  have hτ : 0 < τ := by positivity
  set ε₁ := min s (min (1 / 2) (η / (20 * (Cψ + 1)))) with hε₁d
  have hε₁0 : 0 < ε₁ := lt_min hs (lt_min (by norm_num) (div_pos hη (by positivity)))
  have hε₁s : ε₁ ≤ s := min_le_left _ _
  have hε₁h : ε₁ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁C : ε₁ ≤ η / (20 * (Cψ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨δ2, hδ2, hnear⟩ := gph_near_id_all (R := ‖c‖ + r + s0) hε₁0
  set ρ0 := min δ2 (min (1 / 2) (Real.sqrt (τ / 2))) with hρ0
  have hρ0p : 0 < ρ0 := lt_min hδ2 (lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity)))
  have hev : ∀ᶠ κ in 𝓝[LinfStarBall] (0 : LinfStar), κ ∈ LinfStarBall ∧ ‖κ‖ < ρ0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : LinfStar) hρ0p)]
      with κ h1 h2
    exact ⟨h1, by simpa using h2⟩
  filter_upwards [hev] with κ hκ
  obtain ⟨hκb, hκρ⟩ := hκ
  have hκ1 : ‖κ‖ < δ2 := hκρ.trans_le (min_le_left _ _)
  have hκ2 : ‖κ‖ < 1 / 2 := hκρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hκ3 : ‖κ‖ < Real.sqrt (τ / 2) := hκρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hκsq : ‖κ‖ ^ 2 < τ / 2 := (Real.lt_sqrt (norm_nonneg κ)).1 hκ3
  have hq : 1 / (1 - ‖κ‖ ^ 2) ≤ 1 + τ := by
    have hx : ‖κ‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg κ]
    have hpos : 0 < 1 - ‖κ‖ ^ 2 := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg ‖κ‖, mul_pos hτ hpos]
  have hnear' : ∀ z ∈ closedBall c χ.rOut, ‖wA κ z - z‖ < ε₁ := by
    intro z hz
    have hz1 : ‖z - c‖ ≤ r + s := by
      have h := mem_closedBall.1 hz
      rwa [dist_eq_norm] at h
    have hz' : ‖z‖ ≤ ‖c‖ + r + s0 := by
      have := norm_le_insert' z c
      linarith
    exact (hnear κ hκb hκ1 z hz').2
  have hest := l42_wz_est χ hSE hκb hε₁h hnear'
  refine hest.trans ?_
  rw [← ENNReal.ofReal_toReal het]
  apply ENNReal.ofReal_le_ofReal
  show 1 / (1 - ‖κ‖ ^ 2) * (π * (r + s + ε₁) ^ 2) - π * r ^ 2 + 2 * ε₁ * Cψ ≤ η
  have hpos : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hD : 0 < 10 * π * (r + s0 + 1) ^ 2 := by positivity
  have h40 : 0 < 40 * π * (r + 1) := by positivity
  have h20 : 0 < 20 * (Cψ + 1) := by positivity
  exact l42_arith hπ hr0 hs hs1 hs2 ((le_div_iff₀ h40).1 hs3) (div_mul_cancel₀ η hD.ne') hτ.le hε₁0.le hε₁s
    ((le_div_iff₀ h20).1 hε₁C) hC0 (div_nonneg zero_le_one hpos.le) hq

/-- (W) on a compact subset of `𝔻*` (finite cover by closed balls). -/
theorem l42_wz_cpt {K : Set ℂ} (hK : IsCompact K) (hKE : K ⊆ unitDiscExterior) :
    Tendsto (fun κ : LinfStar => ∫⁻ z in K, ‖dz (wA κ) z - 1‖ₑ ^ 2) (𝓝[LinfStarBall] 0) (𝓝 0) := by
  have hloc : ∀ x ∈ K, ∃ r > 0, closedBall x r ⊆ unitDiscExterior := by
    intro x hx
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 wp_exterior_isOpen x (hKE hx)
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hb⟩
  choose! r hr hsub using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => closedBall x (r x))
    (fun x hx => closedBall_mem_nhds x (hr x hx))
  have hle : ∀ κ : LinfStar, ∫⁻ z in K, ‖dz (wA κ) z - 1‖ₑ ^ 2 ≤
      ∑ i : t, ∫⁻ z in closedBall (i : ℂ) (r i), ‖dz (wA κ) z - 1‖ₑ ^ 2 := by
    intro κ
    have hsub' : K ⊆ ⋃ i : t, closedBall (i : ℂ) (r i) := by
      intro z hz
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcov hz)
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hzx⟩
    calc ∫⁻ z in K, ‖dz (wA κ) z - 1‖ₑ ^ 2 ≤ ∫⁻ z in ⋃ i : t, closedBall (i : ℂ) (r i), ‖dz (wA κ) z - 1‖ₑ ^ 2 :=
          lintegral_mono_set hsub'
      _ ≤ ∑' i : t, ∫⁻ z in closedBall (i : ℂ) (r i), ‖dz (wA κ) z - 1‖ₑ ^ 2 := lintegral_iUnion_le _ _
      _ = ∑ i : t, ∫⁻ z in closedBall (i : ℂ) (r i), ‖dz (wA κ) z - 1‖ₑ ^ 2 := tsum_fintype _
  have hsum : Tendsto (fun κ : LinfStar => ∑ i : t, ∫⁻ z in closedBall (i : ℂ) (r i), ‖dz (wA κ) z - 1‖ₑ ^ 2)
      (𝓝[LinfStarBall] 0) (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ i : t, (0 : ℝ≥0∞) by simp]
    exact tendsto_finset_sum _ fun i _ => l42_wz_ball (hsub i (htK i i.2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) hle

/-- `|a - ā| ≤ 2 |a - 1|`. -/
theorem l42_im_le (a : ℂ) : ‖a - conj a‖ ≤ 2 * ‖a - 1‖ := by
  have h : a - conj a = (a - 1) - conj (a - 1) := by simp [map_sub]
  rw [h]
  calc ‖(a - 1) - conj (a - 1)‖ ≤ ‖a - 1‖ + ‖conj (a - 1)‖ := norm_sub_le _ _
    _ = 2 * ‖a - 1‖ := by rw [Complex.norm_conj]; ring

/-- The pointwise algebra behind (R3): with `P = a/ā`, `c = 1/(1 - k²)`,
`(1 - k²)|a|² |x c P - y|² ≤ 3 (4|x|²|a - 1|² + |x|² σ² |a|² + |x - y|² |a|²)` for `c - 1 ≤ σ`. -/
theorem l42_pt_alg {a x y : ℂ} {k σ : ℝ} (ha : a ≠ 0) (hk0 : 0 ≤ k) (hk1 : k < 1) (hσ : 1 / (1 - k ^ 2) - 1 ≤ σ) :
    (1 - k ^ 2) * ‖a‖ ^ 2 * ‖x / (1 - (k : ℂ) ^ 2) * (a / conj a) - y‖ ^ 2 ≤
      3 * (4 * ‖x‖ ^ 2 * ‖a - 1‖ ^ 2 + ‖x‖ ^ 2 * σ ^ 2 * ‖a‖ ^ 2 + ‖x - y‖ ^ 2 * ‖a‖ ^ 2) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hk3 : 1 - k ^ 2 ≤ 1 := by nlinarith
  have hca : conj a ≠ 0 := by simpa using ha
  have hc : (1 - (k : ℂ) ^ 2) = ((1 - k ^ 2 : ℝ) : ℂ) := by push_cast; ring
  set c : ℝ := 1 / (1 - k ^ 2) with hcd
  have hc1 : 0 ≤ c - 1 := by
    rw [hcd, sub_nonneg, le_div_iff₀ hk2]
    linarith
  have hσ0 : c - 1 ≤ σ := hσ
  set P : ℂ := a / conj a with hPd
  have hP : ‖P‖ = 1 := by rw [hPd, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 ha)]
  have hPa : ‖P - 1‖ * ‖a‖ = ‖a - conj a‖ := by
    have : P - 1 = (a - conj a) / conj a := by rw [hPd]; field_simp
    rw [this, norm_div, Complex.norm_conj, div_mul_cancel₀ _ (norm_ne_zero_iff.2 ha)]
  have hX : x / (1 - (k : ℂ) ^ 2) * P - y = x * (P - 1) + x * P * ((c - 1 : ℝ) : ℂ) + (x - y) := by
    rw [hc, hcd]
    push_cast
    field_simp
    ring
  have hn : ‖x / (1 - (k : ℂ) ^ 2) * P - y‖ ≤ ‖x‖ * ‖P - 1‖ + ‖x‖ * (c - 1) + ‖x - y‖ := by
    rw [hX]
    calc ‖x * (P - 1) + x * P * ((c - 1 : ℝ) : ℂ) + (x - y)‖
        ≤ ‖x * (P - 1)‖ + ‖x * P * ((c - 1 : ℝ) : ℂ)‖ + ‖x - y‖ := norm_add₃_le
      _ = ‖x‖ * ‖P - 1‖ + ‖x‖ * (c - 1) + ‖x - y‖ := by
        rw [norm_mul, norm_mul, norm_mul, hP, mul_one, Complex.norm_real, Real.norm_of_nonneg hc1]
  have hsq : ‖x / (1 - (k : ℂ) ^ 2) * P - y‖ ^ 2 ≤
      3 * ((‖x‖ * ‖P - 1‖) ^ 2 + (‖x‖ * (c - 1)) ^ 2 + ‖x - y‖ ^ 2) := by
    have h0 := norm_nonneg (x / (1 - (k : ℂ) ^ 2) * P - y)
    nlinarith [sq_nonneg (‖x‖ * ‖P - 1‖ - ‖x‖ * (c - 1)), sq_nonneg (‖x‖ * ‖P - 1‖ - ‖x - y‖),
      sq_nonneg (‖x‖ * (c - 1) - ‖x - y‖), mul_nonneg (norm_nonneg x) (norm_nonneg (P - 1)),
      mul_nonneg (norm_nonneg x) hc1, norm_nonneg (x - y)]
  have hIm := l42_im_le a
  have h1 : (‖x‖ * ‖P - 1‖) ^ 2 * ‖a‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 * ‖a - 1‖ ^ 2 := by
    have : (‖x‖ * ‖P - 1‖) ^ 2 * ‖a‖ ^ 2 = ‖x‖ ^ 2 * ‖a - conj a‖ ^ 2 := by rw [← hPa]; ring
    rw [this]
    have h2 : ‖a - conj a‖ ^ 2 ≤ (2 * ‖a - 1‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hIm 2
    nlinarith [sq_nonneg ‖x‖]
  have h2 : (‖x‖ * (c - 1)) ^ 2 ≤ ‖x‖ ^ 2 * σ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc1 hσ0 2) (sq_nonneg _)
  have hA : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  calc (1 - k ^ 2) * ‖a‖ ^ 2 * ‖x / (1 - (k : ℂ) ^ 2) * P - y‖ ^ 2
      ≤ 1 * ‖a‖ ^ 2 * ‖x / (1 - (k : ℂ) ^ 2) * P - y‖ ^ 2 := by gcongr
    _ ≤ ‖a‖ ^ 2 * (3 * ((‖x‖ * ‖P - 1‖) ^ 2 + (‖x‖ * (c - 1)) ^ 2 + ‖x - y‖ ^ 2)) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hsq hA
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 hA]

/-- `‖f‖₂² = ∬_{𝔻*} |f|² ρ d²z`. -/
theorem l42_normL2_sq (f : ℂ → ℂ) :
    normL2 unitDiscExterior f ^ 2 =
      ∫⁻ z in unitDiscExterior, (‖f z‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho z) := by
  unfold normL2
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- (R3) for one `κ`: pull back by `w_κ` and bound pointwise with `l42_pt_alg`. -/
theorem l42_Rcpt_est {η : ℂ → ℂ} (hηm : MemLp η ∞ (volume.restrict unitDiscExterior)) {T Tε : Set ℂ}
    (hTm : MeasurableSet T) (hTεm : MeasurableSet Tε) (hTE : Tε ⊆ unitDiscExterior) (hTT : T ⊆ Tε)
    (hη0 : ∀ z ∉ T, η z = 0) {M ρ1 ω : ℝ} (hM0 : 0 ≤ M) (hρ10 : 0 ≤ ρ1) (hω0 : 0 ≤ ω) (hM : ∀ z, ‖η z‖ ≤ M)
    {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (hρ : ∀ z ∈ Tε, rho (wA κ z) ≤ ρ1)
    (hω : ∀ z ∈ Tε, ‖η z - η (wA κ z)‖ ≤ ω) (hpre : ∀ z ∈ unitDiscExterior, wA κ z ∈ T → z ∈ Tε) :
    normL2 unitDiscExterior (fun u => Rnm (toLinf η) κ u - η u) ^ 2 ≤
      ENNReal.ofReal (12 * ρ1 * M ^ 2) * (∫⁻ z in T, ‖dz (wA κ) z - 1‖ₑ ^ 2) +
      ENNReal.ofReal (3 * ρ1 * M ^ 2 * (1 / (1 - ‖κ‖ ^ 2) - 1) ^ 2) * (∫⁻ z in T, ‖dz (wA κ) z‖ₑ ^ 2) +
      ENNReal.ofReal (3 * ρ1 * ω ^ 2) * ∫⁻ z in Tε, ‖dz (wA κ) z‖ₑ ^ 2 := by
  have hE : MeasurableSet unitDiscExterior := wp_exterior_isOpen.measurableSet
  have hk := WPCV.wpcv_norm_lt_one hκ
  have hk2 : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  set σ := 1 / (1 - ‖κ‖ ^ 2) - 1 with hσd
  have hind : ∀ (S : Set ℂ) (g : ℂ → ℝ≥0∞), MeasurableSet S → S ⊆ unitDiscExterior →
      ∫⁻ z in S, g z = ∫⁻ z in unitDiscExterior, S.indicator g z := fun S g hS hSE => by
    rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.2 hSE]
  have hAm : Measurable fun z => ‖dz (wA κ) z - 1‖ₑ ^ 2 := ((measurable_dz _).sub_const 1).enorm.pow_const 2
  have hBm : Measurable fun z => ‖dz (wA κ) z‖ₑ ^ 2 := (measurable_dz _).enorm.pow_const 2
  rw [hind T _ hTm (hTT.trans hTE), hind T _ hTm (hTT.trans hTE), hind Tε _ hTεm hTE, l42_normL2_sq,
    WPCV.wpcv_lcov hκ (fun u => (‖Rnm (toLinf η) κ u - η u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho u))]
  refine (lintegral_mono_ae (g := fun z => ENNReal.ofReal (12 * ρ1 * M ^ 2) *
      T.indicator (fun z => ‖dz (wA κ) z - 1‖ₑ ^ 2) z + ENNReal.ofReal (3 * ρ1 * M ^ 2 * σ ^ 2) *
      T.indicator (fun z => ‖dz (wA κ) z‖ₑ ^ 2) z + ENNReal.ofReal (3 * ρ1 * ω ^ 2) *
      Tε.indicator (fun z => ‖dz (wA κ) z‖ₑ ^ 2) z) ?_).trans (le_of_eq ?_)
  swap
  · have hm2 : Measurable fun z => ENNReal.ofReal (12 * ρ1 * M ^ 2) *
        T.indicator (fun z => ‖dz (wA κ) z - 1‖ₑ ^ 2) z + ENNReal.ofReal (3 * ρ1 * M ^ 2 * σ ^ 2) *
        T.indicator (fun z => ‖dz (wA κ) z‖ₑ ^ 2) z :=
      ((hAm.indicator hTm).const_mul _).add ((hBm.indicator hTm).const_mul _)
    have hm1 : Measurable fun z => ENNReal.ofReal (12 * ρ1 * M ^ 2) *
        T.indicator (fun z => ‖dz (wA κ) z - 1‖ₑ ^ 2) z :=
      (hAm.indicator hTm).const_mul _
    rw [lintegral_add_left hm2, lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hR1 := bc_pullback_ae hκ (WPCV.wpcv_RnmFun_ae hκ (toLinf η))
  have hηae := bc_toLinf_ae hηm
  filter_upwards [WPCV.wpcv_ae_facts hκ, hR1, hηae, ae_restrict_mem hE] with z hz hRz hηz hzE
  obtain ⟨hw1, hj, hkz, hdz⟩ := hz
  have hwn : wA κ z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw1
    linarith
  have hR : Rnm (toLinf η) κ (wA κ z) =
      η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (dz (wA κ) z / conj (dz (wA κ) z)) := by
    rw [hRz]
    show (fun u => (toLinf η) u / (1 - ‖κ u‖ ^ 2) * (dz (wA κ) u / conj (dz (wA κ) u)))
      (Function.invFun (wA κ) (wA κ z)) = _
    rw [bc_invFun_wA hwn]
    simp only [hηz]
  have e1 : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
  have e2 : ∀ x : ℂ, ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hkz1 : ‖κ z‖ < 1 := lt_of_le_of_lt hkz hk
  have hkk : 0 < 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
  have hJ : 0 ≤ jacobian (wA κ) z := by rw [hj]; exact mul_nonneg hkk.le (sq_nonneg _)
  show ENNReal.ofReal (jacobian (wA κ) z) *
      ((‖Rnm (toLinf η) κ (wA κ z) - η (wA κ z)‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho (wA κ z))) ≤ _
  by_cases hzε : z ∈ Tε
  · have hρz := hρ z hzε
    have hωz := hω z hzε
    have hσk : 1 / (1 - ‖κ z‖ ^ 2) - 1 ≤ σ := by
      rw [hσd]
      have : 1 - ‖κ‖ ^ 2 ≤ 1 - ‖κ z‖ ^ 2 := by nlinarith [norm_nonneg (κ z)]
      have := one_div_le_one_div_of_le hk2 this
      linarith
    have hpt := l42_pt_alg (x := η z) (y := η (wA κ z)) hdz (norm_nonneg _) hkz1 hσk
    have hρw : 0 ≤ rho (wA κ z) := l42_rho_nonneg _
    set a := dz (wA κ) z with had
    set X := Rnm (toLinf η) κ (wA κ z) - η (wA κ z) with hXd
    have hXe : X = η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (a / conj a) - η (wA κ z) := by rw [hXd, hR]
    have hreal : jacobian (wA κ) z * (‖X‖ ^ 2 * rho (wA κ z)) ≤
        ρ1 * (3 * (4 * ‖η z‖ ^ 2 * ‖a - 1‖ ^ 2 + ‖η z‖ ^ 2 * σ ^ 2 * ‖a‖ ^ 2 + ω ^ 2 * ‖a‖ ^ 2)) := by
      rw [hj, hXe]
      have hω2 : ‖η z - η (wA κ z)‖ ^ 2 * ‖a‖ ^ 2 ≤ ω ^ 2 * ‖a‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hωz 2) (sq_nonneg _)
      have hP0 : 0 ≤ (1 - ‖κ z‖ ^ 2) * ‖a‖ ^ 2 *
          ‖η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (a / conj a) - η (wA κ z)‖ ^ 2 := by positivity
      calc (1 - ‖κ z‖ ^ 2) * ‖a‖ ^ 2 * (‖η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (a / conj a) - η (wA κ z)‖ ^ 2 *
            rho (wA κ z))
          = rho (wA κ z) * ((1 - ‖κ z‖ ^ 2) * ‖a‖ ^ 2 *
              ‖η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (a / conj a) - η (wA κ z)‖ ^ 2) := by ring
        _ ≤ ρ1 * ((1 - ‖κ z‖ ^ 2) * ‖a‖ ^ 2 *
              ‖η z / (1 - (‖κ z‖ : ℂ) ^ 2) * (a / conj a) - η (wA κ z)‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hρz hP0
        _ ≤ ρ1 * (3 * (4 * ‖η z‖ ^ 2 * ‖a - 1‖ ^ 2 + ‖η z‖ ^ 2 * σ ^ 2 * ‖a‖ ^ 2 +
              ‖η z - η (wA κ z)‖ ^ 2 * ‖a‖ ^ 2)) := mul_le_mul_of_nonneg_left hpt hρ10
        _ ≤ _ := by nlinarith
    rw [e1, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hJ]
    by_cases hzT : z ∈ T
    · rw [indicator_of_mem hzT, indicator_of_mem hzT, indicator_of_mem hzε, e2, e2,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : ‖η z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM z) 2
      refine hreal.trans ?_
      nlinarith [mul_le_mul_of_nonneg_right hx (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (mul_nonneg hρ10
        (sq_nonneg ‖a - 1‖))), mul_le_mul_of_nonneg_right hx (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        hρ10) (mul_nonneg (sq_nonneg σ) (sq_nonneg ‖a‖)))]
    · have hx0 : η z = 0 := hη0 z hzT
      rw [indicator_of_notMem hzT, indicator_of_notMem hzT, indicator_of_mem hzε, e2, mul_zero, mul_zero,
        zero_add, zero_add, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine hreal.trans ?_
      rw [hx0, norm_zero]
      nlinarith
  · have hzT : z ∉ T := fun h => hzε (hTT h)
    have hx0 : η z = 0 := hη0 z hzT
    have hy0 : η (wA κ z) = 0 := hη0 _ fun h => hzε (hpre z hzE h)
    rw [hR, hx0, hy0]
    simp

/-- `ρ` is continuous on `𝔻*`. -/
theorem l42_rho_contOn : ContinuousOn rho unitDiscExterior := by
  unfold rho
  refine continuousOn_const.div (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
  have h : 1 < ‖z‖ := hz
  have : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith
  exact pow_ne_zero 2 this

/-- A finite point of `ℂ̄` is the coercion of its finite part. -/
theorem l42_coe_finPart {p : ExtPlane} (hp : p ≠ extInf) : ((finPart p : ℂ) : ExtPlane) = p := by
  obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hp
  rw [← hy]
  rfl

/-- If `w_κ(z) = u` is finite, then `w_{κ⁻¹}(u) = z`. -/
theorem l42_inv_apply {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {z : ℂ} (hz : wA κ z ≠ 0) :
    wA (beltramiInv κ) (wA κ z) = z := by
  have h1 : wAS κ (z : ExtPlane) = ((wA κ z : ℂ) : ExtPlane) := (l42_coe_finPart (l42_wAS_ne hz)).symm
  have h2 := congrFun (grp_wAS_inv_right hκ) (z : ExtPlane)
  simp only [Function.comp_apply, id_eq] at h2
  rw [h1] at h2
  show finPart (wAS (beltramiInv κ) ((wA κ z : ℂ) : ExtPlane)) = z
  rw [h2]
  rfl

/-- (R3) for one `κ`, in terms of the nested thickenings `T ⊆ K₁ ⊆ K₂` of the support. -/
theorem l42_Rcpt_fix {η : ℂ → ℂ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ unitDiscExterior) {δ0 δ1 ε R ρ1 M ω : ℝ}
    (hK1E : cthickening δ0 (tsupport η) ⊆ unitDiscExterior)
    (hK2E : cthickening δ1 (cthickening δ0 (tsupport η)) ⊆ unitDiscExterior) (hεδ0 : ε ≤ δ0)
    (hεδ1 : ε ≤ δ1) (hR : cthickening δ1 (cthickening δ0 (tsupport η)) ⊆ closedBall 0 R)
    (hρ1 : ∀ x ∈ cthickening δ1 (cthickening δ0 (tsupport η)), rho x ≤ ρ1) (hρ10 : 0 ≤ ρ1) (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖η z‖ ≤ M) (hω0 : 0 ≤ ω) (hunif : ∀ x y, ‖x - y‖ < ε → ‖η x - η y‖ ≤ ω) {κ : LinfStar}
    (hκ : κ ∈ LinfStarBall) (hκ2 : ‖κ‖ < 1 / 2) (hnκ : ∀ z, ‖z‖ ≤ R → ‖wA κ z - z‖ < ε)
    (hnv : ∀ u, ‖u‖ ≤ R → ‖wA (beltramiInv κ) u - u‖ < ε) :
    normL2 unitDiscExterior (fun u => Rnm (toLinf η) κ u - η u) ^ 2 ≤
      ENNReal.ofReal (12 * ρ1 * M ^ 2) * (∫⁻ z in tsupport η, ‖dz (wA κ) z - 1‖ₑ ^ 2) +
      ENNReal.ofReal (3 * ρ1 * M ^ 2 * (1 / (1 - ‖κ‖ ^ 2) - 1) ^ 2) *
        ENNReal.ofReal (2 * (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal) +
      ENNReal.ofReal (3 * ρ1 * ω ^ 2) *
        ENNReal.ofReal (2 * (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal) := by
  have hTm : MeasurableSet (tsupport η) := (isClosed_tsupport η).measurableSet
  have hK2c : IsCompact (cthickening δ1 (cthickening δ0 (tsupport η))) := (hc.isCompact.cthickening).cthickening
  have hK2m : MeasurableSet (cthickening δ1 (cthickening δ0 (tsupport η))) := isClosed_cthickening.measurableSet
  have hη0 : ∀ z ∉ tsupport η, η z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hηm : MemLp η ∞ (volume.restrict unitDiscExterior) := (hη.memLp_of_hasCompactSupport hc).restrict _
  have hV0 : 0 ≤ (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal := ENNReal.toReal_nonneg
  have hVe : volume (cthickening δ1 (cthickening δ0 (tsupport η))) =
      ENNReal.ofReal (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal :=
    (ENNReal.ofReal_toReal hK2c.measure_lt_top.ne).symm
  have hTεK1 : cthickening ε (tsupport η) ⊆ cthickening δ0 (tsupport η) := cthickening_mono hεδ0 _
  have hnK1 : ∀ z ∈ cthickening δ0 (tsupport η), ‖wA κ z - z‖ < ε := fun z hz =>
    hnκ z (by simpa using hR (self_subset_cthickening _ hz))
  have hwK2 : ∀ z ∈ cthickening δ0 (tsupport η), wA κ z ∈ cthickening δ1 (cthickening δ0 (tsupport η)) :=
    fun z hz => mem_cthickening_of_dist_le _ z δ1 _ hz (by rw [dist_eq_norm]; exact (hnK1 z hz).le.trans hεδ1)
  have hρ : ∀ z ∈ cthickening ε (tsupport η), rho (wA κ z) ≤ ρ1 := fun z hz => hρ1 _ (hwK2 z (hTεK1 hz))
  have hωz : ∀ z ∈ cthickening ε (tsupport η), ‖η z - η (wA κ z)‖ ≤ ω := fun z hz =>
    hunif z (wA κ z) (by rw [norm_sub_rev]; exact hnK1 z (hTεK1 hz))
  have hpre : ∀ z ∈ unitDiscExterior, wA κ z ∈ tsupport η → z ∈ cthickening ε (tsupport η) := by
    intro z _ hzT
    have hwz : wA κ z ≠ 0 := by
      intro h0
      have h1 : 1 < ‖wA κ z‖ := hs hzT
      rw [h0, norm_zero] at h1
      linarith
    have hu : ‖wA κ z‖ ≤ R := by
      simpa using hR (self_subset_cthickening _ (self_subset_cthickening _ hzT))
    have h := hnv (wA κ z) hu
    rw [l42_inv_apply hκ hwz] at h
    exact mem_cthickening_of_dist_le z (wA κ z) ε _ hzT (by rw [dist_eq_norm]; exact h.le)
  have hq : 1 / (1 - ‖κ‖ ^ 2) ≤ 2 := by
    have hpos : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg κ]
  have hEn : ∀ S ⊆ cthickening δ0 (tsupport η), MeasurableSet S → ∫⁻ z in S, ‖dz (wA κ) z‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal) := by
    intro S hS hSm
    refine (l42_energy hκ hSm (hS.trans hK1E) hK2m fun z hz => hwK2 z (hS hz)).trans ?_
    nth_rewrite 1 [hVe]
    rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (by nlinarith [norm_nonneg κ]))]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hq hV0)
  have hET := hEn (tsupport η) (self_subset_cthickening _) hTm
  have hEε := hEn _ hTεK1 isClosed_cthickening.measurableSet
  refine (l42_Rcpt_est hηm hTm isClosed_cthickening.measurableSet (hTεK1.trans hK1E)
    (self_subset_cthickening _) hη0 hM0 hρ10 hω0 hM hκ hρ hωz hpre).trans ?_
  gcongr

/-- The arithmetic closing (R3). -/
theorem l42_arith3 {c1 a1 ρ1 M σ s0 ω V t : ℝ} (hρ10 : 0 ≤ ρ1) (hV0 : 0 ≤ V) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ s0)
    (hs01 : s0 ≤ 1) (hs0 : s0 * (18 * (ρ1 + 1) * (M ^ 2 + 1) * (V + 1)) ≤ t ^ 2) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hω2 : ω * (18 * (ρ1 + 1) * (V + 1)) ≤ t ^ 2) (h1 : c1 * a1 ≤ t ^ 2 / 3) :
    c1 * a1 + 3 * ρ1 * M ^ 2 * σ ^ 2 * (2 * V) + 3 * ρ1 * ω ^ 2 * (2 * V) ≤ t ^ 2 := by
  have hσs : σ ^ 2 ≤ s0 := by nlinarith
  have hωω : ω ^ 2 ≤ ω := by nlinarith
  have hA : ρ1 * M ^ 2 * V ≤ (ρ1 + 1) * (M ^ 2 + 1) * (V + 1) := by
    have e1 : 0 ≤ ρ1 * M ^ 2 := mul_nonneg hρ10 (sq_nonneg M)
    nlinarith [mul_nonneg e1 hV0, mul_nonneg hρ10 hV0, sq_nonneg M, mul_nonneg (sq_nonneg M) hV0]
  have hB : ρ1 * V ≤ (ρ1 + 1) * (V + 1) := by nlinarith
  have h2 : 3 * ρ1 * M ^ 2 * σ ^ 2 * (2 * V) ≤ t ^ 2 / 3 := by
    have e : 3 * ρ1 * M ^ 2 * σ ^ 2 * (2 * V) = 6 * (σ ^ 2 * (ρ1 * M ^ 2 * V)) := by ring
    have f1 : σ ^ 2 * (ρ1 * M ^ 2 * V) ≤ s0 * ((ρ1 + 1) * (M ^ 2 + 1) * (V + 1)) :=
      mul_le_mul hσs hA (by positivity) (by linarith [hσ0.trans hσ1])
    nlinarith
  have h3 : 3 * ρ1 * ω ^ 2 * (2 * V) ≤ t ^ 2 / 3 := by
    have e : 3 * ρ1 * ω ^ 2 * (2 * V) = 6 * (ω ^ 2 * (ρ1 * V)) := by ring
    have f1 : ω ^ 2 * (ρ1 * V) ≤ ω * ((ρ1 + 1) * (V + 1)) :=
      mul_le_mul hωω hB (by positivity) hω0
    nlinarith
  linarith

/-- (R3), the choice of parameters: eventually `‖R(η, κ) - η‖₂ ≤ e`. -/
theorem l42_Rcpt_ev {η : ℂ → ℂ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ unitDiscExterior) {δ0 δ1 ρ1 M R : ℝ} (hδ0 : 0 < δ0) (hδ1 : 0 < δ1)
    (hK1E : cthickening δ0 (tsupport η) ⊆ unitDiscExterior)
    (hK2E : cthickening δ1 (cthickening δ0 (tsupport η)) ⊆ unitDiscExterior)
    (hρ1 : ∀ x ∈ cthickening δ1 (cthickening δ0 (tsupport η)), rho x ≤ ρ1) (hρ10 : 0 ≤ ρ1) (hM0 : 0 ≤ M)
    (hM : ∀ z, ‖η z‖ ≤ M) (hR : cthickening δ1 (cthickening δ0 (tsupport η)) ⊆ closedBall 0 R)
    {e : ℝ≥0∞} (ht : 0 < e.toReal) (het : e ≠ ⊤) :
    ∀ᶠ κ in 𝓝[LinfStarBall] (0 : LinfStar), normL2 unitDiscExterior (fun u => Rnm (toLinf η) κ u - η u) ≤ e := by
  have hTc : IsCompact (tsupport η) := hc
  set V := (volume (cthickening δ1 (cthickening δ0 (tsupport η)))).toReal with hVd
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set t := e.toReal with htd
  set c1 := 12 * ρ1 * M ^ 2 with hc1d
  have hc10 : 0 ≤ c1 := by positivity
  set a1 := t ^ 2 / (3 * (c1 + 1)) with ha1d
  have ha1 : 0 < a1 := by positivity
  have h1 : c1 * a1 ≤ t ^ 2 / 3 := by
    rw [ha1d, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg t]
  set ω := min 1 (t ^ 2 / (18 * (ρ1 + 1) * (V + 1))) with hωd
  have hω0 : 0 < ω := lt_min one_pos (by positivity)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hω2 : ω * (18 * (ρ1 + 1) * (V + 1)) ≤ t ^ 2 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  obtain ⟨δω, hδω, hunif⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hη) ω hω0
  set ε := min (min δ0 δ1) (δω / 2) with hεd
  have hε0 : 0 < ε := lt_min (lt_min hδ0 hδ1) (half_pos hδω)
  have hεδ0 : ε ≤ δ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hεδ1 : ε ≤ δ1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεω : ε < δω := (min_le_right _ _).trans_lt (half_lt_self hδω)
  have hunif' : ∀ x y, ‖x - y‖ < ε → ‖η x - η y‖ ≤ ω := fun x y hxy => by
    have h := hunif (a := x) (b := y) (by rw [dist_eq_norm]; exact hxy.trans hεω)
    rw [dist_eq_norm] at h
    exact h.le
  set s0 := min 1 (t ^ 2 / (18 * (ρ1 + 1) * (M ^ 2 + 1) * (V + 1))) with hs0d
  have hs00 : 0 < s0 := lt_min one_pos (by positivity)
  have hs01 : s0 ≤ 1 := min_le_left _ _
  have hs0 : s0 * (18 * (ρ1 + 1) * (M ^ 2 + 1) * (V + 1)) ≤ t ^ 2 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  obtain ⟨δκ, hδκ, hnear⟩ := gph_near_id_all (R := R) hε0
  set ρ0 := min δκ (min (1 / 2) (Real.sqrt (s0 / 2))) with hρ0d
  have hρ0 : 0 < ρ0 := lt_min hδκ (lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity)))
  have hIT := (ENNReal.tendsto_nhds_zero.1 (l42_wz_cpt hTc ((self_subset_cthickening _).trans hK1E)))
    (ENNReal.ofReal a1) (ENNReal.ofReal_pos.2 ha1)
  have hev : ∀ᶠ κ in 𝓝[LinfStarBall] (0 : LinfStar), κ ∈ LinfStarBall ∧ ‖κ‖ < ρ0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : LinfStar) hρ0)]
      with κ h1 h2
    exact ⟨h1, by simpa using h2⟩
  filter_upwards [hev, hIT] with κ hκ hIκ
  obtain ⟨hκb, hκρ⟩ := hκ
  have hκ1 : ‖κ‖ < δκ := hκρ.trans_le (min_le_left _ _)
  have hκ2 : ‖κ‖ < 1 / 2 := hκρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hκ3 : ‖κ‖ ^ 2 < s0 / 2 :=
    (Real.lt_sqrt (norm_nonneg κ)).1 (hκρ.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hvb : beltramiInv κ ∈ LinfStarBall := bc_beltramiInv_mem_ball hκb
  have hv1 : ‖beltramiInv κ‖ < δκ := (bc_beltramiInv_norm_le hκb).trans_lt hκ1
  have hfix := l42_Rcpt_fix hη hc hs hK1E hK2E hεδ0 hεδ1 hR hρ1 hρ10 hM0 hM hω0.le hunif' hκb hκ2
    (fun z hz => (hnear κ hκb hκ1 z (by simpa using hz)).2)
    (fun u hu => (hnear (beltramiInv κ) hvb hv1 u (by simpa using hu)).2)
  set σ := 1 / (1 - ‖κ‖ ^ 2) - 1 with hσd
  have hpos : 0 < 1 - ‖κ‖ ^ 2 := by nlinarith [norm_nonneg κ]
  have hσ0 : 0 ≤ σ := by
    rw [hσd, sub_nonneg, le_div_iff₀ hpos]
    nlinarith [norm_nonneg κ]
  have hσ1 : σ ≤ s0 := by
    rw [hσd, sub_le_iff_le_add, div_le_iff₀ hpos]
    nlinarith [norm_nonneg κ]
  have hfin : normL2 unitDiscExterior (fun u => Rnm (toLinf η) κ u - η u) ^ 2 ≤ ENNReal.ofReal (t ^ 2) := by
    refine hfix.trans ?_
    calc ENNReal.ofReal c1 * (∫⁻ z in tsupport η, ‖dz (wA κ) z - 1‖ₑ ^ 2) +
          ENNReal.ofReal (3 * ρ1 * M ^ 2 * σ ^ 2) * ENNReal.ofReal (2 * V) +
          ENNReal.ofReal (3 * ρ1 * ω ^ 2) * ENNReal.ofReal (2 * V)
        ≤ ENNReal.ofReal c1 * ENNReal.ofReal a1 + ENNReal.ofReal (3 * ρ1 * M ^ 2 * σ ^ 2) *
          ENNReal.ofReal (2 * V) + ENNReal.ofReal (3 * ρ1 * ω ^ 2) * ENNReal.ofReal (2 * V) := by gcongr
      _ = ENNReal.ofReal (c1 * a1 + 3 * ρ1 * M ^ 2 * σ ^ 2 * (2 * V) + 3 * ρ1 * ω ^ 2 * (2 * V)) := by
          rw [← ENNReal.ofReal_mul hc10, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (t ^ 2) :=
          ENNReal.ofReal_le_ofReal (l42_arith3 hρ10 hV0 hσ0 hσ1 hs01 hs0 hω0.le hω1 hω2 h1)
  rw [← ENNReal.ofReal_toReal het]
  rw [ENNReal.ofReal_pow ht.le] at hfin
  have h2 := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  exact h2

/-- (R3) `R(η, κ) → η` in `L²(𝔻*, ρ)` as `κ → 0`, for continuous `η` with compact support in `𝔻*`. -/
theorem l42_R_cpt {η : ℂ → ℂ} (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ unitDiscExterior) :
    Tendsto (fun κ : LinfStar => normL2 unitDiscExterior (fun z => Rnm (toLinf η) κ z - η z))
      (𝓝[LinfStarBall] 0) (𝓝 0) := by
  have hEo : IsOpen unitDiscExterior := wp_exterior_isOpen
  have hTc : IsCompact (tsupport η) := hc
  obtain ⟨δ0, hδ0, hK1E⟩ := hTc.exists_cthickening_subset_open hEo hs
  have hK1c : IsCompact (cthickening δ0 (tsupport η)) := hTc.cthickening
  obtain ⟨δ1, hδ1, hK2E⟩ := hK1c.exists_cthickening_subset_open hEo hK1E
  have hK2c : IsCompact (cthickening δ1 (cthickening δ0 (tsupport η))) := hK1c.cthickening
  obtain ⟨ρ1', hρ1'⟩ := hK2c.exists_bound_of_continuousOn (l42_rho_contOn.mono hK2E)
  have hρ10 : 0 ≤ max ρ1' 0 := le_max_right _ _
  have hρ1 : ∀ x ∈ cthickening δ1 (cthickening δ0 (tsupport η)), rho x ≤ max ρ1' 0 := fun x hx =>
    (le_abs_self _).trans ((hρ1' x hx).trans (le_max_left _ _))
  obtain ⟨M', hM'⟩ := hη.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ max M' 0 := le_max_right _ _
  have hM : ∀ z, ‖η z‖ ≤ max M' 0 := fun z => (hM' z).trans (le_max_left _ _)
  obtain ⟨R, hR⟩ := hK2c.isBounded.subset_closedBall 0
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | het
  · exact Eventually.of_forall fun _ => le_top
  exact l42_Rcpt_ev hη hc hs hδ0 hδ1 hK1E hK2E hρ1 hρ10 hM0 hM hR (ENNReal.toReal_pos he.ne' het) het

/-- `R(a - b, κ) = R(a, κ) - R(b, κ)`. -/
theorem l42_Rnm_sub {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (a b : LinfStar) : Rnm (a - b) κ = Rnm a κ - Rnm b κ := by
  obtain ⟨L, hL⟩ := bc_exists_RnmCLM hκ
  rw [← hL, ← hL, ← hL, map_sub]

/-- `‖f + g‖₂ ≤ ‖f‖₂ + ‖g‖₂`. -/
theorem l42_normL2_add_le {f g : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior)) :
    normL2 unitDiscExterior (fun z => f z + g z) ≤ normL2 unitDiscExterior f + normL2 unitDiscExterior g := by
  have h := grp_normL2_sub_le hf hg.neg
  have e1 : (fun z => f z - (-g) z) = fun z => f z + g z := by
    funext z
    simp [sub_eq_add_neg]
  have e2 : normL2 unitDiscExterior (-g) = normL2 unitDiscExterior g := by
    unfold normL2
    simp only [Pi.neg_apply, nnnorm_neg]
  rw [e1, e2] at h
  exact h

/-- `‖f + g - h‖₂ ≤ ‖f‖₂ + ‖g‖₂ + ‖h‖₂`. -/
theorem l42_normL2_three {f g h : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict unitDiscExterior))
    (hg : AEStronglyMeasurable g (volume.restrict unitDiscExterior))
    (hh : AEStronglyMeasurable h (volume.restrict unitDiscExterior)) :
    normL2 unitDiscExterior (fun z => f z + g z - h z) ≤
      normL2 unitDiscExterior f + normL2 unitDiscExterior g + normL2 unitDiscExterior h :=
  (grp_normL2_sub_le (hf.add hg) hh).trans (add_le_add (l42_normL2_add_le hf hg) le_rfl)

/-- (R4) `R(μ, κ) → μ` in `L²(𝔻*, ρ)` as `κ → 0` in `Ω^{-1,1}(𝔻*)`, for `μ ∈ H^{-1,1}(𝔻*)`. -/
theorem l42_R_tendsto {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    Tendsto (fun κ : LinfStar => normL2 unitDiscExterior (fun z => Rnm (toLinf μ) κ z - μ z))
      (𝓝[(harmonicBeltrami : Set LinfStar)] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, C, hC⟩ := l42_R_bound
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | het
  · exact Eventually.of_forall fun _ => le_top
  have ht : 0 < e.toReal := ENNReal.toReal_pos he.ne' het
  set t := e.toReal with htd
  set C' := max C 0 with hC'd
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set a := t / (4 * (C' + 1)) with had
  have ha : 0 < a := div_pos ht (by positivity)
  obtain ⟨η, hηc, hηs, hηt, hηa⟩ := l42_cutoff hμ ha
  have hηm : MemLp η ∞ (volume.restrict unitDiscExterior) := (hηc.memLp_of_hasCompactSupport hηs).restrict _
  have hηae : (toLinf η : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] η := bc_toLinf_ae hηm
  have hμae := wp_harmonic_toLinf_ae hμ
  have hηaesm : AEStronglyMeasurable η (volume.restrict unitDiscExterior) := hηc.aestronglyMeasurable
  have hR3 := (ENNReal.tendsto_nhds_zero.1 (l42_R_cpt hηc hηs hηt)) (ENNReal.ofReal (t / 2))
    (ENNReal.ofReal_pos.2 (half_pos ht))
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hR3
  have hev : ∀ᶠ κ in 𝓝[(harmonicBeltrami : Set LinfStar)] (0 : LinfStar),
      κ ∈ harmonicBeltrami ∧ κ ∈ U ∧ ‖κ‖ < min δ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Filter.inter_mem hU (Metric.ball_mem_nhds (0 : LinfStar) (lt_min hδ one_pos)))]
      with κ h1 h2
    exact ⟨h1, h2.1, by simpa using h2.2⟩
  filter_upwards [hev] with κ hκ
  obtain ⟨hκh, hκU, hκm⟩ := hκ
  have hκδ : ‖κ‖ < δ := hκm.trans_le (min_le_left _ _)
  have hκb : κ ∈ LinfStarBall := mem_ball_zero_iff.2 (hκm.trans_le (min_le_right _ _))
  have hE := hUsub ⟨hκU, hκb⟩
  -- the three pieces
  set D : LinfStar := Rnm (toLinf μ - toLinf η) κ with hDd
  have hDae : (D : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] fun z => Rnm (toLinf μ) κ z - Rnm (toLinf η) κ z := by
    rw [hDd, l42_Rnm_sub hκb]
    exact Lp.coeFn_sub _ _
  have hdiff : normL2 unitDiscExterior ⇑(toLinf μ - toLinf η) = normL2 unitDiscExterior (fun z => μ z - η z) := by
    apply grp_normL2_congr_ae
    filter_upwards [Lp.coeFn_sub (toLinf μ) (toLinf η), hμae, hηae] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hD : normL2 unitDiscExterior D ≤ ENNReal.ofReal (C' * a) := by
    refine (hC κ hκh hκδ _).trans ?_
    rw [hdiff, ENNReal.ofReal_mul hC'0]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hηa.le zero_le zero_le
  have hsplit : normL2 unitDiscExterior (fun z => Rnm (toLinf μ) κ z - μ z) =
      normL2 unitDiscExterior (fun z => D z + (Rnm (toLinf η) κ z - η z) - (μ z - η z)) := by
    apply grp_normL2_congr_ae
    filter_upwards [hDae] with z hz
    rw [hz]
    ring
  rw [hsplit]
  refine (l42_normL2_three (Lp.aestronglyMeasurable D)
    ((Lp.aestronglyMeasurable _).sub hηaesm) ((l42_aesm hμ).sub hηaesm)).trans ?_
  calc normL2 unitDiscExterior D + normL2 unitDiscExterior (fun z => Rnm (toLinf η) κ z - η z) +
        normL2 unitDiscExterior (fun z => μ z - η z)
      ≤ ENNReal.ofReal (C' * a) + ENNReal.ofReal (t / 2) + ENNReal.ofReal a := add_le_add (add_le_add hD hE) hηa.le
    _ = ENNReal.ofReal (C' * a + t / 2 + a) := by
        rw [ENNReal.ofReal_add (by positivity) ha.le, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ e := by
        rw [← ENNReal.ofReal_toReal het]
        apply ENNReal.ofReal_le_ofReal
        have h4 : (C' + 1) * a = t / 4 := by rw [had]; field_simp
        nlinarith

/-- **Lemma 4.2** (TT:2170–2186). The Weil–Petersson metric is continuous on `T(1)`.
- By right-invariance (Corollary 2.12) it suffices that, for every `μ ∈ H^{-1,1}(𝔻*)`, `g_{μμ̄}` is continuous at the
  origin.
- The proof shows this already for the (weaker) Banach topology of `A∞(𝔻)` on a neighbourhood of `0` in `U₀`; this
  is stated here. -/
theorem l42_lemma_4_2 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : ContinuousAt (gWPChart μ μ) 0 := by
  have hΛ : Tendsto Lambda (𝓝 0) (𝓝[(harmonicBeltrami : Set LinfStar)] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall Lambda_mem_harmonic⟩
    have hc : Continuous Lambda := by
      have : Lambda = fun φ => ((LambdaEquiv φ : harmonicBeltrami) : LinfStar) := rfl
      rw [this]
      exact continuous_subtype_val.comp LambdaEquiv.continuous
    simpa only [wp_Lambda_zero] using hc.tendsto (0 : AInf unitDisc)
  have hball : ∀ᶠ φ in 𝓝 (0 : AInf unitDisc), Lambda φ ∈ LinfStarBall := by
    have h := (tendsto_nhdsWithin_iff.1 hΛ).1
    exact h (isOpen_ball.mem_nhds (by simp))
  have hd := (l42_R_tendsto hμ).comp hΛ
  have hd' : Tendsto (fun φ => (normL2 unitDiscExterior
      (fun z => Rnm (toLinf μ) (Lambda φ) z - μ z)).toReal) (𝓝 0) (𝓝 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hd
  have hb : Tendsto (fun φ => (normL2 unitDiscExterior (fun z => Rnm (toLinf μ) (Lambda φ) z - μ z)).toReal *
      ((normL2 unitDiscExterior (fun z => Rnm (toLinf μ) (Lambda φ) z - μ z)).toReal +
        2 * (normL2 unitDiscExterior μ).toReal)) (𝓝 0) (𝓝 0) := by
    simpa using hd'.mul (hd'.add tendsto_const_nhds)
  rw [ContinuousAt, gWP_origin hμ hμ, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hball] with φ hφ
  exact l42_gWP_near hμ hφ

/-- **Lemma 4.2** (TT:2170–2186). The Weil–Petersson metric is continuous on `T(1)`.
- By right-invariance (Corollary 2.12) it suffices that, for every `μ ∈ H^{-1,1}(𝔻*)`, `g_{μμ̄}` is continuous at the
  origin.
- The proof shows this already for the (weaker) Banach topology of `A∞(𝔻)` on a neighbourhood of `0` in `U₀`; this
  is stated here. -/
theorem lemma_4_2 {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) : ContinuousAt (gWPChart μ μ) 0 :=
  l42_lemma_4_2 hμ

end TakhtajanTeo
