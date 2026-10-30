import TakhtajanTeo.Ch1.S7FirstVariation
import TakhtajanTeo.Ch1.S7SecondVarGeneric
import TakhtajanTeo.Ch1.S7PolarizationCompleted
import TakhtajanTeo.Ch1.S6Eq64
import TakhtajanTeo.Ch1.L613

/-!
# Program G, F2: `thm_7_7` (下属1)

Proof of the F2 sub-interface (742eaa55). Stubs A–D (`s7g_f2_mixed`, `s7g_f2_ddpartial`,
`s7g_f2_conjflip`, `s7g_f2_conjW`, `s7g_f2_germ`, `s7g_f2_herm`) are in `S7SecondVarGeneric`; this file
proves stubs E, F1, F2, G, H and assembles `s7g_thm_7_7`.

Route ("P² = P", in the `𝕌`-model, all ε-derivatives through holomorphic extensions + torus Cauchy):
with `e = ε̄`, `X = \overline{Q_U(m_μ, e m')}`, `Y = Q_U(m_ν, e m')`, `C = 1 - |e|²|m'|²`, `D = ρ^{e m'}`,
* (7.7) line 1 gives `g(ε̄ κ) = ∫_𝕌 X Y C D` (F1), line 2 gives `g = ∫ \overline{m_μ} Y D` (core of F1) and,
  by Hermitian symmetry, `g = ∫ m_ν X D`;
* `∂_ē∂_e` passes under all three integrals (F2b, E: holomorphic extension in `P = (a, b)`, uniform `L¹` bound,
  `s7g_f2_mixed`);
* pointwise (G), `T₁ - T₂ - T₃ = -\overline{m_μ} m_ν |m'|² ρ - \overline{m_μ} m_ν ρ̈ + \overline{Q̇_U μ} Q̇_U ν ρ`
  (all `Q̈` terms cancel; `∂Q = 0`, `∂ρ = 0`, `prop_6_3`);
* so `g̈ = ∫ (\overline{m_μ} m_ν |m'|² ρ + \overline{m_μ} m_ν ρ̈ - \overline{Q̇μ} Q̇ν ρ)`; transport to `𝔻*` (H) and
  `cor_7_3` give `(μκ̄, G(νκ̄)) + (μν̄, G(|κ|²))`.
`lemma_7_8` is NOT on this route (no `Q̈` integrability is needed).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC

/-- The `𝕌`-model data of line 2 of (7.7): the double-kernel integrand `F_P(s, t) = \overline{m_μ(s)} m_ν(t)
K_P(t, s)²` on `(𝕌 ∖ {i})²`, its joint continuity and uniform `L¹` bound on a polydisc, and
`g(ē κ) = (12/π) ∫ F_{(e, ē)}` near `0`. -/
theorem s7g_f2_Edata {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgκ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), κ z = g z) {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ')
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {mμ φμ mν φν : ℂ → ℂ} (hμh : IsHarmonicU mμ φμ)
    (hμf : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (μ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hνh : IsHarmonicU mν φν)
    (hνf : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (ν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {F : ℂ × ℂ → ℂ × ℂ → ℂ} (hF : F = fun P x => conj (mμ x.1) * (mν x.2 *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2)) :
    ∃ C R0 : ℝ, 0 ≤ C ∧ IsBeltramiCoeff m' upperHalf C ∧ 0 < R0 ∧ 2 * R0 * C < 1 ∧
      (∃ M : ℝ, ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0,
        ∫⁻ x in (upperHalf \ {I}) ×ˢ (upperHalf \ {I}), ‖F P x‖ₑ ≤ ENNReal.ofReal M) ∧
      ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 p.2)
        ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ ((upperHalf \ {I}) ×ˢ (upperHalf \ {I}))) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ R0 ∧ ∀ e ∈ ball (0 : ℂ) r,
        gWP μ ν (conj e • κ) = (12 / π : ℂ) * ∫ x in (upperHalf \ {I}) ×ˢ (upperHalf \ {I}), F (e, conj e) x := by
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
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  have hAc : ContinuousOn (fun s => conj (mμ s)) S :=
    Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hμh).mono hSU)
  have hBc : ContinuousOn (fun s => conj (mν s)) S :=
    Complex.continuous_conj.comp_continuousOn ((harmonicU_continuousOn hνh).mono hSU)
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = 1 / (4 * (C + 1)) := ⟨_, rfl⟩
  have hR0p : 0 < R0 := by rw [hR0]; positivity
  have hR0k2 : 2 * R0 * C < 1 := by
    rw [hR0, show 2 * (1 / (4 * (C + 1))) * C = C / (2 * (C + 1)) by field_simp; ring,
      div_lt_one (by positivity)]
    linarith
  have hR0k : R0 * C < 1 := by nlinarith
  have hFeq : ∀ P x, F P x = conj (mμ x.1) * (conj (conj (mν x.2)) *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2) := fun P x => by
    rw [hF, Complex.conj_conj]
  have hcont : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 p.2)
      ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ (S ×ˢ S)) :=
    (s7g_l3_cont hC0 hmB hms hW hSU hAc hBc hR0k).congr fun p _ => hFeq p.1 p.2
  obtain ⟨M, hM⟩ := s7g_l3_L1 (A := fun s => conj (mμ s)) (B := fun s => conj (mν s)) hC0 hmB hms hW hSm hSU
    hμh hνh hfμ hfν (fun s _ => Complex.norm_conj _) (fun s _ => Complex.norm_conj _) hR0p.le hR0k2
  have hM' : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ∫⁻ x in S ×ˢ S, ‖F P x‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    have h := hM P hP
    have e : (fun x => ‖F P x‖ₑ) = fun x : ℂ × ℂ => ‖conj (mμ x.1) * (conj (conj (mν x.2)) *
        (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2)‖ₑ :=
      funext fun x => by rw [hFeq]
    rw [e]
    exact h
  have hTm : MeasurableSet (S ×ˢ S) := hSm.prod hSm
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R0 (1 / (‖κ‖ + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min hR0p (by positivity)
  have hrR : r ≤ R0 := by rw [hr]; exact min_le_left _ _
  refine ⟨C, R0, hC0, hmB, hR0p, hR0k2, ⟨M, hM'⟩, hcont, r, hr0, hrR, fun e he => ?_⟩
  set ε : ℂ := conj e with hεd
  have hεr : ‖ε‖ < r := by rw [hεd, Complex.norm_conj]; exact mem_ball_zero_iff.1 he
  have hεR : ‖ε‖ < R0 := lt_of_lt_of_le hεr hrR
  have hεκ : ‖ε‖ < 1 / (‖κ‖ + 1) := lt_of_lt_of_le hεr (by rw [hr]; exact min_le_right _ _)
  have hε1 : ‖ε‖ * ‖κ‖ < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hεκ
    nlinarith [norm_nonneg ε, norm_nonneg κ]
  have hε2 : ‖conj ε‖ * C < 1 := by
    rw [Complex.norm_conj]
    nlinarith [norm_nonneg ε]
  have hce : conj ε = e := by rw [hεd, Complex.conj_conj]
  have hne : ‖e‖ < R0 := by
    have h := hεR
    rwa [hεd, Complex.norm_conj] at h
  have hPmem : ((e, conj e) : ℂ × ℂ) ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 :=
    ⟨mem_closedBall_zero_iff.2 hne.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact hne.le)⟩
  rw [s7g_l2 hμ hν hκ hg hgκ hharm hm' hC0 hCb hε1 hε2]
  congr 1
  have hV : (wU fun u => conj ε * m' u) = W (e, conj e) := by
    rw [hce, wr_wU_eq, hW]
  rw [hV]
  have hint : Integrable (F (e, conj e)) ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    refine ⟨?_, lt_of_le_of_lt (hM' _ hPmem) ENNReal.ofReal_lt_top⟩
    exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hPmem, hx⟩)).aestronglyMeasurable hTm
  have hprod := integral_prod (F (e, conj e)) hint
  have e2 : (∫ x in S ×ˢ S, F (e, conj e) x) = ∫ s in S, ∫ t in S, F (e, conj e) (s, t) := by
    rw [← hprod, Measure.prod_restrict]
    rfl
  rw [e2, ← setIntegral_congr_set hnull]
  refine setIntegral_congr_fun hSm fun s hs => ?_
  rw [← setIntegral_congr_set hnull, ← integral_const_mul]
  refine setIntegral_congr_fun hSm fun t ht => ?_
  rw [hF, s7g_l3_Aconj μ hs.1 hs.2 (hμf s hs.1 hs.2)]
  have hB := s7g_l3_Aconj ν ht.1 ht.2 (hνf t ht.1 ht.2)
  rw [show conj (ν (cayley (conj t)) * (conj (2 * I / (conj t + I) ^ 2) / (2 * I / (conj t + I) ^ 2))) = mν t by
    rw [hB, Complex.conj_conj]]

/-- `∂_z∂_z̄` depends only on the germ. -/
theorem s7g_f2_germ2 {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[𝓝 z] h) : dz (dzbar f) z = dz (dzbar h) z := by
  have h1 : (dzbar f) =ᶠ[𝓝 z] (dzbar h) := by
    filter_upwards [hfh.fderiv (𝕜 := ℝ)] with y hy
    simp only [dzbar, hy]
  exact s7g_f2_dz_congr h1

/-- The fixed-`s` swap: `∂_ē∂_e J_s(0) = ∂_ē∂_e J_s(0)` (both orders) is the mixed partial of the holomorphic
extension `j_s(a, b) = ∫_{𝕌∖{i}} m_ν(t) K_{(a,b)}(t, s)²`, and it passes under the `t`-integral. -/
theorem s7g_f2_Jdd {m' mν : ℂ → ℂ} {C R0 Mν : ℝ} (hC0 : 0 ≤ C) (hmB : IsBeltramiCoeff m' upperHalf C)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf) (hνc : ContinuousOn mν upperHalf) (hMν0 : 0 ≤ Mν)
    (hνb : ∀ u ∈ upperHalf, ‖mν u‖ ≤ Mν) (hR0p : 0 < R0) (hR0k : R0 * C < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {s : ℂ} (hs : s ∈ upperHalf) :
    deriv (fun b => deriv (fun a => ∫ t in upperHalf \ {I}, mν t *
        (dz (W (a, b)) t * dz (W (a, b)) (conj s) / (W (a, b) t - W (a, b) (conj s)) ^ 2) ^ 2) 0) 0 =
      ∫ t in upperHalf \ {I}, deriv (fun b => deriv (fun a => mν t *
        (dz (W (a, b)) t * dz (W (a, b)) (conj s) / (W (a, b) t - W (a, b) (conj s)) ^ 2) ^ 2) 0) 0 ∧
    dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 =
      deriv (fun b => deriv (fun a => ∫ t in upperHalf \ {I}, mν t *
        (dz (W (a, b)) t * dz (W (a, b)) (conj s) / (W (a, b) t - W (a, b) (conj s)) ^ 2) ^ 2) 0) 0 ∧
    dz (dzbar fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 =
      deriv (fun b => deriv (fun a => ∫ t in upperHalf \ {I}, mν t *
        (dz (W (a, b)) t * dz (W (a, b)) (conj s) / (W (a, b) t - W (a, b) (conj s)) ^ 2) ^ 2) 0) 0 := by
  have hU := measurableSet_upperHalf_aux
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ → ℂ, Ψ = fun P u =>
      mν u * (dz (W P) u * dz (W P) (conj s) / (W P u - W P (conj s)) ^ 2) ^ 2 := ⟨_, rfl⟩
  have hc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Ψ p.1 p.2) ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ S) :=
    (s71_b2_cont hC0 hmB hms hνc hs hR0k hW hΨ).mono (prod_mono subset_rfl hSU)
  have hhol : ∀ u ∈ S, (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => Ψ (a, b) u) (ball (0 : ℂ) R0)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => Ψ (a, b) u) (ball (0 : ℂ) R0) := fun u hu =>
    s71_b2_holo hC0 hmB hms hs hR0k hW hΨ (hSU hu)
  obtain ⟨M, hM⟩ := s71_b2_L1 hC0 hmB hms hνc hMν0 hνb hs hR0k hW hΨ
  have hM' : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ∫⁻ u in S, ‖Ψ P u‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    obtain ⟨hi, hb⟩ := hM P hP
    calc _ ≤ ∫⁻ u in upperHalf, ‖Ψ P u‖ₑ := lintegral_mono_set hSU
      _ = ENNReal.ofReal (∫ u in upperHalf, ‖Ψ P u‖) := (ofReal_integral_norm_eq_lintegral_enorm hi).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb
  obtain ⟨-, hmix⟩ := s7g_f2_mixed (m := volume) hSm hR0p hc hhol hM'
  have hj2 := (s7g_f2_mixC2 hSm hc hhol hM').1
  obtain ⟨hd1, hd2⟩ := s7g_f2_ddpartial hR0p hj2
  have hev : (fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) =ᶠ[𝓝 (0 : ℂ)]
      fun e => (fun P => ∫ u in S, Ψ P u) (e, conj e) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 1 / (C + 1) by positivity)] with e he
    have he' : ‖e‖ * C < 1 := by
      rw [mem_ball_zero_iff, lt_div_iff₀ (by positivity)] at he
      nlinarith [norm_nonneg e]
    rw [← setIntegral_congr_set hnull]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact (s71_b2_diag hC0 hmB hW hΨ he' t).symm
  rw [hΨ] at hmix hd1 hd2 hev
  refine ⟨hmix, ?_, ?_⟩
  · rw [s7g_f2_germ hev]
    exact hd1
  · rw [s7g_f2_germ2 hev]
    exact hd2

/-- STUB E (line 2 under the integral). In the `𝕌`-model (data as in `s7g_l3_core`), with
`J_s(e) = ∫_𝕌 m_ν(t) K̄_{e m'}(t, s)²`: `g(ē κ) = (12/π) ∫ \overline{m_μ} J_s(e)` near `0`, the integrand of
`∂_ē∂_e` is integrable, and `∂_ē∂_e` passes under the integral. -/
theorem s7g_f2_line2 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
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
    (∃ r : ℝ, 0 < r ∧ ∀ e ∈ ball (0 : ℂ) r, gWP μ ν (conj e • κ) = (12 / π : ℂ) * ∫ s in upperHalf, conj (mμ s) *
      ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) ∧
    IntegrableOn (fun s => conj (mμ s) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) upperHalf ∧
    dzbar (dz fun e => gWP μ ν (conj e • κ)) 0 = (12 / π : ℂ) * ∫ s in upperHalf, conj (mμ s) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 ∧
    IntegrableOn (fun s => conj (mμ s) *
      dz (dzbar fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) upperHalf ∧
    dz (dzbar fun e => gWP μ ν (conj e • κ)) 0 = (12 / π : ℂ) * ∫ s in upperHalf, conj (mμ s) *
      dz (dzbar fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
  have hU := measurableSet_upperHalf_aux
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  have hTm : MeasurableSet (S ×ˢ S) := hSm.prod hSm
  have hms := wr_isHarmonicU_contDiffOn hharm
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ × ℂ → ℂ, F = fun P x => conj (mμ x.1) * (mν x.2 *
      (dz (W P) x.2 * dz (W P) (conj x.1) / (W P x.2 - W P (conj x.1)) ^ 2) ^ 2) := ⟨_, rfl⟩
  obtain ⟨C, R0, hC0, hmB, hR0p, hR0k2, ⟨M, hM⟩, hcont, r, hr0, hrR, hEq⟩ :=
    s7g_f2_Edata hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf hW hF
  have hR0k : R0 * C < 1 := by nlinarith
  obtain ⟨Mν, hMν0, hνb⟩ := harmonicU_bounded hνh
  have hνc := harmonicU_continuousOn hνh
  have hhol : ∀ x ∈ S ×ˢ S,
      (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R0)) ∧
        ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R0) := by
    intro x hx
    have h := s71_b2_holo (μ := fun t => conj (mμ x.1) * mν t) hC0 hmB hms (hSU hx.1) hR0k hW rfl (hSU hx.2)
    refine ⟨fun b hb => (h.1 b hb).congr fun a _ => ?_, fun a ha => (h.2 a ha).congr fun b _ => ?_⟩
    · rw [hF]
      ring
    · rw [hF]
      ring
  obtain ⟨hmixi, hmix⟩ := s7g_f2_mixed (m := volume) hTm hR0p hcont hhol hM
  have hΦ2 := (s7g_f2_mixC2 hTm hcont hhol hM).1
  -- the `s`-pointwise identification
  have hpt : ∀ s ∈ S, (∫ t in S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0) =
      conj (mμ s) * dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
    intro s hs
    obtain ⟨hJ1, hJ2, -⟩ := s7g_f2_Jdd hC0 hmB hms hνc hMν0 hνb hR0p hR0k hW (hSU hs)
    rw [hJ2, hJ1, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hF, deriv_const_mul_field']
  have hsym : ∀ s ∈ S,
      dz (dzbar fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 =
        dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
    intro s hs
    obtain ⟨-, hJ2, hJ3⟩ := s7g_f2_Jdd hC0 hmB hms hνc hMν0 hνb hR0p hR0k hW (hSU hs)
    rw [hJ2, hJ3]
  -- integrability of the outer integrand
  have hint2 : Integrable (fun x : ℂ × ℂ => deriv (fun b => deriv (fun a => F (a, b) x) 0) 0)
      ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hmixi
  have hI1 : IntegrableOn (fun s => conj (mμ s) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) upperHalf := by
    have h := hint2.integral_prod_left
    refine (integrableOn_congr_set_ae hnull).1 ?_
    refine h.congr ?_
    filter_upwards [ae_restrict_mem hSm] with s hs
    exact hpt s hs
  have hI2 : IntegrableOn (fun s => conj (mμ s) *
      dz (dzbar fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) upperHalf := by
    refine (integrableOn_congr_set_ae hnull).1 ?_
    refine (hI1.mono_set hSU).congr ?_
    filter_upwards [ae_restrict_mem hSm] with s hs
    rw [hsym s hs]
  -- the derivative of `g`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ × ℂ → ℂ, Φ = fun P => (12 / π : ℂ) * ∫ x in S ×ˢ S, F P x := ⟨_, rfl⟩
  have hΦC : ContDiffOn ℂ 2 Φ (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := by
    rw [hΦ]
    exact contDiffOn_const.mul hΦ2
  have hgev : (fun e => gWP μ ν (conj e • κ)) =ᶠ[𝓝 (0 : ℂ)] fun e => Φ (e, conj e) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr0] with e he
    rw [hEq e he, hΦ]
  obtain ⟨hdd1, hdd2⟩ := s7g_f2_ddpartial hR0p hΦC
  have hval : deriv (fun b => deriv (fun a => Φ (a, b)) 0) 0 = (12 / π : ℂ) * ∫ s in upperHalf, conj (mμ s) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 := by
    rw [hΦ]
    simp only [deriv_const_mul_field']
    rw [hmix]
    congr 1
    have e1 : (∫ x in S ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) x) 0) 0) =
        ∫ s in S, ∫ t in S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 := by
      rw [← integral_prod _ hint2, Measure.prod_restrict]
      rfl
    rw [e1, ← setIntegral_congr_set hnull]
    exact setIntegral_congr_fun hSm hpt
  refine ⟨⟨r, hr0, fun e he => ?_⟩, hI1, ?_, hI2, ?_⟩
  · have hne : ‖e‖ * C < 1 := by
      have h1 : ‖e‖ < R0 := lt_of_lt_of_le (mem_ball_zero_iff.1 he) hrR
      nlinarith [norm_nonneg e]
    rw [hEq e he]
    congr 1
    have hint : Integrable (F (e, conj e)) ((volume.restrict S).prod (volume.restrict S)) := by
      have hPmem : ((e, conj e) : ℂ × ℂ) ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 := by
        have h1 : ‖e‖ ≤ R0 := (lt_of_lt_of_le (mem_ball_zero_iff.1 he) hrR).le
        exact ⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact h1)⟩
      rw [Measure.prod_restrict]
      refine ⟨?_, lt_of_le_of_lt (hM _ hPmem) ENNReal.ofReal_lt_top⟩
      exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨hPmem, hx⟩)).aestronglyMeasurable hTm
    have e2 : (∫ x in S ×ˢ S, F (e, conj e) x) = ∫ s in S, ∫ t in S, F (e, conj e) (s, t) := by
      rw [← integral_prod _ hint, Measure.prod_restrict]
      rfl
    rw [e2, ← setIntegral_congr_set hnull]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    dsimp only
    rw [← setIntegral_congr_set hnull, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hd := s71_b2_diag (μ := mν) (z := s) hC0 hmB hW (Ψ := fun P u =>
      mν u * (dz (W P) u * dz (W P) (conj s) / (W P u - W P (conj s)) ^ 2) ^ 2) rfl hne t
    rw [hF]
    simp only [] at hd ⊢
    rw [hd]
  · rw [s7g_f2_germ hgev, hdd1, hval]
  · rw [s7g_f2_germ2 hgev, hdd2, hval, ← setIntegral_congr_set hnull, ← setIntegral_congr_set hnull]
    congr 1
    exact setIntegral_congr_fun hSm fun s hs => by rw [hsym s hs]

/-- `|m(u)| = |μ(S ū)|` for the pulled-back weight. -/
theorem s7g_f2_mnorm {μ m : ℂ → ℂ}
    (hmf : ∀ u ∈ upperHalf, u ≠ I → m u = conj (μ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    ∀ u ∈ upperHalf, u ≠ I → ‖m u‖ = ‖μ (cayley (conj u))‖ := by
  intro u hu huI
  rw [hmf u hu huI, norm_mul, norm_mul, (p71_AB_norm hu huI).1, (p71_AB_norm hu huI).2, mul_one, mul_one,
    Complex.norm_conj]

/-- `p71_wm_Q` at a fixed parameter `ε` (same proof): `Q_A(μ, εν)(z) = c(z) · \overline{Q_U(m_μ, ε̄ m_ν)(y)}`,
`y = \overline{S⁻¹ z}`, for `‖ε‖ ‖ν‖ < 1`, `‖ε̄‖ C < 1` and `w_U(ε̄ m')(y) ≠ i`. -/
theorem s7g_f2_wmQ {μ ν : LinfStar} (hμ : μ ∈ harmonicBeltrami) (hν : ν ∈ harmonicBeltrami) {gμ gν : ℂ → ℂ}
    (hgμc : ContinuousOn gμ unitDiscExterior) (hgμ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), μ z = gμ z)
    (hgνc : ContinuousOn gν unitDiscExterior) (hgν : ∀ᵐ z ∂(volume.restrict unitDiscExterior), ν z = gν z)
    {mμ mν : ℂ → ℂ}
    (hmμ : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (gμ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hmν : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {m' ψ' : ℂ → ℂ} (hharm' : IsHarmonicU m' ψ')
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {C : ℝ} (hC0 : 0 ≤ C) (hCb : ∀ z ∈ upperHalf, ‖m' z‖ ≤ C)
    {z : ℂ} (hz : z ∈ unitDiscExterior) {ε : ℂ} (hε1 : ‖ε‖ * ‖ν‖ < 1) (hε2 : ‖conj ε‖ * C < 1)
    (hVy : wU (fun u => conj ε * m' u) (conj (cayleyInv z)) ≠ I) :
    Qfun μ (ε • ν) z =
      (2 * I / (cayleyInv z + I) ^ 2) / conj (2 * I / (cayleyInv z + I) ^ 2) *
        conj (QfunU mμ (fun u => conj ε * mν u) (conj (cayleyInv z))) := by
  -- `V = w_U(ε̄ m')` with `m'` the harmonic representative of WM1'; `wU (ε̄ mν) = V = wU (ε̄ m[gν])` because the
  -- coefficients agree off `±i` (`p71_ns_congr`, i.e. `thm13_5_uniqueness_plane`). WM2 gives `w_A(εν) = S∘V∘S⁻¹`.
  -- `P` is transported by `p71_cov` + `p71_kernel`; `R` pointwise a.e. (`RnmFunU` differs from `R[m[g]]` only on
  -- the null set `{η = V(i)}`).
  have hU := measurableSet_upperHalf_aux
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm').aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hjoint := wr_joint_contDiff_U hC0 hmB (wr_isHarmonicU_contDiffOn hharm')
  have hz1 : (1 : ℝ) < ‖z‖ := hz
  have hzne : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hx : (cayleyInv z).im < 0 := p71_cinv_im hz1
  have hTx : cayley (cayleyInv z) = z := p71_cay_cinv hzne
  have hxI : cayleyInv z + I ≠ 0 := by
    rw [p71_cinv_add hzne]
    exact div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (sub_ne_zero.mpr (Ne.symm hzne))
  have hy : conj (cayleyInv z) ∈ upperHalf := by
    show 0 < (conj (cayleyInv z)).im
    rw [Complex.conj_im]
    linarith
  have hyI : conj (cayleyInv z) ≠ I := by
    intro h
    apply hxI
    have e : cayleyInv z = -I := by
      have := congrArg conj h
      rwa [Complex.conj_conj, Complex.conj_I] at this
    rw [e]
    ring
  have hρ : ε • ν ∈ LinfStarBall := by
    show ε • ν ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact hε1
  obtain ⟨hVc, -, hVs, hVi⟩ := p71_V_facts hC0 hmB hε2
  have hVd : DifferentiableOn ℝ (wU fun u => conj ε * m' u) upperHalf :=
    (hjoint.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun u hu => (⟨hε2, hu⟩ : (conj ε, u) ∈ {ε : ℂ | ‖ε‖ * C < 1} ×ˢ upperHalf))).differentiableOn
      (by norm_num)
  have hVup : ∀ u ∈ upperHalf, wU (fun y => conj ε * m' y) u ∈ upperHalf := fun u hu =>
    e124_wU_upper hC0 hmB hε2 hu
  have hmν' : ∀ u ∈ upperHalf, u ≠ I → mν u = m' u := fun u hu hI => by rw [hmν u hu hI, hm' u hu hI]
  have hconjU : ∀ u : ℂ, u.im < 0 → conj u ∈ upperHalf := fun u hu => by
    show 0 < (conj u).im
    rw [Complex.conj_im]
    linarith
  have hconjI : ∀ u : ℂ, u ≠ -I → conj u ≠ I := fun u h1 h => by
    apply h1
    have := congrArg conj h
    rwa [Complex.conj_conj, Complex.conj_I] at this
  have hVeq : wU (fun u => conj ε * mν u) = wU (fun u => conj ε * m' u) := by
    show normalizedSolution _ = normalizedSolution _
    refine p71_ns_congr ?_
    filter_upwards [Measure.ae_ne volume I, Measure.ae_ne volume (-I)] with u h1 h2
    unfold extU
    split_ifs with ha hb
    · simp only [hmν' u ha h1]
    · simp only [hmν' (conj u) (hconjU u hb) (hconjI u h2)]
    · rfl
  have hV2 : wU (fun u => conj ε * (conj (gν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
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
  have hF1 : ∀ x', x' + I ≠ 0 → V x' + I ≠ 0 → wA (ε • ν) (cayley x') = cayley (V x') := by
    intro x' h1 h2
    have h := p71_wm_conj hν hgνc hgν hε1 x'
    rw [hV2, p71_S_coe h1, p71_S_coe h2] at h
    show finPart (wAS (ε • ν) ((cayley x' : ℂ) : ExtPlane)) = _
    rw [h]
    rfl
  have hdzs : ∀ u ∈ upperHalf, dz V (conj u) = conj (dz V u) := by
    intro u hu
    have hd : DifferentiableAt ℝ V (conj (conj u)) := by
      rw [Complex.conj_conj]
      exact hVd.differentiableAt (hUo.mem_nhds hu)
    have h := (abR_x_dz_dzbar_conj hd).2.1
    have hfun : (fun w => conj (V (conj w))) = V := funext fun w => by rw [hVs, Complex.conj_conj]
    rwa [hfun, Complex.conj_conj] at h
  -- local representation `w_A(εν) = S ∘ V ∘ S⁻¹` and its `∂_z`
  have hcinvc : ∀ z0 : ℂ, z0 ≠ 1 → ContinuousAt cayleyInv z0 := fun z0 h => (p71_cinv_hasDeriv h).continuousAt
  have hloc : ∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → V (cayleyInv z0) + I ≠ 0 →
      wA (ε • ν) =ᶠ[𝓝 z0] fun z' => cayley (V (cayleyInv z')) := by
    intro z0 h0 h1 h2
    have hc1 : ContinuousAt (fun z' => cayleyInv z' + I) z0 := (hcinvc z0 h0).add continuousAt_const
    have hc2 : ContinuousAt (fun z' => V (cayleyInv z') + I) z0 :=
      (hVc.continuousAt.comp (hcinvc z0 h0)).add continuousAt_const
    filter_upwards [hc1.eventually_ne h1, hc2.eventually_ne h2, continuousAt_id.eventually_ne h0]
      with z' e1 e2 e3
    have := hF1 (cayleyInv z') e1 e2
    rwa [p71_cay_cinv (show z' ≠ 1 from e3)] at this
  have hdzw : ∀ z0 : ℂ, z0 ≠ 1 → cayleyInv z0 + I ≠ 0 → V (cayleyInv z0) + I ≠ 0 →
      dz (wA (ε • ν)) z0 = 2 * I / (V (cayleyInv z0) + I) ^ 2 *
        (dz V (cayleyInv z0) * (2 * I / (1 - z0) ^ 2)) := by
    intro z0 h0 h1 h2
    have e0 : dz (wA (ε • ν)) z0 = dz (fun z' => cayley (V (cayleyInv z'))) z0 := by
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
  -- the point `z`
  have hVx : V (cayleyInv z) = conj (V (conj (cayleyInv z))) := by
    rw [← hVs, Complex.conj_conj]
  have hVxI : V (cayleyInv z) + I ≠ 0 := by
    rw [hVx]
    intro h
    apply hVy
    have := congrArg conj h
    simp only [map_add, Complex.conj_conj, Complex.conj_I, map_zero] at this
    linear_combination this
  have hXim : (V (cayleyInv z)).im < 0 := by
    rw [hVx, Complex.conj_im]
    have : 0 < (V (conj (cayleyInv z))).im := hVup _ hy
    linarith
  have hXI : V (cayleyInv z) ≠ -I := fun h => hVxI (by rw [h]; ring)
  have hwz : wA (ε • ν) z = cayley (V (cayleyInv z)) := by
    have := hF1 (cayleyInv z) hxI hVxI
    rwa [hTx] at this
  -- the `R` identity, a.e. on `𝕌`
  have hsm : ∀ᵐ w ∂(volume.restrict unitDiscExterior), (ε • ν) w = ε * gν w := by
    filter_upwards [Lp.coeFn_smul ε ν, hgν] with w h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have hR : ∀ᵐ η ∂(volume.restrict upperHalf),
      RnmFun μ (ε • ν) (cayley (conj η)) = (2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) *
        conj (RnmFunU mμ (fun u => conj ε * mν u) η) := by
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I),
      ae_restrict_of_ae (Measure.ae_ne volume (V I)), p71_V_push hVd hVi (p71_phi_ae hgμ),
      p71_V_push hVd hVi (p71_phi_ae hsm)] with η hη hηI hηV hμt hνt
    obtain ⟨ht, hVt⟩ := hVi η hη
    set t := Function.invFun V η with htdef
    have htI : t ≠ I := fun h => hηV (by rw [← hVt, h])
    have ht0 : 0 < t.im := ht
    have hη0 : 0 < η.im := hη
    have hctI : conj t + I ≠ 0 := by
      intro h; apply htI
      have : conj (conj t) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hcηI : conj η + I ≠ 0 := by
      intro h; apply hηI
      have : conj (conj η) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hVct : V (conj t) = conj η := by rw [hVs, hVt]
    have hVctI : V (conj t) + I ≠ 0 := by rw [hVct]; exact hcηI
    have hwt : wA (ε • ν) (cayley (conj t)) = cayley (conj η) := by rw [hF1 (conj t) hctI hVctI, hVct]
    have hext : cayley (conj η) ∈ unitDiscExterior :=
      p71_cay_ext (by rw [Complex.conj_im]; linarith) hcηI
    have hne0 : wA (ε • ν) (cayley (conj t)) ≠ 0 := by
      rw [hwt]
      intro h
      have : (1 : ℝ) < ‖cayley (conj η)‖ := hext
      rw [h, norm_zero] at this
      linarith
    have hinv : Function.invFun (wA (ε • ν)) (cayley (conj η)) = cayley (conj t) := by
      rw [← hwt]
      exact bc_invFun_wA hne0
    have hu1 : cayley (conj t) ≠ 1 := p71_cay_ne_one hctI
    have hci : cayleyInv (cayley (conj t)) = conj t := p71_cinv_cay hctI
    have hdzu := hdzw (cayley (conj t)) hu1 (by rw [hci]; exact hctI) (by rw [hci]; exact hVctI)
    rw [hci, hVct, hdzs t ht, p71_DT hu1, hci] at hdzu
    have hext' : cayley (conj t) ∈ unitDiscExterior :=
      p71_cay_ext (by rw [Complex.conj_im]; linarith) hctI
    obtain ⟨hA1, hB1⟩ := p71_AB_norm ht htI
    have hkey := p71_key ht htI
    show (fun u => μ u / (1 - ‖(ε • ν) u‖ ^ 2) * (dz (wA (ε • ν)) u / conj (dz (wA (ε • ν)) u)))
        (Function.invFun (wA (ε • ν)) (cayley (conj η))) = _ * conj ((fun u => mμ u / (1 - ‖conj ε * mν u‖ ^ 2) *
          (dz (wU fun u => conj ε * mν u) u / conj (dz (wU fun u => conj ε * mν u) u)))
            (Function.invFun (wU fun u => conj ε * mν u) η))
    rw [hVeq, hinv]
    simp only []
    rw [← htdef, hdzu, hmμ t ht htI, hmν t ht htI, hμt, hνt]
    have hnorm : ‖conj ε * (conj (gν (cayley (conj t))) * (cayley t ^ 2 / conj (cayley t) ^ 2) *
        (conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2)))‖ = ‖ε * gν (cayley (conj t))‖ := by
      rw [norm_mul, norm_mul, norm_mul, hA1, hB1, Complex.norm_conj, Complex.norm_conj, norm_mul]
      ring
    rw [hnorm]
    have hT1 : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hcηI)
    have hT2 : 2 * I / (conj t + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hctI)
    have hT1' : conj (2 * I / (conj η + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT1
    have hT2' : conj (2 * I / (conj t + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT2
    generalize cayley t ^ 2 / conj (cayley t) ^ 2 = A at hkey hA1 ⊢
    generalize conj (2 * I / (t + I) ^ 2) / (2 * I / (t + I) ^ 2) = B at hkey hB1 ⊢
    generalize 2 * I / (conj η + I) ^ 2 = T1 at hT1 hT1' ⊢
    generalize 2 * I / (conj t + I) ^ 2 = T2 at hkey hT2 hT2' ⊢
    generalize gμ (cayley (conj t)) = a
    generalize dz V t = d
    have hA0 : conj A ≠ 0 := (map_ne_zero _).mpr (norm_ne_zero_iff.mp (by rw [hA1]; norm_num))
    have hB' : conj B = conj T2 / T2 / conj A := by
      rw [← hkey]
      field_simp
    simp only [map_mul, map_div₀, map_sub, map_one, map_pow, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    rw [hB']
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hd0' : conj d ≠ 0 := (map_ne_zero _).mpr hd0
      field_simp
  -- assembly
  show harmonicProjFun (RnmFun μ (ε • ν)) (wA (ε • ν) z) * (conj (dz (wA (ε • ν)) z) / dz (wA (ε • ν)) z) =
    _ * conj (harmonicProjU (RnmFunU mμ (fun u => conj ε * mν u)) (wU (fun u => conj ε * mν u) (conj (cayleyInv z))) *
      (conj (dz (wU (fun u => conj ε * mν u)) (conj (cayleyInv z))) /
        dz (wU (fun u => conj ε * mν u)) (conj (cayleyInv z))))
  have hdz := hdzw z hzne hxI hVxI
  have hdzx : dz V (cayleyInv z) = conj (dz V (conj (cayleyInv z))) := by
    have := hdzs _ hy
    rwa [Complex.conj_conj] at this
  rw [hwz, hdz, hVeq, hdzx]
  have hP : harmonicProjFun (RnmFun μ (ε • ν)) (cayley (V (cayleyInv z))) =
      (2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2) *
        conj (harmonicProjU (RnmFunU mμ (fun u => conj ε * mν u)) (conj (V (cayleyInv z)))) := by
    show (3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) * ∫ ζ in unitDiscExterior,
        RnmFun μ (ε • ν) ζ / (1 - ζ * conj (cayley (V (cayleyInv z)))) ^ 4 =
      (2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2) *
      conj (-(3 * (conj (V (cayleyInv z)) - conj (conj (V (cayleyInv z)))) ^ 2 / (π : ℂ)) *
        ∫ u in upperHalf, RnmFunU mμ (fun u => conj ε * mν u) u / (u - conj (conj (V (cayleyInv z)))) ^ 4)
    rw [p71_cov, ← integral_const_mul, ← integral_const_mul, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hR, ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hRη hη hηI
    have hη0 : 0 < η.im := hη
    have hcηI : conj η + I ≠ 0 := by
      intro h; apply hηI
      have : conj (conj η) = conj (-I) := by rw [eq_neg_of_add_eq_zero_left h]
      rwa [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at this
    have hT1 : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hcηI)
    have hT1' : conj (2 * I / (conj η + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hT1
    have hX1 : 2 * I / (V (cayleyInv z) + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hVxI)
    have hX1' : conj (2 * I / (V (cayleyInv z) + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hX1
    have hk := p71_kernel hη hηI hXim hXI
    have hsq := p71_sq_phase hT1
    rw [hRη]
    calc (3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) * (((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) *
          ((2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) *
            conj (RnmFunU mμ (fun u => conj ε * mν u) η) / (1 - cayley (conj η) * conj (cayley (V (cayleyInv z)))) ^ 4))
        = ((3 * (1 - ‖cayley (V (cayleyInv z))‖ ^ 2) ^ 2 / π : ℂ) *
            ((2 * I / (conj η + I) ^ 2) ^ 2 / (1 - cayley (conj η) * conj (cayley (V (cayleyInv z)))) ^ 4) *
            (conj (2 * I / (V (cayleyInv z) + I) ^ 2) / (2 * I / (V (cayleyInv z) + I) ^ 2))) *
          ((2 * I / (V (cayleyInv z) + I) ^ 2) / conj (2 * I / (V (cayleyInv z) + I) ^ 2)) *
            conj (RnmFunU mμ (fun u => conj ε * mν u) η) := by
          rw [← hsq]
          field_simp
      _ = _ := by
          rw [hk]
          simp only [map_mul, map_div₀, map_neg, map_pow, map_sub, Complex.conj_conj, Complex.conj_ofReal,
            map_ofNat]
          ring
  rw [hVs (cayleyInv z), hP]
  have hX1 : 2 * I / (V (cayleyInv z) + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hVxI)
  have hX1' : conj (2 * I / (V (cayleyInv z) + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hX1
  have hx1 : 2 * I / (cayleyInv z + I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hxI)
  have hx1' : conj (2 * I / (cayleyInv z + I) ^ 2) ≠ 0 := (map_ne_zero _).mpr hx1
  rw [p71_DT hzne]
  generalize 2 * I / (V (cayleyInv z) + I) ^ 2 = TX at hX1 hX1' ⊢
  generalize 2 * I / (cayleyInv z + I) ^ 2 = Tx at hx1 hx1' ⊢
  generalize harmonicProjU (RnmFunU mμ fun u => conj ε * mν u) (conj (V (cayleyInv z))) = Pu
  generalize dz V (conj (cayleyInv z)) = d
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hd0' : conj d ≠ 0 := (map_ne_zero _).mpr hd0
    simp only [map_mul, map_div₀, map_inv₀, Complex.conj_conj]
    field_simp

/-- `ρ^{e m'}(η) = ρ_U(V η) |∂V(η)|²` for `V = w_U(e m')`. -/
theorem s7g_f2_rhoV (m' : ℂ → ℂ) (e η : ℂ) (hη : η ∈ upperHalf) :
    rhoVar m' e η = (rhoU (wU (fun u => e * m' u) η) : ℂ) * (‖dz (wU fun u => e * m' u) η‖ : ℂ) ^ 2 := by
  rw [(rhoVar_pullback m' e hη).1]
  unfold pullbackTensor
  rw [zpow_one, zpow_one, rhoVar_dzbar_conj, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- STUB F1 (line 1 in `𝕌`). (7.7) line 1 transported by the Cayley chart, near `0`. -/
theorem s7g_f2_line1U {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
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
    ∃ r : ℝ, 0 < r ∧ ∀ e ∈ ball (0 : ℂ) r, gWP μ ν (conj e • κ) = ∫ s in upperHalf,
      conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hm'n := s7g_f2_mnorm hm'
  have hK1 : 0 < ‖κ‖ + C + 1 := by positivity
  refine ⟨1 / (‖κ‖ + C + 1), by positivity, fun e he => ?_⟩
  have he' : ‖e‖ * (‖κ‖ + C + 1) < 1 := by
    rw [mem_ball_zero_iff, lt_div_iff₀ hK1] at he
    exact he
  have hε1 : ‖conj e‖ * ‖κ‖ < 1 := by
    rw [Complex.norm_conj]
    nlinarith [norm_nonneg e, norm_nonneg κ]
  have heC : ‖e‖ * C < 1 := by nlinarith [norm_nonneg e, norm_nonneg κ]
  have hε2 : ‖conj (conj e)‖ * C < 1 := by rw [Complex.conj_conj]; exact heC
  have hκ' : conj e • κ ∈ LinfStarBall := by
    show conj e • κ ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul]
    exact hε1
  obtain ⟨-, hbij, hVs, hVi⟩ := p71_V_facts hC0 hmB heC
  obtain ⟨hF1, hdzw⟩ := s7g_l2_conj hκ hg hgκ hm' hC0 hmB hε1 hε2
  simp only [Complex.conj_conj] at hF1 hdzw
  set V := wU (fun u => e * m' u) with hVdef
  have hdV : ∀ x, dz V (conj x) = conj (dz V x) := QCV.qcv_dz_conj_sym hVs
  have hIU : I ∈ upperHalf := by
    show (0 : ℝ) < I.im
    simp
  obtain ⟨-, hVt0⟩ := hVi I hIU
  have hsm : ∀ᵐ w ∂(volume.restrict unitDiscExterior), (conj e • κ) w = conj e * g w := by
    filter_upwards [Lp.coeFn_smul (conj e) κ, hgκ] with w h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have h1 : (∫ z in unitDiscExterior, Qfun (toLinf μ) (conj e • κ) z * conj (Qfun (toLinf ν) (conj e • κ) z) *
      (1 - ‖(conj e • κ) z‖ ^ 2) * (rho (wA (conj e • κ) z) * ‖dz (wA (conj e • κ)) z‖ ^ 2)) =
      ∫ z in unitDiscExterior, Qfun (toLinf μ) (conj e • κ) z * conj (Qfun (toLinf ν) (conj e • κ) z) *
      (1 - ‖conj e * g z‖ ^ 2) * (rho (wA (conj e • κ) z) * ‖dz (wA (conj e • κ)) z‖ ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hsm] with z hz
    rw [hz]
  rw [(eq_7_7 hμ hν hκ').1, h1, p71_cov]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I),
    ae_restrict_of_ae (Measure.ae_ne volume (Function.invFun V I))] with η hη hηI hηt
  have hc : conj η + I ≠ 0 := s7g_l3_cne hηI
  have hz : cayley (conj η) ∈ unitDiscExterior := by
    have h1 : (conj η).im < 0 := by
      rw [Complex.conj_im]
      exact neg_neg_of_pos hη
    exact p71_cay_ext h1 hc
  have hz1 : cayley (conj η) ≠ 1 := p71_cay_ne_one hc
  have hci : cayleyInv (cayley (conj η)) = conj η := p71_cinv_cay hc
  have hvI : V η ≠ I := fun h => hηt (hbij.1 (h.trans hVt0.symm))
  have hv : V η ∈ upperHalf := e124_wU_upper hC0 hmB heC hη
  have hcv : conj (V η) + I ≠ 0 := s7g_l3_cne hvI
  have hVc' : V (conj η) + I ≠ 0 := by rw [hVs]; exact hcv
  have hVy : wU (fun u => conj (conj e) * m' u) (conj (cayleyInv (cayley (conj η)))) ≠ I := by
    simp only [Complex.conj_conj]
    rw [hci, Complex.conj_conj]
    exact hvI
  have hQ := fun {ρ0 : ℂ → ℂ} (hρ0 : ρ0 ∈ harmonicL2 unitDiscExterior) {mρ φρ : ℂ → ℂ}
      (hρh : IsHarmonicU mρ φρ)
      (hρf : ∀ u ∈ upperHalf, u ≠ I → mρ u = conj (ρ0 (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
        (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) =>
    s7g_f2_wmQ (hCc ρ0 hρ0).1 hκ (wp_harmonic_continuousOn hρ0) (wp_harmonic_toLinf_ae hρ0) hg hgκ hρf hm' hharm hm'
      hC0 hCb hz hε1 hε2 hVy
  have hQμ := hQ hμ hμh hμf
  have hQν := hQ hν hνh hνf
  simp only [Complex.conj_conj] at hQμ hQν
  rw [hci, Complex.conj_conj] at hQμ hQν
  have hw : wA (conj e • κ) (cayley (conj η)) = cayley (conj (V η)) := by
    rw [hF1 (conj η) hc hVc', hVs]
  have hdw : dz (wA (conj e • κ)) (cayley (conj η)) = 2 * I / (conj (V η) + I) ^ 2 *
      (conj (dz V η) * ((conj η + I) ^ 2 / (2 * I))) := by
    rw [hdzw _ hz1 (by rw [hci]; exact hc) (by rw [hci]; exact hVc'), hci, hVs, hdV, s7g_l2_dt hc]
  have hcg : ‖conj e * g (cayley (conj η))‖ = ‖e‖ * ‖m' η‖ := by
    rw [norm_mul, Complex.norm_conj, hm'n η hη hηI]
  have hφ : (2 * I / (conj η + I) ^ 2) ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hc)
  have hφc : conj (2 * I / (conj η + I) ^ 2) ≠ 0 := (map_ne_zero _).2 hφ
  have hφB : ‖(2 * I / (conj η + I) ^ 2)‖ * ‖(conj η + I) ^ 2 / (2 * I)‖ = 1 := by
    rw [← norm_mul, show (2 * I / (conj η + I) ^ 2) * ((conj η + I) ^ 2 / (2 * I)) = 1 by
      have hI2 : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
      field_simp, norm_one]
  have hreal : ‖(2 * I / (conj η + I) ^ 2)‖ ^ 2 * (rho (cayley (conj (V η))) *
      ‖2 * I / (conj (V η) + I) ^ 2 * (conj (dz V η) * ((conj η + I) ^ 2 / (2 * I)))‖ ^ 2) =
      rhoU (V η) * ‖dz V η‖ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, ← (p71r_iso hv hv hvI hvI).2]
    calc ‖(2 * I / (conj η + I) ^ 2)‖ ^ 2 * (rho (cayley (conj (V η))) * (‖2 * I / (conj (V η) + I) ^ 2‖ *
          (‖dz V η‖ * ‖(conj η + I) ^ 2 / (2 * I)‖)) ^ 2) =
        rho (cayley (conj (V η))) * ‖2 * I / (conj (V η) + I) ^ 2‖ ^ 2 * ‖dz V η‖ ^ 2 *
          (‖(2 * I / (conj η + I) ^ 2)‖ * ‖(conj η + I) ^ 2 / (2 * I)‖) ^ 2 := by ring
      _ = _ := by rw [hφB]; ring
  have hcplx : (‖(2 * I / (conj η + I) ^ 2)‖ : ℂ) ^ 2 * ((rho (cayley (conj (V η))) : ℂ) *
      (‖2 * I / (conj (V η) + I) ^ 2 * (conj (dz V η) * ((conj η + I) ^ 2 / (2 * I)))‖ : ℂ) ^ 2) =
      (rhoU (V η) : ℂ) * (‖dz V η‖ : ℂ) ^ 2 := by exact_mod_cast hreal
  have hph : (2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) * (conj (2 * I / (conj η + I) ^ 2) / (2 * I / (conj η + I) ^ 2)) = 1 := by field_simp
  have hcc : ∀ X : ℂ, conj ((2 * I / (conj η + I) ^ 2) / conj (2 * I / (conj η + I) ^ 2) * conj X) = conj (2 * I / (conj η + I) ^ 2) / (2 * I / (conj η + I) ^ 2) * X := fun X => by
    rw [map_mul, map_div₀, Complex.conj_conj, Complex.conj_conj]
  rw [hQμ, hQν, hcc, hcg, hw, hdw, s7g_f2_rhoV m' e η hη]
  push_cast
  generalize 2 * I / (conj η + I) ^ 2 = φ at hcplx hph ⊢
  set X := QfunU mμ (fun u => e * m' u) η
  set Y := QfunU mν (fun u => e * m' u) η
  linear_combination (conj X * Y * (1 - (‖e‖ : ℂ) ^ 2 * (‖m' η‖ : ℂ) ^ 2)) * hcplx +
    (conj X * Y * (1 - (‖e‖ : ℂ) ^ 2 * (‖m' η‖ : ℂ) ^ 2) * ((‖φ‖ : ℂ) ^ 2 * ((rho (cayley (conj (V η))) : ℂ) *
      (‖2 * I / (conj (V η) + I) ^ 2 * (conj (dz V η) * ((conj η + I) ^ 2 / (2 * I)))‖ : ℂ) ^ 2))) * hph

/-- First-order Wirtinger product rules. -/
theorem s7g_f2_dzmul {f g : ℂ → ℂ} {y : ℂ} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dz (fun e => f e * g e) y = f y * dz g y + g y * dz f y ∧
      dzbar (fun e => f e * g e) y = f y * dzbar g y + g y * dzbar f y := by
  have h : fderiv ℝ (fun e => f e * g e) y = f y • fderiv ℝ g y + g y • fderiv ℝ f y :=
    (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  unfold dz dzbar
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  constructor <;> ring

/-- `∂_z̄` of a sum. -/
theorem s7g_f2_dzbar_add {f g : ℂ → ℂ} {y : ℂ} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzbar (fun e => f e + g e) y = dzbar f y + dzbar g y := by
  have h : fderiv ℝ (fun e => f e + g e) y = fderiv ℝ f y + fderiv ℝ g y := fderiv_add hf hg
  unfold dzbar
  rw [h]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- **Second-order Wirtinger product rule** at `0` for functions of class `C²` near `0`. -/
theorem s7g_f2_wmul {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : ContDiffOn ℝ 2 f (ball 0 r))
    (hg : ContDiffOn ℝ 2 g (ball 0 r)) :
    dzbar (dz fun e => f e * g e) 0 =
      f 0 * dzbar (dz g) 0 + g 0 * dzbar (dz f) 0 + dz f 0 * dzbar g 0 + dzbar f 0 * dz g 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hfd : ∀ y ∈ ball (0 : ℂ) r, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hy)
  have hgd : ∀ y ∈ ball (0 : ℂ) r, DifferentiableAt ℝ g y := fun y hy =>
    (hg.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hy)
  have hev : (dz fun e => f e * g e) =ᶠ[𝓝 (0 : ℂ)] fun y => f y * dz g y + g y * dz f y := by
    filter_upwards [isOpen_ball.mem_nhds h0] with y hy
    exact (s7g_f2_dzmul (hfd y hy) (hgd y hy)).1
  rw [p71_dzbar_congr hev]
  have hdg := (s7g_f2_dz_diff hg h0).1
  have hdf := (s7g_f2_dz_diff hf h0).1
  have d1 : DifferentiableAt ℝ (fun e => f e * dz g e) 0 := (hfd 0 h0).mul hdg
  have d2 : DifferentiableAt ℝ (fun e => g e * dz f e) 0 := (hgd 0 h0).mul hdf
  rw [s7g_f2_dzbar_add d1 d2, (s7g_f2_dzmul (hfd 0 h0) hdg).2,
    (s7g_f2_dzmul (hgd 0 h0) hdf).2]
  ring

/-- `e ↦ H(e, ē)` is `C²` over `ℝ` when `H` is `C²` over `ℂ` on a polydisc. -/
theorem s7g_f2_diagC2 {H : ℂ × ℂ → ℂ} {R : ℝ} (hH : ContDiffOn ℂ 2 H (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)) :
    ContDiffOn ℝ 2 (fun e => H (e, conj e)) (ball 0 R) := by
  have hmap : ContDiff ℝ 2 (fun e : ℂ => ((e, conj e) : ℂ × ℂ)) := contDiff_id.prodMk Complex.conjCLE.contDiff
  refine (hH.restrict_scalars ℝ).comp hmap.contDiffOn fun e he => ⟨he, ?_⟩
  rw [mem_ball_zero_iff, Complex.norm_conj]
  exact mem_ball_zero_iff.1 he

/-- On the diagonal `P = (ε, ε̄)` the kernel of `W_P` is `K̄_{εm'}` (unsquared `s71_b2_diag`). -/
theorem s7g_f2_Kdiag {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {ε : ℂ} (hε : ‖ε‖ * k < 1) (u z : ℂ) :
    dz (W (ε, conj ε)) u * dz (W (ε, conj ε)) (conj z) / (W (ε, conj ε) u - W (ε, conj ε) (conj z)) ^ 2 =
      kernelKbar (fun y => ε * m' y) u z := by
  have hWe : W (ε, conj ε) = wU (fun y => ε * m' y) := by rw [hW, wr_wU_eq]
  set f := wU (fun y => ε * m' y) with hf
  have hνε : IsBeltramiCoeff (fun y => ε * m' y) upperHalf (‖ε‖ * k) :=
    ⟨hmk.1.const_mul ε, hmk.2.mono fun z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)⟩
  have hsym : ∀ x, f (conj x) = conj (f x) := by
    rw [hf, e124_wU_eq_fMuSym hk hmk hε]
    exact (fMuSym_upperHalf (by positivity) hε hνε).2.2.1
  have hdsym : ∀ x, dz f (conj x) = conj (dz f x) := QCV.qcv_dz_conj_sym hsym
  rw [hWe]
  unfold kernelKbar
  rw [← hf, hsym z, hdsym z]

/-- The holomorphic extension `P ↦ K_P(u, z̄)` of the kernel is `C²` over `ℂ` on a polydisc. -/
theorem s7g_f2_Kreg {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1) :
    ContDiffOn ℂ 2 (fun P => dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := by
  obtain ⟨-, hinj, hhol⟩ := e64_W_basic hk hmk hms hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hk hmk hms hW
  have hsub := e64_polydisc_sub hk hRk
  have hU : IsOpen (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := isOpen_ball.prod isOpen_ball
  have hbc : ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R :=
    prod_mono ball_subset_closedBall ball_subset_closedBall
  have hzim : 0 < z.im := hz
  have huim : 0 < u.im := hu
  have hy1 : u.im ≠ 0 := huim.ne'
  have hy3 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; linarith
  have hne : ∀ P ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1}, (W P u - W P (conj z)) ^ 2 ≠ 0 := by
    intro P hP
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := hinj P hP h
    have h2 : u.im = (conj z).im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  have hcurve : ∀ (c : ℂ → ℂ × ℂ) (t : ℂ), c t ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} →
      (∀ y, DifferentiableAt ℂ (fun t' => W (c t') y) t) →
      (∀ y, y.im ≠ 0 → DifferentiableAt ℂ (fun t' => dz (W (c t')) y) t) →
      DifferentiableAt ℂ (fun t' => dz (W (c t')) u * dz (W (c t')) (conj z) /
        (W (c t') u - W (c t') (conj z)) ^ 2) t := by
    intro c t hct hWy hDy
    exact ((hDy u hy1).mul (hDy _ hy3)).div (((hWy u).sub (hWy (conj z))).pow 2) (hne _ hct)
  have h1 : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ
      (fun a => dz (W (a, p.2)) u * dz (W (a, p.2)) (conj z) / (W (a, p.2) u - W (a, p.2) (conj z)) ^ 2) p.1 := by
    intro p hp
    have hP : (p.1, p.2) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub (hbc hp)
    refine hcurve (fun t => (t, p.2)) p.1 hP (fun y => ?_) (fun y hy => ?_)
    · exact DifferentiableAt.comp (g := fun Q => W Q y) p.1 (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hmk hms hW hP hy).1
  have h2 : ∀ p ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R, DifferentiableAt ℂ
      (fun b => dz (W (p.1, b)) u * dz (W (p.1, b)) (conj z) / (W (p.1, b) u - W (p.1, b) (conj z)) ^ 2) p.2 := by
    intro p hp
    have hP : (p.1, p.2) ∈ {P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} := hsub (hbc hp)
    refine hcurve (fun t => (p.1, t)) p.2 hP (fun y => ?_) (fun y hy => ?_)
    · exact DifferentiableAt.comp (g := fun Q => W Q y) p.2 (hhol y _ hP) (by fun_prop)
    · exact (e64_dzW_holo hk hmk hms hW hP hy).2
  -- continuity on the closed polydisc, hence local bounds
  have hcomp : ∀ y : ℂ, y.im ≠ 0 →
      ContinuousOn (fun P : ℂ × ℂ => W P y) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) ∧
        ContinuousOn (fun P : ℂ × ℂ => dz (W P) y) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) := by
    intro y hy
    have hm : MapsTo (fun P : ℂ × ℂ => (P, y)) (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R)
        ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) := fun P hP => ⟨hsub hP, hy⟩
    have hc : Continuous fun P : ℂ × ℂ => (P, y) := continuous_id.prodMk continuous_const
    have k1 := hWc.comp hc.continuousOn hm
    have k2 := hDc.comp hc.continuousOn hm
    simp only [Function.comp_def] at k1 k2
    exact ⟨k1, k2⟩
  obtain ⟨hWu, hDu⟩ := hcomp u hy1
  obtain ⟨hWz, hDz⟩ := hcomp (conj z) hy3
  have hKc : ContinuousOn (fun P => dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2)
      (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
    (hDu.mul hDz).div ((hWu.sub hWz).pow 2) fun P hP => hne P (hsub hP)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hKc
  have h := s7g_h_contDiffOn hU 2 (fun P => dz (W P) u * dz (W P) (conj z) / (W P u - W P (conj z)) ^ 2) h1 h2
    (fun p hp => by
      obtain ⟨ρ, hρ, hs⟩ := Metric.isOpen_iff.1 hU p hp
      exact ⟨ρ, hρ, B, fun q hq => hB q (hbc (hs hq))⟩)
  simpa using h

/-- `Q_U(m, 0) = m` on `𝕌` for harmonic `m`. -/
theorem s7g_f2_Q0 {m m' φ : ℂ → ℂ} (hm : IsHarmonicU m φ) {s : ℂ} (hs : s ∈ upperHalf) :
    QfunU m (fun u => 0 * m' u) s = m s := by
  have hw0 := e64_t9_w0 m'
  have hinv : ∀ u, Function.invFun (id : ℂ → ℂ) u = u := fun u =>
    Function.leftInverse_invFun Function.injective_id u
  have hR : RnmFunU m (fun u => 0 * m' u) = m := by
    funext z
    unfold RnmFunU
    rw [hw0, hinv]
    simp [rhoVar_dz_id]
  unfold QfunU
  rw [hR, hw0, rhoVar_dz_id, id, (harmonicProjU_spec hm).1 s hs]
  simp

/-- The resolvent of a real function is real. -/
theorem s7g_f2_res_real (f : ℂ → ℝ) (z : ℂ) :
    conj (resolventOpU (fun u => (f u : ℂ)) z) = resolventOpU (fun u => (f u : ℂ)) z := by
  unfold resolventOpU
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [map_mul, Complex.conj_ofReal]

/-- `J_s(e) = ∫_𝕌 m(t) K̄_{e m'}(t, s)²` is `C²` near `0`. -/
theorem s7g_f2_Jreg {m' m φ : ℂ → ℂ} (hm : IsHarmonicU m φ) {C R0 : ℝ} (hC0 : 0 ≤ C)
    (hmB : IsBeltramiCoeff m' upperHalf C) (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf) (hR0p : 0 < R0)
    (hR0k : R0 * C < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {s : ℂ} (hs : s ∈ upperHalf) :
    ContDiffOn ℝ 2 (fun e => ∫ t in upperHalf, m t * kernelKbar (fun y => e * m' y) t s ^ 2)
      (ball 0 (min R0 (1 / (C + 1)))) := by
  have hU := measurableSet_upperHalf_aux
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨Mm, hMm0, hmb⟩ := harmonicU_bounded hm
  have hmc := harmonicU_continuousOn hm
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℂ → ℂ → ℂ, Ψ = fun P u =>
      m u * (dz (W P) u * dz (W P) (conj s) / (W P u - W P (conj s)) ^ 2) ^ 2 := ⟨_, rfl⟩
  have hc : ContinuousOn (fun p : (ℂ × ℂ) × ℂ => Ψ p.1 p.2) ((closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0) ×ˢ S) :=
    (s71_b2_cont hC0 hmB hms hmc hs hR0k hW hΨ).mono (prod_mono subset_rfl hSU)
  have hhol : ∀ u ∈ S, (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => Ψ (a, b) u) (ball (0 : ℂ) R0)) ∧
      ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => Ψ (a, b) u) (ball (0 : ℂ) R0) := fun u hu =>
    s71_b2_holo hC0 hmB hms hs hR0k hW hΨ (hSU hu)
  obtain ⟨M, hM⟩ := s71_b2_L1 hC0 hmB hms hmc hMm0 hmb hs hR0k hW hΨ
  have hM' : ∀ P ∈ closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0, ∫⁻ u in S, ‖Ψ P u‖ₑ ≤ ENNReal.ofReal M := by
    intro P hP
    obtain ⟨hi, hb⟩ := hM P hP
    calc _ ≤ ∫⁻ u in upperHalf, ‖Ψ P u‖ₑ := lintegral_mono_set hSU
      _ = ENNReal.ofReal (∫ u in upperHalf, ‖Ψ P u‖) := (ofReal_integral_norm_eq_lintegral_enorm hi).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb
  have hj2 := (s7g_f2_mixC2 (m := volume) hSm hc hhol hM').1
  refine ((s7g_f2_diagC2 hj2).mono (ball_subset_ball (min_le_left _ _))).congr fun e he => ?_
  have he' : ‖e‖ * C < 1 := by
    have h := lt_of_lt_of_le (mem_ball_zero_iff.1 he) (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg e]
  rw [← setIntegral_congr_set hnull]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  exact (s71_b2_diag hC0 hmB hW hΨ he' t).symm

/-- `ρ^{e m'}(s)` is `C²` near `0`. -/
theorem s7g_f2_Dreg {m' : ℂ → ℂ} {C R0 : ℝ} (hC0 : 0 ≤ C)
    (hmB : IsBeltramiCoeff m' upperHalf C) (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf) (hR0k : R0 * C < 1)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {s : ℂ} (hs : s ∈ upperHalf) :
    ContDiffOn ℝ 2 (fun e => rhoVar m' e s) (ball 0 (min R0 (1 / (C + 1)))) := by
  have hK := s7g_f2_Kreg hC0 hmB hms hW hs hs hR0k
  refine ((s7g_f2_diagC2 ((contDiffOn_const (c := (-4 : ℂ))).mul hK)).mono (ball_subset_ball (min_le_left _ _))).congr
    fun e he => ?_
  have he' : ‖e‖ * C < 1 := by
    have h := lt_of_lt_of_le (mem_ball_zero_iff.1 he) (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg e]
  show rhoVar m' e s = -4 * _
  rw [eq_6_1, s7g_f2_Kdiag hC0 hmB hW he']

/-- Wirtinger derivatives of `1 - c e ē`. -/
theorem s7g_f2_Cquad (c : ℂ) :
    dz (fun e : ℂ => 1 - c * (e * conj e)) = (fun y => -c * conj y) ∧
      dzbar (fun e : ℂ => 1 - c * (e * conj e)) = (fun y => -c * y) ∧
      dzbar (fun y : ℂ => -c * conj y) 0 = -c := by
  have hd : ∀ y : ℂ, HasFDerivAt (fun e : ℂ => 1 - c * (e * conj e))
      (-(c • (y • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap +
        conj y • ContinuousLinearMap.id ℝ ℂ))) y := by
    intro y
    have h1 : HasFDerivAt (fun e : ℂ => e * conj e)
        (y • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap + conj y • ContinuousLinearMap.id ℝ ℂ) y :=
      (hasFDerivAt_id y).mul (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
    exact ((h1.const_mul c).const_sub 1)
  have hc : ∀ y : ℂ, HasFDerivAt (fun y : ℂ => -c * conj y)
      ((-c) • (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) y := fun y =>
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.const_mul (-c)
  refine ⟨funext fun y => ?_, funext fun y => ?_, ?_⟩
  · unfold dz
    rw [(hd y).fderiv]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, ContinuousLinearMap.id_apply, map_one,
      Complex.conj_I, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  · unfold dzbar
    rw [(hd y).fderiv]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, ContinuousLinearMap.id_apply, map_one,
      Complex.conj_I, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  · unfold dzbar
    rw [(hc 0).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
      Complex.conj_I, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- `∂_z̄∂_z` of a constant multiple. -/
theorem s7g_f2_wconst {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : ContDiffOn ℝ 2 f (ball 0 r)) (c : ℂ) :
    dzbar (dz fun e => c * f e) 0 = c * dzbar (dz f) 0 := by
  have h := s7g_f2_wmul hr (contDiffOn_const (c := c)) hf
  have hz : dz (fun _ : ℂ => c) = fun _ => 0 := funext fun y => by simp [dz]
  have hzb : dzbar (fun _ : ℂ => c) = fun _ => 0 := funext fun y => by simp [dzbar]
  rw [h, hz, hzb]
  simp [dzbar]

/-- Quasisymmetry across `ℝ`: `|W s - W s̄| ≤ (λ + λ²) d(W s̄, W(𝕌))` for `s ∈ 𝕌` (`s7g_r3_wqs` twice, through
the foot `Re s`). -/
theorem s7g_f2_wd {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (hs : W '' univ = univ) {s : ℂ}
    (hsU : s ∈ upperHalf) :
    ‖W s - W (conj s)‖ ≤ (lambdaInv K + lambdaInv K ^ 2) * infDist (W (conj s)) (W '' upperHalf) := by
  have hsim : 0 < s.im := hsU
  have hlam : 0 < lambdaInv K := zero_lt_one.trans_le (td_one_le_lambdaInv hW.2.1)
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℂ, m0 = (s.re : ℂ) := ⟨_, rfl⟩
  have hd0 : ‖m0 - conj s‖ = s.im := by
    have e : m0 - conj s = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [hm0]
    rw [e, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hsim.le]
  have hd1 : ‖s - m0‖ = s.im := by
    have e : s - m0 = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [hm0]
    rw [e, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hsim.le]
  have hd2 : ‖conj s - m0‖ = s.im := by rw [norm_sub_rev]; exact hd0
  have hne : (W '' upperHalf).Nonempty := ⟨W I, I, by show (0 : ℝ) < I.im; simp, rfl⟩
  have h1 : ‖W m0 - W (conj s)‖ ≤ lambdaInv K * infDist (W (conj s)) (W '' upperHalf) := by
    rw [← div_le_iff₀' hlam]
    refine (le_infDist hne).2 fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    have hu' : 0 < u.im := hu
    have hle : ‖m0 - conj s‖ ≤ ‖u - conj s‖ := by
      rw [hd0]
      refine le_trans ?_ (abs_im_le_norm _)
      rw [Complex.sub_im, Complex.conj_im, abs_of_pos (by linarith)]
      linarith
    have hpos : 0 < ‖u - conj s‖ := lt_of_lt_of_le (by rw [hd0]; exact hsim) hle
    have h := s7g_r3_wqs hW hs hle hpos
    rw [div_le_iff₀' hlam, dist_eq_norm, norm_sub_rev (W (conj s)) (W u)]
    exact h
  have h2 : ‖W s - W m0‖ ≤ lambdaInv K * ‖W (conj s) - W m0‖ :=
    s7g_r3_wqs hW hs (by rw [hd1, hd2]) (by rw [hd2]; exact hsim)
  calc ‖W s - W (conj s)‖ ≤ ‖W s - W m0‖ + ‖W m0 - W (conj s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ lambdaInv K * ‖W (conj s) - W m0‖ + ‖W m0 - W (conj s)‖ := by gcongr
    _ = (lambdaInv K + 1) * ‖W m0 - W (conj s)‖ := by rw [norm_sub_rev (W (conj s))]; ring
    _ ≤ (lambdaInv K + 1) * (lambdaInv K * infDist (W (conj s)) (W '' upperHalf)) := by gcongr
    _ = _ := by ring

/-- **R5a.** For a `K`-q.c. `W` of `ℂ` with `(1 - k'²)|∂W|² ≤ J_W` off `ℝ` and a harmonic `m`:
`∫_𝕌 |∂W(z̄)|² (∫_𝕌 |m||∂W|²/|W u - W z̄|⁴)² d(W z̄, W(𝕌))² ≤ c₀³ π² C₃ ‖m‖²` (change of variables, Cauchy–Schwarz
against `∫_{W(𝕌)} |X - Y|⁻⁴ ≤ π/d²`, `s7g_r2_side`, and the transfer `C₃`). -/
theorem s7g_f2_R5a {W : ℂ → ℂ} {K k' : ℝ} (hK : IsKQC W univ K) (hs : W '' univ = univ)
    (hC : ContDiffOn ℝ 1 W {u : ℂ | u.im ≠ 0}) (hk0 : 0 ≤ k') (hk1 : k' < 1)
    (hker : ∀ y : ℂ, y.im ≠ 0 → (1 - k' ^ 2) * ‖dz W y‖ ^ 2 ≤ jacobian W y) {C3 : ℝ≥0∞}
    (hC3 : ∀ W : ℂ → ℂ, IsKQC W univ K → W '' univ = univ → ContDiffOn ℝ 1 W upperHalf → ∀ m φ : ℂ → ℂ,
      DifferentiableOn ℂ φ upperHalf → (∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) →
      (∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (jacobian W u) /
          ENNReal.ofReal (infDist (W u) (W '' upperHalf)ᶜ) ^ 2) ≤
        C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u))
    {m φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hm : ∀ u ∈ upperHalf, m u = (u - conj u) ^ 2 / 2 * conj (φ u)) :
    (∫⁻ z in upperHalf, ‖dz W (conj z)‖ₑ ^ 2 *
        (∫⁻ u in upperHalf, ‖m u‖ₑ * ‖dz W u‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4) ^ 2 *
          ENNReal.ofReal (infDist (W (conj z)) (W '' upperHalf)) ^ 2) ≤
      ENNReal.ofReal ((1 - k' ^ 2)⁻¹) ^ 3 * ENNReal.ofReal π ^ 2 *
        (C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  have hinj : Function.Injective W := by rw [← he]; exact e.injective
  set L : Set ℂ := {u : ℂ | u.im < 0} with hLd
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen L := isOpen_lt Complex.continuous_im continuous_const
  have hKU : IsKQC W upperHalf K := nx_isKQC_restrict hK hU (subset_univ _)
  have hKL : IsKQC W L K := nx_isKQC_restrict hK hLo (subset_univ _)
  set Ω : Set ℂ := W '' upperHalf with hΩd
  set Ωs : Set ℂ := W '' L with hΩsd
  have hΩo : IsOpen Ω := by rw [hΩd, ← he]; exact e.isOpenMap _ hU
  have hΩso : IsOpen Ωs := by rw [hΩsd, ← he]; exact e.isOpenMap _ hLo
  have hdisj : Disjoint Ωs Ω := by
    rw [disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ ⟨u, hu, huw⟩
    have := hinj huw
    have h1 : 0 < u.im := hu
    have h2 : w.im < 0 := hw
    rw [this] at h1
    linarith
  have hΩsc : Ωs ⊆ Ωᶜ := fun Y hY hYΩ => disjoint_left.1 hdisj hY hYΩ
  have hΩsne : Ωs.Nonempty := ⟨W (-I), -I, by show (-I).im < 0; simp, rfl⟩
  have hΩne : Ω.Nonempty := ⟨W I, I, by show (0 : ℝ) < I.im; simp, rfl⟩
  set n : ℂ → ℝ≥0∞ := fun u => ‖m u‖ₑ with hn
  set f : ℂ → ℝ≥0∞ := Ω.piecewise (fun X => n (e.symm X)) 0 with hfd
  have hfm : Measurable f := s7g_r1_pw_meas e he hU (s7g_r1_m_cont hφ hm)
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((1 - k' ^ 2)⁻¹) with hc0
  have hc : 0 < 1 - k' ^ 2 := by nlinarith
  have hb : ∀ y : ℂ, y.im ≠ 0 → ‖dz W y‖ₑ ^ 2 ≤ c0 * ENNReal.ofReal (jacobian W y) := by
    intro y hy
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hker y hy
  set H : ℂ → ℝ≥0∞ := fun Y => ∫⁻ X in Ω, f X / ‖X - Y‖ₑ ^ 4 with hHd
  set Φ : ℂ → ℝ≥0∞ := fun Y => ∫⁻ X in Ω, f X ^ 2 / ‖X - Y‖ₑ ^ 4 with hΦd
  -- (a) the inner integral through the change of variables on `𝕌`
  have ha : ∀ z ∈ upperHalf, (∫⁻ u in upperHalf, ‖m u‖ₑ * ‖dz W u‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4) ≤
      c0 * H (W (conj z)) := by
    intro z _
    have hinner : (∫⁻ u in upperHalf, ENNReal.ofReal (jacobian W u) * (n u / ‖W u - W (conj z)‖ₑ ^ 4)) =
        H (W (conj z)) :=
      s7g_r1_cov e he hKU n (fun X t => t / ‖X - W (conj z)‖ₑ ^ 4)
    rw [← hinner, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hU.measurableSet fun u hu => ?_
    have hui : u.im ≠ 0 := ne_of_gt hu
    calc ‖m u‖ₑ * ‖dz W u‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4
        ≤ ‖m u‖ₑ * (c0 * ENNReal.ofReal (jacobian W u)) / ‖W u - W (conj z)‖ₑ ^ 4 := by
          gcongr
          exact hb u hui
      _ = c0 * (ENNReal.ofReal (jacobian W u) * (n u / ‖W u - W (conj z)‖ₑ ^ 4)) := by
          simp only [hn, div_eq_mul_inv]
          ring
  -- (b) Cauchy–Schwarz against `∫_Ω |X - Y|⁻⁴ ≤ π/d²`
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / (2 : ℝ))) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hb2 : ∀ Y ∈ Ωs, H Y ^ 2 * ENNReal.ofReal (infDist Y Ω) ^ 2 ≤ ENNReal.ofReal π * Φ Y := by
    intro Y hY
    have hd : 0 < infDist Y Ω := by
      rcases (infDist_nonneg (x := Y) (s := Ω)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hcl : Y ∈ closure Ω := (mem_closure_iff_infDist_zero hΩne).2 h.symm
        exact disjoint_left.1 (hdisj.closure_right hΩso) hY hcl
    have hR : ∀ X ∈ Ω, infDist Y Ω ≤ ‖X - Y‖ := fun X hX => by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hX
    have hout : (∫⁻ X in Ω, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4) ≤ ENNReal.ofReal (π / infDist Y Ω ^ 2) :=
      r24_lintegral_outside hd hR
    have hmA : AEMeasurable (fun X => f X / ‖X - Y‖ₑ ^ 2) (volume.restrict Ω) :=
      (hfm.div (by fun_prop)).aemeasurable
    have hmB : AEMeasurable (fun X : ℂ => (‖X - Y‖ₑ ^ 2)⁻¹) (volume.restrict Ω) :=
      (by fun_prop : Measurable fun X : ℂ => (‖X - Y‖ₑ ^ 2)⁻¹).aemeasurable
    have hcs : (∫⁻ X in Ω, f X / ‖X - Y‖ₑ ^ 2 * (‖X - Y‖ₑ ^ 2)⁻¹) ≤
        (∫⁻ X in Ω, (f X / ‖X - Y‖ₑ ^ 2) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ X in Ω, ((‖X - Y‖ₑ ^ 2)⁻¹) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hmA hmB
    have e0 : H Y = ∫⁻ X in Ω, f X / ‖X - Y‖ₑ ^ 2 * (‖X - Y‖ₑ ^ 2)⁻¹ := by
      simp only [hHd]
      congr 1
      funext X
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, show ‖X - Y‖ₑ ^ 4 = ‖X - Y‖ₑ ^ 2 * ‖X - Y‖ₑ ^ 2 by ring,
        ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top enorm_ne_top)) (Or.inl (ENNReal.pow_ne_top enorm_ne_top))]
    have e1 : (∫⁻ X in Ω, (f X / ‖X - Y‖ₑ ^ 2) ^ (2 : ℝ)) = Φ Y := by
      simp only [hΦd]
      congr 1
      funext X
      rw [ENNReal.rpow_two]
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← pow_mul]
    have e2 : (∫⁻ X in Ω, ((‖X - Y‖ₑ ^ 2)⁻¹) ^ (2 : ℝ)) = ∫⁻ X in Ω, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4 := by
      congr 1
      funext X
      rw [ENNReal.rpow_two, ← ENNReal.inv_pow, ← ENNReal.inv_pow, ← pow_mul, enorm_eq_nnnorm]
    rw [← e0, e1, e2] at hcs
    have hd2 : ENNReal.ofReal (infDist Y Ω) ^ 2 ≠ 0 := pow_ne_zero 2 (ENNReal.ofReal_pos.2 hd).ne'
    have hd2' : ENNReal.ofReal (infDist Y Ω) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    calc H Y ^ 2 * ENNReal.ofReal (infDist Y Ω) ^ 2
        ≤ (Φ Y ^ (1 / (2 : ℝ)) * (∫⁻ X in Ω, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4) ^ (1 / (2 : ℝ))) ^ 2 *
            ENNReal.ofReal (infDist Y Ω) ^ 2 := by gcongr
      _ = Φ Y * (∫⁻ X in Ω, (‖X - Y‖₊ : ℝ≥0∞)⁻¹ ^ 4) * ENNReal.ofReal (infDist Y Ω) ^ 2 := by
          rw [mul_pow, hsq, hsq]
      _ ≤ Φ Y * ENNReal.ofReal (π / infDist Y Ω ^ 2) * ENNReal.ofReal (infDist Y Ω) ^ 2 := by gcongr
      _ = ENNReal.ofReal π * Φ Y := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hd.le, mul_assoc,
            ENNReal.div_mul_cancel hd2 hd2', mul_comm]
  -- (c) the outer integral, through `conj` and the change of variables on `𝕃`
  have hc1 : (∫⁻ z in upperHalf, ‖dz W (conj z)‖ₑ ^ 2 *
        (∫⁻ u in upperHalf, ‖m u‖ₑ * ‖dz W u‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4) ^ 2 *
          ENNReal.ofReal (infDist (W (conj z)) (W '' upperHalf)) ^ 2) ≤
      ∫⁻ z in upperHalf, c0 ^ 2 * ENNReal.ofReal π * (‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z))) := by
    refine setLIntegral_mono' hU.measurableSet fun z hz => ?_
    have hzi : (conj z).im < 0 := by
      have : 0 < z.im := hz
      rw [Complex.conj_im]
      linarith
    have hY : W (conj z) ∈ Ωs := ⟨conj z, hzi, rfl⟩
    calc ‖dz W (conj z)‖ₑ ^ 2 *
          (∫⁻ u in upperHalf, ‖m u‖ₑ * ‖dz W u‖ₑ ^ 2 / ‖W u - W (conj z)‖ₑ ^ 4) ^ 2 *
            ENNReal.ofReal (infDist (W (conj z)) (W '' upperHalf)) ^ 2
        ≤ ‖dz W (conj z)‖ₑ ^ 2 * (c0 * H (W (conj z))) ^ 2 *
            ENNReal.ofReal (infDist (W (conj z)) Ω) ^ 2 := by
          gcongr
          exact ha z hz
      _ = c0 ^ 2 * ‖dz W (conj z)‖ₑ ^ 2 * (H (W (conj z)) ^ 2 * ENNReal.ofReal (infDist (W (conj z)) Ω) ^ 2) := by
          ring
      _ ≤ c0 ^ 2 * ‖dz W (conj z)‖ₑ ^ 2 * (ENNReal.ofReal π * Φ (W (conj z))) := by
          exact mul_le_mul_right (hb2 _ hY) _
      _ = _ := by ring
  have hc2 : (∫⁻ z in upperHalf, ‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z))) ≤ c0 * ∫⁻ Y in Ωs, Φ Y := by
    calc (∫⁻ z in upperHalf, ‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z)))
        ≤ ∫⁻ z in upperHalf, c0 * (ENNReal.ofReal (jacobian W (conj z)) * Φ (W (conj z))) := by
          refine setLIntegral_mono' hU.measurableSet fun z hz => ?_
          have hzi : (conj z).im ≠ 0 := by
            have : 0 < z.im := hz
            rw [Complex.conj_im]
            linarith
          calc ‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z))
              ≤ c0 * ENNReal.ofReal (jacobian W (conj z)) * Φ (W (conj z)) := by
                gcongr
                exact hb _ hzi
            _ = _ := by ring
      _ = c0 * ∫⁻ w in L, ENNReal.ofReal (jacobian W w) * Φ (W w) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          have hemb := Complex.conjLIE.toHomeomorph.measurableEmbedding
          rw [hLd, ← s7g_r1_conj_image, ← gzE_conj_measurePreserving.setLIntegral_comp_emb hemb _ upperHalf]
      _ = c0 * ∫⁻ Y in Ωs, Φ Y := by
          congr 1
          exact s7g_r1_cov e he hKL (fun _ => (0 : ℝ≥0∞)) (fun Y _ => Φ Y)
  -- (d) Schur's side estimate
  have hd2 : (∫⁻ Y in Ωs, Φ Y) ≤ ENNReal.ofReal π * ∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2 := by
    have hmeas : AEMeasurable (Function.uncurry fun (Y X : ℂ) => f X ^ 2 / ‖X - Y‖ₑ ^ 4)
        ((volume.restrict Ωs).prod (volume.restrict Ω)) :=
      (((hfm.comp measurable_snd).pow_const 2).div
        (show Measurable fun p : ℂ × ℂ => ‖p.2 - p.1‖ₑ ^ 4 by fun_prop)).aemeasurable
    have hswap : (∫⁻ Y in Ωs, Φ Y) = ∫⁻ X in Ω, ∫⁻ Y in Ωs, f X ^ 2 / ‖X - Y‖ₑ ^ 4 :=
      lintegral_lintegral_swap hmeas
    rw [hswap]
    exact s7g_r2_side hΩo hΩsc hΩsne f
  -- (e) the transfer
  have he5 : (∫⁻ X in Ω, f X ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2) ≤
      C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) := by
    rw [← s7g_r1_cov e he hKU n (fun X t => t ^ 2 / ENNReal.ofReal (infDist X Ωᶜ) ^ 2)]
    refine le_trans (le_of_eq ?_) (hC3 W hK hs (hC.mono fun u hu => ne_of_gt hu) m φ hφ hm)
    refine setLIntegral_congr_fun hU.measurableSet fun u _ => ?_
    simp only [hn, div_eq_mul_inv]
    ring
  have hcπ : c0 ^ 2 * ENNReal.ofReal π ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  calc _ ≤ ∫⁻ z in upperHalf, c0 ^ 2 * ENNReal.ofReal π * (‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z))) := hc1
    _ = c0 ^ 2 * ENNReal.ofReal π * ∫⁻ z in upperHalf, ‖dz W (conj z)‖ₑ ^ 2 * Φ (W (conj z)) :=
        lintegral_const_mul' _ _ hcπ
    _ ≤ c0 ^ 2 * ENNReal.ofReal π * (c0 * (ENNReal.ofReal π *
          (C3 * ∫⁻ u in upperHalf, ‖m u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)))) := by
        gcongr
        exact hc2.trans (by gcongr; exact hd2.trans (by gcongr))
    _ = _ := by ring

/-- Reflection between two normalized solutions: if `\overline{σ'(z̄)} = σ(z)` off `ℝ` and `σ` has unique normalized
solution `f`, then `f(z̄) = \overline{f'(z)}` (the argument of `qcv_ns_conj_comm`, with two coefficients). -/
theorem s7g_f2_nsconj {σ σ' f f' : ℂ → ℂ} (hsym : ∀ z : ℂ, z.im ≠ 0 → conj (σ' (conj z)) = σ z)
    (hN' : IsNormalizedSolution f' σ') (huniq : ∀ g : ℂ → ℂ, IsNormalizedSolution g σ → g = f) (z : ℂ) :
    f (conj z) = conj (f' z) := by
  obtain ⟨⟨K, hK⟩, hs, h0, h1, hd⟩ := hN'
  have hgK : IsKQC (fun w => conj (f' (conj w))) univ K := by
    have h := abR_x_isKQC_conj hK
    rwa [preimage_univ] at h
  have hgs : (fun w => conj (f' (conj w))) '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    have hw : conj w ∈ f' '' univ := by
      rw [hs]
      exact mem_univ _
    obtain ⟨v, -, hv⟩ := hw
    exact ⟨conj v, mem_univ _, by simp only [Complex.conj_conj, hv]⟩
  have hnull : ∀ᵐ w : ℂ, w ∉ {v : ℂ | v.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  have hgd : ∀ᵐ w, complexDilatation (fun w => conj (f' (conj w))) w = σ w := by
    filter_upwards [gzE_conj_measurePreserving.quasiMeasurePreserving.ae hd, hnull] with w hw1 hw2
    rw [QCV.qcv_dilatation_conj, hw1]
    exact hsym w hw2
  have hg : IsNormalizedSolution (fun w => conj (f' (conj w))) σ :=
    ⟨⟨_, hgK⟩, hgs, by simp [h0], by simp [h1], hgd⟩
  have h := congrFun (huniq _ hg) (conj z)
  rw [← h, Complex.conj_conj]

/-- The reflection symmetry of the `W`-family: `W_{(a,b)}(z̄) = \overline{W_{(b̄,ā)}(z)}`. -/
theorem s7g_f2_Wsym {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {P : ℂ × ℂ} (hP : max ‖P.1‖ ‖P.2‖ * k < 1) (z : ℂ) :
    W P (conj z) = conj (W (conj P.2, conj P.1) z) := by
  obtain ⟨-, -, -, -, hcomb⟩ := wr_U_coeffs hk hmk hms
  have hP' : max ‖conj P.2‖ ‖conj P.1‖ * k < 1 := by
    rw [Complex.norm_conj, Complex.norm_conj, max_comm]
    exact hP
  obtain ⟨k1, hk1, hb1⟩ := hcomb P.1 P.2 hP
  obtain ⟨hb1', hk10, hk11⟩ := wr_coeff_nonneg hk1 hb1
  obtain ⟨k2, hk2, hb2⟩ := hcomb (conj P.2) (conj P.1) hP'
  obtain ⟨hb2', hk20, hk21⟩ := wr_coeff_nonneg hk2 hb2
  obtain ⟨F0, -, -, huniq0⟩ := thm13_7_normalized_existence hk10 hk11 hb1'
  have hN := QCV.qcv_ns_spec hk10 hk11 hb1'
  have hN' := QCV.qcv_ns_spec hk20 hk21 hb2'
  have hsym : ∀ x : ℂ, x.im ≠ 0 → conj ((fun u => conj P.2 * (if 0 < u.im then m' u else 0) +
      conj P.1 * (if u.im < 0 then conj (m' (conj u)) else 0)) (conj x)) =
      (fun u => P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0)) x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hc : 0 < (conj x).im := by rw [Complex.conj_im]; linarith
      have h2 : ¬ (conj x).im < 0 := by rw [Complex.conj_im]; linarith
      have h3 : ¬ 0 < x.im := by linarith
      simp only [hc, h2, h3, h, if_true, if_false, Complex.conj_conj, map_mul, map_add, map_zero, mul_zero,
        add_zero, zero_add]
    · have hc : (conj x).im < 0 := by rw [Complex.conj_im]; linarith
      have h2 : ¬ 0 < (conj x).im := by rw [Complex.conj_im]; linarith
      have h3 : ¬ x.im < 0 := by linarith
      simp only [hc, h2, h3, h, if_true, if_false, Complex.conj_conj, map_mul, map_add, map_zero, mul_zero,
        add_zero, zero_add]
  rw [hW]
  exact s7g_f2_nsconj hsym hN' (fun g hg => (huniq0 g hg).trans (huniq0 _ hN).symm) z

/-- `∂W_{(a,b)}(z̄) = \overline{∂W_{(b̄,ā)}(z)}` off `ℝ`. -/
theorem s7g_f2_dWsym {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {P : ℂ × ℂ} (hP : max ‖P.1‖ ‖P.2‖ * k < 1) {z : ℂ} (hz : z.im ≠ 0) :
    dz (W P) (conj z) = conj (dz (W (conj P.2, conj P.1)) z) := by
  obtain ⟨hC, -, -⟩ := e64_W_basic hk hmk hms hW
  have hP' : max ‖(conj P.2, conj P.1).1‖ ‖(conj P.2, conj P.1).2‖ * k < 1 := by
    show max ‖conj P.2‖ ‖conj P.1‖ * k < 1
    rw [Complex.norm_conj, Complex.norm_conj, max_comm]
    exact hP
  have hΩ : IsOpen ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) :=
    (isOpen_lt (((continuous_norm.comp continuous_fst).max (continuous_norm.comp continuous_snd)).mul
      continuous_const) continuous_const).prod (isOpen_ne_fun Complex.continuous_im continuous_const)
  have hd : DifferentiableAt ℝ (W (conj P.2, conj P.1)) (conj (conj z)) := by
    rw [Complex.conj_conj]
    have h := (hC.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds (show (((conj P.2, conj P.1), z) : (ℂ × ℂ) × ℂ) ∈ _ from ⟨hP', hz⟩))
    exact DifferentiableAt.comp (g := fun q : (ℂ × ℂ) × ℂ => W q.1 q.2) z h
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hfun : W P = fun w => conj (W (conj P.2, conj P.1) (conj w)) := funext fun w => by
    rw [← s7g_f2_Wsym hk hmk hms hW hP, Complex.conj_conj]
  rw [hfun, (abR_x_dz_dzbar_conj hd).2.1, Complex.conj_conj]

/-- `∂W` is measurable (for any `W`). -/
theorem s7g_f2_dzmeas (W : ℂ → ℂ) : Measurable (dz W) := by
  unfold dz
  fun_prop

/-- `|K(t, s)|² = |∂W(s̄)|² |∂W(t)|²/|W t - W s̄|⁴` in `ℝ≥0∞` (off the diagonal of `W`). -/
theorem s7g_f2_Knorm {W : ℂ → ℂ} {t s : ℂ} (hne : W t - W (conj s) ≠ 0) :
    ‖dz W t * dz W (conj s) / (W t - W (conj s)) ^ 2‖ₑ ^ 2 =
      ‖dz W (conj s)‖ₑ ^ 2 * (‖dz W t‖ₑ ^ 2 / ‖W t - W (conj s)‖ₑ ^ 4) := by
  have h1 : ‖dz W t * dz W (conj s) / (W t - W (conj s)) ^ 2‖ₑ =
      ‖dz W t‖ₑ * ‖dz W (conj s)‖ₑ / ‖W t - W (conj s)‖ₑ ^ 2 := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_div, nnnorm_mul,
      nnnorm_pow, ENNReal.coe_div (pow_ne_zero 2 (nnnorm_ne_zero_iff.2 hne)), ENNReal.coe_mul, ENNReal.coe_pow]
  rw [h1, div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ENNReal.inv_pow, ← pow_mul, ENNReal.inv_pow]
  ring

/-- `|c|²|b|² |(a b/z²)⁻¹| = |a||b||z|²` when `|c| = |a|` and `a, b ≠ 0`. -/
theorem s7g_f2_cnorm {a b c z : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : ‖c‖ = ‖a‖) :
    ‖c‖ₑ ^ 2 * ‖b‖ₑ ^ 2 * ‖(a * b / z ^ 2)⁻¹‖ₑ = ‖a‖ₑ * ‖b‖ₑ * ‖z‖ₑ ^ 2 := by
  have e : ∀ x : ℂ, ‖x‖ₑ = ENNReal.ofReal ‖x‖ := fun x => (ofReal_norm x).symm
  simp only [e]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
  rw [norm_inv, norm_div, norm_mul, norm_pow, hc, inv_div]
  field_simp

/-- The `W`-data on the closed polydisc: `K₀`-q.c. onto `ℂ`, `C¹` off `ℝ`, `(1 - (2Rk)²)|∂W|² ≤ J` off `ℝ`. -/
theorem s7g_f2_Wdata {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) {P : ℂ × ℂ}
    (hP : P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :
    IsKQC (W P) univ ((1 + 2 * R * k) / (1 - 2 * R * k)) ∧ W P '' univ = univ ∧
      ContDiffOn ℝ 1 (W P) {u : ℂ | u.im ≠ 0} ∧
      ∀ y : ℂ, y.im ≠ 0 → (1 - (2 * R * k) ^ 2) * ‖dz (W P) y‖ ^ 2 ≤ jacobian (W P) y := by
  have hzero : IsBeltramiCoeff (fun _ : ℂ => (0 : ℂ)) upperHalf k :=
    ⟨aestronglyMeasurable_const, Eventually.of_forall fun _ => by simpa using hk⟩
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
  rw [hWP]
  exact s7g_r1_W hk hmk hzero hms contDiffOn_const hR hRk rfl hP'

/-- **R5**: the uniform `L¹` bound of the line-1 triple integrand on the closed polydisc. With
`P* = (P̄₂, P̄₁)`, `|∂W_{P*}(s̄)| = |∂W_P(s)|` and `|W_P s - W_P s̄| = |W_{P*} s - W_{P*} s̄|` (`s7g_f2_Wsym`), the
`(t₁, t₂)`-integral at `s` is `≤ L² G_ν(s) G_μ*(s)` (`s7g_f2_wd` twice), and Hölder with `s7g_f2_R5a` closes. -/
theorem s7g_f2_R5 {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {mμ φμ mν φν : ℂ → ℂ} (hμh : IsHarmonicU mμ φμ) (hνh : IsHarmonicU mν φν)
    (hfμ : ∫⁻ u in upperHalf, ‖mμ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (hfν : ∫⁻ u in upperHalf, ‖mν u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    {R : ℝ} (hR : 0 ≤ R) (hRk : 2 * R * k < 1) :
    ∃ M : ℝ, ∀ P ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R,
      (∫⁻ s in upperHalf, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
        ‖mμ t₁‖ₑ * ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
          (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
          ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) ≤ ENNReal.ofReal M := by
  have hU := measurableSet_upperHalf_aux
  set K0 : ℝ := (1 + 2 * R * k) / (1 - 2 * R * k) with hK0
  have hk'0 : 0 ≤ 2 * R * k := by positivity
  have hK1 : 1 ≤ K0 := by
    rw [hK0, le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨C3, hC3t, hC3⟩ := s7g_transfer hK1
  set L : ℝ := lambdaInv K0 + lambdaInv K0 ^ 2 with hLd
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((1 - (2 * R * k) ^ 2)⁻¹) with hc0
  set Bμ : ℝ≥0∞ := c0 ^ 3 * ENNReal.ofReal π ^ 2 * (C3 * ∫⁻ u in upperHalf, ‖mμ u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u))
    with hBμ
  set Bν : ℝ≥0∞ := c0 ^ 3 * ENNReal.ofReal π ^ 2 * (C3 * ∫⁻ u in upperHalf, ‖mν u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u))
    with hBν
  have hBμt : Bμ ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.mul_lt_top hC3t hfμ)).ne
  have hBνt : Bν ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.mul_lt_top hC3t hfν)).ne
  have hMt : ENNReal.ofReal (L ^ 2) * (Bν ^ (1 / (2 : ℝ)) * Bμ ^ (1 / (2 : ℝ))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBνt) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBμt))
  refine ⟨(ENNReal.ofReal (L ^ 2) * (Bν ^ (1 / (2 : ℝ)) * Bμ ^ (1 / (2 : ℝ)))).toReal, fun P hP => ?_⟩
  rw [ENNReal.ofReal_toReal hMt]
  set Ps : ℂ × ℂ := (conj P.2, conj P.1) with hPsd
  have hPs : Ps ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R := by
    obtain ⟨h1, h2⟩ := hP
    refine ⟨?_, ?_⟩
    · show conj P.2 ∈ closedBall (0 : ℂ) R
      rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h2
    · show conj P.1 ∈ closedBall (0 : ℂ) R
      rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h1
  have hRk1 : R * k < 1 := by nlinarith
  have hPk : max ‖P.1‖ ‖P.2‖ * k < 1 := e64_polydisc_sub hk hRk1 hP
  have hPsk : max ‖Ps.1‖ ‖Ps.2‖ * k < 1 := e64_polydisc_sub hk hRk1 hPs
  have hPP : (conj Ps.2, conj Ps.1) = P := by
    rw [hPsd]
    simp only [Complex.conj_conj]
  obtain ⟨hKP, hsP, hCP, hkerP⟩ := s7g_f2_Wdata hk hmk hms hW hR hRk hP
  obtain ⟨hKQ, hsQ, hCQ, hkerQ⟩ := s7g_f2_Wdata hk hmk hms hW hR hRk hPs
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hmk hms hW
  have hWc : Continuous (W P) := continuousOn_univ.1 hKP.2.2.1.1
  have hWcQ : Continuous (W Ps) := continuousOn_univ.1 hKQ.2.2.1.1
  -- the reflection identities
  have hWs1 : ∀ s, W Ps (conj s) = conj (W P s) := fun s => by
    have h := s7g_f2_Wsym hk hmk hms hW hPsk s
    rwa [hPP] at h
  have hWs2 : ∀ s, W Ps s = conj (W P (conj s)) := fun s => by
    have h := s7g_f2_Wsym hk hmk hms hW hPk s
    rw [h, Complex.conj_conj]
  have hdzs : ∀ s : ℂ, s.im ≠ 0 → dz (W Ps) (conj s) = conj (dz (W P) s) := fun s hs => by
    have h := s7g_f2_dWsym hk hmk hms hW hPsk hs
    rwa [hPP] at h
  have hdz0 : ∀ y : ℂ, y.im ≠ 0 → dz (W P) y ≠ 0 := by
    intro y hy h0
    rcases lt_or_gt_of_ne hy with h | h
    · obtain ⟨hb, hJ⟩ := e64_t5_beltrami hk hmk hms hW hPk h
      unfold jacobian at hJ
      rw [hb, h0] at hJ
      simp at hJ
    · obtain ⟨hb, hJ⟩ := s71_b2_beltrami hk hmk hms hW hPk h
      unfold jacobian at hJ
      rw [hb, h0] at hJ
      simp at hJ
  have hμc := harmonicU_continuousOn hμh
  have hνc := harmonicU_continuousOn hνh
  -- the two weights
  set Iν : ℂ → ℝ≥0∞ := fun s => ∫⁻ t in upperHalf, ‖mν t‖ₑ * ‖dz (W P) t‖ₑ ^ 2 / ‖W P t - W P (conj s)‖ₑ ^ 4
    with hIν
  set Iμ : ℂ → ℝ≥0∞ := fun s => ∫⁻ t in upperHalf, ‖mμ t‖ₑ * ‖dz (W Ps) t‖ₑ ^ 2 / ‖W Ps t - W Ps (conj s)‖ₑ ^ 4
    with hIμ
  set Gν : ℂ → ℝ≥0∞ := fun s => ‖dz (W P) (conj s)‖ₑ * Iν s *
    ENNReal.ofReal (infDist (W P (conj s)) (W P '' upperHalf)) with hGν
  set Gμ : ℂ → ℝ≥0∞ := fun s => ‖dz (W Ps) (conj s)‖ₑ * Iμ s *
    ENNReal.ofReal (infDist (W Ps (conj s)) (W Ps '' upperHalf)) with hGμ
  -- the kernel integral against a weight
  have hA : ∀ {Q : ℂ × ℂ} {m : ℂ → ℂ}, Continuous (W Q) → ContinuousOn m upperHalf →
      (∀ t ∈ upperHalf, ∀ s ∈ upperHalf, W Q t - W Q (conj s) ≠ 0) → ∀ s ∈ upperHalf,
      (∫⁻ t in upperHalf, ‖m t‖ₑ * ‖dz (W Q) t * dz (W Q) (conj s) / (W Q t - W Q (conj s)) ^ 2‖ₑ ^ 2) =
        ‖dz (W Q) (conj s)‖ₑ ^ 2 *
          ∫⁻ t in upperHalf, ‖m t‖ₑ * ‖dz (W Q) t‖ₑ ^ 2 / ‖W Q t - W Q (conj s)‖ₑ ^ 4 := by
    intro Q m _ _ hne s hs
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    refine setLIntegral_congr_fun hU fun t ht => ?_
    rw [s7g_f2_Knorm (hne t ht s hs), mul_div_assoc]
    ring
  have hneP : ∀ t ∈ upperHalf, ∀ s ∈ upperHalf, W P t - W P (conj s) ≠ 0 := by
    intro t ht s hs h
    have := hinj P hPk (sub_eq_zero.1 h)
    have h1 : 0 < t.im := ht
    have h2 : 0 < s.im := hs
    have h3 := congrArg Complex.im this
    rw [Complex.conj_im] at h3
    linarith
  have hneQ : ∀ t ∈ upperHalf, ∀ s ∈ upperHalf, W Ps t - W Ps (conj s) ≠ 0 := by
    intro t ht s hs h
    have := hinj Ps hPsk (sub_eq_zero.1 h)
    have h1 : 0 < t.im := ht
    have h2 : 0 < s.im := hs
    have h3 := congrArg Complex.im this
    rw [Complex.conj_im] at h3
    linarith
  -- the pointwise `(t₁, t₂)`-bound
  have hpt : ∀ s ∈ upperHalf,
      (∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
        ‖mμ t₁‖ₑ * ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
          (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
          ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) ≤
        ENNReal.ofReal (L ^ 2) * (Gν s * Gμ s) := by
    intro s hs
    have hsi : s.im ≠ 0 := ne_of_gt hs
    have hsc : (conj s).im ≠ 0 := by
      have : 0 < s.im := hs
      rw [Complex.conj_im]
      linarith
    set c : ℝ≥0∞ := ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ with hcd
    have hmeas : AEMeasurable (fun t => ‖mμ t‖ₑ *
        ‖dz (W Ps) t * dz (W Ps) (conj s) / (W Ps t - W Ps (conj s)) ^ 2‖ₑ ^ 2) (volume.restrict upperHalf) :=
      (hμc.aemeasurable hU).enorm.mul
        ((((s7g_f2_dzmeas (W Ps)).mul measurable_const).div
          ((hWcQ.measurable.sub measurable_const).pow_const 2)).enorm.pow_const 2).aemeasurable
    have e1 : (∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf,
        ‖mμ t₁‖ₑ * ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2 *
          (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) * c) =
        (∫⁻ t₁ in upperHalf, ‖mμ t₁‖ₑ *
          ‖dz (W Ps) t₁ * dz (W Ps) (conj s) / (W Ps t₁ - W Ps (conj s)) ^ 2‖ₑ ^ 2) *
        ((∫⁻ t₂ in upperHalf, ‖mν t₂‖ₑ *
          ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) * c) := by
      rw [← lintegral_mul_const'' _ hmeas]
      refine setLIntegral_congr_fun hU fun t₁ _ => ?_
      rw [← lintegral_mul_const' _ _ enorm_ne_top,
        ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top (ENNReal.pow_ne_top enorm_ne_top))]
      refine lintegral_congr fun t₂ => ?_
      ring
    rw [e1, hA hWcQ hμc hneQ s hs, hA hWc hνc hneP s hs]
    have hcn := s7g_f2_cnorm (z := W P s - W P (conj s)) (hdz0 s hsi) (hdz0 _ hsc)
      (show ‖dz (W Ps) (conj s)‖ = ‖dz (W P) s‖ by rw [hdzs s hsi, Complex.norm_conj])
    have hW2 : ‖W P s - W P (conj s)‖ = ‖W Ps s - W Ps (conj s)‖ := by
      rw [hWs1, hWs2, ← map_sub, Complex.norm_conj, norm_sub_rev]
    have hlam := td_one_le_lambdaInv hKP.2.1
    have hL0 : 0 ≤ L := by rw [hLd]; nlinarith
    have hd1 := s7g_f2_wd hKP hsP hs
    have hd2 := s7g_f2_wd hKQ hsQ hs
    have hz2 : ‖W P s - W P (conj s)‖ₑ ^ 2 ≤ ENNReal.ofReal (L ^ 2) *
        (ENNReal.ofReal (infDist (W P (conj s)) (W P '' upperHalf)) *
          ENNReal.ofReal (infDist (W Ps (conj s)) (W Ps '' upperHalf))) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul infDist_nonneg,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      calc ‖W P s - W P (conj s)‖ ^ 2 = ‖W P s - W P (conj s)‖ * ‖W Ps s - W Ps (conj s)‖ := by rw [← hW2]; ring
        _ ≤ (L * infDist (W P (conj s)) (W P '' upperHalf)) * (L * infDist (W Ps (conj s)) (W Ps '' upperHalf)) :=
            mul_le_mul hd1 hd2 (norm_nonneg _) (mul_nonneg hL0 infDist_nonneg)
        _ = _ := by ring
    have hdn : ‖dz (W Ps) (conj s)‖ₑ = ‖dz (W P) s‖ₑ := by rw [hdzs s hsi, ← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
    calc ‖dz (W Ps) (conj s)‖ₑ ^ 2 * Iμ s * (‖dz (W P) (conj s)‖ₑ ^ 2 * Iν s * c)
        = Iμ s * Iν s * (‖dz (W Ps) (conj s)‖ₑ ^ 2 * ‖dz (W P) (conj s)‖ₑ ^ 2 * c) := by ring
      _ = Iμ s * Iν s * (‖dz (W P) s‖ₑ * ‖dz (W P) (conj s)‖ₑ * ‖W P s - W P (conj s)‖ₑ ^ 2) := by
          rw [hcd, hcn]
      _ ≤ Iμ s * Iν s * (‖dz (W P) s‖ₑ * ‖dz (W P) (conj s)‖ₑ * (ENNReal.ofReal (L ^ 2) *
            (ENNReal.ofReal (infDist (W P (conj s)) (W P '' upperHalf)) *
              ENNReal.ofReal (infDist (W Ps (conj s)) (W Ps '' upperHalf))))) := by gcongr
      _ = ENNReal.ofReal (L ^ 2) * (Gν s * Gμ s) := by
          simp only [hGν, hGμ, hdn]
          ring
  -- measurability of the weights
  have hIνm : AEMeasurable Iν (volume.restrict upperHalf) := by
    have h : AEMeasurable (fun p : ℂ × ℂ => ‖mν p.2‖ₑ * ‖dz (W P) p.2‖ₑ ^ 2 / ‖W P p.2 - W P (conj p.1)‖ₑ ^ 4)
        ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) :=
      (((hνc.aemeasurable hU).enorm.comp_snd).mul
        (((s7g_f2_dzmeas (W P)).comp measurable_snd).enorm.pow_const 2).aemeasurable).div
        (((hWc.measurable.comp measurable_snd).sub
          (hWc.measurable.comp (Complex.continuous_conj.measurable.comp measurable_fst))).enorm.pow_const 4).aemeasurable
    exact h.lintegral_prod_right'
  have hIμm : AEMeasurable Iμ (volume.restrict upperHalf) := by
    have h : AEMeasurable (fun p : ℂ × ℂ => ‖mμ p.2‖ₑ * ‖dz (W Ps) p.2‖ₑ ^ 2 / ‖W Ps p.2 - W Ps (conj p.1)‖ₑ ^ 4)
        ((volume.restrict upperHalf).prod (volume.restrict upperHalf)) :=
      (((hμc.aemeasurable hU).enorm.comp_snd).mul
        (((s7g_f2_dzmeas (W Ps)).comp measurable_snd).enorm.pow_const 2).aemeasurable).div
        (((hWcQ.measurable.comp measurable_snd).sub
          (hWcQ.measurable.comp (Complex.continuous_conj.measurable.comp measurable_fst))).enorm.pow_const 4).aemeasurable
    exact h.lintegral_prod_right'
  have hGνm : AEMeasurable Gν (volume.restrict upperHalf) :=
    ((((s7g_f2_dzmeas (W P)).comp Complex.continuous_conj.measurable).enorm.aemeasurable).mul hIνm).mul
      (ENNReal.measurable_ofReal.comp ((continuous_infDist_pt _).measurable.comp
        (hWc.measurable.comp Complex.continuous_conj.measurable))).aemeasurable
  have hGμm : AEMeasurable Gμ (volume.restrict upperHalf) :=
    ((((s7g_f2_dzmeas (W Ps)).comp Complex.continuous_conj.measurable).enorm.aemeasurable).mul hIμm).mul
      (ENNReal.measurable_ofReal.comp ((continuous_infDist_pt _).measurable.comp
        (hWcQ.measurable.comp Complex.continuous_conj.measurable))).aemeasurable
  -- the two `R5a` norms
  have hsq : ∀ G : ℂ → ℝ≥0∞, ∀ a b d : ℂ → ℝ≥0∞, G = (fun s => a s * b s * d s) →
      (∫⁻ s in upperHalf, G s ^ (2 : ℝ)) = ∫⁻ s in upperHalf, a s ^ 2 * b s ^ 2 * d s ^ 2 := by
    intro G a b d hG
    rw [hG]
    congr 1
    funext s
    rw [ENNReal.rpow_two]
    ring
  have hRν : (∫⁻ s in upperHalf, Gν s ^ (2 : ℝ)) ≤ Bν := by
    rw [hsq Gν _ _ _ hGν]
    exact s7g_f2_R5a hKP hsP hCP hk'0 (by nlinarith) hkerP hC3 hνh.1 hνh.2.2
  have hRμ : (∫⁻ s in upperHalf, Gμ s ^ (2 : ℝ)) ≤ Bμ := by
    rw [hsq Gμ _ _ _ hGμ]
    exact s7g_f2_R5a hKQ hsQ hCQ hk'0 (by nlinarith) hkerQ hC3 hμh.1 hμh.2.2
  calc _ ≤ ∫⁻ s in upperHalf, ENNReal.ofReal (L ^ 2) * (Gν s * Gμ s) := setLIntegral_mono' hU hpt
    _ = ENNReal.ofReal (L ^ 2) * ∫⁻ s in upperHalf, Gν s * Gμ s := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L ^ 2) * ((∫⁻ s in upperHalf, Gν s ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ s in upperHalf, Gμ s ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) := by
        gcongr
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hGνm hGμm
    _ ≤ ENNReal.ofReal (L ^ 2) * (Bν ^ (1 / (2 : ℝ)) * Bμ ^ (1 / (2 : ℝ))) := by gcongr

/-- `∂W_P ≠ 0` off `ℝ` (positive Jacobian). -/
theorem s7g_f2_dz0 {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {P : ℂ × ℂ} (hP : max ‖P.1‖ ‖P.2‖ * k < 1) {y : ℂ} (hy : y.im ≠ 0) : dz (W P) y ≠ 0 := by
  intro h0
  rcases lt_or_gt_of_ne hy with h | h
  · obtain ⟨hb, hJ⟩ := e64_t5_beltrami hk hmk hms hW hP h
    unfold jacobian at hJ
    rw [hb, h0] at hJ
    simp at hJ
  · obtain ⟨hb, hJ⟩ := s71_b2_beltrami hk hmk hms hW hP h
    unfold jacobian at hJ
    rw [hb, h0] at hJ
    simp at hJ

/-- The diagonal kernel `K_P(s, s)` does not vanish on `𝕌`. -/
theorem s7g_f2_Kd0 {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {P : ℂ × ℂ} (hP : max ‖P.1‖ ‖P.2‖ * k < 1) {s : ℂ} (hs : s ∈ upperHalf) :
    dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2 ≠ 0 := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hmk hms hW
  have hsi : 0 < s.im := hs
  have hne : W P s - W P (conj s) ≠ 0 := fun h => by
    have := congrArg Complex.im (hinj P hP (sub_eq_zero.1 h))
    rw [Complex.conj_im] at this
    linarith
  exact div_ne_zero (mul_ne_zero (s7g_f2_dz0 hk hmk hms hW hP hsi.ne')
    (s7g_f2_dz0 hk hmk hms hW hP (by rw [Complex.conj_im]; linarith))) (pow_ne_zero 2 hne)

/-- Joint continuity of `x ↦ K_{p(x)}(u(x), z(x))` on a set where `p` stays in a closed polydisc and `u, z ∈ 𝕌`. -/
theorem s7g_f2_Kc {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {R : ℝ} (hRk : R * k < 1) {X : Type*} [TopologicalSpace X] {T : Set X} {p : X → ℂ × ℂ} {u z : X → ℂ}
    (hp : ContinuousOn p T) (hpT : MapsTo p T (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R))
    (hu : Continuous u) (hz : Continuous z) (huT : ∀ x ∈ T, u x ∈ upperHalf) (hzT : ∀ x ∈ T, z x ∈ upperHalf) :
    ContinuousOn (fun x => dz (W (p x)) (u x) * dz (W (p x)) (conj (z x)) /
      (W (p x) (u x) - W (p x) (conj (z x))) ^ 2) T := by
  obtain ⟨-, hinj, -⟩ := e64_W_basic hk hmk hms hW
  obtain ⟨hWc, hDc⟩ := e64_dzW_cont hk hmk hms hW
  have hsub := e64_polydisc_sub hk hRk
  have hcomp : ∀ g : X → ℂ, Continuous g → (∀ x ∈ T, (g x).im ≠ 0) →
      ContinuousOn (fun x => W (p x) (g x)) T ∧ ContinuousOn (fun x => dz (W (p x)) (g x)) T := by
    intro g hg hgi
    have hm : MapsTo (fun x => (p x, g x)) T ({P : ℂ × ℂ | max ‖P.1‖ ‖P.2‖ * k < 1} ×ˢ {u : ℂ | u.im ≠ 0}) :=
      fun x hx => ⟨hsub (hpT hx), hgi x hx⟩
    have hc : ContinuousOn (fun x => (p x, g x)) T := hp.prodMk hg.continuousOn
    have h1 := hWc.comp hc hm
    have h2 := hDc.comp hc hm
    simp only [Function.comp_def] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨hWu, hDu⟩ := hcomp u hu fun x hx => ne_of_gt (huT x hx)
  obtain ⟨hWz, hDz⟩ := hcomp (fun x => conj (z x)) (Complex.continuous_conj.comp hz) fun x hx => by
    have : 0 < (z x).im := hzT x hx
    rw [Complex.conj_im]
    linarith
  have hne : ∀ x ∈ T, (W (p x) (u x) - W (p x) (conj (z x))) ^ 2 ≠ 0 := by
    intro x hx
    refine pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
    have := congrArg Complex.im (hinj (p x) (hsub (hpT hx)) h)
    rw [Complex.conj_im] at this
    have h1 : 0 < (u x).im := huT x hx
    have h2 : 0 < (z x).im := hzT x hx
    linarith
  exact (hDu.mul hDz).div ((hWu.sub hWz).pow 2) hne

/-- `P ↦ K_P(u, z)` is holomorphic on the open polydisc of radius `R`, `R k < 1`. -/
theorem s7g_f2_Khol {m' : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hmk : IsBeltramiCoeff m' upperHalf k)
    (hms : ContDiffOn ℝ (⊤ : ℕ∞) m' upperHalf)
    {W : ℂ × ℂ → ℂ → ℂ} (hW : W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0))
    {u z : ℂ} (hu : u ∈ upperHalf) (hz : z ∈ upperHalf) {R : ℝ} (hRk : R * k < 1) {P : ℂ × ℂ}
    (hP : P ∈ ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) :
    DifferentiableAt ℂ (fun Q => dz (W Q) u * dz (W Q) (conj z) / (W Q u - W Q (conj z)) ^ 2) P :=
  ((s7g_f2_Kreg hk hmk hms hW hu hz hRk).differentiableOn (by norm_num)).differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hP)

/-- STUB F2 (line 1 under the integral). The new analytic input: the holomorphic extension of the line-1
integrand as a triple integral over `(𝕌 ∖ {i})³`, with a uniform `L¹` bound on a polydisc (Schur `R2` (dual) +
transfer `R3` + `|W s - W s̄| ≤ (λ + λ²) d(W s, ∂W(𝕌))` from `s7g_r3_wqs`), then `s7g_f2_mixed`. -/
theorem s7g_f2_line1D {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ') {mμ φμ mν φν : ℂ → ℂ} (hμh : IsHarmonicU mμ φμ)
    (hμf : ∀ u ∈ upperHalf, u ≠ I → mμ u = conj (μ (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    (hνh : IsHarmonicU mν φν)
    (hνf : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (ν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2))) :
    IntegrableOn (fun s => dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0) upperHalf ∧
    dzbar (dz fun e => ∫ s in upperHalf, conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 =
      ∫ s in upperHalf, dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 := by
  have hU := measurableSet_upperHalf_aux
  set S : Set ℂ := upperHalf \ {I} with hSdef
  have hSm : MeasurableSet S := hU.diff (measurableSet_singleton I)
  have hSU : S ⊆ upperHalf := sdiff_subset
  have hnull : (S : Set ℂ) =ᵐ[volume] upperHalf := sdiff_null_ae_eq_self (measure_singleton I)
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm
  have hmB : IsBeltramiCoeff m' upperHalf C :=
    ⟨(harmonicU_continuousOn hharm).aestronglyMeasurable hU, by
      filter_upwards [ae_restrict_mem hU] with u hu
      exact hCb u hu⟩
  have hms := wr_isHarmonicU_contDiffOn hharm
  have hfμ := s7g_l3_L2fin hμ (s7g_f2_mnorm hμf)
  have hfν := s7g_l3_L2fin hν (s7g_f2_mnorm hνf)
  obtain ⟨Mμ, hMμ0, hμb⟩ := harmonicU_bounded hμh
  obtain ⟨Mν, hMν0, hνb⟩ := harmonicU_bounded hνh
  have hμc := harmonicU_continuousOn hμh
  have hνc := harmonicU_continuousOn hνh
  have hm'c := harmonicU_continuousOn hharm
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = 1 / (4 * (C + 1)) := ⟨_, rfl⟩
  have hR0p : 0 < R0 := by rw [hR0]; positivity
  have hR0k2 : 2 * R0 * C < 1 := by
    rw [hR0, show 2 * (1 / (4 * (C + 1))) * C = C / (2 * (C + 1)) by field_simp; ring,
      div_lt_one (by positivity)]
    linarith
  have hR0k : R0 * C < 1 := by nlinarith
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℂ × ℂ → ℂ × (ℂ × ℂ) → ℂ, F = fun P x =>
      conj (mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2) *
      (mν x.2.2 * (dz (W P) x.2.2 * dz (W P) (conj x.1) / (W P x.2.2 - W P (conj x.1)) ^ 2) ^ 2) *
      (1 - P.1 * P.2 * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) x.1 * dz (W P) (conj x.1) / (W P x.1 - W P (conj x.1)) ^ 2) := ⟨_, rfl⟩
  set D : Set (ℂ × ℂ) := closedBall (0 : ℂ) R0 ×ˢ closedBall (0 : ℂ) R0 with hDdef
  have hTm : MeasurableSet (S ×ˢ (S ×ˢ S)) := hSm.prod (hSm.prod hSm)
  have hsub := e64_polydisc_sub hC0 hR0k
  have hswD : ∀ P ∈ D, ((conj P.2, conj P.1) : ℂ × ℂ) ∈ D := by
    rintro P ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h2
    · rw [mem_closedBall_zero_iff, Complex.norm_conj]
      exact mem_closedBall_zero_iff.1 h1
  -- continuity on `D × (𝕌 ∖ {i})³`
  have hcont : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => F p.1 p.2) (D ×ˢ (S ×ˢ (S ×ˢ S))) := by
    have hmem : ∀ p ∈ D ×ˢ (S ×ˢ (S ×ˢ S)), p.1 ∈ D ∧ p.2.1 ∈ upperHalf ∧ p.2.2.1 ∈ upperHalf ∧
        p.2.2.2 ∈ upperHalf := by
      rintro p ⟨h1, h2, h3, h4⟩
      exact ⟨h1, hSU h2, hSU h3, hSU h4⟩
    have hK1 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (S ×ˢ (S ×ˢ S)))
      (p := fun p => ((conj p.1.2, conj p.1.1) : ℂ × ℂ)) (u := fun p => p.2.2.1) (z := fun p => p.2.1)
      (by fun_prop) (fun p hp => hswD _ (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.2.1) (fun p hp => (hmem p hp).2.1)
    have hK2 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (S ×ˢ (S ×ˢ S)))
      (p := fun p => p.1) (u := fun p => p.2.2.2) (z := fun p => p.2.1)
      continuous_fst.continuousOn (fun p hp => (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.2.2) (fun p hp => (hmem p hp).2.1)
    have hK3 := s7g_f2_Kc hC0 hmB hms hW hR0k (T := D ×ˢ (S ×ˢ (S ×ˢ S)))
      (p := fun p => p.1) (u := fun p => p.2.1) (z := fun p => p.2.1)
      continuous_fst.continuousOn (fun p hp => (hmem p hp).1) (by fun_prop) (by fun_prop)
      (fun p hp => (hmem p hp).2.1) (fun p hp => (hmem p hp).2.1)
    have hA : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => mμ p.2.2.1) (D ×ˢ (S ×ˢ (S ×ˢ S))) :=
      hμc.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.2.1).continuousOn
        fun p hp => (hmem p hp).2.2.1
    have hB : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => mν p.2.2.2) (D ×ˢ (S ×ˢ (S ×ˢ S))) :=
      hνc.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.2.2).continuousOn
        fun p hp => (hmem p hp).2.2.2
    have hM' : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => ((‖m' p.2.1‖ ^ 2 : ℝ) : ℂ))
        (D ×ˢ (S ×ˢ (S ×ˢ S))) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn
        (hm'c.comp (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.2.1).continuousOn
          fun p hp => (hmem p hp).2.1)).pow 2)
    have hP1 : ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.1.1 * p.1.2) (D ×ˢ (S ×ˢ (S ×ˢ S))) :=
      (by fun_prop : Continuous fun p : (ℂ × ℂ) × (ℂ × (ℂ × ℂ)) => p.1.1 * p.1.2).continuousOn
    have h := (((Complex.continuous_conj.comp_continuousOn (hA.mul (hK1.pow 2))).mul (hB.mul (hK2.pow 2))).mul
      ((continuousOn_const (c := (1 : ℂ))).sub (hP1.mul hM'))).div hK3
      (fun p hp => s7g_f2_Kd0 hC0 hmB hms hW (hsub (hmem p hp).1) (hmem p hp).2.1)
    rw [hF]
    exact h
  -- separate holomorphy
  have hR2 : 2 * R0 * C < 1 := hR0k2
  have hhol : ∀ x ∈ S ×ˢ (S ×ˢ S),
      (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) x) (ball (0 : ℂ) R0)) ∧
        ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) x) (ball (0 : ℂ) R0) := by
    intro x hx
    have hs : x.1 ∈ upperHalf := hSU hx.1
    have ht1 : x.2.1 ∈ upperHalf := hSU hx.2.1
    have ht2 : x.2.2 ∈ upperHalf := hSU hx.2.2
    have hin : ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        ((a, b) : ℂ × ℂ) ∈ ball (0 : ℂ) (2 * R0) ×ˢ ball (0 : ℂ) (2 * R0) := fun a b ha hb =>
      ⟨mem_ball_zero_iff.2 (by linarith), mem_ball_zero_iff.2 (by linarith)⟩
    have hK : ∀ {u z : ℂ}, u ∈ upperHalf → z ∈ upperHalf → ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        DifferentiableAt ℂ (fun Q => dz (W Q) u * dz (W Q) (conj z) / (W Q u - W Q (conj z)) ^ 2) (a, b) :=
      fun hu hz a b ha hb => s7g_f2_Khol hC0 hmB hms hW hu hz hR2 (hin a b ha hb)
    have hden : ∀ a b : ℂ, ‖a‖ ≤ R0 → ‖b‖ ≤ R0 →
        dz (W (a, b)) x.1 * dz (W (a, b)) (conj x.1) / (W (a, b) x.1 - W (a, b) (conj x.1)) ^ 2 ≠ 0 :=
      fun a b ha hb => s7g_f2_Kd0 hC0 hmB hms hW
        (hsub ⟨mem_closedBall_zero_iff.2 ha, mem_closedBall_zero_iff.2 hb⟩) hs
    constructor
    · intro b hb a ha
      have ha' : ‖a‖ ≤ R0 := (mem_ball_zero_iff.1 ha).le
      have hb' : ‖b‖ ≤ R0 := mem_closedBall_zero_iff.1 hb
      have hg : DifferentiableAt ℂ (fun a'' => mμ x.2.1 * (dz (W (conj b, a'')) x.2.1 * dz (W (conj b, a'')) (conj x.1) /
          (W (conj b, a'') x.2.1 - W (conj b, a'') (conj x.1)) ^ 2) ^ 2) (conj a) :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.1 * dz (W Q) (conj x.1) / (W Q x.2.1 - W Q (conj x.1)) ^ 2) (conj a)
          (hK ht1 hs (conj b) (conj a) (by rwa [Complex.norm_conj]) (by rwa [Complex.norm_conj]))
          ((differentiableAt_const _).prodMk differentiableAt_id)).pow 2)
      have h1 : DifferentiableAt ℂ (fun a' => conj (mμ x.2.1 * (dz (W (conj b, conj a')) x.2.1 *
          dz (W (conj b, conj a')) (conj x.1) / (W (conj b, conj a') x.2.1 - W (conj b, conj a') (conj x.1)) ^ 2) ^ 2))
          a := differentiableAt_conj_conj_iff.2 hg
      have h2 : DifferentiableAt ℂ (fun a' => mν x.2.2 * (dz (W (a', b)) x.2.2 * dz (W (a', b)) (conj x.1) /
          (W (a', b) x.2.2 - W (a', b) (conj x.1)) ^ 2) ^ 2) a :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.2 * dz (W Q) (conj x.1) / (W Q x.2.2 - W Q (conj x.1)) ^ 2) a (hK ht2 hs a b ha' hb')
          (differentiableAt_id.prodMk (differentiableAt_const _))).pow 2)
      have h3 : DifferentiableAt ℂ (fun a' : ℂ => 1 - a' * b * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) a := by fun_prop
      have h4 : DifferentiableAt ℂ (fun a' => dz (W (a', b)) x.1 * dz (W (a', b)) (conj x.1) /
          (W (a', b) x.1 - W (a', b) (conj x.1)) ^ 2) a :=
        DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.1 * dz (W Q) (conj x.1) / (W Q x.1 - W Q (conj x.1)) ^ 2) a (hK hs hs a b ha' hb') (differentiableAt_id.prodMk (differentiableAt_const _))
      have h := (((h1.mul h2).mul h3).div h4 (hden a b ha' hb')).differentiableWithinAt (s := ball (0 : ℂ) R0)
      rw [hF]
      exact h
    · intro a ha b hb
      have ha' : ‖a‖ ≤ R0 := mem_closedBall_zero_iff.1 ha
      have hb' : ‖b‖ ≤ R0 := (mem_ball_zero_iff.1 hb).le
      have hg : DifferentiableAt ℂ (fun b'' => mμ x.2.1 * (dz (W (b'', conj a)) x.2.1 * dz (W (b'', conj a)) (conj x.1) /
          (W (b'', conj a) x.2.1 - W (b'', conj a) (conj x.1)) ^ 2) ^ 2) (conj b) :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.1 * dz (W Q) (conj x.1) / (W Q x.2.1 - W Q (conj x.1)) ^ 2) (conj b)
          (hK ht1 hs (conj b) (conj a) (by rwa [Complex.norm_conj]) (by rwa [Complex.norm_conj]))
          (differentiableAt_id.prodMk (differentiableAt_const _))).pow 2)
      have h1 : DifferentiableAt ℂ (fun b' => conj (mμ x.2.1 * (dz (W (conj b', conj a)) x.2.1 *
          dz (W (conj b', conj a)) (conj x.1) / (W (conj b', conj a) x.2.1 - W (conj b', conj a) (conj x.1)) ^ 2) ^ 2))
          b := differentiableAt_conj_conj_iff.2 hg
      have h2 : DifferentiableAt ℂ (fun b' => mν x.2.2 * (dz (W (a, b')) x.2.2 * dz (W (a, b')) (conj x.1) /
          (W (a, b') x.2.2 - W (a, b') (conj x.1)) ^ 2) ^ 2) b :=
        (differentiableAt_const _).mul ((DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.2.2 * dz (W Q) (conj x.1) / (W Q x.2.2 - W Q (conj x.1)) ^ 2) b (hK ht2 hs a b ha' hb')
          ((differentiableAt_const _).prodMk differentiableAt_id)).pow 2)
      have h3 : DifferentiableAt ℂ (fun b' : ℂ => 1 - a * b' * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)) b := by fun_prop
      have h4 : DifferentiableAt ℂ (fun b' => dz (W (a, b')) x.1 * dz (W (a, b')) (conj x.1) /
          (W (a, b') x.1 - W (a, b') (conj x.1)) ^ 2) b :=
        DifferentiableAt.comp (g := fun Q : ℂ × ℂ => dz (W Q) x.1 * dz (W Q) (conj x.1) / (W Q x.1 - W Q (conj x.1)) ^ 2) b (hK hs hs a b ha' hb') ((differentiableAt_const _).prodMk differentiableAt_id)
      have h := (((h1.mul h2).mul h3).div h4 (hden a b ha' hb')).differentiableWithinAt (s := ball (0 : ℂ) R0)
      rw [hF]
      exact h
  -- pointwise norm of `F`
  have hCf : ∀ P ∈ D, ∀ s ∈ upperHalf, ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ₑ ≤ 2 := by
    rintro P ⟨h1, h2⟩ s hs
    have hp1 : ‖P.1‖ ≤ R0 := mem_closedBall_zero_iff.1 h1
    have hp2 : ‖P.2‖ ≤ R0 := mem_closedBall_zero_iff.1 h2
    have hm := hCb s hs
    have hle : ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : ‖P.1‖ * ‖P.2‖ * ‖m' s‖ ^ 2 ≤ (R0 * C) ^ 2 := by
        have := mul_le_mul hp1 hp2 (norm_nonneg _) hR0p.le
        have h4 : ‖m' s‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
        nlinarith [norm_nonneg P.1, norm_nonneg P.2, sq_nonneg ‖m' s‖]
      have h5 : (R0 * C) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hR0p.le hC0]
      linarith
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
      _ = 2 := by norm_num
  have hFn : ∀ P x, ‖F P x‖ₑ = ‖mμ x.2.1‖ₑ * ‖dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2‖ₑ ^ 2 *
      (‖mν x.2.2‖ₑ * ‖dz (W P) x.2.2 * dz (W P) (conj x.1) / (W P x.2.2 - W P (conj x.1)) ^ 2‖ₑ ^ 2) *
      ‖1 - P.1 * P.2 * ((‖m' x.1‖ ^ 2 : ℝ) : ℂ)‖ₑ *
      ‖(dz (W P) x.1 * dz (W P) (conj x.1) / (W P x.1 - W P (conj x.1)) ^ 2)⁻¹‖ₑ := by
    intro P x
    rw [hF]
    simp only [div_eq_mul_inv (_ * _ * _), enorm_mul, enorm_pow]
    rw [show ‖conj (mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2)‖ₑ =
        ‖mμ x.2.1 * (dz (W (conj P.2, conj P.1)) x.2.1 * dz (W (conj P.2, conj P.1)) (conj x.1) /
        (W (conj P.2, conj P.1) x.2.1 - W (conj P.2, conj P.1) (conj x.1)) ^ 2) ^ 2‖ₑ by
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj], enorm_mul, enorm_pow]
  -- the uniform `L¹` bound on `D`
  obtain ⟨M5, hM5⟩ := s7g_f2_R5 hC0 hmB hms hW hμh hνh hfμ hfν hR0p.le hR0k2
  have hmeas3 : (volume.restrict (S ×ˢ (S ×ˢ S)) : Measure (ℂ × (ℂ × ℂ))) =
      (volume.restrict S).prod ((volume.restrict S).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    rfl
  have hmeas2 : (volume.restrict (S ×ˢ S) : Measure (ℂ × ℂ)) = (volume.restrict S).prod (volume.restrict S) := by
    rw [Measure.prod_restrict]
    rfl
  have hM : ∀ P ∈ D, ∫⁻ x in S ×ˢ (S ×ˢ S), ‖F P x‖ₑ ≤ ENNReal.ofReal (2 * M5) := by
    intro P hP
    have h2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc ∫⁻ x in S ×ˢ (S ×ˢ S), ‖F P x‖ₑ
        ≤ ∫⁻ s in S, ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖F P (s, (t₁, t₂))‖ₑ := by
          rw [hmeas3]
          exact (lintegral_prod_le _).trans (lintegral_mono fun s => lintegral_prod_le _)
      _ ≤ ∫⁻ s in S, ∫⁻ t₁ in S, ∫⁻ t₂ in S, 2 * (‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) := by
          refine setLIntegral_mono' hSm fun s hs => setLIntegral_mono' hSm fun t₁ _ =>
            setLIntegral_mono' hSm fun t₂ _ => ?_
          rw [hFn]
          calc _ = (‖mμ t₁‖ₑ * ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
                (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
              (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
              ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) *
                ‖1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)‖ₑ := by ring
            _ ≤ _ := by
              rw [mul_comm 2]
              exact mul_le_mul_right (hCf P hP s (hSU hs)) _
      _ ≤ ∫⁻ s in upperHalf, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf, 2 * (‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ) :=
          (lintegral_mono fun s => (lintegral_mono fun t₁ => lintegral_mono_set hSU).trans
            (lintegral_mono_set hSU)).trans (lintegral_mono_set hSU)
      _ = 2 * ∫⁻ s in upperHalf, ∫⁻ t₁ in upperHalf, ∫⁻ t₂ in upperHalf, ‖mμ t₁‖ₑ *
            ‖dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2‖ₑ ^ 2 *
            (‖mν t₂‖ₑ * ‖dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2‖ₑ ^ 2) *
            ‖(dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)⁻¹‖ₑ := by
          simp only [lintegral_const_mul' (2 : ℝ≥0∞) _ h2]
      _ ≤ 2 * ENNReal.ofReal M5 := by gcongr; exact hM5 P hP
      _ = ENNReal.ofReal (2 * M5) := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hce : ∀ z : ℂ, ‖conj z‖ₑ = ‖z‖ₑ := fun z => by rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
  -- the fixed-`s` bound
  have hfix : ∀ s ∈ S, ∃ Ms : ℝ, ∀ P ∈ D, ∫⁻ t in S ×ˢ S, ‖F P (s, t)‖ₑ ≤ ENNReal.ofReal Ms := by
    intro s hs
    have hsU := hSU hs
    obtain ⟨M1, hM1⟩ := s71_b2_L1 hC0 hmB hms hμc hMμ0 hμb hsU hR0k hW rfl
    obtain ⟨M2, hM2⟩ := s71_b2_L1 hC0 hmB hms hνc hMν0 hνb hsU hR0k hW rfl
    have hcq : ContinuousOn (fun P : ℂ × ℂ => (1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)) D :=
      ((continuousOn_const (c := (1 : ℂ))).sub
        (by fun_prop : Continuous fun P : ℂ × ℂ => P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)).continuousOn).div
        (s7g_f2_Kc hC0 hmB hms hW hR0k (T := D) (p := fun P => P) (u := fun _ => s) (z := fun _ => s)
          continuousOn_id (fun P hP => hP) continuous_const continuous_const (fun _ _ => hsU) (fun _ _ => hsU))
        (fun P hP => s7g_f2_Kd0 hC0 hmB hms hW (hsub hP) hsU)
    obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℂ) R0).prod (isCompact_closedBall (0 : ℂ) R0)).exists_bound_of_continuousOn hcq
    refine ⟨max M1 0 * (max M2 0 * max B 0), fun P hP => ?_⟩
    have hPs := hswD P hP
    obtain ⟨hi1, hb1⟩ := hM1 _ hPs
    obtain ⟨hi2, hb2⟩ := hM2 P hP
    have hL1 : (∫⁻ t in S, ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
        (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) ≤ ENNReal.ofReal (max M1 0) :=
      calc _ ≤ ∫⁻ t in upperHalf, ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ := lintegral_mono_set hSU
        _ = ENNReal.ofReal (∫ t in upperHalf, ‖mμ t * (dz (W (conj P.2, conj P.1)) t *
            dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖) :=
          (ofReal_integral_norm_eq_lintegral_enorm hi1).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb1.trans (le_max_left _ _))
    have hL2 : (∫⁻ t in S, ‖mν t * (dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2) ^ 2‖ₑ) ≤
        ENNReal.ofReal (max M2 0) :=
      calc _ ≤ ∫⁻ t in upperHalf, ‖mν t * (dz (W P) t * dz (W P) (conj s) / (W P t - W P (conj s)) ^ 2) ^ 2‖ₑ :=
            lintegral_mono_set hSU
        _ = ENNReal.ofReal (∫ t in upperHalf, ‖mν t * (dz (W P) t * dz (W P) (conj s) /
            (W P t - W P (conj s)) ^ 2) ^ 2‖) := (ofReal_integral_norm_eq_lintegral_enorm hi2).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hb2.trans (le_max_left _ _))
    have hcB : ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
        (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ ≤ ENNReal.ofReal (max B 0) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hB P hP).trans (le_max_left _ _))
    have hmeasμ : AEMeasurable (fun t => ‖mμ t * (dz (W (conj P.2, conj P.1)) t * dz (W (conj P.2, conj P.1)) (conj s) /
        (W (conj P.2, conj P.1) t - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) (volume.restrict S) :=
      (hi1.mono_set hSU).aestronglyMeasurable.enorm
    calc ∫⁻ t in S ×ˢ S, ‖F P (s, t)‖ₑ ≤ ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖F P (s, (t₁, t₂))‖ₑ := by
          rw [hmeas2]
          exact lintegral_prod_le _
      _ = ∫⁻ t₁ in S, ∫⁻ t₂ in S, ‖mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ *
            (‖mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2‖ₑ *
              ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ) := by
          refine lintegral_congr fun t₁ => lintegral_congr fun t₂ => ?_
          have e : F P (s, (t₁, t₂)) = conj (mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ *
              dz (W (conj P.2, conj P.1)) (conj s) /
              (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2) *
              ((mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2) *
              ((1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2))) := by
            simp only [hF]
            ring
          rw [e, enorm_mul, enorm_mul, hce]
      _ = (∫⁻ t₁ in S, ‖mμ t₁ * (dz (W (conj P.2, conj P.1)) t₁ * dz (W (conj P.2, conj P.1)) (conj s) /
            (W (conj P.2, conj P.1) t₁ - W (conj P.2, conj P.1) (conj s)) ^ 2) ^ 2‖ₑ) *
            ((∫⁻ t₂ in S, ‖mν t₂ * (dz (W P) t₂ * dz (W P) (conj s) / (W P t₂ - W P (conj s)) ^ 2) ^ 2‖ₑ) *
              ‖(1 - P.1 * P.2 * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
                (dz (W P) s * dz (W P) (conj s) / (W P s - W P (conj s)) ^ 2)‖ₑ) := by
          rw [← lintegral_mul_const'' _ hmeasμ]
          refine lintegral_congr fun t₁ => ?_
          rw [← lintegral_mul_const' _ _ enorm_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]
      _ ≤ ENNReal.ofReal (max M1 0) * (ENNReal.ofReal (max M2 0) * ENNReal.ofReal (max B 0)) := by
          gcongr
      _ = ENNReal.ofReal (max M1 0 * (max M2 0 * max B 0)) := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul (le_max_right _ _)]
  -- the diagonal: line 1 at `s` is `c ∫∫ F`
  have hdiag : ∀ e ∈ ball (0 : ℂ) R0, ∀ s ∈ S,
      conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s * (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) *
        rhoVar m' e s = (12 / π : ℂ) ^ 2 / (-4) * ∫ t in S ×ˢ S, F (e, conj e) (s, t) := by
    intro e he s hs
    have hsU := hSU hs
    have he1 : ‖e‖ < R0 := mem_ball_zero_iff.1 he
    have hε : ‖e‖ * C < 1 := by nlinarith [norm_nonneg e]
    have hPd : ((e, conj e) : ℂ × ℂ) ∈ D :=
      ⟨mem_closedBall_zero_iff.2 he1.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact he1.le)⟩
    have hKd := s7g_f2_Kdiag hC0 hmB hW hε
    have hFd : ∀ t : ℂ × ℂ, F (e, conj e) (s, t) = conj (mμ t.1 * kernelKbar (fun y => e * m' y) t.1 s ^ 2) *
        (mν t.2 * kernelKbar (fun y => e * m' y) t.2 s ^ 2) * (1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
          kernelKbar (fun y => e * m' y) s s := by
      intro t
      simp only [hF, Complex.conj_conj]
      rw [hKd, hKd, hKd]
    have hfac : (∫ t in S ×ˢ S, F (e, conj e) (s, t)) =
        conj (∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) *
          (∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) *
          ((1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) / kernelKbar (fun y => e * m' y) s s) := by
      have e1 : ∀ t : ℂ × ℂ, F (e, conj e) (s, t) = conj (mμ t.1 * kernelKbar (fun y => e * m' y) t.1 s ^ 2) *
          (mν t.2 * kernelKbar (fun y => e * m' y) t.2 s ^ 2) * ((1 - e * conj e * ((‖m' s‖ ^ 2 : ℝ) : ℂ)) /
            kernelKbar (fun y => e * m' y) s s) := fun t => by rw [hFd]; ring
      rw [hmeas2]
      simp_rw [e1]
      rw [integral_mul_const, integral_prod_mul (fun t => conj (mμ t * kernelKbar (fun y => e * m' y) t s ^ 2))
        (fun t => mν t * kernelKbar (fun y => e * m' y) t s ^ 2), integral_conj, setIntegral_congr_set hnull,
        setIntegral_congr_set hnull]
    have h71μ := s71_eq_7_1 hμh hharm hC0 hmB hε hsU
    have h71ν := s71_eq_7_1 hνh hharm hC0 hmB hε hsU
    have hρ : rhoVar m' e s = -4 * kernelKbar (fun y => e * m' y) s s := eq_6_1 m' e s
    have hkd0 : kernelKbar (fun y => e * m' y) s s ≠ 0 := by
      rw [← hKd]
      exact s7g_f2_Kd0 hC0 hmB hms hW (hsub hPd) hsU
    have hρ0 : rhoVar m' e s ≠ 0 := by rw [hρ]; exact mul_ne_zero (by norm_num) hkd0
    have hc12 : conj (12 / π : ℂ) = 12 / π := by rw [map_div₀, Complex.conj_ofReal, map_ofNat]
    have hQ2 : QfunU mν (fun u => e * m' u) s = (12 / π : ℂ) *
        (∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) / rhoVar m' e s := by
      rw [eq_div_iff hρ0]
      linear_combination h71ν
    have hQ1 : conj (QfunU mμ (fun u => e * m' u) s) = (12 / π : ℂ) *
        conj (∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) / rhoVar m' e s := by
      rw [eq_div_iff hρ0]
      have h := congrArg conj h71μ
      rw [map_mul, map_mul, s71_rho_real, hc12] at h
      linear_combination h
    rw [hfac, hQ1, hQ2, hρ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    field_simp
    push_cast
    ring
  -- the mixed partials, outer and fixed-`s`
  obtain ⟨hmixi, hmix⟩ := s7g_f2_mixed (m := volume) hTm hR0p hcont hhol hM
  have hΦ2 := (s7g_f2_mixC2 hTm hcont hhol hM).1
  have hcs : ∀ s ∈ S, ContinuousOn (fun p : (ℂ × ℂ) × (ℂ × ℂ) => F p.1 (s, p.2)) (D ×ˢ (S ×ˢ S)) := fun s hs =>
    hcont.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      fun p hp => ⟨hp.1, hs, hp.2⟩
  have hinner : ∀ s ∈ S,
      deriv (fun b => deriv (fun a => ∫ t in S ×ˢ S, F (a, b) (s, t)) 0) 0 =
        ∫ t in S ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 ∧
      ContDiffOn ℂ 2 (fun P => ∫ t in S ×ˢ S, F P (s, t)) (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := by
    intro s hs
    obtain ⟨Ms, hMs⟩ := hfix s hs
    have hh : ∀ t ∈ S ×ˢ S, (∀ b ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun a => F (a, b) (s, t))
        (ball (0 : ℂ) R0)) ∧ ∀ a ∈ closedBall (0 : ℂ) R0, DifferentiableOn ℂ (fun b => F (a, b) (s, t))
        (ball (0 : ℂ) R0) := fun t ht => hhol (s, t) ⟨hs, ht⟩
    exact ⟨(s7g_f2_mixed (m := volume) (hSm.prod hSm) hR0p (hcs s hs) hh hMs).2,
      (s7g_f2_mixC2 (m := volume) (hSm.prod hSm) (hcs s hs) hh hMs).1⟩
  have hpt : ∀ s ∈ S, dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
      (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 =
        (12 / π : ℂ) ^ 2 / (-4) * ∫ t in S ×ˢ S, deriv (fun b => deriv (fun a => F (a, b) (s, t)) 0) 0 := by
    intro s hs
    obtain ⟨hm2, hC2⟩ := hinner s hs
    have hev : (fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (12 / π : ℂ) ^ 2 / (-4) * (fun P => ∫ t in S ×ˢ S, F P (s, t)) (e, conj e) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hR0p] with e he
      exact hdiag e he s hs
    rw [s7g_f2_germ hev, s7g_f2_wconst hR0p (s7g_f2_diagC2 hC2), (s7g_f2_ddpartial hR0p hC2).1, hm2]
  have hint3 : Integrable (fun x : ℂ × (ℂ × ℂ) => deriv (fun b => deriv (fun a => F (a, b) x) 0) 0)
      ((volume.restrict S).prod ((volume.restrict S).prod (volume.restrict S))) := by
    rw [← hmeas3]
    exact hmixi
  refine ⟨?_, ?_⟩
  · refine (integrableOn_congr_set_ae hnull).1 ?_
    refine (hint3.integral_prod_left.const_mul ((12 / π : ℂ) ^ 2 / (-4))).congr ?_
    filter_upwards [ae_restrict_mem hSm] with s hs
    rw [hpt s hs, hmeas2]
  · have hgev : (fun e => ∫ s in upperHalf, conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) =ᶠ[𝓝 (0 : ℂ)]
        fun e => (fun P => (12 / π : ℂ) ^ 2 / (-4) * ∫ x in S ×ˢ (S ×ˢ S), F P x) (e, conj e) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hR0p] with e he
      have he1 : ‖e‖ < R0 := mem_ball_zero_iff.1 he
      have hPd : ((e, conj e) : ℂ × ℂ) ∈ D :=
        ⟨mem_closedBall_zero_iff.2 he1.le, mem_closedBall_zero_iff.2 (by rw [Complex.norm_conj]; exact he1.le)⟩
      have hint : Integrable (F (e, conj e)) ((volume.restrict S).prod ((volume.restrict S).prod (volume.restrict S))) := by
        rw [← hmeas3]
        refine ⟨?_, lt_of_le_of_lt (hM _ hPd) ENNReal.ofReal_lt_top⟩
        exact (hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun x hx => ⟨hPd, hx⟩)).aestronglyMeasurable hTm
      show _ = (12 / π : ℂ) ^ 2 / (-4) * ∫ x in S ×ˢ (S ×ˢ S), F (e, conj e) x
      rw [hmeas3, integral_prod _ hint, ← hmeas2, ← integral_const_mul, ← setIntegral_congr_set hnull]
      exact setIntegral_congr_fun hSm fun s hs => hdiag e he s hs
    have hΦC : ContDiffOn ℂ 2 (fun P => (12 / π : ℂ) ^ 2 / (-4) * ∫ x in S ×ˢ (S ×ˢ S), F P x)
        (ball (0 : ℂ) R0 ×ˢ ball (0 : ℂ) R0) := contDiffOn_const.mul hΦ2
    rw [s7g_f2_germ hgev, (s7g_f2_ddpartial hR0p hΦC).1]
    simp only [deriv_const_mul_field']
    rw [hmix, hmeas3, integral_prod _ hint3, ← integral_const_mul, ← setIntegral_congr_set hnull]
    refine setIntegral_congr_fun hSm fun s hs => ?_
    rw [hpt s hs, hmeas2]

/-- The algebra of stub G for abstract `C²` factors: the second derivatives of `X` and `Y` cancel. -/
theorem s7g_f2_ptalg {X Y Cf D : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hX : ContDiffOn ℝ 2 X (ball 0 r))
    (hY : ContDiffOn ℝ 2 Y (ball 0 r)) (hCf : ContDiffOn ℝ 2 Cf (ball 0 r)) (hD : ContDiffOn ℝ 2 D (ball 0 r))
    (hX1 : dzbar X 0 = 0) (hY1 : dz Y 0 = 0) (hC0 : Cf 0 = 1) (hC1 : dz Cf 0 = 0) (hC2 : dzbar Cf 0 = 0)
    (hD1 : dz D 0 = 0) (hD2 : dzbar D 0 = 0) :
    dzbar (dz fun e => X e * Y e * Cf e * D e) 0 - X 0 * dzbar (dz fun e => D e * Y e) 0 -
        Y 0 * dzbar (dz fun e => D e * X e) 0 =
      X 0 * Y 0 * dzbar (dz Cf) 0 * D 0 - X 0 * Y 0 * dzbar (dz D) 0 + dz X 0 * dzbar Y 0 * D 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hd : ∀ {f : ℂ → ℂ}, ContDiffOn ℝ 2 f (ball 0 r) → DifferentiableAt ℝ f 0 := fun hf =>
    (hf.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds h0)
  have hXY := hX.mul hY
  have h1 := s7g_f2_wmul hr (hXY.mul hCf) hD
  have h2 := s7g_f2_wmul hr hXY hCf
  have h3 := s7g_f2_wmul hr hX hY
  have h4 := s7g_f2_wmul hr hD hY
  have h5 := s7g_f2_wmul hr hD hX
  have d1 := s7g_f2_dzmul (hd hXY) (hd hCf)
  have d2 := s7g_f2_dzmul (hd hX) (hd hY)
  rw [h1, h2, h3, h4, h5, d1.1, d1.2, d2.1, d2.2, hX1, hY1, hC0, hC1, hC2, hD1, hD2]
  ring

/-- STUB G (pointwise algebra, `Q̈` cancels). For `s ∈ 𝕌`, with `X = \overline{Q_U(m_μ, e m')(s)}`,
`Y = Q_U(m_ν, e m')(s)`, `C = 1 - |e|²|m'(s)|²`, `D = ρ^{e m'}(s)` and `L̈ = ∂_ē∂_e|₀`:
`T₁ - T₂ - T₃ = L̈(XYCD) - X₀ L̈(YD) - Y₀ L̈(XD)
  = -\overline{m_μ} m_ν |m'|² ρ - \overline{m_μ} m_ν ρ̈ + \overline{Q̇_U(m_μ)} Q̇_U(m_ν) ρ`
(the `Ẍ`, `Ÿ` terms cancel; `∂_e X = \overline{Q̇μ}`, `∂_ē X = 0`, `∂_e Y = 0`, `∂_ē Y = Q̇ν`, `∂D = ∂̄D = 0`,
`L̈C = -|m'|²`, `L̈D = ρ G_U(|m'|²)` by `prop_6_3`). -/
theorem s7g_f2_pt {m' φ' mμ φμ mν φν : ℂ → ℂ} (hharm : IsHarmonicU m' φ') (hμh : IsHarmonicU mμ φμ)
    (hνh : IsHarmonicU mν φν) {s : ℂ} (hs : s ∈ upperHalf) :
    dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) * QfunU mν (fun u => e * m' u) s *
        (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 -
      conj (mμ s) * ((12 / π : ℂ) *
        dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) -
      mν s * conj ((12 / π : ℂ) *
        dz (dzbar fun e => ∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) =
    -(conj (mμ s) * mν s * (‖m' s‖ ^ 2 : ℝ) * rhoU s) -
      conj (mμ s) * mν s * (rhoU s * resolventOpU (fun u => (‖m' u‖ ^ 2 : ℝ)) s) +
      conj (dzbar (fun e => QfunU mμ (fun u => e * m' u) s) 0) *
        dzbar (fun e => QfunU mν (fun u => e * m' u) s) 0 * rhoU s := by
  obtain ⟨C, hC0, hmB, hms⟩ := s71_harm_setup hharm
  obtain ⟨W, hW⟩ : ∃ W : ℂ × ℂ → ℂ → ℂ, W = fun P => normalizedSolution fun u =>
      P.1 * (if 0 < u.im then m' u else 0) + P.2 * (if u.im < 0 then conj (m' (conj u)) else 0) := ⟨_, rfl⟩
  have hC1 : 0 < C + 1 := by linarith
  have hR0p : 0 < 1 / (C + 1) := by positivity
  have hR0k : 1 / (C + 1) * C < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hC1]
    linarith
  set r1 := min (1 / (C + 1)) (1 / (C + 1)) with hr1d
  have hr1 : 0 < r1 := lt_min hR0p hR0p
  have hJν := s7g_f2_Jreg hνh hC0 hmB hms hR0p hR0k hW hs
  have hJμ := s7g_f2_Jreg hμh hC0 hmB hms hR0p hR0k hW hs
  have hDr := s7g_f2_Dreg hC0 hmB hms hR0k hW hs
  have hD0 : rhoVar m' 0 s = rhoU s := (rhoVar_pullback m' 0 hs).2
  have hρ0 : (rhoU s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have him : 0 < s.im := hs
    unfold rhoU
    positivity
  have hDc : ContinuousAt (fun e => rhoVar m' e s) 0 :=
    hDr.continuousOn.continuousAt (ball_mem_nhds 0 hr1)
  have hev : ∀ᶠ e in 𝓝 (0 : ℂ), rhoVar m' e s ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 :=
    (hDc.eventually_ne (show rhoVar m' 0 s ≠ 0 by rw [hD0]; exact hρ0)).and (ball_mem_nhds 0 hr1)
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : ∀ e ∈ ball (0 : ℂ) r, rhoVar m' e s ≠ 0 ∧ e ∈ ball (0 : ℂ) r1 := fun e he =>
    hrr (by rwa [mem_ball] at he)
  have hsub : ball (0 : ℂ) r ⊆ ball (0 : ℂ) r1 := fun e he => (hball e he).2
  have hεk : ∀ e ∈ ball (0 : ℂ) r, ‖e‖ * C < 1 := by
    intro e he
    have h := lt_of_lt_of_le (mem_ball_zero_iff.1 (hsub he)) (min_le_right _ _)
    rw [lt_div_iff₀ hC1] at h
    nlinarith [norm_nonneg e]
  have hQ : ∀ {m φ : ℂ → ℂ}, IsHarmonicU m φ →
      ContDiffOn ℝ 2 (fun e => ∫ t in upperHalf, m t * kernelKbar (fun y => e * m' y) t s ^ 2) (ball 0 r1) →
      ContDiffOn ℝ 2 (fun e => QfunU m (fun u => e * m' u) s) (ball 0 r) ∧
        ∀ e ∈ ball (0 : ℂ) r, (12 / π : ℂ) * (∫ t in upperHalf, m t * kernelKbar (fun y => e * m' y) t s ^ 2) =
          rhoVar m' e s * QfunU m (fun u => e * m' u) s := by
    intro m φ hm hJ
    have heq : ∀ e ∈ ball (0 : ℂ) r, (12 / π : ℂ) * (∫ t in upperHalf, m t * kernelKbar (fun y => e * m' y) t s ^ 2) =
        rhoVar m' e s * QfunU m (fun u => e * m' u) s := fun e he =>
      (s71_eq_7_1 hm hharm hC0 hmB (hεk e he) hs).symm
    refine ⟨(((contDiffOn_const (c := (12 / π : ℂ))).mul (hJ.mono hsub)).mul ((hDr.mono hsub).inv fun e he => (hball e he).1)).congr
      fun e he => ?_, heq⟩
    rw [Pi.inv_apply, ← div_eq_mul_inv, eq_div_iff (hball e he).1, heq e he]
    ring
  obtain ⟨hYr, hYe⟩ := hQ hνh hJν
  obtain ⟨hQμr, hXe⟩ := hQ hμh hJμ
  have hXr : ContDiffOn ℝ 2 (fun e => conj (QfunU mμ (fun u => e * m' u) s)) (ball 0 r) :=
    (Complex.conjCLE.contDiff.comp_contDiffOn hQμr).congr fun e _ => rfl
  have hDr' := hDr.mono hsub
  -- the factor `C`
  obtain ⟨c, hcd⟩ : ∃ c : ℂ, c = ((‖m' s‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hCf : (fun e : ℂ => (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2 : ℂ)) = fun e => 1 - c * (e * conj e) := by
    funext e
    rw [hcd, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  obtain ⟨hCq1, hCq2, hCq3⟩ := s7g_f2_Cquad c
  have hCr : ContDiffOn ℝ 2 (fun e : ℂ => (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2 : ℂ)) (ball 0 r) := by
    rw [hCf]
    exact (contDiff_const.sub (contDiff_const.mul (contDiff_id.mul Complex.conjCLE.contDiff))).contDiffOn
  have hCd1 : dz (fun e : ℂ => (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2 : ℂ)) 0 = 0 := by
    rw [hCf, hCq1]
    simp
  have hCd2 : dzbar (fun e : ℂ => (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2 : ℂ)) 0 = 0 := by
    rw [hCf, hCq2]
    simp
  have hCdd : dzbar (dz fun e : ℂ => (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2 : ℂ)) 0 = -c := by
    rw [hCf, hCq1, hCq3]
  -- the factor `D`
  have hDreal : (fun e => rhoVar m' e s) = fun e => conj (rhoVar m' e s) :=
    funext fun e => (s71_rho_real m' e s).symm
  have hDd1 : dz (fun e => rhoVar m' e s) 0 = 0 := lemma_6_1 hharm hs
  have hDd2 : dzbar (fun e => rhoVar m' e s) 0 = 0 := by
    rw [hDreal, p71r_dzbar_conj, hDd1, map_zero]
  have hDdd : dzbar (dz fun e => rhoVar m' e s) 0 = rhoU s * resolventOpU (fun u => (‖m' u‖ ^ 2 : ℝ)) s := by
    rw [hDreal, s7g_f2_conjW, prop_6_3 hharm hs, map_mul, Complex.conj_ofReal,
      s7g_f2_res_real (fun u => ‖m' u‖ ^ 2)]
  -- the factors `X`, `Y`
  have hX1 : dzbar (fun e => conj (QfunU mμ (fun u => e * m' u) s)) 0 = 0 := by
    rw [p71r_dzbar_conj, (p71_prop_7_1U hμh hharm hs).2.1, map_zero]
  have hY1 : dz (fun e => QfunU mν (fun u => e * m' u) s) 0 = 0 := (p71_prop_7_1U hνh hharm hs).2.1
  have hXd : dz (fun e => conj (QfunU mμ (fun u => e * m' u) s)) 0 =
      conj (dzbar (fun e => QfunU mμ (fun u => e * m' u) s) 0) := s7g_f2_dz_conj _ 0
  -- `T₂` and `T₃` as second derivatives of products
  have hc : conj (12 / π : ℂ) = 12 / π := by
    rw [map_div₀, Complex.conj_ofReal, map_ofNat]
  have hballn : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
  have hT2 : (12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0 =
      dzbar (dz fun e => rhoVar m' e s * QfunU mν (fun u => e * m' u) s) 0 := by
    rw [← s7g_f2_wconst hr (hJν.mono hsub)]
    exact s7g_f2_germ (Filter.eventually_of_mem hballn hYe)
  have hT3 : conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) =
      dzbar (dz fun e => rhoVar m' e s * conj (QfunU mμ (fun u => e * m' u) s)) 0 := by
    have hJc : ContDiffOn ℝ 2 (fun e => conj (∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2))
        (ball 0 r) :=
      (Complex.conjCLE.contDiff.comp_contDiffOn (hJμ.mono hsub)).congr fun e _ => rfl
    rw [map_mul, hc, ← s7g_f2_conjW, ← s7g_f2_wconst hr hJc]
    refine s7g_f2_germ (Filter.eventually_of_mem hballn fun e he => ?_)
    have h := congrArg conj (hXe e he)
    simp only [map_mul, hc, s71_rho_real] at h
    exact h
  have key := s7g_f2_ptalg hr hXr hYr hCr hDr' hX1 hY1 (by simp) hCd1 hCd2 hDd1 hDd2
  rw [hCdd, hDdd, hXd, hD0, s7g_f2_Q0 hμh hs, s7g_f2_Q0 hνh hs, hcd] at key
  rw [hT2, hT3]
  linear_combination key

/-- `\overline{m₁} m₂ h ρ` is integrable on `𝕌` for weights of finite weighted `L²` norm and bounded `h`. -/
theorem s7g_f2_wint {m1 m2 h : ℂ → ℂ} (h1c : ContinuousOn m1 upperHalf) (h2c : ContinuousOn m2 upperHalf)
    (hhc : ContinuousOn h upperHalf) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ u ∈ upperHalf, ‖h u‖ ≤ M)
    (h1 : ∫⁻ u in upperHalf, ‖m1 u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞)
    (h2 : ∫⁻ u in upperHalf, ‖m2 u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) < ∞) :
    IntegrableOn (fun u => conj (m1 u) * m2 u * h u * rhoU u) upperHalf := by
  have hU := measurableSet_upperHalf_aux
  have hρ0 : ∀ u, 0 ≤ rhoU u := fun u => inv_nonneg.2 (sq_nonneg _)
  have hρr : ContinuousOn rhoU upperHalf := by
    show ContinuousOn (fun u : ℂ => (u.im ^ 2)⁻¹) upperHalf
    exact ((Complex.continuous_im.pow 2).continuousOn).inv₀ fun u hu => by
      have : 0 < u.im := hu
      exact pow_ne_zero 2 this.ne'
  have hρc : ContinuousOn (fun u : ℂ => ((rhoU u : ℝ) : ℂ)) upperHalf :=
    Complex.continuous_ofReal.comp_continuousOn hρr
  have hmeas : AEStronglyMeasurable (fun u => conj (m1 u) * m2 u * h u * rhoU u) (volume.restrict upperHalf) :=
    ((((Complex.continuous_conj.comp_continuousOn h1c).mul h2c).mul hhc).mul hρc).aestronglyMeasurable hU
  have hgc : ContinuousOn (fun u => M * ((‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * rhoU u)) upperHalf :=
    continuousOn_const.mul ((((continuous_norm.comp_continuousOn h1c).pow 2).add
      ((continuous_norm.comp_continuousOn h2c).pow 2)).mul hρr)
  have ha1 : AEMeasurable (fun u => ‖m1 u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) (volume.restrict upperHalf) :=
    ((h1c.aestronglyMeasurable hU).enorm.pow_const 2).mul (ENNReal.measurable_ofReal.comp_aemeasurable
      (hρr.aestronglyMeasurable hU).aemeasurable)
  have hgi : IntegrableOn (fun u => M * ((‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * rhoU u)) upperHalf := by
    refine ⟨hgc.aestronglyMeasurable hU, (hasFiniteIntegral_iff_ofReal ?_).2 ?_⟩
    · exact Eventually.of_forall fun u => by
        show (0 : ℝ) ≤ M * ((‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * rhoU u)
        have := hρ0 u
        positivity
    · have e : ∀ u, ENNReal.ofReal (M * ((‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * rhoU u)) =
          ENNReal.ofReal M * (‖m1 u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u) + ‖m2 u‖ₑ ^ 2 * ENNReal.ofReal (rhoU u)) := by
        intro u
        rw [ENNReal.ofReal_mul hM, add_mul, ENNReal.ofReal_add (by have := hρ0 u; positivity)
          (by have := hρ0 u; positivity), ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
          ofReal_norm]
      simp only [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' ha1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨h1, h2⟩)
  refine hgi.mono' hmeas ?_
  filter_upwards [ae_restrict_mem hU] with u hu
  have e : ‖conj (m1 u) * m2 u * h u * (rhoU u : ℂ)‖ = ‖m1 u‖ * ‖m2 u‖ * ‖h u‖ * rhoU u := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hρ0 u)]
  rw [e]
  have hab : ‖m1 u‖ * ‖m2 u‖ ≤ ‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2 := by
    nlinarith [sq_nonneg (‖m1 u‖ - ‖m2 u‖), norm_nonneg (m1 u), norm_nonneg (m2 u)]
  have hh := hb u hu
  have hr := hρ0 u
  calc ‖m1 u‖ * ‖m2 u‖ * ‖h u‖ * rhoU u ≤ (‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * M * rhoU u := by gcongr
    _ = M * ((‖m1 u‖ ^ 2 + ‖m2 u‖ ^ 2) * rhoU u) := by ring

/-- The Cayley transport of `Q̇`: `Q̇(ν)[κ](S η̄) = (S'/\overline{S'}) \overline{∂_ē Q_U(m_ν, e m')(η)}`. -/
theorem s7g_f2_Qdot {ν : ℂ → ℂ} (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) {g : ℂ → ℂ} (hg : ContinuousOn g unitDiscExterior)
    (hgκ : ∀ᵐ z ∂(volume.restrict unitDiscExterior), κ z = g z) {m' φ' : ℂ → ℂ} (hharm : IsHarmonicU m' φ')
    (hm' : ∀ u ∈ upperHalf, u ≠ I → m' u = conj (g (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {mν φν : ℂ → ℂ} (hνh : IsHarmonicU mν φν)
    (hνf : ∀ u ∈ upperHalf, u ≠ I → mν u = conj (ν (cayley (conj u))) * (cayley u ^ 2 / conj (cayley u) ^ 2) *
      (conj (2 * I / (u + I) ^ 2) / (2 * I / (u + I) ^ 2)))
    {η : ℂ} (hη : η ∈ upperHalf) (hηI : η ≠ I) :
    Qdot (toLinf ν) κ (cayley (conj η)) = 2 * I / (conj η + I) ^ 2 / conj (2 * I / (conj η + I) ^ 2) *
      conj (dzbar (fun e => QfunU mν (fun u => e * m' u) η) 0) := by
  obtain ⟨Cc, hCc⟩ := harmonicL2_subset_harmonic
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
  exact hE

/-- STUB H (transport to `𝔻*`). The three `𝕌`-integrals of the final formula. -/
theorem s7g_f2_transport {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior)
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
    IntegrableOn (fun s => conj (mμ s) * mν s * (‖m' s‖ ^ 2 : ℝ) * rhoU s) upperHalf ∧
      IntegrableOn (fun s => conj (mμ s) * mν s * (rhoU s * resolventOpU (fun u => (‖m' u‖ ^ 2 : ℝ)) s))
        upperHalf ∧
      (∫ s in upperHalf, conj (mμ s) * mν s * (‖m' s‖ ^ 2 : ℝ) * rhoU s) =
        l2Inner (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) ∧
      (∫ s in upperHalf, conj (mμ s) * mν s * (rhoU s * resolventOpU (fun u => (‖m' u‖ ^ 2 : ℝ)) s)) =
        l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖κ z‖ ^ 2 : ℝ)) ∧
      (∫ s in upperHalf, conj (dzbar (fun e => QfunU mμ (fun u => e * m' u) s) 0) *
          dzbar (fun e => QfunU mν (fun u => e * m' u) s) 0 * rhoU s) =
        l2Inner (Qdot (toLinf μ) κ) (Qdot (toLinf ν) κ) := by
  have hU := measurableSet_upperHalf_aux
  have hμn := s7g_f2_mnorm hμf
  have hνn := s7g_f2_mnorm hνf
  have hm'n := s7g_f2_mnorm hm'
  have hfμ := s7g_l3_L2fin hμ hμn
  have hfν := s7g_l3_L2fin hν hνn
  obtain ⟨C, hC0, hCb⟩ := harmonicU_bounded hharm
  have hm'c := harmonicU_continuousOn hharm
  have hμc := harmonicU_continuousOn hμh
  have hνc := harmonicU_continuousOn hνh
  have hsq : ContinuousOn (fun u => ((‖m' u‖ ^ 2 : ℝ) : ℂ)) upperHalf :=
    Complex.continuous_ofReal.comp_continuousOn ((continuous_norm.comp_continuousOn hm'c).pow 2)
  have hsqb : ∀ u ∈ upperHalf, ‖((‖m' u‖ ^ 2 : ℝ) : ℂ)‖ ≤ C ^ 2 := by
    intro u hu
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCb u hu) 2
  have hGc := resolventOpU_continuousOn_of_continuous_bounded hsq hsqb
  have iA := s7g_f2_wint hμc hνc hsq (sq_nonneg C) hsqb hfμ hfν
  have iB : IntegrableOn (fun s => conj (mμ s) * mν s *
      ((rhoU s : ℂ) * resolventOpU (fun u => ((‖m' u‖ ^ 2 : ℝ) : ℂ)) s)) upperHalf := (s7g_f2_wint hμc hνc hGc (sq_nonneg C) (fun u hu => resolventOpU_norm_le hsqb hu) hfμ hfν).congr_fun
    (fun s _ => by ring) hU
  -- pointwise transport data on `𝕌 ∖ {i}`
  have hpt : ∀ η ∈ upperHalf, η ≠ I →
      2 * I / (conj η + I) ^ 2 ≠ 0 ∧ conj (2 * I / (conj η + I) ^ 2) ≠ 0 ∧
      μ (cayley (conj η)) * (conj (2 * I / (conj η + I) ^ 2) / (2 * I / (conj η + I) ^ 2)) = conj (mμ η) ∧
      conj (ν (cayley (conj η))) * (2 * I / (conj η + I) ^ 2 / conj (2 * I / (conj η + I) ^ 2)) = mν η ∧
      (((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) =
        2 * I / (conj η + I) ^ 2 * conj (2 * I / (conj η + I) ^ 2)) ∧
      (rhoU η : ℂ) = (rho (cayley (conj η)) : ℂ) * ((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) := by
    intro η hη hηI
    have hc : conj η + I ≠ 0 := s7g_l3_cne hηI
    have hφ : 2 * I / (conj η + I) ^ 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (pow_ne_zero _ hc)
    refine ⟨hφ, (map_ne_zero _).2 hφ, s7g_l3_Aconj μ hη hηI (hμf η hη hηI), ?_, ?_, ?_⟩
    · have h := congrArg conj (s7g_l3_Aconj ν hη hηI (hνf η hη hηI))
      simpa only [map_mul, map_div₀, Complex.conj_conj] using h
    · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [← (p71r_iso hη hη hηI hηI).2, Complex.ofReal_mul]
  refine ⟨iA, iB, ?_, ?_, ?_⟩
  · have hκg : l2Inner (fun z => μ z * conj (κ z)) (fun z => ν z * conj (κ z)) =
        ∫ z in unitDiscExterior, μ z * conj (g z) * conj (ν z * conj (g z)) * (rho z : ℂ) := by
      unfold l2Inner
      refine integral_congr_ae ?_
      filter_upwards [hgκ] with z hz
      rw [hz]
    rw [hκg, p71_cov]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hη hηI
    obtain ⟨hφ, hφc, hA, hB, eφ, eρ⟩ := hpt η hη hηI
    have eg : ((‖g (cayley (conj η))‖ ^ 2 : ℝ) : ℂ) = g (cayley (conj η)) * conj (g (cayley (conj η))) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← hA, ← hB, hm'n η hη hηI, eρ, eφ, eg]
    simp only [map_mul, Complex.conj_conj]
    field_simp
  · unfold l2Inner
    rw [p71_cov]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hη hηI
    obtain ⟨hφ, hφc, hA, hB, eφ, eρ⟩ := hpt η hη hηI
    have hR : resolventStar (fun z => ((‖κ z‖ ^ 2 : ℝ) : ℂ)) (cayley (conj η)) =
        resolventStar (fun z => ((‖g z‖ ^ 2 : ℝ) : ℂ)) (cayley (conj η)) := by
      unfold resolventStar resolventOp
      refine integral_congr_ae ?_
      filter_upwards [hgκ] with z hz
      rw [hz]
    have hG : resolventOpU (fun w => ((‖g (cayley (conj w))‖ ^ 2 : ℝ) : ℂ)) η =
        resolventOpU (fun u => ((‖m' u‖ ^ 2 : ℝ) : ℂ)) η := by
      unfold resolventOpU
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with w hw hwI
      rw [hm'n w hw hwI]
    show conj (mμ η) * mν η * ((rhoU η : ℂ) * resolventOpU (fun u => ((‖m' u‖ ^ 2 : ℝ) : ℂ)) η) =
      ((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) * (μ (cayley (conj η)) * conj (ν (cayley (conj η))) *
        conj (resolventStar (fun z => ((‖κ z‖ ^ 2 : ℝ) : ℂ)) (cayley (conj η))) * (rho (cayley (conj η)) : ℂ))
    rw [hR, p71r_cov _ hη hηI, hG, s7g_f2_res_real (fun u => ‖m' u‖ ^ 2), ← hA, ← hB, eρ, eφ]
    field_simp
  · unfold l2Inner
    rw [p71_cov]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hU, ae_restrict_of_ae (Measure.ae_ne volume I)] with η hη hηI
    obtain ⟨hφ, hφc, -, -, eφ, eρ⟩ := hpt η hη hηI
    show conj (dzbar (fun e => QfunU mμ (fun u => e * m' u) η) 0) *
        dzbar (fun e => QfunU mν (fun u => e * m' u) η) 0 * (rhoU η : ℂ) =
      ((‖2 * I / (conj η + I) ^ 2‖ ^ 2 : ℝ) : ℂ) * (Qdot (toLinf μ) κ (cayley (conj η)) *
        conj (Qdot (toLinf ν) κ (cayley (conj η))) * (rho (cayley (conj η)) : ℂ))
    rw [s7g_f2_Qdot hμ hκ hg hgκ hharm hm' hμh hμf hη hηI, s7g_f2_Qdot hν hκ hg hgκ hharm hm' hνh hνf hη hηI,
      eρ, eφ]
    simp only [map_mul, map_div₀, Complex.conj_conj]
    field_simp

/-- `thm_7_7`, assembled from the stubs, `s7g_line_C2`, `s7g_l3_weight` and `cor_7_3`. -/
theorem s7g_thm_7_7 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    dz (dzbar fun ε => gWP μ ν (ε • κ)) 0 =
      l2Inner (fun z => μ z * conj (κ z)) (resolventStar fun z => ν z * conj (κ z)) +
        l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  have hU := measurableSet_upperHalf_aux
  obtain ⟨g, hgs, hgκ⟩ := wr_harm_rep hκ
  have hg : ContinuousOn g unitDiscExterior := hgs.continuousOn
  obtain ⟨m', φ', hharm, hm'⟩ := p71_wm_harm hκ hg hgκ
  obtain ⟨mμ, φμ, hμh, hμf, -⟩ := s7g_l3_weight hμ
  obtain ⟨mν, φν, hνh, hνf, -⟩ := s7g_l3_weight hν
  obtain ⟨r, hr, hC⟩ := s7g_line_C2 hμ hν hκ
  have hLC : ContDiffOn ℝ 2 (fun e : ℂ => gWP μ ν (conj e • κ)) (ball 0 r) := by
    have hm : MapsTo (fun e : ℂ => conj e) (ball 0 r) (ball 0 r) := fun e he => by
      rw [mem_ball_zero_iff, Complex.norm_conj]
      exact mem_ball_zero_iff.1 he
    exact hC.comp Complex.conjCLE.contDiff.contDiffOn hm
  have hG : (fun ε : ℂ => gWP μ ν (ε • κ)) = fun ε => (fun e : ℂ => gWP μ ν (conj e • κ)) (conj ε) := by
    funext ε
    simp only [Complex.conj_conj]
  rw [hG, s7g_f2_conjflip hr hLC]
  obtain ⟨-, hT2i, hT2, -, -⟩ := s7g_f2_line2 hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf
  obtain ⟨-, -, -, hT3i, hT3⟩ := s7g_f2_line2 hν hμ hκ hg hgκ hharm hm' hνh hνf hμh hμf
  obtain ⟨r1, hr1, hl1⟩ := s7g_f2_line1U hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf
  obtain ⟨hT1i, hT1⟩ := s7g_f2_line1D hμ hν hharm hμh hμf hνh hνf
  obtain ⟨hAi, hBi, hA, hB, hQ⟩ := s7g_f2_transport hμ hν hκ hg hgκ hharm hm' hμh hμf hνh hνf
  -- the three expressions of `L̈ = ∂_ē∂_e g(ē κ)|₀`
  have e1 := (s7g_f2_germ (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr1) hl1)).trans hT1
  have e3 : dzbar (dz fun e : ℂ => gWP μ ν (conj e • κ)) 0 = ∫ s in upperHalf, mν s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) := by
    have hsym : (fun e : ℂ => gWP μ ν (conj e • κ)) = fun e => conj (gWP ν μ (conj e • κ)) := by
      funext e
      rw [s7g_f2_herm ν μ]
    rw [hsym, s7g_f2_conjW, hT3, map_mul, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have I2 : IntegrableOn (fun s => conj (mμ s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0)) upperHalf := by
    refine (hT2i.const_mul (12 / π : ℂ)).congr (Eventually.of_forall fun s => ?_)
    simp only []
    ring
  have I3 : IntegrableOn (fun s => mν s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) 0)) upperHalf := by
    refine ((Complex.conjCLE.toContinuousLinearMap.integrable_comp hT3i).const_mul (12 / π : ℂ)).congr
      (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_div₀, map_ofNat,
      Complex.conj_ofReal, Complex.conj_conj]
    ring
  have e2' : dzbar (dz fun e : ℂ => gWP μ ν (conj e • κ)) 0 = ∫ s in upperHalf, conj (mμ s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) := by
    rw [hT2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only []
    ring
  -- pointwise: `T₁ - T₂ - T₃ = R`
  -- named integrands
  obtain ⟨T1, hT1d⟩ : ∃ T1 : ℂ → ℂ, T1 = fun s => dzbar (dz fun e => conj (QfunU mμ (fun u => e * m' u) s) *
      QfunU mν (fun u => e * m' u) s * (1 - ‖e‖ ^ 2 * ‖m' s‖ ^ 2) * rhoVar m' e s) 0 := ⟨_, rfl⟩
  obtain ⟨T2, hT2d⟩ : ∃ T2 : ℂ → ℂ, T2 = fun s => conj (mμ s) * ((12 / π : ℂ) *
      dzbar (dz fun e => ∫ t in upperHalf, mν t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) := ⟨_, rfl⟩
  obtain ⟨T3, hT3d⟩ : ∃ T3 : ℂ → ℂ, T3 = fun s => mν s * conj ((12 / π : ℂ) *
      dz (dzbar fun e => ∫ t in upperHalf, mμ t * kernelKbar (fun y => e * m' y) t s ^ 2) 0) := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun s => conj (mμ s) * mν s * (‖m' s‖ ^ 2 : ℝ) * rhoU s := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun s =>
      conj (mμ s) * mν s * (rhoU s * resolventOpU (fun u => (‖m' u‖ ^ 2 : ℝ)) s) := ⟨_, rfl⟩
  obtain ⟨Cq, hCd⟩ : ∃ Cq : ℂ → ℂ, Cq = fun s => conj (dzbar (fun e => QfunU mμ (fun u => e * m' u) s) 0) *
      dzbar (fun e => QfunU mν (fun u => e * m' u) s) 0 * rhoU s := ⟨_, rfl⟩
  have i1 : IntegrableOn T1 upperHalf := by rw [hT1d]; exact hT1i
  have i2 : IntegrableOn T2 upperHalf := by rw [hT2d]; exact I2
  have i3 : IntegrableOn T3 upperHalf := by rw [hT3d]; exact I3
  have iA : IntegrableOn A upperHalf := by rw [hAd]; exact hAi
  have iB : IntegrableOn B upperHalf := by rw [hBd]; exact hBi
  have hpt : ∀ s ∈ upperHalf, T1 s - T2 s - T3 s = -A s - B s + Cq s := by
    intro s hs
    rw [hT1d, hT2d, hT3d, hAd, hBd, hCd]
    exact s7g_f2_pt hharm hμh hνh hs
  have iC : IntegrableOn Cq upperHalf := by
    refine (((i1.sub i2).sub i3).add (iA.add iB)).congr ?_
    filter_upwards [ae_restrict_mem hU] with s hs
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt s hs]
    ring
  have hR : ∫ s in upperHalf, (T1 s - T2 s - T3 s) = ∫ s in upperHalf, (-A s - B s + Cq s) :=
    setIntegral_congr_fun hU hpt
  rw [integral_sub (f := fun s => T1 s - T2 s) (i1.sub i2) i3, integral_sub i1 i2,
    integral_add (f := fun s => -A s - B s) (iA.neg.sub iB) iC, integral_sub (f := fun s => -A s) iA.neg iB,
    integral_neg] at hR
  rw [← hT1d] at e1
  rw [← hT2d] at e2'
  rw [← hT3d] at e3
  rw [← hAd] at hA
  rw [← hBd] at hB
  rw [← hCd] at hQ
  rw [← e1, ← e2', ← e3, hA, hB, hQ, cor_7_3 hμ hν hκ] at hR
  linear_combination -hR

/-- **Theorem 7.7** (TT:2878–2882). For `μ, ν ∈ H^{-1,1}(𝔻*)` and `κ ∈ Ω^{-1,1}(𝔻*)`:
`∂²/∂ε∂ε̄ g_{μν̄}(εκ)|_{ε=0} = (μκ̄, G(νκ̄)) + (μν̄, G(|κ|²))`. -/
theorem thm_7_7 {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) (hν : ν ∈ harmonicL2 unitDiscExterior)
    {κ : LinfStar} (hκ : κ ∈ harmonicBeltrami) :
    dz (dzbar fun ε => gWP μ ν (ε • κ)) 0 =
      l2Inner (fun z => μ z * conj (κ z)) (resolventStar fun z => ν z * conj (κ z)) +
        l2Inner (fun z => μ z * conj (ν z)) (resolventStar fun z => (‖κ z‖ ^ 2 : ℝ)) := by
  exact s7g_thm_7_7 hμ hν hκ

end TakhtajanTeo
