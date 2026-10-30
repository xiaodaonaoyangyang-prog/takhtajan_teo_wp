import TakhtajanTeo.Ch2.S1_BP78Completed
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.QCVariationCovariance
import TakhtajanTeo.Ch1.QCVariationSurjSmall

/-!
# Theorem 1.6 (Becker–Pommerenke), (i) ⇒ (ii) ⇒ (iii) (prefix `bpa_`)

Route: an analytic splitting, in place of the blow-up. Fix `ε`, take `ρ ∈ (1, R)` with `|μ_F| ≤ ε` on
`1 < |z| < ρ`, and let `ν = μ_F · 1_{1<|z|<ρ}` on `𝔻*`.
- `W = qcv_planeSolution ν` is conformal on `𝔻`, and `H = F ∘ W⁻¹` is conformal on `W(B(0, ρ))`, since the two maps
  have equal dilatations there (`ahQ_comp_inv_dilatation`). Then `f = H ∘ W` on `𝔻` (`bpa_factor`).
- `S_f = (S_H ∘ W) W'² + S_W` (`bpa_schwarzian_comp`), with:
  - `(1-|z|²)²|S_W| ≤ ‖βΦ(ν)‖ ≤ 7‖ν‖ ≤ 7ε` (Schwarz lemma for `t ↦ βΦ(tν)` with Nehari's bound `6`; this gives
    `bpa_bersPhi_le` and `bpa_weighted_S_le`);
  - `S_H` bounded on the compact `W(𝔻̄)`;
  - `(1-|z|²)|W'(z)| ≤ 4 dist(W z, W(z/|z|)) → 0` (Koebe 1/4, `bpa_koebe_decay`).
- (ii) ⇒ (iii) is `ab16_ii_imp_iii`.
The TFAE assembly `bpa_thm_1_6` lives in a final module with 下属1's (iii) ⇒ (i).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

namespace Ch2

/-- Schwarz lemma for the Bers map: `‖βΦ(ν)‖ ≤ 7 ‖ν‖` on `L∞(𝔻*)₁`. -/
theorem bpa_bersPhi_le {ν : LinfStar} (hν : ν ∈ LinfStarBall) : ‖bersPhi ν‖ ≤ 7 * ‖ν‖ := by
  by_cases h0 : ν = 0
  · rw [h0, QCV.qs_bersPhi_zero, norm_zero, norm_zero, mul_zero]
  have hn : 0 < ‖ν‖ := norm_pos_iff.mpr h0
  have hn1 : ‖ν‖ < 1 := mem_ball_zero_iff.mp hν
  have hnC : ((‖ν‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ : ∃ u : LinfStar, u = ((‖ν‖ : ℂ))⁻¹ • ν := ⟨_, rfl⟩
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le, inv_mul_cancel₀ hn.ne']
  have hmaps : MapsTo (fun t : ℂ => t • u) (ball (0 : ℂ) 1) LinfStarBall := by
    intro t ht
    show t • u ∈ ball (0 : LinfStar) 1
    rw [mem_ball_zero_iff, norm_smul, hun, mul_one]
    exact mem_ball_zero_iff.mp ht
  have hd : DifferentiableOn ℂ (fun t : ℂ => bersPhi (t • u)) (ball (0 : ℂ) 1) :=
    QCV.qcv_bersPhi_differentiableOn.comp ((differentiable_id.smul_const u).differentiableOn) hmaps
  have hmaps2 : MapsTo (fun t : ℂ => bersPhi (t • u)) (ball (0 : ℂ) 1)
      (closedBall ((fun t : ℂ => bersPhi (t • u)) 0) 6) := by
    intro t ht
    simp only [zero_smul, QCV.qs_bersPhi_zero, mem_closedBall, dist_zero_right]
    exact (bersPhi_spec (hmaps ht)).2
  have hz : ((‖ν‖ : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hn.le]
    exact hn1
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps2 hz
  have hνu : ((‖ν‖ : ℝ) : ℂ) • u = ν := by rw [hu, smul_smul, mul_inv_cancel₀ hnC, one_smul]
  simp only [zero_smul, QCV.qs_bersPhi_zero, dist_zero_right, hνu, div_one, Complex.norm_real,
    Real.norm_of_nonneg hn.le] at hS
  linarith

/-- The weighted Schwarzian of the plane solution `W^ν` is bounded by `‖βΦ(ν)‖`. -/
theorem bpa_weighted_S_le {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol (QCV.qcv_planeSolution ν) z‖ ≤ ‖bersPhi ν‖ := by
  have hS : schwarzianHol (QCV.qcv_planeSolution ν) z = AInf.toFun (bersPhi ν) z := by
    rw [(bersPhi_spec hν).1 z hz, QCV.qcv_schwarzian_fB_eq hν hz]
    rfl
  rw [hS]
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hden : ((1 : ℂ) - (‖z‖ : ℂ) ^ 2) ^ 2 ≠ 0 := by
    have : ((1 : ℂ) - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact pow_ne_zero 2 (by exact_mod_cast (show (1 - ‖z‖ ^ 2 : ℝ) ≠ 0 by nlinarith [norm_nonneg z]))
  have he : ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * AInf.toFun (bersPhi ν) z = (bersPhi ν).1 ⟨z, hz⟩ := by
    show ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * unweight unitDisc (bersPhi ν).1 z = _
    simp only [unweight, hz, ↓reduceDIte]
    have hden1 : (1 : ℂ) - (‖z‖ : ℂ) ^ 2 ≠ 0 := fun h => hden (by rw [h]; ring)
    field_simp
  rw [he]
  exact (bersPhi ν).1.norm_coe_le_norm _

/-- Koebe decay: `(1 - |z|²) |W'(z)| → 0` as `|z| → 1⁻` for `W = W^ν` (continuous and injective on `ℂ`). -/
theorem bpa_koebe_decay {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    Tendsto (fun z => (1 - ‖z‖ ^ 2) * ‖deriv (QCV.qcv_planeSolution ν) z‖)
      (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  have hk : ‖ν‖ < 1 := mem_ball_zero_iff.mp hν
  obtain ⟨hN, hhol, hinj, -⟩ := QCV.qcv_W_props hk
  obtain ⟨⟨K, hK⟩, -⟩ := hN
  obtain ⟨W, hW⟩ : ∃ W : ℂ → ℂ, W = QCV.qcv_planeSolution ν := ⟨_, rfl⟩
  have hhol' : DifferentiableOn ℂ W unitDisc := by rw [hW]; exact hhol
  have hinj' : InjOn W univ := by rw [hW]; exact hinj
  have hcont : Continuous W := by rw [hW]; exact continuousOn_univ.mp hK.2.2.1.1
  rw [← hW]
  -- Koebe: `(1 - |z|²) |W'(z)| ≤ 4 |W(z/|z|) - W(z)|`
  have hkoebe : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv W z‖ ≤ 4 * ‖W (z / (‖z‖ : ℂ)) - W z‖ := by
    intro z hz0 hz1
    have ha : ‖-z‖ < 1 := by rwa [norm_neg]
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz1
    have hb0 : blaschke (-z) 0 = z := by simp [blaschke]
    have hbd := hasDerivAt_blaschke ha (show ‖(0 : ℂ)‖ < 1 by simp)
    have hval : (1 - -z * conj (-z)) / (1 - conj (-z) * 0) ^ 2 = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) := by
      rw [map_neg, neg_mul_neg, mul_zero, sub_zero, one_pow, div_one, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hval] at hbd
    have hWd : HasDerivAt W (deriv W z) (blaschke (-z) 0) := by
      rw [hb0]
      exact (hhol'.differentiableAt (isOpen_ball.mem_nhds hzD)).hasDerivAt
    have hψd : HasDerivAt (fun u => W (blaschke (-z) u) - W z)
        (deriv W z * (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ)) 0 := (hWd.comp 0 hbd).sub_const (W z)
    have hmaps : MapsTo (blaschke (-z)) (ball (0 : ℂ) 1) unitDisc := fun u hu =>
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp hu))
    have hψ : DifferentiableOn ℂ (fun u => W (blaschke (-z) u) - W z) (ball (0 : ℂ) 1) :=
      (hhol'.comp (differentiableOn_blaschke ha) hmaps).sub_const _
    have hψinj : InjOn (fun u => W (blaschke (-z) u) - W z) (ball (0 : ℂ) 1) := by
      intro u hu v hv h
      have h1 := hinj' (mem_univ _) (mem_univ _) (sub_left_inj.mp h)
      exact (isConformalOnto_blaschke ha).2.1 hu hv h1
    have hψ0 : (fun u => W (blaschke (-z) u) - W z) 0 = 0 := by simp only [hb0, sub_self]
    have hζ : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hz0.le, div_self hz0.ne']
    have hw : W (z / (‖z‖ : ℂ)) - W z ∉ (fun u => W (blaschke (-z) u) - W z) '' ball (0 : ℂ) 1 := by
      rintro ⟨u, hu, he⟩
      have h1 := hinj' (mem_univ _) (mem_univ _) (sub_left_inj.mp he)
      have h2 := blaschke_mem_unitDisc ha (mem_ball_zero_iff.mp hu)
      rw [h1, hζ] at h2
      exact lt_irrefl _ h2
    have hq := koebe_quarter_of_not_mem hψ hψinj hψ0 hw
    rw [hψd.deriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)] at hq
    linarith
  -- uniform continuity on the closed disc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hcont.continuousOn) (ε / 4)
    (by positivity)
  have hlt : max (1 - δ) 0 < 1 := max_lt (by linarith) one_pos
  have hev : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝[<] 1), ‖z‖ ∈ Ioo (max (1 - δ) 0) 1 :=
    tendsto_comap.eventually (Ioo_mem_nhdsLT hlt)
  filter_upwards [hev] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz1
  have hzδ : 1 - δ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz1
  have hdist : dist (z / (‖z‖ : ℂ)) z < δ := by
    have he : z / (‖z‖ : ℂ) - z = ((1 / ‖z‖ - 1 : ℝ) : ℂ) * z := by
      push_cast
      field_simp
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hz0]; linarith)]
    rw [sub_mul, div_mul_cancel₀ _ hz0.ne', one_mul]
    linarith
  have hm1 : z / (‖z‖ : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hz0.le, div_self hz0.ne']
  have hm2 : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz2.le
  have hW1 := hu _ hm1 _ hm2 hdist
  rw [dist_eq_norm] at hW1
  have hk := hkoebe z hz0 hz2
  have hnn : 0 ≤ (1 - ‖z‖ ^ 2) * ‖deriv W z‖ := mul_nonneg (by nlinarith) (norm_nonneg _)
  rw [dist_zero_right, Real.norm_of_nonneg hnn]
  linarith

/-- Chain rule for the Schwarzian: `S_{H∘g} = (S_H ∘ g) g'² + S_g`. -/
theorem bpa_schwarzian_comp {H g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hH : AnalyticAt ℂ H (g z))
    (hg' : deriv g z ≠ 0) (hH' : deriv H (g z) ≠ 0) :
    schwarzianHol (H ∘ g) z = schwarzianHol H (g z) * deriv g z ^ 2 + schwarzianHol g z := by
  have hgev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g w := hg.eventually_analyticAt
  have hHev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ H (g w) := hg.continuousAt.eventually hH.eventually_analyticAt
  have hg'ev : ∀ᶠ w in 𝓝 z, deriv g w ≠ 0 := hg.deriv.continuousAt.eventually_ne hg'
  have hH'ev : ∀ᶠ w in 𝓝 z, deriv H (g w) ≠ 0 :=
    (hH.deriv.continuousAt.comp hg.continuousAt).eventually_ne hH'
  have hd1 : ∀ᶠ w in 𝓝 z, deriv (H ∘ g) w = deriv H (g w) * deriv g w := by
    filter_upwards [hgev, hHev] with w hw hHw
    exact deriv_comp w hHw.differentiableAt hw.differentiableAt
  have hd2 : ∀ᶠ w in 𝓝 z, deriv (deriv (H ∘ g)) w =
      deriv (deriv H) (g w) * deriv g w * deriv g w + deriv H (g w) * deriv (deriv g) w := by
    filter_upwards [hd1.eventually_nhds, hgev, hHev] with w hw1 hw hHw
    have hw1' : deriv (H ∘ g) =ᶠ[𝓝 w] fun x => deriv H (g x) * deriv g x := hw1
    rw [hw1'.deriv_eq]
    have h1 : HasDerivAt (fun w => deriv H (g w)) (deriv (deriv H) (g w) * deriv g w) w :=
      hHw.deriv.differentiableAt.hasDerivAt.comp w hw.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) w) w := hw.deriv.differentiableAt.hasDerivAt
    exact (h1.mul h2).deriv
  have hA : (fun w => deriv (deriv (H ∘ g)) w / deriv (H ∘ g) w) =ᶠ[𝓝 z]
      fun w => deriv (deriv H) (g w) / deriv H (g w) * deriv g w + deriv (deriv g) w / deriv g w := by
    filter_upwards [hd1, hd2, hg'ev, hH'ev] with w h1 h2 hgw hHw
    rw [h1, h2]
    field_simp
    try ring
  have hAH : HasDerivAt (fun y => deriv (deriv H) y / deriv H y)
      (deriv (fun y => deriv (deriv H) y / deriv H y) (g z)) (g z) :=
    (hH.deriv.deriv.div hH.deriv hH').differentiableAt.hasDerivAt
  have hAg : HasDerivAt (fun w => deriv (deriv g) w / deriv g w)
      (deriv (fun w => deriv (deriv g) w / deriv g w) z) z :=
    (hg.deriv.deriv.div hg.deriv hg').differentiableAt.hasDerivAt
  have htot : HasDerivAt
      (fun w => deriv (deriv H) (g w) / deriv H (g w) * deriv g w + deriv (deriv g) w / deriv g w)
      (deriv (fun y => deriv (deriv H) y / deriv H y) (g z) * deriv g z * deriv g z +
        deriv (deriv H) (g z) / deriv H (g z) * deriv (deriv g) z +
        deriv (fun w => deriv (deriv g) w / deriv g w) z) z :=
    ((hAH.comp z hg.differentiableAt.hasDerivAt).mul hg.deriv.differentiableAt.hasDerivAt).add hAg
  unfold schwarzianHol
  rw [hA.deriv_eq, htot.deriv, hd2.self_of_nhds, hd1.self_of_nhds]
  field_simp
  ring

/-- The splitting: a q.c. extension `F` with `μ_F → 0` at `|z| = 1⁺` factors, for each `ε`, as `f = H ∘ W^ν` on `𝔻`
with `‖ν‖ ≤ ε` and `H` conformal near `W^ν(𝔻̄)`. -/
theorem bpa_factor {f F : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hF : IsQuasiconformal F (ball 0 R))
    (hFf : EqOn F f unitDisc) (hf : DifferentiableOn ℂ f unitDisc)
    (hμ : Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ν ∈ LinfStarBall, ‖ν‖ ≤ ε ∧ ∃ H : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧
      QCV.qcv_planeSolution ν '' closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ H U ∧ InjOn H U ∧
      ∀ z ∈ unitDisc, f z = H (QCV.qcv_planeSolution ν z) := by
  obtain ⟨K, hK⟩ := hF
  -- the radius `ρ`
  have hev := (Metric.tendsto_nhds.mp hμ) ε hε
  rw [Filter.eventually_comap] at hev
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min u ((1 + R) / 2) := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρ]; exact lt_min hu1 (by linarith)
  have hρR : ρ < R := by rw [hρ]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < ρ → ‖complexDilatation F z‖ < ε := by
    intro z h1 h2
    have h := hu ⟨h1, lt_of_lt_of_le h2 (by rw [hρ]; exact min_le_left _ _)⟩ z rfl
    rwa [dist_zero_right] at h
  -- the coefficient `ν`
  let A : Set ℂ := {z : ℂ | 1 < ‖z‖} ∩ {z : ℂ | ‖z‖ < ρ}
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm measurable_const)
  have hμm : Measurable (complexDilatation F) := (measurable_dzbar F).div (measurable_dz F)
  have hbound : ∀ z, ‖A.indicator (complexDilatation F) z‖ ≤ ε := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      exact (hsmall z hz.1 hz.2).le
    · rw [indicator_of_notMem hz, norm_zero]
      exact hε.le
  have hmem : MemLp (A.indicator (complexDilatation F)) ∞ (volume.restrict unitDiscExterior) :=
    memLp_top_of_bound ((hμm.indicator hAm).aestronglyMeasurable) ε (ae_of_all _ hbound)
  obtain ⟨ν, hνd⟩ : ∃ ν : LinfStar, ν = toLinf (A.indicator (complexDilatation F)) := ⟨_, rfl⟩
  have hνle : ‖ν‖ ≤ ε := by rw [hνd]; exact norm_toLinf_le_of_ae_bound hε.le (ae_of_all _ hbound)
  have hνB : ν ∈ LinfStarBall := mem_ball_zero_iff.mpr (lt_of_le_of_lt hνle hε1)
  have hνae : (ν : ℂ → ℂ) =ᵐ[volume.restrict unitDiscExterior] A.indicator (complexDilatation F) := by
    rw [hνd]
    exact bc_toLinf_ae hmem
  -- the plane solution `W`
  have hk : ‖ν‖ < 1 := lt_of_le_of_lt hνle hε1
  obtain ⟨hN, -, -, -⟩ := QCV.qcv_W_props hk
  obtain ⟨⟨KW, hKW⟩, -, -, -, hWμ⟩ := hN
  obtain ⟨W, hW⟩ : ∃ W : ℂ → ℂ, W = QCV.qcv_planeSolution ν := ⟨_, rfl⟩
  have hKW' : IsKQC W univ KW := by rw [hW]; exact hKW
  have hWμ' : ∀ᵐ z, complexDilatation W z = extB ν z := by rw [hW]; exact hWμ
  -- equal dilatations on `D = B(0, ρ)`
  let D : Set ℂ := ball (0 : ℂ) ρ
  have hFD : IsKQC F D K := t3b_isKQC_restrict hK isOpen_ball (ball_subset_ball hρR.le)
  have hWD : IsKQC W D KW := t3b_isKQC_restrict hKW' isOpen_ball (subset_univ _)
  have hEm : MeasurableSet unitDiscExterior := resolvent_exterior_isOpen.measurableSet
  have h2 : ∀ᵐ z, z ∈ unitDiscExterior → ν z = A.indicator (complexDilatation F) z :=
    (ae_restrict_iff' hEm).mp hνae
  have h3 : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 1)
  have hdil : ∀ᵐ z ∂(volume.restrict D), complexDilatation W z = complexDilatation F z := by
    rw [ae_restrict_iff' isOpen_ball.measurableSet]
    filter_upwards [hWμ', h2, h3] with z hz1 hz2 hz3 hzD
    rw [hz1]
    have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hzD
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · have hzE : z ∉ unitDiscExterior := fun h => by
        have : 1 < ‖z‖ := h
        linarith
      rw [extB, indicator_of_notMem hzE]
      have hzD1 : z ∈ unitDisc := mem_ball_zero_iff.mpr hlt
      have hev : F =ᶠ[𝓝 z] f := Filter.eventually_of_mem (isOpen_ball.mem_nhds hzD1) (fun w hw => hFf hw)
      have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (isOpen_ball.mem_nhds hzD1)
      exact (complexDilatation_eq_zero_of_diffAt (hfd.congr_of_eventuallyEq hev)).symm
    · exact absurd (mem_sphere_zero_iff_norm.mpr heq) hz3
    · have hzE : z ∈ unitDiscExterior := hgt
      rw [extB, indicator_of_mem hzE, hz2 hzE, indicator_of_mem (show z ∈ A from ⟨hgt, hzρ⟩)]
  -- the conformal map `H = F ∘ W⁻¹`
  obtain ⟨hβW, hsolW⟩ := thm10_2_genHomeoSolution_of_isKQC hWD
  obtain ⟨-, hsolF⟩ := thm10_2_genHomeoSolution_of_isKQC hFD
  have hsolF' : IsGenHomeoSolution F (complexDilatation W) D 2 := by
    obtain ⟨hghom, gx, gy, hgp, hgae⟩ := hsolF
    refine ⟨hghom, gx, gy, hgp, ?_⟩
    filter_upwards [hgae, hdil] with z h1 h2
    rw [h2]
    exact h1
  have hK1 : (1 : ℝ) ≤ KW := hKW.2.1
  have hk' : (KW - 1) / (KW + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hFφ⟩ := same_dilatation_conformal isOpen_ball hk' hβW hsolW hsolF'
  subst hW
  refine ⟨ν, hνB, hνle, φ, QCV.qcv_planeSolution ν '' D, t3b_isOpenMap hKW' (subset_univ _) isOpen_ball,
    image_mono (closedBall_subset_ball hρ1), hφ.1, hφ.2.1, fun z hz => ?_⟩
  rw [← hFf hz]
  exact hFφ z (ball_subset_ball hρ1.le hz)

/-- **(i) ⇒ (ii)** of Theorem 1.6. -/
theorem bpa_i_imp_ii {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (h1 : ∃ R > 1, ∃ F : ℂ → ℂ, IsQuasiconformal F (ball 0 R) ∧ EqOn F f unitDisc ∧
      Tendsto (complexDilatation F) (comap (fun z : ℂ => ‖z‖) (𝓝[>] 1)) (𝓝 0)) :
    Tendsto (fun z => ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol f z) (comap (fun z : ℂ => ‖z‖) (𝓝[<] 1)) (𝓝 0) := by
  -- `hinj` is not needed here (the statement stays true without it): `f = H ∘ W` near `𝔻` already
  -- gives univalence; it is part of the frozen statement for the TFAE assembly.
  have _hinj := hinj
  obtain ⟨R, hR, F, hF, hFf, hμ⟩ := h1
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- for this `ε`: the splitting `f = H ∘ W` with `‖ν‖ ≤ ε/14`
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (ε / 14) (1 / 2) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hε'1 : ε' < 1 := by rw [hε']; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε'ε : ε' ≤ ε / 14 := by rw [hε']; exact min_le_left _ _
  obtain ⟨ν, hνB, hνle, H, U, hUo, hsub, hHd, hHinj, hfac⟩ := bpa_factor hR hF hFf hf hμ hε'0 hε'1
  have hk : ‖ν‖ < 1 := mem_ball_zero_iff.mp hνB
  obtain ⟨hN, hholW, hinjW, -⟩ := QCV.qcv_W_props hk
  obtain ⟨⟨KW, hKW⟩, -⟩ := hN
  obtain ⟨W, hW⟩ : ∃ W : ℂ → ℂ, W = QCV.qcv_planeSolution ν := ⟨_, rfl⟩
  have hholW' : DifferentiableOn ℂ W unitDisc := by rw [hW]; exact hholW
  have hinjW' : InjOn W univ := by rw [hW]; exact hinjW
  have hcontW : Continuous W := by rw [hW]; exact continuousOn_univ.mp hKW.2.2.1.1
  rw [← hW] at hsub hfac
  -- `S_H` is bounded on the compact `W(𝔻̄)`
  have hH' : ∀ y ∈ U, deriv H y ≠ 0 := fun y hy => deriv_ne_zero_of_injOn hUo hHd hHinj hy
  have hSc : ContinuousOn (schwarzianHol H) (W '' closedBall 0 1) := fun y hy =>
    (analyticAt_schwarzianHol (hHd.analyticAt (hUo.mem_nhds (hsub hy))) (hH' y (hsub hy))).continuousAt.continuousWithinAt
  obtain ⟨M0, hM0⟩ := ((isCompact_closedBall (0 : ℂ) 1).image hcontW).exists_bound_of_continuousOn hSc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max M0 0 := ⟨_, rfl⟩
  have hM0' : 0 ≤ M := by rw [hM]; exact le_max_right _ _
  have hMb : ∀ y ∈ W '' closedBall 0 1, ‖schwarzianHol H y‖ ≤ M := fun y hy =>
    (hM0 y hy).trans (by rw [hM]; exact le_max_left _ _)
  -- the decay of the `H`-term
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (ε / (2 * (M + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  have hηM : M * η < ε / 2 := by
    have h1 : η ≤ ε / (2 * (M + 1)) := by rw [hη]; exact min_le_right _ _
    calc M * η ≤ M * (ε / (2 * (M + 1))) := mul_le_mul_of_nonneg_left h1 hM0'
      _ < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hdec := (Metric.tendsto_nhds.mp (hW ▸ bpa_koebe_decay hνB)) η hη0
  have hin : ∀ᶠ z in comap (fun z : ℂ => ‖z‖) (𝓝[<] 1), ‖z‖ < 1 :=
    tendsto_comap.eventually self_mem_nhdsWithin
  filter_upwards [hdec, hin] with z hz hz1
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz1
  have hzc : z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz1.le
  have hWz : W z ∈ U := hsub ⟨z, hzc, rfl⟩
  -- locality: `S_f = S_{H ∘ W}` at `z`
  have he : f =ᶠ[𝓝 z] H ∘ W := Filter.eventually_of_mem (isOpen_ball.mem_nhds hzD) (fun w hw => hfac w hw)
  have he1 := he.deriv
  have he2 := he1.deriv
  have he3 : (fun w => deriv (deriv f) w / deriv f w) =ᶠ[𝓝 z]
      fun w => deriv (deriv (H ∘ W)) w / deriv (H ∘ W) w := he2.div he1
  have hloc : schwarzianHol f z = schwarzianHol (H ∘ W) z := by
    unfold schwarzianHol
    rw [he3.deriv_eq, he2.eq_of_nhds, he1.eq_of_nhds]
  have hWd : deriv W z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hholW' (hinjW'.mono (subset_univ _)) hzD
  have hcomp := bpa_schwarzian_comp (hholW'.analyticAt (isOpen_ball.mem_nhds hzD))
    (hHd.analyticAt (hUo.mem_nhds hWz)) hWd (hH' _ hWz)
  -- the estimate
  have hS1 : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol W z‖ ≤ 7 * ε' := by
    have := bpa_weighted_S_le hνB hzD
    rw [← hW] at this
    exact this.trans ((bpa_bersPhi_le hνB).trans (by linarith))
  have ht : (1 - ‖z‖ ^ 2) * ‖deriv W z‖ < η := by
    have h := hz
    rw [dist_zero_right] at h
    exact lt_of_le_of_lt (le_abs_self _) (by rwa [Real.norm_eq_abs] at h)
  have ht0 : 0 ≤ (1 - ‖z‖ ^ 2) * ‖deriv W z‖ := mul_nonneg (by nlinarith [norm_nonneg z]) (norm_nonneg _)
  have hnorm : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ)‖ = (1 - ‖z‖ ^ 2) ^ 2 := by
    have : ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) = (((1 - ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hS2 : ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * (schwarzianHol H (W z) * deriv W z ^ 2)‖ ≤ M * η := by
    rw [norm_mul, hnorm, norm_mul, norm_pow]
    have hb := hMb _ ⟨z, hzc, rfl⟩
    calc (1 - ‖z‖ ^ 2) ^ 2 * (‖schwarzianHol H (W z)‖ * ‖deriv W z‖ ^ 2) =
          ‖schwarzianHol H (W z)‖ * ((1 - ‖z‖ ^ 2) * ‖deriv W z‖) ^ 2 := by ring
      _ ≤ M * η := by
          have h1 : ((1 - ‖z‖ ^ 2) * ‖deriv W z‖) ^ 2 ≤ η := by nlinarith
          exact mul_le_mul hb h1 (sq_nonneg _) hM0'
  rw [dist_zero_right, hloc, hcomp, mul_add]
  calc ‖((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * (schwarzianHol H (W z) * deriv W z ^ 2) +
        ((1 - ‖z‖ ^ 2) ^ 2 : ℂ) * schwarzianHol W z‖ ≤ M * η + 7 * ε' := (norm_add_le _ _).trans (add_le_add hS2 hS1)
    _ < ε := by linarith

end Ch2

end TakhtajanTeo
