import TakhtajanTeo.Ch1.S2Core
import TakhtajanTeo.Ch1.CuiPieces
import TakhtajanTeo.Ch1.CuiKernelTonelli

/-!
# Chapter 1, §2 — Cui's bound `‖S_f‖_{A₂} ≤ C(k) ‖ν‖₂` (μ = 0 case) — INTERFACE (stubs)

Cui (Sci. China A 43 (2000), Thm 2), re-derived directly in the plane coordinate `W = W_ν` (no Möbius-normalised
`g`, no area theorem; Koebe `1/4` replaces it).  For `z ∈ 𝔻`, with `κ = W'(z)(1 - |z|²)`:

* (exact formula, Stokes for the q.c. map `W` on the cut-off form of
  `Φ(w) = -κ(1-|z|²) / ((W(w) - W(z)) (w - z)²)`; `Res_{w=z} Φ = (1-|z|²)² S_W(z)/6`):
  `S_W(z) = -(6/π) W'(z) ∬_{𝔻*} ν(w) ∂W(w) / ((W(w) - W(z))² (w - z)²) dA(w)`;
* Cauchy–Schwarz with `|ν||∂W| = (|ν|/√(1-|ν|²)) √J_W`;
* `κ² ∬_{𝔻*} J_W / |W - W(z)|⁴ ≤ 16π`  (Koebe: `W(𝔻*) ∩ B(W(z), |κ|/4) = ∅`);
* Fubini with `∬_𝔻 |w - z|⁻⁴ dA(z) = π/(|w|²-1)²`.

Result: `‖S‖²_{A₂} ≤ 36/(1-k²) ‖ν‖₂²`, i.e. `C = 6/√(1-k²)`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo
namespace CUI

open QCV LiZhongQC

/-- (C1) `bersPhi ν` is the Schwarzian of the normalised plane solution on `𝔻`. -/
theorem cui_bers_eq_schwarzian {ν : LinfStar} (hν : ν ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    AInf.toFun (bersPhi ν) z = schwarzianHol (qcv_planeSolution ν) z := by
  rw [(bersPhi_spec hν).1 z hz]
  obtain ⟨a, b, c, d, hdet, hf, -⟩ := S2C.s2c_mobius hν
  have hUo : IsOpen unitDisc := isOpen_ball
  have hconf := qcv_planeSolution_conformal hν
  have hWd : DifferentiableOn ℂ (qcv_planeSolution ν) unitDisc := hconf.1
  have hWi : InjOn (qcv_planeSolution ν) unitDisc := hconf.2.1
  have hWa : AnalyticAt ℂ (qcv_planeSolution ν) z := hWd.analyticAt (hUo.mem_nhds hz)
  have hW' : deriv (qcv_planeSolution ν) z ≠ 0 := deriv_ne_zero_of_injOn hUo hWd hWi hz
  have he : fB ν =ᶠ[𝓝 z]
      fun w => (a * qcv_planeSolution ν w + b) / (c * qcv_planeSolution ν w + d) := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    rw [← S2C.s2c_fsans_eq hν]
    exact (hf w hw).2
  have h1 : schwarzianHol (fB ν) z =
      schwarzianHol (fun w => (a * qcv_planeSolution ν w + b) / (c * qcv_planeSolution ν w + d)) z := by
    have hpre := (he.deriv.deriv.div he.deriv).deriv_eq
    simp only [schwarzianHol, he.deriv_eq, he.deriv.deriv_eq]
    exact congrArg (fun t : ℂ => t - (1 / 2 : ℂ) *
      (deriv (deriv (fun w => (a * qcv_planeSolution ν w + b) / (c * qcv_planeSolution ν w + d))) z /
        deriv (fun w => (a * qcv_planeSolution ν w + b) / (c * qcv_planeSolution ν w + d)) z) ^ 2) hpre
  have hMa : AnalyticAt ℂ
      (fun w => (a * qcv_planeSolution ν w + b) / (c * qcv_planeSolution ν w + d)) z :=
    ((analyticAt_const.mul hWa).add analyticAt_const).div
      ((analyticAt_const.mul hWa).add analyticAt_const) (hf z hz).1
  have h2 := schwarzian_mobius_comp_of_ne hWa hW' hdet (hf z hz).1
  rw [schwarzian_of_analyticAt hMa, schwarzian_of_analyticAt hWa] at h2
  rw [h1, h2]

/-- Green's formula on a disc for a function with `L²` generalized partials: the `C¹` approximants
pass to the limit (circle: locally uniform convergence; area: `L²` convergence on a finite measure). -/
theorem cui_green_gen {F g h : ℂ → ℂ} (hF : HasGenPartials F g h univ 2) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(c, R), F z) = 2 * I * ∫ z in ball c R, genDzbar g h z := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hF
  have hK : IsCompact (closedBall c R) := isCompact_closedBall c R
  obtain ⟨hgK, hhK⟩ := hloc _ (subset_univ _) hK
  obtain ⟨hL1, hL2⟩ := hLp _ (subset_univ _) hK
  have hball : volume.restrict (ball c R) ≤ volume.restrict (closedBall c R) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hGreen : ∀ n, (∮ z in C(c, R), fn n z) = 2 * I * ∫ z in ball c R, dzbar (fn n) z :=
    fun n => eq11_9_green_dz hR ((hfn n).mono (subset_univ _))
  have hfc : Continuous F := by
    have := hconv.continuousOn (Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  -- circle
  have hunif : TendstoUniformlyOn fn F atTop (sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hconv _ (subset_univ _)
      (isCompact_sphere c R)
  have hlim1 : Tendsto (fun n => ∮ z in C(c, R), fn n z) atTop (𝓝 (∮ z in C(c, R), F z)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (4 * π * R) := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hε'] with n hn
    rw [dist_eq_norm, ← circleIntegral.integral_sub
      (((hfn n).continuousOn.mono (subset_univ _)).circleIntegrable hR.le)
      (hfc.continuousOn.circleIntegrable hR.le)]
    refine lt_of_le_of_lt (circleIntegral.norm_integral_le_of_norm_le_const hR.le
      (C := ε / (4 * π * R)) fun z hz => ?_) ?_
    · rw [← dist_eq_norm, dist_comm]
      exact (hn z hz).le
    · have hπR : 4 * π * R ≠ 0 := by positivity
      calc 2 * π * R * (ε / (4 * π * R)) = ε / 2 := by field_simp; ring
        _ < ε := half_lt_self hε
  -- area
  have hgenK : MemLp (genDzbar g h) 2 (volume.restrict (ball c R)) := by
    have h1 : MemLp (fun z => (1 / 2 : ℂ) * (g z + I * h z)) 2 (volume.restrict (closedBall c R)) :=
      (hgK.add (hhK.const_mul I)).const_mul _
    refine (h1.mono_measure hball).congr_norm ?_ ?_
    · exact (h1.aestronglyMeasurable.mono_measure hball).congr (Eventually.of_forall fun z => by
        simp only [genDzbar]; ring)
    · exact Eventually.of_forall fun z => by simp only [genDzbar]; congr 1; ring
  have : IsFiniteMeasure (volume.restrict (ball c R)) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top).ne
  have hint_gen : Integrable (genDzbar g h) (volume.restrict (ball c R)) :=
    hgenK.integrable (by norm_num)
  have hint_n : ∀ n, Integrable (dzbar (fn n)) (volume.restrict (ball c R)) := fun n =>
    ((continuous_dzbar (contDiffOn_univ.mp (hfn n))).continuousOn.integrableOn_compact hK).mono_set
      ball_subset_closedBall
  have hdiff : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z 1 - g z)
      (volume.restrict (ball c R)) ∧ AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z I - h z)
      (volume.restrict (ball c R)) := fun n =>
    ⟨(measurable_fderiv_apply_const ℝ (fn n) 1).aestronglyMeasurable.sub
        (hgK.aestronglyMeasurable.mono_measure hball),
      (measurable_fderiv_apply_const ℝ (fn n) I).aestronglyMeasurable.sub
        (hhK.aestronglyMeasurable.mono_measure hball)⟩
  set Kv : ℝ≥0∞ := (volume.restrict (ball c R)) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
    with hKv
  have hKv_top : Kv ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hlim2 : Tendsto (fun n => ∫ z in ball c R, dzbar (fn n) z) atTop
      (𝓝 (∫ z in ball c R, genDzbar g h z)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hbound : ∀ n, edist (∫ z in ball c R, dzbar (fn n) z) (∫ z in ball c R, genDzbar g h z) ≤
        ‖(1 / 2 : ℂ)‖ₑ * (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) 2 (volume.restrict (closedBall c R)) +
          ‖I‖ₑ * eLpNorm (fun z => fderiv ℝ (fn n) z I - h z) 2 (volume.restrict (closedBall c R))) * Kv := by
      intro n
      have hA := hdiff n
      rw [edist_eq_enorm_sub, ← integral_sub (hint_n n) hint_gen]
      have hpt : ∀ z, dzbar (fn n) z - genDzbar g h z =
          (1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) + I * (fderiv ℝ (fn n) z I - h z)) := by
        intro z
        simp only [dzbar, genDzbar]
        ring
      simp only [hpt]
      have hm : AEStronglyMeasurable (fun z => (1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) +
          I * (fderiv ℝ (fn n) z I - h z))) (volume.restrict (ball c R)) :=
        ((hA.1.add (hA.2.const_mul I)).const_mul _)
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← eLpNorm_one_eq_lintegral_enorm]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm).trans
        (mul_le_mul' ?_ le_rfl)
      calc eLpNorm (fun z => (1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) +
            I * (fderiv ℝ (fn n) z I - h z))) 2 (volume.restrict (ball c R))
          = ‖(1 / 2 : ℂ)‖ₑ * eLpNorm (fun z => (fderiv ℝ (fn n) z 1 - g z) +
            I * (fderiv ℝ (fn n) z I - h z)) 2 (volume.restrict (ball c R)) :=
            eLpNorm_const_smul (1 / 2 : ℂ) (fun z => (fderiv ℝ (fn n) z 1 - g z) +
              I * (fderiv ℝ (fn n) z I - h z)) _ _
        _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) 2
              (volume.restrict (ball c R)) + eLpNorm (fun z => I * (fderiv ℝ (fn n) z I - h z))
                2 (volume.restrict (ball c R))) := by
            gcongr
            exact eLpNorm_add_le (by norm_num)
        _ ≤ _ := by
            rw [show (fun z => I * (fderiv ℝ (fn n) z I - h z)) =
              I • (fun z => fderiv ℝ (fn n) z I - h z) from rfl, eLpNorm_const_smul]
            gcongr
      exact hm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      hbound
    have h0 := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul
      (hL1.add (ENNReal.Tendsto.const_mul hL2 (Or.inr (by simp : ‖I‖ₑ ≠ ⊤))))
      (Or.inr (by simp : ‖(1 / 2 : ℂ)‖ₑ ≠ ⊤))) (Or.inr hKv_top)
    rw [show (0 : ℝ≥0∞) = ‖(1 / 2 : ℂ)‖ₑ * (0 + ‖I‖ₑ * 0) * Kv by simp]
    exact h0
  have hlimR := hlim2.const_mul (2 * I)
  have hlimL : Tendsto (fun n => ∮ z in C(c, R), fn n z) atTop
      (𝓝 (2 * I * ∫ z in ball c R, genDzbar g h z)) := by
    simpa only [← hGreen] using hlimR
  exact tendsto_nhds_unique hlim1 hlimL

/-- `L²` convergence of the second term in the chain rule: dominated convergence. -/
theorem cui_comp_sec {ψ : ℂ → ℂ} (hdψ : Continuous (fderiv ℝ ψ)) {B : ℝ} (hB : ∀ u, ‖fderiv ℝ ψ u‖ ≤ B)
    {μ : Measure ℂ} {fn : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} (hfn : ∀ z, Tendsto (fun n => fn n z) atTop (𝓝 (f z)))
    (hfnc : ∀ n, Continuous (fn n)) (hfc : Continuous f) (hg : MemLp g 2 μ) :
    Tendsto (fun n => eLpNorm (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) 2 μ) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmeas : ∀ n, AEStronglyMeasurable (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) μ :=
    fun n => (show Continuous (Function.uncurry fun (A : ℂ →L[ℝ] ℂ) (v : ℂ) => A v) from
      continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
        ((hdψ.comp (hfnc n)).sub (hdψ.comp hfc)).aestronglyMeasurable hg.aestronglyMeasurable
  have hrew : ∀ n, eLpNorm (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) 2 μ =
      (∫⁻ z, ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hmeas n)]
    simp
  simp only [hrew]
  have hint : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
    have := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable] at this
    simp only [ENNReal.toReal_ofNat] at this
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at this
    simp at this
  have hlim : Tendsto (fun n => ∫⁻ z, ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (F := fun n z => ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (bound := fun z => ENNReal.ofReal (2 * B) ^ (2 : ℝ) * ‖g z‖ₑ ^ (2 : ℝ))
      (fun n => (hmeas n).enorm.pow_const _)
      ?_ ?_ ?_
    · simpa using this
    · intro n
      refine Eventually.of_forall fun z => ?_
      have hz : ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ≤ ENNReal.ofReal (2 * B) * ‖g z‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖
            ≤ ‖fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)‖ * ‖g z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (2 * B) * ‖g z‖ := by
              gcongr
              exact (norm_sub_le _ _).trans (by linarith [hB (fn n z), hB (f z)])
      calc ‖(fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal (2 * B) * ‖g z‖ₑ) ^ (2 : ℝ) := by gcongr
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    · have h1 : ∫⁻ z, ENNReal.ofReal (2 * B) ^ (2 : ℝ) * ‖g z‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
          hint.ne
      exact h1
    · refine Eventually.of_forall fun z => ?_
      have h1 : Tendsto (fun n => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (g z)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n => fderiv ℝ ψ (fn n z)) atTop (𝓝 (fderiv ℝ ψ (f z))) :=
          (hdψ.tendsto (f z)).comp (hfn z)
        have h3 : Tendsto (fun n => fderiv ℝ ψ (fn n z) (g z)) atTop (𝓝 (fderiv ℝ ψ (f z) (g z))) :=
          ((ContinuousLinearMap.apply ℝ ℂ (g z)).continuous.tendsto _).comp h2
        have h4 := h3.sub (tendsto_const_nhds (x := fderiv ℝ ψ (f z) (g z)))
        simpa only [sub_apply, sub_self] using h4
      have h4 := (continuous_enorm.tendsto 0).comp h1
      rw [enorm_zero] at h4
      have h5 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h4
      simpa [Function.comp_def] using h5
  have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  simpa [Function.comp_def] using this

/-- Composition of a function with `L²` generalized partials with a `C¹` outer function with bounded
derivative. -/
theorem cui_hasGen_comp {f g h ψ : ℂ → ℂ} (hf : HasGenPartials f g h univ 2)
    (hψ : ContDiff ℝ 1 ψ) {B : ℝ} (hB : ∀ u, ‖fderiv ℝ ψ u‖ ≤ B) :
    HasGenPartials (fun z => ψ (f z)) (fun z => fderiv ℝ ψ (f z) (g z))
      (fun z => fderiv ℝ ψ (f z) (h z)) univ 2 := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hf
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hdψc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hfc : Continuous f := by
    have := hconv.continuousOn (Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  have hfnc : ∀ n, Continuous (fn n) := fun n => by
    have := (hfn n).continuousOn
    rwa [continuousOn_univ] at this
  have hfnd : ∀ n, Differentiable ℝ (fn n) := fun n =>
    differentiableOn_univ.mp ((hfn n).differentiableOn one_ne_zero)
  have hlip : LipschitzWith ⟨B, hB0⟩ ψ :=
    lipschitzWith_of_nnnorm_fderiv_le hψd (fun x => by exact_mod_cast hB x)
  have hptw : ∀ z, Tendsto (fun n => fn n z) atTop (𝓝 (f z)) := fun z =>
    hconv.tendsto_at (mem_univ z)
  have happly : Continuous (Function.uncurry fun (A : ℂ →L[ℝ] ℂ) (w : ℂ) => A w) :=
    continuous_fst.clm_apply continuous_snd
  refine ⟨?_, fun n z => ψ (fn n z), fun n => hψ.comp_contDiffOn (hfn n), ?_, ?_⟩
  · intro C _ hC
    obtain ⟨hMg, hMh⟩ := hloc C (subset_univ _) hC
    have hM : ∀ v : ℂ → ℂ, MemLp v 2 (volume.restrict C) →
        MemLp (fun z => fderiv ℝ ψ (f z) (v z)) 2 (volume.restrict C) := by
      intro v hv
      refine MemLp.of_le_mul (c := B) hv ?_ ?_
      · exact happly.comp_aestronglyMeasurable₂ (hdψc.comp hfc).aestronglyMeasurable
          hv.aestronglyMeasurable
      · exact Eventually.of_forall fun z =>
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    exact ⟨hM g hMg, hM h hMh⟩
  · exact hlip.uniformContinuous.comp_tendstoLocallyUniformlyOn hconv
  · intro C _ hC
    obtain ⟨hL1, hL2⟩ := hLp C (subset_univ _) hC
    obtain ⟨hMg, hMh⟩ := hloc C (subset_univ _) hC
    have key : ∀ (v : ℂ) (gv : ℂ → ℂ), MemLp gv 2 (volume.restrict C) →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - gv z) 2 (volume.restrict C)) atTop
          (𝓝 0) →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fun z => ψ (fn n z)) z v -
          fderiv ℝ ψ (f z) (gv z)) 2 (volume.restrict C)) atTop (𝓝 0) := by
      intro v gv hgv hl
      have hsplit : ∀ n z, fderiv ℝ (fun z => ψ (fn n z)) z v - fderiv ℝ ψ (f z) (gv z) =
          fderiv ℝ ψ (fn n z) (fderiv ℝ (fn n) z v - gv z) +
            (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (gv z) := by
        intro n z
        have e : fderiv ℝ (fun z => ψ (fn n z)) z =
            (fderiv ℝ ψ (fn n z)).comp (fderiv ℝ (fn n) z) :=
          fderiv_comp z (hψd (fn n z)) (hfnd n z)
        rw [e, ContinuousLinearMap.comp_apply, map_sub, sub_apply]
        abel
      have hmeas1 : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z v - gv z)
          (volume.restrict C) := fun n =>
        (measurable_fderiv_apply_const ℝ (fn n) v).aestronglyMeasurable.sub hgv.aestronglyMeasurable
      have hb : ∀ n, eLpNorm (fun z => fderiv ℝ (fun z => ψ (fn n z)) z v - fderiv ℝ ψ (f z) (gv z)) 2
          (volume.restrict C) ≤
          ENNReal.ofReal B * eLpNorm (fun z => fderiv ℝ (fn n) z v - gv z) 2 (volume.restrict C) +
            eLpNorm (fun z => (fderiv ℝ ψ (fn n z) - fderiv ℝ ψ (f z)) (gv z)) 2
              (volume.restrict C) := by
        intro n
        simp only [hsplit]
        refine (eLpNorm_add_le (by norm_num)).trans ?_
        gcongr
        have hfirst : AEStronglyMeasurable (fun z => fderiv ℝ ψ (fn n z) (fderiv ℝ (fn n) z v - gv z))
            (volume.restrict C) :=
          happly.comp_aestronglyMeasurable₂ (hdψc.comp (hfnc n)).aestronglyMeasurable (hmeas1 n)
        have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := ⟨B, hB0⟩) hfirst
          (Eventually.of_forall fun z => by
            rw [← NNReal.coe_le_coe]
            simp only [coe_nnnorm, NNReal.coe_mul]
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))) 2
        refine this.trans (le_of_eq ?_)
        first
          | (rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hB0]; rfl)
          | (simp [ENNReal.smul_def, ENNReal.ofReal, Real.toNNReal_of_nonneg hB0])
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
      have h0 := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) hl (Or.inr ENNReal.ofReal_ne_top)).add
        (cui_comp_sec hdψc hB hptw hfnc hfc hgv)
      simpa using h0
    exact ⟨key 1 g hMg hL1, key I h hMh hL2⟩

/-- A smooth compactly supported bump (complex valued): `1` on `closedBall c r`, `0` off `ball c R`. -/
theorem cui_bump (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ b : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ w, ‖w - c‖ ≤ r → b w = 1) ∧ (∀ w, R ≤ ‖w - c‖ → b w = 0) ∧ (∀ w, ‖b w‖ ≤ 1) := by
  let f : ContDiffBump c := ⟨r, R, hr, hrR⟩
  refine ⟨fun w => ((f w : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  · intro w hw
    have : f w = 1 := f.one_of_mem_closedBall (by simpa [dist_eq_norm] using hw)
    simp [this]
  · intro w hw
    have : f w = 0 := f.zero_of_le_dist (by simpa [dist_eq_norm] using hw)
    simp [this]
  · intro w
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg f.nonneg]
    exact f.le_one

/-- A family of smooth cut-offs `χR` (`1` on `‖w‖ ≤ R`, `0` off `‖w‖ < 2R`) with `|∂̄χR| ≤ M/R`. -/
theorem cui_cutoff_family :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 0 < R → ∃ χR : ℂ → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χR ∧ HasCompactSupport χR ∧ (∀ w, ‖w‖ ≤ R → χR w = 1) ∧
        (∀ w, 2 * R ≤ ‖w‖ → χR w = 0) ∧ (∀ w, ‖χR w‖ ≤ 1) ∧ ∀ w, ‖dzbar χR w‖ ≤ M / R := by
  obtain ⟨b₁, hb₁, hb₁c, hb₁1, hb₁0, hb₁b⟩ := cui_bump (0 : ℂ) (r := 1) (R := 2) one_pos one_lt_two
  have hdb : Continuous (fderiv ℝ b₁) := hb₁.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (hb₁c.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hdb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun R hR => ?_⟩
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hnorm : ∀ w : ℂ, ‖(R : ℂ)⁻¹ * w‖ = ‖w‖ / R := fun w => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, div_eq_inv_mul]
  refine ⟨fun w => b₁ ((R : ℂ)⁻¹ * w), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hb₁.comp (contDiff_const.mul contDiff_id)
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (2 * R)) ?_
    intro w hw
    rw [mem_closedBall_zero_iff]
    by_contra hlt
    rw [not_le] at hlt
    apply hw
    apply hb₁0
    rw [sub_zero, hnorm, le_div_iff₀ hR]
    linarith
  · intro w hw
    apply hb₁1
    rw [sub_zero, hnorm, div_le_iff₀ hR]
    linarith
  · intro w hw
    apply hb₁0
    rw [sub_zero, hnorm, le_div_iff₀ hR]
    linarith
  · intro w
    exact hb₁b _
  · intro w
    have hd : HasFDerivAt (fun u : ℂ => (R : ℂ)⁻¹ * u)
        ((ContinuousLinearMap.toSpanSingleton ℂ ((R : ℂ)⁻¹)).restrictScalars ℝ) w := by
      have h0 := ((hasDerivAt_id w).const_mul ((R : ℂ)⁻¹)).hasFDerivAt.restrictScalars ℝ
      rw [mul_one] at h0
      exact h0
    have hb₁d : DifferentiableAt ℝ b₁ ((R : ℂ)⁻¹ * w) :=
      (hb₁.differentiable (by simp)) _
    have hcomp := hb₁d.hasFDerivAt.comp w hd
    have hfd : fderiv ℝ (fun w => b₁ ((R : ℂ)⁻¹ * w)) w = (fderiv ℝ b₁ ((R : ℂ)⁻¹ * w)).comp
        ((ContinuousLinearMap.toSpanSingleton ℂ ((R : ℂ)⁻¹)).restrictScalars ℝ) :=
      hcomp.fderiv
    have hv : ∀ v : ℂ, ‖fderiv ℝ (fun w => b₁ ((R : ℂ)⁻¹ * w)) w v‖ ≤ M / R * ‖v‖ := by
      intro v
      rw [hfd, ContinuousLinearMap.comp_apply]
      have hLv : ‖((ContinuousLinearMap.toSpanSingleton ℂ ((R : ℂ)⁻¹)).restrictScalars ℝ) v‖ =
          ‖v‖ / R := by
        simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
        field_simp
      calc ‖fderiv ℝ b₁ ((R : ℂ)⁻¹ * w) (((ContinuousLinearMap.toSpanSingleton ℂ ((R : ℂ)⁻¹)).restrictScalars ℝ) v)‖
          ≤ ‖fderiv ℝ b₁ ((R : ℂ)⁻¹ * w)‖ *
            ‖((ContinuousLinearMap.toSpanSingleton ℂ ((R : ℂ)⁻¹)).restrictScalars ℝ) v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * (‖v‖ / R) := by
            rw [hLv]
            gcongr
            exact hM _
        _ = M / R * ‖v‖ := by ring
    have h1 := hv 1
    have hI := hv I
    simp only [norm_one, norm_I, mul_one] at h1 hI
    unfold dzbar
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul]
    linarith

/-- Outside a ball around `z`, a qc homeomorphism stays a definite distance away from `W z`. -/
theorem cui_proper_lower {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ w, ε ≤ ‖w - z‖ → r₀ ≤ ‖W w - W z‖ := by
  have hinj : InjOn W univ := hW.2.2.1.2.1
  have hball : IsOpen (W '' ball z ε) := isOpen_image_of_isKQC (t3b_isKQC_restrict hW isOpen_ball (subset_univ _))
  have hmem : W z ∈ W '' ball z ε := ⟨z, mem_ball_self hε, rfl⟩
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.1 hball (W z) hmem
  refine ⟨r₀, hr₀, fun w hw => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w', hw', hww'⟩ := hsub (show W w ∈ Metric.ball (W z) r₀ by
    rw [mem_ball, dist_eq_norm]; exact hlt)
  have : w' = w := hinj (mem_univ _) (mem_univ _) hww'
  rw [← this] at hw
  rw [mem_ball, dist_eq_norm] at hw'
  linarith

/-- The cut-off Stokes identity: for the compactly supported smooth cut-off `a = χ χR (w - z)⁻²` and the
compactly supported `C¹` function `ψ` that equals `(u - W z)⁻¹` where it matters,
`∬ (a·(-∂̄W/(W - W z)²) + (W - W z)⁻¹ ∂̄a) = 0`. -/
theorem cui_stokes_cut {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) {z : ℂ} {ε R : ℝ} (hR : 0 < R)
    {χ χR ψ : ℂ → ℂ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χR) (hε : 0 < ε)
    (hχ0 : ∀ w, ‖w - z‖ < ε → χ w = 0) (hχRc : HasCompactSupport χR)
    (hχR0 : ∀ w, 2 * R ≤ ‖w‖ → χR w = 0)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψloc : ∀ w, ε ≤ ‖w - z‖ → ‖w‖ < 2 * R → ψ =ᶠ[𝓝 (W w)] fun u => (u - W z)⁻¹) :
    ∫ w in ball (0 : ℂ) (2 * R), (χ w * χR w * ((w - z) ^ 2)⁻¹ * (-(dzbar W w / (W w - W z) ^ 2)) +
      (W w - W z)⁻¹ * dzbar (fun w => χ w * χR w * ((w - z) ^ 2)⁻¹) w) = 0 := by
  have hinj : InjOn W univ := hW.2.2.1.2.1
  set a : ℂ → ℂ := fun w => χ w * χR w * ((w - z) ^ 2)⁻¹ with ha_def
  have ha_zero : ∀ w, ‖w - z‖ < ε → a w = 0 := fun w hw => by simp [ha_def, hχ0 w hw]
  have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = z
    · subst hx
      have hev : a =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [Metric.ball_mem_nhds x hε] with w hw
        exact ha_zero w (by simpa [dist_eq_norm] using hw)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (hχ.contDiffAt.mul hχR.contDiffAt).mul
        (((contDiffAt_id.sub contDiffAt_const).pow 2).inv (pow_ne_zero 2 (sub_ne_zero.2 hx)))
  have hac : HasCompactSupport a := by
    refine hχRc.mono' ?_
    intro w hw
    have : χR w ≠ 0 := by
      intro h0
      apply hw
      simp [ha_def, h0]
    exact subset_closure this
  obtain ⟨Ba, hBa⟩ := hac.exists_bound_of_continuous ha.continuous
  have hdx : Continuous fun w => fderiv ℝ a w 1 :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdy : Continuous fun w => fderiv ℝ a w I :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdxc : HasCompactSupport fun w => fderiv ℝ a w 1 :=
    (hac.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L 1) (by simp)
  have hdyc : HasCompactSupport fun w => fderiv ℝ a w I :=
    (hac.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L I) (by simp)
  obtain ⟨Bx, hBx⟩ := hdxc.exists_bound_of_continuous hdx
  obtain ⟨By, hBy⟩ := hdyc.exists_bound_of_continuous hdy
  have hψdc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := (hψc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hψdc
  have hGW := (thm9_5_L2_derivatives hW).1
  have hGψ := cui_hasGen_comp hGW hψ hB
  have hGF := hasGenPartials_mul_contDiff (p := 2) (by norm_num) hGψ ha Ba Bx By hBa hBx hBy
  obtain ⟨gF, hF, hGF', hgF, hhF⟩ : ∃ gF hF : ℂ → ℂ,
      HasGenPartials (fun w => ψ (W w) * a w) gF hF univ 2 ∧
      (∀ w, gF w = fderiv ℝ ψ (W w) (partialX W w) * a w + ψ (W w) * fderiv ℝ a w 1) ∧
      (∀ w, hF w = fderiv ℝ ψ (W w) (partialY W w) * a w + ψ (W w) * fderiv ℝ a w I) :=
    ⟨_, _, hGF, fun _ => rfl, fun _ => rfl⟩
  have hR2 : 0 < 2 * R := by linarith
  have hcirc : (∮ w in C((0 : ℂ), 2 * R), ψ (W w) * a w) = 0 := by
    have hz0 : EqOn (fun w => ψ (W w) * a w) (fun _ => (0 : ℂ)) (sphere (0 : ℂ) (2 * R)) := by
      intro w hw
      have hn : ‖w‖ = 2 * R := by simpa using hw
      simp [ha_def, hχR0 w (le_of_eq hn.symm)]
    rw [circleIntegral.integral_congr hR2.le hz0]
    simp [circleIntegral]
  have hG := cui_green_gen hGF' 0 hR2
  have hGint : ∫ w in ball (0 : ℂ) (2 * R), genDzbar gF hF w = 0 := by
    have h2 : (2 * I : ℂ) * ∫ w in ball (0 : ℂ) (2 * R), genDzbar gF hF w = 0 := by
      rw [← hG]; exact hcirc
    exact (mul_eq_zero.1 h2).resolve_left (by simp)
  have hdiffW : ∀ᵐ w ∂(volume.restrict (ball (0 : ℂ) (2 * R))), DifferentiableAt ℝ W w := by
    have := thm9_3_differentiable_ae hW
    rw [Measure.restrict_univ] at this
    exact ae_restrict_of_ae this
  have hae : ∀ᵐ w ∂(volume.restrict (ball (0 : ℂ) (2 * R))), genDzbar gF hF w =
      a w * (-(dzbar W w / (W w - W z) ^ 2)) + (W w - W z)⁻¹ * dzbar a w := by
    filter_upwards [hdiffW, ae_restrict_mem measurableSet_ball] with w hwd hw
    have hpx := partialX_eq_of_differentiableAt hwd
    have hpy := partialY_eq_of_differentiableAt hwd
    by_cases hwz : ‖w - z‖ < ε
    · have hev : a =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        have hopen : IsOpen {w' : ℂ | ‖w' - z‖ < ε} :=
          isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
        filter_upwards [hopen.mem_nhds hwz] with w' hw'
        exact ha_zero w' hw'
      have hfd : fderiv ℝ a w = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [genDzbar, dzbar, hgF, hhF, hfd, ha_zero w hwz]
    · rw [not_lt] at hwz
      have hwz0 : w ≠ z := by
        intro h
        rw [h, sub_self, norm_zero] at hwz
        linarith
      have hloc := hψloc w hwz (mem_ball_zero_iff.1 hw)
      have hne : W w - W z ≠ 0 := sub_ne_zero.2 fun h => hwz0 (hinj (mem_univ _) (mem_univ _) h)
      have hval : ψ (W w) = (W w - W z)⁻¹ := hloc.eq_of_nhds
      have hd : HasDerivAt (fun u : ℂ => (u - W z)⁻¹) (-1 / (W w - W z) ^ 2) (W w) :=
        ((hasDerivAt_id (W w)).sub_const (W z)).inv hne |>.congr_deriv (by simp)
      have hfd : ∀ v : ℂ, fderiv ℝ ψ (W w) v = (-1 / (W w - W z) ^ 2) * v := by
        intro v
        rw [hloc.fderiv_eq, (hd.hasFDerivAt.restrictScalars ℝ).fderiv]
        simp [mul_comm]
      simp only [genDzbar, dzbar, hgF, hhF, hpx, hpy, hfd, hval]
      ring
  have hfin := integral_congr_ae hae
  rw [hGint] at hfin
  exact hfin.symm

/-- The residue of `1/((W - W z)(w - z)²)` at `z` is `-S_W(z)/(6 W'(z))`. -/
theorem cui_residue {W : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : DifferentiableOn ℂ W (ball z (2 * r))) (hinj : InjOn W (ball z (2 * r))) :
    (∮ w in C(z, r), ((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) =
      2 * π * I * (-(schwarzianHol W z) / (6 * deriv W z)) := by
  have hr2 : 0 < 2 * r := by linarith
  have hopen : IsOpen (ball z (2 * r)) := isOpen_ball
  have hzmem : z ∈ ball z (2 * r) := mem_ball_self hr2
  have hWa : AnalyticAt ℂ W z := hW.analyticAt (hopen.mem_nhds hzmem)
  have hW' : deriv W z ≠ 0 := deriv_ne_zero_of_injOn hopen hW hinj hzmem
  set u : ℂ → ℂ := dslope W z with hu_def
  have hu : DifferentiableOn ℂ u (ball z (2 * r)) :=
    (differentiableOn_dslope (hopen.mem_nhds hzmem)).2 hW
  have hu0 : ∀ w ∈ ball z (2 * r), u w ≠ 0 := by
    intro w hw
    by_cases hwz : w = z
    · subst hwz
      simpa [hu_def, dslope_same] using hW'
    · rw [hu_def, dslope_of_ne _ hwz, slope_def_field]
      refine div_ne_zero (sub_ne_zero.2 fun h => hwz (hinj hw hzmem h)) (sub_ne_zero.2 hwz)
  set h : ℂ → ℂ := fun w => (u w)⁻¹ with hh_def
  have hh : DifferentiableOn ℂ h (ball z (2 * r)) := hu.inv hu0
  set h₁ : ℂ → ℂ := dslope h z with hh1_def
  have hh1 : DifferentiableOn ℂ h₁ (ball z (2 * r)) :=
    (differentiableOn_dslope (hopen.mem_nhds hzmem)).2 hh
  set h₂ : ℂ → ℂ := dslope h₁ z with hh2_def
  have hh2 : DifferentiableOn ℂ h₂ (ball z (2 * r)) :=
    (differentiableOn_dslope (hopen.mem_nhds hzmem)).2 hh1
  set h₃ : ℂ → ℂ := dslope h₂ z with hh3_def
  have hh3 : DifferentiableOn ℂ h₃ (ball z (2 * r)) :=
    (differentiableOn_dslope (hopen.mem_nhds hzmem)).2 hh2
  have htay : ∀ f : ℂ → ℂ, ∀ w, w ≠ z → f w = f z + (w - z) * dslope f z w := by
    intro f w hw
    have := sub_smul_dslope f z w
    rw [smul_eq_mul] at this
    linear_combination -this
  have hexp : ∀ w ∈ sphere z r, ((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹ =
      h z * ((w - z) ^ (-3 : ℤ)) + h₁ z * ((w - z) ^ (-2 : ℤ)) + h₂ z * ((w - z) ^ (-1 : ℤ)) + h₃ w := by
    intro w hw
    have hwz : w - z ≠ 0 := by
      intro h0
      rw [mem_sphere_iff_norm, h0, norm_zero] at hw
      linarith
    have hwz' : w ≠ z := sub_ne_zero.1 hwz
    have hwb : w ∈ ball z (2 * r) := by
      rw [mem_ball_iff_norm]
      rw [mem_sphere_iff_norm] at hw
      linarith
    have hu_w : u w ≠ 0 := hu0 w hwb
    have hW_w : W w - W z = u w * (w - z) := by
      rw [hu_def, dslope_of_ne _ hwz', slope_def_field]
      field_simp
    have e1 : h w = h z + (w - z) * h₁ w := htay h w hwz'
    have e2 : h₁ w = h₁ z + (w - z) * h₂ w := htay h₁ w hwz'
    have e3 : h₂ w = h₂ z + (w - z) * h₃ w := htay h₂ w hwz'
    have hhw : h w = (u w)⁻¹ := rfl
    have key : ((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹ = h w * ((w - z) ^ 3)⁻¹ := by
      rw [hW_w, hhw]
      field_simp
    rw [key, e1, e2, e3]
    simp only [zpow_neg, zpow_natCast, zpow_one]
    field_simp
    ring
  -- the circle integral
  have hsph : sphere z r ⊆ ball z (2 * r) := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    rw [mem_ball_iff_norm, hw]
    linarith
  have hcont : ∀ n : ℤ, ContinuousOn (fun w : ℂ => (w - z) ^ n) (sphere z r) := fun n =>
    (continuousOn_id.sub continuousOn_const).zpow₀ n (fun w hw => Or.inl (by
      intro h0
      have : w = z := sub_eq_zero.1 h0
      rw [mem_sphere_iff_norm, this, sub_self, norm_zero] at hw
      linarith))
  have hci : ∀ (c : ℂ) (n : ℤ), CircleIntegrable (fun w : ℂ => c * (w - z) ^ n) z r := fun c n =>
    (continuousOn_const.mul (hcont n)).circleIntegrable hr.le
  have hci3 : CircleIntegrable h₃ z r := (hh3.continuousOn.mono hsph).circleIntegrable hr.le
  have hA : CircleIntegrable (fun w : ℂ => h z * (w - z) ^ (-3 : ℤ)) z r := hci _ _
  have hB : CircleIntegrable (fun w : ℂ => h₁ z * (w - z) ^ (-2 : ℤ)) z r := hci _ _
  have hC : CircleIntegrable (fun w : ℂ => h₂ z * (w - z) ^ (-1 : ℤ)) z r := hci _ _
  rw [circleIntegral.integral_congr hr.le hexp]
  have st1 : (∮ w in C(z, r), (h z * (w - z) ^ (-3 : ℤ) + h₁ z * (w - z) ^ (-2 : ℤ) +
      h₂ z * (w - z) ^ (-1 : ℤ) + h₃ w)) =
      (∮ w in C(z, r), (h z * (w - z) ^ (-3 : ℤ) + h₁ z * (w - z) ^ (-2 : ℤ) +
        h₂ z * (w - z) ^ (-1 : ℤ))) + ∮ w in C(z, r), h₃ w :=
    circleIntegral.integral_add ((hA.add hB).add hC) hci3
  have st2 : (∮ w in C(z, r), (h z * (w - z) ^ (-3 : ℤ) + h₁ z * (w - z) ^ (-2 : ℤ) +
      h₂ z * (w - z) ^ (-1 : ℤ))) =
      (∮ w in C(z, r), (h z * (w - z) ^ (-3 : ℤ) + h₁ z * (w - z) ^ (-2 : ℤ))) +
        ∮ w in C(z, r), h₂ z * (w - z) ^ (-1 : ℤ) :=
    circleIntegral.integral_add (hA.add hB) hC
  have st3 : (∮ w in C(z, r), (h z * (w - z) ^ (-3 : ℤ) + h₁ z * (w - z) ^ (-2 : ℤ))) =
      (∮ w in C(z, r), h z * (w - z) ^ (-3 : ℤ)) + ∮ w in C(z, r), h₁ z * (w - z) ^ (-2 : ℤ) :=
    circleIntegral.integral_add hA hB
  rw [st1, st2, st3]
  have i3 : (∮ w in C(z, r), h z * (w - z) ^ (-3 : ℤ)) = 0 := by
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne (by norm_num), mul_zero]
  have i2 : (∮ w in C(z, r), h₁ z * (w - z) ^ (-2 : ℤ)) = 0 := by
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne (by norm_num), mul_zero]
  have i1 : (∮ w in C(z, r), h₂ z * (w - z) ^ (-1 : ℤ)) = h₂ z * (2 * π * I) := by
    rw [circleIntegral.integral_const_mul]
    simp only [zpow_neg, zpow_one]
    rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]
  have i0 : (∮ w in C(z, r), h₃ w) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
      (hh3.continuousOn.mono (closedBall_subset_ball (by linarith))) (fun w hw => by
        exact hh3.differentiableAt (hopen.mem_nhds (ball_subset_ball (by linarith) hw.1)))
  rw [i3, i2, i1, i0]
  -- the value of h₂ z
  have hua : AnalyticAt ℂ u z := hu.analyticAt (hopen.mem_nhds hzmem)
  have hha : AnalyticAt ℂ h z := hh.analyticAt (hopen.mem_nhds hzmem)
  have hu1 : deriv u z = deriv (deriv W) z / 2 := kn_deriv_dslope_same hWa
  have hu2 : deriv (deriv u) z = deriv (deriv (deriv W)) z / 3 := kn_deriv2_dslope_same hWa
  have huz : u z = deriv W z := by simp [hu_def, dslope_same]
  have hh2z : h₂ z = deriv (deriv h) z / 2 := by
    rw [hh2_def, dslope_same, hh1_def]
    exact kn_deriv_dslope_same hha
  have hderh : deriv h =ᶠ[𝓝 z] fun w => -deriv u w / u w ^ 2 := by
    filter_upwards [hopen.mem_nhds hzmem] with w hw
    exact ((hu.differentiableAt (hopen.mem_nhds hw)).hasDerivAt.inv (hu0 w hw)).deriv
  have hdu : DifferentiableAt ℂ (deriv u) z := hua.deriv.differentiableAt
  have hD2 : HasDerivAt (fun w => -deriv u w / u w ^ 2)
      ((-deriv (deriv u) z * u z ^ 2 - (-deriv u z) * (2 * u z * deriv u z)) / (u z ^ 2) ^ 2) z := by
    have hn : HasDerivAt (fun w => -deriv u w) (-deriv (deriv u) z) z := hdu.hasDerivAt.neg
    have hd : HasDerivAt (fun w => u w ^ 2) (2 * u z * deriv u z) z :=
      ((hua.differentiableAt.hasDerivAt.mul hua.differentiableAt.hasDerivAt).congr_of_eventuallyEq
        (Eventually.of_forall fun w => pow_two (u w))).congr_deriv (by ring)
    exact hn.div hd (pow_ne_zero 2 (hu0 z hzmem))
  have hdh2 : deriv (deriv h) z = (-deriv (deriv u) z * u z ^ 2 - (-deriv u z) * (2 * u z * deriv u z)) /
      (u z ^ 2) ^ 2 := by
    rw [hderh.deriv_eq]
    exact hD2.deriv
  -- the Schwarzian
  have hW2 : DifferentiableAt ℂ (deriv W) z := hWa.deriv.differentiableAt
  have hW3 : DifferentiableAt ℂ (deriv (deriv W)) z := hWa.deriv.deriv.differentiableAt
  have hW4 : DifferentiableAt ℂ (deriv (deriv (deriv W))) z := hWa.deriv.deriv.deriv.differentiableAt
  have hsch : schwarzianHol W z = deriv (deriv (deriv W)) z / deriv W z -
      (3 / 2) * (deriv (deriv W) z / deriv W z) ^ 2 := by
    have hq : HasDerivAt (fun w => deriv (deriv W) w / deriv W w)
        ((deriv (deriv (deriv W)) z * deriv W z - deriv (deriv W) z * deriv (deriv W) z) /
          deriv W z ^ 2) z :=
      (hW3.hasDerivAt.div hW2.hasDerivAt hW')
    unfold schwarzianHol
    rw [hq.deriv]
    field_simp
    ring
  rw [hh2z, hdh2, hu1, hu2, huz, hsch]
  field_simp
  ring

/-- The local term of the cut-off Stokes identity: Green on `ball z (2ε)` and the residue. -/
theorem cui_B_eval {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hWΩ : DifferentiableOn ℂ W Ω) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : ball z (4 * ε) ⊆ Ω)
    {χ : ℂ → ℂ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχ0 : ∀ w, ‖w - z‖ < ε → χ w = 0)
    (hχ1 : ∀ w, 3 * ε / 2 ≤ ‖w - z‖ → χ w = 1) :
    ∫ w in ball z (2 * ε), dzbar χ w * (((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) =
      π * (-(schwarzianHol W z) / (6 * deriv W z)) := by
  have hinj : InjOn W univ := hW.2.2.1.2.1
  have hWd : DifferentiableOn ℂ W (ball z (2 * (2 * ε))) := by
    refine hWΩ.mono (fun w hw => hball ?_)
    rwa [show 4 * ε = 2 * (2 * ε) by ring]
  have hWi : InjOn W (ball z (2 * (2 * ε))) := hinj.mono (subset_univ _)
  set g₀ : ℂ → ℂ := fun w => χ w * (((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) with hg₀_def
  have hopenz : IsOpen {w : ℂ | ‖w - z‖ < ε} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hg0 : ∀ w, ‖w - z‖ < ε → g₀ =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
    intro w hw
    filter_upwards [hopenz.mem_nhds hw] with w' hw'
    simp [hg₀_def, hχ0 w' hw']
  have hχ0' : ∀ w, ‖w - z‖ < ε → χ =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
    intro w hw
    filter_upwards [hopenz.mem_nhds hw] with w' hw'
    exact hχ0 w' hw'
  have hWa : ∀ w ∈ ball z (4 * ε), AnalyticAt ℂ W w := fun w hw =>
    hWΩ.analyticAt (hΩ.mem_nhds (hball hw))
  have hne : ∀ w, ε ≤ ‖w - z‖ → W w - W z ≠ 0 := by
    intro w hw
    have hwz : w ≠ z := by
      intro h; rw [h, sub_self, norm_zero] at hw; linarith
    exact sub_ne_zero.2 fun h => hwz (hinj (mem_univ _) (mem_univ _) h)
  have hΦd : ∀ w ∈ ball z (4 * ε), ε ≤ ‖w - z‖ →
      AnalyticAt ℂ (fun w => ((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) w := by
    intro w hw hwε
    have hwz : w - z ≠ 0 := by
      intro h; rw [h, norm_zero] at hwε; linarith
    exact ((((analyticAt_id).sub analyticAt_const).pow 2).inv (pow_ne_zero 2 hwz)).mul
      (((hWa w hw).sub analyticAt_const).inv (hne w hwε))
  have hg₀c : ContDiffOn ℝ 1 g₀ (closedBall z (2 * ε)) := by
    intro w hw
    have hwb : w ∈ ball z (4 * ε) := by
      rw [mem_closedBall_iff_norm] at hw
      rw [mem_ball_iff_norm]; linarith
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hwε : ‖w - z‖ < ε
    · exact contDiffAt_const.congr_of_eventuallyEq (hg0 w hwε)
    · rw [not_lt] at hwε
      exact (hχ.contDiffAt.of_le (by simp)).mul
        ((hΦd w hwb hwε).contDiffAt.restrict_scalars ℝ)
  have hgreen := eq11_9_green_dz (c := z) (R := 2 * ε) (by linarith) hg₀c
  have hdz : ∀ w ∈ ball z (2 * ε), dzbar g₀ w =
      dzbar χ w * (((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) := by
    intro w hw
    have hwb : w ∈ ball z (4 * ε) := by
      rw [mem_ball_iff_norm] at hw ⊢; linarith
    by_cases hwε : ‖w - z‖ < ε
    · have h1 : dzbar g₀ w = 0 := by
        unfold dzbar; rw [(hg0 w hwε).fderiv_eq]; simp
      have h2 : dzbar χ w = 0 := by
        unfold dzbar; rw [(hχ0' w hwε).fderiv_eq]; simp
      rw [h1, h2, zero_mul]
    · rw [not_lt] at hwε
      have hχd : DifferentiableAt ℝ χ w := (hχ.differentiable (by simp)) w
      have hΦ := (hΦd w hwb hwε).differentiableAt
      have := dzbar_mul hχd (hΦ.restrictScalars ℝ)
      rw [hg₀_def]
      rw [this, (cauchyRiemann_iff.1 hΦ).2]
      ring
  have hcirc : (∮ w in C(z, 2 * ε), g₀ w) = 2 * π * I * (-(schwarzianHol W z) / (6 * deriv W z)) := by
    rw [← cui_residue (by linarith : (0 : ℝ) < 2 * ε) hWd hWi]
    refine circleIntegral.integral_congr (by linarith) (fun w hw => ?_)
    have hn : ‖w - z‖ = 2 * ε := by simpa [mem_sphere_iff_norm] using hw
    simp [hg₀_def, hχ1 w (by linarith)]
  rw [hcirc] at hgreen
  have hint : ∫ w in ball z (2 * ε), dzbar g₀ w =
      ∫ w in ball z (2 * ε), dzbar χ w * (((w - z) ^ 2)⁻¹ * (W w - W z)⁻¹) :=
    setIntegral_congr_fun measurableSet_ball hdz
  rw [← hint]
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have : (2 * I : ℂ) * (π * (-(schwarzianHol W z) / (6 * deriv W z))) =
      (2 * I) * ∫ w in ball z (2 * ε), dzbar g₀ w := by
    rw [← hgreen]; ring
  exact (mul_left_cancel₀ h2I this.symm)

/-- A compactly supported smooth inverse agrees with the true inverse on
the image of the annular region used in Stokes. -/
theorem cui_inverse_cutoff {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) (z : ℂ)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      ∀ w, ε ≤ ‖w-z‖ → ‖w‖ < 2*R → ψ =ᶠ[𝓝 (W w)] (fun u => (u-W z)⁻¹) := by
  obtain ⟨r,hr,hrW⟩ := cui_proper_lower hW z hε
  have hWc : Continuous W := continuousOn_univ.mp hW.2.2.1.1
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) (2*R)).exists_bound_of_continuousOn
    (hWc.sub (continuous_const : Continuous (fun _ : ℂ => W z))).continuousOn
  let L : ℝ := max C 0 + r + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨bi,hbi,hbic,hbi1,hbi0,hbib⟩ := cui_bump (W z) (r := r/4) (R := r/2)
    (by positivity) (by linarith)
  obtain ⟨bo,hbo,hboc,hbo1,hbo0,hbob⟩ := cui_bump (W z) (r := L) (R := 2*L)
    hL (by linarith)
  let ψ : ℂ → ℂ := fun u => (1-bi u)*bo u*(u-W z)⁻¹
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu : u = W z
    · subst u
      have he : ψ =ᶠ[𝓝 (W z)] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds (W z) (show 0 < r/4 by positivity)] with v hv
        have hvi : bi v = 1 := hbi1 v (mem_ball_iff_norm.mp hv).le
        simp [ψ,hvi]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact ((contDiffAt_const.sub hbi.contDiffAt).mul hbo.contDiffAt).mul
        ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hu))
  refine ⟨ψ,hψ.of_le (by simp),?_,?_⟩
  · apply hboc.mono'
    intro u hu
    apply subset_closure
    intro hzero
    exact hu (by simp [ψ,hzero])
  · intro w hw hwR
    have hlow : r/2 < ‖W w-W z‖ := by linarith [hrW w hw]
    have hupp : ‖W w-W z‖ < L := by
      have hh := hC w (mem_closedBall_zero_iff.mpr hwR.le)
      change ‖W w-W z‖ ≤ C at hh
      dsimp [L]
      linarith [le_max_left C 0]
    have hcont : ContinuousAt (fun u : ℂ => ‖u-W z‖) (W w) := by fun_prop
    filter_upwards [hcont.eventually (lt_mem_nhds hlow),hcont.eventually (gt_mem_nhds hupp)] with u hu hl
    simp [ψ,hbi0 u hu.le,hbo1 u hl.le]

/-- Derivatives vanish on either open plateau of a smooth cutoff. -/
theorem cui_dzbar_plateau {χ : ℂ → ℂ} {c w : ℂ} {r : ℝ}
    (hχ : ∀ v, ‖v-c‖ < r → χ v = 1) (hw : ‖w-c‖ < r) : dzbar χ w = 0 := by
  have he : χ =ᶠ[𝓝 w] fun _ => (1 : ℂ) := by
    filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds hw] with v hv
    exact hχ v hv
  unfold dzbar
  rw [he.fderiv_eq]
  simp

/-- The outer cutoff term has the quantitative O(1/R) bound used when
passing the compactly supported Stokes identity to the whole plane. -/
theorem cui_outer_error_bound {W χ χR : ℂ → ℂ} {z : ℂ} {ε R r M : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hr : 0 < r) (hM : 0 ≤ M)
    (hRz : 2*‖z‖ ≤ R) (hRε : 4*ε ≤ R)
    (hlow : ∀ w, ε ≤ ‖w-z‖ → r ≤ ‖W w-W z‖)
    (hχ1 : ∀ w, 3*ε/2 ≤ ‖w-z‖ → χ w = 1)
    (hχR1 : ∀ w, ‖w‖ ≤ R → χR w = 1)
    (hdR : ∀ w, ‖dzbar χR w‖ ≤ M/R) :
    ‖∫ w in ball (0 : ℂ) (2*R), χ w*((w-z)^2)⁻¹*(W w-W z)⁻¹*dzbar χR w‖ ≤
      16*π*M/(r*R) := by
  have hb : ∀ w, ‖χ w*((w-z)^2)⁻¹*(W w-W z)⁻¹*dzbar χR w‖ ≤ 4*M/(r*R^3) := by
    intro w
    by_cases hw : ‖w‖ < R
    · have hzR : dzbar χR w = 0 := cui_dzbar_plateau (c := 0)
        (fun v hv => hχR1 v (by simpa using hv.le)) (by simpa using hw)
      rw [hzR,mul_zero,norm_zero]
      positivity
    · have hwR : R ≤ ‖w‖ := not_lt.mp hw
      have hn : R/2 ≤ ‖w-z‖ := by linarith [norm_sub_norm_le w z]
      have hnε : ε ≤ ‖w-z‖ := by linarith
      rw [hχ1 w (by linarith),one_mul]
      simp only [norm_mul,norm_inv,norm_pow]
      have hden : (R/2)^2*r ≤ ‖w-z‖^2*‖W w-W z‖ :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hn 2) (hlow w hnε) hr.le (sq_nonneg _)
      calc (‖w-z‖^2)⁻¹ * ‖W w-W z‖⁻¹ * ‖dzbar χR w‖ =
          ‖dzbar χR w‖/(‖w-z‖^2*‖W w-W z‖) := by simp only [div_eq_mul_inv,mul_inv]; ring
        _ ≤ (M/R)/((R/2)^2*r) := div_le_div₀ (by positivity) (hdR w) (by positivity) hden
        _ = 4*M/(r*R^3) := by field_simp; ring
  have hi := norm_setIntegral_le_of_norm_le_const_ae
    (measure_ball_lt_top : volume (ball (0 : ℂ) (2*R)) < ∞)
    (Eventually.of_forall hb)
  apply hi.trans_eq
  simp only [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,NNReal.coe_real_pi,ENNReal.toReal_ofReal (show 0 ≤ 2*R by positivity)]
  field_simp
  <;> ring

/-- Removing a neighborhood of the pole gives a continuous kernel. -/
theorem cui_cut_kernel_continuous {W a : ℂ → ℂ} {K ε : ℝ} {z : ℂ}
    (hW : IsKQC W univ K) (ha : Continuous a) (hε : 0 < ε)
    (ha0 : ∀ w, ‖w-z‖ < ε → a w = 0) :
    Continuous (fun w => a w * ((w-z)^2)⁻¹ * (W w-W z)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = z
  · subst w
    have he : (fun w => a w * ((w-z)^2)⁻¹ * (W w-W z)⁻¹) =ᶠ[𝓝 z]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with v hv
      simp [ha0 v (mem_ball_iff_norm.mp hv)]
    exact continuousAt_const.congr_of_eventuallyEq he
  · have hi : Function.Injective W := fun x y h => hW.2.2.1.2.1 (mem_univ x) (mem_univ y) h
    exact (ha.continuousAt.mul (((continuousAt_id.sub continuousAt_const).pow 2).inv₀
      (pow_ne_zero 2 (sub_ne_zero.mpr hw)))).mul
        (((continuousOn_univ.mp hW.2.2.1.1).continuousAt.sub continuousAt_const).inv₀
          (sub_ne_zero.mpr (fun h => hw (hi h))))

/-- The Wirtinger derivative of the cut-off meromorphic factor. -/
theorem cui_dzbar_cut {χ χR : ℂ → ℂ} {z : ℂ} {ε : ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χR) (hε : 0 < ε)
    (hχ0 : ∀ w, ‖w-z‖ < ε → χ w = 0) (w : ℂ) :
    dzbar (fun w => χ w * χR w * ((w-z)^2)⁻¹) w =
      dzbar χ w * χR w * ((w-z)^2)⁻¹ + χ w * dzbar χR w * ((w-z)^2)⁻¹ := by
  by_cases hw : w = z
  · subst w
    have he : (fun w => χ w * χR w * ((w-z)^2)⁻¹) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with v hv
      simp [hχ0 v (mem_ball_iff_norm.mp hv)]
    unfold dzbar
    rw [he.fderiv_eq]
    simp
  · have hχd := (hχ.differentiable (by simp)) w
    have hχRd := (hχR.differentiable (by simp)) w
    have hp : DifferentiableAt ℂ (fun w : ℂ => ((w-z)^2)⁻¹) w :=
      ((differentiableAt_id.sub_const z).pow 2).inv (pow_ne_zero 2 (sub_ne_zero.mpr hw))
    have hmul : DifferentiableAt ℝ (fun v => χ v * χR v) w := hχd.mul hχRd
    rw [dzbar_mul hmul (hp.restrictScalars ℝ),
      dzbar_mul hχd hχRd, (cauchyRiemann_iff.mp hp).2]
    ring

/-- (C2g) The exact (nonlinear) Bers-type formula for a qc homeomorphism `W` of the plane that is
conformal on an open set `Ω`: for `z ∈ Ω`,
`S_W(z) = -(6/π) W'(z) ∬_{Ωᶜ} ∂̄W(w) / ((W(w) - W(z))² (w - z)²) dA(w)`,
assuming the integral converges absolutely. -/
theorem cui_exact_formula_gen {W : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hWΩ : DifferentiableOn ℂ W Ω) {z : ℂ} (hz : z ∈ Ω)
    (hint : IntegrableOn (fun w => dzbar W w / ((W w - W z) ^ 2 * (w - z) ^ 2)) Ωᶜ) :
    schwarzianHol W z = -(6 / π) * deriv W z *
      ∫ w in Ωᶜ, dzbar W w / ((W w - W z) ^ 2 * (w - z) ^ 2) := by
  obtain ⟨δ,hδ,hδΩ⟩ := Metric.isOpen_iff.mp hΩ z hz
  let ε := δ/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hball : ball z (4*ε) ⊆ Ω := by convert hδΩ using 1; dsimp [ε]; congr 1; ring
  obtain ⟨b,hb,hbc,hb1,hb0,hbn⟩ := cui_bump z (r := ε) (R := 3*ε/2) hε (by linarith)
  let χ : ℂ → ℂ := fun w => 1-b w
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contDiff_const.sub hb
  have hχ0 : ∀ w, ‖w-z‖ < ε → χ w = 0 := fun w hw => by simp [χ,hb1 w hw.le]
  have hχ1 : ∀ w, 3*ε/2 ≤ ‖w-z‖ → χ w = 1 := fun w hw => by simp [χ,hb0 w hw]
  have hd0 : ∀ w, ‖w-z‖ < ε → dzbar χ w = 0 := by
    intro w hw
    have he : χ =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
        continuous_const).mem_nhds hw] with v hv
      exact hχ0 v hv
    unfold dzbar; rw [he.fderiv_eq]; simp
  have hd1 : ∀ w, 2*ε ≤ ‖w-z‖ → dzbar χ w = 0 := by
    intro w hw
    have he : χ =ᶠ[𝓝 w] fun _ => (1 : ℂ) := by
      have hh : 3*ε/2 < ‖w-z‖ := by linarith
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hh] with v hv
      exact hχ1 v hv.le
    unfold dzbar; rw [he.fderiv_eq]; simp
  let G : ℂ → ℂ := fun w => dzbar W w / ((W w-W z)^2*(w-z)^2)
  have hG0 : ∀ w ∈ Ω, G w = 0 := by
    intro w hw
    have hh := (cauchyRiemann_iff.mp (hWΩ.differentiableAt (hΩ.mem_nhds hw))).2
    simp [G,hh]
  have hGind : Ωᶜ.indicator G = G := by
    funext w
    by_cases hw : w ∈ Ω <;> simp [hw,hG0]
  have hGi : Integrable G := by
    rw [← hGind]
    exact (integrable_indicator_iff hΩ.measurableSet.compl).mpr hint
  have hχG : ∀ w, χ w * G w = G w := by
    intro w
    by_cases hw : w ∈ Ω
    · simp [hG0 w hw]
    · have hh : 4*ε ≤ ‖w-z‖ := le_of_not_gt (fun hh => hw (hball (mem_ball_iff_norm.mpr hh)))
      rw [hχ1 w (by linarith),one_mul]
  let B : ℂ → ℂ := fun w => dzbar χ w * ((w-z)^2)⁻¹ * (W w-W z)⁻¹
  have hBc : Continuous B := cui_cut_kernel_continuous hW
    (continuous_dzbar (hχ.of_le (by simp))) hε hd0
  have hB0 : ∀ w, w ∉ ball z (2*ε) → B w = 0 := by
    intro w hw
    simp [B,hd1 w (le_of_not_gt (fun hh => hw (mem_ball_iff_norm.mpr hh)))]
  have hBeval : ∫ w in ball z (2*ε), B w = π * (-schwarzianHol W z/(6*deriv W z)) := by
    simpa only [B,mul_assoc] using cui_B_eval hW hΩ hWΩ hε hball hχ hχ0 hχ1
  obtain ⟨r,hr,hrW⟩ := cui_proper_lower hW z hε
  obtain ⟨M,hM,hcut⟩ := cui_cutoff_family
  have hstep : ∀ R : ℝ, 2*‖z‖+4*ε+1 ≤ R →
      ∃ χR : ℂ → ℂ, (∀ w, ‖χR w‖ ≤ 1) ∧ Continuous χR ∧
        (∀ w, ‖w‖ ≤ R → χR w = 1) ∧
        ‖(∫ w, χR w*G w) - π * (-schwarzianHol W z/(6*deriv W z))‖ ≤
          16*π*M/(r*R) := by
    intro R hlarge
    have hR : 0 < R := by linarith [norm_nonneg z]
    obtain ⟨χR,hχR,hχRc,hχR1,hχR0,hχRn,hdR⟩ := hcut R hR
    obtain ⟨ψ,hψ,hψc,hψloc⟩ := cui_inverse_cutoff hW z hε hR
    have hs := cui_stokes_cut hW hR hχ hχR hε hχ0 hχRc hχR0 hψ hψc hψloc
    let C : ℂ → ℂ := fun w => χ w*((w-z)^2)⁻¹*(W w-W z)⁻¹*dzbar χR w
    have hCc : Continuous C := (cui_cut_kernel_continuous hW hχ.continuous hε hχ0).mul
      (continuous_dzbar (hχR.of_le (by simp)))
    have hBi : IntegrableOn (fun w => χR w*B w) (ball (0 : ℂ) (2*R)) :=
      ((hχR.continuous.mul hBc).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) (2*R))).mono_set ball_subset_closedBall
    have hCi : IntegrableOn C (ball (0 : ℂ) (2*R)) :=
      (hCc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) (2*R))).mono_set
        ball_subset_closedBall
    have hAi : Integrable (fun w => χR w*G w) :=
      hGi.bdd_mul hχR.continuous.aestronglyMeasurable (Eventually.of_forall hχRn)
    have halg : ∀ w,
        χ w*χR w*((w-z)^2)⁻¹*(-(dzbar W w/(W w-W z)^2)) +
          (W w-W z)⁻¹*dzbar (fun w => χ w*χR w*((w-z)^2)⁻¹) w =
        -(χR w*G w)+χR w*B w+C w := by
      intro w
      rw [cui_dzbar_cut hχ hχR hε hχ0]
      have hh := hχG w
      dsimp [G] at hh
      dsimp [G,B,C]
      simp only [div_eq_mul_inv,mul_inv] at hh ⊢
      linear_combination -χR w * hh
    simp_rw [halg] at hs
    have hAn : IntegrableOn (fun w => -(χR w*G w)) (ball (0 : ℂ) (2*R)) := hAi.integrableOn.neg
    have hsum : IntegrableOn (fun w => -(χR w*G w)+χR w*B w) (ball (0 : ℂ) (2*R)) := hAn.add hBi
    rw [integral_add hsum hCi,integral_add hAn hBi,integral_neg] at hs
    have hAeq : ∫ w in ball (0 : ℂ) (2*R), χR w*G w = ∫ w, χR w*G w := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      have hh : 2*R ≤ ‖w‖ := le_of_not_gt (fun hh => hw (mem_ball_zero_iff.mpr hh))
      simp [hχR0 w hh]
    have hsub : ball z (2*ε) ⊆ ball (0 : ℂ) (2*R) := by
      intro w hw
      rw [mem_ball_iff_norm] at hw
      rw [mem_ball_zero_iff]
      have hh := norm_le_insert' w z
      linarith [norm_nonneg z]
    have hBeq : ∫ w in ball (0 : ℂ) (2*R), χR w*B w = ∫ w in ball z (2*ε), B w := by
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
        (fun w hw => by simp [hB0 w hw.2])]
      apply setIntegral_congr_fun measurableSet_ball
      intro w hw
      have hn : ‖w‖ ≤ R := by
        have hh := mem_ball_iff_norm.mp hw
        linarith [norm_le_insert' w z,norm_nonneg z]
      simp only [hχR1 w hn,one_mul]
    rw [hAeq,hBeq,hBeval] at hs
    refine ⟨χR,hχRn,hχR.continuous,hχR1,?_⟩
    have heq : (∫ w, χR w*G w) - π * (-schwarzianHol W z/(6*deriv W z)) =
        ∫ w in ball (0 : ℂ) (2*R), C w := by linear_combination -hs
    rw [heq]
    exact cui_outer_error_bound hε hR hr hM (by linarith) (by linarith [norm_nonneg z])
      hrW hχ1 hχR1 hdR
  let R : ℕ → ℝ := fun n => 2*‖z‖+4*ε+1+n
  have hRlarge : ∀ n, 2*‖z‖+4*ε+1 ≤ R n := fun n => by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
  choose χn hχnb hχnc hχn1 hn using fun n => hstep (R n) (hRlarge n)
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => by dsimp [R]; linarith [norm_nonneg z])
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hmain : Tendsto (fun n => ∫ w, χn n w*G w) atTop (𝓝 (∫ w, G w)) := by
    apply tendsto_integral_of_dominated_convergence (fun w => ‖G w‖)
    · intro n
      exact (hχnc n).aestronglyMeasurable.mul hGi.aestronglyMeasurable
    · exact hGi.norm
    · intro n
      filter_upwards [] with w
      simpa only [norm_mul,one_mul] using
        mul_le_mul_of_nonneg_right (hχnb n w) (norm_nonneg (G w))
    · exact Eventually.of_forall (fun w => tendsto_const_nhds.congr'
        ((hRt.eventually_ge_atTop ‖w‖).mono (fun n hn => by simp only [hχn1 n w hn,one_mul])))
  have herr : Tendsto (fun n => 16*π*M/(r*R n)) atTop (𝓝 0) := by
    simpa only [div_div] using hRt.const_div_atTop (16*π*M/r)
  have hres : Tendsto (fun n => ∫ w, χn n w*G w) atTop
      (𝓝 (π * (-schwarzianHol W z/(6*deriv W z)))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hn herr)
  have heq := tendsto_nhds_unique hmain hres
  have hGset : ∫ w in Ωᶜ, G w = ∫ w, G w :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => hG0 w (by simpa using hw))
  change schwarzianHol W z = -(6/π)*deriv W z*∫ w in Ωᶜ, G w
  rw [hGset,heq]
  have hd : deriv W z ≠ 0 := deriv_ne_zero_of_injOn hΩ hWΩ
    (hW.2.2.1.2.1.mono (subset_univ Ω)) hz
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The Beltrami equation for a quasiconformal map forces measurability of its coefficient. -/
theorem cui_beltrami_measurable {W ν : ℂ → ℂ} {K : ℝ} (hW : IsKQC W univ K)
    (hν : ∀ᵐ w, dzbar W w = ν w * dz W w) : AEMeasurable ν volume := by
  have hJ : ∀ᵐ w, 0 < jacobian W w := by simpa using thm9_6_cor2_jacobian_pos hW
  apply ((measurable_dzbar W).div (measurable_dz W)).aemeasurable.congr
  filter_upwards [hν,hJ] with w hw hJw
  have hd : dz W w ≠ 0 := by
    intro hd
    simp [jacobian,hd] at hJw
    linarith [sq_nonneg ‖dzbar W w‖]
  exact (div_eq_iff hd).mpr hw

/-- Cauchy–Schwarz for extended nonnegative integrals, including infinite values. -/
theorem cui_lintegral_cauchy_schwarz {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : α → ℝ≥0∞} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) :
    (∫⁻ w, A w*B w ∂μ)^2 ≤ (∫⁻ w, A w^2 ∂μ)*(∫⁻ w, B w^2 ∂μ) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hA hB
  have hh2 := pow_le_pow_left₀ zero_le hh 2
  simp only [Pi.mul_apply,ENNReal.rpow_two,mul_pow,← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul] at hh2 ⊢
  norm_num at hh2 ⊢
  exact hh2

/-- (C4g) Pointwise Cauchy–Schwarz (Cui):
`|S_W(z)|² c_z² ≤ 576/(π(1-k²)) ∬_{Ωᶜ} |ν|²/|w - z|⁴`. -/
theorem cui_pointwise_gen {W : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hW : IsKQC W univ K) {Ω : Set ℂ} (hΩ : IsOpen Ω) (hWΩ : DifferentiableOn ℂ W Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hfΩ : f '' unitDisc ⊆ Ω) {ν : ℂ → ℂ} (hν : ∀ᵐ w, dzbar W w = ν w * dz W w)
    (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) {z' : ℂ} (hz' : z' ∈ unitDisc) :
    ENNReal.ofReal (‖schwarzianHol W (f z')‖ ^ 2 * ((1 - ‖z'‖ ^ 2) * ‖deriv f z'‖) ^ 2) ≤
      ENNReal.ofReal (576 / (π * (1 - k ^ 2))) *
        ∫⁻ w in Ωᶜ, ENNReal.ofReal (‖ν w‖ ^ 2 / ‖w - f z'‖ ^ 4) := by
  have hq : 0 < 1-k^2 := by nlinarith
  have hz1 : ‖z'‖ < 1 := mem_ball_zero_iff.mp hz'
  have hzq : 0 < 1-‖z'‖^2 := by nlinarith [norm_nonneg z']
  have hfz : f z' ∈ Ω := hfΩ ⟨z',hz',rfl⟩
  have hdW : deriv W (f z') ≠ 0 := deriv_ne_zero_of_injOn hΩ hWΩ
    (hW.2.2.1.2.1.mono (subset_univ Ω)) hfz
  have hdf : deriv f z' ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf hfi hz'
  let c : ℝ := (1-‖z'‖^2)*‖deriv f z'‖
  have hc : 0 < c := mul_pos hzq (norm_pos_iff.mpr hdf)
  let d : ℝ := ‖deriv W (f z')‖^2*c^2
  have hd : 0 < d := mul_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hdW)) (sq_pos_of_pos hc)
  let μ := volume.restrict Ωᶜ
  let A : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖ν w‖/‖w-f z'‖^2)
  let B : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖dz W w‖/‖W w-W (f z')‖^2)
  let G : ℂ → ℂ := fun w => dzbar W w/((W w-W (f z'))^2*(w-f z')^2)
  let J : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (jacobian W w/‖W w-W (f z')‖^4) ∂μ
  let N : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (‖ν w‖^2/‖w-f z'‖^4) ∂μ
  have hWm : Measurable W := (continuousOn_univ.mp hW.2.2.1.1).measurable
  have hAm : AEMeasurable A μ :=
    ((cui_beltrami_measurable hW hν).restrict.norm.div
      ((measurable_id.sub_const (f z')).norm.pow_const 2).aemeasurable).ennreal_ofReal
  have hBm : AEMeasurable B μ :=
    ((measurable_dz W).norm.div ((hWm.sub_const (W (f z'))).norm.pow_const 2)).ennreal_ofReal.aemeasurable
  have hA2 : (∫⁻ w, A w^2 ∂μ) = N := by
    apply lintegral_congr
    intro w
    dsimp [A]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    simp only [div_pow,← pow_mul]
  have hB2 : (∫⁻ w, B w^2 ∂μ) ≤ ENNReal.ofReal (1/(1-k^2))*J := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hν,ae_restrict_of_ae hνk] with w hνw hνkw
    have hcontrol : ‖dz W w‖^2 ≤ jacobian W w/(1-k^2) := by
      apply (le_div_iff₀ hq).mpr
      dsimp [jacobian]
      rw [hνw,norm_mul,mul_pow]
      have hn := pow_le_pow_left₀ (norm_nonneg (ν w)) hνkw 2
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg ‖dz W w‖)]
    dsimp [B]
    rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc (‖dz W w‖/‖W w-W (f z')‖^2)^2 = ‖dz W w‖^2/‖W w-W (f z')‖^4 := by
          simp only [div_pow,← pow_mul]
      _ ≤ (jacobian W w/(1-k^2))/‖W w-W (f z')‖^4 :=
        div_le_div_of_nonneg_right hcontrol (by positivity)
      _ = _ := by ring
  have harea : ENNReal.ofReal d*J ≤ ENNReal.ofReal (16*π) :=
    cui_area_bound_gen hW hΩ hWΩ hf hfi hfΩ hz'
  have hmass : (∫⁻ w, ‖G w‖ₑ ∂μ)^2 ≤ N*(ENNReal.ofReal (1/(1-k^2))*J) := by
    have he : (fun w => ‖G w‖ₑ) =ᵐ[μ] fun w => A w*B w := by
      filter_upwards [ae_restrict_of_ae hν] with w hw
      dsimp [G,A,B]
      rw [← ofReal_norm,hw,norm_div,norm_mul,norm_mul,norm_pow,norm_pow,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [div_eq_mul_inv,mul_inv]
      ring
    rw [lintegral_congr_ae he]
    exact (cui_lintegral_cauchy_schwarz μ hAm hBm).trans
      (mul_le_mul' hA2.le hB2)
  have hconst : 0 < 576/(π*(1-k^2)) := by positivity
  by_cases hN : N = ⊤
  · change _ ≤ ENNReal.ofReal (576/(π*(1-k^2)))*N
    rw [hN,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hconst))]
    exact le_top
  have hJfin : J < ⊤ := by
    by_contra hh
    have he : J = ⊤ := eq_top_iff.mpr (not_lt.mp hh)
    rw [he,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hd))] at harea
    exact ENNReal.ofReal_ne_top (top_le_iff.mp harea)
  have hmassfin : (∫⁻ w, ‖G w‖ₑ ∂μ) < ⊤ := by
    have hh := lt_of_le_of_lt hmass
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hN) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJfin))
    by_contra ht
    have he : (∫⁻ w, ‖G w‖ₑ ∂μ) = ⊤ := eq_top_iff.mpr (not_lt.mp ht)
    simp [he] at hh
  have hGi : Integrable G μ := ⟨((measurable_dzbar W).div
    (((hWm.sub_const (W (f z'))).pow_const 2).mul
      ((measurable_id.sub_const (f z')).pow_const 2))).aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.mpr hmassfin⟩
  have hformula := cui_exact_formula_gen hW hΩ hWΩ hfz hGi
  have hnorm : ENNReal.ofReal (‖schwarzianHol W (f z')‖^2*c^2) =
      ENNReal.ofReal (36/π^2)*ENNReal.ofReal d*‖∫ w, G w ∂μ‖ₑ^2 := by
    rw [hformula]
    have hn : ‖(-(6/π) : ℂ)‖ = 6/π := by
      rw [norm_neg,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      norm_num
    change ENNReal.ofReal (‖(-(6/π) : ℂ)*deriv W (f z')*∫ w, G w ∂μ‖^2*c^2) = _
    rw [norm_mul,norm_mul,hn,← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [d]
    ring
  change ENNReal.ofReal (‖schwarzianHol W (f z')‖^2*c^2) ≤
    ENNReal.ofReal (576/(π*(1-k^2)))*N
  rw [hnorm]
  calc ENNReal.ofReal (36/π^2)*ENNReal.ofReal d*‖∫ w, G w ∂μ‖ₑ^2
      ≤ ENNReal.ofReal (36/π^2)*ENNReal.ofReal d*(∫⁻ w, ‖G w‖ₑ ∂μ)^2 :=
        mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le (enorm_integral_le_lintegral_enorm G) 2)
    _ ≤ ENNReal.ofReal (36/π^2)*ENNReal.ofReal d*(N*(ENNReal.ofReal (1/(1-k^2))*J)) :=
        mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal (36/π^2)*ENNReal.ofReal (1/(1-k^2))*(ENNReal.ofReal d*J)*N := by ring
    _ ≤ ENNReal.ofReal (36/π^2)*ENNReal.ofReal (1/(1-k^2))*ENNReal.ofReal (16*π)*N :=
        mul_le_mul' (mul_le_mul' le_rfl harea) le_rfl
    _ = ENNReal.ofReal (576/(π*(1-k^2)))*N := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        <;> ring

/-- (C6g) **Cui's bound in disc coordinates** (frozen cross-lane statement; used by `l29r` part (b)).
`F` is a global `K`-qc homeomorphism of the plane, conformal on `Ω = f 𝔻`, with dilatation `ν` (`‖ν‖ ≤ k`);
`hI` is the exterior kernel bound on the interior of `Ωᶜ`, with the hyperbolic density `ρs` of `Ω*`. -/
theorem cui_disc_bound {f F ν : ℂ → ℂ} {K k C0 : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hC0 : 0 ≤ C0)
    (hf : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hF : IsKQC F univ K) (hFs : F '' univ = univ) (hFΩ : DifferentiableOn ℂ F (f '' unitDisc))
    (hν : ∀ᵐ u, dzbar F u = ν u * dz F u) (hνk : ∀ᵐ u, ‖ν u‖ ≤ k)
    (hnull : volume (frontier (f '' unitDisc)) = 0) (ρs : ℂ → ℝ)
    (hI : ∀ u ∈ interior ((f '' unitDisc)ᶜ),
      ∫⁻ y in f '' unitDisc, ENNReal.ofReal (1 / ‖u - y‖ ^ 4) ≤ ENNReal.ofReal (C0 * ρs u)) :
    ∫⁻ z in unitDisc, (‖schwarzianHol (F ∘ f) z - schwarzianHol f z‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (rho z)⁻¹ ≤
      ENNReal.ofReal (144 * C0 / (π * (1 - k ^ 2))) *
        ∫⁻ u in (f '' unitDisc)ᶜ, (‖ν u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (ρs u) := by
  have hΩ : IsOpen (f '' unitDisc) :=
    (show IsConformalOnto f unitDisc (f '' unitDisc) from ⟨hf,hfi,rfl⟩).isOpen isOpen_ball
  have hq : 0 < 1-k^2 := by nlinarith
  let P : ℂ → ℝ≥0∞ := fun y => ∫⁻ u in (f '' unitDisc)ᶜ,
    (‖ν u‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (1/‖u-y‖^4)
  have hP : ∀ y, (∫⁻ u in (f '' unitDisc)ᶜ, ENNReal.ofReal (‖ν u‖^2/‖u-y‖^4)) = P y := by
    intro y
    apply lintegral_congr
    intro u
    simp only [← enorm_eq_nnnorm,← ofReal_norm,← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  have hpoint : ∀ z ∈ unitDisc,
      (‖schwarzianHol (F ∘ f) z-schwarzianHol f z‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho z)⁻¹ ≤
        ENNReal.ofReal (144/(π*(1-k^2)))*(ENNReal.ofReal (‖deriv f z‖^2)*P (f z)) := by
    intro z hz
    have hfa := hf.analyticAt (isOpen_ball.mem_nhds hz)
    have hFa := hFΩ.analyticAt (hΩ.mem_nhds ⟨z,hz,rfl⟩)
    have hdf : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf hfi hz
    have hdF : deriv F (f z) ≠ 0 := deriv_ne_zero_of_injOn hΩ hFΩ
      (hF.2.2.1.2.1.mono (subset_univ _)) ⟨z,hz,rfl⟩
    have hchain := eq19_1_chain_rule hfa hdf hFa hdF
    rw [schwarzian_of_analyticAt (hFa.comp hfa),schwarzian_of_analyticAt hFa,
      schwarzian_of_analyticAt hfa] at hchain
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hzq : 0 < 1-‖z‖^2 := by nlinarith [norm_nonneg z]
    have hρ : 0 < rho z := by unfold rho; positivity
    have he : (‖schwarzianHol (F ∘ f) z-schwarzianHol f z‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho z)⁻¹ =
        ENNReal.ofReal (‖schwarzianHol F (f z)‖^2*((1-‖z‖^2)*‖deriv f z‖)^2)*
          ENNReal.ofReal (‖deriv f z‖^2/4) := by
      rw [hchain,add_sub_cancel_right]
      simp only [← enorm_eq_nnnorm,← ofReal_norm,norm_mul,norm_pow]
      rw [← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold rho
      field_simp
      <;> ring
    have hh := cui_pointwise_gen hk0 hk1 hF hΩ hFΩ hf hfi (Subset.refl _) hν hνk hz
    rw [hP] at hh
    rw [he]
    refine (mul_le_mul' hh le_rfl).trans_eq ?_
    calc (ENNReal.ofReal (576/(π*(1-k^2)))*P (f z))*ENNReal.ofReal (‖deriv f z‖^2/4)
        = ENNReal.ofReal ((576/(π*(1-k^2)))*(‖deriv f z‖^2/4))*P (f z) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ = ENNReal.ofReal (144/(π*(1-k^2)))*(ENNReal.ofReal (‖deriv f z‖^2)*P (f z)) := by
            rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring
  have hton := cui_kernel_tonelli_bound hΩ hnull
    ((cui_beltrami_measurable hF hν).restrict.nnnorm.coe_nnreal_ennreal.pow_const 2) hC0 ρs hI
  calc (∫⁻ z in unitDisc, (‖schwarzianHol (F ∘ f) z-schwarzianHol f z‖₊ : ℝ≥0∞)^2*
          ENNReal.ofReal (rho z)⁻¹)
      ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (144/(π*(1-k^2)))*
          (ENNReal.ofReal (‖deriv f z‖^2)*P (f z)) :=
        setLIntegral_mono' measurableSet_ball hpoint
    _ = ENNReal.ofReal (144/(π*(1-k^2)))*∫⁻ y in f '' unitDisc, P y := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact (r24_conformal_lintegral (U := unitDisc) isOpen_ball hf hfi P).symm
    _ ≤ ENNReal.ofReal (144/(π*(1-k^2)))*(ENNReal.ofReal C0*
        ∫⁻ u in (f '' unitDisc)ᶜ, (‖ν u‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (ρs u)) :=
          mul_le_mul' le_rfl hton
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

/-- **Cui's bound** (frozen statement; `C = 6/√(1-k²)`). -/
theorem cui_A2_bound {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : LinfStar, ‖ν‖ ≤ k →
      normA2 unitDisc (AInf.toFun (bersPhi ν)) ≤ ENNReal.ofReal C * normL2 unitDiscExterior ⇑ν := by
  have hq : 0 < 1-k^2 := by nlinarith
  let C : ℝ := 6/Real.sqrt (1-k^2)
  have hC : 0 < C := div_pos (by norm_num) (Real.sqrt_pos.mpr hq)
  refine ⟨C,hC,?_⟩
  intro ν hνk
  have hν : ν ∈ LinfStarBall := mem_ball_zero_iff.mpr (lt_of_le_of_lt hνk hk1)
  obtain ⟨hN,hWd,hWi,hW0⟩ := qcv_W_props (lt_of_le_of_lt hνk hk1)
  obtain ⟨K,hK⟩ := hN.1
  let W := qcv_planeSolution ν
  have hW : IsKQC W univ K := hK
  have hJ : ∀ᵐ u, 0 < jacobian W u := by simpa using thm9_6_cor2_jacobian_pos hW
  have hbel : ∀ᵐ u, dzbar W u = extB ν u*dz W u := by
    filter_upwards [hJ,hN.2.2.2.2] with u hJu hdu
    have hd : dz W u ≠ 0 := by
      intro hd
      simp [jacobian,hd] at hJu
      linarith [sq_nonneg ‖dzbar W u‖]
    exact (div_eq_iff hd).mp hdu
  have hbk : ∀ᵐ u, ‖extB ν u‖ ≤ k := by
    have hb := (extB_isBeltramiCoeff ν).2
    rw [Measure.restrict_univ] at hb
    exact hb.mono (fun u hu => hu.trans hνk)
  have hnull : volume (frontier unitDisc) = 0 := by
    rw [unitDisc,frontier_ball (0 : ℂ) one_ne_zero]
    exact Measure.addHaar_sphere volume (0 : ℂ) 1
  have hinside : interior unitDiscᶜ = unitDiscExterior := by
    rw [interior_compl,unitDisc,closure_ball (0 : ℂ) one_ne_zero]
    ext u
    simp [unitDiscExterior,mem_closedBall_zero_iff]
  have hI : ∀ u ∈ interior unitDiscᶜ,
      ∫⁻ y in unitDisc, ENNReal.ofReal (1/‖u-y‖^4) ≤ ENNReal.ofReal ((π/4)*rho u) := by
    intro u hu
    rw [hinside] at hu
    rw [cui_bergman hu]
    apply le_of_eq
    congr 1
    unfold rho
    ring
  have hb := cui_disc_bound (f := id) (F := W) hk0 hk1 (show 0 ≤ π/4 by positivity)
    differentiableOn_id (fun _ _ _ _ h => h) hW hN.2.1
    (by simpa only [image_id,W,qcv_planeSolution] using hWd) hbel hbk
    (by simpa using hnull) rho (by simpa using hI)
  have hright : (∫⁻ u in unitDiscᶜ, (‖extB ν u‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho u)) =
      ∫⁻ u in unitDiscExterior, (‖ν u‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho u) := by
    rw [← lintegral_indicator (show MeasurableSet unitDisc from isOpen_ball.measurableSet).compl,
      ← lintegral_indicator (show MeasurableSet unitDiscExterior from
        (isOpen_lt continuous_const continuous_norm).measurableSet)]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ unitDiscExterior
    · have hu' : u ∈ unitDiscᶜ := by
        rw [mem_compl_iff,unitDisc,mem_ball_zero_iff]
        exact not_lt.mpr (le_of_lt hu)
      simp [extB,hu,hu']
    · simp [extB,hu]
  have hidS : ∀ z : ℂ, schwarzianHol id z = 0 := by intro z; simp [schwarzianHol]
  simp only [image_id,Function.comp_id,hidS,sub_zero] at hb
  rw [hright] at hb
  have hcoef : 144*(π/4)/(π*(1-k^2)) = C^2 := by
    dsimp [C]
    rw [div_pow,Real.sq_sqrt hq.le]
    field_simp
    <;> ring
  rw [hcoef] at hb
  have hleft : (∫⁻ z in unitDisc, (‖AInf.toFun (bersPhi ν) z‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho z)⁻¹) =
      ∫⁻ z in unitDisc, (‖schwarzianHol W z‖₊ : ℝ≥0∞)^2*ENNReal.ofReal (rho z)⁻¹ := by
    apply setLIntegral_congr_fun isOpen_ball.measurableSet
    intro z hz
    simp only [W,cui_bers_eq_schwarzian hν hz]
  unfold normA2 normL2
  rw [hleft]
  refine (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1/2)).trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),ENNReal.ofReal_pow hC.le,
    ← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

end CUI
end TakhtajanTeo
