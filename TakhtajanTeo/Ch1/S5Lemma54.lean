import TakhtajanTeo.Ch1.S5RightTranslationHol
import TakhtajanTeo.Ch1.BanachHolomorphicAnalytic
import TakhtajanTeo.Ch1.S5Lemma51Completed

/-!
# `lemma_5_4` (`s5l54_`, 下属3, Program G): right invariance of `c₁(V)`

Host: new module `TakhtajanTeo/Ch1/S5Lemma54.lean`. Target `s5l54_lemma_5_4` is `lemma_5_4` (S5_ChernForms 574b3a9d) with
the prefixed name and a byte-identical statement.

Route (TT:2310–2326). Put `R = tcurveRight q₀`, `R̃ = tcCoordExpr R`, `x = tcCoordH q`, `D = dR̃(x)`.
* `R̃` is holomorphic near `x` (`s5rh_right_holo` on the open chart image `s5l54_image_nhds`; Banach holomorphy implies
  analyticity, `bha_analyticOnNhd`).
* Fibre metric law (`s5l54_metric_law`): near `x`, `log‖z²∂_z‖²(q') = log‖z²∂_z‖²(R q') + log|h|²`, with `h`
  holomorphic and nonvanishing. Here `h` is the fibre derivative of `R̃`: the hyperbolic metric is invariant under the
  conformal fibre isomorphisms.
* `log‖z²∂_z‖² ∘ tcCoordHInv` is real `C²` (`s5l54_regular`: `lemma_5_1` plus the real-analytic shift `c = f''(0)/2`).
* Levi chain rule for a real `C²` function under a holomorphic map (`s5l54_levi_chain`), and `∂∂̄ log|h|² = 0`
  (`s5l54_levi_log`). Hence `Levi_q(Y) = Levi_{Rq}(DY)` for all `Y`, and `polarize` along the linear `D` gives the
  `Θ` identity.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The memoir shift through the welding pole: `c_μ = f''(0)/2 = b_μ + a_μ P(μ)`, where `a = W'(0)`,
`b = W''(0)/(2a)`, and the pole term `P(μ) = 1/W(p_μ)` (`acc_wB_rep`) equals GPT's analytic
`ψ_{(μ,μ*)}(α_{(μ,μ*)}(0))` (`s5cf_planeB_inverse_wAS_reciprocal` at `t = 0`). -/
theorem s5l54_c_formula {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    deriv (deriv (fB μ)) 0 / 2 =
      deriv (deriv (normalizedSolution (extB μ))) 0 / (2 * deriv (normalizedSolution (extB μ)) 0) +
        deriv (normalizedSolution (extB μ)) 0 * s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := by
  have hinf0 : inversion extInf = ((0 : ℂ) : ExtPlane) := by
    rw [← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl, tcc_inversion_invol]
  have hv : OnePoint.map (normalizedSolution (extB μ)) extInf ≠ ((0 : ℂ) : ExtPlane) := by
    show (extInf : ExtPlane) ≠ _
    exact OnePoint.infty_ne_coe 0
  have hm := s5rh_memoir hμ hv
  obtain ⟨hd, -, hrep⟩ := AppA.acc_wB_rep hμ
  set d := deriv (normalizedSolution (extB μ)) 0 with hddef
  set P := finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
    (Function.invFun (wAS μ) extInf))) with hPdef
  have hZ : mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ)) extInf) = ((0 : ℂ) : ExtPlane) :=
    hinf0
  have h1 := s5cf_normalized_mobius_reciprocal (c := -P) hd hZ
  rw [← hrep] at h1
  have hP : P = s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := by
    have h := s5cf_planeB_inverse_wAS_reciprocal hμ (t := 0) (by simp [unitDisc])
    rw [mobiusExt_coe_of_eq_zero (by norm_num)] at h
    rw [hPdef, h]
    rfl
  have hw : finPart (inversion (wB μ extInf)) = d * (0 + -P) := by
    change finPart (mobiusExt 0 1 1 0 (wB μ extInf)) = _
    rw [h1]
    rfl
  have hW : finPart (inversion (OnePoint.map (normalizedSolution (extB μ)) extInf)) = 0 := by
    change finPart (inversion extInf) = 0
    rw [hinf0]
    rfl
  rw [hw, hW] at hm
  rw [← hP]
  linear_combination hm

/-- `c : ν ↦ f_ν''(0)/2` is real-analytic on `L∞(𝔻*)₁`. -/
theorem s5l54_c_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℝ (fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2) μ := by
  have hd := s5cf_planeB_deriv_analytic hμ
  have hd0 := s5cf_planeB_deriv_ne_zero hμ
  have h2 : AnalyticAt ℂ (fun ν : LinfStar => deriv (deriv (normalizedSolution (extB ν))) 0) μ := by
    exact bha_analyticOnNhd isOpen_ball s5rh_jet2_holo μ hμ
  have hP : AnalyticAt ℝ (fun ν : LinfStar => s5cf_reciprocal (ν, star ν) (s5cf_alpha (ν, star ν) 0)) μ := by
    have hc : AnalyticAt ℝ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 (s5cf_alpha q.1 q.2))
        ((μ, star μ), (0 : ℂ)) :=
      (s5cf_normalized_transition_analytic hμ (t := 0) (by simp [unitDisc])).restrictScalars
    have hJ : AnalyticAt ℝ (fun ν : LinfStar => (ν, star ν)) μ := analyticAt_id.prod (s5cf_star_analytic μ)
    have hm : AnalyticAt ℝ (fun ν : LinfStar => ((ν, star ν), (0 : ℂ))) μ :=
      hJ.prod (analyticAt_const (v := (0 : ℂ)))
    have hcomp := AnalyticAt.comp_of_eq
      (g := fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 (s5cf_alpha q.1 q.2))
      (f := fun ν : LinfStar => ((ν, star ν), (0 : ℂ))) hc hm rfl
    exact hcomp
  have hb : AnalyticAt ℝ (fun ν : LinfStar => deriv (deriv (normalizedSolution (extB ν))) 0 /
      (2 * deriv (normalizedSolution (extB ν)) 0)) μ :=
    (h2.div (analyticAt_const.mul hd) (mul_ne_zero two_ne_zero hd0)).restrictScalars
  have hS : AnalyticAt ℝ (fun ν : LinfStar =>
      deriv (deriv (normalizedSolution (extB ν))) 0 / (2 * deriv (normalizedSolution (extB ν)) 0) +
        deriv (normalizedSolution (extB ν)) 0 * s5cf_reciprocal (ν, star ν) (s5cf_alpha (ν, star ν) 0)) μ :=
    hb.add (hd.restrictScalars.mul hP)
  refine hS.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hμ] with ν hν
  exact (s5l54_c_formula hν).symm

/-- The image of the holomorphic chart `tcCoordH` is a neighbourhood of each of its points. -/
theorem s5l54_image_nhds {q : T1 × ExtPlane} (hq : q ∈ TCurve) : tcCoordH '' TCurve ∈ 𝓝 (tcCoordH q) := by
  suffices hs : ∀ᶠ y in 𝓝 (tcCoordH q), y ∈ tcCoordH '' TCurve from hs
  obtain ⟨sec, U, hU, hpU, hsa, hs0, hsec⟩ := s5cf_section_analytic q.1
  set ν₀ : LinfStar := ((Quotient.out q.1 : LinfStarBall) : LinfStar) with hν₀def
  have hν₀ : ν₀ ∈ LinfStarBall := (Quotient.out q.1 : LinfStarBall).2
  have hsd : DifferentiableAt ℂ sec (bers q.1) := (hsa _ hpU).differentiableAt
  set c : LinfStar → ℂ := fun ν => deriv (deriv (fB ν)) 0 / 2 with hc
  set x := tcCoordH q with hx
  have hsc : ContinuousAt (fun y : AInf unitDisc × ℂ => sec y.1) x := by
    have h1 : ContinuousAt sec x.1 := hsd.continuousAt
    exact h1.comp continuousAt_fst
  have hcc : ContinuousAt c (sec x.1) := by
    rw [show x.1 = bers q.1 from rfl, hs0]
    exact (s5rh_c_continuousOn.continuousAt (isOpen_ball.mem_nhds hν₀)).div_const 2
  set m : AInf unitDisc × ℂ → LinfStar × ExtPlane := fun y =>
    (sec y.1, inversion ((y.2 - c (sec y.1) : ℂ) : ExtPlane)) with hm
  have hmc : ContinuousAt m x := by
    refine hsc.prodMk ?_
    exact (tcc_inversion_continuous.comp OnePoint.continuous_coe).continuousAt.comp
      (continuousAt_snd.sub (ContinuousAt.comp (g := c) (f := fun y : AInf unitDisc × ℂ => sec y.1) hcc hsc))
  have ha0 : q.2 ≠ ((0 : ℂ) : ExtPlane) := fun h0 => tcc_zero_not_mem hν₀ (h0 ▸ hq)
  have hm0 : m x = (ν₀, q.2) := by
    have hback : inversion ((finPart (inversion q.2) : ℂ) : ExtPlane) = q.2 := by
      rw [coe_finPart_of_ne (fun h => ha0 ((tcc_inversion_eq_inf_iff q.2).mp h)), tcc_inversion_invol]
    have hs0' : sec x.1 = ν₀ := hs0
    simp only [hm, hs0']
    have he : x.2 - c ν₀ = finPart (inversion q.2) := by
      show finPart (inversion q.2) + deriv (deriv (fB ν₀)) 0 / 2 - deriv (deriv (fB ν₀)) 0 / 2 = _
      ring
    rw [he, hback]
  have hT := tcc_tube hν₀ hq
  have hT' : ∀ᶠ y in 𝓝 x, (m y).2 ∈ wB (m y).1 '' extDiscExterior := by
    have := hmc.tendsto
    rw [hm0] at this
    exact this.eventually hT
  have hUev : ∀ᶠ y in 𝓝 x, y.1 ∈ U := continuousAt_fst.eventually (hU.mem_nhds hpU)
  filter_upwards [hT', hUev] with y hyT hyU
  obtain ⟨h, hb⟩ := hsec y.1 hyU
  set q' : T1 × ExtPlane := (Phi (Subtype.mk (sec y.1) h), inversion ((y.2 - c (sec y.1) : ℂ) : ExtPlane))
    with hq'
  have hcls : teichSetoid (Quotient.out (Phi (Subtype.mk (sec y.1) h)) : LinfStarBall) (Subtype.mk (sec y.1) h) :=
    Quotient.mk_out (s := teichSetoid) (Subtype.mk (sec y.1) h : LinfStarBall)
  have hq'm : q' ∈ TCurve := by
    show q'.2 ∈ wB (Quotient.out q'.1 : LinfStarBall) '' extDiscExterior
    rw [fiber_independent hcls]
    exact hyT
  have hHq : tcCoordH q' = y := by
    simp only [hq', tcCoordH, tcc_inversion_invol, s5rh_c_congr (Subtype.mk (sec y.1) h)]
    refine Prod.ext hb ?_
    show (y.2 - c (sec y.1)) + deriv (deriv (fB (sec y.1))) 0 / 2 = y.2
    simp only [hc]
    ring
  exact ⟨q', hq'm, hHq⟩

/-- `log‖z²∂_z‖² ∘ tcCoordHInv` is real `C²` at every point of the chart image. -/
theorem s5l54_regular {q : T1 × ExtPlane} (hq : q ∈ TCurve) :
    ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w)) (tcCoordH q) := by
  -- Near `tcCoordH q`: `tcCoord ∘ tcCoordHInv = S`, `S(y) = (y.1, y.2 - c(sec y.1))` with an analytic Bers section
  -- `sec` and the real-analytic `c` (`s5l54_c_analytic`); then `lemma_5_1` and `logNormSq = 2 (potentialK + log 2)`.
  obtain ⟨sec, U, hU, hpU, hsa, hs0, hsec⟩ := s5cf_section_analytic q.1
  have hν₀ : ((Quotient.out q.1 : LinfStarBall) : LinfStar) ∈ LinfStarBall := (Quotient.out q.1 : LinfStarBall).2
  set S : AInf unitDisc × ℂ → AInf unitDisc × ℂ := fun y => (y.1, y.2 - deriv (deriv (fB (sec y.1))) 0 / 2)
    with hSdef
  have hsecR : AnalyticAt ℝ (fun y : AInf unitDisc × ℂ => sec y.1) (tcCoordH q) :=
    AnalyticAt.comp_of_eq (g := sec) (f := fun y : AInf unitDisc × ℂ => y.1)
      ((hsa _ hpU).restrictScalars (𝕜 := ℝ)) analyticAt_fst rfl
  have hc : AnalyticAt ℝ (fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2) (sec (tcCoordH q).1) := by
    rw [show (tcCoordH q).1 = bers q.1 from rfl, hs0]
    exact s5l54_c_analytic hν₀
  have hcs : AnalyticAt ℝ (fun y : AInf unitDisc × ℂ => deriv (deriv (fB (sec y.1))) 0 / 2) (tcCoordH q) :=
    AnalyticAt.comp_of_eq (g := fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2)
      (f := fun y : AInf unitDisc × ℂ => sec y.1) hc hsecR rfl
  have hS : AnalyticAt ℝ S (tcCoordH q) := analyticAt_fst.prod (analyticAt_snd.sub hcs)
  have hS0 : S (tcCoordH q) = tcCoord q := by
    show ((tcCoordH q).1, (tcCoordH q).2 - deriv (deriv (fB (sec (tcCoordH q).1))) 0 / 2) =
      (bers q.1, finPart (inversion q.2))
    rw [show (tcCoordH q).1 = bers q.1 from rfl, hs0]
    show (bers q.1, finPart (inversion q.2) + deriv (deriv (fB ((Quotient.out q.1 : LinfStarBall) : LinfStar))) 0 / 2 -
      deriv (deriv (fB ((Quotient.out q.1 : LinfStarBall) : LinfStar))) 0 / 2) = _
    rw [add_sub_cancel_right]
  have hK := lemma_5_1.1 (tcCoord q) ⟨q, hq, rfl⟩
  have hKS : AnalyticAt ℝ (fun w => potentialK (tcCoordInv (S w))) (tcCoordH q) :=
    AnalyticAt.comp_of_eq (g := fun x => potentialK (tcCoordInv x)) (f := S) hK hS hS0
  have hF : AnalyticAt ℝ (fun w => 2 * (potentialK (tcCoordInv (S w)) + Real.log 2)) (tcCoordH q) :=
    analyticAt_const.mul (hKS.add analyticAt_const)
  refine hF.contDiffAt.congr_of_eventuallyEq ?_
  have hUev : ∀ᶠ y : AInf unitDisc × ℂ in 𝓝 (tcCoordH q), y.1 ∈ U :=
    continuousAt_fst.eventually (hU.mem_nhds hpU)
  filter_upwards [s5l54_image_nhds hq, hUev] with y hy hyU
  have hq'm : tcCoordHInv y ∈ TCurve := Function.invFunOn_mem hy
  have hHy : tcCoordH (tcCoordHInv y) = y := Function.invFunOn_eq hy
  set q' := tcCoordHInv y with hq'def
  obtain ⟨h, hb⟩ := hsec y.1 hyU
  have h1 : q'.1 = Phi ⟨sec y.1, h⟩ := bers_injective (by rw [hb]; exact congrArg Prod.fst hHy)
  have hc' : deriv (deriv (fB ((Quotient.out q'.1 : LinfStarBall) : LinfStar))) 0 =
      deriv (deriv (fB (sec y.1))) 0 := by
    rw [h1]
    exact s5rh_c_congr _
  have hT : tcCoord q' = S y := by
    have h2 := congrArg Prod.snd hHy
    change finPart (inversion q'.2) + deriv (deriv (fB ((Quotient.out q'.1 : LinfStarBall) : LinfStar))) 0 / 2 =
      y.2 at h2
    rw [hc'] at h2
    refine Prod.ext (show bers q'.1 = y.1 from congrArg Prod.fst hHy) ?_
    show finPart (inversion q'.2) = y.2 - deriv (deriv (fB (sec y.1))) 0 / 2
    rw [← h2]
    ring
  have hinv : tcCoordInv (tcCoord q') = q' := tcCoord_chart.1.leftInvOn_invFunOn hq'm
  show logNormSq q' = 2 * (potentialK (tcCoordInv (S y)) + Real.log 2)
  rw [← hT, hinv]
  show logNormSq q' = 2 * (logNormSq q' / 2 - Real.log 2 + Real.log 2)
  ring

/-- Fibre points in the `ζ = 1/z` coordinate, in the form used by `fiberUniformizer` (any `μ` in the ball; the
representative version is `s5fg_actual_fiber_condition`). -/
theorem s5l54_fib_cond {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ExtPlane} (hz : z ∈ wB μ '' extDiscExterior) :
    finPart (inversion z) = 0 ∨ ∃ w ∈ unitDiscExterior, finPart (inversion z) = (gMu μ w)⁻¹ := by
  rw [← tcg_welding_image hμ] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  rcases hu with ⟨w, hw, rfl⟩ | hu
  · right
    refine ⟨w, hw, ?_⟩
    have hg := gMu_exterior_ne_zero hμ hw
    rw [← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw]
    simp [inversion, mobiusExt, hg, finPart]
  · have hu' : u = extInf := hu
    subst u
    left
    rw [normalizedWeldingSphere_infty hμ]
    simp [inversion, mobiusExt, finPart, extInf]

/-- Conversely, the points `0` and `1/g_μ(w)` are fibre points. -/
theorem s5l54_cond_fib {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ζ : ℂ}
    (hζ : ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) :
    inversion (ζ : ExtPlane) ∈ wB μ '' extDiscExterior := by
  rw [← tcg_welding_image hμ]
  rcases hζ with rfl | ⟨w, hw, rfl⟩
  · refine ⟨extInf, Or.inr rfl, ?_⟩
    rw [normalizedWeldingSphere_infty hμ, ← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl]
  · have hg := gMu_exterior_ne_zero hμ hw
    refine ⟨(w : ExtPlane), Or.inl ⟨w, hw, rfl⟩, ?_⟩
    rw [s5rh_inversion_coe (inv_ne_zero hg), inv_inv, ← normalizedWeldingExterior_coe hμ,
      ← gMu_eq_normalizedWeldingExterior hμ hw]

/-- The inverse uniformizer `gchart` takes values in the `fiberUniformizer` domain. -/
theorem s5l54_gchart_cond {μ : LinfStar} {t : ℂ} (ht : t ∈ unitDisc) :
    s5cf_gchart μ t = 0 ∨ ∃ w ∈ unitDiscExterior, s5cf_gchart μ t = (gMu μ w)⁻¹ := by
  by_cases ht0 : t = 0
  · left
    simp [s5cf_gchart, ht0]
  · right
    have hw : t⁻¹ ∈ unitDiscExterior := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ht0, mem_ball_zero_iff.mp ht⟩
    exact ⟨t⁻¹, hw, by simp [s5cf_gchart, ht0]⟩

/-- A fibre point is not `0`, so `inversion` of its `ζ` coordinate gives it back. -/
theorem s5l54_inv_finPart {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ExtPlane} (hz : z ∈ wB μ '' extDiscExterior) :
    inversion ((finPart (inversion z) : ℂ) : ExtPlane) = z := by
  have h0 : z ≠ ((0 : ℂ) : ExtPlane) := fun h => tcc_zero_not_mem hμ (h ▸ hz)
  rw [coe_finPart_of_ne (fun h => h0 ((tcc_inversion_eq_inf_iff z).mp h)), tcc_inversion_invol]

/-- `OnePoint.map` of an injective map is injective. -/
theorem s5l54_map_inj {f : ℂ → ℂ} (hf : Function.Injective f) : Function.Injective (OnePoint.map f) := by
  intro a b hab
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => rfl
    | coe b => exact absurd hab.symm (by simp [OnePoint.map_some, OnePoint.map_infty])
  | coe a =>
    induction b using OnePoint.rec with
    | infty => exact absurd hab (by simp [OnePoint.map_some, OnePoint.map_infty])
    | coe b =>
      simp only [OnePoint.map_some] at hab
      rw [hf (OnePoint.coe_injective hab)]

/-- The fibre map `T_ν(ζ) = 1/(w^λ ∘ 𝗀 ∘ (w^ν)⁻¹)(1/ζ)` of the right translation (`λ = λ(ν, 𝗀)`): it maps the fibre
of `ν` bijectively onto the fibre of `λ`, and is holomorphic there (`s5rh_fibre_holo`). -/
theorem s5l54_T_props {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {ν : LinfStar} (hν : ν ∈ LinfStarBall) :
    tcurveLambda ν G ∈ LinfStarBall ∧
    (∀ ζ : ℂ, inversion (ζ : ExtPlane) ∈ wB ν '' extDiscExterior →
      tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane)) ∈ wB (tcurveLambda ν G) '' extDiscExterior ∧
      DifferentiableAt ℂ (fun ζ : ℂ => finPart (inversion (tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane)))))
        ζ) ∧
    InjOn (fun ζ : ℂ => finPart (inversion (tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane)))))
      {ζ | inversion (ζ : ExtPlane) ∈ wB ν '' extDiscExterior} ∧
    (∀ ξ : ℂ, inversion (ξ : ExtPlane) ∈ wB (tcurveLambda ν G) '' extDiscExterior →
      ∃ ζ : ℂ, inversion (ζ : ExtPlane) ∈ wB ν '' extDiscExterior ∧
        finPart (inversion (tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane)))) = ξ) := by
  obtain ⟨hLd, hLm⟩ := s5rh_lambda_holo hμ hu hG
  obtain ⟨K, e, hK, he, hD, hCl, -⟩ := tmi_G_data hμ hu hG
  have hcb : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ e x ∈ closedBall (0 : ℂ) 1 := tmi_cb_iff (he ▸ hCl)
  have hGext : ∀ p ∈ extDiscExterior, OnePoint.map G p ∈ extDiscExterior := by
    intro p hp
    rw [fi_extDiscExterior_eq_compl] at hp ⊢
    exact fun h => hp ((tmi_map_iff hcb p).2 (by simpa [← he] using h))
  have hGinj : Function.Injective G := by
    rw [← he]
    exact e.injective
  have hGsurj : ∀ p ∈ extDiscExterior, ∃ y ∈ extDiscExterior, OnePoint.map G y = p := by
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact ⟨extInf, Or.inr rfl, OnePoint.map_infty G⟩
    | coe z =>
      rcases hp with ⟨w, hw, hwz⟩ | hp
      · have hwz' : w = z := OnePoint.coe_injective hwz
        subst hwz'
        rw [← hD] at hw
        obtain ⟨y, hy, rfl⟩ := hw
        exact ⟨(y : ExtPlane), Or.inl ⟨y, hy, rfl⟩, OnePoint.map_some G y⟩
      · exact absurd hp (OnePoint.coe_ne_infty z)
  set lam := tcurveLambda ν G with hlam
  have hl : lam ∈ LinfStarBall := hLm hν
  have hZ : ∀ y ∈ extDiscExterior, tcurveZ ν G lam (wB ν y) = wB lam (OnePoint.map G y) := by
    intro y hy
    show wB lam (OnePoint.map G (Function.invFun (wB ν) (wB ν y))) = _
    rw [Function.leftInverse_invFun (wB_bijective ν).1 y]
  refine ⟨hl, fun ζ hζ => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨y, hy, hyz⟩ := hζ
    rw [← hyz, hZ y hy]
    exact ⟨_, hGext y hy, rfl⟩
  · set c : LinfStar → ℂ := fun ν => deriv (deriv (fB ν)) 0 / 2 with hc
    have hs₀ : inversion (((ζ + c ν) - deriv (deriv (fB ν)) 0 / 2 : ℂ) : ExtPlane) ∈ wB ν '' extDiscExterior := by
      simpa [hc] using hζ
    have hfib := s5rh_fibre_holo hμ hu hG hν hs₀
    have hk : DifferentiableAt ℂ (fun ζ' : ℂ => (ν, ζ' + c ν)) ζ :=
      (differentiableAt_const _).prodMk (differentiableAt_id.add_const _)
    have hcomp := DifferentiableAt.comp (g := fun p : LinfStar × ℂ =>
      finPart (inversion (tcurveZ p.1 G (tcurveLambda p.1 G)
        (inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane)))) +
        deriv (deriv (fB (tcurveLambda p.1 G))) 0 / 2) (f := fun ζ' : ℂ => (ν, ζ' + c ν)) ζ hfib hk
    have hT := hcomp.sub_const (deriv (deriv (fB lam)) 0 / 2)
    convert hT using 1
    funext ζ'
    simp only [Function.comp_apply, hc, hlam, add_sub_cancel_right]
  · intro ζ₁ h₁ ζ₂ h₂ h12
    obtain ⟨y₁, hy₁, hz₁⟩ := h₁
    obtain ⟨y₂, hy₂, hz₂⟩ := h₂
    have hm₁ : tcurveZ ν G lam (inversion (ζ₁ : ExtPlane)) ∈ wB lam '' extDiscExterior := by
      rw [← hz₁, hZ y₁ hy₁]; exact ⟨_, hGext y₁ hy₁, rfl⟩
    have hm₂ : tcurveZ ν G lam (inversion (ζ₂ : ExtPlane)) ∈ wB lam '' extDiscExterior := by
      rw [← hz₂, hZ y₂ hy₂]; exact ⟨_, hGext y₂ hy₂, rfl⟩
    have h := congrArg (fun ξ : ℂ => inversion (ξ : ExtPlane)) h12
    simp only [s5l54_inv_finPart hl hm₁, s5l54_inv_finPart hl hm₂] at h
    rw [← hz₁, ← hz₂, hZ y₁ hy₁, hZ y₂ hy₂] at h
    have hy : y₁ = y₂ := s5l54_map_inj hGinj ((wB_bijective lam).1 h)
    have hc' : inversion (ζ₁ : ExtPlane) = inversion (ζ₂ : ExtPlane) := by rw [← hz₁, ← hz₂, hy]
    have hc := congrArg inversion hc'
    rw [tcc_inversion_invol, tcc_inversion_invol] at hc
    exact OnePoint.coe_injective hc
  · intro ξ hξ
    obtain ⟨y'', hy'', hyξ⟩ := hξ
    obtain ⟨y, hy, rfl⟩ := hGsurj y'' hy''
    have hz : wB ν y ∈ wB ν '' extDiscExterior := ⟨y, hy, rfl⟩
    refine ⟨finPart (inversion (wB ν y)), ?_, ?_⟩
    · rw [s5l54_inv_finPart hν hz]; exact hz
    · rw [s5l54_inv_finPart hν hz, hZ y hy, hyξ, tcc_inversion_invol]
      rfl

/-- `A = F_λ ∘ T_ν ∘ F_ν⁻¹` is a conformal automorphism of `𝔻` (`F = fiberUniformizer`, `F_ν⁻¹ = gchart`). -/
theorem s5l54_A_conformal {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {ν : LinfStar} (hν : ν ∈ LinfStarBall) {T : ℂ → ℂ}
    (hT : T = fun ζ : ℂ => finPart (inversion (tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane))))) :
    IsConformalOnto (fun t => fiberUniformizer (tcurveLambda ν G) (T (s5cf_gchart ν t))) unitDisc unitDisc := by
  obtain ⟨hl, hmap, hinj, hsurj⟩ := s5l54_T_props hμ hu hG hν
  subst hT
  set lam := tcurveLambda ν G with hlam
  have hpt : ∀ t ∈ unitDisc, inversion ((s5cf_gchart ν t : ℂ) : ExtPlane) ∈ wB ν '' extDiscExterior := fun t ht =>
    s5l54_cond_fib hν (s5l54_gchart_cond ht)
  refine ⟨fun t ht => ?_, fun t₁ h₁ t₂ h₂ he => ?_, ?_⟩
  · obtain ⟨hzm, hTd⟩ := hmap _ (hpt t ht)
    have hF := (s5fg_uniformizer_regular hl (s5l54_fib_cond hl hzm)).1
    have hg := (s5cf_gchart_analytic hν ht).differentiableAt
    exact (hF.differentiableAt.comp t (hTd.comp t hg)).differentiableWithinAt
  · obtain ⟨hzm₁, -⟩ := hmap _ (hpt t₁ h₁)
    obtain ⟨hzm₂, -⟩ := hmap _ (hpt t₂ h₂)
    have e₁ := (s5cf_uniformizer_inverse_data hl (s5l54_fib_cond hl hzm₁)).2
    have e₂ := (s5cf_uniformizer_inverse_data hl (s5l54_fib_cond hl hzm₂)).2
    have he' := congrArg (s5cf_gchart lam) he
    simp only [] at he'
    rw [e₁, e₂] at he'
    exact s5cf_gchart_inj hν h₁ h₂ (hinj (hpt t₁ h₁) (hpt t₂ h₂) he')
  · ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨hzm, -⟩ := hmap _ (hpt t ht)
      exact (s5cf_uniformizer_inverse_data hl (s5l54_fib_cond hl hzm)).1
    · intro hv
      obtain ⟨ζ, hζ, hTζ⟩ := hsurj _ (s5l54_cond_fib hl (s5l54_gchart_cond (μ := lam) hv))
      have hζc := s5l54_fib_cond hν hζ
      rw [tcc_inversion_invol] at hζc
      change ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu ν w)⁻¹ at hζc
      obtain ⟨hu', hgu⟩ := s5cf_uniformizer_inverse_data hν hζc
      refine ⟨fiberUniformizer ν ζ, hu', ?_⟩
      show fiberUniformizer lam (finPart (inversion (tcurveZ ν G lam
        (inversion ((s5cf_gchart ν (fiberUniformizer ν ζ) : ℂ) : ExtPlane))))) = v
      rw [hgu, hTζ, s5cf_uniformizer_left hl hv]

/-- **Pointwise fibre metric law.** At a fibre point `ζ` of `ν`, the hyperbolic metric `log ρ_ν` of the fibre is
`log ρ_λ(T ζ) + log |T'(ζ)|²`, and `T'(ζ) ≠ 0` (`tcg_density_pullback` for the automorphism `s5l54_A_conformal`). -/
theorem s5l54_metric_pointwise {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {ν : LinfStar} (hν : ν ∈ LinfStarBall) {T : ℂ → ℂ}
    (hT : T = fun ζ : ℂ => finPart (inversion (tcurveZ ν G (tcurveLambda ν G) (inversion (ζ : ExtPlane)))))
    {ζ : ℂ} (hζ : inversion (ζ : ExtPlane) ∈ wB ν '' extDiscExterior) :
    deriv T ζ ≠ 0 ∧
      Real.log (4 * ‖deriv (fiberUniformizer ν) ζ‖ ^ 2 / (1 - ‖fiberUniformizer ν ζ‖ ^ 2) ^ 2) =
        Real.log (4 * ‖deriv (fiberUniformizer (tcurveLambda ν G)) (T ζ)‖ ^ 2 /
          (1 - ‖fiberUniformizer (tcurveLambda ν G) (T ζ)‖ ^ 2) ^ 2) + Real.log (‖deriv T ζ‖ ^ 2) := by
  have hA := s5l54_A_conformal hμ hu hG hν hT
  obtain ⟨hl, hmap, -, -⟩ := s5l54_T_props hμ hu hG hν
  set lam := tcurveLambda ν G with hlam
  obtain ⟨hzm, hTd⟩ := hmap ζ hζ
  rw [← hT] at hTd
  have hζc := s5l54_fib_cond hν hζ
  rw [tcc_inversion_invol] at hζc
  change ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu ν w)⁻¹ at hζc
  obtain ⟨hFa, hFn, hFd⟩ := s5fg_uniformizer_regular hν hζc
  obtain ⟨hu', hgu⟩ := s5cf_uniformizer_inverse_data hν hζc
  have hTc : T ζ = 0 ∨ ∃ w ∈ unitDiscExterior, T ζ = (gMu lam w)⁻¹ := by
    rw [hT]
    exact s5l54_fib_cond hl hzm
  obtain ⟨hLa, hLn, hLd⟩ := s5fg_uniformizer_regular hl hTc
  set t₀ := fiberUniformizer ν ζ with ht₀
  have hdens := tcg_density_pullback hA hu'
  have hg := (s5cf_gchart_analytic hν hu').differentiableAt.hasDerivAt
  -- `F_ν ∘ gchart_ν = id` near `t₀`
  have hF1 : HasDerivAt (fiberUniformizer ν) (deriv (fiberUniformizer ν) ζ) (s5cf_gchart ν t₀) := by
    rw [hgu]
    exact hFa.differentiableAt.hasDerivAt
  have hFg := hF1.comp t₀ hg
  have hid : HasDerivAt (fiberUniformizer ν ∘ s5cf_gchart ν) 1 t₀ := by
    refine (hasDerivAt_id t₀).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hu'] with t ht
    exact s5cf_uniformizer_left hν ht
  have hone : deriv (fiberUniformizer ν) ζ * deriv (s5cf_gchart ν) t₀ = 1 := hFg.unique hid
  -- the derivative of `A` at `t₀`
  have hT1 : HasDerivAt T (deriv T ζ) (s5cf_gchart ν t₀) := by
    rw [hgu]
    exact hTd.hasDerivAt
  have hTg := hT1.comp t₀ hg
  have hL1 : HasDerivAt (fiberUniformizer lam) (deriv (fiberUniformizer lam) (T ζ)) ((T ∘ s5cf_gchart ν) t₀) := by
    show HasDerivAt _ _ (T (s5cf_gchart ν t₀))
    rw [hgu]
    exact hLa.differentiableAt.hasDerivAt
  have hAd : HasDerivAt (fun t => fiberUniformizer lam (T (s5cf_gchart ν t)))
      (deriv (fiberUniformizer lam) (T ζ) * (deriv T ζ * deriv (s5cf_gchart ν) t₀)) t₀ := hL1.comp t₀ hTg
  rw [hAd.deriv] at hdens
  rw [hgu] at hdens
  -- algebra
  set a := deriv (fiberUniformizer lam) (T ζ) with ha
  set b := deriv T ζ with hb
  set c := deriv (s5cf_gchart ν) t₀ with hc
  set d := deriv (fiberUniformizer ν) ζ with hd
  have hn : ‖d‖ ^ 2 * ‖c‖ ^ 2 = 1 := by rw [← mul_pow, ← norm_mul, hone, norm_one, one_pow]
  have hkey : rho t₀ * ‖d‖ ^ 2 = rho (fiberUniformizer lam (T ζ)) * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    rw [← hdens, norm_mul, norm_mul]
    linear_combination (rho (fiberUniformizer lam (T ζ)) * ‖a‖ ^ 2 * ‖b‖ ^ 2) * hn
  have hrho : ∀ z : ℂ, ‖z‖ < 1 → 0 < rho z := fun z hz => by
    unfold rho
    have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    positivity
  have hP1 : 0 < rho t₀ * ‖d‖ ^ 2 := mul_pos (hrho _ hFn) (by positivity)
  have hP2 : 0 < rho (fiberUniformizer lam (T ζ)) * ‖a‖ ^ 2 := mul_pos (hrho _ hLn) (by positivity)
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hkey
    nlinarith
  have hE : ∀ z w : ℂ, 4 * ‖w‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 = rho z * ‖w‖ ^ 2 := fun z w => by
    unfold rho
    ring
  refine ⟨hb0, ?_⟩
  rw [hE, hE, hkey, Real.log_mul hP2.ne' (by positivity)]

/-- The fibre metric law at one point `q'`: with `h = ∂_s R̃₂` (the fibre derivative of `R̃` in `tcCoordH`),
`h(q') = T'(ζ') ≠ 0` and `log‖z²∂_z‖²(q') = log‖z²∂_z‖²(R q') + log|h|²`. -/
theorem s5l54_law_at {q₀ q' : T1 × ExtPlane} (hq₀ : q₀ ∈ TCurve) (hq' : q' ∈ TCurve) :
    (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q') ((0 : AInf unitDisc), (1 : ℂ))).2 ≠ 0 ∧
      logNormSq q' = logNormSq (tcurveRight q₀ q') +
        Real.log (‖(fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q') ((0 : AInf unitDisc), (1 : ℂ))).2‖ ^ 2) := by
  set b := tcurveMulInv tOrigin q₀ with hbdef
  have hb : b ∈ TCurve := tcg_mul_mem_curve s5rh_tOrigin_mem hq₀
  set μb : LinfStar := ((Quotient.out b.1 : LinfStarBall) : LinfStar) with hμbdef
  have hμb : μb ∈ LinfStarBall := (Quotient.out b.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμb hb
  obtain ⟨G, hG⟩ := tcg_extension_exists hμb hu
  set ν : LinfStar := ((Quotient.out q'.1 : LinfStarBall) : LinfStar) with hνdef
  have hν : ν ∈ LinfStarBall := (Quotient.out q'.1 : LinfStarBall).2
  have hcl : Phi ⟨ν, hν⟩ = q'.1 := Quotient.out_eq q'.1
  obtain ⟨hl, hRq⟩ := s5rh_mulInv_rep hq' hb hν hcl hG
  set lam := tcurveLambda ν G with hlam
  set T : ℂ → ℂ := fun ζ => finPart (inversion (tcurveZ ν G lam (inversion (ζ : ExtPlane)))) with hT
  set ζ' := finPart (inversion q'.2) with hζ'def
  have hback : inversion (ζ' : ExtPlane) = q'.2 := s5l54_inv_finPart hν hq'
  have hζ : inversion (ζ' : ExtPlane) ∈ wB ν '' extDiscExterior := by
    rw [hback]
    exact hq'
  obtain ⟨hT0, hlaw⟩ := s5l54_metric_pointwise hμb hu hG hν hT hζ
  obtain ⟨-, hmap, -, -⟩ := s5l54_T_props hμb hu hG hν
  have hTd : DifferentiableAt ℂ T ζ' := (hmap ζ' hζ).2
  set R := tcurveRight q₀ with hRdef
  set w := tcCoordH q' with hwdef
  -- `h(w) = T'(ζ')`
  set D := fderiv ℂ (tcCoordExpr R) w with hDdef
  have hRd : HasFDerivAt (tcCoordExpr R) D w := (s5rh_right_holo hq₀ hq').hasFDerivAt
  have hline : HasDerivAt (fun s : ℂ => (w.1, s)) ((0 : AInf unitDisc), (1 : ℂ)) w.2 :=
    (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2)
  have hcomp := hRd.comp_hasDerivAt_of_eq w.2 hline rfl
  have hsnd := (ContinuousLinearMap.snd ℂ (AInf unitDisc) ℂ).hasFDerivAt.comp_hasDerivAt w.2 hcomp
  have hw2 : w.2 - deriv (deriv (fB ν)) 0 / 2 = ζ' := by
    show finPart (inversion q'.2) + deriv (deriv (fB ν)) 0 / 2 - deriv (deriv (fB ν)) 0 / 2 = _
    ring
  have hTd' : HasDerivAt T (deriv T ζ') (w.2 - deriv (deriv (fB ν)) 0 / 2) := by
    rw [hw2]
    exact hTd.hasDerivAt
  have hmodel : HasDerivAt (fun s : ℂ => T (s - deriv (deriv (fB ν)) 0 / 2) + deriv (deriv (fB lam)) 0 / 2)
      (deriv T ζ' * 1) w.2 :=
    (hTd'.comp w.2 ((hasDerivAt_id w.2).sub_const _)).add_const _
  have hmem : tcCoordH '' TCurve ∈ 𝓝 ((fun s : ℂ => (w.1, s)) w.2) := s5l54_image_nhds hq'
  have hNb : ∀ᶠ s in 𝓝 w.2, (w.1, s) ∈ tcCoordH '' TCurve :=
    ((continuous_const.prodMk continuous_id).tendsto w.2).eventually_mem hmem
  have hev : (fun s : ℂ => T (s - deriv (deriv (fB ν)) 0 / 2) + deriv (deriv (fB lam)) 0 / 2) =ᶠ[𝓝 w.2]
      fun s : ℂ => (ContinuousLinearMap.snd ℂ (AInf unitDisc) ℂ) (tcCoordExpr R (w.1, s)) := by
    filter_upwards [hNb] with s hs
    obtain ⟨qs, hqs, hqsw⟩ := hs
    have hqs1 : qs.1 = q'.1 := bers_injective (congrArg Prod.fst hqsw)
    have hcl' : Phi ⟨ν, hν⟩ = qs.1 := hcl.trans hqs1.symm
    have hνs : ((Quotient.out qs.1 : LinfStarBall) : LinfStar) = ν := by rw [hqs1]
    have hqs2 : finPart (inversion qs.2) + deriv (deriv (fB ν)) 0 / 2 = s := by
      have h2 := congrArg Prod.snd hqsw
      change finPart (inversion qs.2) +
        deriv (deriv (fB ((Quotient.out qs.1 : LinfStarBall) : LinfStar))) 0 / 2 = s at h2
      rwa [hνs] at h2
    have hqsν : qs.2 ∈ wB ν '' extDiscExterior := by
      have h := hqs
      change qs.2 ∈ wB ((Quotient.out qs.1 : LinfStarBall) : LinfStar) '' extDiscExterior at h
      rwa [hνs] at h
    have hqs2' : qs.2 = inversion ((s - deriv (deriv (fB ν)) 0 / 2 : ℂ) : ExtPlane) := by
      rw [← s5l54_inv_finPart hν hqsν, ← hqs2, add_sub_cancel_right]
    have hinv : tcCoordHInv (w.1, s) = qs := by
      rw [← hqsw]
      exact s5rh_injOn.leftInvOn_invFunOn hqs
    obtain ⟨hl', hRqs⟩ := s5rh_mulInv_rep hqs hb hν hcl' hG
    show _ = (tcCoordH (R (tcCoordHInv (w.1, s)))).2
    rw [hinv]
    show _ = (tcCoordH (tcurveMulInv qs b)).2
    rw [hRqs]
    show _ = finPart (inversion (tcurveZ ν G lam qs.2)) +
      deriv (deriv (fB ((Quotient.out (Phi ⟨lam, hl'⟩) : LinfStarBall) : LinfStar))) 0 / 2
    rw [s5rh_c_congr ⟨lam, hl'⟩, hqs2']
  have hmodel' := hmodel.congr_of_eventuallyEq hev.symm
  have hhT : (D ((0 : AInf unitDisc), (1 : ℂ))).2 = deriv T ζ' := by
    have h := hsnd.unique hmodel'
    rw [mul_one] at h
    exact h
  rw [hhT]
  refine ⟨hT0, ?_⟩
  -- the two metrics
  have hcls : teichSetoid (Quotient.out (Phi ⟨lam, hl⟩) : LinfStarBall) ⟨lam, hl⟩ :=
    Quotient.mk_out (s := teichSetoid) (⟨lam, hl⟩ : LinfStarBall)
  have hU := s5cf_uniformizer_congr hcls
  have hRq' : R q' = (Phi ⟨lam, hl⟩, tcurveZ ν G lam q'.2) := hRq
  have hL : logNormSq (R q') = Real.log (4 * ‖deriv (fiberUniformizer lam) (T ζ')‖ ^ 2 /
      (1 - ‖fiberUniformizer lam (T ζ')‖ ^ 2) ^ 2) := by
    rw [hRq']
    show Real.log (4 * ‖deriv (fiberUniformizer ((Quotient.out (Phi ⟨lam, hl⟩) : LinfStarBall) : LinfStar))
      (finPart (inversion (tcurveZ ν G lam q'.2)))‖ ^ 2 /
      (1 - ‖fiberUniformizer ((Quotient.out (Phi ⟨lam, hl⟩) : LinfStarBall) : LinfStar)
        (finPart (inversion (tcurveZ ν G lam q'.2)))‖ ^ 2) ^ 2) = _
    rw [hU, ← hback]
  rw [hL]
  exact hlaw

/-- The fibre metric law for `R = tcurveRight q₀` near `tcCoordH q`: the hyperbolic metric of the fibres changes by
`log|h|²`, with `h` (the fibre derivative of `R̃`) holomorphic and nonvanishing. -/
theorem s5l54_metric_law {q₀ q : T1 × ExtPlane} (hq₀ : q₀ ∈ TCurve) (hq : q ∈ TCurve) :
    ∃ h : AInf unitDisc × ℂ → ℂ, AnalyticAt ℂ h (tcCoordH q) ∧ h (tcCoordH q) ≠ 0 ∧
      ∀ᶠ w in 𝓝 (tcCoordH q), logNormSq (tcCoordHInv w) =
        logNormSq (tcCoordHInv (tcCoordExpr (tcurveRight q₀) w)) + Real.log (‖h w‖ ^ 2) := by
  have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  have hΦa : AnalyticAt ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) := by
    obtain ⟨U, hUsub, hUo, hxU⟩ := _root_.mem_nhds_iff.mp (s5l54_image_nhds hq)
    have hd : DifferentiableOn ℂ (tcCoordExpr (tcurveRight q₀)) U := fun w hw => by
      obtain ⟨q', hq', rfl⟩ := hUsub hw
      exact (s5rh_right_holo hq₀ hq').differentiableWithinAt
    exact bha_analyticOnNhd hUo hd _ hxU
  refine ⟨fun w => (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) w ((0 : AInf unitDisc), (1 : ℂ))).2, ?_,
    (s5l54_law_at hq₀ hq).1, ?_⟩
  · have h := ((ContinuousLinearMap.snd ℂ (AInf unitDisc) ℂ).analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ (AInf unitDisc × ℂ) ((0 : AInf unitDisc), (1 : ℂ))).analyticAt _).comp
        hΦa.fderiv)
    exact h
  · filter_upwards [s5l54_image_nhds hq] with w hw
    obtain ⟨q', hq', rfl⟩ := hw
    have hRq : tcurveRight q₀ q' ∈ TCurve := tcg_mul_mem_curve hq' (tcg_mul_mem_curve s5rh_tOrigin_mem hq₀)
    have hi : tcCoordHInv (tcCoordH q') = q' := s5rh_injOn.leftInvOn_invFunOn hq'
    have hi' : tcCoordHInv (tcCoordExpr (tcurveRight q₀) (tcCoordH q')) = tcurveRight q₀ q' := by
      show tcCoordHInv (tcCoordH (tcurveRight q₀ (tcCoordHInv (tcCoordH q')))) = _
      rw [hi]
      exact s5rh_injOn.leftInvOn_invFunOn hRq
    rw [hi, hi']
    exact (s5l54_law_at hq₀ hq').2

/-- A one-variable analytic map is `C²` (no completeness needed: analytic on a neighbourhood). -/
theorem s5l54_analytic_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {γ : ℂ → E} {t : ℂ}
    (h : AnalyticAt ℂ γ t) : ContDiffAt ℂ 2 γ t := by
  exact h.contDiffAt

/-- A `ℂ`-linear map on `ℂ` is `v ↦ v • L 1`. -/
theorem s5l54_clm_apply_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (L : ℂ →L[ℂ] F) (v : ℂ) :
    L v = v • L 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

/-- Second derivative of `g ∘ γ` along `v`, for real `C²` `g` and holomorphic `γ`:
`D²(g∘γ)(0)(v,v) = D²g(γ0)(vγ'(0), vγ'(0)) + Dg(γ0)(v² γ''(0))`. -/
theorem s5l54_hess_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {g : E → ℝ} {γ : ℂ → E}
    (hg : ContDiffAt ℝ 2 g (γ 0)) (hγ : AnalyticAt ℂ γ 0) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (fun t => g (γ t))) 0 v v =
      fderiv ℝ (fderiv ℝ g) (γ 0) (v • deriv γ 0) (v • deriv γ 0) +
        fderiv ℝ g (γ 0) ((v * v) • deriv (deriv γ) 0) := by
  have hγ2 : ContDiffAt ℂ 2 γ 0 := s5l54_analytic_contDiffAt hγ
  have hγR : ContDiffAt ℝ 2 γ 0 := hγ2.restrict_scalars ℝ
  have hu : ContDiffAt ℝ 2 (fun t => g (γ t)) 0 := hg.comp 0 hγR
  have hd1 : ContDiffAt ℂ 1 (fderiv ℂ γ) 0 := hγ2.fderiv_right (m := 1) (by norm_num)
  have hdd : DifferentiableAt ℂ (deriv γ) 0 := by
    have h : DifferentiableAt ℂ (fun t => fderiv ℂ γ t 1) 0 :=
      (hd1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    exact h
  have hγev : ∀ᶠ t in 𝓝 0, DifferentiableAt ℂ γ t :=
    hγ.eventually_analyticAt.mono fun t ht => ht.differentiableAt
  have hgev : ∀ᶠ y in 𝓝 (γ 0), DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hgev' : ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ g (γ t) := hγR.continuousAt.tendsto.eventually hgev
  have hfu : (fun t => fderiv ℝ (fun t => g (γ t)) t v) =ᶠ[𝓝 0]
      fun t => fderiv ℝ g (γ t) (v • deriv γ t) := by
    filter_upwards [hγev, hgev'] with t ht hgt
    have h := (hgt.hasFDerivAt.comp t (ht.hasFDerivAt.restrictScalars ℝ)).fderiv
    rw [show (fun t => g (γ t)) = g ∘ γ from rfl, h]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [s5l54_clm_apply_eq (fderiv ℂ γ t) v]
    rfl
  have hu1 : DifferentiableAt ℝ (fderiv ℝ (fun t => g (γ t))) 0 :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have e1 : fderiv ℝ (fderiv ℝ (fun t => g (γ t))) 0 v v =
      fderiv ℝ (fun t => fderiv ℝ (fun t => g (γ t)) t v) 0 v := by
    rw [fderiv_clm_apply hu1 (differentiableAt_const v)]
    simp
  rw [e1, hfu.fderiv_eq]
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) (γ 0) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA := hg1.hasFDerivAt.comp (0 : ℂ) (hγ.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have hB : HasFDerivAt (fun t => v • deriv γ t) (v • ((fderiv ℂ (deriv γ) 0).restrictScalars ℝ)) 0 :=
    (hdd.hasFDerivAt.restrictScalars ℝ).const_smul v
  have hAB := hA.clm_apply hB
  rw [show (fun t => fderiv ℝ g (γ t) (v • deriv γ t)) = fun t => ((fderiv ℝ g ∘ γ) t) (v • deriv γ t) from rfl,
    hAB.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    smul_apply, ContinuousLinearMap.coe_restrictScalars', Function.comp_apply]
  rw [s5l54_clm_apply_eq (fderiv ℂ (deriv γ) 0) v, s5l54_clm_apply_eq (fderiv ℂ γ 0) v, smul_smul, add_comm]
  rfl

/-- The Levi form of `g ∘ γ` for holomorphic `γ` depends only on `γ(0)` and `γ'(0)`. -/
theorem s5l54_levi_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {g : E → ℝ} {γ : ℂ → E}
    (hg : ContDiffAt ℝ 2 g (γ 0)) (hγ : AnalyticAt ℂ γ 0) :
    ContDiffAt ℝ 2 (fun t : ℂ => ((g (γ t) : ℝ) : ℂ)) 0 ∧
      dz (dzbar fun t : ℂ => ((g (γ t) : ℝ) : ℂ)) 0 =
        ((fderiv ℝ (fderiv ℝ g) (γ 0) (deriv γ 0) (deriv γ 0) +
          fderiv ℝ (fderiv ℝ g) (γ 0) (I • deriv γ 0) (I • deriv γ 0) : ℝ) : ℂ) / 4 := by
  have hu : ContDiffAt ℝ 2 (fun t => g (γ t)) 0 :=
    hg.comp 0 ((s5l54_analytic_contDiffAt hγ).restrict_scalars ℝ)
  have hc : ContDiffAt ℝ 2 (fun t : ℂ => ((g (γ t) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hu
  refine ⟨hc, ?_⟩
  rw [s5vc_mixed_laplacian hc]
  have hL : Laplacian.laplacian (fun t : ℂ => ((g (γ t) : ℝ) : ℂ)) 0 =
      ((Laplacian.laplacian (fun t => g (γ t)) 0 : ℝ) : ℂ) :=
    hu.laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  rw [hL, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [s5l54_hess_curve hg hγ 1, s5l54_hess_curve hg hγ I]
  simp only [one_smul, mul_one, I_mul_I, neg_smul, map_neg]
  push_cast
  ring

/-- Levi chain rule: for real `C²` `g` and holomorphic `Φ`, `∂_t∂_t̄ g(Φ(x + tY))|₀ = ∂_t∂_t̄ g(Φx + t dΦ(x)Y)|₀`. -/
theorem s5l54_levi_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {g : E → ℝ} {Φ : E → E} {x : E}
    (hg : ContDiffAt ℝ 2 g (Φ x)) (hΦ : AnalyticAt ℂ Φ x) (Y : E) :
    ContDiffAt ℝ 2 (fun t : ℂ => ((g (Φ (x + t • Y)) : ℝ) : ℂ)) 0 ∧
      dz (dzbar fun t : ℂ => ((g (Φ (x + t • Y)) : ℝ) : ℂ)) 0 =
        dz (dzbar fun t : ℂ => ((g (Φ x + t • fderiv ℂ Φ x Y) : ℝ) : ℂ)) 0 := by
  set V := fderiv ℂ Φ x Y with hV
  have hlin : AnalyticAt ℂ (fun t : ℂ => x + t • Y) 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hγ : AnalyticAt ℂ (fun t : ℂ => Φ (x + t • Y)) 0 := hΦ.comp_of_eq hlin (by simp)
  have hℓ : AnalyticAt ℂ (fun t : ℂ => Φ x + t • V) 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hgγ : ContDiffAt ℝ 2 g ((fun t : ℂ => Φ (x + t • Y)) 0) := by simpa using hg
  have hgℓ : ContDiffAt ℝ 2 g ((fun t : ℂ => Φ x + t • V) 0) := by simpa using hg
  obtain ⟨hc1, e1⟩ := s5l54_levi_curve hgγ hγ
  obtain ⟨-, e2⟩ := s5l54_levi_curve hgℓ hℓ
  have hdγ : deriv (fun t : ℂ => Φ (x + t • Y)) 0 = V := by
    have hl : HasDerivAt (fun t : ℂ => x + t • Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const Y).const_add x
    have h := hΦ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    exact h.deriv
  have hdℓ : deriv (fun t : ℂ => Φ x + t • V) 0 = V := by
    have h : HasDerivAt (fun t : ℂ => Φ x + t • V) V 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const V).const_add (Φ x)
    exact h.deriv
  refine ⟨hc1, ?_⟩
  rw [e1, e2, hdγ, hdℓ]
  simp only [zero_smul, add_zero]

/-- `∂_t∂_t̄ log|h(x + tY)|²|₀ = 0` for holomorphic nonvanishing `h`. -/
theorem s5l54_levi_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → ℂ} {x : E}
    (hh : AnalyticAt ℂ h x) (h0 : h x ≠ 0) (Y : E) :
    ContDiffAt ℝ 2 (fun t : ℂ => ((Real.log (‖h (x + t • Y)‖ ^ 2) : ℝ) : ℂ)) 0 ∧
      dz (dzbar fun t : ℂ => ((Real.log (‖h (x + t • Y)‖ ^ 2) : ℝ) : ℂ)) 0 = 0 := by
  have ha : AnalyticAt ℂ (fun t : ℂ => x + t • Y) 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hf : AnalyticAt ℂ (fun t : ℂ => h (x + t • Y)) 0 := hh.comp_of_eq ha (by simp)
  have hf0 : h (x + (0 : ℂ) • Y) ≠ 0 := by simpa using h0
  have hfc : ContDiffAt ℝ 2 (fun t : ℂ => h (x + t • Y)) 0 := hf.contDiffAt.restrict_scalars ℝ
  have hn : ContDiffAt ℝ 2 (fun t : ℂ => ‖h (x + t • Y)‖) 0 := hfc.norm ℂ hf0
  have hl : ContDiffAt ℝ 2 (fun t : ℂ => Real.log ‖h (x + t • Y)‖) 0 := hn.log (norm_ne_zero_iff.mpr hf0)
  have hL : ContDiffAt ℝ 2 (fun t : ℂ => ((Real.log ‖h (x + t • Y)‖ : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hl
  have he : (fun t : ℂ => ((Real.log (‖h (x + t • Y)‖ ^ 2) : ℝ) : ℂ)) =
      fun t => 2 * ((Real.log ‖h (x + t • Y)‖ : ℝ) : ℂ) := by
    funext t
    rw [Real.log_pow]
    push_cast
    ring
  rw [he]
  refine ⟨contDiffAt_const.mul hL, ?_⟩
  rw [s5vc_mixed_const_mul hL, s5vc_mixed_log_norm hf hf0, mul_zero]

/-- **Lemma 5.4** (TT:2310–2326). The `(1,1)`-form `c₁(V)` is right-invariant:
`Θ_{R_{q₀}(q)}(D R_{q₀} X, \overline{D R_{q₀} X}) = Θ_q(X, X̄)`, with `D R_{q₀}` the differential in coordinates. -/
theorem s5l54_lemma_5_4 {q₀ q : T1 × ExtPlane} (hq₀ : q₀ ∈ TCurve) (hq : q ∈ TCurve) (X : AInf unitDisc × ℂ) :
    thetaForm (tcurveRight q₀ q) (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) X)
        (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) X) = thetaForm q X X := by
  set x := tcCoordH q with hxdef
  set D := fderiv ℂ (tcCoordExpr (tcurveRight q₀)) x with hDdef
  have hb : tcurveMulInv tOrigin q₀ ∈ TCurve := tcg_mul_mem_curve s5rh_tOrigin_mem hq₀
  have hRq : tcurveRight q₀ q ∈ TCurve := tcg_mul_mem_curve hq hb
  have hqx : tcCoordHInv x = q := s5rh_injOn.leftInvOn_invFunOn hq
  have hΦx : tcCoordExpr (tcurveRight q₀) x = tcCoordH (tcurveRight q₀ q) := by
    show tcCoordH (tcurveRight q₀ (tcCoordHInv x)) = _
    rw [hqx]
  -- `R̃` is analytic at `x`
  have hΦa : AnalyticAt ℂ (tcCoordExpr (tcurveRight q₀)) x := by
    have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
    obtain ⟨U, hUsub, hUo, hxU⟩ := _root_.mem_nhds_iff.mp (s5l54_image_nhds hq)
    have hd : DifferentiableOn ℂ (tcCoordExpr (tcurveRight q₀)) U := fun w hw => by
      obtain ⟨q', hq', rfl⟩ := hUsub hw
      exact (s5rh_right_holo hq₀ hq').differentiableWithinAt
    exact bha_analyticOnNhd hUo hd x hxU
  have hg : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
      (tcCoordExpr (tcurveRight q₀) x) := by
    rw [hΦx]
    exact s5l54_regular hRq
  obtain ⟨h, hha, hh0, hlaw⟩ := s5l54_metric_law hq₀ hq
  -- the Levi form is transported by `D`
  have key : ∀ Y : AInf unitDisc × ℂ, leviTC logNormSq q Y = leviTC logNormSq (tcurveRight q₀ q) (D Y) := by
    intro Y
    have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
    obtain ⟨hc1, hch⟩ := s5l54_levi_chain hg hΦa Y
    obtain ⟨hc2, hlog⟩ := s5l54_levi_log hha hh0 Y
    have ht : Tendsto (fun t : ℂ => x + t • Y) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℂ => x + t • Y) := by fun_prop
      simpa using hc.tendsto 0
    have hev : (fun t : ℂ => ((logNormSq (tcCoordHInv (tcCoordH q + t • Y)) : ℝ) : ℂ)) =ᶠ[𝓝 0]
        fun t => ((logNormSq (tcCoordHInv (tcCoordExpr (tcurveRight q₀) (x + t • Y))) : ℝ) : ℂ) +
          ((Real.log (‖h (x + t • Y)‖ ^ 2) : ℝ) : ℂ) := by
      filter_upwards [ht.eventually hlaw] with t hlt
      rw [hlt]
      push_cast
      rfl
    unfold leviTC
    rw [s5vc_mixed_congr hev, s5vc_mixed_add hc1 hc2, hlog, add_zero, hch, hΦx]
  have e1 : D X + D X = D (X + X) := (map_add D X X).symm
  have e2 : D X - D X = D (X - X) := (map_sub D X X).symm
  have e3 : D X + I • D X = D (X + I • X) := by rw [map_add, map_smul]
  have e4 : D X - I • D X = D (X - I • X) := by rw [map_sub, map_smul]
  unfold thetaForm polarize
  rw [e1, e2, e3, e4, ← key, ← key, ← key, ← key]

/-- **Lemma 5.4** (TT:2310–2326). The `(1,1)`-form `c₁(V)` is right-invariant:
`Θ_{R_{q₀}(q)}(D R_{q₀} X, \overline{D R_{q₀} X}) = Θ_q(X, X̄)`, with `D R_{q₀}` the differential in coordinates. -/
theorem lemma_5_4 {q₀ q : T1 × ExtPlane} (hq₀ : q₀ ∈ TCurve) (hq : q ∈ TCurve) (X : AInf unitDisc × ℂ) :
    thetaForm (tcurveRight q₀ q) (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) X)
        (fderiv ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) X) = thetaForm q X X := by
  exact s5l54_lemma_5_4 hq₀ hq X

end TakhtajanTeo
