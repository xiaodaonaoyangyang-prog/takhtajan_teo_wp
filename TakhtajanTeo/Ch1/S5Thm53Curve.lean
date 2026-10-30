import TakhtajanTeo.Ch1.S5Thm53
import TakhtajanTeo.Ch1.S5CoefficientVariation
import TakhtajanTeo.Appendix.B6Completed

/-!
# `thm_5_3` support: the welding curve pieces (`s5t53_`, 下属3, Program G)

Proved pieces of the (parked) A1 curve route for `thm_5_3`; the open walls are recorded in
`collaboration/下属3/WALL_T53.md`.

* C0 cut-off, C6 analytic section, C1 welding, C2 start, C5 potential (`K = log |G_t'(∞)|`).
* Joint `C²` of the curve maps `F` (`s5t53_F_joint`) and `G` (`s5t53_G_joint`, via
  `G = 1/(g^♯(r(ω, x)) + c)`).
* Interior area theorem `s5t53_area` (Green's identity `ab6_gap_green`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- Second derivative of a real `C²` function along a real line: `(d/dt)² g(t v)|₀ = D²g(0)(v, v)`. -/
theorem s5t53_hess_line {g : ℂ → ℝ} (hg : ContDiffAt ℝ 2 g 0) (v : ℂ) :
    deriv (deriv fun t : ℝ => g ((t : ℂ) * v)) 0 = fderiv ℝ (fderiv ℝ g) 0 v v := by
  have hev : ∀ᶠ y in 𝓝 (0 : ℂ), DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt two_ne_zero
  have hL : Continuous fun t : ℝ => (t : ℂ) * v := Complex.continuous_ofReal.mul continuous_const
  have hL0 : (fun t : ℝ => (t : ℂ) * v) 0 = 0 := by simp
  have hT : Tendsto (fun t : ℝ => (t : ℂ) * v) (𝓝 0) (𝓝 0) := by
    have h := hL.tendsto 0
    simpa using h
  have hev' : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ g ((t : ℂ) * v) := hT.eventually hev
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * v) v t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v
  have hd1 : (deriv fun t : ℝ => g ((t : ℂ) * v)) =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ => fderiv ℝ g ((t : ℂ) * v) v := by
    filter_upwards [hev'] with t ht
    exact (HasFDerivAt.comp_hasDerivAt (l := g) (f := fun t : ℝ => (t : ℂ) * v) t ht.hasFDerivAt (hline t)).deriv
  rw [hd1.deriv_eq]
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hg1' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) ((fun t : ℝ => (t : ℂ) * v) 0) := by
    rw [hL0]; exact hg1.hasFDerivAt
  have hc1 := HasFDerivAt.comp_hasDerivAt (l := fderiv ℝ g) (f := fun t : ℝ => (t : ℂ) * v) (0 : ℝ) hg1' (hline 0)
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ g ((t : ℂ) * v) v)
      ((fderiv ℝ (fderiv ℝ g) 0 v) v + (fderiv ℝ g ((fun t : ℝ => (t : ℂ) * v) 0)) 0) 0 :=
    hc1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [hc.deriv, map_zero, add_zero]

/-- The origin in `tcCoordH`. -/
theorem s5t53_tcCoordH_origin : tcCoordH tOrigin = ((0 : AInf unitDisc), (0 : ℂ)) := by
  have hq0 : tOrigin = ((originT, inversion ((0 : ℂ) : ExtPlane)) : T1 × ExtPlane) := by
    show (originT, extInf) = _
    rw [(tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl]
  have hc0 : deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 = 0 := by
    have he : fB ((Quotient.out originT : LinfStarBall) : LinfStar) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])] with z hz
      exact s5tg_origin_fB hz
    have hd : deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar)) =ᶠ[𝓝 (0 : ℂ)] fun _ => 1 := by
      filter_upwards [he.eventuallyEq_nhds] with z hz
      rw [hz.deriv_eq, deriv_id]
    rw [hd.deriv_eq, deriv_const]
  rw [hq0]
  show (bers (Phi ⟨0, mem_ball_self one_pos⟩), finPart (inversion (inversion ((0 : ℂ) : ExtPlane))) +
    deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 / 2) = _
  rw [c32_bers_origin, tcc_inversion_invol, hc0, zero_div, add_zero]
  rfl

/-- `g'(∞)` depends only on the germ of `g` at `∞`. -/
theorem s5t53_derivAtInfty_congr {g g' : ℂ → ℂ} (h : g =ᶠ[cocompact ℂ] g') : derivAtInfty g = derivAtInfty g' := by
  unfold derivAtInfty limUnder
  have heq : (fun z => g z / z) =ᶠ[cocompact ℂ] fun z => g' z / z := h.mono fun z hz => by show g z / z = g' z / z; rw [show g z = g' z from hz]
  rw [Filter.map_congr heq]

/-- Points near `∞` lie in `𝔻*`. -/
theorem s5t53_ev_exterior : ∀ᶠ z : ℂ in cocompact ℂ, z ∈ unitDiscExterior := by
  filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
  simpa [unitDiscExterior] using hz

/-- **The potential at the fibre point `∞`**: `K([μ], ∞) = log |g_μ'(∞)|`. -/
theorem s5t53_K_infty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    potentialK (Phi ⟨μ, hμ⟩, extInf) = Real.log ‖derivAtInfty (gMu μ)‖ := by
  set ν : LinfStarBall := Quotient.out (Phi ⟨μ, hμ⟩) with hνdef
  have hν := ν.2
  have hcls : teichSetoid ν ⟨μ, hμ⟩ := Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
  have hgc := s5cf_gMu_congr hcls
  have hgd : derivAtInfty (gMu (ν : LinfStar)) = derivAtInfty (gMu μ) := by
    apply s5t53_derivAtInfty_congr
    filter_upwards [s5t53_ev_exterior] with z hz
    exact hgc hz
  set g := gMu (ν : LinfStar) with hgdef
  set F := fiberUniformizer (ν : LinfStar) with hFdef
  obtain ⟨hFa, hF0, hFd⟩ := s5fg_uniformizer_analytic_zero hν
  have hu : IsUnivalentAtInfty g := (gMu_isWelding hν).2.2.2.2.2.2
  -- the local inverse `H(ζ) = 1/g(1/ζ)` of `F` at `0`
  set H : ℂ → ℂ := fun ζ => if ζ = 0 then 0 else (g ζ⁻¹)⁻¹ with hHdef
  have hH0 : H 0 = 0 := by simp [hHdef]
  have hHc : ContinuousAt H 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hH0]
    have h1 : Tendsto (fun ζ : ℂ => ζ⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    have h3 := h2.comp (hu.2.2.comp h1)
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have hζ0 : ζ ≠ 0 := hζ
    simp [hHdef, hζ0]
  have hFH : ∀ᶠ ζ in 𝓝 (0 : ℂ), F (H ζ) = ζ := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball (0 : ℂ) 1 by simp)] with ζ hζ
    by_cases h0 : ζ = 0
    · subst ζ
      rw [hH0]
      exact hF0
    · have hw : ζ⁻¹ ∈ unitDiscExterior := by
        change 1 < ‖ζ⁻¹‖
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp hζ⟩
      have hg0 : g ζ⁻¹ ≠ 0 := gMu_exterior_ne_zero hν hw
      have hHζ : H ζ = (g ζ⁻¹)⁻¹ := by simp [hHdef, h0]
      rw [hHζ]
      show (if (g ζ⁻¹)⁻¹ = 0 then 0 else (Function.invFunOn g unitDiscExterior ((g ζ⁻¹)⁻¹)⁻¹)⁻¹) = ζ
      simp only [inv_ne_zero hg0, ↓reduceIte]
      rw [inv_inv, hu.2.1.leftInvOn_invFunOn hw, inv_inv]
  have hFd' : HasDerivAt F (deriv F 0) (H 0) := by
    rw [hH0]
    exact hFa.differentiableAt.hasDerivAt
  have hHd := HasDerivAt.of_local_left_inverse hHc hFd' hFd hFH
  have hrec : ∀ᶠ z in cocompact ℂ, H z⁻¹ = (g z)⁻¹ := by
    filter_upwards [s5t53_ev_exterior] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hz
    simp [hHdef, hz0]
  have hdi := s5wr_derivAtInfty_of_reciprocal hHd hH0 (inv_ne_zero hFd) hrec
  rw [inv_inv] at hdi
  -- the potential
  have hz : finPart (inversion extInf) = 0 := by
    rw [← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl, tcc_inversion_invol]
    rfl
  show logNormSq (Phi ⟨μ, hμ⟩, extInf) / 2 - Real.log 2 = _
  show Real.log (4 * ‖deriv (fiberUniformizer (ν : LinfStar)) (finPart (inversion extInf))‖ ^ 2 /
    (1 - ‖fiberUniformizer (ν : LinfStar) (finPart (inversion extInf))‖ ^ 2) ^ 2) / 2 - Real.log 2 = _
  rw [hz, hF0, ← hgd, show derivAtInfty (gMu (ν : LinfStar)) = deriv F 0 from hdi, norm_zero]
  have hn : 0 < ‖deriv F 0‖ := norm_pos_iff.mpr hFd
  rw [show (4 : ℝ) * ‖deriv F 0‖ ^ 2 / (1 - 0 ^ 2) ^ 2 = 2 ^ 2 * ‖deriv F 0‖ ^ 2 by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- The pole term `P(μ) = 1/W_μ(p_μ)` is real-analytic on `L∞(𝔻*)₁` (as in `s5l54_c_analytic`). -/
theorem s5t53_P_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℝ (fun ν : LinfStar => s5cf_reciprocal (ν, star ν) (s5cf_alpha (ν, star ν) 0)) μ := by
  have hc : AnalyticAt ℝ (fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 (s5cf_alpha q.1 q.2))
      ((μ, star μ), (0 : ℂ)) :=
    (s5cf_normalized_transition_analytic hμ (t := 0) (by simp [unitDisc])).restrictScalars
  have hJ : AnalyticAt ℝ (fun ν : LinfStar => (ν, star ν)) μ := analyticAt_id.prod (s5cf_star_analytic μ)
  have hm : AnalyticAt ℝ (fun ν : LinfStar => ((ν, star ν), (0 : ℂ))) μ :=
    hJ.prod (analyticAt_const (v := (0 : ℂ)))
  exact AnalyticAt.comp_of_eq
    (g := fun q : (LinfStar × LinfStar) × ℂ => s5cf_reciprocal q.1 (s5cf_alpha q.1 q.2))
    (f := fun ν : LinfStar => ((ν, star ν), (0 : ℂ))) hc hm rfl

/-- On `𝔻`, `f^μ = (W_μ/d_μ)/(1 - P_μ W_μ)` with `W_μ` the plane-B normalized solution, `d_μ = W_μ'(0)`, and the pole
term `P_μ` (`acc_wB_rep`); the denominator does not vanish. -/
theorem s5t53_fB_formula {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    -s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) z + 1 ≠ 0 ∧
      fB μ z = (1 / deriv (normalizedSolution (extB μ)) 0 * normalizedSolution (extB μ) z + 0) /
        (-s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) z + 1) := by
  obtain ⟨hd, -, hrep⟩ := AppA.acc_wB_rep hμ
  have hP : finPart (mobiusExt 0 1 1 0 (OnePoint.map (normalizedSolution (extB μ))
      (Function.invFun (wAS μ) extInf))) = s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) := by
    have h := s5cf_planeB_inverse_wAS_reciprocal hμ (t := 0) (by simp [unitDisc])
    rw [mobiusExt_coe_of_eq_zero (by norm_num)] at h
    rw [h]
    rfl
  have h1 := hrep (z : ExtPlane)
  rw [hP, Ch2.e13_wB_disc hμ hz] at h1
  change ((fB μ z : ℂ) : ExtPlane) = mobiusExt _ 0 _ 1 ((normalizedSolution (extB μ) z : ℂ) : ExtPlane) at h1
  have hden : -s5cf_reciprocal (μ, star μ) (s5cf_alpha (μ, star μ) 0) * normalizedSolution (extB μ) z + 1 ≠ 0 := by
    intro h0
    rw [mobiusExt_coe_of_eq_zero h0] at h1
    exact OnePoint.coe_ne_infty _ h1
  refine ⟨hden, ?_⟩
  rw [mobiusExt_coe hden] at h1
  exact OnePoint.coe_injective h1

/-- **Joint real-analyticity of `(μ, z) ↦ f^μ(z)`** on `L∞(𝔻*)₁ × 𝔻`. -/
theorem s5t53_fB_joint {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDisc) :
    AnalyticAt ℝ (fun q : LinfStar × ℂ => fB q.1 q.2) (μ, z) := by
  have hW : AnalyticAt ℝ (fun q : LinfStar × ℂ => normalizedSolution (extB q.1) q.2) (μ, z) :=
    (s5cf_planeB_disk_analytic (μ, z) ⟨hμ, hz⟩).restrictScalars
  have hd : AnalyticAt ℝ (fun q : LinfStar × ℂ => deriv (normalizedSolution (extB q.1)) 0) (μ, z) :=
    AnalyticAt.comp_of_eq (g := fun ν : LinfStar => deriv (normalizedSolution (extB ν)) 0)
      (f := fun q : LinfStar × ℂ => q.1) (s5cf_planeB_deriv_analytic hμ).restrictScalars analyticAt_fst rfl
  have hP : AnalyticAt ℝ (fun q : LinfStar × ℂ => s5cf_reciprocal (q.1, star q.1) (s5cf_alpha (q.1, star q.1) 0))
      (μ, z) :=
    AnalyticAt.comp_of_eq (g := fun ν : LinfStar => s5cf_reciprocal (ν, star ν) (s5cf_alpha (ν, star ν) 0))
      (f := fun q : LinfStar × ℂ => q.1) (s5t53_P_analytic hμ) analyticAt_fst rfl
  have hd0 := s5cf_planeB_deriv_ne_zero hμ
  obtain ⟨hden, -⟩ := s5t53_fB_formula hμ hz
  have hnum : AnalyticAt ℝ (fun q : LinfStar × ℂ =>
      1 / deriv (normalizedSolution (extB q.1)) 0 * normalizedSolution (extB q.1) q.2 + 0) (μ, z) :=
    ((analyticAt_const.div hd hd0).mul hW).add analyticAt_const
  have hdn : AnalyticAt ℝ (fun q : LinfStar × ℂ =>
      -s5cf_reciprocal (q.1, star q.1) (s5cf_alpha (q.1, star q.1) 0) * normalizedSolution (extB q.1) q.2 + 1)
      (μ, z) := (hP.neg.mul hW).add analyticAt_const
  refine (hnum.div hdn hden).congr ?_
  have hU : LinfStarBall ×ˢ unitDisc ∈ 𝓝 (μ, z) := (isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμ, hz⟩
  filter_upwards [hU] with q hq
  exact ((s5t53_fB_formula hq.1 hq.2).2).symm

/-- The base curve `t ↦ μ_t = sec(ψ(t) φ)` is `C²` into `L∞`, with values in the ball. -/
theorem s5t53_mu_curve {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ}
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε)) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) (t : ℝ) :
    ContDiffAt ℝ 2 (fun t : ℝ => sec ((ψ t : ℂ) • Y.1)) t := by
  have hin : ((ψ t : ℂ) • Y.1) ∈ ball (0 : AInf unitDisc) ε := by
    rw [mem_ball, dist_zero_right]
    calc ‖(ψ t : ℂ) • Y.1‖ = ‖(((ψ t : ℝ) : ℂ) • Y).1‖ := rfl
      _ ≤ ‖((ψ t : ℝ) : ℂ) • Y‖ := norm_fst_le _
      _ < ε := hψb t
  have hs : ContDiffAt ℝ 2 sec ((ψ t : ℂ) • Y.1) := ((hsa _ hin).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hl : ContDiff ℝ 2 (fun t : ℝ => (ψ t : ℂ) • Y.1) :=
    (Complex.ofRealCLM.contDiff.comp hψ).smul contDiff_const
  exact ContDiffAt.comp (g := sec) (f := fun t : ℝ => (ψ t : ℂ) • Y.1) t hs hl.contDiffAt

/-- The fibre point and the `λ`-denominator: `c_t f^{μ_t}(x) + 1 ≠ 0` on `𝔻` (the pole `-1/c_t` of `λ_{c_t}` is the
fibre point, which lies in the exterior image `w^{μ_t}(𝔻*)`). -/
theorem s5t53_den {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ}
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) (t : ℝ) {x : ℂ} (hx : x ∈ unitDisc) :
    sec ((ψ t : ℂ) • Y.1) ∈ LinfStarBall ∧
      (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) *
        fB (sec ((ψ t : ℂ) • Y.1)) x + 1 ≠ 0 := by
  obtain ⟨hμ, hq, hqm⟩ := hsec (((ψ t : ℝ) : ℂ) • Y) (hψb t)
  set μ := sec ((ψ t : ℂ) • Y.1) with hμdef
  set s := (ψ t : ℂ) * Y.2 with hsdef
  set cμ := deriv (deriv (fB μ)) 0 / 2 with hcμ
  set z : ExtPlane := inversion ((s - cμ : ℂ) : ExtPlane) with hzdef
  replace hμ : μ ∈ LinfStarBall := hμ
  refine ⟨hμ, ?_⟩
  have hq' : tcCoordHInv (((ψ t : ℝ) : ℂ) • Y) = (Phi ⟨μ, hμ⟩, z) := hq
  have hz : z ∈ wB μ '' extDiscExterior := by
    have hm := hqm
    rw [hq'] at hm
    have hcls : teichSetoid (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) ⟨μ, hμ⟩ :=
      Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
    change z ∈ wB (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) '' extDiscExterior at hm
    rwa [fiber_independent hcls] at hm
  intro h0
  have hc0 : cμ - s ≠ 0 := by
    intro hc
    rw [hc, zero_mul, zero_add] at h0
    exact one_ne_zero h0
  have hsc : s - cμ ≠ 0 := by
    intro h
    apply hc0
    linear_combination -h
  have hfx : fB μ x = (s - cμ)⁻¹ := by
    have h1 : fB μ x * (s - cμ) = 1 := by linear_combination -h0
    exact eq_inv_of_mul_eq_one_left h1
  have hwx : wB μ (x : ExtPlane) = z := by
    rw [Ch2.e13_wB_disc hμ hx, hfx, hzdef, s5rh_inversion_coe hsc]
  obtain ⟨y, hy, hyz⟩ := hz
  have hxy : (x : ExtPlane) = y := (wB_bijective μ).1 (hwx.trans hyz.symm)
  rw [← hxy, fi_extDiscExterior_eq_compl] at hy
  exact hy ⟨x, ball_subset_closedBall hx, rfl⟩

/-- **(C3a) joint `C²` of `F`** on `ℝ × 𝔻`. -/
theorem s5t53_F_joint {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ}
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℂ => lambdaW (deriv (deriv (fB (sec ((ψ p.1 : ℂ) • Y.1)))) 0 / 2 -
      (ψ p.1 : ℂ) * Y.2) (fB (sec ((ψ p.1 : ℂ) • Y.1)) p.2)) (univ ×ˢ unitDisc) := by
  intro p hp
  have hx : p.2 ∈ unitDisc := hp.2
  obtain ⟨hμ, hden⟩ := s5t53_den hsec hψb p.1 hx
  have hμc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => sec ((ψ q.1 : ℂ) • Y.1)) p :=
    ContDiffAt.comp (g := fun t : ℝ => sec ((ψ t : ℂ) • Y.1)) (f := fun q : ℝ × ℂ => q.1) p
      (s5t53_mu_curve hsa hψ hψb p.1) contDiffAt_fst
  have hm : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => (sec ((ψ q.1 : ℂ) • Y.1), q.2)) p := hμc.prodMk contDiffAt_snd
  have hfB : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => fB (sec ((ψ q.1 : ℂ) • Y.1)) q.2) p :=
    ContDiffAt.comp (g := fun q : LinfStar × ℂ => fB q.1 q.2)
      (f := fun q : ℝ × ℂ => (sec ((ψ q.1 : ℂ) • Y.1), q.2)) p (s5t53_fB_joint hμ hx).contDiffAt hm
  have hcc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2) p :=
    ContDiffAt.comp (g := fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2)
      (f := fun q : ℝ × ℂ => sec ((ψ q.1 : ℂ) • Y.1)) p (s5l54_c_analytic hμ).contDiffAt hμc
  have hψc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => (ψ q.1 : ℂ) * Y.2) p :=
    ((Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst)).mul contDiff_const).contDiffAt
  have hc := hcc.sub hψc
  refine (ContDiffAt.contDiffWithinAt ?_)
  have hD : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => (deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 -
      (ψ q.1 : ℂ) * Y.2) * fB (sec ((ψ q.1 : ℂ) • Y.1)) q.2 + 1) p := (hc.mul hfB).add contDiffAt_const
  unfold lambdaW
  simp only [div_eq_mul_inv]
  exact hfB.mul (hD.inv hden)

/-- `z ↦ z/(c z + 1)` after `z ↦ 1/z`: `g ↦ 1/(g + c)`, including the point `g = 0`. -/
theorem s5t53_mob_recip {g c : ℂ} (h : g + c ≠ 0) :
    mobiusExt 1 0 c 1 (mobiusExt 0 1 1 0 (g : ExtPlane)) = (((g + c)⁻¹ : ℂ) : ExtPlane) := by
  by_cases hg : g = 0
  · subst hg
    have hc : c ≠ 0 := by simpa using h
    rw [mobiusExt_coe_of_eq_zero (by simp), mobiusExt_infty_of_ne hc]
    congr 1
    simp
  · rw [mobiusExt_coe (by simpa using hg)]
    have hd : c * mobiusFn 0 1 1 0 g + 1 = (g + c) / g := by
      simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
      field_simp
      ring
    rw [mobiusExt_coe (by rw [hd]; exact div_ne_zero h hg)]
    congr 1
    rw [show mobiusFn 1 0 c 1 (mobiusFn 0 1 1 0 g) = mobiusFn 0 1 1 0 g / (c * mobiusFn 0 1 1 0 g + 1) by
      simp only [mobiusFn, one_mul, add_zero], hd]
    simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
    field_simp

/-- The denominator `(ω - 1) ω̄ + x (ω̄ - 1)` of the reciprocal fibre chart does not vanish for `ω ∈ 𝔻`, `x ∈ 𝔻*`. -/
theorem s5t53_rden {ω x : ℂ} (hω : ω ∈ unitDisc) (hx : x ∈ unitDiscExterior) :
    (ω - 1) * conj ω + x * (conj ω - 1) ≠ 0 := by
  have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have hx1 : 1 < ‖x‖ := hx
  intro h0
  have h1 : x * (conj ω - 1) = -((ω - 1) * conj ω) := by linear_combination h0
  have h2 := congrArg norm h1
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj] at h2
  have h3 : ‖conj ω - 1‖ = ‖ω - 1‖ := by
    rw [← Complex.norm_conj (ω - 1), map_sub, map_one]
  rw [h3] at h2
  have h4 : 0 < ‖ω - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    rintro rfl
    norm_num at hω1
  have h5 : ‖x‖ = ‖ω‖ := by
    have := h2
    nlinarith [mul_comm ‖x‖ ‖ω - 1‖]
  linarith

/-- **`σ_w⁻¹` in the reciprocal chart.** With `ω = 1/w` (`ω = 0` for `w = ∞`), `1/σ_w⁻¹(x)` is the explicit Möbius
expression `(x ω (ω̄ - 1) + ω - 1)/((ω - 1) ω̄ + x (ω̄ - 1))`. -/
theorem s5t53_sigma_recip {w : ExtPlane} {ω x : ℂ} (hω : ω ∈ unitDisc) (hx : x ∈ unitDiscExterior)
    (hw : (w = extInf ∧ ω = 0) ∨ (ω ≠ 0 ∧ w = ((ω⁻¹ : ℂ) : ExtPlane))) :
    mobiusExt 0 1 1 0 (sigmaInvSphere w (x : ExtPlane)) =
      (((x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1)) : ℂ) : ExtPlane) := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hx
  have hx1 : 1 < ‖x‖ := hx
  have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
  have hD := s5t53_rden hω hx
  rcases hw with ⟨rfl, rfl⟩ | ⟨hω0, rfl⟩
  · show mobiusExt 0 1 1 0 (x : ExtPlane) = _
    rw [mobiusExt_coe (by simpa using hx0)]
    congr 1
    simp only [mobiusFn, map_zero]
    field_simp
    ring
  · have hc0 : conj ω ≠ 0 := by simpa using hω0
    show mobiusExt 0 1 1 0 (mobiusExt _ _ _ _ (x : ExtPlane)) = _
    have hcv : conj ω⁻¹ = (conj ω)⁻¹ := map_inv₀ _ _
    by_cases hd : -(1 - conj ω⁻¹) * x + -(1 - ω⁻¹) * conj ω⁻¹ = 0
    · rw [mobiusExt_coe_of_eq_zero hd, mobiusExt_infty_of_ne one_ne_zero]
      congr 1
      have hN : x * ω * (conj ω - 1) + ω - 1 =
          -(ω * conj ω) * (-(1 - conj ω⁻¹) * x + -(1 - ω⁻¹) * conj ω⁻¹) := by
        rw [hcv]
        field_simp
        ring
      rw [hN, hd]
      simp
    · rw [mobiusExt_coe hd]
      have hn : -ω⁻¹ * (1 - conj ω⁻¹) * x + -(1 - ω⁻¹) ≠ 0 := by
        intro h0
        have h1 : ω⁻¹ * (1 - conj ω⁻¹) * x = -(1 - ω⁻¹) := by linear_combination -h0
        have h2 := congrArg norm h1
        rw [norm_neg, norm_mul, norm_mul, hcv] at h2
        have h3 : ‖1 - (conj ω)⁻¹‖ = ‖1 - ω⁻¹‖ := by
          rw [← map_inv₀, ← Complex.norm_conj (1 - ω⁻¹), map_sub, map_one]
        rw [h3, norm_inv] at h2
        have h4 : 0 < ‖1 - ω⁻¹‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          intro h
          have : ‖ω⁻¹‖ = 1 := by rw [← h, norm_one]
          rw [norm_inv] at this
          have hp : 0 < ‖ω‖ := norm_pos_iff.mpr hω0
          have : ‖ω‖ = 1 := by
            have := inv_eq_one.mp this
            exact this
          linarith
        have hp : 0 < ‖ω‖ := norm_pos_iff.mpr hω0
        have h5 : ‖x‖ = ‖ω‖ := by
          field_simp at h2
          have h6 : ‖(ω - 1) / ω‖ ≠ 0 := by
            rw [norm_ne_zero_iff]
            refine div_ne_zero ?_ hω0
            rw [sub_ne_zero]
            rintro rfl
            norm_num at hω1
          exact mul_left_cancel₀ h6 (h2.trans (mul_comm _ _))
        linarith
      have hv : 1 * mobiusFn (-ω⁻¹ * (1 - conj ω⁻¹)) (-(1 - ω⁻¹)) (-(1 - conj ω⁻¹)) (-(1 - ω⁻¹) * conj ω⁻¹) x +
          0 ≠ 0 := by
        simp only [mobiusFn, one_mul, add_zero]
        exact div_ne_zero hn hd
      rw [mobiusExt_coe hv]
      congr 1
      simp only [mobiusFn, zero_mul, zero_add, one_mul, add_zero]
      rw [one_div, inv_div, div_eq_div_iff hn hD]
      rw [hcv]
      field_simp
      ring

/-- The fibre point of the curve: `μ_t ∈ L∞(𝔻*)₁` and `1/(s_t - c(μ_t))` lies in the exterior image `w^{μ_t}(𝔻*)`. -/
theorem s5t53_fibre_mem {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ}
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) (t : ℝ) :
    sec ((ψ t : ℂ) • Y.1) ∈ LinfStarBall ∧
      inversion (((ψ t : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 : ℂ) : ExtPlane) ∈
        wB (sec ((ψ t : ℂ) • Y.1)) '' extDiscExterior := by
  obtain ⟨hμ, hq, hqm⟩ := hsec (((ψ t : ℝ) : ℂ) • Y) (hψb t)
  set μ := sec ((ψ t : ℂ) • Y.1) with hμdef
  set z : ExtPlane := inversion (((ψ t : ℂ) * Y.2 - deriv (deriv (fB μ)) 0 / 2 : ℂ) : ExtPlane) with hzdef
  replace hμ : μ ∈ LinfStarBall := hμ
  refine ⟨hμ, ?_⟩
  have hq' : tcCoordHInv (((ψ t : ℝ) : ℂ) • Y) = (Phi ⟨μ, hμ⟩, z) := hq
  have hm := hqm
  rw [hq'] at hm
  have hcls : teichSetoid (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) ⟨μ, hμ⟩ :=
    Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
  change z ∈ wB (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) '' extDiscExterior at hm
  rwa [fiber_independent hcls] at hm

/-- **The welding parameter in the uniformizer chart.** For `1/ζ ∈ w^μ(𝔻*)`, `ζ` is `0` or `1/g_μ(w)`, and the
parameter `w = (𝗇^μ)⁻¹(1/ζ)` is `1/ω` with `ω = F_μ(ζ)` (`ω = 0 ↔ w = ∞`). -/
theorem s5t53_G_param {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {ζ : ℂ}
    (hz : inversion (ζ : ExtPlane) ∈ wB μ '' extDiscExterior) :
    (ζ = 0 ∨ ∃ w ∈ unitDiscExterior, ζ = (gMu μ w)⁻¹) ∧
      ((Function.invFun (normalizedWeldingSphere μ) (inversion (ζ : ExtPlane)) = extInf ∧
          fiberUniformizer μ ζ = 0) ∨
        (fiberUniformizer μ ζ ≠ 0 ∧ Function.invFun (normalizedWeldingSphere μ) (inversion (ζ : ExtPlane)) =
          (((fiberUniformizer μ ζ)⁻¹ : ℂ) : ExtPlane))) := by
  have hz' : inversion (ζ : ExtPlane) ∈ normalizedWeldingSphere μ '' extDiscExterior := by
    rw [tcg_welding_image hμ]; exact hz
  set w := Function.invFun (normalizedWeldingSphere μ) (inversion (ζ : ExtPlane)) with hwdef
  have hwz : normalizedWeldingSphere μ w = inversion (ζ : ExtPlane) := by
    obtain ⟨a, -, ha⟩ := hz'
    exact Function.invFun_eq ⟨a, ha⟩
  have hw : w ∈ extDiscExterior := tcg_parameter_mem hμ hz
  rcases hw with ⟨w', hw', hww⟩ | hwi
  · have hg := gMu_exterior_ne_zero hμ hw'
    have hgz : ((gMu μ w' : ℂ) : ExtPlane) = inversion (ζ : ExtPlane) := by
      rw [← hwz, ← hww, ← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw']
    have h1 : inversion ((gMu μ w' : ℂ) : ExtPlane) = (ζ : ExtPlane) := by
      rw [hgz, tcc_inversion_invol]
    rw [s5rh_inversion_coe hg] at h1
    have h2 : ζ = (gMu μ w')⁻¹ := (OnePoint.coe_injective h1).symm
    have hw0 : w' ≠ 0 := by intro h; norm_num [h, unitDiscExterior] at hw'
    have hF : fiberUniformizer μ ζ = w'⁻¹ := by rw [h2]; exact (s5wr_uniformizer_jet hμ hw').1
    refine ⟨Or.inr ⟨w', hw', h2⟩, Or.inr ⟨by rw [hF]; exact inv_ne_zero hw0, ?_⟩⟩
    rw [hF, inv_inv]
    exact hww.symm
  · have hwi' : w = extInf := hwi
    have hzi : inversion (ζ : ExtPlane) = extInf := by rw [← hwz, hwi', normalizedWeldingSphere_infty hμ]
    have hζ : ζ = 0 := OnePoint.coe_injective ((tcc_inversion_eq_inf_iff _).mp hzi)
    refine ⟨Or.inl hζ, Or.inl ⟨hwi', ?_⟩⟩
    rw [hζ]
    simp [fiberUniformizer]

/-- **The exterior map in the reciprocal chart.** With `ω ∈ 𝔻`, `g_μ^♯(ω) = -c` (`g^♯ = s5cf_gchart`, `g^♯(t) =
1/g_μ(1/t)`) and `w = 1/ω`, the exterior map of the curve is `x ↦ 1/(g^♯(r(ω, x)) + c)` on `𝔻*`, with `r(ω, x) ∈ 𝔻`
and a nonvanishing denominator. -/
theorem s5t53_G_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {c ω x : ℂ} {w : ExtPlane}
    (hω : ω ∈ unitDisc) (hgω : s5cf_gchart μ ω = -c)
    (hw : (w = extInf ∧ ω = 0) ∨ (ω ≠ 0 ∧ w = ((ω⁻¹ : ℂ) : ExtPlane))) (hx : x ∈ unitDiscExterior) :
    (x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1)) ∈ unitDisc ∧
      s5cf_gchart μ ((x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1))) + c ≠ 0 ∧
      finPart (mobiusExt 1 0 c 1 (normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane)))) =
        (s5cf_gchart μ ((x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1))) + c)⁻¹ := by
  set R := (x * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + x * (conj ω - 1)) with hRdef
  have hD := s5t53_rden hω hx
  have hS := s5t53_sigma_recip hω hx hw
  rw [← hRdef] at hS
  have hy : sigmaInvSphere w (x : ExtPlane) = mobiusExt 0 1 1 0 (R : ExtPlane) := by
    rw [← hS, sigma_invol]
  have hwE : w ∈ extDiscExterior := by
    rcases hw with ⟨rfl, -⟩ | ⟨hω0, rfl⟩
    · exact Or.inr rfl
    · refine Or.inl ⟨ω⁻¹, ?_, rfl⟩
      change 1 < ‖ω⁻¹‖
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hω0, mem_ball_zero_iff.mp hω⟩
  have hyE : sigmaInvSphere w (x : ExtPlane) ∈ extDiscExterior :=
    (sigmaSphere_mapsTo hwE).2 (Or.inl ⟨x, hx, rfl⟩)
  have hR : R ∈ unitDisc := by
    by_cases hR0 : R = 0
    · rw [hR0]; simp [unitDisc]
    · rw [hy, mobiusExt_coe (by simpa using hR0)] at hyE
      have hE : mobiusFn 0 1 1 0 R ∈ unitDiscExterior := by
        simpa [extDiscExterior, toExt] using hyE
      have hE' : 1 < ‖R⁻¹‖ := by simpa [mobiusFn, unitDiscExterior] using hE
      rw [norm_inv] at hE'
      have hp : 0 < ‖R‖ := norm_pos_iff.mpr hR0
      exact mem_ball_zero_iff.mpr ((one_lt_inv_iff₀).mp hE').2
  have hRω : R ≠ ω := by
    intro he
    have h1 := he
    rw [hRdef, div_eq_iff hD] at h1
    have h2 : (ω - 1) * (1 - ω * conj ω) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · have : ω = 1 := sub_eq_zero.mp h
      have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
      rw [this, norm_one] at hω1
      exact lt_irrefl _ hω1
    · rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
      have h3 : normSq ω < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        have hω1 : ‖ω‖ < 1 := mem_ball_zero_iff.mp hω
        nlinarith [norm_nonneg ω]
      have h4 : (1 - normSq ω : ℝ) = 0 := Complex.ofReal_eq_zero.mp h
      linarith
  have hne : s5cf_gchart μ R + c ≠ 0 := by
    intro h0
    apply hRω
    apply s5cf_gchart_inj hμ hR hω
    rw [hgω]
    linear_combination h0
  refine ⟨hR, hne, ?_⟩
  have hn : normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane)) =
      mobiusExt 0 1 1 0 ((s5cf_gchart μ R : ℂ) : ExtPlane) := by
    rw [s5cf_gchart_sphere hμ hR, sigma_invol, hy]
  rw [hn, s5t53_mob_recip hne]
  rfl

/-- **(C3b) joint `C²` of `G`** on `ℝ × 𝔻*`, via `G(t, x) = 1/(g^♯_{μ_t}(r(ω_t, x)) + c_t)` with `ω_t = F_{μ_t}(ζ_t)`
jointly real-analytic (`s5cf_uniformizer_parameter_analytic`, `s5cf_gchart_realAnalytic`). -/
theorem s5t53_G_joint {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ}
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℂ => finPart (mobiusExt 1 0 (deriv (deriv (fB (sec ((ψ p.1 : ℂ) • Y.1)))) 0 / 2 -
      (ψ p.1 : ℂ) * Y.2) 1 (normalizedWeldingSphere (sec ((ψ p.1 : ℂ) • Y.1))
        (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec ((ψ p.1 : ℂ) • Y.1)))
          (inversion (((ψ p.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ p.1 : ℂ) • Y.1)))) 0 / 2 : ℂ) : ExtPlane)))
          (p.2 : ExtPlane))))) (univ ×ˢ unitDiscExterior) := by
  -- the pointwise formula
  have hform : ∀ q : ℝ × ℂ, q.2 ∈ unitDiscExterior →
      (fun q : ℝ × ℂ => fiberUniformizer (sec ((ψ q.1 : ℂ) • Y.1))
        ((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2)) q ∈ unitDisc ∧
      ((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 = 0 ∨
        ∃ w ∈ unitDiscExterior, (ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 =
          (gMu (sec ((ψ q.1 : ℂ) • Y.1)) w)⁻¹) ∧
      ∀ ω : ℂ, ω = fiberUniformizer (sec ((ψ q.1 : ℂ) • Y.1))
          ((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2) →
        (q.2 * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + q.2 * (conj ω - 1)) ∈ unitDisc ∧
        s5cf_gchart (sec ((ψ q.1 : ℂ) • Y.1))
            ((q.2 * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + q.2 * (conj ω - 1))) +
          (deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 - (ψ q.1 : ℂ) * Y.2) ≠ 0 ∧
        finPart (mobiusExt 1 0 (deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 -
          (ψ q.1 : ℂ) * Y.2) 1 (normalizedWeldingSphere (sec ((ψ q.1 : ℂ) • Y.1))
            (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec ((ψ q.1 : ℂ) • Y.1)))
              (inversion (((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 : ℂ) :
                ExtPlane))) (q.2 : ExtPlane)))) =
          (s5cf_gchart (sec ((ψ q.1 : ℂ) • Y.1))
            ((q.2 * ω * (conj ω - 1) + ω - 1) / ((ω - 1) * conj ω + q.2 * (conj ω - 1))) +
          (deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2 - (ψ q.1 : ℂ) * Y.2))⁻¹ := by
    intro q hx
    obtain ⟨hμ, hz⟩ := s5t53_fibre_mem hsec hψb q.1
    obtain ⟨hζ, hw⟩ := s5t53_G_param hμ hz
    obtain ⟨hω, hgω⟩ := s5cf_uniformizer_inverse_data hμ hζ
    refine ⟨hω, hζ, ?_⟩
    rintro ω rfl
    exact s5t53_G_eq hμ hω (by rw [hgω]; ring) hw hx
  intro p hp
  have hx : p.2 ∈ unitDiscExterior := hp.2
  obtain ⟨hμ, -⟩ := s5t53_fibre_mem hsec hψb p.1
  obtain ⟨hωp, hζp, hfp⟩ := hform p hx
  obtain ⟨hRp, hnep, -⟩ := hfp _ rfl
  have hμc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => sec ((ψ q.1 : ℂ) • Y.1)) p :=
    ContDiffAt.comp (g := fun t : ℝ => sec ((ψ t : ℂ) • Y.1)) (f := fun q : ℝ × ℂ => q.1) p
      (s5t53_mu_curve hsa hψ hψb p.1) contDiffAt_fst
  have hcc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2) p :=
    ContDiffAt.comp (g := fun ν : LinfStar => deriv (deriv (fB ν)) 0 / 2)
      (f := fun q : ℝ × ℂ => sec ((ψ q.1 : ℂ) • Y.1)) p (s5l54_c_analytic hμ).contDiffAt hμc
  have hψc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => (ψ q.1 : ℂ) * Y.2) p :=
    ((Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_fst)).mul contDiff_const).contDiffAt
  have hζc := hψc.sub hcc
  have hω : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => fiberUniformizer (sec ((ψ q.1 : ℂ) • Y.1))
      ((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2)) p :=
    ContDiffAt.comp (g := fun q : LinfStar × ℂ => fiberUniformizer q.1 q.2)
      (f := fun q : ℝ × ℂ => (sec ((ψ q.1 : ℂ) • Y.1),
        (ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2)) p
      (s5cf_uniformizer_parameter_analytic hμ hζp).1.contDiffAt (hμc.prodMk hζc)
  set ω := fun q : ℝ × ℂ => fiberUniformizer (sec ((ψ q.1 : ℂ) • Y.1))
      ((ψ q.1 : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ q.1 : ℂ) • Y.1)))) 0 / 2) with hωdef
  have hcj : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => conj (ω q)) p :=
    ContDiffAt.comp (g := fun z : ℂ => conj z) (f := ω) p Complex.conjCLE.contDiff.contDiffAt hω
  have hN : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => q.2 * ω q * (conj (ω q) - 1) + ω q - 1) p :=
    (((contDiffAt_snd.mul hω).mul (hcj.sub contDiffAt_const)).add hω).sub contDiffAt_const
  have hDc : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => (ω q - 1) * conj (ω q) + q.2 * (conj (ω q) - 1)) p :=
    ((hω.sub contDiffAt_const).mul hcj).add (contDiffAt_snd.mul (hcj.sub contDiffAt_const))
  have hR : ContDiffAt ℝ 2 (fun q : ℝ × ℂ =>
      (q.2 * ω q * (conj (ω q) - 1) + ω q - 1) / ((ω q - 1) * conj (ω q) + q.2 * (conj (ω q) - 1))) p := by
    simp only [div_eq_mul_inv]
    exact hN.mul (hDc.inv (s5t53_rden hωp hx))
  have hg : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => s5cf_gchart (sec ((ψ q.1 : ℂ) • Y.1))
      ((q.2 * ω q * (conj (ω q) - 1) + ω q - 1) / ((ω q - 1) * conj (ω q) + q.2 * (conj (ω q) - 1)))) p :=
    ContDiffAt.comp (g := fun q : LinfStar × ℂ => s5cf_gchart q.1 q.2)
      (f := fun q : ℝ × ℂ => (sec ((ψ q.1 : ℂ) • Y.1),
        (q.2 * ω q * (conj (ω q) - 1) + ω q - 1) / ((ω q - 1) * conj (ω q) + q.2 * (conj (ω q) - 1)))) p
      (s5cf_gchart_realAnalytic hμ hRp).contDiffAt (hμc.prodMk hR)
  have hΦ := (hg.add (hcc.sub hψc)).inv hnep
  refine hΦ.contDiffWithinAt.congr (fun q hq => ((hform q hq.2).2.2 _ rfl).2.2) ((hfp _ rfl).2.2)

/-- **Area bound at radius `ρ`.** For `f` univalent on `𝔻` with `f(z) = Σ a_m z^{m+1}` and `|f| < K` on `|z| ≤ ρ`,
`Σ (j+1) |a_j|² ρ^{2(j+1)} ≤ K²/ρ²` (Green's identity on the gap between `f(|z| ≤ ρ)` and `|w| = K/ρ`,
`ab6_gap_green` with `U = id`, the gap having nonnegative area). -/
theorem s5t53_area_rho {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℂ} (hV : ∀ z ∈ unitDisc, HasSum (fun m : ℕ => a m * z ^ (m + 1)) (f z))
    {K : ℝ} (hK : 0 < K) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hKb : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖f z‖ < K) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1)))) ∧
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))) ≤ K ^ 2 / ρ ^ 2 := by
  have hG := AppB.ab6_gap_green (g := fun z => (K : ℂ) * z) hfd hfi hf0 hK (fun z => rfl) hρ0 hρ1 hKb
    (U := fun w => w) differentiableOn_id
  set F : ℕ → ℂ := fun n => if n = 0 then 0 else a (n - 1) with hF
  set d : ℤ → ℂ := fun n => if 0 ≤ n then F n.toNat else (fun _ : ℕ => (0 : ℂ)) (-n).toNat with hd
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℝ, r1 = ρ / 2 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℝ, r2 = (ρ + 1) / 2 := ⟨_, rfl⟩
  have hr1p : 0 < r1 := by rw [hr1]; positivity
  have hr1ρ : r1 < ρ := by rw [hr1]; linarith
  have hρr2 : ρ < r2 := by rw [hr2]; linarith
  have hr2one : r2 < 1 := by rw [hr2]; linarith
  have hdpos : ∀ n : ℕ, d (n : ℤ) = F n := fun n => by simp [hd]
  have hFs : ∀ n : ℕ, F (n + 1) = a n := fun n => by simp [hF]
  have hFsum : ∀ w ∈ unitDisc, HasSum (fun n : ℕ => F n * w ^ n) (f w) := by
    intro w hw
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, hF, if_true, zero_mul, sub_zero]
    refine (hV w hw).congr_fun (fun n => ?_)
    simp
  have hLaurent : ∀ w : ℂ, r1 < ‖w‖ → ‖w‖ < r2 → f w = ∑' n : ℤ, d n * w ^ n := by
    intro w _ hw2
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (hw2.trans hr2one)
    have h0 : HasSum (fun n : ℕ => (fun _ : ℕ => (0 : ℂ)) (n + 1) * w ^ (-((n : ℤ) + 1))) 0 := by
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    have h := Ch2.mg_hasSum_int F (fun _ : ℕ => (0 : ℂ)) (hFsum w hwD) h0
    rw [add_zero] at h
    exact h.tsum_eq.symm
  have hpos : Summable (fun n : ℕ => ‖d n‖ * r2 ^ n) := by
    have hr2D : ((r2 : ℝ) : ℂ) ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hr2one)
    have hn := summable_norm_iff.mpr (hFsum _ hr2D).summable
    refine hn.congr (fun j => ?_)
    rw [hdpos, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hneg : Summable (fun n : ℕ => ‖d (-(n : ℤ))‖ * (r1 ^ n)⁻¹) := by
    refine summable_of_ne_finset_zero (s := Finset.range 1) (fun n hn => ?_)
    have hn' : 1 ≤ n := by simp at hn; omega
    have h1 : ¬ (0 : ℤ) ≤ -(n : ℤ) := by omega
    simp only [hd, h1, if_false, norm_zero, zero_mul]
  have hE := Ch2.mg_circle_energy (H := f) d hr1p hr1ρ hρr2 hpos hneg hLaurent
  obtain ⟨hgs, hTc⟩ := Ch2.mg_energy_real hr1p hr1ρ hρr2 hpos hneg
  obtain ⟨hsp, -, hsplit⟩ := Ch2.mg_energy_split hr1p hr1ρ hρr2 hpos hneg
  have e1 : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖d ((j + 1 : ℕ) : ℤ)‖ ^ 2 * ρ ^ (2 * (j + 1)))) =
      fun j : ℕ => ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))) := by
    funext j
    rw [hdpos, hFs]
  have hneg0 : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (‖d (-((k + 1 : ℕ) : ℤ))‖ ^ 2 * (ρ ^ (2 * (k + 1)))⁻¹)) = 0 := by
    refine (tsum_congr fun k => ?_).trans tsum_zero
    have h1 : ¬ (0 : ℤ) ≤ -((k + 1 : ℕ) : ℤ) := by omega
    simp only [hd, h1, if_false, norm_zero]
    ring
  rw [e1] at hsp hsplit
  rw [hneg0, sub_zero] at hsplit
  refine ⟨hsp, ?_⟩
  set S := ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))) with hS
  have hfside : (∫ θ in (0 : ℝ)..2 * π, conj ((fun w : ℂ => w) (f (circleMap 0 ρ θ))) *
      deriv (fun z => (fun w : ℂ => w) (f z)) (circleMap 0 ρ θ) * circleMap 0 ρ θ) = 2 * π * (S : ℂ) := by
    show (∫ θ in (0 : ℝ)..2 * π, conj (f (circleMap 0 ρ θ)) * deriv f (circleMap 0 ρ θ) * circleMap 0 ρ θ) = _
    rw [hE, hTc, hsplit]
  have hgside : (∫ θ in (0 : ℝ)..2 * π, conj ((fun w : ℂ => w) ((fun z => (K : ℂ) * z) (circleMap 0 (1 / ρ) θ))) *
      deriv (fun z => (fun w : ℂ => w) ((fun z => (K : ℂ) * z) z)) (circleMap 0 (1 / ρ) θ) *
        circleMap 0 (1 / ρ) θ) = 2 * π * ((K ^ 2 / ρ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ θ : ℝ, conj ((fun w : ℂ => w) ((fun z => (K : ℂ) * z) (circleMap 0 (1 / ρ) θ))) *
        deriv (fun z => (fun w : ℂ => w) ((fun z => (K : ℂ) * z) z)) (circleMap 0 (1 / ρ) θ) *
          circleMap 0 (1 / ρ) θ = ((K ^ 2 / ρ ^ 2 : ℝ) : ℂ) := by
      intro θ
      have hz : ‖circleMap 0 (1 / ρ) θ‖ = 1 / ρ := by
        rw [norm_circleMap_zero, abs_of_pos (by positivity)]
      have hd : deriv (fun z => (fun w : ℂ => w) ((fun z => (K : ℂ) * z) z)) (circleMap 0 (1 / ρ) θ) = K :=
        ((hasDerivAt_id _).const_mul (K : ℂ)).deriv.trans (mul_one _)
      rw [hd]
      show conj ((K : ℂ) * circleMap 0 (1 / ρ) θ) * K * circleMap 0 (1 / ρ) θ = _
      rw [map_mul, Complex.conj_ofReal,
        show (K : ℂ) * conj (circleMap 0 (1 / ρ) θ) * K * circleMap 0 (1 / ρ) θ =
          (K : ℂ) ^ 2 * (conj (circleMap 0 (1 / ρ) θ) * circleMap 0 (1 / ρ) θ) by ring,
        Complex.conj_mul', hz]
      push_cast
      field_simp
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  rw [hfside, hgside] at hG
  set L := ∫ w in (f '' closedBall (0 : ℂ) ρ ∪ (fun z => (K : ℂ) * z) '' {z : ℂ | 1 / ρ ≤ ‖z‖})ᶜ,
    ‖deriv (fun w : ℂ => w) w‖ ^ 2 with hL
  have hL0 : 0 ≤ L := integral_nonneg fun _ => by positivity
  have hLr : L = -π * S + π * (K ^ 2 / ρ ^ 2) := by
    have h : (L : ℂ) = ((-π * S + π * (K ^ 2 / ρ ^ 2) : ℝ) : ℂ) := by
      rw [hG]
      push_cast
      ring
    exact_mod_cast h
  have hpi : 0 < π := Real.pi_pos
  nlinarith

/-- **Area theorem (interior, bounded).** For `f` univalent on `𝔻` with `f(z) = Σ a_m z^{m+1}` and `|f| < K` on `𝔻`,
`Σ (j+1) |a_j|² ≤ K²`. -/
theorem s5t53_area {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f unitDisc) (hfi : InjOn f unitDisc)
    (hf0 : f 0 = 0) {a : ℕ → ℂ} (hV : ∀ z ∈ unitDisc, HasSum (fun m : ℕ => a m * z ^ (m + 1)) (f z))
    {K : ℝ} (hK : 0 < K) (hb : ∀ z ∈ unitDisc, ‖f z‖ < K) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖a j‖ ^ 2) ∧
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * ‖a j‖ ^ 2 ≤ K ^ 2 := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * ‖a j‖ ^ 2 ≤ K ^ 2 := by
    intro N
    have hev : ∀ᶠ ρ : ℝ in 𝓝[<] 1,
        ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))) ≤ K ^ 2 / ρ ^ 2 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
      have hKb : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖f z‖ < K := fun z hz =>
        hb z (mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hρ.2))
      obtain ⟨hs, hle⟩ := s5t53_area_rho hfd hfi hf0 hV hK hρ.1 hρ.2 hKb
      exact (hs.sum_le_tsum _ (fun j _ => by have := hρ.1; positivity)).trans hle
    have hc1 : Tendsto (fun ρ : ℝ => ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * ρ ^ (2 * (j + 1))))
        (𝓝[<] 1) (𝓝 (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) * (‖a j‖ ^ 2 * 1 ^ (2 * (j + 1))))) :=
      ((continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_const.mul
        (continuous_pow _))).tendsto 1).mono_left nhdsWithin_le_nhds
    have hc2 : Tendsto (fun ρ : ℝ => K ^ 2 / ρ ^ 2) (𝓝[<] 1) (𝓝 (K ^ 2 / 1 ^ 2)) :=
      ((continuousAt_const.div (continuousAt_id.pow 2) (by norm_num : ((1 : ℝ)) ^ 2 ≠ 0)).tendsto).mono_left nhdsWithin_le_nhds
    have h := le_of_tendsto_of_tendsto hc1 hc2 hev
    simpa using h
  have hnn : ∀ j : ℕ, 0 ≤ ((j + 1 : ℕ) : ℝ) * ‖a j‖ ^ 2 := fun j => by positivity
  have hs := summable_of_sum_range_le hnn hpart
  exact ⟨hs, hs.tsum_le_of_sum_range_le hpart⟩

/-- **(C0) the cut-off.** A `C²` function `ψ` with `ψ = id` near `0` and `|ψ| < δ`. -/
theorem s5t53_c0_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧ ψ 0 = 0 ∧ deriv ψ 0 = 1 ∧ ψ =ᶠ[𝓝 0] id ∧ ∀ t, |ψ t| < δ := by
  let b : ContDiffBump (0 : ℝ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  refine ⟨fun t => t * b t, contDiff_id.mul b.contDiff, by simp, ?_, ?_, ?_⟩
  · have hev : (fun t : ℝ => t * b t) =ᶠ[𝓝 0] id := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < δ / 4 by positivity)] with t ht
      rw [b.one_of_mem_closedBall (ball_subset_closedBall ht), mul_one, id]
    rw [hev.deriv_eq, deriv_id]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < δ / 4 by positivity)] with t ht
    rw [b.one_of_mem_closedBall (ball_subset_closedBall ht), mul_one, id]
  · intro t
    show |t * b t| < δ
    by_cases ht : |t| < δ / 2
    · rw [abs_mul, abs_of_nonneg b.nonneg]
      calc |t| * b t ≤ |t| * 1 := by gcongr; exact b.le_one
        _ < δ := by linarith
    · have h0 : b t = 0 := b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact not_lt.mp ht)
      rw [h0, mul_zero, abs_zero]
      exact hδ

/-- **(C6) the analytic local section at the origin** (as `s5rh_local_coords`, with analyticity on a ball). -/
theorem s5t53_c6_section :
    ∃ sec : AInf unitDisc → LinfStar, ∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℂ sec (ball 0 ε) ∧
      sec 0 = ((Quotient.out originT : LinfStarBall) : LinfStar) ∧
      ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
        tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
          tcCoordHInv y ∈ TCurve := by
  obtain ⟨sec, U, hU, hpU, hsa, hs0, hsec⟩ := s5cf_section_analytic tOrigin.1
  have hsd : DifferentiableAt ℂ sec (bers tOrigin.1) := (hsa _ hpU).differentiableAt
  have hev : ∀ᶠ y : AInf unitDisc × ℂ in 𝓝 (tcCoordH tOrigin), ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi (Subtype.mk (sec y.1) h),
        inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
      tcCoordHInv y ∈ TCurve := by
    set ν₀ : LinfStar := ((Quotient.out tOrigin.1 : LinfStarBall) : LinfStar) with hν₀def
    have hν₀ : ν₀ ∈ LinfStarBall := (Quotient.out tOrigin.1 : LinfStarBall).2
    have hsd : DifferentiableAt ℂ sec (bers tOrigin.1) := (hsa _ hpU).differentiableAt
    set c : LinfStar → ℂ := fun ν => deriv (deriv (fB ν)) 0 / 2 with hc
    set x := tcCoordH tOrigin with hx
    have hsc : ContinuousAt (fun y : AInf unitDisc × ℂ => sec y.1) x := by
      have h1 : ContinuousAt sec x.1 := hsd.continuousAt
      exact h1.comp continuousAt_fst
    have hcc : ContinuousAt c (sec x.1) := by
      rw [show x.1 = bers tOrigin.1 from rfl, hs0]
      exact (s5rh_c_continuousOn.continuousAt (isOpen_ball.mem_nhds hν₀)).div_const 2
    set m : AInf unitDisc × ℂ → LinfStar × ExtPlane := fun y =>
      (sec y.1, inversion ((y.2 - c (sec y.1) : ℂ) : ExtPlane)) with hm
    have hmc : ContinuousAt m x := by
      refine hsc.prodMk ?_
      exact (tcc_inversion_continuous.comp OnePoint.continuous_coe).continuousAt.comp
        (continuousAt_snd.sub (ContinuousAt.comp (g := c) (f := fun y : AInf unitDisc × ℂ => sec y.1) hcc hsc))
    have ha0 : tOrigin.2 ≠ ((0 : ℂ) : ExtPlane) := fun h0 => tcc_zero_not_mem hν₀ (h0 ▸ s5rh_tOrigin_mem)
    have hm0 : m x = (ν₀, tOrigin.2) := by
      have hback : inversion ((finPart (inversion tOrigin.2) : ℂ) : ExtPlane) = tOrigin.2 := by
        rw [coe_finPart_of_ne (fun h => ha0 ((tcc_inversion_eq_inf_iff tOrigin.2).mp h)), tcc_inversion_invol]
      have hs0' : sec x.1 = ν₀ := hs0
      simp only [hm, hs0']
      have he : x.2 - c ν₀ = finPart (inversion tOrigin.2) := by
        show finPart (inversion tOrigin.2) + deriv (deriv (fB ν₀)) 0 / 2 - deriv (deriv (fB ν₀)) 0 / 2 = _
        ring
      rw [he, hback]
    have hT := tcc_tube hν₀ s5rh_tOrigin_mem
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
    have hinv : tcCoordHInv (tcCoordH q') = q' := s5rh_injOn.leftInvOn_invFunOn hq'm
    rw [hHq] at hinv
    exact ⟨h, hinv, hinv ▸ hq'm⟩
  rw [s5t53_tcCoordH_origin, Prod.mk_zero_zero] at hev
  obtain ⟨ε₁, hε₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hb0 : bers tOrigin.1 = 0 := c32_bers_origin
  rw [hb0] at hpU hs0
  obtain ⟨ε₂, hε₂, hU2⟩ := Metric.isOpen_iff.mp hU 0 hpU
  refine ⟨sec, min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx => hsa x (hU2 (ball_subset_ball (min_le_right _ _) hx)),
    hs0, fun y hy => ?_⟩
  have hy' : y ∈ ball (0 : AInf unitDisc × ℂ) ε₁ := by
    rw [mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨h, h1, h2⟩ := hb y hy'
  exact ⟨h, h1, h2⟩

/-- **(C1) welding.** Each `(F t, G t)` is the CW2′ welding of `h_t = σ_{w_t} ∘ 𝗀_{μ_t}` (`fiber_welding`; `welding_of_wA` when `w_t = ∞`). -/
theorem s5t53_c1_welding {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ} (hε : 0 < ε)
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε)) (hs0 : sec 0 = ((Quotient.out originT : LinfStarBall) : LinfStar))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0 = 0) (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) :
    ∀ t, ∃ h, IsOneFixedQS h ∧ IsWeldingPrime h ((fun t : ℝ => fun x : ℂ => lambdaW (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) (fB (sec ((ψ t : ℂ) • Y.1)) x)) t) ((fun t : ℝ => fun x : ℂ => finPart (mobiusExt 1 0 (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) 1 (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1)) (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1))) (inversion (((ψ t : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane))))) t) := by
  intro t
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z => rw [mobiusExt_coe (by simp)]; simp [mobiusFn]
  obtain ⟨hμ, hq, hqm⟩ := hsec (((ψ t : ℝ) : ℂ) • Y) (hψb t)
  set μ := sec ((ψ t : ℂ) • Y.1) with hμdef
  set s := (ψ t : ℂ) * Y.2 with hsdef
  set cμ := deriv (deriv (fB μ)) 0 / 2 with hcμ
  set z : ExtPlane := inversion ((s - cμ : ℂ) : ExtPlane) with hzdef
  replace hμ : μ ∈ LinfStarBall := hμ
  have hq' : tcCoordHInv (((ψ t : ℝ) : ℂ) • Y) = (Phi ⟨μ, hμ⟩, z) := hq
  have hz : z ∈ wB μ '' extDiscExterior := by
    have hm := hqm
    rw [hq'] at hm
    have hcls : teichSetoid (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) ⟨μ, hμ⟩ :=
      Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
    change z ∈ wB (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) '' extDiscExterior at hm
    rwa [fiber_independent hcls] at hm
  have hz' : z ∈ normalizedWeldingSphere μ '' extDiscExterior := by rw [tcg_welding_image hμ]; exact hz
  set w := Function.invFun (normalizedWeldingSphere μ) z with hwdef
  have hwz : normalizedWeldingSphere μ w = z := by
    obtain ⟨a, -, ha⟩ := hz'
    exact Function.invFun_eq ⟨a, ha⟩
  have hw : w ∈ extDiscExterior := tcg_parameter_mem hμ hz
  rcases hw with ⟨w', hw', hww⟩ | hwi
  · -- `w_t` finite: `fiber_welding`
    have hg := gMu_exterior_ne_zero hμ hw'
    have hgz : ((gMu μ w' : ℂ) : ExtPlane) = z := by
      rw [← hwz, ← hww, ← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw']
    have hc : -1 / gMu μ w' = cμ - s := by
      have h1 : inversion ((gMu μ w' : ℂ) : ExtPlane) = ((s - cμ : ℂ) : ExtPlane) := by
        rw [hgz, hzdef, tcc_inversion_invol]
      rw [s5rh_inversion_coe hg] at h1
      have h2 : (gMu μ w')⁻¹ = s - cμ := OnePoint.coe_injective h1
      rw [div_eq_mul_inv, neg_one_mul, h2]
      ring
    obtain ⟨h1, h2, -⟩ := fiber_welding hμ hw'
    refine ⟨_, h1, ?_⟩
    show IsWeldingPrime _ (fun x => lambdaW (cμ - s) (fB μ x))
      (fun x => finPart (mobiusExt 1 0 (cμ - s) 1 (normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane)))))
    rw [← hww, ← hc]
    exact h2
  · -- `w_t = ∞`: `welding_of_wA`
    have hwi' : w = extInf := hwi
    have hzi : z = extInf := by rw [← hwz, hwi', normalizedWeldingSphere_infty hμ]
    have hsc : s - cμ = 0 := by
      have h := (tcc_inversion_eq_inf_iff _).mp hzi
      exact OnePoint.coe_injective h
    have hc : cμ - s = 0 := by linear_combination -hsc
    obtain ⟨hα, ⟨F', G', hF', hFs, hFe, hG', hGs, hGe, hbd⟩, hd, hinj, h0, h1, huniv⟩ := (welding_of_wA hμ).1
    refine ⟨wA μ, tmi_wA_oneFixed hμ, ?_⟩
    show IsWeldingPrime (wA μ) (fun x => lambdaW (cμ - s) (fB μ x))
      (fun x => finPart (mobiusExt 1 0 (cμ - s) 1 (normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane)))))
    rw [hc, hwi']
    have hF : (fun x => lambdaW 0 (fB μ x)) = fB μ := funext fun x => by simp [lambdaW]
    have hG : EqOn (fun x : ℂ => finPart (mobiusExt 1 0 0 1 (normalizedWeldingSphere μ
        (sigmaInvSphere extInf (x : ExtPlane))))) (gMu μ) unitDiscExterior := by
      intro x hx
      show finPart (mobiusExt 1 0 0 1 (normalizedWeldingSphere μ (x : ExtPlane))) = _
      rw [hid, id, gMu_eq_normalizedWeldingExterior hμ hx]
      rfl
    rw [hF]
    refine ⟨⟨F', G', hF', hFs, hFe, hG', hGs, hGe.trans hG.symm, fun x hx => ?_⟩, hd, hinj, h0, h1, ?_⟩
    · have h := hbd x hx
      rw [hα] at h
      exact OnePoint.coe_injective h
    · refine ⟨huniv.1.congr hG, huniv.2.1.congr hG.symm, huniv.2.2.congr' ?_⟩
      filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with x hx
      have hx' : x ∈ unitDiscExterior := by simpa [unitDiscExterior] using hx
      exact (hG hx').symm

/-- **(C2) start.** `F 0 = id` on `𝔻`, `G 0 = id` on `𝔻*` (the origin class, `w_0 = ∞`). -/
theorem s5t53_c2_origin {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ} (hε : 0 < ε)
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε)) (hs0 : sec 0 = ((Quotient.out originT : LinfStarBall) : LinfStar))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0 = 0) (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) :
    (∀ x ∈ unitDisc, (fun t : ℝ => fun x : ℂ => lambdaW (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) (fB (sec ((ψ t : ℂ) • Y.1)) x)) 0 x = x) ∧ ∀ x ∈ unitDiscExterior, (fun t : ℝ => fun x : ℂ => finPart (mobiusExt 1 0 (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) 1 (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1)) (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1))) (inversion (((ψ t : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane))))) 0 x = x := by
  have hμ := (Quotient.out originT : LinfStarBall).2
  have hc0 : deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 = 0 := by
    have he : fB ((Quotient.out originT : LinfStarBall) : LinfStar) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])] with z hz
      exact s5tg_origin_fB hz
    have hd : deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar)) =ᶠ[𝓝 (0 : ℂ)] fun _ => 1 := by
      filter_upwards [he.eventuallyEq_nhds] with z hz
      rw [hz.deriv_eq, deriv_id]
    rw [hd.deriv_eq, deriv_const]
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z => rw [mobiusExt_coe (by simp)]; simp [mobiusFn]
  have hinf : Function.invFun (normalizedWeldingSphere ((Quotient.out originT : LinfStarBall) : LinfStar)) extInf =
      extInf := by
    conv_lhs => rw [← normalizedWeldingSphere_infty hμ]
    exact Function.leftInverse_invFun (normalizedWeldingSphere_bijective _).1 extInf
  have hinv0 : inversion ((0 : ℂ) : ExtPlane) = extInf := (tcc_inversion_eq_inf_iff _).mpr rfl
  have hσ : sigmaInvSphere extInf = id := rfl
  have hl0 : ∀ z : ℂ, lambdaW 0 z = z := fun z => by simp [lambdaW]
  simp only [hψ0, Complex.ofReal_zero, zero_smul, zero_mul, sub_zero, hs0, hc0, zero_div]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [hl0, s5tg_origin_fB hx]
  · rw [hinv0, hinf, hσ, id, s5tg_origin_nWS (Or.inl ⟨x, hx, rfl⟩), hid]
    rfl

/-- **(C5) the potential, wall (iii).** `K = log |G_t'(∞)|` along the curve: `lemma_5_1` part 2 when `w_t ∈ 𝔻*`, and the fibre-`∞` formula `K = log |F_μ'(0)|` when `w_t = ∞` (including `t = 0`). -/
theorem s5t53_c5_potential {Y : AInf unitDisc × ℂ} {sec : AInf unitDisc → LinfStar} {ε : ℝ} (hε : 0 < ε)
    (hsa : AnalyticOnNhd ℂ sec (ball 0 ε)) (hs0 : sec 0 = ((Quotient.out originT : LinfStarBall) : LinfStar))
    (hsec : ∀ y : AInf unitDisc × ℂ, ‖y‖ < ε → ∃ h : sec y.1 ∈ LinfStarBall,
      tcCoordHInv y = (Phi ⟨sec y.1, h⟩, inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ψ 0 = 0) (hψb : ∀ t, ‖((ψ t : ℝ) : ℂ) • Y‖ < ε) :
    ∀ t, potentialK (tcCoordHInv (((ψ t : ℝ) : ℂ) • Y)) = Real.log ‖derivAtInfty ((fun t : ℝ => fun x : ℂ => finPart (mobiusExt 1 0 (deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 - (ψ t : ℂ) * Y.2) 1 (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1)) (sigmaInvSphere (Function.invFun (normalizedWeldingSphere (sec ((ψ t : ℂ) • Y.1))) (inversion (((ψ t : ℂ) * Y.2 - deriv (deriv (fB (sec ((ψ t : ℂ) • Y.1)))) 0 / 2 : ℂ) : ExtPlane))) (x : ExtPlane))))) t)‖ := by
  intro t
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z => rw [mobiusExt_coe (by simp)]; simp [mobiusFn]
  obtain ⟨hμ, hq, hqm⟩ := hsec (((ψ t : ℝ) : ℂ) • Y) (hψb t)
  set μ := sec ((ψ t : ℂ) • Y.1) with hμdef
  set s := (ψ t : ℂ) * Y.2 with hsdef
  set cμ := deriv (deriv (fB μ)) 0 / 2 with hcμ
  set z : ExtPlane := inversion ((s - cμ : ℂ) : ExtPlane) with hzdef
  replace hμ : μ ∈ LinfStarBall := hμ
  have hq' : tcCoordHInv (((ψ t : ℝ) : ℂ) • Y) = (Phi ⟨μ, hμ⟩, z) := hq
  have hcls : teichSetoid (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) ⟨μ, hμ⟩ :=
    Quotient.mk_out (s := teichSetoid) (⟨μ, hμ⟩ : LinfStarBall)
  have hgc := s5cf_gMu_congr hcls
  have hz : z ∈ wB μ '' extDiscExterior := by
    have hm := hqm
    rw [hq'] at hm
    change z ∈ wB (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) '' extDiscExterior at hm
    rwa [fiber_independent hcls] at hm
  have hz' : z ∈ normalizedWeldingSphere μ '' extDiscExterior := by rw [tcg_welding_image hμ]; exact hz
  set w := Function.invFun (normalizedWeldingSphere μ) z with hwdef
  have hwz : normalizedWeldingSphere μ w = z := by
    obtain ⟨a, -, ha⟩ := hz'
    exact Function.invFun_eq ⟨a, ha⟩
  have hw : w ∈ extDiscExterior := tcg_parameter_mem hμ hz
  rw [hq']
  rcases hw with ⟨w', hw', hww⟩ | hwi
  · -- `w_t` finite: `lemma_5_1` part 2
    have hg := gMu_exterior_ne_zero hμ hw'
    have hgz : ((gMu μ w' : ℂ) : ExtPlane) = z := by
      rw [← hwz, ← hww, ← normalizedWeldingExterior_coe hμ, ← gMu_eq_normalizedWeldingExterior hμ hw']
    have hc : -1 / gMu μ w' = cμ - s := by
      have h1 : inversion ((gMu μ w' : ℂ) : ExtPlane) = ((s - cμ : ℂ) : ExtPlane) := by
        rw [hgz, hzdef, tcc_inversion_invol]
      rw [s5rh_inversion_coe hg] at h1
      have h2 : (gMu μ w')⁻¹ = s - cμ := OnePoint.coe_injective h1
      rw [div_eq_mul_inv, neg_one_mul, h2]
      ring
    have hgc' : ∀ x ∈ unitDiscExterior, gMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) x = gMu μ x :=
      fun x hx => hgc hx
    have hK := (lemma_5_1.2 (Phi ⟨μ, hμ⟩) w' hw')
    rw [hgc' w' hw', hgz] at hK
    rw [hK]
    congr 2
    apply s5t53_derivAtInfty_congr
    set k : ℂ := (1 - w') / (1 - conj w') with hk
    filter_upwards [s5t53_ev_exterior, (isCompact_singleton (x := -(k * conj w'))).compl_mem_cocompact]
      with x hx hd
    have hden : x + k * conj w' ≠ 0 := by simpa [eq_neg_iff_add_eq_zero] using hd
    have hσ := sigmaInvSphere_coe_eq hw' hden
    have hfin := fiberWeldingExterior_finite hμ hw' hx hσ
    have hinvf := sigmaW_invFun_of_finite_inverse hw' hx hσ
    have huE : sigmaInv w' x ∈ unitDiscExterior := by
      have he := (sigmaSphere_mapsTo (Or.inl ⟨w', hw', rfl⟩)).2 (Or.inl ⟨x, hx, rfl⟩)
      rw [hσ] at he
      simpa [extDiscExterior, toExt] using he
    show lambdaW (-1 / gMu μ w')
        (gMu (Quotient.out (Phi ⟨μ, hμ⟩) : LinfStarBall) (Function.invFun (sigmaW w') x)) =
      finPart (mobiusExt 1 0 (cμ - s) 1 (normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane))))
    rw [← hc, ← hww]
    change _ = fiberWeldingExterior μ w' x
    rw [hfin, hinvf, hgc' _ huE]
  · -- `w_t = ∞` (in particular `t = 0`): the fibre-`∞` formula
    have hwi' : w = extInf := hwi
    have hzi : z = extInf := by rw [← hwz, hwi', normalizedWeldingSphere_infty hμ]
    have hsc : s - cμ = 0 := by
      have h := (tcc_inversion_eq_inf_iff _).mp hzi
      exact OnePoint.coe_injective h
    have hc : cμ - s = 0 := by linear_combination -hsc
    rw [hzi, s5t53_K_infty hμ]
    congr 2
    apply s5t53_derivAtInfty_congr
    filter_upwards [s5t53_ev_exterior] with x hx
    show gMu μ x = finPart (mobiusExt 1 0 (cμ - s) 1 (normalizedWeldingSphere μ (sigmaInvSphere w (x : ExtPlane))))
    rw [hc, hwi']
    show gMu μ x = finPart (mobiusExt 1 0 0 1 (normalizedWeldingSphere μ (x : ExtPlane)))
    rw [hid, id, gMu_eq_normalizedWeldingExterior hμ hx]
    rfl

/-- The outer derivative in (A) is not a junk value: `t ↦ (d/dt) K(tY)` is differentiable at `0` (`s5l54_regular`). -/
theorem s5t53_K_line_differentiable (Y : AInf unitDisc × ℂ) :
    DifferentiableAt ℝ (deriv fun t : ℝ => potentialK (tcCoordHInv ((t : ℂ) • Y))) 0 := by
  have hreg := s5l54_regular s5rh_tOrigin_mem
  have hx0 : tcCoordH tOrigin = 0 := by
    rw [← Prod.mk_zero_zero]
    exact s5t53_tcCoordH_origin
  rw [hx0] at hreg
  have hL : ContDiff ℝ 2 fun t : ℝ => (t : ℂ) • Y :=
    (Complex.ofRealCLM.contDiff).smul contDiff_const
  have hreg' : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
      ((fun t : ℝ => (t : ℂ) • Y) 0) := by simpa using hreg
  have hc := ContDiffAt.comp (g := fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
    (f := fun t : ℝ => (t : ℂ) • Y) 0 hreg' hL.contDiffAt
  have hK : ContDiffAt ℝ 2 (fun t : ℝ => potentialK (tcCoordHInv ((t : ℂ) • Y))) 0 :=
    (hc.div_const 2).sub contDiffAt_const
  have hd1 : ContDiffAt ℝ 1 (fderiv ℝ fun t : ℝ => potentialK (tcCoordHInv ((t : ℂ) • Y))) 0 :=
    hK.fderiv_right (m := 1) (by norm_num)
  have h := (hd1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const (1 : ℝ))
  exact h

/-- `vkNormSqCoordOrigin` is quadratic. -/
theorem s5t53_vkO_smul (a : ℂ) (Y : AInf unitDisc × ℂ) :
    vkNormSqCoordOrigin (a • Y) = ‖a‖ ^ 2 * vkNormSqCoordOrigin Y := by
  unfold vkNormSqCoordOrigin
  simp only [Prod.smul_fst, Prod.smul_snd, s5t53_tangentCoeff_smul, norm_mul, norm_smul, mul_pow]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · congr 1
    funext n
    ring

end TakhtajanTeo
