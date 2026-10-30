import TakhtajanTeo.Ch1.S5Lemma54
import TakhtajanTeo.Ch1.ComponentTB
import TakhtajanTeo.Ch1.S5TCurveGroup

/-!
# `thm_5_3` (`s5t53_`, 下属3, Program G)

Host: new module `TakhtajanTeo/Ch1/S5Thm53.lean`.

* Reduction of (ii) to the origin (`s5t53_ii_of_origin`): `q * q⁻¹ = (0, ∞)` and the Levi transport.
* Reduction (ii) ⇒ (i): `leviTC logNormSq = 2 leviTC potentialK` (`s5l54_regular`); `vkNormSq` is a Hermitian
  quadratic form, so `polarize` gives it back on the diagonal.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- `∂_t∂_t̄` of a constant vanishes. -/
theorem s5t53_mixed_const (a z : ℂ) : dz (dzbar fun _ : ℂ => a) z = 0 := by
  have h : dzbar (fun _ : ℂ => a) = fun _ => 0 := by
    funext w
    simp [dzbar]
  rw [h]
  simp [dz]

/-- `leviTC logNormSq = 2 leviTC potentialK` on `𝒯(1)`. -/
theorem s5t53_levi_log_K {q : T1 × ExtPlane} (hq : q ∈ TCurve) (Y : AInf unitDisc × ℂ) :
    leviTC logNormSq q Y = 2 * leviTC potentialK q Y := by
  have hg := s5l54_regular hq
  have ha : ContDiffAt ℝ 2 (fun t : ℂ => tcCoordH q + t • Y) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  have hg' : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
      ((fun t : ℂ => tcCoordH q + t • Y) 0) := by
    simpa using hg
  have hc : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (tcCoordH q + t • Y))) 0 := ContDiffAt.comp (g := fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w))
    (f := fun t : ℂ => tcCoordH q + t • Y) 0 hg' ha
  have hK : ContDiffAt ℝ 2 (fun t : ℂ => ((potentialK (tcCoordHInv (tcCoordH q + t • Y)) : ℝ) : ℂ)) 0 := by
    have h1 : ContDiffAt ℝ 2 (fun t : ℂ => logNormSq (tcCoordHInv (tcCoordH q + t • Y)) / 2 - Real.log 2) 0 :=
      (hc.div_const 2).sub contDiffAt_const
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 h1
  have he : (fun t : ℂ => ((logNormSq (tcCoordHInv (tcCoordH q + t • Y)) : ℝ) : ℂ)) =
      fun t => 2 * ((potentialK (tcCoordHInv (tcCoordH q + t • Y)) : ℝ) : ℂ) + ((2 * Real.log 2 : ℝ) : ℂ) := by
    funext t
    unfold potentialK
    push_cast
    ring
  unfold leviTC
  rw [he, s5vc_mixed_add (contDiffAt_const.mul hK) contDiffAt_const, s5vc_mixed_const_mul hK,
    s5t53_mixed_const, add_zero]
  simp

/-- `tangentCoeff` is linear in `φ`. -/
theorem s5t53_tangentCoeff_smul (a : ℂ) (φ : AInf unitDisc) (n : ℕ) :
    tangentCoeff (a • φ) n = a * tangentCoeff φ n := by
  unfold tangentCoeff
  rw [ctb_toFun_smul]
  have h : (fun z => a * AInf.toFun φ z) = a • AInf.toFun φ := by
    funext z
    simp
  rw [h, iteratedDeriv_const_smul_field, smul_eq_mul]
  ring

/-- `vkNormSq q` is quadratic: `‖aX‖² = |a|² ‖X‖²`. -/
theorem s5t53_vk_smul (q : T1 × ExtPlane) (a : ℂ) (X : AInf unitDisc × ℂ) :
    vkNormSq q (a • X) = ‖a‖ ^ 2 * vkNormSq q X := by
  unfold vkNormSq vkNormSqCoordOrigin
  rw [map_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, s5t53_tangentCoeff_smul, norm_mul, norm_smul, mul_pow]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · congr 1
    funext n
    ring

/-- `polarize N X X = N X` for a quadratic `N`. -/
theorem s5t53_polarize_diag {N : AInf unitDisc × ℂ → ℝ} (hN : ∀ (a : ℂ) X, N (a • X) = ‖a‖ ^ 2 * N X)
    (X : AInf unitDisc × ℂ) : polarize N X X = N X := by
  unfold polarize
  have e1 : X + X = (2 : ℂ) • X := (two_smul ℂ X).symm
  have e2 : X - X = (0 : ℂ) • X := by simp
  have e3 : X + I • X = (1 + I) • X := by rw [add_smul, one_smul]
  have e4 : X - I • X = (1 - I) • X := by
    rw [show (1 - I : ℂ) = 1 + -I by ring, add_smul, one_smul, neg_smul, sub_eq_add_neg]
  have n3 : ‖(1 + I : ℂ)‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    norm_num
  have n4 : ‖(1 - I : ℂ)‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    norm_num
  rw [e1, e2, e3, e4, hN, hN, hN, hN, n3, n4]
  simp only [norm_zero, Complex.norm_ofNat]
  push_cast
  ring

/-- **(ii) ⇒ (i)** of `thm_5_3`: the Kähler potential identity gives `c₁(V) = -(2/π) ω_VK`. -/
theorem s5t53_i_of_ii (h : ∀ q ∈ TCurve, ∀ X, leviTC potentialK q X = vkNormSq q X) :
    ∀ q ∈ TCurve, ∀ X, chernForm q X = -(2 / π) * omegaVK q X := by
  intro q hq X
  have hL : leviTC logNormSq q = fun Y => 2 * vkNormSq q Y := by
    funext Y
    rw [s5t53_levi_log_K hq, h q hq]
  have hP : polarize (leviTC logNormSq q) X X = ((2 * vkNormSq q X : ℝ) : ℂ) := by
    rw [hL]
    exact s5t53_polarize_diag (fun a Y => by rw [s5t53_vk_smul]; ring) X
  unfold chernForm thetaForm omegaVK
  rw [hP]
  push_cast
  field_simp

/-- The fibre metric law at one point `q'`: with `h = ∂_s R̃₂` (the fibre derivative of `R̃` in `tcCoordH`),
`h(q') = T'(ζ') ≠ 0` and `log‖z²∂_z‖²(q') = log‖z²∂_z‖²(R q') + log|h|²`; here `R = (· * b⁻¹)` for any `b ∈ 𝒯(1)`
(`s5l54_law_at` is the case `b = q₀⁻¹`). -/
theorem s5t53_law_at {b q' : T1 × ExtPlane} (hb : b ∈ TCurve) (hq' : q' ∈ TCurve) :
    (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x b) (tcCoordH q') ((0 : AInf unitDisc), (1 : ℂ))).2 ≠ 0 ∧
      logNormSq q' = logNormSq (tcurveMulInv q' b) +
        Real.log (‖(fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x b) (tcCoordH q') ((0 : AInf unitDisc), (1 : ℂ))).2‖ ^ 2) := by
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
  set R : T1 × ExtPlane → T1 × ExtPlane := fun x => tcurveMulInv x b with hRdef
  set w := tcCoordH q' with hwdef
  -- `h(w) = T'(ζ')`
  set D := fderiv ℂ (tcCoordExpr R) w with hDdef
  have hRd : HasFDerivAt (tcCoordExpr R) D w := (s5rh_mulInv_holo hq' hb).hasFDerivAt
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

/-- The Levi form of `log‖z²∂_z‖²` is transported by the right translation `R = (· * b⁻¹)`:
`Levi_q(Y) = Levi_{q * b⁻¹}(dR̃(Y))` (the proof of `s5l54_lemma_5_4`, for any `b ∈ 𝒯(1)`). -/
theorem s5t53_levi_transport {b q : T1 × ExtPlane} (hb : b ∈ TCurve) (hq : q ∈ TCurve) (Y : AInf unitDisc × ℂ) :
    leviTC logNormSq q Y = leviTC logNormSq (tcurveMulInv q b)
      (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x b) (tcCoordH q) Y) := by
  have : CompleteSpace (AInf unitDisc) := AInf_completeSpace_disc
  set R : T1 × ExtPlane → T1 × ExtPlane := fun x => tcurveMulInv x b with hRdef
  set x := tcCoordH q with hxdef
  have hRq : R q ∈ TCurve := tcg_mul_mem_curve hq hb
  have hqx : tcCoordHInv x = q := s5rh_injOn.leftInvOn_invFunOn hq
  have hΦx : tcCoordExpr R x = tcCoordH (R q) := by
    show tcCoordH (R (tcCoordHInv x)) = _
    rw [hqx]
  have hΦa : AnalyticAt ℂ (tcCoordExpr R) x := by
    obtain ⟨U, hUsub, hUo, hxU⟩ := _root_.mem_nhds_iff.mp (s5l54_image_nhds hq)
    have hd : DifferentiableOn ℂ (tcCoordExpr R) U := fun w hw => by
      obtain ⟨q', hq', rfl⟩ := hUsub hw
      exact (s5rh_mulInv_holo hq' hb).differentiableWithinAt
    exact bha_analyticOnNhd hUo hd x hxU
  have hg : ContDiffAt ℝ 2 (fun w : AInf unitDisc × ℂ => logNormSq (tcCoordHInv w)) (tcCoordExpr R x) := by
    rw [hΦx]
    exact s5l54_regular hRq
  -- the metric law for `R`
  set h : AInf unitDisc × ℂ → ℂ := fun w => (fderiv ℂ (tcCoordExpr R) w ((0 : AInf unitDisc), (1 : ℂ))).2 with hhdef
  have hha : AnalyticAt ℂ h x := by
    have h' := ((ContinuousLinearMap.snd ℂ (AInf unitDisc) ℂ).analyticAt _).comp
      (((ContinuousLinearMap.apply ℂ (AInf unitDisc × ℂ) ((0 : AInf unitDisc), (1 : ℂ))).analyticAt _).comp
        hΦa.fderiv)
    exact h'
  have hh0 : h x ≠ 0 := (s5t53_law_at hb hq).1
  have hlaw : ∀ᶠ w in 𝓝 x, logNormSq (tcCoordHInv w) =
      logNormSq (tcCoordHInv (tcCoordExpr R w)) + Real.log (‖h w‖ ^ 2) := by
    filter_upwards [s5l54_image_nhds hq] with w hw
    obtain ⟨q', hq', rfl⟩ := hw
    have hRq' : R q' ∈ TCurve := tcg_mul_mem_curve hq' hb
    have hi : tcCoordHInv (tcCoordH q') = q' := s5rh_injOn.leftInvOn_invFunOn hq'
    have hi' : tcCoordHInv (tcCoordExpr R (tcCoordH q')) = R q' := by
      show tcCoordHInv (tcCoordH (R (tcCoordHInv (tcCoordH q')))) = _
      rw [hi]
      exact s5rh_injOn.leftInvOn_invFunOn hRq'
    rw [hi, hi']
    exact (s5t53_law_at hb hq').2
  obtain ⟨hc1, hch⟩ := s5l54_levi_chain hg hΦa Y
  obtain ⟨hc2, hlog⟩ := s5l54_levi_log hha hh0 Y
  have ht : Tendsto (fun t : ℂ => x + t • Y) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℂ => x + t • Y) := by fun_prop
    simpa using hc.tendsto 0
  have hev : (fun t : ℂ => ((logNormSq (tcCoordHInv (tcCoordH q + t • Y)) : ℝ) : ℂ)) =ᶠ[𝓝 0]
      fun t => ((logNormSq (tcCoordHInv (tcCoordExpr R (x + t • Y))) : ℝ) : ℂ) +
        ((Real.log (‖h (x + t • Y)‖ ^ 2) : ℝ) : ℂ) := by
    filter_upwards [ht.eventually hlaw] with t hlt
    rw [hlt]
    push_cast
    rfl
  unfold leviTC
  rw [s5vc_mixed_congr hev, s5vc_mixed_add hc1 hc2, hlog, add_zero, hch, hΦx]

/-- **Reduction of thm_5_3 (ii) to the origin.** By `q * q⁻¹ = (0, ∞)` (`s5tg_mul_self`) and the transport
`s5t53_levi_transport` (with `b = q`), `Levi_q K(X) = Levi_{(0,∞)} K(dR̃ X)`, and `vkNormSq q X` is `(4.1)` of `dR̃ X`. -/
theorem s5t53_ii_of_origin (h0 : ∀ Y, leviTC potentialK tOrigin Y = vkNormSqCoordOrigin Y) :
    ∀ q ∈ TCurve, ∀ X, leviTC potentialK q X = vkNormSq q X := by
  intro q hq X
  have ht := s5t53_levi_transport hq hq X
  rw [s5tg_mul_self hq, s5t53_levi_log_K hq, s5t53_levi_log_K s5rh_tOrigin_mem, h0] at ht
  have h2 : leviTC potentialK q X = vkNormSqCoordOrigin
      (fderiv ℂ (tcCoordExpr fun x => tcurveMulInv x q) (tcCoordH q) X) := by linarith
  rw [h2]
  rfl

/-- Levi forms scale by `|c|²` under `t ↦ c t`: `∂∂̄ (g(c·))(0) = |c|² ∂∂̄ g(0)` for real `C²` `g`. -/
theorem s5t53_levi_scale {g : ℂ → ℝ} (hg : ContDiffAt ℝ 2 g 0) (c : ℂ) :
    dz (dzbar fun t : ℂ => ((g (c * t) : ℝ) : ℂ)) 0 = ((‖c‖ ^ 2 : ℝ) : ℂ) * dz (dzbar fun t : ℂ => ((g t : ℝ) : ℂ)) 0 := by
  have hγ : AnalyticAt ℂ (fun t : ℂ => c * t) 0 := analyticAt_const.mul analyticAt_id
  have hι : AnalyticAt ℂ (fun t : ℂ => t) 0 := analyticAt_id
  have hg1 : ContDiffAt ℝ 2 g ((fun t : ℂ => c * t) 0) := by simpa using hg
  have hg2 : ContDiffAt ℝ 2 g ((fun t : ℂ => t) 0) := hg
  obtain ⟨-, e1⟩ := s5l54_levi_curve hg1 hγ
  obtain ⟨-, e2⟩ := s5l54_levi_curve hg2 hι
  have d1 : deriv (HMul.hMul c) 0 = c := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_mul c).deriv
    simp only [id, mul_one] at h
    exact h
  have d2 : deriv (fun t : ℂ => t) 0 = 1 := deriv_id 0
  simp only [mul_zero] at e1
  rw [e1, e2, d1, d2]
  set B := fderiv ℝ (fderiv ℝ g) 0 with hB
  have hquad : ∀ a b : ℝ, B (a • (1 : ℂ) + b • I) (a • (1 : ℂ) + b • I) +
      B ((-b) • (1 : ℂ) + a • I) ((-b) • (1 : ℂ) + a • I) = (a ^ 2 + b ^ 2) * (B 1 1 + B I I) := by
    intro a b
    simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : c = c.re • (1 : ℂ) + c.im • I := by
    apply Complex.ext <;> simp
  have hIc : I • c = (-c.im) • (1 : ℂ) + c.re • I := by
    apply Complex.ext <;> simp
  have hn : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hkey := hquad c.re c.im
  rw [← hc, ← hIc, hn] at hkey
  simp only [smul_eq_mul, mul_one] at hkey ⊢
  rw [hkey]
  push_cast
  ring

/-- The inverse uniformizer of the origin fibre is the identity on `𝔻`. -/
theorem s5t53_origin_F {s : ℂ} (hs : s ∈ unitDisc) :
    fiberUniformizer (Quotient.out originT : LinfStarBall) s = s := by
  by_cases h0 : s = 0
  · subst s
    simp [fiberUniformizer]
  · have hw : s⁻¹ ∈ unitDiscExterior := by
      change 1 < ‖s⁻¹‖
      rw [norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp hs⟩
    have h := (s5vc_origin_uniformizer_jet hw).1
    rwa [inv_inv] at h

/-- `K = -log(1 - |s|²)` on the origin fibre, in `tcCoordH`. -/
theorem s5t53_origin_fibre_K {s : ℂ} (hs : s ∈ unitDisc) :
    potentialK (tcCoordHInv ((0 : AInf unitDisc), s)) = -Real.log (1 - ‖s‖ ^ 2) := by
  have hμ := (Quotient.out originT : LinfStarBall).2
  have hc0 : deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 = 0 := by
    have he : fB ((Quotient.out originT : LinfStarBall) : LinfStar) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])] with z hz
      exact s5tg_origin_fB hz
    have hd : deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar)) =ᶠ[𝓝 (0 : ℂ)] fun _ => 1 := by
      filter_upwards [he.eventuallyEq_nhds] with z hz
      rw [hz.deriv_eq, deriv_id]
    rw [hd.deriv_eq, deriv_const]
  set q : T1 × ExtPlane := (originT, inversion (s : ExtPlane)) with hqdef
  have hcond : s = 0 ∨ ∃ w ∈ unitDiscExterior, s = (gMu (Quotient.out originT : LinfStarBall) w)⁻¹ := by
    by_cases h0 : s = 0
    · exact Or.inl h0
    · right
      have hw : s⁻¹ ∈ unitDiscExterior := by
        change 1 < ‖s⁻¹‖
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr h0, mem_ball_zero_iff.mp hs⟩
      exact ⟨s⁻¹, hw, by rw [s5vc_origin_gMu hw, inv_inv]⟩
  have hq : q ∈ TCurve := s5l54_cond_fib hμ hcond
  have hH : tcCoordH q = ((0 : AInf unitDisc), s) := by
    show (bers (Phi ⟨0, mem_ball_self one_pos⟩), finPart (inversion (inversion (s : ExtPlane))) +
      deriv (deriv (fB ((Quotient.out originT : LinfStarBall) : LinfStar))) 0 / 2) = _
    rw [c32_bers_origin, tcc_inversion_invol, hc0, zero_div, add_zero]
    rfl
  have hinv : tcCoordHInv ((0 : AInf unitDisc), s) = q := by
    rw [← hH]
    exact s5rh_injOn.leftInvOn_invFunOn hq
  have hF : fiberUniformizer (Quotient.out originT : LinfStarBall) =ᶠ[𝓝 s] id := by
    filter_upwards [isOpen_ball.mem_nhds hs] with z hz
    exact s5t53_origin_F hz
  have hdF : deriv (fiberUniformizer (Quotient.out originT : LinfStarBall)) s = 1 := by
    rw [hF.deriv_eq, deriv_id]
  have hp : 0 < 1 - ‖s‖ ^ 2 := by
    have hn := mem_ball_zero_iff.mp hs
    nlinarith [norm_nonneg s]
  rw [hinv]
  show logNormSq q / 2 - Real.log 2 = _
  show Real.log (4 * ‖deriv (fiberUniformizer (Quotient.out originT : LinfStarBall))
    (finPart (inversion (inversion (s : ExtPlane))))‖ ^ 2 /
    (1 - ‖fiberUniformizer (Quotient.out originT : LinfStarBall)
      (finPart (inversion (inversion (s : ExtPlane))))‖ ^ 2) ^ 2) / 2 - Real.log 2 = _
  rw [tcc_inversion_invol]
  show Real.log (4 * ‖deriv (fiberUniformizer (Quotient.out originT : LinfStarBall)) s‖ ^ 2 /
    (1 - ‖fiberUniformizer (Quotient.out originT : LinfStarBall) s‖ ^ 2) ^ 2) / 2 - Real.log 2 = _
  rw [hdF, s5t53_origin_F hs, norm_one, one_pow, mul_one, Real.log_div (by norm_num) (by positivity),
    Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- **O1.** The vertical Levi form of `K` at the origin: `Levi_{(0,∞)} K(0, c) = |c|²`. -/
theorem s5t53_origin_vertical (c : ℂ) : leviTC potentialK tOrigin ((0 : AInf unitDisc), c) = ‖c‖ ^ 2 := by
  have hx0 : tcCoordH tOrigin = ((0 : AInf unitDisc), (0 : ℂ)) := by
    have h := s5t53_origin_fibre_K (s := 0) (by simp [unitDisc])
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
  set g : ℂ → ℝ := fun w => -Real.log (1 - ‖w‖ ^ 2) with hgdef
  have hg : ContDiffAt ℝ 2 g 0 := by
    have hq : AnalyticAt ℝ (fun w : ℂ => 1 - ‖w‖ ^ 2) 0 :=
      analyticAt_const.sub (s5fg_norm_sq_analytic analyticAt_id)
    have hlog := (analyticAt_log (show (0 : ℝ) < 1 - ‖(0 : ℂ)‖ ^ 2 by simp)).comp_of_eq hq rfl
    exact hlog.neg.contDiffAt
  have hev : (fun t : ℂ => ((potentialK (tcCoordHInv (tcCoordH tOrigin + t • ((0 : AInf unitDisc), c))) : ℝ) : ℂ))
      =ᶠ[𝓝 0] fun t => ((g (c * t) : ℝ) : ℂ) := by
    have hcont : Continuous fun t : ℂ => c * t := continuous_const.mul continuous_id
    have hmem : ∀ᶠ t in 𝓝 (0 : ℂ), c * t ∈ unitDisc :=
      hcont.continuousAt.eventually_mem (isOpen_ball.mem_nhds (by simp))
    filter_upwards [hmem] with t ht
    have hpt : tcCoordH tOrigin + t • ((0 : AInf unitDisc), c) = ((0 : AInf unitDisc), c * t) := by
      rw [hx0]
      ext <;> simp [mul_comm]
    rw [hpt, s5t53_origin_fibre_K ht]
  have hD : dz (dzbar fun t : ℂ => ((g t : ℝ) : ℂ)) 0 = 1 := by
    have h := s5vc_disk_potential_mixed (z := 0) (by simp [unitDisc])
    have he : (fun t : ℂ => ((g t : ℝ) : ℂ)) = fun w : ℂ => (-Real.log (1 - ‖w‖ ^ 2) : ℂ) := by
      funext w
      simp [hgdef]
    rw [he, h]
    simp
  unfold leviTC
  rw [s5vc_mixed_congr hev, s5t53_levi_scale hg c, hD, mul_one, Complex.ofReal_re]

end TakhtajanTeo
