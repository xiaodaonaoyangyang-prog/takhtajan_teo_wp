import TakhtajanTeo.Ch1.S5VerticalCurvature
import TakhtajanTeo.Ch1.TCurveTopGroup
import TakhtajanTeo.Ch1.S5ConformalFamily
import TakhtajanTeo.Ch1.QCVariation
import TakhtajanTeo.Ch1.TCurveFiberFormula
import TakhtajanTeo.Ch1.S5ExteriorReciprocalFormula
import TakhtajanTeo.Ch1.S5PlaneJets

/-!
# H5a (`s5rh_`, 下属3, Program G): right translations of `𝒯(1)` are holomorphic in `tcCoordH`

Host: new module `TakhtajanTeo/Ch1/S5RightTranslationHol.lean`.
Main results:
- `s5rh_mulInv_holo`: for `a, b ∈ TCurve`, the map `x ↦ x * b⁻¹` in the coordinates `tcCoordH` is ℂ-differentiable
  at `tcCoordH a`;
- `s5rh_right_holo`: the same for `tcurveRight q₀` (lemma_5_4), via `b = tOrigin * q₀⁻¹`.

Route. Write `c(ν) = fB(ν)''(0)/2`, so that `s = 1/z + c` is the memoir coordinate (`tcCoordH`).
1. Representatives: the frozen (1.13)–(1.14) operation can be computed with any representative `ν` of `a.1` and any
   valid extension `G` (`s5rh_mulInv_rep`). This generalizes `tcg_mul_eq_of_extension` from `out` to any `ν`; it is
   the class identity of wall 1.
2. Local coordinates: near `tcCoordH a`, `tcCoordHInv y = ([sec y.1], 1/(y.2 - c(sec y.1)))` with an analytic local
   Bers section `sec` (`s5rh_local_coords`).
3. Base: `ν ↦ λ(ν) = tcurveLambda ν G` is holomorphic and maps the ball to the ball (`s5rh_lambda_holo`), and
   `bersPhi` is holomorphic (`bersPhi_differentiableOn`). `c` descends to classes (`s5rh_c_congr`, from
   `modelA_to_modelB`).
4. Fibre: `(ν, s) ↦ 1/(w^{λ(ν)} G (w^ν)⁻¹(1/(s - c ν))) + c(λ ν)` is jointly ℂ-differentiable (`s5rh_fibre_holo`).
   This is `w_mem^{λ(ν)} ∘ G ∘ (w_mem^ν)⁻¹` in memoir coordinates (H5 scout S3–S6).

Junk branches, all explicit: `λ(ν) ∈ ball` is derived (`s5rh_lambda_holo`, from `tmi_main`); `G` exists
(`tcg_extension_exists`); `b.2 ↦ u ∈ 𝔻* ∪ ∞` (`tcg_parameter_mem`); the fibre point `a.2 ≠ 0`
(`tcc_zero_not_mem`).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC

/-- The memoir shift `c = f''(0)/2` depends only on the class (`modelA_to_modelB`). -/
theorem s5rh_c_congr (μ : LinfStarBall) :
    deriv (deriv (fB ((Quotient.out (Phi μ) : LinfStarBall) : LinfStar))) 0 = deriv (deriv (fB (μ : LinfStar))) 0 := by
  have h : teichSetoid.r (Phi μ).out μ := Quotient.mk_out (s := teichSetoid) μ
  have hD := modelA_to_modelB _ _ h
  have he : fB ((Quotient.out (Phi μ) : LinfStarBall) : LinfStar) =ᶠ[𝓝 (0 : ℂ)] fB (μ : LinfStar) := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])] with z hz
    exact hD z hz
  exact he.deriv.deriv_eq

/-- `tOrigin = (0, ∞)` lies on `𝒯(1)`. -/
theorem s5rh_tOrigin_mem : tOrigin ∈ TCurve := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hclass : teichSetoid (Quotient.out originT : LinfStarBall) ⟨0, h0⟩ :=
    Quotient.exact (Quotient.out_eq originT)
  change extInf ∈ wB (Quotient.out originT : LinfStarBall) '' extDiscExterior
  rw [fiber_independent hclass, s5vc_wB_zero, image_id]
  exact Or.inr rfl

/-- `ν ↦ fB(ν)''(0)` is continuous on `L∞(𝔻*)₁` (`ac2_fpp_seq`). -/
theorem s5rh_c_continuousOn : ContinuousOn (fun ν : LinfStar => deriv (deriv (fB ν)) 0) LinfStarBall := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro x μ₀ hx
  exact AppA.ac2_fpp_seq μ₀.2 (fun n => (x n).2) ((continuous_subtype_val.tendsto _).comp hx)

/-- (1.13)–(1.14) with any representative `ν` of `a.1` and any valid extension `G` for `b`. This generalizes
`tcg_mul_eq_of_extension` (the case `ν = out a.1`). -/
theorem s5rh_mulInv_rep {a b : T1 × ExtPlane} (ha : a ∈ TCurve) (hb : b ∈ TCurve)
    {ν : LinfStar} (hν : ν ∈ LinfStarBall) (hcl : Phi ⟨ν, hν⟩ = a.1) {G : ℂ → ℂ}
    (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere (Quotient.out b.1 : LinfStarBall)) b.2)
          (gammaMu (Quotient.out b.1 : LinfStarBall) z))) unitCircle) :
    ∃ hl : tcurveLambda ν G ∈ LinfStarBall,
      tcurveMulInv a b = (Phi ⟨_, hl⟩, tcurveZ ν G (tcurveLambda ν G) a.2) := by
  -- Route: replace `G` by the normalized extension `G* = e.trans R` (`tcurve_mul_independent`, any `ν`), compute
  -- with GPT's transport lemmas for both representatives `ν` and `ν₀ = out a.1`, and compare: the classes of
  -- `κ_ρ = ρ * ξ⁻¹` agree, so do the Möbius maps `B_ρ` (three points of `f_{κ₀}(𝔻)`), and the welding parameters.
  set μ : LinfStar := ((Quotient.out b.1 : LinfStarBall) : LinfStar) with hμdef
  have hμ : μ ∈ LinfStarBall := (Quotient.out b.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμ hb
  set ν₀ : LinfStar := ((Quotient.out a.1 : LinfStarBall) : LinfStar) with hν₀def
  have hν₀ : ν₀ ∈ LinfStarBall := (Quotient.out a.1 : LinfStarBall).2
  have hrel : teichSetoid (Quotient.out a.1 : LinfStarBall) ⟨ν, hν⟩ :=
    Quotient.exact ((Quotient.out_eq a.1).trans hcl.symm)
  have haν : a.2 ∈ wB ν '' extDiscExterior := by
    have h : a.2 ∈ wB ν₀ '' extDiscExterior := ha
    rwa [fiber_independent hrel] at h
  obtain ⟨hl₀, hres⟩ := tcg_mul_eq_of_extension ha hb hG
  obtain ⟨e, K, ξ, he, heE, heC, heb, hm1, hmI, h1, hξae, -⟩ := tcg_normalized_extension hμ
  obtain ⟨R, KR, hR, hRE, hRD, hRb⟩ := tcg_sigma_extension hu
  have hG' : IsQuasiconformal (⇑(e.trans R)) univ ∧ (e.trans R) '' univ = univ ∧
      EqOn (⇑(e.trans R)) (fun w : ℂ => finPart
        (sigmaSphere (Function.invFun (normalizedWeldingSphere μ) b.2) (gammaMu μ w))) unitCircle := by
    refine ⟨⟨K * KR, ?_⟩, image_univ.trans (e.trans R).surjective.range_eq, ?_⟩
    · change IsKQC ((⇑R) ∘ (⇑e)) univ (K * KR)
      exact thm7_1_comp he hR (subset_univ _)
    · intro w hw
      change R (e w) = _
      rw [heb hw]
      obtain ⟨hγ, hn⟩ := tce_gamma_circle hμ hw
      rw [hRb (show wA μ w ∈ unitCircle from hn)]
      dsimp only
      rw [hγ]
  have hRs : R '' univ = univ := image_univ.trans R.surjective.range_eq
  have hRconf : IsConformalOnto (⇑R) unitDisc unitDisc := tcg_inverse_disk_conformal R.symm hRD
  -- the computation for one representative `ρ` of `a.1`
  have key : ∀ ρ : LinfStar, ρ ∈ LinfStarBall → a.2 ∈ wB ρ '' extDiscExterior →
      ∃ B : ExtPlane → ExtPlane, IsMobius B ∧
        (∀ p, wB (tcurveLambda (beltramiMul ρ (beltramiInv (ξ : LinfStar))) R) (OnePoint.map R p) =
          B (wB (beltramiMul ρ (beltramiInv (ξ : LinfStar))) p)) ∧
        tcurveLambda ρ (e.trans R) = tcurveLambda (beltramiMul ρ (beltramiInv (ξ : LinfStar))) R ∧
        tcurveZ ρ (e.trans R) (tcurveLambda ρ (e.trans R)) a.2 =
          B (normalizedWeldingSphere (beltramiMul ρ (beltramiInv (ξ : LinfStar)))
            (Function.invFun (normalizedWeldingSphere ρ) a.2)) := by
    intro ρ hρ hρa
    have hκ := grp_mul_mem hρ (grp_inv_mem ξ.2)
    have hlaw : tcurveLambda ρ (e.trans R) = tcurveLambda (beltramiMul ρ (beltramiInv (ξ : LinfStar))) R := by
      rw [tcg_lambda_comp hρ e R he hR heE hRE, tcg_lambda_eq_group ξ.2 hρ e he heC hm1 hmI h1 hξae]
    obtain ⟨B, hB, hBR⟩ := tcg_transport_mobius hκ R hR hRE hRD
    refine ⟨B, hB, hBR, hlaw, ?_⟩
    have hmap : OnePoint.map (e.trans R) = (OnePoint.map R) ∘ (OnePoint.map e) := by
      funext v
      induction v using OnePoint.rec <;> rfl
    change wB (tcurveLambda ρ (e.trans R)) (OnePoint.map (e.trans R) (Function.invFun (wB ρ) a.2)) = _
    rw [hlaw, hmap, Function.comp_apply, hBR]
    exact congrArg B (tcg_normalized_fibre_quotient ξ.2 hρ e he heC hm1 hmI h1 hξae hρa)
  obtain ⟨B₁, hB₁, hBR₁, hlaw₁, hz₁⟩ := key ν hν haν
  obtain ⟨B₀, hB₀, hBR₀, hlaw₀, hz₀⟩ := key ν₀ hν₀ ha
  set κ₁ : LinfStar := beltramiMul ν (beltramiInv (ξ : LinfStar)) with hκ₁def
  set κ₀ : LinfStar := beltramiMul ν₀ (beltramiInv (ξ : LinfStar)) with hκ₀def
  have hκ₁ : κ₁ ∈ LinfStarBall := grp_mul_mem hν (grp_inv_mem ξ.2)
  have hκ₀ : κ₀ ∈ LinfStarBall := grp_mul_mem hν₀ (grp_inv_mem ξ.2)
  -- the classes of `κ₁, κ₀` agree
  have hκrel : teichSetoid (⟨κ₁, hκ₁⟩ : LinfStarBall) ⟨κ₀, hκ₀⟩ := by
    apply Quotient.exact
    have e1 := gtp_mulT_phi ⟨ν, hν⟩ ⟨beltramiInv (ξ : LinfStar), grp_inv_mem ξ.2⟩
    have e0 := gtp_mulT_phi (Quotient.out a.1) ⟨beltramiInv (ξ : LinfStar), grp_inv_mem ξ.2⟩
    have ha1 : Phi (⟨ν, hν⟩ : LinfStarBall) = Phi (Quotient.out a.1) :=
      hcl.trans (Quotient.out_eq a.1).symm
    rw [ha1] at e1
    exact e1.symm.trans e0
  -- the classes of `λ(κ₁, R), λ(κ₀, R)` agree (`tcg_lambda_bers`)
  have hL₁ := (tmi_lambda_props hκ₁ hR hRs hRE).1
  have hL₀ := (tmi_lambda_props hκ₀ hR hRs hRE).1
  have hLrel : teichSetoid (⟨tcurveLambda κ₁ R, hL₁⟩ : LinfStarBall) ⟨tcurveLambda κ₀ R, hL₀⟩ := by
    apply Quotient.exact
    apply bers_injective
    show bers (Phi (⟨tcurveLambda κ₁ R, hL₁⟩ : LinfStarBall)) = bers (Phi ⟨tcurveLambda κ₀ R, hL₀⟩)
    rw [bers_Phi, bers_Phi]
    apply AInf.ext_toFun_disc
    intro z hz
    have hb : bersPhi κ₁ = bersPhi κ₀ := by
      have hP : Phi (⟨κ₁, hκ₁⟩ : LinfStarBall) = Phi ⟨κ₀, hκ₀⟩ := Quotient.sound hκrel
      have h := congrArg bers hP
      rwa [bers_Phi, bers_Phi] at h
    show AInf.toFun (bersPhi (tcurveLambda κ₁ R)) z = AInf.toFun (bersPhi (tcurveLambda κ₀ R)) z
    rw [tcg_lambda_bers hκ₁ R hR hRE hRD hz, tcg_lambda_bers hκ₀ R hR hRE hRD hz, hb]
  have hind₁ := tcurve_mul_independent hμ hν hu hG hG'
  have hind₀ := tcurve_mul_independent hμ hν₀ hu hG hG'
  have hl : tcurveLambda ν G ∈ LinfStarBall := (tmi_main hμ hν hu hG hG').1
  refine ⟨hl, ?_⟩
  rw [hres]
  refine Prod.ext ?_ ?_
  · show Phi (⟨tcurveLambda ν₀ G, hl₀⟩ : LinfStarBall) = Phi ⟨tcurveLambda ν G, hl⟩
    refine Quotient.sound (fun z hz => ?_)
    show wA (tcurveLambda ν₀ G) z = wA (tcurveLambda ν G) z
    have hL1 : wA (tcurveLambda κ₁ R) z = wA (tcurveLambda κ₀ R) z := hLrel z hz
    rw [hind₀.1 z hz, hlaw₀, ← hL1, ← hlaw₁, ← hind₁.1 z hz]
  · show tcurveZ ν₀ G (tcurveLambda ν₀ G) a.2 = tcurveZ ν G (tcurveLambda ν G) a.2
    rw [hind₀.2 a.2 ha, hind₁.2 a.2 haν, hz₀, hz₁]
    have hX : Function.invFun (normalizedWeldingSphere ν₀) a.2 =
        Function.invFun (normalizedWeldingSphere ν) a.2 := tcg_parameter_congr hrel ha
    have hXm : Function.invFun (normalizedWeldingSphere ν) a.2 ∈ extDiscExterior := tcg_parameter_mem hν haν
    have hW : normalizedWeldingSphere κ₁ (Function.invFun (normalizedWeldingSphere ν) a.2) =
        normalizedWeldingSphere κ₀ (Function.invFun (normalizedWeldingSphere ν) a.2) :=
      tcg_welding_congr hκrel hXm
    -- the Möbius maps agree at three points of `f_{κ₀}(𝔻)`
    have hpt : ∀ z ∈ unitDisc, B₀ ((fB κ₀ z : ℂ) : ExtPlane) = B₁ ((fB κ₀ z : ℂ) : ExtPlane) := by
      intro z hz
      have h0 := hBR₀ (z : ExtPlane)
      have h1' := hBR₁ (z : ExtPlane)
      change wB (tcurveLambda κ₀ R) ((R z : ℂ) : ExtPlane) = B₀ (wB κ₀ (z : ExtPlane)) at h0
      change wB (tcurveLambda κ₁ R) ((R z : ℂ) : ExtPlane) = B₁ (wB κ₁ (z : ExtPlane)) at h1'
      rw [wB_disc_eq_fB hL₀ (hRconf.mapsTo hz), wB_disc_eq_fB hκ₀ hz] at h0
      rw [wB_disc_eq_fB hL₁ (hRconf.mapsTo hz), wB_disc_eq_fB hκ₁ hz] at h1'
      have hf : fB κ₁ z = fB κ₀ z := (modelA_iff_modelB _ _).mp hκrel z hz
      have hfL : fB (tcurveLambda κ₁ R) (R z) = fB (tcurveLambda κ₀ R) (R z) :=
        (modelA_iff_modelB _ _).mp hLrel (R z) (hRconf.mapsTo hz)
      rw [hf, hfL] at h1'
      exact h0.symm.trans h1'
    have hinj := (fB_holomorphic_injective hκ₀).2
    have hd0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
    have hd1 : (1 / 2 : ℂ) ∈ unitDisc := by
      simp only [unitDisc, mem_ball_zero_iff]; norm_num
    have hd2 : (-1 / 2 : ℂ) ∈ unitDisc := by
      simp only [unitDisc, mem_ball_zero_iff]; norm_num
    have hBB : B₀ = B₁ := mobius_eq_of_three_points hB₀ hB₁
      (fun h => by have := hinj hd0 hd1 h; norm_num at this)
      (fun h => by have := hinj hd0 hd2 h; norm_num at this)
      (fun h => by have := hinj hd1 hd2 h; norm_num at this)
      (hpt 0 hd0) (hpt _ hd1) (hpt _ hd2)
    rw [hX, ← hW, hBB]

/-- Inverse of a plane q.c. homeomorphism preserving `𝔻*` is quasi-measure-preserving on `𝔻*`. -/
theorem s5rh_inv_qmp {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hGs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) :
    Measure.QuasiMeasurePreserving (Function.invFun G) (volume.restrict unitDiscExterior)
      (volume.restrict unitDiscExterior) := by
  obtain ⟨e, he⟩ := t1_homeomorph hK hGs
  have hinvm : Measurable (Function.invFun G) := by
    subst he
    have : Function.invFun (⇑e) = ⇑e.symm := by
      funext y
      apply e.injective
      rw [e.apply_symm_apply]
      exact Function.invFun_eq (e.surjective y)
    rw [this]
    exact e.symm.continuous.measurable
  refine ⟨hinvm, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply hinvm hs]
  have h : ∀ᵐ u ∂(volume.restrict unitDiscExterior), u ∉ s :=
    measure_eq_zero_iff_ae_notMem.mp hs0
  exact measure_eq_zero_iff_ae_notMem.mpr (tmi_ae_pull_inv hK hGs hD h)

/-- Weighted composition `ν ↦ W · (ν ∘ G⁻¹)` is a bounded ℂ-linear operator on `L∞(𝔻*)`. -/
theorem s5rh_comp_op {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hGs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) {W : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hW : AEStronglyMeasurable W (volume.restrict unitDiscExterior))
    (hWb : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖W w‖ ≤ C) :
    ∃ D : LinfStar →L[ℂ] LinfStar, ∀ ν : LinfStar, ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      D ν w = W w * ν (Function.invFun G w) := by
  have hq := s5rh_inv_qmp hK hGs hD
  have hbound : ∀ ν : LinfStar, ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      ‖W w * ν (Function.invFun G w)‖ ≤ C * ‖ν‖ := by
    intro ν
    filter_upwards [tmi_ae_pull_inv hK hGs hD (LinfStar_ae_norm_le ν), hWb] with w hν hw
    rw [norm_mul]
    exact mul_le_mul hw hν (norm_nonneg _) hC
  have hmemLp : ∀ ν : LinfStar, MemLp (fun w => W w * ν (Function.invFun G w)) ∞
      (volume.restrict unitDiscExterior) := fun ν =>
    memLp_top_of_bound (hW.mul ((Lp.aestronglyMeasurable ν).comp_quasiMeasurePreserving hq))
      (C * ‖ν‖) (hbound ν)
  let g : LinfStar → ℂ → ℂ := fun ν w => W w * ν (Function.invFun G w)
  let D0 : LinfStar →ₗ[ℂ] LinfStar :=
    { toFun := fun ν => toLinf (g ν)
      map_add' := by
        intro ν₁ ν₂
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (hmemLp (ν₁ + ν₂)), bc_toLinf_ae (hmemLp ν₁),
          bc_toLinf_ae (hmemLp ν₂), Lp.coeFn_add (toLinf (g ν₁)) (toLinf (g ν₂)),
          tmi_ae_pull_inv hK hGs hD (Lp.coeFn_add ν₁ ν₂)] with z h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h2, h3]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.add_apply]
        ring
      map_smul' := by
        intro c ν
        apply Lp.ext
        filter_upwards [bc_toLinf_ae (hmemLp (c • ν)), bc_toLinf_ae (hmemLp ν),
          Lp.coeFn_smul c (toLinf (g ν)), tmi_ae_pull_inv hK hGs hD (Lp.coeFn_smul c ν)]
          with z h1 h2 h4 h5
        simp only [RingHom.id_apply]
        rw [h4, Pi.smul_apply, h2]
        simp only [g] at h1 ⊢
        rw [h1, h5, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  refine ⟨D0.mkContinuous C (fun ν => ?_), fun ν => ?_⟩
  · exact norm_toLinf_le_of_ae_bound (mul_nonneg hC (norm_nonneg ν)) (hbound ν)
  · exact bc_toLinf_ae (hmemLp ν)

/-- The derivative of `ν ↦ λ(ν) = tcurveLambda ν G` at `l₀`: the `bd_hasFDerivAt` argument with the fixed q.c. map
`G⁻¹` in place of `w_μ`. The Möbius denominators are controlled by `‖μ_G‖ ≤ (K-1)/(K+1) < 1` a.e. (validity of `G`). -/
theorem s5rh_lambda_hasFDerivAt {G : ℂ → ℂ} {K : ℝ} (hK : IsKQC G univ K) (hGs : G '' univ = univ)
    (hD : G '' unitDiscExterior = unitDiscExterior) {l₀ : LinfStar} (hl₀ : l₀ ∈ LinfStarBall) :
    ∃ D : LinfStar →L[ℂ] LinfStar, HasFDerivAt (fun l => tcurveLambda l G) D l₀ := by
  have hs1 := bc_norm_lt_one hl₀
  set s := ‖l₀‖ with hs
  have hs2 : 0 < 1 - s := by linarith
  have hq := s5rh_inv_qmp hK hGs hD
  have hGD : IsKQC G unitDiscExterior K := t3b_isKQC_restrict hK bc_hEo (subset_univ _)
  obtain ⟨-, hk1', hkb⟩ := c36_b_dilatation_bound hGD
  have hPb : ∀ᵐ w ∂(volume.restrict unitDiscExterior),
      ‖complexDilatation G (Function.invFun G w)‖ ≤ 1 := by
    filter_upwards [tmi_ae_pull_inv hK hGs hD hkb] with w hw
    exact hw.trans hk1'.le
  have hTb : ∀ w, ‖dz G (Function.invFun G w) / conj (dz G (Function.invFun G w))‖ ≤ 1 := by
    intro w
    by_cases h0 : dz G (Function.invFun G w) = 0
    · simp [h0]
    · rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr h0)]
  set P : ℂ → ℂ := fun w => complexDilatation G (Function.invFun G w) with hP
  set T : ℂ → ℂ := fun w => dz G (Function.invFun G w) / conj (dz G (Function.invFun G w)) with hT
  have hPm : AEStronglyMeasurable P (volume.restrict unitDiscExterior) :=
    (((measurable_dzbar G).div (measurable_dz G)).aestronglyMeasurable).comp_quasiMeasurePreserving hq
  have hTm : AEStronglyMeasurable T (volume.restrict unitDiscExterior) :=
    (((measurable_dz G).div (Complex.continuous_conj.measurable.comp (measurable_dz G))).aestronglyMeasurable
      ).comp_quasiMeasurePreserving hq
  have hl₀m : AEStronglyMeasurable (fun w => l₀ (Function.invFun G w)) (volume.restrict unitDiscExterior) :=
    (Lp.aestronglyMeasurable l₀).comp_quasiMeasurePreserving hq
  set W : ℂ → ℂ := fun w => (((1 - ‖P w‖ ^ 2 : ℝ)) : ℂ) /
    (1 - conj (P w) * l₀ (Function.invFun G w)) ^ 2 * T w with hW
  have hWm : AEStronglyMeasurable W (volume.restrict unitDiscExterior) := by
    have hnum : AEStronglyMeasurable (fun w => (((1 - ‖P w‖ ^ 2 : ℝ)) : ℂ))
        (volume.restrict unitDiscExterior) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub (hPm.norm.pow 2))
    have hden : AEStronglyMeasurable (fun w => (1 - conj (P w) * l₀ (Function.invFun G w)) ^ 2)
        (volume.restrict unitDiscExterior) :=
      (aestronglyMeasurable_const.sub ((continuous_conj.comp_aestronglyMeasurable hPm).mul hl₀m)).pow 2
    exact ((hnum.aemeasurable.div hden.aemeasurable).aestronglyMeasurable).mul hTm
  have hb0 : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖l₀ (Function.invFun G w)‖ ≤ s :=
    tmi_ae_pull_inv hK hGs hD (LinfStar_ae_norm_le l₀)
  have hden : ∀ w, ‖P w‖ ≤ 1 → ‖l₀ (Function.invFun G w)‖ ≤ s →
      1 - s ≤ ‖1 - conj (P w) * l₀ (Function.invFun G w)‖ := by
    intro w hm hb
    have hm' : ‖-P w‖ ≤ 1 := by rw [norm_neg]; exact hm
    have hd := bd_den_ne hm' hb
    have e : (1 : ℂ) + conj (-P w) * l₀ (Function.invFun G w) = 1 - conj (P w) * l₀ (Function.invFun G w) := by
      rw [map_neg]; ring
    rwa [e] at hd
  have hWb : ∀ᵐ w ∂(volume.restrict unitDiscExterior), ‖W w‖ ≤ 1 / (1 - s) ^ 2 := by
    filter_upwards [hPb, hb0] with w hm hb
    have hd := hden w hm hb
    have hnum : ‖(((1 - ‖P w‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [norm_nonneg (P w)]
    simp only [hW]
    rw [norm_mul, norm_div, norm_pow]
    calc ‖(((1 - ‖P w‖ ^ 2 : ℝ)) : ℂ)‖ / ‖1 - conj (P w) * l₀ (Function.invFun G w)‖ ^ 2 * ‖T w‖
        ≤ 1 / (1 - s) ^ 2 * 1 :=
          mul_le_mul (div_le_div₀ zero_le_one hnum (by positivity) (pow_le_pow_left₀ hs2.le hd 2))
            (hTb w) (norm_nonneg _) (by positivity)
      _ = 1 / (1 - s) ^ 2 := mul_one _
  obtain ⟨D, hDf⟩ := s5rh_comp_op hK hGs hD (by positivity) hWm hWb
  refine ⟨D, ?_⟩
  have hrem : ∀ h : LinfStar, ‖h‖ ≤ (1 - s) / 2 →
      ‖tcurveLambda (l₀ + h) G - tcurveLambda l₀ G - D h‖ ≤ 2 * ‖h‖ ^ 2 / (1 - s) ^ 3 := by
    intro h hh
    have hlh : l₀ + h ∈ LinfStarBall := by
      have : ‖l₀ + h‖ < 1 := by
        have := norm_add_le l₀ h
        linarith
      simpa [LinfStarBall] using this
    refine bc_Lp_norm_le _ (by positivity) ?_
    filter_upwards [(tmi_lambda_props hlh hK hGs hD).2, (tmi_lambda_props hl₀ hK hGs hD).2, hDf h,
      Lp.coeFn_sub (tcurveLambda (l₀ + h) G - tcurveLambda l₀ G) (D h),
      Lp.coeFn_sub (tcurveLambda (l₀ + h) G) (tcurveLambda l₀ G),
      tmi_ae_pull_inv hK hGs hD (Lp.coeFn_add l₀ h), hPb, hb0,
      tmi_ae_pull_inv hK hGs hD (LinfStar_ae_norm_le h)] with w h1 h2 h3 h4 h5 h6 hm hb hbh
    rw [h4, Pi.sub_apply, h5, Pi.sub_apply, h1, h2, h3, h6, Pi.add_apply]
    have hm' : ‖-P w‖ ≤ 1 := by rw [norm_neg]; exact hm
    have key := bd_mobius_taylor (m := -P w) (b := l₀ (Function.invFun G w))
      (h := h (Function.invFun G w)) hm' hb hbh hs1 hh
    rw [norm_neg] at key
    have he : (l₀ (Function.invFun G w) + h (Function.invFun G w) - P w) /
          (1 - conj (P w) * (l₀ (Function.invFun G w) + h (Function.invFun G w))) * T w -
        (l₀ (Function.invFun G w) - P w) / (1 - conj (P w) * l₀ (Function.invFun G w)) * T w -
        W w * h (Function.invFun G w) =
      ((-P w + (l₀ (Function.invFun G w) + h (Function.invFun G w))) /
          (1 + conj (-P w) * (l₀ (Function.invFun G w) + h (Function.invFun G w))) -
        (-P w + l₀ (Function.invFun G w)) / (1 + conj (-P w) * l₀ (Function.invFun G w)) -
        (((1 - ‖P w‖ ^ 2 : ℝ)) : ℂ) * h (Function.invFun G w) /
          (1 + conj (-P w) * l₀ (Function.invFun G w)) ^ 2) * T w := by
      simp only [hW, map_neg]
      ring
    simp only [hP, hT] at he ⊢
    rw [he, norm_mul]
    calc _ ≤ 2 * ‖h (Function.invFun G w)‖ ^ 2 / (1 - s) ^ 3 * 1 :=
          mul_le_mul key (hTb w) (norm_nonneg _) (by positivity)
      _ ≤ 2 * ‖h‖ ^ 2 / (1 - s) ^ 3 := by
          rw [mul_one]
          gcongr
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hev : ∀ᶠ h : LinfStar in nhds 0, ‖h‖ < min ((1 - s) / 2) (c * (1 - s) ^ 3 / 2) := by
    have := Metric.ball_mem_nhds (0 : LinfStar)
      (lt_min (half_pos hs2) (by positivity : 0 < c * (1 - s) ^ 3 / 2))
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  have h1 : ‖h‖ ≤ (1 - s) / 2 := (lt_min_iff.mp hh).1.le
  have h2 : ‖h‖ ≤ c * (1 - s) ^ 3 / 2 := (lt_min_iff.mp hh).2.le
  refine (hrem h h1).trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg h]

/-- For a valid extension `G`, `ν ↦ λ(ν) = tcurveLambda ν G` (the dilatation of `w^ν ∘ G⁻¹`) is holomorphic on
`L∞(𝔻*)₁` and maps it into itself. -/
theorem s5rh_lambda_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle) :
    DifferentiableOn ℂ (fun ν => tcurveLambda ν G) LinfStarBall ∧
      MapsTo (fun ν => tcurveLambda ν G) LinfStarBall LinfStarBall := by
  obtain ⟨K, e, hK, he, hD, -, -⟩ := tmi_G_data hμ hu hG
  refine ⟨fun l₀ hl₀ => ?_, fun ν hν => (tmi_lambda_props hν hK hG.2.1 hD).1⟩
  obtain ⟨D, hDf⟩ := s5rh_lambda_hasFDerivAt hK hG.2.1 hD hl₀
  exact hDf.differentiableAt.differentiableWithinAt

/-- The memoir coordinate in terms of the normalized plane solution `W = W_{extB μ}` (fixing `0, 1, ∞`): for `v` with
`W(v) ≠ 0`, `1/w^μ(v) + f''(0)/2 = W'(0)/W(v) + W''(0)/(2W'(0))`. The welding pole term of `acc_wB_rep` cancels. -/
theorem s5rh_memoir {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {v : ExtPlane}
    (hv : OnePoint.map (normalizedSolution (extB μ)) v ≠ ((0 : ℂ) : ExtPlane)) :
    finPart (inversion (wB μ v)) + deriv (deriv (fB μ)) 0 / 2 =
      deriv (normalizedSolution (extB μ)) 0 * finPart (inversion (OnePoint.map (normalizedSolution (extB μ)) v)) +
        deriv (deriv (normalizedSolution (extB μ))) 0 / (2 * deriv (normalizedSolution (extB μ)) 0) := by
  have hk : ‖μ‖ < 1 := by simpa [LinfStarBall] using hμ
  set W := normalizedSolution (extB μ) with hWdef
  obtain ⟨hd, -, hrep⟩ := AppA.acc_wB_rep hμ
  set d := deriv W 0 with hddef
  set P := finPart (mobiusExt 0 1 1 0 (OnePoint.map W (Function.invFun (wAS μ) extInf))) with hPdef
  obtain ⟨-, hWd, -, hW0⟩ := QCV.qcv_W_props hk
  replace hW0 : W 0 = 0 := hW0
  replace hWd : DifferentiableOn ℂ W unitDisc := hWd
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hx : mobiusExt 0 1 1 0 (OnePoint.map W v) =
      ((finPart (inversion (OnePoint.map W v)) : ℂ) : ExtPlane) :=
    (coe_finPart_of_ne (fun h => hv ((tcc_inversion_eq_inf_iff _).mp h))).symm
  have h1 : inversion (wB μ v) = ((d * (finPart (inversion (OnePoint.map W v)) + -P) : ℂ) : ExtPlane) := by
    rw [hrep v]
    exact s5cf_normalized_mobius_reciprocal hd hx
  have hWc : ContinuousAt W 0 := (hWd.differentiableAt (isOpen_ball.mem_nhds h0)).continuousAt
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), -P * W z + 1 ≠ 0 := by
    have ht : Tendsto (fun z => -P * W z + 1) (𝓝 0) (𝓝 (-P * W 0 + 1)) :=
      (hWc.const_mul _).add_const 1
    rw [hW0, mul_zero, zero_add] at ht
    exact ht.eventually (isOpen_ne.mem_nhds one_ne_zero)
  have hfB : fB μ =ᶠ[𝓝 (0 : ℂ)] fun z => mobiusFn (1 / d) 0 (-P) 1 (W z) := by
    filter_upwards [hne] with z hz
    unfold fB
    rw [hrep]
    change finPart (mobiusExt (1 / d) 0 (-P) 1 ((W z : ℂ) : ExtPlane)) = _
    rw [mobiusExt_coe hz]
    rfl
  have hWa : AnalyticAt ℂ W 0 := hWd.analyticAt (isOpen_ball.mem_nhds h0)
  have hden : -P * W 0 + 1 ≠ 0 := by rw [hW0]; simp
  obtain ⟨-, h2⟩ := mobius_comp_first_second (a := 1 / d) (b := 0) hWa hden
  have he : deriv (deriv (fB μ)) 0 = deriv (deriv (fun z => mobiusFn (1 / d) 0 (-P) 1 (W z))) 0 :=
    hfB.deriv.deriv_eq
  rw [he, h2, h1, hW0]
  change d * (finPart (inversion (OnePoint.map W v)) + -P) + _ = _
  field_simp
  ring

/-- `q ↦ W_q'(0)` is holomorphic on `L∞(𝔻*)₁`. -/
theorem s5rh_jet1_holo :
    DifferentiableOn ℂ (fun q : LinfStar => deriv (normalizedSolution (extB q)) 0) LinfStarBall :=
  fun _ hq => (s5cf_planeB_deriv_analytic hq).differentiableAt.differentiableWithinAt

/-- `q ↦ W_q''(0)` is holomorphic on `L∞(𝔻*)₁`. -/
theorem s5rh_jet2_holo :
    DifferentiableOn ℂ (fun q : LinfStar => deriv (deriv (normalizedSolution (extB q))) 0) LinfStarBall := by
  intro q hq
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have ha := s5cf_planeB_disk_analytic (q, 0) ⟨hq, h0⟩
  have hD : AnalyticAt ℂ (fun x : LinfStar × ℂ => deriv (normalizedSolution (extB x.1)) x.2) (q, 0) := by
    have hEval : AnalyticAt ℂ (fun x : LinfStar × ℂ =>
        fderiv ℂ (fun x : LinfStar × ℂ => normalizedSolution (extB x.1) x.2) x (0, 1)) (q, 0) :=
      ((ContinuousLinearMap.apply ℂ ℂ ((0 : LinfStar), (1 : ℂ))).analyticAt _).comp_of_eq ha.fderiv rfl
    apply hEval.congr
    filter_upwards [ha.eventually_analyticAt] with x hx
    have hh := hx.differentiableAt.hasFDerivAt.comp x.2 (hasFDerivAt_prodMk_right (𝕜 := ℂ) x.1 x.2)
    change fderiv ℂ (fun x : LinfStar × ℂ => normalizedSolution (extB x.1) x.2) x (0, 1) =
      deriv (normalizedSolution (extB x.1)) x.2
    convert! hh.hasDerivAt.deriv.symm using 1
  exact (s5cf_partial_deriv_analytic hD).differentiableAt.differentiableWithinAt

/-- Normalized plane solutions are homeomorphisms of `ℂ`. -/
theorem s5rh_W_homeo {q : LinfStar} (hq : q ∈ LinfStarBall) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution (extB q) := by
  have hk : ‖q‖ < 1 := by simpa [LinfStarBall] using hq
  obtain ⟨⟨⟨K, hK⟩, hs, -⟩, -⟩ := QCV.qcv_W_props hk
  exact t1_homeomorph hK hs

/-- Their sphere extensions are bijections of `ℂ̄`. -/
theorem s5rh_W_map_bij {q : LinfStar} (hq : q ∈ LinfStarBall) :
    Function.Bijective (OnePoint.map (normalizedSolution (extB q))) := by
  obtain ⟨e, he⟩ := s5rh_W_homeo hq
  rw [← he]
  exact e.onePointCongr.bijective

/-- `finPart` is continuous at finite points of `ℂ̄`. -/
theorem s5rh_finPart_contAt {z : ExtPlane} (hz : z ≠ extInf) : ContinuousAt finPart z := by
  induction z using OnePoint.rec with
  | infty => exact absurd rfl hz
  | coe w =>
    show Tendsto finPart (𝓝 (w : ExtPlane)) (𝓝 (finPart (w : ExtPlane)))
    rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq w, tendsto_map'_iff]
    exact tendsto_id

/-- `W_q(v) = 0` only at `v = 0`. -/
theorem s5rh_W_map_eq_zero {q : LinfStar} (hq : q ∈ LinfStarBall) {v : ExtPlane}
    (hv : OnePoint.map (normalizedSolution (extB q)) v = ((0 : ℂ) : ExtPlane)) : v = ((0 : ℂ) : ExtPlane) := by
  have hk : ‖q‖ < 1 := by simpa [LinfStarBall] using hq
  have h0 := (QCV.qcv_W_props hk).2.2.2
  apply (s5rh_W_map_bij hq).1
  rw [hv]
  show ((0 : ℂ) : ExtPlane) = ((normalizedSolution (extB q) 0 : ℂ) : ExtPlane)
  rw [h0]

/-- The plane transition `Ψ_q = W_{λ(q)} ∘ G ∘ W_q⁻¹` is conformal on `W_q(𝔻*)`, with `Ψ_q(W_q y) = W_{λ(q)}(G y)`. -/
theorem s5rh_transition_conformal {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {q : LinfStar} (hq : q ∈ LinfStarBall) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (normalizedSolution (extB q) '' unitDiscExterior) ∧
      ∀ y ∈ unitDiscExterior, Ψ (normalizedSolution (extB q) y) =
        normalizedSolution (extB (tcurveLambda q G)) (G y) := by
  obtain ⟨K, e, hK, he, hD, -, -⟩ := tmi_G_data hμ hu hG
  have hGs := hG.2.1
  have hk : ‖q‖ < 1 := by simpa [LinfStarBall] using hq
  obtain ⟨hlam, hae⟩ := tmi_lambda_props hq hK hGs hD
  have hkl : ‖tcurveLambda q G‖ < 1 := by simpa [LinfStarBall] using hlam
  obtain ⟨⟨⟨KW, hKW⟩, -, -, -, hWae0⟩, -⟩ := QCV.qcv_W_props hk
  obtain ⟨⟨⟨K', hK'⟩, -, -, -, hW'ae⟩, -⟩ := QCV.qcv_W_props hkl
  set W := normalizedSolution (extB q) with hWdef
  set W' := normalizedSolution (extB (tcurveLambda q G)) with hW'def
  have hWae : ∀ᵐ z ∂(volume.restrict unitDiscExterior), complexDilatation W z = q z := by
    filter_upwards [ae_restrict_of_ae hWae0, ae_restrict_mem bc_hEo.measurableSet] with z h hz
    rw [h]
    simp [extB, Set.indicator_of_mem hz]
  have hGD : IsKQC G unitDiscExterior K := t3b_isKQC_restrict hK bc_hEo (subset_univ _)
  have hWD : IsKQC W unitDiscExterior KW := t3b_isKQC_restrict hKW bc_hEo (subset_univ _)
  have hW'D : IsKQC W' unitDiscExterior K' := t3b_isKQC_restrict hK' bc_hEo (subset_univ _)
  have hinv : IsKQC (Function.invFunOn G unitDiscExterior) unitDiscExterior K := by
    have := thm7_2_inv hGD
    rwa [hD] at this
  have hleft : LeftInvOn (Function.invFunOn G unitDiscExterior) G unitDiscExterior :=
    hGD.2.2.1.2.1.leftInvOn_invFunOn
  have hinvimg : Function.invFunOn G unitDiscExterior '' unitDiscExterior = unitDiscExterior := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hD] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hleft hx]
      exact hx
    · intro x hx
      refine ⟨G x, ?_, hleft hx⟩
      rw [← hD]
      exact mem_image_of_mem G hx
  have hh : IsKQC (W ∘ Function.invFunOn G unitDiscExterior) unitDiscExterior (K * KW) :=
    thm7_1_comp hinv hWD hinvimg.le
  have hdil : ∀ᵐ z ∂(volume.restrict unitDiscExterior),
      complexDilatation W' z = complexDilatation (W ∘ Function.invFunOn G unitDiscExterior) z := by
    filter_upwards [ae_restrict_of_ae hW'ae, hae, tmi_dilatation_comp_inv hKW hK hGs hD hWae,
      ae_restrict_mem bc_hEo.measurableSet] with z h1 h2 h3 hzE
    rw [h1, h3]
    simp only [extB, Set.indicator_of_mem hzE]
    exact h2
  have hconf := bg_conformal_of_dilatation_eq hh hW'D hdil
  have himg : (W ∘ Function.invFunOn G unitDiscExterior) '' unitDiscExterior = W '' unitDiscExterior := by
    rw [image_comp, hinvimg]
  rw [himg] at hconf
  refine ⟨W' ∘ Function.invFunOn (W ∘ Function.invFunOn G unitDiscExterior) unitDiscExterior, hconf.1, ?_⟩
  intro y hy
  have hGy : G y ∈ unitDiscExterior := by rw [← hD]; exact mem_image_of_mem G hy
  have e1 : (W ∘ Function.invFunOn G unitDiscExterior) (G y) = W y := by
    simp only [Function.comp_apply, hleft hy]
  have e2 : Function.invFunOn (W ∘ Function.invFunOn G unitDiscExterior) unitDiscExterior (W y) = G y := by
    rw [← e1]
    exact hh.2.2.1.2.1.leftInvOn_invFunOn hGy
  simp only [Function.comp_apply, e2]

/-- `1/w` on finite nonzero points of `ℂ̄`. -/
theorem s5rh_inversion_coe {w : ℂ} (hw : w ≠ 0) : inversion (w : ExtPlane) = ((w⁻¹ : ℂ) : ExtPlane) := by
  unfold inversion
  rw [mobiusExt_coe (by simpa using hw)]
  simp [mobiusFn]

/-- **Joint holomorphy of the reciprocal fibre transition** `ψ_q(t) = 1/W_{λ(q)}(G(W_q⁻¹(1/t)))` (with `ψ_q(0) = 0`)
at every point `(ν₀, t₀)` whose fibre point `W_{ν₀}⁻¹(1/t₀)` lies in `𝔻* ∪ ∞`.
- Spatial holomorphy: `s5rh_transition_conformal` at `t ≠ 0`; removable singularity at `t = 0`.
- Joint continuity of the derivative: Cauchy formula on a common closed disc (`s5cf_cauchy_family_regular`).
- Parameter derivative at fixed `t₀`: moving evaluation (`med_hasFDerivAt_fixed_evaluation`) with
  `A(q) = 1/W_q(y₀)`, `B(q) = 1/W_{λ(q)}(G y₀)`, both holomorphic (`qcv_planeB_differentiableOn`, `s5rh_lambda_holo`).
No quasiconformal inverse is differentiated. -/
theorem s5rh_psi_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {ν₀ : LinfStar} (hν₀ : ν₀ ∈ LinfStarBall) {t₀ : ℂ}
    (ht₀ : Function.invFun (OnePoint.map (normalizedSolution (extB ν₀))) (inversion (t₀ : ExtPlane)) ∈
      extDiscExterior) :
    DifferentiableAt ℂ (fun p : LinfStar × ℂ => finPart (inversion
      (OnePoint.map (normalizedSolution (extB (tcurveLambda p.1 G)))
        (OnePoint.map G (Function.invFun (OnePoint.map (normalizedSolution (extB p.1)))
          (inversion (p.2 : ExtPlane))))))) (ν₀, t₀) := by
  obtain ⟨K, e, hK, he, hD, hCl, -⟩ := tmi_G_data hμ hu hG
  obtain ⟨hLd, hLm⟩ := s5rh_lambda_holo hμ hu hG
  let Y : LinfStar → ℂ → ExtPlane := fun q t =>
    Function.invFun (OnePoint.map (normalizedSolution (extB q))) (inversion (t : ExtPlane))
  let X : LinfStar → ℂ → ExtPlane := fun q t =>
    OnePoint.map (normalizedSolution (extB (tcurveLambda q G))) (OnePoint.map G (Y q t))
  let ψ : LinfStar → ℂ → ℂ := fun q t => finPart (inversion (X q t))
  let Ω : Set (LinfStar × ℂ) := {p | p.1 ∈ LinfStarBall ∧ Y p.1 p.2 ∈ extDiscExterior}
  show DifferentiableAt ℂ (fun p : LinfStar × ℂ => ψ p.1 p.2) (ν₀, t₀)
  have h0ext : ((0 : ℂ) : ExtPlane) ∉ extDiscExterior := by
    rw [fi_extDiscExterior_eq_compl]
    exact fun h => h ⟨0, by simp, rfl⟩
  have hcb : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ e x ∈ closedBall (0 : ℂ) 1 := tmi_cb_iff (he ▸ hCl)
  have hGext : ∀ p ∈ extDiscExterior, OnePoint.map G p ∈ extDiscExterior := by
    intro p hp
    rw [fi_extDiscExterior_eq_compl] at hp ⊢
    exact fun h => hp ((tmi_map_iff hcb p).2 (by simpa [← he] using h))
  have hext_open : IsOpen extDiscExterior := by
    rw [fi_extDiscExterior_eq_compl]
    exact ((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed.isOpen_compl
  have hGmap : Continuous (OnePoint.map G) := by
    rw [← he]
    exact e.onePointCongr.continuous
  have hinvc : ContinuousOn (fun p : LinfStar × ExtPlane =>
      Function.invFun (OnePoint.map (normalizedSolution (extB p.1))) p.2) (LinfStarBall ×ˢ univ) :=
    AppA.acc_inv_cont AppA.acc_WB_cont (fun q hq => s5rh_W_map_bij hq)
  have hinvC : Continuous fun t : ℂ => inversion (t : ExtPlane) :=
    tcc_inversion_continuous.comp OnePoint.continuous_coe
  have hYc : ContinuousOn (fun p : LinfStar × ℂ => Y p.1 p.2) (LinfStarBall ×ˢ univ) :=
    ContinuousOn.comp (g := fun p : LinfStar × ExtPlane =>
        Function.invFun (OnePoint.map (normalizedSolution (extB p.1))) p.2)
      (f := fun p : LinfStar × ℂ => (p.1, inversion (p.2 : ExtPlane))) hinvc
      (continuousOn_fst.prodMk (hinvC.comp_continuousOn continuousOn_snd)) (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hBc : ContinuousOn (fun p : LinfStar × ExtPlane =>
      OnePoint.map (normalizedSolution (extB (tcurveLambda p.1 G))) p.2) (LinfStarBall ×ˢ univ) :=
    ContinuousOn.comp (g := fun p : LinfStar × ExtPlane => OnePoint.map (normalizedSolution (extB p.1)) p.2)
      (f := fun p : LinfStar × ExtPlane => (tcurveLambda p.1 G, p.2)) AppA.acc_WB_cont
      ((hLd.continuousOn.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)
      (fun p hp => ⟨hLm hp.1, mem_univ _⟩)
  have hGY : ContinuousOn (fun p : LinfStar × ℂ => OnePoint.map G (Y p.1 p.2)) (LinfStarBall ×ˢ univ) :=
    ContinuousOn.comp (g := OnePoint.map G) (f := fun p : LinfStar × ℂ => Y p.1 p.2)
      hGmap.continuousOn hYc (fun _ _ => mem_univ _)
  have hXc : ContinuousOn (fun p : LinfStar × ℂ => X p.1 p.2) (LinfStarBall ×ˢ univ) :=
    ContinuousOn.comp (g := fun p : LinfStar × ExtPlane =>
        OnePoint.map (normalizedSolution (extB (tcurveLambda p.1 G))) p.2)
      (f := fun p : LinfStar × ℂ => (p.1, OnePoint.map G (Y p.1 p.2))) hBc
      (continuousOn_fst.prodMk hGY) (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hX0 : ∀ p ∈ Ω, X p.1 p.2 ≠ ((0 : ℂ) : ExtPlane) := by
    intro p hp h0
    have h1 := s5rh_W_map_eq_zero (hLm hp.1) h0
    have h2 := hGext _ hp.2
    rw [h1] at h2
    exact h0ext h2
  have hψc : ∀ p ∈ Ω, ContinuousAt (fun p : LinfStar × ℂ => ψ p.1 p.2) p := by
    intro p hp
    have hXa : ContinuousAt (fun p : LinfStar × ℂ => X p.1 p.2) p :=
      hXc.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hp.1, mem_univ _⟩)
    have hne : inversion (X p.1 p.2) ≠ extInf := fun h => hX0 p hp ((tcc_inversion_eq_inf_iff _).mp h)
    exact ContinuousAt.comp (g := finPart) (f := fun p : LinfStar × ℂ => inversion (X p.1 p.2))
      (s5rh_finPart_contAt hne)
      (ContinuousAt.comp (g := inversion) (f := fun p : LinfStar × ℂ => X p.1 p.2)
        tcc_inversion_continuous.continuousAt hXa)
  have hΩo : IsOpen Ω := by
    have h := hYc.isOpen_inter_preimage (isOpen_ball.prod isOpen_univ) hext_open
    convert h using 1
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, mem_univ _⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  -- spatial holomorphy away from `t = 0`
  have hsp_ne : ∀ p ∈ Ω, p.2 ≠ 0 → DifferentiableAt ℂ (ψ p.1) p.2 := by
    rintro ⟨q, t⟩ ⟨hq, hy⟩ ht
    obtain ⟨Ψ, hΨd, hΨ⟩ := s5rh_transition_conformal hμ hu hG hq
    obtain ⟨eq, heq⟩ := s5rh_W_homeo hq
    have hk : ‖q‖ < 1 := by simpa [LinfStarBall] using hq
    have hkl : ‖tcurveLambda q G‖ < 1 := by simpa [LinfStarBall] using hLm hq
    obtain ⟨-, -, hWinj, hW0⟩ := QCV.qcv_W_props hkl
    have hO : IsOpen (normalizedSolution (extB q) '' unitDiscExterior) := by
      rw [← heq]
      exact eq.isOpenMap _ bc_hEo
    have hval : ∀ t' : ℂ, ∀ x ∈ unitDiscExterior, t'⁻¹ = normalizedSolution (extB q) x → t' ≠ 0 →
        ψ q t' = (Ψ t'⁻¹)⁻¹ := by
      intro t' x hx hxe ht'
      have h1 : inversion (t' : ExtPlane) = OnePoint.map (normalizedSolution (extB q)) (x : ExtPlane) := by
        rw [s5rh_inversion_coe ht', hxe]
        rfl
      have h2 : Y q t' = (x : ExtPlane) := by
        show Function.invFun (OnePoint.map (normalizedSolution (extB q))) (inversion (t' : ExtPlane)) = _
        rw [h1]
        exact Function.leftInverse_invFun (s5rh_W_map_bij hq).1 _
      have hGx : G x ∈ unitDiscExterior := by rw [← hD]; exact mem_image_of_mem G hx
      have hGx0 : G x ≠ 0 := fun h => by rw [h] at hGx; norm_num [unitDiscExterior] at hGx
      have hWne : normalizedSolution (extB (tcurveLambda q G)) (G x) ≠ 0 := by
        intro h
        apply hGx0
        apply hWinj (mem_univ _) (mem_univ _)
        rw [h, hW0]
      have hΨx : Ψ t'⁻¹ = normalizedSolution (extB (tcurveLambda q G)) (G x) := by
        rw [hxe]
        exact hΨ x hx
      show finPart (inversion (OnePoint.map _ (OnePoint.map G (Y q t')))) = _
      rw [h2, hΨx]
      show finPart (inversion ((normalizedSolution (extB (tcurveLambda q G)) (G x) : ℂ) : ExtPlane)) = _
      rw [s5rh_inversion_coe hWne]
      rfl
    -- `t⁻¹ ∈ W_q(𝔻*)`
    have hmem : ∀ t' : ℂ, t' ≠ 0 → Y q t' ∈ extDiscExterior →
        ∃ x ∈ unitDiscExterior, t'⁻¹ = normalizedSolution (extB q) x := by
      intro t' ht' hy'
      obtain ⟨v, hv⟩ := (s5rh_W_map_bij hq).2 (((t'⁻¹ : ℂ)) : ExtPlane)
      have hYv : Y q t' = v := by
        show Function.invFun (OnePoint.map (normalizedSolution (extB q))) (inversion (t' : ExtPlane)) = v
        rw [s5rh_inversion_coe ht', ← hv]
        exact Function.leftInverse_invFun (s5rh_W_map_bij hq).1 v
      rw [hYv] at hy'
      rcases hy' with ⟨x, hx, rfl⟩ | hinf
      · exact ⟨x, hx, (OnePoint.coe_injective hv).symm⟩
      · rw [hinf] at hv
        exact absurd hv.symm (OnePoint.coe_ne_infty _)
    obtain ⟨x₀, hx₀, hx₀e⟩ := hmem t ht hy
    have hOt : t⁻¹ ∈ normalizedSolution (extB q) '' unitDiscExterior := ⟨x₀, hx₀, hx₀e.symm⟩
    have hΨ0 : Ψ t⁻¹ ≠ 0 := by
      have hv := hval t x₀ hx₀ hx₀e ht
      intro h0
      have hGx : G x₀ ∈ unitDiscExterior := by rw [← hD]; exact mem_image_of_mem G hx₀
      have hGx0 : G x₀ ≠ 0 := fun h => by rw [h] at hGx; norm_num [unitDiscExterior] at hGx
      apply hGx0
      apply hWinj (mem_univ _) (mem_univ _)
      rw [hW0, ← hΨ x₀ hx₀, ← hx₀e, h0]
    have hd : DifferentiableAt ℂ (fun t' : ℂ => (Ψ t'⁻¹)⁻¹) t :=
      ((hΨd.differentiableAt (hO.mem_nhds hOt)).comp t (differentiableAt_inv ht)).inv hΨ0
    refine hd.congr_of_eventuallyEq ?_
    have hnear : ∀ᶠ t' in 𝓝 t, t' ≠ 0 ∧ (q, t') ∈ Ω := by
      have h1 : ∀ᶠ t' in 𝓝 t, t' ≠ 0 := isOpen_ne.mem_nhds ht
      have h2 : ∀ᶠ t' in 𝓝 t, (q, t') ∈ Ω :=
        (Continuous.prodMk continuous_const continuous_id).continuousAt.preimage_mem_nhds
          (hΩo.mem_nhds ⟨hq, hy⟩)
      filter_upwards [h1, h2] with t' h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hnear] with t' ht'
    obtain ⟨x, hx, hxe⟩ := hmem t' ht'.1 ht'.2.2
    exact hval t' x hx hxe ht'.1
  -- spatial holomorphy including `t = 0` (removable singularity)
  have hsp : ∀ p ∈ Ω, DifferentiableAt ℂ (ψ p.1) p.2 := by
    rintro ⟨q, t⟩ hp
    by_cases ht : t = 0
    · subst ht
      have hsl : IsOpen {t : ℂ | (q, t) ∈ Ω} := hΩo.preimage (Continuous.prodMk continuous_const continuous_id)
      obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hsl 0 hp
      have hdiff : DifferentiableOn ℂ (ψ q) (ball (0 : ℂ) r \ {0}) := fun t ht' =>
        (hsp_ne (q, t) (hrΩ ht'.1) ht'.2).differentiableWithinAt
      have hcont : ContinuousAt (ψ q) 0 :=
        ContinuousAt.comp (f := fun t : ℂ => (q, t)) (g := fun p : LinfStar × ℂ => ψ p.1 p.2) (hψc (q, 0) hp)
          (Continuous.prodMk continuous_const continuous_id).continuousAt
      have h := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 hr)).mp
        ⟨hdiff, hcont⟩
      exact h.differentiableAt (ball_mem_nhds 0 hr)
    · exact hsp_ne (q, t) hp ht
  -- a common closed disc and the Cauchy estimate
  have hp0 : (ν₀, t₀) ∈ Ω := ⟨hν₀, ht₀⟩
  obtain ⟨r, hr, hrΩ⟩ : ∃ r > 0, closedBall t₀ r ⊆ {t | (ν₀, t) ∈ Ω} := by
    obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp
      (hΩo.preimage (Continuous.prodMk continuous_const continuous_id)) t₀ hp0
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans h⟩
  set S : Set LinfStar := {q | ∀ t ∈ closedBall t₀ r, (q, t) ∈ Ω} with hS
  have hSn : S ∈ 𝓝 ν₀ :=
    (isCompact_closedBall t₀ r).eventually_forall_of_forall_eventually fun t ht => hΩo.mem_nhds (hrΩ ht)
  have hcauchy := s5cf_cauchy_family_regular (S := S) (F := ψ) (c := t₀) hr
    (fun p hp => (hψc p (hp.1 p.2 (sphere_subset_closedBall hp.2))).continuousWithinAt)
    (fun q hq t ht => (hsp (q, t) (hq t ht)).continuousAt.continuousWithinAt)
    (fun q hq t ht => (hsp (q, t) (hq t (ball_subset_closedBall ht))).differentiableWithinAt)
  have hDc : ContinuousAt (fun p : LinfStar × ℂ => deriv (ψ p.1) p.2) (ν₀, t₀) :=
    hcauchy.2.continuousAt (prod_mem_nhds hSn (ball_mem_nhds t₀ hr))
  -- the parameter derivative at the fixed coordinate `t₀`
  set U := interior S with hUdef
  have hU : IsOpen U := isOpen_interior
  have hν₀U : ν₀ ∈ U := mem_interior_iff_mem_nhds.mpr hSn
  have hT : ∀ q ∈ U, DifferentiableOn ℂ (ψ q) (ball t₀ r) := fun q hq t ht =>
    (hsp (q, t) (interior_subset hq t (ball_subset_closedBall ht))).differentiableWithinAt
  set y₀ : ExtPlane := Y ν₀ t₀ with hy₀
  have hy₀0 : y₀ ≠ ((0 : ℂ) : ExtPlane) := fun h => h0ext (h ▸ ht₀)
  let A : LinfStar → ℂ := fun q => finPart (inversion (OnePoint.map (normalizedSolution (extB q)) y₀))
  let B : LinfStar → ℂ := fun q =>
    finPart (inversion (OnePoint.map (normalizedSolution (extB (tcurveLambda q G))) (OnePoint.map G y₀)))
  have hA0 : A ν₀ = t₀ := by
    have h1 : OnePoint.map (normalizedSolution (extB ν₀)) y₀ = inversion (t₀ : ExtPlane) :=
      Function.invFun_eq ((s5rh_W_map_bij hν₀).2 _)
    show finPart (inversion (OnePoint.map _ y₀)) = t₀
    rw [h1, tcc_inversion_invol]
    rfl
  have hAB : ∀ q ∈ LinfStarBall, ψ q (A q) = B q := by
    intro q hq
    have hne : OnePoint.map (normalizedSolution (extB q)) y₀ ≠ ((0 : ℂ) : ExtPlane) := fun h =>
      hy₀0 (s5rh_W_map_eq_zero hq h)
    have h1 : inversion ((A q : ℂ) : ExtPlane) = OnePoint.map (normalizedSolution (extB q)) y₀ := by
      show inversion ((finPart (inversion (OnePoint.map _ y₀)) : ℂ) : ExtPlane) = _
      rw [coe_finPart_of_ne (fun h => hne ((tcc_inversion_eq_inf_iff _).mp h)), tcc_inversion_invol]
    show finPart (inversion (OnePoint.map _ (OnePoint.map G
      (Function.invFun (OnePoint.map (normalizedSolution (extB q))) (inversion ((A q : ℂ) : ExtPlane)))))) = B q
    rw [h1, Function.leftInverse_invFun (s5rh_W_map_bij hq).1]
  have hinf0 : inversion extInf = ((0 : ℂ) : ExtPlane) := by
    rw [← (tcc_inversion_eq_inf_iff ((0 : ℂ) : ExtPlane)).mpr rfl, tcc_inversion_invol]
  have hABd : DifferentiableAt ℂ A ν₀ ∧ DifferentiableAt ℂ B ν₀ := by
    rcases ht₀ with ⟨y, hy, hyy⟩ | hinf
    · -- a finite fibre point `y ∈ 𝔻*`
      have hy₀e : y₀ = (y : ExtPlane) := hyy.symm
      have hy0 : y ≠ 0 := fun h => by rw [h] at hy; norm_num [unitDiscExterior] at hy
      have hGy : G y ∈ unitDiscExterior := by rw [← hD]; exact mem_image_of_mem G hy
      have hGy0 : G y ≠ 0 := fun h => by rw [h] at hGy; norm_num [unitDiscExterior] at hGy
      have hWne : ∀ q ∈ LinfStarBall, ∀ z : ℂ, z ≠ 0 → normalizedSolution (extB q) z ≠ 0 := by
        intro q hq z hz h
        have hk : ‖q‖ < 1 := by simpa [LinfStarBall] using hq
        obtain ⟨-, -, hinj, h0⟩ := QCV.qcv_W_props hk
        exact hz (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
      have hAe : A =ᶠ[𝓝 ν₀] fun q => (normalizedSolution (extB q) y)⁻¹ := by
        filter_upwards [isOpen_ball.mem_nhds hν₀] with q hq
        show finPart (inversion (OnePoint.map _ y₀)) = _
        rw [hy₀e]
        show finPart (inversion ((normalizedSolution (extB q) y : ℂ) : ExtPlane)) = _
        rw [s5rh_inversion_coe (hWne q hq y hy0)]
        rfl
      have hBe : B =ᶠ[𝓝 ν₀] fun q => (normalizedSolution (extB (tcurveLambda q G)) (G y))⁻¹ := by
        filter_upwards [isOpen_ball.mem_nhds hν₀] with q hq
        show finPart (inversion (OnePoint.map _ (OnePoint.map G y₀))) = _
        rw [hy₀e]
        show finPart (inversion ((normalizedSolution (extB (tcurveLambda q G)) (G y) : ℂ) : ExtPlane)) = _
        rw [s5rh_inversion_coe (hWne _ (hLm hq) (G y) hGy0)]
        rfl
      refine ⟨?_, ?_⟩
      · refine DifferentiableAt.congr_of_eventuallyEq ?_ hAe
        exact ((QCV.qcv_planeB_differentiableOn y).differentiableAt (isOpen_ball.mem_nhds hν₀)).inv
          (hWne ν₀ hν₀ y hy0)
      · refine DifferentiableAt.congr_of_eventuallyEq ?_ hBe
        have hc := DifferentiableAt.comp (g := fun κ : LinfStar => normalizedSolution (extB κ) (G y))
          (f := fun q => tcurveLambda q G) ν₀
          ((QCV.qcv_planeB_differentiableOn (G y)).differentiableAt (isOpen_ball.mem_nhds (hLm hν₀)))
          (hLd.differentiableAt (isOpen_ball.mem_nhds hν₀))
        exact hc.inv (hWne _ (hLm hν₀) (G y) hGy0)
    · -- the fibre point `∞`: both maps are identically `0`
      have hy₀e : y₀ = extInf := hinf
      have hA : A = fun _ => 0 := by
        funext q
        show finPart (inversion (OnePoint.map _ y₀)) = 0
        rw [hy₀e]
        show finPart (inversion extInf) = 0
        rw [hinf0]
        rfl
      have hB : B = fun _ => 0 := by
        funext q
        show finPart (inversion (OnePoint.map _ (OnePoint.map G y₀))) = 0
        rw [hy₀e]
        show finPart (inversion extInf) = 0
        rw [hinf0]
        rfl
      rw [hA, hB]
      exact ⟨differentiableAt_const _, differentiableAt_const _⟩
  have hBf : HasFDerivAt (fun q => ψ q (A q)) (fderiv ℂ B ν₀) ν₀ := by
    refine hABd.2.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hν₀] with q hq
    exact hAB q hq
  have hA0V : A ν₀ ∈ ball t₀ r := by rw [hA0]; exact mem_ball_self hr
  have hDc' : ContinuousAt (fun p : LinfStar × ℂ => deriv (ψ p.1) p.2) (ν₀, A ν₀) := by
    rw [hA0]; exact hDc
  have hmed := med_hasFDerivAt_fixed_evaluation hU hν₀U isOpen_ball hA0V hT hDc' hABd.1.hasFDerivAt hBf
  rw [hA0] at hmed
  exact s5cf_joint_differentiableAt hU hν₀U isOpen_ball (mem_ball_self hr) hT hDc hmed.differentiableAt

/-- The memoir coordinate `s` of a fibre point `y` (`w^q(y) = 1/(s - c_q)`) gives the reciprocal plane coordinate
`t = (s - b_q)/a_q = 1/W_q(y)`, `a_q = W_q'(0)`, `b_q = W_q''(0)/(2a_q)`. -/
theorem s5rh_coord_identity {q : LinfStar} (hq : q ∈ LinfStarBall) {s : ℂ} {y : ExtPlane}
    (hy : y ∈ extDiscExterior)
    (hz : wB q y = inversion ((s - deriv (deriv (fB q)) 0 / 2 : ℂ) : ExtPlane)) :
    Function.invFun (OnePoint.map (normalizedSolution (extB q)))
      (inversion (((s - deriv (deriv (normalizedSolution (extB q))) 0 / (2 * deriv (normalizedSolution (extB q)) 0)) /
        deriv (normalizedSolution (extB q)) 0 : ℂ) : ExtPlane)) = y := by
  have hy0 : y ≠ ((0 : ℂ) : ExtPlane) := by
    rintro rfl
    rw [fi_extDiscExterior_eq_compl] at hy
    exact hy ⟨0, by simp, rfl⟩
  have hne : OnePoint.map (normalizedSolution (extB q)) y ≠ ((0 : ℂ) : ExtPlane) := fun h =>
    hy0 (s5rh_W_map_eq_zero hq h)
  have hd := s5cf_planeB_deriv_ne_zero hq
  have hm := s5rh_memoir hq hne
  rw [hz, tcc_inversion_invol] at hm
  have hfin : inversion (OnePoint.map (normalizedSolution (extB q)) y) =
      ((finPart (inversion (OnePoint.map (normalizedSolution (extB q)) y)) : ℂ) : ExtPlane) :=
    (coe_finPart_of_ne (fun h => hne ((tcc_inversion_eq_inf_iff _).mp h))).symm
  have hT : (s - deriv (deriv (normalizedSolution (extB q))) 0 / (2 * deriv (normalizedSolution (extB q)) 0)) /
      deriv (normalizedSolution (extB q)) 0 = finPart (inversion (OnePoint.map (normalizedSolution (extB q)) y)) := by
    change (s - deriv (deriv (fB q)) 0 / 2) + deriv (deriv (fB q)) 0 / 2 = _ at hm
    rw [sub_add_cancel] at hm
    rw [hm]
    field_simp
    ring
  rw [hT, ← hfin, tcc_inversion_invol]
  exact Function.leftInverse_invFun (s5rh_W_map_bij hq).1 y

/-- The fibre part of `x ↦ x * b⁻¹` in memoir coordinates: with `c(ν) = fB(ν)''(0)/2`, the map
`(ν, s) ↦ 1/w^{λ(ν)}(G((w^ν)⁻¹(1/(s - c ν)))) + c(λ ν)` is jointly ℂ-differentiable at every fibre point.
It is `w_mem^{λ(ν)} ∘ G ∘ (w_mem^ν)⁻¹` in `s_mem = 1/z_mem`. -/
theorem s5rh_fibre_holo {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {u : ExtPlane} (hu : u ∈ extDiscExterior)
    {G : ℂ → ℂ} (hG : IsQuasiconformal G univ ∧ G '' univ = univ ∧
      EqOn G (fun z : ℂ => finPart (sigmaSphere u (gammaMu μ z))) unitCircle)
    {ν₀ : LinfStar} (hν₀ : ν₀ ∈ LinfStarBall) {s₀ : ℂ}
    (hs₀ : inversion ((s₀ - deriv (deriv (fB ν₀)) 0 / 2 : ℂ) : ExtPlane) ∈ wB ν₀ '' extDiscExterior) :
    DifferentiableAt ℂ (fun p : LinfStar × ℂ =>
      finPart (inversion (tcurveZ p.1 G (tcurveLambda p.1 G)
        (inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane)))) +
        deriv (deriv (fB (tcurveLambda p.1 G))) 0 / 2) (ν₀, s₀) := by
  -- Route: near `(ν₀, s₀)` the map is `a_{λ q} ψ_q((s - b_q)/a_q) + b_{λ q}` (`s5rh_memoir`, `s5rh_coord_identity`),
  -- with `a = W'(0)`, `b = W''(0)/(2W'(0))` holomorphic (`s5rh_jet*_holo`) and `ψ` jointly holomorphic (`s5rh_psi_holo`).
  obtain ⟨hLd, hLm⟩ := s5rh_lambda_holo hμ hu hG
  obtain ⟨K, e, hK, he, hD, hCl, -⟩ := tmi_G_data hμ hu hG
  have hcb : ∀ x : ℂ, x ∈ closedBall (0 : ℂ) 1 ↔ e x ∈ closedBall (0 : ℂ) 1 := tmi_cb_iff (he ▸ hCl)
  have hGext : ∀ p ∈ extDiscExterior, OnePoint.map G p ∈ extDiscExterior := by
    intro p hp
    rw [fi_extDiscExterior_eq_compl] at hp ⊢
    exact fun h => hp ((tmi_map_iff hcb p).2 (by simpa [← he] using h))
  have h0ext : ((0 : ℂ) : ExtPlane) ∉ extDiscExterior := by
    rw [fi_extDiscExterior_eq_compl]
    exact fun h => h ⟨0, by simp, rfl⟩
  have hd0 := s5cf_planeB_deriv_ne_zero hν₀
  have hdl0 := s5cf_planeB_deriv_ne_zero (hLm hν₀)
  obtain ⟨y₀, hy₀, hy₀z⟩ := hs₀
  have ht₀ := s5rh_coord_identity hν₀ hy₀ hy₀z
  have hmem : Function.invFun (OnePoint.map (normalizedSolution (extB ν₀)))
      (inversion (((s₀ - deriv (deriv (normalizedSolution (extB ν₀))) 0 /
        (2 * deriv (normalizedSolution (extB ν₀)) 0)) / deriv (normalizedSolution (extB ν₀)) 0 : ℂ) : ExtPlane)) ∈
      extDiscExterior := by
    rw [ht₀]
    exact hy₀
  have hψ := s5rh_psi_holo hμ hu hG hν₀ hmem
  -- the holomorphic model
  have hj1 : DifferentiableAt ℂ (fun q : LinfStar => deriv (normalizedSolution (extB q)) 0) ν₀ :=
    s5rh_jet1_holo.differentiableAt (isOpen_ball.mem_nhds hν₀)
  have hj2 : DifferentiableAt ℂ (fun q : LinfStar => deriv (deriv (normalizedSolution (extB q))) 0) ν₀ :=
    s5rh_jet2_holo.differentiableAt (isOpen_ball.mem_nhds hν₀)
  have hj1l : DifferentiableAt ℂ (fun q : LinfStar => deriv (normalizedSolution (extB q)) 0) (tcurveLambda ν₀ G) :=
    s5rh_jet1_holo.differentiableAt (isOpen_ball.mem_nhds (hLm hν₀))
  have hj2l : DifferentiableAt ℂ (fun q : LinfStar => deriv (deriv (normalizedSolution (extB q))) 0)
      (tcurveLambda ν₀ G) :=
    s5rh_jet2_holo.differentiableAt (isOpen_ball.mem_nhds (hLm hν₀))
  have hL0 : DifferentiableAt ℂ (fun q : LinfStar => tcurveLambda q G) ν₀ :=
    hLd.differentiableAt (isOpen_ball.mem_nhds hν₀)
  have hfst : DifferentiableAt ℂ (fun p : LinfStar × ℂ => p.1) (ν₀, s₀) := differentiableAt_fst
  have ha1 : DifferentiableAt ℂ (fun p : LinfStar × ℂ => deriv (normalizedSolution (extB p.1)) 0) (ν₀, s₀) :=
    DifferentiableAt.comp (g := fun q : LinfStar => deriv (normalizedSolution (extB q)) 0)
      (f := fun p : LinfStar × ℂ => p.1) (ν₀, s₀) hj1 hfst
  have ha2 : DifferentiableAt ℂ (fun p : LinfStar × ℂ => deriv (deriv (normalizedSolution (extB p.1))) 0)
      (ν₀, s₀) :=
    DifferentiableAt.comp (g := fun q : LinfStar => deriv (deriv (normalizedSolution (extB q))) 0)
      (f := fun p : LinfStar × ℂ => p.1) (ν₀, s₀) hj2 hfst
  have hlam : DifferentiableAt ℂ (fun p : LinfStar × ℂ => tcurveLambda p.1 G) (ν₀, s₀) :=
    DifferentiableAt.comp (g := fun q : LinfStar => tcurveLambda q G) (f := fun p : LinfStar × ℂ => p.1)
      (ν₀, s₀) hL0 hfst
  have hl1 : DifferentiableAt ℂ (fun p : LinfStar × ℂ =>
      deriv (normalizedSolution (extB (tcurveLambda p.1 G))) 0) (ν₀, s₀) :=
    DifferentiableAt.comp (g := fun q : LinfStar => deriv (normalizedSolution (extB q)) 0)
      (f := fun p : LinfStar × ℂ => tcurveLambda p.1 G) (ν₀, s₀) hj1l hlam
  have hl2 : DifferentiableAt ℂ (fun p : LinfStar × ℂ =>
      deriv (deriv (normalizedSolution (extB (tcurveLambda p.1 G)))) 0) (ν₀, s₀) :=
    DifferentiableAt.comp (g := fun q : LinfStar => deriv (deriv (normalizedSolution (extB q))) 0)
      (f := fun p : LinfStar × ℂ => tcurveLambda p.1 G) (ν₀, s₀) hj2l hlam
  have hg : DifferentiableAt ℂ (fun p : LinfStar × ℂ => (p.1, (p.2 - deriv (deriv (normalizedSolution (extB p.1))) 0 /
      (2 * deriv (normalizedSolution (extB p.1)) 0)) / deriv (normalizedSolution (extB p.1)) 0)) (ν₀, s₀) :=
    by
      have hq2 : DifferentiableAt ℂ (fun p : LinfStar × ℂ => deriv (deriv (normalizedSolution (extB p.1))) 0 /
          (2 * deriv (normalizedSolution (extB p.1)) 0)) (ν₀, s₀) :=
        by simpa only [div_eq_mul_inv] using ha2.fun_mul ((ha1.const_mul 2).fun_inv (mul_ne_zero two_ne_zero hd0))
      have hq3 : DifferentiableAt ℂ (fun p : LinfStar × ℂ => p.2 - deriv (deriv (normalizedSolution (extB p.1))) 0 /
          (2 * deriv (normalizedSolution (extB p.1)) 0)) (ν₀, s₀) :=
        differentiableAt_snd.fun_sub hq2
      have hq4 : DifferentiableAt ℂ (fun p : LinfStar × ℂ => (p.2 - deriv (deriv (normalizedSolution (extB p.1))) 0 /
          (2 * deriv (normalizedSolution (extB p.1)) 0)) / deriv (normalizedSolution (extB p.1)) 0) (ν₀, s₀) :=
        by simpa only [div_eq_mul_inv] using hq3.fun_mul (ha1.fun_inv hd0)
      exact hfst.prodMk hq4
  have hψg := DifferentiableAt.comp (g := fun p : LinfStar × ℂ => finPart (inversion
      (OnePoint.map (normalizedSolution (extB (tcurveLambda p.1 G)))
        (OnePoint.map G (Function.invFun (OnePoint.map (normalizedSolution (extB p.1)))
          (inversion (p.2 : ExtPlane)))))))
    (f := fun p : LinfStar × ℂ => (p.1, (p.2 - deriv (deriv (normalizedSolution (extB p.1))) 0 /
      (2 * deriv (normalizedSolution (extB p.1)) 0)) / deriv (normalizedSolution (extB p.1)) 0)) (ν₀, s₀) hψ hg
  have hl3 : DifferentiableAt ℂ (fun p : LinfStar × ℂ =>
      deriv (deriv (normalizedSolution (extB (tcurveLambda p.1 G)))) 0 /
        (2 * deriv (normalizedSolution (extB (tcurveLambda p.1 G))) 0)) (ν₀, s₀) :=
    by simpa only [div_eq_mul_inv] using hl2.fun_mul ((hl1.const_mul 2).fun_inv (mul_ne_zero two_ne_zero hdl0))
  have hR := (hl1.fun_mul hψg).fun_add hl3
  refine hR.congr_of_eventuallyEq ?_
  -- the coordinate map agrees with the model near `(ν₀, s₀)`
  have hc0 : ContinuousAt (fun q : LinfStar => deriv (deriv (fB q)) 0 / 2) ν₀ :=
    (s5rh_c_continuousOn.continuousAt (isOpen_ball.mem_nhds hν₀)).div_const 2
  have hcont : ContinuousAt (fun p : LinfStar × ℂ =>
      (p.1, inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane))) (ν₀, s₀) := by
    refine continuousAt_fst.prodMk ?_
    exact ContinuousAt.comp (g := fun t : ℂ => inversion (t : ExtPlane))
      (f := fun p : LinfStar × ℂ => p.2 - deriv (deriv (fB p.1)) 0 / 2)
      (tcc_inversion_continuous.comp OnePoint.continuous_coe).continuousAt
      (continuousAt_snd.sub (ContinuousAt.comp (g := fun q : LinfStar => deriv (deriv (fB q)) 0 / 2)
        (f := fun p : LinfStar × ℂ => p.1) hc0 continuousAt_fst))
  have hT := tcc_tube hν₀ (⟨y₀, hy₀, hy₀z⟩ : inversion ((s₀ - deriv (deriv (fB ν₀)) 0 / 2 : ℂ) : ExtPlane) ∈
    wB ν₀ '' extDiscExterior)
  have hev : ∀ᶠ p : LinfStar × ℂ in 𝓝 (ν₀, s₀),
      inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane) ∈ wB p.1 '' extDiscExterior :=
    hcont.tendsto.eventually hT
  have hball : ∀ᶠ p : LinfStar × ℂ in 𝓝 (ν₀, s₀), p.1 ∈ LinfStarBall :=
    continuousAt_fst.eventually (isOpen_ball.mem_nhds hν₀)
  filter_upwards [hev, hball] with p hp hpb
  obtain ⟨y, hy, hyz⟩ := hp
  have hGy := hGext y hy
  have hneL : OnePoint.map (normalizedSolution (extB (tcurveLambda p.1 G))) (OnePoint.map G y) ≠
      ((0 : ℂ) : ExtPlane) := fun h => h0ext ((s5rh_W_map_eq_zero (hLm hpb) h) ▸ hGy)
  have hmL := s5rh_memoir (hLm hpb) hneL
  have hZ : tcurveZ p.1 G (tcurveLambda p.1 G) (inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane)) =
      wB (tcurveLambda p.1 G) (OnePoint.map G y) := by
    show wB _ (OnePoint.map G (Function.invFun (wB p.1) _)) = _
    rw [← hyz, Function.leftInverse_invFun (wB_bijective p.1).1 y]
  have hcid := s5rh_coord_identity hpb hy hyz
  show finPart (inversion (tcurveZ p.1 G (tcurveLambda p.1 G)
      (inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane)))) +
      deriv (deriv (fB (tcurveLambda p.1 G))) 0 / 2 = _
  rw [hZ, hmL]
  dsimp only [Function.comp_apply]
  rw [hcid]

/-- `tcCoordH` is injective on `𝒯(1)`: the shift depends only on the base point. -/
theorem s5rh_injOn : InjOn tcCoordH TCurve := by
  intro a ha b hb hab
  have h1 : a.1 = b.1 := bers_injective (congrArg Prod.fst hab)
  have h2 := congrArg Prod.snd hab
  simp only [tcCoordH] at h2
  rw [h1] at h2
  exact tcCoord_chart.1 ha hb (Prod.ext (congrArg bers h1) (add_right_cancel h2))

/-- Local form of `tcCoordHInv` near `tcCoordH a`, through an analytic local Bers section. -/
theorem s5rh_local_coords {a : T1 × ExtPlane} (ha : a ∈ TCurve) :
    ∃ sec : AInf unitDisc → LinfStar, DifferentiableAt ℂ sec (bers a.1) ∧
      sec (bers a.1) = ((Quotient.out a.1 : LinfStarBall) : LinfStar) ∧
      ∀ᶠ y : AInf unitDisc × ℂ in 𝓝 (tcCoordH a), ∃ h : sec y.1 ∈ LinfStarBall,
        tcCoordHInv y = (Phi (Subtype.mk (sec y.1) h),
          inversion ((y.2 - deriv (deriv (fB (sec y.1))) 0 / 2 : ℂ) : ExtPlane)) ∧
        tcCoordHInv y ∈ TCurve := by
  obtain ⟨sec, U, hU, hpU, hsa, hs0, hsec⟩ := s5cf_section_analytic a.1
  set ν₀ : LinfStar := ((Quotient.out a.1 : LinfStarBall) : LinfStar) with hν₀def
  have hν₀ : ν₀ ∈ LinfStarBall := (Quotient.out a.1 : LinfStarBall).2
  have hsd : DifferentiableAt ℂ sec (bers a.1) := (hsa _ hpU).differentiableAt
  refine ⟨sec, hsd, hs0, ?_⟩
  set c : LinfStar → ℂ := fun ν => deriv (deriv (fB ν)) 0 / 2 with hc
  set x := tcCoordH a with hx
  have hsc : ContinuousAt (fun y : AInf unitDisc × ℂ => sec y.1) x := by
    have h1 : ContinuousAt sec x.1 := hsd.continuousAt
    exact h1.comp continuousAt_fst
  have hcc : ContinuousAt c (sec x.1) := by
    rw [show x.1 = bers a.1 from rfl, hs0]
    exact (s5rh_c_continuousOn.continuousAt (isOpen_ball.mem_nhds hν₀)).div_const 2
  set m : AInf unitDisc × ℂ → LinfStar × ExtPlane := fun y =>
    (sec y.1, inversion ((y.2 - c (sec y.1) : ℂ) : ExtPlane)) with hm
  have hmc : ContinuousAt m x := by
    refine hsc.prodMk ?_
    exact (tcc_inversion_continuous.comp OnePoint.continuous_coe).continuousAt.comp
      (continuousAt_snd.sub (ContinuousAt.comp (g := c) (f := fun y : AInf unitDisc × ℂ => sec y.1) hcc hsc))
  have ha0 : a.2 ≠ ((0 : ℂ) : ExtPlane) := fun h0 => tcc_zero_not_mem hν₀ (h0 ▸ ha)
  have hm0 : m x = (ν₀, a.2) := by
    have hback : inversion ((finPart (inversion a.2) : ℂ) : ExtPlane) = a.2 := by
      rw [coe_finPart_of_ne (fun h => ha0 ((tcc_inversion_eq_inf_iff a.2).mp h)), tcc_inversion_invol]
    have hs0' : sec x.1 = ν₀ := hs0
    simp only [hm, hs0']
    have he : x.2 - c ν₀ = finPart (inversion a.2) := by
      show finPart (inversion a.2) + deriv (deriv (fB ν₀)) 0 / 2 - deriv (deriv (fB ν₀)) 0 / 2 = _
      ring
    rw [he, hback]
  have hT := tcc_tube hν₀ ha
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

/-- **H5a.** The right translation `x ↦ x * b⁻¹` of `𝒯(1)` is ℂ-differentiable in the holomorphic coordinates
`tcCoordH` at every point of `𝒯(1)`. -/
theorem s5rh_mulInv_holo {a b : T1 × ExtPlane} (ha : a ∈ TCurve) (hb : b ∈ TCurve) :
    DifferentiableAt ℂ (tcCoordExpr fun x => tcurveMulInv x b) (tcCoordH a) := by
  set μb : LinfStar := ((Quotient.out b.1 : LinfStarBall) : LinfStar) with hμbdef
  have hμb : μb ∈ LinfStarBall := (Quotient.out b.1 : LinfStarBall).2
  have hu := tcg_parameter_mem hμb hb
  obtain ⟨G, hG⟩ := tcg_extension_exists hμb hu
  obtain ⟨sec, hsd, hs0, hev⟩ := s5rh_local_coords ha
  obtain ⟨hLd, hLm⟩ := s5rh_lambda_holo hμb hu hG
  set ν₀ : LinfStar := ((Quotient.out a.1 : LinfStarBall) : LinfStar) with hν₀def
  have hν₀ : ν₀ ∈ LinfStarBall := (Quotient.out a.1 : LinfStarBall).2
  set Fib : LinfStar × ℂ → ℂ := fun p =>
    finPart (inversion (tcurveZ p.1 G (tcurveLambda p.1 G)
      (inversion ((p.2 - deriv (deriv (fB p.1)) 0 / 2 : ℂ) : ExtPlane)))) +
      deriv (deriv (fB (tcurveLambda p.1 G))) 0 / 2 with hFib
  set f : AInf unitDisc × ℂ → AInf unitDisc × ℂ := fun y =>
    (bersPhi (tcurveLambda (sec y.1) G), Fib (sec y.1, y.2)) with hf
  -- the coordinate expression agrees with `f` near `tcCoordH a`
  have heq : (tcCoordExpr fun x => tcurveMulInv x b) =ᶠ[𝓝 (tcCoordH a)] f := by
    filter_upwards [hev] with y hy
    obtain ⟨h, hinv, hmem⟩ := hy
    rw [hinv] at hmem
    obtain ⟨hl, hmul⟩ := s5rh_mulInv_rep hmem hb h rfl hG
    simp only [tcCoordExpr, Function.comp_apply, hinv, hmul, tcCoordH, hf, hFib, bers_Phi,
      s5rh_c_congr ⟨tcurveLambda (sec y.1) G, hl⟩]
  -- the fibre point of `a` in memoir coordinates
  have ha0 : a.2 ≠ ((0 : ℂ) : ExtPlane) := fun h0 => tcc_zero_not_mem hν₀ (h0 ▸ ha)
  have hs₀ : inversion (((tcCoordH a).2 - deriv (deriv (fB ν₀)) 0 / 2 : ℂ) : ExtPlane) ∈
      wB ν₀ '' extDiscExterior := by
    have hback : inversion ((finPart (inversion a.2) : ℂ) : ExtPlane) = a.2 := by
      rw [coe_finPart_of_ne (fun h => ha0 ((tcc_inversion_eq_inf_iff a.2).mp h)), tcc_inversion_invol]
    have he : (tcCoordH a).2 - deriv (deriv (fB ν₀)) 0 / 2 = finPart (inversion a.2) := by
      show finPart (inversion a.2) + deriv (deriv (fB ν₀)) 0 / 2 - deriv (deriv (fB ν₀)) 0 / 2 = _
      ring
    rw [he, hback]
    exact ha
  have hfib := s5rh_fibre_holo hμb hu hG hν₀ hs₀
  have hsec : DifferentiableAt ℂ (fun y : AInf unitDisc × ℂ => sec y.1) (tcCoordH a) :=
    hsd.comp (tcCoordH a) differentiableAt_fst
  have hpt : (sec (tcCoordH a).1, (tcCoordH a).2) = (ν₀, (tcCoordH a).2) := by
    rw [show (tcCoordH a).1 = bers a.1 from rfl, hs0]
  have h2 : DifferentiableAt ℂ (fun y : AInf unitDisc × ℂ => Fib (sec y.1, y.2)) (tcCoordH a) := by
    rw [← hpt] at hfib
    exact hfib.comp (tcCoordH a) (hsec.prodMk differentiableAt_snd)
  have hL0 : DifferentiableAt ℂ (fun ν => tcurveLambda ν G) ν₀ :=
    hLd.differentiableAt (isOpen_ball.mem_nhds hν₀)
  have hB0 : DifferentiableAt ℂ bersPhi (tcurveLambda ν₀ G) :=
    bersPhi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds (hLm hν₀))
  have hsec0 : sec (tcCoordH a).1 = ν₀ := hs0
  have h1 : DifferentiableAt ℂ (fun y : AInf unitDisc × ℂ => bersPhi (tcurveLambda (sec y.1) G)) (tcCoordH a) := by
    rw [← hsec0] at hL0 hB0
    exact DifferentiableAt.comp (g := bersPhi) (f := fun y : AInf unitDisc × ℂ => tcurveLambda (sec y.1) G)
      (tcCoordH a) hB0 (DifferentiableAt.comp (g := fun ν => tcurveLambda ν G)
        (f := fun y : AInf unitDisc × ℂ => sec y.1) (tcCoordH a) hL0 hsec)
  exact (h1.prodMk h2).congr_of_eventuallyEq heq

/-- **H5a for lemma_5_4.** `tcurveRight q₀` is ℂ-differentiable in `tcCoordH` at every point of `𝒯(1)`. -/
theorem s5rh_right_holo {q₀ q : T1 × ExtPlane} (hq₀ : q₀ ∈ TCurve) (hq : q ∈ TCurve) :
    DifferentiableAt ℂ (tcCoordExpr (tcurveRight q₀)) (tcCoordH q) :=
  s5rh_mulInv_holo hq (tcg_mul_mem_curve s5rh_tOrigin_mem hq₀)

end TakhtajanTeo
