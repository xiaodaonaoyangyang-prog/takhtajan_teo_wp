import TakhtajanTeo.Ch2.S3DFormula
import TakhtajanTeo.Ch2.S35Reused
import TakhtajanTeo.Ch2.S3DS1Cont
import TakhtajanTeo.Ch2.S3DS2Cont
import TakhtajanTeo.Ch2.S3DPolyDense
import TakhtajanTeo.Ch2.S3WConst
import TakhtajanTeo.Ch2.S4GThm41
import TakhtajanTeo.Ch2.S4GReductions
import TakhtajanTeo.Ch2.S3S1Tilde
import TakhtajanTeo.Ch2.S3FirstVariationCompleted
import TakhtajanTeo.Ch2.R43Potential
import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.GroupTopology
import TakhtajanTeo.Ch1.Lemma29Plane
import TakhtajanTeo.Ch1.GroupChainCompleted
import TakhtajanTeo.Ch1.GroupTopGroup

/-! # Density route: Theorem 3.8 and its consequences (Program G install module)

Master interface `S3Density_IFACE` (29319fbc) proved, plus the `s3z_` copies of `thm_3_5`, `cor_3_7`, `cor_3_9`, `thm_4_1`, `cor_4_2`, `wpPotential_spec` for `reloc_g.py`. -/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-- **(1) Schauder core, in the consumed (domination) form.** On a `D`-base `κ` (a finite product of chart points with
polynomial `φ`), with polynomial-harmonic `a` and direction `m`, the exterior pre-Schwarzian `𝒜(g_s)` and its
`s`-derivative are dominated on `𝔻*` by one `G ∈ L²(𝔻*)` for `s` near `0`.
Truth: `extA` of every factor is `C^{1,1}` across `𝕊¹` (the coefficient `(1 - |z|²)² conj φ` vanishes to second order),
so the weldings are `C^{2,α}` up to `𝕊¹` by Beltrami–Schauder across the circle plus Kellogg, uniformly for `s` small.
Hence `𝒜(g_s)` is bounded near `𝕊¹`, while `𝒜(g_s)′` and the unwelded `∂_s 𝒜(g_s) = ∂C_s - (𝒜(g_s) ψ_s)′` are
`O(dist^{α-1})` (`C^{2,α}` welding, `α < 1`), hence square-integrable for `α > 1/2`; at `∞` everything is `O(|z|⁻³)`.
So an `L²` dominating `G` exists. (Under route (iii), analytic welding for polynomial `φ`, `g_s` extends analytically
across `𝕊¹` and the terms are even bounded.) GO/NO-GO checkpoint of the route. -/
theorem s3d_g_dom {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    ∃ r > 0, ∃ G : ℂ → ℝ, MemLp G 2 (volume.restrict unitDiscExterior) ∧ ∀ s ∈ ball (0 : ℂ) r,
      AEStronglyMeasurable (preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)))
        (volume.restrict unitDiscExterior) ∧ ∀ z ∈ unitDiscExterior,
        DifferentiableAt ℝ (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) s ∧
        ‖fderiv ℝ (fun t : ℂ => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) s‖ ≤ G z ∧
        ‖preSchwarzian (gsans (beltramiMul (a + s • toLinf m) κ)) z‖ ≤ G z := by
  exact s3d_g_dom_proof hκ hκD ha has haL haD hm hmD

/-- **Off-centre first variation of `S₁` on `D`.** Assembly (to be written in the install module): `N_f` by (G) + (A),
`N_g` by `s3d_l2sq_dom` + `s3d_g_dom` (whose domination also gives `hB`, `hB1`, `hB2`), `log |g'(∞)|` by (C), then
`s3d_formula`, as in the old `s35_S1_offcentre_variation`. -/
theorem s3d_S1_off {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
    DifferentiableAt ℝ (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 ∧
      dz (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 =
        2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (beltramiMul a κ)) z * RnmFun (toLinf m) a z := by
  have hd := delta0_bounds
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hzero : a + (0 : ℂ) • toLinf m = a := by rw [zero_smul, add_zero]
  obtain ⟨hAd, hA1, hA2, hAL, hAR⟩ := s35_f_variation hκ ha has haL hm
  have hC := s35_beta_variation hκ ha has haL hm
  -- `N_g` by domination (the Schauder core `s3d_g_dom_proof` on the `D`-base)
  have hdom := s3d_g_dom_proof hκ hκD ha has haL haD hm hmD
  obtain ⟨hBd, hB1, hB2⟩ := s3x_dom_data (D := unitDiscExterior)
    (F := fun t z => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z) hEo.measurableSet hdom
  have hD := s3d_formula hκ hκD ha has haL haD hm hmD hAd hBd hA1 hA2 hB1 hB2 hC
  obtain ⟨hGf, hGfv⟩ := s35_l2sq_variation (D := unitDisc)
    (F := fun t z => preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z)
    (F₀ := preSchwarzian (fsans (beltramiMul a κ))) measurableSet_ball (by funext z; rw [hzero]) hAL hA1 hA2 hAR
  obtain ⟨hGg, hGgv⟩ := s3d_l2sq_dom (D := unitDiscExterior)
    (F := fun t z => preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z)
    (F₀ := preSchwarzian (gsans (beltramiMul a κ))) hEo.measurableSet (by funext z; rw [hzero]) hdom
  -- `𝗀_0'(∞) ≠ 0`
  have ha1 : a ∈ LinfStarBall := mem_ball_zero_iff.mpr (has.trans hd.2)
  have hβ0 : derivAtInfty (gsans (beltramiMul (a + (0 : ℂ) • toLinf m) κ)) ≠ 0 := by
    rw [hzero]
    exact e24_dinf_ne (remark_2_2 (bg_mul_mem_ball κ.2 ha1)).1
  have hLd : DifferentiableAt ℝ
      (fun t : ℂ => ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 := by
    have hn := (hC.norm ℝ hβ0).log (norm_ne_zero_iff.mpr hβ0)
    exact Complex.ofRealCLM.differentiableAt.comp (0 : ℂ) hn
  -- near `0` the line stays in the ball, where `S₁` is computed from the representative `ν_t`
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), a + t • toLinf m ∈ LinfStarBall := by
    have hcont : Continuous (fun t : ℂ => a + t • toLinf m) := continuous_const.add (continuous_id.smul continuous_const)
    have h0 : a + (0 : ℂ) • toLinf m ∈ LinfStarBall := by rw [hzero]; exact ha1
    exact hcont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds h0)
  have hev : (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) =ᶠ[𝓝 0] fun t : ℂ =>
      ((∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ) +
        ((∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ) -
        4 * (π : ℂ) * ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ) := by
    filter_upwards [hball] with t ht
    have hν := bg_mul_mem_ball κ.2 ht
    set q : T1 := Phi ⟨beltramiMul (a + t • toLinf m) κ, hν⟩ with hqdef
    have hq : teichSetoid (Quotient.out (s := teichSetoid) q) ⟨beltramiMul (a + t • toLinf m) κ, hν⟩ :=
      Quotient.exact (Quotient.out_eq (s := teichSetoid) q)
    obtain ⟨hcf, hcg⟩ := s2c_class_pair hq
    have hpf := preSchwarzian_eqOn isOpen_ball hcf
    have hpg := preSchwarzian_eqOn hEo hcg
    have e1 : (∫ z in unitDisc, ‖preSchwarzian (fsans ((Quotient.out q : LinfStarBall) : LinfStar)) z‖ ^ 2) =
        ∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_ball fun z hz => congrArg (fun w : ℂ => ‖w‖ ^ 2) (hpf hz)
    have e2 : (∫ z in unitDiscExterior, ‖preSchwarzian (gsans ((Quotient.out q : LinfStarBall) : LinfStar)) z‖ ^ 2) =
        ∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 :=
      setIntegral_congr_fun hEo.measurableSet fun z hz => congrArg (fun w : ℂ => ‖w‖ ^ 2) (hpg hz)
    have e3 : derivAtInfty (gsans ((Quotient.out q : LinfStarBall) : LinfStar)) =
        derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ)) := FB.fb_derivAtInfty_congr hcg
    have hpt : ptT (beltramiMul (a + t • toLinf m) κ) = q := by unfold ptT; exact dif_pos hν
    rw [hpt]
    show (((∫ z in unitDisc, ‖preSchwarzian (fsans ((Quotient.out q : LinfStarBall) : LinfStar)) z‖ ^ 2) +
      (∫ z in unitDiscExterior, ‖preSchwarzian (gsans ((Quotient.out q : LinfStarBall) : LinfStar)) z‖ ^ 2) -
      4 * π * Real.log ‖derivAtInfty (gsans ((Quotient.out q : LinfStarBall) : LinfStar))‖ : ℝ) : ℂ) = _
    rw [e1, e2, e3]
    push_cast
    ring
  have hS : DifferentiableAt ℝ (fun t : ℂ =>
      ((∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ) +
        ((∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ) -
        4 * (π : ℂ) * ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 :=
    (hGf.add hGg).sub (hLd.const_mul _)
  refine ⟨hS.congr_of_eventuallyEq hev, ?_⟩
  have hcm : dz (fun t : ℂ => 4 * (π : ℂ) *
      ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 =
      4 * (π : ℂ) * dz (fun t : ℂ =>
        ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 := by
    simp only [dz, fderiv_const_mul hLd, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hAB : DifferentiableAt ℝ (fun t : ℂ => ((∫ z in unitDisc, ‖preSchwarzian (fsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ) + ((∫ z in unitDiscExterior, ‖preSchwarzian (gsans (beltramiMul (a + t • toLinf m) κ)) z‖ ^ 2 : ℝ) : ℂ)) 0 := hGf.add hGg
  have hML : DifferentiableAt ℝ (fun t : ℂ => 4 * (π : ℂ) * ((Real.log ‖derivAtInfty (gsans (beltramiMul (a + t • toLinf m) κ))‖ : ℝ) : ℂ)) 0 := hLd.const_mul _
  rw [l613_dz_congr hev, dz_sub_pointwise hAB hML, (l613_dz_add hGf hGg).1, hGfv, hGgv, hcm]
  exact hD

theorem s3d_dir (ψ : A2 unitDisc) :
    ∃ m ∈ harmonicL2 unitDiscExterior, toLinf m = Lambda (A2toAInf ψ) := by
  have hmem : AInf.toFun (A2toAInf ψ) ∈ A2fun unitDisc := by
    have hr : A2toAInf ψ ∈ range A2toAInf := mem_range_self ψ
    rw [A2toAInf_range] at hr
    exact hr
  obtain ⟨m, hm, hmz⟩ := D0bers_harmonicL2.2 _ hmem
  have he : fderiv ℂ bersPhi 0 (toLinf m) = A2toAInf ψ := AInf.ext_toFun_disc fun z hz => hmz z hz
  refine ⟨m, hm, ?_⟩
  rw [← he, ← hp_eq_Lambda, wp_harmonicProj_fix hm]

theorem s3d_seg {F : T1 → ℝ}
    {κ : LinfStarBall} {φ : A2 unitDisc}
    (hoff : ∀ ψ : A2 unitDisc, ‖ψ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) →
      (∃ c : ℂ, ψ = c • φ) → ∀ m : ℂ → ℂ, m ∈ harmonicL2 unitDiscExterior → toLinf m = Lambda (A2toAInf φ) →
        DifferentiableAt ℝ (fun t : ℂ => (F (ptT (beltramiMul (Lambda (A2toAInf ψ) + t • toLinf m) κ)) : ℂ)) 0 ∧
          dz (fun t : ℂ => (F (ptT (beltramiMul (Lambda (A2toAInf ψ) + t • toLinf m) κ)) : ℂ)) 0 = 0)
    (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    F (ptT (beltramiMul (Lambda (A2toAInf φ)) κ)) = F (Phi κ) := by
  set ε₁ : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hε₁
  have hz : Lambda (0 : AInf unitDisc) = 0 := by
    have := Lambda_smul 0 (0 : AInf unitDisc)
    simpa using this
  obtain ⟨m, hm, hmt⟩ := s3d_dir φ
  set g : ℝ → ℝ := fun t => F (ptT (beltramiMul (Lambda (A2toAInf ((t : ℂ) • φ))) κ)) with hg
  have hD : ∀ t₀ ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t₀ := by
    intro t₀ ht₀
    have hsm : ‖(t₀ : ℂ) • φ‖ < ε₁ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀.1]
      calc t₀ * ‖φ‖ ≤ 1 * ‖φ‖ := mul_le_mul_of_nonneg_right ht₀.2 (norm_nonneg _)
        _ = ‖φ‖ := one_mul _
        _ < ε₁ := hφ
    obtain ⟨hdiff, hdz⟩ := hoff _ hsm ⟨_, rfl⟩ m hm hmt
    set Gr : ℂ → ℝ := fun s => F (ptT (beltramiMul (Lambda (A2toAInf ((t₀ : ℂ) • φ)) + s • toLinf m) κ))
      with hGr
    have hGd : DifferentiableAt ℝ Gr 0 := Complex.reCLM.differentiableAt.comp (0 : ℂ) hdiff
    have hG' : HasFDerivAt (fun s : ℂ => ((F (ptT (beltramiMul
        (Lambda (A2toAInf ((t₀ : ℂ) • φ)) + s • toLinf m) κ)) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ Gr 0)) 0 :=
      Complex.ofRealCLM.hasFDerivAt.comp (0 : ℂ) hGd.hasFDerivAt
    unfold dz at hdz
    rw [hG'.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Complex.ofRealCLM_apply] at hdz
    have h2 : ((fderiv ℝ Gr 0 1 : ℝ) : ℂ) - I * ((fderiv ℝ Gr 0 I : ℝ) : ℂ) = 0 := by
      linear_combination 2 * hdz
    have hx : fderiv ℝ Gr 0 1 = 0 := by
      have := congrArg Complex.re h2
      simpa using this
    have hgt : ∀ t : ℝ, g t = Gr (((t - t₀ : ℝ)) : ℂ) := fun t => by
      have hL : Lambda (A2toAInf ((t : ℂ) • φ)) =
          Lambda (A2toAInf ((t₀ : ℂ) • φ)) + (((t - t₀ : ℝ)) : ℂ) • toLinf m := by
        rw [hmt, ← Lambda_smul, ← Lambda_add, ← A2toAInfCLM_apply, ← A2toAInfCLM_apply,
          ← A2toAInfCLM_apply, ← map_smul, ← map_add, ← add_smul,
          show ((t₀ : ℂ) + (((t - t₀ : ℝ)) : ℂ)) = (t : ℂ) by push_cast; ring]
      show F (ptT (beltramiMul (Lambda (A2toAInf ((t : ℂ) • φ))) κ)) =
        F (ptT (beltramiMul (Lambda (A2toAInf ((t₀ : ℂ) • φ)) + (((t - t₀ : ℝ)) : ℂ) • toLinf m) κ))
      rw [hL]
    have hline : HasDerivAt (fun t : ℝ => (((t - t₀ : ℝ)) : ℂ)) ((1 : ℝ) : ℂ) t₀ :=
      ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
    have hGr0 : HasFDerivAt Gr (fderiv ℝ Gr 0) (((t₀ - t₀ : ℝ)) : ℂ) := by
      rw [sub_self, Complex.ofReal_zero]
      exact hGd.hasFDerivAt
    have hc := hGr0.comp_hasDerivAt t₀ hline
    rw [Complex.ofReal_one, hx] at hc
    exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall hgt)
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := 1)
    (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hD t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  have h1 := hconst 1 (right_mem_Icc.2 zero_le_one)
  have hg1 : g 1 = F (ptT (beltramiMul (Lambda (A2toAInf φ)) κ)) := by
    simp only [hg, Complex.ofReal_one, one_smul]
  have hg0 : g 0 = F (Phi κ) := by
    simp only [hg, Complex.ofReal_zero, zero_smul, A2toAInf_zero, hz, hb_zero_mul κ.2]
    unfold ptT
    rw [dif_pos κ.2]
  rw [← hg1, ← hg0]
  exact h1

theorem s3d_F_off {κ : LinfStarBall} (hκ : Phi κ ∈ T01)
    (hκD : ∃ L : List (A2 unitDisc), (∀ φ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      (κ : LinfStar) = L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)
    {a : LinfStar} (ha : a ∈ harmonicBeltrami) (has : ‖a‖ < delta0) (haL : normL2 unitDiscExterior a < ∞)
    (haD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧ a = Lambda (A2toAInf ψ))
    {m : ℂ → ℂ} (hm : m ∈ harmonicL2 unitDiscExterior)
    (hmD : ∃ ψ : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
      toLinf m = Lambda (A2toAInf ψ)) :
        DifferentiableAt ℝ (fun t : ℂ => (((fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p)
          (ptT (beltramiMul (a + t • toLinf m) κ)) : ℝ) : ℂ)) 0 ∧
          dz (fun t : ℂ => (((fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p)
            (ptT (beltramiMul (a + t • toLinf m) κ)) : ℝ) : ℂ)) 0 = 0 := by
  obtain ⟨hD2, hV2⟩ := s4g_S2_offcentre_variation hκ ha has haL hm
  obtain ⟨hD1, hV1⟩ := s3d_S1_off hκ hκD ha has haL haD hm hmD
  have hfun : (fun t : ℂ => (((fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p)
      (ptT (beltramiMul (a + t • toLinf m) κ)) : ℝ) : ℂ)) =
      fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ) +
        ((1 / (12 * π) : ℝ) : ℂ) * (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ) := by
    funext t
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
  rw [hfun]
  refine ⟨hD2.add (hD1.const_mul _), ?_⟩
  unfold dz at hV2 hV1 ⊢
  have hs : HasFDerivAt (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ) +
      ((1 / (12 * π) : ℝ) : ℂ) * (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ))
      (fderiv ℝ (fun t : ℂ => (liouvilleS2 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0 +
        ((1 / (12 * π) : ℝ) : ℂ) • fderiv ℝ (fun t : ℂ => (liouvilleS1 (ptT (beltramiMul (a + t • toLinf m) κ)) : ℂ)) 0)
      0 :=
    hD2.hasFDerivAt.add (hD1.hasFDerivAt.const_mul ((1 / (12 * π) : ℝ) : ℂ))
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  linear_combination hV2 + (1 / (12 * (π : ℂ))) * hV1

/-- Chart points at the origin of the `√(π/3)`-ball lie in `T₀(1)` (connected image of a ball). -/
theorem s3d_chart0_T01 {φ : A2 unitDisc} (hφ : ‖φ‖ < Real.sqrt (π / 3)) :
    bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ) ∈ T01 := by
  letI : TopologicalSpace T1 := hilbertTopology
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  have hco : ContinuousOn (fun φ : A2 unitDisc =>
      bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_restrict.2 gtp_chart0_continuous
  have hc := (convex_ball (0 : A2 unitDisc) (Real.sqrt (π / 3))).isPreconnected.image _ hco
  have hsub := hc.subset_connectedComponent (x := originT) ⟨0, mem_ball_self hr0, gtp_chart0_zero⟩
  exact hsub ⟨φ, mem_ball_zero_iff.2 hφ, rfl⟩

/-- One chart step stays in `T₀(1)`: `[Λφ * κ] = [Λφ] · [κ]` (`gtp_mulT_phi`, `lemma_3_4`). -/
theorem s3d_step_T01 {κ : LinfStarBall} (hκ : Phi κ ∈ T01) {φ : A2 unitDisc}
    (hφ : ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    ptT (beltramiMul (Lambda (A2toAInf φ)) κ) ∈ T01 := by
  obtain ⟨hn, -, -, hch⟩ := gtp_small_a hφ
  have h1 : Phi ⟨Lambda (A2toAInf φ), Lambda_mem_ball hn⟩ ∈ T01 :=
    hch ▸ s3d_chart0_T01 (lt_of_lt_of_le hφ (min_le_left _ _))
  have h2 := grp_lemma_3_4.2.1 _ h1 _ hκ
  rw [gtp_mulT_phi] at h2
  unfold ptT
  rw [dif_pos (bg_mul_mem_ball κ.2 (Lambda_mem_ball hn))]
  exact h2

/-- `D ⊆ T₀(1)`, with the ball membership of the representative. -/
theorem s3d_D_T01 (L : List (A2 unitDisc)) (hL : ∀ φ ∈ L,
    (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧ ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0 ∈ LinfStarBall ∧
      ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0) ∈ T01 := by
  induction L with
  | nil =>
    have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
    refine ⟨h0, ?_⟩
    show ptT 0 ∈ T01
    unfold ptT
    rw [dif_pos h0]
    exact @mem_connectedComponent T1 hilbertTopology _
  | cons φ L ih =>
    obtain ⟨hb, hT⟩ := ih fun ψ hψ => hL ψ (List.mem_cons_of_mem φ hψ)
    have hφ := (hL φ List.mem_cons_self).2
    obtain ⟨hn, -, -, -⟩ := gtp_small_a hφ
    have hκ : Phi ⟨_, hb⟩ ∈ T01 := by
      unfold ptT at hT
      rwa [dif_pos hb] at hT
    exact ⟨bg_mul_mem_ball hb (Lambda_mem_ball hn), s3d_step_T01 (κ := ⟨_, hb⟩) hκ hφ⟩

/-- **(3) Constancy on `D`.** -/
theorem s3d_const_D :
    ∀ p ∈ {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)},
      liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p = liouvilleS2 originT + 1 / (12 * π) * liouvilleS1 originT := by
  set F : T1 → ℝ := fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p with hFdef
  have hcirc : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun z hz => (mem_ball_zero_iff.1 hz).ne
  have key : ∀ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧ ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) →
      F (ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)) = F originT := by
    intro L
    induction L with
    | nil =>
      intro _
      have h0 : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
      show F (ptT 0) = F originT
      unfold ptT
      rw [dif_pos h0]
      rfl
    | cons φ L ih =>
      intro hL
      have hL' : ∀ ψ ∈ L, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ z = q.eval z) ∧
          ‖ψ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) := fun ψ hψ => hL ψ (List.mem_cons_of_mem φ hψ)
      obtain ⟨hb, hT⟩ := s3d_D_T01 L hL'
      have hκ : Phi ⟨_, hb⟩ ∈ T01 := by
        unfold ptT at hT
        rwa [dif_pos hb] at hT
      obtain ⟨⟨q, hq⟩, hφ⟩ := hL φ List.mem_cons_self
      have hseg := s3d_seg (F := F) (κ := ⟨_, hb⟩) (φ := φ) (fun ψ hψ hc m hm hmt => by
        obtain ⟨-, ha, has, -⟩ := gtp_small_a hψ
        have haL : normL2 unitDiscExterior ⇑(Lambda (A2toAInf ψ)) < ∞ := by
          rw [l29b_Lambda_L2]
          exact ENNReal.mul_lt_top (by norm_num) ENNReal.coe_lt_top
        obtain ⟨c, rfl⟩ := hc
        have haD : ∃ ψ' : A2 unitDisc, (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun ψ' z = q.eval z) ∧
            Lambda (A2toAInf (c • φ)) = Lambda (A2toAInf ψ') := by
          refine ⟨c • φ, ⟨Polynomial.C c * q, fun z hz => ?_⟩, rfl⟩
          rw [A2.toFun_smul (D := unitDisc) isOpen_ball hcirc c φ hz, Pi.smul_apply, smul_eq_mul, hq z hz,
            Polynomial.eval_mul, Polynomial.eval_C]
        exact s3d_F_off hκ ⟨L, hL', rfl⟩ ha has haL haD hm ⟨φ, ⟨q, hq⟩, hmt⟩) hφ
      have hfold : ptT ((φ :: L).foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0) =
          ptT (beltramiMul (Lambda (A2toAInf φ)) ((⟨_, hb⟩ : LinfStarBall) : LinfStar)) := rfl
      have hPhi : Phi ⟨_, hb⟩ = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0) := by
        unfold ptT
        rw [dif_pos hb]
      rw [hfold, hseg, hPhi]
      exact ih hL'
  rintro p ⟨L, hL, rfl⟩
  exact key L hL

/-- `D`-representatives lie in `𝒪(𝔻*)₁`. -/
theorem s3d_D_groupO (L : List (A2 unitDisc)) (hL : ∀ φ ∈ L,
    (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧ ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0 ∈ groupO := by
  induction L with
  | nil => exact zero_mem_groupO
  | cons φ L ih =>
    obtain ⟨-, ha, has, -⟩ := gtp_small_a (hL φ List.mem_cons_self).2
    exact groupO_mul_mem (groupO_mem_of_harmonic ha has)
      (ih fun ψ hψ => hL ψ (List.mem_cons_of_mem φ hψ))

/-- The `ε₁`-chart image at a `D`-representative lies in the closure of `D` (polynomial density + chart
continuity `gtr_c_chart_continuous`). -/
theorem s3d_image_closure (L : List (A2 unitDisc)) (hL : ∀ φ ∈ L,
    (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧ ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)))
    {ψ : A2 unitDisc} (hψ : ‖ψ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) :
    bersChartInv (⟨_, (s3d_D_T01 L hL).1⟩ : LinfStarBall) (A2toAInf ψ) ∈ @closure T1 hilbertTopology
      {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)} := by
  letI : TopologicalSpace T1 := hilbertTopology
  set κ : LinfStarBall := ⟨_, (s3d_D_T01 L hL).1⟩ with hκ
  have hO : (κ : LinfStar) ∈ groupO := s3d_D_groupO L hL
  have hco : ContinuousOn (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ))
      (ball (0 : A2 unitDisc) (Real.sqrt (π / 3))) :=
    continuousOn_iff_continuous_restrict.2 (gtr_c_chart_continuous hO)
  have hψr : ψ ∈ ball (0 : A2 unitDisc) (Real.sqrt (π / 3)) :=
    mem_ball_zero_iff.2 (lt_of_lt_of_le hψ (min_le_left _ _))
  rw [mem_closure_iff_nhds]
  intro W hW
  have hpre : (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) ⁻¹' W ∈ 𝓝 ψ :=
    (hco.continuousAt (isOpen_ball.mem_nhds hψr)) hW
  have hb1 : ball (0 : A2 unitDisc) (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∈ 𝓝 ψ :=
    isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hψ)
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre hb1)
  obtain ⟨ψ', hpoly, hclose⟩ := s3d_poly_dense ψ hη
  have hmem : ψ' ∈ ball ψ η := by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    exact hclose
  obtain ⟨hW', hsm⟩ := hηs hmem
  have hsm' : ‖ψ'‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) := mem_ball_zero_iff.1 hsm
  obtain ⟨hn, -, -, -⟩ := gtp_small_a hsm'
  have hpt : bersChartInv κ (A2toAInf ψ') = ptT (beltramiMul (Lambda (A2toAInf ψ')) (κ : LinfStar)) := by
    rw [ct_bersChartInv_eq hn, bt_rightTrans_phi]
    unfold ptT
    rw [dif_pos (bg_mul_mem_ball κ.2 (Lambda_mem_ball hn))]
  refine ⟨bersChartInv κ (A2toAInf ψ'), hW', ψ' :: L, ?_, ?_⟩
  · intro φ hφ
    rcases List.mem_cons.1 hφ with rfl | hφL
    · exact ⟨hpoly, hsm'⟩
    · exact hL φ hφL
  · rw [hpt]
    rfl

/-- **(4) Density.** -/
theorem s3d_dense :
    {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)} ⊆ T01 ∧
    T01 ⊆ @closure T1 hilbertTopology {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)} := by
  letI : TopologicalSpace T1 := hilbertTopology
  set D : Set T1 := {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)} with hDdef
  have hε₁0 : 0 < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) := by
    have hd := delta0_bounds
    exact lt_min (by positivity) (div_pos (by linarith [hd.1]) (Real.sqrt_pos.2 (by positivity)))
  have hDT : D ⊆ T01 := by
    rintro p ⟨L, hL, rfl⟩
    exact (s3d_D_T01 L hL).2
  refine ⟨hDT, ?_⟩
  have hone : ∀ x : T1, mulT originT x = x := by
    intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    change mulT (Phi ⟨0, mem_ball_self one_pos⟩) (Phi a) = Phi a
    rw [gtp_mulT_phi]
    exact congrArg Phi (Subtype.ext (hb_zero_mul a.2))
  have hopen : IsOpen (closure D) := by
    refine isOpen_iff_forall_mem_open.2 fun q hq => ?_
    obtain ⟨κq, hκqO, rfl⟩ := r43p_groupO_rep q
    obtain ⟨δ, hδ, hδr, hinv⟩ := gtr_inv_SM _ hε₁0 (min_le_left _ _)
    have hN := gtr_c_image_mem hκqO hδ hδr
    obtain ⟨p, ⟨φ, hφ, rfl⟩, ⟨L, hL, hpL⟩⟩ := mem_closure_iff_nhds.1 hq _ hN
    have hφδ : ‖φ‖ < δ := mem_ball_zero_iff.1 hφ
    obtain ⟨φ', hφ'ε, hinvφ⟩ := hinv φ hφδ
    have hb := (s3d_D_T01 L hL).1
    set κp : LinfStarBall := ⟨_, hb⟩ with hκp
    have hPp : Phi κp = bersChartInv κq (A2toAInf φ) := by
      rw [show bersChartInv κq (A2toAInf φ) =
        ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0) from hpL]
      unfold ptT
      rw [dif_pos hb]
    have hq' : Phi κq = bersChartInv κp (A2toAInf φ') := by
      rw [gtr_c_chart_mul κp (lt_of_lt_of_le hφ'ε (min_le_left _ _)), ← hinvφ, hPp,
        gtr_c_chart_mul κq (lt_of_lt_of_le hφδ hδr), ← gtr_c_assoc, gtr_c_inv_mul_self, hone]
    refine ⟨(fun ψ : A2 unitDisc => bersChartInv κp (A2toAInf ψ)) '' ball 0 (min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))), ?_,
      glr_chart_image_open (s3d_D_groupO L hL) isOpen_ball (ball_subset_ball (min_le_left _ _)),
      ⟨φ', mem_ball_zero_iff.2 hφ'ε, hq'.symm⟩⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    exact s3d_image_closure L hL (mem_ball_zero_iff.1 hψ)
  have h0 : originT ∈ closure D := by
    refine subset_closure ⟨[], fun φ hφ => by simp at hφ, ?_⟩
    have h0b : (0 : LinfStar) ∈ LinfStarBall := mem_ball_self one_pos
    show originT = ptT 0
    unfold ptT
    rw [dif_pos h0b]
    rfl
  exact (IsClopen.connectedComponent_subset ⟨isClosed_closure, hopen⟩ h0 :
    connectedComponent originT ⊆ closure D)

theorem s3d_F_cont :
    @ContinuousOn T1 ℝ hilbertTopology _ (fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p) T01 := by
  letI : TopologicalSpace T1 := hilbertTopology
  exact s3d_S2_cont.add (continuousOn_const.mul s1c_continuousOn)

/-- `S₁(origin) = 0` and `S₂(origin) = 0`: `s3wc_S1_origin`, `s3wc_S2_origin` of the accepted module
`Ch2/S3WConst` (6a4bf6a9, install deferred); restated here only because that module is not built yet. -/
theorem s3d_origin : liouvilleS1 originT = 0 ∧ liouvilleS2 originT = 0 := by
  exact ⟨s3wc_S1_origin, s3wc_S2_origin⟩

/-- **(6a)** `S₂ = -(1/12π) S₁` on `T₀(1)`: `F` vanishes on `D` (`s3d_const_D`, `F(origin) = 0`), is continuous on
`T₀(1)` and `D` is dense. -/
theorem s3d_h38 : ∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p := by
  letI : TopologicalSpace T1 := hilbertTopology
  intro p hp
  set D : Set T1 := {p : T1 | ∃ L : List (A2 unitDisc), (∀ φ ∈ L,
      (∃ q : Polynomial ℂ, ∀ z ∈ unitDisc, A2.toFun φ z = q.eval z) ∧
      ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π))) ∧
      p = ptT (L.foldr (fun φ acc => beltramiMul (Lambda (A2toAInf φ)) acc) 0)} with hDdef
  set F : T1 → ℝ := fun p => liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p with hFdef
  have h0 : F originT = 0 := by
    simp only [hFdef, s3d_origin.1, s3d_origin.2, mul_zero, add_zero]
  have hD0 : ∀ q ∈ D, F q = 0 := fun q hq => (s3d_const_D q hq).trans h0
  obtain ⟨hDT, hTD⟩ := s3d_dense
  have hcw : ContinuousWithinAt F D p := (s3d_F_cont p hp).mono hDT
  have hmem := hcw.mem_closure_image (hTD hp)
  have himg : F '' D ⊆ {0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact hD0 q hq
  have hFp : F p = 0 := by
    have := closure_mono himg hmem
    rwa [closure_singleton, mem_singleton_iff] at this
  have hFp' : liouvilleS2 p + 1 / (12 * π) * liouvilleS1 p = 0 := hFp
  linarith [hFp']

/-- **(6b) Theorem 3.8**, same statement as Ch2 `thm_3_8`: `s3wc_thm_3_8` with the off-centre `S₁` variation supplied
by the installed `s4g_S1_offcentre_variation` from `s3d_h38`. -/
theorem s3d_thm_3_8 :
    (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p) ∧
      (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1Tilde p) ∧
      ∀ p ∈ T01, ∀ μ ∈ harmonicL2 unitDiscExterior,
        BersDiffAt liouvilleS1 (Quotient.out p : LinfStarBall) μ ∧
          bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ =
            2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z * μ z := by
  exact s3wc_thm_3_8 (fun _ hκ _ ha has haL _ hm => s4g_S1_offcentre_variation s3d_h38 hκ ha has haL hm)

/-- Prefixed copy of Ch2 `thm_3_5` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_thm_3_5 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    BersDiffAt liouvilleS1Tilde ν μ ∧
      bersDz liouvilleS1Tilde ν μ = 2 * ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z := by
  intro ν
  obtain ⟨hD, hV⟩ := s3d_thm_3_8.2.2 p hp μ hμ
  obtain ⟨h1, h2⟩ := s35_bers_transfer hp hμ
  exact ⟨h1.mpr hD, h2.trans hV⟩

/-- Prefixed copy of Ch2 `cor_3_7` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_cor_3_7 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  exact s3wc_cor_3_7 (s3z_thm_3_5 hp hμ).2

/-- Prefixed copy of Ch2 `cor_3_9` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_cor_3_9 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  exact s3wc_cor_3_9 (s3d_thm_3_8.2.2 p hp μ hμ).2

/-- Prefixed copy of Ch2 `thm_4_1` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_thm_4_1 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  exact s4g_thm_4_1 s3d_h38 hp hμ hν

/-- Prefixed copy of Ch2 `cor_4_2` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_cor_4_2 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = -2 * I * omegaWPOrigin μ ν := by
  exact s4g_cor_4_2 (s3z_thm_4_1 hp hμ hν)

/-- Prefixed copy of Ch2 `wpPotential_spec` for the relocation by `reloc_g.py` (statement byte-identical). -/
theorem s3z_wpPotential_spec (p : T1) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar wpPotential (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  exact s4g_wpPotential_spec hμ hν (fun q hq => s3z_thm_4_1 hq hμ hν) p

/-- **Theorem 3.8** (TT:5162–5198). On `T₀(1)`: `S₂ = -(1/12π) S₁ = -(1/12π) S̃₁`. In particular, in the Bers coordinates
of `V_ν`, `∂S₁/∂ε_μ([ν]) = 2 ∬_{𝔻*} 𝒮(𝗀_ν)(z) μ(z) d²z`. -/
theorem thm_3_8 :
    (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1 p) ∧
      (∀ p ∈ T01, liouvilleS2 p = -(1 / (12 * π)) * liouvilleS1Tilde p) ∧
      ∀ p ∈ T01, ∀ μ ∈ harmonicL2 unitDiscExterior,
        BersDiffAt liouvilleS1 (Quotient.out p : LinfStarBall) μ ∧
          bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ =
            2 * ∫ z in unitDiscExterior, schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z * μ z := by
  exact s3d_thm_3_8

/-- **Theorem 3.5** (TT:4780–4960). `S̃₁ : T₀(1) → ℝ` is differentiable at every `[ν] ∈ T₀(1)`, and in the Bers
coordinates `ε_μ` of the chart `V_ν`: `∂S̃₁/∂ε_μ([ν]) = 2 ∬_{𝔻*} 𝒮(𝗀_ν)(z) μ(z) d²z`. -/
theorem thm_3_5 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    let ν : LinfStar := (Quotient.out p : LinfStarBall)
    BersDiffAt liouvilleS1Tilde ν μ ∧
      bersDz liouvilleS1Tilde ν μ = 2 * ∫ z in unitDiscExterior, schwarzianHol (gsans ν) z * μ z := by
  exact s3z_thm_3_5 hp hμ

/-- **Corollary 3.7** (TT:5156). `∂S̃₁ = 2ϑ` on `T₀(1)`. -/
theorem cor_3_7 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS1Tilde (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  exact s3z_cor_3_7 hp hμ

/-- **Corollary 3.9** (TT:5200). `∂S₁ = 2ϑ` on `T₀(1)`. -/
theorem cor_3_9 {p : T1} (hp : p ∈ T01) {μ : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior) :
    bersDz liouvilleS1 (Quotient.out p : LinfStarBall) μ = 2 * varthetaPair p μ := by
  exact s3z_cor_3_9 hp hμ

/-- **Theorem 4.1** (TT:5300–5346). In the Bers coordinates of the chart `V_κ` at `[κ] ∈ T₀(1)`:
`∂²S₁/∂ε_μ∂ε̄_ν([κ]) = ∬_{𝔻*} μ(z) \overline{ν(z)} ρ(z) d²z`. -/
theorem thm_4_1 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  exact s3z_thm_4_1 hp hμ hν

/-- **Corollary 4.2** (TT:5348). `∂∂̄S₁ = -2i ω_WP` on `T₀(1)`: `S₁` is a potential of the Weil–Petersson metric. -/
theorem cor_4_2 {p : T1} (hp : p ∈ T01) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar liouvilleS1 (Quotient.out p : LinfStarBall) μ ν = -2 * I * omegaWPOrigin μ ν := by
  exact s3z_cor_4_2 hp hμ hν

/-- (TT:5408) By the right invariance of the Weil–Petersson metric, `S` is a Weil–Petersson potential on all of `T(1)`:
`∂²S/∂ε_μ∂ε̄_ν([κ]) = ⟨μ, ν⟩_WP` in the Bers coordinates of every chart `V_κ`, `[κ] ∈ T(1)`. -/
theorem wpPotential_spec (p : T1) {μ ν : ℂ → ℂ} (hμ : μ ∈ harmonicL2 unitDiscExterior)
    (hν : ν ∈ harmonicL2 unitDiscExterior) :
    bersDzDzbar wpPotential (Quotient.out p : LinfStarBall) μ ν = wpInner μ ν := by
  exact s3z_wpPotential_spec p hμ hν

end TakhtajanTeo.Ch2
