import TakhtajanTeo.Ch2.S2_Lemma27
import TakhtajanTeo.Ch2.S2_Grunsky
import TakhtajanTeo.Ch2.S2_Completed4
import TakhtajanTeo.Ch2.S3_Completed
import TakhtajanTeo.Ch2.S2_Remark28
import TakhtajanTeo.Ch1.GroupTopGroup
import TakhtajanTeo.Ch1.GroupL2Representatives
import TakhtajanTeo.Ch1.Lemma29Plane
import TakhtajanTeo.Ch2.S2_Completed5
import TakhtajanTeo.Ch1.HilbertPreimageMetric

/-!
# Ch2 §2: Theorem 2.6 assembly (`gk_` interface, 下属2)

Host: new module `Ch2/S2_Thm26.lean` (imports `Ch2/S2_Lemma27` of 下属4 for `l27_general`, `l27_fderiv_continuousOn`).
Route (leader-approved fix of TT:4110–4160):
* `gk_T01_induction`: every `p ∈ T₀(1)` is reached from the origin by chart steps `[κ] ↦ [Λφ * κ]`, `φ ∈ A₂(𝔻)` small
  (so `Λφ` is harmonic, `‖Λφ‖∞ < δ₀`, `‖Λφ‖₂ = 2‖φ‖₂`); clopen argument as `glr_good_clopen`, inverse steps by `gtr_inv_SM`.
* `gk_path_C1`: the path `γ(s) = (sν) * κ` is `C¹` on `[0, 1]` and its right-invariant tangent is `D_{sν}R_{(sν)⁻¹}(ν)`.
* `gk_step`: one chart step keeps `∬∬_{𝔻×𝔻} |K₁|² < ∞`: FTC in `s` (`l27_general` + `l27_fderiv_continuousOn`),
  Cauchy–Schwarz and Tonelli, change of variables by `f_s⁻¹`, Beurling `L²` isometry (`thm11_3_isometry`,
  `hilbertH_eq_integral_ae_off_support`, truncation + Fatou) in `z` for fixed `w`, Fubini, `remark_2_8`, pull-back by `g_s`,
  and `grp_cor_2_6` (second clause) for `‖D_{sν}R_{(sν)⁻¹}(ν)‖₂ ≤ √2/(1-‖sν‖)² ‖ν‖₂`.
* `gk_fsans_congr`: `K₁` is a class function on `𝔻 × 𝔻` (from `s2c_class_pair`).
* `gk_mu_aesm`, `gk_pullback` and their support lemmas (`gk_ext_measurable` … `gk_phase_norm`) are by 下属4.
* `gk_thm_2_6`: byte-identical copy of `thm_2_6`. Base point `𝖿^0 = id` (`gk_fsans_zero`); the `K₄` half from the `K₁`
  half at `[μ]⁻¹ ∈ T₀(1)` (`lemma_3_4`, `gtp_invT_phi`) by inversion (`s2c_kerK4_lintegral`) and conjugation of both
  variables (`s2c_f_eq_conj`, `s2c_kerK1_conj`), `gk_K4_of_K1`.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real
noncomputable section
namespace TakhtajanTeo
open LiZhongQC
namespace Ch2

/-! ### `K₁` is a class function -/

theorem gk_kerK1_congr_eventually {f g : ℂ → ℂ} {z w : ℂ} (hz : f =ᶠ[𝓝 z] g) (hw : f =ᶠ[𝓝 w] g) :
    kerK1 f z w = kerK1 g z w := by
  have hz1 : deriv f =ᶠ[𝓝 z] deriv g := hz.deriv
  have hz2 : deriv (deriv f) =ᶠ[𝓝 z] deriv (deriv g) := hz1.deriv
  have hz3 : (fun u => deriv (deriv f) u / deriv f u) =ᶠ[𝓝 z]
      (fun u => deriv (deriv g) u / deriv g u) := by
    filter_upwards [hz1, hz2] with u h1 h2
    rw [h1, h2]
  unfold kerK1
  split_ifs with h
  · subst h
    unfold schwarzianHol
    rw [hz3.deriv_eq, hz2.eq_of_nhds, hz1.eq_of_nhds]
  · rw [hz.eq_of_nhds, hw.eq_of_nhds, hz1.eq_of_nhds, hw.deriv.eq_of_nhds]

/-- `K₁(𝖿^μ)` on `𝔻 × 𝔻` depends only on the class `[μ]` (TT:4048). -/
theorem gk_fsans_congr {μ ν : LinfStarBall} (h : Phi μ = Phi ν) {z w : ℂ} (hz : z ∈ unitDisc)
    (hw : w ∈ unitDisc) :
    kerK1 (fsans (μ : LinfStar)) z w = kerK1 (fsans (ν : LinfStar)) z w := by
  have hc := (s2c_class_pair (Quotient.exact h)).1
  have hD : IsOpen unitDisc := isOpen_ball
  apply gk_kerK1_congr_eventually
  · filter_upwards [hD.mem_nhds hz] with u hu
    exact hc hu
  · filter_upwards [hD.mem_nhds hw] with u hu
    exact hc hu

/-! ### Chart-step induction on `T₀(1)` -/

theorem gk_phi_mul_congr {a a' κ : LinfStarBall} (h : Phi a = Phi a') :
    Phi ⟨beltramiMul (a : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 a.2⟩ =
      Phi ⟨beltramiMul (a' : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 a'.2⟩ :=
  Quotient.sound (bc_beltramiMul_respects (Quotient.exact h) (teichSetoid.refl κ))

/-- Chart-step induction on `T₀(1)`: a property of classes that holds at the origin and is preserved by the left
chart steps `[κ] ↦ [Λφ * κ]` (`φ ∈ A₂(𝔻)` small) holds on all of `T₀(1)`. -/
theorem gk_T01_induction {P : T1 → Prop} (h0 : P originT)
    (hstep : ∀ κ ν : LinfStarBall, P (Phi κ) →
      (∃ φ : A2 unitDisc, ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) ∧
        (ν : LinfStar) = Lambda (A2toAInf φ)) →
      P (Phi ⟨beltramiMul (ν : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 ν.2⟩)) :
    ∀ p ∈ T01, P p := by
  letI : TopologicalSpace T1 := hilbertTopology
  set r0 : ℝ := min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) with hr0
  have hd := delta0_bounds
  have hr0pos : 0 < r0 :=
    lt_min (by positivity) (div_pos (by linarith [hd.1]) (Real.sqrt_pos.2 (by positivity)))
  have hr0s : r0 ≤ Real.sqrt (π / 3) := min_le_left _ _
  -- the reachable set
  set R : Set T1 := {p | ∀ S : Set T1, originT ∈ S →
    (∀ κ ν : LinfStarBall, Phi κ ∈ S →
      (∃ φ : A2 unitDisc, ‖φ‖ < r0 ∧ (ν : LinfStar) = Lambda (A2toAInf φ)) →
      Phi ⟨beltramiMul (ν : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 ν.2⟩ ∈ S) → p ∈ S} with hR
  have hR0 : originT ∈ R := fun S h0S _ => h0S
  have hRstep : ∀ κ ν : LinfStarBall, Phi κ ∈ R →
      (∃ φ : A2 unitDisc, ‖φ‖ < r0 ∧ (ν : LinfStar) = Lambda (A2toAInf φ)) →
      Phi ⟨beltramiMul (ν : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 ν.2⟩ ∈ R :=
    fun κ ν hκ hν S h0S hS => hS κ ν (hκ S h0S hS) hν
  have hRP : R ⊆ {p | P p} := fun p hp => hp {p | P p} h0 (fun κ ν hκ hν => hstep κ ν hκ hν)
  -- a chart step from `Phi κ`
  have hchart : ∀ (κ : LinfStarBall) (φ : A2 unitDisc), ‖φ‖ < r0 →
      ∃ hl : Lambda (A2toAInf φ) ∈ LinfStarBall,
        rightTrans κ (bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) =
          Phi ⟨beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar), bg_mul_mem_ball κ.2 hl⟩ := by
    intro κ φ hφ
    have hn : ‖A2toAInf φ‖ < 2 := ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ hr0s))
    refine ⟨Lambda_mem_ball hn, ?_⟩
    rw [gtp_chart0 φ hn, bt_rightTrans_phi]
  have hopenU : ∀ (κ : LinfStarBall), (κ : LinfStar) ∈ groupO → ∀ r, 0 < r → r ≤ r0 →
      IsOpen (rightTrans κ '' ((fun φ : A2 unitDisc =>
        bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) '' ball 0 r)) ∧
      Phi κ ∈ rightTrans κ '' ((fun φ : A2 unitDisc =>
        bersChartInv (⟨0, mem_ball_self one_pos⟩ : LinfStarBall) (A2toAInf φ)) '' ball 0 r) := by
    intro κ hκ r hr hrr
    refine ⟨glr_right_image_open hκ (gtp_chart0_image_open (hrr.trans hr0s)), ?_⟩
    refine ⟨originT, ⟨0, mem_ball_self hr, gtp_chart0_zero⟩, grp_rightTrans_origin κ⟩
  -- `R` is open
  have hRo : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨κ, hκ, rfl⟩ := ctb_exists_groupO_rep p
    obtain ⟨ho, hm⟩ := hopenU κ hκ r0 hr0pos le_rfl
    refine ⟨_, ?_, ho, hm⟩
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨hl, he⟩ := hchart κ φ (mem_ball_zero_iff.1 hφ)
    rw [he]
    exact hRstep κ ⟨_, hl⟩ hp ⟨φ, mem_ball_zero_iff.1 hφ, rfl⟩
  -- the complement of `R` is open (inverse steps)
  obtain ⟨δ, hδ, hδs, hinv⟩ := gtr_inv_SM r0 hr0pos hr0s
  have hRc : IsOpen Rᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨κ, hκ, rfl⟩ := ctb_exists_groupO_rep p
    obtain ⟨ho, hm⟩ := hopenU κ hκ (min δ r0) (lt_min hδ hr0pos) (min_le_right _ _)
    refine ⟨_, ?_, ho, hm⟩
    rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩ hq
    have hφ' : ‖φ‖ < min δ r0 := mem_ball_zero_iff.1 hφ
    obtain ⟨hl, he⟩ := hchart κ φ (lt_of_lt_of_le hφ' (min_le_right _ _))
    rw [he] at hq
    obtain ⟨φ', hφ'r, hφ'e⟩ := hinv φ (lt_of_lt_of_le hφ' (min_le_left _ _))
    have hn : ‖A2toAInf φ‖ < 2 :=
      ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ' ((min_le_right _ _).trans hr0s)))
    have hn' : ‖A2toAInf φ'‖ < 2 :=
      ct_A2toAInf_norm_lt (mem_ball_zero_iff.2 (lt_of_lt_of_le hφ'r hr0s))
    rw [gtp_chart0 φ hn, gtp_invT_phi, gtp_chart0 φ' hn'] at hφ'e
    -- step from `Phi (Λφ * κ)` by `Λφ'`
    have hstep' := hRstep ⟨_, bg_mul_mem_ball κ.2 hl⟩ ⟨_, Lambda_mem_ball hn'⟩ hq ⟨φ', hφ'r, rfl⟩
    apply hp
    have hcongr := gk_phi_mul_congr (κ := ⟨_, bg_mul_mem_ball κ.2 hl⟩) hφ'e.symm
    rw [hcongr] at hstep'
    have heq : beltramiMul (beltramiInv (Lambda (A2toAInf φ)))
        (beltramiMul (Lambda (A2toAInf φ)) (κ : LinfStar)) = (κ : LinfStar) := by
      rw [← grp_mul_assoc (grp_inv_mem hl) hl κ.2, grp_inv_mul hl, grp_zero_mul κ.2]
    have hκeq : (⟨_, bg_mul_mem_ball (bg_mul_mem_ball κ.2 hl) (grp_inv_mem hl)⟩ : LinfStarBall) = κ :=
      Subtype.ext heq
    rw [hκeq] at hstep'
    exact hstep'
  have hclopen : IsClopen R := ⟨⟨hRc⟩, hRo⟩
  intro p hp
  exact hRP (hclopen.connectedComponent_subset hR0 hp)

/-! ### The left-translated path `γ(s) = (sν) * κ` -/

/-- The left-translated path `γ(s) = (sν) * κ` is `C¹` on `[0, 1]`, and its right-invariant tangent
`D_{γ(s)}R_{γ(s)⁻¹}(γ'(s))` equals `D_{sν}R_{(sν)⁻¹}(ν)` (associativity; `κ` drops out). -/
theorem gk_path_C1 {ν κ : LinfStar} (hν : ‖ν‖ < 1) (hκ : κ ∈ LinfStarBall) :
    ∃ γ' : ℝ → LinfStar, ContinuousOn γ' (Icc 0 1) ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => beltramiMul ((t : ℂ) • ν) κ) (γ' s) s ∧
      fderiv ℂ (fun l => beltramiMul l (beltramiInv (beltramiMul ((s : ℂ) • ν) κ)))
          (beltramiMul ((s : ℂ) • ν) κ) (γ' s) =
        fderiv ℂ (fun l => beltramiMul l (beltramiInv ((s : ℂ) • ν))) ((s : ℂ) • ν) ν := by
  set U : Set ℂ := {t | t • ν ∈ LinfStarBall} with hU
  have hUo : IsOpen U := isOpen_ball.preimage (continuous_id.smul continuous_const)
  have hball : ∀ s ∈ Icc (0 : ℝ) 1, ((s : ℂ)) ∈ U := by
    intro s hs
    show (s : ℂ) • ν ∈ LinfStarBall
    have : ‖(s : ℂ) • ν‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg ν, hs.2]
    simpa [LinfStarBall] using this
  set g : ℂ → LinfStar := fun t => beltramiMul (t • ν) κ with hg
  have hgd : ∀ t ∈ U, HasDerivAt g (fderiv ℂ (fun l => beltramiMul l κ) (t • ν) ν) t := by
    intro t ht
    obtain ⟨D, hD, -⟩ := bd_hasFDerivAt hκ ht
    have hl : HasDerivAt (fun t : ℂ => t • ν) ν t := by
      simpa using (hasDerivAt_id t).smul_const ν
    have := hD.comp_hasDerivAt t hl
    rw [hD.fderiv]
    exact this
  have hdiff : DifferentiableOn ℂ g U := fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn (deriv g) U := (hdiff.analyticOnNhd hUo).deriv.continuousOn
  refine ⟨fun s => deriv g s, ?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact hcont.comp Complex.continuous_ofReal.continuousOn (fun s hs => hball s hs)
  · have h := (hgd _ (hball s hs)).differentiableAt.hasDerivAt
    have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) ((1 : ℝ) : ℂ) s := (hasDerivAt_id s).ofReal_comp
    have := (h.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hr
    simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', Complex.ofReal_one,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] at this
    exact this
  · -- uniqueness of the derivative of `t ↦ γ(t) * γ(s)⁻¹ = (tν) * (sν)⁻¹` at `t = s`
    have ha : (s : ℂ) • ν ∈ LinfStarBall := hball s hs
    set a : LinfStar := (s : ℂ) • ν with hadef
    set b : LinfStar := beltramiMul a κ with hbdef
    have hb : b ∈ LinfStarBall := bg_mul_mem_ball hκ ha
    obtain ⟨Db, hDb, -⟩ := bd_hasFDerivAt (grp_inv_mem hb) hb
    obtain ⟨Da, hDa, -⟩ := bd_hasFDerivAt (grp_inv_mem ha) ha
    have hgs := hgd _ (hball s hs)
    have hgs' : HasDerivAt g (deriv g (s : ℂ)) (s : ℂ) := hgs.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun t : ℂ => beltramiMul (g t) (beltramiInv b)) (Db (deriv g (s : ℂ))) (s : ℂ) :=
      by simpa only [Function.comp_def] using hDb.comp_hasDerivAt (s : ℂ) hgs'
    have hl : HasDerivAt (fun t : ℂ => t • ν) ν (s : ℂ) := by
      simpa using (hasDerivAt_id (s : ℂ)).smul_const ν
    have h2 : HasDerivAt (fun t : ℂ => beltramiMul (t • ν) (beltramiInv a)) (Da ν) (s : ℂ) :=
      by simpa only [Function.comp_def] using hDa.comp_hasDerivAt (s : ℂ) hl
    have hev : (fun t : ℂ => beltramiMul (g t) (beltramiInv b)) =ᶠ[𝓝 (s : ℂ)]
        fun t : ℂ => beltramiMul (t • ν) (beltramiInv a) := by
      filter_upwards [hUo.mem_nhds (hball s hs)] with t ht
      have ht' : t • ν ∈ LinfStarBall := ht
      show beltramiMul (beltramiMul (t • ν) κ) (beltramiInv b) = _
      rw [hbdef, grp_inv_mul_rev ha hκ, ← grp_mul_assoc (bg_mul_mem_ball hκ ht') (grp_inv_mem hκ)
        (grp_inv_mem ha), grp_mul_assoc ht' hκ (grp_inv_mem hκ), grp_mul_inv hκ, grp_mul_zero ht']
    have huniq := (h1.congr_of_eventuallyEq hev.symm).unique h2
    rw [hDb.fderiv, hDa.fderiv]
    exact huniq

/-! ### FTC + Cauchy–Schwarz on `[0, 1]` -/

theorem gk_ftc_sq {F F' : ℝ → ℂ} (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' s) s)
    (hc : ContinuousOn F' (Icc 0 1)) :
    (‖F 1 - F 0‖₊ : ℝ≥0∞) ^ 2 ≤ ∫⁻ s in Icc (0 : ℝ) 1, (‖F' s‖₊ : ℝ≥0∞) ^ 2 := by
  have hu : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hint : IntervalIntegrable F' volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [hu]
    exact hc
  have hftc : ∫ s in (0 : ℝ)..1, F' s = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hd s (hu ▸ hs)) hint
  have hnc : ContinuousOn (fun s => ‖F' s‖) (Icc 0 1) := hc.norm
  have hn2c : ContinuousOn (fun s => ‖F' s‖ ^ 2) (Icc 0 1) := hnc.pow 2
  have hIn : IntegrableOn (fun s => ‖F' s‖) (Icc (0 : ℝ) 1) := hnc.integrableOn_compact isCompact_Icc
  have hIn2 : IntegrableOn (fun s => ‖F' s‖ ^ 2) (Icc (0 : ℝ) 1) := hn2c.integrableOn_compact isCompact_Icc
  set A : ℝ := ∫ s in Icc (0 : ℝ) 1, ‖F' s‖ with hA
  -- `‖F 1 - F 0‖ ≤ A`
  have h1 : ‖F 1 - F 0‖ ≤ A := by
    rw [← hftc, intervalIntegral.integral_of_le zero_le_one, hA, ← integral_Icc_eq_integral_Ioc]
    exact norm_integral_le_integral_norm _
  -- `A² ≤ ∫ ‖F'‖²` (variance on a probability interval)
  have hvol : (volume (Icc (0 : ℝ) 1)).toReal = 1 := by simp
  have h2 : A ^ 2 ≤ ∫ s in Icc (0 : ℝ) 1, ‖F' s‖ ^ 2 := by
    have hvar : 0 ≤ ∫ s in Icc (0 : ℝ) 1, (‖F' s‖ - A) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _)
    have he : ∫ s in Icc (0 : ℝ) 1, (‖F' s‖ - A) ^ 2 =
        (∫ s in Icc (0 : ℝ) 1, ‖F' s‖ ^ 2) - 2 * A * A + A ^ 2 := by
      have hexp : (fun s => (‖F' s‖ - A) ^ 2) = fun s => ‖F' s‖ ^ 2 - 2 * A * ‖F' s‖ + A ^ 2 := by
        funext s
        ring
      have i1 : IntegrableOn (fun s => ‖F' s‖ ^ 2 - 2 * A * ‖F' s‖) (Icc (0 : ℝ) 1) :=
        (hn2c.sub (continuousOn_const.mul hnc)).integrableOn_compact isCompact_Icc
      have i2 : IntegrableOn (fun s => 2 * A * ‖F' s‖) (Icc (0 : ℝ) 1) :=
        (continuousOn_const.mul hnc).integrableOn_compact isCompact_Icc
      have i3 : IntegrableOn (fun _ : ℝ => A ^ 2) (Icc (0 : ℝ) 1) :=
        continuousOn_const.integrableOn_compact isCompact_Icc
      rw [hexp, integral_add i1 i3, integral_sub hIn2 i2, integral_const_mul, integral_const]
      simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, hvol]
      rw [← hA]
      ring
    linarith
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Icc (fun s _ => norm_nonneg _)
  have h3 : ‖F 1 - F 0‖ ^ 2 ≤ ∫ s in Icc (0 : ℝ) 1, ‖F' s‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hlin : ∫⁻ s in Icc (0 : ℝ) 1, (‖F' s‖₊ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (∫ s in Icc (0 : ℝ) 1, ‖F' s‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hIn2 (Eventually.of_forall (fun s => sq_nonneg _))]
    apply lintegral_congr
    intro s
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [hlin]
  calc (‖F 1 - F 0‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖F 1 - F 0‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        rfl
    _ ≤ _ := ENNReal.ofReal_le_ofReal h3

/-! ### The Beurling transform bound off the support -/

theorem gk_eLpNorm_two_sq {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [← ENNReal.rpow_natCast]
  norm_num
  rfl

/-- Off the support of a compactly supported `φ ∈ L²`, the kernel integral `∬ φ(ζ)/(ζ - z)²` is `-π` times the
Beurling transform, an `L²` isometry (`thm11_3_isometry`). -/
theorem gk_beurling_cpt {φ : ℂ → ℂ} (hφm : Measurable φ) (hφ2 : MemLp φ 2 volume)
    (hφc : HasCompactSupport φ) {U : Set ℂ} (hU : Disjoint U (tsupport φ)) :
    ∫⁻ z in U, (‖∫ ζ, φ ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (π ^ 2) * ∫⁻ ζ, (‖φ ζ‖₊ : ℝ≥0∞) ^ 2 := by
  have hae := hilbertH_eq_integral_ae_off_support hφm hφ2 hφc
  have hUsub : U ⊆ (tsupport φ)ᶜ := fun z hz hz' => hU.ne_of_mem hz hz' rfl
  have hae' : ∀ᵐ z ∂(volume.restrict U), (‖∫ ζ, φ ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (π ^ 2) * (‖hilbertH φ z‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUsub hae] with z hz
    have he : ∫ ζ, φ ζ / (ζ - z) ^ 2 = -(π : ℂ) * hilbertH φ z := by
      rw [hz, ← integral_const_mul]
      congr 1
      funext ζ
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
    rw [he, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
    congr 1
    have : ((‖(π : ℂ)‖₊ : ℝ≥0∞)) = ENNReal.ofReal π := by
      rw [ENNReal.ofReal, ENNReal.coe_inj]
      ext
      simp [abs_of_pos Real.pi_pos, Real.pi_pos.le]
    rw [this, ← ENNReal.ofReal_pow Real.pi_pos.le]
  rw [lintegral_congr_ae hae', lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ?_
  calc ∫⁻ z in U, (‖hilbertH φ z‖₊ : ℝ≥0∞) ^ 2 ≤ ∫⁻ z, (‖hilbertH φ z‖₊ : ℝ≥0∞) ^ 2 :=
        setLIntegral_le_lintegral _ _
    _ = eLpNorm (hilbertH φ) 2 volume ^ 2 := (gk_eLpNorm_two_sq (hilbertH_memLp_two hφ2).1.aestronglyMeasurable).symm
    _ = eLpNorm φ 2 volume ^ 2 := by rw [thm11_3_isometry hφ2]
    _ = ∫⁻ ζ, (‖φ ζ‖₊ : ℝ≥0∞) ^ 2 := gk_eLpNorm_two_sq hφ2.aestronglyMeasurable

/-- A point of an open set disjoint from `Ωs` keeps a positive distance from `Ωs`. -/
theorem gk_sep {Ω Ωs : Set ℂ} (hΩ : IsOpen Ω) (hd : Disjoint Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    ∃ r > 0, ∀ u ∈ Ωs, r ≤ ‖u - z‖ := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hΩ z hz
  refine ⟨r, hr, fun u hu => ?_⟩
  by_contra h
  push_neg at h
  have : u ∈ Ω := hb (by rw [mem_ball, dist_eq_norm]; exact h)
  exact hd.ne_of_mem this hu rfl

theorem gk_kernel_integrable {Ωs : Set ℂ} (hΩsm : MeasurableSet Ωs) {m : ℂ → ℂ} (hm : Measurable m)
    {M : ℝ} (hM : ∀ u, ‖m u‖ ≤ M) {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrz : ∀ u ∈ Ωs, r ≤ ‖u - z‖) (hsw : ∀ u ∈ Ωs, s ≤ ‖u - w‖) :
    Integrable (Ωs.indicator fun u => m u / ((u - z) ^ 2 * (u - w) ^ 2)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨hz4, -⟩ := Ch2.s2c_l4_outside_ball z hr
  obtain ⟨hw4, -⟩ := Ch2.s2c_l4_outside_ball w hs
  have hsubz : Ωs ⊆ {ω : ℂ | r ≤ ‖ω - z‖} := fun u hu => hrz u hu
  have hsubw : Ωs ⊆ {ω : ℂ | s ≤ ‖ω - w‖} := fun u hu => hsw u hu
  have hg : IntegrableOn (fun u : ℂ => M * ((‖u - z‖ ^ 4)⁻¹ + (‖u - w‖ ^ 4)⁻¹)) Ωs :=
    ((hz4.mono_set hsubz).add (hw4.mono_set hsubw)).const_mul M
  rw [integrable_indicator_iff hΩsm]
  refine Integrable.mono' hg ?_ ?_
  · exact (by fun_prop : Measurable fun u => m u / ((u - z) ^ 2 * (u - w) ^ 2)).aestronglyMeasurable
  · refine (ae_restrict_iff' hΩsm).2 (Eventually.of_forall fun u hu => ?_)
    have h1 : 0 < ‖u - z‖ := hr.trans_le (hrz u hu)
    have h2 : 0 < ‖u - w‖ := hs.trans_le (hsw u hu)
    rw [norm_div, norm_mul, norm_pow, norm_pow]
    have hamgm : 1 / (‖u - z‖ ^ 2 * ‖u - w‖ ^ 2) ≤ (‖u - z‖ ^ 4)⁻¹ + (‖u - w‖ ^ 4)⁻¹ := by
      have ha : 0 < ‖u - z‖ ^ 2 := by positivity
      have hb : 0 < ‖u - w‖ ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      have e1 : (‖u - z‖ ^ 4)⁻¹ * (‖u - z‖ ^ 2 * ‖u - w‖ ^ 2) = ‖u - w‖ ^ 2 / ‖u - z‖ ^ 2 := by
        field_simp
      have e2 : (‖u - w‖ ^ 4)⁻¹ * (‖u - z‖ ^ 2 * ‖u - w‖ ^ 2) = ‖u - z‖ ^ 2 / ‖u - w‖ ^ 2 := by
        field_simp
      rw [add_mul, e1, e2]
      have key : 2 ≤ ‖u - w‖ ^ 2 / ‖u - z‖ ^ 2 + ‖u - z‖ ^ 2 / ‖u - w‖ ^ 2 := by
        rw [div_add_div _ _ ha.ne' hb.ne', le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖u - w‖ ^ 2 - ‖u - z‖ ^ 2)]
      linarith
    calc ‖m u‖ / (‖u - z‖ ^ 2 * ‖u - w‖ ^ 2) = ‖m u‖ * (1 / (‖u - z‖ ^ 2 * ‖u - w‖ ^ 2)) := by ring
      _ ≤ M * ((‖u - z‖ ^ 4)⁻¹ + (‖u - w‖ ^ 4)⁻¹) :=
        mul_le_mul (hM u) hamgm (by positivity) hM0

/-- The two-pole kernel bound of TT:4126–4140: for fixed `w ∈ Ω`,
`∬_Ω |∬_{Ω*} m(u)/((u - z)²(u - w)²)|² ≤ π² ∬_{Ω*} |m(u)|²/|u - w|⁴` (Beurling isometry, truncation, Fatou). -/
theorem gk_beurling_kernel {Ω Ωs : Set ℂ} (hΩ : IsOpen Ω) (hd : Disjoint Ω Ωs) (hΩsm : MeasurableSet Ωs)
    {m : ℂ → ℂ} (hm : Measurable m) {M : ℝ} (hM : ∀ u, ‖m u‖ ≤ M) {w : ℂ} (hw : w ∈ Ω) :
    ∫⁻ z in Ω, (‖∫ u in Ωs, m u / ((u - z) ^ 2 * (u - w) ^ 2)‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (π ^ 2) * ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - w‖₊ : ℝ≥0∞) ^ 4)⁻¹ := by
  obtain ⟨s, hs, hsw⟩ := gk_sep hΩ hd hw
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- truncations
  let φ : ℕ → ℂ → ℂ := fun n => (Ωs ∩ closedBall 0 n).indicator fun u => m u / (u - w) ^ 2
  have hφm : ∀ n, Measurable (φ n) := fun n =>
    (by fun_prop : Measurable fun u => m u / (u - w) ^ 2).indicator
      (hΩsm.inter measurableSet_closedBall)
  have hφb : ∀ n u, ‖φ n u‖ ≤ M / s ^ 2 := by
    intro n u
    by_cases hu : u ∈ Ωs ∩ closedBall 0 n
    · simp only [φ, indicator_of_mem hu, norm_div, norm_pow]
      have h1 : s ≤ ‖u - w‖ := hsw u hu.1
      have h2 : s ^ 2 ≤ ‖u - w‖ ^ 2 := pow_le_pow_left₀ hs.le h1 2
      calc ‖m u‖ / ‖u - w‖ ^ 2 ≤ M / ‖u - w‖ ^ 2 :=
            div_le_div_of_nonneg_right (hM u) (by positivity)
        _ ≤ M / s ^ 2 := div_le_div_of_nonneg_left hM0 (by positivity) h2
    · simp only [φ, indicator_of_notMem hu, norm_zero]
      positivity
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall 0 (n : ℝ)) (fun u hu => by
      simp only [φ]
      exact indicator_of_notMem (fun h => hu h.2) _)
  have hφ2 : ∀ n, MemLp (φ n) 2 volume := by
    intro n
    have hSm : MeasurableSet (Ωs ∩ closedBall (0 : ℂ) n) := hΩsm.inter measurableSet_closedBall
    have hSfin : volume (Ωs ∩ closedBall (0 : ℂ) n) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    haveI : IsFiniteMeasure (volume.restrict (Ωs ∩ closedBall (0 : ℂ) n)) := isFiniteMeasure_restrict.2 hSfin
    refine (memLp_indicator_iff_restrict hSm).2 (MemLp.of_bound
      (by fun_prop : Measurable fun u => m u / (u - w) ^ 2).aestronglyMeasurable (M / s ^ 2) ?_)
    refine (ae_restrict_iff' hSm).2 (Eventually.of_forall fun u hu => ?_)
    have h := hφb n u
    simp only [φ] at h
    rwa [indicator_of_mem hu] at h
  have htsupp : ∀ n, Disjoint Ω (tsupport (φ n)) := by
    intro n
    have hcl : tsupport (φ n) ⊆ closure Ωs := closure_mono (fun u hu => by
      by_contra h
      exact hu (indicator_of_notMem (fun h' => h h'.1) _))
    exact (hd.closure_right hΩ).mono_right hcl
  -- each truncation is bounded by the full right-hand side
  have hRHS : ∀ n, ∫⁻ ζ, (‖φ n ζ‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - w‖₊ : ℝ≥0∞) ^ 4)⁻¹ := by
    intro n
    rw [← lintegral_indicator hΩsm]
    refine lintegral_mono fun u => ?_
    by_cases hu : u ∈ Ωs ∩ closedBall 0 n
    · simp only [φ, indicator_of_mem hu, indicator_of_mem hu.1]
      have hne : u - w ≠ 0 := by
        intro h
        have := hsw u hu.1
        rw [h, norm_zero] at this
        linarith
      refine le_of_eq ?_
      rw [nnnorm_div, nnnorm_pow, ENNReal.coe_div (pow_ne_zero 2 (nnnorm_ne_zero_iff.2 hne)), ENNReal.coe_pow,
        div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, ← pow_mul]
    · simp only [φ, indicator_of_notMem hu, nnnorm_zero, ENNReal.coe_zero]
      simp
  have hbound : ∀ n, ∫⁻ z in Ω, (‖∫ ζ, φ n ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (π ^ 2) * ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - w‖₊ : ℝ≥0∞) ^ 4)⁻¹ :=
    fun n => (gk_beurling_cpt (hφm n) (hφ2 n) (hφc n) (htsupp n)).trans (mul_le_mul' le_rfl (hRHS n))
  -- pointwise convergence on `Ω`
  have hconv : ∀ z ∈ Ω, Tendsto (fun n => ∫ ζ, φ n ζ / (ζ - z) ^ 2) atTop
      (𝓝 (∫ u in Ωs, m u / ((u - z) ^ 2 * (u - w) ^ 2))) := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := gk_sep hΩ hd hz
    have hint := gk_kernel_integrable hΩsm hm hM hr hs hrz hsw
    rw [← integral_indicator hΩsm]
    refine tendsto_integral_of_dominated_convergence (fun u => ‖(Ωs.indicator
      fun u => m u / ((u - z) ^ 2 * (u - w) ^ 2)) u‖) ?_ hint.norm ?_ ?_
    · intro n
      exact ((hφm n).div (by fun_prop : Measurable fun ζ : ℂ => (ζ - z) ^ 2)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun u => ?_
      by_cases hu : u ∈ Ωs ∩ closedBall 0 n
      · show ‖(Ωs ∩ closedBall 0 (n : ℝ)).indicator (fun u => m u / (u - w) ^ 2) u / (u - z) ^ 2‖ ≤ _
        rw [indicator_of_mem hu, indicator_of_mem hu.1, div_div, mul_comm ((u - w) ^ 2)]
      · show ‖(Ωs ∩ closedBall 0 (n : ℝ)).indicator (fun u => m u / (u - w) ^ 2) u / (u - z) ^ 2‖ ≤ _
        rw [indicator_of_notMem hu, zero_div, norm_zero]
        exact norm_nonneg _
    · refine Eventually.of_forall fun u => ?_
      have hev : ∀ᶠ n : ℕ in atTop, φ n u / (u - z) ^ 2 = (Ωs.indicator
          fun u => m u / ((u - z) ^ 2 * (u - w) ^ 2)) u := by
        filter_upwards [eventually_ge_atTop ⌈‖u‖⌉₊] with n hn
        have hun : u ∈ closedBall (0 : ℂ) n := by
          rw [mem_closedBall_zero_iff]
          exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
        show (Ωs ∩ closedBall 0 (n : ℝ)).indicator (fun u => m u / (u - w) ^ 2) u / (u - z) ^ 2 = _
        by_cases hu : u ∈ Ωs
        · rw [indicator_of_mem (mem_inter hu hun), indicator_of_mem hu, div_div,
            mul_comm ((u - w) ^ 2)]
        · rw [indicator_of_notMem (fun h => hu h.1), indicator_of_notMem hu, zero_div]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  -- Fatou
  have hmeas : ∀ n, AEMeasurable (fun z => (‖∫ ζ, φ n ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2)
      (volume.restrict Ω) := by
    intro n
    have hj : StronglyMeasurable (Function.uncurry fun (z ζ : ℂ) => φ n ζ / (ζ - z) ^ 2) :=
      ((hφm n).comp measurable_snd |>.div ((measurable_snd.sub measurable_fst).pow_const 2)).stronglyMeasurable
    have hI : StronglyMeasurable (fun z : ℂ => ∫ ζ, φ n ζ / (ζ - z) ^ 2) := hj.integral_prod_right'
    exact (hI.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  calc ∫⁻ z in Ω, (‖∫ u in Ωs, m u / ((u - z) ^ 2 * (u - w) ^ 2)‖₊ : ℝ≥0∞) ^ 2
      = ∫⁻ z in Ω, liminf (fun n => (‖∫ ζ, φ n ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2) atTop := by
        refine setLIntegral_congr_fun hΩ.measurableSet fun z hz => ?_
        have h := (((continuous_nnnorm.comp continuous_id).tendsto _).comp (hconv z hz))
        have h2 : Tendsto (fun n => (‖∫ ζ, φ n ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2) atTop
            (𝓝 ((‖∫ u in Ωs, m u / ((u - z) ^ 2 * (u - w) ^ 2)‖₊ : ℝ≥0∞) ^ 2)) :=
          ((ENNReal.continuous_pow 2).tendsto _).comp ((ENNReal.continuous_coe.tendsto _).comp h)
        exact h2.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ z in Ω, (‖∫ ζ, φ n ζ / (ζ - z) ^ 2‖₊ : ℝ≥0∞) ^ 2) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ _ := Filter.liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- `𝔻*` is measurable. -/
theorem gk_ext_measurable : MeasurableSet unitDiscExterior :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

/-- The image `𝗀_κ(𝔻*)` is measurable (Lusin–Souslin). -/
theorem gk_image_measurable {κ : LinfStar} (hκ : κ ∈ LinfStarBall) :
    MeasurableSet (gsans κ '' unitDiscExterior) := by
  have hc := S2C.s2c_conf_g hκ
  exact gk_ext_measurable.image_of_continuousOn_injOn hc.1.continuousOn hc.2.1

/-- A property holding a.e. on `𝔻*` holds a.e. on `𝗀_κ(𝔻*)` at `𝗀_κ⁻¹(u)` (a conformal map sends null sets to null
sets). -/
theorem gk_ae_transfer {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {P : ℂ → Prop}
    (hP : ∀ᵐ ξ ∂(volume.restrict unitDiscExterior), P ξ) :
    ∀ᵐ u ∂(volume.restrict (gsans κ '' unitDiscExterior)),
      P (Function.invFunOn (gsans κ) unitDiscExterior u) := by
  have hc := S2C.s2c_conf_g hκ
  rw [ae_restrict_iff' gk_ext_measurable] at hP
  have hN : volume {ξ | ξ ∈ unitDiscExterior ∧ ¬ P ξ} = 0 := by
    have h := ae_iff.1 hP
    simpa only [Classical.not_imp] using h
  have hB : volume (gsans κ '' {ξ | ξ ∈ unitDiscExterior ∧ ¬ P ξ}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hc.1.restrictScalars ℝ).mono fun ξ hξ => hξ.1) hN
  rw [ae_restrict_iff' (gk_image_measurable hκ)]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB] with u hu hmem
  by_contra hneg
  apply hu
  obtain ⟨ξ, hξ, rfl⟩ := hmem
  have hleft : Function.invFunOn (gsans κ) unitDiscExterior (gsans κ ξ) = ξ :=
    hc.2.1.leftInvOn_invFunOn hξ
  rw [hleft] at hneg
  exact ⟨ξ, ⟨hξ, hneg⟩, rfl⟩

/-- The phase `g'/conj g'` has norm `1` on `𝔻*`. -/
theorem gk_phase_norm {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {ξ : ℂ} (hξ : ξ ∈ unitDiscExterior) :
    ‖deriv (gsans κ) ξ / conj (deriv (gsans κ) ξ)‖ = 1 := by
  have hc := S2C.s2c_conf_g hκ
  have hne : deriv (gsans κ) ξ ≠ 0 :=
    deriv_ne_zero_of_injOn (isOpen_lt continuous_const continuous_norm) hc.1 hc.2.1 hξ
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

/-- The transported coefficient `μ_s(u) = x(g⁻¹u) g'(g⁻¹u)/conj g'(g⁻¹u)` on `Ω* = 𝗀_κ(𝔻*)` is a.e. strongly
measurable and bounded by `‖x‖∞` a.e. on `Ω*`. -/
theorem gk_mu_aesm {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (x : LinfStar) :
    AEStronglyMeasurable (fun u => x (Function.invFunOn (gsans κ) unitDiscExterior u) *
        (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
          conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u))))
      (volume.restrict (gsans κ '' unitDiscExterior)) ∧
    ∀ᵐ u ∂(volume.restrict (gsans κ '' unitDiscExterior)),
      ‖x (Function.invFunOn (gsans κ) unitDiscExterior u) *
        (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
          conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u)))‖ ≤ ‖x‖ := by
  have hc := S2C.s2c_conf_g hκ
  have hVo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  set ginv := Function.invFunOn (gsans κ) unitDiscExterior with hginv
  have hgc : ContinuousOn ginv (gsans κ '' unitDiscExterior) := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact (hc.differentiableAt_invFunOn hVo hξ).continuousAt.continuousWithinAt
  have hgm : AEMeasurable ginv (volume.restrict (gsans κ '' unitDiscExterior)) :=
    hgc.aemeasurable (gk_image_measurable hκ)
  have hxm : AEStronglyMeasurable (⇑x) (volume.restrict unitDiscExterior) := Lp.aestronglyMeasurable x
  have hxx := hxm.ae_eq_mk
  have hphase : Measurable fun ξ => deriv (gsans κ) ξ / conj (deriv (gsans κ) ξ) :=
    (measurable_deriv (gsans κ)).div (Complex.continuous_conj.measurable.comp (measurable_deriv (gsans κ)))
  have hmem : ∀ᵐ u ∂(volume.restrict (gsans κ '' unitDiscExterior)), ginv u ∈ unitDiscExterior := by
    rw [ae_restrict_iff' (gk_image_measurable hκ)]
    exact ae_of_all _ fun u hu => Function.invFunOn_mem hu
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable (fun u => hxm.mk x (ginv u) *
        (deriv (gsans κ) (ginv u) / conj (deriv (gsans κ) (ginv u))))
        (volume.restrict (gsans κ '' unitDiscExterior)) :=
      (hxm.stronglyMeasurable_mk.aestronglyMeasurable.comp_aemeasurable hgm).mul
        (hphase.comp_aemeasurable hgm).aestronglyMeasurable
    refine h1.congr ?_
    filter_upwards [gk_ae_transfer hκ hxx] with u hu
    rw [hu]
  · filter_upwards [gk_ae_transfer hκ (LinfStar_ae_norm_le x), hmem] with u hu hm
    rw [norm_mul, gk_phase_norm hκ hm, mul_one]
    exact hu

/-- Pull-back by `𝗀_κ` (TT:4140): `∬_{Ω*} |μ_s|² ρ₂² = ‖x‖₂²` (`ρ₂ = poincareDensityNearInfty`, `ρ = rho`). -/
theorem gk_pullback {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (x : LinfStar) :
    ∫⁻ u in gsans κ '' unitDiscExterior,
        (‖x (Function.invFunOn (gsans κ) unitDiscExterior u) *
          (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
            conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u)))‖₊ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (poincareDensityNearInfty (gsans κ '' unitDiscExterior) u ^ 2) =
      normL2 unitDiscExterior x ^ 2 := by
  have hc := S2C.s2c_conf_g hκ
  have hVo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  rw [d2_lintegral_image hVo hc.1 hc.2.1]
  have hR : normL2 unitDiscExterior x ^ 2 =
      ∫⁻ ξ in unitDiscExterior, (‖x ξ‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (rho ξ) := by
    unfold normL2
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hR]
  refine setLIntegral_congr_fun hVo.measurableSet fun ξ hξ => ?_
  have hleft : Function.invFunOn (gsans κ) unitDiscExterior (gsans κ ξ) = ξ :=
    hc.2.1.leftInvOn_invFunOn hξ
  have hρ := hbSurj_exterior_density hκ ⟨ξ, hξ, rfl⟩
  have hne : deriv (gsans κ) ξ ≠ 0 := deriv_ne_zero_of_injOn hVo hc.1 hc.2.1 hξ
  have hi : deriv (Function.invFunOn (gsans κ) unitDiscExterior) (gsans κ ξ) = (deriv (gsans κ) ξ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (t1_deriv_invFunOn_mul hVo hc hξ)
  have hp : ‖deriv (gsans κ) ξ / conj (deriv (gsans κ) ξ)‖₊ = 1 := by
    rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one, gk_phase_norm hκ hξ]
  rw [hρ, hleft, hi, nnnorm_mul, hp, mul_one, mul_left_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 2
  rw [norm_inv]
  have hn : ‖deriv (gsans κ) ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  field_simp

/-! ### The `L²` bound of the variation kernel at a fixed base point (TT:4116–4146) -/

theorem gk_ofReal_inv4 {a : ℂ} (ha : a ≠ 0) :
    ENNReal.ofReal (1 / ‖a‖ ^ 4) = ((‖a‖₊ : ℝ≥0∞) ^ 4)⁻¹ := by
  have hpos : 0 < ‖a‖ ^ 4 := by positivity
  rw [one_div, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl

/-- `remark_2_8` in `ℝ≥0∞` form. -/
theorem gk_remark28_lint {κ : LinfStar} (hκ : κ ∈ LinfStarBall) {u : ℂ} (hu : u ∈ gsans κ '' unitDiscExterior) :
    ∫⁻ w in fsans κ '' unitDisc, ((‖u - w‖₊ : ℝ≥0∞) ^ 4)⁻¹ ≤
      ENNReal.ofReal (π / 4 * poincareDensityNearInfty (gsans κ '' unitDiscExterior) u ^ 2) := by
  have hΩo : IsOpen (gsans κ '' unitDiscExterior) := (S2C.s2c_conf_g hκ).isOpen bc_hEo
  have hdisj : Disjoint (gsans κ '' unitDiscExterior) (fsans κ '' unitDisc) :=
    (AppB.b8_welding_normalized_pair hκ).2.2.2.2.2.symm
  obtain ⟨r, hr, hrw⟩ := gk_sep hΩo hdisj hu
  obtain ⟨hint4, -⟩ := Ch2.s2c_l4_outside_ball u hr
  have hsub : fsans κ '' unitDisc ⊆ {ω : ℂ | r ≤ ‖ω - u‖} := fun w hw => hrw w hw
  have hint : IntegrableOn (fun w : ℂ => 1 / ‖w - u‖ ^ 4) (fsans κ '' unitDisc) := by
    simpa only [one_div] using hint4.mono_set hsub
  have hΩm : MeasurableSet (fsans κ '' unitDisc) := ((S2C.s2c_conf_f hκ).isOpen isOpen_ball).measurableSet
  have heq : ∫⁻ w in fsans κ '' unitDisc, ((‖u - w‖₊ : ℝ≥0∞) ^ 4)⁻¹ =
      ENNReal.ofReal (∫ w in fsans κ '' unitDisc, 1 / ‖w - u‖ ^ 4) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => by positivity)]
    refine setLIntegral_congr_fun hΩm fun w hw => ?_
    have hne : w - u ≠ 0 := by
      intro h
      have := hrw w hw
      rw [h, norm_zero] at this
      linarith
    rw [gk_ofReal_inv4 hne, ← nnnorm_neg, neg_sub]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (remark_2_8 hκ hu)

/-- Per base point `κ`: if `k(a, b) = π⁻² f'(a) f'(b) ∬_{Ω*} μ_s/((u - f a)²(u - f b)²)` off the diagonal, then
`∬∬_{𝔻×𝔻} |k|² ≤ (4π)⁻¹ ‖x‖₂²`. -/
theorem gk_I_bound {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (x : LinfStar) {k : ℂ → ℂ → ℂ}
    (hk : ∀ a ∈ unitDisc, ∀ b ∈ unitDisc, a ≠ b → k a b =
      1 / π ^ 2 * (deriv (fsans κ) a * deriv (fsans κ) b) *
        ∫ u in gsans κ '' unitDiscExterior,
          x (Function.invFunOn (gsans κ) unitDiscExterior u) *
            (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
              conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u))) /
            ((u - fsans κ a) ^ 2 * (u - fsans κ b) ^ 2)) :
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖k q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal (1 / (4 * π)) * normL2 unitDiscExterior x ^ 2 := by
  set f := fsans κ with hf
  set Ω := fsans κ '' unitDisc with hΩ
  set Ωs := gsans κ '' unitDiscExterior with hΩs
  set μt : ℂ → ℂ := fun u => x (Function.invFunOn (gsans κ) unitDiscExterior u) *
    (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
      conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u))) with hμt
  have hcf := S2C.s2c_conf_f hκ
  have hΩo : IsOpen Ω := hcf.isOpen isOpen_ball
  have hΩso : IsOpen Ωs := (S2C.s2c_conf_g hκ).isOpen bc_hEo
  have hdisj : Disjoint Ω Ωs := (AppB.b8_welding_normalized_pair hκ).2.2.2.2.2
  obtain ⟨hae, hbd⟩ := gk_mu_aesm hκ x
  -- a measurable, globally bounded version `m` of `μ_s` on `Ω*`
  set m0 := hae.mk μt with hm0
  have hm0m : Measurable m0 := hae.stronglyMeasurable_mk.measurable
  set m : ℂ → ℂ := fun u => if ‖m0 u‖ ≤ ‖x‖ then m0 u else 0 with hmdef
  have hmm : Measurable m :=
    Measurable.ite (measurableSet_le hm0m.norm measurable_const) hm0m measurable_const
  have hmb : ∀ u, ‖m u‖ ≤ ‖x‖ := by
    intro u
    simp only [hmdef]
    split_ifs with h
    · exact h
    · simpa using norm_nonneg x
  have hmeq : μt =ᵐ[volume.restrict Ωs] m := by
    filter_upwards [hae.ae_eq_mk, hbd] with u h1 h2
    have h1' : μt u = m0 u := h1
    have h2' : ‖μt u‖ ≤ ‖x‖ := h2
    have h3 : ‖m0 u‖ ≤ ‖x‖ := by rw [← h1']; exact h2'
    show μt u = if ‖m0 u‖ ≤ ‖x‖ then m0 u else 0
    rw [if_pos h3, h1']
  set J : ℂ → ℂ → ℂ := fun z w => ∫ u in Ωs, μt u / ((u - z) ^ 2 * (u - w) ^ 2) with hJ
  have hJm : ∀ z w, J z w = ∫ u in Ωs, m u / ((u - z) ^ 2 * (u - w) ^ 2) := by
    intro z w
    refine integral_congr_ae ?_
    filter_upwards [hmeq] with u hu
    rw [hu]
  have hJsymm : ∀ z w, J z w = J w z := by
    intro z w
    simp only [hJ, mul_comm ((_ - z) ^ 2)]
  -- step 1: Tonelli inequality on the product
  have hprod : volume.restrict (unitDisc ×ˢ unitDisc) =
      (volume.restrict unitDisc).prod (volume.restrict unitDisc) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have h1 : (∫⁻ q in unitDisc ×ˢ unitDisc, (‖k q.1 q.2‖₊ : ℝ≥0∞) ^ 2) ≤
      ∫⁻ a in unitDisc, ∫⁻ b in unitDisc, (‖k a b‖₊ : ℝ≥0∞) ^ 2 := by
    rw [hprod]
    exact lintegral_prod_le _
  -- step 2: change of variables in `b` and then in `a`
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsq : ∀ c : ℂ, ENNReal.ofReal (‖c‖ ^ 2) = (‖c‖₊ : ℝ≥0∞) ^ 2 := by
    intro c
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  set cπ : ℝ≥0∞ := (‖(1 / (π : ℂ) ^ 2)‖₊ : ℝ≥0∞) ^ 2 with hcπ
  have hcπ' : cπ = ENNReal.ofReal (1 / π ^ 4) := by
    rw [hcπ, ← hsq]
    congr 1
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    ring
  have hcπt : cπ ≠ ⊤ := by rw [hcπ']; exact ENNReal.ofReal_ne_top
  set H : ℂ → ℝ≥0∞ := fun z => cπ * ∫⁻ w in Ω, (‖J z w‖₊ : ℝ≥0∞) ^ 2 with hH
  -- step 2: the inner integral in `b`
  have h2 : ∀ a ∈ unitDisc, ∫⁻ b in unitDisc, (‖k a b‖₊ : ℝ≥0∞) ^ 2 =
      (‖deriv f a‖₊ : ℝ≥0∞) ^ 2 * H (f a) := by
    intro a ha
    have hne : ∀ᵐ b ∂(volume.restrict unitDisc), b ≠ a :=
      ae_restrict_of_ae (volume.ae_ne a)
    calc ∫⁻ b in unitDisc, (‖k a b‖₊ : ℝ≥0∞) ^ 2
        = ∫⁻ b in unitDisc, ENNReal.ofReal (‖deriv f b‖ ^ 2) *
            (cπ * (‖deriv f a‖₊ : ℝ≥0∞) ^ 2 * (‖J (f a) (f b)‖₊ : ℝ≥0∞) ^ 2) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hne, ae_restrict_mem isOpen_ball.measurableSet] with b hb hbD
          rw [hk a ha b hbD (Ne.symm hb), hsq]
          simp only [nnnorm_mul, ENNReal.coe_mul, mul_pow, hcπ]
          ring
      _ = ∫⁻ w in Ω, cπ * (‖deriv f a‖₊ : ℝ≥0∞) ^ 2 * (‖J (f a) w‖₊ : ℝ≥0∞) ^ 2 :=
          (d2_lintegral_image (U := unitDisc) isOpen_ball hcf.1 hcf.2.1
            (fun w => cπ * (‖deriv f a‖₊ : ℝ≥0∞) ^ 2 * (‖J (f a) w‖₊ : ℝ≥0∞) ^ 2)).symm
      _ = (‖deriv f a‖₊ : ℝ≥0∞) ^ 2 * H (f a) := by
          rw [hH]
          simp only
          rw [← lintegral_const_mul' _ _ hcπt, ← lintegral_const_mul' _ _ (by simp)]
          refine lintegral_congr fun w => ?_
          ring
  -- step 3: the outer integral in `a`
  have h3 : ∫⁻ a in unitDisc, ∫⁻ b in unitDisc, (‖k a b‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ z in Ω, H z := by
    have hDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
    rw [setLIntegral_congr_fun hDm h2, d2_lintegral_image (U := unitDisc) isOpen_ball hcf.1 hcf.2.1 H]
    refine setLIntegral_congr_fun hDm fun a _ => ?_
    rw [hsq]
  -- step 4: Beurling in `w` for fixed `z`
  have h4 : ∀ z ∈ Ω, H z ≤ cπ * (ENNReal.ofReal (π ^ 2) *
      ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - z‖₊ : ℝ≥0∞) ^ 4)⁻¹) := by
    intro z hz
    refine mul_le_mul' le_rfl ?_
    have he : ∀ w, J z w = ∫ u in Ωs, m u / ((u - w) ^ 2 * (u - z) ^ 2) := fun w => by
      rw [hJsymm, hJm]
    simp only [he]
    exact gk_beurling_kernel hΩo hdisj hΩso.measurableSet hmm hmb hz
  -- step 5: Tonelli and `remark_2_8`
  have hjm : Measurable (Function.uncurry fun (z u : ℂ) =>
      (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - z‖₊ : ℝ≥0∞) ^ 4)⁻¹) := by
    refine ((hmm.comp measurable_snd).nnnorm.coe_nnreal_ennreal.pow_const 2).mul ?_
    exact (((measurable_snd.sub measurable_fst).nnnorm.coe_nnreal_ennreal.pow_const 4).inv)
  have h5 : ∫⁻ z in Ω, ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - z‖₊ : ℝ≥0∞) ^ 4)⁻¹ ≤
      ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (π / 4 * poincareDensityNearInfty Ωs u ^ 2) := by
    rw [lintegral_lintegral_swap hjm.aemeasurable]
    refine setLIntegral_mono' hΩso.measurableSet fun u hu => ?_
    rw [lintegral_const_mul' _ _ (by simp)]
    exact mul_le_mul' le_rfl (gk_remark28_lint hκ hu)
  -- step 6: the pull-back
  have h6 : ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (π / 4 * poincareDensityNearInfty Ωs u ^ 2) =
      ENNReal.ofReal (π / 4) * normL2 unitDiscExterior x ^ 2 := by
    rw [← gk_pullback hκ x, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hmeq] with u hu
    rw [← hu, ENNReal.ofReal_mul (by positivity)]
    ring
  -- assembly
  calc (∫⁻ q in unitDisc ×ˢ unitDisc, (‖k q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      ≤ ∫⁻ z in Ω, H z := h1.trans h3.le
    _ ≤ ∫⁻ z in Ω, cπ * (ENNReal.ofReal (π ^ 2) *
          ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - z‖₊ : ℝ≥0∞) ^ 4)⁻¹) :=
        setLIntegral_mono' hΩo.measurableSet h4
    _ = cπ * ENNReal.ofReal (π ^ 2) *
          ∫⁻ z in Ω, ∫⁻ u in Ωs, (‖m u‖₊ : ℝ≥0∞) ^ 2 * ((‖u - z‖₊ : ℝ≥0∞) ^ 4)⁻¹ := by
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hcπt ENNReal.ofReal_ne_top)]
        refine lintegral_congr fun z => ?_
        ring
    _ ≤ cπ * ENNReal.ofReal (π ^ 2) * (ENNReal.ofReal (π / 4) * normL2 unitDiscExterior x ^ 2) :=
        mul_le_mul' le_rfl (h5.trans h6.le)
    _ = ENNReal.ofReal (1 / (4 * π)) * normL2 unitDiscExterior x ^ 2 := by
        rw [hcπ', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        try ring

/-! ### Measurability of the variation kernel in `(a, b)` -/

theorem gk_offdiag_open :
    IsOpen {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} :=
  (isOpen_ball.preimage continuous_fst).inter
    ((isOpen_ball.preimage continuous_snd).inter (isOpen_ne_fun continuous_fst continuous_snd))

/-- The right-hand side of `l27_general` in source coordinates is measurable on the off-diagonal part of `𝔻 × 𝔻`. -/
theorem gk_kform_meas {κ : LinfStar} (hκ : κ ∈ LinfStarBall) (x : LinfStar) :
    Measurable ({q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2}.indicator fun q =>
      1 / π ^ 2 * (deriv (fsans κ) q.1 * deriv (fsans κ) q.2) *
        ∫ u in gsans κ '' unitDiscExterior,
          x (Function.invFunOn (gsans κ) unitDiscExterior u) *
            (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
              conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u))) /
            ((u - fsans κ q.1) ^ 2 * (u - fsans κ q.2) ^ 2)) := by
  set D := {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} with hD
  have hDo : IsOpen D := gk_offdiag_open
  have hDm : MeasurableSet D := hDo.measurableSet
  set f := fsans κ with hf
  have hcf := S2C.s2c_conf_f hκ
  have hfc : ContinuousOn f unitDisc := hcf.1.continuousOn
  have hf'c : ContinuousOn (deriv f) unitDisc := (hcf.1.deriv isOpen_ball).continuousOn
  set μt : ℂ → ℂ := fun u => x (Function.invFunOn (gsans κ) unitDiscExterior u) *
    (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u) /
      conj (deriv (gsans κ) (Function.invFunOn (gsans κ) unitDiscExterior u))) with hμt
  obtain ⟨hae, -⟩ := gk_mu_aesm hκ x
  set m := hae.mk μt with hm
  have hmm : Measurable m := hae.stronglyMeasurable_mk.measurable
  -- the kernel integral as a measurable function of the pair of poles
  set Jt : ℂ × ℂ → ℂ := fun p => ∫ u in gsans κ '' unitDiscExterior, m u / ((u - p.1) ^ 2 * (u - p.2) ^ 2)
    with hJt
  have hJtm : Measurable Jt := by
    have hj : StronglyMeasurable (Function.uncurry fun (p : ℂ × ℂ) (u : ℂ) =>
        m u / ((u - p.1) ^ 2 * (u - p.2) ^ 2)) := by
      refine Measurable.stronglyMeasurable ?_
      exact (hmm.comp measurable_snd).div
        (((measurable_snd.sub (measurable_fst.comp measurable_fst)).pow_const 2).mul
          ((measurable_snd.sub (measurable_snd.comp measurable_fst)).pow_const 2))
    exact (hj.integral_prod_right' (ν := volume.restrict (gsans κ '' unitDiscExterior))).measurable
  -- measurable versions of the pole map and of the Jacobian factor
  have hPc : ContinuousOn (fun q : ℂ × ℂ => (f q.1, f q.2)) D :=
    ((hfc.comp continuous_fst.continuousOn fun q hq => hq.1).prodMk
      (hfc.comp continuous_snd.continuousOn fun q hq => hq.2.1))
  have hPm : Measurable (D.piecewise (fun q : ℂ × ℂ => (f q.1, f q.2)) fun _ => ((0 : ℂ), (0 : ℂ))) :=
    hPc.measurable_piecewise continuousOn_const hDm
  have hFc : ContinuousOn (fun q : ℂ × ℂ => deriv f q.1 * deriv f q.2) D :=
    (hf'c.comp continuous_fst.continuousOn fun q hq => hq.1).mul
      (hf'c.comp continuous_snd.continuousOn fun q hq => hq.2.1)
  have hFm : Measurable (D.piecewise (fun q : ℂ × ℂ => deriv f q.1 * deriv f q.2) fun _ => (0 : ℂ)) :=
    hFc.measurable_piecewise continuousOn_const hDm
  have hmeas : Measurable (D.piecewise (fun q : ℂ × ℂ => 1 / π ^ 2 *
      (D.piecewise (fun q : ℂ × ℂ => deriv f q.1 * deriv f q.2) (fun _ => (0 : ℂ)) q) *
        Jt (D.piecewise (fun q : ℂ × ℂ => (f q.1, f q.2)) (fun _ => ((0 : ℂ), (0 : ℂ))) q))
      fun _ => (0 : ℂ)) :=
    ((measurable_const.mul hFm).mul (hJtm.comp hPm)).piecewise hDm measurable_const
  have heq : (D.piecewise (fun q : ℂ × ℂ => 1 / π ^ 2 *
      (D.piecewise (fun q : ℂ × ℂ => deriv f q.1 * deriv f q.2) (fun _ => (0 : ℂ)) q) *
        Jt (D.piecewise (fun q : ℂ × ℂ => (f q.1, f q.2)) (fun _ => ((0 : ℂ), (0 : ℂ))) q))
      fun _ => (0 : ℂ)) = (D.indicator fun q =>
      1 / π ^ 2 * (deriv f q.1 * deriv f q.2) *
        ∫ u in gsans κ '' unitDiscExterior, μt u / ((u - f q.1) ^ 2 * (u - f q.2) ^ 2)) := by
    funext q
    by_cases hq : q ∈ D
    · rw [Set.piecewise_eq_of_mem _ _ _ hq, Set.indicator_of_mem hq, Set.piecewise_eq_of_mem _ _ _ hq,
        Set.piecewise_eq_of_mem _ _ _ hq]
      congr 1
      show Jt (f q.1, f q.2) = _
      refine (integral_congr_ae ?_).symm
      filter_upwards [hae.ae_eq_mk] with u hu
      have hu' : μt u = m u := hu
      show μt u / _ = m u / _
      rw [hu']
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq, Set.indicator_of_notMem hq]
  rw [← heq]
  exact hmeas

/-! ### One chart step keeps `K₁` Hilbert–Schmidt -/

/-- `l27_general` in source coordinates: the derivative of `v ↦ K₁(𝖿^v)(a, b)` along `γ'` at `γ s` is
`π⁻² f'(a) f'(b) ∬_{Ω*} μ_s/((u - f a)²(u - f b)²)`. -/
theorem gk_k_eq {γ : ℝ → LinfStar} {γ'' : LinfStar} {s : ℝ} (hγ : HasDerivAt γ γ'' s)
    (hball : γ s ∈ LinfStarBall) {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) a b) (γ s) γ'' =
      1 / π ^ 2 * (deriv (fsans (γ s)) a * deriv (fsans (γ s)) b) *
        ∫ u in gsans (γ s) '' unitDiscExterior,
          fderiv ℂ (fun l => beltramiMul l (beltramiInv (γ s))) (γ s) γ''
              (Function.invFunOn (gsans (γ s)) unitDiscExterior u) *
            (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u) /
              conj (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u))) /
            ((u - fsans (γ s) a) ^ 2 * (u - fsans (γ s) b) ^ 2) := by
  have hcf := S2C.s2c_conf_f hball
  have hD : IsOpen unitDisc := isOpen_ball
  have hfa : Function.invFunOn (fsans (γ s)) unitDisc (fsans (γ s) a) = a := hcf.2.1.leftInvOn_invFunOn ha
  have hfb : Function.invFunOn (fsans (γ s)) unitDisc (fsans (γ s) b) = b := hcf.2.1.leftInvOn_invFunOn hb
  have hda := t1_deriv_invFunOn_mul hD hcf ha
  have hdb := t1_deriv_invFunOn_mul hD hcf hb
  have hfa0 : deriv (fsans (γ s)) a ≠ 0 := deriv_ne_zero_of_injOn hD hcf.1 hcf.2.1 ha
  have hfb0 : deriv (fsans (γ s)) b ≠ 0 := deriv_ne_zero_of_injOn hD hcf.1 hcf.2.1 hb
  have hzw : fsans (γ s) a ≠ fsans (γ s) b := fun h => hab (hcf.2.1 ha hb h)
  have hL := l27_general hγ hball (mem_image_of_mem (fsans (γ s)) ha) (mem_image_of_mem (fsans (γ s)) hb) hzw
  simp only [hfa, hfb] at hL
  -- our derivative, times the constant Jacobian factors
  have hΦ := ((l27_kerK1_differentiableOn ha hb hab (γ s) hball).differentiableAt
    (isOpen_ball.mem_nhds hball)).hasFDerivAt
  have hc := (((hΦ.restrictScalars ℝ).comp_hasDerivAt s hγ).mul_const (deriv (Function.invFunOn (fsans (γ s)) unitDisc) (fsans (γ s) a))).mul_const
    (deriv (Function.invFunOn (fsans (γ s)) unitDisc) (fsans (γ s) b))
  have huniq := hc.unique hL
  simp only [ContinuousLinearMap.coe_restrictScalars'] at huniq
  have hia : deriv (Function.invFunOn (fsans (γ s)) unitDisc) (fsans (γ s) a) = (deriv (fsans (γ s)) a)⁻¹ := eq_inv_of_mul_eq_one_left hda
  have hib : deriv (Function.invFunOn (fsans (γ s)) unitDisc) (fsans (γ s) b) = (deriv (fsans (γ s)) b)⁻¹ := eq_inv_of_mul_eq_one_left hdb
  rw [hia, hib] at huniq
  have key : fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) a b) (γ s) γ'' =
      (1 / π ^ 2 * ∫ u in gsans (γ s) '' unitDiscExterior,
          fderiv ℂ (fun l => beltramiMul l (beltramiInv (γ s))) (γ s) γ''
              (Function.invFunOn (gsans (γ s)) unitDiscExterior u) *
            (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u) /
              conj (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u))) /
            ((u - fsans (γ s) a) ^ 2 * (u - fsans (γ s) b) ^ 2)) * deriv (fsans (γ s)) a * deriv (fsans (γ s)) b := by
    rw [← huniq]
    field_simp
  rw [key]
  ring

theorem gk_sq_tri (x y : ℂ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x - y‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
  have h : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg x, norm_nonneg (x - y), norm_nonneg y, sq_nonneg (‖x - y‖ - ‖y‖)]
  have e : ∀ c : ℂ, (‖c‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖c‖ ^ 2) := by
    intro c
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [e, e, e, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

theorem gk_offdiag_ae :
    ∀ᵐ q ∂(volume.restrict (unitDisc ×ˢ unitDisc)), q ∈ {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} := by
  have hdiag : (volume : Measure (ℂ × ℂ)) {q | q.1 = q.2} = 0 := by
    rw [Measure.volume_eq_prod]
    have hm : MeasurableSet {q : ℂ × ℂ | q.1 = q.2} := measurableSet_diagonal
    rw [Measure.measure_prod_null hm]
    refine Eventually.of_forall fun a => ?_
    have : Prod.mk a ⁻¹' {q : ℂ × ℂ | q.1 = q.2} = {a} := by
      ext b
      simp [eq_comm]
    simp [this]
  have h1 : ∀ᵐ q ∂(volume : Measure (ℂ × ℂ)), q.1 ≠ q.2 := by
    rw [ae_iff]
    simpa using hdiag
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem (isOpen_ball.prod isOpen_ball).measurableSet]
    with q hq hm
  exact ⟨hm.1, hm.2, hq⟩

theorem gk_kerK1_aemeas {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AEMeasurable (fun q : ℂ × ℂ => (‖kerK1 (fsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (volume.restrict (unitDisc ×ˢ unitDisc)) := by
  set D := {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} with hD
  have hDo : IsOpen D := gk_offdiag_open
  have hcf := S2C.s2c_conf_f hμ
  have hfc : ContinuousOn (fsans μ) unitDisc := hcf.1.continuousOn
  have hf'c : ContinuousOn (deriv (fsans μ)) unitDisc := (hcf.1.deriv isOpen_ball).continuousOn
  have hcont : ContinuousOn (fun q : ℂ × ℂ => kerK1 (fsans μ) q.1 q.2) D := by
    have h1 : ContinuousOn (fun q : ℂ × ℂ => 1 / π * (1 / (q.1 - q.2) ^ 2 -
        deriv (fsans μ) q.1 * deriv (fsans μ) q.2 / (fsans μ q.1 - fsans μ q.2) ^ 2)) D := by
      refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
      · refine continuousOn_const.div ((continuous_fst.sub continuous_snd).pow 2).continuousOn ?_
        intro q hq
        exact pow_ne_zero 2 (sub_ne_zero.2 hq.2.2)
      · refine ContinuousOn.div ?_ ?_ ?_
        · exact (hf'c.comp continuous_fst.continuousOn fun q hq => hq.1).mul
            (hf'c.comp continuous_snd.continuousOn fun q hq => hq.2.1)
        · exact ((hfc.comp continuous_fst.continuousOn fun q hq => hq.1).sub
            (hfc.comp continuous_snd.continuousOn fun q hq => hq.2.1)).pow 2
        · intro q hq
          exact pow_ne_zero 2 (sub_ne_zero.2 fun h => hq.2.2 (hcf.2.1 hq.1 hq.2.1 h))
    refine h1.congr fun q hq => ?_
    simp only [kerK1, if_neg hq.2.2]
  have hae : AEMeasurable (fun q : ℂ × ℂ => (‖kerK1 (fsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) (volume.restrict D) :=
    ((hcont.aemeasurable hDo.measurableSet).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hset : (unitDisc ×ˢ unitDisc : Set (ℂ × ℂ)) =ᵐ[volume] D := by
    have h := gk_offdiag_ae
    have hm : MeasurableSet (unitDisc ×ˢ unitDisc : Set (ℂ × ℂ)) := (isOpen_ball.prod isOpen_ball).measurableSet
    rw [ae_restrict_iff' hm] at h
    exact Filter.eventuallyEq_set.2 (h.mono fun q hq => ⟨hq, fun hd => ⟨hd.1, hd.2.1⟩⟩)
  rwa [Measure.restrict_congr_set hset]

/-- One chart step keeps `𝖪₁` Hilbert–Schmidt (`∬∬_{𝔻×𝔻} |K₁|² < ∞`), TT:4110–4160 along `γ(s) = (sν) * κ`. -/
theorem gk_step {κ ν : LinfStarBall}
    (hν : ∃ φ : A2 unitDisc, ‖φ‖ < min (Real.sqrt (π / 3)) (2 * delta0 / Real.sqrt (12 / π)) ∧
      (ν : LinfStar) = Lambda (A2toAInf φ))
    (hK : (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞) :
    (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (beltramiMul (ν : LinfStar) (κ : LinfStar))) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  obtain ⟨φ, hφ, hνe⟩ := hν
  obtain ⟨hn, hharm, hsm, -⟩ := gtp_small_a hφ
  rw [← hνe] at hharm hsm
  have hd := delta0_bounds
  have hν1 : ‖(ν : LinfStar)‖ < 1 := hsm.trans hd.2
  have hνL : normL2 unitDiscExterior (ν : LinfStar) = ENNReal.ofReal (2 * ‖φ‖) := by
    rw [hνe]; exact gtp_normL2_Lambda φ
  obtain ⟨γ', hγ'c, hγ'⟩ := gk_path_C1 (ν := (ν : LinfStar)) (κ := (κ : LinfStar)) hν1 κ.2
  set γ : ℝ → LinfStar := fun t => beltramiMul ((t : ℂ) • (ν : LinfStar)) (κ : LinfStar) with hγ
  have hsν : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • (ν : LinfStar) ∈ LinfStarBall := by
    intro s hs
    have : ‖(s : ℂ) • (ν : LinfStar)‖ < 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    simpa [LinfStarBall] using this
  have hγb : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ LinfStarBall := fun s hs => bg_mul_mem_ball κ.2 (hsν s hs)
  have hγ0 : γ 0 = (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_zero, zero_smul]
    exact grp_zero_mul κ.2
  have hγ1 : γ 1 = beltramiMul (ν : LinfStar) (κ : LinfStar) := by
    simp only [hγ, Complex.ofReal_one, one_smul]
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hγcont : ContinuousOn γ (Icc 0 1) := fun s hs =>
    (hγ' s hs).1.continuousAt.continuousWithinAt
  -- the variation kernel
  set D := {q : ℂ × ℂ | q.1 ∈ unitDisc ∧ q.2 ∈ unitDisc ∧ q.1 ≠ q.2} with hDdef
  set k : ℝ → ℂ × ℂ → ℂ := fun s q => fderiv ℂ (fun v : LinfStar => kerK1 (fsans v) q.1 q.2) (γ s) (γ' s)
    with hk
  have hkder : ∀ q ∈ D, ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => kerK1 (fsans (γ t)) q.1 q.2) (k s q) s := by
    intro q hq s hs
    have hΦ := ((l27_kerK1_differentiableOn hq.1 hq.2.1 hq.2.2 (γ s) (hγb s hs)).differentiableAt
      (isOpen_ball.mem_nhds (hγb s hs))).hasFDerivAt
    exact (hΦ.restrictScalars ℝ).comp_hasDerivAt s (hγ' s hs).1
  have hkcont : ∀ q ∈ D, ContinuousOn (fun s => k s q) (Icc 0 1) := by
    intro q hq
    have hF := (l27_fderiv_continuousOn hq.1 hq.2.1 hq.2.2).comp hγcont (fun s hs => hγb s hs)
    exact hF.clm_apply hγ'c
  -- the tangent: `μ̃_s = D_{sν}R_{(sν)⁻¹}(ν)`
  set xs : ℝ → LinfStar := fun s =>
    fderiv ℂ (fun l => beltramiMul l (beltramiInv ((s : ℂ) • (ν : LinfStar)))) ((s : ℂ) • (ν : LinfStar))
      (ν : LinfStar) with hxs
  have hkform : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ D, k s q =
      1 / π ^ 2 * (deriv (fsans (γ s)) q.1 * deriv (fsans (γ s)) q.2) *
        ∫ u in gsans (γ s) '' unitDiscExterior,
          xs s (Function.invFunOn (gsans (γ s)) unitDiscExterior u) *
            (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u) /
              conj (deriv (gsans (γ s)) (Function.invFunOn (gsans (γ s)) unitDiscExterior u))) /
            ((u - fsans (γ s) q.1) ^ 2 * (u - fsans (γ s) q.2) ^ 2) := by
    intro s hs q hq
    have h := gk_k_eq (hγ' s hs).1 (hγb s hs) hq.1 hq.2.1 hq.2.2
    rw [(hγ' s hs).2] at h
    exact h
  -- uniform bound for the tangent
  set B : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * π)) *
    (ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖)) ^ 2 with hB
  have hBfin : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
  have hxbound : ∀ s ∈ Icc (0 : ℝ) 1, normL2 unitDiscExterior (xs s) ≤
      ENNReal.ofReal (Real.sqrt 2 / (1 - ‖(ν : LinfStar)‖) ^ 2) * ENNReal.ofReal (2 * ‖φ‖) := by
    intro s hs
    have hsn : ‖(s : ℂ) • (ν : LinfStar)‖ ≤ ‖(ν : LinfStar)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.1]
      nlinarith [norm_nonneg (ν : LinfStar), hs.2]
    have hh : (s : ℂ) • (ν : LinfStar) ∈ harmonicBeltrami := Submodule.smul_mem _ _ hharm
    have hδ : ‖(s : ℂ) • (ν : LinfStar)‖ < delta0 := lt_of_le_of_lt hsn hsm
    have h := (grp_cor_2_6 hh hδ (hsν s hs) (ν : LinfStar)).2
    rw [hνL] at h
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h1 : 0 < 1 - ‖(ν : LinfStar)‖ := by linarith
    have h2 : 1 - ‖(ν : LinfStar)‖ ≤ 1 - ‖(s : ℂ) • (ν : LinfStar)‖ := by linarith
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_left₀ h1.le h2 2)
  -- a jointly measurable version of the kernel (Carathéodory)
  set c : ℝ → ℝ := fun s => max 0 (min 1 s) with hcdef
  have hcI : ∀ s, c s ∈ Icc (0 : ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcs : ∀ s ∈ Icc (0 : ℝ) 1, c s = s := fun s hs => by
    simp only [hcdef, min_eq_right hs.2, max_eq_right hs.1]
  set K : ℝ → ℂ × ℂ → ℂ := fun s q => D.indicator (fun q => k (c s) q) q with hKdef
  have hKform : ∀ s, K s = D.indicator fun q =>
      1 / π ^ 2 * (deriv (fsans (γ (c s))) q.1 * deriv (fsans (γ (c s))) q.2) *
        ∫ u in gsans (γ (c s)) '' unitDiscExterior,
          xs (c s) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) *
            (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u) /
              conj (deriv (gsans (γ (c s))) (Function.invFunOn (gsans (γ (c s))) unitDiscExterior u))) /
            ((u - fsans (γ (c s)) q.1) ^ 2 * (u - fsans (γ (c s)) q.2) ^ 2) := by
    intro s
    funext q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact hkform (c s) (hcI s) q hq
    · simp only [hKdef, Set.indicator_of_notMem hq]
  have hKm : ∀ s, Measurable (K s) := fun s => by
    rw [hKform s]
    exact gk_kform_meas (hγb (c s) (hcI s)) (xs (c s))
  have hKc : ∀ q, Continuous fun s => K s q := by
    intro q
    by_cases hq : q ∈ D
    · simp only [hKdef, Set.indicator_of_mem hq]
      exact (hkcont q hq).comp_continuous hcc hcI
    · simp only [hKdef, Set.indicator_of_notMem hq]
      exact continuous_const
  have hjoint : Measurable (Function.uncurry K) := measurable_uncurry_of_continuous_of_measurable hKc hKm
  -- pointwise FTC
  have hpt : ∀ q ∈ D, (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    intro q hq
    have h := gk_ftc_sq (F := fun t => kerK1 (fsans (γ t)) q.1 q.2) (F' := fun s => k s q)
      (hkder q hq) (hkcont q hq)
    refine h.trans (le_of_eq (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_))
    simp only [hKdef, Set.indicator_of_mem hq, hcs s hs]
  -- per-`s` bound
  have hper : ∀ s, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 ≤ B := by
    intro s
    have hb := gk_I_bound (hγb (c s) (hcI s)) (xs (c s)) (k := fun a b => K s (a, b)) (by
      intro a ha b hb hab
      have hq : (a, b) ∈ D := ⟨ha, hb, hab⟩
      show K s (a, b) = _
      rw [hKform s, Set.indicator_of_mem hq])
    refine hb.trans ?_
    rw [hB]
    exact mul_le_mul' le_rfl (pow_le_pow_left₀ bot_le (hxbound (c s) (hcI s)) 2)
  -- Tonelli
  have hswap : ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 =
      ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ q in unitDisc ×ˢ unitDisc, (‖K s q‖₊ : ℝ≥0∞) ^ 2 := by
    refine lintegral_lintegral_swap ?_
    have hm2 : Measurable (fun p : (ℂ × ℂ) × ℝ => (‖K p.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      ((hjoint.comp measurable_swap).nnnorm.coe_nnreal_ennreal).pow_const 2
    exact hm2.aemeasurable
  have hdiff : ∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 < ∞ := by
    calc _ ≤ ∫⁻ q in unitDisc ×ˢ unitDisc, ∫⁻ s in Icc (0 : ℝ) 1, (‖K s q‖₊ : ℝ≥0∞) ^ 2 :=
          lintegral_mono_ae (gk_offdiag_ae.mono fun q hq => hpt q hq)
      _ = _ := hswap
      _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, B := lintegral_mono fun s => hper s
      _ = B * volume (Icc (0 : ℝ) 1) := setLIntegral_const _ _
      _ < ∞ := by
          rw [Real.volume_Icc]
          exact ENNReal.mul_lt_top hBfin.lt_top ENNReal.ofReal_lt_top
  -- conclusion
  rw [← hγ1]
  have hK0 : ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 < ∞ := by
    rw [hγ0]; exact hK
  calc ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (γ 1)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ q in unitDisc ×ˢ unitDisc,
          (2 * (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 +
            2 * (‖kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
        lintegral_mono fun q => gk_sq_tri _ _
    _ ≤ 2 * (∫⁻ q in unitDisc ×ˢ unitDisc,
            (‖kerK1 (fsans (γ 1)) q.1 q.2 - kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) +
          2 * ∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (γ 0)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
        rw [lintegral_add_right' _ ((gk_kerK1_aemeas (hγb 0 h01)).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hdiff,
          ENNReal.mul_lt_top (by norm_num) hK0⟩

/-! ### The base point and the exterior kernel -/

/-- At the origin `𝖿^0 = id`, so `K₁(𝖿^0) ≡ 0`. -/
theorem gk_fsans_zero : fsans (0 : LinfStar) = id := by
  have h0 : (0 : LinfStar) ∈ LinfStarBall := by simp [LinfStarBall]
  have hid : mobiusExt 1 0 0 1 = id := by
    funext p
    induction p using OnePoint.rec with
    | infty => exact mobiusExt_infty_of_eq rfl
    | coe z =>
      rw [mobiusExt_coe (by simp)]
      simp [mobiusFn]
  obtain ⟨M, hM, W, hW, -⟩ := (wB_spec h0).1
  have hWeq : normalizedSolution (extB (0 : LinfStar)) = W :=
    QCV.qcv_ns_eq (norm_nonneg _) (by simp) (extB_isBeltramiCoeff 0) hW
  have hW0 : normalizedSolution (extB (0 : LinfStar)) = id := by
    have h := QCV.qcv_W_zero (0 : LinfStar)
    simpa only [zero_smul] using h
  rw [hW0] at hWeq
  subst hWeq
  have hnorm : IsNormalizedB 0 id := by
    refine ⟨id, ⟨1, 0, 0, 1, by norm_num, hid.symm⟩, _root_.id, hW, fun z => rfl, rfl, _root_.id,
      fun z _ => rfl, rfl, deriv_id _, ?_⟩
    rw [grp_wAS_zero]
    exact Function.leftInverse_invFun Function.injective_id extInf
  have hwB : wB 0 = id := (wB_unique hnorm).symm
  rw [S2C.s2c_fsans_eq h0]
  funext z
  show finPart (wB 0 z) = z
  rw [hwB]
  rfl

theorem gk_K1_origin :
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (0 : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  rw [gk_fsans_zero]
  simp [AppB.kerK1_id]

/-- `K₄(𝗀_μ)` is Hilbert–Schmidt on `𝔻* × 𝔻*` as soon as `K₁(𝖿^{μ⁻¹})` is on `𝔻 × 𝔻` (inversion and reflection,
as in `s2c_kerK1_refl`). -/
theorem gk_K4_of_K1 {μ : LinfStar} (hμ : μ ∈ LinfStarBall)
    (h : (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (beltramiInv μ)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞) :
    (∫⁻ q in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 (gsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  obtain ⟨φ, b, hφd, hφi, hφ0, -, hb, hbg, hg⟩ :=
    g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  rw [s2c_kerK4_lintegral hφd hφi hφ0 hb hg]
  set F := fsans (beltramiInv μ) with hFdef
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hF : ∀ y ∈ unitDisc, y ≠ 0 → F y = conj (φ (conj y)) :=
    fun y hy hy0 => s2c_f_eq_conj hμ hφi hφ0 hb hbg hg hy hy0
  have hder : ∀ y ∈ unitDisc, y ≠ 0 → deriv F y = conj (deriv φ (conj y)) := by
    intro y hy hy0
    have hev : F =ᶠ[𝓝 y] fun x => conj (φ (conj x)) := by
      filter_upwards [hopen.mem_nhds ⟨hy, hy0⟩] with x hx
      exact hF x hx.1 hx.2
    rw [hev.deriv_eq]
    exact congrFun (deriv_conj_conj (f := φ)) y
  have hcD : ∀ y : ℂ, y ∈ unitDisc ↔ conj y ∈ unitDisc := by
    intro y
    simp [unitDisc]
  -- the conjugation of both variables preserves the measure and `𝔻 × 𝔻`
  set T : ℂ × ℂ → ℂ × ℂ := fun q => (conj q.1, conj q.2) with hT
  have hTmp : MeasurePreserving T (volume : Measure (ℂ × ℂ)) volume := by
    have h1 := Complex.conjLIE.measurePreserving
    have h2 := h1.prod h1
    exact h2
  have hTemb : MeasurableEmbedding T :=
    (Complex.conjLIE.toHomeomorph.prodCongr Complex.conjLIE.toHomeomorph).measurableEmbedding
  have hpre : T ⁻¹' (unitDisc ×ˢ unitDisc) = unitDisc ×ˢ unitDisc := by
    ext q
    simp only [hT, mem_preimage, mem_prod]
    rw [← hcD, ← hcD]
  have hchg := hTmp.setLIntegral_comp_preimage_emb hTemb
    (fun q : ℂ × ℂ => (‖kerK1 F q.1 q.2‖₊ : ℝ≥0∞) ^ 2) (unitDisc ×ˢ unitDisc)
  rw [hpre] at hchg
  -- `|K₁(φ)| = |K₁(𝖿^{μ⁻¹})| ∘ T` off a null set
  have hnull : ∀ᵐ q ∂(volume.restrict (unitDisc ×ˢ unitDisc)), q.1 ≠ 0 ∧ q.2 ≠ 0 := by
    have h1 : (volume : Measure (ℂ × ℂ)) {q | q.1 = 0} = 0 := by
      have : {q : ℂ × ℂ | q.1 = 0} = ({0} : Set ℂ) ×ˢ univ := by
        ext q
        simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have h2 : (volume : Measure (ℂ × ℂ)) {q | q.2 = 0} = 0 := by
      have : {q : ℂ × ℂ | q.2 = 0} = univ ×ˢ ({0} : Set ℂ) := by
        ext q
        simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have h1' := ae_restrict_of_ae (s := unitDisc ×ˢ unitDisc) (measure_eq_zero_iff_ae_notMem.1 h1)
    have h2' := ae_restrict_of_ae (s := unitDisc ×ˢ unitDisc) (measure_eq_zero_iff_ae_notMem.1 h2)
    filter_upwards [h1', h2'] with q hq1 hq2
    exact ⟨hq1, hq2⟩
  have heq : (fun q : ℂ × ℂ => (‖kerK1 φ q.1 q.2‖₊ : ℝ≥0∞) ^ 2) =ᵐ[volume.restrict (unitDisc ×ˢ unitDisc)]
      fun q => (‖kerK1 F (T q).1 (T q).2‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [gk_offdiag_ae, hnull] with q hq hq0
    obtain ⟨hz, hu, hzu⟩ := hq
    have hcz : conj q.1 ∈ unitDisc := (hcD _).1 hz
    have hcu : conj q.2 ∈ unitDisc := (hcD _).1 hu
    have hcz0 : conj q.1 ≠ 0 := by simpa using hq0.1
    have hcu0 : conj q.2 ≠ 0 := by simpa using hq0.2
    have hczu : conj q.1 ≠ conj q.2 := fun e => hzu ((starRingEnd ℂ).injective e)
    have hk := s2c_kerK1_conj hczu (hF _ hcz hcz0) (hF _ hcu hcu0) (hder _ hcz hcz0) (hder _ hcu hcu0)
    simp only [Complex.conj_conj] at hk
    show _ = (‖kerK1 F (conj q.1) (conj q.2)‖₊ : ℝ≥0∞) ^ 2
    rw [hk, RCLike.nnnorm_conj]
  rw [lintegral_congr_ae heq]
  exact lt_of_eq_of_lt hchg h

theorem gk_K1_transport {κ κ' : LinfStarBall} (h : Phi κ = Phi κ')
    (hK : (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞) :
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ' : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  have hs : MeasurableSet (unitDisc ×ˢ unitDisc) := measurableSet_ball.prod measurableSet_ball
  have he : (fun q : ℂ × ℂ => (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[volume.restrict (unitDisc ×ˢ unitDisc)]
      fun q => (‖kerK1 (fsans (κ' : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
    refine (ae_restrict_iff' hs).2 (Eventually.of_forall fun q hq => ?_)
    dsimp only
    rw [gk_fsans_congr h hq.1 hq.2]
  rw [← lintegral_congr_ae he]
  exact hK

/-! ### Theorem 2.6 -/

/-- `K₁(𝖿^κ)` is Hilbert–Schmidt for every representative `κ` of a class of `T₀(1)` (chart-step induction). -/
theorem gk_K1_T01 : ∀ q ∈ T01, ∀ κ : LinfStarBall, Phi κ = q →
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  refine gk_T01_induction (P := fun q => ∀ κ : LinfStarBall, Phi κ = q →
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans (κ : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞) ?_ ?_
  · intro κ hκ
    exact gk_K1_transport hκ.symm gk_K1_origin
  · intro κ ν hP hν κ' hκ'
    have h1 := gk_step hν (hP κ rfl)
    exact gk_K1_transport (κ := ⟨beltramiMul (ν : LinfStar) (κ : LinfStar), bg_mul_mem_ball κ.2 ν.2⟩)
      hκ'.symm h1

/-- **Theorem 2.6** (TT:4048). For the pair `(𝖿^μ, 𝗀_μ)` of `[μ] ∈ T₀(1)`, `𝖪₁` and `𝖪₄` are of trace class:
`∬∬ |K₁|² < ∞` and `∬∬ |K₄|² < ∞`. -/
theorem gk_thm_2_6 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ∧
      (∫⁻ q in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 (gsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ := by
  have hpΦ : Phi (Quotient.out p) = p := Quotient.out_eq p
  have hK : (∫⁻ q in unitDisc ×ˢ unitDisc,
      (‖kerK1 (fsans ((Quotient.out p : LinfStarBall) : LinfStar)) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ :=
    gk_K1_T01 p hp _ hpΦ
  have hinv : invT p ∈ T01 := TakhtajanTeo.lemma_3_4.2.2 p hp
  have hΦ := gtp_invT_phi (Quotient.out p)
  rw [hpΦ] at hΦ
  have hK1' := gk_K1_T01 (invT p) hinv
    ⟨beltramiInv ((Quotient.out p : LinfStarBall) : LinfStar), grp_inv_mem (Quotient.out p : LinfStarBall).2⟩ hΦ.symm
  have hK' := gk_K4_of_K1 (Quotient.out p : LinfStarBall).2 hK1'
  exact ⟨hK, hK'⟩

/-- **Theorem 2.6** (TT:4048). For the pair `(𝖿^μ, 𝗀_μ)` of `[μ] ∈ T₀(1)`, `𝖪₁` and `𝖪₄` are of trace class:
`∬∬ |K₁|² < ∞` and `∬∬ |K₄|² < ∞`. -/
theorem thm_2_6 {p : T1} (hp : p ∈ T01) :
    let μ : LinfStar := (Quotient.out p : LinfStarBall)
    (∫⁻ q in unitDisc ×ˢ unitDisc, (‖kerK1 (fsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ ∧
      (∫⁻ q in unitDiscExterior ×ˢ unitDiscExterior, (‖kerK4 (gsans μ) q.1 q.2‖₊ : ℝ≥0∞) ^ 2) < ∞ :=
  gk_thm_2_6 hp

end Ch2
end TakhtajanTeo
