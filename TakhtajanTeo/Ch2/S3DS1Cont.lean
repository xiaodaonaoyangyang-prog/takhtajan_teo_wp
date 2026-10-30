import TakhtajanTeo.Appendix.AppACor4Final
import TakhtajanTeo.Ch1.TCurveWeldingContinuity
import TakhtajanTeo.Ch1.GroupTopGroup
import TakhtajanTeo.Ch1.S5ExteriorChartRegularity
import TakhtajanTeo.Ch1.S5Thm53Curve
import TakhtajanTeo.Ch1.S5WeldingRegularity
import TakhtajanTeo.Ch2.S1_LiouvilleWellDefined

/-!
# S1Continuity: continuity of the universal Liouville action on `T₀(1)` (Program G, 下属3)

Statement file. `S₁ = ∬_𝔻 |𝒜(𝖿)|² + ∬_{𝔻*} |𝒜(𝗀)|² - 4π log |𝗀'(∞)|` is continuous on `T₀(1)` in the Hilbert manifold
topology. Pieces:

* (S) first countability of `hilbertTopology` at points of `T₀(1)` (chart balls at the origin, `gtp_nhds_origin`,
  transported by the continuous group operations, `GroupTopGroup.thm_3_8`), so continuity is sequential;
* (B) `log |𝗀'(∞)|` is continuous on all of `T(1)`: class-invariant and real-analytic in the coefficient
  (`𝗀'(∞) = 1/∂_u E((μ, μ̄), 0)`, W-NORM), then `tcg_class_family_continuous`;
* (I) the two `L²` integrands are square integrable on `T₀(1)`;
* (F)/(G) `L²` convergence of `𝒜(𝖿_n)` on `𝔻` and of `𝒜(𝗀_n)` on `𝔻*` along Hilbert-convergent sequences: `cor_A_4`
  (ii)/(iii) at a fixed fibre point `v` (with `w_n = v`; the fibre points converge by (B)-type continuity of
  `𝗀_μ(v)`), plus the explicit Möbius bridge from the fibre normalization (`weldF`, `weldG`: `λ_c`, `σ_v`) to the
  standard one (`fsans`, `gsans`);
* (L) `L²` convergence gives convergence of the squared norms.

Prefix `s1c_`. No new definitions.
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo.Ch2

open LiZhongQC

/-! ### Helpers (copies of the W-NORM helpers, 下属3) -/

/-- `𝗀 = g_μ` (welding normalization `c = 0`, `α_μ = id`). -/
theorem s1c_gsans_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) (ζ : ℂ) : gsans μ ζ = gMu μ ζ := by
  have hid : Function.invFun (id : ExtPlane → ExtPlane) = id :=
    funext fun z => Function.leftInverse_invFun Function.injective_id z
  show lambdaW (weldConst μ) (gMu μ (finPart (Function.invFun (alphaMu μ) (ζ : ExtPlane)))) = gMu μ ζ
  rw [AppB.b8_weldConst_zero hμ, alphaMu_eq_id, hid]
  simp only [lambdaW, zero_mul, zero_add, div_one]
  rfl

/-- `𝗀_μ'(∞) = 1/(g^♯_μ)'(0)` with `g^♯_μ(u) = 1/g_μ(1/u)` written through the exterior reciprocal chart
(`s5cf_gchart_eq`). -/
theorem s1c_derivAtInfty {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    derivAtInfty (gsans μ) = (deriv (fun w => s5cf_exterior_reciprocal (μ, star μ) w) 0)⁻¹ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hev : s5cf_gchart μ =ᶠ[𝓝 0] fun w => s5cf_exterior_reciprocal (μ, star μ) w := by
    filter_upwards [isOpen_ball.mem_nhds h0] with s hs
    exact s5cf_gchart_eq hμ hs
  rw [← hev.deriv_eq]
  have hHa : HasDerivAt (s5cf_gchart μ) (deriv (s5cf_gchart μ) 0) 0 :=
    (s5cf_gchart_analytic hμ h0).differentiableAt.hasDerivAt
  have hH0 : s5cf_gchart μ 0 = 0 := by
    show (if (0 : ℂ) = 0 then 0 else (gMu μ (0 : ℂ)⁻¹)⁻¹) = 0
    simp
  refine s5wr_derivAtInfty_of_reciprocal hHa hH0 (s5cf_gchart_deriv_ne_zero hμ h0) ?_
  filter_upwards [s5t53_ev_exterior] with z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num [unitDiscExterior] at hz
  show (if z⁻¹ = 0 then 0 else (gMu μ z⁻¹⁻¹)⁻¹) = (gsans μ z)⁻¹
  rw [ite_eq_right_of_eq_false _ _ (eq_false (inv_ne_zero hz0)), inv_inv, s1c_gsans_eq hμ z]

/-- `ν ↦ (g^♯_ν)'(0)` is real-analytic on the ball (the exterior reciprocal chart is jointly holomorphic in
`(ν, ν̄, u)`, `s5cf_exterior_reciprocal_analytic`). -/
theorem s1c_gchart_deriv_analytic {μ : LinfStar} (hμ : μ ∈ LinfStarBall) :
    AnalyticAt ℝ (fun ν : LinfStar => deriv (fun w => s5cf_exterior_reciprocal (ν, star ν) w) 0) μ := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hc : AnalyticAt ℂ (fun p : LinfStar × LinfStar => deriv (s5cf_exterior_reciprocal p) 0) (μ, star μ) :=
    s5cf_partial_deriv_analytic (F := s5cf_exterior_reciprocal) (s5cf_exterior_reciprocal_analytic hμ h0)
  have hm : AnalyticAt ℝ (fun ν : LinfStar => (ν, star ν)) μ := analyticAt_id.prod (s5cf_star_analytic μ)
  exact hc.restrictScalars.comp_of_eq hm rfl

/-- `𝒮(𝗀_{μ⁻¹})(z) = z⁻⁴ · conj 𝒮(𝖿^μ)(1/z̄)` on `𝔻*` (the complex form of `ab112_S_G`, same proof). -/
theorem s1c_S_G_eq {μ : LinfStar} (hμ : μ ∈ LinfStarBall) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    schwarzianHol (gsans (beltramiInv μ)) z = (z ^ 4)⁻¹ * conj (schwarzianHol (fsans μ) (refl z)) := by
  obtain ⟨hfd, hfi, hf0, -, -, -, -, -, hf0', hf1'⟩ := s2c_facts hμ
  obtain ⟨φ, b, -, -, -, -, hb, hbg, -⟩ := g1_inverted_exterior (AppB.b8_welding_normalized_pair hμ)
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hE : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hbc : conj b ≠ 0 := by simpa using hb
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hconjE : ∀ y ∈ unitDisc \ {0}, conj y ∈ unitDisc \ {0} := fun y hy =>
    ⟨by simpa [unitDisc] using hy.1, by simpa using hy.2⟩
  set fs : ℂ → ℂ := fun y => conj (fsans μ (conj y)) with hfs
  have hfsd : DifferentiableOn ℂ fs (unitDisc \ {0}) := by
    intro y hy
    have h := (hfd.differentiableAt (isOpen_ball.mem_nhds (hconjE y hy).1)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have hfs0 : ∀ y ∈ unitDisc \ {0}, fs y ≠ 0 := fun y hy h =>
    hf0' (conj y) (hconjE y hy).1 (hconjE y hy).2 (by simpa [hfs] using h)
  have hfs1 : ∀ y ∈ unitDisc \ {0}, deriv fs y ≠ 0 := by
    intro y hy h
    have h' : deriv fs y = conj (deriv (fsans μ) (conj y)) := s2c_conj_deriv _ _
    rw [h'] at h
    exact hf1' (conj y) (hconjE y hy).1 (by simpa using h)
  set Gm : ℂ → ℂ := fun x => conj b * (fs x⁻¹)⁻¹ with hGm
  have hev : gsans (beltramiInv μ) =ᶠ[𝓝 z] Gm := by
    filter_upwards [hopenE.mem_nhds hz] with x hx
    rw [(w3_eq_1_3 hμ).2 x hx, hbg]
    simp [hGm, hfs, refl, map_inv₀]
  have hsE : z⁻¹ ∈ unitDisc \ {0} :=
    ⟨mem_ball_zero_iff.2 (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz1), inv_ne_zero hz0⟩
  rw [ab112_S_congr hev, hGm, ab112_S_const_mul hbc,
    ab112_S_inv_inv hE hfsd hfs0 hfs1 hz0 hsE]
  have e1 : schwarzianHol fs z⁻¹ = conj (schwarzianHol (fsans μ) (conj z⁻¹)) := ab112_S_conj _ _
  have hrefl : conj z⁻¹ = refl z := by simp [refl]
  rw [e1, hrefl]

/-- `normA2` transfer under `z ↦ 1/z̄` for a pointwise `|z|⁻⁴` relation (the computation of `ab112_normA2_G`). -/
theorem s1c_normA2_refl {F H : ℂ → ℂ}
    (h : ∀ z ∈ unitDiscExterior, ‖F z‖ = (‖z‖ ^ 4)⁻¹ * ‖H (refl z)‖) :
    normA2 unitDiscExterior F = normA2 unitDisc H := by
  unfold normA2
  congr 1
  rw [ab112_refl_lintegral]
  refine lintegral_congr_ae ?_
  refine (ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)).2 ?_
  filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with u hu0 hu
  have hu0' : u ≠ 0 := hu0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0'
  have hz : refl u ∈ unitDiscExterior := (refl_mem_exterior_iff hu0').2 hu
  have h1 := h _ hz
  rw [refl_involutive u, norm_refl] at h1
  have hrho : (rho (refl u))⁻¹ = (rho u)⁻¹ * (‖u‖ ^ 4)⁻¹ := by
    simp only [rho, norm_refl, inv_div]
    field_simp
    ring
  have hr0 : 0 ≤ (rho u)⁻¹ := by unfold rho; positivity
  rw [ab112_enorm_sq, ab112_enorm_sq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h1, hrho]
  congr 1
  field_simp

/-- `𝒮(𝗀_p)(z) = z⁻⁴ · conj 𝒮(𝖿^{p⁻¹})(1/z̄)` on `𝔻*`. -/
theorem s1c_S_rep (p : T1) {z : ℂ} (hz : z ∈ unitDiscExterior) :
    schwarzianHol (gsans (Quotient.out p : LinfStarBall)) z =
      (z ^ 4)⁻¹ * conj (schwarzianHol (fsans (Quotient.out (invT p) : LinfStarBall)) (refl z)) := by
  set r := invT p with hr
  have hμ := (Quotient.out r : LinfStarBall).2
  have hcl : Phi ⟨beltramiInv ((Quotient.out r : LinfStarBall) : LinfStar), grp_inv_mem hμ⟩ = p := by
    have h1 : Phi (Quotient.out r) = r := Quotient.out_eq r
    have h2 := gtp_invT_phi (Quotient.out r : LinfStarBall)
    rw [h1] at h2
    rw [← h2, hr, grp_invT_invT]
  have hrel : teichSetoid (⟨beltramiInv ((Quotient.out r : LinfStarBall) : LinfStar), grp_inv_mem hμ⟩ : LinfStarBall)
      (Quotient.out p : LinfStarBall) :=
    Quotient.exact (hcl.trans (Quotient.out_eq p).symm)
  have hG := (s2c_class_pair hrel).2
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  rw [← ab112_S_eqOn hopenE hG hz]
  exact s1c_S_G_eq hμ hz

/-- **(S)** The Hilbert manifold topology is first countable at points of `T₀(1)`. -/
theorem s1c_nhds_countable {q : T1} (hq : q ∈ T01) : (@nhds T1 hilbertTopology q).IsCountablyGenerated := by
  -- holds at every point of `T(1)` (every class has a representative in `𝒪(𝔻*)₁`); `hq` is not needed
  have _h := hq
  obtain ⟨κ, hκ, rfl⟩ := ctb_exists_groupO_rep q
  have hr0 : 0 < Real.sqrt (π / 3) := by positivity
  have hδ0 : ∀ n : ℕ, 0 < min (1 / ((n : ℝ) + 1)) (Real.sqrt (π / 3)) := fun n => lt_min (by positivity) hr0
  have hB : (@nhds T1 hilbertTopology (Phi κ)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun φ : A2 unitDisc => bersChartInv κ (A2toAInf φ)) ''
        ball 0 (min (1 / ((n : ℝ) + 1)) (Real.sqrt (π / 3)))) := by
    refine ⟨fun W => ⟨fun hW => ?_, ?_⟩⟩
    · obtain ⟨ε, hε, -, hW'⟩ := gtr_c_nhds hκ hW
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine ⟨n, trivial, ?_⟩
      rintro _ ⟨φ, hφ, rfl⟩
      exact hW' φ (((mem_ball_zero_iff.1 hφ).trans_le (min_le_left _ _)).trans hn)
    · rintro ⟨n, -, hn⟩
      exact Filter.mem_of_superset (gtr_c_image_mem hκ (hδ0 n) (min_le_right _ _)) hn
  exact hB.isCountablyGenerated

/-- **(B)** `p ↦ log |𝗀_p'(∞)|` is continuous on `T(1)` in the Hilbert manifold topology. -/
theorem s1c_beta_continuous :
    @Continuous T1 ℝ hilbertTopology _
      (fun p : T1 => Real.log ‖derivAtInfty (gsans (Quotient.out p : LinfStarBall))‖) := by
  letI : TopologicalSpace T1 := hilbertTopology
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  -- continuous in the coefficient: `𝗀'(∞) = 1/∂_u E((μ, μ̄), 0)`, real-analytic and nonzero
  have hg : ContinuousOn (fun μ : LinfStar => Real.log ‖derivAtInfty (gsans μ)‖) LinfStarBall := by
    intro μ hμ
    have hne := s5cf_exterior_reciprocal_deriv_ne_zero hμ h0
    have hc : ContinuousAt (fun ν : LinfStar => (deriv (fun w => s5cf_exterior_reciprocal (ν, star ν) w) 0)⁻¹) μ :=
      (s1c_gchart_deriv_analytic hμ).continuousAt.inv₀ hne
    have hc' : ContinuousAt (fun ν : LinfStar => derivAtInfty (gsans ν)) μ := by
      refine hc.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hμ] with ν hν
      exact (s1c_derivAtInfty hν).symm
    have hn : ‖derivAtInfty (gsans μ)‖ ≠ 0 := by
      rw [s1c_derivAtInfty hμ, norm_ne_zero_iff]
      exact inv_ne_zero hne
    exact (hc'.norm.log hn).continuousWithinAt
  have hF : ContinuousOn (fun x : LinfStar × Unit => Real.log ‖derivAtInfty (gsans x.1)‖)
      (LinfStarBall ×ˢ (univ : Set Unit)) :=
    hg.comp continuousOn_fst fun x hx => hx.1
  -- class invariance (`s5cf_gMu_congr`)
  have hcls : ∀ μ ν : LinfStarBall, teichSetoid μ ν →
      Real.log ‖derivAtInfty (gsans (μ : LinfStar))‖ = Real.log ‖derivAtInfty (gsans (ν : LinfStar))‖ := by
    intro μ ν h
    have hgc := s5cf_gMu_congr h
    have he : derivAtInfty (gsans (μ : LinfStar)) = derivAtInfty (gsans (ν : LinfStar)) := by
      apply s5t53_derivAtInfty_congr
      filter_upwards [s5t53_ev_exterior] with z hz
      rw [s1c_gsans_eq μ.2, s1c_gsans_eq ν.2]
      exact hgc hz
    rw [he]
  exact tcg_class_family_continuous (fun x : LinfStar × Unit => Real.log ‖derivAtInfty (gsans x.1)‖) isOpen_univ hF
    (fun μ ν h _ _ => hcls μ ν h) (fun r : T1 => r) (fun _ => ()) continuous_id continuous_const
    (fun _ => mem_univ _)

/-- **(I)** On `T₀(1)`, `𝒜(𝖿) ∈ L²(𝔻)` and `𝒜(𝗀) ∈ L²(𝔻*)`. -/
theorem s1c_memLp {p : T1} (hp : p ∈ T01) :
    MemLp (preSchwarzian (fsans (Quotient.out p : LinfStarBall))) 2 (volume.restrict unitDisc) ∧
      MemLp (preSchwarzian (gsans (Quotient.out p : LinfStarBall))) 2 (volume.restrict unitDiscExterior) := by
  have hE : MeasurableSet unitDiscExterior := (isOpen_lt continuous_const continuous_norm).measurableSet
  exact ⟨((mem_A21fun_iff_memLp measurableSet_ball).1 (ls1wd_preSchwarzian_disc hp)).2,
    ((mem_A21fun_iff_memLp hE).1 (ls1wd_preSchwarzian_exterior hp)).2⟩

/-- **(F)** Along a Hilbert-convergent sequence in `T₀(1)`, `𝒜(𝖿_n) → 𝒜(𝖿)` in `L²(𝔻)`. -/
theorem s1c_f_tendsto {p : ℕ → T1} {q : T1} (hp : ∀ n, p n ∈ T01) (hq : q ∈ T01)
    (hlim : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q)) :
    Tendsto (fun n => ∫⁻ z in unitDisc, ‖preSchwarzian (fsans (Quotient.out (p n) : LinfStarBall)) z -
      preSchwarzian (fsans (Quotient.out q : LinfStarBall)) z‖ₑ ^ 2) atTop (𝓝 0) := by
  have hμ := (Quotient.out q : LinfStarBall).2
  obtain ⟨hd, hi, -, -⟩ := ab112_fsans_facts hμ
  have hne : ∀ z ∈ unitDisc, deriv (fsans (Quotient.out q : LinfStarBall)) z ≠ 0 :=
    fun z hz => deriv_ne_zero_of_injOn isOpen_ball hd hi hz
  have h1 : deriv (fsans (Quotient.out q : LinfStarBall)) 0 = 1 := by
    rw [S2C.s2c_fsans_eq hμ]
    exact (fB_normalization _).2.1
  have hS := (AppA.a4_T01_tendsto_iff hp hq).1 hlim
  have hinv := AppA.a4_inverse hd hne h1 (ls1wd_preSchwarzian_disc hq)
    (fun n => ls1wd_preSchwarzian_disc (hp n)) hS (AppA.a4_preSchwarzian_zero_tendsto hlim)
  have hsq : ∀ φ : ℂ → ℂ, (∫⁻ z in unitDisc, ‖φ z‖ₑ ^ 2) = normA21 unitDisc φ ^ (2 : ℝ) := by
    intro φ
    unfold normA21
    rw [← ENNReal.rpow_mul]
    norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rfl
  have hc : Tendsto (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  have hfin := hc.comp hinv
  refine hfin.congr fun n => ?_
  exact (hsq _).symm

/-- **(G)** Along a Hilbert-convergent sequence in `T₀(1)`, `𝒜(𝗀_n) → 𝒜(𝗀)` in `L²(𝔻*)`. -/
theorem s1c_g_tendsto {p : ℕ → T1} {q : T1} (hp : ∀ n, p n ∈ T01) (hq : q ∈ T01)
    (hlim : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q)) :
    Tendsto (fun n => ∫⁻ z in unitDiscExterior, ‖preSchwarzian (gsans (Quotient.out (p n) : LinfStarBall)) z -
      preSchwarzian (gsans (Quotient.out q : LinfStarBall)) z‖ₑ ^ 2) atTop (𝓝 0) := by
  letI : TopologicalSpace T1 := hilbertTopology
  have hopenE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hinv : Tendsto (fun n => invT (p n)) atTop (𝓝 (invT q)) := by
    have hc := (_root_.TakhtajanTeo.thm_3_8 (originT, q) ⟨grp_lemma_3_4.1, hq⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hlim,
        Eventually.of_forall fun n => ⟨grp_lemma_3_4.1, hp n⟩⟩)
    simpa only [Function.comp_def, AppA.a6_origin_mul] using hc
  have hp' : ∀ n, invT (p n) ∈ T01 := fun n => grp_lemma_3_4.2.2 _ (hp n)
  have hq' := grp_lemma_3_4.2.2 _ hq
  have hSf := (AppA.a4_T01_tendsto_iff hp' hq').1 hinv
  have hS : Tendsto (fun n => normA2 unitDiscExterior (fun z =>
      PsiOp (preSchwarzian (gsans (Quotient.out (p n) : LinfStarBall))) z -
        PsiOp (preSchwarzian (gsans (Quotient.out q : LinfStarBall))) z)) atTop (𝓝 0) := by
    refine hSf.congr fun n => ?_
    symm
    apply s1c_normA2_refl
    intro z hz
    show ‖schwarzianHol (gsans (Quotient.out (p n) : LinfStarBall)) z -
        schwarzianHol (gsans (Quotient.out q : LinfStarBall)) z‖ = _
    rw [s1c_S_rep (p n) hz, s1c_S_rep q hz, ← mul_sub, ← map_sub, norm_mul, norm_inv, norm_pow,
      RCLike.norm_conj]
  have hmem : ∀ r ∈ T01, preSchwarzian (gsans (Quotient.out r : LinfStarBall)) ∈ AppA.A21tildeExt := by
    intro r hr
    exact ⟨ls1wd_preSchwarzian_exterior hr, AppA.appa2_preSchwarzian_cubic
      (AppB.b8_welding_normalized_pair (Quotient.out r : LinfStarBall).2).2.2.2.2.1⟩
  have hinvG := AppA.a6_ext_inverse (hmem q hq) (fun n => hmem _ (hp n)) hS
  have hsq : ∀ φ : ℂ → ℂ, (∫⁻ z in unitDiscExterior, ‖φ z‖ₑ ^ 2) =
      normA21 unitDiscExterior φ ^ (2 : ℝ) := by
    intro φ
    unfold normA21
    rw [← ENNReal.rpow_mul]
    norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rfl
  have hc : Tendsto (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  have hfin := hc.comp hinvG
  refine hfin.congr fun n => ?_
  exact (hsq _).symm

/-- **(L)** `L²` convergence implies convergence of `∫ |F_n|²`. -/
theorem s1c_sq_tendsto {D : Set ℂ} {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ n, MemLp (F n) 2 (volume.restrict D)) (hG : MemLp G 2 (volume.restrict D))
    (h : Tendsto (fun n => ∫⁻ z in D, ‖F n z - G z‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in D, ‖F n z‖ ^ 2) atTop (𝓝 (∫ z in D, ‖G z‖ ^ 2)) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  -- `∫ |f|² = ‖f‖₂²` for `f ∈ L²`
  have hsq : ∀ f : ℂ → ℂ, MemLp f 2 (volume.restrict D) →
      ∫ z in D, ‖f z‖ ^ 2 = (eLpNorm f 2 (volume.restrict D)).toReal ^ 2 := by
    intro f hf
    have hnn : 0 ≤ ∫ z in D, ‖f z‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun z => by positivity
    rw [hf.eLpNorm_eq_integral_rpow_norm h2 h2', ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),
      ← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  -- `‖F_n - G‖₂ → 0`
  have hd : Tendsto (fun n => eLpNorm (F n - G) 2 (volume.restrict D)) atTop (𝓝 0) := by
    have he : ∀ n, eLpNorm (F n - G) 2 (volume.restrict D) =
        (∫⁻ z in D, ‖F n z - G z‖ₑ ^ 2) ^ (1 / (2 : ℝ)) := by
      intro n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2' ((hF n).aestronglyMeasurable.sub hG.aestronglyMeasurable)]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, Pi.sub_apply]
    simp_rw [he]
    have hc : Tendsto (fun x : ℝ≥0∞ => x ^ (1 / (2 : ℝ))) (𝓝 0) (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    exact hc.comp h
  have hdr : Tendsto (fun n => (eLpNorm (F n - G) 2 (volume.restrict D)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hd
    exact this
  -- the reverse triangle inequality
  have hab : ∀ n, |(eLpNorm (F n) 2 (volume.restrict D)).toReal - (eLpNorm G 2 (volume.restrict D)).toReal| ≤
      (eLpNorm (F n - G) 2 (volume.restrict D)).toReal := by
    intro n
    have hFn := (hF n).eLpNorm_lt_top.ne
    have hGn := hG.eLpNorm_lt_top.ne
    have hdn := ((hF n).sub hG).eLpNorm_lt_top.ne
    have e1 : eLpNorm (F n) 2 (volume.restrict D) ≤
        eLpNorm (F n - G) 2 (volume.restrict D) + eLpNorm G 2 (volume.restrict D) := by
      calc eLpNorm (F n) 2 (volume.restrict D) = eLpNorm ((F n - G) + G) 2 (volume.restrict D) := by
            rw [sub_add_cancel]
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    have e2 : eLpNorm G 2 (volume.restrict D) ≤
        eLpNorm (F n - G) 2 (volume.restrict D) + eLpNorm (F n) 2 (volume.restrict D) := by
      calc eLpNorm G 2 (volume.restrict D) = eLpNorm ((G - F n) + F n) 2 (volume.restrict D) := by
            rw [sub_add_cancel]
        _ ≤ eLpNorm (G - F n) 2 (volume.restrict D) + eLpNorm (F n) 2 (volume.restrict D) :=
            eLpNorm_add_le (by norm_num)
        _ = _ := by rw [eLpNorm_sub_comm]
    have e1' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdn, hGn⟩) e1
    have e2' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hdn, hFn⟩) e2
    rw [ENNReal.toReal_add hdn hGn] at e1'
    rw [ENNReal.toReal_add hdn hFn] at e2'
    rw [abs_le]
    constructor <;> linarith
  have ha : Tendsto (fun n => (eLpNorm (F n) 2 (volume.restrict D)).toReal) atTop
      (𝓝 (eLpNorm G 2 (volume.restrict D)).toReal) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hab n) hdr
  have hfun : (fun n => ∫ z in D, ‖F n z‖ ^ 2) = fun n => (eLpNorm (F n) 2 (volume.restrict D)).toReal ^ 2 :=
    funext fun n => hsq _ (hF n)
  rw [hfun, hsq G hG]
  exact ha.pow 2

/-- **Continuity of `S₁`** on `T₀(1)` in the Hilbert manifold topology. -/
theorem s1c_continuousOn : @ContinuousOn T1 ℝ hilbertTopology _ liouvilleS1 T01 := by
  letI : TopologicalSpace T1 := hilbertTopology
  intro q hq
  haveI := s1c_nhds_countable hq
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro x hx
  have hx0 : Tendsto x atTop (𝓝 q) := hx.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eventually self_mem_nhdsWithin)
  set p : ℕ → T1 := fun n => x (n + N) with hpdef
  have hp : ∀ n, p n ∈ T01 := fun n => hN _ (Nat.le_add_left N n)
  have hpl : Tendsto p atTop (𝓝 q) := hx0.comp (tendsto_add_atTop_nat N)
  have hf := s1c_sq_tendsto (fun n => (s1c_memLp (hp n)).1) (s1c_memLp hq).1 (s1c_f_tendsto hp hq hpl)
  have hg := s1c_sq_tendsto (fun n => (s1c_memLp (hp n)).2) (s1c_memLp hq).2 (s1c_g_tendsto hp hq hpl)
  have hb := (s1c_beta_continuous.tendsto q).comp hpl
  have hS : Tendsto (fun n => liouvilleS1 (p n)) atTop (𝓝 (liouvilleS1 q)) :=
    (hf.add hg).sub (hb.const_mul (4 * π))
  exact (tendsto_add_atTop_iff_nat N).1 hS

end TakhtajanTeo.Ch2
