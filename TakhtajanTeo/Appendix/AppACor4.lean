import TakhtajanTeo.Appendix.AppACor2
import TakhtajanTeo.Appendix.AppACompleted2
import TakhtajanTeo.Ch1.TCurveTopGroupCompleted
import TakhtajanTeo.Ch1.TCurveLocalRepresentatives
import TakhtajanTeo.Ch1.TCurveBaseContinuity
import TakhtajanTeo.Ch1.GroupTopGroup

/-!
# Appendix A, Corollary A.4 (`a4_`, 下属2, Program G)

Host: new module `Appendix/AppACor4.lean`; the leader relocates `cor_A_4` here (body `a4_cor_A_4 hp hw hq hv`).

Route.
- (i) ⇔ (ii):
  - `β̂ = 𝒜(f)` and `Ψ(β̂) = 𝒮(f) = β` (`ac2_psi_betaHat`).
  - `β̂(0) = 𝒜(𝖿)(0) + 2/𝗀(w)` (`ac2_betaHat_zero`).
  - (ii) ⇒ (i): `Ψ` is continuous `A₂¹ → A₂` (`ac2_psi_cont_disc`), then S1 and S3.
  - (i) ⇒ (ii): S1 and S2/S3 give `Ψ(β̂ₙ) → Ψ(β̂)` in `A₂` and `β̂ₙ(0) → β̂(0)`. Then S4: the inverse function theorem
    for `x ↦ (x' - x²/2, x(0))`, in the coordinates `x ↦ (x', x(0)) ∈ A2 unitDisc × ℂ`, which is complete.
    - The derivative is bijective by `thm_A_3_analytic`; the open mapping theorem gives an equivalence.
    - The local inverse is continuous, and global injectivity (`PsiOp_injective_with_value`) identifies it with `β̂ₙ`.
- (i) ⇔ (iii), S5: the paper's inversion argument.
  - `G = j ∘ g ∘ j` is univalent on `𝔻`, and `𝒜(G) = -(lg g ∘ j)·z⁻²`. The norm is transported by `a55_inv_normA21`.
  - S4 applied at `G` (after scaling `G'(0) = 1`).
  - The exterior Bers map: `𝒮(g)` is the reflection of `β(γ⁻¹)` (`appa2_betaStar_spec`), plus continuity of `invT`
    (`thm_3_8`) and of `σ_w`.
  - S5 is frozen as the exact clause equivalence; its own sub-interface follows after (i) ⇔ (ii).
-/

open Complex Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate Classical Real

noncomputable section

namespace TakhtajanTeo

open LiZhongQC Ch2

namespace AppA

/-- **S1.** In `T₀(1)`, convergence in the Hilbert manifold topology is `A₂(𝔻)` convergence of the Bers images
`𝒮(𝖿^p)` (`bers` is an open embedding, `hbSurj_bers_openEmbedding`, `tcg_A2_bers_continuous`). -/
theorem a4_T01_tendsto_iff {p : ℕ → T1} {q : T1} (hp : ∀ n, p n ∈ T01) (hq : q ∈ T01) :
    @Tendsto _ _ p atTop (@nhds _ hilbertTopology q) ↔
      Tendsto (fun n => normA2 unitDisc (fun z => schwarzianHol (fsans (Quotient.out (p n) : LinfStarBall)) z -
        schwarzianHol (fsans (Quotient.out q : LinfStarBall)) z)) atTop (𝓝 0) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  let _ : TopologicalSpace (AInf unitDisc) := hilbertTopologyA
  -- the Bers function on the disk
  have hspec : ∀ r : T1, EqOn (AInf.toFun (bers r)) (schwarzianHol (fsans (Quotient.out r : LinfStarBall)))
      unitDisc := by
    intro r y hy
    have hμ := (Quotient.out r : LinfStarBall).2
    obtain ⟨hfd, hfi⟩ := fB_holomorphic_injective hμ
    rw [S2C.s2c_fsans_eq hμ]
    exact (schwarzianHol_AInf_spec hfd hfi).1 y hy
  have hA : ∀ r ∈ T01, AInf.toFun (bers r) ∈ A2fun unitDisc := fun r hr => by
    rw [cor_3_2] at hr
    exact hr
  have hedist : ∀ n, edist (toA2 unitDisc (AInf.toFun (bers (p n)))) (toA2 unitDisc (AInf.toFun (bers q))) =
      normA2 unitDisc (fun z => schwarzianHol (fsans (Quotient.out (p n) : LinfStarBall)) z -
        schwarzianHol (fsans (Quotient.out q : LinfStarBall)) z) := fun n => by
    rw [t31_edist_toA2 (hA _ (hp n)) (hA _ hq)]
    apply normA2_congr measurableSet_ball
    intro z hz
    simp only [hspec (p n) hz, hspec q hz]
  have hiff : Tendsto (fun n => toA2 unitDisc (AInf.toFun (bers (p n)))) atTop
      (𝓝 (toA2 unitDisc (AInf.toFun (bers q)))) ↔
      Tendsto (fun n => normA2 unitDisc (fun z => schwarzianHol (fsans (Quotient.out (p n) : LinfStarBall)) z -
        schwarzianHol (fsans (Quotient.out q : LinfStarBall)) z)) atTop (𝓝 0) := by
    rw [tendsto_iff_edist_tendsto_0]
    exact tendsto_congr hedist
  rw [← hiff]
  constructor
  · intro h
    have hc := (tcg_A2_bers_continuous q hq).tendsto
    exact hc.comp (tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall hp⟩)
  · intro h
    have hi : Topology.IsOpenEmbedding A2toAInf := by
      simpa only [zero_add] using hib_affine_openEmbedding (0 : AInf unitDisc)
    have hb : Tendsto (fun n => bers (p n)) atTop (𝓝 (bers q)) := by
      have h2 := (hi.continuous.tendsto _).comp h
      rw [ctb_A2toAInf_toA2 (hA q hq)] at h2
      exact h2.congr fun n => ctb_A2toAInf_toA2 (hA _ (hp n))
    exact hbSurj_bers_openEmbedding.isInducing.tendsto_nhds_iff.mpr hb

/-- **S2.** `𝒜(𝖿^p)(0) = (𝖿^p)''(0)` depends continuously on `p` in the Hilbert topology
(`tcg_fB_class_continuous_family` and Cauchy estimates). -/
theorem a4_preSchwarzian_zero_tendsto {p : ℕ → T1} {q : T1}
    (hlim : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q)) :
    Tendsto (fun n => preSchwarzian (fsans (Quotient.out (p n) : LinfStarBall)) 0) atTop
      (𝓝 (preSchwarzian (fsans (Quotient.out q : LinfStarBall)) 0)) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set F : LinfStar × Unit → ℂ := fun x => deriv (deriv (fB x.1)) 0 with hF
  have hval : ∀ μ : LinfStarBall, preSchwarzian (fsans (μ : LinfStar)) 0 = F ((μ : LinfStar), ()) := by
    intro μ
    rw [S2C.s2c_fsans_eq μ.2]
    show deriv (deriv (fB (μ : LinfStar))) 0 / deriv (fB (μ : LinfStar)) 0 = _
    rw [(fB_normalization _).2.1, div_one]
  have hcls : ∀ μ ν : LinfStarBall, teichSetoid μ ν → ∀ y ∈ (univ : Set Unit),
      F ((μ : LinfStar), y) = F ((ν : LinfStar), y) := by
    intro μ ν h y _
    have he : fB (μ : LinfStar) =ᶠ[𝓝 0] fB (ν : LinfStar) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with z hz
      have hz' := (s2c_class_pair h).1 hz
      rwa [S2C.s2c_fsans_eq μ.2, S2C.s2c_fsans_eq ν.2] at hz'
    exact he.deriv.deriv_eq
  have hFc : ContinuousOn F (LinfStarBall ×ˢ (univ : Set Unit)) := by
    have hg : ContinuousOn (fun μ : LinfStar => deriv (deriv (fB μ)) 0) LinfStarBall := by
      rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
      intro x μ₀ hx
      exact ac2_fpp_seq μ₀.2 (fun n => (x n).2) ((continuous_subtype_val.tendsto _).comp hx)
    exact hg.comp continuousOn_fst fun x hx => hx.1
  have hc := tcg_class_family_continuous F isOpen_univ hFc hcls (fun r : T1 => r) (fun _ => ())
    continuous_id continuous_const (fun _ => mem_univ _)
  have ht := (hc.tendsto q).comp hlim
  have he : ∀ r : T1, preSchwarzian (fsans (Quotient.out r : LinfStarBall)) 0 =
      F (((Quotient.out r : LinfStarBall) : LinfStar), ()) := fun r => hval _
  simp only [he]
  exact ht

/-- **S3.** Given `pₙ → q`, convergence of the fibre points `𝗀_{μₙ}(wₙ) ∈ ℂ̄` is convergence of `β̂(pₙ, wₙ)(0)`
(`ac2_betaHat_zero`, `s2c_gsans_eq`, `ac2_g_ne_zero`; `x ↦ 2/x` is a homeomorphism near the nonzero finite limit). -/
theorem a4_point_tendsto_iff {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ}
    (hw : ∀ n, w n ∈ unitDiscExterior) (hv : v ∈ unitDiscExterior)
    (hlim : @Tendsto _ _ p atTop (@nhds _ hilbertTopology q)) :
    Tendsto (fun n => ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane)) atTop
        (𝓝 ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane)) ↔
      Tendsto (fun n => betaHat (p n) (w n) 0) atTop (𝓝 (betaHat q v 0)) := by
  have hA := a4_preSchwarzian_zero_tendsto hlim
  have hgne : ∀ (r : T1) {u : ℂ}, u ∈ unitDiscExterior → gMu (Quotient.out r : LinfStarBall) u ≠ 0 := by
    intro r u hu
    rw [← S2C.s2c_gsans_eq (Quotient.out r : LinfStarBall).2]
    exact ac2_g_ne_zero (Quotient.out r : LinfStarBall).2 hu
  have hβ : ∀ (r : T1) {u : ℂ}, u ∈ unitDiscExterior → betaHat r u 0 =
      preSchwarzian (fsans (Quotient.out r : LinfStarBall)) 0 + 2 / gMu (Quotient.out r : LinfStarBall) u := by
    intro r u hu
    rw [ac2_betaHat_zero r hu, S2C.s2c_gsans_eq (Quotient.out r : LinfStarBall).2]
  have hcoe := (OnePoint.isOpenEmbedding_coe (X := ℂ)).isInducing.tendsto_nhds_iff
    (f := fun n => gMu (Quotient.out (p n) : LinfStarBall) (w n)) (l := atTop)
    (y := gMu (Quotient.out q : LinfStarBall) v)
  rw [show (fun n => ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane)) =
    (OnePoint.some ∘ fun n => gMu (Quotient.out (p n) : LinfStarBall) (w n)) from rfl, ← hcoe]
  rw [show (fun n => betaHat (p n) (w n) 0) = fun n => preSchwarzian (fsans (Quotient.out (p n) : LinfStarBall)) 0 +
    2 / gMu (Quotient.out (p n) : LinfStarBall) (w n) from funext fun n => hβ (p n) (hw n), hβ q hv]
  have hg := hgne q hv
  constructor
  · intro h
    exact hA.add (tendsto_const_nhds.div h hg)
  · intro h
    have h2 : Tendsto (fun n => 2 / gMu (Quotient.out (p n) : LinfStarBall) (w n)) atTop
        (𝓝 (2 / gMu (Quotient.out q : LinfStarBall) v)) := by
      have := h.sub hA
      simpa only [add_sub_cancel_left] using this
    have h3 : Tendsto (fun n => 2 / (2 / gMu (Quotient.out (p n) : LinfStarBall) (w n))) atTop
        (𝓝 (2 / (2 / gMu (Quotient.out q : LinfStarBall) v))) :=
      (tendsto_const_nhds (x := (2 : ℂ))).div h2 (div_ne_zero two_ne_zero hg)
    have hfun : (fun n => 2 / (2 / gMu (Quotient.out (p n) : LinfStarBall) (w n))) =
        fun n => gMu (Quotient.out (p n) : LinfStarBall) (w n) :=
      funext fun n => by rw [div_div_cancel₀ two_ne_zero]
    rwa [hfun, div_div_cancel₀ two_ne_zero] at h3


/-- **Corollary A.4, (ii) ⇒ (i)** (early delivery for `lemma_3_6`): `A₂¹(𝔻)` convergence of `β̂(pₙ, wₙ)` gives
convergence of `(pₙ, 𝗀_{μₙ}(wₙ))` in `T₀(1) × ℂ̄` (Hilbert topology on the first factor). -/
theorem a4_ii_imp_i {p : ℕ → T1} {w : ℕ → ℂ} {q : T1} {v : ℂ} (hp : ∀ n, p n ∈ T01)
    (hw : ∀ n, w n ∈ unitDiscExterior) (hq : q ∈ T01) (hv : v ∈ unitDiscExterior)
    (h : Tendsto (fun n => normA21 unitDisc (fun z => betaHat (p n) (w n) z - betaHat q v z)) atTop (𝓝 0)) :
    @Tendsto _ _ (fun n => (p n, ((gMu (Quotient.out (p n) : LinfStarBall) (w n) : ℂ) : ExtPlane))) atTop
      (@nhds _ (@instTopologicalSpaceProd _ _ hilbertTopology inferInstance)
        (q, ((gMu (Quotient.out q : LinfStarBall) v : ℂ) : ExtPlane))) := by
  let _ : TopologicalSpace T1 := hilbertTopology
  have hβq : betaHat q v ∈ A21fun unitDisc := (appa_betaHat_spec q hv).1.mpr hq
  have hβp : ∀ n, betaHat (p n) (w n) ∈ A21fun unitDisc := fun n => (appa_betaHat_spec (p n) (hw n)).1.mpr (hp n)
  have hSeq : ∀ n, normA2 unitDisc (fun z => schwarzianHol (fsans (Quotient.out (p n) : LinfStarBall)) z -
      schwarzianHol (fsans (Quotient.out q : LinfStarBall)) z) =
      normA2 unitDisc (fun z => PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z) := fun n => by
    apply normA2_congr measurableSet_ball
    intro z hz
    show _ = PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z
    rw [ac2_psi_betaHat (p n) (hw n) hz, ac2_psi_betaHat q hv hz]
  -- `Ψ` is continuous `A₂¹ → A₂`
  have hS : Tendsto (fun n => normA2 unitDisc (fun z => PsiOp (betaHat (p n) (w n)) z - PsiOp (betaHat q v) z))
      atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => absurd ha not_lt_zero, fun a ha => ?_⟩
    obtain ⟨ε, -, hε0, hεa⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
    have hε : 0 < ε := ENNReal.ofReal_pos.mp hε0
    obtain ⟨δ, hδ, hcont⟩ := ac2_psi_cont_disc hβq ε hε
    filter_upwards [(tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.mpr hδ)] with n hn
    exact (hcont _ (hβp n) hn).trans hεa
  have hpl : Tendsto p atTop (𝓝 q) := (a4_T01_tendsto_iff hp hq).mpr (hS.congr fun n => (hSeq n).symm)
  -- the values at `0` (Lemma 1.3 at `z = 0`)
  have h0 : Tendsto (fun n => betaHat (p n) (w n) 0) atTop (𝓝 (betaHat q v 0)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    obtain ⟨N, hN⟩ := (tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.mpr (mul_pos hε hπ)) |>.exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have hd : (fun z => betaHat (p n) (w n) z - betaHat q v z) ∈ A21fun unitDisc := by
      have h2 := a21_add measurableSet_ball (hβp n) (a21_const_mul measurableSet_ball hβq (-1))
      refine (ab112_A21fun_congr (U := unitDisc) isOpen_ball (fun z _ => ?_)).mp h2
      ring
    have hb := lemma_1_3 (Or.inl rfl) hd 0 (mem_ball_self one_pos)
    have he : ENNReal.ofReal (ε * Real.sqrt π) * ENNReal.ofReal (1 / Real.sqrt π) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hlt : ENNReal.ofReal ‖(1 - ((‖(0 : ℂ)‖ : ℝ) : ℂ) ^ 2) * (betaHat (p n) (w n) 0 - betaHat q v 0)‖ <
        ENNReal.ofReal ε := by
      refine hb.trans_lt ?_
      rw [mul_comm, ← he]
      exact ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < 1 / Real.sqrt π)).ne'
        ENNReal.ofReal_ne_top (hN n hn)
    rw [ENNReal.ofReal_lt_ofReal_iff hε] at hlt
    simpa [dist_eq_norm] using hlt
  exact hpl.prodMk_nhds ((a4_point_tendsto_iff hw hv hpl).mpr h0)


/-! ### S4 support: coordinates `x = (a, c) ∈ A₂(𝔻) × ℂ` for `A₂¹(𝔻)` -/

theorem a4_circle : ∀ z ∈ unitDisc, ‖z‖ ≠ 1 := fun _ hz => ne_of_lt (mem_ball_zero_iff.mp hz)

/-- Holomorphic functions on the disk with equal derivatives and equal values at `0` agree. -/
theorem a4_eqOn_of_deriv {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hg : DifferentiableOn ℂ g unitDisc)
    (hd : EqOn (deriv f) (deriv g) unitDisc) (h0 : f 0 = g 0) : EqOn f g unitDisc := by
  intro z hz
  have hF : ∀ w ∈ unitDisc, HasDerivAt (fun u => f u - g u) 0 w := by
    intro w hw
    have h1 := (hf.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h2 := (hg.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h3 := h1.sub h2
    rwa [hd hw, sub_self] at h3
  have hconst : f z - g z = f 0 - g 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF w hw).deriv) hz (mem_ball_self (by norm_num))
  rw [h0, sub_self, sub_eq_zero] at hconst
  exact hconst

theorem a4_toA2_eqOn {g : ℂ → ℂ} (hg : g ∈ A2fun unitDisc) : EqOn (A2.toFun (toA2 unitDisc g)) g unitDisc :=
  toA2_spec (D := unitDisc) isOpen_ball a4_circle hg

theorem a4_toA2_norm {g : ℂ → ℂ} (hg : g ∈ A2fun unitDisc) :
    (‖toA2 unitDisc g‖₊ : ℝ≥0∞) = normA2 unitDisc g := by
  rw [← A2.norm_toFun]
  exact normA2_congr (D := unitDisc) measurableSet_ball (a4_toA2_eqOn hg)

theorem a4_toA2_ext {g h : ℂ → ℂ} (hg : g ∈ A2fun unitDisc) (hh : h ∈ A2fun unitDisc) :
    toA2 unitDisc g = toA2 unitDisc h ↔ EqOn g h unitDisc := by
  constructor
  · intro e z hz
    rw [← a4_toA2_eqOn hg hz, ← a4_toA2_eqOn hh hz, e]
  · intro e
    apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
    intro z hz
    rw [a4_toA2_eqOn hg hz, a4_toA2_eqOn hh hz, e hz]

theorem a4_toFun_zero : EqOn (A2.toFun (0 : A2 unitDisc)) 0 unitDisc := by
  intro z hz
  have h := A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle (0 : ℂ) (0 : A2 unitDisc) hz
  simpa using h

theorem a4_A2_add {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (hg : g ∈ A2fun unitDisc) :
    (fun z => f z + g z) ∈ A2fun unitDisc :=
  ⟨hf.1.add hg.1, (a55_normA2_add_le (hf.1.continuousOn.aestronglyMeasurable measurableSet_ball)
    (hg.1.continuousOn.aestronglyMeasurable measurableSet_ball)).trans_lt (ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩)⟩

theorem a4_A2_const_mul {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (c : ℂ) :
    (fun z => c * f z) ∈ A2fun unitDisc :=
  ⟨hf.1.const_mul c, by rw [normA2_const_mul]; exact ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2⟩

theorem a4_A2_sub {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (hg : g ∈ A2fun unitDisc) :
    (fun z => f z - g z) ∈ A2fun unitDisc := by
  have h := a4_A2_add hf (a4_A2_const_mul hg (-1))
  refine ⟨hf.1.sub hg.1, ?_⟩
  have he : (fun z => f z - g z) = fun z => f z + -1 * g z := funext fun z => by ring
  rw [he]
  exact h.2

theorem a4_A2_mul {h k : ℂ → ℂ} (hh : h ∈ A21fun unitDisc) (hk : k ∈ A21fun unitDisc) :
    (fun z => h z * k z) ∈ A2fun unitDisc := by
  obtain ⟨C, hC⟩ := ac2_mul_disc
  exact ⟨hh.1.mul hk.1, (hC h hh k hk).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2) hk.2)⟩

/-- The `A₂¹(𝔻)` function with derivative `a` and value `c` at `0`. -/
theorem a4_r_hasDerivAt (x : A2 unitDisc × ℂ) {z : ℂ} (hz : z ∈ unitDisc) :
    HasDerivAt (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) (A2.toFun x.1 z) z := by
  simpa using (disk_segment_integral_hasDerivAt (A2.toFun_spec x.1).1 hz).const_add x.2

theorem a4_r_diff (x : A2 unitDisc × ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) unitDisc :=
  fun _ hz => (a4_r_hasDerivAt x hz).differentiableAt.differentiableWithinAt

theorem a4_r_deriv (x : A2 unitDisc × ℂ) :
    EqOn (deriv fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) (A2.toFun x.1) unitDisc :=
  fun _ hz => (a4_r_hasDerivAt x hz).deriv

theorem a4_r_zero (x : A2 unitDisc × ℂ) :
    (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) 0 = x.2 := by
  simp

theorem a4_const_norm (c : ℂ) : normA21 unitDisc (fun _ => c) ≤ ENNReal.ofReal (2 * ‖c‖) := by
  apply a55_le_of_sq_le
  rw [a55_normA21_sq, setLIntegral_const, show unitDisc = ball (0 : ℂ) 1 from rfl, Complex.volume_ball]
  rw [← ENNReal.ofReal_pow (by positivity), one_pow, ENNReal.ofReal_one, one_mul]
  have hπ : ((NNReal.pi : ℝ≥0) : ℝ≥0∞) ≤ 4 := by
    have : (NNReal.pi : ℝ) ≤ 4 := by rw [NNReal.coe_real_pi]; linarith [Real.pi_lt_four]
    exact_mod_cast this
  calc (‖c‖₊ : ℝ≥0∞) ^ 2 * (NNReal.pi : ℝ≥0∞) ≤ (‖c‖₊ : ℝ≥0∞) ^ 2 * 4 := by gcongr
    _ = ENNReal.ofReal (2 * ‖c‖) ^ 2 := by
      rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm, enorm_eq_nnnorm, ENNReal.ofReal_ofNat]
      ring

theorem a4_r_mem (x : A2 unitDisc × ℂ) :
    (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) ∈ A21fun unitDisc := by
  apply a21_of_derivative_A2 (a4_r_diff x)
  refine ⟨(a4_r_diff x).deriv isOpen_ball, ?_⟩
  rw [normA2_congr (D := unitDisc) measurableSet_ball (a4_r_deriv x)]
  exact (A2.toFun_mem x.1).2

theorem a4_r_norm (x : A2 unitDisc × ℂ) :
    normA21 unitDisc (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) ≤
      ENNReal.ofReal (5 * ‖x‖) := by
  have hS := disk_segment_integral_norm_bound (A2.toFun_mem x.1)
  rw [A2.norm_toFun] at hS
  have hm1 : AEStronglyMeasurable (fun _ : ℂ => x.2) (volume.restrict unitDisc) := aestronglyMeasurable_const
  have hm2 : AEStronglyMeasurable (fun z : ℂ => ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z)
      (volume.restrict unitDisc) :=
    (disk_segment_integral_A21 (A2.toFun_mem x.1)).1.continuousOn.aestronglyMeasurable measurableSet_ball
  refine (a55_normA21_add_le hm1 hm2).trans ?_
  refine (add_le_add (a4_const_norm x.2) hS).trans ?_
  have h1 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
  have h2 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have h8 : Real.sqrt 8 ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [show ((‖x.1‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ‖x.1‖ from (ofReal_norm x.1).symm.trans rfl,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg x.1, norm_nonneg x.2]

theorem a4_normA21_congr {f g : ℂ → ℂ} (h : EqOn f g unitDisc) : normA21 unitDisc f = normA21 unitDisc g := by
  unfold normA21
  congr 1
  exact setLIntegral_congr_fun measurableSet_ball (fun z hz => by rw [h hz])

theorem a4_A2_congr {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (h : EqOn f g unitDisc) : g ∈ A2fun unitDisc :=
  ⟨hf.1.congr (fun z hz => (h hz).symm), by rw [← normA2_congr (D := unitDisc) measurableSet_ball h]; exact hf.2⟩

theorem a4_toA2_congr {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (h : EqOn f g unitDisc) :
    toA2 unitDisc f = toA2 unitDisc g :=
  (a4_toA2_ext hf (a4_A2_congr hf h)).mpr h

theorem a4_toA2_add {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (hg : g ∈ A2fun unitDisc) :
    toA2 unitDisc (fun z => f z + g z) = toA2 unitDisc f + toA2 unitDisc g := by
  apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
  intro z hz
  rw [a4_toA2_eqOn (a4_A2_add hf hg) hz, A2.toFun_add (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.add_apply,
    a4_toA2_eqOn hf hz, a4_toA2_eqOn hg hz]

theorem a4_toA2_smul {f : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (c : ℂ) :
    toA2 unitDisc (fun z => c * f z) = c • toA2 unitDisc f := by
  apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
  intro z hz
  rw [a4_toA2_eqOn (a4_A2_const_mul hf c) hz, A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle _ _ hz,
    Pi.smul_apply, smul_eq_mul, a4_toA2_eqOn hf hz]

theorem a4_toA2_sub {f g : ℂ → ℂ} (hf : f ∈ A2fun unitDisc) (hg : g ∈ A2fun unitDisc) :
    toA2 unitDisc (fun z => f z - g z) = toA2 unitDisc f - toA2 unitDisc g := by
  apply A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball
  intro z hz
  rw [a4_toA2_eqOn (a4_A2_sub hf hg) hz, A2.toFun_sub (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.sub_apply,
    a4_toA2_eqOn hf hz, a4_toA2_eqOn hg hz]

/-- Real form of the product estimate `‖hk‖_{A₂} ≤ C‖h‖_{A₂¹}‖k‖_{A₂¹}`. -/
theorem a4_mul_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ A21fun unitDisc, ∀ k ∈ A21fun unitDisc,
    ‖toA2 unitDisc (fun z => h z * k z)‖ ≤ C * (normA21 unitDisc h).toReal * (normA21 unitDisc k).toReal := by
  obtain ⟨C, hC⟩ := ac2_mul_disc
  refine ⟨max C 0, le_max_right _ _, fun h hh k hk => ?_⟩
  have hm := a4_A2_mul hh hk
  have e : ‖toA2 unitDisc (fun z => h z * k z)‖ = (normA2 unitDisc (fun z => h z * k z)).toReal := by
    rw [← a4_toA2_norm hm]; rfl
  rw [e]
  have hb := hC h hh k hk
  refine (ENNReal.toReal_mono (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2) hk.2).ne hb).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal']

theorem a4_r_normReal (x : A2 unitDisc × ℂ) :
    (normA21 unitDisc (fun z : ℂ => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z)).toReal ≤ 5 * ‖x‖ :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (a4_r_norm x)

theorem a4_r_add (x y : A2 unitDisc × ℂ) :
    EqOn (fun z : ℂ => (x + y).2 + ∫ t in (0 : ℝ)..1, A2.toFun (x + y).1 ((t : ℂ) * z) * z)
      (fun z => (x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) +
        (y.2 + ∫ t in (0 : ℝ)..1, A2.toFun y.1 ((t : ℂ) * z) * z)) unitDisc := by
  apply a4_eqOn_of_deriv (a4_r_diff _) ((a4_r_diff x).add (a4_r_diff y))
  · intro z hz
    rw [a4_r_deriv _ hz, deriv_add ((a4_r_hasDerivAt x hz).differentiableAt) ((a4_r_hasDerivAt y hz).differentiableAt),
      (a4_r_hasDerivAt x hz).deriv, (a4_r_hasDerivAt y hz).deriv, Prod.fst_add,
      A2.toFun_add (D := unitDisc) isOpen_ball a4_circle _ _ hz, Pi.add_apply]
  · simp

theorem a4_r_smul (c : ℂ) (x : A2 unitDisc × ℂ) :
    EqOn (fun z : ℂ => (c • x).2 + ∫ t in (0 : ℝ)..1, A2.toFun (c • x).1 ((t : ℂ) * z) * z)
      (fun z => c * (x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z)) unitDisc := by
  apply a4_eqOn_of_deriv (a4_r_diff _) ((a4_r_diff x).const_mul c)
  · intro z hz
    rw [a4_r_deriv _ hz, deriv_const_mul _ ((a4_r_hasDerivAt x hz).differentiableAt),
      (a4_r_hasDerivAt x hz).deriv, Prod.smul_fst, A2.toFun_smul (D := unitDisc) isOpen_ball a4_circle _ _ hz,
      Pi.smul_apply, smul_eq_mul]
  · simp

theorem a4_r_sub (x y : A2 unitDisc × ℂ) :
    EqOn (fun z : ℂ => (x - y).2 + ∫ t in (0 : ℝ)..1, A2.toFun (x - y).1 ((t : ℂ) * z) * z)
      (fun z => (x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z) -
        (y.2 + ∫ t in (0 : ℝ)..1, A2.toFun y.1 ((t : ℂ) * z) * z)) unitDisc := by
  intro z hz
  have h1 := a4_r_add (x - y) y hz
  simp only [sub_add_cancel] at h1
  simp only
  rw [h1]
  ring

theorem a4_r_zero_fun : EqOn (fun z : ℂ => (0 : A2 unitDisc × ℂ).2 +
    ∫ t in (0 : ℝ)..1, A2.toFun (0 : A2 unitDisc × ℂ).1 ((t : ℂ) * z) * z) 0 unitDisc := by
  intro z hz
  have h := a4_r_smul 0 (0 : A2 unitDisc × ℂ) hz
  simp only [zero_smul, zero_mul] at h
  exact h

/-- **S4 (inverse function theorem for `Ψ̂`).** At a pre-Schwarzian `𝒜(f) ∈ A₂¹(𝔻)` of a locally univalent normalized
`f`, the map `ψ ↦ (Ψ(ψ), ψ(0))` has a continuous inverse on its image: `A₂` convergence of `Ψ(ψₙ)` and convergence
of `ψₙ(0)` force `A₂¹` convergence of `ψₙ`. -/
theorem a4_inverse {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hne : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hzero : deriv f 0 = 1) (hpre : preSchwarzian f ∈ A21fun unitDisc) {ψ : ℕ → ℂ → ℂ}
    (hψ : ∀ n, ψ n ∈ A21fun unitDisc)
    (hS : Tendsto (fun n => normA2 unitDisc (fun z => PsiOp (ψ n) z - PsiOp (preSchwarzian f) z)) atTop (𝓝 0))
    (h0 : Tendsto (fun n => ψ n 0) atTop (𝓝 (preSchwarzian f 0))) :
    Tendsto (fun n => normA21 unitDisc (fun z => ψ n z - preSchwarzian f z)) atTop (𝓝 0) := by
  set P := preSchwarzian f with hPdef
  set R : A2 unitDisc × ℂ → ℂ → ℂ := fun x z => x.2 + ∫ t in (0 : ℝ)..1, A2.toFun x.1 ((t : ℂ) * z) * z
    with hRdef
  have hRmem : ∀ x, R x ∈ A21fun unitDisc := a4_r_mem
  have hPR : ∀ x, (fun z => P z * R x z) ∈ A2fun unitDisc := fun x => a4_A2_mul hpre (hRmem x)
  have hRR : ∀ x, (fun z => (1 / 2 : ℂ) * (R x z * R x z)) ∈ A2fun unitDisc :=
    fun x => a4_A2_const_mul (a4_A2_mul (hRmem x) (hRmem x)) (1 / 2)
  obtain ⟨C, hC0, hC⟩ := a4_mul_le
  set NP := (normA21 unitDisc P).toReal with hNP
  have hNP0 : 0 ≤ NP := ENNReal.toReal_nonneg
  -- the linear part `x ↦ (a - P·r(x), c)`
  let ℓ : (A2 unitDisc × ℂ) →ₗ[ℂ] (A2 unitDisc × ℂ) :=
    { toFun := fun x => (x.1 - toA2 unitDisc (fun z => P z * R x z), x.2)
      map_add' := by
        intro x y
        have e : toA2 unitDisc (fun z => P z * R (x + y) z) =
            toA2 unitDisc (fun z => P z * R x z) + toA2 unitDisc (fun z => P z * R y z) := by
          rw [← a4_toA2_add (hPR x) (hPR y)]
          apply a4_toA2_congr (hPR _)
          intro z hz
          show P z * R (x + y) z = P z * R x z + P z * R y z
          rw [show R (x + y) z = R x z + R y z from a4_r_add x y hz]
          ring
        refine Prod.ext ?_ ?_
        · show (x + y).1 - toA2 unitDisc (fun z => P z * R (x + y) z) =
            (x.1 - toA2 unitDisc (fun z => P z * R x z)) + (y.1 - toA2 unitDisc (fun z => P z * R y z))
          rw [e, Prod.fst_add]
          abel
        · rfl
      map_smul' := by
        intro c x
        have e : toA2 unitDisc (fun z => P z * R (c • x) z) = c • toA2 unitDisc (fun z => P z * R x z) := by
          rw [← a4_toA2_smul (hPR x) c]
          apply a4_toA2_congr (hPR _)
          intro z hz
          show P z * R (c • x) z = c * (P z * R x z)
          rw [show R (c • x) z = c * R x z from a4_r_smul c x hz]
          ring
        refine Prod.ext ?_ ?_
        · show (c • x).1 - toA2 unitDisc (fun z => P z * R (c • x) z) =
            c • (x.1 - toA2 unitDisc (fun z => P z * R x z))
          rw [e, Prod.smul_fst, smul_sub]
        · rfl }
  have hℓb : ∀ x, ‖ℓ x‖ ≤ (1 + 5 * C * NP) * ‖x‖ := by
    intro x
    have hb := hC P hpre (R x) (hRmem x)
    have hr := a4_r_normReal x
    have h1 : ‖toA2 unitDisc (fun z => P z * R x z)‖ ≤ 5 * C * NP * ‖x‖ := by
      refine hb.trans ?_
      calc C * NP * (normA21 unitDisc (R x)).toReal ≤ C * NP * (5 * ‖x‖) := by gcongr
        _ = 5 * C * NP * ‖x‖ := by ring
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · show ‖x.1 - toA2 unitDisc (fun z => P z * R x z)‖ ≤ _
      have hx1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
      calc ‖x.1 - toA2 unitDisc (fun z => P z * R x z)‖ ≤ ‖x.1‖ + ‖toA2 unitDisc (fun z => P z * R x z)‖ :=
            norm_sub_le _ _
        _ ≤ _ := by nlinarith [norm_nonneg x]
    · show ‖x.2‖ ≤ _
      have hx2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
      nlinarith [norm_nonneg x, mul_nonneg (mul_nonneg hC0 hNP0) (norm_nonneg x)]
  let ℓc : (A2 unitDisc × ℂ) →L[ℂ] (A2 unitDisc × ℂ) := LinearMap.mkContinuous ℓ (1 + 5 * C * NP) hℓb
  -- the nonlinear map `G = ℓ - (½ r², 0)`
  let N : A2 unitDisc × ℂ → A2 unitDisc := fun x => toA2 unitDisc (fun z => (1 / 2 : ℂ) * (R x z * R x z))
  let G : A2 unitDisc × ℂ → A2 unitDisc × ℂ := fun x => ℓc x - (N x, 0)
  have hNdiff : ∀ x y, ‖N x - N y‖ ≤ 25 * C * ‖x - y‖ * (‖x‖ + ‖y‖) := by
    intro x y
    have he : N x - N y = (1 / 2 : ℂ) • toA2 unitDisc (fun z => R (x - y) z * R (x + y) z) := by
      rw [← a4_toA2_sub (hRR x) (hRR y), ← a4_toA2_smul (a4_A2_mul (hRmem _) (hRmem _))]
      apply a4_toA2_congr (a4_A2_sub (hRR x) (hRR y))
      intro z hz
      show (1 / 2 : ℂ) * (R x z * R x z) - (1 / 2 : ℂ) * (R y z * R y z) =
        (1 / 2 : ℂ) * (R (x - y) z * R (x + y) z)
      rw [show R (x - y) z = R x z - R y z from a4_r_sub x y hz,
        show R (x + y) z = R x z + R y z from a4_r_add x y hz]
      ring
    rw [he, norm_smul]
    have hb := hC _ (hRmem (x - y)) _ (hRmem (x + y))
    have h1 := a4_r_normReal (x - y)
    have h2 := a4_r_normReal (x + y)
    have h3 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hn]
    have h4 : C * (normA21 unitDisc (R (x - y))).toReal * (normA21 unitDisc (R (x + y))).toReal ≤
        C * (5 * ‖x - y‖) * (5 * (‖x‖ + ‖y‖)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) (by linarith) ENNReal.toReal_nonneg (by positivity)
    nlinarith [norm_nonneg (toA2 unitDisc (fun z => R (x - y) z * R (x + y) z)),
      mul_nonneg (mul_nonneg hC0 (norm_nonneg (x - y))) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
  have hG : HasStrictFDerivAt G ℓc 0 := by
    rw [hasStrictFDerivAt_iff_isLittleO]
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    have hδ : 0 < c / (50 * C + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds ((0 : A2 unitDisc × ℂ), (0 : A2 unitDisc × ℂ)) hδ] with p hp
    have hp' : ‖p‖ < c / (50 * C + 1) := by
      rw [Metric.mem_ball, Prod.mk_zero_zero, dist_zero_right] at hp
      exact hp
    have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    have he : G p.1 - G p.2 - ℓc (p.1 - p.2) = (N p.2 - N p.1, 0) := by
      simp only [G, map_sub]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_sub]
        abel
      · simp
    rw [he]
    have hN := hNdiff p.2 p.1
    rw [norm_sub_rev p.2 p.1] at hN
    have hq : ‖((N p.2 - N p.1, 0) : A2 unitDisc × ℂ)‖ = ‖N p.2 - N p.1‖ := by
      simp [Prod.norm_def]
    rw [hq]
    have hsum : ‖p.2‖ + ‖p.1‖ ≤ 2 * ‖p‖ := by linarith
    have hpc : (50 * C + 1) * ‖p‖ ≤ c := by
      rw [lt_div_iff₀ (by positivity)] at hp'
      linarith
    calc ‖N p.2 - N p.1‖ ≤ 25 * C * ‖p.1 - p.2‖ * (‖p.2‖ + ‖p.1‖) := hN
      _ ≤ 25 * C * ‖p.1 - p.2‖ * (2 * ‖p‖) := by gcongr
      _ = ‖p.1 - p.2‖ * (50 * C * ‖p‖) := by ring
      _ ≤ ‖p.1 - p.2‖ * c := by
          gcongr
          nlinarith [norm_nonneg p]
      _ = c * ‖p.1 - p.2‖ := by ring
  -- `ℓ` is bijective (Theorem A.3)
  have hinj : ∀ x, ℓc x = 0 → x = 0 := by
    intro x hx
    have h1 : x.1 - toA2 unitDisc (fun z => P z * R x z) = 0 := congrArg Prod.fst hx
    have h2 : x.2 = 0 := congrArg Prod.snd hx
    have hx1 : EqOn (A2.toFun x.1) (fun z => P z * R x z) unitDisc := by
      intro z hz
      rw [sub_eq_zero.mp h1]
      exact a4_toA2_eqOn (hPR x) hz
    have heq : EqOn (fun z => deriv (R x) z - P z * R x z) 0 unitDisc := by
      intro z hz
      show deriv (R x) z - P z * R x z = 0
      rw [a4_r_deriv x hz, hx1 hz, sub_self]
    have hR0 := linearized_Psi_injective hpre.1 (hRmem x).1 heq ((a4_r_zero x).trans h2)
    have ha : EqOn (A2.toFun x.1) (A2.toFun (0 : A2 unitDisc)) unitDisc := by
      intro z hz
      rw [a4_toFun_zero hz, ← a4_r_deriv x hz]
      have hev : R x =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        exact hR0 hw
      rw [hev.deriv_eq, deriv_const]
      rfl
    exact Prod.ext (A2.ext_of_toFun_eqOn (D := unitDisc) measurableSet_ball ha) h2
  have hsurj : ∀ y, ∃ x, ℓc x = y := by
    intro y
    obtain ⟨hpart1, -, -⟩ := thm_A_3_analytic hf hne hzero hpre
    obtain ⟨φ, hφ, hφeq, hφ0⟩ : ∃ φ : ℂ → ℂ, φ ∈ A21fun unitDisc ∧
        EqOn (fun z => deriv φ z - P z * φ z) (A2.toFun y.1) unitDisc ∧ (1 / 2) * φ 0 = y.2 / 2 :=
      ⟨_, hpart1 (A2.toFun y.1) (A2.toFun_mem y.1) (y.2 / 2)⟩
    have hφ' : deriv φ ∈ A2fun unitDisc := by
      refine a4_A2_congr (a4_A2_add (A2.toFun_mem y.1) (a4_A2_mul hpre hφ)) ?_
      intro z hz
      have h := hφeq hz
      simp only at h
      show A2.toFun y.1 z + P z * φ z = deriv φ z
      rw [← h]
      ring
    refine ⟨(toA2 unitDisc (deriv φ), φ 0), ?_⟩
    set x : A2 unitDisc × ℂ := (toA2 unitDisc (deriv φ), φ 0) with hxdef
    have hRx : EqOn (R x) φ unitDisc :=
      a4_eqOn_of_deriv (a4_r_diff x) hφ.1 (fun z hz => by rw [a4_r_deriv x hz]; exact a4_toA2_eqOn hφ' hz)
        (a4_r_zero x)
    refine Prod.ext ?_ ?_
    · show toA2 unitDisc (deriv φ) - toA2 unitDisc (fun z => P z * R x z) = y.1
      rw [a4_toA2_congr (hPR x) (g := fun z => P z * φ z) (fun z hz => by simp only; rw [hRx hz]),
        ← a4_toA2_sub hφ' (a4_A2_mul hpre hφ), a4_toA2_congr (a4_A2_sub hφ' (a4_A2_mul hpre hφ)) hφeq]
      exact toA2_toFun (D := unitDisc) isOpen_ball a4_circle y.1
    · show φ 0 = y.2
      linear_combination 2 * hφ0
  have hker :=
    (LinearMap.ker_eq_bot' (f := (ℓc : (A2 unitDisc × ℂ) →ₗ[ℂ] (A2 unitDisc × ℂ)))).mpr hinj
  have hran := (LinearMap.range_eq_top (f := (ℓc : (A2 unitDisc × ℂ) →ₗ[ℂ] (A2 unitDisc × ℂ)))).mpr hsurj
  let e := ContinuousLinearEquiv.ofBijective ℓc hker hran
  have hG' : HasStrictFDerivAt G (e : (A2 unitDisc × ℂ) →L[ℂ] (A2 unitDisc × ℂ)) 0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hG
  -- the data
  have hG0 : G 0 = 0 := by
    have hN0 : N 0 = 0 := by
      apply t31_toA2_zero
      intro z hz
      show (1 / 2 : ℂ) * (R 0 z * R 0 z) = 0
      rw [show R 0 z = 0 from a4_r_zero_fun hz]
      ring
    show ℓc 0 - (N 0, 0) = 0
    rw [map_zero, hN0, Prod.mk_zero_zero, sub_zero]
  have hΔ : ∀ᶠ n in atTop, (fun z => PsiOp (ψ n) z - PsiOp P z) ∈ A2fun unitDisc := by
    filter_upwards [(tendsto_order.1 hS).2 ⊤ ENNReal.zero_lt_top] with n hn
    refine ⟨?_, hn⟩
    have hd : ∀ g ∈ A21fun unitDisc, DifferentiableOn ℂ (PsiOp g) unitDisc := fun g hg =>
      (hg.1.deriv isOpen_ball).sub ((hg.1.pow 2).const_mul _)
    exact (hd _ (hψ n)).sub (hd _ hpre)
  let y : ℕ → A2 unitDisc × ℂ := fun n => (toA2 unitDisc (fun z => PsiOp (ψ n) z - PsiOp P z), ψ n 0 - P 0)
  have hy : Tendsto y atTop (𝓝 (G 0)) := by
    rw [hG0, show (0 : A2 unitDisc × ℂ) = ((0 : A2 unitDisc), (0 : ℂ)) from rfl]
    refine Tendsto.prodMk_nhds ?_ ?_
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
      rw [ENNReal.toReal_zero] at ht
      refine ht.congr' ?_
      filter_upwards [hΔ] with n hn
      show (normA2 unitDisc _).toReal = ‖toA2 unitDisc _‖
      rw [← a4_toA2_norm hn]
      rfl
    · simpa using h0.sub_const (P 0)
  set Linv := hG'.localInverse G e 0 with hLinv
  have hxt : Tendsto (fun n => Linv (y n)) atTop (𝓝 0) := by
    have h := hG'.localInverse_continuousAt.tendsto.comp hy
    rwa [hG'.localInverse_apply_image] at h
  have hev : ∀ᶠ n in atTop, G (Linv (y n)) = y n := hy.eventually hG'.eventually_right_inverse
  have hup : Tendsto (fun n => ENNReal.ofReal (5 * ‖Linv (y n)‖)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((hxt.norm).const_mul 5)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hev, hΔ] with n hn hΔn
  set x := Linv (y n) with hxdef
  have e1 : x.1 - toA2 unitDisc (fun z => P z * R x z) - N x =
      toA2 unitDisc (fun z => PsiOp (ψ n) z - PsiOp P z) := congrArg Prod.fst hn
  have e2 : x.2 - 0 = ψ n 0 - P 0 := congrArg Prod.snd hn
  have hE : EqOn (fun z => A2.toFun x.1 z - P z * R x z - (1 / 2 : ℂ) * (R x z * R x z))
      (fun z => PsiOp (ψ n) z - PsiOp P z) unitDisc := by
    have hm1 := a4_A2_sub (A2.toFun_mem x.1) (hPR x)
    refine (a4_toA2_ext (a4_A2_sub hm1 (hRR x)) hΔn).mp ?_
    rw [a4_toA2_sub hm1 (hRR x), a4_toA2_sub (A2.toFun_mem x.1) (hPR x),
      toA2_toFun (D := unitDisc) isOpen_ball a4_circle x.1]
    exact e1
  have hPsi : EqOn (PsiOp (fun z => P z + R x z)) (PsiOp (ψ n)) unitDisc := by
    intro z hz
    have h := hE hz
    simp only [PsiOp] at h ⊢
    have hd : HasDerivAt (fun w => P w + R x w) (deriv P z + A2.toFun x.1 z) z :=
      (hpre.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.add (a4_r_hasDerivAt x hz)
    rw [hd.deriv]
    linear_combination h
  have hval : (fun z => P z + R x z) 0 = ψ n 0 := by
    show P 0 + R x 0 = ψ n 0
    rw [show R x 0 = x.2 from a4_r_zero x]
    linear_combination e2
  have hEq := PsiOp_injective_with_value (hpre.1.add (hRmem x).1) (hψ n).1 hPsi hval
  rw [a4_normA21_congr (g := R x) (fun z hz => by
    show ψ n z - P z = R x z
    rw [← hEq hz, Pi.add_apply]
    ring)]
  exact a4_r_norm x

end AppA

end TakhtajanTeo
